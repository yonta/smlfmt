(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParseSmi:
sig
  datatype parser_output = Ast of SmiAst.t | JustComments of Token.t Seq.t

  val parse: Token.t Seq.t -> parser_output
end =
struct

  structure PC = ParserCombinators
  structure PS = ParseSimple

  datatype parser_output = Ast of SmiAst.t | JustComments of Token.t Seq.t

  (** Reached only through Token.isRecordLabel, which takes an AstAllows.t so
    * that `.sml` can gate string labels behind -allow-smlsharp. The `.smi`
    * grammar admits them unconditionally.
    *)
  val allows = AstAllows.make
    { topExp = false
    , optBar = false
    , recordPun = false
    , orPat = false
    , extendedText = false
    , sigWithtype = false
    , smlSharp = true
    }


  fun parse allTokens =
    let
      val toks = Seq.filter (not o Token.isCommentOrWhitespace) allTokens
      val numToks = Seq.length toks
      fun tok i = Seq.nth toks i
      fun check f i =
        i < numToks andalso f (tok i)
      fun isReserved rc i =
        check (fn t => Token.Reserved rc = Token.getClass t) i

      fun err i what explain =
        ParserUtils.tokError toks {pos = i, what = what, explain = explain}

      (** `_require`, `_use` and `_builtin` lex as an underscore followed by an
        * ordinary identifier, so they are recognised by name.
        *)
      fun isDirective name i =
        check Token.isIdentifier i
        andalso Source.toString (Token.getSource (tok i)) = name

      fun parse_reserved rc i =
        PS.reserved toks rc i
      fun parse_maybeReserved rc i =
        PS.maybeReserved toks rc i
      fun parse_maybeLongTycon i = PS.maybeLongTycon toks i
      fun parse_oneOrMoreWhile c p i =
        PC.oneOrMoreWhile c p i
      fun parse_token i = (i + 1, tok i)

      fun parse_string i =
        if check Token.isStringConstant i then
          (i + 1, tok i)
        else
          err i "Unexpected token." (SOME
            "Expected the path of a .smi file, in quotes.")
      fun parse_tyvar i = PS.tyvar toks i
      fun parse_tyvars i = PS.tyvars toks i
      fun parse_tycon i = PS.tycon toks i
      fun parse_strid i = PS.strid toks i
      fun parse_funid i = PS.funid toks i
      fun parse_vid i = PS.vid toks i
      fun parse_longvid i = PS.longvid toks i
      fun parse_maybeLongStrid i = PS.maybeLongStrid toks i
      fun parse_recordLabel i =
        PS.recordLabel allows toks i
      fun parse_zeroOrMoreDelimitedByReserved x i =
        PC.zeroOrMoreDelimitedByReserved toks x i
      fun parse_oneOrMoreDelimitedByReserved x i =
        PC.oneOrMoreDelimitedByReserved toks x i
      fun parse_zeroOrMoreWhile c p i =
        PC.zeroOrMoreWhile c p i


      (** ================================================================
        * Types.
        *)

      fun parse_ty i =
        parse_tyWithRestriction {permitArrows = true, permitTuple = true} i


      and parse_tyWithRestriction restriction i =
        let
          val (i, ty) =
            if check Token.isTyVar i then
              (i + 1, SmiAst.Ty.Var (tok i))
            else if isReserved Token.OpenParen i then
              let
                val leftParen = tok i
                val (i, ty) = parse_ty (i + 1)
              in
                parse_tyParensOrSequence leftParen [ty] [] i
              end
            else if isReserved Token.OpenCurlyBracket i then
              parse_tyRecord (tok i) (i + 1)
            else if isReserved Token.OpenSquareBracket i then
              parse_tyPoly (tok i) (i + 1)
            else if check Token.isMaybeLongIdentifier i then
              ( i + 1
              , SmiAst.Ty.Con
                  { id = MaybeLongToken.make (tok i)
                  , args = SmiAst.SyntaxSeq.Empty
                  }
              )
            else
              err i "Unexpected token." (SOME "Expected a type.")
        in
          parse_afterTy restriction ty i
        end


      (** ty
        *   ^
        *
        * Multiple possibilities for what could be found after a type:
        *   ty -> ty        -- function type
        *   ty longtycon    -- type constructor
        *   ty * ...        -- tuple
        *)
      and parse_afterTy (restriction as {permitArrows: bool, permitTuple: bool})
        ty i =
        let
          val (again, (i, ty)) =
            if check Token.isMaybeLongTyCon i then
              ( true
              , ( i + 1
                , SmiAst.Ty.Con
                    { id = MaybeLongToken.make (tok i)
                    , args = SmiAst.SyntaxSeq.One ty
                    }
                )
              )
            else if permitArrows andalso isReserved Token.Arrow i then
              (true, parse_tyArrow ty (i + 1))
            else if permitTuple andalso check Token.isStar i then
              (true, parse_tyTuple [ty] [] (i + 1))
            else
              (false, (i, ty))
        in
          if again then parse_afterTy restriction ty i else (i, ty)
        end


      (** { label: ty [, ...] }
        *  ^
        *)
      and parse_tyRows i =
        let
          fun parseElem i =
            let
              val (i, lab) = parse_recordLabel i
              val (i, colon) = parse_reserved Token.Colon i
              val (i, ty) = parse_ty i
            in
              (i, SmiAst.Ty.LabTy {lab = lab, colon = colon, ty = ty})
            end

          val (i, {elems, delims}) =
            parse_zeroOrMoreDelimitedByReserved
              { parseElem = parseElem
              , delim = Token.Comma
              , shouldStop = isReserved Token.CloseCurlyBracket
              } i

          val (i, right) = parse_reserved Token.CloseCurlyBracket i
        in
          (i, {elems = elems, delims = delims, right = right})
        end


      and parse_tyRecord leftBracket i =
        let
          val (i, {elems, delims, right}) = parse_tyRows i
        in
          ( i
          , SmiAst.Ty.Record
              { left = leftBracket
              , elems = elems
              , delims = delims
              , right = right
              }
          )
        end


      (** #boxed, or #{lab: ty, ...}
        * ^
        *)
      and parse_kind i =
        let
          val hash = tok i
          val i = i + 1
        in
          if isReserved Token.OpenCurlyBracket i then
            let
              val left = tok i
              val (i, {elems, delims, right}) = parse_tyRows (i + 1)
            in
              ( i
              , SmiAst.Ty.KindRecord
                  { hash = hash
                  , left = left
                  , elems = elems
                  , delims = delims
                  , right = right
                  }
              )
            end
          else if check Token.isTyCon i then
            (i + 1, SmiAst.Ty.KindProp {hash = hash, prop = tok i})
          else
            err i "Unexpected token." (SOME
              "Expected a kind property name or a record kind.")
        end


      (** [ 'a #kind ..., 'b. ty ]
        *  ^
        *)
      and parse_tyPoly left i =
        let
          fun parseElem i =
            let
              val (i, tyvar) = parse_tyvar i
              val (i, kinds) =
                parse_zeroOrMoreWhile (isReserved Token.Hash) parse_kind i
            in
              (i, {tyvar = tyvar, kinds = kinds})
            end

          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parseElem, delim = Token.Comma} i

          val (i, dot) = parse_reserved Token.Dot i
          val (i, ty) = parse_ty i
          val (i, right) = parse_reserved Token.CloseSquareBracket i
        in
          ( i
          , SmiAst.Ty.Poly
              { left = left
              , elems = elems
              , delims = delims
              , dot = dot
              , ty = ty
              , right = right
              }
          )
        end


      (** ty -> ty
        *      ^
        *)
      and parse_tyArrow fromTy i =
        let
          val arrow = tok (i - 1)
          val (i, toTy) = parse_ty i
        in
          (i, SmiAst.Ty.Arrow {from = fromTy, arrow = arrow, to = toTy})
        end


      (** [... *] ty * ...
        *             ^
        *)
      and parse_tyTuple tys delims i =
        let
          val star = tok (i - 1)
          val (i, ty) =
            parse_tyWithRestriction {permitArrows = false, permitTuple = false}
              i
          val tys = ty :: tys
          val delims = star :: delims
        in
          if check Token.isStar i then
            parse_tyTuple tys delims (i + 1)
          else
            ( i
            , SmiAst.Ty.Tuple
                {elems = Seq.fromRevList tys, delims = Seq.fromRevList delims}
            )
        end


      (** ( ty )
        *     ^
        * OR
        * ( ty [, ty ...] ) longtycon
        *     ^
        *)
      and parse_tyParensOrSequence leftParen tys delims i =
        if isReserved Token.CloseParen i then
          parse_tyEndParensOrSequence leftParen tys delims (i + 1)
        else if isReserved Token.Comma i then
          let
            val comma = tok i
            val (i, ty) = parse_ty (i + 1)
          in
            parse_tyParensOrSequence leftParen (ty :: tys) (comma :: delims) i
          end
        else
          err i "Unexpected token." NONE


      (** ( ty )
        *       ^
        * OR
        * ( ty, ... ) longtycon
        *            ^
        *)
      and parse_tyEndParensOrSequence leftParen tys delims i =
        let
          val rightParen = tok (i - 1)
        in
          case (tys, delims) of
            ([t], []) =>
              ( i
              , SmiAst.Ty.Parens {left = leftParen, ty = t, right = rightParen}
              )

          | _ =>
              if check Token.isMaybeLongTyCon i then
                ( i + 1
                , SmiAst.Ty.Con
                    { id = MaybeLongToken.make (tok i)
                    , args = SmiAst.SyntaxSeq.Many
                        { left = leftParen
                        , elems = Seq.fromRevList tys
                        , delims = Seq.fromRevList delims
                        , right = rightParen
                        }
                    }
                )
              else
                err i "Unexpected token." (SOME
                  "Expected to see a type constructor.")
        end


      (** ================================================================
        * Core declarations.
        *)

      (** case 'a in ty of ty => inst | ...
        * ^
        *)
      fun parse_overloadExp i =
        let
          val casee = tok i
          val (i, tyvar) = parse_tyvar (i + 1)
          val (i, inn) = parse_reserved Token.In i
          val (i, ty) = parse_ty i
          val (i, off) = parse_reserved Token.Of i
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_overloadMatch, delim = Token.Bar} i
        in
          ( i
          , SmiAst.Dec.OverloadExp
              { casee = casee
              , tyvar = tyvar
              , inn = inn
              , ty = ty
              , off = off
              , elems = elems
              , delims = delims
              }
          )
        end


      and parse_overloadMatch i =
        let
          val (i, ty) = parse_ty i
          val (i, arrow) = parse_reserved Token.FatArrow i
          val (i, inst) = parse_overloadInst i
        in
          (i, {ty = ty, arrow = arrow, inst = inst})
        end


      and parse_overloadInst i =
        if isReserved Token.Case i then
          let val (i, e) = parse_overloadExp i
          in (i, SmiAst.Dec.InstOverload e)
          end
        else if isReserved Token.OpenParen i then
          let
            val left = tok i
            val (i, inst) = parse_overloadInst (i + 1)
            val (i, right) = parse_reserved Token.CloseParen i
          in
            (i, SmiAst.Dec.InstParens {left = left, inst = inst, right = right})
          end
        else
          let val (i, id) = parse_longvid i
          in (i, SmiAst.Dec.InstLongId id)
          end


      (** val valbind
        * ^
        *)
      fun parse_decVal i =
        let
          val vall = tok i
          val (i, vid) = parse_vid (i + 1)

          val (i, bind) =
            if isReserved Token.Colon i then
              let
                val colon = tok i
                val (i, ty) = parse_ty (i + 1)
              in
                (i, SmiAst.Dec.ValTy {vid = vid, colon = colon, ty = ty})
              end
            else
              let
                val (i, eq) = parse_reserved Token.Equal i
              in
                if
                  isReserved Token.Underscore i
                  andalso isDirective "builtin" (i + 1)
                then
                  let
                    val underscore = tok i
                    val builtin = tok (i + 1)
                    val (i, vall2) = parse_reserved Token.Val (i + 2)
                    val (i, builtinVid) = parse_vid i
                    val (i, colon) = parse_reserved Token.Colon i
                    val (i, ty) = parse_ty i
                  in
                    ( i
                    , SmiAst.Dec.ValBuiltin
                        { vid = vid
                        , eq = eq
                        , underscore = underscore
                        , builtin = builtin
                        , vall = vall2
                        , builtinVid = builtinVid
                        , colon = colon
                        , ty = ty
                        }
                    )
                  end
                else if
                  isReserved Token.Case i
                then
                  let val (i, exp) = parse_overloadExp i
                  in (i, SmiAst.Dec.ValOverload {vid = vid, eq = eq, exp = exp})
                  end
                else
                  let val (i, id) = parse_longvid i
                  in (i, SmiAst.Dec.ValAlias {vid = vid, eq = eq, id = id})
                  end
              end
        in
          (i, SmiAst.Dec.Val {vall = vall, bind = bind})
        end


      (** tyvarseq tycon ( = impl )
        *                ^
        *)
      fun parse_typbindOpaque tyvars tycon i =
        let
          val left = tok i
          val (i, eq) = parse_reserved Token.Equal (i + 1)
          val (i, impl) =
            if isReserved Token.Arrow i then
              (i + 1, SmiAst.Dec.ImplFunc (tok i))
            else if isReserved Token.OpenCurlyBracket i then
              let
                val implLeft = tok i
                val (i, implRight) =
                  parse_reserved Token.CloseCurlyBracket (i + 1)
              in
                (i, SmiAst.Dec.ImplRecord {left = implLeft, right = implRight})
              end
            else
              let val (i, id) = parse_longvid i
              in (i, SmiAst.Dec.ImplTy id)
              end
          val (i, right) = parse_reserved Token.CloseParen i
        in
          ( i
          , SmiAst.Dec.Opaque
              { tyvars = tyvars
              , tycon = tycon
              , left = left
              , eq = eq
              , impl = impl
              , right = right
              }
          )
        end


      (** tyvarseq tycon = ty
        *                ^
        *)
      fun parse_typbindTransparentAfter tyvars tycon i =
        let
          val (i, eq) = parse_reserved Token.Equal i
          val (i, ty) = parse_ty i
        in
          ( i
          , SmiAst.Dec.Transparent
              {tyvars = tyvars, tycon = tycon, eq = eq, ty = ty}
          )
        end


      fun parse_typbindTransparent i =
        let
          val (i, tyvars) = parse_tyvars i
          val (i, tycon) = parse_tycon i
        in
          parse_typbindTransparentAfter tyvars tycon i
        end


      fun parse_typbind i =
        let
          val (i, tyvars) = parse_tyvars i
          val (i, tycon) = parse_tycon i
        in
          if isReserved Token.OpenParen i then
            parse_typbindOpaque tyvars tycon i
          else
            parse_typbindTransparentAfter tyvars tycon i
        end


      (** An eqtype has no transparent form: the runtime representation is
        * mandatory.
        *)
      fun parse_eqtypbind i =
        let
          val (i, tyvars) = parse_tyvars i
          val (i, tycon) = parse_tycon i
        in
          if isReserved Token.OpenParen i then
            parse_typbindOpaque tyvars tycon i
          else
            err i "Unexpected token." (SOME
              "An eqtype in a .smi must give a runtime representation, as \
              \in `eqtype t (= int)`.")
        end


      (** type typbind [and typbind ...]
        * ^
        *)
      fun parse_decType i =
        let
          val typee = tok i
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_typbind, delim = Token.And} (i + 1)
        in
          (i, SmiAst.Dec.Type {typee = typee, elems = elems, delims = delims})
        end


      (** eqtype eqtypbind [and eqtypbind ...]
        * ^
        *)
      fun parse_decEqtype i =
        let
          val eqtypee = tok i
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_eqtypbind, delim = Token.And} (i + 1)
        in
          ( i
          , SmiAst.Dec.Eqtype
              {eqtypee = eqtypee, elems = elems, delims = delims}
          )
        end


      fun parse_conbind i =
        let
          val (i, opp) = parse_maybeReserved Token.Op i
          val (i, vid) = parse_vid i
          val (i, arg) =
            if isReserved Token.Of i then
              let
                val off = tok i
                val (i, ty) = parse_ty (i + 1)
              in
                (i, SOME {off = off, ty = ty})
              end
            else
              (i, NONE)
        in
          (i, {opp = opp, vid = vid, arg = arg})
        end


      fun parse_datbind i =
        let
          val (i, tyvars) = parse_tyvars i
          val (i, tycon) = parse_tycon i
          val (i, eq) = parse_reserved Token.Equal i
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_conbind, delim = Token.Bar} i
        in
          ( i
          , { tyvars = tyvars
            , tycon = tycon
            , eq = eq
            , elems = elems
            , delims = delims
            }
          )
        end


      (** datatype datbind [and ...] [withtype ...]
        * ^
        * OR
        * datatype tycon = datatype longtycon
        * OR
        * datatype tycon = _builtin datatype tycon
        *)
      fun parse_decDatatype i =
        let
          val left_datatypee = tok i

          val looksLikeRep =
            check Token.isTyCon (i + 1) andalso isReserved Token.Equal (i + 2)
        in
          if
            looksLikeRep andalso isReserved Token.Datatype (i + 3)
          then
            let
              val tycon = tok (i + 1)
              val eq = tok (i + 2)
              val right_datatypee = tok (i + 3)
              val (i, id) = parse_maybeLongTycon (i + 4)
            in
              ( i
              , SmiAst.Dec.DatatypeRep
                  { left_datatypee = left_datatypee
                  , tycon = tycon
                  , eq = eq
                  , right_datatypee = right_datatypee
                  , id = id
                  }
              )
            end
          else if
            looksLikeRep andalso isReserved Token.Underscore (i + 3)
            andalso isDirective "builtin" (i + 4)
            andalso isReserved Token.Datatype (i + 5)
          then
            let
              val tycon = tok (i + 1)
              val eq = tok (i + 2)
              val underscore = tok (i + 3)
              val builtin = tok (i + 4)
              val right_datatypee = tok (i + 5)
              val (i, builtinTycon) = parse_tycon (i + 6)
            in
              ( i
              , SmiAst.Dec.DatatypeBuiltin
                  { left_datatypee = left_datatypee
                  , tycon = tycon
                  , eq = eq
                  , underscore = underscore
                  , builtin = builtin
                  , right_datatypee = right_datatypee
                  , builtinTycon = builtinTycon
                  }
              )
            end
          else
            let
              val (i, {elems, delims}) =
                parse_oneOrMoreDelimitedByReserved
                  {parseElem = parse_datbind, delim = Token.And} (i + 1)

              val (i, withtypee) =
                if isReserved Token.Withtype i then
                  let
                    val withtypee = tok i
                    val (i, {elems, delims}) =
                      parse_oneOrMoreDelimitedByReserved
                        { parseElem = parse_typbindTransparent
                        , delim = Token.And
                        } (i + 1)
                  in
                    ( i
                    , SOME
                        {withtypee = withtypee, elems = elems, delims = delims}
                    )
                  end
                else
                  (i, NONE)
            in
              ( i
              , SmiAst.Dec.Datatype
                  { datatypee = left_datatypee
                  , elems = elems
                  , delims = delims
                  , withtypee = withtypee
                  }
              )
            end
        end


      fun parse_exbind i =
        let
          val (i, opp) = parse_maybeReserved Token.Op i
          val (i, vid) = parse_vid i
        in
          if isReserved Token.Equal i then
            let
              val eq = tok i
              val (i, id) = parse_longvid (i + 1)
            in
              (i, SmiAst.Dec.ExnRep {opp = opp, vid = vid, eq = eq, id = id})
            end
          else if isReserved Token.Of i then
            let
              val off = tok i
              val (i, ty) = parse_ty (i + 1)
            in
              ( i
              , SmiAst.Dec.ExnNew
                  {opp = opp, vid = vid, arg = SOME {off = off, ty = ty}}
              )
            end
          else
            (i, SmiAst.Dec.ExnNew {opp = opp, vid = vid, arg = NONE})
        end


      (** exception exbind [and exbind ...]
        * ^
        *)
      fun parse_decException i =
        let
          val exceptionn = tok i
          val (i, {elems, delims}) =
            parse_oneOrMoreDelimitedByReserved
              {parseElem = parse_exbind, delim = Token.And} (i + 1)
        in
          ( i
          , SmiAst.Dec.Exception
              {exceptionn = exceptionn, elems = elems, delims = delims}
          )
        end


      (** ================================================================
        * Structures.
        *)

      fun isStrDecStart i =
        isReserved Token.Val i orelse isReserved Token.Type i
        orelse isReserved Token.Eqtype i orelse isReserved Token.Datatype i
        orelse isReserved Token.Exception i orelse isReserved Token.Structure i
        orelse isReserved Token.Semicolon i


      fun parse_strdec i =
        let
          fun core parser i =
            let val (i, d) = parser i
            in (i, SmiAst.Str.Dec d)
            end
        in
          if isReserved Token.Semicolon i then
            (i + 1, SmiAst.Str.Semicolon (tok i))
          else if isReserved Token.Val i then
            core parse_decVal i
          else if isReserved Token.Type i then
            core parse_decType i
          else if isReserved Token.Eqtype i then
            core parse_decEqtype i
          else if isReserved Token.Datatype i then
            core parse_decDatatype i
          else if isReserved Token.Exception i then
            core parse_decException i
          else if isReserved Token.Structure i then
            parse_strdecStructure i
          else
            err i "Unexpected token." (SOME
              "Expected beginning of declaration.")
        end


      (** structure strid = strexp
        * ^
        *)
      and parse_strdecStructure i =
        let
          val structuree = tok i
          val (i, strid) = parse_strid (i + 1)
          val (i, eq) = parse_reserved Token.Equal i
          val (i, strexp) = parse_strexp i
        in
          ( i
          , SmiAst.Str.Structure
              {structuree = structuree, strid = strid, eq = eq, strexp = strexp}
          )
        end


      and parse_strexp i =
        if
          isReserved Token.Struct i
        then
          let
            val structt = tok i
            val (i, elems) = parse_strdecs (i + 1)
            val (i, endd) = parse_reserved Token.End i
          in
            ( i
            , SmiAst.Str.Struct {structt = structt, elems = elems, endd = endd}
            )
          end
        else if
          check Token.isStrIdentifier i
          andalso isReserved Token.OpenParen (i + 1)
        then
          let
            val (i, funid) = parse_funid i
            val (i, left) = parse_reserved Token.OpenParen i
            val (i, id) = parse_maybeLongStrid i
            val (i, right) = parse_reserved Token.CloseParen i
          in
            ( i
            , SmiAst.Str.FunAppIdent
                {funid = funid, left = left, id = id, right = right}
            )
          end
        else
          let val (i, id) = parse_maybeLongStrid i
          in (i, SmiAst.Str.Ident id)
          end


      and parse_strdecs i =
        parse_zeroOrMoreWhile isStrDecStart parse_strdec i


      (** ================================================================
        * Whole file.
        *)

      (** infix [prec] vid ...
        * ^
        *)
      fun parse_topInfix i =
        let
          val infixx = tok i
          val (i, precedence) =
            if check Token.isDecimalIntegerConstant (i + 1) then
              (i + 2, SOME (tok (i + 1)))
            else
              (i + 1, NONE)
          val (i, elems) =
            parse_oneOrMoreWhile (check Token.isValueIdentifier) parse_token i
        in
          ( i
          , SmiAst.TopInfix
              {infixx = infixx, precedence = precedence, elems = elems}
          )
        end


      fun isTopDecStart i =
        isStrDecStart i orelse isReserved Token.Infix i
        orelse isReserved Token.Infixr i


      fun parse_topdec i =
        if isReserved Token.Infix i orelse isReserved Token.Infixr i then
          parse_topInfix i
        else
          let val (i, d) = parse_strdec i
          in (i, SmiAst.TopStrDec d)
          end


      fun isRequireStart i =
        isReserved Token.Semicolon i
        orelse
        (isReserved Token.Underscore i
         andalso
         (isDirective "require" (i + 1) orelse isDirective "use" (i + 1)))


      fun parse_require i =
        if isReserved Token.Semicolon i then
          (i + 1, SmiAst.RequireSemicolon (tok i))
        else
          let
            val underscore = tok i
            val directive = tok (i + 1)
            val isUse = isDirective "use" (i + 1)
            val (i, locall) = parse_maybeReserved Token.Local (i + 2)
          in
            case (isUse, locall) of
              (true, NONE) =>
                err i "Unexpected token." (SOME
                  "A .smi cannot use the bare `_use` of a .sml; it must be \
                  \written `_use local \"path\"`.")

            | (true, SOME l) =>
                let
                  val (i, path) = parse_string i
                in
                  ( i
                  , SmiAst.Use
                      { underscore = underscore
                      , directive = directive
                      , locall = l
                      , path = path
                      }
                  )
                end

            | _ =>
                let
                  val (i, path) = parse_string i
                  val (i, options) =
                    parse_zeroOrMoreWhile (check Token.isValueIdentifier)
                      parse_token i
                in
                  ( i
                  , SmiAst.Require
                      { underscore = underscore
                      , directive = directive
                      , locall = locall
                      , path = path
                      , options = options
                      }
                  )
                end
          end


      val (i, requires) = parse_zeroOrMoreWhile isRequireStart parse_require 0
      val (i, topdecs) = parse_zeroOrMoreWhile isTopDecStart parse_topdec i

      val _ =
        if i >= numToks then
          ()
        else
          ParserUtils.error
            { pos = Token.getSource (tok i)
            , what = "Unexpected token."
            , explain = SOME "Invalid start of top-level declaration."
            }

      val ast = SmiAst.Interface {requires = requires, topdecs = topdecs}
    in
      if numToks > 0 then
        Ast ast
      else
        let
          val commentsOnly = Seq.filter Token.isComment allTokens
        in
          if Seq.length commentsOnly > 0 then JustComments commentsOnly
          else Ast ast
        end
    end

end

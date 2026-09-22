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

      fun parse_reserved rc i =
        PS.reserved toks rc i
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
      and parse_tyRecord leftBracket i =
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

          val (i, rightBracket) = parse_reserved Token.CloseCurlyBracket i
        in
          ( i
          , SmiAst.Ty.Record
              { left = leftBracket
              , elems = elems
              , delims = delims
              , right = rightBracket
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

      (** val vid : ty
        * ^
        *)
      fun parse_decVal i =
        let
          val vall = tok i
          val (i, vid) = parse_vid (i + 1)
          val (i, colon) = parse_reserved Token.Colon i
          val (i, ty) = parse_ty i
        in
          (i, SmiAst.Dec.Val {vall = vall, vid = vid, colon = colon, ty = ty})
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


      fun parse_typbind i =
        let
          val (i, tyvars) = parse_tyvars i
          val (i, tycon) = parse_tycon i
        in
          if isReserved Token.OpenParen i then
            parse_typbindOpaque tyvars tycon i
          else
            let
              val (i, eq) = parse_reserved Token.Equal i
              val (i, ty) = parse_ty i
            in
              ( i
              , SmiAst.Dec.Transparent
                  {tyvars = tyvars, tycon = tycon, eq = eq, ty = ty}
              )
            end
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


      (** ================================================================
        * Structures.
        *)

      fun isStrDecStart i =
        isReserved Token.Val i orelse isReserved Token.Type i
        orelse isReserved Token.Structure i orelse isReserved Token.Semicolon i


      fun parse_strdec i =
        if isReserved Token.Semicolon i then
          (i + 1, SmiAst.Str.Semicolon (tok i))
        else if isReserved Token.Val i then
          let val (i, d) = parse_decVal i
          in (i, SmiAst.Str.Dec d)
          end
        else if isReserved Token.Type i then
          let val (i, d) = parse_decType i
          in (i, SmiAst.Str.Dec d)
          end
        else if isReserved Token.Structure i then
          parse_strdecStructure i
        else
          err i "Unexpected token." (SOME "Expected beginning of declaration.")


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

      fun isDirective name i =
        check Token.isIdentifier i
        andalso Source.toString (Token.getSource (tok i)) = name


      fun isRequireStart i =
        isReserved Token.Semicolon i
        orelse
        (isReserved Token.Underscore i andalso isDirective "require" (i + 1))


      fun parse_require i =
        if isReserved Token.Semicolon i then
          (i + 1, SmiAst.RequireSemicolon (tok i))
        else
          let
            val underscore = tok i
            val directive = tok (i + 1)
            val i = i + 2
          in
            if check Token.isStringConstant i then
              ( i + 1
              , SmiAst.Require
                  {underscore = underscore, directive = directive, path = tok i}
              )
            else
              err i "Unexpected token." (SOME
                "Expected the path of a .smi file, in quotes.")
          end


      val (i, requires) = parse_zeroOrMoreWhile isRequireStart parse_require 0
      val (i, topdecs) = parse_strdecs i

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

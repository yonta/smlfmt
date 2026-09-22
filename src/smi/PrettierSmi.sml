(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure PrettierSmi:
sig
  val pretty:
    {ribbonFrac: real, maxWidth: int, tabWidth: int, indent: int, debug: bool}
    -> SmiAst.t
    -> TerminalColorString.t
end =
struct

  open TabbedTokenDoc
  open PrettierUtil
  infix 2 ++
  fun x ++ y = concat (x, y)


  (** A label or identifier hugs the `:` that follows it, unless that would
    * glue two symbols together or swallow a comment.
    *)
  fun hugNext tok =
    if Token.isSymbolicIdentifier tok orelse Token.hasCommentsAfter tok then
      empty
    else
      nospace


  (** Lay out a run of items, each of which says whether it begins a line.
    * A bare `;` does not: it trails the declaration it follows.
    *)
  fun joinAt tab (items: (bool * doc) Seq.t) =
    if Seq.length items = 0 then
      empty
    else
      let
        fun showOne (ownLine, doc) =
          if ownLine then at tab doc else doc
        val (_, first) = Seq.nth items 0
      in
        Seq.iterate op++ first (Seq.map showOne (Seq.drop items 1))
      end


  fun showTyRow tab (SmiAst.Ty.LabTy {lab, colon, ty}) =
    token lab ++ hugNext lab ++ token colon ++ showTy tab ty


  (** A kind constraint hugs the type variable it constrains: `'a#boxed`. *)
  and showKind tab kind =
    let
      open SmiAst.Ty
    in
      case kind of
        KindProp {hash, prop} => nospace ++ token hash ++ nospace ++ token prop

      | KindRecord {hash, left, elems, delims, right} =>
          nospace ++ token hash ++ nospace
          ++
          showSequence (fn _ => false) (withNewChild showTyRow) tab
            {openn = left, elems = elems, delims = delims, close = right}
    end


  and showTy tab ty : doc =
    let
      open SmiAst.Ty
    in
      case ty of
        Var tok => token tok

      | Con {args = SmiAst.SyntaxSeq.Empty, id} =>
          token (MaybeLongToken.getToken id)

      | Con {args, id} =>
          showSyntaxSeq (withNewChild showTy) tab args
          ++ token (MaybeLongToken.getToken id)

      | Parens {left, ty, right} =>
          token left ++ nospace ++ withNewChild showTy tab ty ++ nospace
          ++ token right

      | Tuple {elems, delims} =>
          newTab tab (fn tab =>
            let
              fun f (delim, x) =
                at tab (token delim ++ withNewChild showTy tab x)
            in
              Seq.iterate op++
                (at tab (withNewChild showTy tab (Seq.nth elems 0)))
                (Seq.zipWith f (delims, Seq.drop elems 1))
            end)

      | Record {left, elems, delims, right} =>
          showSequence (fn _ => false) (withNewChild showTyRow) tab
            {openn = left, elems = elems, delims = delims, close = right}

      | Poly {left, elems, delims, dot, ty, right} =>
          let
            fun showKindedTyvar {tyvar, kinds} =
              Seq.iterate op++ (token tyvar) (Seq.map (showKind tab) kinds)

            fun showRest (delim, x) =
              nospace ++ token delim ++ showKindedTyvar x
          in
            token left ++ nospace
            ++
            Seq.iterate op++ (showKindedTyvar (Seq.nth elems 0))
              (Seq.zipWith showRest (delims, Seq.drop elems 1)) ++ nospace
            ++ token dot ++ withNewChild showTy tab ty ++ nospace ++ token right
          end

      | Arrow {from, arrow, to} =>
          let
            fun loop (arr, right) =
              at tab
                (token arr
                 ++
                 (case right of
                    Arrow {from, arrow, to} =>
                      withNewChild showTy tab from ++ loop (arrow, to)
                  | _ => withNewChild showTy tab right))
          in
            withNewChild showTy tab from ++ loop (arrow, to)
          end
    end


  fun showImpl impl =
    let
      open SmiAst.Dec
    in
      case impl of
        ImplTy id => token (MaybeLongToken.getToken id)
      | ImplFunc tok => token tok
      | ImplRecord {left, right} => token left ++ nospace ++ token right
    end


  fun showTypbind tab tb =
    let
      open SmiAst.Dec
    in
      case tb of
        Transparent {tyvars, tycon, eq, ty} =>
          showTokenSyntaxSeq tab tyvars ++ token tycon ++ token eq
          ++ withNewChild showTy tab ty

      | Opaque {tyvars, tycon, left, eq, impl, right} =>
          showTokenSyntaxSeq tab tyvars ++ token tycon ++ token left ++ nospace
          ++ token eq ++ showImpl impl ++ nospace ++ token right
    end


  (** `type ...` and `eqtype ...` lay out the same way; only the keyword that
    * starts the first binding differs.
    *)
  fun showTypbinds tab starter elems delims =
    newTab tab (fn inner =>
      let
        fun showOne (delim, tb) =
          at inner (token delim ++ showTypbind inner tb)
      in
        at inner
          (Seq.iterate op++
             (token starter ++ showTypbind inner (Seq.nth elems 0))
             (Seq.map showOne (Seq.zip (delims, Seq.drop elems 1))))
      end)


  (** Laid out like SML's `case`: the bars line up under the keyword, and the
    * first branch is padded to match.
    *)
  fun showOverloadExp tab
    (SmiAst.Dec.OverloadExp {casee, tyvar, inn, ty, off, elems, delims}) =
    let
      fun showMatch inner {ty, arrow, inst} =
        withNewChild showTy inner ty ++ token arrow
        ++
        withNewChildWithStyle (indentedAtLeastBy 4) showOverloadInst inner inst

      fun mk inner (delim, m) =
        at inner
          ((case delim of
              SOME d => token d
            | NONE => cond inner {active = space ++ space, inactive = empty})
           ++ showMatch inner m)
    in
      newTabWithStyle tab (rigidInplace, fn inner1 =>
        newTab inner1 (fn inner2 =>
          at inner1 (token casee ++ token tyvar ++ token inn)
          ++ at inner2 (showTy inner2 ty)
          ++ cond inner2 {inactive = token off, active = at inner1 (token off)}
          ++
          Seq.iterate op++ (mk inner1 (NONE, Seq.nth elems 0))
            (Seq.zipWith (mk inner1) (Seq.map SOME delims, Seq.drop elems 1))))
    end


  and showOverloadInst tab inst =
    let
      open SmiAst.Dec
    in
      case inst of
        InstOverload e => showOverloadExp tab e

      | InstLongId id => token (MaybeLongToken.getToken id)

      | InstParens {left, inst, right} =>
          token left ++ nospace ++ showOverloadInst tab inst ++ nospace
          ++ token right
    end


  fun showConbind tab {opp, vid, arg} =
    showMaybeOpToken opp vid
    ++
    (case arg of
       NONE => empty
     | SOME {off, ty} => token off ++ withNewChild showTy tab ty)


  fun showDatbind tab {tyvars, tycon, eq, elems, delims} =
    showTokenSyntaxSeq tab tyvars ++ token tycon ++ token eq
    ++
    newTab tab (fn inner =>
      let
        fun showOne (delim, c) =
          at inner (token delim ++ showConbind inner c)
      in
        at inner (showConbind inner (Seq.nth elems 0))
        ++
        Seq.iterate op++ empty (Seq.map showOne (Seq.zip
          (delims, Seq.drop elems 1)))
      end)


  fun showValbind tab bind =
    let
      open SmiAst.Dec
    in
      case bind of
        ValTy {vid, colon, ty} =>
          token vid ++ hugNext vid ++ token colon ++ withNewChild showTy tab ty

      | ValAlias {vid, eq, id} =>
          token vid ++ token eq ++ token (MaybeLongToken.getToken id)

      | ValBuiltin {vid, eq, underscore, builtin, vall, builtinVid, colon, ty} =>
          token vid ++ token eq ++ token underscore ++ nospace ++ token builtin
          ++ token vall ++ token builtinVid ++ hugNext builtinVid ++ token colon
          ++ withNewChild showTy tab ty

      | ValOverload {vid, eq, exp} =>
          token vid ++ token eq ++ withNewChild showOverloadExp tab exp
    end


  fun showDec tab dec =
    let
      open SmiAst.Dec
    in
      case dec of
        Val {vall, bind} =>
          newTab tab (fn inner =>
            at inner (token vall ++ showValbind inner bind))

      | Type {typee, elems, delims} => showTypbinds tab typee elems delims

      | Eqtype {eqtypee, elems, delims} => showTypbinds tab eqtypee elems delims

      | Datatype {datatypee, elems, delims, withtypee} =>
          newTab tab (fn inner =>
            let
              fun showOne (delim, db) =
                at inner (token delim ++ showDatbind inner db)

              val withtypeDoc =
                case withtypee of
                  NONE => empty
                | SOME {withtypee, elems, delims} =>
                    at inner (showTypbinds inner withtypee elems delims)
            in
              at inner
                (Seq.iterate op++
                   (token datatypee ++ showDatbind inner (Seq.nth elems 0))
                   (Seq.map showOne (Seq.zip (delims, Seq.drop elems 1))))
              ++ withtypeDoc
            end)

      | DatatypeRep {left_datatypee, tycon, eq, right_datatypee, id} =>
          token left_datatypee ++ token tycon ++ token eq
          ++ token right_datatypee ++ token (MaybeLongToken.getToken id)

      | DatatypeBuiltin
          { left_datatypee
          , tycon
          , eq
          , underscore
          , builtin
          , right_datatypee
          , builtinTycon
          } =>
          token left_datatypee ++ token tycon ++ token eq ++ token underscore
          ++ nospace ++ token builtin ++ token right_datatypee
          ++ token builtinTycon

      | Exception {exceptionn, elems, delims} =>
          newTab tab (fn inner =>
            let
              fun showExbind tab eb =
                case eb of
                  ExnNew c => showConbind tab c
                | ExnRep {opp, vid, eq, id} =>
                    showMaybeOpToken opp vid ++ token eq
                    ++ token (MaybeLongToken.getToken id)

              fun showOne (delim, eb) =
                at inner (token delim ++ showExbind inner eb)
            in
              at inner
                (Seq.iterate op++
                   (token exceptionn ++ showExbind inner (Seq.nth elems 0))
                   (Seq.map showOne (Seq.zip (delims, Seq.drop elems 1))))
            end)
    end


  fun strDecStartsLine (SmiAst.Str.Semicolon _) = false
    | strDecStartsLine _ = true


  fun showStrExp tab e =
    let
      open SmiAst.Str
    in
      case e of
        Ident id => token (MaybeLongToken.getToken id)

      | Struct {structt, elems, endd} =>
          if Seq.length elems = 0 then
            token structt ++ at tab (token endd)
          else
            newTabWithStyle tab (indented, fn inner =>
              token structt ++ at inner (showStrDecs inner elems)
              ++
              cond inner {inactive = token endd, active = at tab (token endd)})

      | FunAppIdent {funid, left, id, right} =>
          newTab tab (fn inner =>
            token funid ++ nospace
            ++
            at inner
              (token left ++ nospace ++ token (MaybeLongToken.getToken id)
               ++ nospace ++ token right))
    end


  and showStrDec tab d =
    let
      open SmiAst.Str
    in
      case d of
        Dec dec => showDec tab dec

      | Semicolon tok => nospace ++ token tok

      | Structure {structuree, strid, eq, strexp} =>
          newTab tab (fn inner =>
            at inner
              (token structuree ++ token strid ++ token eq
               ++
               (case strexp of
                  Struct _ => at inner (showStrExp inner strexp)
                | _ => withNewChild showStrExp inner strexp)))
    end


  and showStrDecs tab elems =
    joinAt tab (Seq.map (fn d => (strDecStartsLine d, showStrDec tab d)) elems)


  fun showRequire tab r =
    case r of
      SmiAst.Require {underscore, directive, locall, path, options} =>
        token underscore ++ nospace ++ token directive
        ++ showOption token locall ++ token path
        ++ Seq.iterate op++ empty (Seq.map token options)

    | SmiAst.Use {underscore, directive, locall, path} =>
        token underscore ++ nospace ++ token directive ++ token locall
        ++ token path

    | SmiAst.RequireSemicolon tok => nospace ++ token tok


  fun requireStartsLine (SmiAst.RequireSemicolon _) = false
    | requireStartsLine _ = true


  fun showTopDec tab td =
    case td of
      SmiAst.TopStrDec d => showStrDec tab d

    | SmiAst.TopInfix {infixx, precedence, elems} =>
        token infixx ++ showOption token precedence
        ++ Seq.iterate op++ empty (Seq.map token elems)


  fun topDecStartsLine (SmiAst.TopStrDec d) = strDecStartsLine d
    | topDecStartsLine _ = true


  fun showAst (SmiAst.Interface {requires, topdecs}) =
    joinAt root (Seq.append
      ( Seq.map (fn r => (requireStartsLine r, showRequire root r)) requires
      , Seq.map (fn d => (topDecStartsLine d, showTopDec root d)) topdecs
      ))


  fun pretty {ribbonFrac, maxWidth, tabWidth, indent, debug} ast =
    let
      fun dbgprintln s =
        if not debug then () else print (s ^ "\n")
      val (doc, tm) = Util.getTime (fn _ => showAst ast)
      val _ = dbgprintln ("to-doc: " ^ Time.fmt 3 tm ^ "s")
    in
      TabbedTokenDoc.pretty
        { ribbonFrac = ribbonFrac
        , maxWidth = maxWidth
        , indentWidth = indent
        , tabWidth = tabWidth
        , debug = debug
        } doc
    end

end

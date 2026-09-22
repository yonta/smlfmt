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


  fun showTy tab ty : doc =
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
          let
            fun showElem tab (LabTy {lab, colon, ty}) =
              token lab ++ hugNext lab ++ token colon ++ showTy tab ty
          in
            showSequence (fn _ => false) (withNewChild showElem) tab
              {openn = left, elems = elems, delims = delims, close = right}
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


  fun showDec tab dec =
    let
      open SmiAst.Dec
    in
      case dec of
        Val {vall, vid, colon, ty} =>
          newTab tab (fn inner =>
            at inner
              (token vall ++ token vid ++ hugNext vid ++ token colon
               ++ withNewChild showTy inner ty))

      | Type {typee, elems, delims} =>
          newTab tab (fn inner =>
            let
              fun showOne (starter, tb) =
                at inner (token starter ++ showTypbind inner tb)
            in
              at inner
                (Seq.iterate op++
                   (token typee ++ showTypbind inner (Seq.nth elems 0))
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
      SmiAst.Require {underscore, directive, path} =>
        token underscore ++ nospace ++ token directive ++ token path
    | SmiAst.RequireSemicolon tok => nospace ++ token tok


  fun requireStartsLine (SmiAst.RequireSemicolon _) = false
    | requireStartsLine _ = true


  fun showAst (SmiAst.Interface {requires, topdecs}) =
    joinAt root (Seq.append
      ( Seq.map (fn r => (requireStartsLine r, showRequire root r)) requires
      , Seq.map (fn d => (strDecStartsLine d, showStrDec root d)) topdecs
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

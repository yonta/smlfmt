(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** AST for SML#'s `.smi` interface files.
  *
  * This is not SML '97's `spec`. The top level of a `.smi` is `idec`, which
  * reads like the body of a `struct` with no implementations: `type` carries a
  * runtime representation instead of standing alone, `structure` is a
  * definition rather than a constraint, and `val` cannot be chained with `and`.
  * Only tokens, `SyntaxSeq` and `MaybeLongToken` are shared with `Ast`.
  *
  * As in `Ast`, each token of the input appears exactly once, so traversing the
  * tree recovers the original token sequence.
  *)
structure SmiAst =
struct

  structure SyntaxSeq = Ast.SyntaxSeq


  (** ======================================================================
    * Types.
    *)
  structure Ty =
  struct
    datatype tyrow =
      LabTy of {lab: Token.t, colon: Token.t, ty: ty}

    (** The constraint on a quantified type variable, as in `'a#boxed` or
      * `'a#{fileId: int}`. Several may follow one variable.
      *)
    and kind =
      KindProp of {hash: Token.t, prop: Token.t}

    | KindRecord of
        { hash: Token.t
        , left: Token.t
        , elems: tyrow Seq.t
        , delims: Token.t Seq.t
        , right: Token.t
        }

    and ty =
      Var of Token.t

    (** { lab : ty, ..., lab : ty } *)
    | Record of
        { left: Token.t
        , elems: tyrow Seq.t
        , delims: Token.t Seq.t
        , right: Token.t
        }

    (** ty * ... * ty *)
    | Tuple of {elems: ty Seq.t, delims: Token.t Seq.t}

    (** tyseq longtycon *)
    | Con of {args: ty SyntaxSeq.t, id: MaybeLongToken.t}

    (** ty -> ty *)
    | Arrow of {from: ty, arrow: Token.t, to: ty}

    (** ( ty ) *)
    | Parens of {left: Token.t, ty: ty, right: Token.t}

    (** [ 'a #kind ..., 'b. ty ] -- SML#'s explicit polymorphism *)
    | Poly of
        { left: Token.t
        , elems: {tyvar: Token.t, kinds: kind Seq.t} Seq.t
        , delims: Token.t Seq.t
        , dot: Token.t
        , ty: ty
        , right: Token.t
        }

    type t = ty
  end


  (** ======================================================================
    * Core declarations.
    *)
  structure Dec =
  struct

    (** The runtime representation of an opaque type, as in `type cs (= int)`.
      * Written `*` for tuples, `->` for functions, `{}` for records, and a
      * type name otherwise.
      *)
    datatype impl =
      ImplTy of MaybeLongToken.t
    | ImplFunc of Token.t
    | ImplRecord of {left: Token.t, right: Token.t}

    datatype typbind =
    (** tyvarseq tycon = ty *)
      Transparent of
        {tyvars: Token.t SyntaxSeq.t, tycon: Token.t, eq: Token.t, ty: Ty.t}

    (** tyvarseq tycon (= impl) *)
    | Opaque of
        { tyvars: Token.t SyntaxSeq.t
        , tycon: Token.t
        , left: Token.t
        , eq: Token.t
        , impl: impl
        , right: Token.t
        }

    datatype dec =
    (** val vid : ty *)
      Val of {vall: Token.t, vid: Token.t, colon: Token.t, ty: Ty.t}

    (** type typbind [and typbind ...] *)
    | Type of {typee: Token.t, elems: typbind Seq.t, delims: Token.t Seq.t}
  end


  (** ======================================================================
    * Structures.
    *)
  structure Str =
  struct

    datatype strexp =
    (** struct strdec ... end *)
      Struct of {structt: Token.t, elems: strdec Seq.t, endd: Token.t}

    (** longstrid *)
    | Ident of MaybeLongToken.t

    (** funid ( longstrid ) *)
    | FunAppIdent of
        {funid: Token.t, left: Token.t, id: MaybeLongToken.t, right: Token.t}

    and strdec =
      Dec of Dec.dec

    (** structure strid = strexp *)
    | Structure of
        {structuree: Token.t, strid: Token.t, eq: Token.t, strexp: strexp}

    (** A bare `;` is derivable wherever a declaration is, so it needs a node
      * of its own; otherwise the token would vanish from the output.
      *)
    | Semicolon of Token.t
  end


  (** ======================================================================
    * Whole file.
    *)

  datatype require =
  (** _require "path" *)
    Require of {underscore: Token.t, directive: Token.t, path: Token.t}
  | RequireSemicolon of Token.t

  datatype ast =
  (** `_require` may only appear before the declarations, never between them. *)
    Interface of {requires: require Seq.t, topdecs: Str.strdec Seq.t}

  type t = ast

end

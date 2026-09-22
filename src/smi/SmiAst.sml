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

    (** The overload declaration, `val + = case 'a in ty of ty => inst | ...`.
      * It reuses `case`, `in` and `of` at the type level.
      *)
    datatype overload_inst =
      InstOverload of overload_exp
    | InstLongId of MaybeLongToken.t
    | InstParens of {left: Token.t, inst: overload_inst, right: Token.t}

    and overload_exp =
      OverloadExp of
        { casee: Token.t
        , tyvar: Token.t
        , inn: Token.t
        , ty: Ty.t
        , off: Token.t
        , elems: {ty: Ty.t, arrow: Token.t, inst: overload_inst} Seq.t
        , delims: Token.t Seq.t
        }

    (** Unlike SML '97, `val` in a .smi cannot be chained with `and`. *)
    datatype valbind =
    (** vid : ty *)
      ValTy of {vid: Token.t, colon: Token.t, ty: Ty.t}

    (** vid = longvid *)
    | ValAlias of {vid: Token.t, eq: Token.t, id: MaybeLongToken.t}

    (** vid = _builtin val vid : ty *)
    | ValBuiltin of
        { vid: Token.t
        , eq: Token.t
        , underscore: Token.t
        , builtin: Token.t
        , vall: Token.t
        , builtinVid: Token.t
        , colon: Token.t
        , ty: Ty.t
        }

    (** vid = case 'a in ty of ... *)
    | ValOverload of {vid: Token.t, eq: Token.t, exp: overload_exp}

    (** vid [of ty], with an optional `op` *)
    type conbind =
      {opp: Token.t option, vid: Token.t, arg: {off: Token.t, ty: Ty.t} option}

    type datbind =
      { tyvars: Token.t SyntaxSeq.t
      , tycon: Token.t
      , eq: Token.t
      , elems: conbind Seq.t
      , delims: Token.t Seq.t
      }

    datatype exbind =
      ExnNew of conbind

    (** vid = longvid -- exception replication, absent from SML '97 specs *)
    | ExnRep of
        {opp: Token.t option, vid: Token.t, eq: Token.t, id: MaybeLongToken.t}

    datatype dec =
    (** val valbind *)
      Val of {vall: Token.t, bind: valbind}

    (** type typbind [and typbind ...] *)
    | Type of {typee: Token.t, elems: typbind Seq.t, delims: Token.t Seq.t}

    (** eqtype typbind [and ...] -- always the opaque form *)
    | Eqtype of {eqtypee: Token.t, elems: typbind Seq.t, delims: Token.t Seq.t}

    (** datatype datbind [and ...] [withtype typbind [and ...]] *)
    | Datatype of
        { datatypee: Token.t
        , elems: datbind Seq.t
        , delims: Token.t Seq.t
        , withtypee:
            {withtypee: Token.t, elems: typbind Seq.t, delims: Token.t Seq.t} option
        }

    (** datatype tycon = datatype longtycon *)
    | DatatypeRep of
        { left_datatypee: Token.t
        , tycon: Token.t
        , eq: Token.t
        , right_datatypee: Token.t
        , id: MaybeLongToken.t
        }

    (** datatype tycon = _builtin datatype tycon *)
    | DatatypeBuiltin of
        { left_datatypee: Token.t
        , tycon: Token.t
        , eq: Token.t
        , underscore: Token.t
        , builtin: Token.t
        , right_datatypee: Token.t
        , builtinTycon: Token.t
        }

    (** exception exbind [and ...] *)
    | Exception of
        {exceptionn: Token.t, elems: exbind Seq.t, delims: Token.t Seq.t}
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

  datatype topdec =
    TopStrDec of Str.strdec

  (** infix [prec] vid ... -- only at top level, never inside a struct.
    * `nonfix` has a rule in interface.grm but interface.lex never produces the
    * token, so it is unreachable and not represented here.
    *)
  | TopInfix of
      {infixx: Token.t, precedence: Token.t option, elems: Token.t Seq.t}

  datatype require =
  (** _require ["local"] "path" [option ...] *)
    Require of
      { underscore: Token.t
      , directive: Token.t
      , locall: Token.t option
      , path: Token.t
      , options: Token.t Seq.t
      }

  (** _use local "path" -- the bare `_use` of .sml is not allowed here *)
  | Use of
      {underscore: Token.t, directive: Token.t, locall: Token.t, path: Token.t}

  | RequireSemicolon of Token.t

  datatype ast =
  (** `_require` may only appear before the declarations, never between them. *)
    Interface of {requires: require Seq.t, topdecs: topdec Seq.t}

  type t = ast

end

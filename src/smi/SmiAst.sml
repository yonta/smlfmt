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
    * Signatures.
    *
    * These appear only inside `sig ... end` and as a functor parameter, and
    * they are SML '97's `spec`, not the `idec` of the top level. The one
    * difference is that a `val` here may also take a poly type.
    *)
  structure Sig =
  struct

    (** vid [of ty] -- no `op`, unlike a top-level datbind *)
    type condesc = {vid: Token.t, arg: {off: Token.t, ty: Ty.t} option}

    type typdesc = {tyvars: Token.t SyntaxSeq.t, tycon: Token.t}

    datatype spec =
      SpecEmpty

    (** val vid : ty [and ...] *)
    | Val of
        { vall: Token.t
        , elems: {vid: Token.t, colon: Token.t, ty: Ty.t} Seq.t
        , delims: Token.t Seq.t
        }

    (** type tyvarseq tycon [and ...] *)
    | Type of {typee: Token.t, elems: typdesc Seq.t, delims: Token.t Seq.t}

    (** type tyvarseq tycon = ty [and ...] -- a derived form *)
    | TypeAlias of
        { typee: Token.t
        , elems:
            {tyvars: Token.t SyntaxSeq.t, tycon: Token.t, eq: Token.t, ty: Ty.t} Seq.t
        , delims: Token.t Seq.t
        }

    (** eqtype tyvarseq tycon [and ...] *)
    | Eqtype of {eqtypee: Token.t, elems: typdesc Seq.t, delims: Token.t Seq.t}

    (** datatype tyvarseq tycon = condesc [| ...] [and ...] *)
    | Datatype of
        { datatypee: Token.t
        , elems:
            { tyvars: Token.t SyntaxSeq.t
            , tycon: Token.t
            , eq: Token.t
            , elems: condesc Seq.t
            , delims: Token.t Seq.t
            } Seq.t
        , delims: Token.t Seq.t
        }

    (** datatype tycon = datatype longtycon *)
    | ReplicateDatatype of
        { left_datatypee: Token.t
        , tycon: Token.t
        , eq: Token.t
        , right_datatypee: Token.t
        , id: MaybeLongToken.t
        }

    (** exception condesc [and ...] *)
    | Exception of
        {exceptionn: Token.t, elems: condesc Seq.t, delims: Token.t Seq.t}

    (** structure strid : sigexp [and ...] *)
    | Structure of
        { structuree: Token.t
        , elems: {strid: Token.t, colon: Token.t, sigexp: sigexp} Seq.t
        , delims: Token.t Seq.t
        }

    | Include of {includee: Token.t, sigexp: sigexp}

    (** include sigid sigid [...] -- a derived form, two or more ids *)
    | IncludeIds of {includee: Token.t, sigids: Token.t Seq.t}

    | SharingType of
        { spec: spec
        , sharingg: Token.t
        , typee: Token.t
        , elems: MaybeLongToken.t Seq.t
        , delims: Token.t Seq.t
        }

    | Sharing of
        { spec: spec
        , sharingg: Token.t
        , elems: MaybeLongToken.t Seq.t
        , delims: Token.t Seq.t
        }

    (** a run of specs, with optional semicolons between them *)
    | Multiple of {elems: spec Seq.t, delims: Token.t option Seq.t}

    and sigexp =
      Ident of Token.t

    | Spec of {sigg: Token.t, spec: spec, endd: Token.t}

    (** sigexp where type ... [and type ...] *)
    | WhereType of
        { sigexp: sigexp
        , elems:
            { wheree: Token.t
            , typee: Token.t
            , tyvars: Token.t SyntaxSeq.t
            , tycon: MaybeLongToken.t
            , eq: Token.t
            , ty: Ty.t
            } Seq.t
        }

    (** signature sigid = sigexp [and ...] -- only in an INCLUDES file *)
    datatype sigdec =
      Signature of
        { signaturee: Token.t
        , elems: {ident: Token.t, eq: Token.t, sigexp: sigexp} Seq.t
        , delims: Token.t Seq.t
        }
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
    * Functors.
    *)
  structure Fun =
  struct

    datatype funarg =
      ArgIdent of {strid: Token.t, colon: Token.t, sigexp: Sig.sigexp}

    (** a spec written directly in the parameter position -- a derived form *)
    | ArgSpec of Sig.spec

    (** functor funid ( funarg ) = strexp
      *
      * The .smi form takes neither a result signature nor `and` chaining; the
      * body itself is the interface the functor provides.
      *)
    datatype fundec =
      Functor of
        { functorr: Token.t
        , funid: Token.t
        , lparen: Token.t
        , funarg: funarg
        , rparen: Token.t
        , eq: Token.t
        , strexp: Str.strexp
        }
  end


  (** ======================================================================
    * Whole file.
    *)

  datatype topdec =
    TopStrDec of Str.strdec

  | TopFunDec of Fun.fundec

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

  (** include "path" -- takes a path, unlike the `include sigexp` of a spec *)
  datatype include_path =
    IncludePath of {includee: Token.t, path: Token.t}

  datatype sigdec_item = SigDec of Sig.sigdec | SigSemicolon of Token.t

  (** A .smi takes one of two exclusive shapes, decided by its first token:
    * `include` or `signature` open the INCLUDES form, anything else (including
    * nothing at all) the INTERFACE form. `_require` and `signature` therefore
    * cannot appear in the same file.
    *)
  datatype ast =
  (** `_require` may only appear before the declarations, never between them. *)
    Interface of {requires: require Seq.t, topdecs: topdec Seq.t}

  | Includes of {includes: include_path Seq.t, sigdecs: sigdec_item Seq.t}

  type t = ast

end

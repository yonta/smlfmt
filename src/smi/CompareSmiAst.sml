(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure CompareSmiAst:
sig
  val equal: {tabWidth: int} -> SmiAst.t * SmiAst.t -> bool
end =
struct

  (* Same combinators as CompareAst, for the same record idiom:
   *
   *   val checker =
   *     at #field1 eq1 <&>
   *     ...           <&>
   *     at #fieldN eqN
   *)

  type 'a eq = 'a * 'a -> bool

  fun at (select: 'b -> 'a) (eq: 'a eq) : 'b eq =
    fn (x: 'b, y: 'b) => eq (select x, select y)

  fun <&> (eq1: 'a eq, eq2: 'a eq) : 'a eq =
    fn (x, y) => eq1 (x, y) andalso eq2 (x, y)

  infix 2 <&>

  (* ======================================================================= *)

  open SmiAst


  fun equal {tabWidth: int} (Interface i1, Interface i2) =
    let

      fun equal_tok (t1, t2) =
        Token.sameExceptForMultilineIndentation {tabWidth = tabWidth} (t1, t2)


      fun equal_longtok (t1, t2) =
        equal_tok (MaybeLongToken.getToken t1, MaybeLongToken.getToken t2)


      fun equal_syntaxseq eq (s1, s2) =
        case (s1, s2) of
          (SyntaxSeq.Empty, SyntaxSeq.Empty) => true
        | (SyntaxSeq.One x, SyntaxSeq.One y) => eq (x, y)
        | (SyntaxSeq.Many x, SyntaxSeq.Many y) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal eq)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (x, y)
            end
        | _ => false


      fun equal_tyrow (Ty.LabTy lt1, Ty.LabTy lt2) =
        let
          val checker =
            at #lab equal_tok <&> at #colon equal_tok <&> at #ty equal_ty
        in
          checker (lt1, lt2)
        end


      and equal_ty (t1, t2) =
        case (t1, t2) of
          (Ty.Var v1, Ty.Var v2) => equal_tok (v1, v2)

        | (Ty.Record r1, Ty.Record r2) =>
            let
              val checker =
                at #left equal_tok <&> at #right equal_tok
                <&> at #delims (Seq.equal equal_tok)
                <&> at #elems (Seq.equal equal_tyrow)
            in
              checker (r1, r2)
            end

        | (Ty.Tuple t1, Ty.Tuple t2) =>
            let
              val checker =
                at #elems (Seq.equal equal_ty)
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (t1, t2)
            end

        | (Ty.Con c1, Ty.Con c2) =>
            let
              val checker =
                at #args (equal_syntaxseq equal_ty) <&> at #id equal_longtok
            in
              checker (c1, c2)
            end

        | (Ty.Arrow a1, Ty.Arrow a2) =>
            let
              val checker =
                at #from equal_ty <&> at #arrow equal_tok <&> at #to equal_ty
            in
              checker (a1, a2)
            end

        | (Ty.Parens p1, Ty.Parens p2) =>
            let
              val checker =
                at #left equal_tok <&> at #ty equal_ty <&> at #right equal_tok
            in
              checker (p1, p2)
            end

        | _ => false


      fun equal_impl (i1, i2) =
        case (i1, i2) of
          (Dec.ImplTy t1, Dec.ImplTy t2) => equal_longtok (t1, t2)

        | (Dec.ImplFunc t1, Dec.ImplFunc t2) => equal_tok (t1, t2)

        | (Dec.ImplRecord r1, Dec.ImplRecord r2) =>
            let val checker = at #left equal_tok <&> at #right equal_tok
            in checker (r1, r2)
            end

        | _ => false


      fun equal_typbind (b1, b2) =
        case (b1, b2) of
          (Dec.Transparent t1, Dec.Transparent t2) =>
            let
              val checker =
                at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
                <&> at #eq equal_tok <&> at #ty equal_ty
            in
              checker (t1, t2)
            end

        | (Dec.Opaque o1, Dec.Opaque o2) =>
            let
              val checker =
                at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
                <&> at #left equal_tok <&> at #eq equal_tok
                <&> at #impl equal_impl <&> at #right equal_tok
            in
              checker (o1, o2)
            end

        | _ => false


      fun equal_dec (d1, d2) =
        case (d1, d2) of
          (Dec.Val v1, Dec.Val v2) =>
            let
              val checker =
                at #vall equal_tok <&> at #vid equal_tok <&> at #colon equal_tok
                <&> at #ty equal_ty
            in
              checker (v1, v2)
            end

        | (Dec.Type t1, Dec.Type t2) =>
            let
              val checker =
                at #typee equal_tok <&> at #elems (Seq.equal equal_typbind)
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (t1, t2)
            end

        | _ => false


      fun equal_strexp (e1, e2) =
        case (e1, e2) of
          (Str.Ident i1, Str.Ident i2) => equal_longtok (i1, i2)

        | (Str.Struct s1, Str.Struct s2) =>
            let
              val checker =
                at #structt equal_tok <&> at #elems (Seq.equal equal_strdec)
                <&> at #endd equal_tok
            in
              checker (s1, s2)
            end

        | (Str.FunAppIdent f1, Str.FunAppIdent f2) =>
            let
              val checker =
                at #funid equal_tok <&> at #left equal_tok
                <&> at #id equal_longtok <&> at #right equal_tok
            in
              checker (f1, f2)
            end

        | _ => false


      and equal_strdec (d1, d2) =
        case (d1, d2) of
          (Str.Dec d1, Str.Dec d2) => equal_dec (d1, d2)

        | (Str.Semicolon s1, Str.Semicolon s2) => equal_tok (s1, s2)

        | (Str.Structure s1, Str.Structure s2) =>
            let
              val checker =
                at #structuree equal_tok <&> at #strid equal_tok
                <&> at #eq equal_tok <&> at #strexp equal_strexp
            in
              checker (s1, s2)
            end

        | _ => false


      fun equal_require (r1, r2) =
        case (r1, r2) of
          (Require q1, Require q2) =>
            let
              val checker =
                at #underscore equal_tok <&> at #directive equal_tok
                <&> at #path equal_tok
            in
              checker (q1, q2)
            end

        | (RequireSemicolon s1, RequireSemicolon s2) => equal_tok (s1, s2)

        | _ => false


      val checker =
        at #requires (Seq.equal equal_require)
        <&> at #topdecs (Seq.equal equal_strdec)
    in
      checker (i1, i2)
    end

end

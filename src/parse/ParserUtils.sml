(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParserUtils:
sig
  val error: {pos: Source.t, what: string, explain: string option} -> 'a
  val tokError: Token.t Seq.t
                -> {pos: int, what: string, explain: string option}
                -> 'a

  val errorIfInfixNotOpped: InfixDict.t -> Token.t option -> Token.t -> unit

  val checkOptBar: AstAllows.t -> Token.t option -> string -> unit

  (** Given the token just after an underscore: does `_<tok>` begin a
    * structure-level declaration? MLton's `_prim` and friends are
    * expressions, so they answer false here.
    *)
  val isUnderscoreStrDec: AstAllows.t -> Token.t -> bool

  val nyi: Token.t Seq.t -> string -> int -> 'a
end =
struct

  fun error {what, pos, explain} =
    raise Error.Error
      (Error.lineError
         {header = "PARSE ERROR", pos = pos, what = what, explain = explain})

  fun tokError toks {what, pos, explain} =
    if pos >= Seq.length toks then
      let
        val wholeSrc = Source.wholeFile (Token.getSource (Seq.nth toks 0))
        val src = Source.drop wholeSrc (Source.length wholeSrc - 1)
      in
        error {pos = src, what = "Unexpected end of file.", explain = NONE}
      end
    else
      error
        { pos = Token.getSource (Seq.nth toks pos)
        , what = what
        , explain = explain
        }

  fun isUnderscoreStrDec allows tok =
    Token.isIdentifier tok
    andalso
    case Source.toString (Token.getSource tok) of
      "overload" => true
    | "use" => AstAllows.smlSharp allows
    | "interface" => AstAllows.smlSharp allows
    | _ => false


  fun errorIfInfixNotOpped infdict opp vid =
    if InfixDict.isInfix infdict vid andalso not (Option.isSome opp) then
      error
        { pos = Token.getSource vid
        , what = "Infix identifier not prefaced by 'op'"
        , explain = NONE
        }
    else
      ()


  fun nyi toks fname i =
    if i >= Seq.length toks then
      raise Error.Error
        (Error.lineError
           { header = "ERROR: NOT YET IMPLEMENTED"
           , pos = Token.getSource (Seq.nth toks (Seq.length toks - 1))
           , what = "Unexpected EOF after token."
           , explain = SOME ("(TODO: see parser " ^ fname ^ ")")
           })
    else if i >= 0 then
      raise Error.Error
        (Error.lineError
           { header = "ERROR: NOT YET IMPLEMENTED"
           , pos = Token.getSource (Seq.nth toks i)
           , what = "Unexpected token."
           , explain = SOME ("(TODO: see parser " ^ fname ^ ")")
           })
    else
      raise Fail ("Bug in parser " ^ fname ^ ": position out of bounds??")


  fun checkOptBar allows optbar msg =
    case optbar of
      NONE => ()
    | SOME bar =>
        if AstAllows.optBar allows then
          ()
        else
          error
            { pos = Token.getSource bar
            , what = msg
            , explain = SOME
                "This is disallowed in Standard ML, but allowed in \
                \SuccessorML with \"optional bar\" syntax. To enable \
                \optional bar syntax, use the command-line argument \
                \'-allow-opt-bar true'."
            }


end

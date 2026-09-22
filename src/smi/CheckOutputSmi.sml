(** Copyright (c) 2020 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(* CheckOutput, for `.smi`. The three things that differ are the lexer, the
 * parser, and the AST comparison; the surrounding checks are the same.
 *)
structure CheckOutputSmi:
sig
  val check:
    { origLexerOutput: Token.t Seq.t
    , origParserOutput: ParseSmi.parser_output
    , origFormattedOutput: string
    , formatter: ParseSmi.parser_output -> string
    , tabWidth: int
    }
    -> CheckOutput.result
end =
struct

  val removeWhitespaceTokens = Seq.filter (not o Token.isWhitespace)


  fun checkTokenSeqs {tabWidth: int} (ts1, ts2) =
    Seq.equal (Token.sameExceptForMultilineIndentation {tabWidth = tabWidth})
      (removeWhitespaceTokens ts1, removeWhitespaceTokens ts2)


  fun checkParserOutputs {tabWidth: int} (po1, po2) =
    case (po1, po2) of
      (ParseSmi.JustComments cs1, ParseSmi.JustComments cs2) =>
        checkTokenSeqs {tabWidth = tabWidth} (cs1, cs2)
    | (ParseSmi.Ast ast1, ParseSmi.Ast ast2) =>
        CompareSmiAst.equal {tabWidth = tabWidth} (ast1, ast2)
    | _ => false


  fun check
    { origLexerOutput
    , origParserOutput
    , origFormattedOutput
    , formatter
    , tabWidth
    } =
    let
      val mockedSource = Source.make
        { fileName = FilePath.fromFields ["<output>"]
        , contents =
            Seq.tabulate (fn i => String.sub (origFormattedOutput, i))
              (String.size origFormattedOutput)
        }

      val newLexerOutput = SOME (Lexer.tokensSmi mockedSource) handle _ => NONE

      val newParserOutput =
        case newLexerOutput of
          NONE => NONE
        | SOME lexOut => SOME (ParseSmi.parse lexOut) handle _ => NONE

      val newFormattedOutput = Option.map formatter newParserOutput

      (* ================================================================= *)

      val tokensOkay =
        case newLexerOutput of
          NONE => false
        | SOME x => checkTokenSeqs {tabWidth = tabWidth} (origLexerOutput, x)

      val reparseOkay =
        case newParserOutput of
          NONE => false
        | SOME x =>
            checkParserOutputs {tabWidth = tabWidth} (origParserOutput, x)

      val reformatOkay =
        case newFormattedOutput of
          NONE => false
        | SOME x => origFormattedOutput = x
    in
      if not tokensOkay then
        CheckOutput.Error {description = "tokens mangled"}
      else if not reparseOkay then
        CheckOutput.Error {description = "unexpected parse failure"}
      else if not reformatOkay then
        CheckOutput.NonIdempotentFormatting
      else
        CheckOutput.AllGood
    end
    handle exn =>
      CheckOutput.Error
        {description = "unexpected exception: " ^ exnMessage exn}

end

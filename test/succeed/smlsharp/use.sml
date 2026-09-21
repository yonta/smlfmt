(* `_use` loads another file and is interleaved with declarations. SML# only
 * accepts it in an interactive session, so this file has to be checked with
 * `smlsharp < use.sml` rather than `smlsharp -c`. *)
_use "basic.sml"

val a = 1

_use "record-update.sml"

val b = a + 1

(* Flexible record types. SML# rejects them in a `type` declaration
 * ("partial record type not allowed in type declaration"), so they only ever
 * show up as type annotations. *)
val f: {x: int, ...} -> int = fn {x, ...} => x
val g: {...} -> unit = fn _ => ()
val h: {name: string, ...} -> string = fn {name, ...} => name

fun sumXY (r: {x: int, y: int, ...}) = #x r + #y r

val
  long:
    { aLongFieldName: int
    , anotherLongFieldName: string
    , yetAnotherLongFieldName: real
    , ...
    }
    -> int = fn r => #aLongFieldName r

(* wildcard types *)
val i: _ = 1
val j: int -> _ = fn x => x
val k = (1, 2) : _ * _

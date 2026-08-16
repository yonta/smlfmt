(* basic record *)
type point = {x: int, y: int}
val p: point = {x = 0, y = 1}
val {x = px, y = py} = p
fun f {x, y} = (x, y)
fun getX (p: point) = #x p

(* flex record allowed in SML# *)
fun getX p = #x p
fun getX {x, ...} = x

(* SQL words that SML# reserves, used here as ordinary identifiers. *)
val asc = 1
val all = 1
val begin = 1
val by = 1
val commit = 1
val cross = 1
val default = 1
val delete = 1
val desc = 1
val distinct = 1
val fetch = 1
val first = 1
val from = 1
val group = 1
val having = 1
val inner = 1
val insert = 1
val into = 1
val is = 1
val join = 1
val limit = 1
val natural = 1
val next = 1
val not = 1
val null = 1
val offset = 1
val only = 1
val on = 1
val or = 1
val order = 1
val outer = 1 (* not supported sql in SML# *)
val rollback = 1
val row = 1
val rows = 1
val select = 1
val set = 1
val update = 1
val values = 1
(* val where = 1 *) (* SML reserved word *)

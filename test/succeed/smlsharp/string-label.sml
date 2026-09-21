val a = {"foo" = 1, "bar baz" = 2}
val b = #"foo" a
val {"foo" = x, ...} = a
val c: {"foo": int, ...} = a
val d = a # {"foo" = 3}

(* `#"c"` is still a char constant when the contents are one character long,
 * which is how SML# itself resolves the ambiguity. *)
val ch: char = #"a"
val nl: char = #"\n"

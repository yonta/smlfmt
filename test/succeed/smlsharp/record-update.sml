type person = {name: string, age: int}

val p: person = {name = "a", age = 1}

(* update by row *)
val q = p # {age = 2}
val r = p # {name = "b", age = 3}

(* empty update *)
val s = p # {}

(* update by a whole record *)
val t = p # {q}
val u = p # {{name = "c"}}

(* chained *)
val v = p # {age = 4} # {name = "d"}

(* tuple label update *)
val w = (1, 2) # (10, 20)
val x = (1, 2, 3) # (10, 20, 30)

(* inside an application *)
fun bump r =
  r # {age = #age r + 1}

val aVeryLongRecordExpressionName =
  {aLongFieldName = 0, anotherLongFieldName = 0, yetAnotherFieldName = 0}
val long =
  aVeryLongRecordExpressionName
    # {aLongFieldName = 1, anotherLongFieldName = 2, yetAnotherFieldName = 3}

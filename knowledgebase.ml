let kb = [
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
Equals (Var "Ry", Var "Arman");
Equals (Var "Parker", Var "Arman")
] in
let alpha = Not (Equals (Var "Ry", Var "Parker")) in
resolution alpha kb

let rec printKB kb =
    match kb with
    | [] -> ""
    | h::t -> (stmtToString h) ^ "\n" ^ (printKB t)
printKB kb

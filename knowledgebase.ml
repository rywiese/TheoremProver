let kb = [
True;
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
Equals (Const (Name "Ry"), Const (Name "Arman"));
Equals (Const (Name "Arman"), Const (Name "Parker"))
] in
let alpha = (Equals (Const (Name "Ry"), Const (Name "Parker")))  in
resolutionProof alpha kb

let s1 = ForAll("x", Equals(Var "x", Var "x")) in
let s2 = (Equals (Const (Name "Ry"), Const (Name "Ry"))) in
getResolvents (splitKB (cnf(Not s1)::[s2]))

let s1 = Not (Equals (Const (Skol ("x", [])), Const (Skol ("x", [])))) in
let s2 = Equals (Const (Name "Ry"), Const (Name "Ry")) in
resolve s1 s2

resolve (Not(Equals (Const (Skol ("x", [])), Const (Skol ("x", []))))) (Equals (Const (Name "Ry"), Const (Name "Ry")))
resolveLit (Not(Equals (Const (Skol ("x", [])), Const (Skol ("x", []))))) (Or ((LessThan (Const (Int 3),(Const (Int 4)))), (Or (False, (LessThan (Const (Int 1), Const (Int 2)))))))

let rec printKB kb =
    match kb with
    | [] -> ""
    | h::t -> (stmtToString h) ^ "\n" ^ (printKB t)
printKB kb

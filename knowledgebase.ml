let kb = [
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
Equals (Const (Name "Ry"), Const (Name "Arman"));
Equals (Const (Name "Arman"), Const (Name "Parker"))
] in
let alpha = (Equals (Const (Name "Ry"), Const (Name "Parker")))  in
resolutionProof alpha kb

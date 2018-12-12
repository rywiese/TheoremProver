let kb = [
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
Equals (Const (Name "Ry"), Const (Name "Arman"));
Equals (Const (Name "Arman"), Const (Name "Parker"))
] in
let alpha = ForAll ("x", Implies ((Equals (Var "x", Const (Name "Parker"))), (Equals (Var "x", Const (Name "Ry"))))) in
(unwindResProof alpha kb)
(resolutionProof alpha kb)

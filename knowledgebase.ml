let kb = [
(*  Axioms of equality  *)
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
(*  Axioms of less than *)
ForAll("x", Not (LessThan (Var "x", Var "x")));
ForAll("x", ForAll("y", Implies ((LessThan(Var "x", Var "y")),(Not (LessThan (Var "y", Var "x"))))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (LessThan (Var "x", Var "y"), LessThan (Var "y", Var "z")), LessThan (Var "x", Var "z")))));
ForAll("x", LessThan(Var "x", Plus(Var "x", Const(Int 1))));
(*  Other things that we are deciding to be true    *)
Equals((Const (Name "Ry")),(Const (Name "Arman")));
Equals((Const (Name "Parker")),(Const (Name "Arman")));
] in
let alphas = [
Equals((Const (Name "Parker")),(Const (Name "Arman")));
Exists ("x", Equals (Var "x", Const (Name "Arman")));
(ForAll ("x", (Implies ((Equals(Const (Name "Parker"), Var "x"), (Equals((Var "x"),(Const (Name "Ry")))))))));
] in
batchProve alphas kb

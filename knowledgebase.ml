let kb = [
(*  Axioms of equality  *)
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
ForAll("x", Equals(Const (Int 0), Times (Const (Int 0),Var "x")));
(*  Axioms of less than *)
ForAll("x", Not (LessThan (Var "x", Var "x")));
ForAll("x", ForAll("y", Implies ((LessThan(Var "x", Var "y")),(Not (LessThan (Var "y", Var "x"))))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (LessThan (Var "x", Var "y"), LessThan (Var "y", Var "z")), LessThan (Var "x", Var "z")))));
ForAll("x", Or ((LessThan (Const (Int 0), Var "x")),(Equals (Const (Int 0), Var "x"))));
ForAll("x", LessThan(Var "x", Plus(Var "x", Const(Int 1))));
ForAll("x", LessThan(Var "x", Times(Var "x", Var "x")));
ForAll("x", Exists ("y", LessThan (Var "x", Var "y")));
(*  Other things that we are deciding to be true    *)
Equals((Const (Name "Ry")),(Const (Name "Arman")));
Equals((Const (Name "Parker")),(Const (Name "Arman")));
ForAll("x", LessThan (Var "x", Const (Name "Ry")));
] in
let alphas = [
Equals((Const (Name "Parker")),(Const (Name "Arman")));
Exists ("x", Equals (Var "x", Const (Name "Arman")));
(ForAll ("x", (Implies ((Equals(Const (Name "Parker"), Var "x"), (Equals((Var "x"),(Const (Name "Ry")))))))));
Not (LessThan ((Const (Name "Ry")),(Const (Name "Arman"))));
ForAll ("x", ForAll ("y", Exists ("z", LessThan (Plus (Var "x", Var "y"),(Var "z")))));
ForAll ("x", Exists ("y", Equals (Var "x", Var "y")));
ForAll ("x", Exists ("y", LessThan (Times (Var "x", Var "x"),Var "y")));
(* Exists ("x", Equals (Var "x", Times (Var "x", Var "x"))); THIS NEVER TERMINATES *)
ForAll ("x", LessThan (Times (Var "x", Var "x"), Times (Times (Var "x",Var "x"),Var "x")));
LessThan (Times (Const (Name "Arman"), (Const (Name "Arman"))), Times (Const (Name "Ry"), (Const (Name "Ry"))));
LessThan (Times (Const (Name "Arman"), (Const (Name "Parker"))), Times (Const (Name "Ry"), (Const (Name "Parker"))));
ForAll ("x", ForAll ("y", Exists ("z", Equals (Var "z", Plus (Var "x", Var "y")))));
Exists ("x", ForAll ("y", Or (LessThan (Var "x",Var "y"), Equals (Var "x",Var "y"))));
ForAll ("x", Exists ("y", LessThan(Times (Var "x",Plus (Const (Int 1), Const (Int 1))),Var "y")));
Not (Exists ("x", ForAll ("y", (LessThan (Var "y", Var "x")))));
Not (ForAll ("x", (LessThan (Var "x", Times (Var "x", Var "x")))));
] in
batchProve alphas kb

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
let alpha1 = Equals((Const (Name "Parker")),(Const (Name "Arman"))) in
let alpha2 = Exists ("x", Equals (Var "x", Const (Name "Arman"))) in
let alpha3 = (ForAll ("x", (Implies ((Equals(Const (Name "Parker"), Var "x"), (Equals((Var "x"),(Const (Name "Ry"))))))))) in
let alpha4 = Not (LessThan ((Const (Name "Ry")),(Const (Name "Arman")))) in
let alpha5 = ForAll ("x", ForAll ("y", Exists ("z", LessThan (Plus (Var "x", Var "y"),(Var "z"))))) in
let alpha6 = ForAll ("x", Exists ("y", Equals (Var "x", Var "y"))) in
let alpha7 = ForAll ("x", Exists ("y", LessThan (Times (Var "x", Var "x"),Var "y"))) in
(* Exists ("x", Equals (Var "x", Times (Var "x", Var "x"))); THIS NEVER TERMINATES *)
let alpha8 = ForAll ("x", LessThan (Times (Var "x", Var "x"), Times (Times (Var "x",Var "x"),Var "x"))) in
let alpha9 = LessThan (Times (Const (Name "Arman"), (Const (Name "Arman"))), Times (Const (Name "Ry"), (Const (Name "Ry")))) in
let alpha10 = LessThan (Times (Const (Name "Arman"), (Const (Name "Parker"))), Times (Const (Name "Ry"), (Const (Name "Parker")))) in
let alpha11 = ForAll ("x", ForAll ("y", Exists ("z", Equals (Var "z", Plus (Var "x", Var "y"))))) in
let alpha12 = Exists ("x", ForAll ("y", Or (LessThan (Var "x",Var "y"), Equals (Var "x",Var "y")))) in
let alpha13 = ForAll ("x", Exists ("y", LessThan(Times (Var "x",Plus (Const (Int 1), Const (Int 1))),Var "y"))) in
let alpha14 = Not (Exists ("x", ForAll ("y", (LessThan (Var "y", Var "x"))))) in
let alpha15 = Not (ForAll ("x", (LessThan (Var "x", Times (Var "x", Var "x"))))) in

proveResolution alpha1 kb

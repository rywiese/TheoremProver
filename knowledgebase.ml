let kb = [
(Implies (Equals (Var "x", Var "y"), Equals (Var "f(x)", Var "f(y)")));
(ForAll ("x", Implies (ForAll ("y", Implies (Equals (Times (Const (Int 2), Var "y"), Const (Int 1)), Equals (Plus (Var "x", Var "y"), Const (Int 1)))), Exists ("y", Equals (Plus (Var "y", Var "x"), Const (Int 1))))));
(Not (ForAll ("x", Not (Or (Equals (Var "x", Var "y"), Equals (Var "x", Var "y"))))));
(Not (ForAll ("x", Equals (Var "x", Var "y"))));
(ForAll ("epsilon", Exists ("K", ForAll ("j", Implies (LessThan (Var "K", Var "j"), LessThan (Var "a_j", Var "epsilon"))))));
]
in splitKB kb

(*      x + 4 * y + 7 * 3       *)
(Plus (Plus (Var "x", Times (Const (Int 4), Var "y")), Times (Const (Int 7), Const (Int 3))))

(*      (x = y) => (f(x) = f(y))        *)
(Implies (Equals (Var "x", Var "y"), Equals (Var "f(x)", Var "f(y)")))

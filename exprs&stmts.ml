(*      x + 4 * y + 7 * 3       *)
(Plus (Plus (Var "x", Times (Const (Int 4), Var "y")), Times (Const (Int 7), Const (Int 3))))

(*      (x = y) => (f(x) = f(y))        *)
(Implies (Equals (Var "x", Var "y"), Equals (Var "f(x)", Var "f(y)")))

(*      For all x, [For all y, (2y = 1) => (x+y = 1)] => [There exists y st (y+x = 1)]         *)
let s = (ForAll ("x", Implies (ForAll ("y", Implies (Equals (Times (Const (Int 2), Var "y"), Const (Int 1)), Equals (Plus (Var "x", Var "y"), Const (Int 1)))), Exists ("y", Equals (Plus (Var
    "y", Var "x"), Const (Int 1)))))) in stmtToString (cnf s)

let s = Not (ForAll ("x", Not (Or (Equals (Var "x", Var "y"), Equals (Var "x", Var "y"))))) in fvStmt s

let s = Not (ForAll ("x", Equals (Var "x", Var "y"))) in stmtToString (cnf s)

(*      x + 4 * y + 7 * 3       *)
(Plus (Plus (Var "x", Times (Const (Int 4), Var "y")), Times (Const (Int 7), Const (Int 3))))

(*      (x = y) => (f(x) = f(y))        *)
let s = (Implies (Equals (Var "x", Var "y"), Equals (Var "f(x)", Var "f(y)"))) in standardize s dv

(*      For all x, [For all y, (2y = 1) => (x+y = 1)] => [There exists y st (y+x = 1)]         *)
let s = (ForAll ("x", Implies (ForAll ("y", Implies (Equals (Times (Const (Int 2), Var "y"), Const (Int 1)), Equals (Plus (Var "x", Var "y"), Const (Int 1)))), Exists ("y", Equals (Plus (Var
    "y", Var "x"), Const (Int 1)))))) in splittyboi (split (cnf s))

let s = Not (ForAll ("x", Not (Or (Equals (Var "x", Var "y"), Equals (Var "x", Var "y"))))) in fvStmt s

let s = Not (ForAll ("x", Equals (Var "x", Var "y"))) in stmtToString (cnf s)

(*      For all epsilon, there exists K st for all j, [K<j] => [a_j < epsilon]      *)
let s = ForAll ("epsilon", Exists ("K", ForAll ("j", Implies (LessThan (Var "K", Var "j"), LessThan (Var "a_j", Var "epsilon"))))) in stmtToString (cnf s)

let s1 = Plus(Var "x", Const (Int 7)) in let s2 = Plus(Const (Int 3), Var "y") in unify s1 s2 (Subst [])

let s1 = ForAll ("x", Equals (Plus(Var "x", Const (Int 7)),Plus(Var "x", Const (Int 7)))) in
let s2 = ForAll ("y", Equals (Plus(Const (Int 3), Var "y"),Plus(Const (Int 3), Var "y"))) in
unifyStmt s1 s2


unifyVar (Var "x") (Const (Int 3)) (Subst [])

getSub (Const (Int 3)) (Subst [])

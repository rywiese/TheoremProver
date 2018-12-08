(* Set operations *)
let rec isIn e l =
    match l with
    | [] -> false
    | h::t -> if e=h then true else isIn e t
let rec remove e l =
    match l with
    | [] -> []
    | h::t ->
        if e=h then remove e t else h::(remove e t)
let rec concat l1 l2 =
    match l1 with
    | [] -> l2
    | h::t -> h::(concat t l2)
let rec intersection l1 l2 =
    match l1 with
    | [] -> []
    | h::t ->
        if isIn h l2 then h::(intersection t l2)
        else intersection t l2
let rec union l1 l2 =
    match l1 with
    | [] -> l2
    | h::t -> h::(union t (remove h l2))
let rec difference l1 l2 =
    match l2 with
    | [] -> l1
    | h::t -> difference (remove h l1) t

(* Statement grammar *)
type const = Int of int | Name of string | Skol of string * string list
type expr =
    | Const of const
    | Var of string
    | Plus of expr * expr
    | Times of expr * expr
type stmt =
    | True
    | False
    | ForAll of string * stmt
    | Exists of string * stmt
    | Implies of stmt * stmt
    | And of stmt * stmt
    | Or of stmt * stmt
    | Not of stmt
    | Equals of expr * expr
    | LessThan of expr * expr
type subst = Failure | Subst of (expr * expr) list

(* getting variables functions *)
let dummyVars = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"]
let rec fvExpr e =
    match e with
    | Const c -> []
    | Var v -> [v]
    | Plus (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | Times (e1, e2) -> union (fvExpr e1) (fvExpr e2)
let rec fvStmt s =
    match s with
    | ForAll (v, s') -> difference (fvStmt s') [v]
    | Exists (v, s') -> difference (fvStmt s') [v]
    | Implies (s1, s2) -> union (fvStmt s1) (fvStmt s2)
    | And (s1, s2) -> union (fvStmt s1) (fvStmt s2)
    | Or (s1, s2) -> union (fvStmt s1) (fvStmt s2)
    | Not s' -> fvStmt s'
    | Equals (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | LessThan (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | _ -> []
let rec bvStmt s =
    match s with
    | ForAll (v, s') -> union [v] (bvStmt s')
    | Exists (v, s') -> union [v] (bvStmt s')
    | Implies (s1, s2) -> union (bvStmt s1) (bvStmt s2)
    | And (s1, s2) -> union (bvStmt s1) (bvStmt s2)
    | Or (s1, s2) -> union (bvStmt s1) (bvStmt s2)
    | Not s' -> fvStmt s'
    | _ -> []
let rec vars s =
    match s with
    | ForAll (v, s') -> union (vars s') [v]
    | Exists (v, s') -> union (vars s') [v]
    | Implies (s1, s2) -> union (vars s1) (vars s2)
    | And (s1, s2) -> union (vars s1) (vars s2)
    | Or (s1, s2) -> union (vars s1) (vars s2)
    | Not s' -> vars s'
    | Equals (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | LessThan (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | _ -> []

(* Converting to strings for printing *)
let rec listToString l =
    match l with
    | [] -> ""
    | h::[] -> h
    | h::t -> h ^ "," ^ (listToString t)
let rec exprToString e =
    match e with
    | Const (Int i) -> string_of_int i
    | Const (Name n) -> n
    | Const (Skol (s,l)) -> s ^"(" ^ (listToString l) ^ ")"
    | Var v -> v
    | Plus (e1,e2) -> (exprToString e1) ^ " + " ^ (exprToString e2)
    | Times (e1,e2) -> (exprToString e1) ^ " * " ^ (exprToString e2)
let rec stmtToString s =
    match s with
    | True -> "True"
    | False -> "False"
    | Equals (e1, e2) -> "(" ^ (exprToString e1) ^ ") = (" ^ (exprToString e2) ^ ")"
    | LessThan (e1, e2) -> "(" ^ (exprToString e1) ^ ") < (" ^ (exprToString e2) ^ ")"
    | Not e -> "~(" ^ (stmtToString e) ^ ")"
    | And (s1, s2) -> "(" ^ (stmtToString s1) ^ ") & (" ^ (stmtToString s2) ^ ")"
    | Or (s1, s2) -> "(" ^ (stmtToString s1) ^ ") or (" ^ (stmtToString s2) ^ ")"
    | Implies (s1, s2) -> "(" ^ (stmtToString s1) ^ ") => (" ^ (stmtToString s2) ^ ")"
    | Exists (v, s) -> "There exists " ^ v ^ " such that (" ^ (stmtToString s) ^ ")"
    | ForAll (v, s) -> "For all " ^ v ^ ", (" ^ (stmtToString s) ^ ")"

(* Converting a statement into CNF *)
let rec elimImp s =
    match s with
    | ForAll (v, s') -> (ForAll (v, elimImp s'))
    | Exists (v, s') -> (Exists (v, elimImp s'))
    | Implies (s1, s2) -> Or (Not (elimImp s1), elimImp s2)
    | And (s1, s2) -> And (elimImp s1, elimImp s2)
    | Or (s1, s2) -> Or (elimImp s1, elimImp s2)
    | Not (s') -> Not (elimImp s')
    | _ -> s
let rec pushNot s =
    match s with
    | Not (ForAll (v, s')) -> Exists (v, pushNot (Not s'))
    | Not (Exists (v, s')) -> ForAll (v, pushNot (Not s'))
    | Not (Implies (s1, s2)) -> Or (pushNot (Not s1), pushNot s2)
    | Not (And (s1, s2)) -> Or (pushNot (Not s1), pushNot (Not s2))
    | Not (Or (s1, s2)) -> And (pushNot (Not s1), pushNot (Not s2))
    | Not (Not s') -> pushNot s'
    | ForAll (v, s') -> ForAll (v, pushNot s')
    | Exists (v, s') -> Exists (v, pushNot s')
    | Implies (s1, s2) -> Implies (pushNot s1, pushNot s2)
    | And (s1, s2) -> And (pushNot s1, pushNot s2)
    | Or (s1, s2) -> Or (pushNot s1, pushNot s2)
    | Not (s') -> Not (pushNot s')
    | _ -> s
let rec replace s old rep =
    let rec replaceExpr e old rep =
        match e with
        | Var v -> if (v = old) then Var rep else e
        | Plus (e1, e2) -> Plus (replaceExpr e1 old rep, replaceExpr e2 old rep)
        | Times (e1, e2) -> Times (replaceExpr e1 old rep, replaceExpr e2 old rep)
        | _ -> e
        in
    match s with
    | ForAll (v, s') -> ForAll (rep, replace s' old rep)
    | Exists (v, s') -> Exists (rep, replace s' old rep)
    | Implies (s1, s2) -> Implies (replace s1 old rep, replace s2 old rep)
    | And (s1, s2) -> And (replace s1 old rep, replace s2 old rep)
    | Or (s1, s2) -> Or (replace s1 old rep, replace s2 old rep)
    | Not s' -> Not (replace s' old rep)
    | Equals (e1, e2) -> Equals (replaceExpr e1 old rep, replaceExpr e2 old rep)
    | LessThan (e1, e2) -> LessThan (replaceExpr e1 old rep, replaceExpr e2 old rep)
    | _ -> s
let standardize s =
    let rec standardize' s b d =
        match s with
        | ForAll (v, s') -> if (isIn v b) then
                                let (v'::t) = d in
                                ForAll (v', standardize' (replace s' v v') (union b [v']) t)
                            else ForAll (v, standardize' s' b d)
        | Exists (v, s') -> if (isIn v b) then
                                let (v'::t) = d in
                                Exists (v', standardize' (replace s' v v') (union b [v']) t)
                            else Exists (v, standardize' s' b d)
        | Implies (s1, s2) -> let s1' = standardize' s1 b d in
                                let b' = union b (bvStmt s1') in
                                Implies (s1', standardize' s2 b' (difference d b'))
        | And (s1, s2) -> let s1' = standardize' s1 b d in
                                let b' = union b (bvStmt s1') in
                                And (s1', standardize' s2 b' (difference d b'))
        | Or (s1, s2) -> let s1' = standardize' s1 b d in
                                let b' = union b (bvStmt s1') in
                                Or (s1', standardize' s2 b' (difference d b'))
        | Not s' -> Not (standardize' s' b d)
        | _ -> s
    in standardize' s [] (difference dummyVars (vars s))
let skolemize s =
    let rec inSV v sv =
        match sv with
        | [] -> false
        | (v',qv)::t -> v = v' in
    let rec findQVs v sv =
        match sv with
        | [] -> []
        | ((v',qv)::t) -> if (v = v') then qv else findQVs v t in
    let rec skolemizeExpr e sv =
        match e with
        | Var v -> if (inSV v sv) then
                        (let qv = findQVs v sv in Const (Skol (v, qv)))
                    else Var v
        | Plus (e1, e2) -> Plus (skolemizeExpr e1 sv, skolemizeExpr e2 sv)
        | Times (e1, e2) -> Times (skolemizeExpr e1 sv, skolemizeExpr e2 sv)
        | _ -> e in
    let rec skolemize' s sv qv =
        match s with
        | ForAll (v, s') -> ForAll (v, skolemize' s' sv (v::qv))
        | Exists (v, s') -> skolemize' s' ((v,qv)::sv) qv
        | Implies (s1, s2) -> Implies (skolemize' s1 sv qv, skolemize' s2 sv qv)
        | And (s1, s2) -> And (skolemize' s1 sv qv, skolemize' s2 sv qv)
        | Or (s1, s2) -> Or (skolemize' s1 sv qv, skolemize' s2 sv qv)
        | Not (s') -> Not (skolemize' s' sv qv)
        | Equals (e1, e2) -> Equals (skolemizeExpr e1 sv, skolemizeExpr e2 sv)
        | LessThan (e1, e2) -> LessThan (skolemizeExpr e1 sv, skolemizeExpr e2 sv)
        | _ -> s in
    skolemize' s [] []
let rec dropQuantifiers s =
    match s with
    | ForAll (v, s') -> dropQuantifiers s'
    | Exists (v, s') -> Exists (v, dropQuantifiers s')
    | Implies (s1, s2) -> Implies (dropQuantifiers s1, dropQuantifiers s2)
    | And (s1, s2) -> And (dropQuantifiers s1, dropQuantifiers s2)
    | Or (s1, s2) -> Or (dropQuantifiers s1, dropQuantifiers s2)
    | Not (s') -> Not (dropQuantifiers s')
    | _ -> s
let rec distributeOr s =
    match s with
    | ForAll (v, s') -> ForAll (v, distributeOr s')
    | Exists (v, s') -> Exists (v, distributeOr s')
    | Implies (s1, s2) -> Implies (distributeOr s1, distributeOr s2)
    | And (s1, s2) -> And (distributeOr s1, distributeOr s2)
    | Or (s1, And (s2, s3)) -> And (distributeOr (Or (s1, s2)), distributeOr (Or (s1, s3)))
    | Or (And (s2, s3), s1) -> And (distributeOr (Or (s2, s1)), distributeOr (Or (s3, s1)))
    | Not s' -> Not (distributeOr s')
    | _ -> s
let cnf s = distributeOr (dropQuantifiers (skolemize (standardize (distributeOr (pushNot (elimImp s))))))

let rec unifyVar v x sub =
    let rec getSub v sub =
        match sub with
        | Subst [] -> Var "None"
        | Subst ((e1,e2)::t) -> if v=e1 then e2 else getSub v (Subst t)
        | _ -> Var "None" in
    match sub with
    | Failure -> Failure
    | Subst (theta) -> (
        let valu = (getSub v sub) in
        if valu <> (Var "None") then Failure (* unify valu x sub *)
        else (
            let valu = (getSub x sub) in
            if valu <> (Var "None") then Failure (* unify v valu sub *)
            else (
                let Var v' = v in
                if isIn v' (fvExpr x) then Failure
                else Subst ((v,x)::theta)
            )
        )
    )
and unify e1 e2 sub =
    let substUnion s1 s2 =
        match (s1, s2) with
        | Failure,_ -> Failure
        | _,Failure -> Failure
        | (Subst l1), (Subst l2) -> Subst (union l1 l2) in
    match sub with
    | Failure -> Failure
    | _ -> (
        if e1 = e2 then sub
        else (
            match (e1, e2) with
            | (Var v),_ -> unifyVar e1 e2 sub
            | _,(Var v) -> unifyVar e2 e1 sub
            | (Plus (e11, e12)),(Plus (e21, e22)) -> substUnion (unify e11 e21 sub) (unify e12 e22 sub)
            | (Times (e11, e12)),(Times (e21, e22)) -> substUnion (unify e11 e21 sub) (unify e12 e22 sub)
            | _ -> Failure
        )
    )

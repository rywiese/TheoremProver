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

type const = Int of int

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

let rec exprToString e =
    match e with
    | Const (Int i) -> string_of_int i
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
    | ForAll (v, s') -> (ForAll (v, pushNot s'))
    | Exists (v, s') -> (Exists (v, pushNot s'))
    | Implies (s1, s2) -> Implies (pushNot s1, pushNot s2)
    | And (s1, s2) -> And (pushNot s1, pushNot s2)
    | Or (s1, s2) -> Or (pushNot s1, pushNot s2)
    | Not (s') -> Not (pushNot s')
    | _ -> s

let cnf s = pushNot (elimImp s)

(*
let rec prove s kb =
    match s with
    | True -> []
    | ForAll (v, s') -> prove s' kb
    | Exists (v, s') -> prove s' kb
    | Implies (s1, s2) -> ("Assume " ^ (stmtToString s1))::(prove s2 (s1::kb))
    | And (s1, s2) -> concat (("Proof of " ^ s1 ^ ":")::(prove s1 kb)) (("Proof of " ^ s2 ^ ":")::(prove s2 kb))
    | _ -> ["Not sure yet"]
*)

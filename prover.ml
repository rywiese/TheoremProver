type const = Int of int

type expr =
    | Const of const
    | Var of string
    | Plus of expr * expr
    | Times of expr * expr

type stmt =
    | ForAll of string * stmt
    | Exists of string * stmt
    | Implies of stmt * stmt
    | And of stmt * stmt
    | Or of stmt * stmt
    | Not of stmt
    | Equals of expr * expr
    | LessThan of expr * expr

let rec exprToString e =
    match e with
    | Const (Int i) -> string_of_int i
    | Var v -> v
    | Plus (e1,e2) -> (exprToString e1) ^ " + " ^ (exprToString e2)
    | Times (e1,e2) -> (exprToString e1) ^ " * " ^ (exprToString e2)

let rec stmtToString s =
    match s with
    | Equals (e1, e2) -> "(" ^ (exprToString e1) ^ ") = (" ^ (exprToString e2) ^ ")"
    | LessThan (e1, e2) -> "(" ^ (exprToString e1) ^ ") < (" ^ (exprToString e2) ^ ")"
    | Not e -> "~" ^ (stmtToString e)
    | And (s1, s2) -> "(" ^ (stmtToString s1) ^ ") & (" ^ (stmtToString s2) ^ ")"
    | Or (s1, s2) -> "(" ^ (stmtToString s1) ^ ") or (" ^ (stmtToString s2) ^ ")"
    | Implies (s1, s2) -> "(" ^ (stmtToString s1) ^ ") => (" ^ (stmtToString s2) ^ ")"
    | Exists (v, s) -> "There exists " ^ v ^ " such that (" ^ (stmtToString s) ^ ")"
    | ForAll (v, s) -> "For all " ^ v ^ ", (" ^ (stmtToString s) ^ ")"

let rec concat l1 l2 =
    match l1 with
    | [] -> l2
    | h::t -> h::(concat t l2)

let rec prove s kb =
    match s with
    | ForAll (v, s') -> prove s' kb
    | Exists (v, s') -> prove s' kb
    | Implies (s1, s2) -> ("Assume " ^ (stmtToString s1))::(prove s2 (s1::kb))
    | And (s1, s2) -> concat (("Proof of " ^ s1 ^ ":")::(prove s1 kb)) (("Proof of " ^ s2 ^ ":")::(prove s2 kb))
    | _ -> ["Not sure yet"]

prove (Implies (Equals (Var "x", Var "y"), Equals (Var "f(x)", Var "f(y)"))) []

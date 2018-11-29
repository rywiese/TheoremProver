let explode s =
  let rec expl n =
    if n >= String.length s then []
    else (String.get s n)::(expl (n+1)) in
  expl 0

let rec implode l =
  match l with
  | [] -> ""
  | h::t -> (String.make 1 h) ^ (implode t)

type const = Inf | Int of int | Real of float

type expr =
    | Const of const
    | Var of string
    | Plus of expr * expr
    | Times of expr * expr

type stmt =
    | Equals of expr * expr
    | LessThan of expr * expr
    | Not of stmt
    | And of stmt * stmt
    | Or of stmt * stmt
    | Implies of stmt * stmt
    | Exists of string * stmt
    | ForAll of string * stmt

let rec exprToString e =
    match e with
    | Const (Inf) -> "Infinity"
    | Const (Int i) -> string_of_int i
    | Const (Real r) -> string_of_float r
    | Var v -> v
    | Plus (e1,e2) -> (exprToString e1) ^ " + " ^ (exprToString e2)
    | Times (e1,e2) -> (exprToString e1) ^ " * " ^ (exprToString e2)

exprToString (Plus (Plus (Var "x", Times (Const (Int 4), Var "y")), Times (Const (Int 7), Const (Int 3))))

let rec stmtToString s =
    match s with
    | Equals (e1, e2) -> "(" ^ (exprToString e1) ^ ") = (" ^ (exprToString e2) ^ ")"
    | LessThan (e1, e2) -> "(" ^ (exprToString e1) ^ ") < (" ^ (exprToString e2) ^ ")"
    | Not e -> "~" ^ (stmtToString e)
    | And (s1, s2) -> "(" ^ (stmtToString e1) ^ ") & (" ^ (stmtToString e2) ^ ")"
    | Or (s1, s2) -> (stmtToString s1) ^ " or " ^ (stmtToString s2)
    | Implies (s1, s2) -> (stmtToString s1) ^ " => " ^ (stmtToString s2)
    | Exists (v, s) -> "There exists " ^ v ^ " such that " (stmtToString s)
    | ForAll (v, s) -> "For all " ^ v ^ ", " (stmtToString s)

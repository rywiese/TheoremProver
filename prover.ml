type const = Inf | Int of int | Real of float

type expr =
    | Const of const
    | Var of string
    | Plus of expr * expr
    | Times of expr * expr

type stmt =
    | Equals of expr * expr
    | LessThan of expr * expr
    | Plus of expr * expr * expr
    | Times of expr * expr * expr
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

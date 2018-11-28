type const = Int of int
type var = string
type value = Const of const | Var of var

type expr =
    | Equals of value * value
    | LessThan of value * value
    | Plus of value * value * value
    | Times of value * value * value
    | Exists of var * expr
    | ForAll of var * expr
    | And of stmt

let

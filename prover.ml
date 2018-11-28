type const = int
type var = string
type value = Const of const | Var of var

type stmt =
    | Equals of value * value * (value * const) list
    | LessThan of var * var * (var * const) list
    | Plus of var * var * var * (var * const) list
    | Times of var * var * var * (var * const) list

type sent = stmt

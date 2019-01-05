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
let rec append e l =
    match l with
    | [] -> e::[]
    | h::t -> h::(append e t)
let rec cross l1 l2 =
    let rec cross' e l2 =
        match l2 with
        | [] -> []
        | h::t -> union [(e,h);] (cross' e t) in
    match l1 with
    | [] -> []
    | h::t -> union (cross' h l2) (cross t l2)
let rec subset s1 s2 =
    match s1 with
    | [] -> true
    | (h::t) -> if isIn h s2 then subset t s2 else false
let revlist l =
    let rec revlist' l r =
        match l with
        | [] -> r
        | h::t -> revlist' t (h::r) in
    revlist' l []
let rec lenList l =
    match l with
    | [] -> 0
    | h::t -> 1 + (lenList t)
let rec crossList l1 l2 =
    let rec crossList' e l =
        match l with
        | [] -> []
        | h::t -> (append e h)::(crossList' e t) in
    match l1 with
    | [] -> []
    | h::t -> union (crossList' h l2) (crossList t l2)
let rec setToTheNth l n =
    let rec listToListList l =
        match l with
        | [] -> []
        | h::t -> [h]::(listToListList t) in
    if n <= 1 then listToListList l
    else crossList l (setToTheNth l (n-1))

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
let dummyVars = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z";"A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z"]
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
let rec constsInExpr e =
    match e with
    | Const (Name n) -> [n]
    | Plus (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | Times (e1, e2) -> union (fvExpr e1) (fvExpr e2)
    | _ -> []
let rec constsIn s =
    match s with
    | ForAll (v, s') -> constsIn s'
    | Exists (v, s') -> constsIn s'
    | Implies (s1, s2) -> union (constsIn s1) (constsIn s2)
    | And (s1, s2) -> union (constsIn s1) (constsIn s2)
    | Or (s1, s2) -> union (constsIn s1) (constsIn s2)
    | Not s' -> constsIn s'
    | Equals (e1, e2) -> union (constsInExpr e1) (constsInExpr e2)
    | LessThan (e1, e2) -> union (constsInExpr e1) (constsInExpr e2)
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
let bvc s = union (bvStmt s) (constsIn s)

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
    | True -> "true"
    | False -> "false"
    | Equals (e1, e2) -> "(" ^ (exprToString e1) ^ ") = (" ^ (exprToString e2) ^ ")"
    | LessThan (e1, e2) -> "(" ^ (exprToString e1) ^ ") < (" ^ (exprToString e2) ^ ")"
    | Not e -> "~(" ^ (stmtToString e) ^ ")"
    | And (s1, s2) -> "(" ^ (stmtToString s1) ^ ") & (" ^ (stmtToString s2) ^ ")"
    | Or (s1, s2) -> "(" ^ (stmtToString s1) ^ ") or (" ^ (stmtToString s2) ^ ")"
    | Implies (s1, s2) -> "(" ^ (stmtToString s1) ^ ") => (" ^ (stmtToString s2) ^ ")"
    | Exists (v, s) -> "there exists " ^ v ^ " such that (" ^ (stmtToString s) ^ ")"
    | ForAll (v, s) -> "for all " ^ v ^ ", (" ^ (stmtToString s) ^ ")"
let substToString s =
    let rec exprListToString l =
        match l with
        | [] -> ""
        | (e1,e2)::t -> (exprToString e1) ^ "/" ^ (exprToString e2) ^ (", ") ^ (exprListToString t) in
    match s with
    | Failure -> "None"
    | Subst l -> exprListToString l

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
    let rec pushNotExpr e =
        match e with
        | Const (Skol (v,l)) -> Var v
        | Plus (e1,e2) -> Plus (pushNotExpr e1, pushNotExpr e2)
        | Times (e1,e2) -> Times (pushNotExpr e1, pushNotExpr e2)
        | _ -> e in
    match s with
    | Not (ForAll (v, s')) -> Exists (v, pushNot (Not s'))
    | Not (Exists (v, s')) -> ForAll (v, pushNot (Not s'))
    | Not (Implies (s1, s2)) -> Or (pushNot (Not s1), pushNot s2)
    | Not (And (s1, s2)) -> Or (pushNot (Not s1), pushNot (Not s2))
    | Not (Or (s1, s2)) -> And (pushNot (Not s1), pushNot (Not s2))
    | Not (Not s') -> pushNot s'
    | Not (Equals (e1, e2)) -> Not (Equals (pushNotExpr e1, pushNotExpr e2))
    | Not (LessThan (e1, e2)) -> Not (LessThan (pushNotExpr e1, pushNotExpr e2))
    | ForAll (v, s') -> ForAll (v, pushNot s')
    | Exists (v, s') -> Exists (v, pushNot s')
    | Implies (s1, s2) -> Implies (pushNot s1, pushNot s2)
    | And (s1, s2) -> And (pushNot s1, pushNot s2)
    | Or (s1, s2) -> Or (pushNot s1, pushNot s2)
    | Not (s') -> Not (pushNot s')
    | Equals (e1, e2) -> Equals (pushNotExpr e1, pushNotExpr e2)
    | LessThan (e1, e2) -> LessThan (pushNotExpr e1, pushNotExpr e2)
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
                                let b' = union b (bvc s1') in
                                Implies (s1', standardize' s2 b' (difference d b'))
        | And (s1, s2) -> let s1' = standardize' s1 b d in
                                let b' = union b (bvc s1') in
                                And (s1', standardize' s2 b' (difference d b'))
        | Or (s1, s2) -> let s1' = standardize' s1 b d in
                                let b' = union b (bvc s1') in
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

(* Unification *)
let rec getSub v sub =
    match sub with
    | Subst [] -> Var "None"
    | Subst ((e1,e2)::t) -> if v=e1 then e2 else getSub v (Subst t)
    | _ -> Var "None"
let rec combinableSubs l1 l2 =
    let rec comb s l =
        match l with
        | [] -> true
        | (v2,e2)::t -> let v1,e1 = s in if (v1 = v2) && (e1 <> e2) then false else comb s t in
    match l1 with
    | [] -> true
    | h::t -> if comb h l2 then combinableSubs t l2 else false
let substUnion s1 s2 =
    match (s1, s2) with
    | Failure,_ -> Failure
    | _,Failure -> Failure
    | (Subst l1), (Subst l2) ->
        if combinableSubs l1 l2 then Subst (union l1 l2) else Failure
let rec substitute s sub =
    let rec subExpr e sub =
        match e with
        | Var v -> let noo = getSub e sub in
                    if noo = Var "None" then e else noo
        | Plus (e1, e2) -> Plus ((subExpr e1 sub), (subExpr e2 sub))
        | Times (e1, e2) -> Times ((subExpr e1 sub), (subExpr e2 sub))
        | _ -> e in
    match s with
    | ForAll (v, s') -> ForAll (v, substitute s' sub)
    | Exists (v, s') -> Exists (v, substitute s' sub)
    | Implies (s1, s2) -> Implies (substitute s1 sub, substitute s2 sub)
    | And (s1, s2) -> And (substitute s1 sub, substitute s2 sub)
    | Or (s1, s2) -> Or (substitute s1 sub, substitute s2 sub)
    | Not s' -> Not (substitute s' sub)
    | Equals (e1, e2) -> Equals (subExpr e1 sub, subExpr e2 sub)
    | LessThan (e1, e2) -> LessThan (subExpr e1 sub, subExpr e2 sub)
    | _ -> s
let rec unifyVar v x sub =
    match sub with
    | Failure -> Failure
    | Subst (theta) -> (
        let valu = (getSub v sub) in
        if valu <> (Var "None") then unify' valu x sub
        else (
            let valu = (getSub x sub) in
            if valu <> (Var "None") then unify' v valu sub
            else (
                match v with
                | Var v' ->
                    if isIn v' (fvExpr x) then Failure
                    else Subst ((v,x)::theta)
                | _ -> Failure
            )
        )
    )
and unify' e1 e2 sub =
    match sub with
    | Failure -> Failure
    | _ -> (
        if e1 = e2 then sub
        else (
            match (e1, e2) with
            | (Var v),_ -> unifyVar e1 e2 sub
            | _,(Var v) -> unifyVar e2 e1 sub
            | (Plus (e11, e12)),(Plus (e21, e22)) -> substUnion (unify' e11 e21 sub) (unify' e12 e22 sub)
            | (Times (e11, e12)),(Times (e21, e22)) -> substUnion (unify' e11 e21 sub) (unify' e12 e22 sub)
            | _ -> Failure
        )
    )
let unifyExpr e1 e2 = unify' e1 e2 (Subst [])
let unifyStmt s1 s2 =
    let rec unifyStmt' s1 s2 sub =
        match (s1,s2) with
        | (ForAll (v1, s1')), (ForAll (v2, s2')) -> unifyStmt' s1' s2' sub
        | (Exists (v1, s1')), (Exists (v2, s2')) -> unifyStmt' s1' s2' sub
        | (Implies (s11, s12)), (Implies (s21, s22)) -> substUnion (unifyStmt' s11 s21 sub) (unifyStmt' s12 s22 sub)
        | (And (s11, s12)), (And (s21, s22)) ->
            let sub1 = substUnion (unifyStmt' s11 s21 sub) (unifyStmt' s12 s22 sub) in
            let sub2 = substUnion (unifyStmt' s11 s22 sub) (unifyStmt' s12 s21 sub) in
            (match sub1,sub2 with
            | Failure,_ -> sub2
            | _,Failure -> sub1
            | _,_ -> substUnion sub1 sub2)
        | (Or (s11, s12)), (Or (s21, s22)) -> substUnion (unifyStmt' s11 s21 sub) (unifyStmt' s12 s22 sub)
        | (Not s1'), (Not s2') -> unifyStmt' s1' s2' sub
        | (Equals (e11,e12)), (Equals (e21,e22)) -> substUnion (unifyExpr e11 e21) (unifyExpr e12 e22)
        | (LessThan (e11,e12)), (LessThan (e21,e22)) -> substUnion (unifyExpr e11 e21) (unifyExpr e12 e22)
        | _ -> Failure in
    unifyStmt' s1 s2 (Subst [])

(* Resolution *)
let rec splitKB kb =
    match kb with
    | And (s1,s2) -> concat (splitKB s1) (splitKB s2)
    | _ -> [kb]
let rec andifyKB kb =
    match kb with
    | [] -> True
    | h::[] -> h
    | h::t -> And (h, (andifyKB t))
let prepare kb = splitKB (cnf (andifyKB kb))
let clauseToList c =
    let rec clauseToList' c l =
        match c with
        | Or (s1, s2) -> union (clauseToList' s1 l) (clauseToList' s2 l)
        | _ -> c::l in
    clauseToList' c []
let rec listToClause l =
    match l with
    | [] -> True
    | h::[] -> h
    | h::t -> Or(h, (listToClause t))
let cnfToList c =
    let rec cnfToList' c l =
        match c with
        | And (s1, s2) -> union (cnfToList' s1 l) (cnfToList' s2 l)
        | _ -> c::l in
    cnfToList' c []


let addForAlls s =
    let rec addForAlls' s vl =
        match vl with
        | [] -> s
        | h::t -> ForAll(h, addForAlls' s t) in
    addForAlls' s (fvStmt s)
let rec availSkols s bv =
    let rec availSkolsExpr e bv =
        match e with
        | Const (Skol (v,vl)) -> if subset vl bv then [e] else []
        | Plus (e1,e2) -> union (availSkolsExpr e1 bv) (availSkolsExpr e2 bv)
        | Times (e1,e2) -> union (availSkolsExpr e1 bv) (availSkolsExpr e2 bv)
        | _ -> [] in
    match s with
    | ForAll (v,s') -> availSkols s' bv
    | And (s1,s2) -> union (availSkols s1 bv) (availSkols s2 bv)
    | Or (s1, s2) -> union (availSkols s1 bv) (availSkols s2 bv)
    | Not s' -> availSkols s' bv
    | Equals (e1,e2) -> union (availSkolsExpr e1 bv) (availSkolsExpr e2 bv)
    | LessThan (e1,e2) -> union (availSkolsExpr e1 bv) (availSkolsExpr e2 bv)
    | _ -> []
let rec replaceSkols s skol =
    let rec replaceSkolsExpr e skol =
        match e with
        | Const (Skol (v,vl)) -> if e = skol then Var v else e
        | Plus (e1,e2) -> Plus ((replaceSkolsExpr e1 skol), (replaceSkolsExpr e2 skol))
        | Times (e1,e2) -> Times ((replaceSkolsExpr e1 skol), (replaceSkolsExpr e2 skol))
        | _ -> e in
    match s with
    | ForAll (v,s') -> ForAll (v, replaceSkols s' skol)
    | And (s1,s2) -> And ((replaceSkols s1 skol),(replaceSkols s2 skol))
    | Or (s1,s2) -> Or ((replaceSkols s1 skol),(replaceSkols s2 skol))
    | Not s' -> Not (replaceSkols s' skol)
    | Equals (e1,e2) -> Equals ((replaceSkolsExpr e1 skol),(replaceSkolsExpr e2 skol))
    | LessThan (e1,e2) -> LessThan ((replaceSkolsExpr e1 skol),(replaceSkolsExpr e2 skol))
    | _ -> s
let addExists s =
    let rec addExists' s bv =
        let rec insertAndReplace s avail =
            match avail with
            | [] -> s
            | h::t -> let Const (Skol (v,l)) = h in Exists(v, (replaceSkols s h)) in
        match insertAndReplace s (availSkols s bv) with
        | ForAll (v, s') -> ForAll (v, (addExists' s' (v::bv)))
        | Exists (v, s') -> Exists (v, (addExists' s' bv))
        | Implies (s1, s2) -> Implies ((addExists' s1 bv),(addExists' s2 bv))
        | And (s1, s2) -> And ((addExists' s1 bv),(addExists' s2 bv))
        | Or (s1, s2) -> Or ((addExists' s1 bv),(addExists' s2 bv))
        | Not s' -> Not (addExists' s' bv)
        | _ -> s in
    addExists' s []
let rec addImp s =
    match s with
    | Or (Not s1, s2) -> Implies (s1, s2)
    | ForAll (v, s') -> ForAll (v, addImp s')
    | Exists (v, s') -> Exists (v, addImp s')
    | Implies (s1, s2) -> Implies (addImp s1, addImp s2)
    | And (s1, s2) -> And (addImp s1, addImp s2)
    | Or (s1, s2) -> Or (addImp s1, addImp s2)
    | Not s' -> Not (addImp s')
    | _ -> s
let expandCNF s sub = addImp (addExists (addForAlls (substitute s sub)))

let addToProof s proof = s::proof
    (* match proof with
    | [] -> [s]
    | h::t -> if (h = "Contradiction.") || (h = "Q.E.D") then proof else s::proof *)
let concatProofs p1 p2 =
    if isIn "Contradiction." p2 then p2 else union p1 p2

type clause = Empty | Lits of stmt list
let stmtToClause s =
    let rec stmtToList s =
        match s with
        | True -> [s]
        | False -> []
        | Or (s1, s2) -> union (stmtToList s1) (stmtToList s2)
        | Not s' -> [s]
        | Equals (e1, e2) -> [s]
        | LessThan (e1, e2) -> [s]
    in match stmtToList s with
    | [] -> Empty
    | h::t -> Lits (h::t)
let rec clauseToStmt c =
    match c with
    | Empty -> False
    | Lits [] ->
        Equals ((Const (Name "Error in clauseToStmt")), (Const (Name "Error in clauseToStmt")))
    | Lits (s::[]) -> s
    | Lits (s::t) -> Or (s, (clauseToStmt (Lits t)))

let rec resolveLit' lit front back proof =
    match back with
    | Empty -> [Empty], proof
    | Lits [] -> ([front], proof)
    | Lits (h::t) -> (
        let ((Lits fList), (Lits bList)) = (front, back) in
        let oldClause = Lits (concat fList bList) in
        let (rest, proof1) = resolveLit' lit (Lits (append h fList)) (Lits t) proof in
        match unifyStmt (cnf (Not lit)) (cnf h) with
        | Failure -> (rest, proof1)
        | Subst s ->
            let newClause = Lits (concat fList t) in
            if newClause = Lits [] then
                let sent = ("Using " ^ (substToString (Subst s)) ^ ", " ^ (stmtToString (expandCNF lit (Subst s))) ^ " and " ^ (stmtToString (expandCNF (clauseToStmt oldClause) (Subst s)))) in
                ((Empty::rest), (addToProof "Contradiction." (addToProof sent proof1)))
            else
            let sent = ((stmtToString (expandCNF lit (Subst s))) ^ " and " ^ (stmtToString (expandCNF (clauseToStmt oldClause) (Subst s))) ^ " therefore " ^ (stmtToString (expandCNF (clauseToStmt newClause) (Subst s)))) in
            ((newClause::rest), (addToProof sent proof1))
        )
let resolveLit lit clause proof = resolveLit' lit (Lits []) clause proof
let rec resolveClauses c1 c2 proof =
        match c1 with
        | Empty -> ([], proof)
        | Lits [] -> ([], proof)
        | Lits (h::t) -> (
            let (resolvents, proof1) = resolveLit h c2 proof in
            let (rest, proof2) = resolveClauses (Lits t) c2 proof1 in
            ((union resolvents rest), proof2))
let rec resolve pair proof =
    match pair with
    | [] -> ([], proof)
    | (c1, c2)::t ->
        let (resolvents, proof1) = resolve t [] in
        let (rest, proof2) = resolveClauses c1 c2 [] in
        ((union resolvents rest), concatProofs (concatProofs (proof1) (proof2)) proof)
let rec resolutionLoop clauseList old proof =
        match clauseList with
        | [] -> proof
        | _ -> (
            let (resolvents, proof') = resolve (cross clauseList clauseList) proof in
            if isIn Empty resolvents then ("Q.E.D")::proof'
            else (let noo = union old resolvents in
            if subset noo clauseList then ("The statement is not entailed")::proof'
            else resolutionLoop clauseList noo proof'))
let resolution alpha kb =
    let resolution' kb proof =
        let clauses =
            let rec clausify kb =
                match kb with
                | [] -> []
                | h::t -> (stmtToClause h)::(clausify t)
            in clausify kb
        in resolutionLoop clauses [] proof
    in (resolution' (prepare ((Not alpha)::kb)) ["Suppose " ^ (stmtToString(Not alpha))])

(* c is assumed to be a clause in cnf form *)
let rec getPosLits c =
    match c with
    | Or (c1, c2) -> union (getPosLits c1) (getPosLits c2)
    | Not c' -> []
    | _ -> [c]
let rec getNegLits c =
    match c with
    | Or (c1, c2) -> union (getNegLits c1) (getNegLits c2)
    | Not c' -> [c']
    | _ -> []
let hornify c =
    let rec negToAnd n =
        match n with
        | h::[] -> h
        | h::t -> And (h, negToAnd t) in
    let (neg, pos) = (getNegLits c, getPosLits c) in
    match (neg, pos) with
    | _,[] -> negToAnd neg
    | [],(p::[]) -> p
    | (h::t),(p::[]) -> Implies ((negToAnd neg), p)
    | _,_ -> False
let rec hornifyKB kb =
    match kb with
    | [] -> []
    | (h::t) -> (hornify h)::(hornifyKB t)
let prepareFC kb = hornifyKB (prepare kb)

let rec numLits s =
    match s with
    | And (s1, s2) -> (numLits s1) + (numLits s2)
    | _ -> 1
let rec unifiesWithAny s l =
    match l with
    | [] -> false
    | (h::t) -> if unifyStmt (cnf s) (cnf h) <> Failure then true else unifiesWithAny s t
let rec getSubsFC' p q rules =
    match rules with
    | [] -> []
    | rule::rest -> (
        let p',r' = (cnf p),(cnf (andifyKB rule)) in
        match (unifyStmt p' r') with
        | Failure -> getSubsFC' p q rest
        | Subst s -> union [((Subst s),((stmtToString (expandCNF (Implies (p, q)) (Subst []))) ^ " and " ^ (stmtToString (andifyKB rule)) ^ ", therefore "))] (getSubsFC' p q rest)
        )
let getSubsFC p q kb = getSubsFC' p q (setToTheNth kb (numLits p))
let rec forEachTheta q subs alpha kb old proof =
    match subs with
    | [] -> old, proof
    | (Failure, subProof)::t -> forEachTheta q t alpha kb old proof
    | (Subst s, subProof)::t ->
        let q' = substitute q (Subst s) in
        if unifyStmt q' alpha <> Failure then
            (q'::old), ("Q.E.D"::(addToProof (subProof ^ (stmtToString q')) proof))
        else if unifiesWithAny q' (prepare (union kb old)) then forEachTheta q t alpha kb old proof
        else forEachTheta q t alpha kb (q'::old) (addToProof (subProof ^ (stmtToString q')) proof)
let rec forwardChainLoop alpha rest kb old proof =
    match rest with
    | [] -> old,proof
    | rule::rest' -> (
        match rule with
        | Implies (p, q) ->
            let subs = getSubsFC p q kb in
            let noo,proof' = forEachTheta q subs alpha kb old proof in
            forwardChainLoop alpha rest' kb noo proof'
        | _ -> forwardChainLoop alpha rest' kb old proof
        )
let rec forwardChain' alpha kb proof =
    let noo,proof' = forwardChainLoop alpha kb kb [] proof in
    if unifiesWithAny alpha (prepare (union noo kb)) then proof' else
    match noo with
    | [] -> ["The statement is not entailed"]
    | (h::t) -> forwardChain' alpha (union noo kb) proof'
let forwardChain alpha kb = forwardChain' (hornify (cnf alpha)) (prepareFC kb) []

let rec makeConstant s x =
    let rec makeConstantExpr e x =
        match e with
        | Var v -> if v = x then Const (Name v) else e
        | Plus (e1, e2) -> Plus ((makeConstantExpr e1 x), (makeConstantExpr e2 x))
        | Times (e1, e2) -> Times ((makeConstantExpr e1 x), (makeConstantExpr e2 x))
        | _ -> e in
    match s with
    | ForAll (v, s') -> ForAll (v, makeConstant s' x)
    | Exists (v, s') -> Exists (v, makeConstant s' x)
    | Implies (s1, s2) -> Implies (makeConstant s1 x, makeConstant s2 x)
    | And (s1, s2) -> And (makeConstant s1 x, makeConstant s2 x)
    | Or (s1, s2) -> Or (makeConstant s1 x, makeConstant s2 x)
    | Not s' -> Not (makeConstant s' x)
    | Equals (e1, e2) -> Equals (makeConstantExpr e1 x, makeConstantExpr e2 x)
    | LessThan (e1, e2) -> LessThan (makeConstantExpr e1 x, makeConstantExpr e2 x)
    | _ -> s
let rec makeSkol s x bv =
    let rec makeSkolExpr e x bv =
        match e with
        | Var v -> if v = x then Const (Skol (v,bv)) else e
        | Plus (e1, e2) -> Plus ((makeSkolExpr e1 x bv), (makeSkolExpr e2 x bv))
        | Times (e1, e2) -> Times ((makeSkolExpr e1 x bv), (makeSkolExpr e2 x bv))
        | _ -> e in
    match s with
    | ForAll (v, s') -> ForAll (v, makeSkol s' x bv)
    | Exists (v, s') -> Exists (v, makeSkol s' x bv)
    | Implies (s1, s2) -> Implies (makeSkol s1 x bv, makeSkol s2 x bv)
    | And (s1, s2) -> And (makeSkol s1 x bv, makeSkol s2 x bv)
    | Or (s1, s2) -> Or (makeSkol s1 x bv, makeSkol s2 x bv)
    | Not s' -> Not (makeSkol s' x bv)
    | Equals (e1, e2) -> Equals (makeSkolExpr e1 x bv, makeSkolExpr e2 x bv)
    | LessThan (e1, e2) -> LessThan (makeSkolExpr e1 x bv, makeSkolExpr e2 x bv)
    | _ -> s
let proveResolution s kb =
    let rec prove' s kb bv proof =
        match s with
        | True -> []
        | False -> ["Contradiction"]
        | ForAll (x, s') -> prove' (makeConstant s' x) kb (x::bv) (("Given " ^ x)::proof)
        | Exists (x, s') -> prove' (makeSkol s' x bv) kb bv
                                    (("Let " ^ x ^ " = " ^ (exprToString (Const (Skol (x,bv)))))::proof)
        | Implies (s1, s2) -> prove' s2 (s1::kb) bv (("Assume " ^ (stmtToString s1))::proof)
        | And (s1, s2) -> let (p1,p2) = (prove' s1 kb bv [], prove' s2 kb bv []) in
                concat (("Proof of " ^ (stmtToString s1))::p1) (("Proof of " ^ (stmtToString s2))::p2)
        | Not (ForAll (x, s')) -> prove' (Exists (x, Not s')) kb bv proof
        | Not (Exists (x, s')) -> prove' (ForAll (x, Not s')) kb bv proof
        | Not (Implies (s1, s2)) -> prove' (Not (And (s1, Not s2))) kb bv proof
        | _ -> concat ((resolution s kb)) proof
    in revlist (prove' s kb [] [])

let proveFC s kb =
    let rec prove' s kb bv proof =
        match s with
        | True -> []
        | False -> ["The statement is not entailed"]
        | ForAll (x, s') -> prove' (makeConstant s' x) kb (x::bv) (("Given " ^ x)::proof)
        | Exists (x, s') -> prove' (makeSkol s' x bv) kb bv (("Let " ^ x ^ " = " ^ (exprToString (Const (Skol (x,bv)))))::proof)
        | Implies (s1, s2) -> prove' s2 (s1::kb) bv (("Assume " ^ (stmtToString s1))::proof)
        | And (s1, s2) -> let (p1,p2) = (prove' s1 kb bv [], prove' s2 kb bv []) in
                concat (("Proof of " ^ (stmtToString s1))::p1) (("Proof of " ^ (stmtToString s2))::p2)
        | Not (ForAll (x, s')) -> prove' (Exists (x, Not s')) kb bv proof
        | Not (Exists (x, s')) -> prove' (ForAll (x, Not s')) kb bv proof
        | Not (Implies (s1, s2)) -> prove' (Not (And (s1, Not s2))) kb bv proof
        | _ -> concat ((forwardChain s kb)) proof
    in revlist (prove' s kb [] [])

let rec batchProve alphas kb =
    match alphas with
    | [] -> []
    | h::t -> ((("Proof of " ^ (stmtToString h) ^ " using resolution:")::(proveResolution h kb)),(("Proof of " ^ (stmtToString h) ^ " using forward chaining:")::(proveFC h kb)),
        "                                                                                                                                                  ")::(batchProve t kb)
;;


let kb = [
(*  Axioms of equality  *)
ForAll("x", Equals(Var "x", Var "x"));
ForAll("x", ForAll("y", Implies(Equals(Var "x", Var "y"),Equals(Var "y", Var "x"))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (Equals (Var "x", Var "y"), Equals (Var "y", Var "z")), Equals (Var "x", Var "z")))));
ForAll("x", Equals(Const (Int 0), Times (Const (Int 0),Var "x")));
(*  Axioms of less than *)
ForAll("x", Not (LessThan (Var "x", Var "x")));
ForAll("x", ForAll("y", Implies ((LessThan(Var "x", Var "y")),(Not (LessThan (Var "y", Var "x"))))));
ForAll("x", ForAll("y", ForAll ("z", Implies (And (LessThan (Var "x", Var "y"), LessThan (Var "y", Var "z")), LessThan (Var "x", Var "z")))));
ForAll("x", Or ((LessThan (Const (Int 0), Var "x")),(Equals (Const (Int 0), Var "x"))));
ForAll("x", LessThan(Var "x", Plus(Var "x", Const(Int 1))));
ForAll("x", LessThan(Var "x", Times(Var "x", Var "x")));
ForAll("x", Exists ("y", LessThan (Var "x", Var "y")));
(*  Other things that we are deciding to be true    *)
Equals((Const (Name "Ry")),(Const (Name "Arman")));
Equals((Const (Name "Parker")),(Const (Name "Arman")));
ForAll("x", LessThan (Var "x", Const (Name "Ry")));
];;
let alpha1 = Equals((Const (Name "Parker")),(Const (Name "Arman")));;
let alpha2 = Exists ("x", Equals (Var "x", Const (Name "Arman")));;
let alpha3 = (ForAll ("x", (Implies ((Equals(Const (Name "Parker"), Var "x"), (Equals((Var "x"),(Const (Name "Ry")))))))));;
let alpha4 = Not (LessThan ((Const (Name "Ry")),(Const (Name "Arman"))));;
let alpha5 = ForAll ("x", ForAll ("y", Exists ("z", LessThan (Plus (Var "x", Var "y"),(Var "z")))));;
let alpha6 = ForAll ("x", Exists ("y", Equals (Var "x", Var "y")));;
let alpha7 = ForAll ("x", Exists ("y", LessThan (Times (Var "x", Var "x"),Var "y")));;
(* Exists ("x", Equals (Var "x", Times (Var "x", Var "x"))); THIS NEVER TERMINATES *)
let alpha8 = ForAll ("x", LessThan (Times (Var "x", Var "x"), Times (Times (Var "x",Var "x"),Var "x")));;
let alpha9 = LessThan (Times (Const (Name "Arman"), (Const (Name "Arman"))), Times (Const (Name "Ry"), (Const (Name "Ry"))));;
let alpha10 = LessThan (Times (Const (Name "Arman"), (Const (Name "Parker"))), Times (Const (Name "Ry"), (Const (Name "Parker"))));;
let alpha11 = ForAll ("x", ForAll ("y", Exists ("z", Equals (Var "z", Plus (Var "x", Var "y")))));;
let alpha12 = Exists ("x", ForAll ("y", Or (LessThan (Var "x",Var "y"), Equals (Var "x",Var "y"))));;
let alpha13 = ForAll ("x", Exists ("y", LessThan(Times (Var "x",Plus (Const (Int 1), Const (Int 1))),Var "y")));;
let alpha14 = Not (Exists ("x", ForAll ("y", (LessThan (Var "y", Var "x")))));;
let alpha15 = Not (ForAll ("x", (LessThan (Var "x", Times (Var "x", Var "x")))));;
proveFC alpha1 kb;;
proveFC alpha2 kb;;
proveFC alpha3 kb;;
proveFC alpha4 kb;;
proveFC alpha5 kb;;
proveFC alpha6 kb;;
proveFC alpha7 kb;;
proveFC alpha8 kb;;
proveFC alpha9 kb;;
proveFC alpha10 kb;;
proveFC alpha11 kb;;
proveFC alpha12 kb;;
proveFC alpha13 kb;;
proveFC alpha14 kb;;
proveFC alpha15 kb;;

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

(* Unification *)
let substUnion s1 s2 =
    match (s1, s2) with
    | Failure,_ -> Failure
    | _,Failure -> Failure
    | (Subst l1), (Subst l2) -> Subst (union l1 l2)
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
        if valu <> (Var "None") then unify' valu x sub
        else (
            let valu = (getSub x sub) in
            if valu <> (Var "None") then unify' v valu sub
            else (
                let Var v' = v in
                if isIn v' (fvExpr x) then Failure
                else Subst ((v,x)::theta)
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
        | (And (s11, s12)), (And (s21, s22)) -> substUnion (unifyStmt' s11 s21 sub) (unifyStmt' s12 s22 sub)
        | (Or (s11, s12)), (Or (s21, s22)) -> substUnion (unifyStmt' s11 s21 sub) (unifyStmt' s12 s22 sub)
        | (Not s1'), (Not s2') -> unifyStmt' s1' s2' sub
        | (Equals (e11,e12)), (Equals (e21,e22)) -> substUnion (unifyExpr e11 e21) (unifyExpr e12 e22)
        | (LessThan (e11,e12)), (LessThan (e21,e22)) -> substUnion (unifyExpr e11 e21) (unifyExpr e12 e22)
        | _ -> Failure in
    unifyStmt' s1 s2 (Subst [])

(* Resolution *)
let rec splitKB kb =
    match kb with
    | [] -> []
    | (And (s1,s2))::t -> splitKB (s1::s2::t)
    | h::t -> h::(splitKB t)
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
let resolveLit l c =
    let rec resolveLit' lit f cl =
        match cl with
        | [] -> []
        | h::t -> (
            match unifyStmt (cnf (Not lit)) h with
            | Failure -> (resolveLit' lit (append h f) t)
            | Subst s -> (listToClause (concat f t))::(resolveLit' lit (append h f) t)
            ) in
    resolveLit' l [] (clauseToList c)
let rec resolve c1 c2 =
    match (unifyStmt (cnf (Not c1)) (cnf c2)) with
    | Subst s -> [False]
    | Failure -> (
        match c1 with
        | Or (s1, s2) -> union (resolve s1 c2) (resolve s2 c2)
        | _ -> resolveLit c1 c2
    )
let resolution alpha kb =
    let getResolvents cl =
        let rec getResolvents' l =
            match l with
            | [] -> []
            | (c1, c2)::t -> union (resolve c1 c2) (getResolvents' t) in
        getResolvents' (cross cl cl) in
    let rec resolution' clauses old =
        let resolvents = getResolvents clauses in
        if isIn False resolvents then true
        else (
            let noo = union old resolvents in
            if subset noo clauses then false
            else resolution' (union noo clauses) noo
        ) in
    resolution' (splitKB (cnf(Not alpha)::kb)) []

let resolveLitProof l c proof =
    let rec resolveLitProof' lit f cl proof =
        match cl with
        | [] -> [],proof
        | h::t -> (
            match unifyStmt (cnf (Not lit)) h with
            | Failure -> let (l, proof') = (resolveLitProof' lit (append h f) t proof) in (l, proof')
            | Subst s -> let clause = (listToClause (concat f t)) in
                    let (l, proof') = (resolveLitProof' lit (append h f) t proof) in
                    (clause::l), (((stmtToString (Not lit)) ^ " and " ^ (stmtToString h) ^ " therefore " ^ (stmtToString clause))::proof')
            ) in
    resolveLitProof' l [] (clauseToList c) proof
let rec resolveProof c1 c2 proof =
    match c1 with
    | Or (s1, s2) -> let (resolve1, proof1) = resolveProof s1 c2 proof in
            let (resolve2, proof2) = resolveProof s2 c2 proof in
            ((union resolve1 resolve2), proof2)
    | _ -> (resolveLitProof c1 c2 proof)
let resolutionProof alpha kb =
    let getResolventsProof cl proof =
        let rec getResolventsProof' l proof =
            match l with
            | [] -> [],proof
            | (c1, c2)::t -> let (resolvents, proof1) = (getResolventsProof' t proof) in
                        let (l,proof2) = (resolveProof c1 c2 proof1) in
                        ((union l resolvents), proof2) in
        getResolventsProof' (cross cl cl) proof in
    let rec resolutionProof' clauses old proof =
        let (resolvents, proof') = getResolventsProof clauses proof in
        if isIn False resolvents then ("Q.E.D")::proof'
        else (
            let noo = union old resolvents in
            if subset noo clauses then ("This statement is not entailed!")::proof'
            else resolutionProof' (union noo clauses) noo proof'
        ) in
    let proof = resolutionProof' (splitKB (cnf(Not alpha)::kb)) [] ["Suppose "^stmtToString(Not alpha)] in
    revlist proof

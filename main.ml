type pterm =
    Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Entier of int
  | Addition of pterm * pterm
  | Soustraction of pterm * pterm
  | Nil
  | Cons of pterm * pterm
  | Izte of pterm * pterm * pterm
  | Iete of pterm * pterm * pterm
  | Fix of pterm
  | Let of string * pterm * pterm
  | Head of pterm
  | Tail of pterm

let is_empty (liste : pterm) : bool = 
  (liste = Nil)

let is_liste (t : pterm) : bool =
  match t with
  | _ -> failwith "TODO"

let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ (print_term t) ^ ")"
    | Entier n -> string_of_int n
    | Addition (x, y) -> (
      match (x, y) with 
      | (Entier i, Entier k) -> string_of_int i ^ " + " ^ string_of_int k
      | (Entier i, k) ->  string_of_int i ^ " + " ^ (print_term k)
      | (i, Entier k) -> (print_term i) ^ " + " ^ string_of_int k
      | (i, k) -> (print_term i) ^ " + " ^ (print_term k))
  | Soustraction (x, y) -> (
      match (x, y) with 
      | (Entier i, Entier k) -> string_of_int i ^ " - " ^ string_of_int k
      | (Entier i, k) ->  string_of_int i ^ " - " ^ (print_term k)
      | (i, Entier k) -> (print_term i) ^ " - " ^ string_of_int k
      | (i, k) -> (print_term i) ^ " - " ^ (print_term k))
  | Nil -> "[]"
  | Cons (x, xs) -> print_term x ^ "::" ^ print_term xs
  | Izte (entier, consequent, alternative) ->
    "if " ^ (print_term entier) ^ " == 0 then " ^ (print_term consequent) ^ " else " ^ (print_term alternative)
  | Iete (liste, consequent, alternative) ->
    "if " ^ (print_term liste) ^ " == [] then " ^ (print_term consequent) ^ " else " ^ (print_term alternative)
  | Fix x -> "(fix " ^ print_term x ^ ")"
  | Let (x, e1, e2) -> "let " ^ x ^ " = " ^ print_term e1 ^ " in (" ^ print_term e2 ^ ")"
  | Head x -> "head " ^ print_term x
  | Tail x -> "tail " ^ print_term x

let compteur_var : int ref = ref 0

let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X"^(string_of_int !compteur_var)

let rec variablesLibres (t : pterm) : string list =
  match t with
  | Var x -> [x]
  | App (t1, t2) -> (variablesLibres t1) @ (variablesLibres t2)
  | Abs (x, t1) -> List.filter (fun y -> y <> x) (variablesLibres t1)
  | _ -> []

let rec substitutions (x : string) (n: pterm) (t : pterm) : pterm =
  match t with
  | Var k -> if (k = x) then n else Var k
  | App (t1, t2) -> App(substitutions x n t1, substitutions x n t2)
  | Abs (k, tt) -> if (k = x) then Abs(k, tt) else
        if (List.mem k (variablesLibres n)) then
          let y' = nouvelle_var () in
          let tt' = substitutions k (Var y') tt in
          Abs(y', substitutions x n tt')
        else
          Abs (k, substitutions x n tt)
  | Addition (t1, t2) -> Addition (substitutions x n t1, substitutions x n t2)
  | Soustraction (t1, t2) -> Soustraction (substitutions x n t1, substitutions x n t2)
  | Cons (t, ts) -> Cons (substitutions x n t, substitutions x n ts)
  | Fix t -> Fix (substitutions x n t)
  | Izte (cond, then_branch, else_branch) ->
    Izte (substitutions x n cond, substitutions x n then_branch, substitutions x n else_branch)
  | Iete (cond, then_branch, else_branch) ->
    Iete (substitutions x n cond, substitutions x n then_branch, substitutions x n else_branch)
  | Let (k, e1, e2) -> Let(k, (substitutions x n e1), (substitutions x n e2))
  | Head ts -> Head (substitutions x n ts)
  | Tail ts -> Tail (substitutions x n ts)
  | _ -> t

let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App(alphaconv t1, alphaconv t2)
  | Abs (x, tt) -> let x' = (nouvelle_var ()) in
      Abs (x', alphaconv (substitutions x (Var x') tt))
  | _ -> t

let rec is_value (t : pterm) : bool =
  match t with
  | Var _ -> true
  | Abs(_, _) -> true
  | App(Var _, v) when is_value v -> true
  | Addition(_, _) -> true
  | Soustraction(_, _) -> true
  | Entier _ -> true
  | Head _ -> true
  | Tail _ -> true
  | _ -> false

let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, t1) -> (
      match ltr_ctb_step t1 with
      | Some t1' -> Some (Abs (x, t1'))
      | None -> None)
  | App(t1, t2) -> (
    match ltr_ctb_step t1 with
    | Some t1' -> Some (App(t1', t2))
    | None -> match ltr_ctb_step t2 with
              | Some t2' -> Some (App(t1, t2'))
              | None -> (
                  match t1 with
                  | Abs(str, t') -> Some (substitutions str t2 t')
                  | _ -> None))
  | Entier x -> None
  | Addition (x, y) -> (
      match (x, y) with 
      | (Entier i, Entier k) -> Some (Entier (i + k))
      | (Entier i, k) -> (
          match ltr_ctb_step k with
          | Some k' -> Some (Addition (Entier i, k'))
          | None -> None)
      | (i, Entier k) -> (
          match ltr_ctb_step i with
          | Some i' -> Some (Addition (i', Entier k))
          | None -> None)
      | (i, k) -> (
          match ltr_ctb_step i, ltr_ctb_step k with
          | Some i', Some k' -> Some (Addition (i', k'))
          | Some i', None -> Some (Addition (i', k))
          | None, Some k' -> Some (Addition (i, k'))
          | None, None -> None))
  | Soustraction (x, y) -> (
      match (x, y) with 
      | (Entier i, Entier k) -> Some (Entier (i - k))
      | (Entier i, k) -> (
          match ltr_ctb_step k with
          | Some k' -> Some (Soustraction (Entier i, k'))
          | None -> None)
      | (i, Entier k) -> (
          match ltr_ctb_step i with
          | Some i' -> Some (Soustraction (i', Entier k))
          | None -> None)
      | (i, k) -> (
          match ltr_ctb_step i, ltr_ctb_step k with
          | Some i', Some k' -> Some (Soustraction (i', k'))
          | Some i', None -> Some (Soustraction (i', k))
          | None, Some k' -> Some (Soustraction (i, k'))
          | None, None -> None))
  | Nil -> None
  | Cons(x, xs) -> (
    let next = (ltr_ctb_step x) in
    match next with
    | Some reduction -> Some (Cons (reduction, xs))
    | None -> let nextXS = (ltr_ctb_step xs) in
        match nextXS with
        | Some reductionXS -> Some (Cons(x, reductionXS))
        | None -> None)
  | Head x -> (
    let next = (ltr_ctb_step x) in
    match next with
    | Some red -> Some (Head(red))
    | None -> match x with
      | Cons (xt, _) -> Some xt
      | _ -> None)
  | Tail x -> (
    let next = (ltr_ctb_step x) in
    match next with
    | Some red -> Some (Tail(red))
    | None -> match x with
      | Cons (xt, Nil) -> Some xt
      | Cons (xt, xts) -> (ltr_ctb_step (Tail(xts)))
      | _ -> None)
  | Izte (Entier 0, consequent, _) -> Some consequent
  | Izte (Entier _, _, alternative) -> Some alternative
  | Izte (x, consequent, alternative) -> (
      match ltr_ctb_step x with
      | Some x' -> Some (Izte (x', consequent, alternative))
      | None -> None)
  | Iete (Nil, consequent, _) -> Some consequent
  | Iete (Cons(_, _), _, alternative) -> Some alternative
  | Iete (x, consequent, alternative) -> (
      match ltr_ctb_step x with
      | Some x' -> Some (Iete (x', consequent, alternative))
      | None -> None)
  | Fix f -> (
    match f with
    | Abs (x, body) -> Some (substitutions x (Fix f) body)
    | _ -> failwith "Fix doit être appliqué à une abstraction")
  | Let(x, e1, e2) -> Some (substitutions x e1 e2)

let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_ctb_step t with
  | Some t' -> ltr_cbv_norm t'
  | None -> t

let rec ltr_cbv_norm' (t : pterm) (n : int) : pterm option =
  if n = 0 then None else
    match ltr_ctb_step t with
    | Some t' -> ltr_cbv_norm' t' (n - 1)
    | None -> Some t

type ptype =
    TypeVar of string
  | Arr of ptype * ptype
  | N
  | Liste of ptype
  | Forall of string * ptype

let rec print_type (t : ptype) : string =
  match t with
    TypeVar x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | N -> "entier"
  | Liste x -> "Liste " ^ print_type x
  | Forall (var, t') -> "∀" ^ var ^ ". " ^ print_type t'

type eqTypage = (ptype * ptype) list

type env = (string * ptype) list

let rec getInEnv (e : env) (x : string) : ptype option =
  match e with
  | [] -> None
  | (s, t) :: envs -> if x = s then Some t else getInEnv envs x

let compteur_var_t : int ref = ref 0

let nouvelle_var_t () : string =
  compteur_var_t := !compteur_var_t + 1;
  "T" ^ string_of_int !compteur_var_t

let rec genereTypage (t : pterm) (e : env) (cible : ptype) : eqTypage =
  match t with
  | Var x ->
      (match getInEnv e x with
      | Some typeV -> [(cible, typeV)]
      | None -> failwith "WIP"
      )
  | Abs(x, t') ->
      let ta = match getInEnv e x with
        | Some t -> t
        | None -> TypeVar (nouvelle_var_t ())
      in
      let tr = TypeVar (nouvelle_var_t ()) in
      (cible, Arr (ta, tr)) :: (genereTypage t' ((x, ta) :: e) tr)
  | App (t1, t2) ->
      let ta = TypeVar (nouvelle_var_t ()) in
      let t1Sys = genereTypage t1 e (Arr (ta, cible)) in
      let t2Sys = genereTypage t2 e ta in
      t1Sys @ t2Sys
  | Entier _ -> [(cible, N)]
  | Addition (x, y) -> (genereTypage x e N) @ (genereTypage y e N) @ [(cible, N)]
  | Soustraction (x, y) -> (genereTypage x e N) @ (genereTypage y e N) @ [(cible, N)]
  | Nil -> [(cible, Liste (TypeVar (nouvelle_var_t ())))]
  | Cons (x, xs) ->
      let tElem = TypeVar (nouvelle_var_t ()) in
      let tListe = Liste tElem in
      (genereTypage x e tElem) @ (genereTypage xs e tListe) @ [(cible, tListe)]
  | Head x ->
      let tElem = TypeVar (nouvelle_var_t ()) in
      let tListe = Liste tElem in
      (genereTypage x e tListe) @ [(cible, tElem)]
  | Tail x ->
      let tElem = TypeVar (nouvelle_var_t ()) in
      let tListe = Liste tElem in
      (genereTypage x e tListe) @ [(cible, tElem)]
  | Izte (cond, consq, alt) -> (* Environnement généralisé, on ajoute le truc à l'env e *)
    (genereTypage cond e N) @ (genereTypage consq e cible) @ (genereTypage alt e cible)
  | Iete (cond, consq, alt) -> (* Environnement généralisé, on ajoute le truc à l'env e *)
    let tElem = TypeVar (nouvelle_var_t ()) in
    let tListe = Liste tElem in
    (genereTypage cond e tListe) @ (genereTypage consq e cible) @ (genereTypage alt e cible)

let rec occurCheck (var : ptype) (unType : ptype) : bool =
  match var with
  | TypeVar x ->
      (match unType with
      | TypeVar t -> (x = t)
      | Arr(t1, t2) -> (occurCheck var t1) || (occurCheck var t2)
      | N -> false
      | Liste t -> (occurCheck var t))
  | _ -> failwith "L'occurCheck ne peut être appelé que sur une variable de type"

let rec egStructurelle (t1 : ptype) (t2 : ptype) : bool =
  match t1, t2 with
  | (N, N) -> true
  | (TypeVar x, TypeVar y) -> x = y
  | (Arr (t1, t2), Arr(t3, t4)) -> (egStructurelle t1 t3) && (egStructurelle t2 t4)
  | (Liste x, Liste y) -> egStructurelle x y
  | (_,_) -> false

type substitutions = (string * ptype) list

let rec substitutDansType (subst : substitutions) (t : ptype) : ptype =
  match t with
  | TypeVar x ->
      (match List.assoc_opt x subst with
       | Some ty -> substitutDansType subst ty
       | None -> t)
  | Arr (t1, t2) ->
      Arr (substitutDansType subst t1, substitutDansType subst t2)
  | N -> N
  | Liste x -> Liste (substitutDansType subst x)

let substitutDansEquation (subst : substitutions) (eqs : eqTypage) : eqTypage =
  List.map (fun (t1, t2) -> (substitutDansType subst t1, substitutDansType subst t2)) eqs

let unification_step (equations : eqTypage) (subst : substitutions) : (eqTypage * substitutions) option =
  match equations with
  | [] -> None
  | (t1, t2)::ts ->
      let t1' = substitutDansType subst t1 in
      let t2' = substitutDansType subst t2 in
      if egStructurelle t1' t2' then
        Some (ts, subst)
      else
        match (t1', t2') with
        | (TypeVar x, t) | (t, TypeVar x) ->
            if occurCheck (TypeVar x) t then
              None
            else
              let subst' = (x, t)::subst in
              let ts' = substitutDansEquation [(x, t)] ts in
              Some (ts', subst')
        | (Arr (l1, r1), Arr (l2, r2)) ->
            Some ((l1, l2)::(r1, r2)::ts, subst)
        | (N, N) -> Some (ts, subst)
        | (Liste x, Liste t) -> Some ((x, t)::ts, subst)
        | _ -> None

let rec unifie (equations : eqTypage) (subst : substitutions) (fuel : int) : substitutions option =
  if fuel <= 0 then None
  else
    match unification_step equations subst with
    | None -> 
        if equations = [] then Some subst else None
    | Some (nouvEquations, nouvSubstitutions) ->
        unifie nouvEquations nouvSubstitutions (fuel - 1)

let inference (t : pterm) (e : env) : ptype option =
  let ta = TypeVar (nouvelle_var_t ()) in
  let systeme = genereTypage t e ta in
  match unifie systeme [] 1000 with
  | Some subst ->
      let typeInfere = substitutDansType subst ta in
      Some typeInfere
  | None -> None

let print_inference_result term env =
  Printf.printf "Terme : %s\n" (print_term term);
  match inference term env with
  | Some typeInfere ->
      Printf.printf "Type inféré : %s\n\n" (print_type typeInfere);
  | None -> Printf.printf "Le terme n'est pas typable ou l'unification a échoué.\n\n"




let () =
  Printf.printf "===== TESTS D'INFERENCE DE TYPE POUR Izte ET Iete =====\n";

  (* Fonction pour tester et afficher les résultats *)
  let test_inference term env description =
    Printf.printf "Test : %s\n" description;
    Printf.printf "Terme : %s\n" (print_term term);
    match inference term env with
    | Some typeInfere -> Printf.printf "Type inféré : %s\n\n" (print_type typeInfere)
    | None -> Printf.printf "Échec de l'inférence de type.\n\n"
  in

  (* Tests pour Izte *)

  (* Test 1 : Izte avec condition 0 *)
  let term1 = Izte (Entier 0, Entier 42, Entier 24) in
  test_inference term1 [] "Izte avec condition 0 (entiers dans les branches)";

  (* Test 2 : Izte avec condition calculée *)
  let term2 = Izte (Addition (Entier 1, Entier (-1)), Entier 10, Entier 20) in
  test_inference term2 [] "Izte avec condition calculée";

  (* Test 3 : Izte avec condition et branches abstraites *)
  let term3 = Izte (Entier 0, Abs ("x", Addition (Var "x", Entier 1)), Abs ("y", Soustraction (Var "y", Entier 2))) in
  test_inference term3 [] "Izte avec condition 0 et branches abstraites";

  (* Test 4 : Izte avec condition non-entière *)
  let term4 = Izte (Nil, Entier 1, Entier 2) in
  test_inference term4 [] "Izte avec condition non-entière (liste)";

  (* Tests pour Iete *)

  (* Test 5 : Iete avec liste vide *)
  let term5 = Iete (Nil, Entier 1, Entier 0) in
  test_inference term5 [] "Iete avec liste vide";

  (* Test 6 : Iete avec liste non vide *)
  let term6 = Iete (Cons (Entier 42, Nil), Entier 1, Entier 0) in
  test_inference term6 [] "Iete avec liste non vide";

  (* Test 7 : Iete avec liste complexe et branches abstraites *)
  let term7 = Iete (Cons (Entier 1, Cons (Entier 2, Nil)), Abs ("x", Soustraction (Var "x", Entier 5)), Entier 100) in
  test_inference term7 [] "Iete avec liste complexe et branches abstraites";

  (* Test 8 : Iete avec liste calculée *)
  let term8 = Iete (Cons (Addition (Entier 1, Entier 1), Nil), Entier 10, Entier 20) in
  test_inference term8 [] "Iete avec liste calculée";

  (* Test 9 : Iete avec type mismatch dans les branches *)
  let term9 = Iete (Cons (Entier 1, Nil), Entier 42, Abs ("x", Var "x")) in
  test_inference term9 [] "Iete avec mismatch de types entre les branches";

  Printf.printf "===== FIN DES TESTS =====\n";

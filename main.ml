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
  | Unit
  | Deref of pterm
  | Ref of pterm
  | Assign of pterm * pterm

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
  | Unit -> "()"
  | Deref e -> "!(" ^ print_term e ^ ")"
  | Ref e -> "Ref " ^ print_term e
  | Assign (e1, e2)  -> print_term e1 ^ " := " ^ print_term e2

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
  | Deref e -> Deref (substitutions x n e)
  | Ref e -> Ref (substitutions x n e)
  | Assign (e1, e2) -> Assign (substitutions x n e1, substitutions x n e2)
  | _ -> t

(* Alpha-conversion (inutilisée) *)
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

type memoire = (string * pterm) list

let regions : memoire ref = ref []

let ajoutMemoire (id : string) (value : pterm) : unit =
  regions := (id, value) :: !regions

let recupererMemoire (region : string) : pterm =
  match List.assoc_opt region !regions with
  | Some value -> value
  | None -> failwith "region introuvable"

let rec modifierMemoire (region : string) (value : pterm) : unit =
  regions := List.map (fun (r, v) -> if r = region then (r, value) else (r, v)) !regions  

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
  | Let(x, e1, e2) -> (
    match ltr_ctb_step e1 with
    | Some e1' -> Some (Let(x, e1', e2))
    | None -> (ltr_ctb_step (substitutions x e1 e2)))
  | Unit -> None
  | Deref e -> (
      match ltr_ctb_step e with
      | Some e' -> Some (Deref e')
      | None -> (
          match e with
          | Var rho -> Some (recupererMemoire rho)
          | _ -> failwith "Tentative de déréférencement sur un terme invalide.")
  )
  | Ref e -> (
    match ltr_ctb_step e with
    | Some e' -> Some (Ref e')
    | None -> 
      let rho = nouvelle_var () in
      ajoutMemoire rho e;
      Some (Var rho))
  | Assign (e1, e2) -> (
    match ltr_ctb_step e1 with
    | Some e1' -> Some (Assign (e1', e2))
    | None -> (
      match ltr_ctb_step e2 with
      | Some e2' -> Some (Assign (e1, e2'))
      | None -> (
        match e1 with 
        | Var rho -> 
          (modifierMemoire rho e2);
          Some Unit
        | _ -> failwith "e1 n'est pas une région initialisée"
      )
    )
  )


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
  | UnitType
  | RefType of ptype

let rec print_type (t : ptype) : string =
  match t with
    TypeVar x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | N -> "entier"
  | Liste x -> "Liste " ^ print_type x
  | Forall (var, t') -> "∀" ^ var ^ ". " ^ print_type t'
  | UnitType -> "UnitType"
  | RefType x -> "RefType " ^ print_type x

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

(* Récupère toutes les variables de type libres dans un type *)
let rec variablesTypeLibres (t : ptype) : string list =
  match t with
  | TypeVar x -> [x]
  | Arr (t1, t2) -> (variablesTypeLibres t1) @ (variablesTypeLibres t2)
  | N -> []
  | Liste t1 -> variablesTypeLibres t1
  | Forall (x, t1) -> List.filter (fun y -> y <> x) (variablesTypeLibres t1)
  | UnitType -> []
  | RefType t1 -> variablesTypeLibres t1

(* Récupère toutes les variables de type libres dans l'environnement *)
let rec variablesTypeEnv (e : env) : string list =
  match e with
  | [] -> []
  | (_, t)::rest -> (variablesTypeLibres t) @ (variablesTypeEnv rest)

(* Généralise un type *)
let generaliserType (t : ptype) (e : env) : ptype =
  let varDansT = variablesTypeLibres t in
  let varDansEnv = variablesTypeEnv e in
  let varsAGeneraliser = List.filter (fun v -> not (List.mem v varDansEnv)) varDansT in
  List.fold_left (fun acc var -> Forall(var, acc)) t varsAGeneraliser

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
  | Forall (x, t_body) ->
    let subst_without_x = List.remove_assoc x subst in
    Forall (x, substitutDansType subst_without_x t_body)
  | UnitType -> UnitType
  | RefType x -> RefType (substitutDansType subst x)

let substitutDansEquation (subst : substitutions) (eqs : eqTypage) : eqTypage =
  List.map (fun (t1, t2) -> (substitutDansType subst t1, substitutDansType subst t2)) eqs

let rec egStructurelle (t1 : ptype) (t2 : ptype) : bool =
  match t1, t2 with
  | (N, N) -> true
  | (TypeVar x, TypeVar y) -> x = y
  | (Arr (t1, t2), Arr(t3, t4)) -> (egStructurelle t1 t3) && (egStructurelle t2 t4)
  | (Liste x, Liste y) -> egStructurelle x y
  | (UnitType, UnitType) -> true
  | (RefType x, RefType y) -> egStructurelle x y
  | (_,_) -> false  

(* Vérifie si la variable var apparait dans untype *)
let rec occurCheck (var : ptype) (unType : ptype) : bool =
  match var with
  | TypeVar x ->
      (match unType with
      | TypeVar t -> (x = t)
      | Arr(t1, t2) -> (occurCheck var t1) || (occurCheck var t2)
      | N -> false
      | Liste t -> (occurCheck var t)
      | Forall (x', t') -> 
        if (x = x') then false (* Même string mais désignant des variables différentes *)
        else (occurCheck var t')
      | UnitType -> false
      | RefType t -> (occurCheck var t)
      )
  | _ -> failwith "L'occurCheck ne peut être appelé que sur une variable de type"

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
        | (Forall (var, t_body), t_other) ->
          (* Barendregtisation and opening of Forall type *)
          let fresh_var = nouvelle_var_t () in
          let t_body_renamed = substitutDansType [(var, TypeVar fresh_var)] t_body in
          let new_equation = (t_body_renamed, t_other) in
          Some (new_equation::ts, subst)
        | (t_other, Forall (var, t_body)) ->
          (* Barendregtisation and opening of Forall type *)
          let fresh_var = nouvelle_var_t () in
          let t_body_renamed = substitutDansType [(var, TypeVar fresh_var)] t_body in
          let new_equation = (t_other, t_body_renamed) in
          Some (new_equation::ts, subst)
        | (UnitType, UnitType) -> Some (ts, subst)
        | (RefType x, RefType t) -> Some ((x, t)::ts, subst)
        | _ -> None

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
  | Let (x, e1, e2) -> (match (inference e1 e) with
                      | Some t0 -> (genereTypage e2 ((x, (generaliserType t0 e))::e) cible) (* TODO: toujours la même cible ? *)
                      | None -> failwith "Erreur de typage de let")
  | Unit -> [(cible, UnitType)]
  | Deref x -> (match (inference x e) with
    | Some RefType(t0) -> [(cible, t0)]
    | _ -> failwith "Erreur de typage de DeRefType")
  | Ref x -> (match (inference x e) with
    | Some t0 -> [(cible, RefType(t0))]
    | None -> failwith "Erreur de typage de RefType")
  | Assign (x, y) -> (match (inference y e) with
    | Some t0 -> (genereTypage x e (RefType(t0))) @ [(cible, UnitType)]
    | None -> failwith "Erreur de typage de Assign")
  (* TODO : Utiliser les fonctions qui accèdent à la mémoire ? *)

and unifie (equations : eqTypage) (subst : substitutions) (fuel : int) : substitutions option =
  if fuel <= 0 then None
  else
    match unification_step equations subst with
    | None -> 
        if equations = [] then Some subst else None
    | Some (nouvEquations, nouvSubstitutions) ->
        unifie nouvEquations nouvSubstitutions (fuel - 1)

and inference (t : pterm) (e : env) : ptype option =
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
  Printf.printf "===== TESTS D'INFERENCE DE TYPE POUR Unit, Ref, Deref ET Assign =====\n\n";

  (* Fonction pour tester l'inférence de type et afficher les résultats *)
  let test_inference term env description =
    Printf.printf "=== Test : %s ===\n" description;
    Printf.printf "Terme : %s\n" (print_term term);
    match inference term env with
    | Some typeInfere -> Printf.printf "Type inféré : %s\n\n" (print_type typeInfere)
    | None -> Printf.printf "Échec de l'inférence de type.\n\n"
  in

  (* Test 1: Inférence sur Unit *)
  let term1 = Unit in
  test_inference term1 [] "Inférence sur Unit";

  (* Test 2: Inférence sur Ref *)
  let term2 = Ref (Entier 42) in
  test_inference term2 [] "Inférence sur Ref avec un entier";

  (* Test 3: Inférence sur Deref *)
  let term3 = Deref (Ref (Entier 100)) in
  test_inference term3 [] "Inférence sur Deref après Ref";

  (* Test 4: Inférence sur Assign *)
  let term4 = Assign (Ref (Entier 50), Entier 200) in
  test_inference term4 [] "Inférence sur Assign";

  (* Test 5: Inférence avec Let combiné avec Ref, Deref et Assign *)
  let term5 =
    Let ("x", Ref (Entier 10),
      Let ("_", Assign (Var "x", Entier 20),
        Deref (Var "x")))
  in
  test_inference term5 [] "Let combiné avec Ref, Assign et Deref";

  (* Test 6: Inférence avec plusieurs références *)
  let term6 =
    Let ("r1", Ref (Entier 30),
      Let ("r2", Ref (Entier 40),
        Let ("_", Assign (Var "r1", Entier 50),
          Addition (Deref (Var "r1"), Deref (Var "r2")))))
  in
  test_inference term6 [] "Let avec plusieurs références et opérations";

  (* Test 7: Inférence avec une liste de références *)
  let term7 =
    Let ("list_ref", Ref (Cons (Entier 1, Cons (Entier 2, Nil))),
      Let ("_", Assign (Var "list_ref", Cons (Entier 3, Nil)),
        Deref (Var "list_ref")))
  in
  test_inference term7 [] "Liste de références combinée avec Assign et Deref";

  (* Test 8: Inférence polymorphique avec Ref *)
  let term8 =
    Let ("id_ref", Abs ("x", Ref (Var "x")),
      App (Var "id_ref", Entier 42))
  in
  test_inference term8 [] "Fonction polymorphe créant une référence";

  (* Test 9: Inférence avec des références imbriquées *)
  let term9 =
    Let ("outer_ref", Ref (Ref (Entier 99)),
      Let ("_", Assign (Deref (Var "outer_ref"), Entier 100),
        Deref (Deref (Var "outer_ref"))))
  in
  test_inference term9 [] "Références imbriquées avec Assign et Deref";

  Printf.printf "===== FIN DES TESTS =====\n";

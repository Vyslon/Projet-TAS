type pterm =
    Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Entier of int
  | Addition of pterm * pterm
  | Soustraction of pterm * pterm 

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

let compteur_var : int ref = ref 0

let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X"^(string_of_int !compteur_var)

(* Donne la liste des variables libres dans le terme t *)
let rec variablesLibres (t : pterm) : string list =
  match t with
  | Var x -> [x]
  | App (t1, t2) -> (variablesLibres t1) @ (variablesLibres t2)
  | Abs (x, t1) -> List.filter (fun y -> y <> x) (variablesLibres t1)
  | _ -> []

(* On remplace dans t chaque occurence de x par n *)
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
  | _ -> t

(* alpha-conversion *)
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App(alphaconv t1, alphaconv t2)
  | Abs (x, tt) -> let x' = (nouvelle_var ()) in
      Abs (x', alphaconv (substitutions x (Var x') tt))
  | _ -> t

(* Cette fonction détermine si le terme est une valeur ("V" dans le CM 2 p.21) *)
let rec is_value (t : pterm) : bool =
  match t with
  | Var _ -> true
  | Abs(_, _) -> true
  | App(Var _, v) when is_value v -> true
  | _ -> false


(* Effectue une étape de la stratégie LtR CbV *)
let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (x, t1) ->
      begin match ltr_ctb_step t1 with
      | Some t1' -> Some (Abs (x, t1'))
      | None -> None
      end
  | App(t1, t2) -> (
      match ltr_ctb_step t1 with
      | Some t1' -> Some (App(t1', t2))
      | None -> match ltr_ctb_step t2 with
                | Some t2' -> Some (App(t1, t2'))
                | None ->
                    match t1, t2 with
                    | Abs(str, t'), valeur when is_value valeur -> Some (substitutions str valeur t')
                    | _ -> None)
  | Entier x -> None (* Déjà une valeur, donc rien à réduire *)
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


(* Appelle consécutivement ltr_ctb_step, pour normaliser un terme autant que possible *)
let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_ctb_step t with
  | Some t' -> ltr_cbv_norm t'
  | None -> t

(* Cette version prend en compte la divergence grâce à l'utilisation de fuel *)
let rec ltr_cbv_norm' (t : pterm) (n : int) : pterm option =
  if n = 0 then None else
    match ltr_ctb_step t with
    | Some t' -> ltr_cbv_norm' t' (n - 1)
    | None -> Some t

type ptype =
    TypeVar of string
  | Arr of ptype * ptype
  | Nat

let rec print_type (t : ptype) : string =
  match t with
    TypeVar x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat"

type eqTypage = (ptype * ptype) list

type env = (string * ptype) list

let rec getInEnv (e : env) (x : string) : ptype =
  match e with
    [] -> failwith ("Variable non présente dans l'environnement: "^x)
    | (s,t)::envs when x = s -> t
    | _::envs -> getInEnv envs x

let compteur_var_t : int ref = ref 0

(* Créer une variable de type fraîche *)
let nouvelle_var_t () : string =
  compteur_var_t := !compteur_var_t + 1;
  "T" ^ string_of_int !compteur_var_t

(* Génère un système d'équations de typage depuis un terme *)
let rec genereTypage (t : pterm) (e : env) (cible : ptype) : eqTypage =
  match t with
  | Var x ->
      let typeV = getInEnv e x in
      [(typeV, cible)]
  | Abs(x, t') ->
      let ta =
        try getInEnv e x
        with _ -> TypeVar (nouvelle_var_t ())
      in
      let tr = TypeVar (nouvelle_var_t ()) in
      (cible, Arr(ta, tr)) :: (genereTypage t' ((x, ta) :: e) tr)
  | App(t1, t2) ->
      let ta = TypeVar (nouvelle_var_t ()) in
      let t1Sys = genereTypage t1 e (Arr(ta, cible)) in
      let t2Sys = genereTypage t2 e ta in
      t1Sys @ t2Sys

(* Vérifie si une variable de type apparaît dans un type *)
let rec occurCheck (var : ptype) (unType : ptype) : bool =
  match var with
  | TypeVar x ->
      (match unType with
      | TypeVar t -> (x = t)
      | Arr(t1, t2) -> (occurCheck var t1) || (occurCheck var t2)
      | Nat -> false
      )
  | _ -> failwith "L'occurCheck ne peut être appelé que sur une variable de type"

(* Vérifie l'égalité structurelle entre 2 types *)
let rec egStructurelle (t1 : ptype) ( t2 : ptype) : bool =
  match t1, t2 with
  |(Nat, Nat) -> true
  | (TypeVar x, TypeVar y) -> x = y
  | (Arr (t1, t2), Arr(t3, t4)) -> (egStructurelle t1 t3) && (egStructurelle t2 t4)
  | (_,_) -> false

(* Représente une liste de substitutions  *)
type substitutions = (string * ptype) list

(* Applique une liste de substitutions à un type *)
let rec substitutDansType (subst : substitutions) (t : ptype) : ptype =
  match t with
  | TypeVar x ->
      (match List.assoc_opt x subst with
       | Some ty -> substitutDansType subst ty
       | None -> t)
  | Arr (t1, t2) ->
      Arr (substitutDansType subst t1, substitutDansType subst t2)
  | Nat -> Nat

(* Applique une liste de substitutions *)
let substitutDansEquation (subst : substitutions) (eqs : eqTypage) : eqTypage =
  List.map (fun (t1, t2) -> (substitutDansType subst t1, substitutDansType subst t2)) eqs

(* Applique une étape d'unification *)
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
              None (* Problème dans l'unification *)
            else
              let subst' = (x, t)::subst in
              let ts' = substitutDansEquation [(x, t)] ts in
              Some (ts', subst')
        | (Arr (l1, r1), Arr (l2, r2)) ->
            Some ((l1, l2)::(r1, r2)::ts, subst)
        | _ -> None

(* Réalise l'unification jusqu'à ce qu'on ait épuisé notre fuel ou notre système d'équations *)
let rec unifie (equations : eqTypage) (subst : substitutions) (fuel : int) : substitutions option =
  if fuel <= 0 then None
  else
    match unification_step equations subst with
    | None -> 
        if equations = [] then Some subst else None
    | Some (nouvEquations, nouvSubstitutions) ->
        unifie nouvEquations nouvSubstitutions (fuel - 1)

(* Infère le type de t si possible *)
let inference (t : pterm) (e : env) : ptype option =
  let ta = TypeVar (nouvelle_var_t ()) in
  let systeme = genereTypage t e ta in
  match unifie systeme [] 1000 with
  | Some subst ->
      let typeInfere = substitutDansType subst ta in
      Some typeInfere
  | None -> None

(* Fonction pour afficher les résultats de l'inférence de type *)
let print_inference_result term env typeAttendu =
  Printf.printf "Terme : %s\n" (print_term term);
  match inference term env with
  | Some typeInfere ->
      Printf.printf "Type inféré : %s\n" (print_type typeInfere);
      Printf.printf "Type attendu : %s\n\n" typeAttendu
  | None -> Printf.printf "Le terme n'est pas typable ou l'unification a échoué.\n\n"

let () =
  (* Define some sample terms *)
  let term1 = Addition (Entier 3, Entier 5) in
  let term2 = Soustraction (Entier 10, Entier 7) in
  let term3 = Addition (Entier 4, Soustraction (Entier 9, Entier 3)) in
  let term4 = Addition (term1, term2) in  (* Nested operations *)

  (* Define a fuel limit for the normalization function *)
  let fuel = 10 in

  (* Print and evaluate term1 *)
  Printf.printf "Evaluating term1: %s\n" (print_term term1);
  (match ltr_cbv_norm' term1 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term1\n\n");

  (* Print and evaluate term2 *)
  Printf.printf "Evaluating term2: %s\n" (print_term term2);
  (match ltr_cbv_norm' term2 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term2\n\n");

  (* Print and evaluate term3 *)
  Printf.printf "Evaluating term3: %s\n" (print_term term3);
  (match ltr_cbv_norm' term3 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term3\n\n");

  (* Print and evaluate term4 *)
  Printf.printf "Evaluating term4: %s\n" (print_term term4);
  (match ltr_cbv_norm' term4 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term4\n\n")

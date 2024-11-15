type pterm =
    Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Entier of int
  | Addition of pterm * pterm (* : Entier * Entier *)
  | Soustraction of pterm * pterm (* : Entier * Entier *)
  | Nil (* Liste vide *)
  | Cons of pterm * pterm
  | Izte of pterm * pterm * pterm (* : Entier * pterm * pterm *)
  | Iete of pterm * pterm * pterm (* : Nil | Cons (pterm * pterm) * pterm * pterm *)

let is_empty (liste : pterm) : bool = 
  (liste = Nil)

let is_zero (entier : pterm) : bool = 
  (entier = (Entier 0))

let is_liste (t : pterm) : bool =
  match t with
  | _ -> failwith "TODO"

let head (liste : pterm) : pterm =
  match liste with
  | Nil -> failwith "Liste vide"
  | Cons (x, _) -> x
  | _ -> failwith "Appel de la fonction head sur un terme qui n'est pas une liste"

let queue (liste : pterm) : pterm =
  match liste with
  | Nil -> failwith "Liste vide"
  | Cons (_, xs) -> xs
  | _ -> failwith "Appel de la fonction tail sur un terme qui n'est pas une liste"

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
(* TODO : modifier aussi *)
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
  | Addition(_, _) -> true
  | Soustraction(_, _) -> true
  | Entier _ -> true
  | _ -> false


(* Effectue une étape de la stratégie LtR CbV *)
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
  | Nil -> None
  | Cons(x, xs) -> (
    let next = (ltr_ctb_step x) in
    match next with
    | Some reduction -> Some (Cons (reduction, xs)) (* TODO : lancer le step sur xs ? *)
    | None -> let nextXS = (ltr_ctb_step xs) in
        match nextXS with
        | Some reductionXS -> Some (Cons(x, reductionXS))
        (* | None -> Some (Cons(x, xs)) *)
        | None -> None)
  | Izte(entier, consequent, alternative) -> (
    match (ltr_ctb_step entier) with
    | Some reduction -> Some (Izte(reduction, consequent, alternative))
    | None -> if (is_zero entier) then (
      let next = (ltr_ctb_step consequent) in
      match next with
      | Some cReduction -> Some (Izte(entier, cReduction, alternative))
      | None -> Some consequent
    ) else (
      let next = (ltr_ctb_step alternative) in
      match next with
      | Some aReduction -> Some (Izte(entier, consequent, aReduction))
      | None -> Some alternative
      ))
  | Iete(liste, consequent, alternative) -> (
    match (ltr_ctb_step liste) with
    | Some reduction -> Some (Iete(reduction, consequent, alternative))
    | None -> if (is_empty liste) then (
      let next = (ltr_ctb_step consequent) in
      match next with
      | Some cReduction -> Some (Iete(liste, cReduction, alternative))
      | None -> Some consequent
    ) else (
      let next = (ltr_ctb_step alternative) in
      match next with
      | Some aReduction -> Some (Iete(liste, consequent, aReduction))
      | None -> Some alternative
      ))

(* TODO : vérifier que le conséquent ou l'alternative soit None*)

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
  (* Définir des termes à tester *)

  (* Test 1 : Izte avec une condition vraie et des opérations complexes dans les branches *)
  let term1 = Izte (Entier 0, Soustraction (Entier 21, Entier 9), App (Abs ("x", Addition (Var "x", Entier 3)), Entier 2)) in

  (* Test 2 : Izte avec une condition fausse et une abstraction dans then et else *)
  let term2 = Izte (Entier 5, Abs ("x", Soustraction (Var "x", Entier 1)), Abs ("y", Addition (Var "y", Entier 42))) in

  (* Test 3 : Izte avec une condition calculée et une liste dans les branches *)
  let term3 = Izte (Soustraction (Entier 3, Entier 3), Cons (Entier 1, Nil), Cons (Entier 2, Cons (Entier 3, Nil))) in

  (* Test 4 : Izte avec une addition calculée et une application *)
  let term4 = Izte (Addition (Entier 1, Entier (-1)), App (Abs ("z", Soustraction (Var "z", Entier 2)), Entier 8), Entier 600) in

  (* Test 5 : Iete avec une liste vide et des abstractions dans les branches *)
  let term5 = Iete (Nil, Abs ("x", Var "x"), App (Abs ("y", Addition (Var "y", Entier 5)), Entier 10)) in

  (* Test 6 : Iete avec une liste non vide et une soustraction dans else *)
  let term6 = Iete (Cons (Entier 42, Nil), Entier 1, Soustraction (Entier 50, Entier 8)) in

  (* Test 7 : Iete avec une liste construite dynamiquement et une application *)
  let term7 = Iete (Cons (Entier 1, Cons (Entier 2, Nil)), Entier 10, App (Abs ("x", Addition (Var "x", Entier 5)), Entier 3)) in

  (* Test 8 : Iete avec une liste construite avec évaluation et une abstraction *)
  let term8 = Iete (Cons (Addition (Entier 1, Entier 1), Nil), Abs ("x", Addition (Var "x", Entier 100)), Entier 200) in

  (* Test 9 : Izte avec une condition et une liste complexe dans then/else *)
  let term9 = Izte (Entier 0, Cons (Entier 10, Cons (Entier 20, Nil)), Cons (Entier 30, Nil)) in

  (* Test 10 : Iete avec une liste imbriquée et une abstraction complexe *)
  let term10 = Iete (Cons (Entier 1, Cons (Entier 2, Cons (Entier 3, Nil))), Abs ("x", App (Abs ("y", Addition (Var "x", Var "y")), Entier 5)), (Addition(Entier 1, Entier 3))) in

  (* Définir une limite de carburant pour l'évaluation *)
  let fuel = 100 in

  (* Fonction pour tester et afficher les résultats *)
  let test term description =
    Printf.printf "Test : %s\n" description;
    Printf.printf "Terme initial : %s\n" (print_term term);
    match ltr_cbv_norm' term fuel with
    | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
    | None -> Printf.printf "Échec de l'évaluation ou divergence.\n\n"
  in

  (* Lancer les tests *)
  test term1 "Izte (0 == 0) avec soustraction et application";
  test term2 "Izte (5 == 0) avec abstraction dans then et else";
  test term3 "Izte ((3 - 3) == 0) avec liste dans then et else";
  test term4 "Izte ((1 + (-1)) == 0) avec application dans then";
  test term5 "Iete (liste vide) avec abstraction et application";
  test term6 "Iete (liste non vide) avec soustraction dans else";
  test term7 "Iete (liste dynamique) avec application dans else";
  test term8 "Iete (liste avec évaluation) avec abstraction dans then";
  test term9 "Izte (0 == 0) avec liste complexe dans then et else";
  test term10 "Iete (liste imbriquée) avec abstraction complexe";

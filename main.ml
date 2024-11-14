type pterm =
    Var of string
  | App of pterm * pterm
  | Abs of string * pterm

let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ (print_term t) ^ ")"

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

(* On remplace dans t chaque occurence de x par n *)
let rec substitution (x : string) (n: pterm) (t : pterm) : pterm =
  match t with
  | Var k -> if (k = x) then n else Var k
  | App (t1, t2) -> App(substitution x n t1, substitution x n t2)
  | Abs (k, tt) -> if (k = x) then Abs(k, tt) else
        if (List.mem k (variablesLibres n)) then
          let y' = nouvelle_var () in
          let tt' = substitution k (Var y') tt in
          Abs(y', substitution x n tt')
        else
          Abs (k, substitution x n tt)

(* alpha-conversion *)
let rec alphaconv (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App(alphaconv t1, alphaconv t2)
  | Abs (x, tt) -> let x' = (nouvelle_var ()) in
      Abs (x', alphaconv (substitution x (Var x') tt))

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
  | App(t1, t2) ->
      match ltr_ctb_step t1 with
      | Some t1' -> Some (App(t1', t2))
      | None -> match ltr_ctb_step t2 with
                | Some t2' -> Some (App(t1, t2'))
                | None ->
                    match t1, t2 with
                    | Abs(str, t'), valeur when is_value valeur -> Some (substitution str valeur t')
                    | _ -> None

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

(* génère des équations de typage à partir d’un terme *)
let rec genereTypage (t : pterm) (e : env) (cible : ptype) : eqTypage =
  match t with
  | Var x -> let typeV = getInEnv e x in [(typeV, cible)]
  | Abs(x, t') ->
      let nomTa = nouvelle_var_t () in
      let ta = TypeVar nomTa in
      let nomTr = nouvelle_var_t () in
      let tr = TypeVar nomTr in
      (cible, Arr(ta, tr))::(genereTypage t' ((x, ta)::e) tr)
  | App(t1, t2) ->
      let nomTa = nouvelle_var_t () in
      let ta = TypeVar nomTa in
      let t1' = genereTypage t1 e (Arr(ta, cible)) in
      let t2' = genereTypage t2 e ta in
      t1'@t2'

(* vérifie si une variable appartient à un type *)
let rec occurCheck (var : ptype) (unType : ptype) : bool =
  match var with
  | TypeVar x ->
      (match unType with
      | TypeVar t -> (x = t)
      | Arr(t1, t2) -> (occurCheck var t1) || (occurCheck var t2)
      | Nat -> false
      )
  | _ -> failwith "L'occurCheck ne peut être appelé que sur une variable de type"

(* substitue une variable de type par un type à l’intérieur d’un autre type *)
let rec subTypeVarType (var : ptype) (unType : ptype) (unAutreType : ptype) : ptype =
  match var with
  | TypeVar x ->
      (match unAutreType with
      | TypeVar t -> if (x = t) then unType else TypeVar t
      | Arr(t1, t2) -> Arr((subTypeVarType var unType t1), (subTypeVarType var unType t2))
      | Nat -> Nat
      )
  | _ -> failwith "La substitution de type ne peut être appelée que sur une variable de type"

(* substitue une variable de type par un type partout dans un système d’équation *)
let rec subTypeVarEquation (var : ptype) (unType : ptype) (systeme : eqTypage) : eqTypage =
  match systeme with
  | [] -> []
  | (t1, t2)::ts ->
      ((subTypeVarType var unType t1), (subTypeVarType var unType t2))::(subTypeVarEquation var unType ts)

let rec egalite_type (t1 : ptype) ( t2 :ptype) : bool =
  match t1,t2 with
  | TypeVar s1, TypeVar s2 -> s1 = s2
  | Arr (t11,t12), Arr(t21,t22) -> (egalite_type t11 t21) && (egalite_type t12 t22)
  | Nat,Nat -> true
  | _,_ -> false

(* Define substitution type *)
type substitution = (string * ptype) list

(* Apply substitution to a type *)
let rec apply_subst_to_type (subst : substitution) (t : ptype) : ptype =
  match t with
  | TypeVar x ->
      (match List.assoc_opt x subst with
       | Some ty -> apply_subst_to_type subst ty
       | None -> t)
  | Arr (t1, t2) ->
      Arr (apply_subst_to_type subst t1, apply_subst_to_type subst t2)
  | Nat -> Nat

(* Apply substitution to equations *)
let apply_subst_to_equations (subst : substitution) (eqs : eqTypage) : eqTypage =
  List.map (fun (t1, t2) -> (apply_subst_to_type subst t1, apply_subst_to_type subst t2)) eqs

(* Unification function *)
let rec unify (equations : eqTypage) (subst : substitution) : substitution option =
  match equations with
  | [] -> Some subst
  | (t1, t2)::rest ->
      let t1 = apply_subst_to_type subst t1 in
      let t2 = apply_subst_to_type subst t2 in
      if egalite_type t1 t2 then
        unify rest subst
      else
        match (t1, t2) with
        | (TypeVar x, t) | (t, TypeVar x) ->
            if occurCheck (TypeVar x) t then
              None  (* Occurs check failed *)
            else
              let subst' = (x, t)::subst in
              let rest' = apply_subst_to_equations [(x, t)] rest in
              unify rest' subst'
        | (Arr (l1, r1), Arr (l2, r2)) ->
            unify ((l1, l2)::(r1, r2)::rest) subst
        | _ -> None  (* Unification failed *)

let rec print_substitution (subst : substitution) : string =
  match subst with
  | [] -> ""
  | (x, t)::rest -> x ^ " = " ^ (print_type t) ^ "\n" ^ (print_substitution rest)

(* Inference function *)
let inference (t : pterm) (e : env) : ptype option =
  let ta = TypeVar (nouvelle_var_t ()) in
  let systeme = genereTypage t e ta in
  match unify systeme [] with
  | Some subst ->
      let inferred_type = apply_subst_to_type subst ta in
      (* For debugging: print the final substitutions *)
      let _ = Printf.printf "Substitutions finales :\n%s" (print_substitution subst) in
      Some inferred_type
  | None -> None

(* Fonction pour afficher les résultats de l'inférence de type *)
let print_inference_result term env expected_type =
  Printf.printf "Terme : %s\n" (print_term term);
  match inference term env with
  | Some inferred_type ->
      Printf.printf "Type inféré : %s\n" (print_type inferred_type);
      Printf.printf "Type attendu : %s\n\n" expected_type
  | None -> Printf.printf "Le terme n'est pas typable ou l'unification a échoué.\n\n"

(* Cas de test *)
let () =
  (* 1. Identité *)
  let id_term = Abs ("x", Var "x") in
  (* Résultat attendu : T -> T *)
  print_inference_result id_term [] "(T -> T)";

  (* 2. Application de l'identité à y *)
  let app_id_y = App (id_term, Var "y") in
  (* Résultat attendu : même type que "y" (par exemple T) *)
  print_inference_result app_id_y [("y", TypeVar "T")] "T";

  (* 3. Fonction constante *)
  let const_term = Abs ("x", Abs ("y", Var "x")) in
  (* Résultat attendu : T1 -> (T2 -> T1) *)
  print_inference_result const_term [] "(T1 -> (T2 -> T1))";

  (* 4. Application de la fonction constante à z et w *)
  let const_app = App (App (const_term, Var "z"), Var "w") in
  (* Résultat attendu : type de "z" (par exemple T3) *)
  print_inference_result const_app [("z", TypeVar "T3"); ("w", TypeVar "T4")] "T3";

  (* 5. Combinator Omega (divergence) *)
  let omega_term = App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))) in
  (* Résultat attendu : non typable ou boucle infinie *)
  print_inference_result omega_term [] "non typable";

  (* 6. Combinator S *)
  let s_term = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))) in
  (* Résultat attendu : (T -> U -> V) -> (T -> U) -> T -> V *)
  print_inference_result s_term [] "((T -> U -> V) -> (T -> U) -> T -> V)";

  (* 7. Combinator S K K combinator (identité) *)
  let k_term = Abs ("x", Abs ("y", Var "x")) in
  let skk_term = App (App (s_term, k_term), k_term) in
  (* Résultat attendu : T -> T (fonction identité) *)
  print_inference_result skk_term [] "(T -> T)";

  (* 8. Application de Nat *)
  let nat_app = Abs ("f", Abs ("x", App (Var "f", Var "x"))) in
  (* Résultat attendu : (Nat -> Nat) -> Nat -> Nat *)
  print_inference_result nat_app [("f", Arr (Nat, Nat)); ("x", Nat)] "((Nat -> Nat) -> Nat -> Nat)";

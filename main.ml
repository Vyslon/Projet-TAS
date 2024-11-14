type pterm = Var of string
| App of pterm * pterm
| Abs of string * pterm

let rec print_term (t : pterm) : string = 
  match t with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")" 
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ (print_term t) ^")"

let compteur_var : int ref = ref 0

let nouvelle_var () : string = compteur_var := !compteur_var + 1;
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

(* Cette foncton détermine si le terme est une valeur ("V" dans le CM 2 p.21) *)
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

type ptype = TypeVar of string 
| Arr of ptype * ptype 
| Nat

let rec print_type (t : ptype) : string = 
  match t with
    TypeVar x -> x (* TypeVar et pas Var pour éviter les conflits *)
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"

type eqTypage = (ptype * ptype) list

type env = (string * ptype) list

let rec getInEnv (e : env) (x : string) : ptype =
  match e with
    [] -> failwith "Variable non présente dans l'environnement"
    | (s,t)::envs when x = s -> t
    | _::envs -> getInEnv envs x

let compteur_var_t : int ref = ref 0

(* Créer une variable de type fraîche *)
let nouvelle_var_t () : string = compteur_var_t := !compteur_var_t + 1;
  "T" ^ string_of_int !compteur_var_t

(* génère des équations de typage à partir d’un terme *)
let rec genereTypage (t : pterm) (e : env) (cible : ptype) : eqTypage =
  match t with
  | Var x -> let typeV = getInEnv e x in [(typeV, cible)]
  | Abs(x, t') -> let nomTa = nouvelle_var_t () in
    let ta = TypeVar nomTa in
    let nomTr = nouvelle_var_t () in 
    let tr = TypeVar nomTr in
    (cible, Arr(ta, tr))::(genereTypage t' ((x, ta)::e) tr)
  | App(t1, t2) -> let nomTa = nouvelle_var_t () in
    let ta = TypeVar nomTa in 
    let nomTr = nouvelle_var_t () in 
    let tr = TypeVar nomTr in
    let t1' = (genereTypage t1 e (Arr(ta, tr))) in
    let t2' = (genereTypage t2 e ta) in
    t1'@t2'

(* vérifie si une variable appartient à un type *)
let rec occurCheck (var : ptype) (unType : ptype) : bool =
  match var with
  | TypeVar x -> (match unType with 
    | TypeVar t -> (x = t)
    | Arr(t1, t2) -> (occurCheck var t1) || (occurCheck var t2)
    | Nat -> false
  )
  | _ -> failwith "L'occurcheck ne peut être appelé que sur une variable de type"

(* substitue une variable de type par un type à l’intérieur d’un autre type *)
let rec subTypeVarType (var : ptype) (unType : ptype) (unAutreType : ptype) : ptype =
  match var with
  | TypeVar x -> (match unAutreType with
    | TypeVar t -> if (x = t) then unType else TypeVar t
    | Arr(t1, t2) -> Arr((subTypeVarType var unType t1), (subTypeVarType var unType t2))
    | Nat -> Nat
  )
  | _ -> failwith "La substitution de type ne peut être appelé que sur une variable de type"

(* substitue une variable de type par un type partout dans un système d’équation *)
let rec subTypeVarEquation (var : ptype) (unType : ptype) (systeme : eqTypage) : eqTypage =
  match var with
  | TypeVar x ->  (match systeme with
    | [] -> []
    | (t1, t2)::ts -> ((subTypeVarType var unType t1), (subTypeVarType var unType t2))::(subTypeVarEquation var unType ts)
  )
  | _ -> failwith "La substitution de type ne peut être appelé que sur une variable de type"

(* TODO:  vraiment nécessaire ? modifier si je le garde *)
let rec egalite_type (t1 : ptype) ( t2 :ptype) : bool = 
  match t1,t2 with
  | TypeVar s1, TypeVar s2 -> s1 = s2
  |(Arr (t11,t12)),(Arr(t21,t22)) -> (egalite_type t11 t21) && (egalite_type t12  t22)
  | Nat,Nat -> true 
  | _,_ -> false

(* Réalise une étape d'unification *)
let rec unification_step (systeme : eqTypage) : eqTypage =
  match systeme with
  | [] -> []
  | (t1, t2)::ts when egalite_type t1 t2 -> (unification_step ts)
  | (TypeVar x, t2)::ts when (not (occurCheck (TypeVar x) t2)) -> (TypeVar x, t2)::(unification_step (subTypeVarEquation (TypeVar x) t2 ts))
  | (t1, TypeVar x)::ts when (not (occurCheck (TypeVar x) t1)) -> (t1, TypeVar x)::(unification_step (subTypeVarEquation (TypeVar x) t1 ts))
  | (Arr(t1, t2), Arr(t3, t4))::ts -> unification_step ((t1, t3)::(t2, t4)::ts)
  | _ -> failwith "erreur d'unification"

(* Résout un système d’équation (avec du fuel à la place du timeout) *)
let rec unification (systeme : eqTypage) (n : int) : eqTypage option =
  if (n = 0) then None else
    let next_step = (unification_step systeme) in
    if (next_step = systeme) then Some systeme else unification next_step (n - 1)

(* let inference (t : pterm) (e : env) : ptype option =
  let ta = TypeVar "T" in
  let systeme = genereTypage t e ta in
  match unification systeme 1000 with
  | Some eq -> Some (findRes ta eq )
  | None -> None *)

(* Build a substitution mapping from unified equations *)
let build_substitution (equations : eqTypage) : eqTypage =
  List.fold_left (fun acc (t1, t2) ->
    match t1, t2 with
    | TypeVar x, ty when not (t1 = ty) -> (TypeVar x, ty) :: acc
    | ty, TypeVar x when not (t1 = ty) -> (TypeVar x, ty) :: acc
    | _ -> acc
  ) [] equations

(* Apply substitutions to a type *)
let rec apply_substitutions (subst : eqTypage) (t : ptype) : ptype =
  match t with
  | TypeVar x ->
      (match List.find_opt (fun (TypeVar y, _) -> x = y) subst with
       | Some (_, ty) -> apply_substitutions subst ty
       | None -> t)
  | Arr (t1, t2) ->
      Arr (apply_substitutions subst t1, apply_substitutions subst t2)
  | Nat -> Nat

(* Inference function *)
let inference (t : pterm) (e : env) : ptype option =
  let ta = TypeVar (nouvelle_var_t ()) in
  let systeme = genereTypage t e ta in
  match unification systeme 1000 with
  | Some unified_system ->
      let substitutions = build_substitution unified_system in
      let inferred_type = apply_substitutions substitutions ta in
      Some inferred_type
  | None -> None

(* Function to compare types structurally, considering all type variables equal *)
let rec types_equal t1 t2 =
  match t1, t2 with
  | TypeVar _, TypeVar _ -> true  (* Consider all type variables as equal *)
  | Arr (a1, b1), Arr (a2, b2) -> types_equal a1 a2 && types_equal b1 b2
  | Nat, Nat -> true
  | _, _ -> false

(* Main function to test the inference function *)
let test_inference () =
  Printf.printf "Testing type inference:\n\n";

  (* Define test cases: (description, term, environment, expected type option) *)
  let test_cases = [
    ("Identity function",
     Abs ("x", Var "x"),
     [],
     Some (Arr (TypeVar "_", TypeVar "_")));  (* Expected type *)

    ("Constant function",
     Abs ("x", Abs ("y", Var "x")),
     [],
     Some (Arr (TypeVar "_", Arr (TypeVar "_", TypeVar "_"))));  (* T1 -> (T2 -> T1) *)

    ("Application of identity function",
     App (Abs ("x", Var "x"), Var "y"),
     [("y", TypeVar "T0")],  (* y : T0 *)
     Some (TypeVar "T0"));  (* Expected type is T0 *)

    ("Omega function (divergence)",
     App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))),
     [],
     None);  (* Not typable *)
  ] in

  (* Run each test case *)
  List.iter (fun (desc, term, env, expected_type) ->
    Printf.printf "Test: %s\n" desc;
    Printf.printf "Term: %s\n" (print_term term);
    (match expected_type with
     | Some ty -> Printf.printf "Expected type: %s\n" (print_type ty)
     | None -> Printf.printf "Expected type: Not typable\n");
    match inference term env with
    | Some inferred_type ->
        Printf.printf "Inferred type: %s\n" (print_type inferred_type);
        (match expected_type with
         | Some expected_type_value ->
             let result = if types_equal inferred_type expected_type_value then "Success" else "Mismatch" in
             Printf.printf "Result: %s\n\n" result
         | None ->
             Printf.printf "Type inference succeeded, but expected failure.\nResult: Failure\n\n")
    | None ->
        (match expected_type with
         | None ->
             Printf.printf "Type inference failed as expected.\nResult: Success\n\n"
         | Some _ ->
             Printf.printf "Type inference failed unexpectedly.\nResult: Failure\n\n")
  ) test_cases

(* Entry point *)
let () = test_inference ()

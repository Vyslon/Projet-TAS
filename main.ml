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

(* TODO : modifier *)
(* Réalise une étape d'unification *)
let rec unification_step (systeme : eqTypage) : eqTypage =
  match systeme with
  | [] -> []
  | (t1, t2)::ts when egalite_type t1 t2 -> (unification_step ts)
  (* | (TypeVar x, t2)::ts when (not (occurCheck (TypeVar x) t2)) -> (subTypeVarEquation (TypeVar x) t2 ts)
  | (t1, TypeVar x)::ts when (not (occurCheck (TypeVar x) t1)) -> (subTypeVarEquation (TypeVar x) t1 ts) *)
  | (TypeVar x, t2)::ts when (not (occurCheck (TypeVar x) t2)) ->
    let queue_substituee = List.map (fun (a, b) -> (subTypeVarType (TypeVar x) t2 a, subTypeVarType (TypeVar x) t2 b)) ts in
              (TypeVar x, t2) :: unification_step queue_substituee
  | (t1, TypeVar x)::ts when (not (occurCheck (TypeVar x) t1)) ->
    let queue_substituee = List.map (fun (a, b) -> (subTypeVarType (TypeVar x) t1 a, subTypeVarType (TypeVar x) t1 b)) ts in
              (t1, TypeVar x) :: unification_step queue_substituee
  | (Arr(t1, t2), Arr(t3, t4))::ts -> unification_step ((t1, t3)::(t2, t4)::ts)
  | _ -> failwith "erreur d'unification"

(* Résout un système d’équation (avec du fuel à la place du timeout) *)
let rec unification (systeme : eqTypage) (n : int) : eqTypage option =
  if (n = 0) then None else
    let next_step = (unification_step systeme) in
    if (next_step = systeme) then Some systeme else unification next_step (n - 1)

(* Define the types and functions as before *)




(* Applique récursivement et complètement les substitutions finales à un type *)
let rec apply_substitutions (subst : eqTypage) (t : ptype) : ptype =
  match t with
  | TypeVar x ->
      (try 
        let replacement = List.assoc (TypeVar x) subst in
        apply_substitutions subst replacement  (* Résoudre récursivement *)
       with Not_found -> t)
  | Arr (t1, t2) -> Arr (apply_substitutions subst t1, apply_substitutions subst t2)
  | Nat -> Nat

let () =
  (* Fonction pour afficher un système d'équations de typage *)
  let print_systeme systeme =
    List.iter (fun (t1, t2) -> Printf.printf "%s = %s\n" (print_type t1) (print_type t2)) systeme;
    Printf.printf "\n"
  in

  (* Fonction pour afficher le type inféré après résolution *)
  let print_inference_result term env expected_type =
    Printf.printf "Terme : %s\n" (print_term term);
    let cible = TypeVar (nouvelle_var_t ()) in  (* Type cible initial *)
    let systeme = genereTypage term env cible in  (* Génération du système d'équations *)
    Printf.printf "Système d'équations généré :\n";
    print_systeme systeme;

    match unification systeme 1000 with
    | Some res -> 
        Printf.printf "Système d'équations après unification :\n";
        print_systeme res;
        
        (* Applique les substitutions pour obtenir le type final résolu *)
        let final_type = apply_substitutions res cible in
        Printf.printf "Type inféré : %s (attendu : %s)\n\n" (print_type final_type) expected_type
    | None -> Printf.printf "Le terme n'est pas typable ou l'unification a échoué.\n\n"
  in

  (* Cas de test pour l'inférence de type *)

  (* 1. Identité *)
  let id_term = Abs ("x", Var "x") in
  (* Résultat attendu : T -> T *)
  print_inference_result id_term [] "(T -> T)";
  
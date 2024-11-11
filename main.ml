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

let rec is_value (t : pterm) : bool = 
  match t with
  | Var _ -> true
  | Abs(_, _) -> true
  | App(Var _, v) when is_value v -> true
  | _ -> false

let rec ltr_ctb_step (t : pterm) : pterm option =
  match t with
  | Var _ -> None
  | Abs (_, _) -> None
  | App(t1, t2) -> 
      match ltr_ctb_step t1 with (* vérifier que t1 n'est pas une value? *)
      | Some t1' -> Some (App(t1', t2))
      | None -> match ltr_ctb_step t2 with
                | Some t2' -> Some (App(t1, t2'))
                | None ->   
                  match t1, t2 with
                  | Abs(str, t'), valeur when is_value valeur -> Some (substitution str valeur t')
                  | _ -> None

let rec ltr_cbv_norm (t : pterm) : pterm =
  match t with
  | Var x -> Var x
  | Abs (x, t') -> Abs (x, t')
  | App(t1, t2) -> match ltr_ctb_step (App(t1, t2)) with
                    | Some t' -> ltr_cbv_norm t'
                    | None -> App(t1, t2)

(* TODO:  Ecrire ensuite une version de cette fonction qui prend en compte la divergence (par exemple avec un timeout ) 
 https://stackoverflow.com/questions/70977947/how-to-efficiently-stop-a-function-after-a-certain-amount-of-time-in-ocaml
 => Fin de la question 6
*)

let () =
let term1 = App (Abs ("x", Var "x"), Var "y") in
let term2 = App (App (Abs ("x", Var "x"), Var "y"), Var "z") in
let term3 = App (App (Abs ("x", Abs ("y", Var "x")), Var "a"), Var "b") in
let term4 = App (App (App (Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))), Var "a"), Var "b"), Var "c") in
let omega = App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))) in

let test term name =
  Printf.printf "%s - Avant réduction : %s\n" name (print_term term);
  try
    let result = ltr_cbv_norm term in
    Printf.printf "%s - Après réduction : %s\n\n" name (print_term result)
  with _ ->
    Printf.printf "%s - Divergence détectée\n\n" name
in

(* Exécuter chaque test *)
test term1 "Test 1 (Identité simple)";
test term2 "Test 2 (Double application de l'identité)";
test term3 "Test 3 (Combinateur K)";
test term4 "Test 4 (Combinateur S appliqué)";
test omega "Test 5 (Application infinie Ω)";
                  
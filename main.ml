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
  (*| Abs (k, tt) -> Abs(k, substitution x n tt)*)
  | Abs (k, tt) -> if (k = x) then Abs(k, tt) else 
        if (List.mem k (variablesLibres n)) then
          let y' = nouvelle_var () in
          let tt' = substitution k (Var y') tt in
          Abs(y', substitution x n tt')
        else 
          Abs (k, substitution x n tt)
    
let rec alphaconv (t : pterm) : pterm = 
  match t with
  | Var x -> Var x
  | App (t1, t2) -> App(alphaconv t1, alphaconv t2)
  | Abs (x, tt) -> let x' = (nouvelle_var ()) in
      Abs (x', alphaconv (substitution x (Var x') tt))

let () =
(* Exemple de termes à utiliser pour les tests *)
let term1 = Abs ("x", Var "x") in
let term2 = Abs ("x", App (Var "x", Var "y")) in
let term3 = App (Abs ("x", Var "x"), Var "y") in
let term4 = Abs ("y", Abs ("x", App (Var "x", Var "y"))) in

(* Affichage des termes avant alpha-conversion *)
Printf.printf "Termes avant alpha-conversion :\n";
Printf.printf "term1 : %s\n" (print_term term1);
Printf.printf "term2 : %s\n" (print_term term2);
Printf.printf "term3 : %s\n" (print_term term3);
Printf.printf "term4 : %s\n\n" (print_term term4);

(* Appliquons l'alpha-conversion *)
let alpha1 = alphaconv term1 in
let alpha2 = alphaconv term2 in
let alpha3 = alphaconv term3 in
let alpha4 = alphaconv term4 in

(* Affichage des résultats après alpha-conversion *)
Printf.printf "Termes après alpha-conversion :\n";
Printf.printf "alpha1 : %s\n" (print_term alpha1);
Printf.printf "alpha2 : %s\n" (print_term alpha2);
Printf.printf "alpha3 : %s\n" (print_term alpha3);
Printf.printf "alpha4 : %s\n" (print_term alpha4);
    
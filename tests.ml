
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

let () =
  (* Test 1 : Application simple avec abstraction *)
  let term1 = App (Abs ("x", Var "x"), Var "y") in
  Printf.printf "Test 1 - Avant réduction : %s\n" (print_term term1);
  (match ltr_ctb_step term1 with
  | Some result -> Printf.printf "Test 1 - Après réduction : %s\n\n" (print_term result)
  | None -> Printf.printf "Test 1 - Aucun pas de réduction possible\n\n");

  (* Test 2 : Application d'une abstraction à une autre abstraction *)
  let term2 = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", Var "y")) in
  Printf.printf "Test 2 - Avant réduction : %s\n" (print_term term2);
  (match ltr_ctb_step term2 with
  | Some result -> Printf.printf "Test 2 - Après réduction : %s\n\n" (print_term result)
  | None -> Printf.printf "Test 2 - Aucun pas de réduction possible\n\n");

  (* Test 3 : Application avec alpha-conversion *)
  let term3 = App (Abs ("x", Abs ("y", App (Var "x", Var "y"))), Var "y") in
  Printf.printf "Test 3 - Avant réduction : %s\n" (print_term term3);
  (match ltr_ctb_step term3 with
  | Some result -> Printf.printf "Test 3 - Après réduction : %s\n\n" (print_term result)
  | None -> Printf.printf "Test 3 - Aucun pas de réduction possible\n\n");

  (* Test 4 : Pas de réduction possible (valeurs) *)
  let term4 = Abs ("x", App (Var "x", Var "x")) in
  Printf.printf "Test 4 - Avant réduction : %s\n" (print_term term4);
  (match ltr_ctb_step term4 with
  | Some result -> Printf.printf "Test 4 - Après réduction : %s\n\n" (print_term result)
  | None -> Printf.printf "Test 4 - Aucun pas de réduction possible\n\n");

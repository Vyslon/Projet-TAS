
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

  let () =
  let term1 = App (Abs ("x", Var "x"), Var "y") in
  let term2 = App (App (Abs ("x", Var "x"), Var "y"), Var "z") in
  let term3 = App (App (Abs ("x", Abs ("y", Var "x")), Var "a"), Var "b") in
  let term4 = App (App (App (Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))), Var "a"), Var "b"), Var "c") in
  let omega = App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))) in

  let fuel = 100000  (* Définir le nombre maximal d'étapes de réduction *) in

  let test term name =
    Printf.printf "%s - Avant réduction : %s\n" name (print_term term);
    match ltr_cbv_norm' term fuel with
    | Some result ->
        Printf.printf "%s - Après réduction : %s\n\n" name (print_term result)
    | None ->
        Printf.printf "%s - Impossible de réduire le terme dans les %d étapes (divergence possible).\n\n" name fuel
  in

  (* Exécuter chaque test *)
  test term1 "Test 1 (Identité simple)";
  test term2 "Test 2 (Double application de l'identité)";
  test term3 "Test 3 (Combinateur K)";
  test term4 "Test 4 (Combinateur S appliqué)";
  test omega "Test 5 (Application infinie Ω)";
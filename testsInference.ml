let () =
  (* 1. Identité *)
  let id_term = Abs ("x", Var "x") in
  (* Résultat attendu : T -> T *)
  print_inference_result id_term [] "(T -> T)";

  (* 2. Application de l'identité à y de type T *)
  let app_id_y = App (id_term, Var "y") in
  (* Résultat attendu : même type que "y" (par exemple T) *)
  print_inference_result app_id_y [("y", TypeVar "T")] "T";

  (* 3. K *)
  let const_term = Abs ("x", Abs ("y", Var "x")) in
  (* Résultat attendu : T1 -> (T2 -> T1) *)
  print_inference_result const_term [] "(T1 -> (T2 -> T1))";

  (* 4.K (z : T3) (w : T4)  *)
  let const_app = App (App (const_term, Var "z"), Var "w") in
  (* Résultat attendu : type de "z" (par exemple T3) *)
  print_inference_result const_app [("z", TypeVar "T3"); ("w", TypeVar "T4")] "T3";

  (* 5. Ω : divergence *)
  let omega_term = App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))) in
  (* Résultat attendu : non typable ou boucle infinie *)
  print_inference_result omega_term [] "non typable";

  (* 6. S *)
  let s_term = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))) in
  (* Résultat attendu : (T -> U -> V) -> (T -> U) -> T -> V *)
  print_inference_result s_term [] "((T -> U -> V) -> (T -> U) -> T -> V)";

  (* 7. S K K *)
  let k_term = Abs ("x", Abs ("y", Var "x")) in
  let skk_term = App (App (s_term, k_term), k_term) in
  (* Résultat attendu : T -> T (fonction identité) *)
  print_inference_result skk_term [] "(T -> T)";

  (* 8. Application de Nat *)
  let nat_app = Abs ("f", Abs ("x", App (Var "f", Var "x"))) in
  (* Résultat attendu : (Nat -> Nat) -> Nat -> Nat *)
  print_inference_result nat_app [("f", Arr (Nat, Nat)); ("x", Nat)] "((Nat -> Nat) -> Nat -> Nat)";


(* Tests typage entier, addition et soustraction *)
let () =
  (* Test 1 : Inférence de type pour un entier *)
  let term1 = Entier 42 in
  let env1 = [] in
  print_inference_result term1 env1;

  (* Test 2 : Inférence de type pour une addition *)
  let term2 = Addition (Entier 5, Entier 3) in
  let env2 = [] in
  print_inference_result term2 env2;

  (* Test 3 : Inférence de type pour une soustraction *)
  let term3 = Soustraction (Entier 10, Entier 4) in
  let env3 = [] in
  print_inference_result term3 env3;

  (* Test 4 : Inférence de type pour une fonction d'addition partielle *)
  let term4 = Abs ("x", Addition (Var "x", Entier 7)) in
  let env4 = [] in
  print_inference_result term4 env4;

  (* Test 5 : Inférence de type pour une fonction polymorphe *)
  let term5 = Abs ("x", Abs ("y", Addition (Var "x", Var "y"))) in
  let env5 = [] in
  print_inference_result term5 env5;

  Printf.printf "Tous les tests d'inférence de type sont terminés.\n";


(* Tests typage listes, head, tail*)
let () =
  Printf.printf "===== TESTS D'INFERENCE DE TYPE =====\n";

  (* Test 1 : Liste vide *)
  let term1 = Nil in
  let env1 = [] in
  Printf.printf "Test 1 : Liste vide\n";
  print_inference_result term1 env1;

  (* Test 2 : Liste avec un entier *)
  let term2 = Cons (Entier 1, Nil) in
  let env2 = [] in
  Printf.printf "Test 2 : Liste avec un entier\n";
  print_inference_result term2 env2;

  (* Test 3 : Liste avec plusieurs entiers *)
  let term3 = Cons (Entier 1, Cons (Entier 2, Nil)) in
  let env3 = [] in
  Printf.printf "Test 3 : Liste avec plusieurs entiers\n";
  print_inference_result term3 env3;

  (* Test 4 : Fonction retournant une liste *)
  let term4 = Abs ("x", Cons (Var "x", Nil)) in
  let env4 = [] in
  Printf.printf "Test 4 : Fonction retournant une liste\n";
  print_inference_result term4 env4;

  (* Test 5 : Fonction ajoutant un élément à une liste *)
  let term5 = Abs ("x", Abs ("y", Cons (Var "x", Var "y"))) in
  let env5 = [] in
  Printf.printf "Test 5 : Fonction ajoutant un élément à une liste\n";
  print_inference_result term5 env5;

  (* Test 6 : Application d'une fonction sur une liste *)
  let term6 = App (Abs ("x", Cons (Var "x", Nil)), Entier 42) in
  let env6 = [] in
  Printf.printf "Test 6 : Application d'une fonction sur une liste\n";
  print_inference_result term6 env6;

  (* Test 7 : Fonction qui construit une liste de deux éléments *)
  let term7 = Abs ("x", Abs ("y", Cons (Var "x", Cons (Var "y", Nil)))) in
  let env7 = [] in
  Printf.printf "Test 7 : Fonction qui construit une liste de deux éléments\n";
  print_inference_result term7 env7;

  (* Test 8 : Normalisation et typage d'une fonction qui concatène deux listes *)
  let term8 = Abs ("x", Abs ("y", App (App (Var "concat", Var "x"), Var "y"))) in
  let env8 = [("concat", Arr (Liste (TypeVar "T"), Arr (Liste (TypeVar "T"), Liste (TypeVar "T"))))] in
  Printf.printf "Test 8 : Normalisation et typage d'une fonction qui concatène deux listes\n";
  let norm_term8 = ltr_cbv_norm' term8 100 in
  (match norm_term8 with
  | Some t -> print_inference_result t env8
  | None -> Printf.printf "Échec de la normalisation.\n");

  (* Test 9 : Liste de listes *)
  let term9 = Cons (Cons (Entier 1, Nil), Cons (Cons (Entier 2, Nil), Nil)) in
  let env9 = [] in
  Printf.printf "Test 9 : Liste de listes\n";
  print_inference_result term9 env9;

  (* Test 10 : Head d'une liste d'entiers *)
  let term10 = Head (Cons (Entier 1, Nil)) in
  let env10 = [] in
  Printf.printf "Test 10 : Head d'une liste d'entiers\n";
  print_inference_result term10 env10;

  (* Test 11 : Head d'une liste polymorphe *)
  let term11 = Head (Var "x") in
  let env11 = [("x", Liste (TypeVar "T"))] in
  Printf.printf "Test 11 : Head d'une liste polymorphe\n";
  print_inference_result term11 env11;

  (* Test 12 : Tail d'une liste d'entiers *)
  let term12 = Tail (Cons (Entier 1, Cons (Entier 2, Nil))) in
  let env12 = [] in
  Printf.printf "Test 12 : Tail d'une liste d'entiers\n";
  print_inference_result term12 env12;

  (* Test 13 : Tail d'une liste polymorphe *)
  let term13 = Tail (Var "x") in
  let env13 = [("x", Liste (TypeVar "T"))] in
  Printf.printf "Test 13 : Tail d'une liste polymorphe\n";
  print_inference_result term13 env13;

  (* Test 14 : Fonction utilisant Head *)
  let term14 = Abs ("x", Head (Var "x")) in
  let env14 = [] in
  Printf.printf "Test 14 : Fonction utilisant Head\n";
  print_inference_result term14 env14;

  (* Test 15 : Fonction utilisant Tail *)
  let term15 = Abs ("x", Tail (Var "x")) in
  let env15 = [] in
  Printf.printf "Test 15 : Fonction utilisant Tail\n";
  print_inference_result term15 env15;

  Printf.printf "===== FIN DES TESTS =====\n";

(* Tests partie 3 *)
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


(* Tests inférence avec let *)
let () =
  Printf.printf "===== TESTS D'INFERENCE DE TYPE AVEC LET =====\n";

  (* Function to test and display inference results *)
  let test_inference term env description =
    Printf.printf "Test : %s\n" description;
    Printf.printf "Terme : %s\n" (print_term term);
    match inference term env with
    | Some typeInfere -> Printf.printf "Type inféré : %s\n\n" (print_type typeInfere)
    | None -> Printf.printf "Échec de l'inférence de type.\n\n"
  in

  (* Test 1: Simple Let with integer *)
  let term1 = Let ("x", Entier 5, Addition (Var "x", Entier 10)) in
  test_inference term1 [] "Let simple avec un entier";

  (* Test 2: Nested Let with multiple bindings *)
  let term2 =
    Let ("x", Entier 5,
      Let ("y", Soustraction (Var "x", Entier 2),
        Addition (Var "x", Var "y")))
  in
  test_inference term2 [] "Let imbriqué avec plusieurs bindings";

  (* Test 3: Let with a function definition *)
  let term3 =
    Let ("f", Abs ("x", Addition (Var "x", Entier 1)),
      App (Var "f", Entier 10))
  in
  test_inference term3 [] "Let avec une définition de fonction";

  (* Test 4: Let with polymorphism *)
  let term4 =
    Let ("id", Abs ("x", Var "x"),
      App (Var "id", Entier 42))
  in
  test_inference term4 [] "Let avec polymorphisme (id appliqué à un entier)";

  (* Test 5: Polymorphism with multiple Let bindings *)
  let term5 =
    Let ("id", Abs ("x", Var "x"),
      Let ("y", App (Var "id", Entier 42),
        App (Var "id", Var "y")))
  in
  test_inference term5 [] "Polymorphisme avec plusieurs Let";

  (* Test 7: Let with type mismatch *)
  let term7 =
    Let ("x", Entier 5,
      App (Var "x", Entier 10))
  in
  test_inference term7 [] "Let avec une incompatibilité de type";

  (* Test 8: Let with a list and polymorphic operations *)
  let term8 =
    Let ("consList", Abs ("x", Abs ("xs", Cons (Var "x", Var "xs"))),
      App (App (Var "consList", Entier 42), Nil))
  in
  test_inference term8 [] "Let avec une liste et des opérations polymorphes";

  Printf.printf "===== FIN DES TESTS =====\n";

(* tests d'inférence pour unit, ref, deref et assign *)
let () =
  Printf.printf "===== TESTS D'INFERENCE DE TYPE POUR Unit, Ref, Deref ET Assign =====\n\n";

  (* Fonction pour tester l'inférence de type et afficher les résultats *)
  let test_inference term env description =
    Printf.printf "=== Test : %s ===\n" description;
    Printf.printf "Terme : %s\n" (print_term term);
    match inference term env with
    | Some typeInfere -> Printf.printf "Type inféré : %s\n\n" (print_type typeInfere)
    | None -> Printf.printf "Échec de l'inférence de type.\n\n"
  in

  (* Test 1: Inférence sur Unit *)
  let term1 = Unit in
  test_inference term1 [] "Inférence sur Unit";

  (* Test 2: Inférence sur Ref *)
  let term2 = Ref (Entier 42) in
  test_inference term2 [] "Inférence sur Ref avec un entier";

  (* Test 3: Inférence sur Deref *)
  let term3 = Deref (Ref (Entier 100)) in
  test_inference term3 [] "Inférence sur Deref après Ref";

  (* Test 4: Inférence sur Assign *)
  let term4 = Assign (Ref (Entier 50), Entier 200) in
  test_inference term4 [] "Inférence sur Assign";

  (* Test 5: Inférence avec Let combiné avec Ref, Deref et Assign *)
  let term5 =
    Let ("x", Ref (Entier 10),
      Let ("_", Assign (Var "x", Entier 20),
        Deref (Var "x")))
  in
  test_inference term5 [] "Let combiné avec Ref, Assign et Deref";

  (* Test 6: Inférence avec plusieurs références *)
  let term6 =
    Let ("r1", Ref (Entier 30),
      Let ("r2", Ref (Entier 40),
        Let ("_", Assign (Var "r1", Entier 50),
          Addition (Deref (Var "r1"), Deref (Var "r2")))))
  in
  test_inference term6 [] "Let avec plusieurs références et opérations";

  (* Test 7: Inférence avec une liste de références *)
  let term7 =
    Let ("list_ref", Ref (Cons (Entier 1, Cons (Entier 2, Nil))),
      Let ("_", Assign (Var "list_ref", Cons (Entier 3, Nil)),
        Deref (Var "list_ref")))
  in
  test_inference term7 [] "Liste de références combinée avec Assign et Deref";

  (* Test 8: Inférence polymorphique avec Ref *)
  let term8 =
    Let ("id_ref", Abs ("x", Ref (Var "x")),
      App (Var "id_ref", Entier 42))
  in
  test_inference term8 [] "Fonction polymorphe créant une référence";

  (* Test 9: Inférence avec des références imbriquées *)
  let term9 =
    Let ("outer_ref", Ref (Ref (Entier 99)),
      Let ("_", Assign (Deref (Var "outer_ref"), Entier 100),
        Deref (Deref (Var "outer_ref"))))
  in
  test_inference term9 [] "Références imbriquées avec Assign et Deref";

  Printf.printf "===== FIN DES TESTS =====\n";

(* Tests inférence point fixe *)
let () =
  Printf.printf "===== TESTS D'INFERENCE DE TYPE AVEC LE COMBINAISON FIX =====\n\n";

  (* Fonction pour tester l'inférence de type et afficher les résultats *)
  let test_inference term env description =
    Printf.printf "=== Test : %s ===\n" description;
    Printf.printf "Terme : %s\n" (print_term term);
    match inference term env with
    | Some typeInfere -> Printf.printf "Type inféré : %s\n\n" (print_type typeInfere)
    | None -> Printf.printf "Échec de l'inférence de type.\n\n"
  in

  (* Test 1: Fix combiné avec un entier *)
  let term1 = Fix (Abs ("x", Addition (Var "x", Entier 1))) in
  test_inference term1 [] "Fix combiné avec une addition";

  (* Test 1: Factorielle *)
  let term1 = 
    Fix (Abs ("fact", Abs ("n", 
      Izte (Var "n", 
            Entier 1, 
            Addition (Var "n", App (Var "fact", Soustraction (Var "n", Entier 1)))))))
  in
  test_inference term1 [] "Factorielle avec Fix";

  (* Test 2: Fibonacci *)
  let term2 = 
    Fix (Abs ("fib", Abs ("n",
      Izte (Var "n", 
            Entier 0, 
            Izte (Soustraction (Var "n", Entier 1),
                  Entier 1,
                  Addition (
                    App (Var "fib", Soustraction (Var "n", Entier 1)),
                    App (Var "fib", Soustraction (Var "n", Entier 2))))))))
  in
  test_inference term2 [] "Fibonacci avec Fix";

  Printf.printf "===== FIN DES TESTS =====\n";

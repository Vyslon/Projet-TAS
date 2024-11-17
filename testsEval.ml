(* tests Partie 2 *)
let () =
  let fuel = 10000 in

  let test term name =
    Printf.printf "%s - Avant réduction : %s\n" name (print_term term);
    match ltr_cbv_norm' term fuel with
    | Some result ->
        Printf.printf "%s - Après réduction : %s\n\n" name (print_term result)
    | None ->
        Printf.printf "%s - Impossible de réduire le terme dans les %d étapes (divergence possible).\n\n" name fuel
  in

  (* I : Identité
    résultat attendu : λx.x 
    donc : (fun x -> x) *)
  let i_term = Abs ("x", Var "x") in

  (* δ : auto-application
    résultat attendu : λx. x x
    donc : (fun x -> (x x)) *)
  let delta_term = Abs ("x", App (Var "x", Var "x")) in

  (* Ω : divergence
    résultat attendu : (λx. x x) (λx. x x)
    donc : divergence ou on peut aussi donner ((fun x -> (x x)) (fun x -> (x x))) *)
  let omega_term = App (delta_term, delta_term) in

  (* S
    résultat attendu : λx. λy. λz. x z (y z)
    donc : (fun x -> (fun y -> (fun z -> ((x z) (y z))))) *)
  let s_term = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))) in

  (* K
   résultat attendu : λx.λy. x
   donc : (fun x -> (fun y -> x)) *)
  let k_term = Abs ("x", Abs ("y", Var "x")) in

  (* S K K
    résultat attendu : λx. λy. x
    donc : (fun z -> z) *)
  let skk_term = App (App (s_term, k_term), k_term) in

  (* S I I
    résultat attendu : λz. z z
    donc : (fun z -> (z z)) *)
  let sii_term = App (App (s_term, i_term), i_term) in

  (* 0 : λf.λx. x *)
  let church_0 = Abs ("f", Abs ("x", Var "x")) in

  (* 1 : λf.λx. f x *)
  let church_1 = Abs ("f", Abs ("x", App (Var "f", Var "x"))) in

  (* 2 : λf.λx. f (f x) *)
  let church_2 = Abs ("f", Abs ("x", App (Var "f", App (Var "f", Var "x")))) in

  (* 3 : λf.λx. f (f (f x)) *)
  let church_3 = Abs ("f", Abs ("x", App (Var "f", App (Var "f", App (Var "f", Var "x"))))) in

  (* Addition : λn.λm.λf.λe. n f (m f e) *)
  let add = Abs ("n", Abs ("m", Abs ("f", Abs ("e", App (App (Var "n", Var "f"), App (App (Var "m", Var "f"), Var "e")))))) in

  (* Multiplication : λn.λm.λf.λe n (m f) e *)
  let mult = Abs ("n", Abs ("m", Abs ("f", Abs ("e", App (App (Var "n", App (Var "m", Var "f")), Var "e"))))) in

  (* Puissance : λn.λm.λf.λe. (m n) f e *)
  let power = Abs ("n", Abs ("m", Abs ("f", Abs ("e", App (App (App (Var "m", Var "n"), Var "f"), Var "e"))))) in

  (* 1 + 2
  résultat attendu : λf.λe. f (f (f x)), 
  donc (fun f -> (fun e -> (f (f (f e))))) *)
  let add_1_2 = App (App (add, church_1), church_2) in

  (* 2 + 2
  résultat attendu : λf.λe. f (f (f (f e)))
  donc (fun f -> (fun e -> (f (f (f (f e)))))) *)
  let add_2_2 = App (App (add, church_2), church_2) in

  (* 1 x 2
  résultat attendu : λf.ex. f (f e)
  donc (fun f -> (fun e -> (f (f e)))) *)
  let mult_1_2 = App (App (mult, church_1), church_2) in
  
  (* 2 x 3
  résultat attendu : λf.λe. f (f (f (f (f (f e)))))
  donc (fun f -> (fun e -> (f (f (f (f (f (f e)))))))) *)
  let mult_2_3 = App (App (mult, church_2), church_3) in

  (* 3 x 3
  résultat attendu : λf.λe. f (f (f (f (f (f (f (f (f e))))))))
  donc (fun f -> (fun e -> (f (f (f (f (f (f (f (f (f e))))))))))) *)
  let mult_3_3 = App (App (mult, church_3), church_3) in
  
  (* 2^3 *)
  (* résultat attendu : λf.λe. f (f (f (f (f (f (f (f (f e))))))))
  donc (fun f -> (fun e -> (f (f (f (f (f (f (f (f e)))))))))) *)
  let power_2_3 = App (App (power, church_2), church_3) in

  (* Test de power 3 2 *)
  (* résultat attendu : λf.λe. f (f (f (f (f (f (f (f (f e))))))))
  donc (fun f -> (fun e -> (f (f (f (f (f (f (f (f (f e))))))))))) *)
  let power_3_2 = App (App (power, church_3), church_2) in

  (* 0^1 *)
  (* résultat attendu : λf.λx. x
  donc (fun f -> (fun x -> x)) *)
  let power_0_1 = App (App (power, church_0), church_1) in

  (* Tests *)
  test i_term "Test I";
  test delta_term "Test δ (Delta)";
  test omega_term "Test Ω (Omega)";
  test s_term "Test S";
  test k_term "Test K";
  test skk_term "Test S K K";
  test sii_term "Test S I I";
  test add_1_2 "Test 1 + 2";
  test add_2_2 "Test 2 + 2";
  test mult_1_2 "Test 1 x 2";
  test mult_2_3 "Test 2 x 3";
  test mult_3_3 "Test 3 x 3";
  test power_2_3 "Test 2^3";
  test power_3_2 "Test 3^2";
  test power_0_1 "Test 0^1";

(* tests Partie 2 *)
let () =
  Printf.printf "===== TESTS DE NORMALISATION AVEC LTR_CBv_NORM' =====\n\n";

  (* Fonction pour normaliser et afficher les résultats *)
  let test_normalisation term n_steps description =
    Printf.printf "=== Test : %s ===\n" description;
    Printf.printf "Terme initial : %s\n" (print_term term);
    match ltr_cbv_norm' term n_steps with
    | Some result ->
        Printf.printf "Terme normalisé : %s\n\n"
         (print_term result)
    | None ->
        Printf.printf "Le terme n'a pas pu être normalisé en %d étapes.\n\n" n_steps
  in

  (* 1. Identité *)
  let id_term = Abs ("x", Var "x") in
  test_normalisation id_term 100 "Identité (Abs \"x\" -> x)";

  (* 2. Application de l'identité à y de type T *)
  let app_id_y = App (id_term, Var "y") in
  test_normalisation app_id_y 100 "Application de l'identité à y";

  (* 3. K combinator *)
  let const_term = Abs ("x", Abs ("y", Var "x")) in
  test_normalisation const_term 100 "K combinator";

  (* 4. K combinator appliqué *)
  let const_app = App (App (const_term, Var "z"), Var "w") in
  test_normalisation const_app 100 "K combinator appliqué à z et w";

  (* 5. Ω : divergence *)
  let omega_term = App (Abs ("x", App (Var "x", Var "x")), Abs ("x", App (Var "x", Var "x"))) in
  test_normalisation omega_term 100 "Ω : divergence";

  (* 6. S combinator *)
  let s_term = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z"))))) in
  test_normalisation s_term 100 "S combinator";

  (* 7. S K K *)
  let k_term = Abs ("x", Abs ("y", Var "x")) in
  let skk_term = App (App (s_term, k_term), k_term) in
  test_normalisation skk_term 100 "S combinator appliqué à K K";

  (* 8. Application d'un Nat *)
  let nat_app = Abs ("f", Abs ("x", App (Var "f", Var "x"))) in
  test_normalisation nat_app 100 "Application de Nat";

  Printf.printf "===== FIN DES TESTS DE NORMALISATION =====\n";

(* Tests des entiers, additions et soustractions *)
let () =
  (* Define some sample terms *)
  let term1 = Addition (Entier 3, Entier 5) in
  let term2 = Soustraction (Entier 10, Entier 7) in
  let term3 = Addition (Entier 4, Soustraction (Entier 9, Entier 3)) in
  let term4 = Addition (term1, term2) in  (* Nested operations *)

  (* Define a fuel limit for the normalization function *)
  let fuel = 10 in

  (* Print and evaluate term1 *)
  Printf.printf "Evaluating term1: %s\n" (print_term term1);
  (match ltr_cbv_norm' term1 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term1\n\n");

  (* Print and evaluate term2 *)
  Printf.printf "Evaluating term2: %s\n" (print_term term2);
  (match ltr_cbv_norm' term2 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term2\n\n");

  (* Print and evaluate term3 *)
  Printf.printf "Evaluating term3: %s\n" (print_term term3);
  (match ltr_cbv_norm' term3 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term3\n\n");

  (* Print and evaluate term4 *)
  Printf.printf "Evaluating term4: %s\n" (print_term term4);
  (match ltr_cbv_norm' term4 fuel with
   | Some result -> Printf.printf "Result: %s\n\n" (print_term result)
   | None -> Printf.printf "Divergence detected in term4\n\n")

(* Tests des listes*)
let () =
  (* Création de listes pour les tests *)
  let liste1 = Cons (Entier 1, Cons (Entier 2, Cons (Entier 3, Nil))) in
  let liste2 = Cons (Entier 4, liste1) in  (* [4, 1, 2, 3] *)
  let liste3 = Cons (Addition (Entier 1, Entier 2), Cons (Entier 2, Cons ((Soustraction (Entier 8, Entier 2)), Nil))) in
  let liste_vide = Nil in

  (* Définition de la limite de carburant pour éviter les boucles infinies *)
  let fuel = 1000 in

  (* Test de l'évaluation de liste1 *)
  Printf.printf "Évaluation de liste1: %s\n" (print_term liste1);
  (match ltr_cbv_norm' liste1 fuel with
  | Some result -> Printf.printf "Résultat: %s\n\n" (print_term result)
  | None -> Printf.printf "Échec de l'évaluation ou divergence pour liste1\n\n");

  (* Test de l'évaluation de liste2 *)
  Printf.printf "Évaluation de liste2: %s\n" (print_term liste2);
  (match ltr_cbv_norm' liste2 fuel with
  | Some result -> Printf.printf "Résultat: %s\n\n" (print_term result)
  | None -> Printf.printf "Échec de l'évaluation ou divergence pour liste2\n\n");

    (* Test de l'évaluation de liste3 *)
  Printf.printf "Évaluation de liste3: %s\n" (print_term liste3);
  (match ltr_cbv_norm' liste3 fuel with
  | Some result -> Printf.printf "Résultat: %s\n\n" (print_term result)
  | None -> Printf.printf "Échec de l'évaluation ou divergence pour liste3\n\n");

  (* Test de l'évaluation d'une liste vide *)
  Printf.printf "Évaluation de liste_vide: %s\n" (print_term liste_vide);
  (match ltr_cbv_norm' liste_vide fuel with
  | Some result -> Printf.printf "Résultat: %s\n\n" (print_term result)
  | None -> Printf.printf "Échec de l'évaluation ou divergence pour liste_vide\n\n");

  (* Test de l'opération head sur liste1 *)
  (* Printf.printf "Head de liste1: ";
  (try Printf.printf "%s\n\n" (print_term (head liste1))
  with Failure msg -> Printf.printf "Erreur: %s\n\n" msg); *)

  (* Test de l'opération queue sur liste1 *)
  (* Printf.printf "Queue de liste1: ";
  (try Printf.printf "%s\n\n" (print_term (queue liste1))
  with Failure msg -> Printf.printf "Erreur: %s\n\n" msg); *)

  (* Test de is_empty sur liste_vide et liste1 *)
  Printf.printf "Liste_vide est vide? %b\n" (is_empty liste_vide);
  Printf.printf "Liste1 est vide? %b\n\n" (is_empty liste1);

(* Tests d'Izte et Iete  *)
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

(* Tests point fixe *)
let () =
  (* Fonctionnelle pour Fibonacci *)
  let fib_functional =
    Abs ("f",
      Abs ("n",
        Izte (Var "n",
              Entier 0,
              Izte (Soustraction (Var "n", Entier 1),
                    Entier 1,
                    Addition (
                      App (Var "f", Soustraction (Var "n", Entier 1)),
                      App (Var "f", Soustraction (Var "n", Entier 2))
                    )
              )
        )
      )
    )
  in

  (* Point fixe explicite *)
  let fib = Fix fib_functional in

  (* Application à un cas de test *)
  let test_case = App (fib, Entier 10) in

  (* Évaluation avec un fuel *)
  let fuel = 1000 in
  match ltr_cbv_norm' test_case fuel with
  | Some result -> Printf.printf "Résultat avec fuel %d : %s\n" fuel (print_term result)
  | None -> Printf.printf "Évaluation interrompue après %d étapes (divergence possible).\n" fuel

(* Tests let *)
let () =
  (* Test 1 : Let avec une simple définition et utilisation *)
  let test1 =
    Let ("x", Entier 5, Addition (Var "x", Entier 10))
  in
  Printf.printf "Test 1 : %s\n" (print_term test1);
  (match ltr_cbv_norm' test1 100 with
   | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
   | None -> Printf.printf "Évaluation interrompue (divergence possible).\n\n");

  (* Test 2 : Let avec un calcul complexe *)
  let test2 =
    Let ("x", Addition (Entier 3, Entier 7),
      Let ("y", Soustraction (Var "x", Entier 5),
        Addition (Var "x", Var "y")))
  in
  Printf.printf "Test 2 : %s\n" (print_term test2);
  (match ltr_cbv_norm' test2 100 with
   | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
   | None -> Printf.printf "Évaluation interrompue (divergence possible).\n\n");

  (* Test 3 : Let combiné avec Izte *)
  let test3 =
    Let ("x", Entier 0,
      Izte (Var "x", Entier 1, Entier 42))
  in
  Printf.printf "Test 3 : %s\n" (print_term test3);
  (match ltr_cbv_norm' test3 100 with
   | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
   | None -> Printf.printf "Évaluation interrompue (divergence possible).\n\n");

  (* Test 4 : Let combiné avec une définition récursive (Fibonacci avec Fix) *)
  let fib_functional =
    Abs ("f",
      Abs ("n",
        Izte (Var "n",
              Entier 0,
              Izte (Soustraction (Var "n", Entier 1),
                    Entier 1,
                    Addition (
                      App (Var "f", Soustraction (Var "n", Entier 1)),
                      App (Var "f", Soustraction (Var "n", Entier 2))
                    )
              )
        )
      )
    )
  in
  let test4 =
    Let ("fib", Fix fib_functional,
      App (Var "fib", Entier 5))
  in
  Printf.printf "Test 4 : %s\n" (print_term test4);
  (match ltr_cbv_norm' test4 500 with
   | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
   | None -> Printf.printf "Évaluation interrompue (divergence possible).\n\n");

  (* Test 5 : Let imbriqué avec des calculs complexes *)
  let test5 =
    Let ("x", Entier 2,
      Let ("y", Addition (Var "x", Entier 3),
        Let ("z", Soustraction (Var "y", Entier 1),
          Addition (Var "z", Var "x"))))
  in
  Printf.printf "Test 5 : %s\n" (print_term test5);
  (match ltr_cbv_norm' test5 100 with
   | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
   | None -> Printf.printf "Évaluation interrompue (divergence possible).\n\n");

  (* Test 6 : Let avec une évaluation partielle *)
  let test6 =
    Let ("x", Addition (Entier 2, Entier 3),
      Let ("y", Var "x",
        Soustraction (Var "y", Entier 1)))
  in
  Printf.printf "Test 6 : %s\n" (print_term test6);
  (match ltr_cbv_norm' test6 100 with
   | Some result -> Printf.printf "Résultat : %s\n\n" (print_term result)
   | None -> Printf.printf "Évaluation interrompue (divergence possible).\n\n");

(* Tests head et tail *)
let () =
   Printf.printf "===== TESTS D'EVALUATION AVEC ltr_cbv_norm' =====\n";
 
   (* Fonction pour afficher le résultat d'une évaluation *)
   let print_evaluation_result term =
       Printf.printf "Terme initial : %s\n" (print_term term);
       match ltr_cbv_norm' term 100 with
       | Some t -> Printf.printf "Résultat de l'évaluation : %s\n\n" (print_term t)
       | None -> Printf.printf "Échec de la normalisation (divergence ou carburant épuisé).\n\n"
   in
 
   (* Test 1 : Head d'une liste concrète *)
   let term1 = Head (Cons (Entier 1, Nil)) in
   Printf.printf "Test 1 : Head d'une liste concrète\n";
   print_evaluation_result term1;
 
   (* Test 2 : Tail d'une liste concrète *)
   let term2 = Tail (Cons (Entier 1, Cons (Entier 2, Nil))) in
   Printf.printf "Test 2 : Tail d'une liste concrète\n";
   print_evaluation_result term2;
 
   (* Test 3 : Fonction utilisant Head *)
   let term3 = App (Abs ("x", Head (Var "x")), Cons (Entier 1, Nil)) in
   Printf.printf "Test 3 : Fonction utilisant Head\n";
   print_evaluation_result term3;
 
   (* Test 4 : Fonction utilisant Tail *)
   let term4 = App (Abs ("x", Tail (Var "x")), Cons (Entier 1, Cons (Entier 2, Nil))) in
   Printf.printf "Test 4 : Fonction utilisant Tail\n";
   print_evaluation_result term4;
 
   (* Test 5 : Fonction retournant une liste manipulée avec Head et Tail *)
   let term5 = Abs ("x", Cons (Head (Var "x"), Tail (Var "x"))) in
   Printf.printf "Test 5 : Fonction retournant une liste manipulée avec Head et Tail\n";
   print_evaluation_result term5;
 
   (* Test 6 : Evaluation d'une liste complexe avec Head et Tail *)
   let term6 = App (Abs ("x", Cons (Head (Var "x"), Tail (Var "x"))), Cons (Entier 1, Cons (Entier 2, Nil))) in
   Printf.printf "Test 6 : Evaluation d'une liste complexe avec Head et Tail\n";
   print_evaluation_result term6;
 
   (* Test 7 : Head sur une liste polymorphe *)
   let term7 = App (Abs ("x", Head (Var "x")), Cons (Entier 1, Cons (Entier 2, Nil))) in
   Printf.printf "Test 7 : Head sur une liste polymorphe\n";
   print_evaluation_result term7;
 
   (* Test 8 : Tail sur une liste polymorphe *)
   let term8 = App (Abs ("x", Tail (Var "x")), Cons (Entier 1, Cons (Entier 2, Nil))) in
   Printf.printf "Test 8 : Tail sur une liste polymorphe\n";
   print_evaluation_result term8;
 
   (* Test 9 : Évaluation récursive avec Fix *)
   let term9 = App (Fix (Abs ("f", Abs ("x", Izte (Var "x", Entier 0, App (Var "f", Soustraction (Var "x", Entier 1)))))), Entier 3) in
   Printf.printf "Test 9 : Évaluation récursive avec Fix (compte à rebours)\n";
   print_evaluation_result term9;
 
   Printf.printf "===== FIN DES TESTS =====\n";
 
(* Tests évaluation unit, ref, deref et assign *)
let () =
  Printf.printf "===== TESTS D'EVALUATION POUR Unit, Ref, Deref ET Assign =====\n\n";

  (* Fonction pour réinitialiser la mémoire *)
  let reset_regions () =
    regions := []
  in

  (* Fonction pour tester une évaluation et afficher les résultats *)
  let test_evaluation term n_steps description =
    Printf.printf "=== Test : %s ===\n" description;
    Printf.printf "Terme initial : %s\n" (print_term term);
    match ltr_cbv_norm' term n_steps with
    | Some result ->
        Printf.printf "Terme après %d étapes : %s\n" n_steps (print_term result);
        Printf.printf "Mémoire actuelle : [ %s ]\n\n"
          (String.concat "; " (List.map (fun (id, value) -> id ^ " -> " ^ print_term value) !regions))
    | None ->
        Printf.printf "Le terme n'a pas pu être évalué en %d étapes.\n" n_steps;
        Printf.printf "Mémoire actuelle : [ %s ]\n\n"
          (String.concat "; " (List.map (fun (id, value) -> id ^ " -> " ^ print_term value) !regions));
    reset_regions () (* Réinitialiser la mémoire après chaque test *)
  in

  (* Test 1: Evaluation de Unit *)
  reset_regions ();
  let term1 = Unit in
  test_evaluation term1 1 "Evaluation de Unit";

  (* Test 2: Evaluation de Ref *)
  reset_regions ();
  let term2 = Ref (Entier 42) in
  test_evaluation term2 5 "Création d'une référence (Ref 42)";

  (* Test 3: Evaluation de Deref *)
  reset_regions ();
  let rho1 = nouvelle_var () in
  ajoutMemoire rho1 (Entier 100); (* On simule une région mémoire avec la valeur 100 *)
  let term3 = Deref (Var rho1) in
  test_evaluation term3 5 ("Déréférencement de la région " ^ rho1 ^ " contenant 100");

  (* Test 4: Assignation *)
  reset_regions ();
  let rho1 = nouvelle_var () in
  ajoutMemoire rho1 (Entier 100);
  let term4 = Assign (Var rho1, Entier 200) in
  test_evaluation term4 5 ("Assignation de 200 à la région " ^ rho1);

  (* Test 5: Ref et Deref combinés *)
  reset_regions ();
  let term5 = Deref (Ref (Entier 500)) in
  test_evaluation term5 10 "Création d'une référence (Ref 500) suivie d'un déréférencement";

  (* Test 6: Combinaison complexe - Ref, Deref, et Assign *)
  reset_regions ();
  let term6 =
    Let ("x", Ref (Entier 10),
      Let ("_", Assign (Var "x", Entier 20),
        Deref (Var "x")))
  in
  test_evaluation term6 15 "Combinaison : Ref 10 -> Assign 20 -> Deref";

  (* Test 7: Création et manipulation de plusieurs références *)
  reset_regions ();
  let term7 =
    Let ("r1", Ref (Entier 30),
      Let ("r2", Ref (Entier 40),
        Let ("_", Assign (Var "r1", Entier 50),
          Addition (Deref (Var "r1"), Deref (Var "r2")))))
  in
  test_evaluation term7 20 "Manipulation de plusieurs références (r1 et r2)";

  (* Test 8: Evaluation imbriquée avec listes et références *)
  reset_regions ();
  let term8 =
    Let ("list_ref", Ref (Cons (Entier 1, Cons (Entier 2, Nil))),
      Let ("_", Assign (Var "list_ref", Cons (Entier 3, Nil)),
        Deref (Var "list_ref")))
  in
  test_evaluation term8 20 "Création et modification d'une liste dans une référence";

  Printf.printf "===== FIN DES TESTS =====\n";

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
  Printf.printf "Head de liste1: ";
  (try Printf.printf "%s\n\n" (print_term (head liste1))
  with Failure msg -> Printf.printf "Erreur: %s\n\n" msg);

  (* Test de l'opération queue sur liste1 *)
  Printf.printf "Queue de liste1: ";
  (try Printf.printf "%s\n\n" (print_term (queue liste1))
  with Failure msg -> Printf.printf "Erreur: %s\n\n" msg);

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
  let test_case = App (fib, Entier 9) in

  (* Évaluation avec un fuel *)
  let fuel = 1000 in
  match ltr_cbv_norm' test_case fuel with
  | Some result -> Printf.printf "Résultat avec fuel %d : %s\n" fuel (print_term result)
  | None -> Printf.printf "Évaluation interrompue après %d étapes (divergence possible).\n" fuel
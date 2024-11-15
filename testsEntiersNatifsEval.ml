
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

(* TODO : listes*)
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

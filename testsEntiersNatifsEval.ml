
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

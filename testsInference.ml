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

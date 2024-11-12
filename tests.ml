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

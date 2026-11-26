import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8225_2
    (hNoJunk :
      let V := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        (∀ j g, C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, V C → C.size ≤ 63 →
        (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ x : Fin 26 → Bool, PEqualNP.EdgeOwnership.gateVal 26 C j x = true → C.eval (List.ofFn x) = true) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, V D ∧ D.size ≤ C.size ∧
          ∃ G : SimpleGraph (Fin 26), G = PEqualNP.EdgeOwnership.edgeGraph 26 (List.flatMap (fun p : Fin 13 => List.map (fun l : Fin 13 => (p.val, 13 + l.val)) (List.filter (fun l : Fin 13 => Decidable.decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) (List.finRange 13))) (List.finRange 13)) ∧
            PEqualNP.EdgeOwnership.HasStarProfile 26 G D ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned 26 G D)
    (hHasJunk :
      let V := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        (∀ j g, C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, V C → C.size ≤ 63 →
        (∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ x : Fin 26 → Bool, PEqualNP.EdgeOwnership.gateVal 26 C j x = true ∧ C.eval (List.ofFn x) = false) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, V D ∧ D.size ≤ C.size ∧
          ∃ G : SimpleGraph (Fin 26), G = PEqualNP.EdgeOwnership.edgeGraph 26 (List.flatMap (fun p : Fin 13 => List.map (fun l : Fin 13 => (p.val, 13 + l.val)) (List.filter (fun l : Fin 13 => Decidable.decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) (List.finRange 13))) (List.finRange 13)) ∧
            PEqualNP.EdgeOwnership.HasStarProfile 26 G D ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned 26 G D) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4) := by
  intro x1 hx1 hfun
  by_cases hbig : 64 ≤ x1.size
  · let mkLine : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun l =>
      [ PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [l % 13, (l + 1) % 13],
        PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(l + 3) % 13, (l + 9) % 13],
        PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [26 + 4 * l, 26 + 4 * l + 1],
        PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [13 + l, 26 + 4 * l + 2] ]
    let lineGates : List PEqualNP.CircuitLowerBounds.Gate := (List.range 13).flatMap mkLine
    let topOrs : List PEqualNP.CircuitLowerBounds.Gate :=
      [ PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [26 + 3, 26 + 7] ] ++
      ((List.range 11).map fun k =>
        PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [78 + k, 26 + 4 * (k + 2) + 3])
    let C64 : PEqualNP.CircuitLowerBounds.Circuit := ⟨lineGates ++ topOrs, 89⟩
    have hlen64 : C64.gates.length = 64 := by decide
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hgetD_app : ∀ (w t : List Bool) (i : ℕ), i < w.length → (w ++ t).getD i false = w.getD i false := by
      intro w t i hi
      simp [List.getD, List.getElem?_append_left hi]
    let lineVal : (Fin 26 → Bool) → ℕ → Bool := fun x l =>
      (List.ofFn x).getD (13 + l) false &&
        (((List.ofFn x).getD (l % 13) false || (List.ofFn x).getD ((l + 1) % 13) false) ||
         ((List.ofFn x).getD ((l + 3) % 13) false || (List.ofFn x).getD ((l + 9) % 13) false))
    have hfoldl_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
        i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i _; rfl
      | cons g gs ih =>
        intro w i hi
        simp only [List.foldl_cons]
        rw [ih (step w g) i (by simp [step]; omega)]
        exact hgetD_app w _ i hi
    have hlines : ∀ (x : Fin 26 → Bool) (k : ℕ), k ≤ 13 →
        let wk := ((List.range k).flatMap mkLine).foldl step (List.ofFn x)
        wk.length = 26 + 4 * k ∧
        (∀ i < 26, wk.getD i false = (List.ofFn x).getD i false) ∧
        (∀ l < k, wk.getD (26 + 4 * l + 3) false = lineVal x l) := by
      intro x k hk
      induction k with
      | zero =>
        refine ⟨by simp, fun i _ => rfl, fun l hl => by omega⟩
      | succ k ih =>
        have hk13 : k ≤ 13 := Nat.le_of_succ_le hk
        obtain ⟨ih_len, ih_inp, ih_val⟩ := ih hk13
        have hflat : (List.range (k + 1)).flatMap mkLine = (List.range k).flatMap mkLine ++ mkLine k := by
          rw [List.range_succ, List.flatMap_append]; simp
        dsimp only
        rw [hflat, List.foldl_append]
        set wk := ((List.range k).flatMap mkLine).foldl step (List.ofFn x)
        have hs : (mkLine k).foldl step wk =
            wk ++ [ (wk.getD (k % 13) false || wk.getD ((k + 1) % 13) false),
                    (wk.getD ((k + 3) % 13) false || wk.getD ((k + 9) % 13) false),
                    ((wk.getD (k % 13) false || wk.getD ((k + 1) % 13) false) ||
                     (wk.getD ((k + 3) % 13) false || wk.getD ((k + 9) % 13) false)),
                    (wk.getD (13 + k) false &&
                     ((wk.getD (k % 13) false || wk.getD ((k + 1) % 13) false) ||
                      (wk.getD ((k + 3) % 13) false || wk.getD ((k + 9) % 13) false))) ] := by
          simp only [mkLine, List.foldl_cons, List.foldl_nil, step, PEqualNP.CircuitLowerBounds.GateOp.eval,
            List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
            id_eq, Bool.or_false, Bool.and_true]
          have h1 : (wk ++ [wk.getD (k % 13) false || wk.getD ((k + 1) % 13) false]).getD ((k + 3) % 13) false = wk.getD ((k + 3) % 13) false :=
            hgetD_app _ _ _ (by rw [ih_len]; omega)
          have h2 : (wk ++ [wk.getD (k % 13) false || wk.getD ((k + 1) % 13) false]).getD ((k + 9) % 13) false = wk.getD ((k + 9) % 13) false :=
            hgetD_app _ _ _ (by rw [ih_len]; omega)
          rw [h1, h2]
          set b0 := wk.getD (k % 13) false || wk.getD ((k + 1) % 13) false
          set b1 := wk.getD ((k + 3) % 13) false || wk.getD ((k + 9) % 13) false
          have h3 : ((wk ++ [b0]) ++ [b1]).getD (26 + 4 * k) false = b0 := by
            rw [List.append_assoc]; simp [List.getD, ih_len]
          have h4 : ((wk ++ [b0]) ++ [b1]).getD (26 + 4 * k + 1) false = b1 := by
            rw [List.append_assoc]; simp [List.getD, ih_len]
          rw [h3, h4]
          set b2 := b0 || b1
          have h5 : (((wk ++ [b0]) ++ [b1]) ++ [b2]).getD (13 + k) false = wk.getD (13 + k) false := by
            rw [List.append_assoc, List.append_assoc]
            exact hgetD_app _ _ _ (by rw [ih_len]; omega)
          have h6 : (((wk ++ [b0]) ++ [b1]) ++ [b2]).getD (26 + 4 * k + 2) false = b2 := by
            rw [List.append_assoc, List.append_assoc]; simp [List.getD, ih_len]
          rw [h5, h6]
          simp [List.append_assoc]
        rw [hs]
        refine ⟨by simp [ih_len]; omega, fun i hi => ?_, fun l hl => ?_⟩
        · rw [hgetD_app _ _ _ (by rw [ih_len]; omega)]; exact ih_inp i hi
        · by_cases hlk : l = k
          · subst hlk
            have h0 : wk.getD (13 + l) false = (List.ofFn x).getD (13 + l) false := ih_inp _ (by omega)
            have h1 : wk.getD (l % 13) false = (List.ofFn x).getD (l % 13) false := ih_inp _ (by omega)
            have h2 : wk.getD ((l + 1) % 13) false = (List.ofFn x).getD ((l + 1) % 13) false := ih_inp _ (by omega)
            have h3 : wk.getD ((l + 3) % 13) false = (List.ofFn x).getD ((l + 3) % 13) false := ih_inp _ (by omega)
            have h4 : wk.getD ((l + 9) % 13) false = (List.ofFn x).getD ((l + 9) % 13) false := ih_inp _ (by omega)
            rw [h0, h1, h2, h3, h4]
            simp [List.getD, ih_len, lineVal]
          · have hlt : l < k := by omega
            rw [hgetD_app _ _ _ (by rw [ih_len]; omega)]
            exact ih_val l hlt
    have hgateVal_line : ∀ (x : Fin 26 → Bool) (l : ℕ), l < 13 →
        PEqualNP.EdgeOwnership.gateVal 26 C64 (4 * l + 3) x = lineVal x l := by
      intro x l hl
      obtain ⟨wlen, _, wval⟩ := hlines x 13 (le_refl 13)
      show ((lineGates ++ topOrs).foldl step (List.ofFn x)).getD (26 + (4 * l + 3)) false = lineVal x l
      rw [List.foldl_append, hfoldl_prefix _ _ _ (by dsimp [lineGates]; rw [wlen]; omega)]
      have heq : 26 + (4 * l + 3) = 26 + 4 * l + 3 := by omega
      rw [heq]
      exact wval l hl
    refine ⟨C64, ?_, ?_, ?_, ?_⟩
    · intro j g hj
      obtain ⟨hj', _⟩ := List.getElem?_eq_some_iff.mp hj
      rw [hlen64] at hj'
      have hall : (List.finRange 64).all (fun k =>
          match C64.gates[k.val]? with
          | none => false
          | some g' =>
            (match g'.op with | PEqualNP.CircuitLowerBounds.GateOp.and => true | PEqualNP.CircuitLowerBounds.GateOp.or => true | _ => false) &&
            match g'.inputs with
            | [a, b] => decide (a ≠ b ∧ a < 26 + k.val ∧ b < 26 + k.val)
            | _ => false) = true := by decide +kernel
      have hk := List.all_eq_true.mp hall ⟨j, hj'⟩ (List.mem_finRange _)
      have hget : C64.gates[j]? = some C64.gates[j] := List.getElem?_eq_getElem (by rw [hlen64]; exact hj')
      rw [hget] at hk
      simp only [Bool.and_eq_true] at hk
      have hgj : g = C64.gates[j] := by
        rw [hget] at hj; exact Option.some.inj hj.symm
      subst hgj
      rcases hk with ⟨hop, hin⟩
      have hop' : C64.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C64.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        cases hc : C64.gates[j].op <;> simp [hc] at hop ⊢
      cases hinp : C64.gates[j].inputs with
      | nil => simp [hinp] at hin
      | cons a t =>
        cases t with
        | nil => simp [hinp] at hin
        | cons b t2 =>
          cases t2 with
          | nil =>
            simp only [hinp, decide_eq_true_eq] at hin
            exact ⟨hop', a, b, rfl, hin.1, hin.2.1, hin.2.2⟩
          | cons _ _ => simp [hinp] at hin
    · intro x
      obtain ⟨w13_len, _, w13_val⟩ := hlines x 13 (le_refl 13)
      set w13 := lineGates.foldl step (List.ofFn x)
      have htop : ∀ m ≤ 11,
          let tm := ([PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [26 + 3, 26 + 7]] ++
            ((List.range m).map fun k =>
              PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [78 + k, 26 + 4 * (k + 2) + 3])).foldl step w13
          tm.length = 79 + m ∧
          (∀ l < 13, tm.getD (26 + 4 * l + 3) false = lineVal x l) ∧
          tm.getD (78 + m) false = (List.range (m + 2)).any (lineVal x) := by
        intro m hm
        induction m with
        | zero =>
          simp only [List.range_zero, List.map_nil, List.append_nil, List.foldl_cons, List.foldl_nil,
            step, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
          refine ⟨by simp [w13_len], fun l hl => ?_, ?_⟩
          · rw [hgetD_app _ _ _ (by rw [w13_len]; omega)]; exact w13_val l hl
          · have hv0 : w13.getD (26 + 3) false = lineVal x 0 := w13_val 0 (by omega)
            have hv1 : w13.getD (26 + 7) false = lineVal x 1 := w13_val 1 (by omega)
            rw [hv0, hv1]
            simp [List.getD, w13_len, List.range_succ]
        | succ m ihm =>
          obtain ⟨ih_len, ih_val, ih_top⟩ := ihm (Nat.le_of_succ_le hm)
          rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc, List.foldl_append]
          set tm := ([PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [26 + 3, 26 + 7]] ++
            ((List.range m).map fun k =>
              PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [78 + k, 26 + 4 * (k + 2) + 3])).foldl step w13
          simp only [List.foldl_cons, List.foldl_nil, step, PEqualNP.CircuitLowerBounds.GateOp.eval,
            List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          refine ⟨by simp [ih_len]; omega, fun l hl => ?_, ?_⟩
          · rw [hgetD_app _ _ _ (by rw [ih_len]; omega)]; exact ih_val l hl
          · have hprev : tm.getD (78 + m) false = (List.range (m + 2)).any (lineVal x) := ih_top
            have hcur : tm.getD (26 + 4 * (m + 2) + 3) false = lineVal x (m + 2) := ih_val (m + 2) (by omega)
            have hidx : (tm ++ [tm.getD (78 + m) false || tm.getD (26 + 4 * (m + 2) + 3) false]).getD (78 + (m + 1)) false =
                (tm.getD (78 + m) false || tm.getD (26 + 4 * (m + 2) + 3) false) := by
              rw [show 78 + (m + 1) = tm.length by rw [ih_len]; omega]
              simp only [List.getD, List.getElem?_concat_length, Option.getD_some]
            rw [hidx, hprev, hcur, show m + 1 + 2 = (m + 2) + 1 by omega]
            conv_rhs => rw [List.range_succ, List.any_append]; simp only [List.any_cons, List.any_nil, Bool.or_false]
      obtain ⟨_, _, heval89⟩ := htop 11 (le_refl 11)
      have heval : C64.eval (List.ofFn x) = (List.range 13).any (lineVal x) := by
        show ((lineGates ++ topOrs).foldl step (List.ofFn x)).getD 89 false = _
        rw [List.foldl_append]
        exact heval89
      have hget_ofFn : ∀ (y : Fin 26 → Bool) (i : ℕ) (hi : i < 26),
          (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
        intro y i hi
        rw [List.getD, List.getElem?_ofFn, dite_eq_left]
        rfl
      rw [heval, List.any_eq_true]
      constructor
      · rintro ⟨l, hl, hlv⟩
        rw [List.mem_range] at hl
        simp only [lineVal, Bool.and_eq_true, Bool.or_eq_true] at hlv
        rcases hlv with ⟨hyl, hpts⟩
        have hyl' : x (Fin.natAdd 13 ⟨l, hl⟩) = true := by
          rw [hget_ofFn x (13 + l) (by omega)] at hyl
          exact hyl
        have hmem_pt : ∀ m : ℕ, (List.ofFn x).getD (m % 13) false = true →
            x (Fin.castAdd 13 ⟨m % 13, Nat.mod_lt m (by omega)⟩) = true := by
          intro m hm
          rw [hget_ofFn x (m % 13) (by omega)] at hm
          exact hm
        rcases hpts with (hp | hp) | (hp | hp)
        · refine ⟨⟨l % 13, Nat.mod_lt _ (by omega)⟩, ⟨l, hl⟩, Or.inl ?_, hmem_pt l hp, hyl'⟩
          ext; exact Nat.mod_eq_of_lt hl
        · refine ⟨⟨(l + 1) % 13, Nat.mod_lt _ (by omega)⟩, ⟨l, hl⟩, Or.inr (Or.inl ?_), hmem_pt (l + 1) hp, hyl'⟩
          ext; simp [Fin.val_add]
        · refine ⟨⟨(l + 3) % 13, Nat.mod_lt _ (by omega)⟩, ⟨l, hl⟩, Or.inr (Or.inr (Or.inl ?_)), hmem_pt (l + 3) hp, hyl'⟩
          ext; simp [Fin.val_add]
        · refine ⟨⟨(l + 9) % 13, Nat.mod_lt _ (by omega)⟩, ⟨l, hl⟩, Or.inr (Or.inr (Or.inr ?_)), hmem_pt (l + 9) hp, hyl'⟩
          ext; simp [Fin.val_add]
      · rintro ⟨p, l, hpl, hp, hl⟩
        refine ⟨l.val, List.mem_range.mpr l.2, ?_⟩
        simp only [lineVal, Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨?_, ?_⟩
        · rw [hget_ofFn x (13 + l.val) (by omega)]; exact hl
        · have hxp' : (List.ofFn x).getD p.val false = true := by
            rw [hget_ofFn x p.val (by omega)]; exact hp
          rcases hpl with h | h | h | h
          · left; left; have hv : p.val = l.val := congrArg Fin.val h
            rw [Nat.mod_eq_of_lt l.2, ← hv]; exact hxp'
          · left; right; have hv : p.val = (l.val + 1) % 13 := by simpa [Fin.val_add] using congrArg Fin.val h
            rw [← hv]; exact hxp'
          · right; left; have hv : p.val = (l.val + 3) % 13 := by simpa [Fin.val_add] using congrArg Fin.val h
            rw [← hv]; exact hxp'
          · right; right; have hv : p.val = (l.val + 9) % 13 := by simpa [Fin.val_add] using congrArg Fin.val h
            rw [← hv]; exact hxp'
    · exact Nat.le_trans (by decide) hbig
    · let edgeList : List (ℕ × ℕ) := List.flatMap (fun x6 : Fin 13 => List.map (fun x7 : Fin 13 => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun x7 : Fin 13 => Decidable.decide (x6 = x7 ∨ x6 = x7 + 1 ∨ x6 = x7 + 3 ∨ x6 = x7 + 9)) (List.finRange 13))) (List.finRange 13)
      let G := PEqualNP.EdgeOwnership.edgeGraph 26 edgeList
      have hget_ofFn : ∀ (y : Fin 26 → Bool) (i : ℕ) (hi : i < 26),
          (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
        intro y i hi
        rw [List.getD, List.getElem?_ofFn, dite_eq_left]
        rfl
      refine ⟨G, rfl, ?_, ?_⟩
      · intro j hj hop
        have honly : ∀ k : Fin 64, (PEqualNP.MetaComplexity.NestedCover.gateAt C64 k.val).op = PEqualNP.CircuitLowerBounds.GateOp.and → k.val % 4 = 3 ∧ k.val < 52 := by
          have hall : (List.finRange 64).all (fun k =>
              match (PEqualNP.MetaComplexity.NestedCover.gateAt C64 k.val).op with
              | PEqualNP.CircuitLowerBounds.GateOp.and => decide (k.val % 4 = 3 ∧ k.val < 52)
              | _ => true) = true := by decide +kernel
          intro k hkop
          have hk := List.all_eq_true.mp hall k (List.mem_finRange k)
          rw [hkop] at hk
          simpa using hk
        rw [hlen64] at hj
        obtain ⟨hmod, hlt52⟩ := honly ⟨j, hj⟩ hop
        dsimp only at hmod hlt52
        set l := j / 4
        have hl13 : l < 13 := by dsimp [l]; omega
        have hj_eq : j = 4 * l + 3 := by dsimp [l]; omega
        right
        refine ⟨⟨13 + l, by omega⟩, ?_⟩
        intro u v _ howns
        have hgv := howns.2.2.1
        rw [hj_eq, hgateVal_line _ l hl13] at hgv
        simp only [lineVal, Bool.and_eq_true] at hgv
        have hpi : PEqualNP.EdgeOwnership.pairInput u v ⟨13 + l, by omega⟩ = true := by
          rw [hget_ofFn _ (13 + l) (by omega)] at hgv
          exact hgv.1
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hpi
        rcases hpi with h | h
        · left; exact h.symm
        · right; exact h.symm
      · intro u v huv
        have hshape : ∀ a b : Fin 26, G.Adj a b →
            (a.val < 13 ∧ 13 ≤ b.val ∧ (let p : Fin 13 := ⟨a.val % 13, Nat.mod_lt _ (by omega)⟩; let l : Fin 13 := ⟨(b.val - 13) % 13, Nat.mod_lt _ (by omega)⟩; p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∨
            (b.val < 13 ∧ 13 ≤ a.val ∧ (let p : Fin 13 := ⟨b.val % 13, Nat.mod_lt _ (by omega)⟩; let l : Fin 13 := ⟨(a.val - 13) % 13, Nat.mod_lt _ (by omega)⟩; p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) := by
          intro a b hab
          dsimp only [G, edgeList, PEqualNP.EdgeOwnership.edgeGraph] at hab
          simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hab
          rcases hab with ⟨_, ⟨p, l, hpl, heq⟩ | ⟨p, l, hpl, heq⟩⟩
          · obtain ⟨ha, hb⟩ := Prod.ext_iff.mp heq
            dsimp only at ha hb
            left
            refine ⟨by omega, by omega, ?_⟩
            have hp' : (⟨a.val % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) = p := by ext; rw [← ha]; exact Nat.mod_eq_of_lt p.2
            have hl' : (⟨(b.val - 13) % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) = l := by ext; rw [← hb, Nat.add_sub_cancel_left]; exact Nat.mod_eq_of_lt l.2
            simpa [hp', hl'] using hpl
          · obtain ⟨hb, ha⟩ := Prod.ext_iff.mp heq
            dsimp only at ha hb
            right
            refine ⟨by omega, by omega, ?_⟩
            have hp' : (⟨b.val % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) = p := by ext; rw [← hb]; exact Nat.mod_eq_of_lt p.2
            have hl' : (⟨(a.val - 13) % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) = l := by ext; rw [← ha, Nat.add_sub_cancel_left]; exact Nat.mod_eq_of_lt l.2
            simpa [hp', hl'] using hpl
        have his_and : ∀ k : Fin 13, (PEqualNP.MetaComplexity.NestedCover.gateAt C64 (4 * k.val + 3)).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
          have hall : (List.finRange 13).all (fun k =>
              match (PEqualNP.MetaComplexity.NestedCover.gateAt C64 (4 * k.val + 3)).op with
              | PEqualNP.CircuitLowerBounds.GateOp.and => true
              | _ => false) = true := by decide +kernel
          intro k
          have hk := List.all_eq_true.mp hall k (List.mem_finRange k)
          cases hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C64 (4 * k.val + 3)).op <;> simp [hop] at hk ⊢
        have hno_earlier : ∀ l : Fin 13, ∀ i : Fin 64, i.val < 4 * l.val + 3 →
            PEqualNP.EdgeOwnership.InCone 26 C64 i.val (4 * l.val + 3) →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C64 i.val).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and := by
          have hall : (List.finRange 13).all (fun l =>
              (List.finRange 64).all (fun i =>
                if i.val < 4 * l.val + 3 then
                  if PEqualNP.EdgeOwnership.InCone 26 C64 i.val (4 * l.val + 3) then
                    match (PEqualNP.MetaComplexity.NestedCover.gateAt C64 i.val).op with
                    | PEqualNP.CircuitLowerBounds.GateOp.and => false
                    | _ => true
                  else true
                else true)) = true := by decide +kernel
          intro l i hi hic hop
          have hl := List.all_eq_true.mp hall l (List.mem_finRange l)
          have hhi := List.all_eq_true.mp hl i (List.mem_finRange i)
          simp [hi, hic, hop] at hhi
        have hmk : ∀ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
            ∀ x : Fin 26 → Bool, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true →
            lineVal x l.val = true := by
          intro p l hpl x hxp hxl
          simp only [lineVal, Bool.and_eq_true, Bool.or_eq_true]
          refine ⟨?_, ?_⟩
          · rw [hget_ofFn x (13 + l.val) (by omega)]; exact hxl
          · have hxp' : (List.ofFn x).getD p.val false = true := by
              rw [hget_ofFn x p.val (by omega)]; exact hxp
            rcases hpl with h | h | h | h
            · left; left; have hv : p.val = l.val := congrArg Fin.val h
              rw [Nat.mod_eq_of_lt l.2, ← hv]; exact hxp'
            · left; right; have hv : p.val = (l.val + 1) % 13 := by simpa [Fin.val_add] using congrArg Fin.val h
              rw [← hv]; exact hxp'
            · right; left; have hv : p.val = (l.val + 3) % 13 := by simpa [Fin.val_add] using congrArg Fin.val h
              rw [← hv]; exact hxp'
            · right; right; have hv : p.val = (l.val + 9) % 13 := by simpa [Fin.val_add] using congrArg Fin.val h
              rw [← hv]; exact hxp'
        rcases hshape u v huv with ⟨hu, hv, hpl⟩ | ⟨hv, hu, hpl⟩
        · let l : Fin 13 := ⟨v.val - 13, by have := v.2; omega⟩
          have hv13 : v.val - 13 < 13 := by have := v.2; omega
          simp only [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv13] at hpl
          refine ⟨4 * l.val + 3, by rw [hlen64]; omega, by rw [hlen64]; omega, his_and l, ?_, ?_⟩
          · rw [hgateVal_line _ l.val l.2]
            apply hmk ⟨u.val, hu⟩ l hpl
            · simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq]; left; ext; rfl
            · simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq]; right; ext; dsimp [l]; omega
          · intro i hi hic
            have hi64 : i < 64 := by omega
            exact fun hop => False.elim (hno_earlier l ⟨i, hi64⟩ hi hic hop)
        · let l : Fin 13 := ⟨u.val - 13, by have := u.2; omega⟩
          have hu13 : u.val - 13 < 13 := by have := u.2; omega
          simp only [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hu13] at hpl
          refine ⟨4 * l.val + 3, by rw [hlen64]; omega, by rw [hlen64]; omega, his_and l, ?_, ?_⟩
          · rw [hgateVal_line _ l.val l.2]
            apply hmk ⟨v.val, hv⟩ l hpl
            · simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq]; right; ext; rfl
            · simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq]; left; ext; dsimp [l]; omega
          · intro i hi hic
            have hi64 : i < 64 := by omega
            exact fun hop => False.elim (hno_earlier l ⟨i, hi64⟩ hi hic hop)
  · have hle : x1.size ≤ 63 := Nat.lt_succ_iff.mp (Nat.not_le.mp hbig)
    dsimp only at hHasJunk hNoJunk
    by_cases hhj : ∃ j < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x : Fin 26 → Bool, PEqualNP.EdgeOwnership.gateVal 26 x1 j x = true ∧ x1.eval (List.ofFn x) = false
    · obtain ⟨D, ⟨hD1, hD2⟩, hD3, G, hG1, hG2, hG3⟩ := hHasJunk x1 ⟨hx1, hfun⟩ hle hhj
      exact ⟨D, hD1, hD2, hD3, G, hG1, hG2, hG3⟩
    · have hnj : ∀ j < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin 26 → Bool, PEqualNP.EdgeOwnership.gateVal 26 x1 j x = true → x1.eval (List.ofFn x) = true := by
        intro j hj hop x hgv
        cases hval : x1.eval (List.ofFn x)
        · exact False.elim (hhj ⟨j, hj, hop, x, hgv, hval⟩)
        · rfl
      obtain ⟨D, ⟨hD1, hD2⟩, hD3, G, hG1, hG2, hG3⟩ := hNoJunk x1 ⟨hx1, hfun⟩ hle hnj
      exact ⟨D, hD1, hD2, hD3, G, hG1, hG2, hG3⟩

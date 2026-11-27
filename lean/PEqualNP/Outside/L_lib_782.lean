import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_782 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool)
    (r : Fin n) (c : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (W : Finset (Fin n) → Finset (Fin m) → Bool)
    (K : Finset (Fin n) → Finset (Fin m) → Bool → Bool),
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  r ∉ S → c ∉ T → (∀ i ∈ S, rc r i) → (∀ j ∈ T, cc c j) →
  (∃ u, ¬ rc r u) → (∃ v, ¬ cc c v) →
  (∀ l l' q q', l ⊆ l' → q ⊆ q' → W l q = true → W l' q' = true) →
  (∀ i j, let x : Finset (Fin n) := {i}
          let y : Finset (Fin m) := {j}
          A i j = K (x ∩ S) (y ∩ T) (W ((x \ S).erase r) ((y \ T).erase c))) →
  ∃ (u : Fin n) (v : Fin m), ¬ rc r u ∧ ¬ cc c v ∧
    (∀ i, i ∉ S ↔ i = r ∨ i = u) ∧ (∀ j, j ∉ T ↔ j = c ∨ j = v) ∧
    K ∅ ∅ false = K ∅ ∅ true ∧ W ∅ ∅ = false ∧ W {u} ∅ = true ∧
    W ∅ {v} = true ∧ W {u} {v} = true) := by
  intro n m A r c S T W K rowLE colLE rc cc hInjR hInjC hrS hcT hS hT hu0 hv0 hWmono hAK
  have inter_mem_S : ∀ i, i ∈ S → ({i} : Finset (Fin n)) ∩ S = {i} := fun i hi => by
    ext x; simp only [Finset.mem_inter, Finset.mem_singleton, and_iff_left_iff_imp]; rintro rfl; exact hi
  have inter_not_S : ∀ i, i ∉ S → ({i} : Finset (Fin n)) ∩ S = ∅ := fun i hi => by
    ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]; rintro rfl; exact hi
  have sdiff_mem_S : ∀ i, i ∈ S → (({i} : Finset (Fin n)) \ S).erase r = ∅ := fun i hi => by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨_, rfl, hns⟩; exact hns hi
  have sdiff_r : (({r} : Finset (Fin n)) \ S).erase r = ∅ := by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨hne, rfl, _⟩; exact hne rfl
  have sdiff_in_S : ∀ i, i ∉ S → i ≠ r → (({i} : Finset (Fin n)) \ S).erase r = {i} := fun i hi hne => by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl, _⟩; rfl
    · rintro rfl; exact ⟨hne, rfl, hi⟩
  have inter_mem_T : ∀ j, j ∈ T → ({j} : Finset (Fin m)) ∩ T = {j} := fun j hj => by
    ext x; simp only [Finset.mem_inter, Finset.mem_singleton, and_iff_left_iff_imp]; rintro rfl; exact hj
  have inter_not_T : ∀ j, j ∉ T → ({j} : Finset (Fin m)) ∩ T = ∅ := fun j hj => by
    ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]; rintro rfl; exact hj
  have sdiff_mem_T : ∀ j, j ∈ T → (({j} : Finset (Fin m)) \ T).erase c = ∅ := fun j hj => by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨_, rfl, hnt⟩; exact hnt hj
  have sdiff_c : (({c} : Finset (Fin m)) \ T).erase c = ∅ := by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨hne, rfl, _⟩; exact hne rfl
  have sdiff_in_T : ∀ j, j ∉ T → j ≠ c → (({j} : Finset (Fin m)) \ T).erase c = {j} := fun j hj hne => by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl, _⟩; rfl
    · rintro rfl; exact ⟨hne, rfl, hj⟩
  rcases hu0 with ⟨u, hu⟩
  rcases hv0 with ⟨v, hv⟩
  have huS : u ∉ S := fun h => hu (hS u h)
  have hur : u ≠ r := fun h => hu (Or.inl (fun _ hj => h ▸ hj))
  have hvT : v ∉ T := fun h => hv (hT v h)
  have hvc : v ≠ c := fun h => hv (Or.inl (fun _ hi => h ▸ hi))
  have hKeq : K ∅ ∅ false = K ∅ ∅ true := by
    by_contra hKne
    have hAic : ∀ i ∈ S, A i c = K {i} ∅ (W ∅ ∅) := fun i hi => by
      simpa [inter_mem_S i hi, inter_not_T c hcT, sdiff_mem_S i hi, sdiff_c] using hAK i c
    have hAiv : ∀ i ∈ S, A i v = K {i} ∅ (W ∅ {v}) := fun i hi => by
      simpa [inter_mem_S i hi, inter_not_T v hvT, sdiff_mem_S i hi, sdiff_in_T v hvT hvc] using hAK i v
    have hArc : A r c = K ∅ ∅ (W ∅ ∅) := by
      simpa [inter_not_S r hrS, inter_not_T c hcT, sdiff_r, sdiff_c] using hAK r c
    have hArv : A r v = K ∅ ∅ (W ∅ {v}) := by
      simpa [inter_not_S r hrS, inter_not_T v hvT, sdiff_r, sdiff_in_T v hvT hvc] using hAK r v
    have hAinc : ∀ i, i ∉ S → i ≠ r → A i c = K ∅ ∅ (W {i} ∅) := fun i hi hne => by
      simpa [inter_not_S i hi, inter_not_T c hcT, sdiff_in_S i hi hne, sdiff_c] using hAK i c
    have hAinv : ∀ i, i ∉ S → i ≠ r → A i v = K ∅ ∅ (W {i} {v}) := fun i hi hne => by
      simpa [inter_not_S i hi, inter_not_T v hvT, sdiff_in_S i hi hne, sdiff_in_T v hvT hvc] using hAK i v
    have hWcv_mono : ∀ l : Finset (Fin n), W l ∅ = true → W l {v} = true :=
      fun l hl => hWmono l l ∅ {v} (Finset.Subset.refl l) (Finset.empty_subset {v}) hl
    by_cases hWeq : W ∅ ∅ = W ∅ {v}
    · cases hKf : K ∅ ∅ false <;> cases hKt : K ∅ ∅ true
      · exact hKne (hKf.trans hKt.symm)
      · apply hv; left; intro i hic
        by_cases hiS : i ∈ S
        · rw [hAiv i hiS, ← hWeq, ← hAic i hiS]; exact hic
        · by_cases hir : i = r
          · subst hir; rw [hArv, ← hWeq, ← hArc]; exact hic
          · rw [hAinc i hiS hir] at hic
            rw [hAinv i hiS hir]
            cases hW1 : W {i} ∅
            · rw [hW1, hKf] at hic; exact Bool.noConfusion hic
            · rw [hWcv_mono {i} hW1, hKt]
      · apply hv; right; intro i hiv
        by_cases hiS : i ∈ S
        · rw [hAic i hiS, hWeq, ← hAiv i hiS]; exact hiv
        · by_cases hir : i = r
          · subst hir; rw [hArc, hWeq, ← hArv]; exact hiv
          · rw [hAinv i hiS hir] at hiv
            rw [hAinc i hiS hir]
            cases hW1 : W {i} ∅
            · rw [hKf]
            · rw [hWcv_mono {i} hW1, hKt] at hiv; exact Bool.noConfusion hiv
      · exact hKne (hKf.trans hKt.symm)
    · have hW00 : W ∅ ∅ = false := by
        cases h0 : W ∅ ∅
        · rfl
        · exfalso; exact hWeq (h0.trans (hWcv_mono ∅ h0).symm)
      have hW0v : W ∅ {v} = true := by
        cases h1 : W ∅ {v}
        · exfalso; exact hWeq (hW00.trans h1.symm)
        · rfl
      have hWiv : ∀ i : Fin n, W {i} {v} = true := fun i =>
        hWmono ∅ {i} {v} {v} (Finset.empty_subset {i}) (Finset.Subset.refl {v}) hW0v
      cases hKf : K ∅ ∅ false <;> cases hKt : K ∅ ∅ true
      · exact hKne (hKf.trans hKt.symm)
      · apply hv; left; intro i hic
        by_cases hiS : i ∈ S
        · by_contra hnv
          have hnv' : A i v = false := Bool.eq_false_iff.mpr hnv
          rcases hS i hiS with hri | hir
          · have h1 := hri v (by rw [hArv, hW0v, hKt])
            rw [hnv'] at h1; exact Bool.noConfusion h1
          · have h1 := hir c hic
            rw [hArc, hW00, hKf] at h1; exact Bool.noConfusion h1
        · by_cases hir : i = r
          · subst hir; rw [hArv, hW0v, hKt]
          · rw [hAinv i hiS hir, hWiv i, hKt]
      · apply hv; right; intro i hiv
        by_cases hiS : i ∈ S
        · by_contra hnc
          have hnc' : A i c = false := Bool.eq_false_iff.mpr hnc
          rcases hS i hiS with hri | hir
          · have h1 := hri c (by rw [hArc, hW00, hKf])
            rw [hnc'] at h1; exact Bool.noConfusion h1
          · have h1 := hir v hiv
            rw [hArv, hW0v, hKt] at h1; exact Bool.noConfusion h1
        · by_cases hir : i = r
          · subst hir; rw [hArc, hW00, hKf]
          · rw [hAinv i hiS hir, hWiv i, hKt] at hiv; exact Bool.noConfusion hiv
      · exact hKne (hKf.trans hKt.symm)
  have hKconst : ∀ b : Bool, K ∅ ∅ b = K ∅ ∅ false := fun b => by
    cases b
    · rfl
    · exact hKeq.symm
  have hRowEq : ∀ i1 i2 : Fin n, i1 ∉ S → i2 ∉ S →
      W (({i1} \ S).erase r) ∅ = W (({i2} \ S).erase r) ∅ → i1 = i2 := by
    intro i1 i2 h1 h2 hW
    apply hInjR
    funext j
    rw [hAK i1 j, hAK i2 j, inter_not_S i1 h1, inter_not_S i2 h2]
    by_cases hjT : j ∈ T
    · rw [inter_mem_T j hjT, sdiff_mem_T j hjT, hW]
    · simp only [inter_not_T j hjT, hKconst]
  have hColEq : ∀ j1 j2 : Fin m, j1 ∉ T → j2 ∉ T →
      W ∅ (({j1} \ T).erase c) = W ∅ (({j2} \ T).erase c) → j1 = j2 := by
    intro j1 j2 h1 h2 hW
    apply hInjC
    funext i
    dsimp only
    rw [hAK i j1, hAK i j2, inter_not_T j1 h1, inter_not_T j2 h2]
    by_cases hiS : i ∈ S
    · rw [inter_mem_S i hiS, sdiff_mem_S i hiS, hW]
    · simp only [inter_not_S i hiS, hKconst]
  have hWu_ne : W {u} ∅ ≠ W ∅ ∅ := fun h => by
    apply hur
    apply hRowEq u r huS hrS
    rw [sdiff_in_S u huS hur, sdiff_r]
    exact h
  have hW00 : W ∅ ∅ = false := by
    cases h0 : W ∅ ∅
    · rfl
    · exfalso
      have h1 : W {u} ∅ = true :=
        hWmono ∅ {u} ∅ ∅ (Finset.empty_subset {u}) (Finset.Subset.refl ∅) h0
      exact hWu_ne (h1.trans h0.symm)
  have hWu0 : W {u} ∅ = true := by
    cases h1 : W {u} ∅
    · exfalso; exact hWu_ne (h1.trans hW00.symm)
    · rfl
  have hWv_ne : W ∅ {v} ≠ W ∅ ∅ := fun h => by
    apply hvc
    apply hColEq v c hvT hcT
    rw [sdiff_in_T v hvT hvc, sdiff_c]
    exact h
  have hW0v : W ∅ {v} = true := by
    cases h1 : W ∅ {v}
    · exfalso; exact hWv_ne (h1.trans hW00.symm)
    · rfl
  have hWuv : W {u} {v} = true :=
    hWmono {u} {u} ∅ {v} (Finset.Subset.refl {u}) (Finset.empty_subset {v}) hWu0
  have hRows : ∀ i, i ∉ S ↔ i = r ∨ i = u := by
    intro i
    constructor
    · intro hiS
      cases hWi : W (({i} \ S).erase r) ∅
      · left
        apply hRowEq i r hiS hrS
        rw [hWi, sdiff_r, hW00]
      · right
        apply hRowEq i u hiS huS
        rw [hWi, sdiff_in_S u huS hur, hWu0]
    · rintro (rfl | rfl)
      · exact hrS
      · exact huS
  have hCols : ∀ j, j ∉ T ↔ j = c ∨ j = v := by
    intro j
    constructor
    · intro hjT
      cases hWj : W ∅ (({j} \ T).erase c)
      · left
        apply hColEq j c hjT hcT
        rw [hWj, sdiff_c, hW00]
      · right
        apply hColEq j v hjT hvT
        rw [hWj, sdiff_in_T v hvT hvc, hW0v]
    · rintro (rfl | rfl)
      · exact hcT
      · exact hvT
  exact ⟨u, v, hu, hv, hRows, hCols, hKeq, hW00, hWu0, hW0v, hWuv⟩

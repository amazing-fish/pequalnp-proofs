import PEqualNP.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace PEqualNP.Outside.L_lib_901_aux

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact (h rfl).elim
  · rfl

private lemma zmod2_eq_of_eq_zero_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rfl
  · exfalso; exact (by decide : (1 : ZMod 2) ≠ 0) (h.mp rfl)
  · exfalso; exact (by decide : (1 : ZMod 2) ≠ 0) (h.mpr rfl)
  · rfl

private lemma card_fintype_zmod2 (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] [Fintype M] :
    Fintype.card M = 2 ^ Module.finrank (ZMod 2) M := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := M)
  simp only [Nat.card_eq_fintype_card, ZMod.card] at h
  exact h

private lemma card_ker_mul_card_range {M N : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] [Fintype M]
    [AddCommGroup N] [Module (ZMod 2) N] [Fintype N]
    (f : M →ₗ[ZMod 2] N) [Fintype (LinearMap.ker f)] [Fintype (LinearMap.range f)] :
    Fintype.card (LinearMap.ker f) * Fintype.card (LinearMap.range f) = Fintype.card M := by
  rw [card_fintype_zmod2 (LinearMap.ker f), card_fintype_zmod2 (LinearMap.range f),
    ← pow_add, add_comm, LinearMap.finrank_range_add_finrank_ker, card_fintype_zmod2 M]

private lemma diff_trilinear_formula {V : Type*} [AddCommGroup V]
    (α β γ : V → ZMod 2)
    (hα : ∀ x y, α (x + y) = α x + α y)
    (hβ : ∀ x y, β (x + y) = β x + β y)
    (hγ : ∀ x y, γ (x + y) = γ x + γ y)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (hγ0 : γ 0 = 0)
    (w x y : V) :
    let diff := fun (f : V → ZMod 2) (a z : V) => f (z + a) - f z
    let g := fun z => α z * β z * γ z
    diff (diff (diff g w) x) y 0 =
      α w * (β x * γ y + γ x * β y) +
      α x * (β w * γ y + γ w * β y) +
      α y * (β w * γ x + γ w * β x) := by
  dsimp only
  simp only [zero_add, hα, hβ, hγ, hα0, hβ0, hγ0]
  ring

private lemma tv_form_eq {k m : ℕ} (A : Fin m → (Fin k → ZMod 2)) (h : (Fin k → ZMod 2) → ZMod 2)
    (w x y : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) :
    let diffS := fun (f : (Fin k → ZMod 2) → ZMod 2) (a z : Fin k → ZMod 2) => f (z + a) - f z
    let ts := fun (h : (Fin k → ZMod 2) → ZMod 2) (a b c : Fin k → ZMod 2) =>
      diffS (diffS (diffS h a) b) c 0
    let diffV := fun (f : ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) → ZMod 2)
      (a z : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) => f (z + a) - f z
    let tv := fun (f : ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) → ZMod 2)
      (a b c : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) =>
      diffV (diffV (diffV f a) b) c 0
    let form := fun (z : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) =>
      h z.1 + ∑ i : Fin m, dotProduct (A i) z.1 * z.2.1 i * z.2.2 i
    tv form w x y =
      ts h w.1 x.1 y.1 +
        ∑ i : Fin m,
          (dotProduct (A i) w.1 * (x.2.1 i * y.2.2 i + x.2.2 i * y.2.1 i) +
           dotProduct (A i) x.1 * (w.2.1 i * y.2.2 i + w.2.2 i * y.2.1 i) +
           dotProduct (A i) y.1 * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i)) := by
  dsimp only
  have h1 : ∀ i : Fin m,
      let g : ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) → ZMod 2 :=
        fun z => dotProduct (A i) z.1 * z.2.1 i * z.2.2 i
      let diff := fun (f : ((Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) → ZMod 2)
        (a z : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))) => f (z + a) - f z
      diff (diff (diff g w) x) y 0 =
        dotProduct (A i) w.1 * (x.2.1 i * y.2.2 i + x.2.2 i * y.2.1 i) +
        dotProduct (A i) x.1 * (w.2.1 i * y.2.2 i + w.2.2 i * y.2.1 i) +
        dotProduct (A i) y.1 * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i) := by
    intro i
    have htri := diff_trilinear_formula
      (fun z : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2)) => dotProduct (A i) z.1)
      (fun z => z.2.1 i)
      (fun z => z.2.2 i)
      (fun a b => by simp [dotProduct_add])
      (fun a b => rfl)
      (fun a b => rfl)
      (by simp) rfl rfl w x y
    simpa [mul_comm, mul_left_comm, mul_assoc] using htri
  have hsum :
      ((h (0 + y + x + w).1 + ∑ i : Fin m, dotProduct (A i) (0 + y + x + w).1 * (0 + y + x + w).2.1 i * (0 + y + x + w).2.2 i) -
       (h (0 + y + x).1 + ∑ i : Fin m, dotProduct (A i) (0 + y + x).1 * (0 + y + x).2.1 i * (0 + y + x).2.2 i) -
       ((h (0 + y + w).1 + ∑ i : Fin m, dotProduct (A i) (0 + y + w).1 * (0 + y + w).2.1 i * (0 + y + w).2.2 i) -
        (h (0 + y).1 + ∑ i : Fin m, dotProduct (A i) (0 + y).1 * (0 + y).2.1 i * (0 + y).2.2 i)) -
       ((h (0 + x + w).1 + ∑ i : Fin m, dotProduct (A i) (0 + x + w).1 * (0 + x + w).2.1 i * (0 + x + w).2.2 i) -
        (h (0 + x).1 + ∑ i : Fin m, dotProduct (A i) (0 + x).1 * (0 + x).2.1 i * (0 + x).2.2 i) -
        ((h (0 + w).1 + ∑ i : Fin m, dotProduct (A i) (0 + w).1 * (0 + w).2.1 i * (0 + w).2.2 i) -
         (h (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).1 +
          ∑ i : Fin m, dotProduct (A i) (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).1 *
            (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).2.1 i *
            (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).2.2 i)))) =
      (h (0 + y.1 + x.1 + w.1) - h (0 + y.1 + x.1) - (h (0 + y.1 + w.1) - h (0 + y.1)) -
       (h (0 + x.1 + w.1) - h (0 + x.1) - (h (0 + w.1) - h 0))) +
      ∑ i : Fin m,
        (dotProduct (A i) (0 + y + x + w).1 * (0 + y + x + w).2.1 i * (0 + y + x + w).2.2 i -
         dotProduct (A i) (0 + y + x).1 * (0 + y + x).2.1 i * (0 + y + x).2.2 i -
         (dotProduct (A i) (0 + y + w).1 * (0 + y + w).2.1 i * (0 + y + w).2.2 i -
          dotProduct (A i) (0 + y).1 * (0 + y).2.1 i * (0 + y).2.2 i) -
         (dotProduct (A i) (0 + x + w).1 * (0 + x + w).2.1 i * (0 + x + w).2.2 i -
          dotProduct (A i) (0 + x).1 * (0 + x).2.1 i * (0 + x).2.2 i -
          (dotProduct (A i) (0 + w).1 * (0 + w).2.1 i * (0 + w).2.2 i -
           dotProduct (A i) (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).1 *
             (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).2.1 i *
             (0 : (Fin k → ZMod 2) × ((Fin m → ZMod 2) × (Fin m → ZMod 2))).2.2 i))) := by
    simp only [Finset.sum_sub_distrib, Prod.fst_add, Prod.fst_zero]
    ring
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact h1 i

private lemma ts_linear {k : ℕ} (h : (Fin k → ZMod 2) → ZMod 2)
    (hcubic : ∀ a b c d x,
      let diffS := fun (f : (Fin k → ZMod 2) → ZMod 2) (a z : Fin k → ZMod 2) => f (z + a) - f z
      diffS (diffS (diffS (diffS h a) b) c) d x = 0)
    (w₁ a : Fin k → ZMod 2) :
    let diffS := fun (f : (Fin k → ZMod 2) → ZMod 2) (a z : Fin k → ZMod 2) => f (z + a) - f z
    let ts := fun (a b c : Fin k → ZMod 2) => diffS (diffS (diffS h a) b) c 0
    (∀ b₁ b₂, ts w₁ a (b₁ + b₂) = ts w₁ a b₁ + ts w₁ a b₂) ∧
    (∀ (c : ZMod 2) b, ts w₁ a (c • b) = c * ts w₁ a b) := by
  let diffS := fun (f : (Fin k → ZMod 2) → ZMod 2) (a z : Fin k → ZMod 2) => f (z + a) - f z
  have hconst : ∀ c x, diffS (diffS (diffS h w₁) a) c x = diffS (diffS (diffS h w₁) a) c 0 := by
    intro c x
    have h0 := hcubic w₁ a c x 0
    dsimp only at h0
    have h1 : diffS (diffS (diffS h w₁) a) c (0 + x) - diffS (diffS (diffS h w₁) a) c 0 = 0 := h0
    rw [zero_add, sub_eq_zero] at h1
    exact h1
  have hadd : ∀ b₁ b₂, diffS (diffS (diffS h w₁) a) (b₁ + b₂) 0 =
      diffS (diffS (diffS h w₁) a) b₁ 0 + diffS (diffS (diffS h w₁) a) b₂ 0 := by
    intro b₁ b₂
    let g := diffS (diffS h w₁) a
    have hstep : diffS g (b₁ + b₂) 0 = diffS g b₂ b₁ + diffS g b₁ 0 := by
      dsimp only [diffS]
      simp only [zero_add]
      ring
    rw [hstep, hconst b₂ b₁, add_comm]
  have hsmul : ∀ (c : ZMod 2) b, diffS (diffS (diffS h w₁) a) (c • b) 0 =
      c * diffS (diffS (diffS h w₁) a) b 0 := by
    intro c b
    rcases zmod2_cases c with rfl | rfl
    · simp [diffS]
    · simp
  exact ⟨hadd, hsmul⟩

private lemma ts_zero_left {k : ℕ} (h : (Fin k → ZMod 2) → ZMod 2) (a b : Fin k → ZMod 2) :
    let diffS := fun (f : (Fin k → ZMod 2) → ZMod 2) (a z : Fin k → ZMod 2) => f (z + a) - f z
    diffS (diffS (diffS h 0) a) b 0 = 0 := by
  dsimp only
  simp

private def dotLin {k : ℕ} (v : Fin k → ZMod 2) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun b => dotProduct v b
    map_add' := fun x y => by simp [dotProduct_add]
    map_smul' := fun c x => by simp [dotProduct_smul, smul_eq_mul] }

private lemma vec_eq_of_dot {k : ℕ} (u v : Fin k → ZMod 2) :
    (∀ b : Fin k → ZMod 2, dotProduct u b = dotProduct v b) ↔ u = v := by
  constructor
  · intro h
    ext r
    have hr := h (Pi.single r 1)
    simpa [dotProduct_single] using hr
  · rintro rfl _; rfl

private lemma ker_dotLin_card {k : ℕ} {v : Fin k → ZMod 2} (hv : v ≠ 0) :
    2 * ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun a => dotProduct v a = 0)).card = 2 ^ k := by
  let f := dotLin v
  have hsurj : Function.Surjective f := by
    intro y
    have hex : ∃ r : Fin k, v r ≠ 0 := by
      by_contra h
      exact hv (funext fun r => Classical.by_contradiction fun hr => h ⟨r, hr⟩)
    obtain ⟨r, hr⟩ := hex
    have hr1 : v r = 1 := zmod2_eq_one_of_ne_zero hr
    refine ⟨y • Pi.single r 1, ?_⟩
    simp [f, dotLin, dotProduct_smul, dotProduct_single, hr1]
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let _ : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  let _ : Fintype (LinearMap.range f) := Fintype.ofFinite _
  have hkm := card_ker_mul_card_range f
  have hcardS : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
    simp [Fintype.card_pi, ZMod.card]
  have hcardR : Fintype.card (LinearMap.range f) = 2 := by
    rw [card_fintype_zmod2 (LinearMap.range f), hrange, finrank_top, Module.finrank_self]
    rfl
  have hcardK : Fintype.card (LinearMap.ker f) =
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun a => dotProduct v a = 0)).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
        invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcardS, hcardR, hcardK] at hkm
  omega

end PEqualNP.Outside.L_lib_901_aux

open PEqualNP.Outside.L_lib_901_aux in
theorem PEqualNP.Outside.L_lib_901 : (∀ k m : ℕ,
  let F := ZMod 2
  let S := Fin k → F
  let D := Fin m → F
  let V := S × (D × D)
  let diffS := fun (f : S → F) (a x : S) => f (x+a) - f x
  let cubic := fun (h : S → F) => ∀ a b c d x, diffS (diffS (diffS (diffS h a) b) c) d x = 0
  let ts := fun (h : S → F) (a b c : S) => diffS (diffS (diffS h a) b) c 0
  let diffV := fun (f : V → F) (a x : V) => f (x+a) - f x
  let tv := fun (f : V → F) (a b c : V) => diffV (diffV (diffV f a) b) c 0
  let form := fun (A : Fin m → S) (h : S → F) (x : V) =>
    h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2 i
  let wt := fun (A : Fin m → S) (s : S) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) s ≠ 0)).card
  let good := fun (A : Fin m → S) => (∀ i, A i ≠ 0) ∧ (∀ s : S, s ≠ 0 → 2 ≤ wt A s)
  ∀ (A : Fin m → S) (h : S → F), cubic h → ∀ w : V,
    let J := (Finset.univ : Finset (Fin m)).filter (fun i =>
      dotProduct (A i) w.1 = 0 ∧ (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0))
    let K := (Finset.univ : Finset S).filter (fun a => ∀ i ∈ J, dotProduct (A i) a = 0)
    let inner := (K.filter (fun a => ∀ b ∈ K, ts h w.1 a b = 0)).card
    let rad := ((Finset.univ : Finset V).filter (fun x => ∀ y, tv (form A h) w x y = 0)).card
    rad * 2^k = 2^(2*(m-wt A w.1)) * K.card * inner ∧
      (good A → (4*rad = Fintype.card V ↔ w.1 = 0 ∧
        ∃ i : Fin m, (w.2.1 i ≠ 0 ∨ w.2.2 i ≠ 0) ∧ ∀ j : Fin m,
          (w.2.1 j ≠ 0 ∨ w.2.2 j ≠ 0) → A j = A i))) := by
  intro k m F S D V diffS cubic ts diffV tv form wt good A h hcubic w J K inner rad
  let I : Finset (Fin m) := Finset.univ.filter (fun i => dotProduct (A i) w.1 ≠ 0)
  let Ic : Finset (Fin m) := Iᶜ
  have hI_card : I.card = wt A w.1 := rfl
  have hIc_card : Ic.card = m - wt A w.1 := by
    have hsum : I.card + Ic.card = m := by simp [Ic]
    omega
  let Ksub : Submodule F S :=
    { carrier := {a : S | ∀ i ∈ J, dotProduct (A i) a = 0}
      , add_mem' := fun {a b} ha hb i hi => by
          change dotProduct (A i) (a + b) = 0
          rw [dotProduct_add, ha i hi, hb i hi, add_zero]
      zero_mem' := fun i _ => by simp
      smul_mem' := fun c {a} ha i hi => by
          change dotProduct (A i) (c • a) = 0
          rw [dotProduct_smul, ha i hi, smul_zero] }
  let _ : Fintype Ksub := Fintype.ofFinite Ksub
  have hKsub_card : Fintype.card Ksub = K.card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact
      { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
        invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let AnnK : Submodule F S :=
    { carrier := {v : S | ∀ b ∈ Ksub, dotProduct v b = 0}
      , add_mem' := fun {v₁ v₂} h1 h2 b hb => by
          change dotProduct (v₁ + v₂) b = 0
          rw [add_dotProduct, h1 b hb, h2 b hb, add_zero]
      zero_mem' := fun _ _ => by simp
      smul_mem' := fun c {v} h1 b hb => by
          change dotProduct (c • v) b = 0
          rw [smul_dotProduct, h1 b hb, smul_zero] }
  let _ : Fintype AnnK := Fintype.ofFinite AnnK
  have hAnn_finrank : Module.finrank F AnnK + Module.finrank F Ksub = k := by
    let ρ : S →ₗ[F] (Ksub →ₗ[F] F) :=
      { toFun := fun v => (dotLin v).comp Ksub.subtype
        map_add' := fun v₁ v₂ => by ext x; change dotProduct (v₁ + v₂) x.1 = dotProduct v₁ x.1 + dotProduct v₂ x.1; rw [add_dotProduct]
        map_smul' := fun c v => by ext x; change dotProduct (c • v) x.1 = c * dotProduct v x.1; rw [smul_dotProduct, smul_eq_mul] }
    have hkerρ : LinearMap.ker ρ = AnnK := by
      ext v
      simp [ρ, AnnK, dotLin, LinearMap.mem_ker, LinearMap.ext_iff]
    have hsurjρ : Function.Surjective ρ := by
      obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Ksub.subtype (Submodule.ker_subtype Ksub)
      intro ψ
      refine ⟨fun r => ψ (L (Pi.single r 1)), ?_⟩
      ext x
      change dotProduct (fun r => ψ (L (Pi.single r 1))) x.1 = ψ x
      have hx : Ksub.subtype x = ∑ r : Fin k, x.1 r • Pi.single r (1 : F) := by
        ext r; simp [Finset.sum_apply, Pi.single_apply]
      have hLx : L (Ksub.subtype x) = x := LinearMap.congr_fun hL x
      calc dotProduct (fun r => ψ (L (Pi.single r 1))) x.1
          = ∑ r : Fin k, ψ (L (Pi.single r 1)) * x.1 r := rfl
        _ = ∑ r : Fin k, x.1 r * ψ (L (Pi.single r 1)) := by
            apply Finset.sum_congr rfl; intro r _; ring
        _ = ψ (L (∑ r : Fin k, x.1 r • Pi.single r (1 : F))) := by
            simp [map_sum, map_smul, smul_eq_mul]
        _ = ψ (L (Ksub.subtype x)) := by rw [← hx]
        _ = ψ x := by rw [hLx]
    have hrangeρ : LinearMap.range ρ = ⊤ := LinearMap.range_eq_top.mpr hsurjρ
    have hrank := LinearMap.finrank_range_add_finrank_ker ρ
    have hfrS : Module.finrank F S = k := by simp [S, Module.finrank_pi]
    have hfrRan : Module.finrank F (LinearMap.range ρ) = Module.finrank F Ksub := by
      rw [hrangeρ, finrank_top]
      exact Subspace.dual_finrank_eq
    rw [hkerρ, hfrRan, hfrS] at hrank
    omega
  have hAnn_card : Fintype.card AnnK * K.card = 2 ^ k := by
    rw [← hKsub_card, card_fintype_zmod2 AnnK, card_fintype_zmod2 Ksub, ← pow_add, hAnn_finrank]
  let T : (Ic → F × F) →ₗ[F] S :=
    { toFun := fun pq => ∑ i : Ic, (w.2.1 i.1 * (pq i).2 + w.2.2 i.1 * (pq i).1) • A i.1
      map_add' := fun pq₁ pq₂ => by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← add_smul]
        congr 1
        change w.2.1 i.1 * ((pq₁ i).2 + (pq₂ i).2) + w.2.2 i.1 * ((pq₁ i).1 + (pq₂ i).1) = _
        ring
      map_smul' := fun c pq => by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        change w.2.1 i.1 * (c * (pq i).2) + w.2.2 i.1 * (c * (pq i).1) =
          c * (w.2.1 i.1 * (pq i).2 + w.2.2 i.1 * (pq i).1)
        ring }
  have hT_dot : ∀ (pq : Ic → F × F) (b : S),
      dotProduct (T pq) b = ∑ i : Ic, (w.2.1 i.1 * (pq i).2 + w.2.2 i.1 * (pq i).1) * dotProduct (A i.1) b := by
    intro pq b
    change dotProduct (∑ i : Ic, (w.2.1 i.1 * (pq i).2 + w.2.2 i.1 * (pq i).1) • A i.1) b = _
    rw [sum_dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_dotProduct, smul_eq_mul]
  let _ : Fintype (LinearMap.ker T) := Fintype.ofFinite _
  let _ : Fintype (LinearMap.range T) := Fintype.ofFinite _
  have hrangeT_le : LinearMap.range T ≤ AnnK := by
    rintro _ ⟨pq, rfl⟩ b hb
    change dotProduct (T pq) b = 0
    rw [hT_dot]
    apply Finset.sum_eq_zero
    intro i _
    have hi0 : dotProduct (A i.1) w.1 = 0 := by
      have hni : i.1 ∉ I := Finset.mem_compl.mp i.2
      simpa [I] using hni
    by_cases hocc : w.2.1 i.1 ≠ 0 ∨ w.2.2 i.1 ≠ 0
    · have hiJ : i.1 ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, hocc⟩
      rw [hb i.1 hiJ, mul_zero]
    · have hu : w.2.1 i.1 = 0 := Classical.by_contradiction fun h => hocc (Or.inl h)
      have hv : w.2.2 i.1 = 0 := Classical.by_contradiction fun h => hocc (Or.inr h)
      rw [hu, hv]; simp
  have hA_mem_rangeT : ∀ i ∈ J, A i ∈ LinearMap.range T := by
    intro i hiJ
    have hiSpec := (Finset.mem_filter.mp hiJ).2
    have hiIc : i ∈ Ic := by
      rw [Finset.mem_compl]
      simp [I, hiSpec.1]
    rcases hiSpec.2 with hu | hv
    · have hu1 : w.2.1 i = 1 := zmod2_eq_one_of_ne_zero hu
      refine ⟨fun j => if j = ⟨i, hiIc⟩ then (0, 1) else (0, 0), ?_⟩
      change ∑ j : Ic, (w.2.1 j.1 * (if j = ⟨i, hiIc⟩ then (0, 1) else (0, 0)).2 +
        w.2.2 j.1 * (if j = ⟨i, hiIc⟩ then (0, 1) else (0, 0)).1) • A j.1 = A i
      rw [Finset.sum_eq_single ⟨i, hiIc⟩]
      · simp [hu1]
      · intro j _ hne; simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · have hv1 : w.2.2 i = 1 := zmod2_eq_one_of_ne_zero hv
      refine ⟨fun j => if j = ⟨i, hiIc⟩ then (1, 0) else (0, 0), ?_⟩
      change ∑ j : Ic, (w.2.1 j.1 * (if j = ⟨i, hiIc⟩ then (1, 0) else (0, 0)).2 +
        w.2.2 j.1 * (if j = ⟨i, hiIc⟩ then (1, 0) else (0, 0)).1) • A j.1 = A i
      rw [Finset.sum_eq_single ⟨i, hiIc⟩]
      · simp [hv1]
      · intro j _ hne; simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
  have hrangeT_eq : LinearMap.range T = AnnK := by
    let E : S →ₗ[F] (LinearMap.range T →ₗ[F] F) :=
      { toFun := fun b =>
          { toFun := fun v => dotProduct v.1 b
            map_add' := fun v₁ v₂ => by change dotProduct (v₁.1 + v₂.1) b = dotProduct v₁.1 b + dotProduct v₂.1 b; rw [add_dotProduct]
            map_smul' := fun c v => by change dotProduct (c • v.1) b = c * dotProduct v.1 b; rw [smul_dotProduct, smul_eq_mul] }
        map_add' := fun b₁ b₂ => by ext v; change dotProduct v.1 (b₁ + b₂) = dotProduct v.1 b₁ + dotProduct v.1 b₂; rw [dotProduct_add]
        map_smul' := fun c b => by ext v; change dotProduct v.1 (c • b) = c * dotProduct v.1 b; rw [dotProduct_smul, smul_eq_mul] }
    have hkerE : LinearMap.ker E = Ksub := by
      ext b
      simp only [LinearMap.mem_ker, LinearMap.ext_iff, E, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.zero_apply]
      constructor
      · intro hb i hiJ
        exact hb ⟨A i, hA_mem_rangeT i hiJ⟩
      · intro hb v
        exact hrangeT_le v.2 b hb
    have hrankE := LinearMap.finrank_range_add_finrank_ker E
    have hfrS : Module.finrank F S = k := by simp [S, Module.finrank_pi]
    have hfrRanE_le : Module.finrank F (LinearMap.range E) ≤ Module.finrank F (LinearMap.range T) := by
      have h1 : Module.finrank F (LinearMap.range E) ≤ Module.finrank F (Module.Dual F (LinearMap.range T)) :=
        Submodule.finrank_le _
      have h2 : Module.finrank F (Module.Dual F (LinearMap.range T)) = Module.finrank F (LinearMap.range T) :=
        Subspace.dual_finrank_eq
      omega
    rw [hkerE, hfrS] at hrankE
    have hfr_le : Module.finrank F AnnK ≤ Module.finrank F (LinearMap.range T) := by omega
    exact Submodule.eq_of_le_of_finrank_le hrangeT_le hfr_le
  have hT_card_mul : Fintype.card (LinearMap.ker T) * Fintype.card AnnK = 2 ^ (2 * (m - wt A w.1)) := by
    have hkm := card_ker_mul_card_range T
    have hcardDom : Fintype.card (Ic → F × F) = 2 ^ (2 * (m - wt A w.1)) := by
      simp [F, Fintype.card_pi, Fintype.card_prod, ZMod.card, hIc_card, pow_mul]
    rw [card_fintype_zmod2 (LinearMap.range T), hrangeT_eq, ← card_fintype_zmod2 AnnK, hcardDom] at hkm
    exact hkm
  have hrad_iff : ∀ x : V, (∀ y : V, tv (form A h) w x y = 0) ↔
      (∀ i : Fin m, dotProduct (A i) w.1 * x.2.1 i + dotProduct (A i) x.1 * w.2.1 i = 0) ∧
      (∀ i : Fin m, dotProduct (A i) w.1 * x.2.2 i + dotProduct (A i) x.1 * w.2.2 i = 0) ∧
      (∀ b : S, ts h w.1 x.1 b +
        ∑ i : Fin m, dotProduct (A i) b * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i) = 0) := by
    intro x
    have htv : ∀ y : V, tv (form A h) w x y =
        ts h w.1 x.1 y.1 +
          ∑ i : Fin m,
            (dotProduct (A i) w.1 * (x.2.1 i * y.2.2 i + x.2.2 i * y.2.1 i) +
             dotProduct (A i) x.1 * (w.2.1 i * y.2.2 i + w.2.2 i * y.2.1 i) +
             dotProduct (A i) y.1 * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i)) :=
      fun y => tv_form_eq A h w x y
    constructor
    · intro hx
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hy := hx (0, (0, (Pi.single (M := fun _ => F) i (1 : F) : D)))
        rw [htv (0, (0, (Pi.single (M := fun _ => F) i (1 : F) : D)))] at hy
        have hts0 : ts h w.1 x.1 0 = 0 := by simp [ts, diffS]
        rw [hts0, zero_add] at hy
        have hsum : (∑ j : Fin m,
            (dotProduct (A j) w.1 * (x.2.1 j * (Pi.single (M := fun _ => F) i (1 : F) : D) j + x.2.2 j * (0 : D) j) +
             dotProduct (A j) x.1 * (w.2.1 j * (Pi.single (M := fun _ => F) i (1 : F) : D) j + w.2.2 j * (0 : D) j) +
             dotProduct (A j) (0 : S) * (w.2.1 j * x.2.2 j + w.2.2 j * x.2.1 j))) =
            dotProduct (A i) w.1 * x.2.1 i + dotProduct (A i) x.1 * w.2.1 i := by
          rw [Finset.sum_eq_single i]
          · simp [D, Pi.single_eq_same]
          · intro j _ hji; simp [D, Pi.single_eq_of_ne hji]
          · intro hi; exact (hi (Finset.mem_univ _)).elim
        rw [← hsum]
        exact hy
      · intro i
        have hy := hx (0, ((Pi.single (M := fun _ => F) i (1 : F) : D), 0))
        rw [htv (0, ((Pi.single (M := fun _ => F) i (1 : F) : D), 0))] at hy
        have hts0 : ts h w.1 x.1 0 = 0 := by simp [ts, diffS]
        rw [hts0, zero_add] at hy
        have hsum : (∑ j : Fin m,
            (dotProduct (A j) w.1 * (x.2.1 j * (0 : D) j + x.2.2 j * (Pi.single (M := fun _ => F) i (1 : F) : D) j) +
             dotProduct (A j) x.1 * (w.2.1 j * (0 : D) j + w.2.2 j * (Pi.single (M := fun _ => F) i (1 : F) : D) j) +
             dotProduct (A j) (0 : S) * (w.2.1 j * x.2.2 j + w.2.2 j * x.2.1 j))) =
            dotProduct (A i) w.1 * x.2.2 i + dotProduct (A i) x.1 * w.2.2 i := by
          rw [Finset.sum_eq_single i]
          · simp [D, Pi.single_eq_same]
          · intro j _ hji; simp [D, Pi.single_eq_of_ne hji]
          · intro hi; exact (hi (Finset.mem_univ _)).elim
        rw [← hsum]
        exact hy
      · intro b
        have hy := hx (b, (0, 0))
        rw [htv (b, (0, 0))] at hy
        simpa [D] using hy
    · rintro ⟨h1, h2, h3⟩ y
      rw [htv y]
      have hre : (∑ i : Fin m,
          (dotProduct (A i) w.1 * (x.2.1 i * y.2.2 i + x.2.2 i * y.2.1 i) +
           dotProduct (A i) x.1 * (w.2.1 i * y.2.2 i + w.2.2 i * y.2.1 i) +
           dotProduct (A i) y.1 * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i))) =
          (∑ i : Fin m, (dotProduct (A i) w.1 * x.2.1 i + dotProduct (A i) x.1 * w.2.1 i) * y.2.2 i) +
          (∑ i : Fin m, (dotProduct (A i) w.1 * x.2.2 i + dotProduct (A i) x.1 * w.2.2 i) * y.2.1 i) +
          (∑ i : Fin m, dotProduct (A i) y.1 * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i)) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hre]
      have hs1 : ∑ i : Fin m, (dotProduct (A i) w.1 * x.2.1 i + dotProduct (A i) x.1 * w.2.1 i) * y.2.2 i = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [h1 i, zero_mul])
      have hs2 : ∑ i : Fin m, (dotProduct (A i) w.1 * x.2.2 i + dotProduct (A i) x.1 * w.2.2 i) * y.2.1 i = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [h2 i, zero_mul])
      rw [hs1, hs2, zero_add, zero_add]
      exact h3 y.1
  let radSet : Finset V := Finset.univ.filter (fun x => ∀ y, tv (form A h) w x y = 0)
  let innerSet : Finset S := K.filter (fun a => ∀ b ∈ K, ts h w.1 a b = 0)
  let tsVec : S → S := fun a r => ts h w.1 a (Pi.single r 1)
  have htsVec_dot : ∀ (a b : S), dotProduct (tsVec a) b = ts h w.1 a b := by
    intro a b
    let φ : S →ₗ[F] F :=
      { toFun := fun c => ts h w.1 a c
        map_add' := (ts_linear h hcubic w.1 a).1
        map_smul' := (ts_linear h hcubic w.1 a).2 }
    have hb : b = ∑ r : Fin k, b r • Pi.single r (1 : F) := by
      ext r; simp [Finset.sum_apply, Pi.single_apply]
    calc dotProduct (tsVec a) b = ∑ r : Fin k, φ (Pi.single r 1) * b r := rfl
      _ = ∑ r : Fin k, b r * φ (Pi.single r 1) := by
          apply Finset.sum_congr rfl; intro r _; ring
      _ = φ (∑ r : Fin k, b r • Pi.single r (1 : F)) := by
          simp [map_sum, map_smul, smul_eq_mul]
      _ = φ b := by rw [← hb]
      _ = ts h w.1 a b := rfl
  have hrad_spec : ∀ x : V, x ∈ radSet ↔
      x.1 ∈ K ∧
      (∀ i ∈ I, x.2.1 i = dotProduct (A i) x.1 * w.2.1 i ∧ x.2.2 i = dotProduct (A i) x.1 * w.2.2 i) ∧
      T (fun i : Ic => (x.2.1 i.1, x.2.2 i.1)) = tsVec x.1 := by
    intro x
    simp only [radSet, Finset.mem_filter, Finset.mem_univ, true_and, hrad_iff]
    have hsplit : ∀ b : S,
        (∀ i ∈ I, x.2.1 i = dotProduct (A i) x.1 * w.2.1 i ∧ x.2.2 i = dotProduct (A i) x.1 * w.2.2 i) →
        (∑ i : Fin m, dotProduct (A i) b * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i)) =
          dotProduct (T (fun i : Ic => (x.2.1 i.1, x.2.2 i.1))) b := by
      intro b hact
      rw [hT_dot, ← Finset.sum_add_sum_compl I]
      have hI0 : ∑ i ∈ I, dotProduct (A i) b * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        obtain ⟨hp, hq⟩ := hact i hi
        rw [hp, hq]
        have hcancel : w.2.1 i * (dotProduct (A i) x.1 * w.2.2 i) +
            w.2.2 i * (dotProduct (A i) x.1 * w.2.1 i) = 0 := by
          have : w.2.1 i * (dotProduct (A i) x.1 * w.2.2 i) +
              w.2.2 i * (dotProduct (A i) x.1 * w.2.1 i) =
              (dotProduct (A i) x.1 * w.2.1 i * w.2.2 i) + (dotProduct (A i) x.1 * w.2.1 i * w.2.2 i) := by ring
          rw [this, zmod2_add_self]
        rw [hcancel, mul_zero]
      rw [hI0, zero_add]
      change ∑ i ∈ Ic, dotProduct (A i) b * (w.2.1 i * x.2.2 i + w.2.2 i * x.2.1 i) = _
      rw [← Finset.sum_coe_sort Ic]
      apply Finset.sum_congr rfl; intro i _; ring
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hact : ∀ i ∈ I, x.2.1 i = dotProduct (A i) x.1 * w.2.1 i ∧
          x.2.2 i = dotProduct (A i) x.1 * w.2.2 i := by
        intro i hi
        have h1w : dotProduct (A i) w.1 = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
        have hp := h1 i
        have hq := h2 i
        rw [h1w, one_mul] at hp hq
        constructor
        · have : x.2.1 i + (dotProduct (A i) x.1 * w.2.1 i + dotProduct (A i) x.1 * w.2.1 i) =
              dotProduct (A i) x.1 * w.2.1 i := by
            rw [← add_assoc, hp, zero_add]
          rwa [zmod2_add_self, add_zero] at this
        · have : x.2.2 i + (dotProduct (A i) x.1 * w.2.2 i + dotProduct (A i) x.1 * w.2.2 i) =
              dotProduct (A i) x.1 * w.2.2 i := by
            rw [← add_assoc, hq, zero_add]
          rwa [zmod2_add_self, add_zero] at this
      have hxK : x.1 ∈ K := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun i hiJ => ?_⟩
        have hiSpec := (Finset.mem_filter.mp hiJ).2
        have hp := h1 i
        have hq := h2 i
        rw [hiSpec.1, zero_mul, zero_add] at hp hq
        rcases hiSpec.2 with hu | hv
        · rw [zmod2_eq_one_of_ne_zero hu, mul_one] at hp; exact hp
        · rw [zmod2_eq_one_of_ne_zero hv, mul_one] at hq; exact hq
      refine ⟨hxK, hact, ?_⟩
      rw [← vec_eq_of_dot]
      intro b
      have hb := h3 b
      rw [hsplit b hact, ← htsVec_dot x.1 b] at hb
      have h1' : dotProduct (T (fun i : Ic => (x.2.1 i.1, x.2.2 i.1))) b +
          (dotProduct (tsVec x.1) b + dotProduct (tsVec x.1) b) = dotProduct (tsVec x.1) b := by
        rw [← add_assoc, add_comm (dotProduct (T _) b), hb, zero_add]
      rwa [zmod2_add_self, add_zero] at h1'
    · rintro ⟨hxK, hact, hT⟩
      have h12 : (∀ i : Fin m, dotProduct (A i) w.1 * x.2.1 i + dotProduct (A i) x.1 * w.2.1 i = 0) ∧
          (∀ i : Fin m, dotProduct (A i) w.1 * x.2.2 i + dotProduct (A i) x.1 * w.2.2 i = 0) := by
        constructor <;> intro i <;> by_cases hi : i ∈ I
        · have h1w : dotProduct (A i) w.1 = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
          rw [h1w, one_mul, (hact i hi).1, zmod2_add_self]
        · have h0w : dotProduct (A i) w.1 = 0 := by simpa [I] using hi
          rw [h0w, zero_mul, zero_add]
          by_cases hu : w.2.1 i = 0
          · rw [hu, mul_zero]
          · have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0w, Or.inl hu⟩
            rw [(Finset.mem_filter.mp hxK).2 i hiJ, zero_mul]
        · have h1w : dotProduct (A i) w.1 = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
          rw [h1w, one_mul, (hact i hi).2, zmod2_add_self]
        · have h0w : dotProduct (A i) w.1 = 0 := by simpa [I] using hi
          rw [h0w, zero_mul, zero_add]
          by_cases hv : w.2.2 i = 0
          · rw [hv, mul_zero]
          · have hiJ : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0w, Or.inr hv⟩
            rw [(Finset.mem_filter.mp hxK).2 i hiJ, zero_mul]
      refine ⟨h12.1, h12.2, fun b => ?_⟩
      rw [hsplit b hact, hT, htsVec_dot, zmod2_add_self]
  have hrad_proj : ∀ x ∈ radSet, x.1 ∈ innerSet := by
    intro x hx
    obtain ⟨hxK, _, hT⟩ := (hrad_spec x).mp hx
    rw [Finset.mem_filter]
    refine ⟨hxK, fun b hbK => ?_⟩
    have hmem : tsVec x.1 ∈ AnnK := by
      rw [← hrangeT_eq]
      exact ⟨_, hT⟩
    rw [← htsVec_dot]
    exact hmem b (Finset.mem_filter.mp hbK).2
  have hfiber_card : ∀ a ∈ innerSet,
      (radSet.filter (fun x => x.1 = a)).card = Fintype.card (LinearMap.ker T) := by
    intro a ha
    have haK : a ∈ K := (Finset.mem_filter.mp ha).1
    have htsAnn : tsVec a ∈ AnnK := by
      intro b hb
      rw [htsVec_dot]
      exact (Finset.mem_filter.mp ha).2 b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    have htsRan : tsVec a ∈ LinearMap.range T := by rwa [hrangeT_eq]
    obtain ⟨pq₀, hpq₀⟩ := htsRan
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    refine
      { toFun := fun x =>
          ⟨fun i : Ic => ((x.1.2.1 i.1, x.1.2.2 i.1) - pq₀ i), ?_⟩
        invFun := fun δ =>
          ⟨(a, (fun i => if hi : i ∈ I then dotProduct (A i) a * w.2.1 i
                  else (pq₀ ⟨i, Finset.mem_compl.mpr hi⟩ + δ.1 ⟨i, Finset.mem_compl.mpr hi⟩).1,
                fun i => if hi : i ∈ I then dotProduct (A i) a * w.2.2 i
                  else (pq₀ ⟨i, Finset.mem_compl.mpr hi⟩ + δ.1 ⟨i, Finset.mem_compl.mpr hi⟩).2)), ?_⟩
        left_inv := fun x => by
          apply Subtype.ext
          have hx := Finset.mem_filter.mp x.2
          obtain ⟨_, hact, _⟩ := (hrad_spec x.1).mp hx.1
          apply Prod.ext
          · exact hx.2.symm
          · apply Prod.ext <;> ext i <;> by_cases hi : i ∈ I
            · simp only [dif_pos hi]; have h1 := (hact i hi).1; rw [hx.2] at h1; exact h1.symm
            · simp only [dif_neg hi]; change (pq₀ ⟨i, _⟩).1 + (x.1.2.1 i - (pq₀ ⟨i, _⟩).1) = x.1.2.1 i; ring
            · simp only [dif_pos hi]; have h2 := (hact i hi).2; rw [hx.2] at h2; exact h2.symm
            · simp only [dif_neg hi]; change (pq₀ ⟨i, _⟩).2 + (x.1.2.2 i - (pq₀ ⟨i, _⟩).2) = x.1.2.2 i; ring
        right_inv := fun δ => by
          apply Subtype.ext; ext i
          · have hni : i.1 ∉ I := Finset.mem_compl.mp i.2
            simp only [dif_neg hni]
            change (pq₀ i).1 + (δ.1 i).1 - (pq₀ i).1 = (δ.1 i).1; ring
          · have hni : i.1 ∉ I := Finset.mem_compl.mp i.2
            simp only [dif_neg hni]
            change (pq₀ i).2 + (δ.1 i).2 - (pq₀ i).2 = (δ.1 i).2; ring }
    · have hx := Finset.mem_filter.mp x.2
      obtain ⟨_, _, hT⟩ := (hrad_spec x.1).mp hx.1
      change T ((fun i : Ic => (x.1.2.1 i.1, x.1.2.2 i.1)) - pq₀) = 0
      rw [map_sub, hpq₀, sub_eq_zero]
      rw [hx.2] at hT
      exact hT
    · rw [Finset.mem_filter]
      refine ⟨(hrad_spec _).mpr ⟨haK, ?_, ?_⟩, rfl⟩
      · intro i hi
        simp [dif_pos hi]
      · have hfun : (fun i : Ic =>
            ((if hi : i.1 ∈ I then dotProduct (A i.1) a * w.2.1 i.1
                else (pq₀ ⟨i.1, Finset.mem_compl.mpr hi⟩ + δ.1 ⟨i.1, Finset.mem_compl.mpr hi⟩).1),
             (if hi : i.1 ∈ I then dotProduct (A i.1) a * w.2.2 i.1
                else (pq₀ ⟨i.1, Finset.mem_compl.mpr hi⟩ + δ.1 ⟨i.1, Finset.mem_compl.mpr hi⟩).2))) =
            pq₀ + δ.1 := by
          ext i
          · have hni : i.1 ∉ I := Finset.mem_compl.mp i.2
            simp only [dif_neg hni]; rfl
          · have hni : i.1 ∉ I := Finset.mem_compl.mp i.2
            simp only [dif_neg hni]; rfl
        rw [hfun, map_add, hpq₀, δ.2, add_zero]
  have hrad_eq : rad = inner * Fintype.card (LinearMap.ker T) := by
    change radSet.card = innerSet.card * Fintype.card (LinearMap.ker T)
    have hpart : radSet.card = ∑ a ∈ innerSet, (radSet.filter (fun x => x.1 = a)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hx; exact ⟨x.1, hrad_proj x hx, hx, rfl⟩
        · rintro ⟨_, _, hx, _⟩; exact hx
      · intro a₁ _ a₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
    rw [hpart, Finset.sum_congr rfl hfiber_card, Finset.sum_const, smul_eq_mul]
  have hpart1 : rad * 2 ^ k = 2 ^ (2 * (m - wt A w.1)) * K.card * inner := by
    calc rad * 2 ^ k = (inner * Fintype.card (LinearMap.ker T)) * (Fintype.card AnnK * K.card) := by
          rw [hrad_eq, hAnn_card]
      _ = (Fintype.card (LinearMap.ker T) * Fintype.card AnnK) * K.card * inner := by ring
      _ = 2 ^ (2 * (m - wt A w.1)) * K.card * inner := by rw [hT_card_mul]
  refine ⟨hpart1, ?_⟩
  intro hgood
  have hcardV : Fintype.card V = 2 ^ (2 * m) * 2 ^ k := by
    have h1 : Fintype.card V = 2 ^ k * (2 ^ m * 2 ^ m) := by
      simp [V, S, D, F, Fintype.card_prod, Fintype.card_pi, ZMod.card]
    rw [h1, ← pow_add, show m + m = 2 * m by omega, mul_comm]
  have hwt_le : wt A w.1 ≤ m := by
    exact le_trans (Finset.card_le_univ _) (by simp)
  have heq_iff : 4 * rad = Fintype.card V ↔
      4 * K.card * inner = 2 ^ (2 * wt A w.1) * 2 ^ k * 2 ^ k := by
    have hpos1 : 0 < 2 ^ k := by positivity
    have hpos2 : 0 < 2 ^ (2 * (m - wt A w.1)) := by positivity
    have hpow : 2 ^ (2 * m) = 2 ^ (2 * (m - wt A w.1)) * 2 ^ (2 * wt A w.1) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · intro h4
      have hmul : 4 * (rad * 2 ^ k) = Fintype.card V * 2 ^ k := by
        calc 4 * (rad * 2 ^ k) = (4 * rad) * 2 ^ k := by ring
          _ = Fintype.card V * 2 ^ k := by rw [h4]
      rw [hpart1, hcardV, hpow] at hmul
      have hmul' : 2 ^ (2 * (m - wt A w.1)) * (4 * K.card * inner) =
          2 ^ (2 * (m - wt A w.1)) * (2 ^ (2 * wt A w.1) * 2 ^ k * 2 ^ k) := by
        linarith
      exact Nat.eq_of_mul_eq_mul_left hpos2 hmul'
    · intro h4
      have hmul : (4 * rad) * 2 ^ k = Fintype.card V * 2 ^ k := by
        calc (4 * rad) * 2 ^ k = 4 * (rad * 2 ^ k) := by ring
          _ = 2 ^ (2 * (m - wt A w.1)) * (4 * K.card * inner) := by rw [hpart1]; ring
          _ = 2 ^ (2 * (m - wt A w.1)) * (2 ^ (2 * wt A w.1) * 2 ^ k * 2 ^ k) := by rw [h4]
          _ = Fintype.card V * 2 ^ k := by rw [hcardV, hpow]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos1 hmul
  rw [heq_iff]
  constructor
  · intro h4
    have hK_le : K.card ≤ 2 ^ k := by
      have : K.card ≤ (Finset.univ : Finset S).card := Finset.card_le_univ K
      simpa [S, F, Fintype.card_pi, ZMod.card] using this
    have hinner_le : inner ≤ K.card := Finset.card_filter_le _ _
    have hw1 : w.1 = 0 := by
      by_contra hne
      have hwt2 : 2 ≤ wt A w.1 := hgood.2 w.1 hne
      have hpow16 : 16 ≤ 2 ^ (2 * wt A w.1) := by
        have : 2 ^ 4 ≤ 2 ^ (2 * wt A w.1) := Nat.pow_le_pow_right (by omega) (by omega)
        norm_num at this
        exact this
      have hupper : 4 * K.card * inner ≤ 4 * (2 ^ k * 2 ^ k) := by
        have h1 : K.card * inner ≤ 2 ^ k * 2 ^ k :=
          Nat.mul_le_mul hK_le (le_trans hinner_le hK_le)
        calc 4 * K.card * inner = 4 * (K.card * inner) := by ring
          _ ≤ 4 * (2 ^ k * 2 ^ k) := Nat.mul_le_mul_left 4 h1
      have hlower : 16 * (2 ^ k * 2 ^ k) ≤ 2 ^ (2 * wt A w.1) * 2 ^ k * 2 ^ k := by
        calc 16 * (2 ^ k * 2 ^ k) ≤ 2 ^ (2 * wt A w.1) * (2 ^ k * 2 ^ k) :=
              Nat.mul_le_mul_right _ hpow16
          _ = 2 ^ (2 * wt A w.1) * 2 ^ k * 2 ^ k := by ring
      have hpos : 0 < 2 ^ k * 2 ^ k := by positivity
      omega
    have hwt0 : wt A w.1 = 0 := by
      rw [hw1]
      simp [wt]
    have hinner_eq : inner = K.card := by
      dsimp only [inner]
      rw [hw1]
      have htriv : ∀ a ∈ K, ∀ b ∈ K, ts h 0 a b = 0 := fun a _ b _ => ts_zero_left h a b
      rw [Finset.filter_true_of_mem htriv]
    rw [hwt0, hinner_eq] at h4
    simp only [mul_zero, pow_zero, one_mul] at h4
    have h2K : 2 * K.card = 2 ^ k := by
      have hsq : (2 * K.card) * (2 * K.card) = 2 ^ k * 2 ^ k := by linarith
      nlinarith
    have hJne : J.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hKuniv : K = Finset.univ := by
        ext a; simp [K, hempty]
      have hK2k : K.card = 2 ^ k := by
        rw [hKuniv]; simp [S, F, Fintype.card_pi, ZMod.card]
      have hpos : 0 < 2 ^ k := by positivity
      omega
    obtain ⟨i₀, hi₀J⟩ := hJne
    have hi₀_occ : w.2.1 i₀ ≠ 0 ∨ w.2.2 i₀ ≠ 0 := (Finset.mem_filter.mp hi₀J).2.2
    refine ⟨hw1, i₀, hi₀_occ, ?_⟩
    intro j hj_occ
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hw1]; simp, hj_occ⟩
    let Ki : Finset S := Finset.univ.filter (fun a => dotProduct (A i₀) a = 0)
    let Kj : Finset S := Finset.univ.filter (fun a => dotProduct (A j) a = 0)
    have hK_sub_i : K ⊆ Ki := fun a ha =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2 i₀ hi₀J⟩
    have hK_sub_j : K ⊆ Kj := fun a ha =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2 j hjJ⟩
    have hKi_card : 2 * Ki.card = 2 ^ k := ker_dotLin_card (hgood.1 i₀)
    have hKj_card : 2 * Kj.card = 2 ^ k := ker_dotLin_card (hgood.1 j)
    have hK_eq_i : K = Ki := Finset.eq_of_subset_of_card_le hK_sub_i (by omega)
    have hK_eq_j : K = Kj := Finset.eq_of_subset_of_card_le hK_sub_j (by omega)
    have hKi_eq_Kj : Ki = Kj := hK_eq_i.symm.trans hK_eq_j
    ext r
    have hiff : dotProduct (A j) (Pi.single r 1) = 0 ↔ dotProduct (A i₀) (Pi.single r 1) = 0 := by
      have hmem : Pi.single r (1 : F) ∈ Ki ↔ Pi.single r (1 : F) ∈ Kj := by rw [hKi_eq_Kj]
      simpa [Ki, Kj] using hmem.symm
    have hdot : dotProduct (A j) (Pi.single r 1) = dotProduct (A i₀) (Pi.single r 1) :=
      zmod2_eq_of_eq_zero_iff hiff
    simpa [dotProduct_single] using hdot
  · rintro ⟨hw1, i₀, hi₀_occ, hall⟩
    have hwt0 : wt A w.1 = 0 := by rw [hw1]; simp [wt]
    have hinner_eq : inner = K.card := by
      dsimp only [inner]
      rw [hw1]
      have htriv : ∀ a ∈ K, ∀ b ∈ K, ts h 0 a b = 0 := fun a _ b _ => ts_zero_left h a b
      rw [Finset.filter_true_of_mem htriv]
    have hi₀J : i₀ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hw1]; simp, hi₀_occ⟩
    have hK_eq : K = Finset.univ.filter (fun a => dotProduct (A i₀) a = 0) := by
      ext a
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ha; exact ha i₀ hi₀J
      · intro ha j hjJ
        rw [hall j (Finset.mem_filter.mp hjJ).2.2]
        exact ha
    have h2K : 2 * K.card = 2 ^ k := by
      rw [hK_eq]
      exact ker_dotLin_card (hgood.1 i₀)
    rw [hwt0, hinner_eq]
    calc 4 * K.card * K.card = (2 * K.card) * (2 * K.card) := by ring
      _ = 2 ^ k * 2 ^ k := by rw [h2K]
      _ = 2 ^ (2 * 0) * 2 ^ k * 2 ^ k := by ring

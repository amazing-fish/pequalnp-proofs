import PEqualNP.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace PEqualNP.Outside.L_lib_803_aux

section FieldProps

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K] [Fintype K]

private abbrev F := ZMod 2

private lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  match a with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private lemma add_self_K (x : K) : x + x = 0 := by
  have h : ((1 : F) + (1 : F)) • x = (1 : F) • x + (1 : F) • x := add_smul 1 1 x
  have h0 : (1 : F) + (1 : F) = 0 := rfl
  rw [h0, zero_smul, one_smul] at h
  exact h.symm

private lemma frob_add (x y : K) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  calc (x + y) ^ 2 = x ^ 2 + (x * y + x * y) + y ^ 2 := by ring
    _ = x ^ 2 + 0 + y ^ 2 := by rw [add_self_K]
    _ = x ^ 2 + y ^ 2 := by ring

private lemma frob_smul (a : F) (x : K) : (a • x) ^ 2 = a • (x ^ 2) := by
  rcases zmod2_cases a with rfl | rfl <;> simp

private def frobLM : K →ₗ[F] K where
  toFun := fun x => x ^ 2
  map_add' := frob_add
  map_smul' := fun a x => by simp [frob_smul]

private lemma card_K_eq : Fintype.card K = 2 ^ Module.finrank F K := by
  rw [Module.card_eq_pow_finrank (K := F) (V := K), ZMod.card]

private lemma card_sub_eq (W : Submodule F K) [Fintype W] :
    Fintype.card W = 2 ^ Module.finrank F W := by
  rw [Module.card_eq_pow_finrank (K := F) (V := W), ZMod.card]

private lemma pow_card_K (x : K) : x ^ (2 ^ Module.finrank F K) = x := by
  classical
  by_cases hx : x = 0
  · subst hx
    exact zero_pow (by positivity)
  · let u : Kˣ := Units.mk0 x hx
    have hcardU : Fintype.card Kˣ = 2 ^ Module.finrank F K - 1 := by
      rw [Fintype.card_units, card_K_eq]
    have hu : u ^ (2 ^ Module.finrank F K - 1) = 1 := by
      rw [← hcardU]
      exact pow_card_eq_one
    have hx1 : x ^ (2 ^ Module.finrank F K - 1) = 1 := by
      have := congrArg Units.val hu
      simpa [u] using this
    have hpos : 1 ≤ 2 ^ Module.finrank F K := Nat.one_le_two_pow
    calc x ^ (2 ^ Module.finrank F K)
        = x ^ (2 ^ Module.finrank F K - 1 + 1) := by rw [Nat.sub_add_cancel hpos]
      _ = x ^ (2 ^ Module.finrank F K - 1) * x := pow_succ _ _
      _ = 1 * x := by rw [hx1]
      _ = x := one_mul x

private def sqSub (L : Submodule F K) : Submodule F K :=
  Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))

private def extSub (L : Submodule F K) (x : K) : Submodule F K :=
  L ⊔ Submodule.span F {x}

private lemma mul_mem_sqSub {L : Submodule F K} {a b : K} (ha : a ∈ L) (hb : b ∈ L) :
    a * b ∈ sqSub L :=
  Submodule.subset_span ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

private lemma sqSub_mono {L1 L2 : Submodule F K} (h : L1 ≤ L2) : sqSub L1 ≤ sqSub L2 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact mul_mem_sqSub (h a.2) (h b.2)

private lemma sqSub_top : sqSub (⊤ : Submodule F K) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h := mul_mem_sqSub (L := (⊤ : Submodule F K)) (a := (1 : K)) (b := x) trivial trivial
  simpa using h

private lemma sqSub_extSub_eq (L : Submodule F K) (x : K) :
    sqSub (extSub L x) = sqSub L ⊔ (extSub L x).map (LinearMap.mulLeft F x) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, y', hy', rfl⟩
    rcases Submodule.mem_span_singleton.mp hy' with ⟨α, rfl⟩
    rcases Submodule.mem_sup.mp hz with ⟨b, hb, z', hz', rfl⟩
    rcases Submodule.mem_span_singleton.mp hz' with ⟨β, rfl⟩
    have hrew : (a + α • x) * (b + β • x) =
        a * b + x * (β • a + α • b + (α * β) • x) := by
      rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
          mul_smul_comm, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm,
          smul_smul, mul_comm x a, mul_comm x b]
      ring
    dsimp only
    rw [hrew]
    apply Submodule.add_mem_sup
    · exact mul_mem_sqSub ha hb
    · refine ⟨β • a + α • b + (α * β) • x, ?_, rfl⟩
      have h1 : β • a + α • b ∈ extSub L x :=
        Submodule.mem_sup_left (L.add_mem (L.smul_mem β ha) (L.smul_mem α hb))
      have h2 : (α * β) • x ∈ extSub L x :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x)))
      exact (extSub L x).add_mem h1 h2
  · apply sup_le
    · exact sqSub_mono le_sup_left
    · rintro _ ⟨y, hy, rfl⟩
      have hx : x ∈ extSub L x :=
        Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))
      exact mul_mem_sqSub hx hy

private lemma finrank_extSub_le (L : Submodule F K) (x : K) :
    Module.finrank F (extSub L x) ≤ Module.finrank F L + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span F {x})
  have h1 : Module.finrank F (Submodule.span F ({x} : Set K)) ≤ 1 := by
    by_cases hx : x = 0
    · subst hx
      rw [Submodule.span_zero_singleton, finrank_bot]
      exact Nat.zero_le 1
    · exact (finrank_span_singleton hx).le
  calc Module.finrank F (extSub L x)
      ≤ Module.finrank F ↥(L ⊔ Submodule.span F ({x} : Set K)) +
          Module.finrank F ↥(L ⊓ Submodule.span F ({x} : Set K)) := Nat.le_add_right _ _
    _ = Module.finrank F L + Module.finrank F (Submodule.span F ({x} : Set K)) := h
    _ ≤ Module.finrank F L + 1 := Nat.add_le_add_left h1 _

private lemma finrank_extSub_of_not_mem (L : Submodule F K) (x : K) (hx : x ∉ L) :
    Module.finrank F (extSub L x) = Module.finrank F L + 1 := by
  dsimp only [extSub]
  have h := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span F {x})
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ L.zero_mem)
  have hspan : Module.finrank F (Submodule.span F ({x} : Set K)) = 1 :=
    finrank_span_singleton hx0
  have hinf : L ⊓ Submodule.span F {x} = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases hy with ⟨hyL, hys⟩
    rcases Submodule.mem_span_singleton.mp hys with ⟨a, rfl⟩
    rcases zmod2_cases a with rfl | rfl
    · simp
    · exfalso; exact hx (by simpa using hyL)
  rw [hinf, finrank_bot, add_zero, hspan] at h
  exact h

private lemma finrank_sqSub_extSub_le (L : Submodule F K) (x : K) :
    Module.finrank F (sqSub (extSub L x)) ≤ Module.finrank F (sqSub L) + Module.finrank F L + 1 := by
  rw [sqSub_extSub_eq]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (sqSub L)
    ((extSub L x).map (LinearMap.mulLeft F x))
  have h2 : Module.finrank F ((extSub L x).map (LinearMap.mulLeft F x)) ≤
      Module.finrank F (extSub L x) := by
    have hmap : ((extSub L x).map (LinearMap.mulLeft F x)) =
        LinearMap.range ((LinearMap.mulLeft F x).comp (extSub L x).subtype) := by
      ext y; simp [Submodule.mem_map, LinearMap.mem_range]
    rw [hmap]
    exact LinearMap.finrank_range_le _
  have h3 := finrank_extSub_le L x
  omega

private def resLM (W : Submodule F K) : (K →ₗ[F] F) →ₗ[F] (W →ₗ[F] F) where
  toFun := fun φ => φ.comp W.subtype
  map_add' := fun φ ψ => by ext w; simp
  map_smul' := fun a φ => by ext w; simp

private lemma resLM_surjective (W : Submodule F K) : Function.Surjective (resLM W) := by
  intro ψ
  obtain ⟨proj, hproj⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  refine ⟨ψ.comp proj, ?_⟩
  ext w
  change ψ (proj (W.subtype w)) = ψ w
  have hw : proj (W.subtype w) = w := LinearMap.ext_iff.mp hproj w
  rw [hw]

private lemma finrank_ker_resLM (W : Submodule F K) :
    Module.finrank F (LinearMap.ker (resLM W)) = Module.finrank F K - Module.finrank F W := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (resLM W)
  rw [LinearMap.range_eq_top.mpr (resLM_surjective W), finrank_top] at hrk
  have hW : Module.finrank F (W →ₗ[F] F) = Module.finrank F W := Subspace.dual_finrank_eq
  have hK : Module.finrank F (K →ₗ[F] F) = Module.finrank F K := Subspace.dual_finrank_eq
  rw [hW, hK] at hrk
  omega

private def mulPair (φ : K →ₗ[F] F) : K →ₗ[F] (K →ₗ[F] F) where
  toFun := fun u => φ.comp (LinearMap.mulLeft F u)
  map_add' := fun u v => by ext x; simp [add_mul]
  map_smul' := fun a u => by ext x; simp

private lemma mulPair_injective {φ : K →ₗ[F] F} (hφ : φ ≠ 0) :
    Function.Injective (mulPair φ) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  by_contra hu0
  have hex : ∃ w : K, φ w ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hφ
    ext w
    exact hall w
  rcases hex with ⟨w, hw⟩
  have h1 : (mulPair φ u) (u⁻¹ * w) = 0 := by rw [hu]; rfl
  simp only [mulPair, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.mulLeft_apply] at h1
  rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at h1
  exact hw h1

private lemma mulPair_surjective {φ : K →ₗ[F] F} (hφ : φ ≠ 0) :
    Function.Surjective (mulPair φ) := by
  have hfin : Module.finrank F K = Module.finrank F (K →ₗ[F] F) :=
    (Subspace.dual_finrank_eq (K := F) (V := K)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp (mulPair_injective hφ)

private lemma exists_u_of_phi (hk : Module.finrank F K % 2 = 1)
    {φ : K →ₗ[F] F} (hφ : φ ≠ 0) :
    ∃ u : K, (∀ x : K, φ (x ^ 2) = φ (u * x)) ∧ φ (u ^ 2) ≠ 0 := by
  obtain ⟨u, hu⟩ := mulPair_surjective hφ (φ.comp frobLM)
  have hu_eq : ∀ x : K, φ (x ^ 2) = φ (u * x) := fun x => by
    have h := congrArg (fun ψ => ψ x) hu
    simpa [mulPair, frobLM] using h.symm
  have hu_ne : u ≠ 0 := by
    intro hu0
    apply hφ
    ext x
    have hsurj : Function.Surjective (frobLM (K := K)) := by
      apply (LinearMap.injective_iff_surjective (f := frobLM (K := K))).mp
      rw [injective_iff_map_eq_zero]
      intro y hy
      change y ^ 2 = 0 at hy
      rw [sq] at hy
      exact mul_self_eq_zero.mp hy
    obtain ⟨y, rfl⟩ := hsurj x
    change φ (y ^ 2) = 0
    rw [hu_eq y, hu0, zero_mul, map_zero]
  let τ : K →ₗ[F] F := mulPair φ (u ^ 2)
  have hτ_ne : τ ≠ 0 := by
    intro h0
    have := mulPair_injective hφ (h0.trans (map_zero (mulPair φ)).symm)
    exact pow_ne_zero 2 hu_ne this
  have hτ_frob : ∀ y : K, τ (y ^ 2) = τ y := fun y => by
    change φ (u ^ 2 * y ^ 2) = φ (u ^ 2 * y)
    have h1 : u ^ 2 * y ^ 2 = (u * y) ^ 2 := by ring
    rw [h1, hu_eq (u * y)]
    have h2 : u * (u * y) = u ^ 2 * y := by ring
    rw [h2]
  have hτ_pow : ∀ (i : ℕ) (y : K), τ (y ^ (2 ^ i)) = τ y := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih =>
      intro y
      rw [pow_succ, pow_mul, hτ_frob, ih]
  have hex : ∃ y : K, τ y ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hτ_ne
    ext y
    exact hall y
  rcases hex with ⟨y, hy⟩
  have hy1 : τ y = 1 := by
    rcases zmod2_cases (τ y) with h0 | h1
    · exact (hy h0).elim
    · exact h1
  let k := Module.finrank F K
  let t : K := ∑ i ∈ Finset.range k, y ^ (2 ^ i)
  have ht2 : t ^ 2 = t := by
    have h1 : t ^ 2 = ∑ i ∈ Finset.range k, y ^ (2 ^ (i + 1)) := by
      change frobLM t = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (y ^ (2 ^ i)) ^ 2 = y ^ (2 ^ (i + 1))
      rw [← pow_mul, ← pow_succ]
    have h2 : (∑ i ∈ Finset.range k, y ^ (2 ^ (i + 1))) + y ^ (2 ^ 0) =
        (∑ i ∈ Finset.range k, y ^ (2 ^ i)) + y ^ (2 ^ k) := by
      rw [← Finset.sum_range_succ' (fun i => y ^ (2 ^ i)) k,
          ← Finset.sum_range_succ (fun i => y ^ (2 ^ i)) k]
    rw [← h1] at h2
    have h0 : y ^ (2 ^ 0) = y := by simp
    have hkpow : y ^ (2 ^ k) = y := pow_card_K y
    rw [h0, hkpow] at h2
    exact add_right_cancel h2
  have ht01 : t = 0 ∨ t = 1 := by
    have hmul : t * (t - 1) = 0 := by
      calc t * (t - 1) = t ^ 2 - t := by ring
        _ = 0 := sub_eq_zero.mpr ht2
    rcases mul_eq_zero.mp hmul with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hτt : τ t = 1 := by
    dsimp only [t]
    rw [map_sum]
    have hsum : (∑ i ∈ Finset.range k, τ (y ^ (2 ^ i))) = ∑ _i ∈ Finset.range k, (1 : F) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hτ_pow i y, hy1]
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hcast : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
      calc (k : ZMod 2) = ((2 * (k / 2) + k % 2 : ℕ) : ZMod 2) := by rw [Nat.div_add_mod]
        _ = (2 : ZMod 2) * ((k / 2 : ℕ) : ZMod 2) + ((k % 2 : ℕ) : ZMod 2) := by push_cast; rfl
        _ = ((k % 2 : ℕ) : ZMod 2) := by
            have h2 : (2 : ZMod 2) = 0 := rfl
            rw [h2, zero_mul, zero_add]
    rw [hcast, hk]
    rfl
  have ht1 : t = 1 := by
    rcases ht01 with h0 | h1
    · rw [h0, map_zero] at hτt
      exact (zero_ne_one hτt).elim
    · exact h1
  refine ⟨u, hu_eq, ?_⟩
  have hval : φ (u ^ 2) = τ 1 := by
    change φ (u ^ 2) = φ (u ^ 2 * 1)
    rw [mul_one]
  rw [hval, ← ht1, hτt]
  exact one_ne_zero

private lemma card_sols_of_phi (hk : Module.finrank F K % 2 = 1)
    (L : Submodule F K) {φ : K →ₗ[F] F} (hφ : φ ≠ 0)
    (hφS : ∀ w ∈ sqSub L, φ w = 0)
    [DecidablePred (fun x : K => ∀ w ∈ sqSub (extSub L x), φ w = 0)] :
    (Finset.univ.filter (fun x : K => ∀ w ∈ sqSub (extSub L x), φ w = 0)).card =
      2 ^ (Module.finrank F K - (Module.finrank F L + 1)) := by
  classical
  obtain ⟨u, hu_eq, hu2⟩ := exists_u_of_phi hk hφ
  have huL : u ∉ L := fun h => hu2 (by
    have hmem : u ^ 2 ∈ sqSub L := by
      rw [sq]
      exact mul_mem_sqSub h h
    exact hφS (u ^ 2) hmem)
  let L' : Submodule F K := extSub L u
  have hdimL' : Module.finrank F L' = Module.finrank F L + 1 :=
    finrank_extSub_of_not_mem L u huL
  let ev : K →ₗ[F] (L' →ₗ[F] F) := (resLM L').comp (mulPair φ)
  have hev_surj : Function.Surjective ev :=
    (resLM_surjective L').comp (mulPair_surjective hφ)
  have hker_dim : Module.finrank F (LinearMap.ker ev) =
      Module.finrank F K - (Module.finrank F L + 1) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.mpr hev_surj, finrank_top] at hrk
    have hL' : Module.finrank F (L' →ₗ[F] F) = Module.finrank F L' := Subspace.dual_finrank_eq
    rw [hL', hdimL'] at hrk
    omega
  have hmem_iff : ∀ x : K, (∀ w ∈ sqSub (extSub L x), φ w = 0) ↔ x ∈ LinearMap.ker ev := by
    intro x
    constructor
    · intro hx
      rw [LinearMap.mem_ker]
      ext ⟨w, hw⟩
      change φ (x * w) = 0
      rcases Submodule.mem_sup.mp hw with ⟨a, ha, w', hw', rfl⟩
      rcases Submodule.mem_span_singleton.mp hw' with ⟨α, rfl⟩
      rw [mul_add, map_add, mul_smul_comm, map_smul]
      have hax : x * a ∈ sqSub (extSub L x) := by
        rw [mul_comm]
        exact mul_mem_sqSub (Submodule.mem_sup_left ha)
          (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x)))
      have hux : φ (x * u) = 0 := by
        rw [mul_comm, ← hu_eq x]
        have hx2 : x ^ 2 ∈ sqSub (extSub L x) := by
          rw [sq]
          have hxm : x ∈ extSub L x :=
            Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))
          exact mul_mem_sqSub hxm hxm
        exact hx (x ^ 2) hx2
      rw [hx (x * a) hax, hux, smul_zero, add_zero]
    · intro hx w hw
      rw [LinearMap.mem_ker] at hx
      rw [sqSub_extSub_eq] at hw
      rcases Submodule.mem_sup.mp hw with ⟨s, hs, y', hy', rfl⟩
      rw [map_add, hφS s hs, zero_add]
      rcases hy' with ⟨y, hy, rfl⟩
      rcases Submodule.mem_sup.mp hy with ⟨a, ha, z', hz', rfl⟩
      rcases Submodule.mem_span_singleton.mp hz' with ⟨α, rfl⟩
      change φ (x * (a + α • x)) = 0
      rw [mul_add, map_add, mul_smul_comm, map_smul]
      have h1 : φ (x * a) = 0 := by
        have h := congrArg (fun ψ => ψ ⟨a, Submodule.mem_sup_left ha⟩) hx
        simpa [ev, resLM, mulPair] using h
      have h2 : φ (x * x) = 0 := by
        rw [← sq, hu_eq x, mul_comm]
        have h := congrArg (fun ψ => ψ ⟨u, Submodule.mem_sup_right
          (Submodule.subset_span (Set.mem_singleton u))⟩) hx
        simpa [ev, resLM, mulPair] using h
      rw [h1, h2, smul_zero, add_zero]
  have hfilt : (Finset.univ.filter (fun x : K => ∀ w ∈ sqSub (extSub L x), φ w = 0)).card =
      Fintype.card (LinearMap.ker ev) := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [hmem_iff]
  rw [hfilt, card_sub_eq, hker_dim]

private lemma quant_bound (hk : Module.finrank F K % 2 = 1) (L : Submodule F K) :
    let k := Module.finrank F K
    let c := k - Module.finrank F (sqSub L)
    let e := Module.finrank F L + 1
    let bad := fun x : K => Module.finrank F (sqSub (extSub L x)) < min k (Module.finrank F (sqSub L) + e)
    2 ^ (max c e) * (@Finset.filter K bad (fun x => Classical.propDecidable (bad x)) Finset.univ).card ≤
      2 ^ k * (2 ^ (min c e) - 1) := by
  classical
  intro k c e bad
  have hB_eq : (@Finset.filter K bad (fun x => Classical.propDecidable (bad x)) Finset.univ).card =
      (Finset.univ.filter bad).card := by
    congr 1
    ext x
    simp
  rw [hB_eq]
  let B := Finset.univ.filter bad
  by_cases hc0 : c = 0
  · have hSqTop : Module.finrank F (sqSub L) = k := by
      have hle : Module.finrank F (sqSub L) ≤ k := Submodule.finrank_le _
      omega
    have hB0 : B.card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      dsimp only [bad]
      have hle : Module.finrank F (sqSub L) ≤ Module.finrank F (sqSub (extSub L x)) :=
        Submodule.finrank_mono (sqSub_mono le_sup_left)
      omega
    rw [hB0, mul_zero]
    exact Nat.zero_le _
  · have hcpos : 1 ≤ c := Nat.pos_of_ne_zero hc0
    have he_le_k : e ≤ k := by
      have hLne : L ≠ ⊤ := by
        intro htop
        have hsq : sqSub L = ⊤ := by rw [htop]; exact sqSub_top
        have hdim : Module.finrank F (sqSub L) = k := by rw [hsq, finrank_top]
        omega
      have hlt : Module.finrank F L < k := Submodule.finrank_lt hLne
      omega
    have hc_le_k : c ≤ k := Nat.sub_le _ _
    have : Finite (K →ₗ[F] F) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
    let : Fintype (K →ₗ[F] F) := Fintype.ofFinite (K →ₗ[F] F)
    let Phi : Finset (K →ₗ[F] F) :=
      Finset.univ.filter (fun φ => φ ≠ 0 ∧ ∀ w ∈ sqSub L, φ w = 0)
    have hcard_ann : ∀ W : Submodule F K,
        (Finset.univ.filter (fun φ : K →ₗ[F] F => φ ≠ 0 ∧ ∀ w ∈ W, φ w = 0)).card =
          2 ^ (k - Module.finrank F W) - 1 := by
      intro W
      let A : Finset (K →ₗ[F] F) := Finset.univ.filter (fun φ => ∀ w ∈ W, φ w = 0)
      have hAcard : A.card = 2 ^ (k - Module.finrank F W) := by
        have h1 : A.card = Fintype.card (LinearMap.ker (resLM W)) := by
          rw [Fintype.card_subtype]
          congr 1
          ext φ
          simp [A, LinearMap.mem_ker, resLM, LinearMap.ext_iff]
        rw [h1, Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker (resLM W)),
            ZMod.card, finrank_ker_resLM]
      have h0A : (0 : K →ₗ[F] F) ∈ A := by simp [A]
      have hfilt : Finset.univ.filter (fun φ : K →ₗ[F] F => φ ≠ 0 ∧ ∀ w ∈ W, φ w = 0) =
          A.erase 0 := by
        ext φ
        simp [A]
      rw [hfilt, Finset.card_erase_of_mem h0A, hAcard]
    have hPhi_card : Phi.card = 2 ^ c - 1 := hcard_ann (sqSub L)
    have hdouble : (∑ x : K, (2 ^ (k - Module.finrank F (sqSub (extSub L x))) - 1)) =
        (2 ^ c - 1) * 2 ^ (k - e) := by
      have hLHS : (∑ x : K, (2 ^ (k - Module.finrank F (sqSub (extSub L x))) - 1)) =
          ∑ x : K, ∑ φ ∈ Phi, if (∀ w ∈ sqSub (extSub L x), φ w = 0) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← hcard_ann (sqSub (extSub L x)), ← Finset.card_filter]
        congr 1
        ext φ
        simp only [Phi, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h0, hW⟩
          exact ⟨⟨h0, fun w hw => hW w (sqSub_mono le_sup_left hw)⟩, hW⟩
        · rintro ⟨⟨h0, _⟩, hW⟩
          exact ⟨h0, hW⟩
      rw [hLHS, Finset.sum_comm]
      have hRHS : (∑ φ ∈ Phi, ∑ x : K, if (∀ w ∈ sqSub (extSub L x), φ w = 0) then 1 else 0) =
          ∑ _φ ∈ Phi, 2 ^ (k - e) := by
        apply Finset.sum_congr rfl
        intro φ hφ
        have hφ' := (Finset.mem_filter.mp hφ).2
        rw [← Finset.card_filter]
        exact card_sols_of_phi hk L hφ'.1 hφ'.2
      rw [hRHS, Finset.sum_const, smul_eq_mul, hPhi_card]
    by_cases hce : c ≤ e
    · have hmax : max c e = e := max_eq_right hce
      have hmin : min c e = c := min_eq_left hce
      rw [hmax, hmin]
      have hB_le : B.card ≤ ∑ x : K, (2 ^ (k - Module.finrank F (sqSub (extSub L x))) - 1) := by
        calc B.card = ∑ _x ∈ B, 1 := by simp
          _ ≤ ∑ x ∈ B, (2 ^ (k - Module.finrank F (sqSub (extSub L x))) - 1) := by
              apply Finset.sum_le_sum
              intro x hx
              have hbad : bad x := (Finset.mem_filter.mp hx).2
              dsimp only [bad] at hbad
              have hlt : Module.finrank F (sqSub (extSub L x)) < k := by omega
              have h1 : 1 ≤ k - Module.finrank F (sqSub (extSub L x)) := by omega
              have h2 : 2 ^ 1 ≤ 2 ^ (k - Module.finrank F (sqSub (extSub L x))) :=
                Nat.pow_le_pow_right (by omega) h1
              omega
          _ ≤ ∑ x : K, (2 ^ (k - Module.finrank F (sqSub (extSub L x))) - 1) :=
              Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      rw [hdouble] at hB_le
      have hmul := Nat.mul_le_mul_left (2 ^ e) hB_le
      have hpow : 2 ^ e * ((2 ^ c - 1) * 2 ^ (k - e)) = 2 ^ k * (2 ^ c - 1) := by
        calc 2 ^ e * ((2 ^ c - 1) * 2 ^ (k - e))
            = (2 ^ e * 2 ^ (k - e)) * (2 ^ c - 1) := by ring
          _ = 2 ^ (e + (k - e)) * (2 ^ c - 1) := by rw [← pow_add]
          _ = 2 ^ k * (2 ^ c - 1) := by rw [Nat.add_sub_of_le he_le_k]
      rw [hpow] at hmul
      exact hmul
    · have hec : e ≤ c := by omega
      have hmax : max c e = c := max_eq_left hec
      have hmin : min c e = e := min_eq_right hec
      rw [hmax, hmin]
      have hlower : ∀ x : K,
          (2 ^ (c - e) - 1) + (if x ∈ B then 2 ^ (c - e) else 0) ≤
            2 ^ (k - Module.finrank F (sqSub (extSub L x))) - 1 := by
        intro x
        have hup : Module.finrank F (sqSub (extSub L x)) ≤ Module.finrank F (sqSub L) + e := by
          have := finrank_sqSub_extSub_le L x
          omega
        by_cases hxB : x ∈ B
        · simp only [hxB, ↓reduceIte]
          have hbad : bad x := (Finset.mem_filter.mp hxB).2
          dsimp only [bad] at hbad
          have hsqle : Module.finrank F (sqSub L) ≤ k := Submodule.finrank_le _
          have hge : c - e + 1 ≤ k - Module.finrank F (sqSub (extSub L x)) := by omega
          have hpow : 2 ^ (c - e + 1) ≤ 2 ^ (k - Module.finrank F (sqSub (extSub L x))) :=
            Nat.pow_le_pow_right (by omega) hge
          have hpow2 : 2 ^ (c - e + 1) = 2 ^ (c - e) + 2 ^ (c - e) := by rw [pow_succ]; omega
          have hpos : 1 ≤ 2 ^ (c - e) := Nat.one_le_two_pow
          omega
        · simp only [hxB, ↓reduceIte, add_zero]
          have hsqle : Module.finrank F (sqSub L) ≤ k := Submodule.finrank_le _
          have hge : c - e ≤ k - Module.finrank F (sqSub (extSub L x)) := by omega
          have hpow : 2 ^ (c - e) ≤ 2 ^ (k - Module.finrank F (sqSub (extSub L x))) :=
            Nat.pow_le_pow_right (by omega) hge
          omega
      have hsum_le : (∑ x : K, ((2 ^ (c - e) - 1) + (if x ∈ B then 2 ^ (c - e) else 0))) ≤
          (2 ^ c - 1) * 2 ^ (k - e) := by
        rw [← hdouble]
        exact Finset.sum_le_sum (fun x _ => hlower x)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_K_eq, smul_eq_mul,
          Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul] at hsum_le
      have hmul := Nat.mul_le_mul_left (2 ^ e) hsum_le
      have h1 : 2 ^ e * (2 ^ k * (2 ^ (c - e) - 1) + B.card * 2 ^ (c - e)) =
          2 ^ k * (2 ^ c - 2 ^ e) + 2 ^ c * B.card := by
        have hpe : 2 ^ e * 2 ^ (c - e) = 2 ^ c := by
          rw [← pow_add, Nat.add_sub_of_le hec]
        have hpe1 : 2 ^ e * (2 ^ (c - e) - 1) = 2 ^ c - 2 ^ e := by
          rw [Nat.mul_sub_left_distrib, hpe, mul_one]
        calc 2 ^ e * (2 ^ k * (2 ^ (c - e) - 1) + B.card * 2 ^ (c - e))
            = 2 ^ k * (2 ^ e * (2 ^ (c - e) - 1)) + (2 ^ e * 2 ^ (c - e)) * B.card := by ring
          _ = 2 ^ k * (2 ^ c - 2 ^ e) + 2 ^ c * B.card := by rw [hpe1, hpe]
      have h2 : 2 ^ e * ((2 ^ c - 1) * 2 ^ (k - e)) = 2 ^ k * (2 ^ c - 1) := by
        calc 2 ^ e * ((2 ^ c - 1) * 2 ^ (k - e))
            = (2 ^ e * 2 ^ (k - e)) * (2 ^ c - 1) := by ring
          _ = 2 ^ (e + (k - e)) * (2 ^ c - 1) := by rw [← pow_add]
          _ = 2 ^ k * (2 ^ c - 1) := by rw [Nat.add_sub_of_le he_le_k]
      rw [h1, h2] at hmul
      have hle_pow : 2 ^ e ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hec
      have hpos_e : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      have hsub_eq : 2 ^ k * (2 ^ c - 1) = 2 ^ k * (2 ^ c - 2 ^ e) + 2 ^ k * (2 ^ e - 1) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      rw [hsub_eq] at hmul
      exact Nat.le_of_add_le_add_left hmul

private lemma exists_good_step (hk : Module.finrank F K % 2 = 1) (L : Submodule F K) :
    ∃ L' : Submodule F K, L ≤ L' ∧
      Module.finrank F L' = min (Module.finrank F K) (Module.finrank F L + 1) ∧
      Module.finrank F (sqSub L') =
        min (Module.finrank F K) (Module.finrank F (sqSub L) + Module.finrank F L + 1) := by
  classical
  let k := Module.finrank F K
  by_cases hsq : Module.finrank F (sqSub L) < k
  · have hq := quant_bound hk L
    dsimp only at hq
    let c := k - Module.finrank F (sqSub L)
    let e := Module.finrank F L + 1
    let bad := fun x : K => Module.finrank F (sqSub (extSub L x)) < min k (Module.finrank F (sqSub L) + e)
    have hlt_pow : 2 ^ (min c e) - 1 < 2 ^ (max c e) := by
      have h1 : 2 ^ (min c e) ≤ 2 ^ (max c e) := Nat.pow_le_pow_right (by omega) (min_le_max)
      have h2 : 1 ≤ 2 ^ (min c e) := Nat.one_le_two_pow
      omega
    have hB_lt : (Finset.univ.filter bad).card < Fintype.card K := by
      have hB_eq : (@Finset.filter K bad (fun x => Classical.propDecidable (bad x)) Finset.univ).card =
          (Finset.univ.filter bad).card := by
        congr 1
        ext x
        simp
      rw [hB_eq] at hq
      have hpos : 0 < 2 ^ (max c e) := by positivity
      have hstrict : 2 ^ (max c e) * (Finset.univ.filter bad).card < 2 ^ (max c e) * 2 ^ k := by
        calc 2 ^ (max c e) * (Finset.univ.filter bad).card
            ≤ 2 ^ k * (2 ^ (min c e) - 1) := hq
          _ < 2 ^ k * 2 ^ (max c e) := Nat.mul_lt_mul_of_pos_left hlt_pow (by positivity)
          _ = 2 ^ (max c e) * 2 ^ k := mul_comm _ _
      rw [card_K_eq]
      exact Nat.lt_of_mul_lt_mul_left hstrict
    have hex : ∃ x : K, ¬ bad x := by
      by_contra hall
      push Not at hall
      have heq : Finset.univ.filter bad = Finset.univ := by
        ext x; simp [hall x]
      rw [heq, Finset.card_univ] at hB_lt
      exact lt_irrefl _ hB_lt
    rcases hex with ⟨x, hx⟩
    dsimp only [bad] at hx
    push Not at hx
    have hxL : x ∉ L := by
      intro hmem
      have hext : extSub L x = L :=
        sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem))
      rw [hext] at hx
      omega
    have hdim_ext : Module.finrank F (extSub L x) = Module.finrank F L + 1 :=
      finrank_extSub_of_not_mem L x hxL
    have hle_k : Module.finrank F L + 1 ≤ k := by
      rw [← hdim_ext]; exact Submodule.finrank_le _
    have hsq_le : Module.finrank F (sqSub (extSub L x)) ≤
        min k (Module.finrank F (sqSub L) + Module.finrank F L + 1) := by
      exact le_min (Submodule.finrank_le _) (finrank_sqSub_extSub_le L x)
    refine ⟨extSub L x, le_sup_left, ?_, ?_⟩
    · rw [hdim_ext]; omega
    · omega
  · have hsq_eq : Module.finrank F (sqSub L) = k := by
      have := Submodule.finrank_le (sqSub L); omega
    by_cases hL : Module.finrank F L < k
    · have hLne : L ≠ ⊤ := by
        intro htop
        have : Module.finrank F L = k := by rw [htop, finrank_top]
        omega
      have hex : ∃ x : K, x ∉ L := by
        by_contra hall
        push Not at hall
        apply hLne
        rw [eq_top_iff]
        intro x _
        exact hall x
      rcases hex with ⟨x, hx⟩
      have hdim_ext : Module.finrank F (extSub L x) = Module.finrank F L + 1 :=
        finrank_extSub_of_not_mem L x hx
      have hsq_ge : k ≤ Module.finrank F (sqSub (extSub L x)) := by
        rw [← hsq_eq]; exact Submodule.finrank_mono (sqSub_mono le_sup_left)
      have hsq_le : Module.finrank F (sqSub (extSub L x)) ≤ k := Submodule.finrank_le _
      refine ⟨extSub L x, le_sup_left, ?_, ?_⟩
      · rw [hdim_ext]; omega
      · omega
    · have hL_eq : Module.finrank F L = k := by
        have := Submodule.finrank_le L; omega
      refine ⟨L, le_refl L, ?_, ?_⟩
      · omega
      · omega

private lemma exists_chain (hk : Module.finrank F K % 2 = 1) (L : Submodule F K) :
    ∃ V : ℕ → Submodule F K, V 0 = L ∧ Monotone V ∧
      ∀ j : ℕ, Module.finrank F (V j) = min (Module.finrank F K) (Module.finrank F L + j) ∧
        Module.finrank F (sqSub (V j)) =
          min (Module.finrank F K)
            (Module.finrank F (sqSub L) + j * Module.finrank F L + j * (j + 1) / 2) := by
  let k := Module.finrank F K
  obtain ⟨step, hstep⟩ : ∃ step : Submodule F K → Submodule F K,
      ∀ M : Submodule F K, M ≤ step M ∧
        Module.finrank F (step M) = min k (Module.finrank F M + 1) ∧
        Module.finrank F (sqSub (step M)) =
          min k (Module.finrank F (sqSub M) + Module.finrank F M + 1) :=
    ⟨fun M => Classical.choose (exists_good_step hk M),
      fun M => Classical.choose_spec (exists_good_step hk M)⟩
  obtain ⟨V, hV0, hVsucc⟩ : ∃ V : ℕ → Submodule F K, V 0 = L ∧ ∀ j, V (j + 1) = step (V j) :=
    ⟨Nat.rec L (fun _ cur => step cur), rfl, fun _ => rfl⟩
  have hVmono : Monotone V :=
    monotone_nat_of_le_succ (fun j => by rw [hVsucc]; exact (hstep (V j)).1)
  refine ⟨V, hV0, hVmono, ?_⟩
  intro j
  induction j with
  | zero =>
    have hLle : Module.finrank F L ≤ k := Submodule.finrank_le L
    have hSqle : Module.finrank F (sqSub L) ≤ k := Submodule.finrank_le (sqSub L)
    rw [hV0]
    simp only [Nat.add_zero, Nat.zero_mul, Nat.zero_div]
    constructor <;> omega
  | succ j ih =>
    rcases ih with ⟨ih1, ih2⟩
    have hs := hstep (V j)
    rw [hVsucc]
    have htri : (j + 1) * (j + 1 + 1) / 2 = j * (j + 1) / 2 + j + 1 := by
      have h : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
      rw [h, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
      omega
    have hlin : (j + 1) * Module.finrank F L = j * Module.finrank F L + Module.finrank F L := by
      ring
    constructor
    · rw [hs.2.1, ih1]
      omega
    · rw [hs.2.2]
      by_cases hfull : k ≤ Module.finrank F (sqSub L) + j * Module.finrank F L + j * (j + 1) / 2
      · rw [ih2]
        omega
      · have hlt : Module.finrank F (sqSub (V j)) < k := by
          rw [ih2]
          omega
        have hVlt : Module.finrank F (V j) < k := by
          by_contra hge
          have htop : V j = ⊤ := Submodule.eq_top_of_finrank_eq (by
            have := Submodule.finrank_le (V j); omega)
          have hsqtop : sqSub (V j) = ⊤ := by rw [htop]; exact sqSub_top
          have hsqk : Module.finrank F (sqSub (V j)) = k := by rw [hsqtop, finrank_top]
          omega
        rw [ih1, ih2]
        rw [ih1] at hVlt
        omega

end FieldProps

end PEqualNP.Outside.L_lib_803_aux

open PEqualNP.Outside.L_lib_803_aux in
theorem PEqualNP.Outside.L_lib_803 : (let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
  let k := Module.finrank F K
  let dim := fun (L : Submodule F K) => Module.finrank F L
  let sq := fun (L : Submodule F K) =>
    Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (L : Submodule F K) (x : K) => L ⊔ Submodule.span F {x}
  k % 2 = 1 → ∀ L : Submodule F K,
    let c := k - dim (sq L)
    let e := dim L + 1
    let bad := fun x : K => dim (sq (extend L x)) < min k (dim (sq L) + e)
    2^(max c e) * (@Finset.filter K bad (fun x => Classical.propDecidable (bad x))
      Finset.univ).card ≤ 2^k * (2^(min c e) - 1) ∧
    ∃ V : ℕ → Submodule F K, V 0 = L ∧ Monotone V ∧
      ∀ j : ℕ, dim (V j) = min k (dim L+j) ∧
        dim (sq (V j)) = min k (dim (sq L) + j*dim L + j*(j+1)/2)) := by
  intro F K _ _ _ _ k dim sq extend hk L
  exact ⟨quant_bound hk L, exists_chain hk L⟩

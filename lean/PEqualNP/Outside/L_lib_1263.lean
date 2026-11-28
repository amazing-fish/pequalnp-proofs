import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1263_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

lemma mem_of_mem_set {α : Type*} {l : List α} {i : ℕ} {a x : α} (h : x ∈ l.set i a) :
    x ∈ l ∨ x = a := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  by_cases hki : k = i
  · right; subst hki; simp [List.getElem_set_self]
  · left; rw [List.getElem_set_ne (Ne.symm hki)]; exact List.getElem_mem (by simpa using hk)

lemma wires_step (gs : List Gate) (x : List Bool) :
    (Circuit.mk gs 0).wires x =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := rfl

lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_length C.gates x

lemma wires_append (gs1 gs2 : List Gate) (x : List Bool) (o : ℕ) :
    (Circuit.mk (gs1 ++ gs2) o).wires x =
      (Circuit.mk gs2 o).wires ((Circuit.mk gs1 0).wires x) := by
  simp only [Circuit.wires, List.foldl_append]

lemma foldl_wires_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD, List.getElem?_append_left hi]

lemma wires_prefix (gs1 gs2 : List Gate) (x : List Bool) (o : ℕ)
    (i : ℕ) (hi : i < x.length + gs1.length) :
    ((Circuit.mk (gs1 ++ gs2) o).wires x).getD i false =
      ((Circuit.mk gs1 0).wires x).getD i false := by
  rw [wires_append]
  apply foldl_wires_prefix
  rw [wires_length]
  exact hi

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) (o : ℕ) :
    (Circuit.mk (gs ++ [g]) o).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  rw [wires_append]
  simp only [Circuit.wires, List.foldl_cons, List.foldl_nil]

lemma wires_snoc_last (n0 : ℕ) (gs : List Gate) (g : Gate) (y : List Bool) (hy : y.length = n0) :
    ((Circuit.mk (gs ++ [g]) 0).wires y).getD (n0 + gs.length) false =
      g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires y).getD i false) := by
  rw [wires_snoc]
  have hl : ((Circuit.mk gs 0).wires y).length = n0 + gs.length := by rw [wires_length, hy]
  simp only [List.getD, List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

lemma wires_get_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_wires_prefix C.gates x i hi

lemma wires_get_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((Circuit.mk (C.gates.take j) 0).wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hC : C.wires x = (Circuit.mk (C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1)) 0).wires x := by
    simp only [Circuit.wires, ← hsplit]
  rw [hC, wires_prefix (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j + 1)) x 0 (x.length + j)
    (by simp [hlen_take]; omega)]
  have hlen_eq : x.length + j = x.length + (C.gates.take j).length := by rw [hlen_take]
  rw [hlen_eq]
  exact wires_snoc_last x.length (C.gates.take j) C.gates[j] x rfl

lemma wires_get_gate_rb (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_get_gate C x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < x.length + j := by
    have h1 := hrb j hj i
    simp only [gateAt, List.getD, List.getElem?_eq_getElem hj, Option.getD_some] at h1
    exact h1 hi
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hC : C.wires x = (Circuit.mk (C.gates.take j ++ C.gates.drop j) 0).wires x := by
    simp only [Circuit.wires, ← hsplit]
  rw [hC, wires_prefix (C.gates.take j) (C.gates.drop j) x 0 i (by omega)]

lemma wires_get_gate_rb_eq (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (j : ℕ) (hj : j < C.gates.length) (hrb : ReadsBack n C) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  subst hx
  exact wires_get_gate_rb C x j hj hrb

lemma notCount_eq_gates (gs : List Gate) (o1 o2 : ℕ) :
    notCount ⟨gs, o1⟩ = notCount ⟨gs, o2⟩ := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp only [notCount, List.filter_append, List.length_append]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_singleton_and (ins : List ℕ) (o : ℕ) : notCount ⟨[⟨GateOp.and, ins⟩], o⟩ = 0 := rfl
lemma notCount_singleton_or (ins : List ℕ) (o : ℕ) : notCount ⟨[⟨GateOp.or, ins⟩], o⟩ = 0 := rfl
lemma notCount_singleton_not (ins : List ℕ) (o : ℕ) : notCount ⟨[⟨GateOp.not, ins⟩], o⟩ = 1 := rfl

lemma readsBack_append (n : ℕ) (gs1 gs2 : List Gate) (o : ℕ)
    (h1 : ReadsBack n ⟨gs1, 0⟩) (h2 : ReadsBack (n + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack n ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  simp only [gateAt, List.getD] at hi
  by_cases hlt : j < gs1.length
  · rw [List.getElem?_append_left hlt] at hi
    exact h1 j hlt i (by simpa [gateAt, List.getD] using hi)
  · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hi
    have hj2 : j - gs1.length < gs2.length := by simp at hj; omega
    have hres := h2 (j - gs1.length) hj2 i (by simpa [gateAt, List.getD] using hi)
    omega

lemma readsBack_snoc (n : ℕ) (gs : List Gate) (g : Gate) (o : ℕ)
    (h1 : ReadsBack n ⟨gs, 0⟩) (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n ⟨gs ++ [g], o⟩ := by
  apply readsBack_append n gs [g] o h1
  intro j hj i hi
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some] at hi
  have := hg i hi; omega

lemma fanInTwo_append (gs1 gs2 : List Gate) (o : ℕ)
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h1 g h
  · exact h2 g h

lemma monotone2_append (gs1 gs2 : List Gate) (o : ℕ)
    (h1 : Monotone2 ⟨gs1, 0⟩) (h2 : Monotone2 ⟨gs2, 0⟩) :
    Monotone2 ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h1 g h
  · exact h2 g h

lemma monotone2_imp_fanInTwo (C : Circuit) (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  have ⟨hop, hlen⟩ := h g hg
  refine ⟨?_, hlen⟩
  rcases hop with h1 | h2
  · left; exact h1
  · right; left; exact h2

lemma notCount_of_monotone2 (C : Circuit) (h : Monotone2 C) : notCount C = 0 := by
  unfold notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  have ⟨hop, _⟩ := h g hg
  rcases hop with h1 | h1
  · simp [h1]
  · simp only [Set.mem_singleton_iff] at h1; simp [h1]

def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + bitsToNat bs

lemma bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    simp only [bitsToNat, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

lemma bitsToNat_head_ge (b : Bool) (bs : List Bool) :
    2 ^ bs.length ≤ bitsToNat (b :: bs) ↔ b = true := by
  have hlt := bitsToNat_lt bs
  cases b <;> simp [bitsToNat] <;> omega

lemma bitsToNat_lt_of_first_diff : ∀ (bs1 bs2 : List Bool),
    bs1.length = bs2.length →
    (∃ i, i < bs1.length ∧ (∀ k < i, bs1[k]! = bs2[k]!) ∧ bs1[i]! = true ∧ bs2[i]! = false) →
    bitsToNat bs2 < bitsToNat bs1
  | [], [], _, ⟨i, hi, _⟩ => by simp at hi
  | a :: as, b :: bs, hlen, ⟨i, hi, hpre, h1, h2⟩ => by
    have hlen' : as.length = bs.length := by simpa using hlen
    cases i with
    | zero =>
      simp only [List.getElem!_cons_zero] at h1 h2
      subst h1; subst h2
      simp only [bitsToNat, ↓reduceIte, Bool.false_eq_true, zero_add, hlen']
      have hlt := bitsToNat_lt bs
      omega
    | succ i' =>
      have hab : a = b := by
        have := hpre 0 (Nat.zero_lt_succ i')
        simpa using this
      subst hab
      have hlt_tail : bitsToNat bs < bitsToNat as := by
        apply bitsToNat_lt_of_first_diff as bs hlen'
        refine ⟨i', by simp at hi; omega, ?_, ?_, ?_⟩
        · intro k hk
          have := hpre (k + 1) (Nat.succ_lt_succ hk)
          simpa using this
        · simpa using h1
        · simpa using h2
      simp only [bitsToNat, hlen']
      omega

def notIndices (gs : List Gate) : List ℕ :=
  (List.range gs.length).filter (fun j => decide ((gateAt ⟨gs, 0⟩ j).op = GateOp.not))

lemma notIndices_length (C : Circuit) : (notIndices C.gates).length = notCount C := by
  unfold notIndices notCount
  have haux : ∀ (gs : List Gate),
      ((List.range gs.length).filter (fun j => decide ((gateAt ⟨gs, 0⟩ j).op = GateOp.not))).length =
      (gs.filter (fun g => decide (g.op = GateOp.not))).length := by
    intro gs
    have hmap : gs = (List.range gs.length).map (fun j => gateAt ⟨gs, 0⟩ j) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_range, gateAt, List.getD,
          List.getElem?_eq_getElem hi1, Option.getD_some]
    conv_rhs => rw [hmap]
    rw [List.filter_map, List.length_map]
    rfl
  exact haux C.gates

lemma notIndices_mem (gs : List Gate) (j : ℕ) :
    j ∈ notIndices gs ↔ j < gs.length ∧ (gateAt ⟨gs, 0⟩ j).op = GateOp.not := by
  simp [notIndices]

lemma notIndices_pairwise_lt (gs : List Gate) : (notIndices gs).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma notIndices_get_lt (gs : List Gate) {a b : ℕ} (ha : a < (notIndices gs).length)
    (hb : b < (notIndices gs).length) (hab : a < b) :
    (notIndices gs)[a] < (notIndices gs)[b] :=
  List.pairwise_iff_getElem.mp (notIndices_pairwise_lt gs) a b ha hb hab

lemma gateOp_and_mono {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i < l1.length, l1[i]! ≤ l2[i]!) :
    GateOp.and.eval l1 ≤ GateOp.and.eval l2 := by
  simp only [GateOp.eval]
  cases h1 : l1.all id
  · exact Bool.false_le _
  · simp only [Bool.le_iff_imp, true_implies]
    rw [List.all_eq_true] at h1 ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi1 : i < l1.length := by omega
    have hle_i := hle i hi1
    have h1i : l1[i]! = true := by
      have : l1[i] = true := h1 l1[i] (List.getElem_mem hi1)
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1] using this
    have h2i : l2[i]! = l2[i] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [h1i, h2i] at hle_i
    cases h : l2[i]
    · rw [h] at hle_i; exact absurd hle_i (by decide)
    · rfl

lemma gateOp_or_mono {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i < l1.length, l1[i]! ≤ l2[i]!) :
    GateOp.or.eval l1 ≤ GateOp.or.eval l2 := by
  simp only [GateOp.eval]
  cases h1 : l1.any id
  · exact Bool.false_le _
  · simp only [Bool.le_iff_imp, true_implies]
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    obtain ⟨i, hi1, heq⟩ := List.mem_iff_getElem.mp hb
    have hi2 : i < l2.length := by omega
    refine ⟨l2[i], List.getElem_mem hi2, ?_⟩
    have hle_i := hle i hi1
    have h1i : l1[i]! = true := by
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1] using heq
    have h2i : l2[i]! = l2[i] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    rw [h1i, h2i] at hle_i
    cases h : l2[i]
    · rw [h] at hle_i; exact absurd hle_i (by decide)
    · rfl

def notOutputs (n : ℕ) (C : Circuit) (y : List Bool) : List Bool :=
  (notIndices C.gates).map (fun j => (C.wires y).getD (n + j) false)

def notRank (n : ℕ) (C : Circuit) (y : List Bool) : ℕ :=
  bitsToNat (notOutputs n C y)

lemma notRank_lt (n : ℕ) (C : Circuit) (y : List Bool) :
    notRank n C y < 2 ^ notCount C := by
  unfold notRank notOutputs
  have hlen : ((notIndices C.gates).map (fun j => (C.wires y).getD (n + j) false)).length = notCount C := by
    rw [List.length_map, notIndices_length]
  rw [← hlen]
  exact bitsToNat_lt _

lemma wires_mono_up_to (n : ℕ) (C : Circuit) (y1 y2 : List Bool) (k : ℕ)
    (hfit : FanInTwo C) (hrb : ReadsBack n C)
    (hy1 : y1.length = n) (hy2 : y2.length = n)
    (hin : ∀ i < n, y1.getD i false ≤ y2.getD i false)
    (hnot : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.not →
      (C.wires y1).getD (n + j) false = (C.wires y2).getD (n + j) false) :
    ∀ w < n + k, w < n + C.gates.length → (C.wires y1).getD w false ≤ (C.wires y2).getD w false := by
  intro w hw hwb
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [wires_get_input C y1 w (by omega), wires_get_input C y2 w (by omega)]
      exact hin w hwn
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have hjk : j < k := by omega
      have hw_eq : w = n + j := by omega
      rw [hw_eq]
      have hgat : gateAt C j = C.gates[j] := by
        simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
      have ⟨hop, _⟩ := hfit C.gates[j] (List.getElem_mem hj)
      rcases hop with hand | hor | hnotop
      · rw [wires_get_gate_rb_eq n C y1 hy1 j hj hrb, wires_get_gate_rb_eq n C y2 hy2 j hj hrb, hand]
        apply gateOp_and_mono (by simp)
        intro idx hidx
        simp only [List.length_map] at hidx
        have h1 : ((C.gates[j]).inputs.map (fun i => (C.wires y1).getD i false))[idx]! =
            (C.wires y1).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        have h2 : ((C.gates[j]).inputs.map (fun i => (C.wires y2).getD i false))[idx]! =
            (C.wires y2).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        rw [h1, h2]
        have hlt_rb : (C.gates[j]).inputs[idx] < n + j := by
          have := hrb j hj (C.gates[j]).inputs[idx] (by rw [hgat]; exact List.getElem_mem hidx)
          exact this
        exact ih _ (by omega) (by omega) (by omega)
      · rw [wires_get_gate_rb_eq n C y1 hy1 j hj hrb, wires_get_gate_rb_eq n C y2 hy2 j hj hrb, hor]
        apply gateOp_or_mono (by simp)
        intro idx hidx
        simp only [List.length_map] at hidx
        have h1 : ((C.gates[j]).inputs.map (fun i => (C.wires y1).getD i false))[idx]! =
            (C.wires y1).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        have h2 : ((C.gates[j]).inputs.map (fun i => (C.wires y2).getD i false))[idx]! =
            (C.wires y2).getD (C.gates[j]).inputs[idx] false := by
          simp [List.getElem!_eq_getElem?_getD, hidx]
        rw [h1, h2]
        have hlt_rb : (C.gates[j]).inputs[idx] < n + j := by
          have := hrb j hj (C.gates[j]).inputs[idx] (by rw [hgat]; exact List.getElem_mem hidx)
          exact this
        exact ih _ (by omega) (by omega) (by omega)
      · have heq := hnot j hjk hj (by rw [hgat]; exact hnotop)
        rw [heq]

lemma markov_step_wire (n : ℕ) (C : Circuit) (y1 y2 : List Bool) (w : ℕ)
    (hfit : FanInTwo C) (hrb : ReadsBack n C) (hw : w < n + C.size)
    (hy1 : y1.length = n) (hy2 : y2.length = n)
    (hin : ∀ i < n, y1.getD i false ≤ y2.getD i false) :
    notRank n C y2 ≤ notRank n C y1 ∧
    (notRank n C y2 = notRank n C y1 → (C.wires y1).getD w false ≤ (C.wires y2).getD w false) := by
  let bs1 := notOutputs n C y1
  let bs2 := notOutputs n C y2
  have hlen : bs1.length = bs2.length := by simp [bs1, bs2, notOutputs]
  by_cases heq : bs1 = bs2
  · have hrk : notRank n C y2 = notRank n C y1 := congrArg bitsToNat heq.symm
    refine ⟨le_of_eq hrk, fun _ => ?_⟩
    have hnot : ∀ j < C.gates.length, j < C.gates.length → (gateAt C j).op = GateOp.not →
        (C.wires y1).getD (n + j) false = (C.wires y2).getD (n + j) false := by
      intro j hj _ hop
      have hmem : j ∈ notIndices C.gates := (notIndices_mem C.gates j).mpr ⟨hj, hop⟩
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
      have h1 : bs1[idx]'(by simp [bs1, notOutputs, hidx]) = (C.wires y1).getD (n + j) false := by
        simp [bs1, notOutputs, hget]
      have h2 : bs2[idx]'(by simp [bs2, notOutputs, hidx]) = (C.wires y2).getD (n + j) false := by
        simp [bs2, notOutputs, hget]
      rw [← h1, ← h2]
      simp [heq]
    exact wires_mono_up_to n C y1 y2 C.gates.length hfit hrb hy1 hy2 hin hnot w hw hw
  · have hex_diff : ∃ idx, idx < bs1.length ∧ bs1[idx]! ≠ bs2[idx]! := by
      by_contra hall
      push_neg at hall
      apply heq
      apply List.ext_getElem hlen
      intro idx h1 h2
      have := hall idx h1
      simpa [List.getElem!_eq_getElem?_getD, h1, h2] using this
    let idx := Nat.find hex_diff
    have hidx_spec : idx < bs1.length ∧ bs1[idx]! ≠ bs2[idx]! := Nat.find_spec hex_diff
    have hidx_lt : idx < (notIndices C.gates).length := by
      have h1 : idx < bs1.length := hidx_spec.1
      simpa only [bs1, notOutputs, List.length_map] using h1
    let j0 := (notIndices C.gates)[idx]
    have hj0_mem : j0 ∈ notIndices C.gates := List.getElem_mem hidx_lt
    have ⟨hj0_lt, hj0_op⟩ := (notIndices_mem C.gates j0).mp hj0_mem
    have hpre_eq : ∀ k < idx, bs1[k]! = bs2[k]! := by
      intro k hk
      by_contra hne
      have hk_lt : k < bs1.length := lt_trans hk hidx_spec.1
      exact Nat.find_min hex_diff hk ⟨hk_lt, hne⟩
    have hnot_pre : ∀ j < j0, j < C.gates.length → (gateAt C j).op = GateOp.not →
        (C.wires y1).getD (n + j) false = (C.wires y2).getD (n + j) false := by
      intro j hjj0 hjlt hop
      have hmem : j ∈ notIndices C.gates := (notIndices_mem C.gates j).mpr ⟨hjlt, hop⟩
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
      have hk_lt_idx : k < idx := by
        by_contra hge
        have hle : idx ≤ k := Nat.le_of_not_lt hge
        rcases lt_or_eq_of_le hle with hlt | rfl
        · have := notIndices_get_lt C.gates hidx_lt hk hlt
          omega
        · omega
      have h1 := hpre_eq k hk_lt_idx
      simp only [bs1, bs2, notOutputs, List.getElem!_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, hget] at h1
      exact h1
    have hmono_pre := wires_mono_up_to n C y1 y2 j0 hfit hrb hy1 hy2 hin hnot_pre
    have hgat : gateAt C j0 = C.gates[j0] := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hj0_lt]
    have hj0_not : (C.gates[j0]).op = GateOp.not := by rw [← hgat]; exact hj0_op
    have hj0_ge : (C.wires y2).getD (n + j0) false ≤ (C.wires y1).getD (n + j0) false := by
      rw [wires_get_gate_rb_eq n C y1 hy1 j0 hj0_lt hrb, wires_get_gate_rb_eq n C y2 hy2 j0 hj0_lt hrb, hj0_not]
      simp only [GateOp.eval]
      cases hins : (C.gates[j0]).inputs with
      | nil => simp
      | cons u us =>
        simp only [List.map_cons, List.headD_cons]
        have hu_lt : u < n + j0 := by
          have := hrb j0 hj0_lt u (by rw [hgat, hins]; simp)
          exact this
        have hle_u := hmono_pre u hu_lt (by omega)
        cases h1 : (C.wires y1).getD u false <;> cases h2 : (C.wires y2).getD u false
        · simp
        · simp
        · rw [h1, h2] at hle_u; exact absurd hle_u (by decide)
        · simp
    have h1_eq : bs1[idx]! = (C.wires y1).getD (n + j0) false := by
      simp [bs1, notOutputs, List.getElem!_eq_getElem?_getD, hidx_lt, j0]
    have h2_eq : bs2[idx]! = (C.wires y2).getD (n + j0) false := by
      simp [bs2, notOutputs, List.getElem!_eq_getElem?_getD, hidx_lt, j0]
    have htf : bs1[idx]! = true ∧ bs2[idx]! = false := by
      have hne := hidx_spec.2
      rw [h1_eq, h2_eq] at hne ⊢
      cases hv1 : (C.wires y1).getD (n + j0) false <;>
        cases hv2 : (C.wires y2).getD (n + j0) false
      · exact (hne (by rw [hv1, hv2])).elim
      · rw [hv1, hv2] at hj0_ge; exact absurd hj0_ge (by decide)
      · exact ⟨rfl, rfl⟩
      · exact (hne (by rw [hv1, hv2])).elim
    have hlt_rk : notRank n C y2 < notRank n C y1 :=
      bitsToNat_lt_of_first_diff bs1 bs2 hlen ⟨idx, hidx_spec.1, hpre_eq, htf.1, htf.2⟩
    exact ⟨Nat.le_of_lt hlt_rk, fun h => by omega⟩

def compileOrChain (n0 cFalse : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, cFalse)
  | [w] => (gs, w)
  | w :: ws =>
    let res1 := compileOrChain n0 cFalse gs ws
    let gs1 := res1.1
    let wRest := res1.2
    let wOut := n0 + gs1.length
    (gs1 ++ [⟨GateOp.or, [w, wRest]⟩], wOut)

lemma compileOrChain_spec (n0 cFalse : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate),
    cFalse < n0 + gs.length →
    (∀ w ∈ ws, w < n0 + gs.length) →
    let res := compileOrChain n0 cFalse gs ws
    (∃ ex, res.1 = gs ++ ex ∧ ex.length ≤ ws.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2 < n0 + res.1.length ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ((Circuit.mk res.1 0).wires y).getD res.2 false =
        ws.any (fun w => ((Circuit.mk gs 0).wires y).getD w false)) := by
  induction ws with
  | nil =>
    intro gs hcf _
    refine ⟨⟨[], by simp [compileOrChain], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      hcf, fun y _ hcfv => by simpa [compileOrChain] using hcfv⟩
  | cons w ws ih =>
    intro gs hcf hws
    cases ws with
    | nil =>
      refine ⟨⟨[], by simp [compileOrChain], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
        hws w (List.mem_cons_self ..), fun y _ _ => by simp [compileOrChain]⟩
    | cons w2 ws' =>
      have hw : w < n0 + gs.length := hws w (List.mem_cons_self ..)
      have hws' : ∀ u ∈ w2 :: ws', u < n0 + gs.length := fun u hu => hws u (List.mem_cons_of_mem w hu)
      have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hout1, hsem1⟩ := ih gs hcf hws'
      let res1 := compileOrChain n0 cFalse gs (w2 :: ws')
      have hw_lt1 : w < n0 + res1.1.length := by rw [hgs1]; simp; omega
      let gOr : Gate := ⟨GateOp.or, [w, res1.2]⟩
      have hgOr_mon : Monotone2 ⟨[gOr], 0⟩ := by
        intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gOr]
      have hgOr_rb : ReadsBack (n0 + res1.1.length) ⟨[gOr], 0⟩ := by
        intro j hj u hu
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some, gOr,
          List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      simp only [compileOrChain]
      refine ⟨⟨ex1 ++ [gOr], by rw [hgs1, List.append_assoc], by simp; omega,
        monotone2_append ex1 [gOr] 0 hmon1 hgOr_mon,
        readsBack_append (n0 + gs.length) ex1 [gOr] 0 hrb1 (by
          have : n0 + gs.length + ex1.length = n0 + res1.1.length := by rw [hgs1, List.length_append]; omega
          rw [this]; exact hgOr_rb)⟩,
        by simp, ?_⟩
      intro y hy hcfv
      change ((Circuit.mk (res1.1 ++ [gOr]) 0).wires y).getD (n0 + res1.1.length) false = _
      rw [wires_snoc_last n0 res1.1 gOr y hy]
      simp only [gOr, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [hgs1, wires_prefix gs ex1 y 0 w (by omega), ← hgs1, hsem1 y hy hcfv]
      simp only [List.any_cons]

lemma list_any_congr_mem {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

lemma list_all_congr_mem {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

lemma wires_prefix_n0 (n0 : ℕ) (gs1 gs2 : List Gate) (y : List Bool) (hy : y.length = n0)
    (i : ℕ) (hi : i < n0 + gs1.length) :
    ((Circuit.mk (gs1 ++ gs2) 0).wires y).getD i false =
      ((Circuit.mk gs1 0).wires y).getD i false :=
  wires_prefix gs1 gs2 y 0 i (by omega)

lemma wires_input_n0 (n0 : ℕ) (gs : List Gate) (y : List Bool) (hy : y.length = n0)
    (i : ℕ) (hi : i < n0) :
    ((Circuit.mk gs 0).wires y).getD i false =
      ((Circuit.mk [] 0).wires y).getD i false := by
  have h := wires_prefix [] gs y 0 i (by simp [hy]; omega)
  simpa using h

def compileAndChain (n0 cTrue : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, cTrue)
  | [w] => (gs, w)
  | w :: ws =>
    let res1 := compileAndChain n0 cTrue gs ws
    let gs1 := res1.1
    let wRest := res1.2
    let wOut := n0 + gs1.length
    (gs1 ++ [⟨GateOp.and, [w, wRest]⟩], wOut)

lemma compileAndChain_spec (n0 cTrue : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate),
    cTrue < n0 + gs.length →
    (∀ w ∈ ws, w < n0 + gs.length) →
    let res := compileAndChain n0 cTrue gs ws
    (∃ ex, res.1 = gs ++ ex ∧ ex.length ≤ ws.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2 < n0 + res.1.length ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cTrue false = true →
      ((Circuit.mk res.1 0).wires y).getD res.2 false =
        ws.all (fun w => ((Circuit.mk gs 0).wires y).getD w false)) := by
  induction ws with
  | nil =>
    intro gs hct _
    refine ⟨⟨[], by simp [compileAndChain], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      hct, fun y _ hctv => by simpa [compileAndChain] using hctv⟩
  | cons w ws ih =>
    intro gs hct hws
    cases ws with
    | nil =>
      refine ⟨⟨[], by simp [compileAndChain], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
        hws w (List.mem_cons_self ..), fun y _ _ => by simp [compileAndChain]⟩
    | cons w2 ws' =>
      have hw : w < n0 + gs.length := hws w (List.mem_cons_self ..)
      have hws' : ∀ u ∈ w2 :: ws', u < n0 + gs.length := fun u hu => hws u (List.mem_cons_of_mem w hu)
      have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hout1, hsem1⟩ := ih gs hct hws'
      let res1 := compileAndChain n0 cTrue gs (w2 :: ws')
      have hw_lt1 : w < n0 + res1.1.length := by rw [hgs1]; simp; omega
      let gAnd : Gate := ⟨GateOp.and, [w, res1.2]⟩
      have hgAnd_mon : Monotone2 ⟨[gAnd], 0⟩ := by
        intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gAnd]
      have hgAnd_rb : ReadsBack (n0 + res1.1.length) ⟨[gAnd], 0⟩ := by
        intro j hj u hu
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some, gAnd,
          List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      simp only [compileAndChain]
      refine ⟨⟨ex1 ++ [gAnd], by rw [hgs1, List.append_assoc], by simp; omega,
        monotone2_append ex1 [gAnd] 0 hmon1 hgAnd_mon,
        readsBack_append (n0 + gs.length) ex1 [gAnd] 0 hrb1 (by
          have : n0 + gs.length + ex1.length = n0 + res1.1.length := by rw [hgs1, List.length_append]; omega
          rw [this]; exact hgAnd_rb)⟩,
        by simp, ?_⟩
      intro y hy hctv
      change ((Circuit.mk (res1.1 ++ [gAnd]) 0).wires y).getD (n0 + res1.1.length) false = _
      rw [wires_snoc_last n0 res1.1 gAnd y hy]
      simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [hgs1, wires_prefix_n0 n0 gs ex1 y hy w hw, ← hgs1, hsem1 y hy hctv]
      simp only [List.all_cons]

def compilePrefOr (n0 : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | w :: ws =>
    let wNext := n0 + gs.length
    let gs1 := gs ++ [⟨GateOp.or, [acc, w]⟩]
    let res := compilePrefOr n0 gs1 wNext ws
    (res.1, acc :: res.2)

lemma compilePrefOr_spec (n0 : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate) (acc : ℕ),
    acc < n0 + gs.length →
    (∀ w ∈ ws, w < n0 + gs.length) →
    let res := compilePrefOr n0 gs acc ws
    (∃ ex, res.1 = gs ++ ex ∧ ex.length = ws.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.length = ws.length ∧
    (∀ u ∈ res.2, u < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 → ∀ i, i < ws.length →
      ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
        (((Circuit.mk gs 0).wires y).getD acc false ||
          (ws.take i).any (fun w => ((Circuit.mk gs 0).wires y).getD w false))) := by
  induction ws with
  | nil =>
    intro gs acc _ _
    refine ⟨⟨[], by simp [compilePrefOr], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      by simp [compilePrefOr], fun u hu => by simp [compilePrefOr] at hu,
      fun _ _ i hi => by simp at hi⟩
  | cons w ws ih =>
    intro gs acc hacc hws
    have hw : w < n0 + gs.length := hws w (List.mem_cons_self ..)
    let wNext := n0 + gs.length
    let gOr : Gate := ⟨GateOp.or, [acc, w]⟩
    let gs1 := gs ++ [gOr]
    have hgOr_mon : Monotone2 ⟨[gOr], 0⟩ := by
      intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gOr]
    have hgOr_rb : ReadsBack (n0 + gs.length) ⟨[gOr], 0⟩ := by
      intro j hj u hu
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0; simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some, gOr,
        List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    have hwNext_lt : wNext < n0 + gs1.length := by simp [wNext, gs1]
    have hws' : ∀ u ∈ ws, u < n0 + gs1.length := fun u hu => by
      have := hws u (List.mem_cons_of_mem w hu); simp [gs1]; omega
    have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hreslen, hreslt, hsem⟩ := ih gs1 wNext hwNext_lt hws'
    dsimp only
    change (∃ ex, (compilePrefOr n0 gs1 wNext ws).1 = gs ++ ex ∧ ex.length = (w :: ws).length ∧
        Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
      (acc :: (compilePrefOr n0 gs1 wNext ws).2).length = (w :: ws).length ∧
      (∀ u ∈ acc :: (compilePrefOr n0 gs1 wNext ws).2, u < n0 + (compilePrefOr n0 gs1 wNext ws).1.length) ∧
      (∀ y : List Bool, y.length = n0 → ∀ i, i < (w :: ws).length →
        ((Circuit.mk (compilePrefOr n0 gs1 wNext ws).1 0).wires y).getD
            ((acc :: (compilePrefOr n0 gs1 wNext ws).2).getD i 0) false =
          (((Circuit.mk gs 0).wires y).getD acc false ||
            ((w :: ws).take i).any (fun u => ((Circuit.mk gs 0).wires y).getD u false)))
    refine ⟨⟨[gOr] ++ ex2, by rw [hgs2]; simp [gs1, List.append_assoc], by simp [hlen2],
      monotone2_append [gOr] ex2 0 hgOr_mon hmon2,
      readsBack_append (n0 + gs.length) [gOr] ex2 0 hgOr_rb (by
        have : n0 + gs.length + [gOr].length = n0 + gs1.length := by simp [gs1]; omega
        rw [this]; exact hrb2)⟩,
      by simp [hreslen], ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · rw [hgs2]; simp [gs1]; omega
      · exact hreslt u hu
    · intro y hy i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.take_zero, List.any_nil, Bool.or_false]
        have heq : (compilePrefOr n0 gs1 wNext ws).1 = gs ++ ([gOr] ++ ex2) := by
          rw [hgs2]; simp [gs1, List.append_assoc]
        rw [heq, wires_prefix_n0 n0 gs ([gOr] ++ ex2) y hy acc hacc]
      | succ i' =>
        simp only [List.getD_cons_succ]
        have hi' : i' < ws.length := by simp at hi; omega
        rw [hsem y hy i' hi']
        have hwNext_val : ((Circuit.mk gs1 0).wires y).getD wNext false =
            (((Circuit.mk gs 0).wires y).getD acc false || ((Circuit.mk gs 0).wires y).getD w false) := by
          change ((Circuit.mk (gs ++ [gOr]) 0).wires y).getD (n0 + gs.length) false = _
          rw [wires_snoc_last n0 gs gOr y hy]
          simp [gOr, GateOp.eval]
        rw [hwNext_val]
        have htake : (ws.take i').any (fun u => ((Circuit.mk gs1 0).wires y).getD u false) =
            (ws.take i').any (fun u => ((Circuit.mk gs 0).wires y).getD u false) := by
          apply list_any_congr_mem
          intro u hu
          have hu_ws : u ∈ ws := List.mem_of_mem_take hu
          have hu_lt : u < n0 + gs.length := hws u (List.mem_cons_of_mem w hu_ws)
          exact wires_prefix_n0 n0 gs [gOr] y hy u hu_lt
        rw [htake]
        simp only [List.take_succ_cons, List.any_cons, Bool.or_assoc]

def compileZipBin (op : GateOp) (n0 : ℕ) (gs : List Gate) : List ℕ → List ℕ → List Gate × List ℕ
  | a :: as, b :: bs =>
    let wOut := n0 + gs.length
    let gs1 := gs ++ [⟨op, [a, b]⟩]
    let res := compileZipBin op n0 gs1 as bs
    (res.1, wOut :: res.2)
  | _, _ => (gs, [])

lemma compileZipBin_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (n0 : ℕ) (as bs : List ℕ) (heqLen : as.length = bs.length) :
    ∀ (gs : List Gate),
    (∀ a ∈ as, a < n0 + gs.length) →
    (∀ b ∈ bs, b < n0 + gs.length) →
    let res := compileZipBin op n0 gs as bs
    (∃ ex, res.1 = gs ++ ex ∧ ex.length = as.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.length = as.length ∧
    (∀ u ∈ res.2, u < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 → ∀ i, i < as.length →
      ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
        op.eval [((Circuit.mk gs 0).wires y).getD (as.getD i 0) false,
                 ((Circuit.mk gs 0).wires y).getD (bs.getD i 0) false]) := by
  induction as generalizing bs with
  | nil =>
    intro gs _ _
    cases bs with
    | nil =>
      refine ⟨⟨[], by simp [compileZipBin], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
        by simp [compileZipBin], fun u hu => by simp [compileZipBin] at hu,
        fun _ _ i hi => by simp at hi⟩
    | cons _ _ => simp at heqLen
  | cons a as ih =>
    cases bs with
    | nil => simp at heqLen
    | cons b bs =>
      intro gs has hbs
      have ha : a < n0 + gs.length := has a (List.mem_cons_self ..)
      have hb : b < n0 + gs.length := hbs b (List.mem_cons_self ..)
      let gBin : Gate := ⟨op, [a, b]⟩
      let wOut := n0 + gs.length
      let gs1 := gs ++ [gBin]
      have hgBin_mon : Monotone2 ⟨[gBin], 0⟩ := by
        intro x hx; simp only [List.mem_singleton] at hx; subst hx
        simp only [gBin]; exact ⟨hop, by simp⟩
      have hgBin_rb : ReadsBack (n0 + gs.length) ⟨[gBin], 0⟩ := by
        intro j hj u hu
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; simp only [gateAt, List.getD, List.getElem?_cons_zero, Option.getD_some, gBin,
          List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      have heqLen' : as.length = bs.length := by simpa using heqLen
      have has' : ∀ u ∈ as, u < n0 + gs1.length := fun u hu => by
        have := has u (List.mem_cons_of_mem a hu); simp [gs1]; omega
      have hbs' : ∀ u ∈ bs, u < n0 + gs1.length := fun u hu => by
        have := hbs u (List.mem_cons_of_mem b hu); simp [gs1]; omega
      have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hreslen, hreslt, hsem⟩ := ih bs heqLen' gs1 has' hbs'
      dsimp only
      change (∃ ex, (compileZipBin op n0 gs1 as bs).1 = gs ++ ex ∧ ex.length = (a :: as).length ∧
          Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
        (wOut :: (compileZipBin op n0 gs1 as bs).2).length = (a :: as).length ∧
        (∀ u ∈ wOut :: (compileZipBin op n0 gs1 as bs).2, u < n0 + (compileZipBin op n0 gs1 as bs).1.length) ∧
        (∀ y : List Bool, y.length = n0 → ∀ i, i < (a :: as).length →
          ((Circuit.mk (compileZipBin op n0 gs1 as bs).1 0).wires y).getD
              ((wOut :: (compileZipBin op n0 gs1 as bs).2).getD i 0) false =
            op.eval [((Circuit.mk gs 0).wires y).getD ((a :: as).getD i 0) false,
                     ((Circuit.mk gs 0).wires y).getD ((b :: bs).getD i 0) false])
      refine ⟨⟨[gBin] ++ ex2, by rw [hgs2]; simp [gs1, List.append_assoc], by simp [hlen2],
        monotone2_append [gBin] ex2 0 hgBin_mon hmon2,
        readsBack_append (n0 + gs.length) [gBin] ex2 0 hgBin_rb (by
          have : n0 + gs.length + [gBin].length = n0 + gs1.length := by simp [gs1]; omega
          rw [this]; exact hrb2)⟩,
        by simp [hreslen], ?_, ?_⟩
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · rw [hgs2]; simp [wOut, gs1]
        · exact hreslt u hu
      · intro y hy i hi
        cases i with
        | zero =>
          simp only [List.getD_cons_zero]
          rw [hgs2, wires_prefix_n0 n0 gs1 ex2 y hy wOut (by simp [wOut, gs1])]
          change ((Circuit.mk (gs ++ [gBin]) 0).wires y).getD (n0 + gs.length) false = _
          rw [wires_snoc_last n0 gs gBin y hy]
          simp [gBin]
        | succ i' =>
          simp only [List.getD_cons_succ]
          have hi' : i' < as.length := by simp at hi; omega
          have hi_b : i' < bs.length := by omega
          rw [hsem y hy i' hi']
          have ha_lt : as.getD i' 0 < n0 + gs.length := by
            rw [List.getD_eq_getElem as 0 hi']; exact has as[i'] (List.mem_cons_of_mem a (List.getElem_mem hi'))
          have hb_lt : bs.getD i' 0 < n0 + gs.length := by
            rw [List.getD_eq_getElem bs 0 hi_b]; exact hbs bs[i'] (List.mem_cons_of_mem b (List.getElem_mem hi_b))
          rw [wires_prefix_n0 n0 gs [gBin] y hy (as.getD i' 0) ha_lt,
              wires_prefix_n0 n0 gs [gBin] y hy (bs.getD i' 0) hb_lt]

def compileExclOr (n0 cFalse : ℕ) (gs : List Gate) (ws : List ℕ) : List Gate × List ℕ :=
  let r1 := compilePrefOr n0 gs cFalse ws
  let r2 := compilePrefOr n0 r1.1 cFalse ws.reverse
  compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse

lemma any_reverse_take_eq_drop {α : Type*} (l : List α) (f : α → Bool) (i : ℕ) (hi : i < l.length) :
    (l.reverse.take (l.length - 1 - i)).any f = (l.drop (i + 1)).any f := by
  have h1 : l.reverse.take (l.length - 1 - i) = (l.drop (i + 1)).reverse := by
    rw [List.reverse_drop]
    congr 1
    omega
  rw [h1]
  simp [List.any_reverse]

lemma any_take_or_drop_iff {α : Type*} (l : List α) (f : α → Bool) (i : ℕ) (hi : i < l.length) :
    ((l.take i).any f || (l.drop (i + 1)).any f) = true ↔
      ∃ j : Fin l.length, j.val ≠ i ∧ f l[j.val] = true := by
  simp only [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (⟨x, hx, hfx⟩ | ⟨x, hx, hfx⟩)
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      have hjl : j < l.length := by simp at hj; omega
      have hji : j < i := by simp at hj; omega
      exact ⟨⟨j, hjl⟩, by dsimp only; omega, by simpa [List.getElem_take] using hfx⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      have hjl : i + 1 + j < l.length := by simp at hj; omega
      refine ⟨⟨i + 1 + j, hjl⟩, by dsimp only; omega, ?_⟩
      simpa [List.getElem_drop] using hfx
  · rintro ⟨⟨j, hjl⟩, hne, hfj⟩
    dsimp only at hne hfj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      refine ⟨l[j], ?_, hfj⟩
      rw [List.mem_iff_getElem]
      exact ⟨j, by simp; omega, by simp [List.getElem_take]⟩
    · right
      refine ⟨l[j], ?_, hfj⟩
      rw [List.mem_iff_getElem]
      refine ⟨j - (i + 1), by simp; omega, ?_⟩
      simp only [List.getElem_drop]
      congr 1; omega

lemma compileExclOr_spec (n0 cFalse : ℕ) (ws : List ℕ) (gs : List Gate)
    (hcf : cFalse < n0 + gs.length)
    (hws : ∀ w ∈ ws, w < n0 + gs.length) :
    let res := compileExclOr n0 cFalse gs ws
    (∃ ex, res.1 = gs ++ ex ∧ ex.length = 3 * ws.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.length = ws.length ∧
    (∀ u ∈ res.2, u < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ∀ i, i < ws.length →
        ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
          decide (∃ j : Fin ws.length, j.val ≠ i ∧ ((Circuit.mk gs 0).wires y).getD ws[j.val] false = true)) := by
  let r1 := compilePrefOr n0 gs cFalse ws
  have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hlen_r1, hlt_r1, hsem1⟩ :=
    compilePrefOr_spec n0 ws gs cFalse hcf hws
  have hcf1 : cFalse < n0 + r1.1.length := by change cFalse < n0 + (compilePrefOr n0 gs cFalse ws).1.length; rw [hgs1]; simp; omega
  have hws_rev : ∀ w ∈ ws.reverse, w < n0 + r1.1.length := fun w hw => by
    change w < n0 + (compilePrefOr n0 gs cFalse ws).1.length
    have := hws w (List.mem_reverse.mp hw); rw [hgs1]; simp; omega
  let r2 := compilePrefOr n0 r1.1 cFalse ws.reverse
  have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hlen_r2, hlt_r2, hsem2⟩ :=
    compilePrefOr_spec n0 ws.reverse r1.1 cFalse hcf1 hws_rev
  have hlen_eq : r1.2.length = r2.2.reverse.length := by
    change (compilePrefOr n0 gs cFalse ws).2.length = (compilePrefOr n0 r1.1 cFalse ws.reverse).2.reverse.length
    simp [hlen_r1, hlen_r2]
  have hr1_lt2 : ∀ u ∈ r1.2, u < n0 + r2.1.length := fun u hu => by
    change u < n0 + (compilePrefOr n0 r1.1 cFalse ws.reverse).1.length
    have h1 : u < n0 + r1.1.length := hlt_r1 u hu; rw [hgs2]; simp; omega
  have hr2_lt2 : ∀ u ∈ r2.2.reverse, u < n0 + r2.1.length := fun u hu =>
    hlt_r2 u (List.mem_reverse.mp hu)
  have ⟨⟨ex3, hgs3, hlen3, hmon3, hrb3⟩, hlen_r3, hlt_r3, hsem3⟩ :=
    compileZipBin_spec GateOp.or (Or.inr rfl) n0 r1.2 r2.2.reverse hlen_eq r2.1 hr1_lt2 hr2_lt2
  dsimp only
  change (∃ ex, (compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse).1 = gs ++ ex ∧ ex.length = 3 * ws.length ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    (compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse).2.length = ws.length ∧
    (∀ u ∈ (compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse).2,
      u < n0 + (compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse).1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ∀ i, i < ws.length →
        ((Circuit.mk (compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse).1 0).wires y).getD
            ((compileZipBin GateOp.or n0 r2.1 r1.2 r2.2.reverse).2.getD i 0) false =
          decide (∃ j : Fin ws.length, j.val ≠ i ∧ ((Circuit.mk gs 0).wires y).getD ws[j.val] false = true))
  have hgs2' : r2.1 = r1.1 ++ ex2 := hgs2
  have hgs1' : r1.1 = gs ++ ex1 := hgs1
  have hlen_r1' : r1.2.length = ws.length := hlen_r1
  have hlen_r2' : r2.2.length = ws.length := by simpa using hlen_r2
  refine ⟨⟨ex1 ++ ex2 ++ ex3, by rw [hgs3, hgs2', hgs1']; simp [List.append_assoc],
      by simp [hlen1, hlen2, hlen3, hlen_r1']; omega,
      monotone2_append (ex1 ++ ex2) ex3 0 (monotone2_append ex1 ex2 0 hmon1 hmon2) hmon3,
      readsBack_append (n0 + gs.length) (ex1 ++ ex2) ex3 0
        (readsBack_append (n0 + gs.length) ex1 ex2 0 hrb1 (by
          have : n0 + gs.length + ex1.length = n0 + r1.1.length := by rw [hgs1', List.length_append]; omega
          rw [this]; exact hrb2))
        (by
          have : n0 + gs.length + (ex1 ++ ex2).length = n0 + r2.1.length := by
            rw [hgs2', hgs1']; simp; omega
          rw [this]; exact hrb3)⟩,
    by rw [hlen_r3, hlen_r1'], hlt_r3, ?_⟩
  intro y hy hcfv i hi
  have hi_r1 : i < r1.2.length := by omega
  rw [hsem3 y hy i hi_r1]
  simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  have hpref_val : ((Circuit.mk r2.1 0).wires y).getD (r1.2.getD i 0) false =
      (ws.take i).any (fun w => ((Circuit.mk gs 0).wires y).getD w false) := by
    have hlt_w : r1.2.getD i 0 < n0 + r1.1.length := by
      rw [List.getD_eq_getElem _ _ hi_r1]; exact hlt_r1 _ (List.getElem_mem hi_r1)
    rw [hgs2', wires_prefix_n0 n0 r1.1 ex2 y hy (r1.2.getD i 0) hlt_w]
    rw [hsem1 y hy i hi, hcfv, Bool.false_or]
  have hsuff_idx : ws.length - 1 - i < ws.reverse.length := by simp; omega
  have hsuff_val : ((Circuit.mk r2.1 0).wires y).getD (r2.2.reverse.getD i 0) false =
      (ws.drop (i + 1)).any (fun w => ((Circuit.mk gs 0).wires y).getD w false) := by
    have hi_rev : i < r2.2.reverse.length := by simp [hlen_r2']; omega
    have hrev_get : r2.2.reverse.getD i 0 = r2.2.getD (ws.length - 1 - i) 0 := by
      rw [List.getD_eq_getElem _ _ hi_rev, List.getD_eq_getElem _ _ (by omega),
          List.getElem_reverse]
      congr 1; omega
    rw [hrev_get, hsem2 y hy (ws.length - 1 - i) hsuff_idx]
    have hcf1v : ((Circuit.mk r1.1 0).wires y).getD cFalse false = false := by
      rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy cFalse hcf]; exact hcfv
    rw [hcf1v, Bool.false_or]
    have hcongr : (ws.reverse.take (ws.length - 1 - i)).any (fun w => ((Circuit.mk r1.1 0).wires y).getD w false) =
        (ws.reverse.take (ws.length - 1 - i)).any (fun w => ((Circuit.mk gs 0).wires y).getD w false) := by
      apply list_any_congr_mem
      intro w hw
      have hw_ws : w ∈ ws := List.mem_reverse.mp (List.mem_of_mem_take hw)
      rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy w (hws w hw_ws)]
    rw [hcongr]
    exact any_reverse_take_eq_drop ws (fun w => ((Circuit.mk gs 0).wires y).getD w false) i hi
  rw [hpref_val, hsuff_val]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact any_take_or_drop_iff ws (fun w => ((Circuit.mk gs 0).wires y).getD w false) i hi

def compileManyOrChains (n0 cFalse : ℕ) (gs : List Gate) : List (List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | xs :: xss =>
    let r1 := compileOrChain n0 cFalse gs xs
    let r2 := compileManyOrChains n0 cFalse r1.1 xss
    (r2.1, r1.2 :: r2.2)

lemma compileManyOrChains_spec (n0 cFalse : ℕ) (xss : List (List ℕ)) :
    ∀ (gs : List Gate),
    cFalse < n0 + gs.length →
    (∀ xs ∈ xss, ∀ w ∈ xs, w < n0 + gs.length) →
    let res := compileManyOrChains n0 cFalse gs xss
    (∃ ex, res.1 = gs ++ ex ∧ ex.length ≤ (xss.map List.length).sum ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.length = xss.length ∧
    (∀ u ∈ res.2, u < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ∀ i (hi : i < xss.length),
        ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
          xss[i].any (fun w => ((Circuit.mk gs 0).wires y).getD w false)) := by
  induction xss with
  | nil =>
    intro gs _ _
    refine ⟨⟨[], by simp [compileManyOrChains], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      by simp [compileManyOrChains], fun u hu => by simp [compileManyOrChains] at hu,
      fun _ _ _ i hi => by simp at hi⟩
  | cons xs xss ih =>
    intro gs hcf hxss
    have hxs : ∀ w ∈ xs, w < n0 + gs.length := hxss xs (List.mem_cons_self ..)
    let r1 := compileOrChain n0 cFalse gs xs
    have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hout1, hsem1⟩ := compileOrChain_spec n0 cFalse xs gs hcf hxs
    have hgs1' : r1.1 = gs ++ ex1 := hgs1
    have hout1' : r1.2 < n0 + r1.1.length := hout1
    have hcf1 : cFalse < n0 + r1.1.length := by rw [hgs1']; simp; omega
    have hxss' : ∀ ys ∈ xss, ∀ w ∈ ys, w < n0 + r1.1.length := fun ys hys w hw => by
      have := hxss ys (List.mem_cons_of_mem xs hys) w hw; rw [hgs1']; simp; omega
    have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hlen_r2, hlt_r2, hsem2⟩ := ih r1.1 hcf1 hxss'
    dsimp only
    change (∃ ex, (compileManyOrChains n0 cFalse r1.1 xss).1 = gs ++ ex ∧
        ex.length ≤ ((xs :: xss).map List.length).sum ∧
        Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
      (r1.2 :: (compileManyOrChains n0 cFalse r1.1 xss).2).length = (xs :: xss).length ∧
      (∀ u ∈ r1.2 :: (compileManyOrChains n0 cFalse r1.1 xss).2,
        u < n0 + (compileManyOrChains n0 cFalse r1.1 xss).1.length) ∧
      (∀ y : List Bool, y.length = n0 →
        ((Circuit.mk gs 0).wires y).getD cFalse false = false →
        ∀ i (hi : i < (xs :: xss).length),
          ((Circuit.mk (compileManyOrChains n0 cFalse r1.1 xss).1 0).wires y).getD
              ((r1.2 :: (compileManyOrChains n0 cFalse r1.1 xss).2).getD i 0) false =
            (xs :: xss)[i].any (fun w => ((Circuit.mk gs 0).wires y).getD w false))
    refine ⟨⟨ex1 ++ ex2, by rw [hgs2, hgs1', List.append_assoc], by simp; omega,
      monotone2_append ex1 ex2 0 hmon1 hmon2,
      readsBack_append (n0 + gs.length) ex1 ex2 0 hrb1 (by
        have : n0 + gs.length + ex1.length = n0 + r1.1.length := by rw [hgs1', List.length_append]; omega
        rw [this]; exact hrb2)⟩,
      by simp [hlen_r2], ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · rw [hgs2]; simp; omega
      · exact hlt_r2 u hu
    · intro y hy hcfv i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hgs2, wires_prefix_n0 n0 r1.1 ex2 y hy r1.2 hout1']
        exact hsem1 y hy hcfv
      | succ i' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hi' : i' < xss.length := by simp at hi; omega
        have hcf1v : ((Circuit.mk r1.1 0).wires y).getD cFalse false = false := by
          rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy cFalse hcf]; exact hcfv
        rw [hsem2 y hy hcf1v i' hi']
        apply list_any_congr_mem
        intro w hw
        have hw_lt : w < n0 + gs.length := hxss xss[i'] (List.mem_cons_of_mem xs (List.getElem_mem hi')) w hw
        rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy w hw_lt]

def compileManyAndChains (n0 cTrue : ℕ) (gs : List Gate) : List (List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | xs :: xss =>
    let r1 := compileAndChain n0 cTrue gs xs
    let r2 := compileManyAndChains n0 cTrue r1.1 xss
    (r2.1, r1.2 :: r2.2)

lemma compileManyAndChains_spec (n0 cTrue : ℕ) (xss : List (List ℕ)) :
    ∀ (gs : List Gate),
    cTrue < n0 + gs.length →
    (∀ xs ∈ xss, ∀ w ∈ xs, w < n0 + gs.length) →
    let res := compileManyAndChains n0 cTrue gs xss
    (∃ ex, res.1 = gs ++ ex ∧ ex.length ≤ (xss.map List.length).sum ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.length = xss.length ∧
    (∀ u ∈ res.2, u < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cTrue false = true →
      ∀ i (hi : i < xss.length),
        ((Circuit.mk res.1 0).wires y).getD (res.2.getD i 0) false =
          xss[i].all (fun w => ((Circuit.mk gs 0).wires y).getD w false)) := by
  induction xss with
  | nil =>
    intro gs _ _
    refine ⟨⟨[], by simp [compileManyAndChains], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      by simp [compileManyAndChains], fun u hu => by simp [compileManyAndChains] at hu,
      fun _ _ _ i hi => by simp at hi⟩
  | cons xs xss ih =>
    intro gs hct hxss
    have hxs : ∀ w ∈ xs, w < n0 + gs.length := hxss xs (List.mem_cons_self ..)
    let r1 := compileAndChain n0 cTrue gs xs
    have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hout1, hsem1⟩ := compileAndChain_spec n0 cTrue xs gs hct hxs
    have hgs1' : r1.1 = gs ++ ex1 := hgs1
    have hout1' : r1.2 < n0 + r1.1.length := hout1
    have hct1 : cTrue < n0 + r1.1.length := by rw [hgs1']; simp; omega
    have hxss' : ∀ ys ∈ xss, ∀ w ∈ ys, w < n0 + r1.1.length := fun ys hys w hw => by
      have := hxss ys (List.mem_cons_of_mem xs hys) w hw; rw [hgs1']; simp; omega
    have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hlen_r2, hlt_r2, hsem2⟩ := ih r1.1 hct1 hxss'
    dsimp only
    change (∃ ex, (compileManyAndChains n0 cTrue r1.1 xss).1 = gs ++ ex ∧
        ex.length ≤ ((xs :: xss).map List.length).sum ∧
        Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
      (r1.2 :: (compileManyAndChains n0 cTrue r1.1 xss).2).length = (xs :: xss).length ∧
      (∀ u ∈ r1.2 :: (compileManyAndChains n0 cTrue r1.1 xss).2,
        u < n0 + (compileManyAndChains n0 cTrue r1.1 xss).1.length) ∧
      (∀ y : List Bool, y.length = n0 →
        ((Circuit.mk gs 0).wires y).getD cTrue false = true →
        ∀ i (hi : i < (xs :: xss).length),
          ((Circuit.mk (compileManyAndChains n0 cTrue r1.1 xss).1 0).wires y).getD
              ((r1.2 :: (compileManyAndChains n0 cTrue r1.1 xss).2).getD i 0) false =
            (xs :: xss)[i].all (fun w => ((Circuit.mk gs 0).wires y).getD w false))
    refine ⟨⟨ex1 ++ ex2, by rw [hgs2, hgs1', List.append_assoc], by simp; omega,
      monotone2_append ex1 ex2 0 hmon1 hmon2,
      readsBack_append (n0 + gs.length) ex1 ex2 0 hrb1 (by
        have : n0 + gs.length + ex1.length = n0 + r1.1.length := by rw [hgs1', List.length_append]; omega
        rw [this]; exact hrb2)⟩,
      by simp [hlen_r2], ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · rw [hgs2]; simp; omega
      · exact hlt_r2 u hu
    · intro y hy hctv i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [hgs2, wires_prefix_n0 n0 r1.1 ex2 y hy r1.2 hout1']
        exact hsem1 y hy hctv
      | succ i' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hi' : i' < xss.length := by simp at hi; omega
        have hct1v : ((Circuit.mk r1.1 0).wires y).getD cTrue false = true := by
          rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy cTrue hct]; exact hctv
        rw [hsem2 y hy hct1v i' hi']
        apply list_all_congr_mem
        intro w hw
        have hw_lt : w < n0 + gs.length := hxss xss[i'] (List.mem_cons_of_mem xs (List.getElem_mem hi')) w hw
        rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy w hw_lt]

def compileDirs (n0 cFalse : ℕ) (gs : List Gate) : List (List (List ℕ)) → List Gate × List (List ℕ)
  | [] => (gs, [])
  | dGroups :: rest =>
    let r1 := compileManyOrChains n0 cFalse gs dGroups
    let r2 := compileExclOr n0 cFalse r1.1 r1.2
    let r3 := compileDirs n0 cFalse r2.1 rest
    (r3.1, r2.2 :: r3.2)

lemma compileDirs_spec (n0 cFalse : ℕ) (dirsGroups : List (List (List ℕ))) :
    ∀ (gs : List Gate),
    cFalse < n0 + gs.length →
    (∀ dg ∈ dirsGroups, ∀ xs ∈ dg, ∀ w ∈ xs, w < n0 + gs.length) →
    let res := compileDirs n0 cFalse gs dirsGroups
    (∃ ex, res.1 = gs ++ ex ∧
      ex.length ≤ (dirsGroups.map (fun dg => (dg.map List.length).sum + 3 * dg.length)).sum ∧
      Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
    res.2.length = dirsGroups.length ∧
    (∀ di, di < dirsGroups.length → (res.2.getD di []).length = (dirsGroups.getD di []).length) ∧
    (∀ row ∈ res.2, ∀ u ∈ row, u < n0 + res.1.length) ∧
    (∀ y : List Bool, y.length = n0 →
      ((Circuit.mk gs 0).wires y).getD cFalse false = false →
      ∀ di (hdi : di < dirsGroups.length) ci, ci < dirsGroups[di].length →
        ((Circuit.mk res.1 0).wires y).getD ((res.2.getD di []).getD ci 0) false =
          decide (∃ cj : Fin dirsGroups[di].length, cj.val ≠ ci ∧
            dirsGroups[di][cj.val].any (fun w => ((Circuit.mk gs 0).wires y).getD w false) = true)) := by
  induction dirsGroups with
  | nil =>
    intro gs _ _
    refine ⟨⟨[], by simp [compileDirs], by simp, fun _ h => by simp at h, fun j hj => by simp at hj⟩,
      by simp [compileDirs], fun di hdi => by simp at hdi,
      fun row hrow => by simp [compileDirs] at hrow,
      fun _ _ _ di hdi => by simp at hdi⟩
  | cons dg rest ih =>
    intro gs hcf hdg
    have hdg0 : ∀ xs ∈ dg, ∀ w ∈ xs, w < n0 + gs.length := hdg dg (List.mem_cons_self ..)
    let r1 := compileManyOrChains n0 cFalse gs dg
    have ⟨⟨ex1, hgs1, hlen1, hmon1, hrb1⟩, hlen_r1, hlt_r1, hsem1⟩ :=
      compileManyOrChains_spec n0 cFalse dg gs hcf hdg0
    have hgs1' : r1.1 = gs ++ ex1 := hgs1
    have hlen_r1' : r1.2.length = dg.length := hlen_r1
    have hcf1 : cFalse < n0 + r1.1.length := by rw [hgs1']; simp; omega
    let r2 := compileExclOr n0 cFalse r1.1 r1.2
    have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hlen_r2, hlt_r2, hsem2⟩ :=
      compileExclOr_spec n0 cFalse r1.2 r1.1 hcf1 hlt_r1
    have hgs2' : r2.1 = r1.1 ++ ex2 := hgs2
    have hlen_r2' : r2.2.length = r1.2.length := hlen_r2
    have hcf2 : cFalse < n0 + r2.1.length := by rw [hgs2']; simp; omega
    have hrest : ∀ dg' ∈ rest, ∀ xs ∈ dg', ∀ w ∈ xs, w < n0 + r2.1.length := fun dg' hdg' xs hxs w hw => by
      have := hdg dg' (List.mem_cons_of_mem dg hdg') xs hxs w hw
      rw [hgs2', hgs1']; simp; omega
    have ⟨⟨ex3, hgs3, hlen3, hmon3, hrb3⟩, hlen_r3, hrowlen_r3, hlt_r3, hsem3⟩ := ih r2.1 hcf2 hrest
    dsimp only
    change (∃ ex, (compileDirs n0 cFalse r2.1 rest).1 = gs ++ ex ∧
        ex.length ≤ ((dg :: rest).map (fun dg => (dg.map List.length).sum + 3 * dg.length)).sum ∧
        Monotone2 ⟨ex, 0⟩ ∧ ReadsBack (n0 + gs.length) ⟨ex, 0⟩) ∧
      (r2.2 :: (compileDirs n0 cFalse r2.1 rest).2).length = (dg :: rest).length ∧
      (∀ di, di < (dg :: rest).length →
        ((r2.2 :: (compileDirs n0 cFalse r2.1 rest).2).getD di []).length = ((dg :: rest).getD di []).length) ∧
      (∀ row ∈ r2.2 :: (compileDirs n0 cFalse r2.1 rest).2,
        ∀ u ∈ row, u < n0 + (compileDirs n0 cFalse r2.1 rest).1.length) ∧
      (∀ y : List Bool, y.length = n0 →
        ((Circuit.mk gs 0).wires y).getD cFalse false = false →
        ∀ di (hdi : di < (dg :: rest).length) ci, ci < (dg :: rest)[di].length →
          ((Circuit.mk (compileDirs n0 cFalse r2.1 rest).1 0).wires y).getD
              (((r2.2 :: (compileDirs n0 cFalse r2.1 rest).2).getD di []).getD ci 0) false =
            decide (∃ cj : Fin (dg :: rest)[di].length, cj.val ≠ ci ∧
              (dg :: rest)[di][cj.val].any (fun w => ((Circuit.mk gs 0).wires y).getD w false) = true))
    refine ⟨⟨ex1 ++ ex2 ++ ex3, by rw [hgs3, hgs2', hgs1']; simp [List.append_assoc],
        by simp only [List.length_append, List.map_cons, List.sum_cons, hlen2, hlen_r1']; omega,
        monotone2_append (ex1 ++ ex2) ex3 0 (monotone2_append ex1 ex2 0 hmon1 hmon2) hmon3,
        readsBack_append (n0 + gs.length) (ex1 ++ ex2) ex3 0
          (readsBack_append (n0 + gs.length) ex1 ex2 0 hrb1 (by
            have : n0 + gs.length + ex1.length = n0 + r1.1.length := by rw [hgs1', List.length_append]; omega
            rw [this]; exact hrb2))
          (by
            have : n0 + gs.length + (ex1 ++ ex2).length = n0 + r2.1.length := by
              rw [hgs2', hgs1']; simp; omega
            rw [this]; exact hrb3)⟩,
      by simp [hlen_r3], ?_, ?_, ?_⟩
    · intro di hdi
      cases di with
      | zero => simp [hlen_r2', hlen_r1']
      | succ di' =>
        simp only [List.getD_cons_succ]
        exact hrowlen_r3 di' (by simp at hdi; omega)
    · intro row hrow u hu
      simp only [List.mem_cons] at hrow
      rcases hrow with rfl | hrow
      · have h1 : u < n0 + r2.1.length := hlt_r2 u hu; rw [hgs3]; simp; omega
      · exact hlt_r3 row hrow u hu
    · intro y hy hcfv di hdi ci hci
      cases di with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero] at hci ⊢
        have hci' : ci < r1.2.length := by omega
        have hci_r2 : ci < r2.2.length := by omega
        have hlt_u : r2.2.getD ci 0 < n0 + r2.1.length := by
          rw [List.getD_eq_getElem _ _ hci_r2]; exact hlt_r2 _ (List.getElem_mem hci_r2)
        rw [hgs3, wires_prefix_n0 n0 r2.1 ex3 y hy (r2.2.getD ci 0) hlt_u]
        have hcf1v : ((Circuit.mk r1.1 0).wires y).getD cFalse false = false := by
          rw [hgs1', wires_prefix_n0 n0 gs ex1 y hy cFalse hcf]; exact hcfv
        rw [hsem2 y hy hcf1v ci hci']
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨⟨cj, hcj⟩, hne, hval⟩
          refine ⟨⟨cj, by omega⟩, hne, ?_⟩
          have h1 := hsem1 y hy hcfv cj (by omega)
          rw [List.getD_eq_getElem _ _ hcj] at h1
          rw [← h1]; exact hval
        · rintro ⟨⟨cj, hcj⟩, hne, hval⟩
          have hcj' : cj < r1.2.length := by omega
          refine ⟨⟨cj, hcj'⟩, hne, ?_⟩
          have h1 := hsem1 y hy hcfv cj hcj
          rw [List.getD_eq_getElem _ _ hcj'] at h1
          rw [h1]; exact hval
      | succ di' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ] at hci ⊢
        have hdi' : di' < rest.length := by simp at hdi; omega
        have hcf2v : ((Circuit.mk r2.1 0).wires y).getD cFalse false = false := by
          rw [hgs2', hgs1', List.append_assoc, wires_prefix_n0 n0 gs (ex1 ++ ex2) y hy cFalse hcf]; exact hcfv
        rw [hsem3 y hy hcf2v di' hdi' ci hci]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor <;> rintro ⟨cj, hne, hval⟩ <;> refine ⟨cj, hne, ?_⟩
        · have hcongr : rest[di'][cj.val].any (fun w => ((Circuit.mk r2.1 0).wires y).getD w false) =
              rest[di'][cj.val].any (fun w => ((Circuit.mk gs 0).wires y).getD w false) := by
            apply list_any_congr_mem; intro w hw
            have hw_lt : w < n0 + gs.length :=
              hdg rest[di'] (List.mem_cons_of_mem dg (List.getElem_mem hdi')) _ (List.getElem_mem cj.isLt) w hw
            rw [hgs2', hgs1', List.append_assoc, wires_prefix_n0 n0 gs (ex1 ++ ex2) y hy w hw_lt]
          rw [← hcongr]; exact hval
        · have hcongr : rest[di'][cj.val].any (fun w => ((Circuit.mk r2.1 0).wires y).getD w false) =
              rest[di'][cj.val].any (fun w => ((Circuit.mk gs 0).wires y).getD w false) := by
            apply list_any_congr_mem; intro w hw
            have hw_lt : w < n0 + gs.length :=
              hdg rest[di'] (List.mem_cons_of_mem dg (List.getElem_mem hdi')) _ (List.getElem_mem cj.isLt) w hw
            rw [hgs2', hgs1', List.append_assoc, wires_prefix_n0 n0 gs (ex1 ++ ex2) y hy w hw_lt]
          rw [hcongr]; exact hval

def runsG {n : ℕ} (g : Finset (Fin n) → Fin n → Bool) : ℕ → Finset (Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)

def setInput {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma setInput_length {n : ℕ} (x : Finset (Fin n)) : (setInput x).length = n + 2 := by
  simp [setInput]

lemma setInput_getD_lt {n : ℕ} (x : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (setInput x).getD i false = decide (⟨i, hi⟩ ∈ x) := by
  simp only [setInput, List.getD]
  have h1 : i < (List.ofFn (fun k : Fin n => decide (k ∈ x))).length := by simp [hi]
  rw [List.getElem?_append_left h1, List.getElem?_eq_getElem h1]
  simp

lemma setInput_getD_n {n : ℕ} (x : Finset (Fin n)) :
    (setInput x).getD n false = false := by
  simp only [setInput, List.getD]
  have hlen : (List.ofFn (fun k : Fin n => decide (k ∈ x))).length = n := by simp
  rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  rfl

lemma setInput_getD_n1 {n : ℕ} (x : Finset (Fin n)) :
    (setInput x).getD (n + 1) false = true := by
  simp only [setInput, List.getD]
  have hlen : (List.ofFn (fun k : Fin n => decide (k ∈ x))).length = n := by simp
  rw [List.getElem?_append_right (by omega), hlen]
  have : n + 1 - n = 1 := by omega
  rw [this]; rfl

lemma setInput_mono {n : ℕ} {x y : Finset (Fin n)} (hxy : x ⊆ y) :
    ∀ i < n + 2, (setInput x).getD i false ≤ (setInput y).getD i false := by
  intro i hi
  by_cases hin : i < n
  · rw [setInput_getD_lt x i hin, setInput_getD_lt y i hin]
    by_cases hm : ⟨i, hin⟩ ∈ x
    · simp [hm, hxy hm]
    · simp [hm]
  · by_cases hi1 : i = n
    · subst hi1; rw [setInput_getD_n, setInput_getD_n]
    · have hi2 : i = n + 1 := by omega
      subst hi2; rw [setInput_getD_n1, setInput_getD_n1]

lemma runsG_markov_aux {n : ℕ} (g : Finset (Fin n) → Fin n → Bool)
    (C : Circuit) (hfit : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (tap : Fin n → Fin (n + 2 + C.size))
    (htap : ∀ x j, (C.wires (setInput x)).getD (tap j).val false = g x j) :
    ∀ m x, runsG g m x → notRank (n + 2) C (setInput x) + m < 2 ^ notCount C := by
  intro m
  induction m with
  | zero =>
    intro x _
    simpa using notRank_lt (n + 2) C (setInput x)
  | succ m ih =>
    intro x ⟨u, v, j, hpu, huv, hvx, hgu, hgv⟩
    have hih := ih u hpu
    have h1 := markov_step_wire (n + 2) C (setInput u) (setInput v) (tap j).val
      hfit hrb (tap j).isLt (setInput_length u) (setInput_length v) (setInput_mono huv)
    have h2 := markov_step_wire (n + 2) C (setInput v) (setInput x) (tap j).val
      hfit hrb (tap j).isLt (setInput_length v) (setInput_length x) (setInput_mono hvx)
    have hlt : notRank (n + 2) C (setInput v) < notRank (n + 2) C (setInput u) := by
      rcases lt_or_eq_of_le h1.1 with h | heq
      · exact h
      · have hle := h1.2 heq
        rw [htap u j, htap v j, hgu, hgv] at hle
        exact absurd hle (by decide)
    omega

lemma runsG_markov_bound {n : ℕ} (g : Finset (Fin n) → Fin n → Bool)
    (C : Circuit) (hfit : FanInTwo C) (hrb : ReadsBack (n + 2) C)
    (tap : Fin n → Fin (n + 2 + C.size))
    (htap : ∀ x j, (C.wires (setInput x)).getD (tap j).val false = g x j)
    (m : ℕ) (x : Finset (Fin n)) (hr : runsG g m x) :
    m + 1 ≤ 2 ^ notCount C := by
  have := runsG_markov_aux g C hfit hrb tap htap m x hr
  omega

lemma runsG_mono {n : ℕ} {g : Finset (Fin n) → Fin n → Bool} {m : ℕ} {x y : Finset (Fin n)}
    (hxy : x ⊆ y) (h : runsG g m x) : runsG g m y := by
  cases m with
  | zero => trivial
  | succ m' =>
    rcases h with ⟨u, v, j, hpu, huv, hvx, hgu, hgv⟩
    exact ⟨u, v, j, hpu, huv, Finset.Subset.trans hvx hxy, hgu, hgv⟩

lemma nat_cauchy_schwarz {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have hnonneg : (0 : ℤ) ≤ ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
      2 * (s.card : ℤ) * (∑ i ∈ s, (f i : ℤ) ^ 2) - 2 * (∑ i ∈ s, (f i : ℤ)) ^ 2 := by
    have h1 : ∀ i ∈ s, ∑ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
        (s.card : ℤ) * (f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (∑ j ∈ s, (f j : ℤ)) + ∑ j ∈ s, (f j : ℤ) ^ 2 := by
      intro i _
      have hsq : ∀ j ∈ s, ((f i : ℤ) - (f j : ℤ)) ^ 2 =
          (f i : ℤ) ^ 2 - 2 * (f i : ℤ) * (f j : ℤ) + (f j : ℤ) ^ 2 := fun j _ => by ring
      rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hexp] at hnonneg
  have hz : (∑ i ∈ s, (f i : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (f i : ℤ) ^ 2 := by linarith
  exact_mod_cast hz

section FieldGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

lemma char2_two_eq_zero : (2 : F) = 0 := CharP.cast_eq_zero F 2

lemma char2_add_self (a : F) : a + a = 0 := by
  have h2 : (2 : F) = 0 := char2_two_eq_zero
  calc a + a = (2 : F) * a := by ring
    _ = 0 := by rw [h2, zero_mul]

lemma char2_eq_iff_add_zero (a b : F) : a = b ↔ a + b = 0 := by
  constructor
  · rintro rfl; exact char2_add_self a
  · intro h
    calc a = a + (b + b) := by rw [char2_add_self, add_zero]
      _ = (a + b) + b := by ring
      _ = b := by rw [h, zero_add]

lemma char2_neg_eq (a : F) : -a = a := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact char2_add_self a

lemma char2_sub_eq_add (a b : F) : a - b = a + b := by
  rw [sub_eq_add_neg, char2_neg_eq]

def det2 (p r : F × F) : F := p.1 * r.2 + p.2 * r.1

lemma det2_symm (p r : F × F) : det2 p r = det2 r p := by
  unfold det2; ring

lemma det2_self (p : F × F) : det2 p p = 0 := by
  unfold det2
  have : p.1 * p.2 + p.2 * p.1 = p.1 * p.2 + p.1 * p.2 := by ring
  rw [this]; exact char2_add_self _

def lineVal : Option F → F × F → F
  | none, p => p.1
  | some m, p => p.2 + m * p.1

def projDir (p : F × F) : Option F :=
  if p.1 = 0 then none else some (p.2 * p.1⁻¹)

lemma projDir_eq_iff_det2_zero {p r : F × F} (hp : p ≠ (0, 0)) (hr : r ≠ (0, 0)) :
    projDir p = projDir r ↔ det2 p r = 0 := by
  unfold projDir det2
  by_cases hp1 : p.1 = 0 <;> by_cases hr1 : r.1 = 0
  · simp [hp1, hr1]
  · have hp2 : p.2 ≠ 0 := fun h => hp (Prod.ext hp1 h)
    simp only [hp1, hr1, ↓reduceIte, zero_mul, zero_add, reduceCtorEq, false_iff]
    exact mul_ne_zero hp2 hr1
  · have hr2 : r.2 ≠ 0 := fun h => hr (Prod.ext hr1 h)
    simp only [hp1, hr1, ↓reduceIte, mul_zero, add_zero, reduceCtorEq, false_iff]
    exact mul_ne_zero hp1 hr2
  · simp only [hp1, hr1, ↓reduceIte, Option.some.injEq]
    constructor
    · intro h
      have h1 : p.2 * p.1⁻¹ * (p.1 * r.1) = r.2 * r.1⁻¹ * (p.1 * r.1) := by rw [h]
      have h2 : p.2 * r.1 = p.1 * r.2 := by
        have ha : p.2 * p.1⁻¹ * (p.1 * r.1) = p.2 * r.1 := by
          calc p.2 * p.1⁻¹ * (p.1 * r.1) = p.2 * (p.1⁻¹ * p.1) * r.1 := by ring
            _ = p.2 * 1 * r.1 := by rw [inv_mul_cancel₀ hp1]
            _ = p.2 * r.1 := by ring
        have hb : r.2 * r.1⁻¹ * (p.1 * r.1) = p.1 * r.2 := by
          calc r.2 * r.1⁻¹ * (p.1 * r.1) = p.1 * r.2 * (r.1⁻¹ * r.1) := by ring
            _ = p.1 * r.2 * 1 := by rw [inv_mul_cancel₀ hr1]
            _ = p.1 * r.2 := by ring
        rw [ha, hb] at h1; exact h1
      rw [h2]; exact char2_add_self _
    · intro h
      have h2 : p.1 * r.2 = p.2 * r.1 := (char2_eq_iff_add_zero (p.1 * r.2) (p.2 * r.1)).mpr h
      calc p.2 * p.1⁻¹ = (p.2 * r.1) * (p.1⁻¹ * r.1⁻¹) := by
            rw [show (p.2 * r.1) * (p.1⁻¹ * r.1⁻¹) = p.2 * p.1⁻¹ * (r.1 * r.1⁻¹) by ring,
                mul_inv_cancel₀ hr1, mul_one]
        _ = (p.1 * r.2) * (p.1⁻¹ * r.1⁻¹) := by rw [h2]
        _ = r.2 * r.1⁻¹ := by
            rw [show (p.1 * r.2) * (p.1⁻¹ * r.1⁻¹) = r.2 * r.1⁻¹ * (p.1 * p.1⁻¹) by ring,
                mul_inv_cancel₀ hp1, mul_one]

lemma common_nbr_unique {p r w : F × F} (hdet : det2 p r ≠ 0)
    (hpw : det2 p w = 1) (hrw : det2 r w = 1) :
    w = ((p.1 + r.1) * (det2 p r)⁻¹, (p.2 + r.2) * (det2 p r)⁻¹) := by
  unfold det2 at hdet hpw hrw ⊢
  have hw1 : (p.1 * r.2 + p.2 * r.1) * w.1 = p.1 + r.1 := by
    have h := congrArg (· * r.1) hpw
    have h' := congrArg (· * p.1) hrw
    have hadd : (p.1 * w.2 + p.2 * w.1) * r.1 + (r.1 * w.2 + r.2 * w.1) * p.1 = 1 * r.1 + 1 * p.1 :=
      congrArg₂ (· + ·) h h'
    have hlhs : (p.1 * w.2 + p.2 * w.1) * r.1 + (r.1 * w.2 + r.2 * w.1) * p.1 =
        (p.1 * r.2 + p.2 * r.1) * w.1 := by
      have hz : p.1 * r.1 * w.2 + p.1 * r.1 * w.2 = 0 := char2_add_self _
      calc (p.1 * w.2 + p.2 * w.1) * r.1 + (r.1 * w.2 + r.2 * w.1) * p.1
          = (p.1 * r.1 * w.2 + p.1 * r.1 * w.2) + (p.1 * r.2 + p.2 * r.1) * w.1 := by ring
        _ = (p.1 * r.2 + p.2 * r.1) * w.1 := by rw [hz, zero_add]
    rw [hlhs] at hadd
    simpa [add_comm] using hadd
  have hw2 : (p.1 * r.2 + p.2 * r.1) * w.2 = p.2 + r.2 := by
    have h := congrArg (· * r.2) hpw
    have h' := congrArg (· * p.2) hrw
    have hadd : (p.1 * w.2 + p.2 * w.1) * r.2 + (r.1 * w.2 + r.2 * w.1) * p.2 = 1 * r.2 + 1 * p.2 :=
      congrArg₂ (· + ·) h h'
    have hlhs : (p.1 * w.2 + p.2 * w.1) * r.2 + (r.1 * w.2 + r.2 * w.1) * p.2 =
        (p.1 * r.2 + p.2 * r.1) * w.2 := by
      have hz : p.2 * r.2 * w.1 + p.2 * r.2 * w.1 = 0 := char2_add_self _
      calc (p.1 * w.2 + p.2 * w.1) * r.2 + (r.1 * w.2 + r.2 * w.1) * p.2
          = (p.2 * r.2 * w.1 + p.2 * r.2 * w.1) + (p.1 * r.2 + p.2 * r.1) * w.2 := by ring
        _ = (p.1 * r.2 + p.2 * r.1) * w.2 := by rw [hz, zero_add]
    rw [hlhs] at hadd
    simpa [add_comm] using hadd
  apply Prod.ext
  · calc w.1 = (p.1 * r.2 + p.2 * r.1) * w.1 * (p.1 * r.2 + p.2 * r.1)⁻¹ := by
          rw [mul_comm _ w.1, mul_assoc, mul_inv_cancel₀ hdet, mul_one]
      _ = (p.1 + r.1) * (p.1 * r.2 + p.2 * r.1)⁻¹ := by rw [hw1]
  · calc w.2 = (p.1 * r.2 + p.2 * r.1) * w.2 * (p.1 * r.2 + p.2 * r.1)⁻¹ := by
          rw [mul_comm _ w.2, mul_assoc, mul_inv_cancel₀ hdet, mul_one]
      _ = (p.2 + r.2) * (p.1 * r.2 + p.2 * r.1)⁻¹ := by rw [hw2]

lemma common_nbr_exists {p r : F × F} (hdet : det2 p r ≠ 0) :
    let w := ((p.1 + r.1) * (det2 p r)⁻¹, (p.2 + r.2) * (det2 p r)⁻¹)
    w ≠ (0, 0) ∧ det2 p w = 1 ∧ det2 r w = 1 := by
  dsimp only
  have hp : det2 p ((p.1 + r.1) * (det2 p r)⁻¹, (p.2 + r.2) * (det2 p r)⁻¹) = 1 := by
    unfold det2 at hdet ⊢
    have hz : p.1 * p.2 + p.1 * p.2 = 0 := char2_add_self _
    calc p.1 * ((p.2 + r.2) * (p.1 * r.2 + p.2 * r.1)⁻¹) +
          p.2 * ((p.1 + r.1) * (p.1 * r.2 + p.2 * r.1)⁻¹)
        = ((p.1 * p.2 + p.1 * p.2) + (p.1 * r.2 + p.2 * r.1)) * (p.1 * r.2 + p.2 * r.1)⁻¹ := by ring
      _ = (p.1 * r.2 + p.2 * r.1) * (p.1 * r.2 + p.2 * r.1)⁻¹ := by rw [hz, zero_add]
      _ = 1 := mul_inv_cancel₀ hdet
  have hr : det2 r ((p.1 + r.1) * (det2 p r)⁻¹, (p.2 + r.2) * (det2 p r)⁻¹) = 1 := by
    unfold det2 at hdet ⊢
    have hz : r.1 * r.2 + r.1 * r.2 = 0 := char2_add_self _
    calc r.1 * ((p.2 + r.2) * (p.1 * r.2 + p.2 * r.1)⁻¹) +
          r.2 * ((p.1 + r.1) * (p.1 * r.2 + p.2 * r.1)⁻¹)
        = ((r.1 * r.2 + r.1 * r.2) + (p.1 * r.2 + p.2 * r.1)) * (p.1 * r.2 + p.2 * r.1)⁻¹ := by ring
      _ = (p.1 * r.2 + p.2 * r.1) * (p.1 * r.2 + p.2 * r.1)⁻¹ := by rw [hz, zero_add]
      _ = 1 := mul_inv_cancel₀ hdet
  refine ⟨?_, hp, hr⟩
  intro hzero
  rw [hzero] at hp
  simp [det2] at hp

lemma no_common_nbr_of_det2_zero {p r w : F × F} (hp : p ≠ (0, 0)) (hr : r ≠ (0, 0))
    (hne : p ≠ r) (hdet : det2 p r = 0) (hpw : det2 p w = 1) (hrw : det2 r w = 1) : False := by
  have hdir : projDir p = projDir r := (projDir_eq_iff_det2_zero hp hr).mpr hdet
  unfold projDir at hdir
  by_cases hp1 : p.1 = 0
  · have hr1 : r.1 = 0 := by
      by_contra h; simp [hp1, h] at hdir
    have hp2 : p.2 ≠ 0 := fun h => hp (Prod.ext hp1 h)
    have hr2 : r.2 ≠ 0 := fun h => hr (Prod.ext hr1 h)
    simp only [det2, hp1, hr1, zero_mul, zero_add] at hpw hrw
    have hw1 : w.1 ≠ 0 := fun h => by rw [h, mul_zero] at hpw; exact zero_ne_one hpw
    have heq2 : p.2 = r.2 := by
      have : p.2 * w.1 = r.2 * w.1 := by rw [hpw, hrw]
      exact mul_right_cancel₀ hw1 this
    exact hne (Prod.ext (by rw [hp1, hr1]) heq2)
  · have hr1 : r.1 ≠ 0 := fun h => by simp [hp1, h] at hdir
    simp only [hp1, hr1, ↓reduceIte, Option.some.injEq] at hdir
    let lam := r.1 * p.1⁻¹
    have hr_eq : r = (lam * p.1, lam * p.2) := by
      apply Prod.ext
      · simp only [lam]; rw [mul_assoc, inv_mul_cancel₀ hp1, mul_one]
      · simp only [lam]
        calc r.2 = (r.2 * r.1⁻¹) * r.1 := by rw [mul_assoc, inv_mul_cancel₀ hr1, mul_one]
          _ = (p.2 * p.1⁻¹) * r.1 := by rw [hdir]
          _ = r.1 * p.1⁻¹ * p.2 := by ring
    have hlam_ne1 : lam ≠ 1 := by
      intro h1; apply hne
      rw [hr_eq, h1, one_mul, one_mul]
    have hdet_scale : det2 r w = lam * det2 p w := by
      rw [hr_eq]; unfold det2; ring
    rw [hpw, hrw, mul_one] at hdet_scale
    exact hlam_ne1 hdet_scale.symm

lemma card_det2_eq_one (p : F × F) (hp : p ≠ (0, 0)) :
    ((Finset.univ : Finset (F × F)).filter (fun r => det2 p r = 1)).card = Fintype.card F := by
  by_cases ha : p.1 = 0
  · have hb : p.2 ≠ 0 := fun h => hp (Prod.ext ha h)
    refine Finset.card_bij (fun r _ => r.2) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro r1 hr1 r2 hr2 h2
      rw [Finset.mem_filter] at hr1 hr2
      have hr1' : p.2 * r1.1 = 1 := by simpa [det2, ha] using hr1.2
      have hr2' : p.2 * r2.1 = 1 := by simpa [det2, ha] using hr2.2
      have h1 : r1.1 = r2.1 := mul_left_cancel₀ hb (hr1'.trans hr2'.symm)
      exact Prod.ext h1 h2
    · intro y _
      refine ⟨(p.2⁻¹, y), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [det2, ha, zero_mul, zero_add]
      exact mul_inv_cancel₀ hb
  · refine Finset.card_bij (fun r _ => r.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro r1 hr1 r2 hr2 h1
      rw [Finset.mem_filter] at hr1 hr2
      have hr1' : p.1 * r1.2 + p.2 * r1.1 = 1 := hr1.2
      have hr2' : p.1 * r2.2 + p.2 * r2.1 = 1 := hr2.2
      have h2 : p.1 * r1.2 = p.1 * r2.2 := by
        rw [h1] at hr1'
        have : p.1 * r1.2 + p.2 * r2.1 = p.1 * r2.2 + p.2 * r2.1 := hr1'.trans hr2'.symm
        exact add_right_cancel this
      exact Prod.ext h1 (mul_left_cancel₀ ha h2)
    · intro x _
      refine ⟨(x, p.1⁻¹ * (1 + p.2 * x)), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold det2
      calc p.1 * (p.1⁻¹ * (1 + p.2 * x)) + p.2 * x
          = (p.1 * p.1⁻¹) * (1 + p.2 * x) + p.2 * x := by ring
        _ = 1 + (p.2 * x + p.2 * x) := by rw [mul_inv_cancel₀ ha, one_mul]; ring
        _ = 1 := by rw [char2_add_self, add_zero]

lemma unique_line_two_pts {p1 p2 : F × F} (hne : p1 ≠ p2) :
    ∃! dc : Option F × F, lineVal dc.1 p1 = dc.2 ∧ lineVal dc.1 p2 = dc.2 := by
  by_cases hx : p1.1 = p2.1
  · have hy : p1.2 ≠ p2.2 := fun h => hne (Prod.ext hx h)
    refine ⟨(none, p1.1), ⟨rfl, hx.symm⟩, ?_⟩
    rintro ⟨d, c⟩ ⟨h1, h2⟩
    cases d with
    | none =>
      simp only [lineVal] at h1
      exact Prod.ext rfl h1.symm
    | some m =>
      simp only [lineVal] at h1 h2
      rw [hx] at h1
      have : p1.2 + m * p2.1 = p2.2 + m * p2.1 := h1.trans h2.symm
      exact (hy (add_right_cancel this)).elim
  · have hxd : p1.1 + p2.1 ≠ 0 := fun h => hx ((char2_eq_iff_add_zero p1.1 p2.1).mpr h)
    let m0 := (p1.2 + p2.2) * (p1.1 + p2.1)⁻¹
    let c0 := p1.2 + m0 * p1.1
    refine ⟨(some m0, c0), ⟨rfl, ?_⟩, ?_⟩
    · simp only [lineVal, c0]
      apply (char2_eq_iff_add_zero _ _).mpr
      calc (p2.2 + m0 * p2.1) + (p1.2 + m0 * p1.1)
          = (p1.2 + p2.2) + m0 * (p1.1 + p2.1) := by ring
        _ = (p1.2 + p2.2) + (p1.2 + p2.2) * ((p1.1 + p2.1)⁻¹ * (p1.1 + p2.1)) := by
            simp only [m0]; ring
        _ = (p1.2 + p2.2) + (p1.2 + p2.2) := by rw [inv_mul_cancel₀ hxd, mul_one]
        _ = 0 := char2_add_self _
    · rintro ⟨d, c⟩ ⟨h1, h2⟩
      cases d with
      | none =>
        simp only [lineVal] at h1 h2
        exact (hx (h1.trans h2.symm)).elim
      | some m =>
        simp only [lineVal] at h1 h2
        have hadd : (p1.2 + m * p1.1) + (p2.2 + m * p2.1) = 0 := by
          rw [h1, h2]; exact char2_add_self c
        have hm_eq : m * (p1.1 + p2.1) = p1.2 + p2.2 := by
          apply (char2_eq_iff_add_zero _ _).mpr
          calc m * (p1.1 + p2.1) + (p1.2 + p2.2)
              = (p1.2 + m * p1.1) + (p2.2 + m * p2.1) := by ring
            _ = 0 := hadd
        have hm : m = m0 := by
          simp only [m0]
          calc m = m * (p1.1 + p2.1) * (p1.1 + p2.1)⁻¹ := by
                rw [mul_assoc, mul_inv_cancel₀ hxd, mul_one]
            _ = (p1.2 + p2.2) * (p1.1 + p2.1)⁻¹ := by rw [hm_eq]
        subst hm
        exact Prod.ext rfl h1.symm

def liftPt (p : F × F) : Fin 3 → F := ![1, p.1, p.2]

lemma liftPt_0 (p : F × F) : liftPt p 0 = 1 := rfl
lemma liftPt_1 (p : F × F) : liftPt p 1 = p.1 := rfl
lemma liftPt_2 (p : F × F) : liftPt p 2 = p.2 := rfl

def lineFunc (d : Option F) (c : F) : (Fin 3 → F) →ₗ[F] F :=
  match d with
  | none =>
    { toFun := fun v => c * v 0 + v 1
      map_add' := fun u v => by simp; ring
      map_smul' := fun a v => by simp; ring }
  | some m =>
    { toFun := fun v => c * v 0 + m * v 1 + v 2
      map_add' := fun u v => by simp; ring
      map_smul' := fun a v => by simp; ring }

lemma lineFunc_liftPt_eq_zero (d : Option F) (c : F) (p : F × F) :
    lineFunc d c (liftPt p) = 0 ↔ lineVal d p = c := by
  cases d with
  | none =>
    simp only [lineFunc, lineVal, LinearMap.coe_mk, AddHom.coe_mk, liftPt_0, liftPt_1, mul_one]
    rw [add_comm, ← char2_eq_iff_add_zero]
  | some m =>
    simp only [lineFunc, lineVal, LinearMap.coe_mk, AddHom.coe_mk, liftPt_0, liftPt_1, liftPt_2, mul_one]
    have : c + m * p.1 + p.2 = (p.2 + m * p.1) + c := by ring
    rw [this, ← char2_eq_iff_add_zero]

def nbrFunc (p : F × F) : (Fin 3 → F) →ₗ[F] F where
  toFun v := v 0 + p.1 * v 2 + p.2 * v 1
  map_add' u v := by simp; ring
  map_smul' a v := by simp; ring

lemma nbrFunc_self (p : F × F) : nbrFunc p (liftPt p) = 1 := by
  simp only [nbrFunc, LinearMap.coe_mk, AddHom.coe_mk, liftPt_0, liftPt_1, liftPt_2]
  have : 1 + p.1 * p.2 + p.2 * p.1 = 1 + (p.1 * p.2 + p.1 * p.2) := by ring
  rw [this, char2_add_self, add_zero]

lemma nbrFunc_adj {p r : F × F} (h : det2 r p = 1) : nbrFunc p (liftPt r) = 0 := by
  simp only [nbrFunc, LinearMap.coe_mk, AddHom.coe_mk, liftPt_0, liftPt_1, liftPt_2]
  unfold det2 at h
  have : 1 + p.1 * r.2 + p.2 * r.1 = 1 + (r.1 * p.2 + r.2 * p.1) := by ring
  rw [this, h]; exact char2_add_self 1

lemma liftPt_mem_span_two_on_line {d : Option F} {c : F} {p1 p2 pj : F × F}
    (hne : p1 ≠ p2)
    (h1 : lineVal d p1 = c) (h2 : lineVal d p2 = c) (hj : lineVal d pj = c) :
    ∃ t : F, liftPt pj = (1 + t) • liftPt p1 + t • liftPt p2 := by
  cases d with
  | none =>
    simp only [lineVal] at h1 h2 hj
    have hyne : p1.2 + p2.2 ≠ 0 := fun h =>
      hne (Prod.ext (h1.trans h2.symm) ((char2_eq_iff_add_zero p1.2 p2.2).mpr h))
    let t := (pj.2 + p1.2) * (p1.2 + p2.2)⁻¹
    refine ⟨t, ?_⟩
    funext k; fin_cases k
    · change liftPt pj 0 = (1 + t) * liftPt p1 0 + t * liftPt p2 0
      rw [liftPt_0, liftPt_0, liftPt_0]
      have hz : t + t = 0 := char2_add_self _
      calc (1 : F) = 1 + (t + t) := by rw [hz, add_zero]
        _ = (1 + t) * 1 + t * 1 := by ring
    · change liftPt pj 1 = (1 + t) * liftPt p1 1 + t * liftPt p2 1
      rw [liftPt_1, liftPt_1, liftPt_1, h1, h2, hj]
      have hz : t * c + t * c = 0 := char2_add_self _
      calc c = c + (t * c + t * c) := by rw [hz, add_zero]
        _ = (1 + t) * c + t * c := by ring
    · change liftPt pj 2 = (1 + t) * liftPt p1 2 + t * liftPt p2 2
      rw [liftPt_2, liftPt_2, liftPt_2]
      have hz : p1.2 + p1.2 = 0 := char2_add_self _
      calc pj.2 = (p1.2 + p1.2) + pj.2 := by rw [hz, zero_add]
        _ = p1.2 + (pj.2 + p1.2) * ((p1.2 + p2.2)⁻¹ * (p1.2 + p2.2)) := by
            rw [inv_mul_cancel₀ hyne, mul_one]; ring
        _ = (1 + t) * p1.2 + t * p2.2 := by simp only [t]; ring
  | some m =>
    simp only [lineVal] at h1 h2 hj
    have hxne : p1.1 + p2.1 ≠ 0 := by
      intro hx0
      have hx : p1.1 = p2.1 := (char2_eq_iff_add_zero p1.1 p2.1).mpr hx0
      rw [hx] at h1
      have hy : p1.2 = p2.2 := add_right_cancel (h1.trans h2.symm)
      exact hne (Prod.ext hx hy)
    let t := (pj.1 + p1.1) * (p1.1 + p2.1)⁻¹
    refine ⟨t, ?_⟩
    have hx_eq : (1 + t) * p1.1 + t * p2.1 = pj.1 := by
      have hz : p1.1 + p1.1 = 0 := char2_add_self _
      calc (1 + t) * p1.1 + t * p2.1
          = p1.1 + (pj.1 + p1.1) * ((p1.1 + p2.1)⁻¹ * (p1.1 + p2.1)) := by simp only [t]; ring
        _ = (p1.1 + p1.1) + pj.1 := by rw [inv_mul_cancel₀ hxne, mul_one]; ring
        _ = pj.1 := by rw [hz, zero_add]
    have hy1 : p1.2 = c + m * p1.1 := by
      apply (char2_eq_iff_add_zero _ _).mpr
      calc p1.2 + (c + m * p1.1) = (p1.2 + m * p1.1) + c := by ring
        _ = c + c := by rw [h1]
        _ = 0 := char2_add_self _
    have hy2 : p2.2 = c + m * p2.1 := by
      apply (char2_eq_iff_add_zero _ _).mpr
      calc p2.2 + (c + m * p2.1) = (p2.2 + m * p2.1) + c := by ring
        _ = c + c := by rw [h2]
        _ = 0 := char2_add_self _
    have hyj : pj.2 = c + m * pj.1 := by
      apply (char2_eq_iff_add_zero _ _).mpr
      calc pj.2 + (c + m * pj.1) = (pj.2 + m * pj.1) + c := by ring
        _ = c + c := by rw [hj]
        _ = 0 := char2_add_self _
    funext k; fin_cases k
    · change liftPt pj 0 = (1 + t) * liftPt p1 0 + t * liftPt p2 0
      rw [liftPt_0, liftPt_0, liftPt_0]
      have hz : t + t = 0 := char2_add_self _
      calc (1 : F) = 1 + (t + t) := by rw [hz, add_zero]
        _ = (1 + t) * 1 + t * 1 := by ring
    · change liftPt pj 1 = (1 + t) * liftPt p1 1 + t * liftPt p2 1
      rw [liftPt_1, liftPt_1, liftPt_1]
      exact hx_eq.symm
    · change liftPt pj 2 = (1 + t) * liftPt p1 2 + t * liftPt p2 2
      rw [liftPt_2, liftPt_2, liftPt_2, hy1, hy2, hyj]
      have hz : t * c + t * c = 0 := char2_add_self _
      calc c + m * pj.1 = c + (t * c + t * c) + m * ((1 + t) * p1.1 + t * p2.1) := by
            rw [hz, add_zero, hx_eq]
        _ = (1 + t) * (c + m * p1.1) + t * (c + m * p2.1) := by ring

lemma span_three_noncollinear_eq_top {p1 p2 p3 : F × F} {d : Option F} {c : F}
    (hne : p1 ≠ p2)
    (h1 : lineVal d p1 = c) (h2 : lineVal d p2 = c) (h3 : lineVal d p3 ≠ c) :
    Submodule.span F ({liftPt p1, liftPt p2, liftPt p3} : Set (Fin 3 → F)) = ⊤ := by
  let f : Fin 3 → (Fin 3 → F) := ![liftPt p1, liftPt p2, liftPt p3]
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hphi : lineFunc d c (∑ i : Fin 3, g i • f i) = 0 := by rw [hg, map_zero]
    rw [map_sum] at hphi
    simp only [Fin.sum_univ_three, map_smul, smul_eq_mul, f, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hphi
    rw [(lineFunc_liftPt_eq_zero d c p1).mpr h1,
        (lineFunc_liftPt_eq_zero d c p2).mpr h2, mul_zero, mul_zero, zero_add, zero_add] at hphi
    have hp3_nz : lineFunc d c (liftPt p3) ≠ 0 := fun h =>
      h3 ((lineFunc_liftPt_eq_zero d c p3).mp h)
    have hg2 : g 2 = 0 := (mul_eq_zero.mp hphi).resolve_right hp3_nz
    simp only [Fin.sum_univ_three, f, hg2, zero_smul, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have h0 : g 0 + g 1 = 0 := by
      have := congrFun hg 0
      simpa [liftPt_0] using this
    have hg01 : g 0 = g 1 := (char2_eq_iff_add_zero (g 0) (g 1)).mpr h0
    have hg0 : g 0 = 0 := by
      by_contra h0ne
      have hx : p1.1 = p2.1 := by
        have := congrFun hg 1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, liftPt_1, hg01] at this
        have hmul : g 1 * (p1.1 + p2.1) = 0 := by calc g 1 * (p1.1 + p2.1) = g 1 * p1.1 + g 1 * p2.1 := by ring
          _ = 0 := this
        have h1ne : g 1 ≠ 0 := by rw [← hg01]; exact h0ne
        exact (char2_eq_iff_add_zero _ _).mpr ((mul_eq_zero.mp hmul).resolve_left h1ne)
      have hy : p1.2 = p2.2 := by
        have := congrFun hg 2
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, liftPt_2, hg01] at this
        have hmul : g 1 * (p1.2 + p2.2) = 0 := by calc g 1 * (p1.2 + p2.2) = g 1 * p1.2 + g 1 * p2.2 := by ring
          _ = 0 := this
        have h1ne : g 1 ≠ 0 := by rw [← hg01]; exact h0ne
        exact (char2_eq_iff_add_zero _ _).mpr ((mul_eq_zero.mp hmul).resolve_left h1ne)
      exact hne (Prod.ext hx hy)
    intro i; fin_cases i
    · exact hg0
    · change g 1 = 0; rw [← hg01]; exact hg0
    · exact hg2
  have hrange : Set.range f = {liftPt p1, liftPt p2, liftPt p3} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp [f]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hrange]
  have hcard : Module.finrank F (Fin 3 → F) = Fintype.card (Fin 3) := by simp
  have hspan := (basisOfLinearIndependentOfCardEqFinrank hli hcard.symm).span_eq
  simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using hspan

end FieldGeometry

end PEqualNP.Outside.L_lib_1263_aux

open scoped Classical in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.L_lib_1263 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ s : Nat, 1 ≤ s →
  let rootQ := 2^s
  let q := rootQ*rootQ
  let n := q*q-1
  ∃ H : Fin n → Fin n → Prop, Symmetric H ∧ (∀ i, ¬ H i i) ∧
  (∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card=q) ∧
  let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
    (∀ x j, (∀ i ∈ x, H i j) → g x j=true) ∧ (∀ x j, j ∈ x → g x j=false)
  let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
      ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
             (C.wires input).getD (tap j).val false = g x j
  let runs := fun (g : Finset (Fin n) → Fin n → Bool) =>
    Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j=true ∧ g v j=false)
  (∀ g, fits g → runs g 3 Finset.univ ∧ ∀ C, computes C g → 2 ≤ PEqualNP.NotBracket.notCount C) ∧
  (∃ g, fits g ∧ (∀ x y, x ⊆ y → ∀ j, g y j=true → g x j=true) ∧
    ¬ runs g 4 Finset.univ ∧ ∃ C, computes C g ∧ PEqualNP.NotBracket.notCount C = 2 ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ 12*(q+1)*(n+1)) ∧
  (∀ A : Finset (Fin n), (∀ i ∈ A, ∀ j ∈ A, ¬ H i j) → A.card ≤ (rootQ-1)*(q+1)) ∧
  ∀ (k : Nat) (color : Fin n → Fin k), (∀ i j, H i j → color i ≠ color j) →
    let g := fun (x : Finset (Fin n)) (j : Fin n) => decide (∀ i ∈ x, color i ≠ color j)
    rootQ+1 ≤ k ∧ runs g (rootQ+1) Finset.univ ∧
    ∀ C, computes C g → s+1 ≤ PEqualNP.NotBracket.notCount C) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
    PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
    PEqualNP.Outside.L_lib_1263_aux in
  intro s hs
  dsimp only
  set rootQ := 2 ^ s with hrootQ_def
  set q := rootQ * rootQ with hq_def
  set n := q * q - 1 with hn_def
  have h2s_ne : 2 * s ≠ 0 := by omega
  have hrootQ_ge2 : 2 ≤ rootQ := by
    have : 2 ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
    simpa [hrootQ_def] using this
  have hq_ge4 : 4 ≤ q := by nlinarith
  have hn_pos : 1 ≤ n := by
    have : 16 ≤ q * q := by nlinarith
    omega
  have hn_add1 : n + 1 = q * q := by
    have : 1 ≤ q * q := by nlinarith
    omega

  let F := GaloisField 2 (2 * s)
  letI : Field F := inferInstanceAs (Field (GaloisField 2 (2 * s)))
  letI : Fintype F := Fintype.ofFinite F
  letI : CharP F 2 := inferInstanceAs (CharP (GaloisField 2 (2 * s)) 2)
  letI : DecidableEq F := Classical.decEq F
  have hcardF : Fintype.card F = q := by
    have hnat : Nat.card F = 2 ^ (2 * s) := GaloisField.card 2 (2 * s) h2s_ne
    rw [Nat.card_eq_fintype_card] at hnat
    rw [hnat, hq_def, hrootQ_def, ← pow_add, show s + s = 2 * s by omega]
  let V := {p : F × F // p ≠ (0, 0)}
  have hcardV : Fintype.card V = n := by
    have hcompl : Fintype.card V = Fintype.card (F × F) - Fintype.card {p : F × F // p = (0, 0)} := by
      simpa [V] using Fintype.card_subtype_compl (fun p : F × F => p = (0, 0))
    have hsing : Fintype.card {p : F × F // p = (0, 0)} = 1 := Fintype.card_unique
    rw [hcompl, Fintype.card_prod, hcardF, hsing]
  let e : Fin n ≃ V := (Fintype.equivFinOfCardEq hcardV).symm
  let pt : Fin n → F × F := fun i => (e i).val
  have hpt_ne : ∀ i : Fin n, pt i ≠ (0, 0) := fun i => (e i).property
  have hpt_inj : Function.Injective pt := fun i j h => e.injective (Subtype.ext h)
  let H : Fin n → Fin n → Prop := fun i j => det2 (pt i) (pt j) = 1

  have hH_symm : Symmetric H := fun i j hij => by
    change det2 (pt j) (pt i) = 1
    rw [det2_symm]; exact hij
  have hH_irrefl : ∀ i, ¬ H i i := fun i hi => by
    change det2 (pt i) (pt i) = 1 at hi
    rw [det2_self] at hi
    exact zero_ne_one hi
  have hH_deg : ∀ i : Fin n, ((Finset.univ : Finset (Fin n)).filter (fun j => H i j)).card = q := by
    intro i
    rw [← hcardF, ← card_det2_eq_one (pt i) (hpt_ne i)]
    refine Finset.card_bij (fun j _ => pt j) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, hj.2⟩
    · intro j1 _ j2 _ h; exact hpt_inj h
    · intro r hr
      rw [Finset.mem_filter] at hr
      have hr_ne : r ≠ (0, 0) := by
        intro h0; rw [h0] at hr; simp [det2] at hr
      refine ⟨e.symm ⟨r, hr_ne⟩, ?_, by simp [pt]⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [H, pt, Equiv.apply_symm_apply]
      exact hr.2

  have hruns_eq : ∀ g, Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false) = runsG g :=
    fun _ => rfl

  have hPart1 : ∀ g : Finset (Fin n) → Fin n → Bool,
      ((∀ x j, (∀ i ∈ x, H i j) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)) →
      runsG g 3 Finset.univ ∧
      ∀ C : Circuit, (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
        ∃ tap : Fin n → Fin (n + 2 + C.size), ∀ x j,
          (C.wires (setInput x)).getD (tap j).val false = g x j) →
        2 ≤ notCount C := by
    intro g ⟨hfit1, hfit2⟩
    let v1 : Fin n := e.symm ⟨((1 : F), 0), fun h => one_ne_zero (congrArg Prod.fst h)⟩
    let v2 : Fin n := e.symm ⟨(0, (1 : F)), fun h => one_ne_zero (congrArg Prod.snd h)⟩
    let v3 : Fin n := e.symm ⟨((1 : F), (1 : F)), fun h => one_ne_zero (congrArg Prod.fst h)⟩
    have hv12 : H v1 v2 := by simp [H, det2, pt, v1, v2]
    have hv13 : H v1 v3 := by simp [H, det2, pt, v1, v3]
    have hv23 : H v2 v3 := by simp [H, det2, pt, v2, v3]
    have hr1 : runsG g 1 {v1} :=
      ⟨∅, {v1}, v1, trivial, Finset.empty_subset _, Finset.Subset.rfl,
       hfit1 ∅ v1 (by simp), hfit2 {v1} v1 (by simp)⟩
    have hr2 : runsG g 2 {v1, v2} :=
      ⟨{v1}, {v1, v2}, v2, hr1, by simp, Finset.Subset.rfl,
       hfit1 {v1} v2 (by simp [hv12]), hfit2 {v1, v2} v2 (by simp)⟩
    have hr3 : runsG g 3 Finset.univ :=
      ⟨{v1, v2}, {v1, v2, v3}, v3, hr2, by intro z hz; simp at hz ⊢; tauto,
       Finset.subset_univ _,
       hfit1 {v1, v2} v3 (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
       hfit2 {v1, v2, v3} v3 (by simp)⟩
    refine ⟨hr3, ?_⟩
    intro C ⟨hfitC, hrbC, _, tap, htap⟩
    have hpow := runsG_markov_bound g C hfitC hrbC tap htap 3 Finset.univ hr3
    by_contra hlt
    have hle1 : notCount C ≤ 1 := by omega
    have : 2 ^ notCount C ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hle1
    omega

  have hPart3 : ∀ A : Finset (Fin n), (∀ i ∈ A, ∀ j ∈ A, ¬ H i j) → A.card ≤ (rootQ - 1) * (q + 1) := by
    intro A hindep
    set h := A.card with hh_def
    by_cases hh0 : h = 0
    · omega
    let B := Finset.univ \ A
    have hB_card : B.card = n - h := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hh_def]
    let dA : Fin n → ℕ := fun w => (A.filter (fun u => H u w)).card

    have hsum1 : ∑ w ∈ B, dA w = q * h := by
      have h1 : ∑ w ∈ B, dA w = ∑ u ∈ A, ((Finset.univ : Finset (Fin n)).filter (fun w => H u w)).card := by
        have hinc : ∀ u ∈ A, (B.filter (fun w => H u w)).card =
            ((Finset.univ : Finset (Fin n)).filter (fun w => H u w)).card := by
          intro u hu
          congr 1; ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, B, Finset.mem_sdiff]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun hwA => hindep u hu w hwA h, h⟩⟩
        calc ∑ w ∈ B, dA w
            = ∑ w ∈ B, ∑ u ∈ A, if H u w then 1 else 0 := by
                apply Finset.sum_congr rfl; intro w _; exact Finset.card_filter _ _
          _ = ∑ u ∈ A, ∑ w ∈ B, if H u w then 1 else 0 := Finset.sum_comm
          _ = ∑ u ∈ A, (B.filter (fun w => H u w)).card := by
                apply Finset.sum_congr rfl; intro u _; exact (Finset.card_filter _ _).symm
          _ = ∑ u ∈ A, ((Finset.univ : Finset (Fin n)).filter (fun w => H u w)).card :=
                Finset.sum_congr rfl hinc
      rw [h1]
      have : ∑ u ∈ A, ((Finset.univ : Finset (Fin n)).filter (fun w => H u w)).card = ∑ _u ∈ A, q :=
        Finset.sum_congr rfl fun u _ => hH_deg u
      rw [this, Finset.sum_const, smul_eq_mul, mul_comm, hh_def]

    let cDir : Option F → ℕ := fun d => (A.filter (fun u => projDir (pt u) = d)).card
    have hsum_c : ∑ d : Option F, cDir d = h := by
      have hfib := Finset.card_eq_sum_card_fiberwise (f := fun u : Fin n => projDir (pt u))
        (s := A) (t := (Finset.univ : Finset (Option F))) (fun _ _ => Finset.mem_univ _)
      simpa [cDir, hh_def] using hfib.symm
    have hcs1 : h ^ 2 ≤ (q + 1) * ∑ d : Option F, cDir d ^ 2 := by
      have hcardDir : (Finset.univ : Finset (Option F)).card = q + 1 := by
        simp [hcardF]
      have hcs := nat_cauchy_schwarz (Finset.univ : Finset (Option F)) cDir
      rw [hsum_c, hcardDir] at hcs
      exact hcs

    let NP := (A ×ˢ A).filter (fun p => det2 (pt p.1) (pt p.2) ≠ 0)
    let PP := (A ×ˢ A).filter (fun p => det2 (pt p.1) (pt p.2) = 0)
    have hNP_PP : NP.card + PP.card = h ^ 2 := by
      have hdisj : Disjoint NP PP := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [NP, PP, Finset.mem_filter] at hp1 hp2
        exact hp1.2 hp2.2
      have hunion : NP ∪ PP = A ×ˢ A := by
        ext p
        simp only [NP, PP, Finset.mem_union, Finset.mem_filter]
        tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_product, ← sq, ← hh_def]
    have hPP_card : PP.card = ∑ d : Option F, cDir d ^ 2 := by
      have hfib : PP.card = ∑ d : Option F, (PP.filter (fun p => projDir (pt p.1) = d)).card :=
        Finset.card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => projDir (pt p.1))
          (s := PP) (t := (Finset.univ : Finset (Option F))) (fun _ _ => Finset.mem_univ _)
      rw [hfib]
      apply Finset.sum_congr rfl
      intro d _
      have heq : PP.filter (fun p => projDir (pt p.1) = d) =
          (A.filter (fun u => projDir (pt u) = d)) ×ˢ (A.filter (fun u => projDir (pt u) = d)) := by
        ext ⟨u, v⟩
        simp only [PP, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨⟨⟨hu, hv⟩, hdet⟩, hdu⟩
          have heqd := (projDir_eq_iff_det2_zero (hpt_ne u) (hpt_ne v)).mpr hdet
          exact ⟨⟨hu, hdu⟩, ⟨hv, heqd.symm.trans hdu⟩⟩
        · rintro ⟨⟨hu, hdu⟩, ⟨hv, hdv⟩⟩
          have hdet := (projDir_eq_iff_det2_zero (hpt_ne u) (hpt_ne v)).mp (hdu.trans hdv.symm)
          exact ⟨⟨⟨hu, hv⟩, hdet⟩, hdu⟩
      rw [heq, Finset.card_product, ← sq]
    have hsum_pairs : ∑ w ∈ B, dA w * (dA w - 1) = NP.card := by

      have hstep : ∀ w ∈ B, dA w * (dA w - 1) =
          (((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w))).card := by
        intro w _
        let Sw := A.filter (fun u => H u w)
        let D := Sw.image (fun u => (u, u))
        have hD_card : D.card = Sw.card :=
          Finset.card_image_of_injective Sw (fun a b h => (Prod.mk.inj h).1)
        have hdisj : Disjoint ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)) D := by
          rw [Finset.disjoint_left]
          intro ⟨u, v⟩ h1 h2
          simp only [Finset.mem_filter, D, Finset.mem_image] at h1 h2
          obtain ⟨a, _, ha⟩ := h2
          exact h1.2.1 ((Prod.mk.inj ha).1.symm.trans (Prod.mk.inj ha).2)
        have hunion : ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)) ∪ D = Sw ×ˢ Sw := by
          ext ⟨u, v⟩
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Sw, D, Finset.mem_image]
          constructor
          · rintro (⟨⟨hu, hv⟩, _, huw, hvw⟩ | ⟨a, ⟨ha, haw⟩, heq⟩)
            · exact ⟨⟨hu, huw⟩, ⟨hv, hvw⟩⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨⟨ha, haw⟩, ⟨ha, haw⟩⟩
          · rintro ⟨⟨hu, huw⟩, ⟨hv, hvw⟩⟩
            by_cases huv : u = v
            · subst huv; exact Or.inr ⟨u, ⟨hu, huw⟩, rfl⟩
            · exact Or.inl ⟨⟨hu, hv⟩, huv, huw, hvw⟩
        have hcard_eq : ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)).card + Sw.card =
            Sw.card * Sw.card := by
          calc ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)).card + Sw.card
              = ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)).card + D.card := by rw [hD_card]
            _ = (((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)) ∪ D).card :=
                (Finset.card_union_of_disjoint hdisj).symm
            _ = (Sw ×ˢ Sw).card := by rw [hunion]
            _ = Sw.card * Sw.card := Finset.card_product Sw Sw
        have hSw_eq : Sw.card = dA w := rfl
        rw [hSw_eq] at hcard_eq
        cases hdw : dA w with
        | zero => rw [hdw] at hcard_eq; omega
        | succ m =>
          rw [hdw] at hcard_eq
          simp only [Nat.succ_sub_one]
          have : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
          omega
      rw [Finset.sum_congr rfl hstep]
      calc ∑ w ∈ B, ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w)).card
          = ∑ w ∈ B, ∑ p ∈ A ×ˢ A, if p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w then 1 else 0 := by
              apply Finset.sum_congr rfl; intro w _; exact Finset.card_filter _ _
        _ = ∑ p ∈ A ×ˢ A, ∑ w ∈ B, if p.1 ≠ p.2 ∧ H p.1 w ∧ H p.2 w then 1 else 0 := Finset.sum_comm
        _ = ∑ p ∈ A ×ˢ A, if det2 (pt p.1) (pt p.2) ≠ 0 then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro ⟨u, v⟩ huv
              simp only [Finset.mem_product] at huv
              by_cases hdet : det2 (pt u) (pt v) ≠ 0
              · rw [if_pos hdet]
                have hne_uv : u ≠ v := by
                  intro heq; subst heq; exact hdet (det2_self (pt u))
                have ⟨hw_ne, hpw, hrw⟩ := common_nbr_exists hdet
                let w_pt := (((pt u).1 + (pt v).1) * (det2 (pt u) (pt v))⁻¹,
                             ((pt u).2 + (pt v).2) * (det2 (pt u) (pt v))⁻¹)
                let w0 : Fin n := e.symm ⟨w_pt, hw_ne⟩
                have hw0_pt : pt w0 = w_pt := by simp [pt, w0]
                have hw0_B : w0 ∈ B := by
                  simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and]
                  intro hwA
                  exact hindep u huv.1 w0 hwA (by simp [H, hw0_pt, w_pt, hpw])
                rw [Finset.sum_eq_single w0]
                · simp [hne_uv, H, hw0_pt, w_pt, hpw, hrw]
                · intro w _ hww0
                  rw [if_neg]
                  rintro ⟨_, huw, hvw⟩
                  have hpt_eq := common_nbr_unique hdet huw hvw
                  apply hww0
                  apply hpt_inj
                  rw [hw0_pt]; exact hpt_eq
                · intro hnot; exact (hnot hw0_B).elim
              · push_neg at hdet
                rw [if_neg (not_not.mpr hdet)]
                apply Finset.sum_eq_zero
                intro w _
                rw [if_neg]
                rintro ⟨hne_uv, huw, hvw⟩
                exact no_common_nbr_of_det2_zero (hpt_ne u) (hpt_ne v)
                  (fun h => hne_uv (hpt_inj h)) hdet huw hvw
        _ = NP.card := (Finset.card_filter _ _).symm
    have hsum2 : ∑ w ∈ B, dA w ^ 2 = q * h + NP.card := by
      have hsq : ∀ w ∈ B, dA w ^ 2 = dA w + dA w * (dA w - 1) := by
        intro w _
        cases hdw : dA w with
        | zero => simp
        | succ m => simp only [Nat.succ_sub_one]; ring
      rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, hsum1, hsum_pairs]

    have hcs2 : (q * h) ^ 2 ≤ (n - h) * ∑ w ∈ B, dA w ^ 2 := by
      have hcs := nat_cauchy_schwarz B dA
      rw [hsum1, hB_card] at hcs
      exact hcs
    have hbound_sum2 : (q + 1) * (∑ w ∈ B, dA w ^ 2) ≤ (q + 1) * (q * h) + q * h ^ 2 := by
      rw [hsum2, mul_add]
      have hNP_le : (q + 1) * NP.card ≤ q * h ^ 2 := by
        have h1 : (q + 1) * NP.card + (q + 1) * PP.card = (q + 1) * h ^ 2 := by
          rw [← mul_add, hNP_PP]
        rw [hPP_card] at h1
        have h2 : (q + 1) * h ^ 2 = q * h ^ 2 + h ^ 2 := by ring
        omega
      omega
    have hmul_cs2 : (q + 1) * (q * h) ^ 2 ≤ (n - h) * ((q + 1) * (q * h) + q * h ^ 2) := by
      calc (q + 1) * (q * h) ^ 2
          ≤ (q + 1) * ((n - h) * ∑ w ∈ B, dA w ^ 2) := Nat.mul_le_mul_left (q + 1) hcs2
        _ = (n - h) * ((q + 1) * ∑ w ∈ B, dA w ^ 2) := by ring
        _ ≤ (n - h) * ((q + 1) * (q * h) + q * h ^ 2) := Nat.mul_le_mul_left (n - h) hbound_sum2
    have hle_n : h ≤ n := by
      have := Finset.card_le_univ A
      simpa [hh_def] using this
    have hqh_pos : 0 < q * h := Nat.mul_pos (by omega) (by omega)
    have hfactor : (q + 1) * (q * h) ^ 2 = (q * h) * (q * h * (q + 1)) := by ring
    have hfactor2 : (n - h) * ((q + 1) * (q * h) + q * h ^ 2) = (q * h) * ((n - h) * (q + 1 + h)) := by ring
    rw [hfactor, hfactor2] at hmul_cs2
    have hcancel : q * h * (q + 1) ≤ (n - h) * (q + 1 + h) := Nat.le_of_mul_le_mul_left hmul_cs2 hqh_pos
    have hcancelZ : (q : ℤ) * h * (q + 1) ≤ ((n : ℤ) - h) * (q + 1 + h) := by
      have := Int.ofNat_le.mpr hcancel
      push_cast [Int.ofNat_sub hle_n] at this
      exact this
    have hnZ : (n : ℤ) = (q : ℤ) * q - 1 := by
      have h1 : (n : ℤ) + 1 = (q : ℤ) * q := by exact_mod_cast hn_add1
      linarith only [h1]
    have hsqZ : ((h : ℤ) + q + 1) ^ 2 ≤ ((rootQ : ℤ) * (q + 1)) ^ 2 := by
      have hqZ : (q : ℤ) = (rootQ : ℤ) * rootQ := by exact_mod_cast hq_def
      rw [hnZ] at hcancelZ
      have hident : ((rootQ : ℤ) * (q + 1)) ^ 2 - ((h : ℤ) + q + 1) ^ 2 =
          ((q : ℤ) * q - 1 - h) * (q + 1 + h) - (q : ℤ) * h * (q + 1) := by
        calc ((rootQ : ℤ) * (q + 1)) ^ 2 - ((h : ℤ) + q + 1) ^ 2
            = ((rootQ : ℤ) * rootQ) * (q + 1) ^ 2 - ((h : ℤ) + q + 1) ^ 2 := by ring
          _ = (q : ℤ) * (q + 1) ^ 2 - ((h : ℤ) + q + 1) ^ 2 := by rw [← hqZ]
          _ = ((q : ℤ) * q - 1 - h) * (q + 1 + h) - (q : ℤ) * h * (q + 1) := by ring
      linarith only [hcancelZ, hident]
    have hsqN : (h + q + 1) ^ 2 ≤ (rootQ * (q + 1)) ^ 2 := by exact_mod_cast hsqZ
    have hlinN : h + q + 1 ≤ rootQ * (q + 1) := by
      by_contra hgt
      have hgt' : rootQ * (q + 1) + 1 ≤ h + q + 1 := by omega
      have hmul : (rootQ * (q + 1) + 1) * (rootQ * (q + 1) + 1) ≤ (h + q + 1) * (h + q + 1) :=
        Nat.mul_le_mul hgt' hgt'
      rw [sq, sq] at hsqN
      have hexp : (rootQ * (q + 1) + 1) * (rootQ * (q + 1) + 1) =
          rootQ * (q + 1) * (rootQ * (q + 1)) + 2 * (rootQ * (q + 1)) + 1 := by ring
      omega
    have hsub : (rootQ - 1) * (q + 1) + (q + 1) = rootQ * (q + 1) := by
      have : (rootQ - 1) + 1 = rootQ := by omega
      calc (rootQ - 1) * (q + 1) + (q + 1) = ((rootQ - 1) + 1) * (q + 1) := by ring
        _ = rootQ * (q + 1) := by rw [this]
    omega

  have hPart4 : ∀ (k : ℕ) (color : Fin n → Fin k), (∀ i j, H i j → color i ≠ color j) →
      let g := fun (x : Finset (Fin n)) (j : Fin n) => decide (∀ i ∈ x, color i ≠ color j)
      rootQ + 1 ≤ k ∧ runsG g (rootQ + 1) Finset.univ ∧
      ∀ C : Circuit, (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
        ∃ tap : Fin n → Fin (n + 2 + C.size), ∀ x j,
          (C.wires (setInput x)).getD (tap j).val false = g x j) →
        s + 1 ≤ notCount C := by
    intro k color hproper
    dsimp only
    let g := fun (x : Finset (Fin n)) (j : Fin n) => decide (∀ i ∈ x, color i ≠ color j)
    let U : Finset (Fin k) := Finset.univ.image color
    have hU_ge : rootQ + 1 ≤ U.card := by
      have hsum_fib : n = ∑ c ∈ U, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card := by
        have := Finset.card_eq_sum_card_fiberwise (f := color)
          (s := (Finset.univ : Finset (Fin n))) (t := U)
          (fun i _ => Finset.mem_image_of_mem color (Finset.mem_univ i))
        simpa using this
      have hle_sum : n ≤ U.card * ((rootQ - 1) * (q + 1)) := by
        rw [hsum_fib]
        calc ∑ c ∈ U, ((Finset.univ : Finset (Fin n)).filter (fun i => color i = c)).card
            ≤ ∑ _c ∈ U, (rootQ - 1) * (q + 1) := by
                apply Finset.sum_le_sum
                intro c _
                apply hPart3
                intro i hi j hj hij
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
                exact hproper i j hij (hi.trans hj.symm)
          _ = U.card * ((rootQ - 1) * (q + 1)) := by rw [Finset.sum_const, smul_eq_mul]
      have hn_fact : n = (rootQ + 1) * ((rootQ - 1) * (q + 1)) := by
        have h1 : (rootQ + 1) * (rootQ - 1) = q - 1 := by
          have h2 : (rootQ + 1) * (rootQ - 1) + 1 = rootQ * rootQ := by
            have : (rootQ - 1) + 1 = rootQ := by omega
            zify [show 1 ≤ rootQ by omega]; ring
          omega
        have h3 : (q - 1) * (q + 1) = n := by
          have : (q - 1) * (q + 1) + 1 = q * q := by
            zify [show 1 ≤ q by omega]; ring
          omega
        calc n = (q - 1) * (q + 1) := h3.symm
          _ = (rootQ + 1) * (rootQ - 1) * (q + 1) := by rw [h1]
          _ = (rootQ + 1) * ((rootQ - 1) * (q + 1)) := by ring
      rw [hn_fact] at hle_sum
      have hpos : 0 < (rootQ - 1) * (q + 1) := Nat.mul_pos (by omega) (by omega)
      exact Nat.le_of_mul_le_mul_right hle_sum hpos
    have hk_ge : rootQ + 1 ≤ k := by
      have : U.card ≤ k := by simpa using Finset.card_le_univ U
      omega
    obtain ⟨U0, hU0_sub, hU0_card⟩ := Finset.exists_subset_card_eq hU_ge
    let cs : List (Fin k) := U0.toList
    have hcs_len : cs.length = rootQ + 1 := by simp [cs, hU0_card]
    have hcs_nd : cs.Nodup := Finset.nodup_toList U0
    have hcs_mem : ∀ c ∈ cs, c ∈ U := fun c hc => hU0_sub (Finset.mem_toList.mp hc)
    have hrep_ex : ∀ c : Fin k, c ∈ U → ∃ v : Fin n, color v = c := fun c hc => by
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hc; exact ⟨v, hv⟩
    let rep : Fin k → Fin n := fun c =>
      if hc : c ∈ U then Classical.choose (hrep_ex c hc) else ⟨0, hn_pos⟩
    have hrep_color : ∀ c ∈ U, color (rep c) = c := fun c hc => by
      simp only [rep, dif_pos hc]; exact Classical.choose_spec (hrep_ex c hc)
    have hruns_list : ∀ l : List (Fin k), l.Nodup → (∀ c ∈ l, c ∈ U) →
        runsG g l.length (l.map rep).toFinset := by
      intro l
      induction l with
      | nil => intro _ _; trivial
      | cons c l' ih =>
        intro hnd hmem
        have ⟨hc_not, hnd'⟩ := List.nodup_cons.mp hnd
        have hcU : c ∈ U := hmem c (List.mem_cons_self ..)
        have hl'U : ∀ c' ∈ l', c' ∈ U := fun c' hc' => hmem c' (List.mem_cons_of_mem c hc')
        have hprev := ih hnd' hl'U
        simp only [List.length_cons, List.map_cons, List.toFinset_cons]
        refine ⟨(l'.map rep).toFinset, insert (rep c) (l'.map rep).toFinset, rep c,
          hprev, Finset.subset_insert _ _, Finset.Subset.rfl, ?_, ?_⟩
        · simp only [g, decide_eq_true_eq]
          intro i hi
          rw [List.mem_toFinset, List.mem_map] at hi
          obtain ⟨c', hc', rfl⟩ := hi
          rw [hrep_color c' (hl'U c' hc'), hrep_color c hcU]
          intro heq; subst heq; exact hc_not hc'
        · simp only [g, decide_eq_false_iff_not, not_forall, not_not]
          exact ⟨rep c, Finset.mem_insert_self _ _, rfl⟩
    have hruns_q : runsG g (rootQ + 1) Finset.univ := by
      rw [← hcs_len]
      exact runsG_mono (Finset.subset_univ _) (hruns_list cs hcs_nd hcs_mem)
    refine ⟨hk_ge, hruns_q, ?_⟩
    intro C ⟨hfitC, hrbC, _, tap, htap⟩
    have hpow := runsG_markov_bound g C hfitC hrbC tap htap (rootQ + 1) Finset.univ hruns_q
    by_contra hlt
    have hles : notCount C ≤ s := by omega
    have hpow_le : 2 ^ notCount C ≤ rootQ := by
      rw [hrootQ_def]; exact Nat.pow_le_pow_right (by omega) hles
    omega

  have hPart2 : ∃ g : Finset (Fin n) → Fin n → Bool,
      ((∀ x j, (∀ i ∈ x, H i j) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)) ∧
      (∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true) ∧
      ¬ runsG g 4 Finset.univ ∧
      ∃ C : Circuit,
        (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
          ∃ tap : Fin n → Fin (n + 2 + C.size), ∀ x j,
            (C.wires (setInput x)).getD (tap j).val false = g x j) ∧
        notCount C = 2 ∧ C.size - notCount C ≤ 12 * (q + 1) * (n + 1) := by
    let spanOf : Finset (Fin n) → Submodule F (Fin 3 → F) :=
      fun x => Submodule.span F ((fun i : Fin n => liftPt (pt i)) '' (x : Set (Fin n)))
    let g : Finset (Fin n) → Fin n → Bool := fun x j => decide (liftPt (pt j) ∉ spanOf x)
    have hg_fits : (∀ x j, (∀ i ∈ x, H i j) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false) := by
      constructor
      · intro x j hadj
        simp only [g, decide_eq_true_eq]
        intro hmem
        have hker : spanOf x ≤ LinearMap.ker (nbrFunc (pt j)) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, hi, rfl⟩
          exact nbrFunc_adj (hadj i hi)
        have h0 : nbrFunc (pt j) (liftPt (pt j)) = 0 := hker hmem
        rw [nbrFunc_self] at h0
        exact one_ne_zero h0
      · intro x j hj
        simp only [g, decide_eq_false_iff_not, not_not]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
    have hg_anti : ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true := by
      intro x y hxy j hy
      simp only [g, decide_eq_true_eq] at hy ⊢
      have hsub : spanOf x ≤ spanOf y := Submodule.span_mono (Set.image_mono (by exact_mod_cast hxy))
      exact fun hx => hy (hsub hx)
    have hno_runs4 : ¬ runsG g 4 Finset.univ := by
      have hrank : ∀ m x, runsG g m x → m ≤ Module.finrank F (spanOf x) := by
        intro m
        induction m with
        | zero => intro _ _; exact Nat.zero_le _
        | succ m ih =>
          intro x ⟨u, v, j, hpu, huv, hvx, hgu, hgv⟩
          have hm := ih u hpu
          have hsub_uv : spanOf u ≤ spanOf v := Submodule.span_mono (Set.image_mono (by exact_mod_cast huv))
          have hsub_vx : spanOf v ≤ spanOf x := Submodule.span_mono (Set.image_mono (by exact_mod_cast hvx))
          simp only [g, decide_eq_true_eq] at hgu
          simp only [g, decide_eq_false_iff_not, not_not] at hgv
          have hlt_uv : spanOf u < spanOf v := lt_of_le_of_ne hsub_uv (fun heq => hgu (heq ▸ hgv))
          have hfr_lt : Module.finrank F (spanOf u) < Module.finrank F (spanOf v) :=
            Submodule.finrank_lt_finrank_of_lt hlt_uv
          have hfr_le : Module.finrank F (spanOf v) ≤ Module.finrank F (spanOf x) :=
            Submodule.finrank_mono hsub_vx
          omega
      intro hr4
      have h4 := hrank 4 Finset.univ hr4
      have hle3 : Module.finrank F (spanOf Finset.univ) ≤ 3 := by
        calc Module.finrank F (spanOf Finset.univ)
            ≤ Module.finrank F (Fin 3 → F) := Submodule.finrank_le _
          _ = 3 := by simp
      omega

    let rank3 : Finset (Fin n) → Prop :=
      fun x => ∀ d : Option F, ∀ c : F, ∃ i ∈ x, lineVal d (pt i) ≠ c
    have hg_char : ∀ (x : Finset (Fin n)) (j : Fin n),
        g x j = (decide (x = ∅) ||
          (decide (x.Nonempty ∧ ¬ (2 ≤ x.card)) && decide (∃ i : Fin n, i ≠ j ∧ i ∈ x)) ||
          (decide (2 ≤ x.card ∧ ¬ rank3 x) &&
            decide (∀ d : Option F, ∃ i ∈ x, lineVal d (pt i) ≠ lineVal d (pt j)))) := by
      intro x j
      by_cases hx0 : x = ∅
      · subst hx0
        have hnot : liftPt (pt j) ∉ spanOf ∅ := by
          simp only [spanOf, Finset.coe_empty, Set.image_empty, Submodule.span_empty,
            Submodule.mem_bot]
          intro h0
          have := congrFun h0 0
          simp [liftPt] at this
        simp [g, hnot]
      · have hxne : x.Nonempty := Finset.nonempty_iff_ne_empty.mpr hx0
        by_cases hx2 : 2 ≤ x.card
        · by_cases hr3 : rank3 x
          ·
            have htop : spanOf x = ⊤ := by
              obtain ⟨p1, hp1⟩ := hxne
              obtain ⟨p2, hp2, hp2_ne⟩ := hr3 none (pt p1).1
              have h12 : p1 ≠ p2 := fun h => hp2_ne (by simp [h, lineVal])
              obtain ⟨⟨d0, c0⟩, ⟨hd1, hd2⟩, _⟩ := unique_line_two_pts (fun h => h12 (hpt_inj h))
              obtain ⟨p3, hp3, hd3⟩ := hr3 d0 c0
              have hsub3 : Submodule.span F ({liftPt (pt p1), liftPt (pt p2), liftPt (pt p3)} : Set (Fin 3 → F)) ≤ spanOf x := by
                rw [Submodule.span_le]
                intro v hv
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
                rcases hv with rfl | rfl | rfl
                · exact Submodule.subset_span ⟨p1, hp1, rfl⟩
                · exact Submodule.subset_span ⟨p2, hp2, rfl⟩
                · exact Submodule.subset_span ⟨p3, hp3, rfl⟩
              rw [span_three_noncollinear_eq_top (fun h => h12 (hpt_inj h)) hd1 hd2 hd3] at hsub3
              exact top_unique hsub3
            simp [g, htop, hx0, hx2, hr3]
          ·
            have ⟨d0, c0, hline⟩ : ∃ d0 : Option F, ∃ c0 : F, ∀ i ∈ x, lineVal d0 (pt i) = c0 := by
              unfold rank3 at hr3; push_neg at hr3; exact hr3
            obtain ⟨p1, hp1, p2, hp2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < x.card)
            obtain ⟨dc_u, hdc_u, huniq⟩ := unique_line_two_pts (fun h => h12 (hpt_inj h))
            have hdc0 : (d0, c0) = dc_u := huniq (d0, c0) ⟨hline p1 hp1, hline p2 hp2⟩
            have hmem_iff : liftPt (pt j) ∈ spanOf x ↔ lineVal d0 (pt j) = c0 := by
              constructor
              · intro hmem
                have hker : spanOf x ≤ LinearMap.ker (lineFunc d0 c0) := by
                  rw [Submodule.span_le]
                  rintro _ ⟨i, hi, rfl⟩
                  exact (lineFunc_liftPt_eq_zero d0 c0 (pt i)).mpr (hline i hi)
                exact (lineFunc_liftPt_eq_zero d0 c0 (pt j)).mp (hker hmem)
              · intro hjline
                obtain ⟨t, ht⟩ := liftPt_mem_span_two_on_line (fun h => h12 (hpt_inj h))
                  (hline p1 hp1) (hline p2 hp2) hjline
                rw [ht]
                exact Submodule.add_mem _
                  (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p1, hp1, rfl⟩))
                  (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p2, hp2, rfl⟩))
            have hoff_iff : (∀ d : Option F, ∃ i ∈ x, lineVal d (pt i) ≠ lineVal d (pt j)) ↔
                lineVal d0 (pt j) ≠ c0 := by
              constructor
              · intro hall heq
                obtain ⟨i, hi, hne⟩ := hall d0
                exact hne ((hline i hi).trans heq.symm)
              · intro hne d
                by_contra hnot; push_neg at hnot
                have huniq_d := huniq (d, lineVal d (pt j)) ⟨hnot p1 hp1, hnot p2 hp2⟩
                have heq_dc : (d, lineVal d (pt j)) = (d0, c0) := huniq_d.trans hdc0.symm
                have hd_eq : d = d0 := congrArg Prod.fst heq_dc
                have hc_eq : lineVal d (pt j) = c0 := congrArg Prod.snd heq_dc
                rw [hd_eq] at hc_eq
                exact hne hc_eq
            simp only [g, hx0, hx2, hr3, not_false_eq_true, and_self, decide_false, decide_true,
              Bool.false_or, Bool.false_and, Bool.true_and, not_true_eq_false, and_false]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, hmem_iff, hoff_iff]
        ·
          have hxcard1 : x.card = 1 := by
            have := Finset.Nonempty.card_pos hxne; omega
          obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hxcard1
          have hmem_iff : liftPt (pt j) ∈ spanOf {p} ↔ j = p := by
            constructor
            · intro hmem
              simp only [spanOf, Finset.coe_singleton, Set.image_singleton, Submodule.mem_span_singleton] at hmem
              obtain ⟨c, hc⟩ := hmem
              have hc1 : c = 1 := by
                have := congrFun hc 0
                simpa [liftPt] using this
              rw [hc1, one_smul] at hc
              apply hpt_inj
              apply Prod.ext
              · have := congrFun hc 1; simpa [liftPt] using this.symm
              · have := congrFun hc 2; simpa [liftPt] using this.symm
            · rintro rfl; exact Submodule.subset_span ⟨j, Finset.mem_singleton_self j, rfl⟩
          have hother_iff : (∃ i : Fin n, i ≠ j ∧ i ∈ ({p} : Finset (Fin n))) ↔ j ≠ p := by
            simp [eq_comm]
          simp only [g, hx0, hx2, hxne, not_false_eq_true, and_self, decide_false, decide_true,
            Bool.false_or, Bool.true_and, Bool.false_and, Bool.or_false, false_and]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, hmem_iff, hother_iff]

    let n0 := n + 2
    let cFalse := n
    let cTrue := n + 1
    let inpWs : List ℕ := List.range n
    have hinp_lt : ∀ w ∈ inpWs, w < n0 := fun w hw => by simp [inpWs] at hw; omega

    have ⟨⟨ex1a, hgs1a, hlen1a, hmon1a, hrb1a⟩, hlen_other, hlt_other, hsem_other⟩ :=
      compileExclOr_spec n0 cFalse inpWs [] (by simp [cFalse, n0]) (by simpa using hinp_lt)
    set st1a := compileExclOr n0 cFalse [] inpWs
    have ⟨⟨ex1b, hgs1b, hlen1b, hmon1b, hrb1b⟩, hlt_r1, hsem_r1⟩ :=
      compileOrChain_spec n0 cFalse inpWs st1a.1 (by simp [cFalse, n0]; omega)
        (fun w hw => by have := hinp_lt w hw; omega)
    set st1b := compileOrChain n0 cFalse st1a.1 inpWs
    have ⟨⟨ex1c, hgs1c, hlen1c, hmon1c, hrb1c⟩, hlen_both, hlt_both, hsem_both⟩ :=
      compileZipBin_spec GateOp.and (Or.inl rfl) n0 inpWs st1a.2
        (by simp [inpWs, hlen_other]) st1b.1
        (fun w hw => by have := hinp_lt w hw; omega)
        (fun w hw => by have := hlt_other w hw; rw [hgs1b]; simp; omega)
    set st1c := compileZipBin GateOp.and n0 st1b.1 inpWs st1a.2
    have ⟨⟨ex1d, hgs1d, hlen1d, hmon1d, hrb1d⟩, hlt_r2, hsem_r2⟩ :=
      compileOrChain_spec n0 cFalse st1c.2 st1c.1 (by simp [cFalse, n0]; omega) hlt_both
    set st1d := compileOrChain n0 cFalse st1c.1 st1c.2

    let dirsL : List (Option F) := (Finset.univ : Finset (Option F)).toList
    let offsL : List F := (Finset.univ : Finset F).toList
    have hdirs_len : dirsL.length = q + 1 := by simp [dirsL, hcardF]
    have hoffs_len : offsL.length = q := by simp [offsL, hcardF]
    have hdirs_nd : dirsL.Nodup := Finset.nodup_toList _
    have hoffs_nd : offsL.Nodup := Finset.nodup_toList _
    let dirGroups : Option F → List (List ℕ) := fun d =>
      offsL.map (fun c => ((List.finRange n).filter (fun i => decide (lineVal d (pt i) = c))).map Fin.val)
    let allDirGroups : List (List (List ℕ)) := dirsL.map dirGroups
    have hallDir_sum : ∀ d : Option F, ((dirGroups d).map List.length).sum = n := by
      intro d
      simp only [dirGroups, List.map_map]
      have h1 : (offsL.map ((List.length ∘ fun c => ((List.finRange n).filter (fun i => decide (lineVal d (pt i) = c))).map Fin.val))).sum =
          ∑ c : F, ((Finset.univ : Finset (Fin n)).filter (fun i => lineVal d (pt i) = c)).card := by
        have hnodup : (offsL.map (fun c => ((Finset.univ : Finset (Fin n)).filter (fun i => lineVal d (pt i) = c)).card)).sum =
            ∑ c ∈ (Finset.univ : Finset F), ((Finset.univ : Finset (Fin n)).filter (fun i => lineVal d (pt i) = c)).card := by
          rw [← List.sum_toFinset _ hoffs_nd]
          simp [offsL]
        rw [← hnodup]
        congr 1
        apply List.map_congr_left
        intro c _
        simp only [Function.comp_apply, List.length_map]
        rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))]
        congr 1; ext i; simp
      rw [h1]
      have hfib := Finset.card_eq_sum_card_fiberwise (f := fun i : Fin n => lineVal d (pt i))
        (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset F))
        (fun _ _ => Finset.mem_univ _)
      simpa using hfib.symm
    have hallDir_bound : (allDirGroups.map (fun dg => (dg.map List.length).sum + 3 * dg.length)).sum =
        (q + 1) * (n + 3 * q) := by
      simp only [allDirGroups, List.map_map]
      have hcongr : dirsL.map ((fun dg => (dg.map List.length).sum + 3 * dg.length) ∘ dirGroups) =
          dirsL.map (fun _ => n + 3 * q) := by
        apply List.map_congr_left
        intro d _
        simp only [Function.comp_apply, hallDir_sum d]
        simp [dirGroups, hoffs_len]
      rw [hcongr, List.map_const', List.sum_replicate, smul_eq_mul, hdirs_len]
    have hallDir_lt : ∀ dg ∈ allDirGroups, ∀ xs ∈ dg, ∀ w ∈ xs, w < n0 + st1d.1.length := by
      intro dg hdg xs hxs w hw
      rw [show allDirGroups = dirsL.map dirGroups from rfl, List.mem_map] at hdg
      obtain ⟨d, _, rfl⟩ := hdg
      rw [show dirGroups d = _ from rfl, List.mem_map] at hxs
      obtain ⟨c, _, rfl⟩ := hxs
      rw [List.mem_map] at hw
      obtain ⟨i, _, rfl⟩ := hw
      have hi := i.isLt
      simp only [n0]; omega
    have ⟨⟨ex2, hgs2, hlen2, hmon2, hrb2⟩, hlen_st2, hrowlen_st2, hlt_st2, hsem_st2⟩ :=
      compileDirs_spec n0 cFalse allDirGroups st1d.1 (by simp [cFalse, n0]; omega) hallDir_lt
    set st2 := compileDirs n0 cFalse st1d.1 allDirGroups

    let flatOut : List ℕ := st2.2.flatten
    have hflat_len : flatOut.length = (q + 1) * q := by
      have h1 : flatOut.length = (st2.2.map List.length).sum := List.length_flatten
      rw [h1]
      have hmap : st2.2.map List.length = List.replicate (q + 1) q := by
        apply List.ext_getElem
        · simp [hlen_st2, allDirGroups, hdirs_len]
        · intro di h1 h2
          simp only [List.getElem_map, List.getElem_replicate]
          have hdi : di < allDirGroups.length := by simpa [hlen_st2] using h1
          have hdi2 : di < st2.2.length := by simpa using h1
          have hrow := hrowlen_st2 di hdi
          rw [List.getD_eq_getElem _ _ hdi2, List.getD_eq_getElem _ _ hdi] at hrow
          rw [hrow]
          simp [allDirGroups, dirGroups, hoffs_len]
      rw [hmap, List.sum_replicate, smul_eq_mul]
    have hflat_lt : ∀ u ∈ flatOut, u < n0 + st2.1.length := by
      intro u hu
      obtain ⟨row, hrow, hurow⟩ := List.mem_flatten.mp hu
      exact hlt_st2 row hrow u hurow
    have ⟨⟨ex3, hgs3, hlen3, hmon3, hrb3⟩, hlt_r3, hsem_r3⟩ :=
      compileAndChain_spec n0 cTrue flatOut st2.1 (by simp [cTrue, n0]; omega) hflat_lt
    set st3 := compileAndChain n0 cTrue st2.1 flatOut

    let wR1 := st1b.2
    let wR2 := st1d.2
    let wR3 := st3.2
    have hwR1_lt3 : wR1 < n0 + st3.1.length := by
      rw [hgs3, hgs2, hgs1d, hgs1c]; simp; omega
    have hwR2_lt3 : wR2 < n0 + st3.1.length := by
      rw [hgs3, hgs2]; simp; omega
    let base4 := n0 + st3.1.length
    let wNB1 := base4
    let wR1NB1 := base4 + 1
    let wB0 := base4 + 2
    let wNB0 := base4 + 3
    let wEq0 := base4 + 4
    let wEq1 := base4 + 5
    let wEq2 := base4 + 6
    let decGates : List Gate :=
      [⟨GateOp.not, [wR2]⟩,
       ⟨GateOp.and, [wR1, wNB1]⟩,
       ⟨GateOp.or, [wR1NB1, wR3]⟩,
       ⟨GateOp.not, [wB0]⟩,
       ⟨GateOp.and, [wNB1, wNB0]⟩,
       ⟨GateOp.and, [wNB1, wB0]⟩,
       ⟨GateOp.and, [wR2, wNB0]⟩]
    let gs4 := st3.1 ++ decGates
    have hdec_fit : FanInTwo ⟨decGates, 0⟩ := by
      intro g hg
      simp only [decGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hdec_rb : ReadsBack (n0 + st3.1.length) ⟨decGates, 0⟩ := by
      intro j hj u hu
      have hj7 : j < 7 := by simpa [decGates] using hj
      interval_cases j <;>
        (simp only [gateAt, List.getD, decGates, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hu;
         rcases hu with rfl | rfl <;> omega)
    have hdec_notCount : notCount ⟨decGates, 0⟩ = 2 := by simp [notCount, decGates]

    let offIdx : F → ℕ := fun c => offsL.idxOf c
    have hoffIdx_lt : ∀ c : F, offIdx c < offsL.length := fun c =>
      List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ c))
    have hoffIdx_get : ∀ c : F, offsL[offIdx c]'(hoffIdx_lt c) = c := fun c =>
      List.getElem_idxOf (hoffIdx_lt c)
    have hst2_row_len : ∀ di, di < q + 1 → (st2.2.getD di []).length = q := by
      intro di hdi
      have hdi' : di < allDirGroups.length := by simp [allDirGroups, hdirs_len]; omega
      rw [hrowlen_st2 di hdi', List.getD_eq_getElem _ _ hdi']
      simp [allDirGroups, dirGroups, hoffs_len]
    have hst2_get_mem : ∀ di, di < q + 1 → ∀ ci, ci < q →
        (st2.2.getD di []).getD ci 0 ∈ st2.2.getD di [] ∧ st2.2.getD di [] ∈ st2.2 := by
      intro di hdi ci hci
      have hdi2 : di < st2.2.length := by rw [hlen_st2]; simp [allDirGroups, hdirs_len]; omega
      have hci2 : ci < (st2.2.getD di []).length := by rw [hst2_row_len di hdi]; exact hci
      refine ⟨?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hci2]; exact List.getElem_mem hci2
      · rw [List.getD_eq_getElem _ _ hdi2]; exact List.getElem_mem hdi2
    let lineWiresFor : Fin n → List ℕ := fun j =>
      (List.finRange (q + 1)).map (fun di =>
        let d := dirsL[di.val]'(by omega)
        let ci := offIdx (lineVal d (pt j))
        (st2.2.getD di.val []).getD ci 0)
    let allLineWires : List (List ℕ) := (List.finRange n).map lineWiresFor
    have hallLine_lt : ∀ xs ∈ allLineWires, ∀ u ∈ xs, u < n0 + gs4.length := by
      intro xs hxs u hu
      simp only [allLineWires, List.mem_map] at hxs
      obtain ⟨j, _, rfl⟩ := hxs
      simp only [lineWiresFor, List.mem_map] at hu
      obtain ⟨di, _, rfl⟩ := hu
      have hci : offIdx (lineVal (dirsL[di.val]'(by omega)) (pt j)) < q := by
        have h := hoffIdx_lt (lineVal (dirsL[di.val]'(by omega)) (pt j)); omega
      have ⟨hu_row, hrow_mem⟩ := hst2_get_mem di.val di.isLt _ hci
      have hlt := hlt_st2 _ hrow_mem _ hu_row
      simp only [gs4, hgs3, List.length_append]; omega
    have ⟨⟨ex5a, hgs5a, hlen5a, hmon5a, hrb5a⟩, hlen_off, hlt_off, hsem_off⟩ :=
      compileManyAndChains_spec n0 cTrue allLineWires gs4 (by simp [cTrue, n0]; omega) hallLine_lt
    set st5a := compileManyAndChains n0 cTrue gs4 allLineWires

    have ⟨⟨ex5b, hgs5b, hlen5b, hmon5b, hrb5b⟩, hlen_5b, hlt_5b, hsem_5b⟩ :=
      compileZipBin_spec GateOp.and (Or.inl rfl) n0 (List.replicate n wEq1) st1a.2
        (by simp [hlen_other, inpWs]) st5a.1
        (fun u hu => by
          have : u = wEq1 := List.eq_of_mem_replicate hu
          subst this; rw [hgs5a]; simp [gs4, wEq1, base4, decGates]; omega)
        (fun u hu => by
          have := hlt_other u hu
          rw [hgs5a]; simp only [gs4, hgs3, hgs2, hgs1d, hgs1c, hgs1b, List.length_append]; omega)
    set st5b := compileZipBin GateOp.and n0 st5a.1 (List.replicate n wEq1) st1a.2
    have ⟨⟨ex5c, hgs5c, hlen5c, hmon5c, hrb5c⟩, hlen_5c, hlt_5c, hsem_5c⟩ :=
      compileZipBin_spec GateOp.and (Or.inl rfl) n0 (List.replicate n wEq2) st5a.2
        (by simp [hlen_off, allLineWires]) st5b.1
        (fun u hu => by
          have : u = wEq2 := List.eq_of_mem_replicate hu
          subst this; rw [hgs5b, hgs5a]; simp [gs4, wEq2, base4, decGates]; omega)
        (fun u hu => by
          have := hlt_off u hu; rw [hgs5b]; simp; omega)
    set st5c := compileZipBin GateOp.and n0 st5b.1 (List.replicate n wEq2) st5a.2
    have ⟨⟨ex5d, hgs5d, hlen5d, hmon5d, hrb5d⟩, hlen_5d, hlt_5d, hsem_5d⟩ :=
      compileZipBin_spec GateOp.or (Or.inr rfl) n0 st5b.2 st5c.2
        (by simp [hlen_5b, hlen_5c]) st5c.1
        (fun u hu => by have := hlt_5b u hu; rw [hgs5c]; simp; omega)
        hlt_5c
    set st5d := compileZipBin GateOp.or n0 st5c.1 st5b.2 st5c.2
    have ⟨⟨ex5e, hgs5e, hlen5e, hmon5e, hrb5e⟩, hlen_5e, hlt_5e, hsem_5e⟩ :=
      compileZipBin_spec GateOp.or (Or.inr rfl) n0 (List.replicate n wEq0) st5d.2
        (by simp [hlen_5d, hlen_5b]) st5d.1
        (fun u hu => by
          have : u = wEq0 := List.eq_of_mem_replicate hu
          subst this; rw [hgs5d, hgs5c, hgs5b, hgs5a]; simp [gs4, wEq0, base4, decGates]; omega)
        hlt_5d
    set st5e := compileZipBin GateOp.or n0 st5d.1 (List.replicate n wEq0) st5d.2
    let C : Circuit := ⟨st5e.1, 0⟩

    let preGates := ex1a ++ ex1b ++ ex1c ++ ex1d ++ ex2 ++ ex3
    let postGates := ex5a ++ ex5b ++ ex5c ++ ex5d ++ ex5e
    have hpre_eq : st3.1 = preGates := by
      rw [hgs3, hgs2, hgs1d, hgs1c, hgs1b, hgs1a]
      simp [preGates, List.append_assoc]
    have hC_eq : C.gates = preGates ++ decGates ++ postGates := by
      change st5e.1 = _
      rw [hgs5e, hgs5d, hgs5c, hgs5b, hgs5a]
      simp [gs4, hpre_eq, postGates, List.append_assoc]
    have hpre_mon : Monotone2 ⟨preGates, 0⟩ :=
      monotone2_append _ _ 0
        (monotone2_append _ _ 0
          (monotone2_append _ _ 0
            (monotone2_append _ _ 0
              (monotone2_append _ _ 0 hmon1a hmon1b) hmon1c) hmon1d) hmon2) hmon3
    have hpost_mon : Monotone2 ⟨postGates, 0⟩ :=
      monotone2_append _ _ 0
        (monotone2_append _ _ 0
          (monotone2_append _ _ 0
            (monotone2_append _ _ 0 hmon5a hmon5b) hmon5c) hmon5d) hmon5e
    have hC_fit : FanInTwo C := by
      have h1 : FanInTwo ⟨preGates ++ decGates ++ postGates, 0⟩ :=
        fanInTwo_append (preGates ++ decGates) postGates 0
          (fanInTwo_append preGates decGates 0
            (monotone2_imp_fanInTwo ⟨preGates, 0⟩ hpre_mon) hdec_fit)
          (monotone2_imp_fanInTwo ⟨postGates, 0⟩ hpost_mon)
      intro g hg
      apply h1 g
      rw [← hC_eq]; exact hg
    have hC_notCount : notCount C = 2 := by
      have h1 : notCount C = notCount ⟨preGates ++ decGates ++ postGates, 0⟩ := by
        rw [notCount_eq_gates _ 0 0, ← hC_eq]
      rw [h1, notCount_append, notCount_append,
          notCount_of_monotone2 ⟨preGates, 0⟩ hpre_mon,
          hdec_notCount,
          notCount_of_monotone2 ⟨postGates, 0⟩ hpost_mon]
    have hC_rb : ReadsBack (n + 2) C := by
      have hrb_1a : ReadsBack n0 ⟨st1a.1, 0⟩ := by
        rw [hgs1a]; simpa using hrb1a
      have hrb_1b : ReadsBack n0 ⟨st1b.1, 0⟩ := by
        rw [hgs1b]; exact readsBack_append n0 st1a.1 ex1b 0 hrb_1a hrb1b
      have hrb_1c : ReadsBack n0 ⟨st1c.1, 0⟩ := by
        rw [hgs1c]; exact readsBack_append n0 st1b.1 ex1c 0 hrb_1b hrb1c
      have hrb_1d : ReadsBack n0 ⟨st1d.1, 0⟩ := by
        rw [hgs1d]; exact readsBack_append n0 st1c.1 ex1d 0 hrb_1c hrb1d
      have hrb_2 : ReadsBack n0 ⟨st2.1, 0⟩ := by
        rw [hgs2]; exact readsBack_append n0 st1d.1 ex2 0 hrb_1d hrb2
      have hrb_3 : ReadsBack n0 ⟨st3.1, 0⟩ := by
        rw [hgs3]; exact readsBack_append n0 st2.1 ex3 0 hrb_2 hrb3
      have hrb_4 : ReadsBack n0 ⟨gs4, 0⟩ :=
        readsBack_append n0 st3.1 decGates 0 hrb_3 hdec_rb
      have hrb_5a : ReadsBack n0 ⟨st5a.1, 0⟩ := by
        rw [hgs5a]; exact readsBack_append n0 gs4 ex5a 0 hrb_4 hrb5a
      have hrb_5b : ReadsBack n0 ⟨st5b.1, 0⟩ := by
        rw [hgs5b]; exact readsBack_append n0 st5a.1 ex5b 0 hrb_5a hrb5b
      have hrb_5c : ReadsBack n0 ⟨st5c.1, 0⟩ := by
        rw [hgs5c]; exact readsBack_append n0 st5b.1 ex5c 0 hrb_5b hrb5c
      have hrb_5d : ReadsBack n0 ⟨st5d.1, 0⟩ := by
        rw [hgs5d]; exact readsBack_append n0 st5c.1 ex5d 0 hrb_5c hrb5d
      have hrb_5e : ReadsBack n0 ⟨st5e.1, 0⟩ := by
        rw [hgs5e]; exact readsBack_append n0 st5d.1 ex5e 0 hrb_5d hrb5e
      exact hrb_5e

    have hlen5a_bound : ex5a.length ≤ n * (q + 1) := by
      have hsum5a : (allLineWires.map List.length).sum = n * (q + 1) := by
        simp only [allLineWires, List.map_map]
        have : (List.finRange n).map (List.length ∘ lineWiresFor) = List.replicate n (q + 1) := by
          apply List.ext_getElem
          · simp
          · intro i h1 h2; simp [lineWiresFor]
        rw [this, List.sum_replicate, smul_eq_mul]
      omega
    have hC_size_bound : C.size - notCount C ≤ 12 * (q + 1) * (n + 1) := by
      rw [hC_notCount]
      have hsz : C.size = preGates.length + 7 + postGates.length := by
        change C.gates.length = _
        rw [hC_eq]; simp [decGates]; omega
      have hpre_le : preGates.length ≤ 6 * n + (q + 1) * (n + 3 * q) + (q + 1) * q := by
        have hlen1a' : ex1a.length = 3 * n := by simpa [inpWs] using hlen1a
        have hlen1b' : ex1b.length ≤ n := by simpa [inpWs] using hlen1b
        have hlen1c' : ex1c.length = n := by simpa [inpWs] using hlen1c
        have hlen1d' : ex1d.length ≤ n := by rw [hlen_both] at hlen1d; simpa [inpWs] using hlen1d
        have hlen2' : ex2.length ≤ (q + 1) * (n + 3 * q) := by rw [hallDir_bound] at hlen2; exact hlen2
        have hlen3' : ex3.length ≤ (q + 1) * q := by rw [hflat_len] at hlen3; exact hlen3
        simp only [preGates, List.length_append]; omega
      have hpost_le : postGates.length ≤ n * (q + 1) + 4 * n := by
        have hlen5b' : ex5b.length = n := by simpa using hlen5b
        have hlen5c' : ex5c.length = n := by simpa using hlen5c
        have hlen5d' : ex5d.length = n := by rw [hlen_5b] at hlen5d; simpa using hlen5d
        have hlen5e' : ex5e.length = n := by simpa using hlen5e
        simp only [postGates, List.length_append]; omega
      have hq_le_n1 : q ≤ n + 1 := by
        rw [hn_add1]; nlinarith only [hq_ge4]
      have hsz_le : C.size ≤ 12 * (q + 1) * (n + 1) := by
        nlinarith only [hsz, hpre_le, hpost_le, hq_le_n1, hq_ge4, hn_pos]
      omega

    let tap : Fin n → Fin (n + 2 + C.size) := fun j =>
      ⟨st5e.2.getD j.val 0, by
        have hj : j.val < st5e.2.length := by rw [hlen_5e]; simp
        rw [List.getD_eq_getElem _ _ hj]
        exact hlt_5e _ (List.getElem_mem hj)⟩
    have hC_sem : ∀ x j, (C.wires (setInput x)).getD (tap j).val false = g x j := by
      intro x j
      let y := setInput x
      have hy : y.length = n0 := setInput_length x
      have hy_cf : ((Circuit.mk [] 0).wires y).getD cFalse false = false := by
        simpa [Circuit.wires, cFalse] using setInput_getD_n x
      have hy_ct : ((Circuit.mk [] 0).wires y).getD cTrue false = true := by
        simpa [Circuit.wires, cTrue] using setInput_getD_n1 x
      have hy_inp : ∀ i : Fin n, ((Circuit.mk [] 0).wires y).getD i.val false = decide (i ∈ x) := by
        intro i
        change (setInput x).getD i.val false = decide (i ∈ x)
        exact setInput_getD_lt x i.val i.isLt

      have hval_other : ∀ k : Fin n,
          ((Circuit.mk st1a.1 0).wires y).getD (st1a.2.getD k.val 0) false =
            decide (∃ i : Fin n, i ≠ k ∧ i ∈ x) := by
        intro k
        have h1 := hsem_other y hy hy_cf k.val (by simp [inpWs])
        rw [h1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨⟨i, hi⟩, hne, hvi⟩
          have hi' : i < n := by simpa [inpWs] using hi
          refine ⟨⟨i, hi'⟩, fun h => hne (congrArg Fin.val h), ?_⟩
          have hget : inpWs[i] = i := by simp [inpWs]
          rw [hget] at hvi
          have := hy_inp ⟨i, hi'⟩
          rw [this] at hvi
          exact of_decide_eq_true hvi
        · rintro ⟨i, hne, hix⟩
          refine ⟨⟨i.val, by simp [inpWs]⟩, fun h => hne (Fin.ext h), ?_⟩
          have hget : inpWs[i.val]'(by simp [inpWs]) = i.val := by simp [inpWs]
          rw [hget, hy_inp i, decide_eq_true hix]
      have hval_r1 : ((Circuit.mk st1b.1 0).wires y).getD wR1 false = decide x.Nonempty := by
        have hcf1a : ((Circuit.mk st1a.1 0).wires y).getD cFalse false = false := by
          rw [wires_input_n0 n0 st1a.1 y hy cFalse (by simp [cFalse, n0])]; exact hy_cf
        have h1 := hsem_r1 y hy hcf1a
        change ((Circuit.mk st1b.1 0).wires y).getD st1b.2 false = _
        rw [h1]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨i, hi, hvi⟩
          have hi' : i < n := by simpa [inpWs] using hi
          rw [wires_input_n0 n0 st1a.1 y hy i (by simp [n0]; omega)] at hvi
          have := hy_inp ⟨i, hi'⟩; rw [this] at hvi
          exact ⟨⟨i, hi'⟩, of_decide_eq_true hvi⟩
        · rintro ⟨i, hix⟩
          refine ⟨i.val, by simp [inpWs], ?_⟩
          rw [wires_input_n0 n0 st1a.1 y hy i.val (by simp [n0]; omega), hy_inp i, decide_eq_true hix]
      have hval_r2 : ((Circuit.mk st1d.1 0).wires y).getD wR2 false = decide (2 ≤ x.card) := by
        have hcf1c : ((Circuit.mk st1c.1 0).wires y).getD cFalse false = false := by
          rw [wires_input_n0 n0 st1c.1 y hy cFalse (by simp [cFalse, n0])]; exact hy_cf
        have h1 := hsem_r2 y hy hcf1c
        change ((Circuit.mk st1d.1 0).wires y).getD st1d.2 false = _
        rw [h1]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨w, hw, hvw⟩
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hw
          have hk' : k < n := by rw [hlen_both] at hk; simpa [inpWs] using hk
          rw [← List.getD_eq_getElem st1c.2 0 hk, hsem_both y hy k (by simp [inpWs]; exact hk')] at hvw
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hvw
          have hget : inpWs.getD k 0 = k := by
            rw [List.getD_eq_getElem _ _ (by simp [inpWs]; exact hk')]; simp [inpWs]
          rw [hget, wires_input_n0 n0 st1b.1 y hy k (by simp [n0]; omega),
              hy_inp ⟨k, hk'⟩, decide_eq_true_eq] at hvw
          have hoth := hvw.2
          have hoth_lt : st1a.2.getD k 0 < n0 + st1a.1.length := by
            have hk_a : k < st1a.2.length := by rw [hlen_other]; simp [inpWs]; exact hk'
            rw [List.getD_eq_getElem _ _ hk_a]; exact hlt_other _ (List.getElem_mem hk_a)
          rw [hgs1b, wires_prefix_n0 n0 st1a.1 ex1b y hy _ hoth_lt] at hoth
          rw [hval_other ⟨k, hk'⟩, decide_eq_true_eq] at hoth
          obtain ⟨i, hik, hix⟩ := hoth
          have h1lt : 1 < x.card := Finset.one_lt_card.mpr ⟨i, hix, ⟨k, hk'⟩, hvw.1, hik⟩
          omega
        · intro h2
          obtain ⟨k, hkx, i, hix, hki⟩ := Finset.one_lt_card.mp (by omega : 1 < x.card)
          have hk_c : k.val < st1c.2.length := by rw [hlen_both]; simp [inpWs]
          refine ⟨st1c.2[k.val]'hk_c, List.getElem_mem hk_c, ?_⟩
          rw [← List.getD_eq_getElem st1c.2 0 hk_c, hsem_both y hy k.val (by simp [inpWs])]
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
          constructor
          · have hget : inpWs.getD k.val 0 = k.val := by
              rw [List.getD_eq_getElem _ _ (by simp [inpWs])]; simp [inpWs]
            rw [hget, wires_input_n0 n0 st1b.1 y hy k.val (by simp [n0]; omega),
                hy_inp k, decide_eq_true hkx]
          · have hoth_lt : st1a.2.getD k.val 0 < n0 + st1a.1.length := by
              have hk_a : k.val < st1a.2.length := by rw [hlen_other]; simp [inpWs]
              rw [List.getD_eq_getElem _ _ hk_a]; exact hlt_other _ (List.getElem_mem hk_a)
            rw [hgs1b, wires_prefix_n0 n0 st1a.1 ex1b y hy _ hoth_lt, hval_other k, decide_eq_true_eq]
            exact ⟨i, hki.symm, hix⟩
      have hval_st2 : ∀ di (hdi : di < q + 1) ci (hci : ci < q),
          ((Circuit.mk st2.1 0).wires y).getD ((st2.2.getD di []).getD ci 0) false =
            decide (∃ i ∈ x, lineVal (dirsL[di]'(by omega)) (pt i) ≠ offsL[ci]'(by omega)) := by
        intro di hdi ci hci
        have hcf1d : ((Circuit.mk st1d.1 0).wires y).getD cFalse false = false := by
          rw [wires_input_n0 n0 st1d.1 y hy cFalse (by simp [cFalse, n0])]; exact hy_cf
        have hdi' : di < allDirGroups.length := by simp [allDirGroups, hdirs_len]; omega
        have hci' : ci < allDirGroups[di].length := by simp [allDirGroups, dirGroups, hoffs_len]; omega
        rw [hsem_st2 y hy hcf1d di hdi' ci hci']
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        have hdg_eq : allDirGroups[di] = dirGroups (dirsL[di]'(by omega)) := by simp [allDirGroups]
        constructor
        · rintro ⟨⟨cj, hcj⟩, hne, hany⟩
          rw [List.any_eq_true] at hany
          obtain ⟨w, hw, hvw⟩ := hany
          have hcj' : cj < offsL.length := by simpa [hdg_eq, dirGroups] using hcj
          have hgrp : allDirGroups[di][cj] =
              ((List.finRange n).filter (fun i => decide (lineVal (dirsL[di]'(by omega)) (pt i) = offsL[cj]))).map Fin.val := by
            simp [hdg_eq, dirGroups]
          rw [hgrp, List.mem_map] at hw
          obtain ⟨i, hi_filt, rfl⟩ := hw
          simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi_filt
          rw [wires_input_n0 n0 st1d.1 y hy i.val (by simp [n0]; omega),
              hy_inp i, decide_eq_true_eq] at hvw
          refine ⟨i, hvw, ?_⟩
          rw [hi_filt]
          intro heq
          have := (List.Nodup.getElem_inj_iff hoffs_nd).mp heq
          exact hne this
        · rintro ⟨i, hix, hne_val⟩
          let cj := offIdx (lineVal (dirsL[di]'(by omega)) (pt i))
          have hcj_lt : cj < offsL.length := hoffIdx_lt _
          have hcj_get : offsL[cj] = lineVal (dirsL[di]'(by omega)) (pt i) := hoffIdx_get _
          have hcj_ne : cj ≠ ci := by
            intro heq
            have h1 : offsL[cj] = offsL[ci]'(by omega) := by congr 1
            rw [hcj_get] at h1
            exact hne_val h1
          refine ⟨⟨cj, by simp [hdg_eq, dirGroups]; exact hcj_lt⟩, hcj_ne, ?_⟩
          rw [List.any_eq_true]
          refine ⟨i.val, ?_, ?_⟩
          · have hgrp : allDirGroups[di][cj]'(by simp [hdg_eq, dirGroups]; exact hcj_lt) =
                ((List.finRange n).filter (fun k => decide (lineVal (dirsL[di]'(by omega)) (pt k) = offsL[cj]))).map Fin.val := by
              simp [hdg_eq, dirGroups]
            rw [hgrp, List.mem_map]
            exact ⟨i, by simp [hcj_get], rfl⟩
          · rw [wires_input_n0 n0 st1d.1 y hy i.val (by simp [n0]; omega),
                hy_inp i, decide_eq_true hix]
      have hval_r3 : ((Circuit.mk st3.1 0).wires y).getD wR3 false = decide (rank3 x) := by
        have hct2 : ((Circuit.mk st2.1 0).wires y).getD cTrue false = true := by
          rw [wires_input_n0 n0 st2.1 y hy cTrue (by simp [cTrue, n0])]; exact hy_ct
        have h1 := hsem_r3 y hy hct2
        change ((Circuit.mk st3.1 0).wires y).getD st3.2 false = _
        rw [h1]
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, decide_eq_true_eq]
        constructor
        · intro hall d c
          have hdi_len : dirsL.idxOf d < dirsL.length :=
            List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ d))
          have hdi : dirsL.idxOf d < q + 1 := by omega
          have hci : offIdx c < q := by have h := hoffIdx_lt c; omega
          let di := dirsL.idxOf d
          let ci := offIdx c
          have ⟨hu_row, hrow_mem⟩ := hst2_get_mem di hdi ci hci
          have hmem_flat : (st2.2.getD di []).getD ci 0 ∈ flatOut :=
            List.mem_flatten.mpr ⟨st2.2.getD di [], hrow_mem, hu_row⟩
          have hv := hall _ hmem_flat
          rw [hval_st2 di hdi ci hci, decide_eq_true_eq] at hv
          have hd_get : dirsL[di]'(by omega) = d := List.getElem_idxOf hdi_len
          have hc_get : offsL[ci]'(by omega) = c := hoffIdx_get c
          simpa [hd_get, hc_get] using hv
        · intro hr3 u hu
          obtain ⟨row, hrow, hurow⟩ := List.mem_flatten.mp hu
          obtain ⟨di, hdi_lt, rfl⟩ := List.mem_iff_getElem.mp hrow
          obtain ⟨ci, hci_lt, rfl⟩ := List.mem_iff_getElem.mp hurow
          have hdi : di < q + 1 := by rw [hlen_st2] at hdi_lt; simpa [allDirGroups, hdirs_len] using hdi_lt
          have hrow_eq : st2.2[di]'hdi_lt = st2.2.getD di [] := (List.getD_eq_getElem st2.2 [] hdi_lt).symm
          have hci : ci < q := by
            have h1 := hst2_row_len di hdi
            rw [← hrow_eq] at h1; omega
          have hu_eq : (st2.2[di]'hdi_lt)[ci]'hci_lt = (st2.2.getD di []).getD ci 0 := by
            rw [← List.getD_eq_getElem _ 0 hci_lt, hrow_eq]
          rw [hu_eq, hval_st2 di hdi ci hci, decide_eq_true_eq]
          exact hr3 (dirsL[di]'(by omega)) (offsL[ci]'(by omega))

      have hr1_in3 : ((Circuit.mk st3.1 0).wires y).getD wR1 false = decide x.Nonempty := by
        have heq1 : st3.1 = st1b.1 ++ (ex1c ++ ex1d ++ ex2 ++ ex3) := by
          rw [hgs3, hgs2, hgs1d, hgs1c]; simp [List.append_assoc]
        rw [heq1, wires_prefix_n0 n0 st1b.1 _ y hy wR1 hlt_r1]
        exact hval_r1
      have hr2_in3 : ((Circuit.mk st3.1 0).wires y).getD wR2 false = decide (2 ≤ x.card) := by
        have heq2 : st3.1 = st1d.1 ++ (ex2 ++ ex3) := by
          rw [hgs3, hgs2]; simp [List.append_assoc]
        rw [heq2, wires_prefix_n0 n0 st1d.1 _ y hy wR2 hlt_r2]
        exact hval_r2
      have hdec_vals :
          ((Circuit.mk gs4 0).wires y).getD wEq0 false = decide (x = ∅) ∧
          ((Circuit.mk gs4 0).wires y).getD wEq1 false = decide (x.Nonempty ∧ ¬ (2 ≤ x.card)) ∧
          ((Circuit.mk gs4 0).wires y).getD wEq2 false = decide (2 ≤ x.card ∧ ¬ rank3 x) := by
        have hrb_4_loc : ReadsBack n0 ⟨gs4, 0⟩ := by
          have hrb_1a : ReadsBack n0 ⟨st1a.1, 0⟩ := by rw [hgs1a]; simpa using hrb1a
          have hrb_1b : ReadsBack n0 ⟨st1b.1, 0⟩ := by rw [hgs1b]; exact readsBack_append n0 st1a.1 ex1b 0 hrb_1a hrb1b
          have hrb_1c : ReadsBack n0 ⟨st1c.1, 0⟩ := by rw [hgs1c]; exact readsBack_append n0 st1b.1 ex1c 0 hrb_1b hrb1c
          have hrb_1d : ReadsBack n0 ⟨st1d.1, 0⟩ := by rw [hgs1d]; exact readsBack_append n0 st1c.1 ex1d 0 hrb_1c hrb1d
          have hrb_2 : ReadsBack n0 ⟨st2.1, 0⟩ := by rw [hgs2]; exact readsBack_append n0 st1d.1 ex2 0 hrb_1d hrb2
          have hrb_3 : ReadsBack n0 ⟨st3.1, 0⟩ := by rw [hgs3]; exact readsBack_append n0 st2.1 ex3 0 hrb_2 hrb3
          exact readsBack_append n0 st3.1 decGates 0 hrb_3 hdec_rb
        have hr1_4 : ((Circuit.mk gs4 0).wires y).getD wR1 false = decide x.Nonempty := by
          rw [wires_prefix_n0 n0 st3.1 decGates y hy wR1 hwR1_lt3]; exact hr1_in3
        have hr2_4 : ((Circuit.mk gs4 0).wires y).getD wR2 false = decide (2 ≤ x.card) := by
          rw [wires_prefix_n0 n0 st3.1 decGates y hy wR2 hwR2_lt3]; exact hr2_in3
        have hr3_4 : ((Circuit.mk gs4 0).wires y).getD wR3 false = decide (rank3 x) := by
          rw [wires_prefix_n0 n0 st3.1 decGates y hy wR3 hlt_r3]; exact hval_r3
        have hgate : ∀ idx (hidx : idx < 7),
            ((Circuit.mk gs4 0).wires y).getD (base4 + idx) false =
              (decGates[idx]).op.eval ((decGates[idx]).inputs.map (fun u => ((Circuit.mk gs4 0).wires y).getD u false)) := by
          intro idx hidx
          have hj : st3.1.length + idx < gs4.length := by simp [gs4, decGates]; omega
          have heq : base4 + idx = n0 + (st3.1.length + idx) := by simp [base4]; omega
          rw [heq, wires_get_gate_rb_eq n0 ⟨gs4, 0⟩ y hy (st3.1.length + idx) hj hrb_4_loc]
          have hget : gs4[st3.1.length + idx] = decGates[idx] := by
            simp [gs4, List.getElem_append_right]
          rw [hget]
        have hNB1 : ((Circuit.mk gs4 0).wires y).getD wNB1 false = !decide (2 ≤ x.card) := by
          have h := hgate 0 (by omega)
          simp only [decGates, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
            List.headD_cons] at h
          rw [show wNB1 = base4 + 0 from rfl, h, hr2_4]
        have hR1NB1 : ((Circuit.mk gs4 0).wires y).getD wR1NB1 false =
            (decide x.Nonempty && !decide (2 ≤ x.card)) := by
          have h := hgate 1 (by omega)
          simp only [decGates, List.getElem_cons_zero, List.getElem_cons_succ, GateOp.eval,
            List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
          rw [show wR1NB1 = base4 + 1 from rfl, h, hr1_4, hNB1]
        have hB0 : ((Circuit.mk gs4 0).wires y).getD wB0 false =
            ((decide x.Nonempty && !decide (2 ≤ x.card)) || decide (rank3 x)) := by
          have h := hgate 2 (by omega)
          simp only [decGates, List.getElem_cons_zero, List.getElem_cons_succ, GateOp.eval,
            List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at h
          rw [show wB0 = base4 + 2 from rfl, h, hR1NB1, hr3_4]
        have hNB0 : ((Circuit.mk gs4 0).wires y).getD wNB0 false =
            !((decide x.Nonempty && !decide (2 ≤ x.card)) || decide (rank3 x)) := by
          have h := hgate 3 (by omega)
          simp only [decGates, List.getElem_cons_zero, List.getElem_cons_succ, GateOp.eval,
            List.map_cons, List.map_nil, List.headD_cons] at h
          rw [show wNB0 = base4 + 3 from rfl, h, hB0]
        have hEq0 : ((Circuit.mk gs4 0).wires y).getD wEq0 false =
            (!decide (2 ≤ x.card) && !((decide x.Nonempty && !decide (2 ≤ x.card)) || decide (rank3 x))) := by
          have h := hgate 4 (by omega)
          simp only [decGates, List.getElem_cons_zero, List.getElem_cons_succ, GateOp.eval,
            List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
          rw [show wEq0 = base4 + 4 from rfl, h, hNB1, hNB0]
        have hEq1 : ((Circuit.mk gs4 0).wires y).getD wEq1 false =
            (!decide (2 ≤ x.card) && ((decide x.Nonempty && !decide (2 ≤ x.card)) || decide (rank3 x))) := by
          have h := hgate 5 (by omega)
          simp only [decGates, List.getElem_cons_zero, List.getElem_cons_succ, GateOp.eval,
            List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
          rw [show wEq1 = base4 + 5 from rfl, h, hNB1, hB0]
        have hEq2 : ((Circuit.mk gs4 0).wires y).getD wEq2 false =
            (decide (2 ≤ x.card) && !((decide x.Nonempty && !decide (2 ≤ x.card)) || decide (rank3 x))) := by
          have h := hgate 6 (by omega)
          simp only [decGates, List.getElem_cons_zero, List.getElem_cons_succ, GateOp.eval,
            List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
          rw [show wEq2 = base4 + 6 from rfl, h, hr2_4, hNB0]

        have hr3_imp_2 : rank3 x → 2 ≤ x.card := by
          intro hr3
          obtain ⟨p1, hp1, _⟩ := hr3 none 0
          obtain ⟨p2, hp2, hne⟩ := hr3 none (pt p1).1
          have h12 : p1 ≠ p2 := fun h => hne (by simp [h, lineVal])
          have := Finset.one_lt_card.mpr ⟨p1, hp1, p2, hp2, h12⟩
          omega
        have h2_imp_ne : 2 ≤ x.card → x.Nonempty := fun h2 =>
          Finset.card_pos.mp (by omega)
        rw [hEq0, hEq1, hEq2]
        by_cases hx0 : x = ∅
        · subst hx0
          have hne : ¬ (∅ : Finset (Fin n)).Nonempty := by simp
          have h2 : ¬ (2 ≤ (∅ : Finset (Fin n)).card) := by simp
          have hr3 : ¬ rank3 ∅ := fun h => h2 (hr3_imp_2 h)
          simp [hne, h2, hr3]
        · have hxne : x.Nonempty := Finset.nonempty_iff_ne_empty.mpr hx0
          by_cases hx2 : 2 ≤ x.card
          · by_cases hr3 : rank3 x
            · simp [hx0, hxne, hx2, hr3]
            · simp [hx0, hxne, hx2, hr3]
          · have hr3 : ¬ rank3 x := fun h => hx2 (hr3_imp_2 h)
            simp [hx0, hxne, hx2, hr3]

      have hval_off : ((Circuit.mk st5a.1 0).wires y).getD (st5a.2.getD j.val 0) false =
          decide (∀ d : Option F, ∃ i ∈ x, lineVal d (pt i) ≠ lineVal d (pt j)) := by
        have hct4 : ((Circuit.mk gs4 0).wires y).getD cTrue false = true := by
          rw [wires_input_n0 n0 gs4 y hy cTrue (by simp [cTrue, n0])]
          exact hy_ct
        have h1 := hsem_off y hy hct4 j.val (by simp [allLineWires])
        rw [h1]
        have hall_eq : allLineWires[j.val]'(by simp [allLineWires]) = lineWiresFor j := by
          simp [allLineWires]
        rw [hall_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, decide_eq_true_eq]
        constructor
        · intro hall d
          let di := dirsL.idxOf d
          have hdi_len : dirsL.idxOf d < dirsL.length :=
            List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ d))
          have hdi : di < q + 1 := by change dirsL.idxOf d < q + 1; omega
          have hd_get : dirsL[di]'(by omega) = d := List.getElem_idxOf hdi_len
          let ci := offIdx (lineVal d (pt j))
          have hci : ci < q := by have h := hoffIdx_lt (lineVal d (pt j)); omega
          have hc_get : offsL[ci]'(by omega) = lineVal d (pt j) := hoffIdx_get _
          let u := (st2.2.getD di []).getD ci 0
          have hu_mem : u ∈ lineWiresFor j := by
            simp only [lineWiresFor, List.mem_map]
            exact ⟨⟨di, hdi⟩, List.mem_finRange _, by simp [u, ci, hd_get]⟩
          have hvu := hall u hu_mem
          have ⟨hu_row, hrow_mem⟩ := hst2_get_mem di hdi ci hci
          have hu_lt2 : u < n0 + st2.1.length := hlt_st2 _ hrow_mem _ hu_row
          rw [wires_prefix_n0 n0 st3.1 decGates y hy u (by rw [hgs3]; simp; omega),
              hgs3, wires_prefix_n0 n0 st2.1 ex3 y hy u hu_lt2,
              hval_st2 di hdi ci hci, decide_eq_true_eq] at hvu
          simpa [hd_get, hc_get] using hvu
        · intro hall u hu
          simp only [lineWiresFor, List.mem_map] at hu
          obtain ⟨⟨di, hdi⟩, _, rfl⟩ := hu
          let d := dirsL[di]'(by rw [hdirs_len]; exact hdi)
          let ci := offIdx (lineVal d (pt j))
          have hci : ci < q := by have h := hoffIdx_lt (lineVal d (pt j)); omega
          have hc_get : offsL[ci]'(by omega) = lineVal d (pt j) := hoffIdx_get _
          have ⟨hu_row, hrow_mem⟩ := hst2_get_mem di hdi ci hci
          have hu_lt2 : (st2.2.getD di []).getD ci 0 < n0 + st2.1.length := hlt_st2 _ hrow_mem _ hu_row
          have hu_lt3 : (st2.2.getD di []).getD ci 0 < n0 + st3.1.length := by rw [hgs3, List.length_append]; omega
          change ((Circuit.mk gs4 0).wires y).getD ((st2.2.getD di []).getD ci 0) false = true
          rw [wires_prefix_n0 n0 st3.1 decGates y hy _ hu_lt3,
              hgs3, wires_prefix_n0 n0 st2.1 ex3 y hy _ hu_lt2,
              hval_st2 di hdi ci hci, decide_eq_true_eq]
          simpa [d, hc_get] using hall d

      change ((Circuit.mk st5e.1 0).wires y).getD (st5e.2.getD j.val 0) false = g x j
      rw [hsem_5e y hy j.val (by simp)]
      have hrep0 : (List.replicate n wEq0).getD j.val 0 = wEq0 := by
        rw [List.getD_eq_getElem _ _ (by simp)]; simp
      simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hrep0]
      rw [hsem_5d y hy j.val (by rw [hlen_5b]; simp)]
      simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]

      have hwEq0_val : ((Circuit.mk st5d.1 0).wires y).getD wEq0 false = decide (x = ∅) := by
        have heq : st5d.1 = gs4 ++ (ex5a ++ ex5b ++ ex5c ++ ex5d) := by
          rw [hgs5d, hgs5c, hgs5b, hgs5a]; simp [List.append_assoc]
        rw [heq, wires_prefix_n0 n0 gs4 _ y hy wEq0 (by simp [gs4, wEq0, base4, decGates]; omega)]
        exact hdec_vals.1
      have hw1_val : ((Circuit.mk st5c.1 0).wires y).getD (st5b.2.getD j.val 0) false =
          (decide (x.Nonempty ∧ ¬ (2 ≤ x.card)) && decide (∃ i : Fin n, i ≠ j ∧ i ∈ x)) := by
        have h5b_lt : st5b.2.getD j.val 0 < n0 + st5b.1.length := by
          have hj : j.val < st5b.2.length := by rw [hlen_5b]; simp
          rw [List.getD_eq_getElem _ _ hj]; exact hlt_5b _ (List.getElem_mem hj)
        rw [hgs5c, wires_prefix_n0 n0 st5b.1 ex5c y hy _ h5b_lt,
            hsem_5b y hy j.val (by simp)]
        have hrep1 : (List.replicate n wEq1).getD j.val 0 = wEq1 := by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hrep1]
        rw [hgs5a, wires_prefix_n0 n0 gs4 ex5a y hy wEq1 (by simp [gs4, wEq1, base4, decGates]; omega), hdec_vals.2.1]
        have hoth_lt : st1a.2.getD j.val 0 < n0 + st1a.1.length := by
          have hj : j.val < st1a.2.length := by rw [hlen_other]; simp [inpWs]
          rw [List.getD_eq_getElem _ _ hj]; exact hlt_other _ (List.getElem_mem hj)
        have heq_pre : gs4 ++ ex5a = st1a.1 ++ (ex1b ++ ex1c ++ ex1d ++ ex2 ++ ex3 ++ decGates ++ ex5a) := by
          simp [gs4, hgs3, hgs2, hgs1d, hgs1c, hgs1b, List.append_assoc]
        rw [heq_pre, wires_prefix_n0 n0 st1a.1 _ y hy _ hoth_lt, hval_other j]
      have hw2_val : ((Circuit.mk st5c.1 0).wires y).getD (st5c.2.getD j.val 0) false =
          (decide (2 ≤ x.card ∧ ¬ rank3 x) &&
            decide (∀ d : Option F, ∃ i ∈ x, lineVal d (pt i) ≠ lineVal d (pt j))) := by
        rw [hsem_5c y hy j.val (by simp)]
        have hrep2 : (List.replicate n wEq2).getD j.val 0 = wEq2 := by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, hrep2]
        have heq2 : st5b.1 = gs4 ++ (ex5a ++ ex5b) := by
          rw [hgs5b, hgs5a]; simp [List.append_assoc]
        rw [heq2, wires_prefix_n0 n0 gs4 _ y hy wEq2 (by simp [gs4, wEq2, base4, decGates]; omega),
            hdec_vals.2.2]
        have hoff_lt : st5a.2.getD j.val 0 < n0 + st5a.1.length := by
          have hj : j.val < st5a.2.length := by rw [hlen_off]; simp [allLineWires]
          rw [List.getD_eq_getElem _ _ hj]; exact hlt_off _ (List.getElem_mem hj)
        have heq3 : gs4 ++ (ex5a ++ ex5b) = st5a.1 ++ ex5b := by rw [hgs5a, ← List.append_assoc]
        rw [heq3, wires_prefix_n0 n0 st5a.1 ex5b y hy _ hoff_lt, hval_off]
      rw [hwEq0_val, hw1_val, hw2_val, hg_char x j, Bool.or_assoc]
    exact ⟨g, hg_fits, hg_anti, hno_runs4, C, ⟨hC_fit, hC_rb, show 0 < n + 2 + C.size by omega, tap, hC_sem⟩, hC_notCount, hC_size_bound⟩

  have hset_eq : ∀ x : Finset (Fin n),
      (List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _))) ++ [false, true] = setInput x := by
    intro x
    unfold setInput
    congr 1
    congr 1
    funext i
    exact decide_eq_decide.mpr Iff.rfl

  refine ⟨H, hH_symm, hH_irrefl, ?_, ?_, ?_, hPart3, ?_⟩
  · intro i
    convert hH_deg i using 2
  · intro g hfits
    have h1 := hPart1 g hfits
    refine ⟨h1.1, fun C hC => h1.2 C ?_⟩
    rcases hC with ⟨hf, hrb, ho, tap, htap⟩
    refine ⟨hf, hrb, ho, tap, fun x j => ?_⟩
    rw [← hset_eq x]
    exact htap x j
  · obtain ⟨g, hg_fits, hg_anti, hno4, C, ⟨hf, hrb, ho, tap, htap⟩, hnc, hsz⟩ := hPart2
    refine ⟨g, hg_fits, hg_anti, hno4, C, ⟨hf, hrb, ho, tap, fun x j => ?_⟩, hnc, hsz⟩
    rw [hset_eq x]
    exact htap x j
  · intro k color hprop
    have h4 := hPart4 k color hprop
    have hg_eq : ∀ (x : Finset (Fin n)) (j : Fin n),
        @decide (∀ i ∈ x, color i ≠ color j) (Classical.propDecidable _) =
          decide (∀ i ∈ x, color i ≠ color j) := fun x j => decide_eq_decide.mpr Iff.rfl
    simp only [hg_eq]
    refine ⟨h4.1, h4.2.1, fun C hC => h4.2.2 C ?_⟩
    rcases hC with ⟨hf, hrb, ho, tap, htap⟩
    refine ⟨hf, hrb, ho, tap, fun x j => ?_⟩
    rw [← hset_eq x]
    exact htap x j

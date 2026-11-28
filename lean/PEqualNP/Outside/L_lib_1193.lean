import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1193

section Build

variable (n k : Nat) (src dst : Fin k → Fin n) (s t : Fin n)

def M : Nat := n + 3 * k + 2

def baseV (v : Fin n) : Fin (M n k) := ⟨v.val, by simp [M]; omega⟩
def sExtra : Fin (M n k) := ⟨n, by simp [M]; omega⟩
def tExtra : Fin (M n k) := ⟨n + 1, by simp [M]⟩
def outCopy (e : Fin k) : Fin (M n k) := ⟨n + 2 + 3 * e.val, by simp [M]; omega⟩
def inCopy (e : Fin k) : Fin (M n k) := ⟨n + 2 + 3 * e.val + 1, by simp [M]; omega⟩
def slotFin (e : Fin k) : Fin (M n k) := ⟨n + 2 + 3 * e.val + 2, by simp [M]; omega⟩

def slotEmb : Fin k ↪ Fin (M n k) :=
  ⟨slotFin n k, fun e1 e2 h => Fin.ext (by simp [slotFin] at h; omega)⟩

def owner (i : Fin (M n k)) : Option (Fin n) :=
  if h1 : i.val < n then some ⟨i.val, h1⟩
  else if i.val = n then some s
  else if i.val = n + 1 then some t
  else if hq : (i.val - (n + 2)) / 3 < k then
    if (i.val - (n + 2)) % 3 = 0 then some (src ⟨(i.val - (n + 2)) / 3, hq⟩)
    else if (i.val - (n + 2)) % 3 = 1 then some (dst ⟨(i.val - (n + 2)) / 3, hq⟩)
    else none
  else none

lemma owner_baseV (v : Fin n) : owner n k src dst s t (baseV n k v) = some v := by
  simp [owner, baseV, v.isLt]

lemma owner_sExtra : owner n k src dst s t (sExtra n k) = some s := by
  simp [owner, sExtra]

lemma owner_tExtra : owner n k src dst s t (tExtra n k) = some t := by
  simp [owner, tExtra]

lemma owner_outCopy (e : Fin k) : owner n k src dst s t (outCopy n k e) = some (src e) := by
  unfold owner
  have h1 : ¬ ((outCopy n k e).val < n) := by simp [outCopy]; omega
  have h2 : (outCopy n k e).val ≠ n := by simp [outCopy]; omega
  have h3 : (outCopy n k e).val ≠ n + 1 := by simp [outCopy]; omega
  have hsub : (outCopy n k e).val - (n + 2) = 3 * e.val := by simp [outCopy]
  have hq : ((outCopy n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((outCopy n k e).val - (n + 2)) % 3 = 0 := by rw [hsub]; omega
  have hqk : ((outCopy n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  rw [dif_neg h1, if_neg h2, if_neg h3, dif_pos hqk, if_pos hr]
  congr 1; congr 1; exact Fin.ext hq

lemma owner_inCopy (e : Fin k) : owner n k src dst s t (inCopy n k e) = some (dst e) := by
  unfold owner
  have h1 : ¬ ((inCopy n k e).val < n) := by simp [inCopy]; omega
  have h2 : (inCopy n k e).val ≠ n := by simp [inCopy]; omega
  have h3 : (inCopy n k e).val ≠ n + 1 := by simp [inCopy]; omega
  have hsub : (inCopy n k e).val - (n + 2) = 3 * e.val + 1 := by simp [inCopy]; omega
  have hq : ((inCopy n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((inCopy n k e).val - (n + 2)) % 3 = 1 := by rw [hsub]; omega
  have hqk : ((inCopy n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  rw [dif_neg h1, if_neg h2, if_neg h3, dif_pos hqk, if_neg (by rw [hr]; omega), if_pos hr]
  congr 1; congr 1; exact Fin.ext hq

lemma owner_slotFin (e : Fin k) : owner n k src dst s t (slotFin n k e) = none := by
  unfold owner
  have h1 : ¬ ((slotFin n k e).val < n) := by simp [slotFin]; omega
  have h2 : (slotFin n k e).val ≠ n := by simp [slotFin]; omega
  have h3 : (slotFin n k e).val ≠ n + 1 := by simp [slotFin]; omega
  have hsub : (slotFin n k e).val - (n + 2) = 3 * e.val + 2 := by simp [slotFin]; omega
  have hq : ((slotFin n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((slotFin n k e).val - (n + 2)) % 3 = 2 := by rw [hsub]; omega
  have hqk : ((slotFin n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  rw [dif_neg h1, if_neg h2, if_neg h3, dif_pos hqk,
    if_neg (by rw [hr]; omega), if_neg (by rw [hr]; omega)]

lemma owner_eq_none_iff (i : Fin (M n k)) :
    owner n k src dst s t i = none ↔ ∃ e : Fin k, slotFin n k e = i := by
  constructor
  · intro h
    unfold owner at h
    split_ifs at h with h1 h2 h3 hq hr0 hr1
    · exact ⟨⟨(i.val - (n + 2)) / 3, hq⟩, Fin.ext (by simp [slotFin]; omega)⟩
    · exfalso; have hi := i.isLt; simp [M] at hi; omega
  · rintro ⟨e, rfl⟩
    exact owner_slotFin n k src dst s t e

def ringList (v : Fin n) : List (Fin (M n k)) :=
  (List.finRange (M n k)).filter (fun i => owner n k src dst s t i == some v)

lemma ringList_nodup (v : Fin n) : (ringList n k src dst s t v).Nodup :=
  (List.nodup_finRange _).filter _

lemma mem_ringList_iff (v : Fin n) (i : Fin (M n k)) :
    i ∈ ringList n k src dst s t v ↔ owner n k src dst s t i = some v := by
  simp [ringList]

def cycNext {α : Type} [DecidableEq α] (l : List α) (x : α) : α :=
  if h : 0 < l.length then l[(l.idxOf x + 1) % l.length]'(Nat.mod_lt _ h) else x

def cycPrev {α : Type} [DecidableEq α] (l : List α) (x : α) : α :=
  if h : 0 < l.length then l[(l.idxOf x + l.length - 1) % l.length]'(Nat.mod_lt _ h) else x

lemma cycNext_mem {α : Type} [DecidableEq α] {l : List α} {x : α} (hx : x ∈ l) :
    cycNext l x ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  simp [cycNext, hpos]

lemma cycPrev_mem {α : Type} [DecidableEq α] {l : List α} {x : α} (hx : x ∈ l) :
    cycPrev l x ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  simp [cycPrev, hpos]

lemma cycPrev_cycNext {α : Type} [DecidableEq α] {l : List α} (hnd : l.Nodup) {x : α} (hx : x ∈ l) :
    cycPrev l (cycNext l x) = x := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  have hidx : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have h1 : l.idxOf (l[(l.idxOf x + 1) % l.length]'(Nat.mod_lt _ hpos)) = (l.idxOf x + 1) % l.length :=
    List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ hpos)
  have hmod : ((l.idxOf x + 1) % l.length + l.length - 1) % l.length = l.idxOf x := by
    by_cases hlast : l.idxOf x + 1 = l.length
    · rw [hlast, Nat.mod_self, Nat.zero_add]
      have : l.length - 1 < l.length := by omega
      rw [Nat.mod_eq_of_lt this]; omega
    · have hlt : l.idxOf x + 1 < l.length := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have : l.idxOf x + 1 + l.length - 1 = l.idxOf x + l.length := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
  simp only [cycPrev, cycNext, hpos, ↓reduceDIte, h1]
  have heq : l[((l.idxOf x + 1) % l.length + l.length - 1) % l.length]'(Nat.mod_lt _ hpos) =
      l[l.idxOf x]'hidx := by congr 1
  rw [heq, List.getElem_idxOf]

lemma cycNext_cycPrev {α : Type} [DecidableEq α] {l : List α} (hnd : l.Nodup) {x : α} (hx : x ∈ l) :
    cycNext l (cycPrev l x) = x := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  have hidx : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have h1 : l.idxOf (l[(l.idxOf x + l.length - 1) % l.length]'(Nat.mod_lt _ hpos)) =
      (l.idxOf x + l.length - 1) % l.length :=
    List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ hpos)
  have hmod : ((l.idxOf x + l.length - 1) % l.length + 1) % l.length = l.idxOf x := by
    by_cases hz : l.idxOf x = 0
    · rw [hz, Nat.zero_add]
      have hlt : l.length - 1 < l.length := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have : l.length - 1 + 1 = l.length := by omega
      rw [this, Nat.mod_self]
    · have : l.idxOf x + l.length - 1 = (l.idxOf x - 1) + l.length := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.idxOf x - 1 < l.length)]
      have h2 : l.idxOf x - 1 + 1 = l.idxOf x := by omega
      rw [h2, Nat.mod_eq_of_lt hidx]
  simp only [cycNext, cycPrev, hpos, ↓reduceDIte, h1]
  have heq : l[((l.idxOf x + l.length - 1) % l.length + 1) % l.length]'(Nat.mod_lt _ hpos) =
      l[l.idxOf x]'hidx := by congr 1
  rw [heq, List.getElem_idxOf]

lemma cyc_reach {α : Type} [DecidableEq α] {l : List α} (hnd : l.Nodup) (P : α → Prop)
    (hstep : ∀ x ∈ l, P x → P (cycNext l x)) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hpx : P x) :
    P y := by
  have hpos : 0 < l.length := List.length_pos_of_mem hx
  have hix : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hiy : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hy
  have hiter : ∀ d : Nat, P (l[(l.idxOf x + d) % l.length]'(Nat.mod_lt _ hpos)) := by
    intro d
    induction d with
    | zero =>
      have hmod : (l.idxOf x + 0) % l.length = l.idxOf x := by
        rw [Nat.add_zero, Nat.mod_eq_of_lt hix]
      have h0 : l[(l.idxOf x + 0) % l.length]'(Nat.mod_lt _ hpos) = l[l.idxOf x]'hix := by congr 1
      rw [h0, List.getElem_idxOf]; exact hpx
    | succ d ih =>
      set cur := l[(l.idxOf x + d) % l.length]'(Nat.mod_lt _ hpos)
      have hcur_mem : cur ∈ l := List.getElem_mem _
      have hnxt := hstep cur hcur_mem ih
      have hidx_cur : l.idxOf cur = (l.idxOf x + d) % l.length :=
        List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ hpos)
      have hmod : ((l.idxOf x + d) % l.length + 1) % l.length = (l.idxOf x + (d + 1)) % l.length := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      have hceq : cycNext l cur = l[(l.idxOf x + (d + 1)) % l.length]'(Nat.mod_lt _ hpos) := by
        simp only [cycNext, hpos, ↓reduceDIte, hidx_cur]
        congr 1
      rwa [hceq] at hnxt
  have h := hiter (l.idxOf y + l.length - l.idxOf x)
  have hmod : (l.idxOf x + (l.idxOf y + l.length - l.idxOf x)) % l.length = l.idxOf y := by
    have : l.idxOf x + (l.idxOf y + l.length - l.idxOf x) = l.idxOf y + l.length := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hiy]
  have heq : l[(l.idxOf x + (l.idxOf y + l.length - l.idxOf x)) % l.length]'(Nat.mod_lt _ hpos) = y := by
    have : l[(l.idxOf x + (l.idxOf y + l.length - l.idxOf x)) % l.length]'(Nat.mod_lt _ hpos) =
        l[l.idxOf y]'hiy := by congr 1
    rw [this, List.getElem_idxOf]
  rwa [heq] at h

def ringNb (i : Fin (M n k)) (c : Bool) : Option (Fin (M n k) × Bool) :=
  match owner n k src dst s t i with
  | none => none
  | some v =>
    if 2 ≤ (ringList n k src dst s t v).length then
      if c then some (cycNext (ringList n k src dst s t v) i, false)
      else some (cycPrev (ringList n k src dst s t v) i, true)
    else none

lemma ringNb_flip {i j : Fin (M n k)} {c c' : Bool}
    (h : ringNb n k src dst s t i c = some (j, c')) : c' = !c := by
  unfold ringNb at h
  cases ho : owner n k src dst s t i <;> rw [ho] at h
  · simp at h
  · dsimp only at h
    split_ifs at h with hlen hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2, hc]; rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hcf : c = false := Bool.eq_false_iff.mpr hc
      rw [← h.2, hcf]; rfl

lemma ringNb_symm (u v : Fin (M n k) × Bool) :
    ringNb n k src dst s t u.1 u.2 = some v ↔ ringNb n k src dst s t v.1 v.2 = some u := by
  have dir : ∀ (a b : Fin (M n k) × Bool),
      ringNb n k src dst s t a.1 a.2 = some b → ringNb n k src dst s t b.1 b.2 = some a := by
    rintro ⟨i, c⟩ ⟨j, c'⟩ h
    unfold ringNb at h ⊢
    cases ho : owner n k src dst s t i with
    | none => simp [ho] at h
    | some w =>
      rw [ho] at h; dsimp only at h
      split_ifs at h with hlen hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hj, hc'⟩
        subst hj; subst hc'
        have hi : i ∈ ringList n k src dst s t w := (mem_ringList_iff n k src dst s t w i).mpr ho
        have hnxt_mem := cycNext_mem hi
        have ho2 : owner n k src dst s t (cycNext (ringList n k src dst s t w) i) = some w :=
          (mem_ringList_iff n k src dst s t w _).mp hnxt_mem
        rw [ho2]; dsimp only
        rw [ite_cond_eq_true _ _ (eq_true hlen)]
        have hprev := cycPrev_cycNext (ringList_nodup n k src dst s t w) hi
        simp [hprev, hc]
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hj, hc'⟩
        subst hj; subst hc'
        have hcf : c = false := Bool.eq_false_iff.mpr hc
        have hi : i ∈ ringList n k src dst s t w := (mem_ringList_iff n k src dst s t w i).mpr ho
        have hprv_mem := cycPrev_mem hi
        have ho2 : owner n k src dst s t (cycPrev (ringList n k src dst s t w) i) = some w :=
          (mem_ringList_iff n k src dst s t w _).mp hprv_mem
        rw [ho2]; dsimp only
        rw [ite_cond_eq_true _ _ (eq_true hlen)]
        have hnxt := cycNext_cycPrev (ringList_nodup n k src dst s t w) hi
        simp [hnxt, hcf]
  exact ⟨dir u v, dir v u⟩

def extraNb (i : Fin (M n k)) (c : Bool) : Option (Fin (M n k) × Bool) :=
  if i = baseV n k s ∧ c = false then some (sExtra n k, false)
  else if i = sExtra n k ∧ c = false then some (baseV n k s, false)
  else if i = baseV n k t ∧ c = true then some (tExtra n k, true)
  else if i = tExtra n k ∧ c = true then some (baseV n k t, true)
  else if n + 2 ≤ i.val then
    if hq : (i.val - (n + 2)) / 3 < k then
      if (i.val - (n + 2)) % 3 = 0 ∧ c = true then some (slotFin n k ⟨(i.val - (n + 2)) / 3, hq⟩, false)
      else if (i.val - (n + 2)) % 3 = 2 ∧ c = false then some (outCopy n k ⟨(i.val - (n + 2)) / 3, hq⟩, true)
      else if (i.val - (n + 2)) % 3 = 2 ∧ c = true then some (inCopy n k ⟨(i.val - (n + 2)) / 3, hq⟩, false)
      else if (i.val - (n + 2)) % 3 = 1 ∧ c = false then some (slotFin n k ⟨(i.val - (n + 2)) / 3, hq⟩, true)
      else none
    else none
  else none

lemma baseV_ne_sExtra (v : Fin n) : baseV n k v ≠ sExtra n k := by
  intro h; have := congrArg Fin.val h; simp [baseV, sExtra] at this; omega

lemma baseV_ne_tExtra (v : Fin n) : baseV n k v ≠ tExtra n k := by
  intro h; have := congrArg Fin.val h; simp [baseV, tExtra] at this; omega

lemma extraNb_baseV_s_false :
    extraNb n k s t (baseV n k s) false = some (sExtra n k, false) := by
  unfold extraNb; rw [if_pos ⟨rfl, rfl⟩]

lemma extraNb_sExtra_false :
    extraNb n k s t (sExtra n k) false = some (baseV n k s, false) := by
  unfold extraNb
  rw [if_neg (fun h => baseV_ne_sExtra n k s h.1.symm), if_pos ⟨rfl, rfl⟩]

lemma extraNb_baseV_t_true :
    extraNb n k s t (baseV n k t) true = some (tExtra n k, true) := by
  unfold extraNb
  rw [if_neg (by simp), if_neg (by simp), if_pos ⟨rfl, rfl⟩]

lemma extraNb_tExtra_true :
    extraNb n k s t (tExtra n k) true = some (baseV n k t, true) := by
  unfold extraNb
  rw [if_neg (by simp), if_neg (by simp),
    if_neg (fun h => baseV_ne_tExtra n k t h.1.symm), if_pos ⟨rfl, rfl⟩]

lemma extraNb_outCopy_true (e : Fin k) :
    extraNb n k s t (outCopy n k e) true = some (slotFin n k e, false) := by
  unfold extraNb
  have hge : n + 2 ≤ (outCopy n k e).val := by simp [outCopy]
  have hsub : (outCopy n k e).val - (n + 2) = 3 * e.val := by simp [outCopy]
  have hq : ((outCopy n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((outCopy n k e).val - (n + 2)) % 3 = 0 := by rw [hsub]; omega
  have hqk : ((outCopy n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  have h3 : outCopy n k e ≠ baseV n k t := fun h => by have := congrArg Fin.val h; simp [outCopy, baseV] at this; omega
  have h4 : outCopy n k e ≠ tExtra n k := fun h => by have := congrArg Fin.val h; simp [outCopy, tExtra] at this; omega
  rw [if_neg (by simp), if_neg (by simp), if_neg (fun h => h3 h.1), if_neg (fun h => h4 h.1),
    if_pos hge, dif_pos hqk, if_pos ⟨hr, rfl⟩]
  congr 1; congr 1; congr 1; exact Fin.ext hq

lemma extraNb_slotFin_false (e : Fin k) :
    extraNb n k s t (slotFin n k e) false = some (outCopy n k e, true) := by
  unfold extraNb
  have hge : n + 2 ≤ (slotFin n k e).val := by simp [slotFin]; omega
  have hsub : (slotFin n k e).val - (n + 2) = 3 * e.val + 2 := by simp [slotFin]; omega
  have hq : ((slotFin n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((slotFin n k e).val - (n + 2)) % 3 = 2 := by rw [hsub]; omega
  have hqk : ((slotFin n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  have h1 : slotFin n k e ≠ baseV n k s := fun h => by have := congrArg Fin.val h; simp [slotFin, baseV] at this; omega
  have h2 : slotFin n k e ≠ sExtra n k := fun h => by have := congrArg Fin.val h; simp [slotFin, sExtra] at this; omega
  rw [if_neg (fun h => h1 h.1), if_neg (fun h => h2 h.1), if_neg (by simp), if_neg (by simp),
    if_pos hge, dif_pos hqk, if_neg (by simp), if_pos ⟨hr, rfl⟩]
  congr 1; congr 1; congr 1; exact Fin.ext hq

lemma extraNb_slotFin_true (e : Fin k) :
    extraNb n k s t (slotFin n k e) true = some (inCopy n k e, false) := by
  unfold extraNb
  have hge : n + 2 ≤ (slotFin n k e).val := by simp [slotFin]; omega
  have hsub : (slotFin n k e).val - (n + 2) = 3 * e.val + 2 := by simp [slotFin]; omega
  have hq : ((slotFin n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((slotFin n k e).val - (n + 2)) % 3 = 2 := by rw [hsub]; omega
  have hqk : ((slotFin n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  have h3 : slotFin n k e ≠ baseV n k t := fun h => by have := congrArg Fin.val h; simp [slotFin, baseV] at this; omega
  have h4 : slotFin n k e ≠ tExtra n k := fun h => by have := congrArg Fin.val h; simp [slotFin, tExtra] at this; omega
  rw [if_neg (by simp), if_neg (by simp), if_neg (fun h => h3 h.1), if_neg (fun h => h4 h.1),
    if_pos hge, dif_pos hqk, if_neg (by rw [hr]; omega), if_neg (by simp), if_pos ⟨hr, rfl⟩]
  congr 1; congr 1; congr 1; exact Fin.ext hq

lemma extraNb_inCopy_false (e : Fin k) :
    extraNb n k s t (inCopy n k e) false = some (slotFin n k e, true) := by
  unfold extraNb
  have hge : n + 2 ≤ (inCopy n k e).val := by simp [inCopy]; omega
  have hsub : (inCopy n k e).val - (n + 2) = 3 * e.val + 1 := by simp [inCopy]; omega
  have hq : ((inCopy n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
  have hr : ((inCopy n k e).val - (n + 2)) % 3 = 1 := by rw [hsub]; omega
  have hqk : ((inCopy n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
  have h1 : inCopy n k e ≠ baseV n k s := fun h => by have := congrArg Fin.val h; simp [inCopy, baseV] at this; omega
  have h2 : inCopy n k e ≠ sExtra n k := fun h => by have := congrArg Fin.val h; simp [inCopy, sExtra] at this; omega
  rw [if_neg (fun h => h1 h.1), if_neg (fun h => h2 h.1), if_neg (by simp), if_neg (by simp),
    if_pos hge, dif_pos hqk, if_neg (by simp), if_neg (by rw [hr]; omega),
    if_neg (by simp), if_pos ⟨hr, rfl⟩]
  congr 1; congr 1; congr 1; exact Fin.ext hq

lemma extraNb_cases {i j : Fin (M n k)} {c c' : Bool}
    (h : extraNb n k s t i c = some (j, c')) :
    (i = baseV n k s ∧ c = false ∧ j = sExtra n k ∧ c' = false) ∨
    (i = sExtra n k ∧ c = false ∧ j = baseV n k s ∧ c' = false) ∨
    (i = baseV n k t ∧ c = true ∧ j = tExtra n k ∧ c' = true) ∨
    (i = tExtra n k ∧ c = true ∧ j = baseV n k t ∧ c' = true) ∨
    (∃ e : Fin k, i = outCopy n k e ∧ c = true ∧ j = slotFin n k e ∧ c' = false) ∨
    (∃ e : Fin k, i = slotFin n k e ∧ c = false ∧ j = outCopy n k e ∧ c' = true) ∨
    (∃ e : Fin k, i = slotFin n k e ∧ c = true ∧ j = inCopy n k e ∧ c' = false) ∨
    (∃ e : Fin k, i = inCopy n k e ∧ c = false ∧ j = slotFin n k e ∧ c' = true) := by
  unfold extraNb at h
  split_ifs at h with h1 h2 h3 h4 hge hq h5 h6 h7 h8
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inl ⟨h1.1, h1.2, h.1.symm, h.2.symm⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inl ⟨h2.1, h2.2, h.1.symm, h.2.symm⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inr (.inl ⟨h3.1, h3.2, h.1.symm, h.2.symm⟩))
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inr (.inr (.inl ⟨h4.1, h4.2, h.1.symm, h.2.symm⟩)))
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inr (.inr (.inr (.inl ⟨⟨(i.val - (n + 2)) / 3, hq⟩,
      Fin.ext (by simp [outCopy]; omega), h5.2, h.1.symm, h.2.symm⟩))))
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨⟨(i.val - (n + 2)) / 3, hq⟩,
      Fin.ext (by simp [slotFin]; omega), h6.2, h.1.symm, h.2.symm⟩)))))
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨⟨(i.val - (n + 2)) / 3, hq⟩,
      Fin.ext (by simp [slotFin]; omega), h7.2, h.1.symm, h.2.symm⟩))))))
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨⟨(i.val - (n + 2)) / 3, hq⟩,
      Fin.ext (by simp [inCopy]; omega), h8.2, h.1.symm, h.2.symm⟩))))))

lemma extraNb_ne_self (i : Fin (M n k)) (c : Bool) : extraNb n k s t i c ≠ some (i, c) := by
  intro h
  rcases extraNb_cases n k s t h with
    ⟨hi, _, hj, _⟩ | ⟨hi, _, hj, _⟩ | ⟨hi, _, hj, _⟩ | ⟨hi, _, hj, _⟩ |
    ⟨_, _, hc, _, hc'⟩ | ⟨_, _, hc, _, hc'⟩ | ⟨_, _, hc, _, hc'⟩ | ⟨_, _, hc, _, hc'⟩
  · exact baseV_ne_sExtra n k s (hi.symm.trans hj)
  · exact baseV_ne_sExtra n k s (hj.symm.trans hi)
  · exact baseV_ne_tExtra n k t (hi.symm.trans hj)
  · exact baseV_ne_tExtra n k t (hj.symm.trans hi)
  · rw [hc] at hc'; cases hc'
  · rw [hc] at hc'; cases hc'
  · rw [hc] at hc'; cases hc'
  · rw [hc] at hc'; cases hc'

lemma extraNb_symm (u v : Fin (M n k) × Bool) :
    extraNb n k s t u.1 u.2 = some v ↔ extraNb n k s t v.1 v.2 = some u := by
  have dir : ∀ (a b : Fin (M n k) × Bool),
      extraNb n k s t a.1 a.2 = some b → extraNb n k s t b.1 b.2 = some a := by
    rintro ⟨i, c⟩ ⟨j, c'⟩ h
    rcases extraNb_cases n k s t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨e, rfl, rfl, rfl, rfl⟩ | ⟨e, rfl, rfl, rfl, rfl⟩ | ⟨e, rfl, rfl, rfl, rfl⟩ | ⟨e, rfl, rfl, rfl, rfl⟩
    · exact extraNb_sExtra_false n k s t
    · exact extraNb_baseV_s_false n k s t
    · exact extraNb_tExtra_true n k s t
    · exact extraNb_baseV_t_true n k s t
    · exact extraNb_slotFin_false n k s t e
    · exact extraNb_outCopy_true n k s t e
    · exact extraNb_inCopy_false n k s t e
    · exact extraNb_slotFin_true n k s t e
  exact ⟨dir u v, dir v u⟩

def nb (u : Fin (M n k) × Bool) : Finset (Fin (M n k) × Bool) :=
  {(u.1, !u.2)} ∪ (ringNb n k src dst s t u.1 u.2).toFinset ∪ (extraNb n k s t u.1 u.2).toFinset

def aPin : Bool → Fin (M n k)
  | false => baseV n k s
  | true => baseV n k t

def bPin : Bool → Fin (M n k)
  | false => sExtra n k
  | true => tExtra n k

lemma nb_irrefl_card (u : Fin (M n k) × Bool) :
    u ∉ nb n k src dst s t u ∧ (nb n k src dst s t u).card ≤ 3 := by
  constructor
  · intro hm
    simp only [nb, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def] at hm
    rcases hm with (h1 | h2) | h3
    · have := congrArg Prod.snd h1; cases u.2 <;> simp at this
    · have := ringNb_flip n k src dst s t h2; cases u.2 <;> simp at this
    · exact extraNb_ne_self n k s t u.1 u.2 h3
  · unfold nb
    calc
      ({(u.1, !u.2)} ∪ (ringNb n k src dst s t u.1 u.2).toFinset ∪ (extraNb n k s t u.1 u.2).toFinset).card
          ≤ ({(u.1, !u.2)} ∪ (ringNb n k src dst s t u.1 u.2).toFinset).card +
            (extraNb n k s t u.1 u.2).toFinset.card := Finset.card_union_le _ _
      _ ≤ ({(u.1, !u.2)} : Finset _).card + (ringNb n k src dst s t u.1 u.2).toFinset.card +
            (extraNb n k s t u.1 u.2).toFinset.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 1 + 1 + 1 := by
        have h1 : ({(u.1, !u.2)} : Finset (Fin (M n k) × Bool)).card = 1 := Finset.card_singleton _
        have h2 : (ringNb n k src dst s t u.1 u.2).toFinset.card ≤ 1 := by
          cases ringNb n k src dst s t u.1 u.2 <;> simp
        have h3 : (extraNb n k s t u.1 u.2).toFinset.card ≤ 1 := by
          cases extraNb n k s t u.1 u.2 <;> simp
        omega

lemma nb_symm (u v : Fin (M n k) × Bool) :
    v ∈ nb n k src dst s t u ↔ u ∈ nb n k src dst s t v := by
  simp only [nb, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ((h1 | h2) | h3)
    · left; left; rcases u with ⟨ui, uc⟩; rcases v with ⟨vi, vc⟩
      simp only [Prod.mk.injEq] at h1 ⊢
      exact ⟨h1.1.symm, by rw [h1.2, Bool.not_not]⟩
    · left; right; exact (ringNb_symm n k src dst s t u v).mp h2
    · right; exact (extraNb_symm n k s t u v).mp h3
  · rintro ((h1 | h2) | h3)
    · left; left; rcases u with ⟨ui, uc⟩; rcases v with ⟨vi, vc⟩
      simp only [Prod.mk.injEq] at h1 ⊢
      exact ⟨h1.1.symm, by rw [h1.2, Bool.not_not]⟩
    · left; right; exact (ringNb_symm n k src dst s t u v).mpr h2
    · right; exact (extraNb_symm n k s t u v).mpr h3

lemma nb_same_shore (c : Bool) :
    aPin n k s t c ≠ bPin n k c ∧
    ∀ i j : Fin (M n k), (j, c) ∈ nb n k src dst s t (i, c) ↔
      (i = aPin n k s t c ∧ j = bPin n k c) ∨ (i = bPin n k c ∧ j = aPin n k s t c) := by
  constructor
  · cases c
    · exact baseV_ne_sExtra n k s
    · exact baseV_ne_tExtra n k t
  · intro i j
    simp only [nb, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
    constructor
    · rintro ((h1 | h2) | h3)
      · have := congrArg Prod.snd h1; cases c <;> simp at this
      · have := ringNb_flip n k src dst s t h2; cases c <;> simp at this
      · rcases extraNb_cases n k s t h3 with
          ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ |
          ⟨_, _, hc, _, hc'⟩ | ⟨_, _, hc, _, hc'⟩ | ⟨_, _, hc, _, hc'⟩ | ⟨_, _, hc, _, hc'⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · rw [hc] at hc'; cases hc'
        · rw [hc] at hc'; cases hc'
        · rw [hc] at hc'; cases hc'
        · rw [hc] at hc'; cases hc'
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · right; cases c
        · exact extraNb_baseV_s_false n k s t
        · exact extraNb_baseV_t_true n k s t
      · right; cases c
        · exact extraNb_sExtra_false n k s t
        · exact extraNb_tExtra_true n k s t

end Build

end PEqualNP.Outside.L_lib_1193

theorem PEqualNP.Outside.L_lib_1193 : (∀ (n k : Nat) (src dst : Fin k → Fin n) (s t : Fin n), s ≠ t →
  ∃ (m : Nat) (slot : Fin k ↪ Fin m)
    (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (a b : Bool → Fin m),
    m ≤ n + 3*k + 2 ∧
    (∀ u, u ∉ nb u ∧ (nb u).card ≤ 3) ∧
    (∀ u v, v ∈ nb u ↔ u ∈ nb v) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∀ c, a c ≠ b c ∧ ∀ i j,
      (j,c) ∈ nb (i,c) ↔ (i = a c ∧ j = b c) ∨ (i = b c ∧ j = a c)) ∧
    ∀ z : Fin k → Bool,
      let walk := Relation.ReflTransGen
        (fun (u v : Fin n) => ∃ e, z e = true ∧ src e = u ∧ dst e = v)
      let possible := ∃ x : (Fin m × Bool) → Bool,
        (∀ u, ∀ v ∈ nb u, x u = true ∨ x v = true) ∧
        (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
        (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
      ¬ possible ↔ walk s t) := by
  open PEqualNP.Outside.L_lib_1193 in
  intro n k src dst s t _hst
  refine ⟨M n k, slotEmb n k, nb n k src dst s t, aPin n k s t, bPin n k, le_rfl,
    nb_irrefl_card n k src dst s t, nb_symm n k src dst s t,
    fun i => by simp [nb], nb_same_shore n k src dst s t, ?_⟩
  intro z
  dsimp only
  set walk := Relation.ReflTransGen (fun (u v : Fin n) => ∃ e, z e = true ∧ src e = u ∧ dst e = v)
  constructor
  · intro hnpos
    by_contra hnw
    apply hnpos
    let _ : DecidablePred (fun v : Fin n => walk s v) := Classical.decPred _
    let reach : Fin n → Bool := fun v => decide (walk s v)
    let x : (Fin (M n k) × Bool) → Bool := fun ⟨i, c⟩ =>
      match owner n k src dst s t i with
      | some v => if c then !(reach v) else reach v
      | none =>
        if hq : (i.val - (n + 2)) / 3 < k then
          let e : Fin k := ⟨(i.val - (n + 2)) / 3, hq⟩
          if z e then (if c then !(reach (src e)) else reach (src e)) else true
        else true
    have hx_owner : ∀ i v c, owner n k src dst s t i = some v →
        x (i, c) = if c then !(reach v) else reach v := by
      intro i v c ho; simp [x, ho]
    have hx_slot : ∀ e c, x (slotFin n k e, c) =
        if z e then (if c then !(reach (src e)) else reach (src e)) else true := by
      intro e c
      have ho := owner_slotFin n k src dst s t e
      have hsub : (slotFin n k e).val - (n + 2) = 3 * e.val + 2 := by simp [slotFin]; omega
      have hq : ((slotFin n k e).val - (n + 2)) / 3 = e.val := by rw [hsub]; omega
      have hqk : ((slotFin n k e).val - (n + 2)) / 3 < k := by rw [hq]; exact e.isLt
      have hfin : (⟨((slotFin n k e).val - (n + 2)) / 3, hqk⟩ : Fin k) = e := Fin.ext hq
      simp only [x, ho, dif_pos hqk, hfin]
    have hreach_s : reach s = true := by simp [reach, walk, Relation.ReflTransGen.refl]
    have hreach_t : reach t = false := by simp [reach, hnw]
    refine ⟨x, ?_, ?_, ?_⟩
    · intro u v hv
      simp only [nb, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def] at hv
      rcases u with ⟨i, c⟩
      rcases v with ⟨j, c'⟩
      rcases hv with (heq | hring) | hextra
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        cases ho : owner n k src dst s t j with
        | some w =>
          rw [hx_owner j w c ho, hx_owner j w (!c) ho]
          cases c <;> cases reach w <;> simp
        | none =>
          obtain ⟨e, rfl⟩ := (owner_eq_none_iff n k src dst s t j).mp ho
          rw [hx_slot e c, hx_slot e (!c)]
          cases z e <;> cases c <;> cases reach (src e) <;> simp
      · unfold ringNb at hring
        cases ho : owner n k src dst s t i with
        | none => simp [ho] at hring
        | some w =>
          rw [ho] at hring; dsimp only at hring
          split_ifs at hring with hlen hc
          · simp only [Option.some.injEq, Prod.mk.injEq] at hring
            rcases hring with ⟨rfl, rfl⟩
            have hi : i ∈ ringList n k src dst s t w := (mem_ringList_iff n k src dst s t w i).mpr ho
            have ho2 := (mem_ringList_iff n k src dst s t w _).mp (cycNext_mem hi)
            rw [hx_owner i w c ho, hx_owner _ w false ho2, hc]
            cases reach w <;> simp
          · simp only [Option.some.injEq, Prod.mk.injEq] at hring
            rcases hring with ⟨rfl, rfl⟩
            have hcf : c = false := Bool.eq_false_iff.mpr hc
            have hi : i ∈ ringList n k src dst s t w := (mem_ringList_iff n k src dst s t w i).mpr ho
            have ho2 := (mem_ringList_iff n k src dst s t w _).mp (cycPrev_mem hi)
            rw [hx_owner i w c ho, hx_owner _ w true ho2, hcf]
            cases reach w <;> simp
      · rcases extraNb_cases n k s t hextra with
          ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
          ⟨e, rfl, rfl, rfl, rfl⟩ | ⟨e, rfl, rfl, rfl, rfl⟩ | ⟨e, rfl, rfl, rfl, rfl⟩ | ⟨e, rfl, rfl, rfl, rfl⟩
        · rw [hx_owner _ s false (owner_baseV n k src dst s t s)]; simp [hreach_s]
        · rw [hx_owner _ s false (owner_sExtra n k src dst s t)]; simp [hreach_s]
        · rw [hx_owner _ t true (owner_baseV n k src dst s t t)]; simp [hreach_t]
        · rw [hx_owner _ t true (owner_tExtra n k src dst s t)]; simp [hreach_t]
        · rw [hx_owner _ (src e) true (owner_outCopy n k src dst s t e), hx_slot e false]
          cases z e <;> cases reach (src e) <;> simp
        · rw [hx_slot e false, hx_owner _ (src e) true (owner_outCopy n k src dst s t e)]
          cases z e <;> cases reach (src e) <;> simp
        · rw [hx_slot e true, hx_owner _ (dst e) false (owner_inCopy n k src dst s t e)]
          cases hze : z e
          · simp
          · cases hsrc : reach (src e)
            · simp
            · right
              have hws : walk s (src e) := of_decide_eq_true hsrc
              have hwd : walk s (dst e) := Relation.ReflTransGen.tail hws ⟨e, hze, rfl, rfl⟩
              simp [reach, hwd]
        · rw [hx_owner _ (dst e) false (owner_inCopy n k src dst s t e), hx_slot e true]
          cases hze : z e
          · simp
          · cases hsrc : reach (src e)
            · simp
            · left
              have hws : walk s (src e) := of_decide_eq_true hsrc
              have hwd : walk s (dst e) := Relation.ReflTransGen.tail hws ⟨e, hze, rfl, rfl⟩
              simp [reach, hwd]
    · intro e
      change xor (x (slotFin n k e, false)) (x (slotFin n k e, true)) = z e
      rw [hx_slot e false, hx_slot e true]
      cases z e <;> cases reach (src e) <;> rfl
    · intro i hi
      cases ho : owner n k src dst s t i with
      | none =>
        obtain ⟨e, he⟩ := (owner_eq_none_iff n k src dst s t i).mp ho
        exact (hi e he).elim
      | some w =>
        rw [hx_owner i w false ho, hx_owner i w true ho]
        cases reach w <;> rfl
  · intro hwalk ⟨x, hclause, hslot, hnon⟩
    have hneg : ∀ i, owner n k src dst s t i ≠ none → x (i, true) = !(x (i, false)) := by
      intro i hne
      have hne' : ∀ e, slotEmb n k e ≠ i := fun e he => hne ((owner_eq_none_iff n k src dst s t i).mpr ⟨e, he⟩)
      have hx := hnon i hne'
      cases hf : x (i, false) <;> cases ht : x (i, true) <;> simp_all
    have hring_eq : ∀ (v : Fin n) (i j : Fin (M n k)),
        owner n k src dst s t i = some v → owner n k src dst s t j = some v →
        x (i, false) = true → x (j, false) = true := by
      intro v i j hoi hoj hxi
      have hi : i ∈ ringList n k src dst s t v := (mem_ringList_iff n k src dst s t v i).mpr hoi
      have hj : j ∈ ringList n k src dst s t v := (mem_ringList_iff n k src dst s t v j).mpr hoj
      by_cases hlen : 2 ≤ (ringList n k src dst s t v).length
      · refine cyc_reach (ringList_nodup n k src dst s t v) (fun p => x (p, false) = true) ?_ hi hj hxi
        intro p hp hxp
        have hop : owner n k src dst s t p = some v := (mem_ringList_iff n k src dst s t v p).mp hp
        have hmem : (cycNext (ringList n k src dst s t v) p, false) ∈ nb n k src dst s t (p, true) := by
          simp only [nb, Finset.mem_union, Option.mem_toFinset, Option.mem_def]
          left; right; simp [ringNb, hop, hlen]
        have hcl := hclause (p, true) _ hmem
        have hpt : x (p, true) = false := by rw [hneg p (by simp [hop]), hxp]; rfl
        simpa [hpt] using hcl
      · have hpos : 0 < (ringList n k src dst s t v).length := List.length_pos_of_mem hi
        have hlen1 : (ringList n k src dst s t v).length = 1 := by omega
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen1
        rw [ha] at hi hj
        simp only [List.mem_singleton] at hi hj
        rwa [hj, ← hi]
    have hs_true : x (baseV n k s, false) = true := by
      have hmem : (sExtra n k, false) ∈ nb n k src dst s t (baseV n k s, false) := by
        simp only [nb, Finset.mem_union, Option.mem_toFinset, Option.mem_def]
        right; exact extraNb_baseV_s_false n k s t
      rcases hclause (baseV n k s, false) _ hmem with h | h
      · exact h
      · exact hring_eq s (sExtra n k) (baseV n k s)
          (owner_sExtra n k src dst s t) (owner_baseV n k src dst s t s) h
    have ht_false : x (baseV n k t, false) = false := by
      have hmem : (tExtra n k, true) ∈ nb n k src dst s t (baseV n k t, true) := by
        simp only [nb, Finset.mem_union, Option.mem_toFinset, Option.mem_def]
        right; exact extraNb_baseV_t_true n k s t
      by_contra hnt
      have htf : x (baseV n k t, false) = true := Bool.eq_true_of_not_eq_false hnt
      have hte : x (tExtra n k, false) = true :=
        hring_eq t (baseV n k t) (tExtra n k)
          (owner_baseV n k src dst s t t) (owner_tExtra n k src dst s t) htf
      have ht1 : x (baseV n k t, true) = false := by
        rw [hneg _ (by simp [owner_baseV]), htf]; rfl
      have ht2 : x (tExtra n k, true) = false := by
        rw [hneg _ (by simp [owner_tExtra]), hte]; rfl
      rcases hclause (baseV n k t, true) _ hmem with h | h <;> simp [ht1, ht2] at h
    have hreach_true : ∀ u : Fin n, walk s u → x (baseV n k u, false) = true := by
      intro u hu
      induction hu with
      | refl => exact hs_true
      | @tail b c _ hstep ih =>
        rcases hstep with ⟨e, hze, rfl, rfl⟩
        have hout_f : x (outCopy n k e, false) = true :=
          hring_eq (src e) (baseV n k (src e)) (outCopy n k e)
            (owner_baseV n k src dst s t (src e)) (owner_outCopy n k src dst s t e) ih
        have hout_t : x (outCopy n k e, true) = false := by
          rw [hneg _ (by simp [owner_outCopy]), hout_f]; rfl
        have hmem1 : (slotFin n k e, false) ∈ nb n k src dst s t (outCopy n k e, true) := by
          simp only [nb, Finset.mem_union, Option.mem_toFinset, Option.mem_def]
          right; exact extraNb_outCopy_true n k s t e
        have hsf : x (slotFin n k e, false) = true := by
          simpa [hout_t] using hclause (outCopy n k e, true) _ hmem1
        have hst : x (slotFin n k e, true) = false := by
          have hxe := hslot e
          change xor (x (slotFin n k e, false)) (x (slotFin n k e, true)) = z e at hxe
          rw [hsf, hze] at hxe
          cases hst' : x (slotFin n k e, true) <;> simp_all
        have hmem2 : (inCopy n k e, false) ∈ nb n k src dst s t (slotFin n k e, true) := by
          simp only [nb, Finset.mem_union, Option.mem_toFinset, Option.mem_def]
          right; exact extraNb_slotFin_true n k s t e
        have hinf : x (inCopy n k e, false) = true := by
          simpa [hst] using hclause (slotFin n k e, true) _ hmem2
        exact hring_eq (dst e) (inCopy n k e) (baseV n k (dst e))
          (owner_inCopy n k src dst s t e) (owner_baseV n k src dst s t (dst e)) hinf
    have hcontra := hreach_true t hwalk
    rw [ht_false] at hcontra
    exact Bool.noConfusion hcontra

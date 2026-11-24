import PNP.TwoN

/-!
# A hard function: "at least two inputs are on"

`TwoN` proves `2n - 3` gates for any hard function. This file shows the class is not empty: the
threshold function `atLeastTwo` is hard, so every circuit for it over the full binary basis has
at least `2n - 3` gates.

Why it mixes two inputs `i` and `j`: with both off the rest must supply two ones, with one on the
rest must supply one, with both on nothing is needed. Three different functions of the rest.
-/

namespace PNP.Full

/-- How many inputs are on. -/
def ones : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + ones bs

/-- At least two inputs are on. -/
def atLeastTwo (x : List Bool) : Bool := decide (2 ≤ ones x)

theorem ones_replicate (n : Nat) : ones (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ones, ih]

theorem zeros_getD (n i : Nat) : (List.replicate n false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem ones_set : ∀ (x : List Bool) (i : Nat) (b : Bool), i < x.length →
    ones (x.set i b) + (if x.getD i false then 1 else 0) = ones x + (if b then 1 else 0)
  | [], _, _, h => by simp at h
  | a :: x, 0, b, _ => by
    cases a <;> cases b <;> simp [ones] <;> omega
  | a :: x, i + 1, b, h => by
    have := ones_set x i b (by simpa using h)
    simp only [List.set_cons_succ, ones, List.getD_cons_succ]
    omega

/-- Switching on an input that was off adds one. -/
theorem ones_set_off (x : List Bool) (i : Nat) (b : Bool) (h : i < x.length)
    (hoff : x.getD i false = false) : ones (x.set i b) = ones x + (if b then 1 else 0) := by
  have := ones_set x i b h
  rw [hoff] at this
  simpa using this

/-- All inputs off, except `i`, `j`, `k`, which hold `a`, `b`, `c`. -/
def pt (n i j k : Nat) (a b c : Bool) : List Bool :=
  (((List.replicate n false).set k c).set j b).set i a

section pt

variable {n i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) (hij : i ≠ j) (hik : i ≠ k)
  (hjk : j ≠ k) (a b c : Bool)

include hi in
theorem pt_i : (pt n i j k a b c).getD i false = a :=
  getD_set_self _ i a (by rw [List.length_set, List.length_set, List.length_replicate]; exact hi)

include hj hij in
theorem pt_j : (pt n i j k a b c).getD j false = b := by
  unfold pt
  rw [getD_set_ne hij,
    getD_set_self _ j b (by rw [List.length_set, List.length_replicate]; exact hj)]

theorem pt_rest (a' b' : Bool) {w : Nat} (hwi : w ≠ i) (hwj : w ≠ j) :
    (pt n i j k a b c).getD w false = (pt n i j k a' b' c).getD w false := by
  unfold pt
  rw [getD_set_ne (Ne.symm hwi), getD_set_ne (Ne.symm hwj), getD_set_ne (Ne.symm hwi),
    getD_set_ne (Ne.symm hwj)]

include hi hj hk hij hik hjk in
theorem pt_ones : ones (pt n i j k a b c) =
    (if c then 1 else 0) + (if b then 1 else 0) + (if a then 1 else 0) := by
  unfold pt
  rw [ones_set_off _ i a
      (by rw [List.length_set, List.length_set, List.length_replicate]; exact hi)
      (by rw [getD_set_ne (Ne.symm hij), getD_set_ne (Ne.symm hik), zeros_getD]),
    ones_set_off _ j b (by rw [List.length_set, List.length_replicate]; exact hj)
      (by rw [getD_set_ne (Ne.symm hjk), zeros_getD]),
    ones_set_off _ k c (by rw [List.length_replicate]; exact hk) (zeros_getD n k),
    ones_replicate, Nat.zero_add]

end pt

theorem exists_third {F : List Nat} (h : 3 ≤ F.length) (hnd : F.Nodup) {i : Nat} (hi : i ∈ F)
    (j : Nat) : ∃ k, k ∈ F ∧ k ≠ i ∧ k ≠ j := by
  have hlen : (F.erase i).length = F.length - 1 := List.length_erase_of_mem hi
  obtain ⟨k, hk, hkj⟩ := exists_ne_of_two (F := F.erase i) (by omega) (hnd.erase i) j
  exact ⟨k, List.mem_of_mem_erase hk, fun h' => not_mem_erase_self hnd i (h' ▸ hk), hkj⟩

/-- The restrictions on which `atLeastTwo` stays hard: every fixed input is off. -/
def Zeroed (n : Nat) (F : List Nat) (P : List Bool → Prop) : Prop :=
  Cube n F P ∧ P (List.replicate n false)

theorem atLeastTwo_hard (n : Nat) : Hard n atLeastTwo (Zeroed n) where
  cube := fun _ _ h => h.1
  fix := fun _ _ h _ i hi => ⟨false, h.1.restrict hi false, h.2, zeros_getD n i⟩
  depends := by
    intro F P h hF i hi
    obtain ⟨j, hj, hji⟩ := exists_ne_of_two (by omega) h.1.nodup i
    have hin := h.1.lt i hi
    have hjn := h.1.lt j hj
    refine ⟨(List.replicate n false).set j true, h.1.free _ h.2 j hj true, ?_⟩
    have hoff : ((List.replicate n false).set j true).getD i false = false := by
      rw [getD_set_ne hji, zeros_getD]
    have hlen : i < ((List.replicate n false).set j true).length := by
      rw [List.length_set, List.length_replicate]
      exact hin
    have hone : ones ((List.replicate n false).set j true) = 1 := by
      rw [ones_set_off _ j true (by rw [List.length_replicate]; exact hjn) (zeros_getD n j),
        ones_replicate]
      rfl
    unfold atLeastTwo
    rw [ones_set_off _ i true hlen hoff, ones_set_off _ i false hlen hoff, hone]
    decide
  mixes := by
    intro F P h hF i j hi hj hij b
    obtain ⟨k, hk, hki, hkj⟩ := exists_third hF h.1.nodup hi j
    have hin := h.1.lt i hi
    have hjn := h.1.lt j hj
    have hkn := h.1.lt k hk
    have hP : ∀ a b' c, P (pt n i j k a b' c) := fun a b' c =>
      h.1.free _ (h.1.free _ (h.1.free _ h.2 k hk c) j hj b') i hi a
    have hf : ∀ a b' c, atLeastTwo (pt n i j k a b' c) =
        decide (2 ≤ (if c then 1 else 0) + (if b' then 1 else 0) + (if a then 1 else 0)) :=
      fun a b' c => by
        unfold atLeastTwo
        rw [pt_ones hin hjn hkn hij (Ne.symm hki) (Ne.symm hkj)]
    -- Of the three ways (off, off), (off, on), (on, on), the bit `b` cannot tell two apart.
    by_cases h1 : b false false = b false true
    · refine ⟨pt n i j k false false true, pt n i j k false true true, hP _ _ _, hP _ _ _,
        fun w hwi hwj => pt_rest _ _ _ _ _ hwi hwj, ?_, ?_⟩
      · rw [pt_i hin, pt_j hjn hij, pt_i hin, pt_j hjn hij]
        exact h1
      · rw [hf, hf]
        decide
    by_cases h2 : b false true = b true true
    · refine ⟨pt n i j k false true false, pt n i j k true true false, hP _ _ _, hP _ _ _,
        fun w hwi hwj => pt_rest _ _ _ _ _ hwi hwj, ?_, ?_⟩
      · rw [pt_i hin, pt_j hjn hij, pt_i hin, pt_j hjn hij]
        exact h2
      · rw [hf, hf]
        decide
    · refine ⟨pt n i j k false false false, pt n i j k true true false, hP _ _ _, hP _ _ _,
        fun w hwi hwj => pt_rest _ _ _ _ _ hwi hwj, ?_, ?_⟩
      · rw [pt_i hin, pt_j hjn hij, pt_i hin, pt_j hjn hij]
        cases h00 : b false false <;> cases h01 : b false true <;> cases h11 : b true true <;>
          simp_all
      · rw [hf, hf]
        decide

/-- **Two gates per input.** Every circuit over the full binary basis that decides whether at
least two of its inputs are on has at least `2n - 3` gates. -/
theorem atLeastTwo_needs_two_gates_per_input (c : Circuit) (hc : c.Computes atLeastTwo) :
    2 * c.inputs - 3 ≤ c.size :=
  hard_needs_two_per_input (atLeastTwo_hard c.inputs)
    ⟨fullCube c.inputs, List.length_replicate⟩ c rfl hc

/-- The bound is met for two inputs: one AND gate. So the theorem is not empty. -/
def andPair : Circuit :=
  { inputs := 2, gates := [{ op := fun a b => a && b, left := 0, right := 1 }] }

theorem andPair_computes_atLeastTwo : andPair.Computes atLeastTwo := by
  constructor
  · intro i h
    have hi : i = 0 := by
      have : i < 1 := h
      omega
    subst hi
    simp [andPair]
  · intro x hx
    rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [andPair] at hx
    · simp [andPair] at hx
    · cases a <;> cases b <;> rfl
    · simp [andPair] at hx

end PNP.Full

import PNP.Kill

/-!
# Fixing inputs one at a time

The main proof fixes one input, then another. `Cube n F P` says where it stands: `P` is the set of
inputs still allowed, the inputs listed in `F` are still free, and every other input is stuck.
`ComputesXorOn` says the circuit outputs the XOR of the free inputs, or its negation, on `P`.
Fix one free input and both statements survive with one input fewer.
-/

namespace PNP

theorem getD_set_self (x : List Bool) (i : Nat) (b : Bool) (h : i < x.length) :
    (x.set i b).getD i false = b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem getD_set_ne {x : List Bool} {i j : Nat} {b : Bool} (h : i ≠ j) :
    (x.set i b).getD j false = x.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- The XOR of the inputs whose positions are listed in `F`. -/
def xorOn : List Nat → List Bool → Bool
  | [], _ => false
  | i :: F, x => x.getD i false != xorOn F x

theorem xorOn_set_of_not_mem (F : List Nat) (x : List Bool) (i : Nat) (b : Bool) (h : i ∉ F) :
    xorOn F (x.set i b) = xorOn F x := by
  induction F with
  | nil => rfl
  | cons j F ih =>
    have hj : i ≠ j := fun e => h (by simp [e])
    have hF : i ∉ F := fun m => h (by simp [m])
    simp only [xorOn, getD_set_ne hj, ih hF]

theorem xorOn_erase (F : List Nat) (x : List Bool) (i : Nat) (hnd : F.Nodup) (hi : i ∈ F) :
    xorOn F x = (x.getD i false != xorOn (F.erase i) x) := by
  induction F with
  | nil => simp at hi
  | cons j F ih =>
    by_cases hji : j = i
    · subst hji
      simp [xorOn]
    · have hi' : i ∈ F := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hji
        · exact h
      have hnd' : F.Nodup := (List.nodup_cons.mp hnd).2
      rw [show (j :: F).erase i = j :: F.erase i by simp [hji]]
      simp only [xorOn, ih hnd' hi']
      cases x.getD j false <;> cases x.getD i false <;> cases xorOn (F.erase i) x <;> rfl

theorem not_mem_erase_self {F : List Nat} (hnd : F.Nodup) (i : Nat) : i ∉ F.erase i := by
  induction F with
  | nil => simp
  | cons j F ih =>
    have hjF : j ∉ F := (List.nodup_cons.mp hnd).1
    have hnd' : F.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hji : j = i
    · subst hji
      simpa using hjF
    · rw [show (j :: F).erase i = j :: F.erase i by simp [hji]]
      intro h
      rcases List.mem_cons.mp h with h | h
      · exact hji h.symm
      · exact ih hnd' h

/-- Setting a free input to `b` leaves `b` XOR the other free inputs. -/
theorem xorOn_set (F : List Nat) (x : List Bool) (i : Nat) (b : Bool) (hnd : F.Nodup)
    (hi : i ∈ F) (hx : i < x.length) :
    xorOn F (x.set i b) = (b != xorOn (F.erase i) x) := by
  rw [xorOn_erase F _ i hnd hi, getD_set_self x i b hx,
    xorOn_set_of_not_mem _ _ _ _ (not_mem_erase_self hnd i)]

/-- `P` is the set of inputs of length `n` in which the positions in `F` are free and every other
position is stuck. -/
structure Cube (n : Nat) (F : List Nat) (P : List Bool → Prop) : Prop where
  len : ∀ x, P x → x.length = n
  nonempty : ∃ x, P x
  free : ∀ x, P x → ∀ i, i ∈ F → ∀ b, P (x.set i b)
  stuck : ∀ i, i ∉ F → ∃ d, ∀ x, P x → x.getD i false = d
  nodup : F.Nodup
  lt : ∀ i, i ∈ F → i < n

/-- The inputs in `P` whose position `i` holds `c0`. -/
abbrev fixInput (P : List Bool → Prop) (i : Nat) (c0 : Bool) : List Bool → Prop :=
  fun x => P x ∧ x.getD i false = c0

theorem Cube.restrict {n : Nat} {F : List Nat} {P : List Bool → Prop} (h : Cube n F P) {i : Nat}
    (hi : i ∈ F) (c0 : Bool) : Cube n (F.erase i) (fixInput P i c0) where
  len := fun x hx => h.len x hx.1
  nonempty := by
    obtain ⟨x, hx⟩ := h.nonempty
    exact ⟨x.set i c0, h.free x hx i hi c0,
      getD_set_self x i c0 (by rw [h.len x hx]; exact h.lt i hi)⟩
  free := by
    intro x hx j hj b
    have hji : j ≠ i := fun e => not_mem_erase_self h.nodup i (by rw [e] at hj; exact hj)
    exact ⟨h.free x hx.1 j (List.mem_of_mem_erase hj) b, by rw [getD_set_ne hji]; exact hx.2⟩
  stuck := by
    intro j hj
    by_cases hji : j = i
    · exact ⟨c0, fun x hx => by rw [hji]; exact hx.2⟩
    · obtain ⟨d, hd⟩ := h.stuck j (fun hjF => hj ((List.mem_erase_of_ne hji).mpr hjF))
      exact ⟨d, fun x hx => hd x hx.1⟩
  nodup := h.nodup.erase i
  lt := fun j hj => h.lt j (List.mem_of_mem_erase hj)

/-- On the inputs in `P`, the output wire is the XOR of the free inputs, or its negation. -/
def ComputesXorOn (n : Nat) (N : List Node) (P : List Bool → Prop) (F : List Nat) : Prop :=
  ∃ c, ∀ x, P x → val N x (n + N.length - 1) = (xorOn F x != c)

theorem ComputesXorOn.congr {n : Nat} {N N' : List Node} {P : List Bool → Prop} {F : List Nat}
    (hX : ComputesXorOn n N P F) (hlen : N'.length = N.length)
    (hval : ∀ x, P x → ∀ w, val N' x w = val N x w) : ComputesXorOn n N' P F := by
  obtain ⟨c, hc⟩ := hX
  exact ⟨c, fun x hx => by rw [hlen, hval x hx]; exact hc x hx⟩

theorem ComputesXorOn.restrict {n : Nat} {N : List Node} {P : List Bool → Prop} {F : List Nat}
    (hX : ComputesXorOn n N P F) (hC : Cube n F P) {i : Nat} (hi : i ∈ F) (c0 : Bool) :
    ComputesXorOn n N (fixInput P i c0) (F.erase i) := by
  obtain ⟨c, hc⟩ := hX
  refine ⟨c0 != c, fun x hx => ?_⟩
  rw [hc x hx.1, xorOn_erase F x i hC.nodup hi, hx.2]
  cases c0 <;> cases xorOn (F.erase i) x <;> cases c <;> rfl

/-- Flip one free input and the output flips. -/
theorem output_moves {n : Nat} {N : List Node} {P : List Bool → Prop} {F : List Nat}
    (hC : Cube n F P) (hX : ComputesXorOn n N P F) {i : Nat} (hi : i ∈ F) {x : List Bool}
    (hx : P x) :
    val N (x.set i true) (n + N.length - 1) ≠ val N (x.set i false) (n + N.length - 1) := by
  obtain ⟨c, hc⟩ := hX
  have hl : i < x.length := by rw [hC.len x hx]; exact hC.lt i hi
  rw [hc _ (hC.free x hx i hi true), hc _ (hC.free x hx i hi false),
    xorOn_set F x i true hC.nodup hi hl, xorOn_set F x i false hC.nodup hi hl]
  cases xorOn (F.erase i) x <;> cases c <;> decide

theorem output_not_const {n : Nat} {N : List Node} {P : List Bool → Prop} {F : List Nat}
    (hC : Cube n F P) (hX : ComputesXorOn n N P F) {i : Nat} (hi : i ∈ F) {d : Bool}
    (hd : ∀ x, P x → val N x (n + N.length - 1) = d) : False := by
  obtain ⟨x, hx⟩ := hC.nonempty
  exact output_moves hC hX hi hx
    ((hd _ (hC.free x hx i hi true)).trans (hd _ (hC.free x hx i hi false)).symm)

theorem exists_ne_of_two {F : List Nat} (h : ¬F.length ≤ 1) (hnd : F.Nodup) (r : Nat) :
    ∃ i, i ∈ F ∧ i ≠ r := by
  match F, h, hnd with
  | [], h, _ => simp at h
  | [_], h, _ => simp at h
  | i1 :: i2 :: _, _, hnd =>
    by_cases h1 : i1 = r
    · refine ⟨i2, by simp, fun h2 => ?_⟩
      exact (List.nodup_cons.mp hnd).1 (by simp [h1, h2])
    · exact ⟨i1, by simp, h1⟩

/-- With two free inputs, the output is not a copy of one input. -/
theorem output_not_input_alias {n : Nat} {N : List Node} {P : List Bool → Prop} {F : List Nat}
    (hN : WF n N) (hC : Cube n F P) (hX : ComputesXorOn n N P F) (hF : ¬F.length ≤ 1)
    {s : Nat} {e : Bool} (hs : s < n) (hal : Alias n N s (n + N.length - 1) e) : False := by
  obtain ⟨i, hi, his⟩ := exists_ne_of_two hF hC.nodup s
  obtain ⟨x, hx⟩ := hC.nonempty
  have hl := hC.len x hx
  have hlen : ∀ b, (x.set i b).length = n := fun b => by rw [List.length_set]; exact hl
  apply output_moves hC hX hi hx
  rw [hal.val_eq hN _ (hlen true), hal.val_eq hN _ (hlen false),
    val_input N _ s (by rw [hlen]; exact hs), val_input N _ s (by rw [hlen]; exact hs),
    getD_set_ne his, getD_set_ne his]

end PNP

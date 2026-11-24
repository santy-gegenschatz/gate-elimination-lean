import PNP.Schnorr

/-!
# Schnorr's bound, stated for plain circuits

`and_gates_for_xor` talks about nodes of known shape. This file carries it back to `Circuit`, where
a gate is any function of two bits: if no gate is XOR or its negation, a circuit for the parity of
`n` inputs has at least `3 (n - 1)` gates.

The bridge is a table: each of the fourteen two-input functions that are not XOR or XNOR is one of
the shapes in `Kind`.
-/

namespace PNP

open Circuit

/-- The gate computes XOR or its negation. -/
def IsXorLike (op : Bool → Bool → Bool) : Prop :=
  (∀ a b, op a b = (a != b)) ∨ (∀ a b, op a b = (a == b))

/-- The shape of the gate whose outputs on `00, 01, 10, 11` are `p, q, r, s`. -/
def classify : Bool → Bool → Bool → Bool → Option Kind
  | false, false, false, false => some (.const false)
  | false, false, false, true => some (.and false false false)
  | false, false, true, false => some (.and false true false)
  | false, false, true, true => some (.copyL false)
  | false, true, false, false => some (.and true false false)
  | false, true, false, true => some (.copyR false)
  | false, true, true, false => none
  | false, true, true, true => some (.and true true true)
  | true, false, false, false => some (.and true true false)
  | true, false, false, true => none
  | true, false, true, false => some (.copyR true)
  | true, false, true, true => some (.and true false true)
  | true, true, false, false => some (.copyL true)
  | true, true, false, true => some (.and false true true)
  | true, true, true, false => some (.and false false true)
  | true, true, true, true => some (.const true)

theorem classify_some (p q r s : Bool) (k : Kind) (h : classify p q r s = some k) :
    k.op false false = p ∧ k.op false true = q ∧ k.op true false = r ∧ k.op true true = s := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp [classify] at h <;> subst h <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem classify_none (p q r s : Bool) (h : classify p q r s = none) :
    (p = false ∧ q = true ∧ r = true ∧ s = false) ∨
      (p = true ∧ q = false ∧ r = false ∧ s = true) := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp [classify] at h ⊢

/-- A gate that is not XOR or XNOR is an AND with NOTs, a copy, or a constant. -/
theorem exists_kind (op : Bool → Bool → Bool) (h : ¬IsXorLike op) : ∃ k : Kind, op = k.op := by
  cases hk : classify (op false false) (op false true) (op true false) (op true true) with
  | some k =>
    obtain ⟨h1, h2, h3, h4⟩ := classify_some _ _ _ _ k hk
    refine ⟨k, ?_⟩
    funext x y
    cases x <;> cases y
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
  | none =>
    exfalso
    apply h
    rcases classify_none _ _ _ _ hk with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      intro x y
      cases x <;> cases y <;> simp [h1, h2, h3, h4]
    · right
      intro x y
      cases x <;> cases y <;> simp [h1, h2, h3, h4]

theorem exists_nodes : ∀ gs : List Gate, (∀ g, g ∈ gs → ¬IsXorLike g.op) →
    ∃ N : List Node, N.map Node.toGate = gs
  | [], _ => ⟨[], rfl⟩
  | ⟨op, l, r⟩ :: gs, h => by
    obtain ⟨N, hN⟩ := exists_nodes gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨k, hk⟩ := exists_kind op (h ⟨op, l, r⟩ (by simp))
    refine ⟨⟨k, l, r⟩ :: N, ?_⟩
    show (⟨k.op, l, r⟩ : Gate) :: N.map Node.toGate = ⟨op, l, r⟩ :: gs
    rw [hN, hk]

theorem xorOn_map_succ (F : List Nat) (b : Bool) (bs : List Bool) :
    xorOn (F.map (· + 1)) (b :: bs) = xorOn F bs := by
  induction F with
  | nil => rfl
  | cons i F ih => simp [xorOn, ih]

/-- The XOR of all positions is `parity`. -/
theorem xorOn_range (x : List Bool) : xorOn (List.range x.length) x = parity x := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    show ((b :: bs).getD 0 false != xorOn ((List.range bs.length).map (· + 1)) (b :: bs)) =
      (b != parity bs)
    rw [xorOn_map_succ, ih]
    rfl

/-- No input fixed yet: every input of length `n` is allowed and every position is free. -/
theorem fullCube (n : Nat) : Cube n (List.range n) (fun x => x.length = n) where
  len := fun _ h => h
  nonempty := ⟨List.replicate n false, by simp⟩
  free := fun x hx _ _ _ => by simp [hx]
  stuck := fun i hi => ⟨false, fun x hx => by
    have hle : x.length ≤ i := by
      have : ¬i < n := fun h => hi (List.mem_range.mpr h)
      omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]⟩
  nodup := List.nodup_range
  lt := fun _ hi => List.mem_range.mp hi

/-- **Schnorr's bound.** A circuit with no XOR and no XNOR gate that computes the parity of its
inputs has at least three gates for every input after the first. -/
theorem xor_needs_three_gates_per_input (c : Circuit)
    (hbasis : ∀ g, g ∈ c.gates → ¬IsXorLike g.op) (hc : c.Computes parity) :
    3 * (c.inputs - 1) ≤ c.size := by
  obtain ⟨n, gates⟩ := c
  obtain ⟨N, rfl⟩ := exists_nodes gates hbasis
  obtain ⟨hwf, hval⟩ := hc
  have hN : WF n N := by
    intro t nd h
    obtain ⟨ht, rfl⟩ := List.getElem?_eq_some_iff.mp h
    have key := hwf t (by rw [List.length_map]; exact ht)
    rw [List.getElem_map] at key
    exact key
  have hX : ComputesXorOn n N (fun x => x.length = n) (List.range n) := by
    refine ⟨false, fun x hx => ?_⟩
    have key : ((N.map Node.toGate).foldl fire x).getLastD false = parity x := hval x hx
    rw [getLastD_eq_getD, length_foldl_fire, List.length_map, hx] at key
    have hx' : x.length = n := hx
    rw [← hx', xorOn_range, Bool.bne_false, hx']
    exact key
  have hbound := and_gates_for_xor n (cost N) N rfl hN _ _ (fullCube n) hX
  have hcost := cost_le_length N
  rw [List.length_range] at hbound
  show 3 * (n - 1) ≤ (N.map Node.toGate).length
  rw [List.length_map]
  omega

end PNP

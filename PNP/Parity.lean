import PNP.Reads

/-!
# Parity needs exactly `n - 1` gates

Over the full binary basis, the XOR of `n` inputs is computed by a chain of `n - 1` XOR gates, and
by `needs_gates_of_depends_on_all` nothing smaller works. Folklore, here as the first exact
circuit complexity in the folder.
-/

namespace PNP

open Circuit

/-- `true` when an odd number of inputs are `true`. -/
def parity : List Bool → Bool
  | [] => false
  | b :: bs => b != parity bs

theorem parity_replicate_false (n : Nat) : parity (List.replicate n false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, parity, ih]

theorem parity_one_true : ∀ (n i : Nat), i < n →
    parity ((List.replicate n false).set i true) = true
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => by simp [List.replicate_succ, parity, parity_replicate_false]
  | n + 1, i + 1, h => by
    simp [List.replicate_succ, parity, parity_one_true n i (by omega)]

theorem parity_depends_on_all (n i : Nat) (h : i < n) : DependsOn n parity i := by
  refine ⟨List.replicate n false, (List.replicate n false).set i true, by simp, by simp, ?_, ?_⟩
  · intro j hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
  · rw [parity_replicate_false, parity_one_true n i h]
    decide

/-- The lower bound: every circuit for parity on `n` inputs has at least `n - 1` gates. -/
theorem parity_needs_gates (n : Nat) : NeedsGates n parity (n - 1) :=
  needs_gates_of_depends_on_all n parity (parity_depends_on_all n)

theorem parity_append_singleton (l : List Bool) (b : Bool) :
    parity (l ++ [b]) = (parity l != b) := by
  induction l with
  | nil => cases b <;> rfl
  | cons a l ih =>
    simp only [List.cons_append, parity, ih]
    cases a <;> cases parity l <;> cases b <;> rfl

theorem parity_take_succ (x : List Bool) (j : Nat) (h : j < x.length) :
    parity (x.take (j + 1)) = (parity (x.take j) != x.getD j false) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, parity_append_singleton,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- Gate `k` of the chain XORs the running total with input `k + 1`. -/
def chainGate (n k : Nat) : Gate :=
  { op := fun a b => a != b, left := if k = 0 then 0 else n + k - 1, right := k + 1 }

/-- The obvious circuit for parity: `n - 1` XOR gates in a row. -/
def xorChain (n : Nat) : Circuit :=
  { inputs := n, gates := (List.range (n - 1)).map (chainGate n) }

/-- After `k` gates of the chain, the new wires hold the parities of the first 2, 3, … inputs. -/
theorem chain_wires (x : List Bool) (k : Nat) (hk : k + 1 ≤ x.length) :
    ((List.range k).map (chainGate x.length)).foldl fire x
      = x ++ (List.range k).map (fun j => parity (x.take (j + 2))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append, ih, List.map_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, fire, chainGate,
      List.append_assoc]
    congr 2
    have hr : (x ++ (List.range k).map (fun j => parity (x.take (j + 2)))).getD (k + 1) false
        = x.getD (k + 1) false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, show k + 1 < x.length by omega]
    rw [hr, parity_take_succ x (k + 1) (by omega)]
    congr 1
    by_cases h0 : k = 0
    · subst h0
      simp [List.getD_eq_getElem?_getD, show 0 < x.length by omega, List.take_add_one, parity]
    · have hpos : x.length + k - 1 - x.length = k - 1 := by omega
      have hlt : ¬ x.length + k - 1 < x.length := by omega
      have hk1 : k - 1 < k := by omega
      have hk2 : k - 1 + 2 = k + 1 := by omega
      simp [h0, List.getD_eq_getElem?_getD, List.getElem?_append, hlt, hpos, hk1, hk2]

theorem xorChain_computes_parity (n : Nat) : (xorChain n).Computes parity := by
  constructor
  · intro i h
    have hi : i < n - 1 := by simpa [xorChain] using h
    simp only [xorChain, List.getElem_map, List.getElem_range, chainGate]
    by_cases h0 : i = 0
    · simp [h0]; omega
    · simp [h0]; omega
  · intro x hx
    have hx' : x.length = n := hx
    show ((xorChain n).gates.foldl fire x).getLastD false = parity x
    by_cases hn : n ≤ 1
    · have : n - 1 = 0 := by omega
      simp only [xorChain, this, List.range_zero, List.map_nil, List.foldl_nil]
      match x, hx' with
      | [], _ => rfl
      | [a], _ => cases a <;> rfl
      | _ :: _ :: _, h => simp at h; omega
    · have hw := chain_wires x (n - 1) (by omega)
      rw [hx'] at hw
      simp only [xorChain]
      rw [hw, getLastD_eq_getD]
      have hlen : (x ++ (List.range (n - 1)).map (fun j => parity (x.take (j + 2)))).length - 1
          = x.length + (n - 2) := by simp; omega
      rw [hlen]
      have h2 : n - 2 < n - 1 := by omega
      have h3 : n - 2 + 2 = x.length := by omega
      simp [List.getD_eq_getElem?_getD, h2, h3]

/-- Exact circuit complexity of parity over the full binary basis: `n - 1` gates. -/
theorem parity_exact (n : Nat) :
    NeedsGates n parity (n - 1) ∧
      ∃ c : Circuit, c.inputs = n ∧ c.Computes parity ∧ c.size = n - 1 :=
  ⟨parity_needs_gates n, xorChain n, rfl, xorChain_computes_parity n, by simp [Circuit.size, xorChain]⟩

end PNP

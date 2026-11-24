import PNP.NoXor

/-!
# Three gates per input are enough

The matching circuit for Schnorr's bound: build each XOR from two ANDs and an OR,
`x XOR y = (x AND NOT y) OR (NOT x AND y)`, and chain them. That is `3 (n - 1)` gates and none of
them is XOR or XNOR. With `xor_needs_three_gates_per_input` this makes the count exact.
-/

namespace PNP

open Circuit

def andNot (p y : Nat) : Gate := ⟨fun a b => a && !b, p, y⟩
def notAnd (p y : Nat) : Gate := ⟨fun a b => !a && b, p, y⟩
def orGate (m : Nat) : Gate := ⟨fun a b => a || b, m, m + 1⟩

/-- The wire that holds the XOR of the first `k + 1` inputs. -/
def running (n k : Nat) : Nat := if k = 0 then 0 else n + 3 * k - 1

/-- The first `k` XOR steps, three gates each. -/
def andChainGates (n : Nat) : Nat → List Gate
  | 0 => []
  | k + 1 => andChainGates n k ++
      [andNot (running n k) (k + 1), notAnd (running n k) (k + 1), orGate (n + 3 * k)]

/-- Parity of `n` inputs from `3 (n - 1)` gates, none of them XOR. -/
def andChain (n : Nat) : Circuit := ⟨n, andChainGates n (n - 1)⟩

theorem andChainGates_length (n : Nat) : ∀ k, (andChainGates n k).length = 3 * k
  | 0 => rfl
  | k + 1 => by
    simp only [andChainGates, List.length_append, andChainGates_length n k, List.length_cons,
      List.length_nil]
    omega

theorem andChainGates_no_xor (n : Nat) : ∀ k g, g ∈ andChainGates n k → ¬IsXorLike g.op
  | 0, g, h => by simp [andChainGates] at h
  | k + 1, g, h => by
    simp only [andChainGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact andChainGates_no_xor n k g h
    · subst h
      rintro (h | h)
      · exact absurd (h false true) (by simp [andNot])
      · exact absurd (h false false) (by simp [andNot])
    · subst h
      rintro (h | h)
      · exact absurd (h true false) (by simp [notAnd])
      · exact absurd (h false false) (by simp [notAnd])
    · subst h
      rintro (h | h)
      · exact absurd (h true true) (by simp [orGate])
      · exact absurd (h true false) (by simp [orGate])

theorem andChainGates_wellFormed (n : Nat) : ∀ k, k + 1 ≤ n ∨ k = 0 →
    ∀ (t : Nat) (g : Gate), (andChainGates n k)[t]? = some g → g.left < n + t ∧ g.right < n + t
  | 0, _, t, g, h => by simp [andChainGates] at h
  | k + 1, hk, t, g, h => by
    have hk' : k + 2 ≤ n := by omega
    simp only [andChainGates, List.getElem?_append, andChainGates_length] at h
    split at h
    · exact andChainGates_wellFormed n k (Or.inl (by omega)) t g h
    · have hrun : running n k < n + 3 * k := by unfold running; split <;> omega
      have ht : t = 3 * k + (t - 3 * k) := by omega
      generalize t - 3 * k = j at h ht
      subst ht
      match j, h with
      | 0, h =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨by show running n k < _; omega, by show k + 1 < _; omega⟩
      | 1, h =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨by show running n k < _; omega, by show k + 1 < _; omega⟩
      | 2, h =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨by show n + 3 * k < _; omega, by show n + 3 * k + 1 < _; omega⟩
      | j + 3, h => simp at h

/-- After `k` steps the running wire holds the XOR of the first `k + 1` inputs. -/
theorem andChain_wires (x : List Bool) : ∀ k, k + 1 ≤ x.length →
    ((andChainGates x.length k).foldl fire x).getD (running x.length k) false =
      parity (x.take (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro h
    have := parity_take_succ x 0 h
    simp [andChainGates, running, this, parity]
  | succ k ih =>
    intro h
    have ihk := ih (by omega)
    have hW : ((andChainGates x.length k).foldl fire x).length = x.length + 3 * k := by
      rw [length_foldl_fire, andChainGates_length]
    have hy : ((andChainGates x.length k).foldl fire x).getD (k + 1) false = x.getD (k + 1) false :=
      getD_foldl_fire_of_lt _ x (k + 1) (by omega)
    have hrun : running x.length k < x.length + 3 * k := by unfold running; split <;> omega
    have hnew : running x.length (k + 1) = x.length + 3 * k + 2 := by
      simp only [running, Nat.add_one_ne_zero, ↓reduceIte]
      omega
    rw [parity_take_succ x (k + 1) (by omega), ← ihk, ← hy, hnew]
    simp only [andChainGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (andChainGates x.length k).foldl fire x = W at hW
    have hk1 : k + 1 < W.length := by omega
    have hr : running x.length k < W.length := by omega
    rw [← hW]
    simp only [getD_fire, length_fire, andNot, notAnd, orGate, hk1, hr, ↓reduceIte]
    simp
    cases W[running x.length k]?.getD false <;> cases W[k + 1]?.getD false <;> rfl

theorem andChain_computes_parity (n : Nat) : (andChain n).Computes parity := by
  constructor
  · intro t ht
    exact andChainGates_wellFormed n (n - 1) (by omega) t _ (List.getElem?_eq_getElem ht)
  · intro x hx
    have hx' : x.length = n := hx
    subst hx'
    show ((andChainGates x.length (x.length - 1)).foldl fire x).getLastD false = parity x
    rw [getLastD_eq_getD, length_foldl_fire, andChainGates_length]
    match x with
    | [] => rfl
    | [b] => cases b <;> rfl
    | b :: b' :: bs =>
      have key := andChain_wires (b :: b' :: bs) ((b :: b' :: bs).length - 1) (by simp)
      have hrun : running (b :: b' :: bs).length ((b :: b' :: bs).length - 1) =
          (b :: b' :: bs).length + 3 * ((b :: b' :: bs).length - 1) - 1 := by
        simp [running]
      rw [hrun] at key
      rw [key]
      simp

/-- **Exact count.** Without XOR and XNOR gates, the parity of `n` inputs needs `3 (n - 1)` gates
and no fewer. -/
theorem parity_exact_without_xor (n : Nat) :
    (∀ c : Circuit, c.inputs = n → (∀ g, g ∈ c.gates → ¬IsXorLike g.op) → c.Computes parity →
        3 * (n - 1) ≤ c.size) ∧
      ∃ c : Circuit, c.inputs = n ∧ (∀ g, g ∈ c.gates → ¬IsXorLike g.op) ∧ c.Computes parity ∧
        c.size = 3 * (n - 1) :=
  ⟨fun c hn hbasis hc => hn ▸ xor_needs_three_gates_per_input c hbasis hc,
    andChain n, rfl, andChainGates_no_xor n (n - 1), andChain_computes_parity n,
    andChainGates_length n (n - 1)⟩

end PNP

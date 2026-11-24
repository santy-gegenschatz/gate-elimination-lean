import PNP.Parity

/-!
# Circuits without XOR gates

Forbid XOR and its negation, and every two-input gate that is left is an AND with optional NOTs on
its wires, a copy of one input, or a constant. This file names those shapes (`Kind`), gives the
value of every wire as a function (`val`), and proves the two equations that all later proofs use:
an input wire carries its input, and a gate wire carries its gate applied to the two wires it
reads. After this file nobody has to look at `foldl` again.

Only AND gates are counted (`cost`). Copies and constants are free, which makes the lower bound
stronger and lets a proof switch a gate off without renumbering the wires behind it.
-/

namespace PNP

open Circuit

/-- What a gate can be once XOR is forbidden. -/
inductive Kind where
  /-- `((x != a) && (y != b)) != c`: an AND with a NOT on any of its three wires. -/
  | and (a b c : Bool)
  /-- The left input, flipped when `e` is true. -/
  | copyL (e : Bool)
  /-- The right input, flipped when `e` is true. -/
  | copyR (e : Bool)
  | const (d : Bool)

namespace Kind

def op : Kind → Bool → Bool → Bool
  | and a b c, x, y => ((x != a) && (y != b)) != c
  | copyL e, x, _ => x != e
  | copyR e, _, y => y != e
  | const d, _, _ => d

/-- Only AND gates are paid for. -/
def costs : Kind → Bool
  | and _ _ _ => true
  | _ => false

end Kind

/-- A gate of known shape, reading two earlier wires. -/
structure Node where
  kind : Kind
  left : Nat
  right : Nat

def Node.toGate (nd : Node) : Gate := ⟨nd.kind.op, nd.left, nd.right⟩

/-- The value on wire `w` when the circuit with nodes `N` runs on input `x`. -/
def val (N : List Node) (x : List Bool) (w : Nat) : Bool :=
  ((N.map Node.toGate).foldl fire x).getD w false

/-- Every node reads wires that already exist. -/
def WF (n : Nat) (N : List Node) : Prop :=
  ∀ (t : Nat) (nd : Node), N[t]? = some nd → nd.left < n + t ∧ nd.right < n + t

/-- The number of AND gates. -/
def cost : List Node → Nat
  | [] => 0
  | nd :: N => (if nd.kind.costs then 1 else 0) + cost N

theorem cost_le_length : ∀ N : List Node, cost N ≤ N.length
  | [] => Nat.le_refl 0
  | nd :: N => by
    have := cost_le_length N
    simp only [cost, List.length_cons]
    split <;> omega

/-! ## Running a circuit, one gate at a time -/

theorem length_fire (w : List Bool) (g : Gate) : (fire w g).length = w.length + 1 := by
  simp [fire]

theorem length_foldl_fire (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl fire w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g rest ih =>
    intro w
    rw [List.foldl_cons, ih, length_fire, List.length_cons]
    omega

/-- Later gates never change a wire that already exists. -/
theorem getD_foldl_fire_of_lt (gs : List Gate) : ∀ (w : List Bool) (j : Nat), j < w.length →
    (gs.foldl fire w).getD j false = w.getD j false := by
  induction gs with
  | nil => intro w j _; rfl
  | cons g rest ih =>
    intro w j hj
    rw [List.foldl_cons, ih (fire w g) j (by rw [length_fire]; omega), getD_fire]
    simp only [hj, ↓reduceIte]

theorem getD_foldl_fire_gate (gs : List Gate) : ∀ (w : List Bool) (t : Nat) (h : t < gs.length),
    gs[t].left < w.length + t → gs[t].right < w.length + t →
    (gs.foldl fire w).getD (w.length + t) false =
      gs[t].op ((gs.foldl fire w).getD gs[t].left false)
        ((gs.foldl fire w).getD gs[t].right false) := by
  induction gs with
  | nil => intro w t h; exact absurd h (Nat.not_lt_zero _)
  | cons g rest ih =>
    intro w t h hl hr
    rw [List.foldl_cons]
    cases t with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hl hr ⊢
      rw [getD_foldl_fire_of_lt rest (fire w g) w.length (by rw [length_fire]; omega),
        getD_foldl_fire_of_lt rest (fire w g) g.left (by rw [length_fire]; omega),
        getD_foldl_fire_of_lt rest (fire w g) g.right (by rw [length_fire]; omega)]
      simp only [getD_fire, Nat.lt_irrefl, ↓reduceIte, hl, hr]
    | succ t =>
      simp only [List.getElem_cons_succ] at hl hr ⊢
      have key := ih (fire w g) t (by simpa using h) (by rw [length_fire]; omega)
        (by rw [length_fire]; omega)
      rw [length_fire] at key
      rw [show w.length + (t + 1) = w.length + 1 + t by omega]
      exact key

/-! ## The two wire equations -/

theorem val_input (N : List Node) (x : List Bool) (w : Nat) (h : w < x.length) :
    val N x w = x.getD w false :=
  getD_foldl_fire_of_lt _ x w h

theorem val_beyond (N : List Node) (x : List Bool) (w : Nat) (h : x.length + N.length ≤ w) :
    val N x w = false := by
  unfold val
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [length_foldl_fire, List.length_map]; exact h)]
  rfl

theorem val_node {n : Nat} {N : List Node} (hN : WF n N) {x : List Bool} (hx : x.length = n)
    {t : Nat} {k : Kind} {l r : Nat} (h : N[t]? = some ⟨k, l, r⟩) :
    val N x (n + t) = k.op (val N x l) (val N x r) := by
  subst hx
  have hlr : l < x.length + t ∧ r < x.length + t := hN t _ h
  obtain ⟨ht, hnd⟩ := List.getElem?_eq_some_iff.mp h
  have ht' : t < (N.map Node.toGate).length := by rw [List.length_map]; exact ht
  have hg : (N.map Node.toGate)[t] = ⟨k.op, l, r⟩ := by rw [List.getElem_map, hnd]; rfl
  have key := getD_foldl_fire_gate (N.map Node.toGate) x t ht'
    (by rw [hg]; exact hlr.1) (by rw [hg]; exact hlr.2)
  rw [hg] at key
  exact key

/-! ## Swapping one node -/

theorem WF.set {n : Nat} {N : List Node} (hN : WF n N) {t : Nat} {k : Kind} {l r : Nat}
    (hnode : N[t]? = some ⟨k, l, r⟩) (k' : Kind) : WF n (N.set t ⟨k', l, r⟩) := by
  intro t0 nd h0
  by_cases h : t = t0
  · subst h
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hnode).1] at h0
    injection h0 with h0
    subst h0
    have hlr : l < n + t ∧ r < n + t := hN t _ hnode
    exact hlr
  · rw [List.getElem?_set_ne h] at h0
    exact hN t0 nd h0

/-- Trading an AND gate for a free node saves exactly one. -/
theorem cost_set : ∀ (N : List Node) (t : Nat) (nd nd' : Node), N[t]? = some nd →
    nd.kind.costs = true → nd'.kind.costs = false → cost (N.set t nd') + 1 = cost N
  | [], _, _, _, h, _, _ => by simp at h
  | m :: N, 0, nd, nd', h, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [cost, h1, h2]
    omega
  | m :: N, t + 1, nd, nd', h, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h
    have := cost_set N t nd nd' h h1 h2
    simp only [List.set_cons_succ, cost]
    omega

end PNP

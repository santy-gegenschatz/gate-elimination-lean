import PNP.NoXor

/-!
# The full binary basis, with free copies

The same setup as `AndBasis`, with every two-input function allowed as a gate, XOR included. A
node is a gate, a copy of one wire, or a constant. Gates are counted; copies and constants are
free, so a proof can switch a gate off by overwriting its node and no wire changes number.

A gate with one wire stuck is a function of its other wire: a copy or a constant. That is all
the full basis gives a gate elimination proof, and it is what `ofLeft` and `ofRight` say.
-/

namespace PNP.Full

open Circuit

inductive Shape where
  | gate (op : Bool → Bool → Bool)
  /-- The left wire, flipped when `e` is true. -/
  | copyL (e : Bool)
  /-- The right wire, flipped when `e` is true. -/
  | copyR (e : Bool)
  | const (d : Bool)

namespace Shape

def op : Shape → Bool → Bool → Bool
  | gate f, x, y => f x y
  | copyL e, x, _ => x != e
  | copyR e, _, y => y != e
  | const d, _, _ => d

/-- Only gates are paid for. -/
def costs : Shape → Bool
  | gate _ => true
  | _ => false

/-- A function of the left wire alone, as a free node. -/
def ofLeft (u : Bool → Bool) : Shape :=
  if u false = u true then const (u false) else copyL (u false)

/-- A function of the right wire alone, as a free node. -/
def ofRight (u : Bool → Bool) : Shape :=
  if u false = u true then const (u false) else copyR (u false)

theorem ofLeft_costs (u : Bool → Bool) : (ofLeft u).costs = false := by
  unfold ofLeft
  split <;> rfl

theorem ofRight_costs (u : Bool → Bool) : (ofRight u).costs = false := by
  unfold ofRight
  split <;> rfl

theorem ofLeft_op (u : Bool → Bool) (x y : Bool) : (ofLeft u).op x y = u x := by
  unfold ofLeft
  cases hf : u false <;> cases ht : u true <;> cases x <;> simp [op, hf, ht]

theorem ofRight_op (u : Bool → Bool) (x y : Bool) : (ofRight u).op x y = u y := by
  unfold ofRight
  cases hf : u false <;> cases ht : u true <;> cases y <;> simp [op, hf, ht]

end Shape

structure Node where
  shape : Shape
  left : Nat
  right : Nat

def Node.toGate (nd : Node) : Gate := ⟨nd.shape.op, nd.left, nd.right⟩

/-- The value on wire `w` when the circuit with nodes `N` runs on input `x`. -/
def val (N : List Node) (x : List Bool) (w : Nat) : Bool :=
  ((N.map Node.toGate).foldl fire x).getD w false

/-- Every node reads wires that already exist. -/
def WF (n : Nat) (N : List Node) : Prop :=
  ∀ (t : Nat) (nd : Node), N[t]? = some nd → nd.left < n + t ∧ nd.right < n + t

/-- The number of gates. -/
def cost : List Node → Nat
  | [] => 0
  | nd :: N => (if nd.shape.costs then 1 else 0) + cost N

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
    {t : Nat} {k : Shape} {l r : Nat} (h : N[t]? = some ⟨k, l, r⟩) :
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

/-! ## Overwriting one node -/

theorem WF.set {n : Nat} {N : List Node} (hN : WF n N) {t : Nat} {k : Shape} {l r : Nat}
    (hnode : N[t]? = some ⟨k, l, r⟩) (k' : Shape) : WF n (N.set t ⟨k', l, r⟩) := by
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

/-- Trading a gate for a free node saves exactly one. -/
theorem cost_set : ∀ (N : List Node) (t : Nat) (nd nd' : Node), N[t]? = some nd →
    nd.shape.costs = true → nd'.shape.costs = false → cost (N.set t nd') + 1 = cost N
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

/-- Overwrite a node by one that does the same thing on every input in `P`: no wire notices. -/
theorem val_set_shape {n : Nat} {N : List Node} (hN : WF n N) {P : List Bool → Prop}
    (hP : ∀ x, P x → x.length = n) {t : Nat} {k : Shape} {l r : Nat} (k' : Shape)
    (hnode : N[t]? = some ⟨k, l, r⟩)
    (hsame : ∀ x, P x → k'.op (val N x l) (val N x r) = k.op (val N x l) (val N x r)) :
    ∀ x, P x → ∀ w, val (N.set t ⟨k', l, r⟩) x w = val N x w := by
  intro x hx w
  have hxl := hP x hx
  have hN' := hN.set hnode k'
  have htl : t < N.length := (List.getElem?_eq_some_iff.mp hnode).1
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases h1 : w < n
    · rw [val_input _ x w (by omega), val_input _ x w (by omega)]
    by_cases h2 : n + N.length ≤ w
    · rw [val_beyond _ x w (by rw [List.length_set]; omega), val_beyond _ x w (by omega)]
    have hwt : w = n + (w - n) := by omega
    by_cases h3 : w - n = t
    · have hlr : l < n + t ∧ r < n + t := hN t _ hnode
      have hnode' : (N.set t ⟨k', l, r⟩)[t]? = some ⟨k', l, r⟩ := List.getElem?_set_self htl
      rw [hwt, h3, val_node hN' hxl hnode', val_node hN hxl hnode, ih l (by omega),
        ih r (by omega)]
      exact hsame x hx
    · have ht : w - n < N.length := by omega
      have hnode0 : N[w - n]? = some N[w - n] := List.getElem?_eq_getElem ht
      generalize N[w - n] = nd at hnode0
      obtain ⟨k0, l0, r0⟩ := nd
      have hlr : l0 < n + (w - n) ∧ r0 < n + (w - n) := hN _ _ hnode0
      have hnode' : (N.set t ⟨k', l, r⟩)[w - n]? = some ⟨k0, l0, r0⟩ :=
        (List.getElem?_set_ne (Ne.symm h3)).trans hnode0
      rw [hwt, val_node hN' hxl hnode', val_node hN hxl hnode0, ih l0 (by omega),
        ih r0 (by omega)]

/-- Trade a gate for a free node that agrees with it on `P`. -/
theorem simplify {n : Nat} {N : List Node} (hN : WF n N) {P : List Bool → Prop}
    (hP : ∀ x, P x → x.length = n) {t : Nat} {f : Bool → Bool → Bool} {l r : Nat}
    (hnode : N[t]? = some ⟨Shape.gate f, l, r⟩) (k' : Shape) (hk' : k'.costs = false)
    (hsame : ∀ x, P x → k'.op (val N x l) (val N x r) = f (val N x l) (val N x r)) :
    ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 1 = cost N ∧
      (∀ x, P x → ∀ w, val N' x w = val N x w) ∧ ∀ t', t' ≠ t → N'[t']? = N[t']? :=
  ⟨N.set t ⟨k', l, r⟩, hN.set hnode k', List.length_set, cost_set N t _ _ hnode rfl hk',
    val_set_shape hN hP k' hnode hsame, fun _ h => List.getElem?_set_ne (Ne.symm h)⟩

/-- A circuit with a gate in it costs something. -/
theorem cost_pos {N : List Node} {t : Nat} {f : Bool → Bool → Bool} {l r : Nat}
    (hnode : N[t]? = some ⟨Shape.gate f, l, r⟩) : 1 ≤ cost N := by
  have := cost_set N t _ ⟨Shape.const false, l, r⟩ hnode rfl rfl
  omega

/-! ## From plain circuits -/

def lift (g : Gate) : Node := ⟨Shape.gate g.op, g.left, g.right⟩

theorem lift_toGate : ∀ gs : List Gate, (gs.map lift).map Node.toGate = gs
  | [] => rfl
  | g :: gs => by
    show (lift g).toGate :: (gs.map lift).map Node.toGate = g :: gs
    rw [lift_toGate gs]
    rfl

/-- Every gate of a plain circuit is counted. -/
theorem cost_lift : ∀ gs : List Gate, cost (gs.map lift) = gs.length
  | [] => rfl
  | g :: gs => by
    show 1 + cost (gs.map lift) = (g :: gs).length
    rw [cost_lift gs, List.length_cons]
    omega

end PNP.Full

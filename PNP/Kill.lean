import PNP.Alias

/-!
# Switching gates off

Gate elimination without removing anything. An AND gate with a stuck input is a copy or a
constant, so its node can be swapped for a free one. No wire changes value and no wire changes
number; the circuit just costs one less.

Everything is said about the inputs in a set `P`, because the main proof fixes inputs one at a
time and only cares about the inputs that are still allowed.
-/

namespace PNP

/-- Swap a node for one that does the same thing on every input in `P`: no wire notices. -/
theorem val_set_kind {n : Nat} {N : List Node} (hN : WF n N) {P : List Bool → Prop}
    (hP : ∀ x, P x → x.length = n) {t : Nat} {k : Kind} {l r : Nat} (k' : Kind)
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

/-- Trade an AND gate for a free node that agrees with it on `P`. -/
theorem simplify {n : Nat} {N : List Node} (hN : WF n N) {P : List Bool → Prop}
    (hP : ∀ x, P x → x.length = n) {t : Nat} {a b c : Bool} {l r : Nat}
    (hnode : N[t]? = some ⟨Kind.and a b c, l, r⟩) (k' : Kind) (hk' : k'.costs = false)
    (hsame : ∀ x, P x →
      k'.op (val N x l) (val N x r) = (Kind.and a b c).op (val N x l) (val N x r)) :
    ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 1 = cost N ∧
      (∀ x, P x → ∀ w, val N' x w = val N x w) ∧ ∀ t', t' ≠ t → N'[t']? = N[t']? :=
  ⟨N.set t ⟨k', l, r⟩, hN.set hnode k', List.length_set, cost_set N t _ _ hnode rfl hk',
    val_set_kind hN hP k' hnode hsame, fun _ h => List.getElem?_set_ne (Ne.symm h)⟩

namespace Kind

/-- What an AND gate is when its left input is stuck at `d`. -/
def fixLeft (a b c d : Bool) : Kind :=
  match d != a with
  | true => copyR (b != c)
  | false => const c

/-- What an AND gate is when its right input is stuck at `d`. -/
def fixRight (a b c d : Bool) : Kind :=
  match d != b with
  | true => copyL (a != c)
  | false => const c

/-- What an AND gate is when both inputs are the same wire `v`, flipped by `e1` and by `e2`. -/
def merge (a b c e1 e2 : Bool) : Kind :=
  match (e1 != a) != (e2 != b) with
  | false => copyL (a != c)
  | true => const c

theorem fixLeft_costs (a b c d : Bool) : (fixLeft a b c d).costs = false := by
  cases a <;> cases d <;> rfl

theorem fixLeft_op (a b c d y : Bool) : (fixLeft a b c d).op d y = (and a b c).op d y := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases y <;> rfl

theorem fixRight_costs (a b c d : Bool) : (fixRight a b c d).costs = false := by
  cases b <;> cases d <;> rfl

theorem fixRight_op (a b c d x : Bool) : (fixRight a b c d).op x d = (and a b c).op x d := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> rfl

theorem merge_costs (a b c e1 e2 : Bool) : (merge a b c e1 e2).costs = false := by
  cases a <;> cases b <;> cases e1 <;> cases e2 <;> rfl

theorem merge_op (a b c e1 e2 v : Bool) :
    (merge a b c e1 e2).op (v != e1) (v != e2) = (and a b c).op (v != e1) (v != e2) := by
  cases a <;> cases b <;> cases c <;> cases e1 <;> cases e2 <;> cases v <;> rfl

end Kind

/-- An AND gate with an input that is constant on `P`. -/
def Dead (N : List Node) (P : List Bool → Prop) (t : Nat) : Prop :=
  ∃ (a b c : Bool) (l r : Nat), N[t]? = some ⟨Kind.and a b c, l, r⟩ ∧
    ((∃ d, ∀ x, P x → val N x l = d) ∨ (∃ d, ∀ x, P x → val N x r = d))

/-- A gate that reads a copy of a stuck wire is dead. -/
theorem dead_of_alias {n : Nat} {N : List Node} {P : List Bool → Prop} (hN : WF n N)
    (hP : ∀ x, P x → x.length = n) {t : Nat} {a b c : Bool} {l r s : Nat} {d : Bool}
    (hnode : N[t]? = some ⟨Kind.and a b c, l, r⟩)
    (hal : (∃ e, Alias n N s l e) ∨ (∃ e, Alias n N s r e))
    (hs : ∀ x, P x → val N x s = d) : Dead N P t := by
  refine ⟨a, b, c, l, r, hnode, ?_⟩
  rcases hal with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d != e, fun x hx => by rw [he.val_eq hN x (hP x hx), hs x hx]⟩
  · exact Or.inr ⟨d != e, fun x hx => by rw [he.val_eq hN x (hP x hx), hs x hx]⟩

theorem Dead.congr {N N' : List Node} {P : List Bool → Prop} {t : Nat} (hd : Dead N P t)
    (hnode : N'[t]? = N[t]?) (hval : ∀ x, P x → ∀ w, val N' x w = val N x w) : Dead N' P t := by
  obtain ⟨a, b, c, l, r, hn, h⟩ := hd
  refine ⟨a, b, c, l, r, hnode.trans hn, ?_⟩
  rcases h with ⟨d, hd⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨d, fun x hx => (hval x hx l).trans (hd x hx)⟩
  · exact Or.inr ⟨d, fun x hx => (hval x hx r).trans (hd x hx)⟩

theorem kill_one {n : Nat} {N : List Node} {P : List Bool → Prop} (hN : WF n N)
    (hP : ∀ x, P x → x.length = n) {t : Nat} (hd : Dead N P t) :
    ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 1 = cost N ∧
      (∀ x, P x → ∀ w, val N' x w = val N x w) ∧ ∀ t', t' ≠ t → N'[t']? = N[t']? := by
  obtain ⟨a, b, c, l, r, hnode, ⟨d, hd⟩ | ⟨d, hd⟩⟩ := hd
  · exact simplify hN hP hnode (Kind.fixLeft a b c d) (Kind.fixLeft_costs a b c d)
      (fun x hx => by rw [hd x hx]; exact Kind.fixLeft_op a b c d _)
  · exact simplify hN hP hnode (Kind.fixRight a b c d) (Kind.fixRight_costs a b c d)
      (fun x hx => by rw [hd x hx]; exact Kind.fixRight_op a b c d _)

/-- Three dead gates: the same circuit on `P`, three AND gates cheaper. -/
theorem kill_three {n : Nat} {N : List Node} {P : List Bool → Prop} (hN : WF n N)
    (hP : ∀ x, P x → x.length = n) {t1 t2 t3 : Nat} (h12 : t1 ≠ t2) (h13 : t1 ≠ t3)
    (h23 : t2 ≠ t3) (d1 : Dead N P t1) (d2 : Dead N P t2) (d3 : Dead N P t3) :
    ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 3 = cost N ∧
      ∀ x, P x → ∀ w, val N' x w = val N x w := by
  obtain ⟨N1, w1, l1, c1, v1, s1⟩ := kill_one hN hP d1
  have d2' := d2.congr (s1 t2 (Ne.symm h12)) v1
  have d3' := d3.congr (s1 t3 (Ne.symm h13)) v1
  obtain ⟨N2, w2, l2, c2, v2, s2⟩ := kill_one w1 hP d2'
  have d3'' := d3'.congr (s2 t3 (Ne.symm h23)) v2
  obtain ⟨N3, w3, l3, c3, v3, _⟩ := kill_one w2 hP d3''
  exact ⟨N3, w3, by omega, by omega, fun x hx w => by rw [v3 x hx, v2 x hx, v1 x hx]⟩

end PNP

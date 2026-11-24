import PNP.FullBasis

/-!
# Copies and dead gates over the full basis

`Alias s w e`: wire `w` is wire `s` seen through a chain of copy nodes, flipped when `e` is true.
`flow`: a change at some wires can only travel through the gates that read a copy of one of them.
`Dead`: a gate with a wire that is constant on the allowed inputs; it can be overwritten for free.
-/

namespace PNP.Full

inductive Alias (n : Nat) (N : List Node) (s : Nat) : Nat → Bool → Prop where
  | self : Alias n N s s false
  | left {t l r : Nat} {e e' : Bool} : N[t]? = some ⟨Shape.copyL e, l, r⟩ → Alias n N s l e' →
      Alias n N s (n + t) (e' != e)
  | right {t l r : Nat} {e e' : Bool} : N[t]? = some ⟨Shape.copyR e, l, r⟩ → Alias n N s r e' →
      Alias n N s (n + t) (e' != e)

namespace Alias

variable {n : Nat} {N : List Node} {s w : Nat} {e : Bool}

theorem val_eq (h : Alias n N s w e) (hN : WF n N) (x : List Bool) (hx : x.length = n) :
    val N x w = (val N x s != e) := by
  induction h with
  | self => simp
  | @left t l r e0 e1 hnode _ ih =>
    rw [val_node hN hx hnode]
    show (val N x l != e0) = (val N x s != (e1 != e0))
    rw [ih]
    cases val N x s <;> cases e1 <;> cases e0 <;> rfl
  | @right t l r e0 e1 hnode _ ih =>
    rw [val_node hN hx hnode]
    show (val N x r != e0) = (val N x s != (e1 != e0))
    rw [ih]
    cases val N x s <;> cases e1 <;> cases e0 <;> rfl

/-- A copy comes after what it copies. -/
theorem le (h : Alias n N s w e) (hN : WF n N) : s ≤ w := by
  induction h with
  | self => exact Nat.le_refl _
  | @left t l r e0 e1 hnode _ ih =>
    have hlr : l < n + t ∧ r < n + t := hN t _ hnode
    omega
  | @right t l r e0 e1 hnode _ ih =>
    have hlr : l < n + t ∧ r < n + t := hN t _ hnode
    omega

end Alias

/-- Every wire is a copy of an input, of a gate, or of a constant. -/
theorem exists_root {n : Nat} {N : List Node} (hN : WF n N) : ∀ w, w < n + N.length →
    ∃ s e, Alias n N s w e ∧ (s < n ∨
      (∃ t f l r, s = n + t ∧ N[t]? = some ⟨Shape.gate f, l, r⟩) ∨
      (∃ t d l r, s = n + t ∧ N[t]? = some ⟨Shape.const d, l, r⟩)) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · exact ⟨w, false, Alias.self, Or.inl hin⟩
    · have ht : w - n < N.length := by omega
      have hwt : w = n + (w - n) := by omega
      have hnode : N[w - n]? = some N[w - n] := List.getElem?_eq_getElem ht
      generalize N[w - n] = nd at hnode
      obtain ⟨k, l, r⟩ := nd
      have hlr : l < n + (w - n) ∧ r < n + (w - n) := hN _ _ hnode
      cases k with
      | gate f =>
        exact ⟨w, false, Alias.self, Or.inr (Or.inl ⟨w - n, f, l, r, hwt, hnode⟩)⟩
      | const d =>
        exact ⟨w, false, Alias.self, Or.inr (Or.inr ⟨w - n, d, l, r, hwt, hnode⟩)⟩
      | copyL e =>
        obtain ⟨s, e', hal, hroot⟩ := ih l (by omega) (by omega)
        refine ⟨s, e' != e, ?_, hroot⟩
        rw [hwt]
        exact Alias.left hnode hal
      | copyR e =>
        obtain ⟨s, e', hal, hroot⟩ := ih r (by omega) (by omega)
        refine ⟨s, e' != e, ?_, hroot⟩
        rw [hwt]
        exact Alias.right hnode hal

/-- Run the circuit on two inputs that differ only at the wires in `S`. If every gate that reads
a copy of a wire in `S` takes the same value on both, so does every wire that is not such a copy. -/
theorem flow {n : Nat} {N : List Node} (hN : WF n N) (S : Nat → Prop) {x x' : List Bool}
    (hx : x.length = n) (hx' : x'.length = n)
    (hin : ∀ w, w < n → ¬S w → x.getD w false = x'.getD w false)
    (hread : ∀ t f l r, N[t]? = some ⟨Shape.gate f, l, r⟩ →
      ((∃ s e, S s ∧ Alias n N s l e) ∨ (∃ s e, S s ∧ Alias n N s r e)) →
        val N x (n + t) = val N x' (n + t)) :
    ∀ w, (¬∃ s e, S s ∧ Alias n N s w e) → val N x w = val N x' w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_input N x w (by omega), val_input N x' w (by omega)]
      exact hin w h1 (fun h => hw ⟨w, false, h, Alias.self⟩)
    by_cases h2 : n + N.length ≤ w
    · rw [val_beyond N x w (by omega), val_beyond N x' w (by omega)]
    have ht : w - n < N.length := by omega
    have hwt : w = n + (w - n) := by omega
    have hnode : N[w - n]? = some N[w - n] := List.getElem?_eq_getElem ht
    generalize N[w - n] = nd at hnode
    obtain ⟨k, l, r⟩ := nd
    have hlr : l < n + (w - n) ∧ r < n + (w - n) := hN _ _ hnode
    cases k with
    | gate f =>
      by_cases hal : (∃ s e, S s ∧ Alias n N s l e) ∨ (∃ s e, S s ∧ Alias n N s r e)
      · rw [hwt]
        exact hread (w - n) f l r hnode hal
      · rw [hwt, val_node hN hx hnode, val_node hN hx' hnode,
          ih l (by omega) (fun h => hal (Or.inl h)), ih r (by omega) (fun h => hal (Or.inr h))]
    | copyL e =>
      have hl : ¬∃ s e', S s ∧ Alias n N s l e' :=
        fun ⟨s, e', hs, h⟩ => hw ⟨s, e' != e, hs, by rw [hwt]; exact Alias.left hnode h⟩
      rw [hwt, val_node hN hx hnode, val_node hN hx' hnode]
      show (val N x l != e) = (val N x' l != e)
      rw [ih l (by omega) hl]
    | copyR e =>
      have hr : ¬∃ s e', S s ∧ Alias n N s r e' :=
        fun ⟨s, e', hs, h⟩ => hw ⟨s, e' != e, hs, by rw [hwt]; exact Alias.right hnode h⟩
      rw [hwt, val_node hN hx hnode, val_node hN hx' hnode]
      show (val N x r != e) = (val N x' r != e)
      rw [ih r (by omega) hr]
    | const d =>
      rw [hwt, val_node hN hx hnode, val_node hN hx' hnode]
      rfl

/-! ## Dead gates -/

/-- A gate with a wire that is constant on `P`. -/
def Dead (N : List Node) (P : List Bool → Prop) (t : Nat) : Prop :=
  ∃ (f : Bool → Bool → Bool) (l r : Nat), N[t]? = some ⟨Shape.gate f, l, r⟩ ∧
    ((∃ d, ∀ x, P x → val N x l = d) ∨ (∃ d, ∀ x, P x → val N x r = d))

/-- A gate that reads a copy of a stuck wire is dead. -/
theorem dead_of_alias {n : Nat} {N : List Node} {P : List Bool → Prop} (hN : WF n N)
    (hP : ∀ x, P x → x.length = n) {t : Nat} {f : Bool → Bool → Bool} {l r s : Nat} {d : Bool}
    (hnode : N[t]? = some ⟨Shape.gate f, l, r⟩)
    (hal : (∃ e, Alias n N s l e) ∨ (∃ e, Alias n N s r e))
    (hs : ∀ x, P x → val N x s = d) : Dead N P t := by
  refine ⟨f, l, r, hnode, ?_⟩
  rcases hal with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨d != e, fun x hx => by rw [he.val_eq hN x (hP x hx), hs x hx]⟩
  · exact Or.inr ⟨d != e, fun x hx => by rw [he.val_eq hN x (hP x hx), hs x hx]⟩

theorem Dead.congr {N N' : List Node} {P : List Bool → Prop} {t : Nat} (hd : Dead N P t)
    (hnode : N'[t]? = N[t]?) (hval : ∀ x, P x → ∀ w, val N' x w = val N x w) : Dead N' P t := by
  obtain ⟨f, l, r, hn, h⟩ := hd
  refine ⟨f, l, r, hnode.trans hn, ?_⟩
  rcases h with ⟨d, hd⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨d, fun x hx => (hval x hx l).trans (hd x hx)⟩
  · exact Or.inr ⟨d, fun x hx => (hval x hx r).trans (hd x hx)⟩

/-- A dead gate is a copy or a constant on `P`: overwrite it, one gate cheaper. -/
theorem kill_one {n : Nat} {N : List Node} {P : List Bool → Prop} (hN : WF n N)
    (hP : ∀ x, P x → x.length = n) {t : Nat} (hd : Dead N P t) :
    ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 1 = cost N ∧
      (∀ x, P x → ∀ w, val N' x w = val N x w) ∧ ∀ t', t' ≠ t → N'[t']? = N[t']? := by
  obtain ⟨f, l, r, hnode, ⟨d, hd⟩ | ⟨d, hd⟩⟩ := hd
  · exact simplify hN hP hnode (Shape.ofRight (f d)) (Shape.ofRight_costs _)
      (fun x hx => by rw [Shape.ofRight_op, hd x hx])
  · exact simplify hN hP hnode (Shape.ofLeft (fun v => f v d)) (Shape.ofLeft_costs _)
      (fun x hx => by rw [Shape.ofLeft_op, hd x hx])

/-- Two dead gates: the same circuit on `P`, two gates cheaper. -/
theorem kill_two {n : Nat} {N : List Node} {P : List Bool → Prop} (hN : WF n N)
    (hP : ∀ x, P x → x.length = n) {t1 t2 : Nat} (h12 : t1 ≠ t2) (d1 : Dead N P t1)
    (d2 : Dead N P t2) :
    ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 2 = cost N ∧
      ∀ x, P x → ∀ w, val N' x w = val N x w := by
  obtain ⟨N1, w1, l1, c1, v1, s1⟩ := kill_one hN hP d1
  have d2' := d2.congr (s1 t2 (Ne.symm h12)) v1
  obtain ⟨N2, w2, l2, c2, v2, _⟩ := kill_one w1 hP d2'
  exact ⟨N2, w2, by omega, by omega, fun x hx w => by rw [v2 x hx, v1 x hx]⟩

end PNP.Full

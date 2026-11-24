import PNP.AndBasis

/-!
# Which wire is a copy of which

Copies are free, so a gate may read an input through a chain of copy nodes. `Alias s w e` says that
wire `w` is wire `s` seen through such a chain, flipped when `e` is true. Following the chain down
from any wire ends at a *root*: an input, an AND gate, or a constant.

The last two theorems are how a proof learns that a gate exists. `flow` says a change at wire `s`
can only travel through the AND gates that read a copy of `s`. `reader_or_useless` turns that into
a choice: an AND gate is read by another AND gate, or it is the output, or it can be thrown away.
-/

namespace PNP

/-- Wire `w` carries wire `s` through a chain of copy nodes, flipped when `e` is true. -/
inductive Alias (n : Nat) (N : List Node) (s : Nat) : Nat → Bool → Prop where
  | self : Alias n N s s false
  | left {t l r : Nat} {e e' : Bool} : N[t]? = some ⟨Kind.copyL e, l, r⟩ → Alias n N s l e' →
      Alias n N s (n + t) (e' != e)
  | right {t l r : Nat} {e e' : Bool} : N[t]? = some ⟨Kind.copyR e, l, r⟩ → Alias n N s r e' →
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

/-- Two chains down from the same wire run along each other. -/
theorem linear (h : Alias n N s w e) : ∀ {s' : Nat} {e' : Bool}, Alias n N s' w e' →
    (∃ d, Alias n N s s' d) ∨ (∃ d, Alias n N s' s d) := by
  induction h with
  | self => intro s' e' h'; exact Or.inr ⟨_, h'⟩
  | @left t l r e0 e1 hnode hl ih =>
    intro s' e' h'
    generalize hw : n + t = w' at h'
    cases h' with
    | self => rw [← hw]; exact Or.inl ⟨_, Alias.left hnode hl⟩
    | @left t2 l2 r2 e2 e3 hnode2 hl2 =>
      have ht : t2 = t := by omega
      subst ht
      rw [hnode] at hnode2
      simp only [Option.some.injEq, Node.mk.injEq, Kind.copyL.injEq] at hnode2
      obtain ⟨_, hll, _⟩ := hnode2
      subst hll
      exact ih hl2
    | @right t2 l2 r2 e2 e3 hnode2 hl2 =>
      have ht : t2 = t := by omega
      subst ht
      rw [hnode] at hnode2
      simp at hnode2
  | @right t l r e0 e1 hnode hr ih =>
    intro s' e' h'
    generalize hw : n + t = w' at h'
    cases h' with
    | self => rw [← hw]; exact Or.inl ⟨_, Alias.right hnode hr⟩
    | @left t2 l2 r2 e2 e3 hnode2 hl2 =>
      have ht : t2 = t := by omega
      subst ht
      rw [hnode] at hnode2
      simp at hnode2
    | @right t2 l2 r2 e2 e3 hnode2 hr2 =>
      have ht : t2 = t := by omega
      subst ht
      rw [hnode] at hnode2
      simp only [Option.some.injEq, Node.mk.injEq, Kind.copyR.injEq] at hnode2
      obtain ⟨_, _, hrr⟩ := hnode2
      subst hrr
      exact ih hr2

/-- No wire is a copy of an input and of an AND gate at once. -/
theorem not_input_and_gate {i g : Nat} {e' a b c : Bool} {l r : Nat} (hN : WF n N) (hi : i < n)
    (hnode : N[g]? = some ⟨Kind.and a b c, l, r⟩) (h1 : Alias n N i w e)
    (h2 : Alias n N (n + g) w e') : False := by
  rcases h1.linear h2 with ⟨d, h⟩ | ⟨d, h⟩
  · generalize hw : n + g = w' at h
    cases h with
    | self => omega
    | @left t l' r' e0 e1 hnode' _ =>
      have ht : t = g := by omega
      subst ht
      rw [hnode] at hnode'
      simp at hnode'
    | @right t l' r' e0 e1 hnode' _ =>
      have ht : t = g := by omega
      subst ht
      rw [hnode] at hnode'
      simp at hnode'
  · have := h.le hN
    omega

end Alias

/-- Every wire is a copy of an input, of an AND gate, or of a constant. -/
theorem exists_root {n : Nat} {N : List Node} (hN : WF n N) : ∀ w, w < n + N.length →
    ∃ s e, Alias n N s w e ∧ (s < n ∨
      (∃ t a b c l r, s = n + t ∧ N[t]? = some ⟨Kind.and a b c, l, r⟩) ∨
      (∃ t d l r, s = n + t ∧ N[t]? = some ⟨Kind.const d, l, r⟩)) := by
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
      | and a b c =>
        exact ⟨w, false, Alias.self, Or.inr (Or.inl ⟨w - n, a, b, c, l, r, hwt, hnode⟩)⟩
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

/-- Run two circuits that differ only at wire `s`, on inputs that differ only at wire `s`. If
they agree at every AND gate that reads a copy of `s`, they agree at every wire that is not a
copy of `s`. -/
theorem flow {n : Nat} {N N' : List Node} (hN : WF n N) (hN' : WF n N')
    (hlen : N'.length = N.length) (s : Nat) (hsame : ∀ t, n + t ≠ s → N'[t]? = N[t]?)
    {x x' : List Bool} (hx : x.length = n) (hx' : x'.length = n)
    (hin : ∀ w, w < n → w ≠ s → x.getD w false = x'.getD w false)
    (hread : ∀ t a b c l r, N[t]? = some ⟨Kind.and a b c, l, r⟩ → n + t ≠ s →
      ((∃ e, Alias n N s l e) ∨ (∃ e, Alias n N s r e)) → val N x (n + t) = val N' x' (n + t)) :
    ∀ w, (¬∃ e, Alias n N s w e) → val N x w = val N' x' w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    have hws : w ≠ s := fun h => hw ⟨false, by rw [h]; exact Alias.self⟩
    by_cases h1 : w < n
    · rw [val_input N x w (by omega), val_input N' x' w (by omega)]
      exact hin w h1 hws
    by_cases h2 : n + N.length ≤ w
    · rw [val_beyond N x w (by omega), val_beyond N' x' w (by omega)]
    have ht : w - n < N.length := by omega
    have hwt : w = n + (w - n) := by omega
    have hnode : N[w - n]? = some N[w - n] := List.getElem?_eq_getElem ht
    generalize N[w - n] = nd at hnode
    obtain ⟨k, l, r⟩ := nd
    have hlr : l < n + (w - n) ∧ r < n + (w - n) := hN _ _ hnode
    have hnode' : N'[w - n]? = some ⟨k, l, r⟩ := (hsame _ (by omega)).trans hnode
    cases k with
    | and a b c =>
      by_cases hal : (∃ e, Alias n N s l e) ∨ (∃ e, Alias n N s r e)
      · rw [hwt]
        exact hread (w - n) a b c l r hnode (by omega) hal
      · rw [hwt, val_node hN hx hnode, val_node hN' hx' hnode',
          ih l (by omega) (fun h => hal (Or.inl h)), ih r (by omega) (fun h => hal (Or.inr h))]
    | copyL e =>
      have hl : ¬∃ e', Alias n N s l e' :=
        fun ⟨e', h⟩ => hw ⟨e' != e, by rw [hwt]; exact Alias.left hnode h⟩
      rw [hwt, val_node hN hx hnode, val_node hN' hx' hnode']
      show (val N x l != e) = (val N' x' l != e)
      rw [ih l (by omega) hl]
    | copyR e =>
      have hr : ¬∃ e', Alias n N s r e' :=
        fun ⟨e', h⟩ => hw ⟨e' != e, by rw [hwt]; exact Alias.right hnode h⟩
      rw [hwt, val_node hN hx hnode, val_node hN' hx' hnode']
      show (val N x r != e) = (val N' x' r != e)
      rw [ih r (by omega) hr]
    | const d =>
      rw [hwt, val_node hN hx hnode, val_node hN' hx' hnode']
      rfl

/-- An AND gate is read by an AND gate, or it is the output, or the circuit works without it. -/
theorem reader_or_useless {n : Nat} {N : List Node} (hN : WF n N) {g : Nat} {a b c : Bool}
    {l r : Nat} (hnode : N[g]? = some ⟨Kind.and a b c, l, r⟩) :
    (∃ (t : Nat) (a' b' c' : Bool) (l' r' : Nat), N[t]? = some ⟨Kind.and a' b' c', l', r'⟩ ∧
        ((∃ e, Alias n N (n + g) l' e) ∨ (∃ e, Alias n N (n + g) r' e))) ∨
      (∃ e, Alias n N (n + g) (n + N.length - 1) e) ∨
      ∃ N', WF n N' ∧ N'.length = N.length ∧ cost N' + 1 = cost N ∧
        ∀ x : List Bool, x.length = n →
          val N' x (n + N'.length - 1) = val N x (n + N.length - 1) := by
  by_cases h1 : ∃ (t : Nat) (a' b' c' : Bool) (l' r' : Nat), N[t]? = some ⟨Kind.and a' b' c', l', r'⟩ ∧
      ((∃ e, Alias n N (n + g) l' e) ∨ (∃ e, Alias n N (n + g) r' e))
  · exact Or.inl h1
  by_cases h2 : ∃ e, Alias n N (n + g) (n + N.length - 1) e
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ⟨N.set g ⟨Kind.const false, l, r⟩, hN.set hnode _, List.length_set,
    cost_set N g _ _ hnode rfl rfl, ?_⟩)
  intro x hx
  rw [List.length_set]
  refine (flow hN (hN.set hnode _) List.length_set (n + g)
    (fun t ht => List.getElem?_set_ne (by omega)) hx hx (fun _ _ _ => rfl) ?_ _ h2).symm
  intro t a' b' c' l' r' hn' _ hal
  exact absurd ⟨t, a', b', c', l', r', hn', hal⟩ h1

end PNP

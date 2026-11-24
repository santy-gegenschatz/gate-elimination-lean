import PNP.Circuit

/-!
# A circuit with `g` gates reads at most `g + 1` inputs

Each gate has two inputs, so walking back from the output, every gate can add at most one new
wire to the set the output depends on. Consequence: a function that really uses all `n` of its
inputs needs at least `n - 1` gates. This is folklore; it is here because it is the first bound
in the folder that holds for every `n`.
-/

namespace PNP

open Circuit

/-- Two wire lists hold the same values at the positions in `N`. -/
def AgreeOn (N : List Nat) (w w' : List Bool) : Prop :=
  ∀ i ∈ N, w.getD i false = w'.getD i false

theorem getD_fire (w : List Bool) (g : Gate) (i : Nat) :
    (fire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op (w.getD g.left false) (w.getD g.right false)
      else false := by
  simp only [fire, List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases h : i < w.length
  · simp [h]
  · by_cases h' : i = w.length
    · simp [h']
    · have : i - w.length ≠ 0 := by omega
      simp [h, h', this]

theorem getLastD_eq_getD (w : List Bool) :
    w.getLastD false = w.getD (w.length - 1) false := by
  simp [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The output wire depends on at most `gates + 1` of the starting wires. -/
theorem last_wire_reads_few (gs : List Gate) :
    ∀ m : Nat, ∃ N : List Nat, N.length ≤ gs.length + 1 ∧
      ∀ w w' : List Bool, w.length = m → w'.length = m → AgreeOn N w w' →
        (gs.foldl fire w).getLastD false = (gs.foldl fire w').getLastD false := by
  induction gs with
  | nil =>
    intro m
    refine ⟨[m - 1], by simp, ?_⟩
    intro w w' hw hw' h
    have := h (m - 1) (by simp)
    show w.getLastD false = w'.getLastD false
    rw [getLastD_eq_getD, getLastD_eq_getD, hw, hw']
    exact this
  | cons g rest ih =>
    intro m
    obtain ⟨N', hlen, hN'⟩ := ih (m + 1)
    by_cases hm : m ∈ N'
    · refine ⟨g.left :: g.right :: N'.erase m, ?_, ?_⟩
      · have hpos : 0 < N'.length := List.length_pos_of_mem hm
        have herase := List.length_erase_of_mem hm
        simp only [List.length_cons]
        omega
      · intro w w' hw hw' h
        apply hN' (fire w g) (fire w' g) (by simp [fire, hw]) (by simp [fire, hw'])
        intro i hi
        rw [getD_fire, getD_fire, hw, hw']
        have hl := h g.left (by simp)
        have hr := h g.right (by simp)
        by_cases him : i = m
        · simp only [him, Nat.lt_irrefl, ↓reduceIte, hl, hr]
        · have hi' := h i (by simp [(List.mem_erase_of_ne him).mpr hi])
          simp only [him, ↓reduceIte, hi']
    · refine ⟨N', by simp only [List.length_cons]; omega, ?_⟩
      intro w w' hw hw' h
      apply hN' (fire w g) (fire w' g) (by simp [fire, hw]) (by simp [fire, hw'])
      intro i hi
      rw [getD_fire, getD_fire, hw, hw']
      have him : i ≠ m := fun e => hm (e ▸ hi)
      simp only [him, ↓reduceIte, h i hi]

/-- A list that contains every number below `n` has at least `n` entries. -/
theorem length_ge_of_contains_below : ∀ (n : Nat) (N : List Nat), (∀ i, i < n → i ∈ N) → n ≤ N.length
  | 0, _, _ => Nat.zero_le _
  | n + 1, N, h => by
    have hn : n ∈ N := h n (Nat.lt_succ_self n)
    have ih := length_ge_of_contains_below n (N.erase n)
      (fun i hi => (List.mem_erase_of_ne (by omega)).mpr (h i (by omega)))
    rw [List.length_erase_of_mem hn] at ih
    have : 0 < N.length := List.length_pos_of_mem hn
    omega

/-- `f` on `n` inputs really uses input `i`: two inputs that differ only there get different answers. -/
def DependsOn (n : Nat) (f : List Bool → Bool) (i : Nat) : Prop :=
  ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
    (∀ j, j ≠ i → x.getD j false = y.getD j false) ∧ f x ≠ f y

/-- A function that uses all `n` of its inputs needs at least `n - 1` gates. -/
theorem needs_gates_of_depends_on_all (n : Nat) (f : List Bool → Bool)
    (h : ∀ i, i < n → DependsOn n f i) : NeedsGates n f (n - 1) := by
  intro c hin hc
  obtain ⟨N, hlen, hN⟩ := last_wire_reads_few c.gates n
  have hall : ∀ i, i < n → i ∈ N := by
    intro i hi
    apply Classical.byContradiction
    intro hnot
    obtain ⟨x, y, hx, hy, hsame, hne⟩ := h i hi
    have heval := hN x y hx hy (fun j hj => hsame j (fun e => hnot (e ▸ hj)))
    have ex := hc.2 x (by omega)
    have ey := hc.2 y (by omega)
    exact hne (by rw [← ex, ← ey]; exact heval)
  have := length_ge_of_contains_below n N hall
  show n - 1 ≤ c.gates.length
  omega

end PNP

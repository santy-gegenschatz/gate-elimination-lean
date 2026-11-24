import PNP.FullAlias

/-!
# Two gates per input, over the full binary basis

Schnorr's other bound (1974). Any two-input gate is allowed, XOR included. If a function `f` of
`n` inputs is "hard" in the sense below, every circuit for it has at least `2n - 3` gates.

`f` is hard when, for any two inputs, the four ways of fixing them leave at least three different
functions of the rest, and this survives fixing inputs one at a time. `Mixes` says the first part
in the form the proof uses: no single bit computed from the two inputs carries everything `f`
needs to know about them.

The proof is gate elimination. The first gate `g` reads two inputs `i` and `j`. If no other gate
read `i` or `j`, the rest of the circuit would see them only through the one bit `g` puts out,
and `f` mixes them. So one of them is read twice. Fix it: two gates are dead.
-/

namespace PNP.Full

/-- The circuit outputs `f` on every input in `P`. -/
def ComputesOn (n : Nat) (N : List Node) (P : List Bool → Prop) (f : List Bool → Bool) : Prop :=
  ∀ x, P x → val N x (n + N.length - 1) = f x

/-- Inside `P`, flipping input `i` can change `f`. -/
def DependsOn (P : List Bool → Prop) (f : List Bool → Bool) (i : Nat) : Prop :=
  ∃ x, P x ∧ f (x.set i true) ≠ f (x.set i false)

/-- Inside `P`, no single bit `b` of inputs `i` and `j` is enough for `f`: two inputs agree
everywhere else and on `b`, and `f` still tells them apart. -/
def Mixes (P : List Bool → Prop) (f : List Bool → Bool) (i j : Nat) : Prop :=
  ∀ b : Bool → Bool → Bool, ∃ x x', P x ∧ P x' ∧
    (∀ w, w ≠ i → w ≠ j → x.getD w false = x'.getD w false) ∧
    b (x.getD i false) (x.getD j false) = b (x'.getD i false) (x'.getD j false) ∧ f x ≠ f x'

/-- `Q F P` marks the restrictions (free inputs `F`, allowed inputs `P`) on which `f` stays
hard: it depends on every free input, mixes every two of them, and each free input can be fixed
to some value so that `Q` still holds. -/
structure Hard (n : Nat) (f : List Bool → Bool) (Q : List Nat → (List Bool → Prop) → Prop) :
    Prop where
  cube : ∀ F P, Q F P → Cube n F P
  depends : ∀ F P, Q F P → 2 ≤ F.length → ∀ i, i ∈ F → DependsOn P f i
  mixes : ∀ F P, Q F P → 3 ≤ F.length → ∀ i j, i ∈ F → j ∈ F → i ≠ j → Mixes P f i j
  fix : ∀ F P, Q F P → 3 ≤ F.length → ∀ i, i ∈ F → ∃ c, Q (F.erase i) (fixInput P i c)

theorem output_not_alias {n : Nat} {N : List Node} {P : List Bool → Prop} {F : List Nat}
    {f : List Bool → Bool} (hN : WF n N) (hC : Cube n F P) (hX : ComputesOn n N P f) {i s : Nat}
    (hi : i ∈ F) (his : i ≠ s) (hs : s < n) (hdep : DependsOn P f i) {e : Bool}
    (hal : Alias n N s (n + N.length - 1) e) : False := by
  obtain ⟨x, hx, hne⟩ := hdep
  have hl := hC.len x hx
  have hlen : ∀ b, (x.set i b).length = n := fun b => by rw [List.length_set]; exact hl
  apply hne
  rw [← hX _ (hC.free x hx i hi true), ← hX _ (hC.free x hx i hi false),
    hal.val_eq hN _ (hlen true), hal.val_eq hN _ (hlen false),
    val_input N _ s (by rw [hlen]; exact hs), val_input N _ s (by rw [hlen]; exact hs),
    getD_set_ne his, getD_set_ne his]

theorem output_not_const {n : Nat} {N : List Node} {P : List Bool → Prop} {F : List Nat}
    {f : List Bool → Bool} (hC : Cube n F P) (hX : ComputesOn n N P f) {i : Nat} (hi : i ∈ F)
    (hdep : DependsOn P f i) {d : Bool} (hd : ∀ x, P x → val N x (n + N.length - 1) = d) :
    False := by
  obtain ⟨x, hx, hne⟩ := hdep
  apply hne
  rw [← hX _ (hC.free x hx i hi true), ← hX _ (hC.free x hx i hi false),
    hd _ (hC.free x hx i hi true), hd _ (hC.free x hx i hi false)]

/-- A circuit for a hard function has at least `2 |F| - 3` gates. -/
theorem gates_for_hard {n : Nat} {f : List Bool → Bool}
    {Q : List Nat → (List Bool → Prop) → Prop} (hQ : Hard n f Q) :
    ∀ (m : Nat) (N : List Node), cost N = m → WF n N →
      ∀ (F : List Nat) (P : List Bool → Prop), Q F P → ComputesOn n N P f → 2 ≤ F.length →
        2 * F.length - 3 ≤ cost N := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro N hm hN F P hq hX hF
  have hC := hQ.cube F P hq
  have hF1 : ¬F.length ≤ 1 := by omega
  -- The same job on fewer allowed inputs, by a circuit with the same wire values.
  have restrict : ∀ {N' : List Node} {P' : List Bool → Prop}, (∀ x, P' x → P x) →
      N'.length = N.length → (∀ x, P' x → ∀ w, val N' x w = val N x w) →
      ComputesOn n N' P' f := by
    intro N' P' hsub hlen hval x hx
    rw [hlen, hval x hx]
    exact hX x (hsub x hx)
  have cheaper : ∀ N', WF n N' → cost N' + 1 = cost N → ComputesOn n N' P f →
      2 * F.length - 3 ≤ cost N := by
    intro N' h1 h2 h3
    have := ih (cost N') (by omega) N' rfl h1 F P hq h3 hF
    omega
  have kill : ∀ t, Dead N P t → 2 * F.length - 3 ≤ cost N := by
    intro t hd
    obtain ⟨N', h1, h2, h3, h4, _⟩ := kill_one hN hC.len hd
    exact cheaper N' h1 h3 (restrict (fun _ h => h) h2 h4)
  have hn : 0 < n := by
    obtain ⟨i, hi, _⟩ := exists_ne_of_two hF1 hC.nodup 0
    exact Nat.lt_of_le_of_lt (Nat.zero_le i) (hC.lt i hi)
  by_cases hgate : ∃ (g : Nat) (op : Bool → Bool → Bool) (l r : Nat),
      N[g]? = some ⟨Shape.gate op, l, r⟩
  case neg =>
    -- No gate at all: the output is a copy of one input, or a constant.
    exfalso
    obtain ⟨s, e, hal, hroot⟩ := exists_root hN (n + N.length - 1) (by omega)
    rcases hroot with hs | ⟨t, op, l, r, _, hnode⟩ | ⟨t, d, l, r, hs, hnode⟩
    · obtain ⟨i, hi, his⟩ := exists_ne_of_two hF1 hC.nodup s
      exact output_not_alias hN hC hX hi his hs (hQ.depends F P hq hF i hi) hal
    · exact hgate ⟨t, op, l, r, hnode⟩
    · obtain ⟨i, hi, _⟩ := exists_ne_of_two hF1 hC.nodup 0
      refine output_not_const hC hX hi (hQ.depends F P hq hF i hi) (d := (d != e))
        (fun x hx => ?_)
      rw [hal.val_eq hN x (hC.len x hx), hs, val_node hN (hC.len x hx) hnode]
      rfl
  obtain ⟨g0, hg0⟩ := hgate
  obtain ⟨g, ⟨op, l, r, hnode⟩, hfirst⟩ := exists_first
    (p := fun g => ∃ (op : Bool → Bool → Bool) (l r : Nat), N[g]? = some ⟨Shape.gate op, l, r⟩)
    g0 hg0
  have hcost : 1 ≤ cost N := cost_pos hnode
  -- With two free inputs the claim is one gate, and there is one.
  by_cases hF2 : F.length ≤ 2
  · omega
  have hF3 : 3 ≤ F.length := by omega
  have hg : g < N.length := (List.getElem?_eq_some_iff.mp hnode).1
  have hlr : l < n + g ∧ r < n + g := hN g _ hnode
  -- A wire below the first gate is a constant or a copy of an input.
  have below : ∀ w, w < n + g → (∃ d, ∀ x : List Bool, x.length = n → val N x w = d) ∨
      ∃ i e, i < n ∧ Alias n N i w e := by
    intro w hw
    obtain ⟨s, e, hal, hroot⟩ := exists_root hN w (by omega)
    rcases hroot with hs | ⟨t, op', l', r', hs, hnode'⟩ | ⟨t, d, l', r', hs, hnode'⟩
    · exact Or.inr ⟨s, e, hs, hal⟩
    · exfalso
      have := hal.le hN
      exact hfirst t (by omega) ⟨op', l', r', hnode'⟩
    · left
      refine ⟨d != e, fun x hx => ?_⟩
      rw [hal.val_eq hN x hx, hs, val_node hN hx hnode']
      rfl
  rcases below l hlr.1 with ⟨d, hd⟩ | ⟨i, e1, hi, hali⟩
  · exact kill g ⟨op, l, r, hnode, Or.inl ⟨d, fun x hx => hd x (hC.len x hx)⟩⟩
  rcases below r hlr.2 with ⟨d, hd⟩ | ⟨j, e2, hj, halj⟩
  · exact kill g ⟨op, l, r, hnode, Or.inr ⟨d, fun x hx => hd x (hC.len x hx)⟩⟩
  have hvl : ∀ x : List Bool, x.length = n → val N x l = (x.getD i false != e1) := fun x hx => by
    rw [hali.val_eq hN x hx, val_input N x i (by omega)]
  have hvr : ∀ x : List Bool, x.length = n → val N x r = (x.getD j false != e2) := fun x hx => by
    rw [halj.val_eq hN x hx, val_input N x j (by omega)]
  -- Both wires of the gate are the same input: the gate is a copy or a constant.
  by_cases hij : i = j
  · subst hij
    obtain ⟨N', h1, h2, h3, h4, _⟩ := simplify hN hC.len hnode
      (Shape.ofLeft (fun v => op v (v != (e1 != e2)))) (Shape.ofLeft_costs _)
      (fun x hx => by
        rw [Shape.ofLeft_op, hvl x (hC.len x hx), hvr x (hC.len x hx)]
        cases x.getD i false <;> cases e1 <;> cases e2 <;> rfl)
    exact cheaper N' h1 h3 (restrict (fun _ h => h) h2 h4)
  -- An input that is already stuck: the gate is dead.
  by_cases hiF : i ∈ F
  case neg =>
    obtain ⟨d, hd⟩ := hC.stuck i hiF
    exact kill g ⟨op, l, r, hnode,
      Or.inl ⟨d != e1, fun x hx => by rw [hvl x (hC.len x hx), hd x hx]⟩⟩
  by_cases hjF : j ∈ F
  case neg =>
    obtain ⟨d, hd⟩ := hC.stuck j hjF
    exact kill g ⟨op, l, r, hnode,
      Or.inr ⟨d != e2, fun x hx => by rw [hvr x (hC.len x hx), hd x hx]⟩⟩
  -- The main case: a second gate reads `i` or `j`.
  have second : ∃ (s h : Nat) (op' : Bool → Bool → Bool) (l' r' : Nat), (s = i ∨ s = j) ∧
      h ≠ g ∧ N[h]? = some ⟨Shape.gate op', l', r'⟩ ∧
      ((∃ e, Alias n N s l' e) ∨ (∃ e, Alias n N s r' e)) := by
    apply Classical.byContradiction
    intro hno
    -- The output is not a copy of `i` or of `j`: `f` needs more than one of them.
    have hout : ¬∃ s e, (s = i ∨ s = j) ∧ Alias n N s (n + N.length - 1) e := by
      rintro ⟨s, e, hs, hal⟩
      have hsn : s < n := by rcases hs with h | h <;> rw [h] <;> assumption
      have hfs : ∀ x, P x → f x = (x.getD s false != e) := fun x hx => by
        rw [← hX x hx, hal.val_eq hN x (hC.len x hx),
          val_input N x s (by rw [hC.len x hx]; exact hsn)]
      rcases hs with h | h
      · obtain ⟨x, x', hx, hx', _, hb, hne⟩ := hQ.mixes F P hq hF3 i j hiF hjF hij (fun u _ => u)
        have hb' : x.getD i false = x'.getD i false := hb
        apply hne
        rw [hfs x hx, hfs x' hx', h, hb']
      · obtain ⟨x, x', hx, hx', _, hb, hne⟩ := hQ.mixes F P hq hF3 i j hiF hjF hij (fun _ v => v)
        have hb' : x.getD j false = x'.getD j false := hb
        apply hne
        rw [hfs x hx, hfs x' hx', h, hb']
    -- So the rest of the circuit sees `i` and `j` only through the bit `g` puts out.
    obtain ⟨x, x', hx, hx', hrest, hb, hne⟩ := hQ.mixes F P hq hF3 i j hiF hjF hij
      (fun u v => op (u != e1) (v != e2))
    apply hne
    rw [← hX x hx, ← hX x' hx']
    refine flow hN (fun s => s = i ∨ s = j) (hC.len x hx) (hC.len x' hx')
      (fun w _ hw => hrest w (fun h => hw (Or.inl h)) (fun h => hw (Or.inr h))) ?_ _ hout
    intro t op' l' r' hn' hal'
    by_cases htg : t = g
    · rw [htg, val_node hN (hC.len x hx) hnode, val_node hN (hC.len x' hx') hnode,
        hvl x (hC.len x hx), hvr x (hC.len x hx), hvl x' (hC.len x' hx'), hvr x' (hC.len x' hx')]
      exact hb
    · exfalso
      apply hno
      rcases hal' with ⟨s, e, hs, hal⟩ | ⟨s, e, hs, hal⟩
      · exact ⟨s, t, op', l', r', hs, htg, hn', Or.inl ⟨e, hal⟩⟩
      · exact ⟨s, t, op', l', r', hs, htg, hn', Or.inr ⟨e, hal⟩⟩
  obtain ⟨s, h, op2, l2, r2, hs, hhg, hnode2, hal2⟩ := second
  have hsF : s ∈ F := by rcases hs with hs | hs <;> rw [hs] <;> assumption
  have hsn : s < n := hC.lt s hsF
  have hgs : (∃ e, Alias n N s l e) ∨ (∃ e, Alias n N s r e) := by
    rcases hs with hs | hs
    · rw [hs]; exact Or.inl ⟨e1, hali⟩
    · rw [hs]; exact Or.inr ⟨e2, halj⟩
  -- Fix that input. Both gates that read it are dead.
  obtain ⟨c, hq'⟩ := hQ.fix F P hq hF3 s hsF
  have hC' := hQ.cube _ _ hq'
  have hs' : ∀ x, fixInput P s c x → val N x s = c := fun x hx => by
    rw [val_input N x s (by rw [hC.len x hx.1]; exact hsn)]
    exact hx.2
  have dg : Dead N (fixInput P s c) g := dead_of_alias hN hC'.len hnode hgs hs'
  have dh : Dead N (fixInput P s c) h := dead_of_alias hN hC'.len hnode2 hal2 hs'
  obtain ⟨N', h1, h2, h3, h4⟩ := kill_two hN hC'.len (Ne.symm hhg) dg dh
  have hlen' : (F.erase s).length = F.length - 1 := List.length_erase_of_mem hsF
  have := ih (cost N') (by omega) N' rfl h1 (F.erase s) _ hq'
    (restrict (fun _ hx => hx.1) h2 h4) (by omega)
  omega

/-- **Schnorr's 2n bound.** If `f` is hard on all inputs of length `n`, every circuit for it over
the full binary basis has at least `2n - 3` gates. -/
theorem hard_needs_two_per_input {n : Nat} {f : List Bool → Bool}
    {Q : List Nat → (List Bool → Prop) → Prop} (hQ : Hard n f Q)
    (hstart : Q (List.range n) (fun x => x.length = n)) (c : Circuit) (hn : c.inputs = n)
    (hc : c.Computes f) : 2 * n - 3 ≤ c.size := by
  by_cases h2 : n ≤ 1
  · omega
  obtain ⟨m, gates⟩ := c
  have hmn : m = n := hn
  subst hmn
  obtain ⟨hwf, hval⟩ := hc
  have hN : WF m (gates.map lift) := by
    intro t nd h
    obtain ⟨ht, rfl⟩ := List.getElem?_eq_some_iff.mp h
    have key := hwf t (by rw [List.length_map] at ht; exact ht)
    rw [List.getElem_map]
    exact key
  have hX : ComputesOn m (gates.map lift) (fun x => x.length = m) f := by
    intro x hx
    have key : (gates.foldl Circuit.fire x).getLastD false = f x := hval x hx
    rw [getLastD_eq_getD, length_foldl_fire, hx] at key
    show (((gates.map lift).map Node.toGate).foldl Circuit.fire x).getD
      (m + (gates.map lift).length - 1) false = f x
    rw [lift_toGate, List.length_map]
    exact key
  have := gates_for_hard hQ (cost (gates.map lift)) _ rfl hN _ _ hstart hX
    (by rw [List.length_range]; omega)
  rw [List.length_range, cost_lift] at this
  exact this

end PNP.Full

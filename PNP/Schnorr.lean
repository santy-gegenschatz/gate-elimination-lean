import PNP.Cube

/-!
# Without XOR gates, parity needs three gates per input

Schnorr's bound (1976): a circuit that computes the XOR of `n` inputs and has no XOR gate needs at
least `3 (n - 1)` gates. Here the bound is proved for AND gates alone, with copies, NOTs and
constants free.

The proof is gate elimination. Take the first AND gate `g`. It reads two inputs `i` and `j`,
through copies. Fix `i` to the value that sticks `g`. Then three AND gates are dead:

1. `g` itself;
2. a second gate `h` that reads `i`, because otherwise fixing `j` instead would cut `i` off from
   the output;
3. a gate that reads `g`, or, when that gate is `h` again, a gate that reads `h`, which is stuck
   too.

Whenever a gate that should exist does not, the circuit works without some AND gate, and the
induction on the number of AND gates takes over.
-/

namespace PNP

theorem exists_first {p : Nat → Prop} : ∀ k, p k → ∃ g, p g ∧ ∀ t, t < g → ¬p t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases h : ∃ t, t < k ∧ p t
    · obtain ⟨t, ht, hpt⟩ := h
      exact ih t ht hpt
    · exact ⟨k, hk, fun t ht hpt => h ⟨t, ht, hpt⟩⟩

/-- A circuit that outputs the XOR of `F.length` free inputs has at least `3 (F.length - 1)` AND
gates. -/
theorem and_gates_for_xor (n : Nat) : ∀ (m : Nat) (N : List Node), cost N = m → WF n N →
    ∀ (F : List Nat) (P : List Bool → Prop), Cube n F P → ComputesXorOn n N P F →
      3 * (F.length - 1) ≤ cost N := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro N hm hN F P hC hX
  by_cases hF : F.length ≤ 1
  · omega
  -- A circuit with one AND gate fewer that does the same job on `P` settles the claim.
  have cheaper : ∀ N', WF n N' → cost N' + 1 = cost N → ComputesXorOn n N' P F →
      3 * (F.length - 1) ≤ cost N := by
    intro N' h1 h2 h3
    have := ih (cost N') (by omega) N' rfl h1 F P hC h3
    omega
  have kill : ∀ t, Dead N P t → 3 * (F.length - 1) ≤ cost N := by
    intro t hd
    obtain ⟨N', h1, h2, h3, h4, _⟩ := kill_one hN hC.len hd
    exact cheaper N' h1 h3 (hX.congr h2 h4)
  obtain ⟨x0, hx0⟩ := hC.nonempty
  have hn : 0 < n := by
    obtain ⟨i, hi, _⟩ := exists_ne_of_two hF hC.nodup 0
    exact Nat.lt_of_le_of_lt (Nat.zero_le i) (hC.lt i hi)
  by_cases hand : ∃ (g : Nat) (a b c : Bool) (l r : Nat), N[g]? = some ⟨Kind.and a b c, l, r⟩
  case neg =>
    -- No AND gate at all: the output is a copy of one input, or a constant.
    exfalso
    obtain ⟨s, e, hal, hroot⟩ := exists_root hN (n + N.length - 1) (by omega)
    rcases hroot with hs | ⟨t, a, b, c, l, r, _, hnode⟩ | ⟨t, d, l, r, hs, hnode⟩
    · exact output_not_input_alias hN hC hX hF hs hal
    · exact hand ⟨t, a, b, c, l, r, hnode⟩
    · obtain ⟨i, hi, _⟩ := exists_ne_of_two hF hC.nodup 0
      refine output_not_const hC hX hi (d := (d != e)) (fun x hx => ?_)
      rw [hal.val_eq hN x (hC.len x hx), hs, val_node hN (hC.len x hx) hnode]
      rfl
  obtain ⟨g0, hg0⟩ := hand
  obtain ⟨g, ⟨a, b, c, l, r, hnode⟩, hfirst⟩ := exists_first
    (p := fun g => ∃ (a b c : Bool) (l r : Nat), N[g]? = some ⟨Kind.and a b c, l, r⟩) g0 hg0
  have hg : g < N.length := (List.getElem?_eq_some_iff.mp hnode).1
  have hlr : l < n + g ∧ r < n + g := hN g _ hnode
  -- A wire below the first AND gate is a constant or a copy of an input.
  have below : ∀ w, w < n + g → (∃ d, ∀ x : List Bool, x.length = n → val N x w = d) ∨
      ∃ i e, i < n ∧ Alias n N i w e := by
    intro w hw
    obtain ⟨s, e, hal, hroot⟩ := exists_root hN w (by omega)
    rcases hroot with hs | ⟨t, a', b', c', l', r', hs, hnode'⟩ | ⟨t, d, l', r', hs, hnode'⟩
    · exact Or.inr ⟨s, e, hs, hal⟩
    · exfalso
      have := hal.le hN
      exact hfirst t (by omega) ⟨a', b', c', l', r', hnode'⟩
    · left
      refine ⟨d != e, fun x hx => ?_⟩
      rw [hal.val_eq hN x hx, hs, val_node hN hx hnode']
      rfl
  rcases below l hlr.1 with ⟨d, hd⟩ | ⟨i, e1, hi, hali⟩
  · exact kill g ⟨a, b, c, l, r, hnode, Or.inl ⟨d, fun x hx => hd x (hC.len x hx)⟩⟩
  rcases below r hlr.2 with ⟨d, hd⟩ | ⟨j, e2, hj, halj⟩
  · exact kill g ⟨a, b, c, l, r, hnode, Or.inr ⟨d, fun x hx => hd x (hC.len x hx)⟩⟩
  have hvl : ∀ x : List Bool, x.length = n → val N x l = (x.getD i false != e1) := fun x hx => by
    rw [hali.val_eq hN x hx, val_input N x i (by omega)]
  have hvr : ∀ x : List Bool, x.length = n → val N x r = (x.getD j false != e2) := fun x hx => by
    rw [halj.val_eq hN x hx, val_input N x j (by omega)]
  -- Both inputs of the gate are the same input: the gate is a copy or a constant.
  by_cases hij : i = j
  · subst hij
    obtain ⟨N', h1, h2, h3, h4, _⟩ := simplify hN hC.len hnode (Kind.merge a b c e1 e2)
      (Kind.merge_costs a b c e1 e2)
      (fun x hx => by
        rw [hvl x (hC.len x hx), hvr x (hC.len x hx)]
        exact Kind.merge_op a b c e1 e2 _)
    exact cheaper N' h1 h3 (hX.congr h2 h4)
  -- An input that is already stuck: the gate is dead.
  by_cases hiF : i ∈ F
  case neg =>
    obtain ⟨d, hd⟩ := hC.stuck i hiF
    exact kill g ⟨a, b, c, l, r, hnode,
      Or.inl ⟨d != e1, fun x hx => by rw [hvl x (hC.len x hx), hd x hx]⟩⟩
  by_cases hjF : j ∈ F
  case neg =>
    obtain ⟨d, hd⟩ := hC.stuck j hjF
    exact kill g ⟨a, b, c, l, r, hnode,
      Or.inr ⟨d != e2, fun x hx => by rw [hvr x (hC.len x hx), hd x hx]⟩⟩
  -- The main case. Fix input `i` to the value that sticks the gate.
  have hC' := hC.restrict hiF (e1 != a)
  have hX' := hX.restrict hC hiF (e1 != a)
  have hFlen : (F.erase i).length = F.length - 1 := List.length_erase_of_mem hiF
  have hjF' : j ∈ F.erase i := (List.mem_erase_of_ne (Ne.symm hij)).mpr hjF
  have three : ∀ t1 t2 t3 : Nat, t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      Dead N (fixInput P i (e1 != a)) t1 → Dead N (fixInput P i (e1 != a)) t2 →
      Dead N (fixInput P i (e1 != a)) t3 → 3 * (F.length - 1) ≤ cost N := by
    intro t1 t2 t3 h12 h13 h23 d1 d2 d3
    obtain ⟨N', h1, h2, h3, h4⟩ := kill_three hN hC'.len h12 h13 h23 d1 d2 d3
    have := ih (cost N') (by omega) N' rfl h1 (F.erase i) _ hC' (hX'.congr h2 h4)
    omega
  have hi' : ∀ x, fixInput P i (e1 != a) x → val N x i = (e1 != a) := fun x hx => by
    rw [val_input N x i (by rw [hC.len x hx.1]; exact hi)]
    exact hx.2
  have hgc : ∀ x, fixInput P i (e1 != a) x → val N x (n + g) = c := by
    intro x hx
    rw [val_node hN (hC.len x hx.1) hnode, hvl x (hC.len x hx.1), hx.2]
    generalize val N x r = y
    cases e1 <;> cases a <;> cases b <;> cases c <;> cases y <;> rfl
  -- A second AND gate reads input `i`.
  have second : ∃ (h : Nat) (a' b' c' : Bool) (l' r' : Nat), h ≠ g ∧
      N[h]? = some ⟨Kind.and a' b' c', l', r'⟩ ∧
      ((∃ e, Alias n N i l' e) ∨ (∃ e, Alias n N i r' e)) := by
    apply Classical.byContradiction
    intro hno
    have hl0 := hC.len x0 hx0
    have hy : P (x0.set j (e2 != b)) := hC.free x0 hx0 j hjF _
    have h1 : P ((x0.set j (e2 != b)).set i true) := hC.free _ hy i hiF _
    have h2 : P ((x0.set j (e2 != b)).set i false) := hC.free _ hy i hiF _
    have gval : ∀ bi, val N ((x0.set j (e2 != b)).set i bi) (n + g) = c := by
      intro bi
      have hl : ((x0.set j (e2 != b)).set i bi).length = n := by
        rw [List.length_set, List.length_set]; exact hl0
      rw [val_node hN hl hnode, hvr _ hl, getD_set_ne hij, getD_set_self _ _ _ (by omega)]
      generalize val N ((x0.set j (e2 != b)).set i bi) l = y
      cases e2 <;> cases a <;> cases b <;> cases c <;> cases y <;> rfl
    have same := flow hN hN rfl i (fun _ _ => rfl) (hC.len _ h1) (hC.len _ h2)
      (fun w _ hw => by rw [getD_set_ne (Ne.symm hw), getD_set_ne (Ne.symm hw)])
      (fun t a' b' c' l' r' hn' _ hal' => by
        by_cases htg : t = g
        · subst htg
          rw [gval, gval]
        · exact absurd ⟨t, a', b', c', l', r', htg, hn', hal'⟩ hno)
    by_cases hout : ∃ e, Alias n N i (n + N.length - 1) e
    · obtain ⟨e, he⟩ := hout
      exact output_not_input_alias hN hC hX hF hi he
    · exact output_moves hC hX hiF hy (same _ hout)
  obtain ⟨h, a2, b2, c2, l2, r2, hhg, hnode2, hal2⟩ := second
  have dg : Dead N (fixInput P i (e1 != a)) g :=
    dead_of_alias hN hC'.len hnode (Or.inl ⟨e1, hali⟩) hi'
  have dh : Dead N (fixInput P i (e1 != a)) h := dead_of_alias hN hC'.len hnode2 hal2 hi'
  -- A stuck AND gate is read by a later AND gate, or the claim already holds.
  have next : ∀ (g1 : Nat) (a1 b1 c1 : Bool) (l1 r1 : Nat) (d : Bool),
      N[g1]? = some ⟨Kind.and a1 b1 c1, l1, r1⟩ →
      (∀ x, fixInput P i (e1 != a) x → val N x (n + g1) = d) →
      3 * (F.length - 1) ≤ cost N ∨ ∃ (q : Nat) (a' b' c' : Bool) (l' r' : Nat), g1 < q ∧
        N[q]? = some ⟨Kind.and a' b' c', l', r'⟩ ∧
        ((∃ e, Alias n N (n + g1) l' e) ∨ (∃ e, Alias n N (n + g1) r' e)) := by
    intro g1 a1 b1 c1 l1 r1 d hn1 hd1
    rcases reader_or_useless hN hn1 with
      ⟨q, a', b', c', l', r', hnq, halq⟩ | ⟨e, he⟩ | ⟨N', h1, h2, h3, h4⟩
    · right
      refine ⟨q, a', b', c', l', r', ?_, hnq, halq⟩
      have hq : l' < n + q ∧ r' < n + q := hN q _ hnq
      rcases halq with ⟨e, he⟩ | ⟨e, he⟩
      · have := he.le hN
        omega
      · have := he.le hN
        omega
    · exfalso
      exact output_not_const hC' hX' hjF' (d := (d != e))
        (fun x hx => by rw [he.val_eq hN x (hC'.len x hx), hd1 x hx])
    · left
      refine cheaper N' h1 h3 ?_
      obtain ⟨cc, hcc⟩ := hX
      exact ⟨cc, fun x hx => by rw [h4 x (hC.len x hx)]; exact hcc x hx⟩
  rcases next g a b c l r c hnode hgc with done | ⟨p, a3, b3, c3, l3, r3, hgp, hnode3, hal3⟩
  · exact done
  have dp : Dead N (fixInput P i (e1 != a)) p := dead_of_alias hN hC'.len hnode3 hal3 hgc
  by_cases hph : p = h
  case neg =>
    exact three g h p (Ne.symm hhg) (by omega) (Ne.symm hph) dg dh dp
  -- The gate that reads `g` is `h`: it reads `i` and `g`, so it is stuck too.
  subst hph
  rw [hnode2] at hnode3
  simp only [Option.some.injEq, Node.mk.injEq, Kind.and.injEq] at hnode3
  obtain ⟨_, hl3, hr3⟩ := hnode3
  subst hl3
  subst hr3
  have hpc : ∃ d, ∀ x, fixInput P i (e1 != a) x → val N x (n + p) = d := by
    rcases hal2 with ⟨e, he⟩ | ⟨e, he⟩ <;> rcases hal3 with ⟨e', he'⟩ | ⟨e', he'⟩
    · exact (Alias.not_input_and_gate hN hi hnode he he').elim
    · refine ⟨(Kind.and a2 b2 c2).op ((e1 != a) != e) (c != e'), fun x hx => ?_⟩
      rw [val_node hN (hC'.len x hx) hnode2, he.val_eq hN x (hC'.len x hx),
        he'.val_eq hN x (hC'.len x hx), hi' x hx, hgc x hx]
    · refine ⟨(Kind.and a2 b2 c2).op (c != e') ((e1 != a) != e), fun x hx => ?_⟩
      rw [val_node hN (hC'.len x hx) hnode2, he.val_eq hN x (hC'.len x hx),
        he'.val_eq hN x (hC'.len x hx), hi' x hx, hgc x hx]
    · exact (Alias.not_input_and_gate hN hi hnode he he').elim
  obtain ⟨d, hpd⟩ := hpc
  rcases next p a2 b2 c2 l2 r2 d hnode2 hpd with
    done | ⟨q, a4, b4, c4, l4, r4, hpq, hnode4, hal4⟩
  · exact done
  exact three g p q (by omega) (by omega) (by omega) dg dh
    (dead_of_alias hN hC'.len hnode4 hal4 hpd)

end PNP

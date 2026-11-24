/-!
# Circuits over the full binary basis

The object every lower bound in this folder talks about: a list of gates, each applying one of
the sixteen two-input Boolean functions to two earlier wires. Size is the number of gates.

Lean core only, no Mathlib, so the file stays light enough for a laptop.
-/

namespace PNP

/-- One gate: any two-input Boolean function, reading two earlier wires. -/
structure Gate where
  op : Bool → Bool → Bool
  left : Nat
  right : Nat

/-- `inputs` input wires, then one new wire per gate, in order. The last wire is the output. -/
structure Circuit where
  inputs : Nat
  gates : List Gate

namespace Circuit

/-- The number every lower bound is about. -/
def size (c : Circuit) : Nat := c.gates.length

/-- Every gate reads only wires that exist when it fires. -/
def WellFormed (c : Circuit) : Prop :=
  ∀ (i : Nat) (h : i < c.gates.length),
    c.gates[i].left < c.inputs + i ∧ c.gates[i].right < c.inputs + i

/-- Add the wire one gate computes. A missing wire reads as `false`; `WellFormed` rules that out. -/
def fire (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op (wires.getD g.left false) (wires.getD g.right false)]

/-- All wires after the circuit runs on input `x`. -/
def wires (c : Circuit) (x : List Bool) : List Bool :=
  c.gates.foldl fire x

def eval (c : Circuit) (x : List Bool) : Bool :=
  (c.wires x).getLastD false

/-- `c` gives the same answer as `f` on every input of the right length. -/
def Computes (c : Circuit) (f : List Bool → Bool) : Prop :=
  c.WellFormed ∧ ∀ x : List Bool, x.length = c.inputs → c.eval x = f x

end Circuit

/-- A lower bound: every circuit for `f` on `n` inputs has at least `k` gates. -/
def NeedsGates (n : Nat) (f : List Bool → Bool) (k : Nat) : Prop :=
  ∀ c : Circuit, c.inputs = n → c.Computes f → k ≤ c.size

/-- XOR of two inputs, one gate. -/
def xorPair : Circuit :=
  { inputs := 2, gates := [{ op := fun a b => a != b, left := 0, right := 1 }] }

example : xorPair.size = 1 := rfl
example : xorPair.eval [true, false] = true := rfl
example : xorPair.eval [true, true] = false := rfl

/-- XOR of exactly two inputs; any other input reads as `false`. -/
def xor2 : List Bool → Bool
  | [a, b] => a != b
  | _ => false

theorem xorPair_computes_xor2 : xorPair.Computes xor2 := by
  constructor
  · intro i h
    have hi : i = 0 := by
      have : i < 1 := h
      omega
    subst hi
    simp [xorPair]
  · intro x hx
    rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp [xorPair] at hx
    · simp [xorPair] at hx
    · cases a <;> cases b <;> rfl
    · simp [xorPair] at hx

/-- The first lower bound of the folder: no circuit computes XOR of two inputs with zero gates.
With no gates the output is the last input, and XOR is not that. -/
theorem xor2_needs_one_gate : NeedsGates 2 xor2 1 := by
  intro c _ hc
  cases hg : c.gates with
  | cons g gs => simp [Circuit.size, hg]
  | nil =>
    have h := hc.2 [true, true] (by simp [*])
    simp [Circuit.eval, Circuit.wires, hg, xor2] at h

end PNP

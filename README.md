# Two of Schnorr's gate elimination bounds, checked in Lean 4

Two old lower bounds on the size of Boolean circuits, with proofs checked by the Lean 4
kernel. Lean core only, no Mathlib, 2,395 lines.

| Theorem | Lean name | File |
|---|---|---|
| With no XOR or XNOR gates, parity of n inputs needs exactly 3(n − 1) gates. | `PNP.parity_exact_without_xor` | `PNP/Tight.lean` |
| With any two-input gates, "at least two inputs are on" needs at least 2n − 3 gates. | `PNP.Full.atLeastTwo_needs_two_gates_per_input` | `PNP/Threshold.lean` |
| The general form of the second: 2n − 3 gates for any function that keeps mixing each pair of its free inputs while inputs are fixed one at a time. | `PNP.Full.hard_needs_two_per_input` | `PNP/TwoN.lean` |

Both bounds go back to C. P. Schnorr in the 1970s. Nothing here is a new theorem. What is
offered is the machine check, and one idea that kept the proofs short: gates are never removed
and wires are never renumbered; a gate that has become useless is overwritten in place by a
free node.

The note in [`note/schnorr-lean.pdf`](note/schnorr-lean.pdf) has the statements, the model,
the proofs in words, and the limits.

## What to read if you want to trust it

Lean checks that each proof matches its statement. It cannot check that the statement is the
one intended. For that, read the definitions the theorems rest on, about 40 lines:
`Gate`, `Circuit`, `size`, `WellFormed`, `eval` and `Computes` in `PNP/Circuit.lean`,
`parity` in `PNP/Parity.lean`, `IsXorLike` in `PNP/NoXor.lean`, `ones` and `atLeastTwo` in
`PNP/Threshold.lean`. Section 2 of the note lists them with the choices made.

## Build and check

Needs [elan](https://github.com/leanprover/elan). The toolchain is pinned to Lean 4.36.0.
The build takes a few seconds.

```bash
lake build
lake env lean Axioms.lean
```

The second command should report `propext`, `Classical.choice` and `Quot.sound` for each
theorem, and nothing else. For a kernel replay of every compiled module, run the
`leanchecker` that ships with the toolchain:

```bash
lake env "$(dirname "$(elan which lean)")/leanchecker" PNP
```

An export of the three theorems was also checked with
[nanoda](https://github.com/ammkrn/nanoda_lib), an independent checker written in Rust:
2,694 declarations, no errors.

## How this was made

The Lean code and the note were written by an AI assistant (Claude Fable 5.2, in Claude Code)
under the direction of Santiago Gegenschatz. A separate AI referee pass tried to break the
note, re-ran the checks and ran the definitions on small circuits. No human has checked the
definitions line by line. If you find a definition that does not say what the note claims,
please open an issue.

## License

MIT, see [`LICENSE`](LICENSE).

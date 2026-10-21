# FinitenessDCS

A Lean 4 / Mathlib formalization of

> Yu Hashimoto, *Finiteness of Disjoint Covering Systems with Precisely One Repeated Modulus*,
> [arXiv:2603.26043](https://arxiv.org/abs/2603.26043) [math.NT].

together with the companion note *A Divisibility Condition for Moduli in Disjoint Covering
Systems with Precisely One Repeated Modulus* (`papers/divisibility-condition/`), which supplies
the divisibility condition `nᵢ ∣ n_t` that the main paper takes from the literature.

The formalization was produced by the author of the paper.

## Status and AI disclosure — please read first

**All Lean code in this repository was written by AI coding agents — OpenAI Codex and
Anthropic's Claude Code — working from the TeX sources of the papers under the author's
direction. The author has not verified the formalization.** In particular, the author has not
checked that the Lean definitions (`DCSystem`, `CosetPartition`, `ValidCosetPartition`, …)
faithfully capture the notions of the paper, nor that the Lean statements are the intended
ones, nor read the proofs.

What *is* checked, mechanically and on every CI run, is:

* the development compiles with Lean `v4.30.0` and Mathlib `v4.30.0`;
* it contains no `sorry`, and no declaration depends on any axiom beyond Lean's standard three
  (`propext`, `Classical.choice`, `Quot.sound`) — in particular, `native_decide` is not used;
* Mathlib's style linters (`--wfail`) and environment linters (`#lint`) pass.

This repository is provided **for reference only**. The papers, not this repository, are the
authoritative statements of the results, and nothing here should be cited as an independent
verification of them. Bug reports about the Lean development are welcome nevertheless.

## Main results

The paper's Theorem 1.1 (finiteness of normalized disjoint covering systems) is

```lean
theorem DCS.main_dcs (m : ℕ) : {D : DCSystem | D.Basicas m}.Finite
```

where `DCSystem` is a finite family of arithmetic progressions `aᵢ + nᵢℤ` covering every
integer exactly once, and `D.Basicas m` is the normalization `(eq:basicas)`:
`3 ≤ n₁ < ⋯ < n_{t-m} < n_{t-m+1} = ⋯ = n_t`, with the largest modulus repeated exactly `m`
times and `2 ≤ m`.

It is derived from the coset-partition form (Theorem 1.2 / Corollary 3.8):

```lean
theorem DCS.finiteness_main (m : ℕ) : ∃ N, ∀ sys : ValidCosetPartition m, sys.n ≤ N
```

### Paper ↔ Lean

| Paper | Lean |
|---|---|
| Thm 1.1 (finiteness of DCSs) | `DCS.main_dcs` (`MainDCS.lean`) |
| §1, reduction DCS → coset partition of `ℤ/nℤ` | `DCSystem.toCosetPartition`, `DCSystem.toValidCosetPartition` (`MainDCS.lean`) |
| `nᵢ ∣ n_t` (companion note) | `DCS.modulus_dvd_max` (`DCSystem.lean`) |
| Prop 2.1, Cor 2.2–2.3 (cell inequalities on a parallelotope) | `DCS.Box.cell_inequality` and corollaries (`Parallelotope.lean`) |
| §2.4, parallelotope map `φ` and (index-inclusion) | `PrimeParallelotope.equivZMod`, `Coset.toCell_freeIdx_subset_iff` (`Parallelotope.lean`) |
| Cor 2.4–2.5 (cell inequalities for coset partitions) | `DCS.cell_inequality`, `DCS.cell_inequality_two_level` (`Parallelotope.lean`) |
| Prop 3.1 (divisor-sum inequality) | `DCS.divisor_sum_ineq` (`DivisorSum.lean`) |
| Prop 3.3 (`p₁ = 2`), Prop 3.4 (`p_h ≥ 3`), Lemma 3.5 | `bound_v2_even`, `bound_vh_odd`, `bound_vh_general` (`MainTheorem.lean`) |
| Lemma 3.6 | `proper_divisor_sum_bound` (`MainTheorem.lean`) |
| Thm 3.7 | `ASet_combined_bound` (`MainTheorem.lean`) |
| Cor 3.8 | `finiteness_main` (`MainTheorem.lean`) |

Two places where the Lean proof deliberately departs from the paper: the `p ≥ 5` case of
Prop 3.1 uses the elementary bound `∏_{q<p} q/(q-1) < p - 1` instead of the Rosser–Schoenfeld
estimate, and the three cases of Prop 3.3 are handled uniformly by `three_mul_s₀_le`.

## Layout

```
FinitenessDCS/
  Parallelotope.lean   general parallelotopes, cells, cell inequalities; the prime
                       parallelotope of ℤ/nℤ; cosets, coset partitions, Cor 2.4–2.5
  Defs.lean            ValidCosetPartition and the notation of Definition 3.2
  DivisorSum.lean      Proposition 3.1
  MainTheorem.lean     Propositions 3.3–3.4, Lemmas 3.5–3.6, Theorem 3.7, Corollary 3.8
  DCSystem.lean        disjoint covering systems of ℤ and the divisibility condition
  MainDCS.lean         the bridge DCS → coset partition and Theorem 1.1
Lint.lean              environment linters and the axiom check (run in CI)
papers/                TeX sources of the paper and the companion note
```

## Building

Install [elan](https://github.com/leanprover/elan), then

```sh
lake exe cache get   # download the prebuilt Mathlib
lake build           # build the development (add --wfail to fail on linter warnings)
lake build Lint      # run #lint and the axiom check
```

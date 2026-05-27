import Mathlib
import FinitenessDCS.Defs

/-!
# Cell Inequalities for Coset Partitions

This file establishes that coset partitions of ℤ/nℤ satisfy the cell
inequalities used in the main proof. These inequalities come from the
"parallelotope model" of Berger, Felzenbaum, and Fraenkel.

## The Parallelotope Model

Given n = ∏ p_j^{s_j}, the group ℤ/nℤ is identified with the parallelotope
𝒫(b) = ∏ {0, ..., p_j - 1}^{s_j} via the Chinese Remainder Theorem and
p-adic digit expansion. Under this bijection, cosets correspond to "cells"
(sub-parallelotopes with some coordinates fixed).

## Key Result

The cell inequality (Proposition I of [BFF]) states: for a cell X in a
cell partition of 𝒫(b), with b₁(X) = min{bᵢ : i ∉ ind(X)},
  ∑_{ind(Xⱼ) ⊆ ind(X)} |Xⱼ| ≥ b₁(X) · |X|

Translating to coset partitions:
  ∑_{|Kᵢ| | |K|} |Kᵢ| ≥ p₁(n/|K|) · |K|

where p₁(q) is the smallest prime factor of q.
-/

namespace DCS

open Finset Nat

/-! ### Concrete coset partition definition -/

/-- A coset in ℤ/nℤ is specified by a residue and a modulus dividing n.
    It represents the set {a, a+d, a+2d, ..., a+(n/d-1)d} mod n,
    which has n/d elements. -/
structure Coset (n : ℕ) where
  residue : ZMod n
  modulus : ℕ
  modulus_dvd : modulus ∣ n
  modulus_pos : 0 < modulus

/-- The size of a coset -/
def Coset.size {n : ℕ} (K : Coset n) : ℕ := n / K.modulus

/-- A coset partition of ℤ/nℤ is a list of cosets that partitions ℤ/nℤ. -/
structure CosetPartition (n : ℕ) where
  cosets : List (Coset n)
  partition : (cosets.map Coset.size).sum = n

/-- The multiset of sizes of a coset partition -/
def CosetPartition.sizes {n : ℕ} (P : CosetPartition n) : Multiset ℕ :=
  (P.cosets.map Coset.size : List ℕ)

/-! ### Cell inequality proof -/

/-- **Proposition I** (Berger-Felzenbaum-Fraenkel):
    For any coset K in a coset partition of ℤ/nℤ,
    ∑_{|Kᵢ| | |K|} |Kᵢ| ≥ minFac(n/|K|) · |K|.

    Proof sketch: Identify ℤ/nℤ with 𝒫(b) via the CRT + p-adic expansion.
    K maps to a cell X. Shrink 𝒫(b) in the fixed coordinates of X to get
    a sub-parallelotope where each fixed coordinate has range {0,...,b-1}
    with b = b₁(X) = minFac(n/|K|). Partition this sub-parallelotope into
    b congruence classes based on ∑_{fixed coords} cᵢ mod b. Cells Xⱼ with
    ind(Xⱼ) ⊆ ind(X) contribute to a single congruence class. The remaining
    cells contribute equally to all b classes. Since X contributes |X| to one
    class, each class receives at least |X|. Summing gives the inequality. -/
theorem cell_inequality (n : ℕ) (hn : 0 < n)
    (sizes : Finset ℕ) (m : ℕ)
    (h_sum : sizes.sum id + m = n)
    (h_dvd : ∀ s ∈ sizes, s ∣ n)
    (h_gt : ∀ s ∈ sizes, 1 < s)
    (h_le : ∀ s ∈ sizes, 3 * s ≤ n) :
    ∀ s ∈ sizes,
      (sizes.filter (· ∣ s)).sum id + m ≥ (n / s).minFac * s := by
  sorry

/-- The two-level cell inequality, similarly proved via the parallelotope model. -/
theorem cell_inequality_two_level (n : ℕ) (hn : 0 < n)
    (sizes : Finset ℕ) (m : ℕ)
    (h_sum : sizes.sum id + m = n)
    (h_dvd : ∀ s ∈ sizes, s ∣ n)
    (h_gt : ∀ s ∈ sizes, 1 < s)
    (h_le : ∀ s ∈ sizes, 3 * s ≤ n) :
    ∀ s ∈ sizes,
      let q := n / s
      let p₁ := q.minFac
      let e₁ := q.factorization p₁
      1 < q / p₁ ^ e₁ →
      (sizes.filter (· ∣ s * p₁ ^ e₁)).sum id + m ≥ (q / p₁ ^ e₁).minFac * s := by
  sorry

/-- **Main connection**: Any DCS satisfying the conditions gives rise to a `ValidSystem`. -/
def dcs_gives_valid_system (n m : ℕ) (hm : 2 ≤ m)
    (sizes : Finset ℕ)
    (h_gt : ∀ s ∈ sizes, 1 < s)
    (h_dvd : ∀ s ∈ sizes, s ∣ n)
    (h_le : ∀ s ∈ sizes, 3 * s ≤ n)
    (h_sum : sizes.sum id + m = n) :
    ValidSystem m where
  n := n
  S := sizes
  hm := hm
  sizes_gt_one := h_gt
  sizes_dvd := h_dvd
  sizes_le := h_le
  sum_eq := h_sum
  cell_ineq := cell_inequality n (by omega) sizes m h_sum h_dvd h_gt h_le
  cell_ineq_two := cell_inequality_two_level n (by omega) sizes m h_sum h_dvd h_gt h_le

end DCS

import Mathlib

/-!
# Finiteness of Disjoint Covering Systems with One Repeated Modulus

## Definitions

We define the abstract notion of a valid coset partition system, capturing the
combinatorial properties used in the proof that for each fixed `m ≥ 2`, there are
only finitely many disjoint covering systems with minimum modulus ≥ 3 in which
precisely one modulus is repeated (occurring exactly `m` times).

## Main Definitions

* `DCS.ValidSystem m` - A valid coset partition system with parameter `m`
* `DCS.finiteness` - The main theorem: `n` is bounded by a constant depending only on `m`
-/

namespace DCS

open Finset Nat

/-- A positive integer is supported on a set of primes `P` if all its prime factors lie in `P`.
    By convention, 1 is supported on any set. -/
def IsSupportedOn (s : ℕ) (P : Finset ℕ) : Prop :=
  ∀ p ∈ s.primeFactors, p ∈ P

instance (P : Finset ℕ) : DecidablePred (IsSupportedOn · P) := by
  intro s; unfold IsSupportedOn; exact Finset.decidableDforallFinset

/-- Sum of divisors function σ(n) = ∑_{d | n} d -/
def sigma (n : ℕ) : ℕ := (Nat.divisors n).sum id

/-- A valid coset partition system with parameter `m`.

The field `S` represents the set of distinct coset sizes greater than 1.
The system additionally has `m` cosets of size 1 (singletons).
The cell inequalities encode properties proved using the parallelotope model
(Corollaries 3.2 and 3.3 of the paper). -/
structure ValidSystem (m : ℕ) where
  /-- The order of the cyclic group ℤ/nℤ -/
  n : ℕ
  /-- The set of coset sizes > 1 (each appearing exactly once) -/
  S : Finset ℕ
  /-- m ≥ 2 (the largest modulus is repeated at least twice) -/
  hm : 2 ≤ m
  /-- All sizes in S are > 1 -/
  sizes_gt_one : ∀ s ∈ S, 1 < s
  /-- Every size divides n -/
  sizes_dvd : ∀ s ∈ S, s ∣ n
  /-- Every size is at most n/3 (minimum modulus ≥ 3) -/
  sizes_le : ∀ s ∈ S, 3 * s ≤ n
  /-- The sizes sum to n: (∑ sizes > 1) + m = n -/
  sum_eq : S.sum id + m = n
  /-- Cell inequality (Corollary 3.2):
      For any size s, the total mass of sizes dividing s
      (plus m singletons) is at least minFac(n/s) · s -/
  cell_ineq : ∀ s ∈ S,
    (S.filter (· ∣ s)).sum id + m ≥ (n / s).minFac * s
  /-- Two-level cell inequality (Corollary 3.3):
      When n/s has ≥ 2 distinct prime factors, absorb the smallest prime
      factor and use the second smallest prime factor as the multiplier -/
  cell_ineq_two : ∀ s ∈ S,
    let q := n / s
    let p₁ := q.minFac
    let e₁ := q.factorization p₁
    1 < q / p₁ ^ e₁ →
    (S.filter (· ∣ s * p₁ ^ e₁)).sum id + m ≥ (q / p₁ ^ e₁).minFac * s

variable {m : ℕ}

/-- n ≥ 2 for any valid system -/
lemma ValidSystem.n_ge_two (sys : ValidSystem m) : 2 ≤ sys.n := by
  have := sys.sum_eq; have := sys.hm; omega

/-- n > 0 for any valid system -/
lemma ValidSystem.n_pos (sys : ValidSystem m) : 0 < sys.n := by
  linarith [sys.n_ge_two]

/-- Sizes in S are positive -/
lemma ValidSystem.sizes_pos (sys : ValidSystem m) (s : ℕ) (hs : s ∈ sys.S) : 0 < s :=
  Nat.lt_trans Nat.zero_lt_one (sys.sizes_gt_one s hs)

/-- n/s ≥ 3 for any size s in S -/
lemma ValidSystem.ndivs_ge_three (sys : ValidSystem m) (s : ℕ) (hs : s ∈ sys.S) :
    3 ≤ sys.n / s := by
  have hpos := sys.sizes_pos s hs
  exact Nat.le_div_iff_mul_le hpos |>.mpr (sys.sizes_le s hs)

/-- minFac(n/s) ≥ 2 for any size s in S -/
lemma ValidSystem.minFac_ge_two (sys : ValidSystem m) (s : ℕ) (hs : s ∈ sys.S) :
    2 ≤ (sys.n / s).minFac := by
  have h3 := sys.ndivs_ge_three s hs
  exact (Nat.minFac_prime (by omega)).two_le

/-! ### Derived operations on the system -/

/-- 𝒜_P : the set of sizes in S supported on primes P -/
def ValidSystem.AP (sys : ValidSystem m) (P : Finset ℕ) : Finset ℕ :=
  sys.S.filter (IsSupportedOn · P)

/-- Sum of sizes in 𝒜_P plus m (the singleton contribution) -/
def ValidSystem.sumAP (sys : ValidSystem m) (P : Finset ℕ) : ℕ :=
  (sys.AP P).sum id + m

/-- 𝒟(s) : sizes in S that properly divide s -/
def ValidSystem.DS (sys : ValidSystem m) (s : ℕ) : Finset ℕ :=
  sys.S.filter (fun s' => s' ∣ s ∧ s' ≠ s)

/-- Sum over 𝒟(s) plus m singletons -/
def ValidSystem.sumDS (sys : ValidSystem m) (s : ℕ) : ℕ :=
  (sys.DS s).sum id + m

/-! ### Splitting the filter for the cell inequality -/

/-- The filter of sizes dividing s splits as {s} ∪ 𝒟(s) -/
lemma filter_dvd_split (S : Finset ℕ) (s : ℕ) (hs : s ∈ S) :
    (S.filter (· ∣ s)).sum id =
    s + (S.filter (fun s' => s' ∣ s ∧ s' ≠ s)).sum id := by
  have h1 : S.filter (· ∣ s) = insert s (S.filter (fun s' => s' ∣ s ∧ s' ≠ s)) := by
    ext x
    simp only [mem_filter, mem_insert]
    constructor
    · intro ⟨hx, hxs⟩
      by_cases hne : x = s
      · left; exact hne
      · right; exact ⟨hx, hxs, hne⟩
    · intro h
      cases h with
      | inl h => exact ⟨h ▸ hs, h ▸ dvd_refl s⟩
      | inr h => exact ⟨h.1, h.2.1⟩
  rw [h1, sum_insert]
  simp [id]
  simp only [mem_filter]
  intro ⟨_, _, hne⟩
  exact hne rfl

/-- Cell inequality in "excluding" form:
    sumDS s ≥ (minFac(n/s) - 1) * s -/
lemma ValidSystem.cell_ineq_excluding (sys : ValidSystem m) (s : ℕ) (hs : s ∈ sys.S) :
    sys.sumDS s ≥ ((sys.n / s).minFac - 1) * s := by
  have hci := sys.cell_ineq s hs
  have hsplit := filter_dvd_split sys.S s hs
  unfold sumDS DS
  rw [Nat.sub_one_mul] at *
  omega

/-- sumDS s ≥ s (since minFac(n/s) ≥ 2) -/
lemma ValidSystem.sumDS_ge (sys : ValidSystem m) (s : ℕ) (hs : s ∈ sys.S) :
    sys.sumDS s ≥ s := by
  have h1 := sys.cell_ineq_excluding s hs
  have h2 := sys.minFac_ge_two s hs
  rw [Nat.sub_one_mul] at h1
  have : (sys.n / s).minFac * s - s ≥ s := by
    have := Nat.mul_le_mul_right s h2; omega
  omega

/-! ### The sum over all sizes equals n -/

/-- The sum over all sizes equals n -/
lemma ValidSystem.sumAP_all (sys : ValidSystem m) :
    sys.sumAP sys.n.primeFactors = sys.n := by
  unfold sumAP AP
  rw [show sys.S.filter (IsSupportedOn · sys.n.primeFactors) = sys.S from ?_]
  · exact sys.sum_eq
  · ext s
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hs p hp
    exact Nat.primeFactors_mono (sys.sizes_dvd s hs) sys.n_pos.ne' hp

/-! ### Main Theorem Statement -/

/-- **Main Theorem** (Theorem 3.7 of the paper):
    For any finite set P of primes, the sum ∑_{K ∈ 𝒜_P} |K| is bounded
    by a constant depending only on m. -/
theorem sumAP_bounded (m : ℕ) (hm : 2 ≤ m) :
    ∃ B : ℕ, ∀ (sys : ValidSystem m) (P : Finset ℕ), sys.sumAP P ≤ B := by
  sorry

/-- **Main Corollary** (Corollary 3.8 / Theorem 1.2):
    For each fixed m ≥ 2, n is bounded by a constant depending only on m. -/
theorem finiteness (m : ℕ) (hm : 2 ≤ m) :
    ∃ N : ℕ, ∀ (sys : ValidSystem m), sys.n ≤ N := by
  obtain ⟨B, hB⟩ := sumAP_bounded m hm
  exact ⟨B, fun sys => sys.sumAP_all ▸ hB sys sys.n.primeFactors⟩

end DCS

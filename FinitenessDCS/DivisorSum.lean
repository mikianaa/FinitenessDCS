import Mathlib
import FinitenessDCS.Defs

/-!
# Divisor-Sum Inequality (Proposition 3.1)

We prove that if `N ≤ σ(N/p) + C₀` where `p ≥ 3` is the largest prime
factor of `N`, then `N` is bounded by a function of `C₀` alone.

## Proof approach

The proof splits into cases:
- **p = 3**: Direct computation shows N = 2^a · 3^b with a, b bounded.
- **p ≥ 5**: We show ∏_{q<p, q prime} q/(q-1) < p - 1 by induction on p,
  which implies σ(M)/M < p - 1 where M = N/p^{ν_p(N)}, giving
  N · (1 - σ(M)/((p-1)M)) ≤ C₀ and hence N is bounded.
-/

namespace DCS

open Finset Nat

/-! ### Product bound over primes

We prove ∏_{q ≤ p', q prime} q < (p'-1) · ∏_{q ≤ p', q prime} (q-1) for p' ≥ 5.
Equivalently, ∏_{q ≤ p'} q/(q-1) < p' - 1. This is a consequence of the
inductive bound and the gap between consecutive primes. -/

/-- The product of primes up to n -/
def primorial (n : ℕ) : ℕ := (Finset.filter Nat.Prime (Finset.range (n + 1))).prod id

/-- The product of (p-1) for primes p up to n -/
def phiProd (n : ℕ) : ℕ := (Finset.filter Nat.Prime (Finset.range (n + 1))).prod (· - 1)

/-
Key bound: primorial(n) < n · phiProd(n) for n ≥ 4.
    This is equivalent to ∏_{p ≤ n} p/(p-1) < n.
-/
theorem primorial_lt_mul_phiProd (n : ℕ) (hn : 4 ≤ n) :
    primorial n < n * phiProd n := by
  induction' n, hn using Nat.le_induction with n ih;
  · native_decide +revert;
  · by_cases h : Nat.Prime ( n + 1 ) <;> simp_all +decide [ primorial, phiProd ];
    · simp_all +decide [ Finset.prod_filter, Finset.prod_range_succ ];
      split_ifs at * <;> nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ];
    · simp_all +decide [ Finset.prod_filter, Finset.prod_range_succ ];
      lia

/-
σ(M)/M < p - 1 when all prime factors of M are < p and p ≥ 5.
    Stated multiplicatively: σ(M) * 1 < (p-1) * M.
-/
theorem sigma_lt_mul (M p : ℕ) (hM : 0 < M) (hp : 5 ≤ p)
    (h_supp : ∀ q : ℕ, q.Prime → q ∣ M → q < p) :
    sigma M < (p - 1) * M := by
  -- By the properties of the sum of divisors function, we know that $\sum_{d \mid M} d \leq \prod_{q \mid M} \frac{q}{q-1} \cdot M$.
  have h_sum_divisors : (∑ d ∈ Nat.divisors M, d) ≤ (Finset.prod (Nat.primeFactors M) (fun q => q / (q - 1 : ℚ))) * M := by
    -- By the properties of the sum of divisors function, we know that $\sum_{d \mid M} d = \prod_{q \mid M} \left(1 + q + q^2 + \cdots + q^{e_q}\right)$.
    have h_sum_divisors : (∑ d ∈ Nat.divisors M, d) = (∏ q ∈ Nat.primeFactors M, (∑ i ∈ Finset.range (Nat.factorization M q + 1), q^i)) := by
      grind +suggestions;
    -- Each term in the product $\prod_{q \mid M} \left(1 + q + q^2 + \cdots + q^{e_q}\right)$ is less than or equal to $\frac{q}{q-1} \cdot q^{e_q}$.
    have h_term_le : ∀ q ∈ Nat.primeFactors M, (∑ i ∈ Finset.range (Nat.factorization M q + 1), q^i : ℚ) ≤ (q / (q - 1 : ℚ)) * q^(Nat.factorization M q) := by
      intro q hq; rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_num [ geom_sum_eq, Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hq ) ] ;
      rw [ geom_sum_mul ] ; ring_nf ; norm_num;
    convert Finset.prod_le_prod ?_ h_term_le <;> norm_cast ; simp_all +decide [ Finset.prod_mul_distrib ];
    · exact Or.inl <| mod_cast Eq.symm <| Nat.factorization_prod_pow_eq_self hM.ne';
    · exact fun _ _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _;
  -- Since all prime factors of $M$ are less than $p$, we have $\prod_{q \mid M} \frac{q}{q-1} \leq \prod_{q < p} \frac{q}{q-1}$.
  have h_prod_le : (Finset.prod (Nat.primeFactors M) (fun q => q / (q - 1 : ℚ))) ≤ (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q / (q - 1 : ℚ))) := by
    rw [ ← Finset.prod_sdiff <| show M.primeFactors ⊆ Finset.filter Nat.Prime ( Finset.range p ) from fun q hq => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| h_supp q ( Nat.prime_of_mem_primeFactors hq ) <| Nat.dvd_of_mem_primeFactors hq, Nat.prime_of_mem_primeFactors hq ⟩ ];
    exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ) ( by exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun x hx => show ( x : ℚ ) / ( x - 1 ) ≥ 1 from by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;> linarith [ show ( x : ℚ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ( by aesop ) ] ) );
  -- By the properties of the primorial function, we know that $\prod_{q < p} \frac{q}{q-1} < p - 1$.
  have h_primorial_lt : (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q / (q - 1 : ℚ))) < (p - 1 : ℚ) := by
    have h_primorial_lt : (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q)) < (p - 1 : ℚ) * (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q - 1)) := by
      convert primorial_lt_mul_phiProd ( p - 1 ) ( Nat.le_sub_one_of_lt hp ) using 1;
      rcases p with ( _ | _ | p ) <;> norm_num [ primorial, phiProd ] at *;
      rw [ ← @Nat.cast_lt ℚ ] ; norm_num [ Finset.prod_filter, Finset.prod_range_succ' ];
    simp_all +decide [ Finset.prod_div_distrib ];
    rw [ div_lt_iff₀ ];
    · convert h_primorial_lt using 1;
      exact congrArg _ ( Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_pred ( Nat.Prime.pos ( by aesop ) ) ] );
    · exact Finset.prod_pos fun x hx => sub_pos.mpr <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hx |>.2;
  rcases p with ( _ | _ | p ) <;> simp_all +decide [ sigma ];
  rw [ ← @Nat.cast_lt ℚ ] ; push_cast ; nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ M ) ]

/-! ### Main divisor-sum inequality -/

/-- **Proposition 3.1** (Divisor-sum inequality):
    For each C₀, there exists B depending only on C₀ such that
    for any N with largest prime p ≥ 3, if N ≤ σ(N/p) + C₀,
    then p ≤ B and N ≤ B. -/
theorem divisor_sum_ineq (C₀ : ℕ) :
    ∃ B : ℕ, ∀ (N p : ℕ), 1 < N → p.Prime → 3 ≤ p → p ∣ N →
      (∀ q : ℕ, q.Prime → q ∣ N → q ≤ p) →
      N ≤ sigma (N / p) + C₀ →
      p ≤ B ∧ N ≤ B := by
  sorry

end DCS
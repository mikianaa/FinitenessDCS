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
open scoped ArithmeticFunction.sigma

/-! ### Product bound over primes

We prove ∏_{q ≤ p', q prime} q < (p'-1) · ∏_{q ≤ p', q prime} (q-1) for p' ≥ 5.
Equivalently, ∏_{q ≤ p'} q/(q-1) < p' - 1. This is a consequence of the
inductive bound and the gap between consecutive primes. -/

/-- The product of primes up to n -/
def primorial (n : ℕ) : ℕ := (Finset.filter Nat.Prime (Finset.range (n + 1))).prod id

/-- The product of (p-1) for primes p up to n -/
def phiProd (n : ℕ) : ℕ := (Finset.filter Nat.Prime (Finset.range (n + 1))).prod (· - 1)

/-- Key bound: `primorial n < n · phiProd n` for `n ≥ 4`, i.e. `∏_{p ≤ n} p/(p-1) < n`. -/
theorem primorial_lt_mul_phiProd (n : ℕ) (hn : 4 ≤ n) :
    primorial n < n * phiProd n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    by_cases h : Nat.Prime ( n + 1 ) <;> simp_all +decide [ primorial, phiProd ];
    · simp_all +decide [ Finset.prod_filter, Finset.prod_range_succ ];
      split_ifs at * <;> nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ];
    · simp_all +decide [ Finset.prod_filter, Finset.prod_range_succ ];
      lia

-- The proof below was machine-generated and closes goals with ad-hoc `simp_all` calls;
-- the flexible-tactic and multi-goal style linters are switched off for it only.
set_option linter.flexible false in
set_option linter.style.multiGoal false in
/-- `σ(M)/M < p - 1` when all prime factors of `M` are `< p` and `p ≥ 5`,
    stated multiplicatively as `σ(M) < (p - 1) · M`. -/
theorem sigma_lt_mul (M p : ℕ) (hM : 0 < M) (hp : 5 ≤ p)
    (h_supp : ∀ q : ℕ, q.Prime → q ∣ M → q < p) :
    σ 1 M < (p - 1) * M := by
  -- ∑_{d ∣ M} d ≤ (∏_{q ∣ M} q/(q-1)) · M.
  have h_sum_divisors : (∑ d ∈ Nat.divisors M, d)
      ≤ (Finset.prod (Nat.primeFactors M) (fun q => q / (q - 1 : ℚ))) * M := by
    -- ∑_{d ∣ M} d = ∏_{q ∣ M} (1 + q + ⋯ + q^{e_q}).
    have h_sum_divisors : (∑ d ∈ Nat.divisors M, d)
        = (∏ q ∈ Nat.primeFactors M,
            (∑ i ∈ Finset.range (Nat.factorization M q + 1), q^i)) := by
      grind +suggestions;
    -- Each factor 1 + q + ⋯ + q^{e_q} is at most q/(q-1) · q^{e_q}.
    have h_term_le : ∀ q ∈ Nat.primeFactors M,
        (∑ i ∈ Finset.range (Nat.factorization M q + 1), q^i : ℚ)
          ≤ (q / (q - 1 : ℚ)) * q^(Nat.factorization M q) := by
      intro q hq
      rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;>
        norm_num [ geom_sum_eq, Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hq ) ] ;
      rw [ geom_sum_mul ] ; ring_nf ; norm_num;
    convert Finset.prod_le_prod ?_ h_term_le <;> norm_cast ;
    simp_all +decide [ Finset.prod_mul_distrib ];
    · exact Or.inl <| mod_cast Eq.symm <| Nat.prod_factorization_pow_eq_self hM.ne';
    · exact fun _ _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _;
  -- All primes of M are < p, so ∏_{q ∣ M} q/(q-1) ≤ ∏_{q < p} q/(q-1).
  have h_prod_le : (Finset.prod (Nat.primeFactors M) (fun q => q / (q - 1 : ℚ)))
      ≤ (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q / (q - 1 : ℚ))) := by
    have hsub : M.primeFactors ⊆ Finset.filter Nat.Prime (Finset.range p) := by
      intro q hq
      have hq' := Nat.prime_of_mem_primeFactors hq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (h_supp q hq' (Nat.dvd_of_mem_primeFactors hq)), hq'⟩
    rw [ ← Finset.prod_sdiff hsub ];
    exact le_mul_of_one_le_left
      ( Finset.prod_nonneg fun _ _ => div_nonneg ( Nat.cast_nonneg _ )
        ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) )
      ( by
        exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity )
          fun x hx => show ( x : ℚ ) / ( x - 1 ) ≥ 1 from by
            rw [ ge_iff_le ] ; rw [ le_div_iff₀ ] <;>
              linarith [ show ( x : ℚ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ( by aesop ) ] ) );
  -- ∏_{q < p} q/(q-1) < p - 1.
  have h_primorial_lt :
      (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q / (q - 1 : ℚ)))
        < (p - 1 : ℚ) := by
    have h_primorial_lt :
        (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q))
          < (p - 1 : ℚ) *
            (Finset.prod (Finset.filter Nat.Prime (Finset.range p)) (fun q => q - 1)) := by
      convert primorial_lt_mul_phiProd ( p - 1 ) ( Nat.le_sub_one_of_lt hp ) using 1;
      rcases p with ( _ | _ | p ) <;> norm_num [ primorial, phiProd ] at *;
      rw [ ← @Nat.cast_lt ℚ ] ; norm_num [ Finset.prod_filter, Finset.prod_range_succ' ];
    simp_all +decide [ Finset.prod_div_distrib ];
    rw [ div_lt_iff₀ ];
    · convert h_primorial_lt using 1;
      exact congrArg _ ( Finset.prod_congr rfl fun x hx => by
        rw [ Nat.cast_pred ( Nat.Prime.pos ( by aesop ) ) ] );
    · exact Finset.prod_pos fun x hx =>
        sub_pos.mpr <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hx |>.2;
  rcases p with ( _ | _ | p ) <;> simp_all +decide [ ArithmeticFunction.sigma_one_apply ];
  rw [ ← @Nat.cast_lt ℚ ] ; push_cast ; nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ M ) ]

/-! ### p = 3 case: closed form of σ(2^a · 3^k) -/

/-- The geometric sum `1 + 2 + ⋯ + 2^a = 2^(a+1) - 1`. -/
lemma sum_two_pow (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (2 : ℕ)^i) + 1 = 2^(a+1) := by
  have := geom_sum_mul_add (1 : ℕ) (a + 1)
  simpa using this

/-- The geometric sum `2·(1 + 3 + ⋯ + 3^k) + 1 = 3^(k+1)`. -/
lemma sum_three_pow (k : ℕ) :
    2 * (∑ i ∈ Finset.range (k + 1), (3 : ℕ)^i) + 1 = 3^(k+1) := by
  have h := geom_sum_mul_add (2 : ℕ) (k + 1)
  -- `geom_sum_mul_add 2 n` gives `(∑ i ∈ range n, (2+1)^i) * 2 + 1 = (2+1)^n`
  -- We need to rewrite `(2+1)` as `3`.
  have h3 : (2 + 1 : ℕ) = 3 := rfl
  rw [h3] at h
  linarith

/-- Closed form: `2 · σ(2^a · 3^k) = (2^(a+1) - 1) · (3^(k+1) - 1)`.
    Stated multiplicatively to avoid integer division. -/
lemma two_mul_sigma_two_pow_mul_three_pow (a k : ℕ) :
    2 * σ 1 (2^a * 3^k) = (2^(a+1) - 1) * (3^(k+1) - 1) := by
  -- Multiplicativity: σ(2^a · 3^k) = σ(2^a) · σ(3^k) since gcd(2^a, 3^k) = 1
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_sigma
        (Nat.Coprime.pow a k (by decide : Nat.Coprime 2 3))]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
  -- Goal: 2 * (∑ i ∈ range(a+1), 2^i) * (∑ j ∈ range(k+1), 3^j)
  --     = (2^(a+1) - 1) * (3^(k+1) - 1)
  have h2 := sum_two_pow a
  have h3 := sum_three_pow k
  -- From h2: ∑ 2^i = 2^(a+1) - 1; from h3: 2 * ∑ 3^j = 3^(k+1) - 1
  -- The product 2 * S₂ * S₃ rearranges to S₂ * (2 * S₃)
  set S₂ := ∑ i ∈ Finset.range (a + 1), (2 : ℕ)^i with hS₂
  set S₃ := ∑ i ∈ Finset.range (k + 1), (3 : ℕ)^i with hS₃
  have hS₂_eq : S₂ = 2^(a+1) - 1 := by omega
  have h2S₃_eq : 2 * S₃ = 3^(k+1) - 1 := by omega
  calc 2 * (S₂ * S₃) = S₂ * (2 * S₃) := by ring
    _ = (2^(a+1) - 1) * (3^(k+1) - 1) := by rw [hS₂_eq, h2S₃_eq]

/-- If every prime factor of `N` is at most 3, then `N = 2^a · 3^b` where
    `a = ν₂(N)` and `b = ν₃(N)`. -/
lemma decomp_two_three (N : ℕ) (hN : 0 < N)
    (h_supp : ∀ q : ℕ, q.Prime → q ∣ N → q ≤ 3) :
    N = 2 ^ N.factorization 2 * 3 ^ N.factorization 3 := by
  have hN0 : N ≠ 0 := hN.ne'
  -- The support of the factorization of N is contained in {2, 3}.
  have hsupp : N.factorization.support ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ 3 := h_supp p hpp hpdvd
    have hpge : 2 ≤ p := hpp.two_le
    interval_cases p
    · simp
    · simp
  -- Rewrite N as the product over its factorization.
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
  -- Extend the product from N.factorization.support to {2, 3}.
  rw [Finsupp.prod_of_support_subset _ hsupp (· ^ ·) (fun _ _ => pow_zero _)]
  -- Now: ∏ p ∈ {2, 3}, p^(N.factorization p) = 2^(N.factorization 2) * 3^(N.factorization 3)
  rw [show ({2, 3} : Finset ℕ) = insert 2 {3} from rfl,
      Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)),
      Finset.prod_singleton]

/-- Algebraic helper: `A·B + 1 = (A-1)(B-1) + A + B` when `A, B ≥ 1`.
    Avoids ℕ subtraction headaches by reducing to a polynomial identity. -/
lemma mul_succ_pred_identity (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    A * B + 1 = (A - 1) * (B - 1) + (A + B) := by
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- **p = 3 case** of the divisor-sum inequality. -/
lemma divisor_sum_ineq_three (C₀ : ℕ) :
    ∃ B : ℕ, ∀ (N : ℕ), 1 < N → 3 ∣ N →
      (∀ q : ℕ, q.Prime → q ∣ N → q ≤ 3) →
      N ≤ σ 1 (N / 3) + C₀ →
      N ≤ B := by
  refine ⟨(2*C₀ + 1) * (2*C₀ + 1), ?_⟩
  intro N hN h3 h_supp h_ineq
  have hN_pos : 0 < N := by omega
  have hN0 : N ≠ 0 := hN_pos.ne'
  -- Decompose N = 2^a · 3^b.
  set a := N.factorization 2 with ha_def
  set b := N.factorization 3 with hb_def
  have h_decomp : N = 2^a * 3^b := decomp_two_three N hN_pos h_supp
  -- b ≥ 1 since 3 ∣ N.
  have hb : 1 ≤ b := by
    rw [hb_def]
    exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_three hN0 h3)
  -- N / 3 = 2^a · 3^(b-1).
  have hN_div : N / 3 = 2^a * 3^(b - 1) := by
    rw [h_decomp]
    have h3b : 3^b = 3^(b - 1) * 3 := by
      rw [← pow_succ]; congr 1; omega
    rw [h3b, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num : 0 < 3)]
  -- Closed form for 2·σ(N/3).
  have h_sigma : 2 * σ 1 (N / 3) = (2^(a+1) - 1) * (3^b - 1) := by
    rw [hN_div]
    have h := two_mul_sigma_two_pow_mul_three_pow a (b - 1)
    have h_eq : b - 1 + 1 = b := by omega
    rw [h_eq] at h
    exact h
  -- Lower bounds on the powers.
  have hA : 2 ≤ 2^(a+1) := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^(a+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBound : 3 ≤ 3^b := by
    calc 3 = 3^1 := by norm_num
      _ ≤ 3^b := Nat.pow_le_pow_right (by norm_num) hb
  -- 2N = 2^(a+1) · 3^b.
  have h_2N : 2 * N = 2^(a+1) * 3^b := by rw [h_decomp]; ring
  -- From N ≤ σ(N/3) + C₀ we get 2N ≤ 2σ(N/3) + 2C₀.
  have h_2N_ineq : 2 * N ≤ 2 * σ 1 (N / 3) + 2 * C₀ := by linarith
  rw [h_2N, h_sigma] at h_2N_ineq
  -- 2^(a+1) · 3^b ≤ (2^(a+1) - 1)(3^b - 1) + 2C₀
  -- Combined with the identity AB + 1 = (A-1)(B-1) + A + B (A,B ≥ 1),
  -- we get A + B ≤ 2C₀ + 1.
  have h_id := mul_succ_pred_identity (2^(a+1)) (3^b) (by omega) (by omega)
  -- h_id : 2^(a+1) * 3^b + 1 = (2^(a+1) - 1) * (3^b - 1) + (2^(a+1) + 3^b)
  have h_bound : 2^(a+1) + 3^b ≤ 2 * C₀ + 1 := by omega
  -- Extract individual bounds.
  have h2pow : 2 ^ a ≤ C₀ := by
    have h_pow : 2 * 2^a = 2^(a+1) := by ring
    omega
  have h3pow : 3^b ≤ 2 * C₀ + 1 := by omega
  -- N = 2^a · 3^b ≤ C₀ · (2C₀ + 1) ≤ (2C₀ + 1)².
  rw [h_decomp]
  calc 2^a * 3^b
      ≤ C₀ * (2 * C₀ + 1) := Nat.mul_le_mul h2pow h3pow
    _ ≤ (2*C₀ + 1) * (2*C₀ + 1) := by nlinarith

/-! ### p ≥ 5 case: building blocks -/

/-- Closed form: `(p - 1) · σ(p^k) = p^(k+1) - 1` for prime `p`. -/
lemma sigma_prime_pow_mul_pred {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p - 1) * σ 1 (p^k) = p^(k+1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  have hp2 : 2 ≤ p := hp.two_le
  have h := geom_sum_mul_add (p - 1) (k + 1)
  rw [show p - 1 + 1 = p from by omega] at h
  -- h : (∑ i ∈ range (k + 1), p ^ i) * (p - 1) + 1 = p ^ (k + 1)
  rw [mul_comm] at h
  -- h : (p - 1) * (∑ i ∈ range (k + 1), p ^ i) + 1 = p ^ (k + 1)
  have hpow_pos : 1 ≤ p^(k+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- σ multiplicativity, specialized to ℕ. -/
lemma sigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    σ 1 (m * n) = σ 1 m * σ 1 n :=
  ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    ArithmeticFunction.isMultiplicative_sigma h

set_option maxHeartbeats 1000000 in
-- The bound extraction below uses several large `nlinarith` calls.
/-- **p ≥ 5 case** of the divisor-sum inequality. -/
lemma divisor_sum_ineq_five (C₀ : ℕ) :
    ∃ B : ℕ, ∀ (N p : ℕ), 1 < N → p.Prime → 5 ≤ p → p ∣ N →
      (∀ q : ℕ, q.Prime → q ∣ N → q ≤ p) →
      N ≤ σ 1 (N / p) + C₀ →
      p ≤ B ∧ N ≤ B := by
  -- We pick B := (C₀+1)^4, generously upper-bounding both sub-cases (e≥2 and e=1).
  refine ⟨(C₀ + 1)^4, ?_⟩
  intro N p hN hp hp5 hpN h_supp h_ineq
  -- ============= Setup =============
  have hN_pos : 0 < N := by omega
  have hN0 : N ≠ 0 := hN_pos.ne'
  -- e := ν_p(N), M := N / p^e is the p-coprime part.
  set e := N.factorization p with he_def
  set M := ordCompl[p] N with hM_def
  -- e ≥ 1 since p ∣ N.
  have he_pos : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp hN0 hpN
  -- The decomposition N = p^e · M.
  have hN_eq : N = p^e * M := by
    have h := Nat.ordProj_mul_ordCompl_eq_self N p
    -- ordProj[p] N = p ^ (N.factorization p) = p^e by definition
    exact h.symm
  have hM_pos : 0 < M := Nat.ordCompl_pos p hN0
  have hcop : Nat.Coprime p M := Nat.coprime_ordCompl hp hN0
  -- p does not divide M (consequence of coprimality with prime p).
  have hp_not_dvd_M : ¬ p ∣ M := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  -- All primes of M are strictly less than p.
  have hM_supp : ∀ q : ℕ, q.Prime → q ∣ M → q < p := by
    intro q hq hqM
    have hqN : q ∣ N := hqM.trans (Nat.ordCompl_dvd N p)
    have hqp : q ≤ p := h_supp q hq hqN
    have hqne : q ≠ p := fun hqe => hp_not_dvd_M (hqe ▸ hqM)
    omega
  -- σ(M) < (p-1)·M from the already-proven Mertens-type bound.
  have h_sigma_M : σ 1 M < (p - 1) * M := sigma_lt_mul M p hM_pos hp5 hM_supp
  -- N/p = p^(e-1) · M.
  have hN_div : N / p = p^(e - 1) * M := by
    rw [hN_eq]
    have hpe : p^e = p * p^(e - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpe, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  -- ============= Core sigma identity =============
  -- gcd(p^(e-1), M) = 1
  have hcop_pow : Nat.Coprime (p^(e - 1)) M := by
    have h := Nat.Coprime.pow (e - 1) 1 hcop
    simpa using h
  -- (p - 1) * sigma(N/p) = (p^e - 1) * σ 1 M.
  have h_sigma_N_div : (p - 1) * σ 1 (N / p) = (p^e - 1) * σ 1 M := by
    rw [hN_div, sigma_mul_of_coprime hcop_pow, ← mul_assoc,
        sigma_prime_pow_mul_pred hp (e - 1), show e - 1 + 1 = e from by omega]
  -- ============= Core inequality: p^e + M ≤ (p-1)·C₀ =============
  -- Multiply the hypothesis by (p-1).
  have hp_pred_pos : 1 ≤ p - 1 := by omega
  have h_mul : (p - 1) * N ≤ (p - 1) * σ 1 (N / p) + (p - 1) * C₀ := by
    calc (p - 1) * N
        ≤ (p - 1) * (σ 1 (N / p) + C₀) := Nat.mul_le_mul_left _ h_ineq
      _ = (p - 1) * σ 1 (N / p) + (p - 1) * C₀ := by ring
  -- σ(M) ≥ M (since M is a divisor of itself when M ≥ 1).
  have h_sigma_ge_M : M ≤ σ 1 M := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self M hM_pos.ne')
  -- p^e ≥ 1 and p^e ≥ p (since e ≥ 1).
  have hpe_pos : 1 ≤ p^e := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpe_ge_p : p ≤ p^e := by
    calc p = p^1 := (pow_one p).symm
      _ ≤ p^e := Nat.pow_le_pow_right (by omega) he_pos
  -- Substitute the identity and N = p^e * M into h_mul.
  rw [h_sigma_N_div] at h_mul
  rw [hN_eq] at h_mul
  -- h_mul : (p-1) * (p^e * M) ≤ (p^e - 1) * σ 1 M + (p-1) * C₀
  -- We want: p^e + M ≤ (p-1) * C₀
  -- Key algebra: (p-1)*p^e*M - (p^e-1)*σM = p^e * ((p-1)M - σM) + σM ≥ p^e + σM ≥ p^e + M.
  have h_core : p^e + M ≤ (p - 1) * C₀ := by
    -- Multiply out: (p-1)*p^e*M = p^e * (p-1)*M
    -- (p-1)*M ≥ σM + 1 from h_sigma_M.
    -- (p^e - 1) * σM + σM = p^e * σM (since p^e ≥ 1).
    have h1 : (p^e - 1) * σ 1 M + σ 1 M = p^e * σ 1 M := by
      rw [Nat.sub_one_mul]
      exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hpe_pos)
    -- Substitute and rearrange
    nlinarith [h_mul, h_sigma_M, h_sigma_ge_M, hpe_pos, hpe_ge_p,
               mul_pos (by omega : 0 < p^e) hM_pos, h1, hM_pos, hp5]
  -- ============= Bound extraction (case split on e) =============
  by_cases h_e_two : 2 ≤ e
  -- Case 1: e ≥ 2.  Then p ≤ C₀, p^e ≤ (C₀+1)², M ≤ (C₀+1)².
  · have hp_pow2 : p^2 ≤ p^e := Nat.pow_le_pow_right hp.pos h_e_two
    have hp_le_C0 : p ≤ C₀ := by
      -- p*p = p² ≤ p^e ≤ (p-1)*C₀ ≤ p*C₀, then cancel p (positive)
      have h_pp_pc : p * p ≤ p * C₀ := by
        calc p * p = p^2 := by ring
          _ ≤ p^e := hp_pow2
          _ ≤ (p - 1) * C₀ := by linarith
          _ ≤ p * C₀ := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      exact Nat.le_of_mul_le_mul_left h_pp_pc hp.pos
    have hp_minus_le : p - 1 ≤ p := Nat.sub_le _ _
    have hpe_le : p^e ≤ p * C₀ := by
      have h_pred : (p - 1) * C₀ ≤ p * C₀ := Nat.mul_le_mul_right _ hp_minus_le
      linarith
    have hM_le : M ≤ p * C₀ := by
      have h_pred : (p - 1) * C₀ ≤ p * C₀ := Nat.mul_le_mul_right _ hp_minus_le
      linarith
    have hpe_le_sq : p^e ≤ (C₀ + 1)^2 := by nlinarith [hpe_le, hp_le_C0]
    have hM_le_sq : M ≤ (C₀ + 1)^2 := by nlinarith [hM_le, hp_le_C0]
    refine ⟨?_, ?_⟩
    · nlinarith [hp_le_C0]
    · rw [hN_eq]
      calc p^e * M
          ≤ (C₀ + 1)^2 * (C₀ + 1)^2 := Nat.mul_le_mul hpe_le_sq hM_le_sq
        _ = (C₀ + 1)^4 := by ring
  -- Case 2: e = 1.  Use σ(M) ≤ M² to bound everything in terms of C₀.
  · have he_one : e = 1 := by omega
    -- N = p * M (after e = 1 substitution).
    have h_eq : N = p * M := by rw [hN_eq, he_one, pow_one]
    -- N / p = M.
    have h_div_eq : N / p = M := by
      rw [h_eq]; exact Nat.mul_div_cancel_left M hp.pos
    -- p * M ≤ σ M + C₀ (from the original hypothesis).
    have h_pM_orig : p * M ≤ σ 1 M + C₀ := by
      have h := h_ineq
      rw [h_div_eq] at h
      linarith [h_eq ▸ h]
    -- M ≤ C₀ - 1 (from the strict bound σ(M) < (p-1)M combined with h_pM_orig).
    have h_alg : (p - 1) * M + M = p * M := by
      rw [Nat.sub_one_mul]
      exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hp.pos)
    have h_M_bd : M + 1 ≤ C₀ := by omega
    -- σ(M) ≤ M² from Mathlib.
    have h_sigma_le_M2 : σ 1 M ≤ M * M := by
      have h := ArithmeticFunction.sigma_le_pow_succ 1 M
      -- h : σ 1 M ≤ M^(1+1)
      have hM2 : M^(1 + 1) = M * M := by ring
      rw [hM2] at h
      exact h
    -- p * M ≤ M² + C₀ ≤ (C₀+1)².
    have h_pM_le_sq : p * M ≤ (C₀ + 1)^2 := by
      calc p * M
          ≤ σ 1 M + C₀ := h_pM_orig
        _ ≤ M^2 + C₀ := by linarith
        _ ≤ (C₀ + 1)^2 := by nlinarith [h_M_bd, hM_pos]
    have h_N_bd : N ≤ (C₀ + 1)^2 := by rw [h_eq]; exact h_pM_le_sq
    refine ⟨?_, ?_⟩
    · -- p ≤ pM (since M ≥ 1) ≤ (C₀+1)² ≤ (C₀+1)^4.
      have hp_le_pM : p ≤ p * M := Nat.le_mul_of_pos_right _ hM_pos
      have hp_le_sq : p ≤ (C₀ + 1)^2 := le_trans hp_le_pM h_pM_le_sq
      nlinarith [hp_le_sq]
    · nlinarith [h_N_bd]

/-- **Proposition 3.1** (Divisor-sum inequality):
    For each C₀, there exists B depending only on C₀ such that
    for any N with largest prime p ≥ 3, if N ≤ σ(N/p) + C₀,
    then p ≤ B and N ≤ B. -/
theorem divisor_sum_ineq (C₀ : ℕ) :
    ∃ B : ℕ, ∀ (N p : ℕ), 1 < N → p.Prime → 3 ≤ p → p ∣ N →
      (∀ q : ℕ, q.Prime → q ∣ N → q ≤ p) →
      N ≤ σ 1 (N / p) + C₀ →
      p ≤ B ∧ N ≤ B := by
  obtain ⟨B₃, hB₃⟩ := divisor_sum_ineq_three C₀
  obtain ⟨B₅, hB₅⟩ := divisor_sum_ineq_five C₀
  refine ⟨max (max B₃ B₅) 3, ?_⟩
  intro N p hN hp hp3 hpN h_supp h_ineq
  by_cases hp_eq_3 : p = 3
  · -- p = 3 case
    subst hp_eq_3
    have hN_bd : N ≤ B₃ := hB₃ N hN hpN h_supp h_ineq
    refine ⟨?_, ?_⟩
    · omega
    · omega
  · -- p ≥ 5 case (since p prime, p ≥ 3, p ≠ 3, p ≠ 4 (4 not prime))
    have hp4 : p ≠ 4 := fun h => absurd (h ▸ hp) (by decide)
    have hp5 : 5 ≤ p := by omega
    obtain ⟨hp_bd, hN_bd⟩ := hB₅ N p hN hp hp5 hpN h_supp h_ineq
    refine ⟨?_, ?_⟩
    · omega
    · omega

end DCS

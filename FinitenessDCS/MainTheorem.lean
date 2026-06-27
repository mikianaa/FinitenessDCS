import Mathlib
import FinitenessDCS.Defs
import FinitenessDCS.DivisorSum

/-!
# Main Theorem: Finiteness of Valid Systems

This file contains the proof of the main theorem (Theorem 3.7 / Corollary 3.8):
for each fixed `m ≥ 2`, the integer `n` in any valid coset partition system
is bounded by a constant depending only on `m`.

## Proof Structure

The proof proceeds by bounding `∑_{K ∈ 𝒜_P} |K|` for successively larger prime
sets P. The key lemmas are:

1. **Divisor-sum inequality** (Proposition 3.1): bounds N in terms of C₀ when
   N − σ(N/p) ≤ C₀.

2. **Valuation bounds** (Propositions 3.3/3.4, Lemma 3.5): the cell inequality
   reduces bounding a maximal valuation to the divisor-sum inequality.

3. **Main induction** (Theorem 3.7): strong induction on |P| to bound sums.
-/

namespace DCS

open Finset Nat
open scoped ArithmeticFunction.sigma

variable {m : ℕ}

/-! ### Structural lemmas for `ℒ_h(Q)`, `π_h` and `d_h` (any level `h`)

These are the level-`h` building blocks shared by both valuation propositions
(3.3, the `p₁ = 2` case, and 3.4, the `p_h ≥ 3` case).  They are phrased
directly in terms of the existing `def:symbols` notation from `Defs.lean`
(`largePart`, `LSet`, `dSet`, `pOrd`), so nothing here is special to `p₁ = 2`.

The single fact that genuinely *does not* generalize past `h = 1` is "equal
`p_h`-valuation ⟹ equal size": for `h > 1` the smaller primes `p₁,…,p_{h-1}`
break it (e.g. `h = 2`, `p₁ = 2, p₂ = 3, Q = 1`: the sizes `3` and `6` share
the same `ν₃` and `3 ∣ 6`, yet `3 ≠ 6`).  That step is therefore handled, in
both propositions, by the existing `DivisionMinimal` predicate rather than by a
same-valuation shortcut. -/

/-- Sum of a finite set of divisors of `M` is at most `σ(M)`. -/
lemma sum_le_sigma_of_dvd (S : Finset ℕ) (M : ℕ)
    (hM : 0 < M)
    (h_dvd : ∀ s ∈ S, s ∣ M) :
    S.sum id ≤ σ 1 M := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.sum_le_sum_of_subset
    (fun s hs => Nat.mem_divisors.mpr ⟨h_dvd s hs, hM.ne'⟩)

namespace ValidCosetPartition

variable (V : ValidCosetPartition m) {s Q : ℕ}

/-- Membership in `ℒ_h(Q)` unfolds to: a size in `S` whose large part `π_h` is `Q`. -/
lemma mem_LSet_iff (h : ℕ) :
    s ∈ V.LSet h Q ↔ s ∈ V.S ∧ V.largePart h s = Q := by
  simp [LSet]

/-- The large part `π_h(s)` always divides `s`: it is the sub-product of `s`'s
    prime factorization over the primes lying strictly above `p_h`. -/
lemma largePart_dvd (h : ℕ) (hs : s ≠ 0) : V.largePart h s ∣ s := by
  have hfull : ∏ q ∈ s.primeFactors, q ^ s.factorization q = s := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hs]
    rw [Nat.prod_factorization_eq_prod_primeFactors (fun p k => p ^ k)]
  calc V.largePart h s
      = ∏ q ∈ s.primeFactors \ V.smallPrimes h, q ^ s.factorization q := rfl
    _ ∣ ∏ q ∈ s.primeFactors, q ^ s.factorization q :=
        Finset.prod_dvd_prod_of_subset _ _ _ Finset.sdiff_subset
    _ = s := hfull

/-- For `s ∈ ℒ_h(Q)` the large part is pinned to `Q`, hence `Q ∣ s` and
    `s = (s / Q) · Q`.  This is the paper's `|K| = N_K · Q` with `N_K = s / Q`
    the "small part" supported on `{p₁,…,p_h}`. -/
lemma eq_div_mul_of_mem_LSet (h : ℕ) (hs : s ∈ V.LSet h Q) :
    s = (s / Q) * Q := by
  rw [V.mem_LSet_iff] at hs
  obtain ⟨hsS, hlarge⟩ := hs
  have hs0 : s ≠ 0 := (V.sizes_pos s hsS).ne'
  have hdvd : Q ∣ s := hlarge ▸ V.largePart_dvd h hs0
  exact (Nat.div_mul_cancel hdvd).symm

/-- On a nonempty `ℒ_h(Q)` the value `d_h(ℒ_h(Q))` is attained: some member `s₀`
    has `ν_{p_h}(s₀) = d_h(ℒ_h(Q))`, maximal among members of `ℒ_h(Q)`.  (For the
    `p₁ = 2` case take `h = 1`, where `p_h = 2`.) -/
lemma exists_mem_LSet_factorization_eq_dSet (h : ℕ) (hL : (V.LSet h Q).Nonempty) :
    ∃ s₀ ∈ V.LSet h Q,
      s₀.factorization (V.pOrd h) = V.dSet h (V.LSet h Q) ∧
      ∀ s ∈ V.LSet h Q, s.factorization (V.pOrd h) ≤ s₀.factorization (V.pOrd h) := by
  obtain ⟨s₀, hs₀, hsup⟩ :=
    Finset.exists_mem_eq_sup (V.LSet h Q) hL (fun s => s.factorization (V.pOrd h))
  refine ⟨s₀, hs₀, ?_, fun s hs => ?_⟩
  · simp only [dSet]; exact hsup.symm
  · rw [← hsup]; exact Finset.le_sup (f := fun s => s.factorization (V.pOrd h)) hs

/-! ### `p₁ = 2` specialization

The following three lemmas pin down the structure used in Proposition 3.3. Under
`p₁ = 2` the level-1 small primes are `{2}`, so every member of `ℒ₁(Q)` has the
form `2^{ν₂(s)} · Q`.  The large part is also monotone under divisibility, which
lets the divisors of the maximizer `s₀` be sorted into `ℒ₁(Q)` (same large part)
versus the `≤ C` tail (smaller large part). -/

/-- Under `p₁ = 2` the level-1 small-prime set is exactly `{2}`. -/
lemma smallPrimes_one (hp : V.pOrd 1 = 2) : V.smallPrimes 1 = {2} := by
  have hpd : V.primeList.getD 0 1 = 2 := hp
  cases hl : V.primeList with
  | nil => rw [hl] at hpd; simp at hpd
  | cons a l =>
    rw [hl] at hpd
    simp only [List.getD_cons_zero] at hpd
    subst hpd
    simp [smallPrimes, hl, List.take_succ_cons]

/-- Bridge (`p₁ = 2`): every member of `ℒ₁(Q)` is `2^{ν₂(s)} · Q`.  In particular
    `ν₂` is injective on `ℒ₁(Q)`, which replaces the same-valuation shortcut. -/
lemma eq_two_pow_mul_of_mem_LSet_one (hp : V.pOrd 1 = 2) (hs : s ∈ V.LSet 1 Q) :
    s = 2 ^ s.factorization 2 * Q := by
  rw [V.mem_LSet_iff] at hs
  obtain ⟨hsS, hlarge⟩ := hs
  have hs0 : s ≠ 0 := (V.sizes_pos s hsS).ne'
  have hfull : ∏ q ∈ s.primeFactors, q ^ s.factorization q = s := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hs0]
    rw [Nat.prod_factorization_eq_prod_primeFactors (fun p k => p ^ k)]
  have hsplit : 2 ^ s.factorization 2 * V.largePart 1 s = s := by
    rw [largePart, V.smallPrimes_one hp]
    by_cases h2 : 2 ∈ s.primeFactors
    · rw [← Finset.erase_eq, Finset.mul_prod_erase s.primeFactors
          (fun q => q ^ s.factorization q) h2]
      exact hfull
    · have hv2 : s.factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (fun hd => h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hs0⟩))
      rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem h2, hv2,
        pow_zero, one_mul]
      exact hfull
  rw [hlarge] at hsplit
  exact hsplit.symm

/-- The large part `π_h` is monotone under divisibility: `a ∣ b → π_h(a) ∣ π_h(b)`. -/
lemma largePart_dvd_of_dvd (h : ℕ) {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    V.largePart h a ∣ V.largePart h b := by
  have ha : a ≠ 0 := fun h0 => hb (by rwa [h0, Nat.zero_dvd] at hab)
  have hfle : a.factorization ≤ b.factorization :=
    (Nat.factorization_le_iff_dvd ha hb).mpr hab
  have hpf : a.primeFactors ⊆ b.primeFactors := Nat.primeFactors_mono hab hb
  unfold largePart
  calc ∏ q ∈ a.primeFactors \ V.smallPrimes h, q ^ a.factorization q
      ∣ ∏ q ∈ a.primeFactors \ V.smallPrimes h, q ^ b.factorization q :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun q _ => pow_dvd_pow q (hfle q))
    _ ∣ ∏ q ∈ b.primeFactors \ V.smallPrimes h, q ^ b.factorization q :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.sdiff_subset_sdiff hpf (Finset.Subset.refl _))

/-- The `p₁ = 2` factorization identity: `2^{ν₂(s)} · π₁(s) = s` (the small part
    is the `2`-power, the large part is the odd part).  This is the engine behind
    both the bridge and the multiply-invariance helper below. -/
lemma two_pow_mul_largePart_one (hp : V.pOrd 1 = 2) (hs : s ≠ 0) :
    2 ^ s.factorization 2 * V.largePart 1 s = s := by
  have hfull : ∏ q ∈ s.primeFactors, q ^ s.factorization q = s := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hs]
    rw [Nat.prod_factorization_eq_prod_primeFactors (fun p k => p ^ k)]
  rw [largePart, V.smallPrimes_one hp]
  by_cases h2 : 2 ∈ s.primeFactors
  · rw [← Finset.erase_eq, Finset.mul_prod_erase s.primeFactors
        (fun q => q ^ s.factorization q) h2]
    exact hfull
  · have hv2 : s.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hd => h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hs⟩))
    rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem h2, hv2,
      pow_zero, one_mul]
    exact hfull

/-- The large part `π₁` of `2^j · x` is `x` whenever `x` is odd: multiplying by a
    power of `2` does not change the odd part.  Used for the two-level case and
    Case 2 of Piece 5 (`n` and `s₀·2^{e₁}` both have odd part `Q`). -/
lemma largePart_two_pow_mul_odd (hp : V.pOrd 1 = 2) {x : ℕ} (j : ℕ)
    (hx0 : x ≠ 0) (hxodd : ¬ 2 ∣ x) :
    V.largePart 1 (2 ^ j * x) = x := by
  have hne : 2 ^ j * x ≠ 0 := by positivity
  have hval : (2 ^ j * x).factorization 2 = j := by
    rw [Nat.factorization_mul (pow_ne_zero j (by norm_num)) hx0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hxodd, add_zero]
  have hsplit := V.two_pow_mul_largePart_one hp hne
  rw [hval] at hsplit
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hsplit

/-! ### Piece 3 (global): the geometric sum bound over all of `ℒ₁(Q)`

Every member of `ℒ₁(Q)` is `2^e · Q` for distinct `e` (the bridge makes `ν₂`
injective), and every such `e` is at most `d₁ = dSet 1 (ℒ₁(Q))` by definition of
`dSet` as a `Finset.sup`.  Hence the whole of `ℒ₁(Q)` sums to at most
`Q · ∑_{e ≤ d₁} 2^e ≤ Q · 2^{d₁+1}`.  (Crucially this is over *all* of `ℒ₁(Q)`,
not just divisors of one element — the two-level case needs that.)  The
geometric sum is computed by a one-line induction rather than invoking `σ`. -/

/-- **Piece 3 (global).** All of `ℒ₁(Q)` sums to at most `Q·2^{d₁+1}`, where
    `d₁ = dSet 1 (ℒ₁(Q))` bounds every member's `ν₂`. -/
lemma sum_LSet_le (hp : V.pOrd 1 = 2) :
    ∑ t ∈ V.LSet 1 Q, t ≤ Q * 2 ^ (V.dSet 1 (V.LSet 1 Q) + 1) := by
  have geom : ∀ k, ∑ i ∈ Finset.range k, 2 ^ i = 2 ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; omega
  have hmem : ∀ t ∈ V.LSet 1 Q,
      t = 2 ^ t.factorization 2 * Q ∧ t.factorization 2 ≤ V.dSet 1 (V.LSet 1 Q) := by
    intro t ht
    refine ⟨V.eq_two_pow_mul_of_mem_LSet_one hp ht, ?_⟩
    have h := Finset.le_sup (f := fun s => s.factorization (V.pOrd 1)) ht
    rw [hp] at h
    simpa [dSet, hp] using h
  have hinj2 : ∀ x ∈ V.LSet 1 Q, ∀ y ∈ V.LSet 1 Q,
      x.factorization 2 = y.factorization 2 → x = y := by
    intro x hx y hy hxy; rw [(hmem x hx).1, (hmem y hy).1, hxy]
  calc ∑ t ∈ V.LSet 1 Q, t
      = ∑ t ∈ V.LSet 1 Q, 2 ^ t.factorization 2 * Q :=
        Finset.sum_congr rfl (fun t ht => (hmem t ht).1)
    _ = (∑ t ∈ V.LSet 1 Q, 2 ^ t.factorization 2) * Q := by rw [Finset.sum_mul]
    _ = (∑ e ∈ (V.LSet 1 Q).image (fun t => t.factorization 2), 2 ^ e) * Q := by
        rw [Finset.sum_image hinj2]
    _ ≤ (∑ e ∈ Finset.range (V.dSet 1 (V.LSet 1 Q) + 1), 2 ^ e) * Q := by
        apply Nat.mul_le_mul _ (le_refl Q)
        apply Finset.sum_le_sum_of_subset
        intro e he; rw [Finset.mem_image] at he; obtain ⟨t, ht, rfl⟩ := he
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hmem t ht).2)
    _ = (2 ^ (V.dSet 1 (V.LSet 1 Q) + 1) - 1) * Q := by rw [geom]
    _ ≤ 2 ^ (V.dSet 1 (V.LSet 1 Q) + 1) * Q := Nat.mul_le_mul (Nat.sub_le _ _) (le_refl Q)
    _ = Q * 2 ^ (V.dSet 1 (V.LSet 1 Q) + 1) := Nat.mul_comm _ _

/-! ### Piece 4 (global), level `h`: the tail accounting

A size `t` whose large part `π_h(t)` is a *proper* divisor of `Q` lies in
`ℒ_h(π_h t)` with `π_h t ∈ Q.properDivisors`, so all such sizes sit in the
*disjoint* union `⋃_{Q'∣Q, Q'≠Q} ℒ_h(Q')`, whose total mass is exactly the
hypothesis's `≤ C` sum.  Stated globally (no divisibility restriction), it needs
neither `p₁ = 2` nor monotonicity — the filter already pins `π_h t ∣ Q`.  This is
the form used by both Proposition 3.3 (`h = 1`) and Proposition 3.4. -/

/-- **Piece 4 (global), any level `h`.** Sizes whose large part is a proper
    divisor of `Q` sit in the disjoint union `⋃_{Q'∣Q, Q'≠Q} ℒ_h(Q')`; their mass
    is the tail sum. -/
lemma sum_properTail_le (h : ℕ) (hQ : 1 ≤ Q) :
    ∑ t ∈ V.S.filter (fun t => V.largePart h t ∣ Q ∧ V.largePart h t ≠ Q), t
      ≤ ∑ Q' ∈ Q.properDivisors, (V.LSet h Q').sum id := by
  have hdisj : (Q.properDivisors : Set ℕ).PairwiseDisjoint (fun Q' => V.LSet h Q') := by
    intro a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t hta htb
    rw [V.mem_LSet_iff] at hta htb
    exact hab (hta.2.symm.trans htb.2)
  rw [← Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum_of_subset
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨htS, htdvd, htne⟩ := ht
  have hpd : V.largePart h t ∈ Q.properDivisors := by
    rw [Nat.mem_properDivisors]
    exact ⟨htdvd, lt_of_le_of_ne (Nat.le_of_dvd (by omega) htdvd) htne⟩
  rw [Finset.mem_biUnion]
  exact ⟨V.largePart h t, hpd, (V.mem_LSet_iff h).mpr ⟨htS, rfl⟩⟩

/-- The combined upper bound on `W = {t ∈ S : π₁(t) ∣ Q}` used in every case of
    Piece 5: splitting `W` by `π₁(t) = Q` gives `ℒ₁(Q)` (Piece 3) plus the proper
    tail (Piece 4). -/
lemma sum_filterLargePartDvd_le (hp : V.pOrd 1 = 2) (hQ : 1 ≤ Q) :
    ∑ t ∈ V.S.filter (fun t => V.largePart 1 t ∣ Q), t
      ≤ Q * 2 ^ (V.dSet 1 (V.LSet 1 Q) + 1)
        + ∑ Q' ∈ Q.properDivisors, (V.LSet 1 Q').sum id := by
  rw [← Finset.sum_filter_add_sum_filter_not (V.S.filter (fun t => V.largePart 1 t ∣ Q))
        (fun t => V.largePart 1 t = Q)]
  have heq1 : (V.S.filter (fun t => V.largePart 1 t ∣ Q)).filter (fun t => V.largePart 1 t = Q)
      = V.LSet 1 Q := by
    ext t
    simp only [Finset.mem_filter, LSet]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, dvd_of_eq h.2⟩, h.2⟩⟩
  have heq2 : (V.S.filter (fun t => V.largePart 1 t ∣ Q)).filter (fun t => ¬ V.largePart 1 t = Q)
      = V.S.filter (fun t => V.largePart 1 t ∣ Q ∧ V.largePart 1 t ≠ Q) := by
    ext t; simp only [Finset.mem_filter]; tauto
  rw [heq1, heq2]
  exact Nat.add_le_add (V.sum_LSet_le hp) (V.sum_properTail_le 1 hQ)

/-! ### Piece 5: the case analysis (the lower bound)

For any `s₀ ∈ ℒ₁(Q)` we show `3·s₀ ≤ (∑_{t∈W} t) + m`, where `W = {t∈S : π₁(t)∣Q}`.
The factor `3` is produced one of three ways, by case-splitting on `q = n/s₀`:
* `q` odd → `cell_ineq` with `minFac(q) ≥ 3` (its divisors lie in `W`);
* `q` even, not a power of `2` → `cell_ineq_two` with second prime `≥ 3` (the
  target `s₀·2^{e₁}` still has odd part `Q`, so its divisors lie in `W`);
* `q` a power of `2` → here every size's odd part divides `Q` (so `S = W`), and
  the size bound `3·s₀ ≤ n = (∑_S) + m` finishes directly. -/

/-- **Piece 5.** In every case, `3·s₀ ≤ (∑_{t∈W} t) + m` where `W = {t∈S : π₁(t)∣Q}`. -/
lemma three_mul_s₀_le (hp : V.pOrd 1 = 2) (hQ : 1 ≤ Q) (hQodd : ¬ 2 ∣ Q)
    (hs₀ : s₀ ∈ V.LSet 1 Q) :
    3 * s₀ ≤ (∑ t ∈ V.S.filter (fun t => V.largePart 1 t ∣ Q), t) + m := by
  have hs₀S : s₀ ∈ V.S := ((V.mem_LSet_iff 1).mp hs₀).1
  have hπ : V.largePart 1 s₀ = Q := ((V.mem_LSet_iff 1).mp hs₀).2
  have hs₀0 : s₀ ≠ 0 := (V.sizes_pos s₀ hs₀S).ne'
  have hbridge : s₀ = 2 ^ s₀.factorization 2 * Q := V.eq_two_pow_mul_of_mem_LSet_one hp hs₀
  -- Any divisor set whose target has large part dividing `Q` sits inside `W`.
  have hsub : ∀ M, M ≠ 0 → V.largePart 1 M ∣ Q →
      (∑ t ∈ V.S.filter (· ∣ M), t)
        ≤ ∑ t ∈ V.S.filter (fun t => V.largePart 1 t ∣ Q), t := by
    intro M hM hMQ
    apply Finset.sum_le_sum_of_subset
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, (V.largePart_dvd_of_dvd 1 hM ht.2).trans hMQ⟩
  set q := V.n / s₀ with hqdef
  have hq3 : 3 ≤ q := V.ndivs_ge_three s₀ hs₀S
  by_cases hodd : 2 ∣ q
  · -- q even
    by_cases h2pow : q / 2 ^ (q.factorization 2) = 1
    · -- Case 2: q is a power of 2; every size's odd part divides Q, so S = W
      have hQ0 : Q ≠ 0 := by omega
      have hn0 : V.n ≠ 0 := V.n_pos.ne'
      have hs₀dvd : s₀ ∣ V.n := V.sizes_dvd s₀ hs₀S
      have hnq : V.n = q * s₀ := by rw [hqdef]; exact (Nat.div_mul_cancel hs₀dvd).symm
      have hqpow : q = 2 ^ q.factorization 2 := by
        have h := Nat.mul_div_cancel' (Nat.ordProj_dvd q 2)
        rw [h2pow, mul_one] at h
        exact h.symm
      have hlpn : V.largePart 1 V.n = Q := by
        have hform : V.n = 2 ^ (q.factorization 2 + s₀.factorization 2) * Q := by
          rw [pow_add, mul_assoc, ← hbridge, ← hqpow, hnq]
        rw [hform]
        exact V.largePart_two_pow_mul_odd hp _ hQ0 hQodd
      have hWeqS : V.S.filter (fun t => V.largePart 1 t ∣ Q) = V.S := by
        apply Finset.filter_true_of_mem
        intro t ht
        have hd := V.largePart_dvd_of_dvd 1 hn0 (V.sizes_dvd t ht)
        rwa [hlpn] at hd
      rw [hWeqS]
      calc 3 * s₀ ≤ V.n := V.sizes_le s₀ hs₀S
        _ = (∑ t ∈ V.S, t) + m := V.sum_eq.symm
    · -- Case 1b: q even but not a power of 2; apply the two-level inequality
      have hQ0 : Q ≠ 0 := by omega
      have hq0 : q ≠ 0 := by omega
      have hminFac2 : q.minFac = 2 :=
        le_antisymm (Nat.minFac_le_of_dvd (le_refl 2) hodd) (Nat.minFac_prime (by omega)).two_le
      have hoc_pos : 0 < q / 2 ^ q.factorization 2 := Nat.ordCompl_pos 2 hq0
      have hoc_gt : 1 < q / 2 ^ q.factorization 2 := by omega
      have hocodd : ¬ 2 ∣ (q / 2 ^ q.factorization 2) := Nat.not_dvd_ordCompl Nat.prime_two hq0
      have hfactor3 : 3 ≤ (q / 2 ^ q.factorization 2).minFac := by
        have hprime := Nat.minFac_prime (by omega : q / 2 ^ q.factorization 2 ≠ 1)
        have hne2 : (q / 2 ^ q.factorization 2).minFac ≠ 2 := by
          intro h
          have hd : (q / 2 ^ q.factorization 2).minFac ∣ q / 2 ^ q.factorization 2 :=
            Nat.minFac_dvd _
          rw [h] at hd; exact hocodd hd
        have := hprime.two_le; omega
      have hcond : 1 < (V.n / s₀) /
          (V.n / s₀).minFac ^ (V.n / s₀).factorization (V.n / s₀).minFac := by
        rw [← hqdef, hminFac2]; exact hoc_gt
      have hres := V.cell_ineq_two s₀ hs₀S hcond
      rw [← hqdef, hminFac2] at hres
      have hlpM : V.largePart 1 (s₀ * 2 ^ q.factorization 2) = Q := by
        have hform : s₀ * 2 ^ q.factorization 2
            = 2 ^ (q.factorization 2 + s₀.factorization 2) * Q := by
          rw [pow_add, mul_assoc, ← hbridge]; ring
        rw [hform]; exact V.largePart_two_pow_mul_odd hp _ hQ0 hQodd
      have hMne : s₀ * 2 ^ q.factorization 2 ≠ 0 :=
        mul_ne_zero hs₀0 (pow_ne_zero _ (by norm_num))
      calc 3 * s₀ ≤ (q / 2 ^ q.factorization 2).minFac * s₀ :=
            Nat.mul_le_mul hfactor3 (le_refl s₀)
        _ ≤ (V.S.filter (· ∣ s₀ * 2 ^ q.factorization 2)).sum id + m := hres
        _ ≤ (∑ t ∈ V.S.filter (fun t => V.largePart 1 t ∣ Q), t) + m :=
            Nat.add_le_add_right (hsub _ hMne (dvd_of_eq hlpM)) m
  · -- Case 1a: q odd, one-level cell inequality
    have hqminFac : 3 ≤ q.minFac := by
      have hqprime : q.minFac.Prime := Nat.minFac_prime (by omega)
      have hne2 : q.minFac ≠ 2 := fun h => hodd (h ▸ Nat.minFac_dvd q)
      have := hqprime.two_le
      omega
    have hci := V.cell_ineq s₀ hs₀S
    rw [← hqdef] at hci
    calc 3 * s₀ ≤ q.minFac * s₀ := Nat.mul_le_mul hqminFac (le_refl s₀)
      _ ≤ (V.S.filter (· ∣ s₀)).sum id + m := hci
      _ ≤ (∑ t ∈ V.S.filter (fun t => V.largePart 1 t ∣ Q), t) + m :=
          Nat.add_le_add_right (hsub s₀ hs₀0 (dvd_of_eq hπ)) m

/-! ### Proposition 3.4 infrastructure

#### Piece 0: ordering API for `primeList`/`smallPrimes`/`pOrd`

`primeList = n.primeFactors.sort (·≤·)` is the increasing list of prime divisors.
The hypothesis `2 ≤ p_h` (in fact `3 ≤ p_h` in Proposition 3.4) forces `h` to be a
valid index (`p_h = 1` would mean `h` is out of range), so `p_h` is a genuine
prime divisor of `n`; with `1 ≤ h` it lies in `{p₁,…,p_h}` and dominates it. -/

variable {h : ℕ}

/-- `x` is in `primeList` iff it is a prime factor of `n`. -/
lemma mem_primeList {x : ℕ} : x ∈ V.primeList ↔ x ∈ V.n.primeFactors := by
  rw [show V.primeList = V.n.primeFactors.sort (· ≤ ·) from rfl, Finset.mem_sort]

/-- `primeList` is strictly increasing (sort of a nodup finset). -/
lemma primeList_sortedLT : V.primeList.SortedLT := by
  rw [show V.primeList = V.n.primeFactors.sort (· ≤ ·) from rfl]
  exact Finset.sortedLT_sort _

/-- If `p_h ≥ 2` then `h` is a valid index into `primeList`. -/
lemma pOrd_range (hh : 2 ≤ V.pOrd h) : h - 1 < V.primeList.length := by
  rw [show V.pOrd h = V.primeList.getD (h - 1) 1 from rfl] at hh
  by_contra hc
  rw [List.getD_eq_default _ _ (not_lt.mp hc)] at hh
  omega

/-- For an in-range `h`, `p_h` is the `(h-1)`-th list element. -/
lemma pOrd_eq_getElem (hh : 2 ≤ V.pOrd h) :
    V.pOrd h = V.primeList[h - 1]'(V.pOrd_range hh) := by
  rw [show V.pOrd h = V.primeList.getD (h - 1) 1 from rfl, List.getD_eq_getElem]

/-- `p_h` is a prime factor of `n` (when `p_h ≥ 2`). -/
lemma pOrd_mem_primeFactors (hh : 2 ≤ V.pOrd h) : V.pOrd h ∈ V.n.primeFactors := by
  rw [← V.mem_primeList, V.pOrd_eq_getElem hh]
  exact List.getElem_mem _

/-- `p_h` is prime (when `p_h ≥ 2`). -/
lemma pOrd_prime (hh : 2 ≤ V.pOrd h) : (V.pOrd h).Prime :=
  Nat.prime_of_mem_primeFactors (V.pOrd_mem_primeFactors hh)

/-- `p_h` divides `n` (when `p_h ≥ 2`). -/
lemma pOrd_dvd (hh : 2 ≤ V.pOrd h) : V.pOrd h ∣ V.n :=
  Nat.dvd_of_mem_primeFactors (V.pOrd_mem_primeFactors hh)

/-- `p_h ∈ {p₁,…,p_h}` (for `1 ≤ h`, `p_h ≥ 2`). -/
lemma pOrd_mem_smallPrimes (hh1 : 1 ≤ h) (hh : 2 ≤ V.pOrd h) :
    V.pOrd h ∈ V.smallPrimes h := by
  rw [show V.smallPrimes h = (V.primeList.take h).toFinset from rfl, List.mem_toFinset,
    V.pOrd_eq_getElem hh]
  have hr := V.pOrd_range hh
  have hlt : h - 1 < (V.primeList.take h).length := by rw [List.length_take]; omega
  have heq : V.primeList[h - 1] = (V.primeList.take h)[h - 1]'hlt := (List.getElem_take ..).symm
  rw [heq]
  exact List.getElem_mem _

/-- Every prime in `{p₁,…,p_h}` is `≤ p_h` (for `1 ≤ h`, `p_h ≥ 2`). -/
lemma smallPrimes_le_pOrd (hh1 : 1 ≤ h) (hh : 2 ≤ V.pOrd h) :
    ∀ q ∈ V.smallPrimes h, q ≤ V.pOrd h := by
  intro q hq
  rw [show V.smallPrimes h = (V.primeList.take h).toFinset from rfl, List.mem_toFinset] at hq
  rw [V.pOrd_eq_getElem hh]
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  rw [List.getElem_take]
  have hr := V.pOrd_range hh
  rw [List.length_take] at hj
  exact (V.primeList_sortedLT.getElem_le_getElem_iff).mpr (by omega)

/-- `{p₁,…,p_h} ⊆` prime factors of `n`. -/
lemma smallPrimes_subset_primeFactors : V.smallPrimes h ⊆ V.n.primeFactors := by
  intro q hq
  rw [show V.smallPrimes h = (V.primeList.take h).toFinset from rfl, List.mem_toFinset] at hq
  rw [← V.mem_primeList]
  exact List.mem_of_mem_take hq

/-- `p_h = 2` forces `h = 1` (2 is the smallest prime, so it sits at index 0). -/
lemma eq_one_of_pOrd_eq_two (hh1 : 1 ≤ h) (hph : V.pOrd h = 2) : h = 1 := by
  by_contra hne
  have h2 : 2 ≤ V.pOrd h := by omega
  have hr : h - 1 < V.primeList.length := V.pOrd_range h2
  have hr0 : 0 < V.primeList.length := by omega
  have hp0_prime : V.primeList[0].Prime :=
    Nat.prime_of_mem_primeFactors (V.mem_primeList.mp (List.getElem_mem hr0))
  have hlt : V.primeList[0] < V.primeList[h - 1] :=
    (V.primeList_sortedLT.getElem_lt_getElem_iff).mpr (by omega)
  rw [← V.pOrd_eq_getElem h2, hph] at hlt
  have := hp0_prime.two_le
  omega

/-! #### Piece 2: the division-minimal maximizer

The `p_h ≥ 3` case has no same-valuation shortcut, so we instead pick `K` as in the
paper: a member of `ℒ_h(Q)` with maximal `ν_{p_h}` that is *division-minimal* among
the maximal-valuation members.  Such a `K` exists because the numerically smallest
maximal-valuation size is automatically division-minimal (a proper divisor of it in
the same set would be both `≤` and `≥` it). -/

/-- **Piece 2.** Among the `ν_{p_h}`-maximal members of `ℒ_h(Q)` there is a
    division-minimal one. -/
lemma exists_divisionMinimal_maximal (h : ℕ) (hNE : (V.LSet h Q).Nonempty) :
    ∃ s₀ ∈ V.LSet h Q,
      s₀.factorization (V.pOrd h) = V.dSet h (V.LSet h Q) ∧
      ∀ s' ∈ V.LSet h Q, s'.factorization (V.pOrd h) = V.dSet h (V.LSet h Q) →
        s' ∣ s₀ → s' = s₀ := by
  set d := V.dSet h (V.LSet h Q) with hd
  obtain ⟨s₁, hs₁L, hs₁d, _⟩ := V.exists_mem_LSet_factorization_eq_dSet h hNE
  have hTne : ((V.LSet h Q).filter (fun s => s.factorization (V.pOrd h) = d)).Nonempty :=
    ⟨s₁, Finset.mem_filter.mpr ⟨hs₁L, hs₁d⟩⟩
  set s₀ := ((V.LSet h Q).filter (fun s => s.factorization (V.pOrd h) = d)).min' hTne with hs₀def
  have hmin : s₀ ∈ (V.LSet h Q).filter (fun s => s.factorization (V.pOrd h) = d) :=
    Finset.min'_mem _ hTne
  rw [Finset.mem_filter] at hmin
  refine ⟨s₀, hmin.1, hmin.2, ?_⟩
  intro s' hs'L hs'd hdvd
  have hs'T : s' ∈ (V.LSet h Q).filter (fun s => s.factorization (V.pOrd h) = d) :=
    Finset.mem_filter.mpr ⟨hs'L, hs'd⟩
  have h1 : s₀ ≤ s' := Finset.min'_le _ s' hs'T
  have hs₀pos : 0 < s₀ := V.sizes_pos _ ((V.mem_LSet_iff h).mp hmin.1).1
  have h2 : s' ≤ s₀ := Nat.le_of_dvd hs₀pos hdvd
  omega

/-! #### Piece 3: structure of the small part `N_K = s₀/Q`

Writing `N_K := s₀/Q`, we have `s₀ = N_K·Q`.  Since `Q` is supported on the
primes *above* `p_h`, `p_h ∤ Q`, so `ν_{p_h}(N_K) = ν_{p_h}(s₀)`.  And `N_K` is
the "small part", supported on `{p₁,…,p_h}`: if a prime `q ∉ {p₁,…,p_h}` divided
`N_K`, then `q^{ν_q(s₀)} ∣ π_h(s₀) = Q`, forcing `ν_q(N_K) = 0`, a contradiction.
Hence every prime of `N_K` is `≤ p_h`. -/

/-- **Piece 3.** Structure of `N_K = s₀/Q` for `s₀ ∈ ℒ_h(Q)`: `s₀ = N_K·Q`,
    `ν_{p_h}(N_K) = ν_{p_h}(s₀)`, and every prime of `N_K` is `≤ p_h`. -/
lemma NK_structure (h : ℕ) (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h)
    (hs₀ : s₀ ∈ V.LSet h Q) (hQ : 1 ≤ Q)
    (hsupp : IsSupportedOn Q (V.n.primeFactors \ V.smallPrimes h)) :
    s₀ = (s₀ / Q) * Q ∧
    (s₀ / Q).factorization (V.pOrd h) = s₀.factorization (V.pOrd h) ∧
    (∀ q : ℕ, q.Prime → q ∣ (s₀ / Q) → q ≤ V.pOrd h) := by
  have hmem := (V.mem_LSet_iff h).mp hs₀
  have hs₀S : s₀ ∈ V.S := hmem.1
  have hπ : V.largePart h s₀ = Q := hmem.2
  have hs₀0 : s₀ ≠ 0 := (V.sizes_pos s₀ hs₀S).ne'
  have hQ0 : Q ≠ 0 := by omega
  have hQdvd : Q ∣ s₀ := by rw [← hπ]; exact V.largePart_dvd h hs₀0
  have hNK : s₀ = (s₀ / Q) * Q := V.eq_div_mul_of_mem_LSet h hs₀
  have hNpos : 0 < s₀ / Q := Nat.div_pos (Nat.le_of_dvd (by omega) hQdvd) (by omega)
  set N := s₀ / Q with hNdef
  have hN0 : N ≠ 0 := hNpos.ne'
  have hfact : s₀.factorization = N.factorization + Q.factorization := by
    conv_lhs => rw [hNK]
    rw [Nat.factorization_mul hN0 hQ0]
  -- p_h ∤ Q (from Q's support and p_h ∈ smallPrimes h).
  have hpQ : ¬ V.pOrd h ∣ Q := by
    intro hd
    have hph_pf : V.pOrd h ∈ Q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨V.pOrd_prime hph, hd, hQ0⟩
    have hin := hsupp _ hph_pf
    rw [Finset.mem_sdiff] at hin
    exact hin.2 (V.pOrd_mem_smallPrimes hh1 hph)
  refine ⟨hNK, ?_, ?_⟩
  · -- ν_{p_h}(N) = ν_{p_h}(s₀)
    have hpQ0 : Q.factorization (V.pOrd h) = 0 := Nat.factorization_eq_zero_of_not_dvd hpQ
    have hadd := congrArg (fun f => f (V.pOrd h)) hfact
    simp only [Finsupp.add_apply] at hadd
    omega
  · -- primes of N ≤ p_h
    intro q hq hqN
    by_contra hgt
    have hnsp : q ∉ V.smallPrimes h := fun hsp => hgt (V.smallPrimes_le_pOrd hh1 hph q hsp)
    have hq_s₀ : q ∣ s₀ := by rw [hNK]; exact hqN.mul_right Q
    have hq_pf : q ∈ s₀.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hq_s₀, hs₀0⟩
    have hmsd : q ∈ s₀.primeFactors \ V.smallPrimes h := Finset.mem_sdiff.mpr ⟨hq_pf, hnsp⟩
    have hpow_dvd : q ^ s₀.factorization q ∣ Q := by
      rw [← hπ, largePart]; exact Finset.dvd_prod_of_mem _ hmsd
    have hνle : s₀.factorization q ≤ Q.factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hq hQ0).mp hpow_dvd
    have hνN : 1 ≤ N.factorization q := hq.factorization_pos_of_dvd hN0 hqN
    have hadd := congrArg (fun f => f q) hfact
    simp only [Finsupp.add_apply] at hadd
    omega

/-! #### Piece 4: the `σ` divisor-sum bound

The members `t` of `𝒟(s₀) ∩ ℒ_h(Q)` (divisors of `s₀`, `≠ s₀`, with `π_h(t)=Q`)
all have `ν_{p_h}(t) < d_h`: equal valuation would put `t` in the maximal set and,
since `t ∣ s₀`, division-minimality (Piece 2) would force `t = s₀`.  Hence `t ∣
s₀/p_h`, so `N_t := t/Q` divides `N_K/p_h`.  Mapping `t ↦ N_t` injectively into the
divisors of `N_K/p_h` and applying `sum_le_sigma_of_dvd` gives `∑ t ≤ Q·σ(N_K/p_h)`. -/

/-- If `a ∣ b`, `p ∣ b` is prime, and `ν_p(a) < ν_p(b)`, then `a ∣ b/p`. -/
lemma dvd_div_prime_of_factorization_lt {a b p : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpb : p ∣ b) (hab : a ∣ b) (hlt : a.factorization p < b.factorization p) :
    a ∣ b / p := by
  have hapb : a * p ∣ b := by
    rw [← Nat.factorization_le_iff_dvd (mul_ne_zero ha hp.ne_zero) hb, Finsupp.le_def]
    intro q
    rw [Nat.factorization_mul ha hp.ne_zero, Finsupp.add_apply, hp.factorization,
      Finsupp.single_apply]
    rcases eq_or_ne p q with hqp | hqp
    · rw [if_pos hqp, ← hqp]; omega
    · rw [if_neg hqp, add_zero]
      exact ((Nat.factorization_le_iff_dvd ha hb).mpr hab) q
  exact (Nat.dvd_div_iff_mul_dvd hpb).mpr (mul_comm a p ▸ hapb)

/-- **Piece 4.** The members of `𝒟(s₀) ∩ ℒ_h(Q)` sum to at most `Q·σ(N_K/p_h)`. -/
lemma sum_DS_LSet_le (h : ℕ) (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h)
    (hs₀ : s₀ ∈ V.LSet h Q) (hQ : 1 ≤ Q)
    (hsupp : IsSupportedOn Q (V.n.primeFactors \ V.smallPrimes h))
    (hd : s₀.factorization (V.pOrd h) = V.dSet h (V.LSet h Q))
    (hmin : ∀ s' ∈ V.LSet h Q, s'.factorization (V.pOrd h) = V.dSet h (V.LSet h Q) →
        s' ∣ s₀ → s' = s₀)
    (hd1 : 1 ≤ s₀.factorization (V.pOrd h)) :
    ∑ t ∈ (V.LSet h Q).filter (fun t => t ∣ s₀ ∧ t ≠ s₀), t
      ≤ Q * σ 1 ((s₀ / Q) / V.pOrd h) := by
  obtain ⟨hNK, hνNK, _⟩ := V.NK_structure h hh1 hph hs₀ hQ hsupp
  have hQ0 : Q ≠ 0 := by omega
  have hmem := (V.mem_LSet_iff h).mp hs₀
  have hs₀0 : s₀ ≠ 0 := (V.sizes_pos s₀ hmem.1).ne'
  have hQdvd : Q ∣ s₀ := by rw [← hmem.2]; exact V.largePart_dvd h hs₀0
  have hpQ : ¬ V.pOrd h ∣ Q := by
    intro hd'
    have := hsupp _ (Nat.mem_primeFactors.mpr ⟨V.pOrd_prime hph, hd', hQ0⟩)
    rw [Finset.mem_sdiff] at this
    exact this.2 (V.pOrd_mem_smallPrimes hh1 hph)
  have hpQ0 : Q.factorization (V.pOrd h) = 0 := Nat.factorization_eq_zero_of_not_dvd hpQ
  set p := V.pOrd h with hpdef
  set N := s₀ / Q with hNdef
  have hNpos : 0 < N := Nat.div_pos (Nat.le_of_dvd (by omega) hQdvd) (by omega)
  have hN0 : N ≠ 0 := hNpos.ne'
  have hpprime : p.Prime := V.pOrd_prime hph
  have hpN : p ∣ N := Nat.dvd_of_factorization_pos (by rw [hνNK]; omega)
  have hNp_pos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hNpos hpN) hpprime.pos
  set D := (V.LSet h Q).filter (fun t => t ∣ s₀ ∧ t ≠ s₀) with hDdef
  have hkey : ∀ t ∈ D, t = (t / Q) * Q ∧ (t / Q) ∣ N / p := by
    intro t ht
    rw [hDdef, Finset.mem_filter] at ht
    obtain ⟨htL, htdvd, htne⟩ := ht
    have htmem := (V.mem_LSet_iff h).mp htL
    have ht0 : t ≠ 0 := (V.sizes_pos t htmem.1).ne'
    have hQt : Q ∣ t := by rw [← htmem.2]; exact V.largePart_dvd h ht0
    have hteq : t = (t / Q) * Q := V.eq_div_mul_of_mem_LSet h htL
    refine ⟨hteq, ?_⟩
    have hle : t.factorization p ≤ s₀.factorization p := by
      rw [hd]; exact Finset.le_sup (f := fun s => s.factorization (V.pOrd h)) htL
    have hne : t.factorization p ≠ s₀.factorization p := by
      intro heq
      apply htne
      apply hmin t htL _ htdvd
      rw [← hd]; exact heq
    have hlt : t.factorization p < s₀.factorization p := lt_of_le_of_ne hle hne
    set Nt := t / Q with hNtdef
    have hNt0 : Nt ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (by omega) hQt) (by omega)).ne'
    have hNtN : Nt ∣ N := by
      have hmul : Nt * Q ∣ N * Q := by rw [← hteq, ← hNK]; exact htdvd
      exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < Q)).mp hmul
    have hνNt : Nt.factorization p = t.factorization p := by
      have hadd : t.factorization = Nt.factorization + Q.factorization := by
        conv_lhs => rw [hteq]
        rw [Nat.factorization_mul hNt0 hQ0]
      have heq := congrArg (fun f => f p) hadd
      simp only [Finsupp.add_apply] at heq
      omega
    have hltN : Nt.factorization p < N.factorization p := by rw [hνNt, hνNK]; exact hlt
    exact dvd_div_prime_of_factorization_lt hpprime hNt0 hN0 hpN hNtN hltN
  have hinj : ∀ x ∈ D, ∀ y ∈ D, x / Q = y / Q → x = y := by
    intro x hx y hy hxy
    rw [(hkey x hx).1, (hkey y hy).1, hxy]
  calc ∑ t ∈ D, t
      = ∑ t ∈ D, (t / Q) * Q := Finset.sum_congr rfl (fun t ht => (hkey t ht).1)
    _ = (∑ t ∈ D, t / Q) * Q := by rw [Finset.sum_mul]
    _ = (∑ x ∈ D.image (fun t => t / Q), x) * Q := by rw [Finset.sum_image hinj]
    _ ≤ σ 1 (N / p) * Q := by
        apply Nat.mul_le_mul _ (le_refl Q)
        refine sum_le_sigma_of_dvd _ _ hNp_pos (fun s hs => ?_)
        rw [Finset.mem_image] at hs
        obtain ⟨t, ht, rfl⟩ := hs
        exact (hkey t ht).2
    _ = Q * σ 1 (N / p) := Nat.mul_comm _ _

/-! #### Piece 5: the core inequality

The cell inequality (`sumDS_ge`: `s₀ ≤ ∑_{𝒟(s₀)} + m`) bounds `s₀` by the mass of
its proper divisors.  Splitting that mass by `π_h(t) = Q`, the `π_h = Q` part is
bounded by Piece 4 (`Q·σ(N_K/p_h)`) and the `π_h ≠ Q` part by the tail (Piece 1,
`≤ C`).  Thus `s₀ ≤ Q·σ(N_K/p_h) + C + m`; dividing by `Q` gives the form fed to
the divisor-sum inequality: `N_K ≤ σ(N_K/p_h) + (C + m)`. -/

/-- **Piece 5.** The core inequality `N_K ≤ σ(N_K/p_h) + (C+m)`. -/
lemma core_inequality (h : ℕ) (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h)
    (hs₀ : s₀ ∈ V.LSet h Q) (hQ : 1 ≤ Q)
    (hsupp : IsSupportedOn Q (V.n.primeFactors \ V.smallPrimes h))
    (hd : s₀.factorization (V.pOrd h) = V.dSet h (V.LSet h Q))
    (hmin : ∀ s' ∈ V.LSet h Q, s'.factorization (V.pOrd h) = V.dSet h (V.LSet h Q) →
        s' ∣ s₀ → s' = s₀)
    (hd1 : 1 ≤ s₀.factorization (V.pOrd h)) (C : ℕ)
    (htail : (∑ Q' ∈ Q.properDivisors, (V.LSet h Q').sum id) ≤ C) :
    s₀ / Q ≤ σ 1 ((s₀ / Q) / V.pOrd h) + (C + m) := by
  have hmem := (V.mem_LSet_iff h).mp hs₀
  have hs₀S : s₀ ∈ V.S := hmem.1
  have hπ : V.largePart h s₀ = Q := hmem.2
  have hs₀0 : s₀ ≠ 0 := (V.sizes_pos s₀ hs₀S).ne'
  obtain ⟨hNK, _, _⟩ := V.NK_structure h hh1 hph hs₀ hQ hsupp
  -- Split (DS s₀).sum by π_h = Q.
  have hsplit : (V.DS s₀).sum id =
      ((V.DS s₀).filter (fun t => V.largePart h t = Q)).sum id
      + ((V.DS s₀).filter (fun t => ¬ V.largePart h t = Q)).sum id :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have heq1 : (V.DS s₀).filter (fun t => V.largePart h t = Q)
      = (V.LSet h Q).filter (fun t => t ∣ s₀ ∧ t ≠ s₀) := by
    ext t; simp only [Finset.mem_filter, DS, LSet]; tauto
  have hbound1 : ((V.DS s₀).filter (fun t => V.largePart h t = Q)).sum id
      ≤ Q * σ 1 ((s₀ / Q) / V.pOrd h) := by
    rw [heq1]; exact V.sum_DS_LSet_le h hh1 hph hs₀ hQ hsupp hd hmin hd1
  have hbound2 : ((V.DS s₀).filter (fun t => ¬ V.largePart h t = Q)).sum id ≤ C := by
    refine le_trans (Finset.sum_le_sum_of_subset ?_) (le_trans (V.sum_properTail_le h hQ) htail)
    intro t ht
    simp only [Finset.mem_filter, DS] at ht
    obtain ⟨⟨htS, htdvd, _⟩, htπ⟩ := ht
    refine Finset.mem_filter.mpr ⟨htS, ?_, htπ⟩
    rw [← hπ]; exact V.largePart_dvd_of_dvd h hs₀0 htdvd
  have hDS_le : (V.DS s₀).sum id ≤ Q * σ 1 ((s₀ / Q) / V.pOrd h) + C := by
    rw [hsplit]; exact Nat.add_le_add hbound1 hbound2
  have hs₀le : s₀ ≤ Q * σ 1 ((s₀ / Q) / V.pOrd h) + C + m := by
    calc s₀ ≤ V.sumDS s₀ := V.sumDS_ge s₀ hs₀S
      _ = (V.DS s₀).sum id + m := rfl
      _ ≤ (Q * σ 1 ((s₀ / Q) / V.pOrd h) + C) + m := Nat.add_le_add_right hDS_le m
  -- Divide by Q.
  have hQpos : 0 < Q := by omega
  refine Nat.le_of_mul_le_mul_left ?_ hQpos
  rw [Nat.mul_comm Q (s₀ / Q)]
  calc (s₀ / Q) * Q
      = s₀ := hNK.symm
    _ ≤ Q * σ 1 ((s₀ / Q) / V.pOrd h) + C + m := hs₀le
    _ ≤ Q * σ 1 ((s₀ / Q) / V.pOrd h) + Q * C + Q * m := by
        gcongr <;> exact Nat.le_mul_of_pos_left _ hQpos
    _ = Q * (σ 1 ((s₀ / Q) / V.pOrd h) + (C + m)) := by ring

/-! ### Lemma 3.6 infrastructure

#### Piece A: the consecutive-level `largePart` relation

Stepping down one level peels off the `p_h`-power.  The structural core is that
`{p₁,…,p_h} = insert p_h {p₁,…,p_{h-1}}` (the prime list grows by one element),
which gives `π_{h-1}(s) = p_h^{ν_{p_h}(s)} · π_h(s)`.  All three lemmas are phrased
with `k`/`k+1` (so `k = h-1`) to avoid `ℕ`-subtraction. -/

/-- `{p₁,…,p_{k+1}} = insert p_{k+1} {p₁,…,p_k}`. -/
lemma smallPrimes_succ (k : ℕ) (hph : 2 ≤ V.pOrd (k + 1)) :
    V.smallPrimes (k + 1) = insert (V.pOrd (k + 1)) (V.smallPrimes k) := by
  have hr : k < V.primeList.length := by have := V.pOrd_range hph; omega
  rw [show V.smallPrimes (k + 1) = (V.primeList.take (k + 1)).toFinset from rfl,
      show V.smallPrimes k = (V.primeList.take k).toFinset from rfl,
      List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
      List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      show V.primeList[k] = V.pOrd (k + 1) from (V.pOrd_eq_getElem hph).symm]
  ext x
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- `p_{k+1} ∉ {p₁,…,p_k}` (the prime list is strictly increasing). -/
lemma pOrd_succ_not_mem_smallPrimes (k : ℕ) (hph : 2 ≤ V.pOrd (k + 1)) :
    V.pOrd (k + 1) ∉ V.smallPrimes k := by
  rw [show V.smallPrimes k = (V.primeList.take k).toFinset from rfl, List.mem_toFinset]
  intro hc
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hc
  rw [List.getElem_take] at hjeq
  rw [List.length_take] at hj
  have hr : k < V.primeList.length := by have := V.pOrd_range hph; omega
  rw [V.pOrd_eq_getElem hph] at hjeq
  have hlt : V.primeList[j] < V.primeList[(k + 1) - 1] :=
    (V.primeList_sortedLT.getElem_lt_getElem_iff).mpr (by omega)
  omega

/-- **Piece A.** Stepping down one level multiplies the large part by the
    `p_{k+1}`-power: `π_k(s) = p_{k+1}^{ν_{p_{k+1}}(s)} · π_{k+1}(s)`. -/
lemma largePart_pred (k : ℕ) (hph : 2 ≤ V.pOrd (k + 1)) (s : ℕ) :
    V.largePart k s
      = V.pOrd (k + 1) ^ s.factorization (V.pOrd (k + 1)) * V.largePart (k + 1) s := by
  have hsp := V.smallPrimes_succ k hph
  have hnm := V.pOrd_succ_not_mem_smallPrimes k hph
  unfold largePart
  rw [hsp, Finset.sdiff_insert]
  by_cases hmem : V.pOrd (k + 1) ∈ s.primeFactors \ V.smallPrimes k
  · exact (Finset.mul_prod_erase (s.primeFactors \ V.smallPrimes k)
      (fun q => q ^ s.factorization q) hmem).symm
  · have hpf : V.pOrd (k + 1) ∉ s.primeFactors :=
      fun hc => hmem (Finset.mem_sdiff.mpr ⟨hc, hnm⟩)
    have hv0 : s.factorization (V.pOrd (k + 1)) = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hpf
    rw [Finset.erase_eq_of_notMem hmem, hv0, pow_zero, one_mul]

/-! #### Piece B: the layer recursion

Partitioning `ℒ_{k+1}(Q')` by `ν_{p_{k+1}}` and sending each fiber into the level
below (Piece A: `ν_{p_{k+1}}(L) = e ⟹ L ∈ ℒ_k(Q'·p_{k+1}^e)`) gives the recursion
`S_{k+1}(Q') ≤ ∑_{e=0}^{d_{k+1}} S_k(Q'·p_{k+1}^e)`.  The `d_{k+1}=0` collapse
`S_{k+1}(Q') ≤ S_k(Q')` is the special case (`range 1 = {0}`, `Q'·p^0 = Q'`). -/

/-- **Piece B.** The layer recursion: `S_{k+1}(Q') ≤ ∑_{e ≤ d_{k+1}} S_k(Q'·p_{k+1}^e)`. -/
lemma sum_LSet_layer_le (k : ℕ) (hph : 2 ≤ V.pOrd (k + 1)) (Q' : ℕ) :
    (V.LSet (k + 1) Q').sum id
      ≤ ∑ e ∈ Finset.range (V.dSet (k + 1) (V.LSet (k + 1) Q') + 1),
          (V.LSet k (Q' * V.pOrd (k + 1) ^ e)).sum id := by
  have hmaps : ∀ L ∈ V.LSet (k + 1) Q',
      L.factorization (V.pOrd (k + 1))
        ∈ Finset.range (V.dSet (k + 1) (V.LSet (k + 1) Q') + 1) := by
    intro L hL
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := fun s => s.factorization (V.pOrd (k + 1))) hL
  rw [← Finset.sum_fiberwise_of_maps_to hmaps id]
  apply Finset.sum_le_sum
  intro e _
  apply Finset.sum_le_sum_of_subset
  intro L hL
  rw [Finset.mem_filter] at hL
  obtain ⟨hLmem, hLe⟩ := hL
  rw [V.mem_LSet_iff] at hLmem
  rw [V.mem_LSet_iff]
  refine ⟨hLmem.1, ?_⟩
  rw [V.largePart_pred k hph L, hLmem.2, hLe]
  ring

/-! #### Piece C: the base level

At level `0` the large part `π_0` is the whole number (`smallPrimes 0 = ∅`), so
`ℒ_0(Q') ⊆ {Q'}` and `S_0(Q') ≤ Q'`.  This is the base of the outer induction. -/

/-- **Piece C.** Base level: `S_0(Q') ≤ Q'` (since `π_0(s) = s`, so `ℒ_0(Q') ⊆ {Q'}`). -/
lemma sum_LSet_zero_le (Q' : ℕ) : (V.LSet 0 Q').sum id ≤ Q' := by
  have hsub : V.LSet 0 Q' ⊆ {Q'} := by
    intro s hs
    rw [V.mem_LSet_iff] at hs
    obtain ⟨hsS, hlp⟩ := hs
    have hs0 : s ≠ 0 := (V.sizes_pos s hsS).ne'
    have hlp0 : V.largePart 0 s = s := by
      have hsp0 : V.smallPrimes 0 = (∅ : Finset ℕ) := by
        rw [show V.smallPrimes 0 = (V.primeList.take 0).toFinset from rfl,
            List.take_zero, List.toFinset_nil]
      unfold largePart
      rw [hsp0, Finset.sdiff_empty]
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hs0]
      rw [Nat.prod_factorization_eq_prod_primeFactors (fun p k => p ^ k)]
    rw [hlp0] at hlp
    rw [Finset.mem_singleton]; exact hlp
  calc (V.LSet 0 Q').sum id ≤ ({Q'} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hsub
    _ = Q' := by simp

/-! #### Piece D: `𝒜_h` monotonicity in the level

Being supported on `{p₁,…,p_k}` implies being supported on the larger
`{p₁,…,p_{k+1}}`, so `𝒜_k ⊆ 𝒜_{k+1}`.  This lets the hypothesis (H2) bound on
`∑_{𝒜_h}` be inherited by the level below in the induction. -/

/-- `{p₁,…,p_k} ⊆ {p₁,…,p_{k+1}}`. -/
lemma smallPrimes_subset_succ (k : ℕ) : V.smallPrimes k ⊆ V.smallPrimes (k + 1) := by
  intro x hx
  rw [show V.smallPrimes k = (V.primeList.take k).toFinset from rfl, List.mem_toFinset] at hx
  rw [show V.smallPrimes (k + 1) = (V.primeList.take (k + 1)).toFinset from rfl,
      List.mem_toFinset, List.take_add_one]
  exact List.mem_append_left _ hx

/-- **Piece D.** `𝒜_k ⊆ 𝒜_{k+1}`: a size supported on `{p₁,…,p_k}` is supported
    on `{p₁,…,p_{k+1}}`.  Propagates hypothesis (H2) down the `h`-induction. -/
lemma ASet_subset_succ (k : ℕ) : V.ASet k ⊆ V.ASet (k + 1) := by
  intro s hs
  simp only [ASet, AP, Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, fun p hp => V.smallPrimes_subset_succ k (hs.2 p hp)⟩

/-! #### Piece E helpers: out-of-range collapse and large-part support

For the core induction we need two robust facts: when `p_{k+1}` is out of range
(`< 2`) the small-prime set does not grow, so `ℒ_{k+1} = ℒ_k`; more generally the
`d_{k+1}=0` collapse `ℒ_{k+1}(Q') ⊆ ℒ_k(Q')`; and that the large part `π_h(s)` only
involves primes of `s` above `p_h` (needed to feed `bound_vh_general`). -/

/-- If `p_{k+1} < 2` (out of range), `{p₁,…,p_{k+1}} = {p₁,…,p_k}`. -/
lemma smallPrimes_eq_of_pOrd_lt (k : ℕ) (h : V.pOrd (k + 1) < 2) :
    V.smallPrimes (k + 1) = V.smallPrimes k := by
  have hlen : V.primeList.length ≤ k := by
    by_contra hc
    have hc' : k < V.primeList.length := not_le.mp hc
    have hpk : V.pOrd (k + 1) = V.primeList[k] := by
      rw [show V.pOrd (k + 1) = V.primeList.getD k 1 from rfl, List.getD_eq_getElem]
    have hmem : V.primeList[k] ∈ V.primeList := List.getElem_mem hc'
    have h2 := (Nat.prime_of_mem_primeFactors (V.mem_primeList.mp hmem)).two_le
    rw [hpk] at h
    omega
  rw [show V.smallPrimes (k + 1) = (V.primeList.take (k + 1)).toFinset from rfl,
      show V.smallPrimes k = (V.primeList.take k).toFinset from rfl,
      List.take_of_length_le (show V.primeList.length ≤ k + 1 by omega),
      List.take_of_length_le hlen]

/-- The `d_{k+1}=0` collapse: `ℒ_{k+1}(Q') ⊆ ℒ_k(Q')`. -/
lemma LSet_succ_subset_of_dSet_zero (k Q' : ℕ)
    (hd0 : V.dSet (k + 1) (V.LSet (k + 1) Q') = 0) :
    V.LSet (k + 1) Q' ⊆ V.LSet k Q' := by
  intro L hL
  have hLmem := (V.mem_LSet_iff (k + 1)).mp hL
  have hle : L.factorization (V.pOrd (k + 1)) ≤ V.dSet (k + 1) (V.LSet (k + 1) Q') :=
    Finset.le_sup (f := fun s => s.factorization (V.pOrd (k + 1))) hL
  have hν0 : L.factorization (V.pOrd (k + 1)) = 0 := by omega
  rw [V.mem_LSet_iff]
  refine ⟨hLmem.1, ?_⟩
  by_cases hph : 2 ≤ V.pOrd (k + 1)
  · rw [V.largePart_pred k hph L, hν0, pow_zero, one_mul, hLmem.2]
  · have hsp := V.smallPrimes_eq_of_pOrd_lt k (by omega)
    rw [show V.largePart k L = V.largePart (k + 1) L from by unfold largePart; rw [hsp], hLmem.2]

/-- The prime factors of `π_h(s)` lie among `s.primeFactors \ {p₁,…,p_h}`. -/
lemma largePart_primeFactors_subset (h s : ℕ) :
    (V.largePart h s).primeFactors ⊆ s.primeFactors \ V.smallPrimes h := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpdvd, _⟩ := hp
  unfold largePart at hpdvd
  rw [(hpp.prime.dvd_finsetProd_iff _)] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
  have : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.prime.dvd_of_dvd_pow hpq)
  rw [this]; exact hq

/-! ### Theorem 3.7 infrastructure (Piece 0): the level/prime correspondence

Characterizations relating a level `h` to the prime `p_h = pOrd h`: which primes
lie in `{p₁,…,p_h}`, which sizes are in `𝒜_h`, that every prime of `n` is some
`p_h`, and that `𝒜_h = S` once `h` covers all prime levels.  Used throughout the
main induction. -/

/-- `p_j = primeList[j-1]` whenever `j-1` is in range (no primality assumption). -/
lemma pOrd_eq_getElem' {j : ℕ} (hr : j - 1 < V.primeList.length) :
    V.pOrd j = V.primeList[j - 1] := by
  rw [show V.pOrd j = V.primeList.getD (j - 1) 1 from rfl, List.getD_eq_getElem]

/-- `p_j ≤ p_h` for `1 ≤ j ≤ h` (with `h` in range). -/
lemma pOrd_le_pOrd {j : ℕ} (hj1 : 1 ≤ j) (hjh : j ≤ h) (hph : 2 ≤ V.pOrd h) :
    V.pOrd j ≤ V.pOrd h := by
  have hrh : h - 1 < V.primeList.length := V.pOrd_range hph
  have hrj : j - 1 < V.primeList.length := by omega
  rw [V.pOrd_eq_getElem' hrj, V.pOrd_eq_getElem hph]
  exact (V.primeList_sortedLT.getElem_le_getElem_iff).mpr (by omega)

/-- `q ∈ {p₁,…,p_h} ↔ q` is a prime factor of `n` with `q ≤ p_h` (for `h` in range). -/
lemma mem_smallPrimes_iff (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h) {q : ℕ} :
    q ∈ V.smallPrimes h ↔ q ∈ V.n.primeFactors ∧ q ≤ V.pOrd h := by
  rw [show V.smallPrimes h = (V.primeList.take h).toFinset from rfl, List.mem_toFinset]
  have hrh : h - 1 < V.primeList.length := V.pOrd_range hph
  constructor
  · intro hq
    refine ⟨V.mem_primeList.mp (List.mem_of_mem_take hq), ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
    rw [List.length_take] at hj
    rw [List.getElem_take, V.pOrd_eq_getElem hph]
    exact (V.primeList_sortedLT.getElem_le_getElem_iff).mpr (by omega)
  · rintro ⟨hqn, hqle⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (V.mem_primeList.mpr hqn)
    rw [V.pOrd_eq_getElem hph] at hqle
    have hile : i ≤ h - 1 := (V.primeList_sortedLT.getElem_le_getElem_iff).mp hqle
    rw [List.mem_iff_getElem]
    exact ⟨i, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩

/-- `s ∈ 𝒜_h ↔ s ∈ S` and every prime of `s` is `≤ p_h` (for `h` in range). -/
lemma mem_ASet_iff_le (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h) {s : ℕ} :
    s ∈ V.ASet h ↔ s ∈ V.S ∧ ∀ p ∈ s.primeFactors, p ≤ V.pOrd h := by
  simp only [ASet, AP, Finset.mem_filter]
  constructor
  · rintro ⟨hsS, hsupp⟩
    exact ⟨hsS, fun p hp => ((V.mem_smallPrimes_iff hh1 hph).mp (hsupp p hp)).2⟩
  · rintro ⟨hsS, hle⟩
    refine ⟨hsS, fun p hp => (V.mem_smallPrimes_iff hh1 hph).mpr
      ⟨Nat.primeFactors_mono (V.sizes_dvd s hsS) V.n_pos.ne' hp, hle p hp⟩⟩

/-- Every prime factor of `n` is `p_h` for some `h ≥ 1`. -/
lemma exists_pOrd_eq {p : ℕ} (hp : p ∈ V.n.primeFactors) :
    ∃ h, 1 ≤ h ∧ V.pOrd h = p := by
  obtain ⟨i, hi, hip⟩ := List.mem_iff_getElem.mp (V.mem_primeList.mpr hp)
  refine ⟨i + 1, by omega, ?_⟩
  rw [V.pOrd_eq_getElem' (by omega : i + 1 - 1 < V.primeList.length)]
  simpa using hip

/-- `𝒜_h = S` once `h ≥ ℓ` (all prime levels covered). -/
lemma ASet_eq_S_of_length_le (hle : V.primeList.length ≤ h) : V.ASet h = V.S := by
  rw [show V.ASet h = V.S.filter (fun s => IsSupportedOn s (V.smallPrimes h)) from rfl]
  apply Finset.filter_true_of_mem
  intro s hsS p hp
  rw [show V.smallPrimes h = (V.primeList.take h).toFinset from rfl, List.take_of_length_le hle,
      List.mem_toFinset, V.mem_primeList]
  exact Nat.primeFactors_mono (V.sizes_dvd s hsS) V.n_pos.ne' hp

/-! ### Theorem 3.7 infrastructure (Piece 3): the σ size-and-sum bound -/

/-- A small prime `q ∈ {p₁,…,p_h}` is `p_j` for some `1 ≤ j ≤ h`. -/
lemma exists_pOrd_eq_of_mem_smallPrimes (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h) {q : ℕ}
    (hq : q ∈ V.smallPrimes h) : ∃ j, 1 ≤ j ∧ j ≤ h ∧ V.pOrd j = q := by
  obtain ⟨hqn, hqle⟩ := (V.mem_smallPrimes_iff hh1 hph).mp hq
  obtain ⟨j, hj1, hpj⟩ := V.exists_pOrd_eq hqn
  refine ⟨j, hj1, ?_, hpj⟩
  have h2j : 2 ≤ V.pOrd j := by rw [hpj]; exact (Nat.prime_of_mem_primeFactors hqn).two_le
  have hrj : j - 1 < V.primeList.length := V.pOrd_range h2j
  have hle : V.pOrd j ≤ V.pOrd h := by rw [hpj]; exact hqle
  rw [V.pOrd_eq_getElem' hrj, V.pOrd_eq_getElem hph] at hle
  have := (V.primeList_sortedLT.getElem_le_getElem_iff).mp hle
  omega

/-- **Piece 3.** With all `d_j(𝒜_h) ≤ D`, every `s ∈ 𝒜_h` divides
    `M = ∏_{q ∈ {p₁,…,p_h}} q^D`, so `∑_{𝒜_h} ≤ σ(M)`.  This is the "finish" of the
    main induction: a uniform bound on `∑_{𝒜_h}` once all the valuations are bounded. -/
lemma sum_ASet_le_sigma (h : ℕ) (hh1 : 1 ≤ h) (hph : 2 ≤ V.pOrd h) (D : ℕ)
    (hd : ∀ j, 1 ≤ j → j ≤ h → V.dSet j (V.ASet h) ≤ D) :
    (V.ASet h).sum id ≤ σ 1 (∏ q ∈ V.smallPrimes h, q ^ D) := by
  set M := ∏ q ∈ V.smallPrimes h, q ^ D with hM
  have hM0 : 0 < M := by
    rw [hM]; apply Finset.prod_pos; intro q hq
    have hqpos : 0 < q := (Nat.prime_of_mem_primeFactors (V.smallPrimes_subset_primeFactors hq)).pos
    exact pow_pos hqpos D
  apply sum_le_sigma_of_dvd _ M hM0
  intro s hsA
  have hsmem := (V.mem_ASet_iff_le hh1 hph).mp hsA
  have hs0 : s ≠ 0 := (V.sizes_pos s hsmem.1).ne'
  rw [← Nat.factorization_le_iff_dvd hs0 hM0.ne', Finsupp.le_def]
  intro q₀
  by_cases hq0 : q₀ ∈ s.primeFactors
  · have hq0prime := Nat.prime_of_mem_primeFactors hq0
    have hq0n : q₀ ∈ V.n.primeFactors :=
      Nat.primeFactors_mono (V.sizes_dvd s hsmem.1) V.n_pos.ne' hq0
    have hq0small : q₀ ∈ V.smallPrimes h :=
      (V.mem_smallPrimes_iff hh1 hph).mpr ⟨hq0n, hsmem.2 q₀ hq0⟩
    obtain ⟨j, hj1, hjh, hpj⟩ := V.exists_pOrd_eq_of_mem_smallPrimes hh1 hph hq0small
    have hνs : s.factorization q₀ ≤ D := by
      rw [← hpj]
      exact le_trans (Finset.le_sup (f := fun t => t.factorization (V.pOrd j)) hsA) (hd j hj1 hjh)
    have hνM : D ≤ M.factorization q₀ :=
      (Nat.Prime.pow_dvd_iff_le_factorization hq0prime hM0.ne').mp
        (by rw [hM]; exact Finset.dvd_prod_of_mem _ hq0small)
    omega
  · have : s.factorization q₀ = 0 :=
      Finsupp.notMem_support_iff.mp (by rw [Nat.support_factorization]; exact hq0)
    omega

/-! ### Theorem 3.7 infrastructure (Piece 2): sup attainment, large-part bound -/

/-- **Piece 2a.** The supremum `d_j(T)` is attained by some member of `T`. -/
lemma dSet_attained {j : ℕ} {T : Finset ℕ} (hT : T.Nonempty) :
    ∃ K ∈ T, V.dSet j T = K.factorization (V.pOrd j) :=
  Finset.exists_mem_eq_sup T hT (fun s => s.factorization (V.pOrd j))

/-- **Piece 2b.** The "large part" `π_j(K)` of `K ∈ 𝒜_H` is `≤ (P^D)^H`, where `P`
    bounds the primes of `K` and `D` bounds the valuations `d_i(𝒜_H)` for `j < i ≤ H`.
    This bounds the `Q = π_j(K)` fed into Lemmas 3.5/3.6 in the descending induction. -/
lemma largePart_le {j H : ℕ} (hj1 : 1 ≤ j) (hpj : 2 ≤ V.pOrd j) (hH1 : 1 ≤ H)
    (hpH : 2 ≤ V.pOrd H) {K : ℕ} (hKA : K ∈ V.ASet H) (P D : ℕ) (hP1 : 1 ≤ P)
    (hP : ∀ p, p.Prime → p ∣ K → p ≤ P)
    (hD : ∀ i, j < i → i ≤ H → V.dSet i (V.ASet H) ≤ D) :
    V.largePart j K ≤ (P ^ D) ^ H := by
  have hKmem := (V.mem_ASet_iff_le hH1 hpH).mp hKA
  have hKS := hKmem.1
  have hKn : K ∣ V.n := V.sizes_dvd K hKS
  unfold largePart
  set A := K.primeFactors \ V.smallPrimes j with hA
  have hfac : ∀ q ∈ A, q ^ K.factorization q ≤ P ^ D := by
    intro q hq
    rw [hA, Finset.mem_sdiff] at hq
    obtain ⟨hqK, hqj⟩ := hq
    have hqprime := Nat.prime_of_mem_primeFactors hqK
    have hqdvd := Nat.dvd_of_mem_primeFactors hqK
    have hqn : q ∈ V.n.primeFactors := Nat.primeFactors_mono hKn V.n_pos.ne' hqK
    have hqsmallH : q ∈ V.smallPrimes H :=
      (V.mem_smallPrimes_iff hH1 hpH).mpr ⟨hqn, hKmem.2 q hqK⟩
    obtain ⟨i, hi1, hiH, hpi⟩ := V.exists_pOrd_eq_of_mem_smallPrimes hH1 hpH hqsmallH
    have hij : j < i := by
      by_contra hc
      push_neg at hc
      exact hqj ((V.mem_smallPrimes_iff hj1 hpj).mpr ⟨hqn, hpi ▸ V.pOrd_le_pOrd hi1 hc hpj⟩)
    have hνq : K.factorization q ≤ D := by
      rw [← hpi]
      exact le_trans (Finset.le_sup (f := fun t => t.factorization (V.pOrd i)) hKA)
        (hD i hij hiH)
    calc q ^ K.factorization q
        ≤ P ^ K.factorization q := Nat.pow_le_pow_left (hP q hqprime hqdvd) _
      _ ≤ P ^ D := Nat.pow_le_pow_right hP1 hνq
  have hcard : A.card ≤ H := by
    calc A.card ≤ K.primeFactors.card := Finset.card_le_card (Finset.sdiff_subset)
      _ ≤ (V.smallPrimes H).card := Finset.card_le_card (fun q hq =>
            (V.mem_smallPrimes_iff hH1 hpH).mpr ⟨Nat.primeFactors_mono hKn V.n_pos.ne' hq,
              hKmem.2 q hq⟩)
      _ ≤ H := by
            rw [show V.smallPrimes H = (V.primeList.take H).toFinset from rfl]
            exact le_trans (List.toFinset_card_le _) (List.length_take_le _ _)
  calc ∏ q ∈ A, q ^ K.factorization q ≤ ∏ q ∈ A, P ^ D := Finset.prod_le_prod' hfac
    _ = (P ^ D) ^ A.card := by rw [Finset.prod_const]
    _ ≤ (P ^ D) ^ H := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hP1) hcard

/-- `𝒜_j ⊆ 𝒜_h` for `j ≤ h` (monotonicity of the family `𝒜`). -/
lemma ASet_mono {j h : ℕ} (hjh : j ≤ h) : V.ASet j ⊆ V.ASet h := by
  induction hjh with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (V.ASet_subset_succ _)

/-- **Piece 4 helper.** A prime factor `q` of `n` with `q ≤ N` lies among the first
    `N` primes `{p₁,…,p_N}`: there are fewer than `N` primes in `[2,N]`, so `q`'s
    index is `< N`.  (This is what makes `𝒜_{P_max} = S` without bounding `ℓ`.) -/
lemma mem_smallPrimes_of_le {N q : ℕ} (hq : q ∈ V.n.primeFactors) (hqN : q ≤ N) :
    q ∈ V.smallPrimes N := by
  obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp (V.mem_primeList.mpr hq)
  have hiN : i < N := by
    have hsub : (V.primeList.take (i + 1)).toFinset ⊆ Finset.Icc 2 N := by
      intro q' hq'
      rw [List.mem_toFinset] at hq'
      obtain ⟨j, hj, hq'j⟩ := List.mem_iff_getElem.mp hq'
      rw [List.length_take] at hj
      rw [List.getElem_take] at hq'j
      rw [Finset.mem_Icc]
      have hq'p : q' ∈ V.n.primeFactors := by
        rw [← hq'j]; exact V.mem_primeList.mp (List.getElem_mem _)
      refine ⟨(Nat.prime_of_mem_primeFactors hq'p).two_le, ?_⟩
      calc q' = V.primeList[j] := hq'j.symm
        _ ≤ V.primeList[i] := (V.primeList_sortedLT.getElem_le_getElem_iff).mpr (by omega)
        _ = q := hqi
        _ ≤ N := hqN
    have hcard : (V.primeList.take (i + 1)).toFinset.card = i + 1 := by
      rw [List.toFinset_card_of_nodup
            ((List.take_sublist (i + 1) V.primeList).nodup V.primeList_sortedLT.nodup),
          List.length_take]
      omega
    have hle := Finset.card_le_card hsub
    rw [hcard, Nat.card_Icc] at hle
    omega
  rw [show V.smallPrimes N = (V.primeList.take N).toFinset from rfl, List.mem_toFinset,
      List.mem_iff_getElem]
  exact ⟨i, by rw [List.length_take]; omega, by rw [List.getElem_take]; exact hqi⟩

end ValidCosetPartition

/-! ### Proposition 3.3 (`prop:bound-v2-even`): the `p₁ = 2` valuation bound

Assume the smallest prime of `n` is `p₁ = 2`.  Fix `Q ≥ 1` supported on the
*larger* primes `{p₂,…,p_ℓ}`.  If the total mass contributed by all sizes whose
"large part" `π₁` is a **proper** divisor of `Q` is bounded by a constant `C`
(read as `C(m)`, depending only on `m`), then the largest `2`-adic valuation
occurring among the sizes in `ℒ₁(Q)`, namely `d₁(ℒ₁(Q))`, is bounded in terms
of `m` only.

Dictionary to the symbols defined in `Defs.lean` (`def:symbols`):

* `sys.pOrd 1`  is `p₁`, so `sys.pOrd 1 = 2` is the hypothesis `p₁ = 2`;
* `sys.smallPrimes 1 = {p₁}`, hence `sys.n.primeFactors \ sys.smallPrimes 1`
  is exactly `{p₂,…,p_ℓ}`, and `IsSupportedOn Q …` says `Q` uses only those;
* `sys.LSet 1 Q'` is `ℒ₁(Q') = {s ∈ S : π₁(s) = Q'}`, and `(·).sum id` sums the
  sizes in it (singletons are absorbed into `C`, as in the paper);
* `Q.properDivisors = {Q' : Q' ∣ Q, Q' ≠ Q}`, so the nested `Finset.sum`
  is the paper's `∑_{Q'∣Q, Q'≠Q} ∑_{L∈ℒ₁(Q')} |L|`;
* `sys.dSet 1 (sys.LSet 1 Q)` is `d₁(ℒ₁(Q))`, the maximal `ν₂` over `ℒ₁(Q)`.

"Bounded in terms of `m` only" is captured by exhibiting a single `B` (depending
on the given `C`, hence on `m`) that works uniformly across *all* valid systems. -/

/-- **Proposition 3.3** (`prop:bound-v2-even`): with `p₁ = 2`, the maximal
    `2`-adic valuation `d₁(ℒ₁(Q))` is bounded once the proper-divisor tail of
    `Q` has bounded mass. -/
theorem bound_v2_even (C : ℕ) :
    ∃ B : ℕ, ∀ (sys : ValidCosetPartition m),
      sys.pOrd 1 = 2 →
      ∀ (Q : ℕ), 1 ≤ Q →
        IsSupportedOn Q (sys.n.primeFactors \ sys.smallPrimes 1) →
        (∑ Q' ∈ Q.properDivisors, (sys.LSet 1 Q').sum id) ≤ C →
        sys.dSet 1 (sys.LSet 1 Q) ≤ B := by
  -- The bound is `B = C + m`.  For the maximizer `s₀` (with `ν₂ s₀ = d₁`):
  -- `3·s₀ ≤ ∑_W + m ≤ Q·2^{d₁+1} + C + m = 2·s₀ + C + m`, so `s₀ ≤ C + m`, and
  -- finally `d₁ ≤ 2^{d₁} ≤ s₀ ≤ C + m`.
  refine ⟨C + m, fun sys hp Q hQ hsupp htail => ?_⟩
  -- Q is odd: its prime factors avoid `smallPrimes 1 = {2}`.
  have hQodd : ¬ 2 ∣ Q := by
    intro h2
    have h2mem : 2 ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, by omega⟩
    have hmem := hsupp 2 h2mem
    rw [sys.smallPrimes_one hp] at hmem
    simp [Finset.mem_sdiff] at hmem
  rcases (sys.LSet 1 Q).eq_empty_or_nonempty with hE | hNE
  · simp [ValidCosetPartition.dSet, hE]
  · obtain ⟨s₀, hs₀, hs₀d, _⟩ := sys.exists_mem_LSet_factorization_eq_dSet 1 hNE
    rw [hp] at hs₀d
    set d := sys.dSet 1 (sys.LSet 1 Q) with hd
    have hbridge : s₀ = 2 ^ d * Q := by
      rw [← hs₀d]; exact sys.eq_two_pow_mul_of_mem_LSet_one hp hs₀
    have h3 := sys.three_mul_s₀_le hp hQ hQodd hs₀
    have hW := sys.sum_filterLargePartDvd_le hp hQ
    rw [← hd] at hW
    have hQ2 : Q * 2 ^ (d + 1) = 2 * s₀ := by rw [hbridge, pow_succ]; ring
    have hs₀le : s₀ ≤ C + m := by
      have hchain : 3 * s₀ ≤ 2 * s₀ + C + m := by
        calc 3 * s₀
            ≤ (∑ t ∈ sys.S.filter (fun t => sys.largePart 1 t ∣ Q), t) + m := h3
          _ ≤ (Q * 2 ^ (d + 1) + ∑ Q' ∈ Q.properDivisors, (sys.LSet 1 Q').sum id) + m :=
              Nat.add_le_add_right hW m
          _ ≤ 2 * s₀ + C + m := by rw [hQ2]; omega
      omega
    have hd2 : d ≤ 2 ^ d := Nat.le_of_lt d.lt_two_pow_self
    have hs₀ge : 2 ^ d ≤ s₀ := by rw [hbridge]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega

/-! ### Proposition 3.4 (`prop:bound-vh_odd`): the `p_h ≥ 3` valuation bound

For `p_h ≥ 3` there is no same-valuation shortcut, so the argument follows the
paper: pick `K ∈ ℒ_h(Q)` with maximal `ν_{p_h}` that is division-minimal among
the maximal-valuation members (Piece 2); write `N_K = |K|/Q` (Piece 3); the
divisors of `K` in `ℒ_h(Q)` then have strictly smaller `ν_{p_h}`, giving the
`σ`-bound (Piece 4) and the core inequality `N_K ≤ σ(N_K/p_h) + (C+m)` (Piece 5);
finally the (already proven) divisor-sum inequality `divisor_sum_ineq` bounds both
`p_h` and `N_K` — hence `d_h ≤ N_K` — in terms of `m` only. -/

/-- **Proposition 3.4** (`prop:bound-vh_odd`): with `p_h ≥ 3` and `Q` supported on
    the primes above `p_h`, both `p_h` and `d_h(ℒ_h(Q))` are bounded once the
    proper-divisor tail of `Q` has bounded mass. -/
theorem bound_vh_odd (C : ℕ) :
    ∃ B : ℕ, ∀ (sys : ValidCosetPartition m) (h : ℕ),
      1 ≤ h → 3 ≤ sys.pOrd h →
      ∀ (Q : ℕ), 1 ≤ Q →
        IsSupportedOn Q (sys.n.primeFactors \ sys.smallPrimes h) →
        (sys.LSet h Q).Nonempty →
        1 ≤ sys.dSet h (sys.LSet h Q) →
        (∑ Q' ∈ Q.properDivisors, (sys.LSet h Q').sum id) ≤ C →
        sys.pOrd h ≤ B ∧ sys.dSet h (sys.LSet h Q) ≤ B := by
  obtain ⟨B, hB⟩ := divisor_sum_ineq (C + m)
  refine ⟨B, fun sys h hh1 hph3 Q hQ hsupp hNE hd1 htail => ?_⟩
  have hph : 2 ≤ sys.pOrd h := by omega
  obtain ⟨s₀, hs₀L, hs₀d, hs₀min⟩ := sys.exists_divisionMinimal_maximal h hNE
  have hd1' : 1 ≤ s₀.factorization (sys.pOrd h) := by rw [hs₀d]; exact hd1
  obtain ⟨hNK, hνNK, hNKprimes⟩ := sys.NK_structure h hh1 hph hs₀L hQ hsupp
  have hmem := (sys.mem_LSet_iff h).mp hs₀L
  have hs₀0 : s₀ ≠ 0 := (sys.sizes_pos s₀ hmem.1).ne'
  have hQdvd : Q ∣ s₀ := by rw [← hmem.2]; exact sys.largePart_dvd h hs₀0
  have hNKpos : 0 < s₀ / Q := Nat.div_pos (Nat.le_of_dvd (by omega) hQdvd) (by omega)
  have hNK0 : s₀ / Q ≠ 0 := hNKpos.ne'
  have hpN : sys.pOrd h ∣ s₀ / Q :=
    Nat.dvd_of_factorization_pos (by rw [hνNK, hs₀d]; omega)
  have h1N : 1 < s₀ / Q := by have := Nat.le_of_dvd hNKpos hpN; omega
  have hcore := sys.core_inequality h hh1 hph hs₀L hQ hsupp hs₀d hs₀min hd1' C htail
  obtain ⟨hp_le, hN_le⟩ :=
    hB (s₀ / Q) (sys.pOrd h) h1N (sys.pOrd_prime hph) hph3 hpN hNKprimes hcore
  refine ⟨hp_le, ?_⟩
  rw [← hs₀d, ← hνNK]
  exact le_trans (Nat.le_of_lt (Nat.factorization_lt _ hNK0)) hN_le

/-! ### Lemma 3.5: Propositions 3.3 and 3.4 combined

For any level `h` (with `1 ≤ h`), both `p_h` and `d_h(ℒ_h(Q))` are bounded in
terms of `m` only.  The proof splits on `p_h`: the case `p_h = 2` forces `h = 1`
(2 is the smallest prime) and is Proposition 3.3 (`bound_v2_even`); the case
`p_h ≥ 3` is Proposition 3.4 (`bound_vh_odd`).  The hypothesis `d_h ≥ 1` is what
guarantees `p_h` is a genuine prime (`≥ 2`), enabling the split. -/

/-- **Lemma 3.5** (`lem:bound-vh-general`): for any level `h`, both `p_h` and
    `d_h(ℒ_h(Q))` are bounded in terms of `m` only. -/
theorem bound_vh_general (C : ℕ) :
    ∃ B : ℕ, ∀ (sys : ValidCosetPartition m) (h : ℕ),
      1 ≤ h →
      ∀ (Q : ℕ), 1 ≤ Q →
        IsSupportedOn Q (sys.n.primeFactors \ sys.smallPrimes h) →
        (sys.LSet h Q).Nonempty →
        1 ≤ sys.dSet h (sys.LSet h Q) →
        (∑ Q' ∈ Q.properDivisors, (sys.LSet h Q').sum id) ≤ C →
        sys.pOrd h ≤ B ∧ sys.dSet h (sys.LSet h Q) ≤ B := by
  obtain ⟨B₂, hB₂⟩ := bound_v2_even C
  obtain ⟨B₃, hB₃⟩ := bound_vh_odd C
  refine ⟨max (max B₂ B₃) 2, fun sys h hh1 Q hQ hsupp hNE hd1 htail => ?_⟩
  obtain ⟨s₀, hs₀L, hs₀d, _⟩ := sys.exists_divisionMinimal_maximal h hNE
  have hd1' : 1 ≤ s₀.factorization (sys.pOrd h) := by rw [hs₀d]; exact hd1
  have hph_prime : (sys.pOrd h).Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime _ hnp] at hd1'
    omega
  rcases lt_or_ge (sys.pOrd h) 3 with hlt3 | hge3
  · -- p_h = 2 (since 2 ≤ p_h < 3), so h = 1 and Proposition 3.3 applies
    have hph_eq : sys.pOrd h = 2 := by have := hph_prime.two_le; omega
    have hh_eq : h = 1 := sys.eq_one_of_pOrd_eq_two hh1 hph_eq
    subst hh_eq
    have hd_le := hB₂ sys hph_eq Q hQ hsupp htail
    refine ⟨?_, le_trans hd_le (by omega)⟩
    rw [hph_eq]; omega
  · -- p_h ≥ 3: Proposition 3.4 applies
    obtain ⟨hp_le, hd_le⟩ := hB₃ sys h hh1 hge3 Q hQ hsupp hNE hd1 htail
    exact ⟨le_trans hp_le (by omega), le_trans hd_le (by omega)⟩

/-! ### Lemma 3.6: Proper divisor-sum bound (`lem:proper-divisor-sum-bound`)

Writing `S_h(Q') := ∑_{L ∈ ℒ_h(Q')} |L| = (sys.LSet h Q').sum id`, the lemma says:
fix a level `h`; if `Q` is bounded (here `Q ≤ B_Q`, hypothesis (H1)) and the
level-`h` supported mass `∑_{L ∈ 𝒜_h} |L| = (sys.ASet h).sum id` is bounded (here
`≤ B_A`, hypothesis (H2)), then the proper-divisor tail `∑_{Q'∣Q, Q'≠Q} S_h(Q')`
is bounded by a constant `C` depending only on `h`, `B_Q`, `B_A` (hence, in the
application, only on `m`).

The proof is a double induction — outer on `h`, inner on divisibility of `Q'` —
using `bound_vh_general` (Lemma 3.5) to bound `d_h` and `p_h`, the consecutive-level
relation `π_{h-1}(s) = p_h^{ν_{p_h}(s)} · π_h(s)`, and `𝒜_h = ℒ_h(1)`. -/

/-- **Piece E** (the core double induction).  Uniformly over systems `sys` with
    `∑_{𝒜_k} ≤ B_A`, the mass `S_k(Q') = (sys.LSet k Q').sum id` is bounded by a
    constant `C` (depending on `k`, `B`, `B_A`) for every `Q' ≤ B`.

    Outer induction on `k` (base: `S_0(Q') ≤ Q'`); inner induction on the bound `B`.
    For each `Q'`: if `d_{k+1}(ℒ_{k+1}(Q')) ≥ 1`, then `p_{k+1}` is prime and
    `bound_vh_general` (with the proper-divisor tail supplied by the inner IH) bounds
    `p_{k+1}` and `d_{k+1}`; the layer recursion (Piece B) then reduces to level `k`
    (outer IH, at the enlarged bound `(B+1)·B_dp^{B_dp}`).  If `d_{k+1}=0` the layer
    collapses to level `k` directly. -/
lemma proper_div_aux (B_A : ℕ) : ∀ (k B : ℕ), ∃ C : ℕ,
    ∀ (sys : ValidCosetPartition m) (Q' : ℕ),
      Q' ≤ B → (sys.ASet k).sum id ≤ B_A → (sys.LSet k Q').sum id ≤ C := by
  intro k
  induction k with
  | zero =>
    exact fun B => ⟨B, fun sys Q' hQ' _ => le_trans (sys.sum_LSet_zero_le Q') hQ'⟩
  | succ k IH_k =>
    intro B
    induction B with
    | zero =>
      refine ⟨0, fun sys Q' hQ' _ => ?_⟩
      have hQ0 : Q' = 0 := Nat.le_zero.mp hQ'
      subst hQ0
      have hempty : sys.LSet (k + 1) 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro s hs
        rw [sys.mem_LSet_iff] at hs
        have hpos : 0 < sys.largePart (k + 1) s := by
          unfold ValidCosetPartition.largePart
          exact Finset.prod_pos fun q hq =>
            pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos _
        omega
      rw [hempty]; simp
    | succ B IH_B =>
      obtain ⟨C', hC'⟩ := IH_B
      obtain ⟨B_dp, hB_dp⟩ := bound_vh_general (m := m) ((B + 1) * C')
      obtain ⟨C_k', hC_k'⟩ := IH_k ((B + 1) * B_dp ^ B_dp)
      have hpow1 : 1 ≤ B_dp ^ B_dp := by
        rcases Nat.eq_zero_or_pos B_dp with h | h
        · rw [h]; simp
        · exact Nat.one_le_pow _ _ h
      refine ⟨(B_dp + 1) * C_k', fun sys Q' hQ' hA => ?_⟩
      have hA_k : (sys.ASet k).sum id ≤ B_A :=
        le_trans (Finset.sum_le_sum_of_subset (sys.ASet_subset_succ k)) hA
      by_cases hd : 1 ≤ sys.dSet (k + 1) (sys.LSet (k + 1) Q')
      · -- d ≥ 1: bound p_{k+1}, d_{k+1} via Lemma 3.5, then the layer recursion
        have hNE : (sys.LSet (k + 1) Q').Nonempty := by
          rcases Finset.eq_empty_or_nonempty (sys.LSet (k + 1) Q') with he | hne
          · rw [he] at hd; simp [ValidCosetPartition.dSet] at hd
          · exact hne
        obtain ⟨L, hL, hLd, _⟩ := sys.exists_mem_LSet_factorization_eq_dSet (k + 1) hNE
        have hLmem := (sys.mem_LSet_iff (k + 1)).mp hL
        have hph : 2 ≤ sys.pOrd (k + 1) := by
          have hpos : 0 < L.factorization (sys.pOrd (k + 1)) := by rw [hLd]; omega
          have hmem : sys.pOrd (k + 1) ∈ L.primeFactors := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
          exact (Nat.prime_of_mem_primeFactors hmem).two_le
        have hlppos : 0 < sys.largePart (k + 1) L := by
          unfold ValidCosetPartition.largePart
          exact Finset.prod_pos fun q hq =>
            pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos _
        have hQ'1 : 1 ≤ Q' := by rw [hLmem.2] at hlppos; omega
        have hsupp : IsSupportedOn Q' (sys.n.primeFactors \ sys.smallPrimes (k + 1)) := by
          intro p hp
          rw [← hLmem.2] at hp
          have hsub := sys.largePart_primeFactors_subset (k + 1) L hp
          rw [Finset.mem_sdiff] at hsub ⊢
          exact ⟨Nat.primeFactors_mono (sys.sizes_dvd L hLmem.1) sys.n_pos.ne' hsub.1, hsub.2⟩
        have hcard : Q'.properDivisors.card ≤ B + 1 := by
          have hsub : Q'.properDivisors ⊆ Finset.range Q' :=
            fun x hx => Finset.mem_range.mpr (Nat.mem_properDivisors.mp hx).2
          calc Q'.properDivisors.card ≤ (Finset.range Q').card := Finset.card_le_card hsub
            _ = Q' := Finset.card_range Q'
            _ ≤ B + 1 := hQ'
        have htail : (∑ Q'' ∈ Q'.properDivisors, (sys.LSet (k + 1) Q'').sum id) ≤ (B + 1) * C' := by
          calc (∑ Q'' ∈ Q'.properDivisors, (sys.LSet (k + 1) Q'').sum id)
              ≤ ∑ _Q'' ∈ Q'.properDivisors, C' := Finset.sum_le_sum fun Q'' hQ'' =>
                  hC' sys Q'' (by have := (Nat.mem_properDivisors.mp hQ'').2; omega) hA
            _ = Q'.properDivisors.card * C' := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ (B + 1) * C' := Nat.mul_le_mul hcard (le_refl C')
        obtain ⟨hp_le, hdSet_le⟩ := hB_dp sys (k + 1) (by omega) Q' hQ'1 hsupp hNE hd htail
        calc (sys.LSet (k + 1) Q').sum id
            ≤ ∑ e ∈ Finset.range (sys.dSet (k + 1) (sys.LSet (k + 1) Q') + 1),
                (sys.LSet k (Q' * sys.pOrd (k + 1) ^ e)).sum id := sys.sum_LSet_layer_le k hph Q'
          _ ≤ ∑ _e ∈ Finset.range (sys.dSet (k + 1) (sys.LSet (k + 1) Q') + 1), C_k' := by
              apply Finset.sum_le_sum
              intro e he
              rw [Finset.mem_range, Nat.lt_succ_iff] at he
              exact hC_k' sys (Q' * sys.pOrd (k + 1) ^ e)
                (Nat.mul_le_mul hQ' (le_trans (Nat.pow_le_pow_left hp_le e)
                  (Nat.pow_le_pow_right (by omega) (by omega)))) hA_k
          _ = (sys.dSet (k + 1) (sys.LSet (k + 1) Q') + 1) * C_k' := by
              rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
          _ ≤ (B_dp + 1) * C_k' := Nat.mul_le_mul (by omega) (le_refl C_k')
      · -- d = 0: collapse to level k
        have hd0 : sys.dSet (k + 1) (sys.LSet (k + 1) Q') = 0 := by omega
        have hcollapse := sys.LSet_succ_subset_of_dSet_zero k Q' hd0
        have hQ'B' : Q' ≤ (B + 1) * B_dp ^ B_dp :=
          le_trans hQ' (Nat.le_mul_of_pos_right _ (by omega))
        calc (sys.LSet (k + 1) Q').sum id
            ≤ (sys.LSet k Q').sum id := Finset.sum_le_sum_of_subset hcollapse
          _ ≤ C_k' := hC_k' sys Q' hQ'B' hA_k
          _ ≤ (B_dp + 1) * C_k' := Nat.le_mul_of_pos_left _ (by omega)

/-- **Lemma 3.6** (`lem:proper-divisor-sum-bound`): for a fixed level `h`, with
    `Q ≤ B_Q` (H1) and `∑_{𝒜_h} |L| ≤ B_A` (H2), the proper-divisor tail
    `∑_{Q'∣Q, Q'≠Q} ∑_{L ∈ ℒ_h(Q')} |L|` is bounded by a constant `C`. -/
theorem proper_divisor_sum_bound (h B_Q B_A : ℕ) :
    ∃ C : ℕ, ∀ (sys : ValidCosetPartition m) (Q : ℕ),
      Q ≤ B_Q → (sys.ASet h).sum id ≤ B_A →
      (∑ Q' ∈ Q.properDivisors, (sys.LSet h Q').sum id) ≤ C := by
  -- Apply Piece E at level `k = h`, bound `B = B_Q`; sum the per-divisor bound `C₀`
  -- over the `≤ B_Q` proper divisors of `Q`.
  obtain ⟨C₀, hC₀⟩ := proper_div_aux (m := m) B_A h B_Q
  refine ⟨B_Q * C₀, fun sys Q hQ hA => ?_⟩
  have hcard : Q.properDivisors.card ≤ B_Q := by
    have hsub : Q.properDivisors ⊆ Finset.range Q :=
      fun x hx => Finset.mem_range.mpr (Nat.mem_properDivisors.mp hx).2
    calc Q.properDivisors.card ≤ (Finset.range Q).card := Finset.card_le_card hsub
      _ = Q := Finset.card_range Q
      _ ≤ B_Q := hQ
  calc (∑ Q' ∈ Q.properDivisors, (sys.LSet h Q').sum id)
      ≤ ∑ _Q' ∈ Q.properDivisors, C₀ := Finset.sum_le_sum fun Q' hQ' =>
          hC₀ sys Q' (by have := (Nat.mem_properDivisors.mp hQ').2; omega) hA
    _ = Q.properDivisors.card * C₀ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ B_Q * C₀ := Nat.mul_le_mul hcard (le_refl C₀)

/-! ### Key structural lemma -/

/-! ### Theorem 3.7: Main induction

The core argument: by strong induction on |P|, we show that ∑_{𝒜_P} is
bounded by a constant depending only on m.

**Key insight**: The bound on p_h (from Lemma 3.5 with Q = 1) depends ONLY
on m, not on h. This means all primes in any valid system are uniformly
bounded, hence the number of prime levels is finite and bounded.
-/

/-
**Lemma (Prime bound)**: For any valid system, every prime dividing any
    size in S is bounded by a constant depending only on m.

    Proof: Apply Lemma 3.5 with Q = 1 (no tail sum). The cell inequality
    gives ∑_{D(s₀)} ≥ s₀, and since the tail is 0, we get s₀ ≤ σ(s₀/p) + (m-1).
    The divisor-sum inequality then bounds p.
-/
theorem prime_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ P_max : ℕ, ∀ (sys : ValidCosetPartition m),
      ∀ s ∈ sys.S, ∀ p : ℕ, p.Prime → p ∣ s → p ≤ P_max := by
  -- **Piece 1.** Apply Lemma 3.5 (`bound_vh_general`) with `Q = 1` (empty tail, so
  -- `C = 0`) at the level `h` of the *largest* prime `P_s` of `s`: there `s ∈ 𝒜_h`
  -- and `d_h(𝒜_h) ≥ 1`, so `p ≤ P_s = p_h ≤ B`.  The bound is uniform over systems.
  obtain ⟨B, hB⟩ := bound_vh_general (m := m) 0
  refine ⟨B, fun sys s hsS p hp hpdvd => ?_⟩
  have hs1 : 1 < s := sys.sizes_gt_one s hsS
  have hs0 : s ≠ 0 := by omega
  have hpf_ne : s.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hs1
  set P_s := s.primeFactors.max' hpf_ne with hPs
  have hPs_mem : P_s ∈ s.primeFactors := Finset.max'_mem _ hpf_ne
  have hPs_prime : P_s.Prime := Nat.prime_of_mem_primeFactors hPs_mem
  have hPs_dvd_s : P_s ∣ s := Nat.dvd_of_mem_primeFactors hPs_mem
  have hPs_n : P_s ∈ sys.n.primeFactors :=
    Nat.primeFactors_mono (sys.sizes_dvd s hsS) sys.n_pos.ne' hPs_mem
  have hp_le : p ≤ P_s := Finset.le_max' _ p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hs0⟩)
  obtain ⟨h, hh1, hPs_eq⟩ := sys.exists_pOrd_eq hPs_n
  have hph : 2 ≤ sys.pOrd h := by rw [hPs_eq]; exact hPs_prime.two_le
  have hsA : s ∈ sys.ASet h := by
    rw [sys.mem_ASet_iff_le hh1 hph]
    exact ⟨hsS, fun q hq => hPs_eq ▸ Finset.le_max' _ q hq⟩
  have hLSet1 : sys.LSet h 1 = sys.ASet h := (sys.ASet_eq_LSet_one h).symm
  have hsL : s ∈ sys.LSet h 1 := by rw [hLSet1]; exact hsA
  have hNE : (sys.LSet h 1).Nonempty := ⟨s, hsL⟩
  have hd1 : 1 ≤ sys.dSet h (sys.LSet h 1) := by
    have hle : s.factorization (sys.pOrd h) ≤ sys.dSet h (sys.LSet h 1) :=
      Finset.le_sup (f := fun t => t.factorization (sys.pOrd h)) hsL
    have hpos : 1 ≤ s.factorization (sys.pOrd h) := by
      rw [hPs_eq]; exact hPs_prime.factorization_pos_of_dvd hs0 hPs_dvd_s
    omega
  have hsupp1 : IsSupportedOn 1 (sys.n.primeFactors \ sys.smallPrimes h) := by
    intro q hq; simp [Nat.primeFactors_one] at hq
  have htail : (∑ Q' ∈ (1 : ℕ).properDivisors, (sys.LSet h Q').sum id) ≤ 0 := by
    simp [Nat.properDivisors_one]
  obtain ⟨hp_le_B, _⟩ := hB sys h hh1 1 (le_refl 1) hsupp1 hNE hd1 htail
  rw [hPs_eq] at hp_le_B
  omega

/-- **Piece 2c/2d.** The descending induction: a uniform bound `D` on every
    valuation `d_j(𝒜_H)` (`1 ≤ j ≤ H`), provided `2 ≤ p_H` (in-range top level).
    Inputs: the uniform prime bound `P` and the IH sum bound `B_h` on `∑_{𝒜_j}`
    for `j ≤ H-1`.  The induction runs descending on `j = H, H-1, …, 1`: each level
    bounds `d_j(𝒜_H)` from the (already-bounded) higher valuations via the
    `Q = π_j(K)` bound (Piece 2b) plus Lemmas 3.6 and 3.5. -/
lemma dSet_ASet_bound (H : ℕ) (hH1 : 1 ≤ H) (P : ℕ) (hP1 : 1 ≤ P)
    (hP : ∀ (sys : ValidCosetPartition m), ∀ s ∈ sys.S, ∀ p, p.Prime → p ∣ s → p ≤ P)
    (B_h : ℕ)
    (hBh : ∀ (sys : ValidCosetPartition m), ∀ j, j ≤ H - 1 → (sys.ASet j).sum id ≤ B_h) :
    ∃ D, ∀ (sys : ValidCosetPartition m), 2 ≤ sys.pOrd H →
      ∀ j, 1 ≤ j → j ≤ H → sys.dSet j (sys.ASet H) ≤ D := by
  suffices hsuf : ∀ t, ∃ D, ∀ (sys : ValidCosetPartition m), 2 ≤ sys.pOrd H →
      ∀ i, 1 ≤ i → H - t ≤ i → i ≤ H → sys.dSet i (sys.ASet H) ≤ D by
    obtain ⟨D, hD⟩ := hsuf (H - 1)
    exact ⟨D, fun sys hpH j hj1 hjH => hD sys hpH j hj1 (by omega) hjH⟩
  intro t
  induction t with
  | zero =>
    obtain ⟨B0, hB0⟩ := bound_vh_general (m := m) 0
    refine ⟨B0, fun sys hpH i hi1 hilo hiH => ?_⟩
    have hiHe : i = H := by omega
    rw [hiHe]
    by_cases hd : 1 ≤ sys.dSet H (sys.ASet H)
    · have hLSet1 : sys.LSet H 1 = sys.ASet H := (sys.ASet_eq_LSet_one H).symm
      have hAne : (sys.ASet H).Nonempty := by
        by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
        rw [show sys.dSet H (sys.ASet H)
              = (sys.ASet H).sup (fun s => s.factorization (sys.pOrd H)) from rfl,
            he, Finset.sup_empty] at hd
        simp at hd
      have hNE : (sys.LSet H 1).Nonempty := by rw [hLSet1]; exact hAne
      have hd1 : 1 ≤ sys.dSet H (sys.LSet H 1) := by rw [hLSet1]; exact hd
      have hsupp1 : IsSupportedOn 1 (sys.n.primeFactors \ sys.smallPrimes H) := by
        intro q hq; simp [Nat.primeFactors_one] at hq
      have htail : (∑ Q' ∈ (1 : ℕ).properDivisors, (sys.LSet H Q').sum id) ≤ 0 := by
        simp [Nat.properDivisors_one]
      obtain ⟨_, hdB⟩ := hB0 sys H hH1 1 (le_refl 1) hsupp1 hNE hd1 htail
      rw [hLSet1] at hdB; exact hdB
    · omega
  | succ t ih =>
    obtain ⟨D_t, hD_t⟩ := ih
    by_cases hj0 : 1 ≤ H - (t + 1)
    · obtain ⟨C, hC⟩ := proper_divisor_sum_bound (H - (t + 1)) ((P ^ D_t) ^ H) B_h
      obtain ⟨B', hB'⟩ := bound_vh_general (m := m) C
      refine ⟨max D_t B', fun sys hpH i hi1 hilo hiH => ?_⟩
      by_cases hcase : H - t ≤ i
      · exact le_trans (hD_t sys hpH i hi1 hcase hiH) (le_max_left _ _)
      · have hije : i = H - (t + 1) := by omega
        subst hije
        set j := H - (t + 1) with hjdef
        have hj1 : 1 ≤ j := hj0
        have hjH : j ≤ H := by omega
        refine le_trans ?_ (le_max_right D_t B')
        by_cases hdj : 1 ≤ sys.dSet j (sys.ASet H)
        · have hAne : (sys.ASet H).Nonempty := by
            by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
            rw [show sys.dSet j (sys.ASet H)
                  = (sys.ASet H).sup (fun s => s.factorization (sys.pOrd j)) from rfl,
                he, Finset.sup_empty] at hdj
            simp at hdj
          obtain ⟨K, hKA, hKeq⟩ := sys.dSet_attained hAne
          have hpjmem : sys.pOrd j ∈ K.primeFactors := by
            rw [← Nat.support_factorization, Finsupp.mem_support_iff, ← hKeq]; omega
          have hpj2 : 2 ≤ sys.pOrd j := (Nat.prime_of_mem_primeFactors hpjmem).two_le
          have hKS := ((sys.mem_ASet_iff_le hH1 hpH).mp hKA).1
          set Q := sys.largePart j K with hQdef
          have hQpos : 0 < Q := by
            rw [hQdef]; unfold ValidCosetPartition.largePart; apply Finset.prod_pos
            intro q hq
            exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos _
          have hQle : Q ≤ (P ^ D_t) ^ H :=
            sys.largePart_le hj1 hpj2 hH1 hpH hKA P D_t hP1 (hP sys K hKS)
              (fun i hji hiH => hD_t sys hpH i (by omega) (by omega) hiH)
          have hsuppQ : IsSupportedOn Q (sys.n.primeFactors \ sys.smallPrimes j) := by
            intro q hq
            have hmem := sys.largePart_primeFactors_subset j K hq
            rw [Finset.mem_sdiff] at hmem ⊢
            exact ⟨Nat.primeFactors_mono (sys.sizes_dvd K hKS) sys.n_pos.ne' hmem.1, hmem.2⟩
          have hKL : K ∈ sys.LSet j Q := by
            rw [show sys.LSet j Q = sys.S.filter (fun s => sys.largePart j s = Q) from rfl,
                Finset.mem_filter]
            exact ⟨hKS, rfl⟩
          have hLne : (sys.LSet j Q).Nonempty := ⟨K, hKL⟩
          have hdL1 : 1 ≤ sys.dSet j (sys.LSet j Q) := by
            have hle : K.factorization (sys.pOrd j) ≤ sys.dSet j (sys.LSet j Q) :=
              Finset.le_sup (f := fun t => t.factorization (sys.pOrd j)) hKL
            rw [← hKeq] at hle; omega
          have htail : (∑ Q' ∈ Q.properDivisors, (sys.LSet j Q').sum id) ≤ C :=
            hC sys Q hQle (hBh sys j (by omega))
          obtain ⟨_, hdLB⟩ := hB' sys j hj1 Q hQpos hsuppQ hLne hdL1 htail
          calc sys.dSet j (sys.ASet H) = K.factorization (sys.pOrd j) := hKeq
            _ ≤ sys.dSet j (sys.LSet j Q) :=
                Finset.le_sup (f := fun t => t.factorization (sys.pOrd j)) hKL
            _ ≤ B' := hdLB
        · omega
    · refine ⟨D_t, fun sys hpH i hi1 hilo hiH => hD_t sys hpH i hi1 (by omega) hiH⟩

/-- **Piece 2e / Theorem 3.7.** The combined induction: for every level `H` there
    is a uniform bound `B` on both all the valuations `d_j(𝒜_H)` (`1 ≤ j ≤ H`) and
    the sum `∑_{𝒜_H}`.  Outer induction on `H`; the collapse cases (`p_H` out of
    range, or `d_H(𝒜_H) = 0`) reduce to the IH, while the real-work case uses the
    descending bound (2d) and the σ finish (Piece 3). -/
theorem ASet_combined_bound (hm : 2 ≤ m) : ∀ H, ∃ B, ∀ (sys : ValidCosetPartition m),
    (∀ j, 1 ≤ j → j ≤ H → sys.dSet j (sys.ASet H) ≤ B) ∧ (sys.ASet H).sum id ≤ B := by
  intro H
  induction H with
  | zero =>
    refine ⟨0, fun sys => ⟨fun j hj1 hj0 => by omega, ?_⟩⟩
    have hempty : sys.ASet 0 = ∅ := by
      rw [show sys.ASet 0 = sys.AP (sys.smallPrimes 0) from rfl,
          show sys.smallPrimes 0 = (sys.primeList.take 0).toFinset from rfl]
      rw [show sys.AP ((sys.primeList.take 0).toFinset)
            = sys.S.filter (fun s => IsSupportedOn s ((sys.primeList.take 0).toFinset)) from rfl]
      apply Finset.filter_false_of_mem
      intro s hs hsupp
      obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (sys.sizes_gt_one s hs)
      simp only [List.take_zero, List.toFinset_nil] at hsupp
      exact absurd (hsupp p hp) (Finset.notMem_empty p)
    rw [hempty, Finset.sum_empty]
  | succ h ih =>
    obtain ⟨B_h, hB_h⟩ := ih
    obtain ⟨P0, hP0⟩ := prime_bound m hm
    set P := max P0 1 with hPdef
    have hP1 : 1 ≤ P := le_max_right _ _
    have hP : ∀ (sys : ValidCosetPartition m), ∀ s ∈ sys.S, ∀ p, p.Prime → p ∣ s → p ≤ P :=
      fun sys s hs p hpp hpd => le_trans (hP0 sys s hs p hpp hpd) (le_max_left _ _)
    have hBh_sum : ∀ (sys : ValidCosetPartition m), ∀ j, j ≤ (h + 1) - 1 →
        (sys.ASet j).sum id ≤ B_h := by
      intro sys j hj
      exact le_trans (Finset.sum_le_sum_of_subset (sys.ASet_mono (by omega))) (hB_h sys).2
    obtain ⟨D, hD⟩ := dSet_ASet_bound (h + 1) (by omega) P hP1 hP B_h hBh_sum
    refine ⟨max (max B_h D) (((P ^ D) ^ (h + 1)) ^ 2), fun sys => ?_⟩
    by_cases hcol : 2 ≤ sys.pOrd (h + 1) ∧ 1 ≤ sys.dSet (h + 1) (sys.ASet (h + 1))
    · obtain ⟨hpH, hdH⟩ := hcol
      have hAne : (sys.ASet (h + 1)).Nonempty := by
        by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he
        rw [show sys.dSet (h + 1) (sys.ASet (h + 1))
              = (sys.ASet (h + 1)).sup (fun s => s.factorization (sys.pOrd (h + 1))) from rfl,
            he, Finset.sup_empty] at hdH
        simp at hdH
      obtain ⟨K, hKA, hKeq⟩ := sys.dSet_attained hAne
      have hppH_le : sys.pOrd (h + 1) ≤ P := by
        have hpmem : sys.pOrd (h + 1) ∈ K.primeFactors := by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff, ← hKeq]; omega
        exact hP sys K (((sys.mem_ASet_iff_le (by omega) hpH).mp hKA).1) (sys.pOrd (h + 1))
          (Nat.prime_of_mem_primeFactors hpmem) (Nat.dvd_of_mem_primeFactors hpmem)
      refine ⟨fun j hj1 hjH =>
        le_trans (hD sys hpH j hj1 hjH) (le_trans (le_max_right _ _) (le_max_left _ _)), ?_⟩
      have hMbound : (∏ q ∈ sys.smallPrimes (h + 1), q ^ D) ≤ (P ^ D) ^ (h + 1) := by
        calc ∏ q ∈ sys.smallPrimes (h + 1), q ^ D
            ≤ ∏ q ∈ sys.smallPrimes (h + 1), P ^ D :=
              Finset.prod_le_prod' (fun q hq => Nat.pow_le_pow_left
                (le_trans ((sys.mem_smallPrimes_iff (by omega) hpH).mp hq).2 hppH_le) D)
          _ = (P ^ D) ^ (sys.smallPrimes (h + 1)).card := by rw [Finset.prod_const]
          _ ≤ (P ^ D) ^ (h + 1) := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hP1) (by
                rw [show sys.smallPrimes (h + 1) = (sys.primeList.take (h + 1)).toFinset from rfl]
                exact le_trans (List.toFinset_card_le _) (List.length_take_le _ _))
      calc (sys.ASet (h + 1)).sum id
          ≤ σ 1 (∏ q ∈ sys.smallPrimes (h + 1), q ^ D) :=
            sys.sum_ASet_le_sigma (h + 1) (by omega) hpH D (fun j hj1 hjH => hD sys hpH j hj1 hjH)
        _ ≤ (∏ q ∈ sys.smallPrimes (h + 1), q ^ D) ^ 2 := by
            have := ArithmeticFunction.sigma_le_pow_succ 1 (∏ q ∈ sys.smallPrimes (h + 1), q ^ D)
            simpa using this
        _ ≤ ((P ^ D) ^ (h + 1)) ^ 2 := Nat.pow_le_pow_left hMbound 2
        _ ≤ max (max B_h D) (((P ^ D) ^ (h + 1)) ^ 2) := le_max_right _ _
    · obtain ⟨hd_h, hsum_h⟩ := hB_h sys
      have hdH0 : sys.dSet (h + 1) (sys.ASet (h + 1)) = 0 := by
        by_cases hp2 : 2 ≤ sys.pOrd (h + 1)
        · have hnd : ¬ 1 ≤ sys.dSet (h + 1) (sys.ASet (h + 1)) := fun hd => hcol ⟨hp2, hd⟩
          omega
        · rw [show sys.dSet (h + 1) (sys.ASet (h + 1))
                = (sys.ASet (h + 1)).sup (fun s => s.factorization (sys.pOrd (h + 1))) from rfl]
          apply le_antisymm _ (Nat.zero_le _)
          apply Finset.sup_le
          intro s _
          have hnp : sys.pOrd (h + 1) ∉ s.primeFactors := fun hmem =>
            absurd (Nat.prime_of_mem_primeFactors hmem).two_le (by omega)
          exact le_of_eq (Finsupp.notMem_support_iff.mp
            (by rw [Nat.support_factorization]; exact hnp))
      have hcollapse : sys.ASet (h + 1) = sys.ASet h := by
        by_cases hp2 : 2 ≤ sys.pOrd (h + 1)
        · apply Finset.Subset.antisymm _ (sys.ASet_subset_succ h)
          rw [sys.ASet_eq_LSet_one (h + 1), sys.ASet_eq_LSet_one h]
          exact sys.LSet_succ_subset_of_dSet_zero h 1
            (by rw [← sys.ASet_eq_LSet_one (h + 1)]; exact hdH0)
        · rw [show sys.ASet (h + 1) = sys.AP (sys.smallPrimes (h + 1)) from rfl,
              show sys.ASet h = sys.AP (sys.smallPrimes h) from rfl,
              sys.smallPrimes_eq_of_pOrd_lt h (by omega)]
      refine ⟨fun j hj1 hjH => ?_, ?_⟩
      · by_cases hjle : j ≤ h
        · rw [hcollapse]
          exact le_trans (hd_h j hj1 hjle) (le_trans (le_max_left _ _) (le_max_left _ _))
        · have hje : j = h + 1 := by omega
          subst hje; rw [hdH0]; exact Nat.zero_le _
      · rw [hcollapse]
        exact le_trans hsum_h (le_trans (le_max_left _ _) (le_max_left _ _))

/-- **Piece 4 / Corollary 3.8.** Finiteness: `n` is uniformly bounded.  Taking
    `H = P_max` (the uniform prime bound) in Theorem 3.7, every size's primes are
    `≤ P_max` hence among the first `P_max` primes, so `𝒜_{P_max} = S`; then
    `n = ∑_S + m ≤ B + m`. -/
theorem finiteness_main (m : ℕ) (hm : 2 ≤ m) :
    ∃ N, ∀ (sys : ValidCosetPartition m), sys.n ≤ N := by
  obtain ⟨P_max, hP⟩ := prime_bound m hm
  obtain ⟨B, hB⟩ := ASet_combined_bound (m := m) hm P_max
  refine ⟨B + m, fun sys => ?_⟩
  have hAS : sys.ASet P_max = sys.S := by
    rw [show sys.ASet P_max
          = sys.S.filter (fun s => IsSupportedOn s (sys.smallPrimes P_max)) from rfl]
    apply Finset.filter_true_of_mem
    intro s hsS p hp
    exact sys.mem_smallPrimes_of_le
      (Nat.primeFactors_mono (sys.sizes_dvd s hsS) sys.n_pos.ne' hp)
      (hP sys s hsS p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have hsum : (sys.S).sum id ≤ B := hAS ▸ (hB sys).2
  rw [← sys.sum_eq]; omega

/-
**Lemma (Valuation bound)**: For any valid system, every p-adic valuation
    of any size in S is bounded by a constant depending only on m.

    Proof: Since p is bounded (by prime_bound), and the divisor-sum inequality
    bounds p^e when N − σ(N/p) ≤ C₀, we get e bounded.
-/
theorem valuation_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ V_max : ℕ, ∀ (sys : ValidCosetPartition m),
      ∀ s ∈ sys.S, ∀ p : ℕ, p.Prime → p ∣ s → s.factorization p ≤ V_max := by
  -- By size_bound, there exists S_max such that for any valid system sys, any size s in sys.S, s ≤ S_max.
  obtain ⟨S_max, hS_max⟩ : ∃ S_max, ∀ (sys : ValidCosetPartition m), ∀ s ∈ sys.S, s ≤ S_max := by
    obtain ⟨ N, hN ⟩ := finiteness_main m hm;
    exact ⟨ N, fun sys s hs => le_trans ( Nat.le_of_dvd ( by linarith [ sys.n_pos ] ) ( sys.sizes_dvd s hs ) ) ( hN sys ) ⟩;
  exact ⟨ S_max, fun sys s hs p hp hps => le_trans ( Nat.le_of_lt ( Nat.factorization_lt _ ( by linarith [ DCS.ValidCosetPartition.sizes_gt_one sys s hs ] ) ) ) ( hS_max sys s hs ) ⟩

/-
**Lemma (Size bound)**: All sizes are bounded by a constant depending only on m.

    Proof: Every size s divides ∏_{p | s} p^{ν_p(s)} ≤ ∏_{p ≤ P_max} p^{V_max},
    which is bounded.
-/
theorem size_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ S_max : ℕ, ∀ (sys : ValidCosetPartition m), ∀ s ∈ sys.S, s ≤ S_max := by
  -- From prime_bound and valuation_bound, every size has bounded factorization
  obtain ⟨P_max, hP⟩ := prime_bound m hm
  obtain ⟨V_max, hV⟩ := valuation_bound m hm
  -- Every size divides M := ∏_{p ≤ P_max, p prime} p^V_max
  -- M is bounded (it depends only on P_max and V_max, hence on m)
  -- So every size ≤ M
  -- By combining the bounds on primes and valuations, we can bound the product.
  have h_prod_bound : ∃ B : ℕ, ∀ (sys : ValidCosetPartition m), ∀ s ∈ sys.S, s ≤ B := by
    have h_prod_bound_step : ∀ (sys : ValidCosetPartition m), ∀ s ∈ sys.S, s ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 P_max), p ^ V_max) := by
      intros sys s hs
      have h_prod : s ∣ ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 P_max), p ^ (s.factorization p) := by
        conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( show s ≠ 0 by linarith [ sys.sizes_gt_one s hs ] ) ] ;
        apply Finset.prod_dvd_prod_of_subset;
        exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.Prime.two_le ( Nat.prime_of_mem_primeFactors hp ), hP sys s hs p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ⟩, Nat.prime_of_mem_primeFactors hp ⟩;
      refine Nat.le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ) h_prod ) ?_;
      exact Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_right ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ( if h : p ∣ s then hV sys s hs p ( Finset.mem_filter.mp hp |>.2 ) h else by rw [ Nat.factorization_eq_zero_of_not_dvd h ] ; norm_num )
    exact ⟨ _, h_prod_bound_step ⟩;
  exact h_prod_bound

/-
**Corollary (Cardinality bound)**: |S| is bounded by a constant depending
    only on m. Since each size > 1 is distinct and divides some bounded M,
    |S| ≤ number of divisors of M.
-/
theorem card_S_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C_max : ℕ, ∀ (sys : ValidCosetPartition m), sys.S.card ≤ C_max := by
  obtain ⟨S_max, hS⟩ := size_bound m hm
  use S_max;
  intro sys;
  exact le_trans ( Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ Nat.succ_le_of_lt ( sys.sizes_gt_one x hx ), hS sys x hx ⟩ ) ( by simp )

/-- **Theorem 3.7**: ∑_{𝒜_P} is bounded for all P. -/
theorem sumAP_bounded_main (m : ℕ) (hm : 2 ≤ m) :
    ∃ B : ℕ, ∀ (sys : ValidCosetPartition m) (P : Finset ℕ), sys.sumAP P ≤ B := by
  -- Since every size is bounded by S_max, and the number of sizes is bounded
  -- by C_max, we get ∑ sizes ≤ S_max * C_max, hence sumAP ≤ S_max * C_max + m.
  obtain ⟨S_max, hS⟩ := size_bound m hm
  obtain ⟨C_max, hC⟩ := card_S_bound m hm
  use S_max * C_max + m
  intro sys P
  unfold ValidCosetPartition.sumAP ValidCosetPartition.AP
  have h1 : (sys.S.filter (IsSupportedOn · P)).sum id ≤ sys.S.sum id := by
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h2 : sys.S.sum id ≤ S_max * sys.S.card := by
    calc sys.S.sum id
        ≤ sys.S.sum (fun _ => S_max) := Finset.sum_le_sum (fun s hs => hS sys s hs)
      _ = S_max * sys.S.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
  have h3 : sys.S.card ≤ C_max := hC sys
  calc (sys.S.filter (IsSupportedOn · P)).sum id + m
      ≤ sys.S.sum id + m := by omega
    _ ≤ S_max * sys.S.card + m := by omega
    _ ≤ S_max * C_max + m := by nlinarith

/-! ### Main finiteness theorem -/

/-- **Corollary 3.8 / Theorem 1.2**: n is bounded by a constant depending only on m. -/
theorem main_finiteness (m : ℕ) (hm : 2 ≤ m) :
    ∃ N : ℕ, ∀ (sys : ValidCosetPartition m), sys.n ≤ N := by
  obtain ⟨B, hB⟩ := sumAP_bounded_main m hm
  exact ⟨B, fun sys => sys.sumAP_all ▸ hB sys sys.n.primeFactors⟩

end DCS
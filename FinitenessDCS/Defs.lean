import Mathlib
import FinitenessDCS.Parallelotope

/-!
# Finiteness of Disjoint Covering Systems with One Repeated Modulus

## Definitions

We work directly with coset partitions of `ℤ/nℤ` (`DCS.CosetPartition`, from
`FinitenessDCS.Parallelotope`).  A `DCS.ValidCosetPartition m` bundles such a
partition together with the structural hypotheses of the problem:

* `2 ≤ m` and exactly `m` singleton cosets (one repeated modulus);
* every coset size is `≤ n/3` (minimum modulus `≥ 3`);
* the non-singleton coset sizes are pairwise distinct.

From these we recover the "system" interface (`S`, `sum_eq`, `cell_ineq`,
`cell_ineq_two`, …) used in the main argument, with the cell inequalities now
**derived** from the proven coset inequalities `DCS.cell_inequality`
(`cor:coset-bff`) and `DCS.cell_inequality_two_level` (`cor:coset-twolevel`).
-/

namespace DCS

open Finset Nat
open scoped ArithmeticFunction.sigma

variable {n : ℕ}

/-- A positive integer is supported on a set of primes `P` if all its prime factors lie in `P`.
    By convention, 1 is supported on any set. -/
def IsSupportedOn (s : ℕ) (P : Finset ℕ) : Prop :=
  ∀ p ∈ s.primeFactors, p ∈ P

instance (P : Finset ℕ) : DecidablePred (IsSupportedOn · P) := by
  intro s; unfold IsSupportedOn; exact Finset.decidableDforallFinset

/-! ### The size-multiset bridge

The multiset of coset sizes splits as `m` singletons (`size 1`) together with the
distinct non-singleton sizes (each once).  This is the bookkeeping link between
sums over `P.cosets` (used by the coset cell inequalities) and sums over the
finset of distinct sizes `S`. -/

/-- `P.cosets.map size = (m singletons) + (distinct non-singleton sizes)`. -/
lemma bridge (P : CosetPartition n) (hn : 0 < n)
    (hdist : ∀ K₁ K₂, K₁ ∈ P.cosets → K₂ ∈ P.cosets →
      K₁.size = K₂.size → 1 < K₁.size → K₁ = K₂) :
    (P.cosets.map Coset.size : Multiset ℕ)
      = Multiset.replicate P.singletonCount 1 + P.distinctSizes.val := by
  classical
  have hcount : ∀ (l : List (Coset n)) (y : ℕ),
      (l.map Coset.size).count y = (l.filter (fun K => K.size = y)).length := by
    intro l y
    induction l with
    | nil => simp
    | cons hd tl ih =>
      by_cases h : hd.size = y <;> simp [h, ih]
  ext x
  rw [Multiset.count_add, Multiset.count_replicate, Multiset.coe_count]
  have hSval : Multiset.count x P.distinctSizes.val = if x ∈ P.distinctSizes then 1 else 0 := by
    by_cases hx : x ∈ P.distinctSizes
    · rw [if_pos hx]; exact Multiset.count_eq_one_of_mem P.distinctSizes.nodup hx
    · rw [if_neg hx]; exact Multiset.count_eq_zero.mpr hx
  rw [hSval]
  by_cases hx1 : x = 1
  · subst hx1
    have h1 : (1 : ℕ) ∉ P.distinctSizes := by simp [CosetPartition.distinctSizes]
    rw [hcount, if_pos rfl, if_neg h1, Nat.add_zero]
    rfl
  · rw [if_neg (Ne.symm hx1), Nat.zero_add]
    by_cases hxgt : 1 < x
    · by_cases hxd : x ∈ P.distinctSizes
      · rw [if_pos hxd]
        have hmem : x ∈ P.cosets.map Coset.size := by
          simp only [CosetPartition.distinctSizes, Finset.mem_filter, List.mem_toFinset] at hxd
          exact hxd.1
        have hge1 : 1 ≤ (P.cosets.map Coset.size).count x := List.count_pos_iff.mpr hmem
        have hle1 : (P.cosets.map Coset.size).count x ≤ 1 := by
          rw [hcount]
          have hnodupf : (P.cosets.filter (fun K => K.size = x)).Nodup :=
            P.cosets_nodup.filter _
          rcases hf : P.cosets.filter (fun K => K.size = x) with _ | ⟨a, _ | ⟨b, t⟩⟩
          · rw [hf]; exact Nat.zero_le 1
          · rw [hf]; exact Nat.le_refl 1
          · exfalso
            have ha : a ∈ P.cosets.filter (fun K => K.size = x) := by rw [hf]; simp
            have hb : b ∈ P.cosets.filter (fun K => K.size = x) := by rw [hf]; simp
            rw [List.mem_filter] at ha hb
            have hax : a.size = x := by simpa using ha.2
            have hbx : b.size = x := by simpa using hb.2
            have hab : a = b := hdist a b ha.1 hb.1 (by rw [hax, hbx]) (by rw [hax]; exact hxgt)
            rw [hf, List.nodup_cons] at hnodupf
            exact hnodupf.1 (by rw [hab]; simp)
        omega
      · rw [if_neg hxd, List.count_eq_zero]
        intro hmem
        apply hxd
        rw [List.mem_map] at hmem
        obtain ⟨K, hK, hKx⟩ := hmem
        simp only [CosetPartition.distinctSizes, Finset.mem_filter, List.mem_toFinset]
        exact ⟨List.mem_map.mpr ⟨K, hK, hKx⟩, hxgt⟩
    · have hx0 : x = 0 := by omega
      subst hx0
      have h0 : (0 : ℕ) ∉ P.distinctSizes := by simp [CosetPartition.distinctSizes]
      rw [if_neg h0, List.count_eq_zero]
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨K, hK, hKsize⟩ := hmem
      have := K.size_pos hn
      omega

/-- Sum of sizes of cosets dividing `X` equals the filtered sum over distinct
    sizes, plus the `m` singletons (which all divide `X`). -/
lemma key_sum (P : CosetPartition n) (hn : 0 < n) (m : ℕ)
    (hsc : P.singletonCount = m)
    (hdist : ∀ K₁ K₂, K₁ ∈ P.cosets → K₂ ∈ P.cosets →
      K₁.size = K₂.size → 1 < K₁.size → K₁ = K₂) (X : ℕ) :
    ((P.cosets.filter (fun K => K.size ∣ X)).map Coset.size).sum
      = (P.distinctSizes.filter (· ∣ X)).sum id + m := by
  classical
  have hbr := bridge P hn hdist
  rw [hsc] at hbr
  have hswap : ∀ (l : List (Coset n)),
      (l.filter (fun K => K.size ∣ X)).map Coset.size = (l.map Coset.size).filter (· ∣ X) := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih => by_cases h : hd.size ∣ X <;> simp [List.map_cons, h, ih]
  rw [hswap]
  have hcore : ((P.cosets.map Coset.size : Multiset ℕ).filter (· ∣ X)).sum
      = (P.distinctSizes.filter (· ∣ X)).sum id + m := by
    rw [hbr, Multiset.filter_add, Multiset.sum_add]
    have hrep : (Multiset.replicate m 1).filter (· ∣ X) = Multiset.replicate m 1 := by
      apply Multiset.filter_eq_self.mpr
      intro a ha
      rw [Multiset.eq_of_mem_replicate ha]; exact one_dvd X
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, Nat.mul_one, add_comm]
    congr 1
    rw [← Finset.filter_val]
    simp [Finset.sum]
  rw [← hcore]
  rfl

/-! ### The valid coset partition structure -/

/-- A valid coset partition system with parameter `m`. -/
structure ValidCosetPartition (m : ℕ) where
  /-- The order of the cyclic group ℤ/nℤ -/
  n : ℕ
  /-- The coset partition of ℤ/nℤ -/
  P : CosetPartition n
  /-- n > 0 -/
  hn : 0 < n
  /-- m ≥ 2 (the largest modulus is repeated at least twice) -/
  hm : 2 ≤ m
  /-- exactly `m` singleton cosets (one repeated modulus) -/
  hsingleton : P.singletonCount = m
  /-- every coset size is ≤ n/3 (minimum modulus ≥ 3) -/
  hsizes_le : ∀ K ∈ P.cosets, 3 * K.size ≤ n
  /-- non-singleton coset sizes are distinct -/
  hdistinct : ∀ K₁ K₂, K₁ ∈ P.cosets → K₂ ∈ P.cosets →
    K₁.size = K₂.size → 1 < K₁.size → K₁ = K₂

namespace ValidCosetPartition

variable {m : ℕ} (V : ValidCosetPartition m)

/-- The set of distinct coset sizes greater than 1. -/
def S : Finset ℕ := V.P.distinctSizes

/-- n > 0 for any valid system -/
lemma n_pos : 0 < V.n := V.hn

/-- Every size in `S` is the size of some coset of the partition. -/
lemma exists_coset_of_mem {s : ℕ} (hs : s ∈ V.S) : ∃ K ∈ V.P.cosets, K.size = s := by
  have hs' : s ∈ V.P.distinctSizes := hs
  simp only [CosetPartition.distinctSizes, Finset.mem_filter, List.mem_toFinset,
             List.mem_map] at hs'
  obtain ⟨⟨K, hK, hKs⟩, _⟩ := hs'
  exact ⟨K, hK, hKs⟩

/-- All sizes in `S` are > 1 -/
lemma sizes_gt_one : ∀ s ∈ V.S, 1 < s := by
  intro s hs
  have hs' : s ∈ V.P.distinctSizes := hs
  simp only [CosetPartition.distinctSizes, Finset.mem_filter] at hs'
  exact hs'.2

/-- Every size divides n -/
lemma sizes_dvd : ∀ s ∈ V.S, s ∣ V.n := by
  intro s hs
  obtain ⟨K, _, hKs⟩ := V.exists_coset_of_mem hs
  rw [← hKs]; exact K.size_dvd

/-- Every size is at most n/3 (minimum modulus ≥ 3) -/
lemma sizes_le : ∀ s ∈ V.S, 3 * s ≤ V.n := by
  intro s hs
  obtain ⟨K, hK, hKs⟩ := V.exists_coset_of_mem hs
  rw [← hKs]; exact V.hsizes_le K hK

/-- Sizes in S are positive -/
lemma sizes_pos (s : ℕ) (hs : s ∈ V.S) : 0 < s :=
  Nat.lt_trans Nat.zero_lt_one (V.sizes_gt_one s hs)

/-- n/s ≥ 3 for any size s in S -/
lemma ndivs_ge_three (s : ℕ) (hs : s ∈ V.S) : 3 ≤ V.n / s := by
  have hpos := V.sizes_pos s hs
  exact Nat.le_div_iff_mul_le hpos |>.mpr (V.sizes_le s hs)

/-- minFac(n/s) ≥ 2 for any size s in S -/
lemma minFac_ge_two (s : ℕ) (hs : s ∈ V.S) : 2 ≤ (V.n / s).minFac := by
  have h3 := V.ndivs_ge_three s hs
  exact (Nat.minFac_prime (by omega)).two_le

/-- The sizes sum to n: (∑ sizes > 1) + m = n -/
lemma sum_eq : V.S.sum id + m = V.n := by
  have h := key_sum V.P V.hn m V.hsingleton V.hdistinct V.n
  rw [show V.P.cosets.filter (fun K => K.size ∣ V.n) = V.P.cosets from
        List.filter_eq_self.mpr (fun K _ => by simp only [decide_eq_true_eq]; exact K.size_dvd),
      V.P.partition] at h
  rw [show V.P.distinctSizes.filter (· ∣ V.n) = V.S from ?_] at h
  · omega
  · ext s
    simp only [S, Finset.mem_filter, and_iff_left_iff_imp]
    intro hs; exact V.sizes_dvd s hs

/-- Cell inequality (`cor:coset-bff`):
    the total mass of sizes dividing `s` (plus `m` singletons) is at least
    `minFac(n/s) · s`. -/
lemma cell_ineq : ∀ s ∈ V.S,
    (V.S.filter (· ∣ s)).sum id + m ≥ (V.n / s).minFac * s := by
  intro s hs
  obtain ⟨K, hK, hKs⟩ := V.exists_coset_of_mem hs
  have hci := DCS.cell_inequality V.hn V.P K hK
  rw [hKs, key_sum V.P V.hn m V.hsingleton V.hdistinct s] at hci
  exact hci

/-- Two-level cell inequality (`cor:coset-twolevel`). -/
lemma cell_ineq_two : ∀ s ∈ V.S,
    let q := V.n / s
    let p₁ := q.minFac
    let e₁ := q.factorization p₁
    1 < q / p₁ ^ e₁ →
    (V.S.filter (· ∣ s * p₁ ^ e₁)).sum id + m ≥ (q / p₁ ^ e₁).minFac * s := by
  intro s hs q p₁ e₁ htwo
  obtain ⟨K, hK, hKs⟩ := V.exists_coset_of_mem hs
  have hct := DCS.cell_inequality_two_level V.hn V.P K hK
  rw [hKs] at hct
  have hres := hct htwo
  rw [key_sum V.P V.hn m V.hsingleton V.hdistinct (s * p₁ ^ e₁)] at hres
  exact hres

/-! ### Derived operations on the system -/

/-- 𝒜_P : the set of sizes in S supported on primes P -/
def AP (P : Finset ℕ) : Finset ℕ := V.S.filter (IsSupportedOn · P)

/-- Sum of sizes in 𝒜_P plus m (the singleton contribution) -/
def sumAP (P : Finset ℕ) : ℕ := (V.AP P).sum id + m

/-- 𝒟(s) : sizes in S that properly divide s -/
def DS (s : ℕ) : Finset ℕ := V.S.filter (fun s' => s' ∣ s ∧ s' ≠ s)

/-- Sum over 𝒟(s) plus m singletons -/
def sumDS (s : ℕ) : ℕ := (V.DS s).sum id + m

/-! ### Notation for the proof (Definition `def:symbols`)

The paper fixes the prime factorization `n = ∏ pⱼ^{sⱼ}` with `p₁ < ⋯ < p_ℓ`
and introduces a family of symbols indexed by a *level* `1 ≤ h ≤ ℓ`.  Because
every quantity used (`|K|`, `ν_{p_h}(|K|)`) depends on a coset `K` only through
its size `|K|`, we record all of these at the level of **sizes** (`V.S`), in line
with the existing `AP`/`sumAP` and `DS`/`sumDS`.  The singleton cosets (size `1`)
are handled, as before, by the `+ m` appearing in the *sum* versions. -/

/-- The prime divisors of `n`, listed in increasing order: `[p₁, …, p_ℓ]`. -/
def primeList : List ℕ := V.n.primeFactors.sort (· ≤ ·)

/-- `ℓ`: the number of distinct primes dividing `n`. -/
def ell : ℕ := V.primeList.length

/-- `pₕ`: the `h`-th smallest prime divisor of `n` (1-indexed, matching the
    paper).  For `h` out of range it returns the harmless sentinel `1`. -/
def pOrd (h : ℕ) : ℕ := V.primeList.getD (h - 1) 1

/-- `{p₁, …, p_h}`: the set of the `h` smallest prime divisors of `n`. -/
def smallPrimes (h : ℕ) : Finset ℕ := (V.primeList.take h).toFinset

/-- **(i)** `d_h(T) := max{ ν_{p_h}(s) : s ∈ T }`, the largest `p_h`-adic
    valuation occurring among a family of sizes `T`.  `Finset.sup` sends the
    empty family to `0`. -/
def dSet (h : ℕ) (T : Finset ℕ) : ℕ := T.sup (fun s => s.factorization (V.pOrd h))

/-- **(iii)** `π_h(s) := ∏_{j>h} pⱼ^{ν_{pⱼ}(s)}`, the "large part" of `s`: the
    divisor of `s` supported on the primes strictly above `p_h`. -/
def largePart (h : ℕ) (s : ℕ) : ℕ :=
  ∏ q ∈ s.primeFactors \ V.smallPrimes h, q ^ s.factorization q

/-- **(iv)** `𝒜_h := { s ∈ S : s supported on {p₁,…,p_h} }`.  (Definition (ii),
    `𝒟(K)`, is already recorded above as `DS`.) -/
def ASet (h : ℕ) : Finset ℕ := V.AP (V.smallPrimes h)

/-- **(v)** `ℒ_h(Q) := { s ∈ S : π_h(s) = Q }`. -/
def LSet (h : ℕ) (Q : ℕ) : Finset ℕ := V.S.filter (fun s => V.largePart h s = Q)

/-- **(vi)** `s` is *division minimal* in a family `T` if the only member of `T`
    dividing `s` is `s` itself. -/
def DivisionMinimal (T : Finset ℕ) (s : ℕ) : Prop :=
  s ∈ T ∧ ∀ s' ∈ T, s' ∣ s → s' = s

/-- The paper's remark "In particular, `𝒜_h = ℒ_h(1)`": a size is supported on
    the small primes `{p₁,…,p_h}` iff its large part `π_h` is trivial. -/
lemma ASet_eq_LSet_one (h : ℕ) : V.ASet h = V.LSet h 1 := by
  unfold ASet AP LSet
  ext s
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hs
  constructor
  · -- supported on the small primes ⟹ the large part is the empty product `1`
    intro hsupp
    have hsub : s.primeFactors ⊆ V.smallPrimes h := fun p hp => hsupp p hp
    unfold largePart
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.prod_empty]
  · -- large part `1` ⟹ no prime factor lies above the small primes
    intro hone p hp
    by_contra hpn
    have hmem : p ∈ s.primeFactors \ V.smallPrimes h := Finset.mem_sdiff.mpr ⟨hp, hpn⟩
    have hdvd : p ^ s.factorization p ∣ V.largePart h s := Finset.dvd_prod_of_mem _ hmem
    rw [hone] at hdvd
    have h1 : p ^ s.factorization p = 1 := Nat.dvd_one.mp hdvd
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpos : 1 ≤ s.factorization p :=
      hpp.factorization_pos_of_dvd (by have := V.sizes_pos s hs; omega)
        (Nat.dvd_of_mem_primeFactors hp)
    have : 2 ≤ p ^ s.factorization p := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ p ^ s.factorization p := Nat.pow_le_pow_left hpp.two_le 1 |>.trans
              (Nat.pow_le_pow_right hpp.pos hpos)
    omega

end ValidCosetPartition

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
  · simp [id]
  · simp only [mem_filter]
    intro ⟨_, _, hne⟩
    exact hne rfl

namespace ValidCosetPartition

variable {m : ℕ} (V : ValidCosetPartition m)

/-- Cell inequality in "excluding" form:
    sumDS s ≥ (minFac(n/s) - 1) * s -/
lemma cell_ineq_excluding (s : ℕ) (hs : s ∈ V.S) :
    V.sumDS s ≥ ((V.n / s).minFac - 1) * s := by
  have hci := V.cell_ineq s hs
  have hsplit := filter_dvd_split V.S s hs
  unfold sumDS DS
  rw [Nat.sub_one_mul] at *
  omega

/-- sumDS s ≥ s (since minFac(n/s) ≥ 2) -/
lemma sumDS_ge (s : ℕ) (hs : s ∈ V.S) : V.sumDS s ≥ s := by
  have h1 := V.cell_ineq_excluding s hs
  have h2 := V.minFac_ge_two s hs
  rw [Nat.sub_one_mul] at h1
  have : (V.n / s).minFac * s - s ≥ s := by
    have := Nat.mul_le_mul_right s h2; omega
  omega

/-! ### The sum over all sizes equals n -/

/-- The sum over all sizes equals n -/
lemma sumAP_all : V.sumAP V.n.primeFactors = V.n := by
  unfold sumAP AP
  rw [show V.S.filter (IsSupportedOn · V.n.primeFactors) = V.S from ?_]
  · exact V.sum_eq
  · ext s
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hs p hp
    exact Nat.primeFactors_mono (V.sizes_dvd s hs) V.n_pos.ne' hp

end ValidCosetPartition

/-! ### Main Theorem Statement

The main results — `ASet_combined_bound` (Theorem 3.7) and `finiteness_main`
(Corollary 3.8) — are proved sorry-free in `MainTheorem.lean`, where the full
proof machinery lives. -/

end DCS

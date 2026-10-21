import Mathlib

/-!
# Disjoint covering systems and the divisibility condition on their moduli

This file sets up disjoint covering systems (DCS) of `ℤ` and proves the
**divisibility condition** for the moduli of a DCS with precisely one repeated
modulus (`modulus_dvd_max`, the note *A Divisibility Condition for Moduli in
Disjoint Covering Systems with Precisely One Repeated Modulus*,
Proposition `prop:weak-completion-divisibility`):

> If `(aᵢ + nᵢℤ)ᵢ` is a DCS whose moduli satisfy
> `n₁ < ⋯ < n_{t-m} < n_{t-m+1} = ⋯ = n_t`, then `nᵢ ∣ n_t` for all `i`.

The proof is the standard generating-function/roots-of-unity argument.  Fix a
common multiple `N` of all the moduli and let `ζ` be a primitive `n_r`-th root of
unity.  Since every `x ∈ [0, N)` is covered exactly once,

`0 = ∑_{x<N} ζ^x = ∑_k ∑_{x<N, x ≡ aₖ (nₖ)} ζ^x = ∑_{k : n_r ∣ nₖ} (N/nₖ)·ζ^{aₖ}`

because the inner geometric sum vanishes unless `ζ^{nₖ} = 1`, i.e. unless
`n_r ∣ nₖ`.  Choosing `n_r` largest among the moduli *not* dividing the top
modulus `M` makes `k = r` the only surviving term, so `(N/n_r) ζ^{a_r} = 0` —
absurd.
-/

namespace DCS

open Finset

/-- An arithmetic progression `{x : ℤ | x ≡ residue [ZMOD modulus]}`, stored by its
    `modulus` and the canonical representative `residue` (intended to satisfy
    `residue < modulus`; see `ArithProg.Valid`).  Two progressions are equal as
    structures iff they are equal as subsets of `ℤ`. -/
structure ArithProg where
  /-- The common difference of the progression. -/
  modulus : ℕ
  /-- The canonical residue (representative in `[0, modulus)`). -/
  residue : ℕ
  deriving DecidableEq

/-- A progression is *valid* when its modulus is positive and its stored residue is
    the canonical representative in `[0, modulus)`. -/
def ArithProg.Valid (ap : ArithProg) : Prop := 0 < ap.modulus ∧ ap.residue < ap.modulus

/-- Membership of an integer `x` in the progression: `x ≡ residue (mod modulus)`. -/
def ArithProg.Mem (ap : ArithProg) (x : ℤ) : Prop := (ap.modulus : ℤ) ∣ (x - ap.residue)

/-- The progression as a subset of `ℤ`, i.e. `residue + modulus·ℤ`. -/
def ArithProg.toSet (ap : ArithProg) : Set ℤ := {x | ap.Mem x}

/-- A **disjoint covering system** of `ℤ`: a finite family of (valid) arithmetic
    progressions such that every integer lies in exactly one of them. -/
structure DCSystem where
  /-- The progressions of the system. -/
  progs : Finset ArithProg
  /-- Each progression is valid (positive modulus, canonical residue). -/
  valid : ∀ ap ∈ progs, ap.Valid
  /-- Every integer lies in *exactly one* progression of the system. -/
  covers : ∀ x : ℤ, ∃! ap, ap ∈ progs ∧ ap.Mem x

/-- The normalization `(eq:basicas)` for a DCS with multiplicity `m`:

* `2 ≤ m`;
* every modulus is `≥ 3` (minimum modulus at least `3`);
* there is a top modulus `M` that bounds all the others and is attained by exactly
  `m` progressions (the largest modulus, repeated `m` times); and
* the progressions with modulus `< M` have pairwise distinct moduli
  (`n₁ < n₂ < ⋯ < n_{t-m}`). -/
def DCSystem.Basicas (D : DCSystem) (m : ℕ) : Prop :=
  2 ≤ m ∧
  (∀ ap ∈ D.progs, 3 ≤ ap.modulus) ∧
  ∃ M, (∀ ap ∈ D.progs, ap.modulus ≤ M) ∧
       (D.progs.filter (fun ap => ap.modulus = M)).card = m ∧
       (∀ ap₁ ∈ D.progs, ∀ ap₂ ∈ D.progs,
          ap₁.modulus < M → ap₁.modulus = ap₂.modulus → ap₁ = ap₂)

/-! ### Ingredients of the roots-of-unity argument -/

/-- A full geometric sum `∑_{j<L} w^j` vanishes as soon as `w^L = 1` and `w ≠ 1`. -/
lemma geom_sum_eq_zero_of_pow_eq_one {w : ℂ} {L : ℕ} (hw : w ^ L = 1) (hw1 : w ≠ 1) :
    ∑ j ∈ range L, w ^ j = 0 := by
  have h := geom_sum_mul w L
  rw [hw, sub_self] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hw1

/-- For a *valid* progression, membership of a natural number is just a congruence
    of remainders: `x ∈ ap ↔ x % modulus = residue`. -/
lemma ArithProg.mem_natCast_iff {ap : ArithProg} (h : ap.Valid) {x : ℕ} :
    ap.Mem (x : ℤ) ↔ x % ap.modulus = ap.residue := by
  have hmod : ap.Mem (x : ℤ) ↔ ap.residue ≡ x [MOD ap.modulus] := by
    rw [Nat.modEq_iff_dvd]; exact Iff.rfl
  rw [hmod]
  change ap.residue % ap.modulus = x % ap.modulus ↔ _
  rw [Nat.mod_eq_of_lt h.2]
  exact eq_comm

/-- The elements of `[0, N)` in a fixed residue class `r` mod `m` are exactly the
    `N/m` numbers `r + j·m` with `j < N/m` (using `m ∣ N` and `r < m`). -/
lemma range_filter_mod_eq_image {m r N : ℕ} (hm : 0 < m) (hr : r < m) (hdvd : m ∣ N) :
    (range N).filter (fun x => x % m = r) = (range (N / m)).image (fun j => r + j * m) := by
  obtain ⟨c, hc⟩ := hdvd
  have hcm : N = c * m := by rw [hc, Nat.mul_comm]
  have hNc : N / m = c := by rw [hc]; exact Nat.mul_div_cancel_left c hm
  rw [hNc]
  ext x
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hxN, hxr⟩
    refine ⟨x / m, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hm, ← hcm]; exact hxN
    · have hd := Nat.div_add_mod' x m
      rw [hxr] at hd
      rw [Nat.add_comm]; exact hd
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, ?_⟩
    · calc r + j * m < m + j * m := by omega
        _ = (j + 1) * m := by ring
        _ ≤ c * m := Nat.mul_le_mul_right m (by omega)
        _ = N := hcm.symm
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The contribution of a single progression to `∑_{x<N} ζ^x`: the geometric sum
    `ζ^{a} · ∑_{j < N/m} (ζ^m)^j`. -/
lemma sum_pow_over_class (ζ : ℂ) {m r N : ℕ} (hm : 0 < m) (hr : r < m) (hdvd : m ∣ N) :
    ∑ x ∈ (range N).filter (fun x => x % m = r), ζ ^ x
      = ζ ^ r * ∑ j ∈ range (N / m), (ζ ^ m) ^ j := by
  rw [range_filter_mod_eq_image hm hr hdvd]
  rw [Finset.sum_image
    (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hm (Nat.add_left_cancel hab))]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_add, pow_mul']

/-- **Disjointness bookkeeping.**  Since every integer lies in exactly one
    progression, a sum over `[0, N)` splits as the sum of the sums over the
    individual progressions. -/
lemma DCSystem.sum_range_eq_sum_progs (D : DCSystem) (N : ℕ) (f : ℕ → ℂ) :
    ∑ x ∈ range N, f x
      = ∑ ap ∈ D.progs,
          ∑ x ∈ (range N).filter (fun y => y % ap.modulus = ap.residue), f x := by
  classical
  set g : ℕ → ArithProg := fun x => (D.covers (x : ℤ)).choose with hg
  have hmem : ∀ x : ℕ, g x ∈ D.progs ∧ (g x).Mem (x : ℤ) :=
    fun x => (D.covers (x : ℤ)).choose_spec.1
  have huniq : ∀ (x : ℕ) (ap : ArithProg), ap ∈ D.progs → ap.Mem (x : ℤ) → ap = g x :=
    fun x ap h1 h2 => (D.covers (x : ℤ)).choose_spec.2 ap ⟨h1, h2⟩
  rw [← Finset.sum_fiberwise_of_maps_to (fun x _ => (hmem x).1) f]
  refine Finset.sum_congr rfl fun ap hap => ?_
  have hfeq : (range N).filter (fun x => g x = ap)
      = (range N).filter (fun y => y % ap.modulus = ap.residue) := by
    refine Finset.filter_congr fun x _ => ?_
    constructor
    · intro hgx
      exact (ArithProg.mem_natCast_iff (x := x) (D.valid ap hap)).mp (hgx ▸ (hmem x).2)
    · intro hx
      exact (huniq x ap hap ((ArithProg.mem_natCast_iff (x := x) (D.valid ap hap)).mpr hx)).symm
  rw [hfeq]

/-! ### The divisibility condition -/

/-- **Divisibility condition for the moduli of a DCS with one repeated modulus**
    (`prop:weak-completion-divisibility`).

    Let `D` be a disjoint covering system whose largest modulus is `M`, and suppose
    the moduli below `M` are pairwise distinct (each is attained by a single
    progression).  Then *every* modulus divides `M`.

    This is the fact `nᵢ ∣ n_t` (`1 ≤ i ≤ t`) of Berger–Felzenbaum–Fraenkel; the
    proof formalized here is the self-contained roots-of-unity argument. -/
theorem modulus_dvd_max (D : DCSystem) {M : ℕ}
    (hM : ∀ ap ∈ D.progs, ap.modulus ≤ M)
    (hdist : ∀ ap₁ ∈ D.progs, ∀ ap₂ ∈ D.progs,
      ap₁.modulus < M → ap₁.modulus = ap₂.modulus → ap₁ = ap₂) :
    ∀ ap ∈ D.progs, ap.modulus ∣ M := by
  by_contra hcon
  -- The moduli that fail to divide `M` form a nonempty set `B`.
  have hBne : (D.progs.filter (fun ap => ¬ ap.modulus ∣ M)).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra h
    exact hcon fun ap hap => by by_contra hd; exact h ⟨ap, hap, hd⟩
  -- Pick `r ∈ B` with the largest modulus.
  obtain ⟨r, hrB, hrmax⟩ :=
    (D.progs.filter (fun ap => ¬ ap.modulus ∣ M)).exists_max_image (fun ap => ap.modulus) hBne
  have hrp : r ∈ D.progs := (Finset.mem_filter.mp hrB).1
  have hrnd : ¬ r.modulus ∣ M := (Finset.mem_filter.mp hrB).2
  have hr0 : 0 < r.modulus := (D.valid r hrp).1
  have hr1 : 1 < r.modulus := by
    have hne : r.modulus ≠ 1 := fun h => hrnd (h ▸ one_dvd M)
    omega
  have hrM : r.modulus < M := by
    have hle := hM r hrp
    have hne : r.modulus ≠ M := by
      intro h; rw [h] at hrnd; exact hrnd dvd_rfl
    omega
  -- `N` is a common multiple of all the moduli.
  set N := ∏ ap ∈ D.progs, ap.modulus with hNdef
  have hN0 : 0 < N := Finset.prod_pos fun ap hap => (D.valid ap hap).1
  have hNdvd : ∀ ap ∈ D.progs, ap.modulus ∣ N := fun ap hap => Finset.dvd_prod_of_mem _ hap
  -- **Maximality.**  `r` is the *only* progression whose modulus is divisible by `n_r`.
  have hkey : ∀ ap ∈ D.progs, r.modulus ∣ ap.modulus → ap = r := by
    intro ap hap hdvdm
    have hap0 : 0 < ap.modulus := (D.valid ap hap).1
    rcases eq_or_lt_of_le (Nat.le_of_dvd hap0 hdvdm) with heq | hlt
    · exact (hdist r hrp ap hap hrM heq).symm
    · exfalso
      have hapnd : ¬ ap.modulus ∣ M := fun h => hrnd (hdvdm.trans h)
      have := hrmax ap (Finset.mem_filter.mpr ⟨hap, hapnd⟩)
      omega
  -- A primitive `n_r`-th root of unity.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ r.modulus :=
    ⟨_, Complex.isPrimitiveRoot_exp r.modulus (by omega)⟩
  have hζ1 : ζ ≠ 1 := by
    intro h
    have hd : r.modulus ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (by rw [pow_one, h])
    have := Nat.le_of_dvd one_pos hd
    omega
  have hζN : ζ ^ N = 1 := (hζ.pow_eq_one_iff_dvd N).mpr (hNdvd r hrp)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  -- The standard DCS identity: `0 = ∑_{x<N} ζ^x = ∑_k (contribution of progression k)`.
  have htot : ∑ x ∈ range N, ζ ^ x = 0 := geom_sum_eq_zero_of_pow_eq_one hζN hζ1
  rw [D.sum_range_eq_sum_progs N (fun x => ζ ^ x)] at htot
  -- Every progression other than `r` contributes `0`.
  have hzero : ∀ ap ∈ D.progs, ap ≠ r →
      ∑ x ∈ (range N).filter (fun y => y % ap.modulus = ap.residue), ζ ^ x = 0 := by
    intro ap hap hne
    rw [sum_pow_over_class ζ (D.valid ap hap).1 (D.valid ap hap).2 (hNdvd ap hap)]
    have hw1 : ζ ^ ap.modulus ≠ 1 := fun h =>
      hne (hkey ap hap ((hζ.pow_eq_one_iff_dvd ap.modulus).mp h))
    have hwL : (ζ ^ ap.modulus) ^ (N / ap.modulus) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (hNdvd ap hap)]; exact hζN
    rw [geom_sum_eq_zero_of_pow_eq_one hwL hw1, mul_zero]
  -- ... so only the `k = r` term survives, and it is nonzero.
  rw [Finset.sum_eq_single_of_mem r hrp hzero,
      sum_pow_over_class ζ (D.valid r hrp).1 (D.valid r hrp).2 (hNdvd r hrp),
      (hζ.pow_eq_one_iff_dvd r.modulus).mpr dvd_rfl] at htot
  have hone : ∑ _j ∈ range (N / r.modulus), (1 : ℂ) ^ _j
      = ((N / r.modulus : ℕ) : ℂ) := by simp
  rw [hone] at htot
  have hcpos : 0 < N / r.modulus := Nat.div_pos (Nat.le_of_dvd hN0 (hNdvd r hrp)) hr0
  rcases mul_eq_zero.mp htot with h | h
  · exact pow_ne_zero _ hζ0 h
  · exact (Nat.cast_ne_zero.mpr (by omega)) h

end DCS

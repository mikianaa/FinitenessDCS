import FinitenessDCS.MainTheorem
import FinitenessDCS.DCSystem

/-!
# The main theorem in the DCS (disjoint covering system) setting

This file states the paper's **Theorem 1.1** (`thm:main-dcs`):

> For each fixed `m ≥ 2`, there exist only finitely many disjoint covering systems
> whose moduli satisfy the normalization `(eq:basicas)`
> `3 ≤ n₁ < n₂ < ⋯ < n_{t-m} < n_{t-m+1} = ⋯ = n_t`.

A *disjoint covering system* (DCS) is a finite family of arithmetic progressions
`aᵢ + nᵢℤ ⊆ ℤ` such that every integer lies in **exactly one** of them.  The
normalization `(eq:basicas)` says the minimum modulus is `≥ 3`, the largest
modulus is repeated exactly `m` times, and all the smaller moduli are pairwise
distinct.  `DCSystem`, `DCSystem.Basicas` and the divisibility condition
`modulus_dvd_max` (`nᵢ ∣ n_t`) live in `FinitenessDCS.DCSystem`.

The proof bridges to the coset-partition setting:
reducing modulo `n := lcm(n₁,…,n_t)`, each progression `aᵢ + nᵢℤ` becomes a coset
of `ℤ/nℤ` of size `n/nᵢ`, the `m` copies of the top modulus `n_t = n` become the
`m` singleton cosets, and the result is a `DCS.ValidCosetPartition m`.  Then
`DCS.finiteness_main` bounds `n`, and a DCS satisfying `(eq:basicas)` is recovered
from its reduction mod `n`, so only finitely many exist.
-/

namespace DCS

open Finset

/-- The largest modulus `M` of a disjoint covering system equals the lcm of all its
    moduli.  (`M` divides the lcm as one of the moduli; conversely every modulus
    divides `M` by `modulus_dvd_max`, so `M` is a common multiple and the lcm
    divides it.)  Hence `n_t = lcm(n₁,…,n_t) = n` — the modulus we reduce by in the
    bridge to coset partitions. -/
theorem max_modulus_eq_lcm (D : DCSystem) {M : ℕ}
    (hM : ∀ ap ∈ D.progs, ap.modulus ≤ M)
    (hM_mem : ∃ ap ∈ D.progs, ap.modulus = M)
    (hdist : ∀ ap₁ ∈ D.progs, ∀ ap₂ ∈ D.progs,
      ap₁.modulus < M → ap₁.modulus = ap₂.modulus → ap₁ = ap₂) :
    M = D.progs.lcm (fun ap => ap.modulus) := by
  apply Nat.dvd_antisymm
  · -- `M ∣ lcm`: `M` is one of the moduli.
    obtain ⟨ap, hap, hapM⟩ := hM_mem
    rw [← hapM]; exact Finset.dvd_lcm hap
  · -- `lcm ∣ M`: every modulus divides `M` (the divisibility condition).
    exact Finset.lcm_dvd (fun ap hap => modulus_dvd_max D hM hdist ap hap)

/-- For a DCS satisfying `Basicas m`, the witnessing top modulus `M` equals the lcm
    of all moduli.  This packages `max_modulus_eq_lcm` with the `Basicas` data
    (the filter for `M` has card `m ≥ 2 > 0`, so `M` is attained). -/
theorem basicas_top_eq_lcm {D : DCSystem} {m : ℕ} (hD : D.Basicas m) :
    ∃ M, (∀ ap ∈ D.progs, ap.modulus ≤ M) ∧
         (D.progs.filter (fun ap => ap.modulus = M)).card = m ∧
         M = D.progs.lcm (fun ap => ap.modulus) := by
  obtain ⟨hm, _, M, hMle, hMcard, hMdist⟩ := hD
  refine ⟨M, hMle, hMcard, max_modulus_eq_lcm D hMle ?_ hMdist⟩
  have hne : (D.progs.filter (fun ap => ap.modulus = M)).Nonempty := by
    rw [← Finset.card_pos, hMcard]; omega
  obtain ⟨ap, hap⟩ := hne
  rw [Finset.mem_filter] at hap
  exact ⟨ap, hap.1, hap.2⟩

/-! ### Piece 1 — the reduction `DCSystem → CosetPartition`

Reducing modulo `n` (the top modulus `= lcm`), each progression becomes a coset of
`ℤ/nℤ`.  The semantic core: the membership correspondence (an integer lies in the
progression iff its reduction lies in the coset) and the coset cardinality. -/

section Reduction

variable {n : ℕ}

/-- Reduce an arithmetic progression to a coset of `ℤ/nℤ` (its modulus must divide `n`). -/
def ArithProg.toCoset (ap : ArithProg) (hdvd : ap.modulus ∣ n) (hpos : 0 < ap.modulus) :
    Coset n where
  residue := (ap.residue : ZMod n)
  modulus := ap.modulus
  modulus_dvd := hdvd
  modulus_pos := hpos

/-- Membership in a coset via the projection `ZMod n → ZMod modulus`. -/
lemma Coset.mem_iff_castHom [NeZero n] {K : Coset n} {y : ZMod n} :
    y ∈ K ↔ ZMod.castHom K.modulus_dvd (ZMod K.modulus) y
          = ZMod.castHom K.modulus_dvd (ZMod K.modulus) K.residue := by
  haveI : NeZero K.modulus := ⟨K.modulus_pos.ne'⟩
  rw [Coset.mem_iff_val_modEq, ← ZMod.natCast_eq_natCast_iff]
  have hcast : ∀ z : ZMod n, ((z.val : ℕ) : ZMod K.modulus)
      = ZMod.castHom K.modulus_dvd (ZMod K.modulus) z := by
    intro z; rw [ZMod.castHom_apply, ZMod.natCast_val]
  rw [hcast, hcast]

/-- **Membership correspondence.**  An integer `x` lies in the progression `ap` iff
    its reduction `x mod n` lies in the coset `ap.toCoset`. -/
lemma ArithProg.mem_toCoset_iff {ap : ArithProg} (hdvd : ap.modulus ∣ n) (hpos : 0 < ap.modulus)
    (hn : 0 < n) {x : ℤ} :
    (↑x : ZMod n) ∈ ap.toCoset hdvd hpos ↔ ap.Mem x := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [Coset.mem_iff_castHom]
  change ZMod.castHom hdvd (ZMod ap.modulus) (↑x : ZMod n)
     = ZMod.castHom hdvd (ZMod ap.modulus) (↑(ap.residue : ℕ) : ZMod n) ↔ ap.Mem x
  rw [map_intCast, map_natCast, ArithProg.Mem, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]

/-- **Coset cardinality.**  The coset `ap.toCoset` contains exactly `size = n/modulus`
    elements of `ZMod n`. -/
lemma ArithProg.toCoset_card (ap : ArithProg) (hdvd : ap.modulus ∣ n) (hpos : 0 < ap.modulus)
    (hn : 0 < n) :
    haveI : NeZero n := ⟨hn.ne'⟩
    (Finset.univ.filter (· ∈ ap.toCoset hdvd hpos)).card = (ap.toCoset hdvd hpos).size := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Coset.toCell_toFinsetZMod, PrimeCell.toFinsetZMod_card _ hn, Coset.toCell_size _ hn]

/-- The reduction `x mod n` of an integer lift of `y : ZMod n` is `y`. -/
lemma intCast_val_cast [NeZero n] (y : ZMod n) : ((y.val : ℤ) : ZMod n) = y := by
  rw [Int.cast_natCast]; exact ZMod.natCast_rightInverse y

/-- A total version of `toCoset` (junk default when the modulus does not divide `n`),
    so we can `map` over a `Finset` without carrying membership proofs. -/
def ArithProg.toCosetTotal (ap : ArithProg) (n : ℕ) : Coset n :=
  if h : ap.modulus ∣ n ∧ 0 < ap.modulus then ap.toCoset h.1 h.2
  else ⟨0, 1, one_dvd n, one_pos⟩

lemma ArithProg.toCosetTotal_eq (ap : ArithProg) (hdvd : ap.modulus ∣ n) (hpos : 0 < ap.modulus) :
    ap.toCosetTotal n = ap.toCoset hdvd hpos := by
  rw [toCosetTotal, dif_pos ⟨hdvd, hpos⟩]

namespace DCSystem

variable (D : DCSystem)

/-- The list of cosets obtained by reducing every progression of `D` mod `n`. -/
noncomputable def cosetList (n : ℕ) : List (Coset n) :=
  D.progs.toList.map (fun ap => ap.toCosetTotal n)

variable {D} in
lemma mem_cosetList {K : Coset n} :
    K ∈ D.cosetList n ↔ ∃ ap ∈ D.progs, ap.toCosetTotal n = K := by
  rw [cosetList, List.mem_map]
  constructor
  · rintro ⟨ap, hap, rfl⟩; exact ⟨ap, (Finset.mem_toList).mp hap, rfl⟩
  · rintro ⟨ap, hap, rfl⟩; exact ⟨ap, (Finset.mem_toList).mpr hap, rfl⟩

lemma cosetList_nodup (hn : 0 < n) (hdvd : ∀ ap ∈ D.progs, ap.modulus ∣ n) :
    (D.cosetList n).Nodup := by
  rw [cosetList]
  apply List.Nodup.map_on _ (Finset.nodup_toList _)
  intro ap hap ap' hap' heq
  rw [Finset.mem_toList] at hap hap'
  rw [ap.toCosetTotal_eq (hdvd ap hap) (D.valid ap hap).1,
      ap'.toCosetTotal_eq (hdvd ap' hap') (D.valid ap' hap').1] at heq
  have hmod : ap.modulus = ap'.modulus := congrArg Coset.modulus heq
  have hres : (↑ap.residue : ZMod n) = (↑ap'.residue : ZMod n) := congrArg Coset.residue heq
  have hresn : ap.residue < n := lt_of_lt_of_le (D.valid ap hap).2 (Nat.le_of_dvd hn (hdvd ap hap))
  have hres'n : ap'.residue < n :=
    lt_of_lt_of_le (D.valid ap' hap').2 (Nat.le_of_dvd hn (hdvd ap' hap'))
  have hreseq : ap.residue = ap'.residue := by
    have := congrArg ZMod.val hres
    rwa [ZMod.val_natCast_of_lt hresn, ZMod.val_natCast_of_lt hres'n] at this
  obtain ⟨m, r⟩ := ap; obtain ⟨m', r'⟩ := ap'; simp_all

/-- The reduced cosets disjointly cover `ℤ/nℤ` (transferred from `D.covers`). -/
lemma cosetList_cover (hn : 0 < n) (hdvd : ∀ ap ∈ D.progs, ap.modulus ∣ n) (y : ZMod n) :
    ∃! K : Coset n, K ∈ D.cosetList n ∧ y ∈ K := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hy : ((y.val : ℤ) : ZMod n) = y := intCast_val_cast y
  obtain ⟨ap, ⟨hap, hapMem⟩, huniq⟩ := D.covers (y.val : ℤ)
  refine ⟨ap.toCosetTotal n, ⟨mem_cosetList.mpr ⟨ap, hap, rfl⟩, ?_⟩, ?_⟩
  · rw [ap.toCosetTotal_eq (hdvd ap hap) (D.valid ap hap).1, ← hy]
    exact (ArithProg.mem_toCoset_iff (hdvd ap hap) (D.valid ap hap).1 hn
      (x := (y.val : ℤ))).mpr hapMem
  · rintro K ⟨hK, hyK⟩
    obtain ⟨ap', hap', rfl⟩ := mem_cosetList.mp hK
    rw [ap'.toCosetTotal_eq (hdvd ap' hap') (D.valid ap' hap').1, ← hy,
        ArithProg.mem_toCoset_iff (hdvd ap' hap') (D.valid ap' hap').1 hn] at hyK
    rw [huniq ap' ⟨hap', hyK⟩]

/-- The reduced coset sizes sum to `n` (disjoint-cover counting). -/
lemma cosetList_partition (hn : 0 < n) (hdvd : ∀ ap ∈ D.progs, ap.modulus ∣ n) :
    ((D.cosetList n).map Coset.size).sum = n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set S : Coset n → Finset (ZMod n) := fun K => Finset.univ.filter (· ∈ K) with hS
  have hdisj : ∀ K₁ ∈ (D.cosetList n).toFinset, ∀ K₂ ∈ (D.cosetList n).toFinset,
      K₁ ≠ K₂ → Disjoint (S K₁) (S K₂) := by
    intro K₁ hK₁ K₂ hK₂ hne
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    rw [hS, Finset.mem_filter] at hy₁ hy₂
    rw [List.mem_toFinset] at hK₁ hK₂
    obtain ⟨_, _, huniq⟩ := D.cosetList_cover hn hdvd y
    exact hne (by rw [huniq K₁ ⟨hK₁, hy₁.2⟩, huniq K₂ ⟨hK₂, hy₂.2⟩])
  have hbu : (Finset.univ : Finset (ZMod n)) = (D.cosetList n).toFinset.biUnion S := by
    ext y
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion, List.mem_toFinset, hS,
      Finset.mem_filter]
    obtain ⟨K, ⟨hK, hyK⟩, _⟩ := D.cosetList_cover hn hdvd y
    exact ⟨K, hK, trivial, hyK⟩
  have hcard : ((D.cosetList n).map Coset.size).sum
      = ∑ K ∈ (D.cosetList n).toFinset, (S K).card := by
    rw [← List.sum_toFinset (l := D.cosetList n) Coset.size (D.cosetList_nodup hn hdvd)]
    apply Finset.sum_congr rfl
    intro K hK
    rw [List.mem_toFinset] at hK
    obtain ⟨ap, hap, rfl⟩ := mem_cosetList.mp hK
    rw [ap.toCosetTotal_eq (hdvd ap hap) (D.valid ap hap).1, hS,
        ap.toCoset_card (hdvd ap hap) (D.valid ap hap).1 hn]
  rw [hcard, ← Finset.card_biUnion hdisj, ← hbu, Finset.card_univ, ZMod.card]

/-- **Piece 1.**  The reduction of a disjoint covering system mod `n` (with every
    modulus dividing `n`) to a coset partition of `ℤ/nℤ`.  Reducing each progression
    `aᵢ + nᵢℤ` to the coset `(aᵢ mod n, nᵢ)`, the membership correspondence turns
    `D.covers` into the coset `cover`, and the disjoint-cover counting gives the size
    accounting `partition`. -/
noncomputable def toCosetPartition (hn : 0 < n)
    (hdvd : ∀ ap ∈ D.progs, ap.modulus ∣ n) : CosetPartition n where
  cosets := D.cosetList n
  partition := D.cosetList_partition hn hdvd
  cover := D.cosetList_cover hn hdvd
  cosets_nodup := D.cosetList_nodup hn hdvd

end DCSystem

end Reduction

namespace DCSystem

variable (D : DCSystem)

/-- **Piece 2.**  A DCS satisfying `Basicas m` reduces to a `ValidCosetPartition m`
    (with `n = M`, the top modulus `= lcm`).  The `m` top-modulus progressions become
    the `m` size-1 singleton cosets (`hsingleton`); `min modulus ≥ 3` gives
    `size ≤ n/3` (`hsizes_le`); distinct smaller moduli give distinct non-singleton
    sizes (`hdistinct`).  `M`'s divisibility of every modulus is `modulus_dvd_max`. -/
noncomputable def toValidCosetPartition {m : ℕ} (hD : D.Basicas m) : ValidCosetPartition m := by
  obtain ⟨hm, h3, hM⟩ := hD
  -- choose the top modulus `M` as data (noncomputably)
  set M := hM.choose with hMdef
  have hMle : ∀ ap ∈ D.progs, ap.modulus ≤ M := hM.choose_spec.1
  have hMcard : (D.progs.filter (fun ap => ap.modulus = M)).card = m := hM.choose_spec.2.1
  have hMdist : ∀ ap₁ ∈ D.progs, ∀ ap₂ ∈ D.progs,
      ap₁.modulus < M → ap₁.modulus = ap₂.modulus → ap₁ = ap₂ := hM.choose_spec.2.2
  have hM_mem : ∃ ap ∈ D.progs, ap.modulus = M := by
    have hne : (D.progs.filter (fun ap => ap.modulus = M)).Nonempty := by
      rw [← Finset.card_pos, hMcard]; omega
    obtain ⟨ap, hap⟩ := hne; rw [Finset.mem_filter] at hap; exact ⟨ap, hap.1, hap.2⟩
  have hM3 : 3 ≤ M := by
    obtain ⟨apM, hapM, hapM_eq⟩ := hM_mem; rw [← hapM_eq]; exact h3 apM hapM
  have hMpos : 0 < M := by omega
  have hdvd : ∀ ap ∈ D.progs, ap.modulus ∣ M := modulus_dvd_max D hMle hMdist
  have hsize : ∀ ap ∈ D.progs, (ap.toCosetTotal M).size = M / ap.modulus := fun ap hap => by
    rw [ap.toCosetTotal_eq (hdvd ap hap) (D.valid ap hap).1]; rfl
  refine
    { n := M
      P := D.toCosetPartition hMpos hdvd
      hn := hMpos
      hm := hm
      hsingleton := ?_
      hsizes_le := ?_
      hdistinct := ?_ }
  · -- hsingleton : singletonCount = m
    have key : ∀ ap ∈ D.progs.toList,
        ((fun K => decide (K.size = 1)) ∘ (fun ap : ArithProg => ap.toCosetTotal M)) ap = true
          ↔ decide (ap.modulus = M) = true := by
      intro ap hap
      rw [Finset.mem_toList] at hap
      simp only [Function.comp_apply, decide_eq_true_eq, hsize ap hap]
      constructor
      · intro h1
        have hc := Nat.mul_div_cancel' (hdvd ap hap)
        rw [h1, Nat.mul_one] at hc; exact hc
      · intro h; rw [h, Nat.div_self hMpos]
    have hcos : (D.toCosetPartition hMpos hdvd).cosets = D.cosetList M := rfl
    rw [CosetPartition.singletonCount, hcos, ← List.countP_eq_length_filter]
    unfold DCSystem.cosetList
    rw [List.countP_map, List.countP_congr key, ← hMcard,
        ← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter, Finset.card,
        Finset.filter_val]
  · -- hsizes_le : ∀ K ∈ cosets, 3 * size ≤ M
    intro K hK
    obtain ⟨ap, hap, rfl⟩ := mem_cosetList.mp hK
    rw [hsize ap hap]
    calc 3 * (M / ap.modulus)
        ≤ ap.modulus * (M / ap.modulus) := Nat.mul_le_mul_right _ (h3 ap hap)
      _ = M := Nat.mul_div_cancel' (hdvd ap hap)
  · -- hdistinct : non-singleton sizes are distinct
    intro K₁ K₂ hK₁ hK₂ hsizeeq hsize1
    obtain ⟨ap₁, hap₁, rfl⟩ := mem_cosetList.mp hK₁
    obtain ⟨ap₂, hap₂, rfl⟩ := mem_cosetList.mp hK₂
    rw [hsize ap₁ hap₁, hsize ap₂ hap₂] at hsizeeq
    rw [hsize ap₁ hap₁] at hsize1
    have hmodeq : ap₁.modulus = ap₂.modulus := by
      rw [← Nat.div_div_self (hdvd ap₁ hap₁) hMpos.ne',
          ← Nat.div_div_self (hdvd ap₂ hap₂) hMpos.ne', hsizeeq]
    have hmodlt : ap₁.modulus < M := by
      by_contra h
      rw [not_lt] at h
      have heq : ap₁.modulus = M := le_antisymm (hMle ap₁ hap₁) h
      rw [heq, Nat.div_self hMpos] at hsize1; omega
    rw [hMdist ap₁ hap₁ ap₂ hap₂ hmodlt hmodeq]

end DCSystem

/-- **Piece 3.**  For each fixed `m`, every modulus of a DCS satisfying `Basicas m`
    is bounded by a constant `N` depending only on `m`.  (Apply `finiteness_main` to
    the reduced `ValidCosetPartition m`, whose `n` is the top modulus `M`; every
    modulus is `≤ M = n ≤ N`.) -/
theorem modulus_bound (m : ℕ) :
    ∃ N, ∀ (D : DCSystem), D.Basicas m → ∀ ap ∈ D.progs, ap.modulus ≤ N := by
  obtain ⟨N, hN⟩ := finiteness_main m
  refine ⟨N, fun D hD ap hap => ?_⟩
  have hle : ap.modulus ≤ (D.toValidCosetPartition hD).n := by
    obtain ⟨hm', h3, hM⟩ := hD
    unfold DCSystem.toValidCosetPartition
    exact hM.choose_spec.1 ap hap
  exact le_trans hle (hN _)

/-- **Theorem 1.1** (`thm:main-dcs`).  For each fixed `m ≥ 2`, there are only
    finitely many disjoint covering systems whose moduli satisfy the normalization
    `(eq:basicas)`.

    Proof (**Piece 4**): by `modulus_bound`, every modulus of a valid system is
    `≤ N`, and residues are `< modulus ≤ N`, so all progressions lie in the finite
    set `B` of arithmetic progressions with `modulus, residue ≤ N`.  A DCS is
    determined by its `progs` (the `valid`/`covers` fields are `Prop`s), so the map
    `D ↦ D.progs` injects `{D | D.Basicas m}` into the finite powerset of `B`. -/
theorem main_dcs (m : ℕ) :
    { D : DCSystem | D.Basicas m }.Finite := by
  obtain ⟨N, hN⟩ := modulus_bound m
  -- finite set of bounded arithmetic progressions (modulus, residue ≤ N)
  set B : Finset ArithProg :=
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).image
      (fun p => ({ modulus := p.1, residue := p.2 } : ArithProg)) with hB
  -- a DCS is determined by its progressions (other fields are Props)
  have hinj : Set.InjOn (fun D : DCSystem => D.progs) {D | D.Basicas m} := by
    intro D _ D' _ h
    obtain ⟨p, v, c⟩ := D; obtain ⟨p', v', c'⟩ := D'
    simp only at h; subst h; rfl
  refine Set.Finite.of_finite_image ?_ hinj
  -- the image lands in the (finite) powerset of `B`
  apply Set.Finite.subset B.powerset.finite_toSet
  rintro _ ⟨D, hD, rfl⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro ap hap
  rw [hB, Finset.mem_image]
  refine ⟨(ap.modulus, ap.residue), ?_, rfl⟩
  have hmod : ap.modulus ≤ N := hN D hD ap hap
  obtain ⟨hvpos, hvres⟩ := D.valid ap hap
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨by omega, by omega⟩

end DCS

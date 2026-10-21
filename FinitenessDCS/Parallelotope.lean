import Mathlib

/-!
# General finite parallelotopes and cells

This file develops the parallelotope / cell combinatorics of the paper in their
**general** form, with no number theory attached.  Following the paper, a
*parallelotope* is a finite product of finite intervals

  `P(b) = ∏_{i ∈ ι} {0, 1, …, b i - 1}`,

modelled here as the dependent function type `∀ i, Fin (b i)`.  A *cell* fixes
the coordinates outside a chosen finite "free" set `T = freeIdx` and lets the
free coordinates range freely; this is the paper's `X(u, T)`.

The number-theoretic parallelotope attached to an integer `n` (obtained via the
Chinese Remainder Theorem and `p`-adic digit expansion) is later recovered as
the special case `ι = PrimeCoord n`, `b c = c.prime` (later in this file).
Keeping this layer general means the cell
cardinality lemma and the cell inequality are stated and (for cardinality)
proved once, exactly as in the paper, before any specialization.

## Design note

We model the parallelotope as a bare dependent function type
`Parallelotope ι b` together with `variable`-level instance assumptions
`[Fintype ι] [DecidableEq ι]`.  This is the idiomatic mathlib style (it lets the
`Pi`/`Fintype`/`Finset.piFinset` machinery apply directly), and is lighter than
bundling everything into a `structure Box`.  A side-length hypothesis such as
`2 ≤ b i` is *not* baked into the type; it is added as an explicit hypothesis to
the lemmas that need it.

## Main definitions

* `DCS.Box.Parallelotope ι b` — the general parallelotope.
* `DCS.Box.Cell ι b` — a cell: free coordinates plus fixed values.
* `DCS.Box.Cell.size` — `∏_{i ∈ freeIdx} b i`.
* `DCS.Box.Cell.toFinset` — the points of the parallelotope lying in the cell.
* `DCS.Box.CellPartition ι b` — a partition of the parallelotope into cells.

## Main results

* `DCS.Box.Parallelotope.card` — `|P(b)| = ∏ i, b i`.
* `DCS.Box.Cell.card_toFinset` — `|X| = ∏_{i ∈ freeIdx} b i = X.size`.
* `DCS.Box.cell_inequality` — the Berger–Felzenbaum–Fraenkel cell inequality
  (Proposition 2.1 of the paper), together with its corollaries.
-/

namespace DCS.Box

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}

/-! ### The general parallelotope -/

/-- The (finite) parallelotope with coordinate set `ι` and side lengths `b`:
    the points whose `i`-th coordinate lies in `{0, …, b i - 1}`, i.e. the
    dependent functions `i ↦ Fin (b i)`. -/
abbrev Parallelotope (ι : Type*) (b : ι → ℕ) : Type _ := ∀ i, Fin (b i)

instance Parallelotope.instFintype
    (ι : Type u) [Fintype ι] [DecidableEq ι] (b : ι → ℕ) :
    Fintype (Parallelotope ι b) := by
  unfold Parallelotope
  infer_instance

/-- The parallelotope has `∏ i, b i` points. -/
@[simp]
lemma Parallelotope.card
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : ι → ℕ) :
    Fintype.card (Parallelotope ι b) = ∏ i, b i := by
  change Fintype.card ((i : ι) → Fin (b i)) = ∏ i, b i
  simpa only [Fintype.card_fin] using
    (Fintype.card_pi :
      Fintype.card ((i : ι) → Fin (b i))
        = ∏ i, Fintype.card (Fin (b i)))

/-! ### Cells -/

/-- A *cell* of the parallelotope, the paper's `X(u, T)`:
    * `freeIdx` is the finite set `T` of free coordinates;
    * `fixedVals` prescribes a value `u i` at every coordinate (the prescribed
      values at *free* coordinates are irrelevant and treated as junk).

    A point lies in the cell iff it agrees with `fixedVals` at every coordinate
    *outside* `freeIdx`; see `Cell.Mem`. -/
structure Cell (ι : Type*) (b : ι → ℕ) where
  /-- The free coordinates `T`: those allowed to vary. -/
  freeIdx : Finset ι
  /-- The prescribed value at each coordinate (only the values outside `freeIdx`
      matter for membership). -/
  fixedVals : ∀ i, Fin (b i)

namespace Cell

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}

/-- The combinatorial size of a cell: `∏_{i ∈ freeIdx} b i`.

    This is the number of ways to fill in the free coordinates, and is shown to
    equal the actual number of points of the cell in `card_toFinset`. -/
def size (X : Cell ι b) : ℕ := ∏ i ∈ X.freeIdx, b i

/-- Membership of a parallelotope point in a cell: it must agree with the cell's
    fixed values at every non-free coordinate. -/
def Mem (X : Cell ι b) (y : Parallelotope ι b) : Prop :=
  ∀ i ∉ X.freeIdx, y i = X.fixedVals i

instance (X : Cell ι b) : DecidablePred X.Mem := fun _ =>
  Fintype.decidableForallFintype

/-- Cells have decidable equality (determined by their free set and fixed
    values), so families of cells can be collected into a `Finset`. -/
instance : DecidableEq (Cell ι b) := fun X Y =>
  decidable_of_iff (X.freeIdx = Y.freeIdx ∧ X.fixedVals = Y.fixedVals)
    (by cases X; cases Y; simp)

/-- The points of the parallelotope lying in the cell, as a `Finset`.  This is
    the cell viewed as a concrete subset `X ⊆ P(b)`. -/
def toFinset (X : Cell ι b) : Finset (Parallelotope ι b) :=
  Finset.univ.filter X.Mem

@[simp] lemma mem_toFinset {X : Cell ι b} {y : Parallelotope ι b} :
    y ∈ X.toFinset ↔ X.Mem y := by
  simp [toFinset]

/-- **Cell cardinality** (paper: `|X(u, T)| = ∏_{i ∈ T} b i`).

    A cell contains exactly `∏_{i ∈ freeIdx} b i = X.size` points: the free
    coordinates may take any value, while the fixed coordinates are pinned.

    The proof rewrites the cell as `Fintype.piFinset` of the "ranges"
    `i ↦ if i ∈ freeIdx then univ else {fixedVals i}`, whose cardinality is the
    product of the ranges' cardinalities (`b i` on free coordinates, `1`
    elsewhere). -/
theorem card_toFinset (X : Cell ι b) : X.toFinset.card = X.size := by
  -- The cell is exactly the box of functions that are unconstrained on
  -- `freeIdx` and pinned to `fixedVals` elsewhere.
  have h : X.toFinset =
      Fintype.piFinset (fun i : ι =>
        if i ∈ X.freeIdx then (Finset.univ : Finset (Fin (b i)))
        else {X.fixedVals i}) := by
    ext y
    rw [mem_toFinset, Fintype.mem_piFinset]
    unfold Mem
    constructor
    · intro hy i
      by_cases hi : i ∈ X.freeIdx
      · simp [hi]
      · simp [hi, hy i hi]
    · intro hy i hi
      have hyi := hy i
      rwa [if_neg hi, Finset.mem_singleton] at hyi
  rw [h]
  simp only [Fintype.card_piFinset]
  -- Each range has cardinality `b i` (free) or `1` (fixed); the `1`s drop out.
  have hcard : ∀ i : ι,
      (if i ∈ X.freeIdx then (Finset.univ : Finset (Fin (b i)))
        else {X.fixedVals i}).card = if i ∈ X.freeIdx then b i else 1 := by
    intro i; by_cases hi : i ∈ X.freeIdx <;> simp [hi]
  rw [Finset.prod_congr rfl (fun i _ => hcard i), Fintype.prod_ite_mem]
  rfl

end Cell

/-! ### Cell partitions -/

/-- A *cell partition* of the parallelotope: a finite family of cells whose
    underlying subsets `Cell.toFinset` tile `P(b)`, i.e. every point lies in
    exactly one cell.  (This is all we need for the counting argument; we do
    not separately demand the cells be distinct, as `∃!` already forbids a
    point being covered twice.) -/
structure CellPartition (ι : Type*) [Fintype ι] [DecidableEq ι] (b : ι → ℕ) where
  /-- The cells of the partition. -/
  cells : Finset (Cell ι b)
  /-- Every point of the parallelotope lies in exactly one cell. -/
  covers : ∀ y : Parallelotope ι b, ∃! X, X ∈ cells ∧ X.Mem y

/-! ### Coordinatewise translation API

To reduce the cell inequality to a *normalized* situation (the distinguished
cell `X` fixed to zero on the remaining coordinates `R`), we relabel each
coordinate `Fin (b i)` by an equivalence `e i`.  This relabelling lifts to the
parallelotope, to cells, and to cell partitions, preserving sizes and the cover
property; only the coordinate values are renamed. -/

section Translation
-- These lemmas are purely coordinatewise and need neither `Fintype ι` nor
-- `DecidableEq ι`; we shadow the section instances to keep the statements clean.
variable {ι : Type*} {b : ι → ℕ}

namespace Parallelotope

/-- Coordinatewise relabelling of the parallelotope by an equivalence `e i` in
    each coordinate. -/
def map (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) :
    Parallelotope ι b ≃ Parallelotope ι b where
  toFun y := fun i => e i (y i)
  invFun y := fun i => (e i).symm (y i)
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp

@[simp] lemma map_apply
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    (y : Parallelotope ι b) (i : ι) :
    (Parallelotope.map e y) i = e i (y i) := rfl

@[simp] lemma map_symm_apply
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    (y : Parallelotope ι b) (i : ι) :
    ((Parallelotope.map e).symm y) i = (e i).symm (y i) := rfl

end Parallelotope

namespace Cell

/-- Coordinatewise relabelling of a cell: keep the free set, push the fixed
    values through `e`. -/
def map (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) (X : Cell ι b) : Cell ι b where
  freeIdx := X.freeIdx
  fixedVals := fun i => e i (X.fixedVals i)

@[simp] lemma map_freeIdx
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) (X : Cell ι b) :
    (X.map e).freeIdx = X.freeIdx := rfl

@[simp] lemma map_fixedVals
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) (X : Cell ι b) (i : ι) :
    (X.map e).fixedVals i = e i (X.fixedVals i) := rfl

@[simp] lemma map_size
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) (X : Cell ι b) :
    (X.map e).size = X.size := rfl

/-- Membership is preserved by the coordinatewise relabelling: `y ∈ X` iff the
    relabelled point lies in the relabelled cell. -/
lemma map_mem_iff
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) {X : Cell ι b} {y : Parallelotope ι b} :
    (X.map e).Mem (Parallelotope.map e y) ↔ X.Mem y := by
  constructor
  · intro h i hi
    have hh := h i hi
    simp only [Parallelotope.map_apply, Cell.map_fixedVals] at hh
    exact (e i).injective hh
  · intro h i hi
    simp only [Parallelotope.map_apply, Cell.map_fixedVals]
    exact congrArg (e i) (h i hi)

/-- Inverse form of `map_mem_iff`. -/
lemma mem_map_iff
    {e : ∀ i : ι, Fin (b i) ≃ Fin (b i)} {X : Cell ι b} {y : Parallelotope ι b} :
    (X.map e).Mem y ↔ X.Mem ((Parallelotope.map e).symm y) := by
  have h := map_mem_iff e (X := X) (y := (Parallelotope.map e).symm y)
  rwa [Equiv.apply_symm_apply] at h

/-- The cell relabelling is injective. -/
lemma map_injective
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) :
    Function.Injective (fun X : Cell ι b => X.map e) := by
  intro X Y h
  obtain ⟨xf, xv⟩ := X
  obtain ⟨yf, yv⟩ := Y
  have hfree : xf = yf := congrArg Cell.freeIdx h
  have hfix : xv = yv := by
    funext i
    have hi := congrArg (fun Z => Z.fixedVals i) h
    simp only [Cell.map_fixedVals] at hi
    exact (e i).injective hi
  subst hfree; subst hfix; rfl

end Cell

end Translation

namespace CellPartition

/-- Push a cell partition through the coordinatewise relabelling `e`. -/
def map (P : CellPartition ι b) (e : ∀ i : ι, Fin (b i) ≃ Fin (b i)) :
    CellPartition ι b where
  cells := P.cells.map ⟨Cell.map e, Cell.map_injective e⟩
  covers := by
    intro y'
    obtain ⟨X, ⟨hX_mem, hX_y⟩, hX_uniq⟩ := P.covers ((Parallelotope.map e).symm y')
    refine ⟨X.map e, ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_map]
      exact ⟨X, hX_mem, rfl⟩
    · rw [Cell.mem_map_iff]
      exact hX_y
    · rintro Z ⟨hZ_mem, hZ_y⟩
      rw [Finset.mem_map] at hZ_mem
      obtain ⟨W, hW_mem, hWZ⟩ := hZ_mem
      simp only [Function.Embedding.coeFn_mk] at hWZ
      subst hWZ
      rw [Cell.mem_map_iff] at hZ_y
      rw [hX_uniq W ⟨hW_mem, hZ_y⟩]

/-- A cell lies in the relabelled partition iff it is the relabelling of a cell
    of the original partition. -/
lemma mem_map_cells_iff
    {P : CellPartition ι b} {e : ∀ i : ι, Fin (b i) ≃ Fin (b i)} {Y : Cell ι b} :
    Y ∈ (P.map e).cells ↔ ∃ X ∈ P.cells, X.map e = Y := by
  simp only [CellPartition.map, Finset.mem_map, Function.Embedding.coeFn_mk]

end CellPartition

/-! ### Stage 2.5: transport of filtered cell sums under translation

Coordinatewise relabelling preserves the right-hand side of the cell
inequality: it carries the "good" cells (those with `freeIdx ⊆ U`) bijectively
to the good cells of the relabelled partition, and preserves their sizes.  This
lets us prove the inequality in a *normalized* partition `P.map e` and then
rewrite the resulting sum back to the original `P.cells`. -/

section TranslationTransport
-- `Cell.map_freeIdx_subset_iff` is purely coordinatewise; shadow the section
-- instances to keep its statement clean.
variable {ι : Type*} {b : ι → ℕ}

namespace Cell

/-- Relabelling does not change whether a cell's free set is contained in `U`
    (the free set is untouched). -/
lemma map_freeIdx_subset_iff
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    {X : Cell ι b} {U : Finset ι} :
    (X.map e).freeIdx ⊆ U ↔ X.freeIdx ⊆ U := by
  simp

end Cell

end TranslationTransport

namespace CellPartition

/-- The relabelling of a cell of `P` is a cell of `P.map e`. -/
lemma map_cell_mem
    (P : CellPartition ι b)
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    {X : Cell ι b} (hX : X ∈ P.cells) :
    X.map e ∈ (P.map e).cells := by
  rw [CellPartition.mem_map_cells_iff]
  exact ⟨X, hX, rfl⟩

/-- The good cells (`freeIdx ⊆ U`) of `P.map e` are exactly the relabellings of
    the good cells of `P`. -/
lemma mem_map_filter_freeIdx_iff
    {P : CellPartition ι b}
    {e : ∀ i : ι, Fin (b i) ≃ Fin (b i)}
    {U : Finset ι} {Y : Cell ι b} :
    Y ∈ (P.map e).cells.filter (fun Y => Y.freeIdx ⊆ U)
      ↔ ∃ X ∈ P.cells.filter (fun X => X.freeIdx ⊆ U), X.map e = Y := by
  rw [Finset.mem_filter, CellPartition.mem_map_cells_iff]
  constructor
  · rintro ⟨⟨X, hX_mem, rfl⟩, hY_sub⟩
    refine ⟨X, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨hX_mem, ?_⟩
    rwa [Cell.map_freeIdx] at hY_sub
  · rintro ⟨X, hX_filter, rfl⟩
    rw [Finset.mem_filter] at hX_filter
    refine ⟨⟨X, hX_filter.1, rfl⟩, ?_⟩
    rw [Cell.map_freeIdx]
    exact hX_filter.2

/-- The "good" filter commutes with the partition relabelling. -/
lemma map_filter_freeIdx
    (P : CellPartition ι b)
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    (U : Finset ι) :
    ((P.map e).cells.filter (fun Y => Y.freeIdx ⊆ U))
      = (P.cells.filter (fun Y => Y.freeIdx ⊆ U)).map
          ⟨Cell.map e, Cell.map_injective e⟩ := by
  ext Y
  rw [mem_map_filter_freeIdx_iff, Finset.mem_map]
  simp only [Function.Embedding.coeFn_mk]

/-- **Key sum-preservation lemma.**  The total size of the good cells is
    invariant under relabelling. -/
lemma map_good_sum_size
    (P : CellPartition ι b)
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    (U : Finset ι) :
    ∑ Y ∈ (P.map e).cells.filter (fun Y => Y.freeIdx ⊆ U), Y.size
      = ∑ Y ∈ P.cells.filter (fun Y => Y.freeIdx ⊆ U), Y.size := by
  rw [CellPartition.map_filter_freeIdx, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro X _
  simp only [Function.Embedding.coeFn_mk, Cell.map_size]

/-- The distinguished cell stays in the relabelled partition (alias of
    `map_cell_mem`, used when applying the normalized inequality). -/
lemma map_distinguished_mem
    (P : CellPartition ι b)
    (e : ∀ i : ι, Fin (b i) ≃ Fin (b i))
    {X : Cell ι b} (hX : X ∈ P.cells) :
    X.map e ∈ (P.map e).cells :=
  CellPartition.map_cell_mem P e hX

end CellPartition

/-! ### The normalizing equivalence

The specific relabelling we use: on each coordinate of a set `R` it swaps the
distinguished cell `X`'s fixed value with zero, so that after relabelling `X`'s
fixed value is zero throughout `R`.  (Side lengths are `≥ 2`, so zero exists.) -/

section Normalize
variable {ι : Type*} [DecidableEq ι] {b : ι → ℕ}

/-- The zero point in coordinate `i` (well-defined since `2 ≤ b i`). -/
def finZero (hb : ∀ i : ι, 2 ≤ b i) (i : ι) : Fin (b i) :=
  ⟨0, by have := hb i; omega⟩

/-- The equivalence that swaps `X`'s fixed value with zero on each coordinate in
    `R`, leaving every other coordinate untouched. -/
def normalizeEquiv
    (hb : ∀ i : ι, 2 ≤ b i) (X : Cell ι b) (R : Finset ι) :
    ∀ i : ι, Fin (b i) ≃ Fin (b i) :=
  fun i =>
    if i ∈ R then
      Equiv.swap (X.fixedVals i) (finZero hb i)
    else
      Equiv.refl _

/-- After normalizing, the distinguished cell `X` has fixed value zero on every
    coordinate of `R`. -/
lemma normalize_fixedVals_eq_zero
    (hb : ∀ i : ι, 2 ≤ b i) (X : Cell ι b) (R : Finset ι) {i : ι} (hi : i ∈ R) :
    ((X.map (normalizeEquiv hb X R)).fixedVals i).val = 0 := by
  rw [Cell.map_fixedVals]
  simp only [normalizeEquiv, if_pos hi]
  rw [Equiv.swap_apply_left]
  rfl

end Normalize

/-! ### Partition counting -/

namespace CellPartition

/-- **Partition counting.**  For any finite set `A` of parallelotope points,
    summing `|Y ∩ A|` over the cells `Y` of the partition recovers `|A|`,
    because every point of `A` lies in exactly one cell (`P.covers`). -/
lemma sum_inter_card
    (P : CellPartition ι b) (A : Finset (Parallelotope ι b)) :
    ∑ Y ∈ P.cells, (Y.toFinset ∩ A).card = A.card := by
  -- Write each `|Y ∩ A|` as a sum of indicators over `A`.
  have step1 : ∀ Y : Cell ι b,
      (Y.toFinset ∩ A).card = ∑ y ∈ A, (if y ∈ Y.toFinset then 1 else 0) := by
    intro Y
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  calc ∑ Y ∈ P.cells, (Y.toFinset ∩ A).card
      = ∑ Y ∈ P.cells, ∑ y ∈ A, (if y ∈ Y.toFinset then 1 else 0) :=
        Finset.sum_congr rfl (fun Y _ => step1 Y)
    _ = ∑ y ∈ A, ∑ Y ∈ P.cells, (if y ∈ Y.toFinset then 1 else 0) := Finset.sum_comm
    _ = ∑ y ∈ A, 1 := by
        apply Finset.sum_congr rfl
        intro y _
        -- The inner sum counts the cells containing `y`; exactly one does.
        rw [← Finset.card_filter]
        obtain ⟨X₀, ⟨hX₀_mem, hX₀_y⟩, hX₀_uniq⟩ := P.covers y
        have hsingle : P.cells.filter (fun Y => y ∈ Y.toFinset) = {X₀} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_filter, Cell.mem_toFinset]
            exact ⟨hX₀_mem, hX₀_y⟩
          · intro Z hZ
            rw [Finset.mem_filter, Cell.mem_toFinset] at hZ
            exact hX₀_uniq Z hZ
        rw [hsingle, Finset.card_singleton]
    _ = A.card := by simp

end CellPartition

/-! ### The general cell inequality

This is Proposition I of Berger–Felzenbaum–Fraenkel, stated in the paper's
general form.  Fix a cell partition and a distinguished cell `X`.  Let `S` be a
set of "harmless" coordinates that we are allowed to also treat as fixed, and let

  `R = ι \ (freeIdx X ∪ S)`

be the remaining coordinates, assumed nonempty, with `b₀ = min_{i ∈ R} b i`.
Then the cells whose free set is contained in `freeIdx X ∪ S` carry total mass at
least `b₀ · |X|`.
-/

/-- **Normalized cell inequality.**

    This is the normalized version of the BFF cell inequality: it has exactly the
    same conclusion as `cell_inequality`, but adds the hypothesis `hX_zero`
    saying the distinguished cell `X` is *fixed to zero* on the remaining
    coordinates `R = ι \ (freeIdx X ∪ S)`.

    The extra assumption corresponds to translating the parallelotope so that
    `X` meets the shrunk parallelotope (the one shrunk in the `R`-coordinates)
    in the easiest possible way — with its fixed digits all equal to `0` there.
    This is the position in which the deep counting argument (shrink + partition
    into `b₀` congruence classes) is cleanest to carry out.

    The full `cell_inequality` is derived from this theorem by applying it to
    the relabelled partition `P.map (normalizeEquiv hb X R)` (in which the
    distinguished cell `X.map …` is zero on `R`, by `normalize_fixedVals_eq_zero`)
    and then transporting the filtered sum back to `P.cells` via
    `CellPartition.map_good_sum_size`. -/
theorem cell_inequality_normalized
    (hb : ∀ i : ι, 2 ≤ b i)
    (P : CellPartition ι b) (X : Cell ι b) (hX : X ∈ P.cells)
    (S : Finset ι) {b₀ : ℕ}
    -- (hS : S ⊆ Finset.univ \ X.freeIdx)
    (hR : (Finset.univ \ (X.freeIdx ∪ S)).Nonempty)
    (hb₀ : b₀ = (Finset.univ \ (X.freeIdx ∪ S)).inf' hR b)
    (hX_zero :
      ∀ i ∈ Finset.univ \ (X.freeIdx ∪ S),
        (X.fixedVals i).val = 0) :
    b₀ * X.size ≤
      ∑ Xⱼ ∈ P.cells.filter
        (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ S), Xⱼ.size := by
  -- ===== Shrunk-box setup =====
  -- 1, 2: the fixed set `U` and the remaining coordinates `R`.
  let U : Finset ι := X.freeIdx ∪ S
  let R : Finset ι := Finset.univ \ U
  have hR_def : R = Finset.univ \ (X.freeIdx ∪ S) := rfl
  -- coordinates of `R` are genuinely fixed for `X`.
  have hR_fixed_X : ∀ i ∈ R, i ∉ X.freeIdx := by
    intro i hi hmem
    have hnot : i ∉ X.freeIdx ∪ S := by
      simpa only [hR_def, Finset.mem_sdiff, Finset.mem_univ, true_and] using hi
    exact hnot (Finset.mem_union_left _ hmem)
  -- 3: `2 ≤ b₀` (hence `0 < b₀`); every side length is `≥ 2`.
  have hb₀_two : 2 ≤ b₀ := by
    rw [hb₀]
    apply Finset.le_inf'
    intro i _
    exact hb i
  have hb₀_pos : 0 < b₀ := by omega
  -- 4: the shrunk box — the `R`-coordinates are restricted to `{0, …, b₀ - 1}`.
  let Shrunk : Finset (Parallelotope ι b) :=
    Finset.univ.filter (fun y => ∀ i ∈ R, (y i).val < b₀)
  have mem_Shrunk : ∀ y : Parallelotope ι b,
      y ∈ Shrunk ↔ ∀ i ∈ R, (y i).val < b₀ := by
    intro y
    simp only [Shrunk, Finset.mem_filter, Finset.mem_univ, true_and]
  -- 5: the truncated cell `Ŷ = Y ∩ Shrunk`.
  let HatCell : Cell ι b → Finset (Parallelotope ι b) :=
    fun Y => Y.toFinset ∩ Shrunk
  -- 6: the distinguished cell `X` lies entirely inside the shrunk box.  This is
  -- exactly where the normalization hypothesis `hX_zero` is used: on the fixed
  -- coordinates `R`, `X`'s value is `0 < b₀`.
  have hX_sub : X.toFinset ⊆ Shrunk := by
    intro y hy
    rw [Cell.mem_toFinset] at hy
    rw [mem_Shrunk]
    intro i hi
    have hyi : y i = X.fixedVals i := hy i (hR_fixed_X i hi)
    rw [hyi, hX_zero i hi]
    exact hb₀_pos
  -- 7: hence `X` is untouched by the truncation.
  have hHatX : HatCell X = X.toFinset := by
    change X.toFinset ∩ Shrunk = X.toFinset
    exact Finset.inter_eq_left.mpr hX_sub
  -- 8: `|HatCell X| = X.size` (the full cell cardinality).
  have hHatX_card : (HatCell X).card = X.size := by
    rw [hHatX, Cell.card_toFinset]
  -- 9: every truncated cell has at most its full size.
  have hHat_le : ∀ Y : Cell ι b, (HatCell Y).card ≤ Y.size := by
    intro Y
    calc (HatCell Y).card ≤ Y.toFinset.card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = Y.size := Cell.card_toFinset Y
  -- ===== Congruence-class setup =====
  -- 1: the class value of a point is the sum of its `R`-coordinates mod `b₀`.
  let classVal : Parallelotope ι b → ℕ :=
    fun y => (∑ i ∈ R, (y i).val) % b₀
  have classVal_lt : ∀ y : Parallelotope ι b, classVal y < b₀ := by
    intro y
    exact Nat.mod_lt _ hb₀_pos
  -- 2: the `b₀` congruence classes, indexed by `Fin b₀`, partition `Shrunk`.
  let G : Fin b₀ → Finset (Parallelotope ι b) :=
    fun k => Shrunk.filter (fun y => classVal y = k.val)
  have mem_G : ∀ (k : Fin b₀) (y : Parallelotope ι b),
      y ∈ G k ↔ y ∈ Shrunk ∧ classVal y = k.val := by
    intro k y
    simp [G]
  -- 3: every point of `Shrunk` lies in its own class.
  have mem_G_self : ∀ {y : Parallelotope ι b} (hy : y ∈ Shrunk),
      y ∈ G ⟨classVal y, classVal_lt y⟩ := by
    intro y hy
    rw [mem_G]
    exact ⟨hy, rfl⟩
  -- 4: distinct classes are disjoint.
  have G_disjoint : ∀ k l : Fin b₀, k ≠ l → Disjoint (G k) (G l) := by
    intro k l hkl
    rw [Finset.disjoint_left]
    intro y hyk hyl
    rw [mem_G] at hyk hyl
    have hval : k.val = l.val := by
      rw [← hyk.2, hyl.2]
    exact hkl (Fin.ext hval)
  -- 5: each class is contained in `Shrunk`.
  have G_subset_Shrunk : ∀ k : Fin b₀, G k ⊆ Shrunk := by
    intro k y hy
    rw [mem_G] at hy
    exact hy.1
  -- ===== Partition-counting facts for the classes =====
  -- Coverage: every point of `Shrunk` lies in some class.
  have G_cover : ∀ {y : Parallelotope ι b}, y ∈ Shrunk → ∃ k : Fin b₀, y ∈ G k := by
    intro y hy
    exact ⟨⟨classVal y, classVal_lt y⟩, mem_G_self hy⟩
  -- Uniqueness of the class.
  have G_unique : ∀ {y : Parallelotope ι b} {k l : Fin b₀},
      y ∈ G k → y ∈ G l → k = l := by
    intro y k l hyk hyl
    rw [mem_G] at hyk hyl
    apply Fin.ext
    rw [← hyk.2, hyl.2]
  -- Exactly one class: `Shrunk` is partitioned by the `G k`.
  have G_existsUnique :
      ∀ {y : Parallelotope ι b}, y ∈ Shrunk → ∃! k : Fin b₀, y ∈ G k := by
    intro y hy
    refine ⟨⟨classVal y, classVal_lt y⟩, mem_G_self hy, ?_⟩
    intro k hk
    exact G_unique (y := y) hk (mem_G_self hy)
  -- Counting by classes: summing `|A ∩ G k|` over `k` recovers `|A ∩ Shrunk|`.
  have sum_inter_G_eq_inter_Shrunk :
      ∀ A : Finset (Parallelotope ι b),
        (∑ k : Fin b₀, (A ∩ G k).card) = (A ∩ Shrunk).card := by
    intro A
    -- Write each `|A ∩ G k|` as an indicator sum over `A ∩ Shrunk` (uses
    -- `G k ⊆ Shrunk`).
    have step1 : ∀ k : Fin b₀,
        (A ∩ G k).card = ∑ y ∈ A ∩ Shrunk, (if y ∈ G k then 1 else 0) := by
      intro k
      rw [← Finset.card_filter]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨hyA, hyG⟩
        exact ⟨⟨hyA, G_subset_Shrunk k hyG⟩, hyG⟩
      · rintro ⟨⟨hyA, _hyS⟩, hyG⟩
        exact ⟨hyA, hyG⟩
    calc (∑ k : Fin b₀, (A ∩ G k).card)
        = ∑ k : Fin b₀, ∑ y ∈ A ∩ Shrunk, (if y ∈ G k then 1 else 0) :=
          Finset.sum_congr rfl (fun k _ => step1 k)
      _ = ∑ y ∈ A ∩ Shrunk, ∑ k : Fin b₀, (if y ∈ G k then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ y ∈ A ∩ Shrunk, 1 := by
          -- For each point, exactly one class contains it (`G_existsUnique`).
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mem_inter] at hy
          obtain ⟨k₀, hk₀, hk₀_uniq⟩ := G_existsUnique hy.2
          rw [← Finset.card_filter]
          have hsingle :
              (Finset.univ.filter (fun k : Fin b₀ => y ∈ G k)) = {k₀} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hk₀⟩
            · intro k hk
              rw [Finset.mem_filter] at hk
              exact hk₀_uniq k hk.2
          rw [hsingle, Finset.card_singleton]
      _ = (A ∩ Shrunk).card := by simp
  -- ===== shift machinery (general coordinate `c ∈ R`) =====
  -- We relabel one chosen coordinate `c ∈ R` by a cyclic shift (mod `b₀`),
  -- which changes the class value by the shift amount while staying in `Shrunk`.
  have hb₀_le : ∀ c ∈ R, b₀ ≤ b c := fun c hc => by rw [hb₀]; exact Finset.inf'_le b hc
  let shift : (c : ι) → c ∈ R → ℕ → Parallelotope ι b → Parallelotope ι b :=
    fun c hc δ y => Function.update y c
      ⟨((y c).val + δ) % b₀, lt_of_lt_of_le (Nat.mod_lt _ hb₀_pos) (hb₀_le c hc)⟩
  -- a `Nat` round-trip fact.
  have round : ∀ (v δ δ' : ℕ), v < b₀ → (δ + δ') % b₀ = 0 →
      ((v + δ) % b₀ + δ') % b₀ = v := by
    intro v δ δ' hv hδ
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_mod, hδ, Nat.add_zero,
        Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv]
  -- shifting changes the class value by `δ` (mod `b₀`).
  have classVal_shift : ∀ (c : ι) (hc : c ∈ R) (δ : ℕ) (y : Parallelotope ι b),
      classVal (shift c hc δ y) = (classVal y + δ) % b₀ := by
    intro c hc δ y
    -- on coordinates `≠ c`, `shift` does nothing.
    have hrest : ∀ i ∈ R.erase c, ((shift c hc δ y) i).val = (y i).val := by
      intro i hi_mem
      have hi_ne : i ≠ c := Finset.ne_of_mem_erase hi_mem
      have hupd : (shift c hc δ y) i = y i := by simp [shift, hi_ne]
      rw [hupd]
    -- split the sum off coordinate `c`.
    have hsum : (∑ i ∈ R, ((shift c hc δ y) i).val)
        = ((y c).val + δ) % b₀ + ∑ i ∈ R.erase c, (y i).val := by
      rw [← Finset.add_sum_erase R (fun i => ((shift c hc δ y) i).val) hc]
      congr 1
      · simp [shift]
      · exact Finset.sum_congr rfl hrest
    have hsum2 : (∑ i ∈ R, (y i).val) = (y c).val + ∑ i ∈ R.erase c, (y i).val :=
      (Finset.add_sum_erase R (fun i => (y i).val) hc).symm
    change (∑ i ∈ R, ((shift c hc δ y) i).val) % b₀
        = ((∑ i ∈ R, (y i).val) % b₀ + δ) % b₀
    rw [hsum, hsum2, Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    ring
  -- shifting preserves `Shrunk`.
  have shift_mem : ∀ (c : ι) (hc : c ∈ R) (δ : ℕ) (y : Parallelotope ι b),
      y ∈ Shrunk → shift c hc δ y ∈ Shrunk := by
    intro c hc δ y hy
    rw [mem_Shrunk] at hy ⊢
    intro i hi
    by_cases h : i = c
    · have hval : ((shift c hc δ y) i).val = ((y c).val + δ) % b₀ := by
        rw [h]; simp [shift]
      rw [hval]; exact Nat.mod_lt _ hb₀_pos
    · have hval : (shift c hc δ y) i = y i := by simp [shift, h]
      rw [hval]; exact hy i hi
  -- the round-trip on `Shrunk`.
  have shift_round : ∀ (c : ι) (hc : c ∈ R) (δ δ' : ℕ) (y : Parallelotope ι b),
      y ∈ Shrunk → (δ + δ') % b₀ = 0 → shift c hc δ' (shift c hc δ y) = y := by
    intro c hc δ δ' y hy hsum
    have hvc : (y c).val < b₀ := (mem_Shrunk y).mp hy c hc
    funext i
    by_cases hi : i = c
    · apply Fin.ext
      have hval : ((shift c hc δ' (shift c hc δ y)) i).val
          = (((y c).val + δ) % b₀ + δ') % b₀ := by rw [hi]; simp [shift]
      rw [hval, hi]
      exact round (y c).val δ δ' hvc hsum
    · simp [shift, hi]
  -- shifting a free coordinate of `Y` preserves membership in `Y`.
  have shift_mem_cell : ∀ (c : ι) (hc : c ∈ R) (δ : ℕ) (Y : Cell ι b),
      c ∈ Y.freeIdx → ∀ y, Y.Mem y → Y.Mem (shift c hc δ y) := by
    intro c hc δ Y hc_free y hy i hi
    have hi_ne : i ≠ c := by rintro rfl; exact hi hc_free
    have hval : (shift c hc δ y) i = y i := by simp [shift, hi_ne]
    rw [hval]; exact hy i hi
  -- ===== Equal cardinality of the classes =====
  -- Biject `G k` with `G l` by shifting one coordinate `r ∈ R` (`k → l`).
  have G_card_eq : ∀ k l : Fin b₀, (G k).card = (G l).card := by
    intro k l
    obtain ⟨r, hr⟩ := hR
    have hk : k.val < b₀ := k.isLt
    have hl : l.val < b₀ := l.isLt
    set δ := b₀ - k.val + l.val with hδ_def
    set δ' := b₀ - l.val + k.val with hδ'_def
    have hsum0 : (δ + δ') % b₀ = 0 := by
      have h2b : δ + δ' = 2 * b₀ := by rw [hδ_def, hδ'_def]; omega
      rw [h2b]; exact Nat.mul_mod_left 2 b₀
    have hsum0' : (δ' + δ) % b₀ = 0 := by rw [Nat.add_comm]; exact hsum0
    refine Finset.card_nbij' (shift r hr δ) (shift r hr δ') ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, mem_G] at hy ⊢
      refine ⟨shift_mem r hr δ y hy.1, ?_⟩
      rw [classVal_shift r hr δ y, hy.2, hδ_def]
      have heq : k.val + (b₀ - k.val + l.val) = b₀ + l.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hl]
    · intro y hy
      simp only [Finset.mem_coe, mem_G] at hy ⊢
      refine ⟨shift_mem r hr δ' y hy.1, ?_⟩
      rw [classVal_shift r hr δ' y, hy.2, hδ'_def]
      have heq : l.val + (b₀ - l.val + k.val) = b₀ + k.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
    · intro y hy
      simp only [Finset.mem_coe, mem_G] at hy
      exact shift_round r hr δ δ' y hy.1 hsum0
    · intro y hy
      simp only [Finset.mem_coe, mem_G] at hy
      exact shift_round r hr δ' δ y hy.1 hsum0'
  -- ===== Bad-cell equidistribution =====
  -- A cell `Y` whose free set is not contained in `U` meets every class equally:
  -- it has a free coordinate `c ∈ R`, and shifting `c` permutes the classes
  -- while fixing `Y` (as `c` is free for `Y`).
  have bad_equidist : ∀ (Y : Cell ι b), ¬ Y.freeIdx ⊆ U →
      ∀ k l : Fin b₀, (Y.toFinset ∩ G k).card = (Y.toFinset ∩ G l).card := by
    intro Y hY_bad k l
    obtain ⟨c, hc_free, hc_notU⟩ := Finset.not_subset.mp hY_bad
    have hc_R : c ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hc_notU⟩
    have hk : k.val < b₀ := k.isLt
    have hl : l.val < b₀ := l.isLt
    set δ := b₀ - k.val + l.val with hδ_def
    set δ' := b₀ - l.val + k.val with hδ'_def
    have hsum0 : (δ + δ') % b₀ = 0 := by
      have h2b : δ + δ' = 2 * b₀ := by rw [hδ_def, hδ'_def]; omega
      rw [h2b]; exact Nat.mul_mod_left 2 b₀
    have hsum0' : (δ' + δ) % b₀ = 0 := by rw [Nat.add_comm]; exact hsum0
    refine Finset.card_nbij' (shift c hc_R δ) (shift c hc_R δ') ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_inter, Cell.mem_toFinset, mem_G] at hy ⊢
      obtain ⟨hyY, hyS, hyk⟩ := hy
      refine ⟨shift_mem_cell c hc_R δ Y hc_free y hyY,
              shift_mem c hc_R δ y hyS, ?_⟩
      rw [classVal_shift c hc_R δ y, hyk, hδ_def]
      have heq : k.val + (b₀ - k.val + l.val) = b₀ + l.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hl]
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_inter, Cell.mem_toFinset, mem_G] at hy ⊢
      obtain ⟨hyY, hyS, hyl⟩ := hy
      refine ⟨shift_mem_cell c hc_R δ' Y hc_free y hyY,
              shift_mem c hc_R δ' y hyS, ?_⟩
      rw [classVal_shift c hc_R δ' y, hyl, hδ'_def]
      have heq : l.val + (b₀ - l.val + k.val) = b₀ + k.val := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_inter, Cell.mem_toFinset, mem_G] at hy
      exact shift_round c hc_R δ δ' y hy.2.1 hsum0
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_inter, Cell.mem_toFinset, mem_G] at hy
      exact shift_round c hc_R δ' δ y hy.2.1 hsum0'
  -- ===== Final mass count =====
  -- The good cells (free set `⊆ U`) are the ones in the target sum.
  set good : Finset (Cell ι b) :=
    P.cells.filter (fun Y => Y.freeIdx ⊆ X.freeIdx ∪ S) with hgood_def
  set bad : Finset (Cell ι b) :=
    P.cells.filter (fun Y => ¬ Y.freeIdx ⊆ X.freeIdx ∪ S) with hbad_def
  -- By normalization (`hX_zero`), `X` sits entirely in class `0`.
  let c0 : Fin b₀ := ⟨0, hb₀_pos⟩
  have hX_class0 : ∀ y ∈ X.toFinset, classVal y = 0 := by
    intro y hy
    rw [Cell.mem_toFinset] at hy
    have hsum0 : (∑ i ∈ R, (y i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hyi : y i = X.fixedVals i := hy i (hR_fixed_X i hi)
      rw [hyi]; exact hX_zero i hi
    change (∑ i ∈ R, (y i).val) % b₀ = 0
    rw [hsum0]; exact Nat.zero_mod b₀
  have hX_sub_G0 : X.toFinset ⊆ G c0 := by
    intro y hy
    rw [mem_G]
    exact ⟨hX_sub hy, hX_class0 y hy⟩
  have hXG0_card : (X.toFinset ∩ G c0).card = X.size := by
    rw [Finset.inter_eq_left.mpr hX_sub_G0, Cell.card_toFinset]
  have hX_good : X ∈ good := by
    rw [hgood_def, Finset.mem_filter]
    exact ⟨hX, Finset.subset_union_left⟩
  -- Class `0` gets at least `|X|` from the good cells.
  have hm_c0_ge : X.size ≤ ∑ Y ∈ good, (Y.toFinset ∩ G c0).card := by
    rw [← hXG0_card]
    exact Finset.single_le_sum (f := fun Y => (Y.toFinset ∩ G c0).card)
      (fun Y _ => Nat.zero_le _) hX_good
  -- Per class: good mass + bad mass = class size.
  have hsplit : ∀ k : Fin b₀, (∑ Y ∈ good, (Y.toFinset ∩ G k).card)
      + (∑ Y ∈ bad, (Y.toFinset ∩ G k).card) = (G k).card := by
    intro k
    rw [hgood_def, hbad_def, Finset.sum_filter_add_sum_filter_not]
    exact P.sum_inter_card (G k)
  -- Bad mass is the same in every class (bad-cell equidistribution).
  have hbadm_const : ∀ k : Fin b₀, (∑ Y ∈ bad, (Y.toFinset ∩ G k).card)
      = ∑ Y ∈ bad, (Y.toFinset ∩ G c0).card := by
    intro k
    apply Finset.sum_congr rfl
    intro Y hY
    rw [hbad_def, Finset.mem_filter] at hY
    exact bad_equidist Y hY.2 k c0
  -- Hence good mass is the same in every class.
  have hm_const : ∀ k : Fin b₀, (∑ Y ∈ good, (Y.toFinset ∩ G k).card)
      = ∑ Y ∈ good, (Y.toFinset ∩ G c0).card := by
    intro k
    have h1 := hsplit k
    have h2 := hsplit c0
    have h3 := G_card_eq k c0
    have h4 := hbadm_const k
    omega
  -- Sum the (constant) good mass over all `b₀` classes.
  have hsum_m : (∑ k : Fin b₀, ∑ Y ∈ good, (Y.toFinset ∩ G k).card)
      = b₀ * (∑ Y ∈ good, (Y.toFinset ∩ G c0).card) := by
    rw [Finset.sum_congr rfl (fun k _ => hm_const k), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  calc b₀ * X.size
      ≤ b₀ * (∑ Y ∈ good, (Y.toFinset ∩ G c0).card) := Nat.mul_le_mul (le_refl b₀) hm_c0_ge
    _ = ∑ k : Fin b₀, ∑ Y ∈ good, (Y.toFinset ∩ G k).card := hsum_m.symm
    _ = ∑ Y ∈ good, ∑ k : Fin b₀, (Y.toFinset ∩ G k).card := Finset.sum_comm
    _ = ∑ Y ∈ good, (Y.toFinset ∩ Shrunk).card := by
        apply Finset.sum_congr rfl
        intro Y _
        exact sum_inter_G_eq_inter_Shrunk Y.toFinset
    _ ≤ ∑ Y ∈ good, Y.size := by
        apply Finset.sum_le_sum
        intro Y _
        exact hHat_le Y

/-- **Cell inequality** (Berger–Felzenbaum–Fraenkel, Proposition I).

    `∑_{freeIdx Xⱼ ⊆ freeIdx X ∪ S} |Xⱼ| ≥ b₀ · |X|`, where
    `b₀ = min_{i ∈ R} b i` and `R = ι \ (freeIdx X ∪ S) ≠ ∅`.

    Derived from `cell_inequality_normalized` by normalization: relabel the
    parallelotope by `normalizeEquiv hb X R` (a coordinatewise swap sending `X`'s
    fixed values to zero on `R`), apply the normalized inequality to the
    relabelled partition `P.map e` and cell `X.map e` (zero on `R` by
    `normalize_fixedVals_eq_zero`), then transport the right-hand sum back to `P`
    via `CellPartition.map_good_sum_size` (relabelling preserves cell sizes and
    the "good" filter, since `(X.map e).freeIdx = X.freeIdx`). -/
theorem cell_inequality
    (hb : ∀ i : ι, 2 ≤ b i)
    (P : CellPartition ι b) (X : Cell ι b) (hX : X ∈ P.cells)
    (S : Finset ι) {b₀ : ℕ}
    -- (hS : S ⊆ Finset.univ \ X.freeIdx)
    (hR : (Finset.univ \ (X.freeIdx ∪ S)).Nonempty)
    (hb₀ : b₀ = (Finset.univ \ (X.freeIdx ∪ S)).inf' hR b) :
    b₀ * X.size ≤
      ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ S), Xⱼ.size := by
  -- Relabel the parallelotope so that `X` becomes zero on `R = ι \ (freeIdx X ∪ S)`.
  let R : Finset ι := Finset.univ \ (X.freeIdx ∪ S)
  let e : ∀ i : ι, Fin (b i) ≃ Fin (b i) := normalizeEquiv hb X R
  -- After relabelling, the distinguished cell `X.map e` is zero on `R`
  -- (`X.map e` and `X` share `freeIdx`, so `R` is unchanged).
  have hX_zero' : ∀ i ∈ Finset.univ \ ((X.map e).freeIdx ∪ S),
      ((X.map e).fixedVals i).val = 0 := by
    intro i hi
    rw [Cell.map_freeIdx] at hi
    exact normalize_fixedVals_eq_zero hb X R hi
  -- Apply the normalized inequality to the relabelled partition.  `hS`, `hR`,
  -- `hb₀` transfer unchanged since `(X.map e).freeIdx = X.freeIdx`.
  have key := cell_inequality_normalized (b₀ := b₀) hb (P.map e) (X.map e)
    (CellPartition.map_cell_mem P e hX) S hR hb₀ hX_zero'
  -- Transport back: sizes and the "good" filter are preserved by relabelling.
  simp only [Cell.map_freeIdx, Cell.map_size] at key
  rwa [CellPartition.map_good_sum_size P e (X.freeIdx ∪ S)] at key

/-! ### Two corollaries of the cell inequality

These are the two specializations of `cell_inequality` used downstream, recorded
exactly as in the paper (corollaries following Proposition I).  The first takes
`S = ∅`: with `b₁(X) = min{bᵢ : i ∉ freeIdx X}`, the cells whose free set is
contained in `freeIdx X` carry mass at least `b₁(X) · |X|`. -/

/-- **Corollary `cor:bff-prop1-including`** (the `S = ∅` case of
    `cell_inequality`).  With `b₁ = min{bᵢ : i ∉ freeIdx X}`,
    `∑_{freeIdx Xⱼ ⊆ freeIdx X} |Xⱼ| ≥ b₁ · |X|`.

    This recovers the formulation of the cell inequality in `[BFF, §2]`.  It is a
    direct consequence of the general inequality: `S = ∅` makes
    `freeIdx X ∪ S = freeIdx X`, so the "remaining" coordinates are exactly
    `i ∉ freeIdx X` and the minimum side length there is `b₁`. -/
theorem cell_inequality_including
    (hb : ∀ i : ι, 2 ≤ b i)
    (P : CellPartition ι b) (X : Cell ι b) (hX : X ∈ P.cells)
    (hR : (Finset.univ \ X.freeIdx).Nonempty)
    {b₁ : ℕ} (hb₁ : b₁ = (Finset.univ \ X.freeIdx).inf' hR b) :
    b₁ * X.size ≤
      ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx), Xⱼ.size := by
  -- Feed `S = ∅` into the general inequality; `freeIdx X ∪ ∅ = freeIdx X`.
  have hRunion : (Finset.univ \ (X.freeIdx ∪ ∅)).Nonempty := by
    rwa [Finset.union_empty]
  have hb₀ : b₁ = (Finset.univ \ (X.freeIdx ∪ ∅)).inf' hRunion b := by
    rw [hb₁]; apply Finset.inf'_congr <;> simp
  have key := cell_inequality hb P X hX ∅ (b₀ := b₁) hRunion hb₀
  simpa using key

/-- **Corollary `cor:bff-prop1-including`, excluding form.**  Equivalently to
    `cell_inequality_including`, separating off `X` itself:
    `∑_{freeIdx Xⱼ ⊆ freeIdx X, Xⱼ ≠ X} |Xⱼ| ≥ (b₁ - 1) · |X|`. -/
theorem cell_inequality_excluding
    (hb : ∀ i : ι, 2 ≤ b i)
    (P : CellPartition ι b) (X : Cell ι b) (hX : X ∈ P.cells)
    (hR : (Finset.univ \ X.freeIdx).Nonempty)
    {b₁ : ℕ} (hb₁ : b₁ = (Finset.univ \ X.freeIdx).inf' hR b) :
    (b₁ - 1) * X.size ≤
      ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∧ Xⱼ ≠ X), Xⱼ.size := by
  have hincl := cell_inequality_including hb P X hX hR hb₁
  -- `X` lies in the "including" sum (its free set is trivially `⊆` itself).
  have hXmem : X ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx) := by
    simp only [Finset.mem_filter]
    exact ⟨hX, Finset.Subset.refl _⟩
  -- Erasing `X` from the "including" index set gives the "excluding" one.
  have hset : (P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx)).erase X
      = P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∧ Xⱼ ≠ X) := by
    ext Y
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  have hsplit : ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx), Xⱼ.size
      = X.size + ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∧ Xⱼ ≠ X),
          Xⱼ.size := by
    rw [← Finset.add_sum_erase _ _ hXmem, hset]
  -- `(b₁ - 1) · |X| = b₁ · |X| - |X|`, and `b₁ · |X| ≤ |X| + (excluding sum)`.
  rw [Nat.sub_one_mul]
  omega

/-! The second corollary takes `S = F₁(X)`, the set of *minimal* fixed
coordinates of `X` (those `i ∉ freeIdx X` whose side length equals
`b₁(X) = min{bᵢ : i ∉ freeIdx X}`).  Absorbing those coordinates into the cell
lets the inequality "see" the next side length `b₂(X)`.  This is the structural
flexibility used later to keep inductions uniform when the smallest prime is
`2`. -/

/-- **Corollary `cor:two-level-variant`** (the `S = F₁(X)` case of
    `cell_inequality`).

    With `b₁ = min{bᵢ : i ∉ freeIdx X}`, let `F₁` be the *minimal fixed
    coordinates* `{i ∉ freeIdx X : bᵢ = b₁}`.  If coordinates remain outside
    `freeIdx X ∪ F₁`, let `b₂ = min{bᵢ : i ∉ freeIdx X ∪ F₁}` be the next side
    length.  Then
    `∑_{freeIdx Xⱼ ⊆ freeIdx X ∪ F₁} |Xⱼ| ≥ b₂ · |X|`.

    Since `F₁` is a set of fixed coordinates of `X`, this is an immediate
    instance of `cell_inequality` with `S = F₁`. -/
theorem cell_inequality_two_level
    (hb : ∀ i : ι, 2 ≤ b i)
    (P : CellPartition ι b) (X : Cell ι b) (hX : X ∈ P.cells)
    (hR₁ : (Finset.univ \ X.freeIdx).Nonempty)
    {b₁ : ℕ} (_hb₁ : b₁ = (Finset.univ \ X.freeIdx).inf' hR₁ b)
    (F₁ : Finset ι)
    (hR₂ : (Finset.univ \ (X.freeIdx ∪ F₁)).Nonempty)
    {b₂ : ℕ} (hb₂ : b₂ = (Finset.univ \ (X.freeIdx ∪ F₁)).inf' hR₂ b) :
    b₂ * X.size ≤
      ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁), Xⱼ.size := by
  -- `hb₁` only fixes the meaning of `b₁` (hence `F₁`); consume it so it is "used".
  exact cell_inequality hb P X hX F₁ (b₀ := b₂) hR₂ hb₂

/-- **Corollary `cor:two-level-variant`, excluding form.**  Equivalently to
    `cell_inequality_two_level`, separating off `X` itself:
    `∑_{freeIdx Xⱼ ⊆ freeIdx X ∪ F₁, Xⱼ ≠ X} |Xⱼ| ≥ (b₂ - 1) · |X|`. -/
theorem cell_inequality_two_level_excluding
    (hb : ∀ i : ι, 2 ≤ b i)
    (P : CellPartition ι b) (X : Cell ι b) (hX : X ∈ P.cells)
    (hR₁ : (Finset.univ \ X.freeIdx).Nonempty)
    {b₁ : ℕ} (hb₁ : b₁ = (Finset.univ \ X.freeIdx).inf' hR₁ b)
    (F₁ : Finset ι)
    (hR₂ : (Finset.univ \ (X.freeIdx ∪ F₁)).Nonempty)
    {b₂ : ℕ} (hb₂ : b₂ = (Finset.univ \ (X.freeIdx ∪ F₁)).inf' hR₂ b) :
    (b₂ - 1) * X.size ≤
      ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁ ∧ Xⱼ ≠ X), Xⱼ.size := by
  have hincl := cell_inequality_two_level hb P X hX hR₁ hb₁ F₁ hR₂ hb₂
  have hXmem : X ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁) := by
    simp only [Finset.mem_filter]
    exact ⟨hX, Finset.subset_union_left⟩
  have hset : (P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁)).erase X
      = P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁ ∧ Xⱼ ≠ X) := by
    ext Y
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  have hsplit : ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁), Xⱼ.size
      = X.size + ∑ Xⱼ ∈ P.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ X.freeIdx ∪ F₁ ∧ Xⱼ ≠ X),
          Xⱼ.size := by
    rw [← Finset.add_sum_erase _ _ hXmem, hset]
  rw [Nat.sub_one_mul]
  omega

end DCS.Box

/-! # Number-theoretic specialization: the parallelotope map

We now specialize the general parallelotope to an integer `n`.  The coordinate
set is `PrimeCoord n` — pairs `(p, k)` of a prime factor `p ∣ n` and an index
`k < ν_p(n)` — and the side length at coordinate `c` is `c.prime`.

The centerpiece is the **parallelotope map** `equivZMod : ZMod n ≃ PrimeParallelotope n`,
the Berger–Felzenbaum–Fraenkel identification of `ℤ/nℤ` with the prime
parallelotope.  Per the paper, it is the composite of three standard pieces, each
taken from mathlib:

* `ZMod.equivPi` — the Chinese Remainder Theorem `ℤ/nℤ ≃ ∏_p ℤ/p^{ν_p}ℤ`;
* `finFunctionFinEquiv` — the base-`p` digit expansion `ℤ/p^kℤ ≃ (Fin k → Fin p)`;
* `PrimeCoord.equivSigma` — reindexing `∏_p (Fin ν_p → Fin p)` to `∀ c, Fin c.prime`.

Because it is assembled from `Equiv`s, `equivZMod` is a genuine bijection with no
`sorry`. -/

namespace DCS

open Finset

variable {n : ℕ}

/-- A coordinate in the parallelotope: a prime factor `p` of `n` together
    with an index `k ∈ {0, ..., ν_p(n) - 1}`. -/
structure PrimeCoord (n : ℕ) where
  /-- The prime `p`. -/
  prime : ℕ
  /-- `p` is a prime factor of `n`. -/
  isPrimeFactor : prime ∈ n.primeFactors
  /-- The digit position `k`. -/
  index : ℕ
  /-- `k < ν_p(n)`. -/
  index_lt : index < n.factorization prime

namespace PrimeCoord

/-- The `prime` field of a `PrimeCoord` is itself a prime number. -/
lemma prime_prime (c : PrimeCoord n) : c.prime.Prime :=
  Nat.prime_of_mem_primeFactors c.isPrimeFactor

/-- The `prime` field is positive. -/
lemma prime_pos (c : PrimeCoord n) : 0 < c.prime := c.prime_prime.pos

/-- The `prime` field is at least 2. -/
lemma prime_two_le (c : PrimeCoord n) : 2 ≤ c.prime := c.prime_prime.two_le

/-- Two coordinates are equal iff their `prime` and `index` fields are equal. -/
@[ext]
lemma ext {c₁ c₂ : PrimeCoord n}
    (h_prime : c₁.prime = c₂.prime) (h_index : c₁.index = c₂.index) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

instance : DecidableEq (PrimeCoord n) := fun c₁ c₂ => by
  by_cases hp : c₁.prime = c₂.prime
  · by_cases hi : c₁.index = c₂.index
    · exact .isTrue (PrimeCoord.ext hp hi)
    · exact .isFalse (fun h => hi (by rw [h]))
  · exact .isFalse (fun h => hp (by rw [h]))

/-- Equivalence to a `Σ`-type, useful for transferring `Fintype` etc. and for
    reindexing the parallelotope map. -/
def equivSigma : PrimeCoord n ≃ Σ p : n.primeFactors, Fin (n.factorization p.val) where
  toFun c := ⟨⟨c.prime, c.isPrimeFactor⟩, ⟨c.index, c.index_lt⟩⟩
  invFun s := ⟨s.fst.val, s.fst.property, s.snd.val, s.snd.isLt⟩
  left_inv c := by cases c; rfl
  right_inv s := by rcases s with ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

instance : Fintype (PrimeCoord n) := Fintype.ofEquiv _ equivSigma.symm

/-- The `c.index`-th digit in base `c.prime` of `x.val`, viewed as a `Fin c.prime`. -/
def digit (c : PrimeCoord n) (x : ZMod n) : Fin c.prime :=
  ⟨(x.val / c.prime ^ c.index) % c.prime, Nat.mod_lt _ c.prime_pos⟩

end PrimeCoord

/-- The parallelotope attached to `n`, as the **special case** of the general
    `DCS.Box.Parallelotope` with coordinate set `PrimeCoord n` and side length
    `c.prime` at coordinate `c`. -/
abbrev PrimeParallelotope (n : ℕ) : Type :=
  Box.Parallelotope (PrimeCoord n) (fun c => c.prime)

namespace PrimeParallelotope

/-- The forward map `ZMod n → PrimeParallelotope n`: at coordinate `c`, record
    the `c.index`-th base-`c.prime` digit of `x`. -/
def ofZMod (x : ZMod n) : PrimeParallelotope n := fun c => c.digit x

end PrimeParallelotope

/-! ### Cardinality of `PrimeParallelotope n` -/

/-- `∏_c c.prime = n` (for `n > 0`), via the factorization. -/
lemma PrimeCoord.prod_prime_eq (n : ℕ) (hn : n ≠ 0) :
    (∏ c : PrimeCoord n, c.prime) = n := by
  trans (∏ s : (Σ p : n.primeFactors, Fin (n.factorization p.val)), s.fst.val)
  · exact Fintype.prod_equiv PrimeCoord.equivSigma _ _ (fun _ => rfl)
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.prod_pow_primeFactors_factorization hn).symm

/-- The parallelotope has cardinality `n` (for `n > 0`).  Combines the general
    `Box.Parallelotope.card` (`= ∏_c c.prime`) with `PrimeCoord.prod_prime_eq`. -/
lemma PrimeParallelotope.card_eq (n : ℕ) (hn : n ≠ 0) :
    Fintype.card (PrimeParallelotope n) = n := by
  rw [Box.Parallelotope.card]
  exact PrimeCoord.prod_prime_eq n hn

/-! ### The parallelotope map -/

/-- **Per-prime digit expansion** `ℤ/p^kℤ ≃ (Fin k → Fin p)`, assembled from
    `ZMod.finEquiv` (`ℤ/mℤ ≃ Fin m`) and `finFunctionFinEquiv`
    (`(Fin k → Fin p) ≃ Fin (p^k)`). -/
def digitEquiv (p : n.primeFactors) :
    ZMod ((p : ℕ) ^ n.factorization (p : ℕ)) ≃
      (Fin (n.factorization (p : ℕ)) → Fin (p : ℕ)) :=
  haveI : NeZero ((p : ℕ) ^ n.factorization (p : ℕ)) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).pos.ne'⟩
  (ZMod.finEquiv ((p : ℕ) ^ n.factorization (p : ℕ))).symm.toEquiv.trans
    finFunctionFinEquiv.symm

/-- **The parallelotope map** `ZMod n ≃ PrimeParallelotope n`.

    This is the Berger–Felzenbaum–Fraenkel identification of `ℤ/nℤ` with the
    prime parallelotope, built as the composite

      `ZMod n  —CRT→  ∏_p ℤ/p^{ν_p}ℤ  —digits→  ∏_p (Fin ν_p → Fin p)`
      `        —piCurry→  ∀ (Σ p, Fin ν_p), Fin p  —reindex→  ∀ c, Fin c.prime.`

    Being a composite of `Equiv`s, it is automatically a bijection. -/
noncomputable def PrimeParallelotope.equivZMod (hn : n ≠ 0) :
    ZMod n ≃ PrimeParallelotope n :=
  (ZMod.equivPi n hn).toEquiv.trans <|
  (Equiv.piCongrRight (fun p => digitEquiv p)).trans <|
  (Equiv.piCurry (fun (p : n.primeFactors) (_ : Fin (n.factorization (p : ℕ))) =>
      Fin (p : ℕ))).symm.trans <|
  (Equiv.piCongrLeft' (fun c : PrimeCoord n => Fin c.prime) PrimeCoord.equivSigma).symm

/-! ### Bijectivity of the digit map

The structural map `equivZMod` above is a bijection by construction.  The
explicit digit map `ofZMod` (used by the coset/cell bridge) is *also* a
bijection; we prove that directly, by counting, since relating `ofZMod` to
`equivZMod` pointwise would require the (mathlib-unavailable) component formula
for `ZMod.equivPi`.  The two maps coincide, but that identity is not needed. -/

/-- If `a` and `b` have the same base-`p` digits `0, …, e-1`, then `a ≡ b mod p^e`.
    This is the injectivity content of the base-`p` digit expansion. -/
lemma mod_pow_eq_of_digit_eq {p : ℕ} (a b : ℕ) :
    ∀ e : ℕ, (∀ k < e, a / p ^ k % p = b / p ^ k % p) → a % p ^ e = b % p ^ e := by
  intro e
  induction e with
  | zero => intro _; simp [Nat.mod_one]
  | succ e ih =>
    intro h
    have hlow : a % p ^ e = b % p ^ e := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hdig : a / p ^ e % p = b / p ^ e % p := h e (Nat.lt_succ_self e)
    -- `m % p^{e+1} = p^e · (e-th digit of m) + (m % p^e)`, so both pieces match.
    have key : ∀ m : ℕ, m % p ^ (e + 1) = p ^ e * (m / p ^ e % p) + m % p ^ e := by
      intro m
      rw [pow_succ]
      conv_lhs => rw [← Nat.div_add_mod (m % (p ^ e * p)) (p ^ e)]
      rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd m (dvd_mul_right (p ^ e) p)]
    rw [key a, key b, hlow, hdig]

/-- Converse of `mod_pow_eq_of_digit_eq`: congruence mod `p ^ e` determines the
    base-`p` digits `0, …, e-1`. -/
lemma digit_eq_of_mod_pow_eq {p a b e : ℕ} (h : a % p ^ e = b % p ^ e)
    {k : ℕ} (hk : k < e) : a / p ^ k % p = b / p ^ k % p := by
  have hdvd : p ^ (k + 1) ∣ p ^ e := pow_dvd_pow p hk
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_succ,
      ← Nat.mod_mod_of_dvd a hdvd, ← Nat.mod_mod_of_dvd b hdvd, h]

/-- **CRT for congruences**: to prove `a ≡ b [MOD d]` it suffices to prove
    `a ≡ b [MOD p ^ v_p(d)]` for every prime factor `p` of `d`. -/
lemma modEq_of_forall_primePow {d : ℕ} (hd : d ≠ 0) {a b : ℕ}
    (h : ∀ p ∈ d.primeFactors, a ≡ b [MOD p ^ d.factorization p]) :
    a ≡ b [MOD d] := by
  -- Each prime-power congruence, as an ℤ-divisibility.
  have hZ : ∀ p ∈ d.primeFactors, ((p : ℤ) ^ d.factorization p) ∣ ((b : ℤ) - a) := by
    intro p hp
    have hdvd := Nat.modEq_iff_dvd.mp (h p hp)
    rwa [Nat.cast_pow] at hdvd
  -- The prime powers are pairwise coprime over ℤ.
  have hcop : (↑d.primeFactors : Set ℕ).Pairwise
      (fun p q : ℕ =>
        IsCoprime ((p : ℤ) ^ d.factorization p) ((q : ℤ) ^ d.factorization q)) := by
    intro p hp q hq hpq
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq)
    exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpp hqp).mpr hpq)).pow
  have hprod := Finset.prod_dvd_of_coprime
    (s := fun p : ℕ => (p : ℤ) ^ d.factorization p) hcop hZ
  have hd_eq : (∏ p ∈ d.primeFactors, (p : ℤ) ^ d.factorization p) = (d : ℤ) := by
    rw [← Finset.prod_coe_sort d.primeFactors (fun p => (p : ℤ) ^ d.factorization p)]
    exact_mod_cast (Nat.prod_pow_primeFactors_factorization hd).symm
  rw [hd_eq] at hprod
  exact Nat.modEq_iff_dvd.mpr hprod

/-- The forward digit map `ofZMod : ZMod n → PrimeParallelotope n` is **bijective**
    for `n > 0`.

    Both sides have `n` elements (`PrimeParallelotope.card_eq`), so it suffices to
    prove injectivity.  If `ofZMod x = ofZMod y` then `x.val` and `y.val` share all
    base-`p` digits for each prime power `p^{ν_p} ∥ n`; hence they agree mod each
    `p^{ν_p}` (`mod_pow_eq_of_digit_eq`), and — the prime powers being pairwise
    coprime with product `n` — agree mod `n`, so `x.val = y.val` (both `< n`). -/
theorem PrimeParallelotope.ofZMod_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (PrimeParallelotope.ofZMod : ZMod n → PrimeParallelotope n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · -- Injectivity.
    intro x y hxy
    apply ZMod.val_injective n
    set a := x.val with ha
    set b := y.val with hb
    -- Digit equality from `ofZMod x = ofZMod y`.
    have hdig : ∀ c : PrimeCoord n,
        a / c.prime ^ c.index % c.prime = b / c.prime ^ c.index % c.prime := by
      intro c
      have hc := congrFun hxy c
      simpa [PrimeParallelotope.ofZMod, PrimeCoord.digit, Fin.ext_iff] using hc
    -- Per prime power `p^{ν_p}`: `a ≡ b`, recorded as an ℤ divisibility.
    have hZ : ∀ p ∈ n.primeFactors,
        ((p : ℤ) ^ n.factorization p) ∣ ((b : ℤ) - a) := by
      intro p hp
      have hmod : a % p ^ n.factorization p = b % p ^ n.factorization p :=
        mod_pow_eq_of_digit_eq a b (n.factorization p)
          (fun k hk => hdig ⟨p, hp, k, hk⟩)
      have hd := Nat.modEq_iff_dvd.mp (hmod : a ≡ b [MOD p ^ n.factorization p])
      rwa [Nat.cast_pow] at hd
    -- The prime powers are pairwise coprime over ℤ.
    have hcop : (↑n.primeFactors : Set ℕ).Pairwise
        (fun p q : ℕ =>
          IsCoprime ((p : ℤ) ^ n.factorization p) ((q : ℤ) ^ n.factorization q)) := by
      intro p hp q hq hpq
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp)
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq)
      exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpp hqp).mpr hpq)).pow
    -- Combine: `n ∣ (b - a)` in ℤ, hence `a = b` since `a, b < n`.
    have hdvd : (n : ℤ) ∣ ((b : ℤ) - a) := by
      have hprod := Finset.prod_dvd_of_coprime
        (s := fun p : ℕ => (p : ℤ) ^ n.factorization p) hcop hZ
      have hn_eq : (∏ p ∈ n.primeFactors, (p : ℤ) ^ n.factorization p) = (n : ℤ) := by
        rw [← Finset.prod_coe_sort n.primeFactors (fun p => (p : ℤ) ^ n.factorization p)]
        exact_mod_cast (Nat.prod_pow_primeFactors_factorization hn.ne').symm
      rwa [hn_eq] at hprod
    have hab : a ≡ b [MOD n] := Nat.modEq_iff_dvd.mpr hdvd
    have ha' : a < n := ZMod.val_lt x
    have hb' : b < n := ZMod.val_lt y
    calc a = a % n := (Nat.mod_eq_of_lt ha').symm
      _ = b % n := hab
      _ = b := Nat.mod_eq_of_lt hb'
  · -- Cardinality: both sides have `n` elements.
    rw [ZMod.card, PrimeParallelotope.card_eq n hn.ne']

/-! ### Cosets of `ZMod n` -/

/-- A coset in ℤ/nℤ is specified by a residue and a modulus dividing n.
    It represents the set {a, a+d, a+2d, ..., a+(n/d-1)d} mod n,
    which has n/d elements. -/
structure Coset (n : ℕ) where
  /-- A representative of the coset. -/
  residue : ZMod n
  /-- The modulus `d`: the coset is `residue + d·(ℤ/nℤ)`. -/
  modulus : ℕ
  /-- The modulus divides `n`. -/
  modulus_dvd : modulus ∣ n
  /-- The modulus is positive. -/
  modulus_pos : 0 < modulus

/-- The size of a coset -/
def Coset.size {n : ℕ} (K : Coset n) : ℕ := n / K.modulus

/-- A coset's size divides `n`. -/
lemma Coset.size_dvd {n : ℕ} (K : Coset n) : K.size ∣ n :=
  Nat.div_dvd_of_dvd K.modulus_dvd

/-- A coset's size is positive (when `n > 0`). -/
lemma Coset.size_pos {n : ℕ} (K : Coset n) (hn : 0 < n) : 0 < K.size :=
  Nat.div_pos (Nat.le_of_dvd hn K.modulus_dvd) K.modulus_pos

/-- Membership in a coset: `x ∈ K` iff `x = K.residue + k · K.modulus` for some `k`. -/
def Coset.Mem {n : ℕ} (K : Coset n) (x : ZMod n) : Prop :=
  ∃ k : ZMod n, x = K.residue + k * (K.modulus : ZMod n)

instance {n : ℕ} : Membership (ZMod n) (Coset n) where
  mem K x := K.Mem x

instance Coset.decidableMem {n : ℕ} [NeZero n] (K : Coset n) (x : ZMod n) :
    Decidable (x ∈ K) :=
  Fintype.decidableExistsFintype (p := fun k => x = K.residue + k * (K.modulus : ZMod n))

instance Coset.decidableEq {n : ℕ} [DecidableEq (ZMod n)] : DecidableEq (Coset n) :=
  fun K K' =>
    if h_res : K.residue = K'.residue then
      if h_mod : K.modulus = K'.modulus then
        .isTrue (by cases K; cases K'; simp_all)
      else
        .isFalse (fun h => h_mod (by cases h; rfl))
    else
      .isFalse (fun h => h_res (by cases h; rfl))

/-- A coset always contains its residue. -/
lemma Coset.residue_mem {n : ℕ} (K : Coset n) : K.residue ∈ K :=
  ⟨0, by simp⟩

/-- A coset partition of ℤ/nℤ is a list of cosets that disjointly cover ℤ/nℤ.
    - `partition`: size accounting
    - `cover`: each element of ℤ/nℤ lies in exactly one coset (uniqueness of value)
    - `cosets_nodup`: distinct list entries (rules out the same coset appearing twice) -/
structure CosetPartition (n : ℕ) where
  /-- The cosets of the partition. -/
  cosets : List (Coset n)
  /-- The sizes of the cosets add up to `n`. -/
  partition : (cosets.map Coset.size).sum = n
  /-- Each `x : ZMod n` is in *exactly one* coset of the partition. -/
  cover : ∀ x : ZMod n, ∃! K : Coset n, K ∈ cosets ∧ x ∈ K
  /-- The list of cosets has no duplicate entries. -/
  cosets_nodup : cosets.Nodup

/-- The multiset of sizes of a coset partition -/
def CosetPartition.sizes {n : ℕ} (P : CosetPartition n) : Multiset ℕ :=
  (P.cosets.map Coset.size : List ℕ)

/-- Distinct sizes greater than 1 appearing in the partition. -/
def CosetPartition.distinctSizes {n : ℕ} (P : CosetPartition n) : Finset ℕ :=
  ((P.cosets.map Coset.size).toFinset).filter (1 < ·)

/-- Number of "singleton" cosets (cosets of size 1). -/
def CosetPartition.singletonCount {n : ℕ} (P : CosetPartition n) : ℕ :=
  (P.cosets.filter (fun K => K.size = 1)).length

/-! ### Cells (prime specialization)

A cell of the prime parallelotope is just a `DCS.Box.Cell` for the prime model;
its combinatorial `size` and its parallelotope cardinality come from the general
layer.  Here we add the `ZMod n`-side notions (membership and cardinality) that
the coset bridge needs. -/

/-- A cell of the prime parallelotope: the special case of the general
    `DCS.Box.Cell`. -/
abbrev PrimeCell (n : ℕ) : Type :=
  Box.Cell (PrimeCoord n) (fun c => c.prime)

namespace PrimeCell

variable {n : ℕ}

/-- An element `x : ZMod n` lies in a prime cell iff its digits at all fixed
    coordinates match the prescribed values — equivalently, iff `ofZMod x` lies
    in the cell as a parallelotope point (`Box.Cell.Mem`). -/
def containsZMod (X : PrimeCell n) (x : ZMod n) : Prop :=
  X.Mem (PrimeParallelotope.ofZMod x)

instance (X : PrimeCell n) : DecidablePred X.containsZMod := fun _ =>
  Fintype.decidableForallFintype

/-- The Finset of elements of `ZMod n` lying in the cell. -/
def toFinsetZMod (X : PrimeCell n) [NeZero n] : Finset (ZMod n) :=
  Finset.univ.filter X.containsZMod

/-- **Cell cardinality on the `ZMod n` side.**  Assuming `ofZMod` is a bijection
    (`PrimeParallelotope.ofZMod_bijective`), a prime cell contains exactly
    `X.size = ∏_{c ∈ freeIdx} c.prime` elements of `ZMod n`.

    The combinatorial core is the *general*, sorry-free `Box.Cell.card_toFinset`;
    here we merely transport it along the digit bijection. -/
theorem toFinsetZMod_card (X : PrimeCell n) (hn : 0 < n) :
    haveI : NeZero n := ⟨hn.ne'⟩
    X.toFinsetZMod.card = X.size := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Box.Cell.card_toFinset X]
  -- `ofZMod` is a bijection `toFinsetZMod ≃ X.toFinset`, so the cards agree.
  refine Finset.card_bij (fun x _ => PrimeParallelotope.ofZMod x) ?_ ?_ ?_
  · intro x hx
    simp only [toFinsetZMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Box.Cell.mem_toFinset]; exact hx
  · intro x _ y _ h
    exact (PrimeParallelotope.ofZMod_bijective n hn).1 h
  · intro p hp
    rw [Box.Cell.mem_toFinset] at hp
    obtain ⟨x, rfl⟩ := (PrimeParallelotope.ofZMod_bijective n hn).2 p
    refine ⟨x, ?_, rfl⟩
    simp only [toFinsetZMod, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp

end PrimeCell

/-! ### Coset → Cell -/

namespace Coset

variable {n : ℕ}

/-- A coset `K = K.residue + K.modulus·ℤ/nℤ` corresponds to a cell whose
    free coordinates are those `(p, k)` with `k ≥ v_p(K.modulus)` (the "high"
    digits, where elements vary). -/
def toCell (K : Coset n) : PrimeCell n where
  freeIdx := Finset.univ.filter (fun c => K.modulus.factorization c.prime ≤ c.index)
  fixedVals c := c.digit K.residue

/-- The free coordinates of `K.toCell` are characterised by the divisibility
    `c.prime ^ (c.index + 1) ∤ K.modulus` (equivalently, `v_p(K.modulus) ≤ k`). -/
lemma mem_toCell_freeIdx {K : Coset n} {c : PrimeCoord n} :
    c ∈ K.toCell.freeIdx ↔ K.modulus.factorization c.prime ≤ c.index := by
  simp [toCell]

/-- The product of `c.prime` over the "fixed" coordinates of `K.toCell`
    (i.e., those `c` with `c.index < v_p(K.modulus)`) equals `K.modulus`.

    This is the modulus-side analogue of `PrimeCoord.prod_prime_eq`. -/
lemma fixed_prod_eq_modulus (K : Coset n) (hn : 0 < n) :
    (Finset.univ.filter
        (fun c : PrimeCoord n => c.index < K.modulus.factorization c.prime)).prod
          (fun c => c.prime)
      = K.modulus := by
  set d := K.modulus with hd_def
  have hd_pos : 0 < d := K.modulus_pos
  have hd_dvd : d ∣ n := K.modulus_dvd
  have hd_ne : d ≠ 0 := hd_pos.ne'
  rw [Finset.prod_filter]
  trans (∏ s : Σ p : n.primeFactors, Fin (n.factorization p.val),
         if s.snd.val < d.factorization s.fst.val then (s.fst.val : ℕ) else 1)
  · exact Fintype.prod_equiv PrimeCoord.equivSigma _ _ (fun _ => rfl)
  rw [Fintype.prod_sigma]
  -- Inner product: ∏ k : Fin s_p, (if k.val < v_p(d) then p else 1) = p^(v_p(d))
  have h_inner : ∀ p : n.primeFactors,
      (∏ k : Fin (n.factorization p.val),
        if k.val < d.factorization p.val then (p.val : ℕ) else 1)
        = p.val ^ d.factorization p.val := by
    intro p
    have h_le : d.factorization p.val ≤ n.factorization p.val :=
      Nat.factorization_le_factorization_of_dvd_right hd_dvd hd_ne hn.ne'
    rw [Fin.prod_univ_eq_prod_range
         (fun k => if k < d.factorization p.val then (p.val : ℕ) else 1)]
    rw [← Finset.prod_filter]
    rw [show (Finset.range (n.factorization p.val)).filter (· < d.factorization p.val)
           = Finset.range (d.factorization p.val) from ?_]
    · rw [Finset.prod_const, Finset.card_range]
    · ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
  rw [Finset.prod_congr rfl (fun p _ => h_inner p)]
  -- Goal: ∏ p : ↑n.primeFactors, p.val^(d.factorization p.val) = d
  rw [Finset.prod_coe_sort n.primeFactors (fun p => p ^ d.factorization p)]
  -- Goal: ∏ p ∈ n.primeFactors, p ^ d.factorization p = d
  -- Shrink from n.primeFactors to d.primeFactors (extra terms are 1)
  rw [show (∏ p ∈ n.primeFactors, p ^ d.factorization p)
         = ∏ p ∈ d.primeFactors, p ^ d.factorization p from ?_]
  · rw [← Finset.prod_coe_sort d.primeFactors (fun p => p ^ d.factorization p)]
    exact (Nat.prod_pow_primeFactors_factorization hd_ne).symm
  · refine (Finset.prod_subset (Nat.primeFactors_mono hd_dvd hn.ne') ?_).symm
    intro p hp_n hp_d
    rw [Nat.mem_primeFactors] at hp_n
    have hp_not_dvd_d : ¬ p ∣ d := fun h =>
      hp_d (Nat.mem_primeFactors.mpr ⟨hp_n.1, h, hd_ne⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_d]
    simp

/-- `K.toCell.size = K.size`. -/
lemma toCell_size (K : Coset n) (hn : 0 < n) :
    K.toCell.size = K.size := by
  -- Strategy: split univ into freeIdx and its complement; the product over univ
  -- is n, the product over the complement is K.modulus, so the product over
  -- freeIdx is n / K.modulus = K.size.
  have h_disj : Disjoint K.toCell.freeIdx (Finset.univ \ K.toCell.freeIdx) :=
    Finset.disjoint_sdiff
  have h_union : K.toCell.freeIdx ∪ (Finset.univ \ K.toCell.freeIdx) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have h_split : K.toCell.size *
      (Finset.univ \ K.toCell.freeIdx).prod (fun c : PrimeCoord n => c.prime) =
      (∏ c : PrimeCoord n, c.prime) := by
    change K.toCell.freeIdx.prod (fun c => c.prime) *
         (Finset.univ \ K.toCell.freeIdx).prod (fun c => c.prime) = _
    rw [← Finset.prod_union h_disj, h_union]
  -- The complement of `freeIdx` is exactly `{c | c.index < v_p(K.modulus)}`.
  have h_compl_eq : (Finset.univ : Finset (PrimeCoord n)) \ K.toCell.freeIdx =
      Finset.univ.filter (fun c => c.index < K.modulus.factorization c.prime) := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter,
               Coset.mem_toCell_freeIdx, not_le]
  rw [h_compl_eq, K.fixed_prod_eq_modulus hn, PrimeCoord.prod_prime_eq n hn.ne'] at h_split
  -- h_split : K.toCell.size * K.modulus = n
  change K.toCell.size = n / K.modulus
  have := Nat.mul_div_cancel K.toCell.size K.modulus_pos
  -- this : K.toCell.size * K.modulus / K.modulus = K.toCell.size
  rw [h_split] at this
  exact this.symm

/-- `K.modulus.factorization p = 0` when `p ∉ n.primeFactors`. -/
lemma factorization_modulus_eq_zero (K : Coset n) (hn : 0 < n) {p : ℕ}
    (hp_n : p ∉ n.primeFactors) : K.modulus.factorization p = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [Nat.support_factorization]
  intro h
  exact hp_n (Nat.primeFactors_mono K.modulus_dvd hn.ne' h)

/-- **Key correspondence**: `K'.toCell.freeIdx ⊆ K.toCell.freeIdx ↔ K'.size ∣ K.size`.
    Divisibility of cell sizes corresponds to subset of free coordinate sets. -/
lemma toCell_freeIdx_subset_iff {K K' : Coset n} (hn : 0 < n) :
    K'.toCell.freeIdx ⊆ K.toCell.freeIdx ↔ K'.size ∣ K.size := by
  -- The pivot: K'.size ∣ K.size ↔ K.modulus ∣ K'.modulus.
  have h_size_iff : K'.size ∣ K.size ↔ K.modulus ∣ K'.modulus := by
    unfold Coset.size
    refine ⟨?_, fun h => Nat.div_dvd_div_left K'.modulus_dvd h⟩
    intro h_div
    obtain ⟨k, hk⟩ := h_div
    have h1 : K.modulus * (n / K.modulus) = n := Nat.mul_div_cancel' K.modulus_dvd
    have h2 : K'.modulus * (n / K'.modulus) = n := Nat.mul_div_cancel' K'.modulus_dvd
    rw [hk] at h1
    have h_pos : 0 < n / K'.modulus :=
      Nat.div_pos (Nat.le_of_dvd hn K'.modulus_dvd) K'.modulus_pos
    refine ⟨k, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right h_pos
    calc K'.modulus * (n / K'.modulus)
        = n := h2
      _ = K.modulus * (n / K'.modulus * k) := h1.symm
      _ = K.modulus * k * (n / K'.modulus) := by ring
  rw [h_size_iff]
  -- Now show: K'.toCell.freeIdx ⊆ K.toCell.freeIdx ↔ K.modulus ∣ K'.modulus.
  -- Equivalently: ∀ c, v_p(K'.modulus) ≤ c.index → v_p(K.modulus) ≤ c.index
  --              ↔ ∀ p, v_p(K.modulus) ≤ v_p(K'.modulus)
  constructor
  · -- Subset → divisibility of moduli
    intro h_subset
    rw [← Nat.factorization_le_iff_dvd K.modulus_pos.ne' K'.modulus_pos.ne']
    intro p
    -- Case split on whether p ∈ n.primeFactors
    by_cases hp_n : p ∈ n.primeFactors
    · -- For p ∈ n.primeFactors: consider whether v_p(K'.modulus) < n.factorization p
      by_cases h_lt : K'.modulus.factorization p < n.factorization p
      · -- Construct a PrimeCoord c at (p, v_p(K'.modulus)).
        let c : PrimeCoord n := ⟨p, hp_n, K'.modulus.factorization p, h_lt⟩
        have hc' : c ∈ K'.toCell.freeIdx := by
          rw [Coset.mem_toCell_freeIdx]
        have hc : c ∈ K.toCell.freeIdx := h_subset hc'
        rwa [Coset.mem_toCell_freeIdx] at hc
      · -- v_p(K'.modulus) ≥ s_p, but v_p(K.modulus) ≤ s_p, so v_p(K.modulus) ≤ v_p(K'.modulus)
        have h_lt' : n.factorization p ≤ K'.modulus.factorization p := not_lt.mp h_lt
        have h_K_le_n : K.modulus.factorization p ≤ n.factorization p :=
          Nat.factorization_le_factorization_of_dvd_right K.modulus_dvd
            K.modulus_pos.ne' hn.ne'
        omega
    · -- p ∉ n.primeFactors: both factorizations are 0
      rw [K.factorization_modulus_eq_zero hn hp_n,
          K'.factorization_modulus_eq_zero hn hp_n]
  · -- Divisibility of moduli → subset
    intro h_dvd c hc
    rw [Coset.mem_toCell_freeIdx] at hc ⊢
    have h_fact_le : K.modulus.factorization c.prime ≤ K'.modulus.factorization c.prime :=
      Nat.factorization_le_factorization_of_dvd_right h_dvd
        K.modulus_pos.ne' K'.modulus_pos.ne'
    omega

/-! #### Coset ↔ cell correspondence -/

/-- Coset membership in terms of `val`s: `x ∈ K` iff
    `x.val ≡ K.residue.val [MOD K.modulus]`. -/
lemma mem_iff_val_modEq [NeZero n] {K : Coset n} {x : ZMod n} :
    x ∈ K ↔ x.val ≡ K.residue.val [MOD K.modulus] := by
  haveI : NeZero K.modulus := ⟨K.modulus_pos.ne'⟩
  constructor
  · rintro ⟨k, rfl⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    -- Project to `ZMod K.modulus` via the cast homomorphism; `K.modulus ↦ 0` there.
    have hcast : ∀ y : ZMod n,
        ((y.val : ℕ) : ZMod K.modulus)
          = ZMod.castHom K.modulus_dvd (ZMod K.modulus) y := by
      intro y
      rw [ZMod.castHom_apply, ZMod.natCast_val]
    rw [hcast, hcast, map_add, map_mul, map_natCast, ZMod.natCast_self,
        mul_zero, add_zero]
  · intro h
    have hmod : x.val % K.modulus = K.residue.val % K.modulus := h
    refine ⟨((x.val / K.modulus : ℕ) : ZMod n)
      - ((K.residue.val / K.modulus : ℕ) : ZMod n), ?_⟩
    -- A subtraction-free `ℕ` identity equivalent to the congruence.
    have hnat : x.val + K.modulus * (K.residue.val / K.modulus)
        = K.residue.val + K.modulus * (x.val / K.modulus) := by
      have h1 := Nat.div_add_mod x.val K.modulus
      have h2 := Nat.div_add_mod K.residue.val K.modulus
      omega
    have hcast := congrArg (fun t : ℕ => (t : ZMod n)) hnat
    push_cast at hcast
    rw [ZMod.natCast_rightInverse x, ZMod.natCast_rightInverse K.residue] at hcast
    linear_combination hcast

/-- Membership of `ofZMod x` in `K.toCell`, unfolded: the digits of `x` agree
    with those of `K.residue` at every coordinate `c` with
    `c.index < v_p(K.modulus)`. -/
lemma mem_toCell_iff_digits {K : Coset n} {x : ZMod n} :
    K.toCell.Mem (PrimeParallelotope.ofZMod x) ↔
      ∀ c : PrimeCoord n, c.index < K.modulus.factorization c.prime →
        c.digit x = c.digit K.residue := by
  constructor
  · intro h c hc
    refine h c ?_
    rw [mem_toCell_freeIdx]
    omega
  · intro h c hc
    rw [mem_toCell_freeIdx, not_le] at hc
    exact h c hc

/-- **Coset ↔ cell correspondence**: `x` lies in the coset `K` iff its
    parallelotope point `ofZMod x` lies in the cell `K.toCell`. -/
theorem mem_toCell_iff [NeZero n] {K : Coset n} {x : ZMod n} :
    K.toCell.Mem (PrimeParallelotope.ofZMod x) ↔ x ∈ K := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [mem_toCell_iff_digits, mem_iff_val_modEq]
  constructor
  · -- digits agree below `v_p(K.modulus)` ⟹ congruence mod each `p^{v_p}` ⟹ mod `K.modulus`
    intro h
    apply modEq_of_forall_primePow K.modulus_pos.ne'
    intro p hp
    have hp_n : p ∈ n.primeFactors :=
      Nat.primeFactors_mono K.modulus_dvd hn.ne' hp
    have hle : K.modulus.factorization p ≤ n.factorization p :=
      Nat.factorization_le_factorization_of_dvd_right K.modulus_dvd
        K.modulus_pos.ne' hn.ne'
    exact mod_pow_eq_of_digit_eq _ _ _ fun k hk =>
      congrArg Fin.val (h ⟨p, hp_n, k, lt_of_lt_of_le hk hle⟩ hk)
  · -- congruence mod `K.modulus` ⟹ mod `p^{v_p}` ⟹ digits agree below `v_p`
    intro h c hc
    exact Fin.ext (digit_eq_of_mod_pow_eq (h.of_dvd (Nat.ordProj_dvd _ _)) hc)

/-- The coset `K` and the cell `K.toCell` cut out the **same subset** of
    `ZMod n`. -/
lemma toCell_toFinsetZMod [NeZero n] (K : Coset n) :
    K.toCell.toFinsetZMod = Finset.univ.filter (· ∈ K) := by
  ext x
  simp [PrimeCell.toFinsetZMod, PrimeCell.containsZMod, mem_toCell_iff]

end Coset

/-! ### Coset partition → cell partition -/

/-- **Coset partition → cell partition.**  A coset partition of `ℤ/nℤ` maps to a
    cell partition of the prime parallelotope: each coset `K` becomes its cell
    `K.toCell`, and the disjoint cover transports along the digit bijection
    `ofZMod`.

    Concretely, for a parallelotope point `y`, write `y = ofZMod x`
    (`ofZMod_bijective`); the unique coset `K₀ ∋ x` from `P.cover` yields the
    unique cell `K₀.toCell ∋ y`, because `K.toCell.Mem (ofZMod x) ↔ x ∈ K`
    (`Coset.mem_toCell_iff`). -/
def CosetPartition.toCellPartition [NeZero n] (P : CosetPartition n) :
    Box.CellPartition (PrimeCoord n) (fun c => c.prime) where
  cells := (P.cosets.map Coset.toCell).toFinset
  covers := by
    intro y
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    obtain ⟨x, hx⟩ := (PrimeParallelotope.ofZMod_bijective n hn).surjective y
    subst hx
    obtain ⟨K₀, ⟨hK₀_mem, hK₀_x⟩, hK₀_uniq⟩ := P.cover x
    refine ⟨K₀.toCell, ⟨?_, ?_⟩, ?_⟩
    · -- the cell of `K₀` is among the cells
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨K₀, hK₀_mem, rfl⟩
    · -- `ofZMod x` lies in `K₀.toCell` since `x ∈ K₀`
      rw [Coset.mem_toCell_iff]
      exact hK₀_x
    · -- uniqueness: any cell containing `ofZMod x` comes from a coset containing `x`
      rintro X ⟨hX_mem, hX_y⟩
      rw [List.mem_toFinset, List.mem_map] at hX_mem
      obtain ⟨K, hK_mem, rfl⟩ := hX_mem
      rw [Coset.mem_toCell_iff] at hX_y
      rw [hK₀_uniq K ⟨hK_mem, hX_y⟩]

/-! ### The coset cell inequality -/

/-- **Coset cell inequality** (`cor:coset-bff`, Berger–Felzenbaum–Fraenkel).

    For any non-singleton coset `K` in a coset partition `P` of `ℤ/nℤ`, the total
    size of cosets in `P` whose size divides `|K|` is at least
    `minFac(n/|K|) · |K|`.

    Derived from the **general** cell inequality
    `DCS.Box.cell_inequality_including` via the coset ↔ cell bridge: `K` maps to
    the cell `K.toCell` of `P.toCellPartition`, the smallest side length over its
    fixed coordinates is `minFac(K.modulus) = minFac(n/|K|)`, and the cell-Finset
    sum transports back to the coset-list sum because `K' ↦ K'.toCell` is
    injective on `P.cosets` (`P.cover`) and preserves both sizes (`toCell_size`)
    and the divisibility ↔ inclusion correspondence
    (`toCell_freeIdx_subset_iff`). -/
theorem cell_inequality (hn : 0 < n) (P : CosetPartition n)
    (K : Coset n) (hK : K ∈ P.cosets) :
    ((P.cosets.filter (fun K' => K'.size ∣ K.size)).map Coset.size).sum
      ≥ (n / K.size).minFac * K.size := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have h_ndiv : n / K.size = K.modulus := Nat.div_div_self K.modulus_dvd hn.ne'
  rw [ge_iff_le, h_ndiv]
  by_cases hK_mod : 1 < K.modulus
  · -- ===== Main case: 1 < K.modulus =====
    -- The smallest prime of `K.modulus` and its parallelotope coordinate `c0`.
    have hmf_prime : (K.modulus.minFac).Prime := Nat.minFac_prime (by omega)
    have hmf_dvd_mod : K.modulus.minFac ∣ K.modulus := Nat.minFac_dvd _
    have hmf_dvd_n : K.modulus.minFac ∣ n := hmf_dvd_mod.trans K.modulus_dvd
    have hmf_in_pf : K.modulus.minFac ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hmf_prime, hmf_dvd_n, hn.ne'⟩
    have hnu_n_pos : 0 < n.factorization (K.modulus.minFac) :=
      hmf_prime.factorization_pos_of_dvd hn.ne' hmf_dvd_n
    let c0 : PrimeCoord n := ⟨K.modulus.minFac, hmf_in_pf, 0, hnu_n_pos⟩
    have hc0_fixed : c0 ∈ Finset.univ \ K.toCell.freeIdx := by
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Coset.mem_toCell_freeIdx]
      change ¬ (K.modulus.factorization (K.modulus.minFac) ≤ 0)
      have := hmf_prime.factorization_pos_of_dvd K.modulus_pos.ne' hmf_dvd_mod
      omega
    have hR : (Finset.univ \ K.toCell.freeIdx).Nonempty := ⟨c0, hc0_fixed⟩
    -- The minimum side length over the fixed coordinates is `minFac(K.modulus)`.
    have hb1 : K.modulus.minFac
        = (Finset.univ \ K.toCell.freeIdx).inf' hR (fun c => c.prime) := by
      apply le_antisymm
      · apply Finset.le_inf'
        intro c hc
        rw [Finset.mem_sdiff] at hc
        obtain ⟨-, hc2⟩ := hc
        rw [Coset.mem_toCell_freeIdx] at hc2
        have hc_fixed : c.index < K.modulus.factorization c.prime := by omega
        have hdvd : c.prime ∣ K.modulus := Nat.dvd_of_factorization_pos (by omega)
        exact Nat.minFac_le_of_dvd c.prime_two_le hdvd
      · exact Finset.inf'_le (fun c => c.prime) hc0_fixed
    have hX_in : K.toCell ∈ P.toCellPartition.cells :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨K, hK, rfl⟩)
    -- Apply the general cell inequality (`S = ∅` form).
    have key := Box.cell_inequality_including (fun c => c.prime_two_le)
      P.toCellPartition K.toCell hX_in hR hb1
    -- ===== Transfer the cell-Finset sum back to the coset-list sum =====
    -- `toCell` is injective on `P.cosets` (cover + same underlying set).
    have hinj : ∀ K1 ∈ P.cosets, ∀ K2 ∈ P.cosets, K1.toCell = K2.toCell → K1 = K2 := by
      intro K1 hK1 K2 hK2 heq
      have hfs : K1.toCell.toFinsetZMod = K2.toCell.toFinsetZMod := by rw [heq]
      rw [Coset.toCell_toFinsetZMod, Coset.toCell_toFinsetZMod] at hfs
      have hr2 : K1.residue ∈ K2 := by
        have hmem := Finset.ext_iff.mp hfs K1.residue
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem.mp K1.residue_mem
      obtain ⟨K0, _, huniq⟩ := P.cover K1.residue
      rw [huniq K1 ⟨hK1, K1.residue_mem⟩, huniq K2 ⟨hK2, hr2⟩]
    have hnodup : (P.cosets.map Coset.toCell).Nodup := P.cosets_nodup.map_on hinj
    -- List helper: filtered size-sum = indicator size-sum.
    have hfiltersum : ∀ (l : List (Coset n)),
        ((l.filter (fun K' => K'.size ∣ K.size)).map Coset.size).sum
          = (l.map (fun K' => if K'.size ∣ K.size then K'.size else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons hd tl ih =>
        by_cases h : hd.size ∣ K.size <;> simp [h, ih]
    -- The cell sum equals the coset sum.
    have htransfer : (∑ Xⱼ ∈ (P.cosets.map Coset.toCell).toFinset.filter
          (fun Xⱼ => Xⱼ.freeIdx ⊆ K.toCell.freeIdx), Xⱼ.size)
        = ((P.cosets.filter (fun K' => K'.size ∣ K.size)).map Coset.size).sum := by
      rw [Finset.sum_filter, List.sum_toFinset _ hnodup, List.map_map, hfiltersum P.cosets]
      apply congrArg List.sum
      apply List.map_congr_left
      intro K' _
      simp only [Function.comp_apply]
      rw [Coset.toCell_size K' hn]
      exact if_congr (Coset.toCell_freeIdx_subset_iff (K := K) (K' := K') hn) rfl rfl
    have key2 : K.modulus.minFac * K.toCell.size ≤
        ∑ Xⱼ ∈ (P.cosets.map Coset.toCell).toFinset.filter
          (fun Xⱼ => Xⱼ.freeIdx ⊆ K.toCell.freeIdx), Xⱼ.size := key
    rw [Coset.toCell_size K hn, htransfer] at key2
    exact key2
  · -- ===== Degenerate case: K.modulus = 1 (so K.size = n) =====
    have hmod1 : K.modulus = 1 := by have := K.modulus_pos; omega
    have hsize_n : K.size = n := by simp [Coset.size, hmod1]
    rw [hmod1, Nat.minFac_one, one_mul]
    have h_filter : P.cosets.filter (fun K' => K'.size ∣ K.size) = P.cosets := by
      apply List.filter_eq_self.mpr
      intro K' _
      simp only [decide_eq_true_eq, hsize_n]
      exact K'.size_dvd
    rw [h_filter, P.partition]
    exact le_of_eq hsize_n

/-! ### The two-level coset cell inequality -/

/-- The minimum side length over the fixed coordinates of `K.toCell` equals
    `minFac(K.modulus)` (the smallest prime dividing the modulus). -/
lemma Coset.toCell_inf'_prime (K : Coset n) (hn : 0 < n) (hmod : 1 < K.modulus)
    (hR : (Finset.univ \ K.toCell.freeIdx).Nonempty) :
    (Finset.univ \ K.toCell.freeIdx).inf' hR (fun c => c.prime) = K.modulus.minFac := by
  have hmf_prime : (K.modulus.minFac).Prime := Nat.minFac_prime (by omega)
  have hmf_dvd_mod : K.modulus.minFac ∣ K.modulus := Nat.minFac_dvd _
  have hmf_dvd_n : K.modulus.minFac ∣ n := hmf_dvd_mod.trans K.modulus_dvd
  have hmf_in_pf : K.modulus.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hmf_prime, hmf_dvd_n, hn.ne'⟩
  have hnu_n_pos : 0 < n.factorization (K.modulus.minFac) :=
    hmf_prime.factorization_pos_of_dvd hn.ne' hmf_dvd_n
  let c0 : PrimeCoord n := ⟨K.modulus.minFac, hmf_in_pf, 0, hnu_n_pos⟩
  have hc0_fixed : c0 ∈ Finset.univ \ K.toCell.freeIdx := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Coset.mem_toCell_freeIdx]
    change ¬ (K.modulus.factorization (K.modulus.minFac) ≤ 0)
    have := hmf_prime.factorization_pos_of_dvd K.modulus_pos.ne' hmf_dvd_mod
    omega
  apply le_antisymm
  · exact Finset.inf'_le (fun c => c.prime) hc0_fixed
  · apply Finset.le_inf'
    intro c hc
    rw [Finset.mem_sdiff] at hc
    obtain ⟨-, hc2⟩ := hc
    rw [Coset.mem_toCell_freeIdx] at hc2
    have hc_fixed : c.index < K.modulus.factorization c.prime := by omega
    have hdvd : c.prime ∣ K.modulus := Nat.dvd_of_factorization_pos (by omega)
    exact Nat.minFac_le_of_dvd c.prime_two_le hdvd

/-- The fixed-coordinate set of `K.toCell` is nonempty when `1 < K.modulus`. -/
lemma Coset.toCell_fixed_nonempty (K : Coset n) (hn : 0 < n) (hmod : 1 < K.modulus) :
    (Finset.univ \ K.toCell.freeIdx).Nonempty := by
  have hmf_prime : (K.modulus.minFac).Prime := Nat.minFac_prime (by omega)
  have hmf_dvd_mod : K.modulus.minFac ∣ K.modulus := Nat.minFac_dvd _
  have hmf_dvd_n : K.modulus.minFac ∣ n := hmf_dvd_mod.trans K.modulus_dvd
  have hmf_in_pf : K.modulus.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hmf_prime, hmf_dvd_n, hn.ne'⟩
  have hnu_n_pos : 0 < n.factorization (K.modulus.minFac) :=
    hmf_prime.factorization_pos_of_dvd hn.ne' hmf_dvd_n
  refine ⟨⟨K.modulus.minFac, hmf_in_pf, 0, hnu_n_pos⟩, ?_⟩
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Coset.mem_toCell_freeIdx]
  change ¬ (K.modulus.factorization (K.modulus.minFac) ≤ 0)
  have := hmf_prime.factorization_pos_of_dvd K.modulus_pos.ne' hmf_dvd_mod
  omega

/-- Generic coset ↔ cell sum transfer: the total size of cells of
    `P.toCellPartition` whose free set lies in `K₀.toCell.freeIdx` equals the
    total size of cosets of `P` whose size divides `K₀.size`.  (Same argument as
    in `cell_inequality`, generalized over the reference coset `K₀`.) -/
lemma CosetPartition.toCell_sum_eq [NeZero n] (P : CosetPartition n) (hn : 0 < n)
    (K₀ : Coset n) :
    (∑ Xⱼ ∈ P.toCellPartition.cells.filter (fun Xⱼ => Xⱼ.freeIdx ⊆ K₀.toCell.freeIdx), Xⱼ.size)
      = ((P.cosets.filter (fun K' => K'.size ∣ K₀.size)).map Coset.size).sum := by
  have hinj : ∀ K1 ∈ P.cosets, ∀ K2 ∈ P.cosets, K1.toCell = K2.toCell → K1 = K2 := by
    intro K1 hK1 K2 hK2 heq
    have hfs : K1.toCell.toFinsetZMod = K2.toCell.toFinsetZMod := by rw [heq]
    rw [Coset.toCell_toFinsetZMod, Coset.toCell_toFinsetZMod] at hfs
    have hr2 : K1.residue ∈ K2 := by
      have hmem := Finset.ext_iff.mp hfs K1.residue
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem.mp K1.residue_mem
    obtain ⟨K0, _, huniq⟩ := P.cover K1.residue
    rw [huniq K1 ⟨hK1, K1.residue_mem⟩, huniq K2 ⟨hK2, hr2⟩]
  have hnodup : (P.cosets.map Coset.toCell).Nodup := P.cosets_nodup.map_on hinj
  have hfiltersum : ∀ (l : List (Coset n)),
      ((l.filter (fun K' => K'.size ∣ K₀.size)).map Coset.size).sum
        = (l.map (fun K' => if K'.size ∣ K₀.size then K'.size else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih => by_cases h : hd.size ∣ K₀.size <;> simp [h, ih]
  change (∑ Xⱼ ∈ (P.cosets.map Coset.toCell).toFinset.filter
      (fun Xⱼ => Xⱼ.freeIdx ⊆ K₀.toCell.freeIdx), Xⱼ.size) = _
  rw [Finset.sum_filter, List.sum_toFinset _ hnodup, List.map_map, hfiltersum P.cosets]
  apply congrArg List.sum
  apply List.map_congr_left
  intro K' _
  simp only [Function.comp_apply]
  rw [Coset.toCell_size K' hn]
  exact if_congr (Coset.toCell_freeIdx_subset_iff (K := K₀) (K' := K') hn) rfl rfl

/-- **Two-level coset cell inequality** (`cor:coset-twolevel`).

    When `n/|K|` has at least two distinct prime factors, absorb the whole
    smallest-prime layer `p₁^{e₁}` and use the second smallest prime `p₂` as the
    multiplier:
    `∑_{|K_i| ∣ |K|·p₁^{e₁}} |K_i| ≥ p₂ · |K|`.

    Derived from the general `DCS.Box.cell_inequality` with `S = F₁` (the minimal
    fixed coordinates, i.e. those of side length `p₁`): `K.toCell.freeIdx ∪ F₁`
    is the free set of the cell of the reduced coset `K''` of modulus
    `K.modulus / p₁^{e₁} = ordCompl[p₁] K.modulus`, whence `b₀ = minFac(K''.modulus) = p₂`
    and the resulting sum transports to cosets with `|K_i| ∣ |K''| = |K|·p₁^{e₁}`. -/
theorem cell_inequality_two_level (hn : 0 < n) (P : CosetPartition n)
    (K : Coset n) (hK : K ∈ P.cosets) :
    let q := n / K.size
    let p₁ := q.minFac
    let e₁ := q.factorization p₁
    1 < q / p₁ ^ e₁ →
    ((P.cosets.filter (fun K' => K'.size ∣ K.size * p₁ ^ e₁)).map Coset.size).sum
      ≥ (q / p₁ ^ e₁).minFac * K.size := by
  intro q p₁ e₁ htwo
  haveI : NeZero n := ⟨hn.ne'⟩
  have hq : q = K.modulus := Nat.div_div_self K.modulus_dvd hn.ne'
  have hqfact : q.factorization = K.modulus.factorization := by rw [hq]
  have hpe_dvd_q : p₁ ^ e₁ ∣ q := Nat.ordProj_dvd q p₁
  have hq_dvd_n : q ∣ n := by rw [hq]; exact K.modulus_dvd
  have hm'_dvd_q : q / p₁ ^ e₁ ∣ q := ⟨p₁ ^ e₁, (Nat.div_mul_cancel hpe_dvd_q).symm⟩
  have hm'_dvd_n : q / p₁ ^ e₁ ∣ n := dvd_trans hm'_dvd_q hq_dvd_n
  have hm'_pos : 0 < q / p₁ ^ e₁ := by omega
  -- The reduced coset (modulus `q / p₁^{e₁}`).
  let K'' : Coset n := ⟨K.residue, q / p₁ ^ e₁, hm'_dvd_n, hm'_pos⟩
  -- The minimal fixed coordinates of `K` (side length `p₁`).
  let F₁ : Finset (PrimeCoord n) :=
    (Finset.univ \ K.toCell.freeIdx).filter (fun c => c.prime = p₁)
  have hfact : ∀ p : ℕ, (q / p₁ ^ e₁).factorization p
      = if p = p₁ then 0 else K.modulus.factorization p := by
    intro p
    rw [show q / p₁ ^ e₁ = ordCompl[p₁] q from rfl,
        Nat.factorization_ordCompl, Finsupp.erase_apply, hqfact]
  -- Geometric core: `freeIdx(K'') = freeIdx(K) ∪ F₁`.
  have hfree : K''.toCell.freeIdx = K.toCell.freeIdx ∪ F₁ := by
    ext c
    rw [Coset.mem_toCell_freeIdx]
    change (q / p₁ ^ e₁).factorization c.prime ≤ c.index ↔ _
    rw [hfact c.prime]
    simp only [F₁, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
               Finset.mem_univ, true_and, Coset.mem_toCell_freeIdx]
    by_cases hcp : c.prime = p₁
    · simp [hcp]
      omega
    · simp [hcp]
  -- `|K''| = |K| · p₁^{e₁}`.
  have hKsize_q : K.size * q = n := by
    rw [hq]; change n / K.modulus * K.modulus = n; exact Nat.div_mul_cancel K.modulus_dvd
  have hK''size : K''.size = K.size * p₁ ^ e₁ := by
    have hmul : (K.size * p₁ ^ e₁) * (q / p₁ ^ e₁) = n := by
      rw [Nat.mul_assoc, Nat.mul_comm (p₁ ^ e₁) (q / p₁ ^ e₁),
          Nat.div_mul_cancel hpe_dvd_q, hKsize_q]
    change n / (q / p₁ ^ e₁) = K.size * p₁ ^ e₁
    exact Nat.div_eq_of_eq_mul_left hm'_pos hmul.symm
  have hR'' : (Finset.univ \ K''.toCell.freeIdx).Nonempty :=
    Coset.toCell_fixed_nonempty K'' hn htwo
  have hR : (Finset.univ \ (K.toCell.freeIdx ∪ F₁)).Nonempty := by rw [← hfree]; exact hR''
  have hb₀ : (q / p₁ ^ e₁).minFac
      = (Finset.univ \ (K.toCell.freeIdx ∪ F₁)).inf' hR (fun c => c.prime) := by
    change K''.modulus.minFac = _
    rw [← Coset.toCell_inf'_prime K'' hn htwo hR'']
    have h₁ : Finset.univ \ K''.toCell.freeIdx
        = Finset.univ \ (K.toCell.freeIdx ∪ F₁) := by rw [hfree]
    exact Finset.inf'_congr hR'' h₁ (fun a _ => rfl)
  have key := Box.cell_inequality (fun c => c.prime_two_le) P.toCellPartition K.toCell
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨K, hK, rfl⟩)) F₁ hR hb₀
  rw [ge_iff_le]
  calc (q / p₁ ^ e₁).minFac * K.size
      = (q / p₁ ^ e₁).minFac * K.toCell.size := by rw [Coset.toCell_size K hn]
    _ ≤ ∑ Xⱼ ∈ P.toCellPartition.cells.filter
          (fun Xⱼ => Xⱼ.freeIdx ⊆ K.toCell.freeIdx ∪ F₁), Xⱼ.size := key
    _ = ∑ Xⱼ ∈ P.toCellPartition.cells.filter
          (fun Xⱼ => Xⱼ.freeIdx ⊆ K''.toCell.freeIdx), Xⱼ.size := by rw [hfree]
    _ = ((P.cosets.filter (fun K' => K'.size ∣ K''.size)).map Coset.size).sum :=
          CosetPartition.toCell_sum_eq P hn K''
    _ = ((P.cosets.filter (fun K' => K'.size ∣ K.size * p₁ ^ e₁)).map Coset.size).sum := by
          rw [hK''size]

end DCS

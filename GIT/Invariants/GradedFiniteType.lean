import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import GIT.Invariants.InheritedGrading

/-!
# Finite generation of a graded algebra from its irrelevant ideal

If `R` is an `ℕ`-graded `k`-algebra and its irrelevant ideal `R₊` is finitely generated as an
ideal, then `R` is finitely generated as a `(𝒜 0)`-algebra. With the extra hypothesis that `𝒜 0`
is itself f.g. as a `k`-algebra, transitivity gives `Algebra.FiniteType k R`. The fixed-subalgebra
specialization `fixedSubalgebra_finiteType` is then immediate.

## Main results

* `GIT.finiteType_of_finitely_generated_irrelevant_ideal`
* `GIT.finiteType_k_of_finitely_generated_irrelevant_ideal`
* `GIT.AlgHom.map_decompose_zero`
* `GIT.fixedSubalgebra_finiteType`
-/

open scoped DirectSum

universe u uR

namespace GIT

variable {k : Type u} [Field k]
variable {R : Type uR} [CommRing R] [Algebra k R]
variable {𝒜 : ℕ → Submodule k R} [GradedAlgebra 𝒜]

/-- Short alias for the irrelevant ideal `R₊` as an `Ideal R`. -/
abbrev irrelevantIdeal : Ideal R := (HomogeneousIdeal.irrelevant 𝒜).toIdeal

/-- **`irrelevant` equals the ideal spanned by all positive-degree pieces.** -/
private lemma irrelevant_eq_span_pos :
    irrelevantIdeal (𝒜 := 𝒜) =
      Ideal.span (⋃ i : ℕ, ⋃ _ : 0 < i, (𝒜 i : Set R)) := by
  simpa [irrelevantIdeal] using (HomogeneousIdeal.irrelevant_eq_span (𝒜 := 𝒜))

/-- **F.g.-ness of the submodule-span of all positive-degree pieces** from f.g.-ness of the
irrelevant ideal. -/
private lemma fg_submodule_span_pos_of_irrelevant_fg
    (h : (irrelevantIdeal (𝒜 := 𝒜)).FG) :
    (Submodule.span R (⋃ i : ℕ, ⋃ _ : 0 < i, (𝒜 i : Set R)) : Submodule R R).FG := by
  have hspan_fg : (Ideal.span (⋃ i : ℕ, ⋃ _ : 0 < i, (𝒜 i : Set R)) : Ideal R).FG := by
    rcases h with ⟨S, hS⟩
    exact ⟨S, hS.trans irrelevant_eq_span_pos⟩
  rcases hspan_fg with ⟨S, hS⟩
  exact ⟨S, congrArg (fun (I : Ideal R) => (I : Submodule R R)) hS⟩

/-- **Pick finitely many homogeneous positive-degree generators** for the irrelevant ideal.

Math statement: if `R₊` is finitely generated, then there is `T : Finset R` whose elements all
lie in some `𝒜 d` with `d > 0` and which still spans `R₊`.

Proof idea: rewrite `R₊` as `Ideal.span (⋃ pos-degree pieces)`
(`irrelevant_eq_span_pos`), transfer f.g.-ness to the submodule span
(`fg_submodule_span_pos_of_irrelevant_fg`), apply `Submodule.fg_span_iff_fg_span_finset_subset`. -/
lemma exists_finset_homogeneous_pos_generators
    (h : (irrelevantIdeal (𝒜 := 𝒜)).FG) :
    ∃ T : Finset R,
      (Ideal.span (T : Set R) = irrelevantIdeal (𝒜 := 𝒜)) ∧
      (∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) := by
  classical
  rcases (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (M := R) _).1
      (fg_submodule_span_pos_of_irrelevant_fg h) with ⟨T, hTs, hspan⟩
  refine ⟨T, ?_, ?_⟩
  · have : Ideal.span _ = Ideal.span (T : Set R) :=
      congrArg (fun (N : Submodule R R) => (N : Ideal R)) hspan
    rw [← this]; exact irrelevant_eq_span_pos.symm
  · intro t ht
    rcases Set.mem_iUnion.1 (hTs (by simpa using ht)) with ⟨d, hd⟩
    rcases Set.mem_iUnion.1 hd with ⟨hdpos, hmem⟩
    exact ⟨d, hdpos, hmem⟩

/-- Algebra instance on `R` over `𝒜 0`. -/
noncomputable def inst_algebra_degreeZero : Algebra (𝒜 0) R := inferInstance

/-- Scalar-tower instance `k → 𝒜 0 → R`. -/
noncomputable def inst_isScalarTower_degreeZero : IsScalarTower k (𝒜 0) R := by
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (𝒜 := 𝒜)
  refine IsScalarTower.of_algebraMap_eq' (R := k) (S := (𝒜 0)) (A := R) ?_
  ext x; simp

/-- The degree-`d` projection on `R` as an `AddMonoidHom`: `z ↦ (decompose 𝒜 z) d`. -/
private noncomputable def degreeProj (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜] (d : ℕ) :
    R →+ R where
  toFun := fun z => ((DirectSum.decompose 𝒜 z) d : R)
  map_zero' := by simp
  map_add' := by simp

/-- `degreeProj 𝒜 d y = y` for `y ∈ 𝒜 d`. -/
private lemma degreeProj_id_on_grade (d : ℕ) {y : R} (hy : y ∈ 𝒜 d) :
    degreeProj 𝒜 d y = y := by
  simpa [degreeProj] using (DirectSum.decompose_of_mem_same 𝒜 (x := y) (i := d) hy)

/-- **Expansion identity.** Apply `degreeProj 𝒜 d` to the linear-combination presentation
`y = Σ l t · t` for `y ∈ 𝒜 d`. -/
private lemma degreeProj_sum_expansion
    {T : Finset R} (l : (T : Set R) →₀ R) {d : ℕ} {y : R} (hy : y ∈ 𝒜 d)
    (hl : (Finsupp.linearCombination R fun t : (T : Set R) => (t : R)) l = y) :
    y = Finset.sum l.support (fun t => degreeProj 𝒜 d (l t * (t : R))) := by
  classical
  have hl_sum : (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R))) l =
      Finset.sum l.support (fun t => l t * (t : R)) := by
    simp [Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]
  have h1 : degreeProj 𝒜 d (Finset.sum l.support (fun t => l t * (t : R))) =
      degreeProj 𝒜 d y := by rw [← hl_sum, hl]
  have h2 := degreeProj_id_on_grade (𝒜 := 𝒜) d hy
  simpa [map_sum, h2] using h1.symm

/-- **Le-branch:** when `degT t ≤ d`, the summand `degreeProj 𝒜 d (l t · t)` lies in the
`(𝒜 0)`-adjoin of `T`, via the inductive hypothesis at `d - degT t < d`. -/
private lemma summand_in_adjoin_le
    {T : Finset R} {t : (T : Set R)} (l : (T : Set R) →₀ R)
    {d e : ℕ} (hdpos : 0 < d) (hepos : 0 < e) (hle : e ≤ d)
    (ht_hom : (t : R) ∈ 𝒜 e)
    (ih : ∀ m, m < d → ∀ y ∈ 𝒜 m, y ∈ Algebra.adjoin (𝒜 0) (T : Set R))
    (ht_mem : (t : R) ∈ Algebra.adjoin (𝒜 0) (T : Set R)) :
    degreeProj 𝒜 d (l t * (t : R)) ∈ Algebra.adjoin (𝒜 0) (T : Set R) := by
  have hπ : degreeProj 𝒜 d (l t * (t : R)) =
      ((DirectSum.decompose 𝒜 (l t)) (d - e) : R) * (t : R) := by
    simpa [degreeProj] using
      (DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := 𝒜) (a := l t) (b := (t : R))
        (n := d) (i := e) ht_hom hle)
  rw [hπ]
  exact (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring.mul_mem
    (ih (d - e) (Nat.sub_lt hdpos hepos) _ ((DirectSum.decompose 𝒜 (l t)) (d - e)).2) ht_mem

/-- **Not-le branch:** when `degT t > d`, the summand `degreeProj 𝒜 d (l t · t)` is zero. -/
private lemma summand_eq_zero_not_le
    {T : Finset R} {t : (T : Set R)} (l : (T : Set R) →₀ R)
    {d e : ℕ} (hle : ¬ e ≤ d) (ht_hom : (t : R) ∈ 𝒜 e) :
    degreeProj 𝒜 d (l t * (t : R)) = 0 := by
  simpa [degreeProj] using
    (DirectSum.coe_decompose_mul_of_right_mem_of_not_le (𝒜 := 𝒜) (a := l t) (b := (t : R))
      (n := d) (i := e) ht_hom hle)

/-- **Inductive step.** For `d > 0` with the inductive hypothesis at every `m < d`, every
`y ∈ 𝒜 d` lies in the `(𝒜 0)`-adjoin of `T`. -/
private lemma homogeneous_mem_adjoin_step
    {T : Finset R}
    (hspan : Ideal.span (T : Set R) = irrelevantIdeal (𝒜 := 𝒜))
    (hT : ∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d)
    {d : ℕ} (hdpos : 0 < d)
    (ih : ∀ m, m < d → ∀ y ∈ 𝒜 m, y ∈ Algebra.adjoin (𝒜 0) (T : Set R))
    {y : R} (hy : y ∈ 𝒜 d) : y ∈ Algebra.adjoin (𝒜 0) (T : Set R) := by
  classical
  have hy_span : y ∈ (Submodule.span R (T : Set R) : Submodule R R) := by
    change y ∈ ((Ideal.span (T : Set R) : Ideal R) : Submodule R R)
    rw [hspan]
    simpa [irrelevantIdeal] using
      HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := 𝒜) (x := y) (i := d) hdpos hy
  rcases (Finsupp.mem_span_iff_linearCombination (R := R) (M := R) (s := (T : Set R)) y).1
      hy_span with ⟨l, hl⟩
  choose degT hdegTpos hdegTmem
    using (fun t : (T : Set R) => (hT t.1 (by simp [Finset.mem_coe.mp t.2])))
  rw [degreeProj_sum_expansion (𝒜 := 𝒜) l hy hl]
  refine Subsemiring.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring (fun t _ => ?_)
  by_cases hle : degT t ≤ d
  · exact summand_in_adjoin_le l hdpos (hdegTpos t) hle (by simpa using hdegTmem t) ih
      (Algebra.subset_adjoin t.2)
  · rw [summand_eq_zero_not_le l hle (by simpa using hdegTmem t)]; exact zero_mem _

/-- **Every homogeneous element of `R` lies in `(𝒜 0)`-adjoin `T`.**

Math statement: if `Ideal.span T = R₊` with each `t ∈ T` homogeneous of positive degree, then
every `y ∈ 𝒜 d` (any `d`) lies in `Algebra.adjoin (𝒜 0) T`.

Proof idea: strong induction on `d`. Base case `d = 0` is `algebraMap_mem`; inductive step is
`homogeneous_mem_adjoin_step`. -/
lemma homogeneous_mem_adjoin_of_irrelevant_eq_span
    {T : Finset R}
    (hspan : Ideal.span (T : Set R) = irrelevantIdeal (𝒜 := 𝒜))
    (hT : ∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) :
    ∀ d : ℕ, ∀ y : R, y ∈ 𝒜 d → y ∈ Algebra.adjoin (𝒜 0) (T : Set R) := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih y hy
  by_cases hd0 : d = 0
  · subst hd0
    simpa using (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ⟨y, hy⟩)
  · exact homogeneous_mem_adjoin_step hspan hT (Nat.pos_of_ne_zero hd0) ih hy

/-- **F.g. over `𝒜 0` from f.g.-ness of the irrelevant ideal.**

Math statement: if `R₊` is f.g. as an ideal, then `R` is finitely generated as a `(𝒜 0)`-algebra.

Proof idea: pick generators `T` via `exists_finset_homogeneous_pos_generators`. Every `r : R`
decomposes as a finite sum of homogeneous pieces; each piece lies in `(𝒜 0)`-adjoin `T` by
`homogeneous_mem_adjoin_of_irrelevant_eq_span`. -/
lemma finiteType_degreeZero_of_irrelevant_fg
    (h : (irrelevantIdeal (𝒜 := 𝒜)).FG) :
    Algebra.FiniteType (𝒜 0) R := by
  classical
  obtain ⟨T, hspan, hT⟩ := exists_finset_homogeneous_pos_generators (𝒜 := 𝒜) h
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro r _
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Subalgebra.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ?_
  intro i _
  exact homogeneous_mem_adjoin_of_irrelevant_eq_span (𝒜 := 𝒜) hspan hT i _
    (SetLike.coe_mem ((DirectSum.decompose 𝒜 r) i))

/-- Form using `HomogeneousIdeal.irrelevant 𝒜` directly (instead of the alias `irrelevantIdeal`). -/
theorem finiteType_of_finitely_generated_irrelevant_ideal
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) R :=
  finiteType_degreeZero_of_irrelevant_fg (𝒜 := 𝒜) (h := by simpa [irrelevantIdeal] using h)

/-- **F.g. over `k` from f.g.-ness of the irrelevant ideal**, assuming `𝒜 0` is itself
f.g. over `k`. Transitivity `k → 𝒜 0 → R`. -/
theorem finiteType_k_of_finitely_generated_irrelevant_ideal
    [Algebra.FiniteType k (𝒜 0)] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType k R := by
  classical
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (𝒜 := 𝒜)
  letI : IsScalarTower k (𝒜 0) R := inst_isScalarTower_degreeZero (𝒜 := 𝒜)
  exact Algebra.FiniteType.trans (R := k) (S := 𝒜 0) (A := R)
    (hRS := inferInstance) (hSA := finiteType_of_finitely_generated_irrelevant_ideal h)

/-- **Same-degree case of `AlgHom.map_decompose_zero`.** -/
private lemma map_decompose_zero_same
    {A : Type*} [CommRing A] [Algebra k A]
    {R : Type*} [CommRing R] [Algebra k R] (toR : A →ₐ[k] R)
    (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]
    (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
    (htoR : ∀ (d : ℕ) (a : A), a ∈ 𝒜G d → toR a ∈ 𝒜 d) {c : A} (hc : c ∈ 𝒜G 0) :
    toR ((DirectSum.decompose 𝒜G c) 0 : A) = ((DirectSum.decompose 𝒜 (toR c)) 0 : R) := by
  rw [DirectSum.decompose_of_mem_same 𝒜G hc, DirectSum.decompose_of_mem_same 𝒜 (htoR 0 c hc)]

/-- **Different-degree case of `AlgHom.map_decompose_zero`.** -/
private lemma map_decompose_zero_ne
    {A : Type*} [CommRing A] [Algebra k A]
    {R : Type*} [CommRing R] [Algebra k R] (toR : A →ₐ[k] R)
    (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]
    (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
    (htoR : ∀ (d : ℕ) (a : A), a ∈ 𝒜G d → toR a ∈ 𝒜 d) {i : ℕ} {c : A}
    (hc : c ∈ 𝒜G i) (hi : i ≠ 0) :
    toR ((DirectSum.decompose 𝒜G c) 0 : A) = ((DirectSum.decompose 𝒜 (toR c)) 0 : R) := by
  rw [DirectSum.decompose_of_mem_ne 𝒜G hc hi, DirectSum.decompose_of_mem_ne 𝒜 (htoR i c hc) hi]
  simp

/-- **Grading-preserving algebra maps commute with the degree-`0` projection.**

Math statement: if `toR : A →ₐ[k] R` sends each `𝒜G d` into `𝒜 d`, then
`toR ((decompose 𝒜G a) 0) = (decompose 𝒜 (toR a)) 0`.

Proof idea: induction on the graded decomposition; for a single homogeneous piece in `𝒜G i`,
split into `i = 0` (`map_decompose_zero_same`) and `i ≠ 0` (`map_decompose_zero_ne`); finite
addition is handled by `simp` on `decompose_add` and `map_add`. -/
lemma AlgHom.map_decompose_zero
    {k : Type u} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {R : Type*} [CommRing R] [Algebra k R]
    (toR : A →ₐ[k] R)
    (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]
    (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]
    (htoR : ∀ (d : ℕ) (a : A), a ∈ 𝒜G d → toR a ∈ 𝒜 d) (a : A) :
    toR ((DirectSum.decompose 𝒜G a) 0 : A) =
      ((DirectSum.decompose 𝒜 (toR a)) 0 : R) := by
  refine DirectSum.Decomposition.inductionOn (ℳ := 𝒜G)
    (motive := fun a => toR ((DirectSum.decompose 𝒜G a) 0 : A) =
      ((DirectSum.decompose 𝒜 (toR a)) 0 : R)) (by simp) ?_ ?_ a
  · rintro i ⟨c, hc⟩
    by_cases hi : i = 0
    · subst hi; exact map_decompose_zero_same toR 𝒜G 𝒜 htoR hc
    · exact map_decompose_zero_ne toR 𝒜G 𝒜 htoR hc hi
  · intro x y hx hy
    simp only [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, map_add, hx, hy]

/-- **The fixed subalgebra `A = R^G` is f.g. as a `k`-algebra**, given its degree-`0` piece is
f.g. and its irrelevant ideal is f.g. Specialisation of
`finiteType_k_of_finitely_generated_irrelevant_ideal` to `R^G`. -/
theorem fixedSubalgebra_finiteType
    {A : Type*} [CommRing A] [Algebra k A]
    (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]
    [Algebra.FiniteType k (𝒜G 0)]
    (hfg : (HomogeneousIdeal.irrelevant 𝒜G).toIdeal.FG) :
    Algebra.FiniteType k A :=
  finiteType_k_of_finitely_generated_irrelevant_ideal hfg

end GIT

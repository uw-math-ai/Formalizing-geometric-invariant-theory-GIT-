import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

universe u

variable {k : Type u} [Field k] (G : Type u) [Group G]

/- Ring of S_n invariants is given by symmetric polynomials -/
#check MvPolynomial.esymmAlgEquiv

/- The Reynolds operator for a finite group -/
#check LinearMap.equivariantProjection

/- A group `G` is linear-algebraic over a field `k` if it is isomorphic to
a subgroup of `GL_n(k)` for some `n` -/
def IsLinearAlgebraic := ∃ (n : Type*), ∃ _ : DecidableEq n, ∃ _ : Fintype n,
    ∃ H : Subgroup (GL n k), Nonempty (H ≃* G)

open Monoid MonoidAlgebra Representation

/- the category of G-representations over k -/
-- use this one
#check Rep k G

/- the Group algebra -/
#check k[G]

--the direct product of two representations
noncomputable
example (V W : Rep k G) : Rep k G := (V ⨯ W)

--morphisms in the representation category are coerced to functions
-- use this representation
example (V W : Rep k G) (f : V ⟶ W) (v : V) : W := f v

noncomputable
example (V W : Rep k G) : V ⨯ W ⟶ V := CategoryTheory.Limits.prod.fst

--expressing a representation is finite-dimensional
example (M : Rep k G) : Prop := FiniteDimensional k M

--expressing a representation is an indexed product of representations
noncomputable
example {α : Type} (ι : α → Rep k G) : Rep k G := ∏ᶜ ι

--expressing a represesntation is irreductible
example (M : Rep k G) : Prop := IsIrreducible M.ρ


section LocallyFinite

variable {k : Type*} [CommSemiring k] {G : Type*} [Monoid G]
    {R : Type*} [AddCommMonoid R] [Module k R] [DistribMulAction G R]

/-- Def1: A `DistribMulAction` of `G` on a `k`-module `R` is locally finite if every element
of `R` is contained in a finite-dimensional `G`-stable `k`-submodule. -/
def Representation.IsLocallyFinite (k : Type*) [CommSemiring k] (G : Type*) [Monoid G]
    (R : Type*) [AddCommMonoid R] [Module k R] [DistribMulAction G R] : Prop :=
  ∀ r : R, ∃ V : Submodule k R, Module.Finite k V ∧
    (∀ (g : G) (v : V), (g • (v : R)) ∈ V) ∧ r ∈ V

/-- Every action of a finite monoid is locally finite: the orbit of any element
spans a finitely generated submodule. -/
theorem Representation.isLocallyFinite_of_finite (k : Type*) [CommSemiring k] (G : Type*)
    [Monoid G] [Finite G] (R : Type*) [AddCommMonoid R] [Module k R]
    [DistribMulAction G R] [SMulCommClass G k R] :
    Representation.IsLocallyFinite k G R := by
  intro r
  refine ⟨Submodule.span k (Set.range (fun g : G => g • r)), ?_, ?_, ?_⟩
  · exact Module.Finite.span_of_finite k (Set.finite_range _)
  · intro g v
    change g • (v : R) ∈ Submodule.span k (Set.range (fun g' : G => g' • r))
    have hv : (v : R) ∈ Submodule.span k (Set.range (fun g' : G => g' • r)) := v.property
    exact Submodule.span_induction
      (mem := fun x ⟨g', hg'⟩ => hg' ▸ Submodule.subset_span ⟨g * g', mul_smul g g' r⟩)
      (zero := by simp)
      (add := fun x y _ _ hx hy => by rw [smul_add]; exact Submodule.add_mem _ hx hy)
      (smul := fun a x _ hx => by rw [smul_comm]; exact Submodule.smul_mem _ a hx)
      hv
  · exact Submodule.subset_span ⟨1, one_smul G r⟩

end LocallyFinite

section ReynoldsOperator

/- reynolds orperator on infinte group-/
variable (k : Type*) [CommSemiring k] (G : Type*) [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (R : Type*) [AddCommMonoid R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]

/-- Def2: The Reynolds operator for a finite group `G` acting on a `k`-module `R`.
This is the `k`-linear projection `R →ₗ[k] R` onto the submodule of `G`-invariants,
defined as `(1/|G|) ∑ g, ρ(g)`. -/
noncomputable def reynoldsOperator : R →ₗ[k] R :=
  (Representation.ofDistribMulAction k G R).averageMap

/-- The Reynolds operator maps every element into the submodule of `G`-invariants. -/
theorem reynoldsOperator_mem_invariants (r : R) :
    reynoldsOperator k G R r ∈ (Representation.ofDistribMulAction k G R).invariants :=
  (Representation.ofDistribMulAction k G R).averageMap_invariant r

/-- The Reynolds operator fixes every `G`-invariant element. -/
theorem reynoldsOperator_id (r : R)
    (hr : r ∈ (Representation.ofDistribMulAction k G R).invariants) :
    reynoldsOperator k G R r = r :=
  (Representation.ofDistribMulAction k G R).averageMap_id r hr

end ReynoldsOperator

section GeneralReynolds

/- Def3: A group `G` is linearly reductive over `k` if every finite-dimensional representation
is completely reducible (every subrepresentation has a complement). -/
class IsLinearlyReductive (k G : Type u) [Field k] [Group G] : Prop where
  isSemisimple : ∀ (M : Rep k G) [FiniteDimensional k M], IsSemisimpleRepresentation M.ρ

/-- Finite groups with invertible cardinality are linearly reductive. -/
instance IsLinearlyReductive.of_fintype (k G : Type u) [Field k] [Group G]
    [Fintype G] [Invertible (Fintype.card G : k)] :
    IsLinearlyReductive k G where
  isSemisimple M _ := by
    haveI : NeZero (Nat.card G : k) := by
      rw [Nat.card_eq_fintype_card]
      exact ⟨Invertible.ne_zero (Fintype.card G : k)⟩
    exact M.ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mpr inferInstance

/-- Def4: The invariants of a representation form a subrepresentation. -/
noncomputable def Representation.invariantSubrepresentation
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g v hv := by
    rw [Representation.mem_invariants] at hv ⊢
    intro g'; simp [hv]

/-- A linearly reductive group admits a `k`-linear projection onto the invariants
of any finite-dimensional representation, with the projection being `G`-equivariant. -/
theorem IsLinearlyReductive.exists_reynolds_projection
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G) [FiniteDimensional k M] :
    ∃ π : M →ₗ[k] M, LinearMap.IsProj M.ρ.invariants π ∧
      ∀ (g : G) (v : M), π (M.ρ g v) = π v := by
  have hss : IsSemisimpleRepresentation M.ρ := hlr.isSemisimple M
  obtain ⟨W, hW⟩ := hss.exists_isCompl M.ρ.invariantSubrepresentation
  -- Convert IsCompl on Subrepresentation to IsCompl on Submodule
  have hc : IsCompl M.ρ.invariants W.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have h := congr_arg Subrepresentation.toSubmodule (disjoint_iff.mp hW.disjoint)
      simpa [Subrepresentation.toSubmodule_inf] using h
    · rw [codisjoint_iff]
      have h := congr_arg Subrepresentation.toSubmodule (codisjoint_iff.mp hW.codisjoint)
      simpa [Subrepresentation.toSubmodule_sup] using h
  -- Build projection using the complement
  let π := M.ρ.invariants.subtype ∘ₗ M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc
  refine ⟨π, ⟨fun x => ?_, fun x hx => ?_⟩, fun g v => ?_⟩
  · exact (M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc x).property
  · have := Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩
    simp [π, this]
  · -- G-equivariance: π (M.ρ g v) = π v
    -- Decompose v = v_inv + v_W via the complement
    have hdecomp := Submodule.mem_sup.mp
      (show v ∈ M.ρ.invariants ⊔ W.toSubmodule from hc.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨vi, hvi, vw, hvw, rfl⟩ := hdecomp
    -- M.ρ g preserves both summands
    have hvi_inv : M.ρ g vi = vi := ((M.ρ.mem_invariants vi).mp hvi) g
    have hvw_W : M.ρ g vw ∈ W.toSubmodule := W.apply_mem_toSubmodule g hvw
    -- π is the identity on invariants and zero on W
    simp only [π, LinearMap.comp_apply, map_add]
    rw [Submodule.linearProjOfIsCompl_apply_left hc ⟨vi, hvi⟩]
    rw [hvi_inv, Submodule.linearProjOfIsCompl_apply_left hc ⟨vi, hvi⟩]
    have : M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc vw = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' hc vw hvw
    have : M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc (M.ρ g vw) = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' hc _ hvw_W
    simp [*]

/-- **Uniqueness of the Reynolds projection.** Any two `k`-linear projections onto `ρ.invariants`
that are `G`-equivariant must agree. The proof reduces to showing that a G-equivariant map
from a representation with no invariants to a trivial representation is zero, which follows
from complete reducibility. -/
theorem IsLinearlyReductive.reynolds_unique
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G) [FiniteDimensional k M]
    (π₁ π₂ : M →ₗ[k] M)
    (h₁ : LinearMap.IsProj M.ρ.invariants π₁) (h₁_eq : ∀ (g : G) (v : M), π₁ (M.ρ g v) = π₁ v)
    (h₂ : LinearMap.IsProj M.ρ.invariants π₂) (h₂_eq : ∀ (g : G) (v : M), π₂ (M.ρ g v) = π₂ v) :
    π₁ = π₂ := by
  -- Strategy: decompose v = vi + vw along ker π₁.
  -- On invariants both projections are the identity.
  -- On ker π₁: π₂(vw) ∈ invariants, but also π₁(π₂ vw) = π₂ vw (π₁ is id on invariants)
  -- while π₁ vw = 0, so π₂ vw ∈ invariants ∩ ker π₁ = ⊥, hence π₂ vw = 0 = π₁ vw.
  have hc₁ := h₁.isCompl
  -- Step 1: ker π₁ is G-stable
  have hker₁_stable : ∀ g, LinearMap.ker π₁ ≤ (LinearMap.ker π₁).comap (M.ρ g) := by
    intro g v hv
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
    rw [h₁_eq, hv]
  -- Step 2: Restrict M.ρ to ker π₁
  let M_W : Rep k G := M.subrepresentation (LinearMap.ker π₁) hker₁_stable
  -- Step 3: ker π₁ is semisimple (subspace of f.d., linearly reductive)
  haveI : FiniteDimensional k (LinearMap.ker π₁) := Submodule.finiteDimensional_of_le le_top
  haveI : FiniteDimensional k M_W := inferInstanceAs (FiniteDimensional k (LinearMap.ker π₁))
  have hss_W : IsSemisimpleRepresentation M_W.ρ := hlr.isSemisimple M_W
  -- Step 4: Form L = {w ∈ ker π₁ | π₂ w = 0} as a subrepresentation of M_W.ρ
  have hker₂_stable : ∀ g, LinearMap.ker π₂ ≤ (LinearMap.ker π₂).comap (M.ρ g) := by
    intro g v hv
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
    rw [h₂_eq, hv]
  let L : Subrepresentation M_W.ρ := {
    toSubmodule := (LinearMap.ker π₂).comap (LinearMap.ker π₁).subtype
    apply_mem_toSubmodule := by
      intro g v hv
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
      change π₂ (M.ρ g (v : M)) = 0
      rw [h₂_eq]; exact hv
  }
  -- Step 5: Get complement T of L in ker π₁
  obtain ⟨T, hLT⟩ := hss_W.exists_isCompl L
  -- Step 6: Show elements of T are G-invariant (hence zero)
  have hT_zero : T = ⊥ := by
    rw [eq_bot_iff]
    intro ⟨t, ht_ker⟩ ht_T
    change (⟨t, ht_ker⟩ : LinearMap.ker π₁) = 0
    -- Show M.ρ g t = t for all g, i.e., t ∈ M.ρ.invariants
    suffices ht_inv : t ∈ M.ρ.invariants by
      -- t ∈ M.ρ.invariants ∩ ker π₁ = ⊥
      have : t ∈ M.ρ.invariants ⊓ LinearMap.ker π₁ := ⟨ht_inv, ht_ker⟩
      rw [hc₁.disjoint.eq_bot] at this
      exact Subtype.ext ((Submodule.mem_bot k).mp this)
    rw [Representation.mem_invariants]
    intro g
    -- M.ρ g t - t ∈ L ∩ T = ⊥, hence M.ρ g t = t
    have h_diff_L : (M_W.ρ g ⟨t, ht_ker⟩ - ⟨t, ht_ker⟩ : LinearMap.ker π₁) ∈ L.toSubmodule := by
      simp only [L, Submodule.mem_comap, LinearMap.mem_ker]
      change π₂ (M.ρ g t - t) = 0
      simp only [map_sub, h₂_eq, sub_self]
    have h_diff_T : (M_W.ρ g ⟨t, ht_ker⟩ - ⟨t, ht_ker⟩ : LinearMap.ker π₁) ∈ T.toSubmodule :=
      T.toSubmodule.sub_mem (T.apply_mem_toSubmodule g ht_T) ht_T
    have h_mem_bot : (M_W.ρ g ⟨t, ht_ker⟩ - ⟨t, ht_ker⟩ : LinearMap.ker π₁) ∈
        L.toSubmodule ⊓ T.toSubmodule := ⟨h_diff_L, h_diff_T⟩
    rw [← Subrepresentation.toSubmodule_inf, hLT.disjoint.eq_bot] at h_mem_bot
    have h_eq : M_W.ρ g ⟨t, ht_ker⟩ = ⟨t, ht_ker⟩ := sub_eq_zero.mp h_mem_bot
    exact congr_arg Subtype.val h_eq
  -- Step 7: L = ⊤ in ker π₁, so ker π₁ ⊆ ker π₂
  have hL_top : L.toSubmodule = ⊤ := by
    have h := hLT.sup_eq_top (α := Subrepresentation M_W.ρ)
    rw [hT_zero, sup_bot_eq] at h
    exact congr_arg Subrepresentation.toSubmodule h
  -- Step 8: Conclude
  ext v
  obtain ⟨vi, hvi, vw, hvw, rfl⟩ := Submodule.mem_sup.mp
    (hc₁.sup_eq_top ▸ Submodule.mem_top : v ∈ M.ρ.invariants ⊔ LinearMap.ker π₁)
  simp only [map_add, h₁.map_id vi hvi, h₂.map_id vi hvi]
  have hvw_ker₁ : π₁ vw = 0 := LinearMap.mem_ker.mp hvw
  have hvw_ker₂ : π₂ vw = 0 := by
    have : (⟨vw, hvw⟩ : LinearMap.ker π₁) ∈ L.toSubmodule := by rw [hL_top]; exact Submodule.mem_top
    simpa [L, Submodule.mem_comap, LinearMap.mem_ker] using this
  rw [hvw_ker₁, hvw_ker₂]

/-- **Naturality of the Reynolds projection.** If `π₁` is a G-equivariant projection onto
the invariants of `ρ₁`, and `π₂` is a G-equivariant projection onto the invariants of `ρ₂`,
and `ι : V₁ →ₗ[k] V₂` intertwines `ρ₁` and `ρ₂`, then `π₂ ∘ ι = ι ∘ π₁`. -/
theorem IsLinearlyReductive.reynolds_natural
    (hlr : IsLinearlyReductive k G)
    (M₁ M₂ : Rep k G) [FiniteDimensional k M₁] [FiniteDimensional k M₂]
    (ι : M₁ →ₗ[k] M₂) (hι : ∀ (g : G) (v : M₁), ι (M₁.ρ g v) = M₂.ρ g (ι v))
    (π₁ : M₁ →ₗ[k] M₁) (π₂ : M₂ →ₗ[k] M₂)
    (h₁ : LinearMap.IsProj M₁.ρ.invariants π₁) (h₁_eq : ∀ (g : G) (v : M₁), π₁ (M₁.ρ g v) = π₁ v)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants π₂) (h₂_eq : ∀ (g : G) (v : M₂), π₂ (M₂.ρ g v) = π₂ v) :
    ∀ v : M₁, ι (π₁ v) = π₂ (ι v) := by
  have hc₁ := h₁.isCompl
  intro v
  -- Decompose v = π₁ v + (v - π₁ v)
  have hdecomp : ι v = ι (π₁ v) + ι (v - π₁ v) := by simp [map_sub, add_sub_cancel]
  -- ι(π₁ v) ∈ M₂.ρ.invariants, so π₂ fixes it
  have hι_inv : ι (π₁ v) ∈ M₂.ρ.invariants := by
    rw [Representation.mem_invariants]; intro g
    rw [← hι, (M₁.ρ.mem_invariants (π₁ v)).mp (h₁.map_mem v) g]
  rw [hdecomp, map_add, h₂.map_id _ hι_inv]
  -- Suffices to show π₂(ι(v - π₁ v)) = 0
  suffices h : π₂ (ι (v - π₁ v)) = 0 by rw [h, add_zero]
  -- w := v - π₁ v ∈ ker π₁
  set w := v - π₁ v with hw_def
  have hw_ker : w ∈ LinearMap.ker π₁ := by
    rw [LinearMap.mem_ker]; simp [hw_def, h₁.map_id (π₁ v) (h₁.map_mem v)]
  -- Same complement argument: restrict to ker π₁, form L, get complement T, show T = 0
  have hker₁_stable : ∀ g, LinearMap.ker π₁ ≤ (LinearMap.ker π₁).comap (M₁.ρ g) := by
    intro g x hx; simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢; rw [h₁_eq, hx]
  let M_W : Rep k G := M₁.subrepresentation (LinearMap.ker π₁) hker₁_stable
  haveI : FiniteDimensional k (LinearMap.ker π₁) := Submodule.finiteDimensional_of_le le_top
  haveI : FiniteDimensional k M_W := inferInstanceAs (FiniteDimensional k (LinearMap.ker π₁))
  have hss_W : IsSemisimpleRepresentation M_W.ρ := hlr.isSemisimple M_W
  -- L = {w ∈ ker π₁ | π₂(ι w) = 0}
  let L : Subrepresentation M_W.ρ := {
    toSubmodule := (LinearMap.ker (π₂ ∘ₗ ι)).comap (LinearMap.ker π₁).subtype
    apply_mem_toSubmodule := by
      intro g x hx
      simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
      change π₂ (ι (M₁.ρ g (x : M₁))) = 0
      rw [hι, h₂_eq]; exact hx
  }
  obtain ⟨T, hLT⟩ := hss_W.exists_isCompl L
  -- Elements of T are invariant, hence zero
  have hT_zero : T = ⊥ := by
    rw [eq_bot_iff]; intro ⟨t, ht_ker⟩ ht_T
    change (⟨t, ht_ker⟩ : LinearMap.ker π₁) = 0
    suffices ht_inv : t ∈ M₁.ρ.invariants by
      have : t ∈ M₁.ρ.invariants ⊓ LinearMap.ker π₁ := ⟨ht_inv, ht_ker⟩
      rw [hc₁.disjoint.eq_bot] at this
      exact Subtype.ext ((Submodule.mem_bot k).mp this)
    rw [Representation.mem_invariants]; intro g
    have h_diff_L : (M_W.ρ g ⟨t, ht_ker⟩ - ⟨t, ht_ker⟩ : LinearMap.ker π₁) ∈ L.toSubmodule := by
      simp only [L, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply]
      change π₂ (ι (M₁.ρ g t - t)) = 0
      simp only [map_sub, hι, h₂_eq, sub_self]
    have h_diff_T : (M_W.ρ g ⟨t, ht_ker⟩ - ⟨t, ht_ker⟩ : LinearMap.ker π₁) ∈ T.toSubmodule :=
      T.toSubmodule.sub_mem (T.apply_mem_toSubmodule g ht_T) ht_T
    have h_mem_bot : (M_W.ρ g ⟨t, ht_ker⟩ - ⟨t, ht_ker⟩ : LinearMap.ker π₁) ∈
        L.toSubmodule ⊓ T.toSubmodule := ⟨h_diff_L, h_diff_T⟩
    rw [← Subrepresentation.toSubmodule_inf, hLT.disjoint.eq_bot] at h_mem_bot
    exact congr_arg Subtype.val (sub_eq_zero.mp h_mem_bot)
  -- L = ⊤, so w ∈ ker(π₂ ∘ ι)
  have hL_top : L.toSubmodule = ⊤ := by
    have h := hLT.sup_eq_top (α := Subrepresentation M_W.ρ)
    rw [hT_zero, sup_bot_eq] at h
    exact congr_arg Subrepresentation.toSubmodule h
  have : (⟨w, hw_ker⟩ : LinearMap.ker π₁) ∈ L.toSubmodule := by rw [hL_top]; exact Submodule.mem_top
  simpa [L, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply] using this

/-- Given a linearly reductive group `G` acting locally finitely on a `k`-module `R`,
there exists a `k`-linear projection `R →ₗ[k] R` onto the `G`-invariants. -/
theorem exists_reynolds_of_locallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : R →ₗ[k] R, LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π ∧
      ∀ (g : G) (r : R), π ((Representation.ofDistribMulAction k G R) g r) = π r := by
  let ρ := Representation.ofDistribMulAction k G R
  -- Bundle the ambient representation as a `Rep k G` so we can call the Rep-based theorems.
  let Mamb : Rep k G := Rep.of ρ
  -- For each r, choose a f.d. G-stable submodule containing r
  choose V hV_fin hV_stable hV_mem using hlf
  -- Convert stability to comap form for subrepresentation
  have hV_comap : ∀ r, ∀ g, (V r) ≤ (V r).comap (ρ g) := by
    intro r g v hv; exact hV_stable r g ⟨v, hv⟩
  -- Local Reynolds projection on each V r
  have local_data : ∀ r, ∃ (π : ↥(V r) →ₗ[k] ↥(V r)),
      LinearMap.IsProj (ρ.subrepresentation (V r) (hV_comap r)).invariants π ∧
      ∀ (g : G) (v : ↥(V r)), π ((ρ.subrepresentation (V r) (hV_comap r)) g v) = π v := by
    intro r
    haveI : FiniteDimensional k ↥(V r) := hV_fin r
    exact IsLinearlyReductive.exists_reynolds_projection (k := k) (G := G) hlr
      (Mamb.subrepresentation (V r) (hV_comap r))
  -- Choose the projections
  choose π_loc hπ_proj hπ_eq using local_data
  -- Key: for any two G-stable f.d. submodules W₁, W₂ with r ∈ W₁ ∩ W₂,
  -- the local projections agree when mapped to R.
  -- This follows from reynolds_natural applied to inclusions W₁ ↪ W₁ ⊔ W₂ ↩ W₂.
  -- We use this to show f(r) doesn't depend on the choice of V r.
  have compat : ∀ (W₁ W₂ : Submodule k R)
      (hW₁_fin : Module.Finite k W₁) (hW₂_fin : Module.Finite k W₂)
      (hW₁_st : ∀ g, W₁ ≤ W₁.comap (ρ g)) (hW₂_st : ∀ g, W₂ ≤ W₂.comap (ρ g))
      (π₁ : ↥W₁ →ₗ[k] ↥W₁) (π₂ : ↥W₂ →ₗ[k] ↥W₂)
      (h₁ : LinearMap.IsProj (ρ.subrepresentation W₁ hW₁_st).invariants π₁)
      (h₁_eq : ∀ (g : G) (v : ↥W₁), π₁ ((ρ.subrepresentation W₁ hW₁_st) g v) = π₁ v)
      (h₂ : LinearMap.IsProj (ρ.subrepresentation W₂ hW₂_st).invariants π₂)
      (h₂_eq : ∀ (g : G) (v : ↥W₂), π₂ ((ρ.subrepresentation W₂ hW₂_st) g v) = π₂ v)
      (r : R) (hr₁ : r ∈ W₁) (hr₂ : r ∈ W₂),
      W₁.subtype (π₁ ⟨r, hr₁⟩) = W₂.subtype (π₂ ⟨r, hr₂⟩) := by
    intro W₁ W₂ hW₁_fin hW₂_fin hW₁_st hW₂_st π₁ π₂ h₁ h₁_eq h₂ h₂_eq r hr₁ hr₂
    -- Use W₁ ⊔ W₂ as common submodule, apply reynolds_natural to inclusions
    let W := W₁ ⊔ W₂
    have hW_stable : ∀ g, W ≤ W.comap (ρ g) := by
      intro g v hv
      rcases Submodule.mem_sup.mp hv with ⟨v₁, hv₁, v₂, hv₂, rfl⟩
      exact Submodule.mem_sup.mpr ⟨ρ g v₁, hW₁_st g hv₁, ρ g v₂, hW₂_st g hv₂,
        (map_add (ρ g) v₁ v₂).symm⟩
    haveI : FiniteDimensional k ↥W₁ := hW₁_fin
    haveI : FiniteDimensional k ↥W₂ := hW₂_fin
    haveI : FiniteDimensional k ↥W := Submodule.finiteDimensional_sup W₁ W₂
    -- Get Reynolds projection on W
    obtain ⟨π_W, hπ_W, hπ_W_eq⟩ :=
      IsLinearlyReductive.exists_reynolds_projection (k := k) (G := G) hlr
        (Mamb.subrepresentation W hW_stable)
    -- Inclusion maps W₁ ↪ W and W₂ ↪ W
    let ι₁ : ↥W₁ →ₗ[k] ↥W := Submodule.inclusion (le_sup_left : W₁ ≤ W)
    let ι₂ : ↥W₂ →ₗ[k] ↥W := Submodule.inclusion (le_sup_right : W₂ ≤ W)
    -- Inclusions intertwine the restricted representations
    have hι₁ : ∀ (g : G) (v : ↥W₁),
        ι₁ ((ρ.subrepresentation W₁ hW₁_st) g v) = (ρ.subrepresentation W hW_stable) g (ι₁ v) := by
      intro g v; ext; simp [ι₁, Representation.subrepresentation, Submodule.inclusion]
    have hι₂ : ∀ (g : G) (v : ↥W₂),
        ι₂ ((ρ.subrepresentation W₂ hW₂_st) g v) = (ρ.subrepresentation W hW_stable) g (ι₂ v) := by
      intro g v; ext; simp [ι₂, Representation.subrepresentation, Submodule.inclusion]
    -- Apply naturality: π_W ∘ ι₁ = ι₁ ∘ π₁ and π_W ∘ ι₂ = ι₂ ∘ π₂
    have hnat₁ := IsLinearlyReductive.reynolds_natural (k := k) (G := G) hlr
      (Mamb.subrepresentation W₁ hW₁_st) (Mamb.subrepresentation W hW_stable)
      ι₁ hι₁ π₁ π_W h₁ h₁_eq hπ_W hπ_W_eq
    have hnat₂ := IsLinearlyReductive.reynolds_natural (k := k) (G := G) hlr
      (Mamb.subrepresentation W₂ hW₂_st) (Mamb.subrepresentation W hW_stable)
      ι₂ hι₂ π₂ π_W h₂ h₂_eq hπ_W hπ_W_eq
    -- ι₁(π₁ r) = π_W(ι₁ r) = π_W(r in W) = π_W(ι₂ r) = ι₂(π₂ r)
    have h₁' := hnat₁ ⟨r, hr₁⟩
    have h₂' := hnat₂ ⟨r, hr₂⟩
    -- Both sides map to the same element in W, hence in R
    have : (ι₁ ⟨r, hr₁⟩ : ↥W) = (ι₂ ⟨r, hr₂⟩ : ↥W) := by
      ext; simp [ι₁, ι₂, Submodule.inclusion]
    rw [this] at h₁'
    -- Now h₁' : ι₁ (π₁ ⟨r, hr₁⟩) = π_W (ι₂ ⟨r, hr₂⟩)
    -- and h₂' : ι₂ (π₂ ⟨r, hr₂⟩) = π_W (ι₂ ⟨r, hr₂⟩)
    -- So ι₁ (π₁ r) = ι₂ (π₂ r) as elements of W, hence as elements of R
    have key : (ι₁ (π₁ ⟨r, hr₁⟩) : ↥W) = (ι₂ (π₂ ⟨r, hr₂⟩) : ↥W) := by rw [h₁', h₂']
    -- Inclusion preserves underlying value, so equality in W implies equality in R
    simpa [ι₁, ι₂, Submodule.inclusion] using congr_arg Subtype.val key
  -- Define the global function
  let f : R → R := fun r => (V r).subtype (π_loc r ⟨r, hV_mem r⟩)
  -- f is additive: for r, s, use compatibility with V r ⊔ V s
  -- Helper: f(r) equals the projection on any G-stable f.d. submodule containing r
  have f_eq : ∀ (W : Submodule k R) (hW_fin : Module.Finite k W)
      (hW_st : ∀ g, W ≤ W.comap (ρ g)) (πW : ↥W →ₗ[k] ↥W)
      (hπW : LinearMap.IsProj (ρ.subrepresentation W hW_st).invariants πW)
      (hπW_eq : ∀ (g : G) (v : ↥W), πW ((ρ.subrepresentation W hW_st) g v) = πW v)
      (r : R) (hr : r ∈ W),
      f r = W.subtype (πW ⟨r, hr⟩) :=
    fun W hW_fin hW_st πW hπW hπW_eq r hr =>
      compat (V r) W (hV_fin r) hW_fin (hV_comap r) hW_st
        (π_loc r) πW (hπ_proj r) (hπ_eq r) hπW hπW_eq r (hV_mem r) hr
  have f_add : ∀ r s, f (r + s) = f r + f s := by
    intro r s
    -- Use V r ⊔ V s as common submodule
    let W := V r ⊔ V s
    have hW_st : ∀ g, W ≤ W.comap (ρ g) := by
      intro g v hv
      rcases Submodule.mem_sup.mp hv with ⟨v₁, hv₁, v₂, hv₂, rfl⟩
      exact Submodule.mem_sup.mpr ⟨ρ g v₁, (hV_comap r) g hv₁, ρ g v₂, (hV_comap s) g hv₂,
        (map_add (ρ g) v₁ v₂).symm⟩
    haveI : FiniteDimensional k ↥(V r) := hV_fin r
    haveI : FiniteDimensional k ↥(V s) := hV_fin s
    haveI : FiniteDimensional k ↥W := Submodule.finiteDimensional_sup (V r) (V s)
    obtain ⟨πW, hπW, hπW_eq⟩ :=
      IsLinearlyReductive.exists_reynolds_projection (k := k) (G := G) hlr
        (Mamb.subrepresentation W hW_st)
    have hr : r ∈ W := Submodule.mem_sup_left (hV_mem r)
    have hs : s ∈ W := Submodule.mem_sup_right (hV_mem s)
    have hrs : r + s ∈ W := W.add_mem hr hs
    rw [f_eq W inferInstance hW_st πW hπW hπW_eq r hr,
        f_eq W inferInstance hW_st πW hπW hπW_eq s hs,
        f_eq W inferInstance hW_st πW hπW hπW_eq (r + s) hrs]
    have : (⟨r + s, hrs⟩ : ↥W) = ⟨r, hr⟩ + ⟨s, hs⟩ := rfl
    rw [this, map_add]; simp
  have f_smul : ∀ (c : k) (r : R), f (c • r) = c • f r := by
    intro c r
    rw [f_eq (V r) (hV_fin r) (hV_comap r) (π_loc r) (hπ_proj r) (hπ_eq r) (c • r)
          ((V r).smul_mem c (hV_mem r)),
        f_eq (V r) (hV_fin r) (hV_comap r) (π_loc r) (hπ_proj r) (hπ_eq r) r (hV_mem r)]
    have : (⟨c • r, (V r).smul_mem c (hV_mem r)⟩ : ↥(V r)) = c • ⟨r, hV_mem r⟩ := rfl
    rw [this, map_smul]; simp
  -- Package as LinearMap
  let π : R →ₗ[k] R := {
    toFun := f
    map_add' := f_add
    map_smul' := f_smul
  }
  refine ⟨π, ⟨fun r => ?_, fun r hr => ?_⟩, fun g r => ?_⟩
  · -- π r ∈ ρ.invariants: the local projection maps into invariants of the subrepresentation,
    -- which embed into invariants of ρ.
    change f r ∈ ρ.invariants
    simp only [f]
    have hmem := (hπ_proj r).map_mem ⟨r, hV_mem r⟩
    rw [Representation.mem_invariants] at hmem ⊢
    intro g
    have := congr_arg (V r).subtype (hmem g)
    simpa only [Submodule.subtype_apply] using this
  · -- r ∈ ρ.invariants → π r = r: the local projection fixes invariants
    change f r = r
    simp only [f]
    have : (⟨r, hV_mem r⟩ : ↥(V r)) ∈ (ρ.subrepresentation (V r) (hV_comap r)).invariants := by
      rw [Representation.mem_invariants]
      intro g
      ext
      simp only [Representation.subrepresentation_apply, LinearMap.restrict_coe_apply]
      exact ((ρ.mem_invariants r).mp hr) g
    have := congr_arg (V r).subtype ((hπ_proj r).map_id ⟨r, hV_mem r⟩ this)
    simpa using this
  · -- π (ρ g r) = π r: use G-equivariance of the local projection
    -- via compatibility with V(g • r) and V r
    change f (g • r) = f r
    -- f(g•r) uses V(g•r); by compat, equals projection on V r at g•r
    have h1 := compat (V (g • r)) (V r)
      (hV_fin (g • r)) (hV_fin r) (hV_comap (g • r)) (hV_comap r)
      (π_loc (g • r)) (π_loc r)
      (hπ_proj (g • r)) (hπ_eq (g • r)) (hπ_proj r) (hπ_eq r)
      (g • r) (hV_mem (g • r)) (hV_stable r g ⟨r, hV_mem r⟩)
    -- Local G-equivariance: π_{V r}(g•r) = π_{V r}(r)
    have h2 : π_loc r ⟨g • r, hV_stable r g ⟨r, hV_mem r⟩⟩ = π_loc r ⟨r, hV_mem r⟩ := by
      have := hπ_eq r g ⟨r, hV_mem r⟩
      convert this using 1
    simp only [f]
    rw [h1]
    exact congr_arg (V r).subtype h2

end GeneralReynolds

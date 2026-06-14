import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

universe u

namespace Representation

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

/-- A group is linearly reductive if every finite-dimensional
representation is semisimple. -/
class IsLinearlyReductive (k G : Type u) [Field k] [Group G] : Prop where
  isSemisimple :
    ∀ (M : Rep k G) [FiniteDimensional k M],
      IsSemisimpleRepresentation M.ρ

/-- Finite groups with invertible cardinality are linearly reductive. -/
instance IsLinearlyReductive.of_fintype
    (k G : Type u)
    [Field k]
    [Group G]
    [Fintype G]
    [Invertible (Fintype.card G : k)] :
    IsLinearlyReductive k G where
  isSemisimple M _ := by
    haveI : NeZero (Nat.card G : k) := by
      rw [Nat.card_eq_fintype_card]
      exact ⟨Invertible.ne_zero (Fintype.card G : k)⟩
    exact
      M.ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mpr
        inferInstance

/-- The invariant vectors form a subrepresentation. -/
noncomputable def invariantSubrepresentation
    {V : Type*}
    [AddCommGroup V]
    [Module k V]
    (ρ : Representation k G V) :
    Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g v hv := by
    rw [Representation.mem_invariants] at hv ⊢
    intro g'
    simp [hv]

/-- Convert a complementary invariant subrepresentation into a
complementary invariant submodule. -/
lemma invariantSubrepresentation_isCompl
    (M : Rep k G)
    (W : Subrepresentation M.ρ)
    (hW : IsCompl (invariantSubrepresentation M.ρ) W) :
    IsCompl M.ρ.invariants W.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    have h :=
      congr_arg Subrepresentation.toSubmodule
        (disjoint_iff.mp hW.disjoint)
    simpa [Subrepresentation.toSubmodule_inf] using h
  · rw [codisjoint_iff]
    have h :=
      congr_arg Subrepresentation.toSubmodule
        (codisjoint_iff.mp hW.codisjoint)
    simpa [Subrepresentation.toSubmodule_sup] using h

/-- A linearly reductive group admits a Reynolds operator on every
finite-dimensional representation. -/
theorem IsLinearlyReductive.exists_reynoldsOperator
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G)
    [FiniteDimensional k M] :
    ∃ π : M →ₗ[k] M,
      LinearMap.IsProj M.ρ.invariants π ∧
      ∀ (g : G) (v : M), π (M.ρ g v) = π v := by
  have hss : IsSemisimpleRepresentation M.ρ := hlr.isSemisimple M
  obtain ⟨W, hW⟩ :=
    hss.exists_isCompl M.ρ.invariantSubrepresentation
  have hc : IsCompl M.ρ.invariants W.toSubmodule :=
    invariantSubrepresentation_isCompl M W hW
  let π :=
    M.ρ.invariants.subtype ∘ₗ
      M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc
  refine ⟨π, ⟨?_, ?_⟩, ?_⟩
  · intro x
    exact
      (M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc x).property
  · intro x hx
    have h :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩
    simp [π, h]
  · intro g v
    have hdecomp :=
      Submodule.mem_sup.mp
        (show v ∈ M.ρ.invariants ⊔ W.toSubmodule from
          hc.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨vi, hvi, vw, hvw, rfl⟩ := hdecomp
    have hvi_inv : M.ρ g vi = vi :=
      ((M.ρ.mem_invariants vi).mp hvi) g
    have hvw_W : M.ρ g vw ∈ W.toSubmodule :=
      W.apply_mem_toSubmodule g hvw
    simp only [π, LinearMap.comp_apply, map_add]
    rw [Submodule.linearProjOfIsCompl_apply_left hc ⟨vi, hvi⟩]
    rw [hvi_inv]
    rw [Submodule.linearProjOfIsCompl_apply_left hc ⟨vi, hvi⟩]
    have h₁ :
        M.ρ.invariants.linearProjOfIsCompl
          W.toSubmodule hc vw = 0 :=
      Submodule.linearProjOfIsCompl_apply_right'
        hc vw hvw
    have h₂ :
        M.ρ.invariants.linearProjOfIsCompl
          W.toSubmodule hc (M.ρ g vw) = 0 :=
      Submodule.linearProjOfIsCompl_apply_right'
        hc _ hvw_W
    simp [h₁, h₂]

end Representation

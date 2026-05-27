import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple

universe u

variable {k : Type u} [Field k] (G : Type u) [Group G]

open Monoid MonoidAlgebra Representation

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

section GeneralReynolds

/-- Def3: A group `G` is linearly reductive over `k` if every finite-dimensional representation
is completely reducible (every subrepresentation has a complement). -/
class IsLinearlyReductive (k G : Type u) [Field k] [Group G] : Prop where
  isSemisimple : ∀ (M : Rep k G) [FiniteDimensional k M], IsSemisimpleRepresentation M.ρ

/-- Finite groups with invertible cardinality are linearly reductive (Maschke's theorem). -/
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
    intro g'
    rw [hv g, hv g']

/-- A linearly reductive group admits a `Rep`-morphism projection onto the invariants
of any finite-dimensional representation. Equivariance is bundled into the morphism. -/
theorem IsLinearlyReductive.exists_reynolds_projection
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G) [FiniteDimensional k M] :
    ∃ π : M ⟶ M, LinearMap.IsProj M.ρ.invariants π.hom.hom := by
  have hss : IsSemisimpleRepresentation M.ρ := hlr.isSemisimple M
  obtain ⟨W, hW⟩ := hss.exists_isCompl M.ρ.invariantSubrepresentation
  have hc : IsCompl M.ρ.invariants W.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have h := congr_arg Subrepresentation.toSubmodule (disjoint_iff.mp hW.disjoint)
      simpa [Subrepresentation.toSubmodule_inf] using h
    · rw [codisjoint_iff]
      have h := congr_arg Subrepresentation.toSubmodule (codisjoint_iff.mp hW.codisjoint)
      simpa [Subrepresentation.toSubmodule_sup] using h
  let πlin : M →ₗ[k] M :=
    M.ρ.invariants.subtype ∘ₗ M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc
  have hproj : LinearMap.IsProj M.ρ.invariants πlin :=
    ⟨fun x => (M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc x).property,
     fun x hx => by
       have := Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩
       simp [πlin, this]⟩
  have hequiv : ∀ (g : G) (v : M), πlin (M.ρ g v) = πlin v := fun g v => by
    have hdecomp := Submodule.mem_sup.mp
      (show v ∈ M.ρ.invariants ⊔ W.toSubmodule from hc.sup_eq_top ▸ Submodule.mem_top)
    obtain ⟨vi, hvi, vw, hvw, rfl⟩ := hdecomp
    have hvi_inv : M.ρ g vi = vi := ((M.ρ.mem_invariants vi).mp hvi) g
    have hvw_W : M.ρ g vw ∈ W.toSubmodule := W.apply_mem_toSubmodule g hvw
    have hproj_vi : M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc vi = ⟨vi, hvi⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hc ⟨vi, hvi⟩
    have hproj_vw : M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc vw = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' hc vw hvw
    have hproj_gvw : M.ρ.invariants.linearProjOfIsCompl W.toSubmodule hc (M.ρ g vw) = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' hc _ hvw_W
    simp only [πlin, LinearMap.comp_apply, map_add, map_add]
    -- LHS: proj(ρ g vi) + proj(ρ g vw)  =  proj(vi) + 0
    -- RHS: proj(vi)     + proj(vw)       =  proj(vi) + 0
    rw [hvi_inv, hproj_vi, hproj_gvw, hproj_vw]
  refine ⟨{ hom := ModuleCat.ofHom πlin
            comm := fun g => by
              ext v
              change πlin (M.ρ g v) = M.ρ g (πlin v)
              have hinv : πlin v ∈ M.ρ.invariants := hproj.map_mem v
              have hfix : M.ρ g (πlin v) = πlin v :=
                ((M.ρ.mem_invariants _).mp hinv) g
              rw [hequiv g v, hfix] }, hproj⟩

/-- **Uniqueness of the Reynolds projection.** Any two `Rep`-morphism projections onto
`ρ.invariants` must agree. The proof reduces to showing that a G-equivariant map
from a representation with no invariants to a trivial representation is zero, which follows
from complete reducibility. -/
theorem IsLinearlyReductive.reynolds_unique
    (hlr : IsLinearlyReductive k G)
    (M : Rep k G) [FiniteDimensional k M]
    (π₁ π₂ : M ⟶ M)
    (h₁ : LinearMap.IsProj M.ρ.invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj M.ρ.invariants π₂.hom.hom) :
    π₁ = π₂ := by
  -- Equivariance of `Rep` morphisms + landing in invariants gives constancy on G-orbits.
  have h₁_eq : ∀ (g : G) (v : M), π₁.hom.hom (M.ρ g v) = π₁.hom.hom v := fun g v => by
    rw [Rep.hom_comm_apply π₁ g v]
    exact ((M.ρ.mem_invariants _).mp (h₁.map_mem v)) g
  have h₂_eq : ∀ (g : G) (v : M), π₂.hom.hom (M.ρ g v) = π₂.hom.hom v := fun g v => by
    rw [Rep.hom_comm_apply π₂ g v]
    exact ((M.ρ.mem_invariants _).mp (h₂.map_mem v)) g
  -- Reduce to linear-map equality.
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  set π₁ : M →ₗ[k] M := π₁.hom.hom with hπ₁
  set π₂ : M →ₗ[k] M := π₂.hom.hom with hπ₂
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

/-- **Naturality of the Reynolds projection.** If `P₁` and `P₂` are `Rep`-morphism projections
onto the invariants of `M₁`, `M₂` respectively and `I : M₁ ⟶ M₂` is a morphism of representations,
then `I ∘ P₁ = P₂ ∘ I` pointwise. Equivariance of `I`, `P₁`, `P₂` is bundled in the morphisms. -/
theorem IsLinearlyReductive.reynolds_natural
    (hlr : IsLinearlyReductive k G)
    (M₁ M₂ : Rep k G) [FiniteDimensional k M₁] [FiniteDimensional k M₂]
    (I : M₁ ⟶ M₂)
    (P₁ : M₁ ⟶ M₁) (P₂ : M₂ ⟶ M₂)
    (h₁ : LinearMap.IsProj M₁.ρ.invariants P₁.hom.hom)
    (h₂ : LinearMap.IsProj M₂.ρ.invariants P₂.hom.hom) :
    ∀ v : M₁, I.hom.hom (P₁.hom.hom v) = P₂.hom.hom (I.hom.hom v) := by
  -- Derive equivariance/orbit-constancy from morphism comm + landing in invariants.
  have hι : ∀ (g : G) (v : M₁), I.hom.hom (M₁.ρ g v) = M₂.ρ g (I.hom.hom v) :=
    fun g v => Rep.hom_comm_apply I g v
  have h₁_eq : ∀ (g : G) (v : M₁), P₁.hom.hom (M₁.ρ g v) = P₁.hom.hom v := fun g v => by
    rw [Rep.hom_comm_apply P₁ g v]
    exact ((M₁.ρ.mem_invariants _).mp (h₁.map_mem v)) g
  have h₂_eq : ∀ (g : G) (v : M₂), P₂.hom.hom (M₂.ρ g v) = P₂.hom.hom v := fun g v => by
    rw [Rep.hom_comm_apply P₂ g v]
    exact ((M₂.ρ.mem_invariants _).mp (h₂.map_mem v)) g
  set ι : M₁ →ₗ[k] M₂ := I.hom.hom
  set π₁ : M₁ →ₗ[k] M₁ := P₁.hom.hom
  set π₂ : M₂ →ₗ[k] M₂ := P₂.hom.hom
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
there exists a `Rep`-morphism projection onto the `G`-invariants on the bundled representation
`Rep.of (Representation.ofDistribMulAction k G R)`. -/
theorem exists_reynolds_of_locallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom := by
  let ρ := Representation.ofDistribMulAction k G R
  -- Bundle the ambient representation as a `Rep k G` so we can call the Rep-based theorems.
  let Mamb : Rep k G := Rep.of ρ
  -- For each r, choose a f.d. G-stable submodule containing r
  choose V hV_fin hV_stable hV_mem using hlf
  -- Convert stability to comap form for subrepresentation
  have hV_comap : ∀ r, ∀ g, (V r) ≤ (V r).comap (ρ g) := by
    intro r g v hv; exact hV_stable r g ⟨v, hv⟩
  -- Local Reynolds projection on each V r as a Rep morphism, plus its underlying data.
  have local_data : ∀ r, ∃ (π : ↥(V r) →ₗ[k] ↥(V r)),
      LinearMap.IsProj (ρ.subrepresentation (V r) (hV_comap r)).invariants π ∧
      ∀ (g : G) (v : ↥(V r)), π ((ρ.subrepresentation (V r) (hV_comap r)) g v) = π v := by
    intro r
    -- `Module.Finite k ↥(V r)` (from `hV_fin r`) implies `FiniteDimensional k ↥(V r)`
    haveI : FiniteDimensional k ↥(V r) := hV_fin r
    obtain ⟨Pr, hπ⟩ := IsLinearlyReductive.exists_reynolds_projection (k := k) (G := G) hlr
      (Mamb.subrepresentation (V r) (hV_comap r))
    refine ⟨Pr.hom.hom, hπ, fun g v => ?_⟩
    change Pr.hom.hom ((Mamb.subrepresentation (V r) (hV_comap r)).ρ g v) = Pr.hom.hom v
    rw [Rep.hom_comm_apply Pr g v]
    exact (((Mamb.subrepresentation (V r) (hV_comap r)).ρ.mem_invariants _).mp
      (hπ.map_mem v)) g
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
    -- `Module.Finite` implies `FiniteDimensional` for the coercion
    haveI hfd₁ : FiniteDimensional k ↥W₁ := hW₁_fin
    haveI hfd₂ : FiniteDimensional k ↥W₂ := hW₂_fin
    haveI : FiniteDimensional k ↥W := Submodule.finiteDimensional_sup W₁ W₂
    -- Get Reynolds projection on W (as a Rep morphism)
    obtain ⟨PW, hπ_W⟩ :=
      IsLinearlyReductive.exists_reynolds_projection (k := k) (G := G) hlr
        (Mamb.subrepresentation W hW_stable)
    let π_W : ↥W →ₗ[k] ↥W := PW.hom.hom
    -- Inclusion maps W₁ ↪ W and W₂ ↪ W (linear) and as `Rep` morphisms
    let ι₁ : ↥W₁ →ₗ[k] ↥W := Submodule.inclusion (le_sup_left : W₁ ≤ W)
    let ι₂ : ↥W₂ →ₗ[k] ↥W := Submodule.inclusion (le_sup_right : W₂ ≤ W)
    have hι₁ : ∀ (g : G) (v : ↥W₁),
        ι₁ ((ρ.subrepresentation W₁ hW₁_st) g v) = (ρ.subrepresentation W hW_stable) g (ι₁ v) := by
      intro g v; ext; simp [ι₁, Representation.subrepresentation, Submodule.inclusion]
    have hι₂ : ∀ (g : G) (v : ↥W₂),
        ι₂ ((ρ.subrepresentation W₂ hW₂_st) g v) = (ρ.subrepresentation W hW_stable) g (ι₂ v) := by
      intro g v; ext; simp [ι₂, Representation.subrepresentation, Submodule.inclusion]
    -- Wrap π₁, π₂, ι₁, ι₂ as `Rep` morphisms so we can call `reynolds_natural`.
    let P₁ : Mamb.subrepresentation W₁ hW₁_st ⟶ Mamb.subrepresentation W₁ hW₁_st :=
      { hom := ModuleCat.ofHom π₁
        comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun v => by
          change π₁ ((Mamb.subrepresentation W₁ hW₁_st).ρ g v) =
              (Mamb.subrepresentation W₁ hW₁_st).ρ g (π₁ v)
          rw [show (Mamb.subrepresentation W₁ hW₁_st).ρ g v
                = (ρ.subrepresentation W₁ hW₁_st) g v from rfl, h₁_eq g v]
          exact (((Mamb.subrepresentation W₁ hW₁_st).ρ.mem_invariants _).mp
            (h₁.map_mem v) g).symm }
    let P₂ : Mamb.subrepresentation W₂ hW₂_st ⟶ Mamb.subrepresentation W₂ hW₂_st :=
      { hom := ModuleCat.ofHom π₂
        comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun v => by
          change π₂ ((Mamb.subrepresentation W₂ hW₂_st).ρ g v) =
              (Mamb.subrepresentation W₂ hW₂_st).ρ g (π₂ v)
          rw [show (Mamb.subrepresentation W₂ hW₂_st).ρ g v
                = (ρ.subrepresentation W₂ hW₂_st) g v from rfl, h₂_eq g v]
          exact (((Mamb.subrepresentation W₂ hW₂_st).ρ.mem_invariants _).mp
            (h₂.map_mem v) g).symm }
    let I₁ : Mamb.subrepresentation W₁ hW₁_st ⟶ Mamb.subrepresentation W hW_stable :=
      { hom := ModuleCat.ofHom ι₁
        comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun v => hι₁ g v }
    let I₂ : Mamb.subrepresentation W₂ hW₂_st ⟶ Mamb.subrepresentation W hW_stable :=
      { hom := ModuleCat.ofHom ι₂
        comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun v => hι₂ g v }
    -- Apply naturality
    have hnat₁ := IsLinearlyReductive.reynolds_natural (k := k) (G := G) hlr
      (Mamb.subrepresentation W₁ hW₁_st) (Mamb.subrepresentation W hW_stable)
      I₁ P₁ PW h₁ hπ_W
    have hnat₂ := IsLinearlyReductive.reynolds_natural (k := k) (G := G) hlr
      (Mamb.subrepresentation W₂ hW₂_st) (Mamb.subrepresentation W hW_stable)
      I₂ P₂ PW h₂ hπ_W
    -- ι₁(π₁ r) = π_W(ι₁ r) = π_W(r in W) = π_W(ι₂ r) = ι₂(π₂ r)
    have h₁' : ι₁ (π₁ ⟨r, hr₁⟩) = π_W (ι₁ ⟨r, hr₁⟩) := hnat₁ ⟨r, hr₁⟩
    have h₂' : ι₂ (π₂ ⟨r, hr₂⟩) = π_W (ι₂ ⟨r, hr₂⟩) := hnat₂ ⟨r, hr₂⟩
    -- Both inclusions send r to the same element of W
    have hreq : (ι₁ ⟨r, hr₁⟩ : ↥W) = (ι₂ ⟨r, hr₂⟩ : ↥W) := by
      ext; simp [ι₁, ι₂, Submodule.inclusion]
    -- Chain: ι₁(π₁ r) = π_W(ι₁ r) = π_W(ι₂ r) = ι₂(π₂ r)
    have key : (ι₁ (π₁ ⟨r, hr₁⟩) : ↥W) = (ι₂ (π₂ ⟨r, hr₂⟩) : ↥W) := by
      rw [h₁', hreq, ← h₂']
    -- Inclusion into W and into R both preserve underlying values
    simpa [ι₁, ι₂, Submodule.inclusion] using congr_arg Subtype.val key
  -- Define the global function
  let f : R → R := fun r => (V r).subtype (π_loc r ⟨r, hV_mem r⟩)
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
    obtain ⟨PW, hπW⟩ :=
      IsLinearlyReductive.exists_reynolds_projection (k := k) (G := G) hlr
        (Mamb.subrepresentation W hW_st)
    let πW : ↥W →ₗ[k] ↥W := PW.hom.hom
    have hπW_eq : ∀ (g : G) (v : ↥W),
        πW ((ρ.subrepresentation W hW_st) g v) = πW v := fun g v => by
      change πW ((Mamb.subrepresentation W hW_st).ρ g v) = πW v
      rw [Rep.hom_comm_apply PW g v]
      exact (((Mamb.subrepresentation W hW_st).ρ.mem_invariants _).mp (hπW.map_mem v)) g
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
  -- Package as a linear map first.
  let π_lin : R →ₗ[k] R := {
    toFun := f
    map_add' := f_add
    map_smul' := f_smul
  }
  -- Show `π_lin` is a projection onto `ρ.invariants`.
  have hπ_proj_global : LinearMap.IsProj ρ.invariants π_lin := by
    refine ⟨fun r => ?_, fun r hr => ?_⟩
    · -- π_lin r ∈ ρ.invariants
      change f r ∈ ρ.invariants
      simp only [f]
      have hmem := (hπ_proj r).map_mem ⟨r, hV_mem r⟩
      rw [Representation.mem_invariants] at hmem ⊢
      intro g
      have := congr_arg (V r).subtype (hmem g)
      simpa only [Submodule.subtype_apply] using this
    · -- r ∈ ρ.invariants → π_lin r = r
      change f r = r
      simp only [f]
      have hmem :
          (⟨r, hV_mem r⟩ : ↥(V r)) ∈ (ρ.subrepresentation (V r) (hV_comap r)).invariants := by
        rw [Representation.mem_invariants]
        intro g
        ext
        simp only [Representation.subrepresentation_apply, LinearMap.restrict_coe_apply]
        exact ((ρ.mem_invariants r).mp hr) g
      have := congr_arg (V r).subtype ((hπ_proj r).map_id ⟨r, hV_mem r⟩ hmem)
      simpa using this
  -- `π_lin` is constant on G-orbits:
  -- for r, g • r ∈ V r (by stability), and equivariance of π_loc r gives the equality.
  have hπ_equiv : ∀ (g : G) (r : R), π_lin (ρ g r) = π_lin r := fun g r => by
    change f (g • r) = f r
    have hgr_mem : g • r ∈ V r := hV_stable r g ⟨r, hV_mem r⟩
    rw [f_eq (V r) (hV_fin r) (hV_comap r) (π_loc r) (hπ_proj r) (hπ_eq r) (g • r) hgr_mem,
        f_eq (V r) (hV_fin r) (hV_comap r) (π_loc r) (hπ_proj r) (hπ_eq r) r (hV_mem r)]
    congr 1
    have heq : (ρ.subrepresentation (V r) (hV_comap r)) g ⟨r, hV_mem r⟩ =
        ⟨g • r, hgr_mem⟩ := rfl
    rw [← heq]
    exact hπ_eq r g ⟨r, hV_mem r⟩
  -- Promote to a `Rep` morphism `Mamb ⟶ Mamb`.
  refine ⟨{ hom := ModuleCat.ofHom π_lin
            comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun r => by
              change π_lin (Mamb.ρ g r) = Mamb.ρ g (π_lin r)
              rw [show Mamb.ρ g r = ρ g r from rfl, hπ_equiv g r]
              exact ((Mamb.ρ.mem_invariants _).mp (hπ_proj_global.map_mem r) g).symm }, ?_⟩
  exact hπ_proj_global

/-- **Locally-finite Reynolds uniqueness.** Any two Rep-morphism projections onto the
invariants of `Rep.of (ofDistribMulAction k G R)` agree, when `G` is linearly reductive
and the `G`-action on `R` is locally finite.

Proof strategy (TODO): for each `r`, pick `W` f.d. G-stable containing `r`, `π₁(r)`,
`π₂(r)` (the latter two extend `r`'s f.d. neighborhood by 1-dim G-stable rays through
invariants). Iterate `W ↦ W + π₁(W) + π₂(W)` finitely many times until stable, obtaining
a f.d. G-stable subspace `W'` closed under both projections. Then `π₁|_{W'}, π₂|_{W'}`
are Rep-projections onto `W'^G`, and `reynolds_unique` (f.d. version) forces equality. -/
theorem IsLinearlyReductive.reynolds_unique_locallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R)
    (π₁ π₂ : Rep.of (Representation.ofDistribMulAction k G R) ⟶
              Rep.of (Representation.ofDistribMulAction k G R))
    (h₁ : LinearMap.IsProj
            (Representation.ofDistribMulAction k G R).invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj
            (Representation.ofDistribMulAction k G R).invariants π₂.hom.hom) :
    π₁ = π₂ := by
  let σ : Representation k G R := Representation.ofDistribMulAction k G R
  let Mamb : Rep k G := Rep.of σ
  let p₁ : R →ₗ[k] R := π₁.hom.hom
  let p₂ : R →ₗ[k] R := π₂.hom.hom
  -- Equivariance of `Rep` morphisms.
  have hp₁_equiv : ∀ (g : G) (r : R), p₁ (σ g r) = σ g (p₁ r) := fun g r =>
    Rep.hom_comm_apply π₁ g r
  have hp₂_equiv : ∀ (g : G) (r : R), p₂ (σ g r) = σ g (p₂ r) := fun g r =>
    Rep.hom_comm_apply π₂ g r
  -- Reduce to pointwise equality on R.
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  ext r
  change p₁ r = p₂ r
  -- Pick a f.d. G-stable submodule V containing r.
  obtain ⟨V, hV_fin, hV_stable, hV_mem⟩ := hlf r
  have hV_comap : ∀ g, V ≤ V.comap (σ g) := fun g v hv => hV_stable g ⟨v, hv⟩
  -- W = V + p₁(V) + p₂(V) — f.d., G-stable, closed under p₁ and p₂.
  let W : Submodule k R := V ⊔ Submodule.map p₁ V ⊔ Submodule.map p₂ V
  -- Both pᵢ(V) lie inside the invariants (so are G-stable).
  have hp₁V_inv : Submodule.map p₁ V ≤ σ.invariants := by
    rintro x ⟨v, _, rfl⟩; exact h₁.map_mem v
  have hp₂V_inv : Submodule.map p₂ V ≤ σ.invariants := by
    rintro x ⟨v, _, rfl⟩; exact h₂.map_mem v
  -- W is G-stable.
  have hW_stable : ∀ g, W ≤ W.comap (σ g) := by
    intro g w hw
    rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
    rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    have h_a₁ : σ g a₁ ∈ V := hV_stable g ⟨a₁, ha₁⟩
    have h_a₂ : σ g a₂ ∈ Submodule.map p₁ V := by
      rw [(σ.mem_invariants a₂).mp (hp₁V_inv ha₂) g]; exact ha₂
    have h_c : σ g c ∈ Submodule.map p₂ V := by
      rw [(σ.mem_invariants c).mp (hp₂V_inv hc) g]; exact hc
    change σ g (a₁ + a₂ + c) ∈ W
    rw [map_add, map_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left h_a₁)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right h_a₂)
    · exact Submodule.mem_sup_right h_c
  -- Finite-dimensionality of W.
  haveI : Module.Finite k V := hV_fin
  have map_finite : ∀ (p : R →ₗ[k] R), Module.Finite k ↥(Submodule.map p V) := by
    intro p
    let f : V →ₗ[k] ↥(Submodule.map p V) :=
      LinearMap.codRestrict (Submodule.map p V) (p ∘ₗ V.subtype)
        (fun v => Submodule.mem_map.mpr ⟨v.1, v.2, rfl⟩)
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hx
      exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩
    exact Module.Finite.of_surjective f hf
  haveI : FiniteDimensional k V := hV_fin
  haveI : FiniteDimensional k ↥(Submodule.map p₁ V) := map_finite p₁
  haveI : FiniteDimensional k ↥(Submodule.map p₂ V) := map_finite p₂
  haveI : FiniteDimensional k ↥(V ⊔ Submodule.map p₁ V : Submodule k R) :=
    Submodule.finiteDimensional_sup _ _
  haveI : FiniteDimensional k ↥W := Submodule.finiteDimensional_sup _ _
  -- p₁ maps W into W.
  have hp₁_W : ∀ w ∈ W, p₁ w ∈ W := by
    intro w hw
    rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
    rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rw [map_add, map_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨a₁, ha₁, rfl⟩)
    · rw [h₁.map_id a₂ (hp₁V_inv ha₂)]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right ha₂)
    · rw [h₁.map_id c (hp₂V_inv hc)]
      exact Submodule.mem_sup_right hc
  -- p₂ maps W into W.
  have hp₂_W : ∀ w ∈ W, p₂ w ∈ W := by
    intro w hw
    rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
    rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rw [map_add, map_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_right ⟨a₁, ha₁, rfl⟩
    · rw [h₂.map_id a₂ (hp₁V_inv ha₂)]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right ha₂)
    · rw [h₂.map_id c (hp₂V_inv hc)]
      exact Submodule.mem_sup_right hc
  have hr_W : r ∈ W := Submodule.mem_sup_left (Submodule.mem_sup_left hV_mem)
  -- Restrict p₁, p₂ to W.
  let q₁ : ↥W →ₗ[k] ↥W := LinearMap.restrict p₁ hp₁_W
  let q₂ : ↥W →ₗ[k] ↥W := LinearMap.restrict p₂ hp₂_W
  let MW : Rep k G := Mamb.subrepresentation W hW_stable
  haveI : FiniteDimensional k MW := inferInstanceAs (FiniteDimensional k ↥W)
  -- Wrap q₁, q₂ as `Rep`-morphisms on MW.
  let Q₁ : MW ⟶ MW :=
    { hom := ModuleCat.ofHom q₁
      comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun w => by
        apply Subtype.ext
        change p₁ (σ g (w : R)) = σ g (p₁ (w : R))
        exact hp₁_equiv g w }
  let Q₂ : MW ⟶ MW :=
    { hom := ModuleCat.ofHom q₂
      comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun w => by
        apply Subtype.ext
        change p₂ (σ g (w : R)) = σ g (p₂ (w : R))
        exact hp₂_equiv g w }
  -- Both are projections onto MW.ρ.invariants.
  have hQ₁_proj : LinearMap.IsProj MW.ρ.invariants q₁ := by
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [Representation.mem_invariants]
      intro g
      apply Subtype.ext
      change σ g (p₁ (w : R)) = p₁ (w : R)
      exact ((σ.mem_invariants _).mp (h₁.map_mem (w : R))) g
    · apply Subtype.ext
      change p₁ (w : R) = (w : R)
      apply h₁.map_id
      rw [Representation.mem_invariants]
      intro g
      have hgw : MW.ρ g w = w := ((MW.ρ.mem_invariants w).mp hw) g
      have := congr_arg Subtype.val hgw
      change σ g (w : R) = (w : R) at this
      exact this
  have hQ₂_proj : LinearMap.IsProj MW.ρ.invariants q₂ := by
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [Representation.mem_invariants]
      intro g
      apply Subtype.ext
      change σ g (p₂ (w : R)) = p₂ (w : R)
      exact ((σ.mem_invariants _).mp (h₂.map_mem (w : R))) g
    · apply Subtype.ext
      change p₂ (w : R) = (w : R)
      apply h₂.map_id
      rw [Representation.mem_invariants]
      intro g
      have hgw : MW.ρ g w = w := ((MW.ρ.mem_invariants w).mp hw) g
      have := congr_arg Subtype.val hgw
      change σ g (w : R) = (w : R) at this
      exact this
  -- Apply the f.d. uniqueness theorem on MW.
  have hQ_eq : Q₁ = Q₂ :=
    IsLinearlyReductive.reynolds_unique (k := k) (G := G) hlr MW Q₁ Q₂ hQ₁_proj hQ₂_proj
  -- Read off equality at ⟨r, hr_W⟩.
  have h_at_r : q₁ ⟨r, hr_W⟩ = q₂ ⟨r, hr_W⟩ := by
    have := congr_arg (fun (P : MW ⟶ MW) => P.hom.hom ⟨r, hr_W⟩) hQ_eq
    exact this
  exact congr_arg Subtype.val h_at_r

/-- **Reynolds is `R^G`-linear on the right.**

For a linearly reductive group `G` acting on a `k`-algebra `R` by ring automorphisms
(`MulSemiringAction G R`) with locally finite action, there exists a Reynolds projection
`π` onto the invariants that is *also* `R^G`-linear: `π(a · r) = a · π(r)` whenever
`a ∈ R^G`. This is the key Reynolds property used in Hilbert's finiteness for GIT.

Proof: define the difference `δ : R →ₗ[k] R, δ r = π(a*r) - a*π(r)`. We show `δ + π`
is another Rep-projection onto invariants, hence equals `π` by
`reynolds_unique_locallyFinite`, so `δ = 0`. -/
theorem exists_reynolds_mul_compat_of_locallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [CommRing R] [Algebra k R]
    [MulSemiringAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom ∧
      ∀ {a : R}, a ∈ (Representation.ofDistribMulAction k G R).invariants →
        ∀ r : R, π.hom.hom (a * r) = a * π.hom.hom r := by
  obtain ⟨πR, hπR⟩ := exists_reynolds_of_locallyFinite (k := k) (G := G) hlr R hlf
  refine ⟨πR, hπR, ?_⟩
  intro a ha r
  -- Local notation: σ for the representation, π_lin for the underlying linear map.
  let σ : Representation k G R := Representation.ofDistribMulAction k G R
  let π_lin : R →ₗ[k] R := πR.hom.hom
  -- `a` is invariant: g • a = a for all g.
  have ha_g : ∀ g : G, g • a = a := fun g =>
    (Representation.mem_invariants σ a).mp ha g
  -- Multiplication by `a` is `G`-equivariant.
  have h_a_equiv : ∀ (g : G) (s : R), g • (a * s) = a * (g • s) := fun g s => by
    rw [smul_mul', ha_g g]
  -- π is `G`-equivariant.
  have hπ_equiv : ∀ (g : G) (s : R), π_lin (g • s) = g • (π_lin s) := fun g s => by
    have := Rep.hom_comm_apply πR g s
    exact this
  -- Build leftMul_a : R →ₗ[k] R.
  let leftMul_a : R →ₗ[k] R :=
    { toFun := fun s => a * s
      map_add' := fun x y => mul_add a x y
      map_smul' := fun c s => by
        simp only [RingHom.id_apply]
        exact mul_smul_comm c a s }
  -- φ₁ r = π(a * r), φ₂ r = a * π(r), δ := φ₁ - φ₂.
  let φ₁ : R →ₗ[k] R := π_lin.comp leftMul_a
  let φ₂ : R →ₗ[k] R := leftMul_a.comp π_lin
  let δ : R →ₗ[k] R := φ₁ - φ₂
  -- δ is G-equivariant.
  have hδ_equiv : ∀ (g : G) (s : R), δ (g • s) = g • (δ s) := by
    intro g s
    have hφ₁ : φ₁ (g • s) = g • (φ₁ s) := by
      change π_lin (a * (g • s)) = g • (π_lin (a * s))
      rw [← h_a_equiv g s, hπ_equiv]
    have hφ₂ : φ₂ (g • s) = g • (φ₂ s) := by
      change a * π_lin (g • s) = g • (a * π_lin s)
      rw [hπ_equiv, h_a_equiv]
    change φ₁ (g • s) - φ₂ (g • s) = g • (φ₁ s - φ₂ s)
    rw [hφ₁, hφ₂, smul_sub]
  -- δ lands in invariants.
  have hπ_mem : ∀ s, π_lin s ∈ σ.invariants := fun s => by
    change πR.hom.hom s ∈ (Representation.ofDistribMulAction k G R).invariants
    exact hπR.map_mem s
  have hδ_inv : ∀ s, δ s ∈ σ.invariants := by
    intro s
    have hφ₁_inv : φ₁ s ∈ σ.invariants := by
      change π_lin (a * s) ∈ σ.invariants
      exact hπ_mem (a * s)
    have hφ₂_inv : φ₂ s ∈ σ.invariants := by
      change a * π_lin s ∈ σ.invariants
      rw [Representation.mem_invariants]
      intro g
      change g • (a * π_lin s) = a * π_lin s
      have hπ_inv : g • (π_lin s) = π_lin s :=
        (Representation.mem_invariants σ (π_lin s)).mp (hπ_mem s) g
      rw [smul_mul', ha_g g, hπ_inv]
    change φ₁ s - φ₂ s ∈ σ.invariants
    exact Submodule.sub_mem _ hφ₁_inv hφ₂_inv
  -- δ vanishes on invariants.
  have hδ_van : ∀ s ∈ σ.invariants, δ s = 0 := by
    intro s hs
    have hs_g : ∀ g : G, g • s = s := fun g =>
      (Representation.mem_invariants σ s).mp hs g
    have h_as_inv : a * s ∈ σ.invariants := by
      rw [Representation.mem_invariants]
      intro g
      change g • (a * s) = a * s
      rw [smul_mul', ha_g g, hs_g g]
    have hφ₁_s : φ₁ s = a * s :=
      hπR.map_id (a * s) h_as_inv
    have hφ₂_s : φ₂ s = a * s := by
      change a * π_lin s = a * s
      rw [hπR.map_id s hs]
    change φ₁ s - φ₂ s = 0
    rw [hφ₁_s, hφ₂_s, sub_self]
  -- Build π_lin' := δ + π_lin.
  let π_lin' : R →ₗ[k] R := δ + π_lin
  have hπ'_id : ∀ s ∈ σ.invariants, π_lin' s = s := by
    intro s hs
    change δ s + π_lin s = s
    rw [hδ_van s hs, zero_add, hπR.map_id s hs]
  have hπ'_mem : ∀ s, π_lin' s ∈ σ.invariants := by
    intro s
    change δ s + π_lin s ∈ σ.invariants
    exact Submodule.add_mem _ (hδ_inv s) (hπ_mem s)
  have hπ'_equiv : ∀ (g : G) (s : R), π_lin' (g • s) = g • (π_lin' s) := by
    intro g s
    change δ (g • s) + π_lin (g • s) = g • (δ s + π_lin s)
    rw [hδ_equiv, hπ_equiv, smul_add]
  -- Wrap π_lin' as a Rep morphism.
  let π' : Rep.of σ ⟶ Rep.of σ :=
    { hom := ModuleCat.ofHom π_lin'
      comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun s => by
        change π_lin' ((Rep.of σ).ρ g s) = (Rep.of σ).ρ g (π_lin' s)
        exact hπ'_equiv g s }
  have hπ'_proj : LinearMap.IsProj σ.invariants π_lin' :=
    ⟨hπ'_mem, hπ'_id⟩
  -- Uniqueness in the locally-finite setting.
  have h_eq : π' = πR :=
    IsLinearlyReductive.reynolds_unique_locallyFinite
      (k := k) (G := G) hlr R hlf π' πR hπ'_proj hπR
  have h_lin_eq : π_lin' = π_lin := by
    have h := congrArg (fun (μ : Rep.of σ ⟶ Rep.of σ) => μ.hom.hom) h_eq
    exact h
  -- δ = 0.
  have hδ_zero : δ = 0 := by
    have h_add : δ + π_lin = π_lin := h_lin_eq
    have : δ = 0 := by
      have := add_right_cancel (a := δ) (b := π_lin) (c := 0)
      apply this
      rw [zero_add]; exact h_add
    exact this
  -- Conclude: π(a*r) = a*π(r).
  have hδ_r : δ r = 0 := by rw [hδ_zero]; rfl
  have h_sub : φ₁ r - φ₂ r = 0 := hδ_r
  change π_lin (a * r) = a * π_lin r
  exact sub_eq_zero.mp h_sub

end GeneralReynolds

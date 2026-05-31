import GIT.Reynolds.LocallyFiniteActions
import GIT.Reynolds.FiniteDimensionalReynolds

/-!
# Reynolds projection: locally finite case

For a linearly reductive `G` acting locally finitely on a `k`-module `R`, this file proves:

* `IsLinearlyReductive.exists_reynolds_of_isLocallyFinite` — existence of a `Rep`-morphism
  projection onto `Rᴳ` on `Rep.of (Representation.ofDistribMulAction k G R)`.
* `IsLinearlyReductive.reynolds_unique_of_isLocallyFinite` — uniqueness of such projections.

The existence argument bundles the local data into a private structure
`IsLinearlyReductive.LRD` (a witness `V r` around every point, together with a local Reynolds
projection on it), assembles the global function `D.f`, and proves linearity/projection/
equivariance properties via the central compat lemma `local_proj_agree_on_overlap`. The
uniqueness argument builds a common-witness submodule `W := V ⊔ p₁(V) ⊔ p₂(V)` closed under
both projections, restricts each projection to `W`, and applies finite-dimensional uniqueness.
-/

universe u

open Monoid MonoidAlgebra Representation

variable {k : Type u} [Field k] {G : Type u} [Group G]

/-- **The supremum of two `G`-stable submodules is `G`-stable.**

Math: if every `σ g` maps `W₁` (resp. `W₂`) into itself, then it maps `W₁ ⊔ W₂` into itself.

Proof: `sup_le` decomposes the goal `W₁ ⊔ W₂ ≤ (W₁ ⊔ W₂).comap (σ g)` into two pieces, each
followed by `Submodule.comap_mono le_sup_left` / `le_sup_right`. -/
lemma Representation.sup_le_comap_of_stable
    {V : Type*} [AddCommGroup V] [Module k V]
    {σ : Representation k G V} {W₁ W₂ : Submodule k V}
    (h₁ : ∀ g, W₁ ≤ W₁.comap (σ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (σ g)) :
    ∀ g, W₁ ⊔ W₂ ≤ (W₁ ⊔ W₂).comap (σ g) := fun g =>
  sup_le ((h₁ g).trans (Submodule.comap_mono le_sup_left))
         ((h₂ g).trans (Submodule.comap_mono le_sup_right))

/-- **Submodule inclusion as a representation morphism.** For `W₁ ≤ W₂` both `G`-stable under a
representation `ρ`, the canonical inclusion `↥W₁ → ↥W₂` lifts to a morphism between the
corresponding subrepresentations of `Rep.of ρ`.

Equivariance: both sides coerce to `ρ g v.val`. -/
noncomputable def Rep.subrepInclusion
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {W₁ W₂ : Submodule k V} (hle : W₁ ≤ W₂)
    (h₁ : ∀ g, W₁ ≤ W₁.comap (ρ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (ρ g)) :
    (Rep.of ρ).subrepresentation W₁ h₁ ⟶ (Rep.of ρ).subrepresentation W₂ h₂ :=
  Rep.mkHom (Submodule.inclusion hle) fun g v => by
    ext; simp [Representation.subrepresentation, Submodule.inclusion]

/-- **Wrap a local linear projection as a representation morphism.** Given a `G`-stable submodule
`W` under a representation `ρ` and a linear projection `π : ↥W → ↥W` onto the invariants of
`ρ.subrepresentation W _` that is constant on `G`-orbits, package it as a `Rep`-morphism on
`(Rep.of ρ).subrepresentation W _`.

Equivariance: `π` is orbit-constant by hypothesis and its image lies in the invariants, so each
`ρ g` fixes `π v`. -/
noncomputable def Rep.wrapLocalProj
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {W : Submodule k V} (hW : ∀ g, W ≤ W.comap (ρ g)) (π : ↥W →ₗ[k] ↥W)
    (hπ : LinearMap.IsProj (ρ.subrepresentation W hW).invariants π)
    (hπ_eq : ∀ (g : G) (v : ↥W), π ((ρ.subrepresentation W hW) g v) = π v) :
    (Rep.of ρ).subrepresentation W hW ⟶ (Rep.of ρ).subrepresentation W hW :=
  Rep.mkHom π fun g v => by
    rw [show ((Rep.of ρ).subrepresentation W hW).ρ g v = (ρ.subrepresentation W hW) g v from rfl,
      hπ_eq g v]
    exact ((((Rep.of ρ).subrepresentation W hW).ρ.mem_invariants _).mp (hπ.map_mem v) g).symm

variable {R : Type u} [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]

/-- **Local Reynolds projections agree on overlaps.** Let `W₁, W₂` be finite-dimensional
`G`-stable submodules of `R` carrying local Reynolds projections `π₁, π₂`. For `r ∈ W₁ ∩ W₂`,
the values `(π₁ ⟨r,·⟩ : R)` and `(π₂ ⟨r,·⟩ : R)` coincide.

Proof idea: form the common ambient `W := W₁ ⊔ W₂`, obtain a Reynolds projection `PW` on it via
`exists_reynolds`, and apply `reynolds_natural` to the inclusions `Wᵢ ↪ W` to get
`ιᵢ(πᵢ r) = PW(ιᵢ r)`. Since `ι₁ r = ι₂ r` inside `W`, the two right-hand sides agree, hence
so do the left-hand sides. -/
private lemma IsLinearlyReductive.local_proj_agree_on_overlap
    (hlr : IsLinearlyReductive k G)
    {W₁ W₂ : Submodule k R} [FiniteDimensional k ↥W₁] [FiniteDimensional k ↥W₂]
    (hW₁_st : ∀ g, W₁ ≤ W₁.comap (Representation.ofDistribMulAction k G R g))
    (hW₂_st : ∀ g, W₂ ≤ W₂.comap (Representation.ofDistribMulAction k G R g))
    {π₁ : ↥W₁ →ₗ[k] ↥W₁} {π₂ : ↥W₂ →ₗ[k] ↥W₂}
    (h₁ : LinearMap.IsProj
      ((Representation.ofDistribMulAction k G R).subrepresentation W₁ hW₁_st).invariants π₁)
    (h₁_eq : ∀ (g : G) (v : ↥W₁),
      π₁ (((Representation.ofDistribMulAction k G R).subrepresentation W₁ hW₁_st) g v) = π₁ v)
    (h₂ : LinearMap.IsProj
      ((Representation.ofDistribMulAction k G R).subrepresentation W₂ hW₂_st).invariants π₂)
    (h₂_eq : ∀ (g : G) (v : ↥W₂),
      π₂ (((Representation.ofDistribMulAction k G R).subrepresentation W₂ hW₂_st) g v) = π₂ v)
    {r : R} (hr₁ : r ∈ W₁) (hr₂ : r ∈ W₂) :
    W₁.subtype (π₁ ⟨r, hr₁⟩) = W₂.subtype (π₂ ⟨r, hr₂⟩) := by
  set σ := Representation.ofDistribMulAction k G R with hσ
  haveI : FiniteDimensional k ↥(W₁ ⊔ W₂) := Submodule.finiteDimensional_sup _ _
  set hSt := Representation.sup_le_comap_of_stable hW₁_st hW₂_st
  obtain ⟨PW, hπW⟩ := hlr.exists_reynolds ((Rep.of σ).subrepresentation (W₁ ⊔ W₂) hSt)
  have hn₁ := hlr.reynolds_natural _ _ (Rep.subrepInclusion σ le_sup_left hW₁_st hSt)
    (Rep.wrapLocalProj σ hW₁_st π₁ h₁ h₁_eq) PW h₁ hπW ⟨r, hr₁⟩
  have hn₂ := hlr.reynolds_natural _ _ (Rep.subrepInclusion σ le_sup_right hW₂_st hSt)
    (Rep.wrapLocalProj σ hW₂_st π₂ h₂ h₂_eq) PW h₂ hπW ⟨r, hr₂⟩
  simp only [Rep.subrepInclusion, Rep.wrapLocalProj, Rep.mkHom_hom] at hn₁ hn₂
  have hreq : (Submodule.inclusion (le_sup_left : W₁ ≤ W₁ ⊔ W₂) ⟨r, hr₁⟩ :
      ↥(W₁ ⊔ W₂)) = Submodule.inclusion le_sup_right ⟨r, hr₂⟩ := rfl
  exact congr_arg Subtype.val (hn₁.trans ((congr_arg PW.hom.hom hreq).trans hn₂.symm))

/-- (Private) **Bundle of local Reynolds data** on a locally finite action: a `G`-stable
finite-dimensional submodule `V r` around every point, together with a local Reynolds projection
`π r` on it that is orbit-constant. Produced by `LRD.of_isLocallyFinite`. -/
private structure IsLinearlyReductive.LRD
    (k : Type u) [Field k] (G : Type u) [Group G] (R : Type u)
    [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R] where
  V : R → Submodule k R
  fin : ∀ r, Module.Finite k ↥(V r)
  comap : ∀ r g, V r ≤ (V r).comap (Representation.ofDistribMulAction k G R g)
  mem : ∀ r, r ∈ V r
  π : ∀ r, ↥(V r) →ₗ[k] ↥(V r)
  isProj : ∀ r, LinearMap.IsProj
    ((Representation.ofDistribMulAction k G R).subrepresentation (V r) (comap r)).invariants (π r)
  apply_rho : ∀ r g v, π r
    (((Representation.ofDistribMulAction k G R).subrepresentation (V r) (comap r)) g v) = π r v

namespace IsLinearlyReductive.LRD

/-- **Local Reynolds data from local finiteness.** Pick the f.d. `G`-stable submodule `V r` from
`hlf`, then a local Reynolds projection on it via `exists_reynolds`. -/
private noncomputable def of_isLocallyFinite (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R) : IsLinearlyReductive.LRD k G R := by
  set σ := Representation.ofDistribMulAction k G R
  choose V hVf hVs hVm using hlf
  have hVc : ∀ r g, V r ≤ (V r).comap (σ g) := fun r g _ hv => hVs r g ⟨_, hv⟩
  haveI : ∀ r, FiniteDimensional k ↥(V r) := hVf
  have local_data : ∀ r, ∃ p : ↥(V r) →ₗ[k] ↥(V r),
      LinearMap.IsProj (σ.subrepresentation (V r) (hVc r)).invariants p ∧
      ∀ g v, p ((σ.subrepresentation (V r) (hVc r)) g v) = p v := fun r => by
    obtain ⟨P, hP⟩ := hlr.exists_reynolds ((Rep.of σ).subrepresentation (V r) (hVc r))
    exact ⟨P.hom.hom, hP, Rep.isProj_invariants_apply_rho hP⟩
  choose π hπp hπe using local_data
  exact ⟨V, hVf, hVc, hVm, π, hπp, hπe⟩

/-- **The global Reynolds function** `f : R → R`, defined by `r ↦ (π r) ⟨r, _⟩` interpreted in
`R` via the inclusion `V r ↪ R`. -/
private noncomputable def f (D : IsLinearlyReductive.LRD k G R) : R → R :=
  fun r => (D.V r).subtype (D.π r ⟨r, D.mem r⟩)

/-- **`D.f r` equals any other local projection at `r`.** Direct application of
`local_proj_agree_on_overlap`. -/
private lemma f_eq (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    {W : Submodule k R} [FiniteDimensional k ↥W]
    (hW_st : ∀ g, W ≤ W.comap (Representation.ofDistribMulAction k G R g))
    {πW : ↥W →ₗ[k] ↥W}
    (hπW : LinearMap.IsProj
      ((Representation.ofDistribMulAction k G R).subrepresentation W hW_st).invariants πW)
    (hπW_eq : ∀ (g : G) (v : ↥W),
      πW (((Representation.ofDistribMulAction k G R).subrepresentation W hW_st) g v) = πW v)
    (r : R) (hr : r ∈ W) : D.f r = W.subtype (πW ⟨r, hr⟩) := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  exact hlr.local_proj_agree_on_overlap (D.comap r) hW_st (D.isProj r) (D.apply_rho r)
    hπW hπW_eq (D.mem r) hr

/-- **Additivity of `f`.** Use the common ambient `W := V r ⊔ V s` with a Reynolds projection
`PW` produced by `exists_reynolds`; both sides equal `W.subtype (PW (⟨r,_⟩ + ⟨s,_⟩))`. -/
private lemma f_add (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    (r s : R) : D.f (r + s) = D.f r + D.f s := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  haveI : FiniteDimensional k ↥(D.V s) := D.fin s
  set σ := Representation.ofDistribMulAction k G R
  let W := D.V r ⊔ D.V s
  set hW_st := Representation.sup_le_comap_of_stable (D.comap r) (D.comap s)
  haveI : FiniteDimensional k ↥W := Submodule.finiteDimensional_sup _ _
  obtain ⟨PW, hπW⟩ := hlr.exists_reynolds ((Rep.of σ).subrepresentation W hW_st)
  have hπW_eq := Rep.isProj_invariants_apply_rho hπW
  have hr : r ∈ W := Submodule.mem_sup_left (D.mem r)
  have hs : s ∈ W := Submodule.mem_sup_right (D.mem s)
  rw [D.f_eq hlr hW_st hπW hπW_eq r hr, D.f_eq hlr hW_st hπW hπW_eq s hs,
    D.f_eq hlr hW_st hπW hπW_eq (r + s) (W.add_mem hr hs)]
  have : (⟨r + s, W.add_mem hr hs⟩ : ↥W) = ⟨r, hr⟩ + ⟨s, hs⟩ := rfl
  rw [this, map_add]; simp

/-- **Scalar-compatibility of `f`.** With `W = V r`, both sides equal
`(V r).subtype (π r (c • ⟨r,_⟩)) = c • (V r).subtype (π r ⟨r,_⟩)`. -/
private lemma f_smul (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    (c : k) (r : R) : D.f (c • r) = c • D.f r := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  rw [D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) (c • r)
        ((D.V r).smul_mem c (D.mem r)),
    D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) r (D.mem r)]
  have : (⟨c • r, (D.V r).smul_mem c (D.mem r)⟩ : ↥(D.V r)) = c • ⟨r, D.mem r⟩ := rfl
  rw [this, map_smul]; simp

/-- **`f r` lies in the invariants.** Direct from `D.isProj r |>.map_mem`. -/
private lemma f_mapMem (D : IsLinearlyReductive.LRD k G R) (r : R) :
    D.f r ∈ (Representation.ofDistribMulAction k G R).invariants := by
  have hmem := (D.isProj r).map_mem ⟨r, D.mem r⟩
  rw [Representation.mem_invariants] at hmem ⊢
  intro g
  have := congr_arg (D.V r).subtype (hmem g)
  simpa only [Submodule.subtype_apply] using this

/-- **`f` fixes invariants.** Direct from `D.isProj r |>.map_id`. -/
private lemma f_mapId (D : IsLinearlyReductive.LRD k G R) {r : R}
    (hr : r ∈ (Representation.ofDistribMulAction k G R).invariants) : D.f r = r := by
  have hmem : (⟨r, D.mem r⟩ : ↥(D.V r)) ∈
      ((Representation.ofDistribMulAction k G R).subrepresentation
        (D.V r) (D.comap r)).invariants := by
    rw [Representation.mem_invariants]; intro g; ext
    simp only [Representation.subrepresentation_apply, LinearMap.restrict_coe_apply]
    exact ((Representation.ofDistribMulAction k G R).mem_invariants r).mp hr g
  have := congr_arg (D.V r).subtype ((D.isProj r).map_id ⟨r, D.mem r⟩ hmem)
  simpa using this

/-- **`f` is orbit-constant.** Use `W := V r`; `g • r ∈ V r` by stability; both projections
agree at `r` and at `g • r` via `D.apply_rho`. -/
private lemma f_apply_rho (hlr : IsLinearlyReductive k G) (D : IsLinearlyReductive.LRD k G R)
    (g : G) (r : R) :
    D.f (Representation.ofDistribMulAction k G R g r) = D.f r := by
  haveI : FiniteDimensional k ↥(D.V r) := D.fin r
  set σ := Representation.ofDistribMulAction k G R
  have hgr : σ g r ∈ D.V r := D.comap r g (D.mem r)
  rw [D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) (σ g r) hgr,
    D.f_eq hlr (D.comap r) (D.isProj r) (D.apply_rho r) r (D.mem r)]
  congr 1
  have heq : (σ.subrepresentation (D.V r) (D.comap r)) g ⟨r, D.mem r⟩ = ⟨σ g r, hgr⟩ := rfl
  rw [← heq]
  exact D.apply_rho r g ⟨r, D.mem r⟩

end IsLinearlyReductive.LRD

/-- **Existence of the Reynolds projection, locally finite case.** A linearly reductive group `G`
acting locally finitely on a `k`-module `R` admits a `Rep`-morphism whose underlying linear map
projects onto the invariants.

Math statement: `∃ π : Rep.of σ ⟶ Rep.of σ, LinearMap.IsProj σ.invariants π.hom.hom`, where
`σ := Representation.ofDistribMulAction k G R`.

Proof idea: build `LRD.of_isLocallyFinite hlr hlf` — for each `r`, a f.d. `G`-stable submodule
`V r ∋ r` (from `hlf`) carrying a local Reynolds projection `π r` (from `exists_reynolds`). The
function `D.f r := (V r).subtype (π r ⟨r,·⟩)` is well-defined by `local_proj_agree_on_overlap`,
additive (`f_add`), scalar-linear (`f_smul`), projects to invariants (`f_mapMem`, `f_mapId`),
and orbit-constant (`f_apply_rho`); assemble these via `Rep.mkHom`. -/
theorem IsLinearlyReductive.exists_reynolds_of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom := by
  set σ := Representation.ofDistribMulAction k G R
  let D := IsLinearlyReductive.LRD.of_isLocallyFinite hlr hlf
  let π_lin : R →ₗ[k] R :=
    { toFun := D.f, map_add' := D.f_add hlr, map_smul' := D.f_smul hlr }
  have hproj : LinearMap.IsProj σ.invariants π_lin := ⟨D.f_mapMem, fun _ hr => D.f_mapId hr⟩
  refine ⟨Rep.mkHom π_lin fun g r => ?_, hproj⟩
  change D.f (σ g r) = σ g (D.f r)
  rw [D.f_apply_rho hlr g r]
  exact ((σ.mem_invariants _).mp (D.f_mapMem r) g).symm

/-- **Image of a submodule under a projection onto invariants lies in invariants.** -/
private lemma IsLinearlyReductive.map_le_invariants
    {p : R →ₗ[k] R}
    (hp : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p)
    (V : Submodule k R) :
    Submodule.map p V ≤ (Representation.ofDistribMulAction k G R).invariants := by
  rintro x ⟨v, _, rfl⟩; exact hp.map_mem v

/-- **A submodule sitting inside the invariants is `G`-stable.** -/
private lemma IsLinearlyReductive.le_invariants_comap
    {S : Submodule k R}
    (hS : S ≤ (Representation.ofDistribMulAction k G R).invariants) (g : G) :
    S ≤ S.comap (Representation.ofDistribMulAction k G R g) := fun x hx => by
  rw [Submodule.mem_comap,
    ((Representation.ofDistribMulAction k G R).mem_invariants x).mp (hS hx) g]
  exact hx

/-- **`Module.Finite` of `Submodule.map p V` from `Module.Finite k V`.**

Use the surjection `V → map p V`, `v ↦ p v.val`. -/
private lemma IsLinearlyReductive.finite_submodule_map (p : R →ₗ[k] R)
    {V : Submodule k R} [hV : Module.Finite k V] :
    Module.Finite k ↥(Submodule.map p V) := by
  let f : V →ₗ[k] ↥(Submodule.map p V) :=
    LinearMap.codRestrict (Submodule.map p V) (p ∘ₗ V.subtype)
      (fun v => Submodule.mem_map.mpr ⟨v.1, v.2, rfl⟩)
  refine Module.Finite.of_surjective f ?_
  rintro ⟨x, hx⟩
  obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hx
  exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩

/-- **Common witness submodule** `W := V ⊔ p₁(V) ⊔ p₂(V)`. Used in the locally-finite uniqueness
proof to host both restrictions of `p₁, p₂` simultaneously. -/
private noncomputable def IsLinearlyReductive.commonWitness
    (V : Submodule k R) (p₁ p₂ : R →ₗ[k] R) : Submodule k R :=
  V ⊔ Submodule.map p₁ V ⊔ Submodule.map p₂ V

/-- **`commonWitness` is `G`-stable.** Reduces by `sup_le` to stability of `V` and to the fact
that `Submodule.map pᵢ V ⊆ invariants` (which is `G`-stable). -/
private lemma IsLinearlyReductive.commonWitness_stable
    {V : Submodule k R}
    (hV_st : ∀ g, V ≤ V.comap (Representation.ofDistribMulAction k G R g))
    {p₁ p₂ : R →ₗ[k] R}
    (hp₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₁)
    (hp₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₂) (g : G) :
    IsLinearlyReductive.commonWitness V p₁ p₂ ≤
      (IsLinearlyReductive.commonWitness V p₁ p₂).comap
        (Representation.ofDistribMulAction k G R g) :=
  sup_le
    (sup_le ((hV_st g).trans (Submodule.comap_mono (le_sup_of_le_left le_sup_left)))
      ((IsLinearlyReductive.le_invariants_comap
        (IsLinearlyReductive.map_le_invariants hp₁ V) g).trans
          (Submodule.comap_mono (le_sup_of_le_left le_sup_right))))
    ((IsLinearlyReductive.le_invariants_comap
      (IsLinearlyReductive.map_le_invariants hp₂ V) g).trans
        (Submodule.comap_mono le_sup_right))

/-- **A projection onto invariants maps `commonWitness` into itself.** Decompose `w ∈ W` via
`mem_sup` twice, and recombine using `map_id` on the invariant pieces. -/
private lemma IsLinearlyReductive.commonWitness_maps_self
    (V : Submodule k R) {p₁ p₂ : R →ₗ[k] R}
    (hp₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₁)
    (hp₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p₂)
    {p : R →ₗ[k] R}
    (hp : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants p)
    (hpV : Submodule.map p V ≤ IsLinearlyReductive.commonWitness V p₁ p₂) :
    ∀ w ∈ IsLinearlyReductive.commonWitness V p₁ p₂,
      p w ∈ IsLinearlyReductive.commonWitness V p₁ p₂ := by
  intro w hw
  unfold IsLinearlyReductive.commonWitness at hw ⊢
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  rw [map_add, map_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ (hpV ⟨a₁, ha₁, rfl⟩) ?_) ?_
  · rw [hp.map_id a₂ (IsLinearlyReductive.map_le_invariants hp₁ V ha₂)]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right ha₂)
  · rw [hp.map_id c (IsLinearlyReductive.map_le_invariants hp₂ V hc)]
    exact Submodule.mem_sup_right hc

/-- **Restriction of a `Rep`-morphism on `Rep.of σ` to a `G`-stable subspace.** -/
private noncomputable def IsLinearlyReductive.restrictHom
    (W : Submodule k R)
    (hW_st : ∀ g, W ≤ W.comap (Representation.ofDistribMulAction k G R g))
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R))
    (hπW : ∀ w ∈ W, π.hom.hom w ∈ W) :
    (Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st ⟶
      (Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st :=
  Rep.mkHom (LinearMap.restrict π.hom.hom hπW) fun g w => by
    apply Subtype.ext; exact Rep.hom_comm_apply π g w

/-- **Restriction of a projection onto invariants is a projection onto the sub-invariants.** -/
private lemma IsLinearlyReductive.restrictHom_isProj
    {W : Submodule k R}
    (hW_st : ∀ g, W ≤ W.comap (Representation.ofDistribMulAction k G R g))
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    (hπW : ∀ w ∈ W, π.hom.hom w ∈ W) :
    LinearMap.IsProj
      ((Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st).ρ.invariants
      (LinearMap.restrict π.hom.hom hπW) := by
  set σ := Representation.ofDistribMulAction k G R
  set MW := (Rep.of σ).subrepresentation W hW_st
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [Representation.mem_invariants]; intro g; apply Subtype.ext
    simp only [LinearMap.restrict_coe_apply]
    exact ((σ.mem_invariants _).mp (hπ.map_mem _)) g
  · apply Subtype.ext
    simp only [LinearMap.restrict_coe_apply]
    apply hπ.map_id; rw [Representation.mem_invariants]; intro g
    exact congr_arg Subtype.val (((MW.ρ.mem_invariants w).mp hw) g)

/-- **Locally-finite uniqueness, pointwise.** For each `r : R`, the two projections agree at `r`.
This is the heart of `reynolds_unique_of_isLocallyFinite`; the latter just promotes pointwise
equality to morphism equality via `Action.hom_ext`/`ModuleCat.hom_ext`. -/
private lemma IsLinearlyReductive.reynolds_unique_at
    (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R)
    (π₁ π₂ : Rep.of (Representation.ofDistribMulAction k G R) ⟶
              Rep.of (Representation.ofDistribMulAction k G R))
    (h₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₂.hom.hom)
    (r : R) : π₁.hom.hom r = π₂.hom.hom r := by
  obtain ⟨V, hV_fin, hV_stable, hV_mem⟩ := hlf r
  have hV_c : ∀ g, V ≤ V.comap (Representation.ofDistribMulAction k G R g) :=
    fun g v hv => hV_stable g ⟨v, hv⟩
  haveI : FiniteDimensional k V := hV_fin
  haveI : Module.Finite k ↥(Submodule.map π₁.hom.hom V) := finite_submodule_map _
  haveI : Module.Finite k ↥(Submodule.map π₂.hom.hom V) := finite_submodule_map _
  haveI : FiniteDimensional k ↥(V ⊔ Submodule.map π₁.hom.hom V : Submodule k R) :=
    Submodule.finiteDimensional_sup _ _
  haveI : FiniteDimensional k ↥(commonWitness V π₁.hom.hom π₂.hom.hom) :=
    Submodule.finiteDimensional_sup _ _
  have hp₁W := commonWitness_maps_self V h₁ h₂ h₁ (le_sup_of_le_left le_sup_right)
  have hp₂W := commonWitness_maps_self V h₁ h₂ h₂ le_sup_right
  set W := commonWitness V π₁.hom.hom π₂.hom.hom
  set hW_st := commonWitness_stable hV_c h₁ h₂
  set MW : Rep k G := (Rep.of (Representation.ofDistribMulAction k G R)).subrepresentation W hW_st
  have hQ : restrictHom W hW_st π₁ hp₁W = restrictHom W hW_st π₂ hp₂W :=
    hlr.reynolds_unique MW _ _ (restrictHom_isProj _ h₁ hp₁W) (restrictHom_isProj _ h₂ hp₂W)
  have hrW : r ∈ W := Submodule.mem_sup_left (Submodule.mem_sup_left hV_mem)
  exact congr_arg Subtype.val
    (congr_arg (fun P : MW ⟶ MW => P.hom.hom ⟨r, hrW⟩) hQ)

/-- **Uniqueness of the Reynolds projection (locally finite case).** Any two `Rep`-morphism
projections onto `Rᴳ` are equal.

Math statement: `π₁ = π₂` whenever both are `Rep`-morphism projections onto
`(ofDistribMulAction k G R).invariants` and the action is locally finite.

Proof idea: by `Action.hom_ext`/`ModuleCat.hom_ext` it suffices to show pointwise equality, i.e.
`π₁.hom.hom r = π₂.hom.hom r` for every `r`, which is `reynolds_unique_at`. -/
theorem IsLinearlyReductive.reynolds_unique_of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R)
    (π₁ π₂ : Rep.of (Representation.ofDistribMulAction k G R) ⟶
              Rep.of (Representation.ofDistribMulAction k G R))
    (h₁ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₁.hom.hom)
    (h₂ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π₂.hom.hom) :
    π₁ = π₂ := by
  apply Action.hom_ext; apply ModuleCat.hom_ext; ext r
  exact hlr.reynolds_unique_at hlf π₁ π₂ h₁ h₂ r

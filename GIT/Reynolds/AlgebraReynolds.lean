import GIT.Reynolds.LocallyFiniteReynolds

/-!
# Reynolds projection on algebras (`Rᴳ`-linearity)

When a linearly reductive `G` acts on a commutative `k`-algebra `R` by ring automorphisms with
locally finite action, the Reynolds projection `π` is automatically `Rᴳ`-linear: for every
invariant `a ∈ Rᴳ` and every `r ∈ R`, `π(a · r) = a · π r`. This is the *Reynolds identity*
underlying Hilbert finiteness in GIT.

The proof goes through the *defect* `δ_a r := π(a r) − a · π r`. We show `δ_a` is
`G`-equivariant, lands in `Rᴳ`, and vanishes on `Rᴳ`; hence `δ_a + π` is again a `Rep`-morphism
projection onto `Rᴳ`. Locally-finite uniqueness forces `δ_a + π = π`, i.e. `δ_a = 0`.

## Main result

* `IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite`
-/

universe u

open Monoid MonoidAlgebra Representation

variable {k : Type u} [Field k] {G : Type u} [Group G]

/-- **Left multiplication by `a` as a `k`-linear map.** -/
noncomputable def Representation.leftMulHom {R : Type u} [CommRing R] [Algebra k R] (a : R) :
    R →ₗ[k] R where
  toFun := (a * ·)
  map_add' x y := mul_add a x y
  map_smul' c s := by simp only [RingHom.id_apply]; exact mul_smul_comm c a s

variable {R : Type u} [CommRing R] [Algebra k R] [MulSemiringAction G R] [SMulCommClass G k R]

/-- **The Reynolds defect** `δ r := π(a r) - a · π r`. Vanishes iff `π` is `Rᴳ`-linear at `a`. -/
private noncomputable def IsLinearlyReductive.reynoldsDefect
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)) (a : R) : R →ₗ[k] R :=
  π.hom.hom.comp (Representation.leftMulHom a) - (Representation.leftMulHom a).comp π.hom.hom

/-- **`reynoldsDefect` is `G`-equivariant.** Uses invariance of `a` and equivariance of `π`. -/
private lemma IsLinearlyReductive.reynoldsDefect_equiv
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R))
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) (g : G) (s : R) :
    IsLinearlyReductive.reynoldsDefect π a (g • s) =
      g • IsLinearlyReductive.reynoldsDefect π a s := by
  have ha_g : g • a = a := (Representation.mem_invariants _ a).mp ha g
  have hπ_eq : ∀ x : R, π.hom.hom (g • x) = g • π.hom.hom x := fun x => Rep.hom_comm_apply π g x
  change π.hom.hom (a * g • s) - a * π.hom.hom (g • s) =
    g • (π.hom.hom (a * s) - a * π.hom.hom s)
  rw [show a * g • s = g • (a * s) by rw [smul_mul', ha_g], hπ_eq, hπ_eq, smul_sub,
    show g • (a * π.hom.hom s) = a * (g • π.hom.hom s) by rw [smul_mul', ha_g]]

/-- **`reynoldsDefect` lands in invariants.** Both `π(a·s)` and `a · π(s)` are invariant
(the second uses that `a` and `π s` are both invariant), so their difference is. -/
private lemma IsLinearlyReductive.reynoldsDefect_mem_invariants
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) (s : R) :
    IsLinearlyReductive.reynoldsDefect π a s ∈
      (Representation.ofDistribMulAction k G R).invariants := by
  have ha_g : ∀ g, g • a = a := (Representation.mem_invariants _ a).mp ha
  have h_a_πs : a * π.hom.hom s ∈
      (Representation.ofDistribMulAction k G R).invariants := by
    rw [Representation.mem_invariants]; intro g
    have hπs : g • π.hom.hom s = π.hom.hom s :=
      (Representation.mem_invariants _ _).mp (hπ.map_mem s) g
    change g • (a * π.hom.hom s) = a * π.hom.hom s
    rw [smul_mul', ha_g, hπs]
  change π.hom.hom (a * s) - a * π.hom.hom s ∈
    (Representation.ofDistribMulAction k G R).invariants
  exact Submodule.sub_mem _ (hπ.map_mem _) h_a_πs

/-- **`reynoldsDefect` vanishes on invariants.** For `s ∈ Rᴳ`, both `π(a·s)` and `a · π s` equal
`a · s` (since `a · s` is invariant and `π` fixes invariants), so their difference is `0`. -/
private lemma IsLinearlyReductive.reynoldsDefect_vanishes_on_invariants
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants)
    {s : R} (hs : s ∈ (Representation.ofDistribMulAction k G R).invariants) :
    IsLinearlyReductive.reynoldsDefect π a s = 0 := by
  have ha_g : ∀ g, g • a = a := (Representation.mem_invariants _ a).mp ha
  have hs_g : ∀ g, g • s = s := (Representation.mem_invariants _ s).mp hs
  have h_as : a * s ∈ (Representation.ofDistribMulAction k G R).invariants := by
    rw [Representation.mem_invariants]; intro g
    change g • (a * s) = a * s; rw [smul_mul', ha_g, hs_g]
  change π.hom.hom (a * s) - a * π.hom.hom s = 0
  rw [hπ.map_id (a * s) h_as, hπ.map_id s hs, sub_self]

/-- **`reynoldsDefect + π` as a representation morphism.** Wrap the linear sum as a `Rep`-morphism
via `Rep.mkHom`; equivariance follows from `reynoldsDefect_equiv` and equivariance of `π`. -/
private noncomputable def IsLinearlyReductive.reynoldsAddDefect
    (π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R))
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) :
    Rep.of (Representation.ofDistribMulAction k G R) ⟶
      Rep.of (Representation.ofDistribMulAction k G R) :=
  Rep.mkHom (IsLinearlyReductive.reynoldsDefect π a + π.hom.hom) fun g s => by
    have hπ_eq : π.hom.hom (g • s) = g • π.hom.hom s := Rep.hom_comm_apply π g s
    change IsLinearlyReductive.reynoldsDefect π a (g • s) + π.hom.hom (g • s) =
      g • (IsLinearlyReductive.reynoldsDefect π a s + π.hom.hom s)
    rw [IsLinearlyReductive.reynoldsDefect_equiv π ha, hπ_eq, smul_add]

/-- **`reynoldsAddDefect` is a projection onto invariants.** Sum-component check:
`δ s ∈ invariants` and `π s ∈ invariants` give `(δ + π) s ∈ invariants`; for `s ∈ invariants`,
`δ s = 0` and `π s = s`, so `(δ + π) s = s`. -/
private lemma IsLinearlyReductive.reynoldsAddDefect_isProj
    {π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
         Rep.of (Representation.ofDistribMulAction k G R)}
    (hπ : LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom)
    {a : R} (ha : a ∈ (Representation.ofDistribMulAction k G R).invariants) :
    LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants
      (IsLinearlyReductive.reynoldsAddDefect π ha).hom.hom := by
  refine ⟨fun s => ?_, fun s hs => ?_⟩
  · simp only [reynoldsAddDefect, Rep.mkHom_hom, LinearMap.add_apply]
    exact Submodule.add_mem _ (reynoldsDefect_mem_invariants hπ ha s) (hπ.map_mem s)
  · simp only [reynoldsAddDefect, Rep.mkHom_hom, LinearMap.add_apply]
    rw [reynoldsDefect_vanishes_on_invariants hπ ha hs, zero_add, hπ.map_id s hs]

/-- **The Reynolds projection is `Rᴳ`-linear.** For a linearly reductive group `G` acting on a
`k`-algebra `R` by ring automorphisms with locally finite action, there is a Reynolds projection
`π` onto the invariants additionally satisfying `π (a * r) = a * π r` for every invariant
`a ∈ Rᴳ`. This is the Reynolds identity underlying Hilbert finiteness in GIT.

Math statement: same `π` as `exists_reynolds_of_isLocallyFinite` plus
`∀ {a} ∈ Rᴳ, ∀ r, π (a r) = a · π r`.

Proof idea: take `π` from `exists_reynolds_of_isLocallyFinite`. The defect
`δ r := π(a r) − a · π r` is `G`-equivariant (`reynoldsDefect_equiv`), lands in invariants
(`reynoldsDefect_mem_invariants`), and vanishes on invariants
(`reynoldsDefect_vanishes_on_invariants`). Hence `δ + π` is again a Rep-morphism projection onto
`Rᴳ` (`reynoldsAddDefect_isProj`); locally-finite uniqueness forces it to equal `π`, hence
`δ = 0`, which gives the desired identity at every `r`. -/
theorem IsLinearlyReductive.exists_reynolds_mulCompat_of_isLocallyFinite
    (hlr : IsLinearlyReductive k G)
    (R : Type u) [CommRing R] [Algebra k R] [MulSemiringAction G R] [SMulCommClass G k R]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
            Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π.hom.hom ∧
      ∀ {a : R}, a ∈ (Representation.ofDistribMulAction k G R).invariants →
        ∀ r : R, π.hom.hom (a * r) = a * π.hom.hom r := by
  obtain ⟨πR, hπR⟩ := hlr.exists_reynolds_of_isLocallyFinite R hlf
  refine ⟨πR, hπR, ?_⟩
  intro a ha r
  have h_eq := hlr.reynolds_unique_of_isLocallyFinite R hlf
    (IsLinearlyReductive.reynoldsAddDefect πR ha) πR
    (IsLinearlyReductive.reynoldsAddDefect_isProj hπR ha) hπR
  have h_lin : IsLinearlyReductive.reynoldsDefect πR a + πR.hom.hom = πR.hom.hom :=
    congrArg (fun μ : Rep.of _ ⟶ Rep.of _ => μ.hom.hom) h_eq
  have hδ_zero : IsLinearlyReductive.reynoldsDefect πR a = 0 :=
    add_right_cancel (b := πR.hom.hom) (by rw [zero_add]; exact h_lin)
  have hδ_r : IsLinearlyReductive.reynoldsDefect πR a r = 0 := by rw [hδ_zero]; rfl
  exact sub_eq_zero.mp hδ_r

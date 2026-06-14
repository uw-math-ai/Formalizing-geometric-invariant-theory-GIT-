import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection

variable (k : Type*) [Field k]
variable (G : Type*) [Group G]
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- Invariants submodule V^G -/
noncomputable def invariants : Submodule k V := ρ.invariants

/-- A submodule is G-stable if it is preserved by every `ρ g`. -/
def Representation.IsStable
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Submodule k V) : Prop :=
  ∀ g : G, ∀ v ∈ W, ρ g v ∈ W

/-- The invariants submodule is G-stable. -/
lemma Representation.invariants_isStable
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ρ.IsStable ρ.invariants := by
  intro g v hv h
  rw [hv g]
  exact hv h

/-
STEP 1: Use linear reductivity to obtain a decomposition
        V = W ⊕ W' for any G-stable W
-/
/-- Linearly reductive: every G-stable submodule of a finite-dimensional
representation has a G-stable complement. -/
class LinearlyReductive (k G : Type*) [Field k] [Group G] where
  split_stable :
    ∀ (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (ρ : Representation k G V) (W : Submodule k V),
      ρ.IsStable W →
      ∃ W' : Submodule k V, IsCompl W W' ∧ ρ.IsStable W'

/-- Extract a G-stable complement of a G-stable submodule W. -/
noncomputable def getComplement
    [LinearlyReductive k G] [FiniteDimensional k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ρ.IsStable W) :
    { W' : Submodule k V // IsCompl W W' ∧ ρ.IsStable W' } :=
  ⟨_, (LinearlyReductive.split_stable V ρ W hW).choose_spec⟩

/-
STEP 2: Define projection and inclusion:
        π : V → W  (projection along G-stable complement)
        ι : W → V   (inclusion map)
        R_W := ι ∘ π
-/
noncomputable def reynoldsOperator
    [LinearlyReductive k G] [FiniteDimensional k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ρ.IsStable W) : V →ₗ[k] V :=
by
  classical
  let C := getComplement k G V ρ W hW
  let π : V →ₗ[k] W := W.linearProjOfIsCompl C.1 C.2.1
  let ι : W →ₗ[k] V := W.subtype
  exact ι ∘ₗ π

/-
STEP 3: R_W(v) lies in W
-/
theorem reynoldsOperator_mem
    [LinearlyReductive k G] [FiniteDimensional k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ρ.IsStable W) (v : V) :
    reynoldsOperator k G V ρ W hW v ∈ W := by
  classical
  unfold reynoldsOperator
  simp only [LinearMap.comp_apply]
  exact Submodule.coe_mem _

/-
STEP 4: R_W is identity on W
-/
theorem reynoldsOperator_id_on
    [LinearlyReductive k G] [FiniteDimensional k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ρ.IsStable W)
    (v : V) (hv : v ∈ W) :
    reynoldsOperator k G V ρ W hW v = v := by
  classical
  unfold reynoldsOperator
  simp only [LinearMap.comp_apply]
  let C := getComplement k G V ρ W hW
  have hproj :
      W.linearProjOfIsCompl C.1 C.2.1 v = ⟨v, hv⟩ :=
    Submodule.linearProjOfIsCompl_apply_left C.2.1 ⟨v, hv⟩
  simpa using congrArg W.subtype hproj

/-!
FINAL RESULT:

We package the construction:
R_W = ι ∘ π satisfies:
  (a) lands in W
  (b) fixes W
-/
structure ReynoldsOperator [LinearlyReductive k G]
    (ρ : Representation k G V) (W : Submodule k V) where
  toLinearMap : V →ₗ[k] V
  mem : ∀ v, toLinearMap v ∈ W
  id_on : ∀ v, v ∈ W → toLinearMap v = v

noncomputable def reynoldsOperatorExists
    [LinearlyReductive k G] [FiniteDimensional k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ρ.IsStable W) :
    ReynoldsOperator k G V ρ W :=
by
  classical
  refine
  { toLinearMap := reynoldsOperator k G V ρ W hW
    mem := reynoldsOperator_mem k G V ρ W hW
    id_on := reynoldsOperator_id_on k G V ρ W hW }

/- Show uniqueness of Reynolds operators (relative to W) -/
theorem reynoldsOperator_unique
    [LinearlyReductive k G] (ρ : Representation k G V) (W : Submodule k V)
    (R1 R2 : ReynoldsOperator k G V ρ W)
    (h_ker : R1.toLinearMap.ker = R2.toLinearMap.ker) :
    R1.toLinearMap = R2.toLinearMap := by
  ext v
  /- Use the fact that V = ker(R) + im(R) because R is a projection onto W -/
  have h_proj (R : ReynoldsOperator k G V ρ W) (x : V) :
      R.toLinearMap (R.toLinearMap x) = R.toLinearMap x := by
    apply R.id_on
    apply R.mem
  /- Every v can be written as (v - Rv) + Rv, where (v - Rv) ∈ ker R -/
  let v_W := R1.toLinearMap v
  let v_ker := v - v_W
  have hv : v = v_ker + v_W := by rw [sub_add_cancel]
  have m_ker : v_ker ∈ R1.toLinearMap.ker := by
    rw [LinearMap.mem_ker, LinearMap.map_sub, h_proj R1 v, sub_self]
  /- Now evaluate R1 and R2 on the decomposition -/
  calc R1.toLinearMap v
    _ = R1.toLinearMap v_ker + R1.toLinearMap v_W := by rw [hv, LinearMap.map_add]
    _ = 0 + v_W := by
        rw [LinearMap.mem_ker.mp m_ker, R1.id_on v_W (R1.mem v)]
    _ = R2.toLinearMap v_ker + R2.toLinearMap v_W := by
        rw [h_ker] at m_ker
        rw [LinearMap.mem_ker.mp m_ker, R2.id_on v_W (R1.mem v), zero_add]
    _ = R2.toLinearMap (v_ker + v_W) := by rw [LinearMap.map_add]
    _ = R2.toLinearMap v := by rw [hv]

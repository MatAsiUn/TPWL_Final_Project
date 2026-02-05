import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic

set_option linter.style.commandStart false

open scoped ComplexInnerProductSpace

/-
  Uniqueness part of the Riesz Representation Theorem.

  Goal:
  Given two vectors v1 and v2 such that
    G x = inner x v1 and G x = inner x v2  for all x,
  prove that v1 = v2.
-/

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/--
Key lemma: if a vector is orthogonal to *every* vector, then it must be zero.
This is the core idea behind uniqueness.
-/
lemma inner_orth_zero (w : E) (h : ∀ x : E, ⟪w, x⟫ = 0) : w = 0 := by
  have hww: ⟪w, w⟫ = 0 := by
    simpa using h w
  exact inner_self_eq_zero.mp hww
  -- Proof idea (to be formalised):
  -- Take x = w. Then:
  --   inner w w = 0.
  -- But inner product is positive definite, so this implies w = 0.

/--
Uniqueness: if the same continuous linear functional G is represented by v1 and v2,
then v1 = v2.
-/
lemma riesz_uniqueness {G : StrongDual ℂ E} {v1 v2 : E}
(h1 : ∀ x : E, G x = ⟪v1, x⟫) (h2 : ∀ x : E, G x = ⟪v2, x⟫) :
v1 = v2 := by
  -- Strategy:
  -- For every x, G x = inner x v1 and also G x = inner x v2.
  -- Therefore for all x:
  --   inner x (v1 - v2) = 0.
  -- Apply inner_orth_zero to conclude v1 - v2 = 0, hence v1 = v2.

  -- Start the proof:
  have hzero : ∀ x : E, ⟪(v1 - v2), x⟫ = 0 := by
    intro x
    have hv: ⟪v1, x⟫ = ⟪v2, x⟫ := by
      calc
        ⟪v1, x⟫ = G x := (h1 x).symm
        _ = ⟪v2, x⟫ := h2 x
    have : ⟪v1, x⟫ - ⟪v2, x⟫ = 0 := sub_eq_zero.mpr hv
    simpa [inner_sub_left] using this
  have hw_zero : v1 - v2 = 0 := inner_orth_zero (w := v1 - v2) hzero
  exact sub_eq_zero.mp hw_zero



set_option linter.unusedSectionVars false

-- Below is some extra work beyond proving the existence and uniqueness of Riesz's Theorem
-- Specifically we are trying to omit the import `Mathlib.Topology.Algebra.Module.LinearMap`
-- This is achieved by writing our own lemma `isClosed_ker_of_strongDual`
-- which replaces `ContinuousLinearMap.isClosed_ker`

-- We now define a module E as before, but we include the assumption that the
-- space is complete
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
open scoped ComplexInnerProductSpace

-- This is a theorem that proves that if U is a Hilbert space, then U and U⟂
-- are complementary, that is
-- to say that U ∩ U⟂ = {0} and U + U⟂ = E. The proof of this theorem requires the
-- projection theorem
theorem UandUperpCompl (U: Submodule ℂ E)(hU: IsClosed (U : Set E)):
IsCompl U Uᗮ := by
constructor
· -- Goal 1: Want to show that U ∩ Uᗮ = 0
    rw [Submodule.disjoint_def]
    intro x hxU hxUperp
    exact inner_self_eq_zero.mp (hxUperp x hxU)

· -- Goal 2: Want to show that U + Uᗮ = E
    refine Submodule.codisjoint_iff_exists_add_eq.mpr ?_ --accessed via apply?
    intro z
    have h_Complete : IsComplete (U: Set E) := by
        exact IsClosed.isComplete hU
    -- We know there is a vector of minimal distance to z in U by Hilbert's
    -- projection theorem, the ⨅ symbol represents the infimum in Lean.
    have h_MinimDist : ∃ z_0 ∈ (U : Set E), ‖z - z_0‖ = ⨅(w : ↥U) , ‖z - w‖ := by
        apply Submodule.exists_norm_eq_iInf_of_complete_subspace U h_Complete z
    -- We will now use z_0 as our witness but we first have to unpack the properties
    -- we know about z_0
    obtain ⟨z_0, hz_0U, hz_0MinimDist⟩ := h_MinimDist
    use z_0, z-z_0
    simp only [add_sub_cancel, and_true]
    constructor
    · --Goal 1, want to show that z_0 ∈ U
        exact hz_0U
    · -- Goal 2, wnat to show that z - z_0 ∈ U⟂
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [inner_eq_zero_symm]
        revert u hu
        rw [←Submodule.norm_eq_iInf_iff_inner_eq_zero U hz_0U]
        exact hz_0MinimDist


-- This is a theorem that proves that if U is a closed subspace, then Uᗮᗮ = U
theorem PerpIsPerp (U: Submodule ℂ E)(hU: IsClosed (U : Set E)): Uᗮᗮ = U := by
apply le_antisymm
swap
· --First we start by proving that U ⊆ Uᗮᗮ.
    intro u hu
    rw [Submodule.mem_orthogonal]
    intro u1 hu1
    rw [inner_eq_zero_symm]
    exact hu1 u hu
· -- Then we show that Uᗮᗮ ⊆ U. This part again requires the projection theorem
-- We start by considering an arbitrary u ∈ U
    intro u hu
    -- We know that U and Uᗮ are complementary from the theorem we previously proved.
    have U_compl : IsCompl U Uᗮ := UandUperpCompl U hU
    -- Since U and Uᗮ are complementary we know that their direct sum (⊔) is the
    -- whole module (the top element)
    have h_sum_top : U ⊔ Uᗮ = ⊤ := U_compl.sup_eq_top
    have h_udecomp1 : u ∈ U ⊔ Uᗮ := by
        rw [h_sum_top]
        exact Submodule.mem_top
    -- Therefore we can write u = u_1 + u_2 with u_1 ∈ U and u_2 ∈ Uᗮ
    rcases Submodule.mem_sup.1 h_udecomp1 with ⟨u_1, hu_1, u_2, hu_2, h_sum⟩
    -- It is sufficient to prove that u = u_1, it is also sufficient to prove that
    -- u_2 = 0
    suffices h_suf : u = u_1 by
        rw [h_suf]
        exact hu_1
    suffices h_suf2 : u_2 = 0 by
        rw[←h_sum]
        simp only [add_eq_left]
        exact h_suf2
    -- We know that ⟪u, u_2⟫ = 0 (since u_2 ∈ Uᗮ and u ∈ Uᗮᗮ)
    have uu_2inner : ⟪u, u_2⟫ = 0 := by
        rw[Submodule.mem_orthogonal] at hu
        rw [inner_eq_zero_symm]
        exact hu u_2 hu_2
    rw [← h_sum] at uu_2inner
    rw[inner_add_left] at uu_2inner
    -- Because u_1 ∈ U and u_2 ∈ Uᗮ, their inner product is zero
    have h_u1_u2_orth :  ⟪u_1, u_2⟫ = 0 := by
        rw [Submodule.mem_orthogonal] at hu_2
        exact hu_2 u_1 hu_1
    rw[h_u1_u2_orth] at uu_2inner
    simp only [zero_add] at uu_2inner
    rw [inner_self_eq_zero] at uu_2inner
    exact uu_2inner

-- Replacement for `ContinuousLinearMap.isClosed_ker` in the special case `G : StrongDual ℂ E`.
-- We prove `ker(G)` is closed by rewriting it as the preimage of `{0}`
-- under the continuous map `G`.
lemma isClosed_ker_of_strongDual (G : StrongDual ℂ E) :
    IsClosed (LinearMap.ker (G : E →ₗ[ℂ] ℂ) : Set E) := by
  -- Rewrite ker as a preimage of {0} under the continuous map G
  have hker :
      (LinearMap.ker (G : E →ₗ[ℂ] ℂ) : Set E) =
        (fun x : E => G x) ⁻¹' ({0} : Set ℂ) := by
    ext x
    simp  -- uses: x ∈ ker ↔ G x = 0, and membership in preimage/singleton

  -- Preimage of a closed set under a continuous map is closed
  simpa [hker] using (isClosed_singleton.preimage G.continuous)


lemma mem_kernel_of_orthogonal_sub
  (G: StrongDual ℂ E)(z : E)
  (hz_unit : ‖z‖ = 1)
  (h_span : ∀ v ∈ (LinearMap.ker G)ᗮ, ∃ c : ℂ, v = c • z) -- Assumption: Kᗮ is 1D
  (x : E) :
  G (x - ⟪z, x⟫ • z) = 0 := by

  -- Setup: Basic norm property for unit vector z
  have h_norm : ⟪z, z⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz_unit]; simp

  let K := LinearMap.ker G

  have hK_closed : IsClosed (K : Set E) := by
    -- Using lemma `isClosed_ker_of_strongDual` instead of imported module
    simpa [K] using (isClosed_ker_of_strongDual (E := E) G)

  have h_double_perp : K = Kᗮᗮ := by
    exact (PerpIsPerp K hK_closed).symm

  -- Step 1: Reformulate goal from "G u = 0" to "u ∈ K"
  change x - ⟪z, x⟫ • z ∈ K

  -- Step 2: Switch to checking orthogonality (u ∈ Kᗮᗮ)
  rw [h_double_perp, Submodule.mem_orthogonal]
  intro v hv_mem_perp

  -- Step 3: Use the span property (v is a scalar multiple of z)
  obtain ⟨c, rfl⟩ := h_span v hv_mem_perp

  -- Step 4: Algebraic verification of orthogonality
  rw [inner_smul_left]
  suffices ⟪z, x - ⟪z, x⟫ • z⟫ = 0 by
    rw [this]; simp

  -- Calculation: ⟪z, x⟩ - ⟪z, x⟩ * ⟪z, z⟩ = 0
  rw [inner_sub_right, inner_smul_right, h_norm]
  simp only [mul_one, sub_self]

import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
--Needed for statement of theorem
--Quotient_Iso_Perp
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal --Needed for
--The projection theorem
import Mathlib.Topology.Algebra.Module.LinearMap --Needed for ContinuousLinearMap.isClosed_ker
set_option linter.style.longLine false
set_option linter.style.commandStart false

set_option linter.style.commandStart false

--Defining a Vector space V
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


-- This theorem in plain english, given a 1 dimensional vector space, there
-- exists a vector u in the Vector space such that every v in the vector space
-- can be expressed as ku for some scalar k
theorem Unidim_Vect_Space(h : Module.finrank K V = 1): ∃ u : V, ∀ v: V ,
    ∃ k : K, v = k • u := by

-- This is all a proof that if the Module has finrank of 1 (dimension 1)
-- Then the module is finite dimensional
have h2 : Module.Finite K V := by
 apply Module.finite_of_finrank_pos
 rw[h]
 exact zero_lt_one


-- This line generates a basis (b) which is indexed by Fin 1
-- Fin 1 is {0} the set containing 0
let b := Module.finBasisOfFinrankEq K V h
use b 0
intro v
use b.repr v 0
rw [← b.sum_repr v]
simp

-- This theorem states that
-- For any vector space V and non-zero functional f, the
-- dimension of the quotient space V / ker(f) is 1.
theorem Functional_Coker_Dim (f: V →ₗ[K] K)(hf : f ≠ 0):
    Module.finrank K (V ⧸ LinearMap.ker f) = 1 := by
    have Iso := f.quotKerEquivRange -- by the first iso thm
    rw[LinearEquiv.finrank_eq Iso]
    -- showing that the dimension of the range of f is less than the dimension of K
    -- by virtue of being a submodule
    have h_le : Module.finrank K (LinearMap.range f) ≤ Module.finrank K K :=
    by exact Submodule.finrank_le (LinearMap.range f)
    rw[Module.finrank_self K] at h_le
    apply le_antisymm h_le
    rw [Nat.succ_le_iff]
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine Submodule.nonzero_mem_of_bot_lt ?_ --This idea was given thanks to apply?
    -- The upside down T is just the "bottom" subspace, in other words the zero subspace
    rw [bot_lt_iff_ne_bot]
    rw[ne_eq]
    rw [LinearMap.range_eq_bot]
    exact hf



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open scoped ComplexInnerProductSpace
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G = 0):
 G x = ⟪x,0⟫ := by
 -- We use a lemma found in IPS.Basic, that tells us the inner
 -- product of anything with 0 on the right is 0
 simp [inner_zero_right]
 rw[h]
 simp

variable [CompleteSpace E]


-- This is a theorem that proves that U and U⟂ are complementary, that is
-- to say that U ∩ U⟂ = {0} and U + U⟂ = E. It is in the proof of this theorem
-- That we need the projection theorem
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
    -- projection theorem, the ⨅ symbol represents the infimum.
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
theorem Perp_PerpIsPerp (U: Submodule ℂ E)(hU: IsClosed (U : Set E)): Uᗮᗮ = U := by
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




-- This is a theorem that proves that if V is a complete inner product space
-- and U is a closed submodule of V, then V/U is isomorphic to U⟂.
-- Since we are trying to construct an isomorphism and this isomorphism
-- implicitly relies on the axiom of choice we want to use noncomputable def
noncomputable def Quotient_Iso_Perp(U: Submodule ℂ E)(hU: IsClosed (U : Set E)):
    (E ⧸ U) ≃ₗ[ℂ] Uᗮ := by
    --We have that U is its own closure since U is closed
    have h_closure : U.topologicalClosure = U :=
    by exact IsClosed.submodule_topologicalClosure_eq hU
    --Since U is a topological closure it is complete
    have h_complete : CompleteSpace U :=
    by rw [← h_closure]; exact Submodule.topologicalClosure.completeSpace U
    -- Since U is complete it has an orthogonal projection
    have h_orth : U.HasOrthogonalProjection :=
    by exact Submodule.HasOrthogonalProjection.ofCompleteSpace U
    -- We have that U and U⟂ are complementary in E (U ⊕ U⟂ = E, U ∩ U⟂ = {0})
    have h_compl : IsCompl U Uᗮ :=
    by exact UandUperpCompl U hU
    -- And then we have a  lemma that tells us that if q is a complement of
    -- p (q ⊕ p = E, q ∩ p = {0} ) then E/p is isomorphic to q
    exact Submodule.quotientEquivOfIsCompl U Uᗮ h_compl


theorem Riesz_Representation_Theorem_Existence(G: StrongDual ℂ E):
 ∃ v : E, ∀ x : E, G x = ⟪x,v⟫ := by
 by_cases hG : G = 0
 {
    use 0
    intro x
    exact Riesz_Representation_Theorem_TrivialG G hG
 }
 {
    -- By definition we get that LinearMap.ker G is a submodule
    have KerGClosed: IsClosed (LinearMap.ker G : Set E) := sorry
    have hG_lin : (G : E →ₗ[ℂ] ℂ) ≠ 0 := by norm_cast --this step is necessary
    -- since our proof hCoker_Rank required the hypothesis that G was a linear map
    -- but we had that G was a continuous linear map (as all members of strong dual are)
    -- We can now use our lemma from before to show that the dimension of the cokernel
    -- must be 1
    have hCoker_Rank : Module.finrank ℂ (E ⧸ LinearMap.ker G) = 1 :=
    by exact Functional_Coker_Dim G.toLinearMap hG_lin
    have Iso : (E ⧸ LinearMap.ker G) ≃ₗ[ℂ] (LinearMap.ker G)ᗮ :=
    by exact Quotient_Iso_Perp (LinearMap.ker G) KerGClosed
    have hPerp_Rank : Module.finrank ℂ (LinearMap.ker G)ᗮ = 1 :=
    by rw[LinearEquiv.finrank_eq Iso.symm]; exact hCoker_Rank

    --We now have that E/ker(G) has dimension 1. It is left to prove that E/ker(G) is
    --Isomorphic to ker(G)⟂
    -- It is proven in Quotient_Iso_Perp, it just needs to be applied to this section
    -- We also need a proof that ker(G) is closed.

    sorry
 }

open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- A lemma which states that we can extract a unit vector from a unidimensional module
lemma exists_unit_vector_of_finrank_one {U : Submodule ℂ E} (h_dim : Module.finrank ℂ U = 1) :
  ∃ z ∈ U, ‖z‖ = 1 := by
have h2 : Module.Finite ℂ U := by
    apply Module.finite_of_finrank_pos
    rw[h_dim]
    exact zero_lt_one
let b := Module.finBasisOfFinrankEq ℂ U h_dim
let v := b 0
have hv : v ≠ 0 := b.ne_zero 0
let z1 := (‖v‖ : ℂ)⁻¹ • v
use z1
constructor
· simp only [SetLike.coe_mem] -- accessed via simp?
simp only [z1]
simp only [AddSubgroupClass.coe_norm, SetLike.val_smul]
rw[norm_smul]
rw[norm_inv]
simp only [Complex.norm_real, norm_norm]
refine inv_mul_cancel₀ ?_ --accessed via apply?
rw [norm_ne_zero_iff]
simp only [ne_eq, ZeroMemClass.coe_eq_zero]
exact hv

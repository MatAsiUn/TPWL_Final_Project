import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
-- ^^ used for Submodule.length_lt
-- All libraries below are for the proofs beyond my section
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection --Needed for statement of theorem
--Quotient_Iso_Perp

--

--Useful Theorems:
--Module.finBasisOfFinrankEq (generates a basis from a module of finite rank)
--Module.finite_of_finrank_eq_succ (Tells us that modules of natural number
--rank are finite dimensional)

set_option linter.style.commandStart false

--Defining a Vector space V
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


--The dimension of a vector space is given using the function Module.finrank
--An extremely useful theorem is hidden at Module.finBasisOfFinrankEq
--There is also an arguably more useful theorem below it


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

-- The second theorem I have to formalise
-- I will actually try to prove the more general statement
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
    rw [LinearMap.range_eq_bot] --an amazing lemma
    exact hf



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
-- This is me working on the project after finishing what I had set out to do

open scoped ComplexInnerProductSpace
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G = 0):
 G x = ⟪x,0⟫ := by
 -- We use a lemma found in IPS.Basic, that tells us the inner
 -- product of anything with 0 on the right is 0
 simp [inner_zero_right]
 rw[h]
 simp

variable [CompleteSpace E]

--for some reason we had to use noncomputable def instead of theorem
noncomputable def Quotient_Iso_Perp(U: Submodule ℂ E)(hU: IsClosed (U : Set E)):
    (E ⧸ U) ≃ₗ[ℂ] Uᗮ := by
    have h_complete : CompleteSpace U := by sorry
    have h_orth : U.HasOrthogonalProjection :=
    by exact Submodule.HasOrthogonalProjection.ofCompleteSpace U
    have h_compl : IsCompl U Uᗮ :=
    by exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
    exact Submodule.quotientEquivOfIsCompl U Uᗮ h_compl


    -- have hcompl : IsCompl U Uᗮ := Submodule.isCompl_orthogonal_of_hasOrthogonalProjection


theorem Riesz_Representation_Theorem_Existence(G: StrongDual ℂ E):
 ∃ v : E, ∀ x : E, G x = ⟪x,v⟫ := by
 by_cases hG : G = 0
 {
    use 0
    intro x
    exact Riesz_Representation_Theorem_TrivialG G hG
 }
 {
    have hG_lin : (G : E →ₗ[ℂ] ℂ) ≠ 0 := by norm_cast --this step is necessary
    -- since our proof hCoker_Rank required the hypothesis that G was a linear map
    -- but we had that G was a continuous linear map (as all members of strong dual are)
    -- We can now use our lemma from before to show that the dimension of the cokernel
    -- must be 1
    have hCoker_Rank : Module.finrank ℂ (E ⧸ LinearMap.ker G) = 1 :=
    by exact Functional_Coker_Dim G.toLinearMap hG_lin
    --We now have that E/ker(G) has dimension 1. It is left to prove that E/ker(G) is
    --Isomorphic to ker(G)⟂
    -- It is proven in Quotient_Iso_Perp, it just needs to be applied to this section
    -- We also need a proof that ker(G) is closed.
    sorry
 }

 theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪x,v⟫ := by
 sorry
 --We first start with the trivial case (where G is the zero element in the dual)

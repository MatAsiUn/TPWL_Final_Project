import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
--import Mathlib.LinearAlgebra.Span.Basic
--import Mathlib.LinearAlgebra.FiniteDimensional.Defs
--import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
--import Mathlib.Analysis.Normed.Module.Basic
--import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.commandStart false

-- We define what it means for a functional to be linear
def linear_function_prop (K V : Type _) [Field K] [AddCommGroup V] [Module K V] (F: V → K) :=
  ∀ (x y : V) (a b : K), F (a • x + b • y) = a * (F x) + b * (F y)
-- Note that "V" is our vector space here

open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- The statment of Riesz Representation Theorem for a trivial G (G identically 0)
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G x = 0):
 G x = ⟪x,0⟫ := by
 -- We use a lemma found in InnerProductSpace.Basic, that tells us the inner
 -- product of anything with 0 is 0
 simp [inner_zero_right]

-- We can use exact as G x = 0, is what is left to prove but this was one of
-- assumptions
 exact h

lemma KerGClosed (G: StrongDual ℂ E): IsClosed (LinearMap.ker G : Set E) := by
 exact ContinuousLinearMap.isClosed_ker G

-- Introduce Hilber Space variable (and add strong dual to make life easier)
variable[CompleteSpace E]

theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪v,x⟫ := by
 sorry

 -- Proving a nice corollary of Riesz Rep that every non-trivial, bounded,
 -- linear operator attains it's norm
lemma elements_of_dual_space_attain_norm (G : StrongDual ℂ E)(hG : G ≠ 0):
  ∃ x : E, ‖x‖ = 1 ∧ ‖G x‖ = ‖G‖ := by
  -- We first obtain v from Riesz
  obtain ⟨v, hv, _⟩ := Riesz_Representation_Theorem G

  --Prove the case for trivial G
  have hv_ne : v ≠ 0 := by
   intro h
   apply hG
   ext z
   simp [hv, h]
  let x := (‖v‖)⁻¹ • v -- Define our candidate x

  -- First justify the norm of x is 1
  have hx_norm: ‖x‖ = 1 := by
   rw [norm_smul, norm_inv, norm_norm]
   apply inv_mul_cancel₀
   exact norm_ne_zero_iff.mpr hv_ne

  -- We now show that the absolute value of G(x) is the operator norm of G
  have hx_attains : ‖G x‖ = ‖G‖ := by
  -- We split into cases to show each side of the equality equals the norm of v
   have h_val: ‖G x‖ = ‖v‖ := by
     rw [hv, inner_smul_right_eq_smul]
     rw [norm_smul, norm_inv, norm_norm]
     rw [inner_self_eq_norm_sq_to_K]
     simp only [Complex.coe_algebraMap, norm_pow, Complex.norm_real, norm_norm]
     field_simp

  -- Showing both inequality in both directions will give us the equality we need
   have h_op : ‖G‖ = ‖v‖ := by
     refine le_antisymm ?_ ?_
     · -- Proving ‖G‖ ≤ ‖v‖
       rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg v)]
       intro y
       rw[hv y]
       exact norm_inner_le_norm v y
     · -- Proving ‖G‖ ≥ ‖v‖
       rw [← h_val]
       exact ContinuousLinearMap.unit_le_opNorm G x hx_norm.le
   rw [h_val, h_op]
  exact ⟨x, hx_norm, hx_attains⟩

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


  --- Corollary 2: Proving all Hilbert Spaces are Reflexive

  --- We first define the canoncical embedding map:

---def canonical_embedding := --- how should we define do we think?

---theorem Hilbert_is_Reflexive (Φ : StrongDual ℂ (StrongDual ℂ E)) :
  ---∃ v : E, Φ = canonical_embedding v := by
 --- sorry

 set_option linter.unusedSectionVars false

 --- I prove some interesting results in inner product spaces:
 --- In a section proving useful theorems on inner product spaces,
 --- we would be remiss to not prove argubly one of the most
 --- famous theorems in mathematics. I recreate the proof we
 --- used in MA3G7 Functional Analysis 1
theorem Pythagoras_Theorem{x y: E}(h: ⟪x, y⟫ = 0):
   ‖x + y‖^2 = ‖x‖^2 + ‖y‖^2 := by
   --- First expand the inner product
  have h_exp : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * (RCLike.re ⟪x, y⟫) + ‖y‖ ^ 2 := by
   exact norm_add_sq x y
   --- The real part of the inner product is also 0
  have h_zer : RCLike.re (⟪x, y⟫) = 0 := by
    rw [h]
    simp
  --- Combine the two
  rw [h_exp]
  rw [h_zer]
  simp

  --- We now prove the Cauchy-Schwartz inequality, another very important
  --- theorem for inner product spaces
  --- I am aware that the existing "norm_inner_le_norm" exists in
  --- Mathlib.Analysis.InnerProductSpace.Basic, my aim is to formalise
  --- the proof we did in MA3G7, which will complete our collection of all
  --- the named theorems from Chapter 4 of that module.
 theorem Cauchy_Scwartz{x y : E}:
   ‖⟪x, y⟫‖ ≤ ‖x‖*‖y‖ := by
  by_cases hy : y = 0
  --- Case y = 0
  rw [hy]
  rw [inner_zero_right]
  simp

  --- Case y ≠ 0
  let α := ⟪x, y⟫ / ‖y‖^2
  have h_nonneg: ‖x - α • y‖^2 ≥ 0 := by
   exact sq_nonneg ‖x - α • y‖
  have h_exp : (‖x - α • y‖^2 : ℂ) = ‖x‖^2 - (star α) * ⟪y, x⟫ - α * ⟪x, y⟫ + ‖α‖^2 * ‖y‖^2 := by

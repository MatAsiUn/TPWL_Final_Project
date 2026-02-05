import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.List.TFAE
import Mathlib.Analysis.Complex.Basic

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
 --- famous theorems in mathematics. I recreate the proofs from
 --- MA3G7 Functional Analysis 1
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

lemma Polarization_Identity_Complex(x y : E) :
    (4 : ℂ) * ⟪x, y⟫
      =
      (↑‖x + y‖ ^ 2 - ↑‖x - y‖ ^ 2
        + (↑‖x - Complex.I • y‖ ^ 2 - ↑‖x + Complex.I • y‖ ^ 2) * Complex.I) := by
  rw[inner_eq_sum_norm_sq_div_four x y]
  simp only [Complex.coe_algebraMap, RCLike.I_to_complex]
  ring_nf

lemma Ptolemy_Inequality{x y z: E}(hx: x ≠ 0)(hy: y ≠ 0)(hz: z ≠ 0) :
   ‖x - y‖*‖z‖ ≤ ‖x - z‖*‖y‖ + ‖z - y‖*‖x‖  := by
   --- Now define the vectors used to apply to triangle inequality
   let x' := (‖x‖ ^ 2)⁻¹ • x
   let y' := (‖y‖ ^ 2)⁻¹ • y
   let z' := (‖z‖ ^2)⁻¹ • z
   --- Note the use of two powers to deal with typing in lean, a⁻¹ computes
   --- the inverse of a so is type dependant, \^-2 does not exist and the ^ ()
   --- function expects type ℕ.
   have identity : ∀ (u v : E), u ≠ 0 → v ≠ 0 →
    let u' := (‖u‖ ^ 2)⁻¹ • u
    let v' := (‖v‖ ^ 2)⁻¹ • v
    ‖u' - v'‖ = ‖u - v‖ / (‖u‖ * ‖v‖) := by
    intros u v hu hv u' v'
    have h_sq : ‖u' - v'‖^2 = (‖u - v‖ / (‖u‖ * ‖v‖))^2 := by
     rw[div_pow, mul_pow]
     have h_exp : ‖u' - v'‖^2 = ‖u'‖^2 - 2 * (RCLike.re ⟪u', v'⟫) + ‖v'‖^2 := by
      exact norm_sub_pow_two u' v'
     rw[h_exp]
     dsimp[u', v']
     rw[norm_smul, norm_smul, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
     simp only [norm_inv, norm_pow, norm_norm]
     have h_u_term : ((‖u‖ ^ 2)⁻¹ * ‖u‖)^2 = (‖u‖^2)⁻¹ := by
      field_simp [norm_ne_zero_iff.mpr hu]
     have h_v_term : ((‖v‖^2)⁻¹ * ‖v‖)^2 = (‖v‖^2)⁻¹ := by
      field_simp [norm_ne_zero_iff.mpr hv]
     rw[h_u_term, h_v_term]
     rw[RCLike.real_smul_eq_coe_mul]
     rw[RCLike.real_smul_eq_coe_mul]
     have h_exp_2 : ‖u - v‖^2 = ‖u‖^2 - 2 * (RCLike.re ⟪u, v⟫) + ‖v‖^2 := by
      exact norm_sub_pow_two u v
     rw[h_exp_2]
     field_simp
     ring_nf
     sorry

    refine (sq_eq_sq₀ (norm_nonneg _) ?_).mp h_sq
    positivity
    --have h_sq : ‖u' - v'‖ ^ 2 = ‖u - v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
   have hxy := identity x y hx hy
   have hzx := identity x z hx hz
   have hyz := identity z y hz hy

   have tri_ineq: ‖x' - y'‖ ≤ ‖x' - z'‖ + ‖z' - y'‖ := by
    exact norm_sub_le_norm_sub_add_norm_sub x' z' y'

   rw[hxy, hyz, hzx] at tri_ineq

   have h_pos : 0 < ‖x‖*‖y‖*‖z‖  := by
    positivity

   rw[← mul_le_mul_iff_left₀ h_pos] at tri_ineq
   field_simp at tri_ineq
   linarith[tri_ineq]




  /-
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
  sorry

  --- Case y ≠ 0
  let α := ⟪x, y⟫ / ‖y‖^2
  have h_nonneg: ‖x - α • y‖^2 ≥ 0 := by
   exact sq_nonneg ‖x - α • y‖
  have h_exp : (‖x - α • y‖^2) = ‖x‖^2 - (star α) • ⟪y, x⟫ - α • ⟪x, y⟫ + ‖α‖^2 • ‖y‖^2 := by
    sorry
  have h_final : (0 : ℝ) ≤ ‖x‖^2 - ‖⟪x, y⟫‖^2 / ‖y‖^2 := by
    -- We use 'norm_cast' to move from Complex h_exp back to Reals
    norm_cast at h_exp
    sorry
  replace h_final : ‖⟪x, y⟫‖^2 ≤ ‖x‖^2 * ‖y‖^2 := by
    ---linarith [mul_le_mul_of_nonneg_right h_final (sq_nonneg ‖y‖)]
   sorry
  sorry



--- Interesting lemma from FA1
lemma orthogonality_equivalence (x y : E) :
  List.TFAE [
  ⟪x, y⟫ = 0,
  ∀ α : ℂ, ‖x + α • y‖ =  ‖x - α • y‖,
  ∀ α : ℂ, ‖x‖ ≤ ‖x + α • y‖
  ] := by
  tfae_have 1 → 2 := by
    intro h α
    have hplus: ‖x + α • y‖^2 = ‖x‖^2 + ‖α‖^2 * ‖y^2‖ := by
      rw[norm_add_sq, nor     m_sub_sq]

    --have hplus: ‖x + α • y‖^2 = ‖x‖^2 + ‖α‖^2 • ‖y‖^2 := by
      --sorry
    --have hminus: ‖x - α • y‖^2 = ‖x‖^2 + ‖α‖^2 • ‖y‖^2 := by
     -- sorry


  sorry
-/

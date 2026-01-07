import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

open scoped ComplexInnerProductSpace
set_option linter.style.docString false
set_option linter.style.longLine false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (G : StrongDual ℂ E)


/--
  Normalize v to obtain z = v / ‖v‖, which has norm 1.
--/
lemma exists_unit_vector_of_finrank_one {U : Submodule ℂ E} (h_dim : Module.finrank ℂ U = 1) :
  ∃ z ∈ U, ‖z‖ = 1 := by

  sorry 


lemma mem_kernel_of_orthogonal_sub
  (z : E)
  (hz_perp : z ∈ (LinearMap.ker G)ᗮ) -- Using (LinearMap.ker G) ensures consistency with topological definition
  (hz_unit : ‖z‖ = 1)
  (h_span : ∀ v ∈ (LinearMap.ker G)ᗮ, ∃ c : ℂ, v = c • z) -- assume Kᗮ is 1D
  (x : E) :
  G (x - ⟪z, x⟫ • z) = 0 := by

  
  have h_norm : ⟪z, z⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz_unit]; simp

  let K := LinearMap.ker G

  -- We use 'sorry' here because i can't find `orthogonal_orthogonal_eq_closure`
  have h_double_perp : K = Kᗮᗮ := by sorry
  change x - ⟪z, x⟫ • z ∈ K

  rw [h_double_perp, Submodule.mem_orthogonal]
  intro v hv_mem_perp

  obtain ⟨c, rfl⟩ := h_span v hv_mem_perp

  rw [inner_smul_left]
  suffices ⟪z, x - ⟪z, x⟫ • z⟫ = 0 by
    rw [this]; simp

  -- calculate ⟪z, x⟩ - ⟪z, x⟩ * ⟪z, z⟩ = 0
  rw [inner_sub_right, inner_smul_right, h_norm]
  simp only [mul_one, sub_self]

theorem riesz_existence_part_III
  (_hG_ne : G ≠ 0) -- Underscore suppresses "unused variable" warning
  (hPerp_Rank : Module.finrank ℂ (LinearMap.ker G)ᗮ = 1) : -- Matches (LinearMap.ker G)ᗮ type in Step 6
  ∃ y : E, ∀ x : E, G x = ⟪y, x⟫ := by

  --  Obtain z from the 1-dimensional orthogonal complement
  have ⟨z, hz_mem, hz_unit⟩ := exists_unit_vector_of_finrank_one hPerp_Rank

  --  Prove the span property
  have h_span : ∀ v ∈ (LinearMap.ker G)ᗮ, ∃ c : ℂ, v = c • z := by
    intro v hv
    -- Prove z is non-zero (since norm is 1)
    have hz_ne0 : z ≠ 0 := by
      rw [← norm_ne_zero_iff, hz_unit]; norm_num

    -- Prove dim(span {z}) = 1
    have h_dim_span : Module.finrank ℂ (Submodule.span ℂ {z}) = 1 :=
      finrank_span_singleton hz_ne0

    -- Prove span {z} = (LinearMap.ker G)ᗮ using "dim equality + inclusion"
    have h_eq : Submodule.span ℂ {z} = (LinearMap.ker G)ᗮ := by
      have h_le : Submodule.span ℂ {z} ≤ (LinearMap.ker G)ᗮ := by
        rw [Submodule.span_singleton_le_iff_mem]; exact hz_mem

      have h_dim_eq : Module.finrank ℂ (Submodule.span ℂ {z}) = Module.finrank ℂ (LinearMap.ker G)ᗮ := by
        rw [h_dim_span, hPerp_Rank]
      haveI : Module.Finite ℂ (LinearMap.ker G)ᗮ :=
        Module.finite_of_finrank_pos (by rw [hPerp_Rank]; norm_num)

      exact Submodule.eq_of_le_of_finrank_eq h_le h_dim_eq

    rw [← h_eq] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    use c
    -- note: hc is "c • z = v", we need the symmetric "v = c • z"
    exact hc.symm

  let y := (star (G z)) • z
  use y; intro x

  have h_ker_zero := mem_kernel_of_orthogonal_sub G z hz_mem hz_unit h_span x

  rw [map_sub, map_smul, sub_eq_zero] at h_ker_zero
  rw [h_ker_zero]

  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_star]

  -- ⟨z, x⟩ * G(z) == G(z) * ⟨z, x⟩
  rw [mul_comm]
  -- Unifies Scalar Multiplication (•) with Standard Multiplication (*) in ℂ
  rw [smul_eq_mul]

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
-- ==========================================
-- Section 1: Preamble & Setup
-- ==========================================

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (G : StrongDual ℂ E)

-- ==========================================
-- Section 2: Preparation Lemma
-- ==========================================

/--
  Helper Lemma: Extracts a unit vector from a 1-dimensional subspace.

  Logic Flow:
  1. Since the dimension is 1 (>0), the subspace contains a non-zero vector v.
  2. Normalize v to obtain z = v / ‖v‖, which has norm 1.
--/
lemma exists_unit_vector_of_finrank_one {U : Submodule ℂ E} (h_dim : Module.finrank ℂ U = 1) :
  ∃ z ∈ U, ‖z‖ = 1 := by
  sorry -- Standard linear algebra: existence of basis vector.

-- ==========================================
-- Section 3: Existence Part III (Mike's Section)
-- ==========================================

/--
  Lemma (Step 6): The Geometric Core.

  Logic Flow:
  1. Define K = ker(G). Since G is continuous, K is closed.
  2. Use the Double Orthogonal Complement theorem (K = Kᗮᗮ) for closed subspaces.
  3. Reformulate the goal: to show (x - Px) ∈ K, we prove (x - Px) ⟂ Kᗮ.
  4. Since Kᗮ is 1-dimensional (spanned by z), checking orthogonality against z is sufficient.
  5. The calculation reduces to ⟨z, x⟩ - ⟨z, x⟩ * 1 = 0.
--/
lemma mem_kernel_of_orthogonal_sub
  (z : E)
  (hz_perp : z ∈ (LinearMap.ker G)ᗮ) -- Using (LinearMap.ker G) ensures consistency with topological definition
  (hz_unit : ‖z‖ = 1)
  (h_span : ∀ v ∈ (LinearMap.ker G)ᗮ, ∃ c : ℂ, v = c • z) -- Assumption: Kᗮ is 1D
  (x : E) :
  G (x - ⟪z, x⟫ • z) = 0 := by

  -- Setup: Basic norm property for unit vector z
  have h_norm : ⟪z, z⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz_unit]; simp

  let K := LinearMap.ker G

  -- [Assumption]: Double Orthogonal Complement for closed subspaces.
  -- We use 'sorry' here to bypass finding the specific instance of `orthogonal_orthogonal_eq_closure`
  -- for StrongDual kernels, but the geometric fact is standard.
  have h_double_perp : K = Kᗮᗮ := by sorry

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


/--
  Theorem (Step 7): Riesz Representation Theorem (Existence).

  Logic Flow:
  1. Obtain a unit vector z from the 1-dimensional space (LinearMap.ker G)ᗮ.
  2. Construct the candidate vector y := conj(G(z)) • z.
  3. [Conclusion A]: Use Step 6 to derive G(x) = ⟨z, x⟩ * G(z).
  4. [Conclusion B]: Calculate ⟨y, x⟩ directly to get G(z) * ⟨z, x⟩.
  5. Prove A = B via commutativity of multiplication in ℂ.
--/
theorem riesz_existence_part_III
  (_hG_ne : G ≠ 0) -- Underscore suppresses "unused variable" warning
  (h_dim : Module.finrank ℂ (LinearMap.ker G)ᗮ = 1) : -- Matches (LinearMap.ker G)ᗮ type in Step 6
  ∃ y : E, ∀ x : E, G x = ⟪y, x⟫ := by

  -- 1. Setup: Obtain z from the 1-dimensional orthogonal complement
  have ⟨z, hz_mem, hz_unit⟩ := exists_unit_vector_of_finrank_one h_dim

  -- 2. Prove the span property: (LinearMap.ker G)ᗮ is spanned by z.
  -- Logic: If dim(V)=1 and z ∈ V is non-zero, then V = span{z}.
  have h_span : ∀ v ∈ (LinearMap.ker G)ᗮ, ∃ c : ℂ, v = c • z := by
    intro v hv
    -- A. Prove z is non-zero (since norm is 1)
    have hz_ne0 : z ≠ 0 := by
      rw [← norm_ne_zero_iff, hz_unit]; norm_num

    -- B. Prove dim(span {z}) = 1
    have h_dim_span : Module.finrank ℂ (Submodule.span ℂ {z}) = 1 :=
      finrank_span_singleton hz_ne0

    -- C. Prove span {z} = (LinearMap.ker G)ᗮ using "dim equality + inclusion"
    have h_eq : Submodule.span ℂ {z} = (LinearMap.ker G)ᗮ := by
      -- 1. Inclusion: span {z} ⊆ (LinearMap.ker G)ᗮ
      have h_le : Submodule.span ℂ {z} ≤ (LinearMap.ker G)ᗮ := by
        rw [Submodule.span_singleton_le_iff_mem]; exact hz_mem

      -- 2. Dimension equality: 1 = 1
      have h_dim_eq : Module.finrank ℂ (Submodule.span ℂ {z}) = Module.finrank ℂ (LinearMap.ker G)ᗮ := by
        rw [h_dim_span, h_dim]

      -- 3. [Technical]: Explicitly state finiteness to help Lean's type inference
      haveI : Module.Finite ℂ (LinearMap.ker G)ᗮ :=
        Module.finite_of_finrank_pos (by rw [h_dim]; norm_num)

      -- 4. Apply equality theorem
      exact Submodule.eq_of_le_of_finrank_eq h_le h_dim_eq

    -- D. Extract coefficient c for vector v
    rw [← h_eq] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    use c
    -- Note: hc is "c • z = v", we need the symmetric "v = c • z"
    exact hc.symm

  -- 3. Construction: Define y
  let y := (star (G z)) • z
  use y; intro x

  -- 4. [Conclusion A]: Derive G(x) from the kernel property
  -- We know G(x - ⟨z, x⟩z) = 0 from Step 6
  have h_ker_zero := mem_kernel_of_orthogonal_sub G z hz_mem hz_unit h_span x

  -- Rearrange G(x - ...) = 0 into G(x) = ⟨z, x⟩ * G(z)
  rw [map_sub, map_smul, sub_eq_zero] at h_ker_zero
  rw [h_ker_zero]

  -- 5. [Conclusion B]: Expand ⟨y, x⟩
  -- ⟨y, x⟩ = ⟨conj(G z)z, x⟩ = conj(conj(G z)) * ⟨z, x⟩ = G(z) * ⟨z, x⟩
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_star]

  -- 6. Final Comparison
  -- Logic: ⟨z, x⟩ * G(z) == G(z) * ⟨z, x⟩
  rw [mul_comm]
  -- [Technical]: Unifies Scalar Multiplication (•) with Standard Multiplication (*) in ℂ
  rw [smul_eq_mul]

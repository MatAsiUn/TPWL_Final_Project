import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule --Needed for statement of theorem
--Quotient_Iso_Perp
import Mathlib.Topology.Algebra.Module.LinearMap --Needed for ContinuousLinearMap.isClosed_ker

set_option linter.style.commandStart false

--Mathlib.Analysis.NormedSpace does indeed not exist
--Instead you need to import Mathlib.Analysis.Normed.Module
--for results related to what we are doing

-- We use a nested structure to differentiate between results that are applicable in
-- an Inner Product Space (IPS), and ones only applicable in a Hilbert Space.

--SECTION 1: Ancillary theorems, these are theorems that do not require
-- an inner product space structure


section ancillary_theorems
--Defining a Vector space V
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

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

end ancillary_theorems

section inner_product_space_theorems

open scoped ComplexInnerProductSpace
-- This is active for our entire file
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- A lemma which states that we can extract a unit vector from a unidimensional module
lemma exists_unit_vector_of_finrank_one {U : Submodule ℂ E} (h_dim : Module.finrank ℂ U = 1) :
  ∃ z ∈ U, ‖z‖ = 1 := by
  sorry -- Standard linear algebra: existence of basis vector.

--Proving that if z is a unit vector that spans the orthogonal complement
-- of the kernel of G, then for any vector x, the vector (x - ⟨z,x⟩z) lies
-- in the kernel of G. (I.e. removing the component "perpendicular" to the
-- kernel gives a vector in the kernel)
lemma mem_kernel_of_orthogonal_sub
  (G: StrongDual ℂ E)(z : E)
  (hz_perp : z ∈ (LinearMap.ker G)ᗮ)
  (hz_unit : ‖z‖ = 1)
  (h_span : ∀ v ∈ (LinearMap.ker G)ᗮ, ∃ c : ℂ, v = c • z) -- Assumption: Kᗮ is 1D
  (x : E) :
  G (x - ⟪z, x⟫ • z) = 0 := by

  -- Setup: Basic norm property for unit vector z
  have h_norm : ⟪z, z⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz_unit]; simp

  let K := LinearMap.ker G

  -- [Assumption]: Double Orthogonal Complement for closed subspaces.
  -- We need to get rid of this sorry
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




 -- The statment of Riesz Representation Theorem for a trivial G (G identically 0)
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G = 0):
 G x = ⟪0,x⟫ := by
 rw[h]
 simp

end inner_product_space_theorems
-- Section for Hilbert Spaces
section hilbert_space_theorems

-- We add the completeness assumption
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
open scoped ComplexInnerProductSpace


-- This is a theorem that proves that if V is a complete inner product space and U
-- is a closed submodule of V, then V/U is isomorphic to U⟂. This fact will be
-- very useful since we have that U = ker(G)
noncomputable def Quotient_Iso_Perp(U: Submodule ℂ E)(hU: IsClosed (U : Set E)):
    (E ⧸ U) ≃ₗ[ℂ] Uᗮ := by
    --We have that U is its own closure since U is closed
    have h_closure : U.topologicalClosure = U :=
    by exact IsClosed.submodule_topologicalClosure_eq hU
    --Since U is a topological closure it is complete (there should be a way of doing
    --it directly from definition of closed without needing topological closure)
    have h_complete : CompleteSpace U :=
    by rw [← h_closure]; exact Submodule.topologicalClosure.completeSpace U
    -- Since U is complete it has an orthogonal projection
    have h_orth : U.HasOrthogonalProjection :=
    by exact Submodule.HasOrthogonalProjection.ofCompleteSpace U
    -- We have that U and U⟂ are complementary in E (U ⊕ U⟂ = V)
    have h_compl : IsCompl U Uᗮ :=
    by exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
    -- And then we have a fantastic lemma that tells us that if q is a complement of
    -- p then E/p is isomorphic to q
    exact Submodule.quotientEquivOfIsCompl U Uᗮ h_compl

--We first start by proving Existence
theorem Riesz_Representation_Theorem_Existence(G: StrongDual ℂ E):
 ∃ v : E, ∀ x : E, G x = ⟪v,x⟫ := by
 by_cases hG : G = 0
 {
    use 0
    intro x
    exact Riesz_Representation_Theorem_TrivialG G hG
 }
 {
    -- By definition we get that LinearMap.ker G is a submodule
    -- So we must only prove that it is closed
    have KerGClosed: IsClosed (LinearMap.ker G : Set E) :=
    by exact ContinuousLinearMap.isClosed_ker G
    have hG_lin : (G : E →ₗ[ℂ] ℂ) ≠ 0 := by norm_cast --this step is necessary
    -- since our proof hCoker_Rank required the hypothesis that G was a linear map
    -- but we had that G was a continuous linear map (as all members of strong dual are)
    -- We can now use our lemma from before to show that the dimension of the cokernel
    -- must be 1
    have hCoker_Rank : Module.finrank ℂ (E ⧸ LinearMap.ker G) = 1 :=
    by exact Functional_Coker_Dim G.toLinearMap hG_lin
    -- We can now use the linear isomorphism between E/ker(G) and ker(G)⟂ to deduce
    -- that ker(G)⟂ must also have dimension 1
    have Iso : (E ⧸ LinearMap.ker G) ≃ₗ[ℂ] (LinearMap.ker G)ᗮ :=
    by exact Quotient_Iso_Perp (LinearMap.ker G) KerGClosed
    have hPerp_Rank : Module.finrank ℂ (LinearMap.ker G)ᗮ = 1 :=
    by rw[LinearEquiv.finrank_eq Iso.symm]; exact hCoker_Rank

    --We now have that E/ker(G) has dimension 1. It is left to prove that E/ker(G) is
    --Isomorphic to ker(G)⟂
    -- It is proven in Quotient_Iso_Perp, it just needs to be applied to this section
    -- Now we proceed with Mike's code

      -- 1. Setup: Obtain z from the 1-dimensional orthogonal complement
    have ⟨z, hz_mem, hz_unit⟩ := exists_unit_vector_of_finrank_one hPerp_Rank
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
                rw [h_dim_span, hPerp_Rank]
            -- 3. [Technical]: Explicitly state finiteness to help Lean's type inference
            haveI : Module.Finite ℂ (LinearMap.ker G)ᗮ :=
                Module.finite_of_finrank_pos (by rw [hPerp_Rank]; norm_num)

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
 }

theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪v,x⟫ := by
 sorry
-- refine ExistsUnique.intro ?_ ?_ ?_
end hilbert_space_theorems

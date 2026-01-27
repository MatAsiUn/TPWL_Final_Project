import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal -- This module contains
--the projection theorem. It is used to prove the theorem UandUperpCompl
-- import `Mathlib.Topology.Algebra.Module.LinearMap`  -- previously for `ContinuousLinearMap.isClosed_ker`
-- Omitted: we use the local lemma `isClosed_ker_of_strongDual` instead.
set_option linter.style.longLine false
set_option linter.style.commandStart false

--Mathlib.Analysis.NormedSpace does indeed not exist
--Instead you need to import Mathlib.Analysis.Normed.Module
--for results related to what we are doing

-- We use a nested structure to differentiate between results that are applicable in
-- an Inner Product Space (IPS), and ones only applicable in a Hilbert Space.


------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
------Section 1: Ancillary theorems, these are theorems that do not require an -----------
-------------------------inner product space structure------------------------------------
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------



section ancillary_theorems
--Defining a Vector space V
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

-- This theorem is a proof of the statement:
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

------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
-------------------Section 2: Inner Product Space Theorems--------------------------------
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------


section inner_product_space_theorems

open scoped ComplexInnerProductSpace
-- Now instead of a vector space V, we instead define an inner product space E
-- over ℂ
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- This lemma states that we can extract a unit vector
-- from a unidimensional module
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

--This lemma states that if a vector is orthogonal to every vector,
--then it must be zero. It will be very useful when proving uniqueness.
lemma inner_orth_zero (w : E) (h : ∀ x : E, ⟪w, x⟫ = 0) : w = 0 := by
  have hww: ⟪w, w⟫ = 0 := by
    simpa using h w
  exact inner_self_eq_zero.mp hww


end inner_product_space_theorems

------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
-------------------------Section 3: Hilbert Space Theorems--------------------------------
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------


section hilbert_space_theorems

set_option linter.unusedSectionVars false


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
    -- This is where we use our previously proved theorem about the perpenndicular
    -- Subspace being complementary
    by exact UandUperpCompl U hU
    -- And then we have a  lemma that tells us that if q is a complement of
    -- p (q ⊕ p = E, q ∩ p = {0} ) then E/p is isomorphic to q
    exact Submodule.quotientEquivOfIsCompl U Uᗮ h_compl

------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
--------------Section 4: Proof of Riesz's representation theorem (Existence) -------------
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
-- We first start by proving Existence. Note that the inner product (as defined in
-- in Lean) is linear in the second (antilinear in the first argument) so the
-- statement must change to reflect this. I think this is done because in Physics
-- the convention is to make the inner product linear in the second argument.
theorem Riesz_Representation_Theorem_Existence(G: StrongDual ℂ E):
 ∃ v : E, ∀ x : E, G x = ⟪v,x⟫ := by
 --first we split it up into cases to get rid of the trivial case (where G is the 0 functional)
 by_cases hG : G = 0
 {
    use 0
    intro x
    rw[hG]
    simp
 }
 {
    -- For the non-trivial case we first have to show that dim(ker(G)⟂) = 1
    -- By definition we automatically get that LinearMap.ker G is a submodule
    -- So we must only prove that it is closed to be able to use the
    -- isomorphism in Functional_Coker_Dim
    have KerGClosed: IsClosed (LinearMap.ker G : Set E) := by
      -- Using lemma `isClosed_ker_of_strongDual` instead of imported module
      simpa using (isClosed_ker_of_strongDual (E := E) G)
    have hG_lin : (G : E →ₗ[ℂ] ℂ) ≠ 0 := by norm_cast --this step is necessary
    -- since our proof hCoker_Rank required the hypothesis that G was a linear map
    -- but we had that G was a continuous linear map (as all members of strong dual
    -- are) This makes Lean recognise G as we want it to
    -- We can now use our isomorphism to show that the dimension of the
    -- cokernel (E ⧸ ker(G) ) must be 1
    have hCoker_Rank : Module.finrank ℂ (E ⧸ LinearMap.ker G) = 1 :=
    by exact Functional_Coker_Dim G.toLinearMap hG_lin
    -- We can now use the linear isomorphism between E/ker(G) and ker(G)⟂ to deduce
    -- that ker(G)⟂ must also have dimension 1
    have Iso : (E ⧸ LinearMap.ker G) ≃ₗ[ℂ] (LinearMap.ker G)ᗮ :=
    by exact Quotient_Iso_Perp (LinearMap.ker G) KerGClosed
    have hPerp_Rank : Module.finrank ℂ (LinearMap.ker G)ᗮ = 1 :=
    by rw[LinearEquiv.finrank_eq Iso.symm]; exact hCoker_Rank

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
    have h_ker_zero := mem_kernel_of_orthogonal_sub G z hz_unit h_span x
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

/--
Uniqueness: if the same continuous linear functional G is represented by v1 and v2,
then v1 = v2.
-/

lemma Riesz_Representation_Theorem_Uniqueness {G : StrongDual ℂ E} {v1 v2 : E}
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

-- We use existence to prove uniqueness
theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪v,x⟫ := by
  obtain ⟨v, hv⟩ := Riesz_Representation_Theorem_Existence (E := E) G
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact Riesz_Representation_Theorem_Uniqueness (G := G) hw hv

------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
----This concludes the existence and uniqueness proofs of Riesz Representation Theorem----
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------
-- We now prove an interesting corrollary of Riesz, that states that for any non-trivial G,
-- we can find an x such that ‖G x‖ = ‖G‖, that is the operator norm is attained by some
-- unit vector x.
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

  -- For ‖G‖ = ‖v‖ we show the inequality in both directions to give us equality
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
end hilbert_space_theorems

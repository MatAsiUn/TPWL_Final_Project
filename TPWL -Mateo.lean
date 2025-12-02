import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- ^^ used for Submodule.length_lt


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

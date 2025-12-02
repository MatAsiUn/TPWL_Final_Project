import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

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

-- this states we will use the first (and only) element in our basis b
-- as our "u"
use b 0
-- This next line is effectively saying "take an arbitrary v"
intro v
-- This next line is saying that we take our "k" to be the
-- coefficient of vector v (at index 0) as the scalar k that
-- we are looking for.
use b.repr v 0
-- This next line replaces v with its expansion in the basis, so on
-- the right of the equation we have its expansion in the basis
-- and on the left of the equation we also have its expansion in the
--basis, therefore the only thing we have to do is simplify
rw [← b.sum_repr v]
simp

-- The second theorem I have to formalise
-- I will actually try to prove the more general statement
-- For any vector space V and non-zero functional f, the
-- dimension of the quotient space V / ker(f) is 1.
theorem Functional_Coker_Dim (f: V →ₗ[K] K)(hf : f ≠ 0):
    Module.finrank K (V ⧸ LinearMap.ker f) = 1 := by
    sorry

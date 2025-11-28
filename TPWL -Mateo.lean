import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

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
theorem Unidim_Vect_Space(h : Module.finrank K V = 1): ∃ u : V, ∀ v: V ,
    ∃ k : K, v = k • u := by

-- This is all a proof that if the Module has finrank of 1 (dimension 1)
-- Then the module is finite dimensional
have h2 : Module.Finite K V := by
 apply Module.finite_of_finrank_pos
 rw[h]
 exact zero_lt_one


-- This line generates a basis (b) which is indexed by Fin 1
-- We needed to do the last part since we required
-- Fin 1 is {0} the set containing 0
let b := Module.finBasisOfFinrankEq K V h
use b 0
intro v


-- theorem Unidim_Vect_Space(h2 : Module.Finite K V)(h : Module.finrank K V = 1): ∃ u : V, ∀ v: V ,
--     ∃ k : K, v = k • u := by
-- -- The first line generates a basis (b) which is indexed by Fin 1
-- -- Fin 1 is {0} the set containing 0
-- let b := Module.finBasisOfFinrankEq K V h



-- We then need to show that all vectors in U
-- ⊥ are of the form cu where c ∈ K, u ∈ U
-- ⊥ This follows from the fact that U
-- ⊥
-- is 1-dimensional.


-- We then need to show that U
-- ⊥ has dimension 1. This part will be quite difficult

import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Complex.Basic


set_option linter.style.commandStart false

--Mathlib.Analysis.NormedSpace does indeed not exist
--Instead you need to import Mathlib.Analysis.Normed.Module
--for results related to what we are doing

-- We use a nested structure to differentiate between results that are applicable in
-- an Inner Product Space (IPS), and ones only applicable in a Hilbert Space
section inner_product_space_theorems

open scoped ComplexInnerProductSpace
-- This is active for our entire file
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 -- The statment of Riesz Representation Theorem for a trivial G (G identically 0)
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G x = 0):
 G x = ⟪x,0⟫ := by
 -- We use a lemma found in IPS.Basic, that tells us the inner
 -- product of anything with 0 is 0
 simp only [inner_zero_right]

-- We can use exact as G x = 0, is what is left to prove but this was one of
-- assumptions
 exact h

-- Section for Hilbert Spaces
section hilbert_space_theorems

-- We add the completeness assumption
variable [CompleteSpace E]

theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪x,v⟫ := by
 sorry

end hilbert_space_theorems
end inner_product_space_theorems

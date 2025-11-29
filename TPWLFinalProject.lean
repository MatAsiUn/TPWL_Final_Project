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
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪x,v⟫ := by
 sorry

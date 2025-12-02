import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
--import Mathlib.LinearAlgebra.Span.Basic
--import Mathlib.LinearAlgebra.FiniteDimensional.Defs
--import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
--import Mathlib.Analysis.Normed.Module.Basic
--import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Complex.Basic

set_option linter.style.commandStart false

-- As in FA1, our first step to defining duals is to define what it means to be a linear functional
def linear_function_prop (K V : Type _) [Field K] [AddCommGroup V] [Module K V] (F: V → K) :=
  ∀ (x y : V) (a b : K), F (a • x + b • y) = a * (F x) + b * (F y)
-- Note that "V" is our vector space here

--Definition Error
-- Now define the linear functional Fy induced by a vector y in Hilbert space H.
--variable {K H: Type _}[RCLike K][InnerProductSpace K H]{y : H}
--def inner_product_functional (x: H) : K :=
 --fun x => inner x y

open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- The statment of Riesz Representation Theorem for a trivial G (G identically 0)
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G x = 0):
 G x = ⟪x,0⟫ := by
 -- We use a lemma found in InnerProductSpace.Basic, that tells us the inner
 -- product of anything with 0 is 0
 simp only [inner_zero_right]

-- We can use exact as G x = 0, is what is left to prove but this was one of
-- assumptions
 exact h

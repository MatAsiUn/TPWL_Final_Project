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
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.commandStart false

-- We define what it means for a functional to be linear
def linear_function_prop (K V : Type _) [Field K] [AddCommGroup V] [Module K V] (F: V → K) :=
  ∀ (x y : V) (a b : K), F (a • x + b • y) = a * (F x) + b * (F y)
-- Note that "V" is our vector space here

open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- The statment of Riesz Representation Theorem for a trivial G (G identically 0)
lemma Riesz_Representation_Theorem_TrivialG {x : E}(G: StrongDual ℂ E)(h: G x = 0):
 G x = ⟪x,0⟫ := by
 -- We use a lemma found in InnerProductSpace.Basic, that tells us the inner
 -- product of anything with 0 is 0
 simp [inner_zero_right]

-- We can use exact as G x = 0, is what is left to prove but this was one of
-- assumptions
 exact h

lemma KerGClosed (G: StrongDual ℂ E): IsClosed (LinearMap.ker G : Set E) := by
 exact ContinuousLinearMap.isClosed_ker G

-- Introduce Hilber Space variable (and add strong dual to make life easier)
variable[CompleteSpace E]

--def kernel_of_G : Set E := { x : E | G x = 0 }

-- Prove that it is closed
-- lemma kernel_of_G_is_closed : IsClosed (kernel_of_G G) := by
 -- G is continuous as it is in the dual
 --have hG : Continuous G := G.continuous

 -- {0} is closed as it is a singleton set
 --have h0 : IsClosed ({0} : Set ℂ) := isClosed_singleton
 --exact?
 --sorry

 -- Cauchy-Schwartz

theorem Riesz_Representation_Theorem(G: StrongDual ℂ E):
 ∃! v : E, ∀ x : E, G x = ⟪v,x⟫ := by
 sorry

 -- Riesz corollary, to prove that canonical map is an isometric conjugate-linear
 -- isomorphism
 -- defn required "noncomputable"

noncomputable def canonical_map (v : E) : StrongDual ℂ E :=
  (innerSL ℂ : E →L⋆[ℂ] E →L[ℂ] ℂ) v

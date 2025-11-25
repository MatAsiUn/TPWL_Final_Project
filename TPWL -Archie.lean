import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
set_option linter.style.commandStart false

--- As in FA1, our first step to defining duals is to define what it means to be a linear functional
def isLinearFunctional (K V : Type _)[Field K][AddCommGroup V][Module K V] (F: V → K) :=
∀ {x y : V} (a b: K), F (a • x + b • y) = a * F x + b * F y
--- Note "V" is our vector space here

import TPWLFinalProject.Basic
import Mathlib.Tactic.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
set_option linter.style.commandStart false

-- As in FA1, our first step to defining duals is to define what it means to be a linear functional
def linear_function_prop (K V : Type _) [Field K] [AddCommGroup V] [Module K V] (F: V → K) :=
  ∀ (x y : V) (a b : K), F (a • x + b • y) = a * (F x) + b * (F y)
-- Note that "V" is our vector space here

--PROBLEM
-- Now define the linear functional Fy induced by a vector y in Hilbert space H.
--variable {K H: Type _}[RCLike K][InnerProductSpace K H]{y : H}
--def inner_product_functional (x: H) : K :=
 --fun x => inner x y

--theorem inner_prod_func_is_lin :

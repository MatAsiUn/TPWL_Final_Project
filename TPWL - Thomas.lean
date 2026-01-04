import TPWLFinalProject.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic

set_option linter.style.commandStart false

open scoped ComplexInnerProductSpace

/-
  Uniqueness part of the Riesz Representation Theorem.

  Goal:
  Given two vectors v1 and v2 such that
    G x = inner x v1 and G x = inner x v2  for all x,
  prove that v1 = v2.
-/

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/--
Key lemma: if a vector is orthogonal to *every* vector, then it must be zero.
This is the core idea behind uniqueness.
-/
lemma inner_orth_zero (w : E) (h : ∀ x : E, ⟪w, x⟫ = 0) : w = 0 := by
  have hww: ⟪w, w⟫ = 0 := by
    simpa using h w
  exact inner_self_eq_zero.mp hww
  -- Proof idea (to be formalised):
  -- Take x = w. Then:
  --   inner w w = 0.
  -- But inner product is positive definite, so this implies w = 0.

/--
Uniqueness: if the same continuous linear functional G is represented by v1 and v2,
then v1 = v2.
-/
lemma riesz_uniqueness {G : StrongDual ℂ E} {v1 v2 : E}
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

import data.int.gcd
import data.matrix.basic
import linear_algebra.determinant
import tactic.linarith

/-! Computing the class number for quadratic number fields -/

/--
  A quadratic form `f` is a function `f(x, y) := a * x^2 + b * x * y + c * y^2`,
  which we represent as a tuple `(a, b, c)` of coefficients.

  To represent this form as a function again, we can use `eval`.
-/
structure quadratic_form := (a : ℤ) (b : ℤ) (c : ℤ)

/-- Matrices with integer entries `((α β) (γ δ))` and determinant 1. -/
def SL₂ℤ := { M : matrix (fin 2) (fin 2) ℤ // M.det = 1 }

namespace SL₂ℤ
def α (M : SL₂ℤ) : ℤ := M.1 0 0
def β (M : SL₂ℤ) : ℤ := M.1 0 1
def γ (M : SL₂ℤ) : ℤ := M.1 1 0
def δ (M : SL₂ℤ) : ℤ := M.1 1 1
end SL₂ℤ

/-- Since `M` and `-M` have the same action on a quadratic form, we choose γ positive. -/
def PSL₂ℤ := { M : matrix (fin 2) (fin 2) ℤ // M.det = 1 ∧ 0 ≤ M 1 0 }
namespace PSL₂ℤ
def α (M : PSL₂ℤ) : ℤ := M.1 0 0
def β (M : PSL₂ℤ) : ℤ := M.1 0 1
def γ (M : PSL₂ℤ) : ℤ := M.1 1 0
def δ (M : PSL₂ℤ) : ℤ := M.1 1 1
end PSL₂ℤ

namespace quadratic_form

/--
  Evaluate the quadratic form as a function.

  This evaluation function is defined for all α for which the expression
  `ax^2 + bxy + cy^2` makes sense.
-/
def eval {α} [has_add α] [has_mul α] [has_pow α ℕ] [has_coe ℤ α] (form : quadratic_form) (x y : α) : α :=
form.a * x^2 + form.b * x * y + form.c * y^2

/--
  A primitive quadratic form has no common divisor of all three coefficients.
-/
def is_primitive (form : quadratic_form) : Prop :=
int.gcd (int.gcd form.a form.b) form.c = 1

/--
  Integer matrices have an action on quadratic forms by multiplication on the input `(x, y)`.

  In other words, `f(x, y)` is mapped to `f(αx + βy, γx + δy)` by the matrix `((α β) (γ δ)).`
-/
def matrix_action (mat : matrix (fin 2) (fin 2) ℤ) (form : quadratic_form) : quadratic_form :=
let α := mat 0 0, β := mat 0 1, γ := mat 1 0, δ := mat 1 1 in ⟨
  form.a * α^2 + form.b * α * γ + form.c * γ^2,
  2 * form.a * α * β + form.b * (α * δ + β * γ) + 2 * form.c * γ * δ,
  form.a * β^2 + form.b * β * δ + form.c * δ^2⟩

infixr ` · `:70 := matrix_action

/--
  The action of a matrix `M` is the same as the action of `-M`.
-/
lemma action_neg_invariant (M : matrix (fin 2) (fin 2) ℤ) (f : quadratic_form) : -M · f = M · f := sorry

/--
  The discriminant of a quadratic form.

  If we fix `y = 1`, this is exactly the discriminant of a quadratic equation.
-/
def discr (form : quadratic_form) : ℤ := form.b^2 - 4 * form.a * form.c

/--
  Matrices with determinant = 1 preserve the discriminant of a quadratic form.
-/
lemma det_invariant_for_SL (f : quadratic_form) (M : SL₂ℤ) : (M.1 · f).discr = f.discr := sorry

end quadratic_form

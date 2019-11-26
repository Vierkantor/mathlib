import data.int.gcd
import data.matrix.basic
import data.vector2
import linear_algebra.determinant
import linear_algebra.matrix
import tactic.linarith
import tactic.fin_cases

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

/-- We can recover the parameters by evaluating the form. -/
lemma a_of_eval (f : quadratic_form) : f.a = eval f 1 0 := by {unfold eval, ring, norm_cast}
lemma c_of_eval (f : quadratic_form) : f.c = eval f 0 1 := by {unfold eval, ring, norm_cast}
lemma b_of_eval (f : quadratic_form) : f.b = eval f 1 1 - eval f 1 0 - eval f 0 1 :=
by {unfold eval, ring, norm_cast}

/-- Quadratic forms are defined uniquely by their evaluation on a specific set of vectors. -/
lemma eq_of_specific_eval_eq (f g : quadratic_form) :
  (eval f 1 0 : ℤ) = eval g 1 0 → (eval f 0 1 : ℤ) = eval g 0 1 → (eval f 1 1 : ℤ) = eval g 1 1 → f = g := 
begin
  intros e10 e01 e11,
  have : f.a = g.a := by rw [a_of_eval, a_of_eval, e10],
  have : f.c = g.c := by rw [c_of_eval, c_of_eval, e01],
  have : f.b = g.b := by rw [b_of_eval, b_of_eval, e10, e01, e11],
  cases f, cases g,
  finish
end

/-- Quadratic forms are defined uniquely by their evaluation. -/
lemma eq_of_eval_eq (f g : quadratic_form) (h : ∀ (x y : ℤ), eval f x y = eval g x y) : f = g :=
eq_of_specific_eval_eq f g (h 1 0) (h 0 1) (h 1 1)

/--
  A primitive quadratic form has no common divisor of all three coefficients.
-/
def is_primitive (form : quadratic_form) : Prop :=
int.gcd (int.gcd form.a form.b) form.c = 1

section matrix_action

abbreviation M₂ℤ := matrix (fin 2) (fin 2) ℤ

/--
  Integer matrices have an action on quadratic forms by multiplication on the input `(x, y)`.

  In other words, `f(x, y)` is mapped to `f(αx + βy, γx + δy)` by the matrix `((α β) (γ δ)).`

  We don't instantiate a class instance yet since we will look primarily at the action of PSL₂,
  on quadratic forms with fixed discriminant.
-/
def matrix_action (mat : M₂ℤ) (form : quadratic_form) : quadratic_form :=
let α := mat 0 0, β := mat 0 1, γ := mat 1 0, δ := mat 1 1, a := form.a, b := form.b, c := form.c in
  ⟨ a * α^2 + b * α * γ + c * γ^2
  , 2 * a * α * β + b * (α * δ + β * γ) + 2 * c * γ * δ
  , a * β^2 + b * β * δ + c * δ^2
  ⟩
local infixr ` · `:70 := matrix_action

/--
  The action of a matrix `M` is the same as the action of `-M`.
-/
lemma action_neg_invariant (M : M₂ℤ) (f : quadratic_form) : -M · f = M · f := 
by simp [matrix_action]

/--
  The action works by multiplicating vectors in `ℤ^2` with the matrix.
-/
@[simp] lemma eval_action (M : M₂ℤ) (f : quadratic_form) (x y : ℤ) :
  eval (M · f) x y = eval f (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) :=
by {unfold matrix_action eval, norm_cast, ring}

/--
  An alternative way of looking at quadratic forms is as maps on vector spaces.
  In this form, proofs about the matrix action are easier to state.
-/
def to_matrix (f : quadratic_form) : fin 2 → fin 2 → ℤ
| ⟨0, _⟩ ⟨0, _⟩ := f.a
| ⟨0, _⟩ ⟨1, _⟩ := f.b
| ⟨1, _⟩ ⟨1, _⟩ := f.c
| _ _ := 0

/--
  Conversion from matrix to quadratic form.

  This is lossy: `M 1 0` should be assumed to be `0`.
-/
def of_matrix (M : M₂ℤ) : quadratic_form := ⟨M 0 0, M 0 1, M 1 1⟩

/-- Allow `simp` to reduce `f.to_matrix 0 0`. -/
@[simp] lemma to_matrix_00 (f : quadratic_form) : to_matrix f 0 0 = f.a := refl _
@[simp] lemma to_matrix_01 (f : quadratic_form) : to_matrix f 0 1 = f.b := refl _
@[simp] lemma to_matrix_10 (f : quadratic_form) : to_matrix f 1 0 = 0 := refl _
@[simp] lemma to_matrix_11 (f : quadratic_form) : to_matrix f 1 1 = f.c := refl _

/--
  Evaluation of these matrices can be defined on ℤ^2:
-/
def eval_matrix (M : M₂ℤ) (xy : fin 2 → ℤ) : ℤ :=
matrix.mul (matrix.row xy) (matrix.mul M (matrix.col xy)) () ()

/--
  Evaluation of these matrices in the same style as `quadratic_form.eval`.
-/
def eval_matrix' (M : M₂ℤ) (x y : ℤ) : ℤ :=
eval_matrix M (vector.nth (x :: y :: vector.nil))

-- TODO: to_additive doesn't work here because it tries to turn `f 0` into `f 1`
@[simp]
lemma finset.prod_fin_2 {α} [comm_monoid α] (f : fin 2 → α) :
  finset.prod finset.univ f = f 0 * f 1 :=
have univ_2 : (@finset.univ (fin 2) _) = [0, 1].to_finset := refl _,
have not_in_0 : (0 : fin 2) ∉ list.to_finset [(1 : fin 2)] := of_to_bool_ff rfl,
have not_in_1 : (1 : fin 2) ∉ list.to_finset (list.nil : list (fin 2)) := not_false,
begin
  -- We use `rw` here to ensure that `insert 0 (list.to_finset ...)` doesn't get simplified further.
  rw [univ_2, list.to_finset_cons, finset.prod_insert not_in_0, list.to_finset_cons, finset.prod_insert not_in_1],
  -- But now we can apply simp.
  simp
end
@[simp]
lemma finset.sum_fin_2 {α} [add_comm_monoid α] (f : fin 2 → α) :
  finset.sum finset.univ f = f 0 + f 1 :=
have univ_2 : (@finset.univ (fin 2) _) = [0, 1].to_finset := refl _,
have not_in_0 : (0 : fin 2) ∉ list.to_finset [(1 : fin 2)] := of_to_bool_ff rfl,
have not_in_1 : (1 : fin 2) ∉ list.to_finset (list.nil : list (fin 2)) := not_false,
begin
  -- We use `rw` here to ensure that `insert 0 (list.to_finset ...)` doesn't get simplified further.
  rw [univ_2, list.to_finset_cons, finset.sum_insert not_in_0, list.to_finset_cons, finset.sum_insert not_in_1],
  -- But now we can apply simp.
  simp
end

/-- We prove that matrix evaluation coincides with the evaluation defined by `eval`. -/
@[simp]
lemma eval_to_matrix (f : quadratic_form) (x y : ℤ) : eval_matrix' (to_matrix f) x y = eval f x y :=
by { simp [eval_matrix', eval_matrix, eval, matrix.mul], ring! }
/-- Since not all matrices correspond to a quadratic form, we add an extra assumption here. -/
@[simp]
lemma eval_of_matrix (M : M₂ℤ) (x y : ℤ) (upper_diag : M 1 0 = 0) : eval (of_matrix M) x y = eval_matrix' M x y :=
by { simp [eval_matrix', eval_matrix, eval, matrix.mul, upper_diag], ring! }

/-- The conversion *to* a matrix has an inverse. -/
@[simp]
theorem of_matrix_to_matrix (f : quadratic_form) : of_matrix (to_matrix f) = f := begin
apply eq_of_specific_eval_eq; rw [eval_of_matrix, eval_to_matrix], repeat {apply to_matrix_10}
end

/--
  The action on quadratic forms as matrices is conjugation.
-/
def matrix_action_matrix (M N : M₂ℤ) : M₂ℤ := M.transpose * (N * M)

-- TODO: move this to the right place.
@[simp] lemma matrix.transpose_col {α m} [fintype m] (v : m → α) : (matrix.col v).transpose = matrix.row v := sorry
@[simp] lemma matrix.transpose_row {α m} [fintype m] (v : m → α) : (matrix.row v).transpose = matrix.col v := sorry
@[simp] lemma row_vec_mul {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.row (matrix.vec_mul v M) = matrix.mul (matrix.row v) M := sorry
@[simp] lemma col_vec_mul {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.col (matrix.vec_mul v M) = (matrix.mul (matrix.row v) M).transpose := sorry
@[simp] lemma col_mul_vec {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.col (matrix.mul_vec M v) = (matrix.mul M (matrix.col v)) := sorry
@[simp] lemma row_mul_vec {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.row (matrix.mul_vec M v) = (matrix.mul M (matrix.col v)).transpose := sorry

/-- Or we can view the action of `M` as multiplying the input with `M`. -/
@[simp] lemma eval_matrix_action (M N : M₂ℤ) (xy : fin 2 → ℤ) :
  eval_matrix (matrix_action_matrix M N) xy = eval_matrix N (matrix.mul_vec M xy) :=
calc eval_matrix (matrix_action_matrix M N) xy
    = matrix.mul (matrix.row xy) (matrix.mul (matrix.mul M.transpose (matrix.mul N M)) (matrix.col xy)) () () : refl _
... = matrix.mul (matrix.mul (matrix.row xy) M.transpose) (matrix.mul N (matrix.mul M (matrix.col xy))) () () : by repeat { rw [matrix.mul_assoc] }
... = matrix.mul ((matrix.mul M (matrix.col xy)).transpose) (matrix.mul N (matrix.mul M (matrix.col xy))) () () : by simp
... = eval_matrix N (matrix.mul_vec M xy) : by simp [eval_matrix]

/--
  Conjugation corresponds to the action of matrices on quadratic forms.
-/
lemma matrix_action_to_matrix (M N : M₂ℤ) :
  of_matrix (matrix_action_matrix M N) = M · (of_matrix N) :=
begin
  apply eq_of_eval_eq,
  intros x y,
  rw [eval_of_matrix, eval_action, eval_matrix', eval_matrix_action, eval_of_matrix, eval_matrix'],
  congr,
  ext,
  fin_cases x_1,
  { calc matrix.vec_mul (vector.nth (x :: y :: vector.nil)) M 0
        = x * M 0 0 + (vector.nth (x :: y :: vector.nil) 1) * M 1 0 : by simp [matrix.vec_mul]
    ... = M 0 0 * x + M 1 0 * y : by ac_refl
    ... = vector.nth ((M 0 0 * x + M 0 1 * y) :: (M 1 0 * x + M 1 1 * y) :: vector.nil) 0 : sorry }, { sorry },
end

/--
  The discriminant of a quadratic form.
-/
def discr (form : quadratic_form) : ℤ := form.b^2 - 4 * form.a * form.c

/-- We can recover the discriminant by evaluating the form. -/
lemma discr_of_eval (f : quadratic_form) :
  f.discr = (eval f 1 1 - eval f 0 1 - eval f 1 0)^2 - 4 * (eval f 1 0 * eval f 0 1) :=
by rw [discr, b_of_eval, a_of_eval, c_of_eval]; ring

/--
  Matrices with determinant = 1 preserve the discriminant of a quadratic form.
-/
lemma det_invariant_for_SL (f : quadratic_form) (M : SL₂ℤ) : (M.1 · f).discr = f.discr :=
begin
  cases M with M h,
  rw discr_of_eval, rw discr_of_eval,
  
end

end matrix_action

end quadratic_form

import data.int.gcd
import data.matrix.basic
import data.vector2
import group_theory.group_action
import linear_algebra.matrix
import linear_algebra.nonsingular_inverse
import tactic.linarith
import tactic.fin_cases
import tactic.find

/-! Computing the class number for quadratic number fields -/

section matrix_helpers

/-! ### `matrix_helpers` section
  This section contains some helper lemmas on (calculating with) matrices.
  TODO: move these to a suitable file
-/

@[to_additive]
lemma finset.prod_univ {α n} [comm_monoid α] (f : fin n → α) : finset.prod finset.univ f =
  ((list.fin_range n).map f).foldr (*) 1
:= rfl

@[simp]
lemma list.foldr_fin_range {α} {f : fin 2 → α → α} {e} : list.foldr f e (list.fin_range 2) = f 0 (f 1 e) := rfl

lemma matrix.det_2x2 {α} [comm_ring α] (M : matrix (fin 2) (fin 2) α) :
M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := calc
M.det = (0 + 1) * (M 0 0 * (M 1 1 * 1)) + ((- (0 + 1) * (M 1 0 * (M 0 1 * 1))) + 0) : refl _
... = M 0 0 * M 1 1 - M 0 1 * M 1 0 : by simp [mul_comm]

end matrix_helpers

/--
  A quadratic form `f` is a function `f(x, y) := a * x^2 + b * x * y + c * y^2`,
  which we represent as a tuple `(a, b, c)` of coefficients.

  To represent this form as a function again, we can use `eval`.
-/
structure quadratic_form := (a : ℤ) (b : ℤ) (c : ℤ)

/-- Matrices with integer entries `((α β) (γ δ))` and determinant 1. -/
@[ext]
structure SL₂ℤ := (M : matrix (fin 2) (fin 2) ℤ) (prop : M.det = 1)

instance : group SL₂ℤ := ⟨
  λ A B, ⟨A.1 * B.1, by rw [matrix.det_mul, A.2, B.2, mul_one]⟩,
  λ A B C, SL₂ℤ.ext _ _ (mul_assoc _ _ _),
  ⟨1, matrix.det_one⟩,
  λ A, SL₂ℤ.ext _ _ (one_mul _),
  λ A, SL₂ℤ.ext _ _ (mul_one _),
  λ A, ⟨matrix.adjugate A.1, matrix.det_adjugate_eq_one_of_det_eq_one A.1 A.2⟩,
  λ A, SL₂ℤ.ext _ _ (matrix.adjugate_mul_det_one A.1 A.2)
⟩

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
open_locale matrix

/--
  A primitive quadratic form has no common divisor of all three coefficients.
-/
def is_primitive (form : quadratic_form) : Prop := -- TODO: move this to another section?
int.gcd (int.gcd form.a form.b) form.c = 1

abbreviation M₂ℤ := matrix (fin 2) (fin 2) ℤ

/--
  An alternative way of looking at quadratic forms is as maps on vector spaces.
  In this form, proofs about the matrix action are easier to state.

  However, we introduce a factor 2 in the `a` and `c` coefficients,
  so conversion back doesn't necessarily work.
-/
def to_matrix (f : quadratic_form) : M₂ℤ
| ⟨0, _⟩ ⟨0, _⟩ := f.a * 2
| ⟨0, _⟩ ⟨1, _⟩ := f.b
| ⟨1, _⟩ ⟨0, _⟩ := f.b
| ⟨1, _⟩ ⟨1, _⟩ := f.c * 2
| _ _ := 0 -- Shouldn't occur, but providing it anyway makes the definition easier to give.

/-- Allow `simp` to reduce `f.to_matrix 0 0`. -/
@[simp] lemma to_matrix_00 (f : quadratic_form) : to_matrix f 0 0 = f.a * 2 := refl _
@[simp] lemma to_matrix_01 (f : quadratic_form) : to_matrix f 0 1 = f.b := refl _
@[simp] lemma to_matrix_10 (f : quadratic_form) : to_matrix f 1 0 = f.b := refl _
@[simp] lemma to_matrix_11 (f : quadratic_form) : to_matrix f 1 1 = f.c * 2 := refl _

/--
  Conversion from matrix to quadratic form.

  Many theorems will assume that `M 0 1 = M 1 0` and that `M 0 0` and `M 1 1` are multiples of `2`,
  e.g. when proving that `to_matrix ∘ of_matrix` is the identity.
  These preconditions are collected in the structure `of_matrix_pre`.
-/
def of_matrix (M : M₂ℤ) : quadratic_form := ⟨M 0 0 / 2, M 0 1, M 1 1 / 2⟩

section even
/-- There is a specific notion of `even` that we need for `of_matrix`. -/
structure even (n : ℤ) : Prop := (h : n / 2 * 2 = n)

lemma even_2 : even 2 := ⟨by norm_num⟩
lemma even_add_even (a b : ℤ) : even a → even b → even (a + b) := λ ha hb, ⟨calc
(a + b) / 2 * 2
    = (a / 2 * 2 + b / 2 * 2) / 2 * 2 : by rw [ha.h, hb.h]
... = (a / 2 + b / 2) * 2 / 2 * 2 : by rw [add_mul]
... = (a / 2 + b / 2) * 2 : by rw [int.mul_div_cancel _ (by linarith : (2 : ℤ) ≠ 0)]
... = a + b : by rw [add_mul, ha.h, hb.h]⟩
lemma even_mul (a b : ℤ) : even a → even (a * b) := λ ha, ⟨calc
(a * b) / 2 * 2 = ((a / 2 * 2) * b) / 2 * 2 : by rw [ha.h]
... = ((a / 2) * b) * 2 / 2 * 2 : by ac_refl
... = ((a / 2) * b) * 2 : by rw [int.mul_div_cancel _ (by linarith : (2 : ℤ) ≠ 0)]
... = ((a / 2 * 2) * b) : by ac_refl
... = a * b : by rw [ha.h]⟩
lemma mul_even (a b : ℤ) : even b → even (a * b) := by { rw [mul_comm], apply even_mul }
end even

/-- The preconditions for when `of_matrix` makes sense. -/
structure of_matrix_pre (M : M₂ℤ) : Prop :=
(ha : even (M 0 0)) (hb : M 0 1 = M 1 0) (hc : even (M 1 1))

/-- Allow `simp` to reduce `(of_matrix M).a`. -/
@[simp] lemma of_matrix_a (M : M₂ℤ) : (of_matrix M).a = M 0 0 / 2 := refl _
@[simp] lemma of_matrix_b (M : M₂ℤ) : (of_matrix M).b = M 0 1 := refl _
@[simp] lemma of_matrix_c (M : M₂ℤ) : (of_matrix M).c = M 1 1 / 2 := refl _

/-- The output to `to_matrix` satisfies the preconditions for `of_matrix`. -/
lemma of_matrix_pre_to_matrix (f : quadratic_form) : of_matrix_pre (to_matrix f) :=
⟨ mul_even _ _ even_2 , rfl , mul_even _ _ even_2⟩

/-- The conversion from a matrix has an inverse only if `of_matrix_pre` holds.

  The theorem `of_matrix_to_matrix` shows the other composition is also the identity.
-/
@[simp]
theorem to_matrix_of_matrix (M : M₂ℤ) (h : of_matrix_pre M) : to_matrix (of_matrix M) = M := begin
ext,
fin_cases i; fin_cases j,
{ exact h.ha.h },
{ refl },
{ exact h.hb },
{ exact h.hc.h },
end

section eval
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
  The equivalent to `eval` for the matrix representation.

  Use `eval_matrix'` if you want to pass arguments in exactly the same way.
-/
def eval_matrix (M : M₂ℤ) (xy : fin 2 → ℤ) : ℤ :=
(matrix.row xy ⬝ M ⬝ matrix.col xy) () ()

def vec2 {α} (x y : α) (i : fin 2) : α := if i = 0 then x else y

/--
  Evaluation of these matrices in the same style as `quadratic_form.eval`.
-/
def eval_matrix' (M : M₂ℤ) (x y : ℤ) : ℤ :=
eval_matrix M (vec2 x y)

/--
  Matrix evaluation coincides with the evaluation defined by `eval`.

  See also `eval_of_matrix` if you are starting with a matrix representation.
-/
@[simp]
lemma eval_to_matrix (f : quadratic_form) (x y : ℤ) : eval_matrix' (to_matrix f) x y = eval f x y * 2 :=
calc eval_matrix' (to_matrix f) x y
    = ((x * (f.a * 2) + (y * f.b + 0)) * x) + ((x * f.b + (y * (f.c * 2) + 0)) * y + 0) : rfl
... = (f.a * x^2 + f.b * x * y + f.c * y^2) * 2 : by ring
... = eval f x y * 2 : by {unfold eval, norm_cast}

/--
  Matrix evaluation coincides with the evaluation defined by `eval`.

  See also `eval_to_matrix` if you are starting with a `quadratic_form` triple.
-/
lemma eval_of_matrix (M : M₂ℤ) (x y : ℤ) (h : of_matrix_pre M) :
  eval (of_matrix M) x y * 2 = eval_matrix' M x y := calc
eval (of_matrix M) x y * 2
    = (M 0 1 * x * y + (M 1 1 / 2 * y ^ 2 + M 0 0 / 2 * x ^ 2)) * 2 : by simp [eval]
... = (M 0 1 * x * y * 2 + ((M 1 1 / 2 * 2) * y ^ 2 + (M 0 0 / 2 * 2) * x ^ 2)) :
  by {rw [add_mul, add_mul], ac_refl}
... = (M 0 1 * x * y * 2 + (M 1 1 * y ^ 2 + M 0 0 * x ^ 2)) : by rw [h.ha.h, h.hc.h]
... = ((x * M 0 0 + (y * M 0 1 + 0)) * x) + ((x * M 0 1 + (y * M 1 1 + 0)) * y + 0) : by ring
... = ((x * M 0 0 + (y * M 1 0 + 0)) * x) + ((x * M 0 1 + (y * M 1 1 + 0)) * y + 0) : by rw [h.hb]
... = eval_matrix' M x y : rfl

/--
  The matrix `M` represents a form `f` if their evaluations agree.
-/
lemma eq_of_eval_matrix_eq (M : M₂ℤ) (f : quadratic_form) (hM : of_matrix_pre M) :
  (∀ x y, eval_matrix' M x y = eval f x y * 2) → of_matrix M = f :=
begin
  intro eval_eq,
  apply eq_of_eval_eq,
  intros x y,
  rw
    [ ←@int.mul_div_cancel (eval (of_matrix M) _ _) 2 (by norm_num)
    , ←@int.mul_div_cancel (eval f _ _) 2 (by norm_num)
    , eval_of_matrix _ _ _ hM
    ],
  congr' 1,
  apply eval_eq
end

/-- The conversion to a matrix always has an inverse.

  The theorem `to_matrix_of_matrix` shows the other composition is also the identity.
-/
@[simp]
theorem of_matrix_to_matrix (f : quadratic_form) : of_matrix (to_matrix f) = f :=
eq_of_eval_matrix_eq _ _ (of_matrix_pre_to_matrix f) (eval_to_matrix f)
end eval

lemma injective_to_matrix : function.injective to_matrix :=
function.injective_of_left_inverse of_matrix_to_matrix

section matrix_action
local attribute [simp] matrix.mul_val
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
  The action on quadratic forms as matrices is conjugation.
-/
def matrix_action_matrix (M N : M₂ℤ) : M₂ℤ := M.transpose ⬝ N ⬝ M

/--
  Conjugation preserves the precondition of `of_matrix`.

  That is, matrices that result from a triple `⟨a, b, c⟩ : quadratic_form`
  will also correspond to a triple after applying the matrix action.
  We will prove later on that the action on triples and the action on matrices are the same.
-/
lemma of_matrix_pre_action (M N : M₂ℤ) (h : of_matrix_pre N) : of_matrix_pre (matrix_action_matrix M N) := begin
  cases h,
  split,
  { suffices : even ((N 1 1 * M 1 0 + 2 * N 1 0 * M 0 0) * M 1 0 + N 0 0 * M 0 0 ^ 2),
    { simp [matrix.mul_val, matrix_action_matrix, h_hb, finset.sum_univ], ring, assumption },
    apply even_add_even; apply even_mul,
    { apply even_add_even; apply even_mul, assumption, exact even_mul _ _ even_2 },
    assumption
    },
  { simp [matrix_action_matrix, h_hb, finset.sum_univ], ring },
  { suffices : even ((N 1 1 * M 1 1 + 2 * N 1 0 * M 0 1) * M 1 1 + N 0 0 * M 0 1 ^ 2),
    { simp [matrix_action_matrix, h_hb, finset.sum_univ], ring, assumption },
    apply even_add_even; apply even_mul,
    { apply even_add_even; apply even_mul, assumption, exact even_mul _ _ even_2 },
    { assumption },
  }
end

/-- Or we can view the action of `M` as multiplying the input with `M`. -/
@[simp] lemma eval_matrix_action (M N : M₂ℤ) (xy : fin 2 → ℤ) :
  eval_matrix (matrix_action_matrix M N) xy = eval_matrix N (matrix.mul_vec M xy) :=
calc eval_matrix (matrix_action_matrix M N) xy
    = (matrix.row xy ⬝ (Mᵀ ⬝ N ⬝ M) ⬝ matrix.col xy) () () : rfl
... = ((matrix.row xy ⬝ Mᵀ) ⬝ N ⬝ (M ⬝ matrix.col xy)) () () : by repeat { rw [matrix.mul_assoc] }
... = ((M ⬝ matrix.col xy)ᵀ ⬝ N ⬝ (M ⬝ matrix.col xy)) () () : by simp
... = eval_matrix N (matrix.mul_vec M xy) :
  by simp [matrix.row_mul_vec, matrix.col_mul_vec, eval_matrix, finset.sum_univ]

/--
  Conjugation corresponds to the action of matrices on quadratic forms.
-/
lemma matrix_action_of_matrix (M N : M₂ℤ) (hN : of_matrix_pre N):
  of_matrix (matrix_action_matrix M N) = M · (of_matrix N) :=
begin
  apply eq_of_eval_matrix_eq,
  { apply of_matrix_pre_action, assumption },
  intros x y,
  rw [eval_matrix', eval_matrix_action, eval_action, eval_of_matrix _ _ _ hN, eval_matrix'],
  congr,
  ext,
  fin_cases x_1,
  { calc matrix.mul_vec M (vec2 x y) 0
        = M 0 0 * vec2 x y 0 + M 0 1 * vec2 x y 1 : by simp [matrix.mul_vec, finset.sum_univ]
    ... = vec2 (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) 0 : rfl },
  { calc matrix.mul_vec M (vec2 x y) 1
      = M 1 0 * vec2 x y 0 + M 1 1 * vec2 x y 1 : by simp [matrix.mul_vec, finset.sum_univ]
    ... = vec2 (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) 1 : rfl }
end

/--
  Conjugation corresponds to the action of matrices on quadratic forms.
-/
lemma matrix_action_to_matrix (M : M₂ℤ) (f : quadratic_form) :
matrix_action_matrix M (to_matrix f) = to_matrix (M · f) :=
by rw
    [ ←of_matrix_to_matrix f
    , to_matrix_of_matrix (to_matrix f) (of_matrix_pre_to_matrix f)
    , ←matrix_action_of_matrix _ _ (of_matrix_pre_to_matrix f)
    , to_matrix_of_matrix _ (of_matrix_pre_action _ _ (of_matrix_pre_to_matrix f))
    ]

/--
  The identity matrix gives the identity action.
-/
lemma matrix_action_identity (f : quadratic_form) : matrix_action 1 f = f := begin
apply injective_to_matrix,
simp [symm (matrix_action_to_matrix 1 f), matrix_action_matrix]
end

/--
  Applying the product of two matrices is the same as applying the matrices consecutively.
-/
lemma matrix_action_mul (M N : M₂ℤ) (f : quadratic_form) :
  matrix_action (M * N) f = matrix_action N (matrix_action M f) :=
begin
  apply injective_to_matrix,
  rw [←matrix_action_to_matrix, ←matrix_action_to_matrix, ←matrix_action_to_matrix, matrix_action_matrix, matrix_action_matrix, matrix_action_matrix],
  simp [matrix.mul_assoc]
end

end matrix_action

section discr
open_locale matrix_action
/--
  The discriminant of a quadratic form.
-/
def discr (form : quadratic_form) : ℤ := form.b^2 - 4 * form.a * form.c

/--
  The discriminant of a matrix representation comes from its determinant.
-/
def discr_matrix (M : M₂ℤ) : ℤ := - M.det

/--
  The two ways to get a discriminant are equal.
-/
lemma discr_eq_discr_matrix (f : quadratic_form) : discr_matrix (to_matrix f) = f.discr := calc
discr_matrix (to_matrix f)
    = (to_matrix f) 0 1 * (to_matrix f) 1 0 - (to_matrix f) 0 0 * (to_matrix f) 1 1 :
      by { unfold discr_matrix, rw [matrix.det_2x2], ring }
... = f.discr : by { simp [discr], ring }

/--
  Matrices with determinant = 1 preserve the discriminant of a quadratic form.
-/
theorem det_invariant_for_SL (f : quadratic_form) (M : SL₂ℤ) : discr (matrix_action M.1 f) = f.discr := calc
discr (matrix_action M.1 f)
    = discr_matrix (to_matrix (matrix_action M.1 f)) : symm (discr_eq_discr_matrix _)
... = discr_matrix (matrix_action_matrix M.1 (to_matrix f)) : by rw [matrix_action_to_matrix]
... = - (M.1ᵀ ⬝ to_matrix f ⬝ M.1).det : by rw [discr_matrix, matrix_action_matrix]
... = - (M.1ᵀ * to_matrix f * M.1).det : rfl
... = - (M.1.det * (to_matrix f).det * M.1.det) :
  by rw [matrix.det_mul, matrix.det_mul, matrix.det_transpose]
... = discr_matrix (to_matrix f) : by simp [discr_matrix, M.2]
... = f.discr : discr_eq_discr_matrix _
end discr

section class_group

variable {d : ℤ}

@[ext]
structure QF (d : ℤ) :=
(form : quadratic_form) (fix_discr : form.discr = d)

-- Turn right action of M into a left action by replacing M with M⁻¹.
-- TODO: can we do this better?
instance : has_scalar SL₂ℤ (QF d) :=
⟨λ M f, ⟨matrix_action M⁻¹.1 f.1, trans (det_invariant_for_SL f.1 M⁻¹) f.fix_discr⟩⟩
instance : mul_action SL₂ℤ (QF d) := ⟨
λ f, QF.ext _ _ (matrix_action_identity _),
λ M N f, QF.ext _ _ (trans (congr_arg2 (λ (M : SL₂ℤ) f, matrix_action M.1 f) (mul_inv_rev M N) rfl)
                           (matrix_action_mul _ _ _))⟩

/-- Quadratic forms are considered equivalent if they share the same orbit. -/
def class_group (d : ℤ) : Type := quotient (mul_action.orbit_rel SL₂ℤ (QF d))

end class_group

end quadratic_form

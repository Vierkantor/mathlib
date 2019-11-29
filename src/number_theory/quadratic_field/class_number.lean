import data.int.gcd
import data.matrix.basic
import data.vector2
import linear_algebra.determinant
import linear_algebra.matrix
import tactic.linarith
import tactic.fin_cases

/-! Computing the class number for quadratic number fields -/

section matrix_helpers

/-! ### `matrix_helpers` section
  This section contains some helper lemmas on (calculating with) matrices.
  TODO: move these to a suitable file
-/

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

@[simp]
lemma matrix.mul_index {α m n p} [add_comm_monoid α] [has_mul α] [fintype m] [fintype n] [fintype p] (M : matrix m n α) (N : matrix n p α) (i : m) (j : p) :
matrix.mul M N i j = finset.sum (finset.univ : finset n) (λ k, M i k * N k j)
:= refl _
@[simp]
lemma matrix.transpose_index {α m n} [fintype m] [fintype n] (M : matrix m n α) (i : m) (j : n) :
M.transpose j i = M i j
:= refl _

lemma matrix.det_2x2 {α} [comm_ring α] (M : matrix (fin 2) (fin 2) α) :
M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := calc
M.det = (0 + 1) * (M 0 0 * (M 1 1 * 1)) + ((- (0 + 1) * (M 1 0 * (M 0 1 * 1))) + 0) : refl _
... = M 0 0 * M 1 1 - M 0 1 * M 1 0 : by simp [mul_comm]

lemma matrix.det_inverse {α n} [comm_ring α] [decidable_eq n] [fintype n] (M : matrix n n α) (σ : equiv.perm n) :
↑(σ⁻¹.sign) * finset.prod finset.univ (λ (i : n), M i (σ⁻¹ i)) = ↑(↑(σ.sign) : ℤ) * finset.prod finset.univ (λ (i : n), M (σ i) i) := begin
  rw [equiv.perm.sign_inv],
  congr' 1,
  apply finset.prod_bij (λ i _, σ⁻¹ i),
  { intros, apply finset.mem_univ },
  { intros, simp },
  { intros, simp at *, assumption },
  { intros, use σ b, simp }
end

lemma matrix.det_transpose {α n} [decidable_eq n] [fintype n] [comm_ring α] (M : matrix n n α) :
matrix.det (M.transpose) = matrix.det M := begin
  apply finset.sum_bij (λ σ _, σ⁻¹),
  { intros, simp },
  { intros, rw ←matrix.det_inverse, refl },
  { intros, simp at *, assumption },
  { intros, use b⁻¹, finish },
end

@[simp]
lemma matrix.transpose_col {α m} [fintype m] (v : m → α) :
  (matrix.col v).transpose = matrix.row v :=
by {ext, refl}
@[simp]
lemma matrix.transpose_row {α m} [fintype m] (v : m → α) :
  (matrix.row v).transpose = matrix.col v :=
by {ext, refl}
lemma row_vec_mul {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : m → α) :
matrix.row (matrix.vec_mul v M) = matrix.mul (matrix.row v) M := by {ext, refl}
lemma col_vec_mul {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : m → α) :
matrix.col (matrix.vec_mul v M) = (matrix.mul (matrix.row v) M).transpose := by {ext, refl}
lemma col_mul_vec {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : n → α) :
matrix.col (matrix.mul_vec M v) = (matrix.mul M (matrix.col v)) := by {ext, refl}
lemma row_mul_vec {α m n} [fintype m] [fintype n] [semiring α] (M : matrix m n α) (v : n → α) :
matrix.row (matrix.mul_vec M v) = (matrix.mul M (matrix.col v)).transpose := by {ext, refl}

end matrix_helpers

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
  A primitive quadratic form has no common divisor of all three coefficients.
-/
def is_primitive (form : quadratic_form) : Prop :=
int.gcd (int.gcd form.a form.b) form.c = 1

abbreviation M₂ℤ := matrix (fin 2) (fin 2) ℤ

/--
  An alternative way of looking at quadratic forms is as maps on vector spaces.
  In this form, proofs about the matrix action are easier to state.

  However, we introduce a factor 2 in the `a` and `c` coefficients,
  so conversion back doesn't necessarily work.
-/
def to_matrix (f : quadratic_form) : fin 2 → fin 2 → ℤ
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

/-- The specific notion of `even` that will be useful in this section. -/
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
  Evaluation of these matrices can be defined on ℤ^2:
-/
def eval_matrix (M : M₂ℤ) (xy : fin 2 → ℤ) : ℤ :=
matrix.mul (matrix.row xy) (matrix.mul M (matrix.col xy)) () ()

/--
  Evaluation of these matrices in the same style as `quadratic_form.eval`.
-/
def eval_matrix' (M : M₂ℤ) (x y : ℤ) : ℤ :=
eval_matrix M (vector.nth (x :: y :: vector.nil))

section matrix_action
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

/-- Matrix evaluation coincides with the evaluation defined by `eval`. -/
@[simp]
lemma eval_to_matrix (f : quadratic_form) (x y : ℤ) : eval_matrix' (to_matrix f) x y = eval f x y * 2 :=
by { simp [eval_matrix', eval_matrix, eval, matrix.mul], ring! }
/--
  Matrix evaluation coincides with the evaluation defined by `eval`.
  
  Since not all matrices correspond to a quadratic form, we need some extra assumptions
  compared to `eval_to_matrix`.
-/
lemma eval_of_matrix (M : M₂ℤ) (x y : ℤ) (h : of_matrix_pre M) :
  eval (of_matrix M) x y * 2 = eval_matrix' M x y := calc
eval (of_matrix M) x y * 2
    = ((of_matrix M).a * 2) * x^2 + ((of_matrix M).b + (of_matrix M).b) * x * y + ((of_matrix M).c * 2) * y^2 : by { unfold eval, norm_cast, ring }
... = ((M 0 0 / 2) * 2) * x^2 + (M 0 1 + M 0 1) * x * y + ((M 1 1 / 2) * 2) * y^2 : by simp
... = M 0 0 * x^2 + (M 0 1 + M 1 0) * x * y + M 1 1 * y^2 : by rw [h.ha.h, h.hb, h.hc.h]
... = eval_matrix' M x y : by { simp [eval_matrix', eval_matrix, matrix.mul], ring! }

/-- A helper for proving when a matrix represents a given form. -/
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

/-- The conversion _to_ a matrix has an inverse in general. -/
@[simp]
theorem of_matrix_to_matrix (f : quadratic_form) : of_matrix (to_matrix f) = f :=
eq_of_eval_matrix_eq _ _ (of_matrix_pre_to_matrix f) (eval_to_matrix f)

/-- The conversion _from_ a matrix has an inverse only if `of_matrix_pre` holds. -/
@[simp]
theorem to_matrix_of_matrix (M : M₂ℤ) (h : of_matrix_pre M) : to_matrix (of_matrix M) = M := begin
ext,
fin_cases i; fin_cases j,
{ exact h.ha.h },
{ refl },
{ exact h.hb },
{ exact h.hc.h },
end

/--
  The action on quadratic forms as matrices is conjugation.
-/
def matrix_action_matrix (M N : M₂ℤ) : M₂ℤ := M.transpose * (N * M)

/--
  Conjugation preserves the precondition of `of_matrix`.

  That is, matrices that result from a triple `⟨a, b, c⟩ : quadratic_form`
  will also correspond to a triple after applying the matrix action.
  We will prove later on that the action on triples and the action on matrices are the same.
-/
lemma of_matrix_pre_action (M N : M₂ℤ) (h : of_matrix_pre N) : of_matrix_pre (matrix_action_matrix M N) := begin
  cases h,
  split,
  { suffices : even ((N 1 1 * M 1 0 + 2 * M 0 0 * N 1 0) * M 1 0 + N 0 0 * M 0 0 ^ 2),
    { simp [matrix_action_matrix, h_hb], ring, assumption },
    apply even_add_even; apply even_mul,
    { apply even_add_even; apply even_mul, assumption, exact even_mul _ _ even_2 }, 
    assumption
    },
  { simp [matrix_action_matrix, h_hb], ring },
  { suffices : even ((N 1 1 * M 1 1 + 2 * M 0 1 * N 1 0) * M 1 1 + N 0 0 * M 0 1 ^ 2),
    { simp [matrix_action_matrix, h_hb], ring, assumption },
    apply even_add_even; apply even_mul,
    { apply even_add_even; apply even_mul, assumption, exact even_mul _ _ even_2 },
    { assumption },
  }
end

/-- Or we can view the action of `M` as multiplying the input with `M`. -/
@[simp] lemma eval_matrix_action (M N : M₂ℤ) (xy : fin 2 → ℤ) :
  eval_matrix (matrix_action_matrix M N) xy = eval_matrix N (matrix.mul_vec M xy) :=
calc eval_matrix (matrix_action_matrix M N) xy
    = matrix.mul (matrix.row xy) (matrix.mul (matrix.mul M.transpose (matrix.mul N M)) (matrix.col xy)) () () : refl _
... = matrix.mul (matrix.mul (matrix.row xy) M.transpose) (matrix.mul N (matrix.mul M (matrix.col xy))) () () : by repeat { rw [matrix.mul_assoc] }
... = matrix.mul ((matrix.mul M (matrix.col xy)).transpose) (matrix.mul N (matrix.mul M (matrix.col xy))) () () : by simp
... = eval_matrix N (matrix.mul_vec M xy) : by simp [row_mul_vec, col_mul_vec, eval_matrix]

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
  { calc matrix.mul_vec M (vector.nth (x :: y :: vector.nil)) 0
        = M 0 0 * x + M 0 1 * vector.nth (x :: y :: vector.nil) 1 : by simp [matrix.mul_vec]
    ... = vector.nth ((M 0 0 * x + M 0 1 * y) :: (M 1 0 * x + M 1 1 * y) :: vector.nil) 0 : rfl },
  { calc matrix.mul_vec M (vector.nth (x :: y :: vector.nil)) 1
      = M 1 0 * x + M 1 1 * vector.nth (x :: y :: vector.nil) 1 : by simp [matrix.mul_vec]
    ... = vector.nth ((M 0 0 * x + M 0 1 * y) :: (M 1 0 * x + M 1 1 * y) :: vector.nil) 1 : rfl }
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
theorem det_invariant_for_SL (f : quadratic_form) (M : SL₂ℤ) : (M.1 · f).discr = f.discr :=
begin
  rw [←discr_eq_discr_matrix, ←discr_eq_discr_matrix, ←matrix_action_to_matrix],
  unfold matrix_action_matrix discr_matrix,
  rw [matrix.det_mul, matrix.det_mul, M.2, matrix.det_transpose, M.2],
  simp
end

end matrix_action

end quadratic_form

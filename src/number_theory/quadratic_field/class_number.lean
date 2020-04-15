import data.int.gcd
import data.zsqrtd.basic
import data.matrix.notation
import group_theory.group_action
import group_theory.quotient_group
import linear_algebra.special_linear_group
import number_theory.class_group
import order.lexicographic
import tactic.fin_cases
import tactic.linarith

/-! Computing the class number for quadratic number fields -/

universes u v

open_locale matrix
open finset
open matrix

section to_other_files

@[simp] lemma fin.one {n : ℕ} : (fin.succ 0 : fin n.succ.succ) = 1 := rfl
lemma fin.one_of_two : (fin.succ 0 : fin 2) = 1 := rfl
@[simp] lemma fin.default_one : (default (fin 1)) = 0 := rfl

@[simp]
lemma int.coe_nat_abs_eq_abs {a : ℤ} : (a.nat_abs : ℤ) = abs a :=
by rw [int.abs_eq_nat_abs]

@[simp]
lemma int.nat_abs_eq_iff_abs_eq {a : ℤ} {b : ℕ} : a.nat_abs = b ↔ abs a = b :=
by rw [int.abs_eq_nat_abs, int.coe_nat_inj']

@[simp]
lemma int.eq_nat_abs_iff_eq_abs {a : ℕ} {b : ℤ} : a = b.nat_abs ↔ (a : ℤ) = abs b :=
by rw [int.abs_eq_nat_abs, int.coe_nat_inj']

@[simp]
lemma int.nat_abs_le_iff_abs_le {a : ℤ} {b : ℕ} : a.nat_abs ≤ b ↔ abs a ≤ b :=
by rw [int.abs_eq_nat_abs, int.coe_nat_le]

@[simp]
lemma int.le_nat_abs_iff_le_abs {a : ℕ} {b : ℤ} : a ≤ b.nat_abs ↔ (a : ℤ) ≤ abs b :=
by rw [int.abs_eq_nat_abs, int.coe_nat_le]

@[simp]
lemma int.nat_abs_lt_iff_abs_lt {a : ℤ} {b : ℕ} : a.nat_abs < b ↔ abs a < b :=
by rw [int.abs_eq_nat_abs, int.coe_nat_lt]

@[simp]
lemma int.le_nat_abs_iff_lt_abs {a : ℕ} {b : ℤ} : a < b.nat_abs ↔ (a : ℤ) < abs b :=
by rw [int.abs_eq_nat_abs, int.coe_nat_lt]

lemma int.nat_abs_of_pos {a : ℤ} (ha : 0 < a) : (↑(a.nat_abs) : ℤ) = a :=
int.nat_abs_of_nonneg (le_of_lt ha)

lemma int.pos_iff_ge_one : ∀ {a : ℤ}, 0 < a ↔ 1 ≤ a
| 0 := by split; intro ha; linarith
| (nat.succ n) := by split; intro ha; linarith
| -[1+ n ] := by split; intro ha; linarith

@[simp] lemma int.units_abs (u : units ℤ) : abs (u : ℤ) = (1 : ℤ) :=
int.nat_abs_eq_iff_abs_eq.mp (int.units_nat_abs u)

lemma le_of_add_le_of_nonneg_left {a b c : ℤ} (ha : 0 ≤ a) (h : a + b ≤ c) : b ≤ c :=
le_trans (le_add_of_nonneg_left' ha) h

lemma le_of_add_le_of_nonneg_right {a b c : ℤ} (hb : 0 ≤ b) (h : a + b ≤ c) : a ≤ c :=
le_trans (le_add_of_nonneg_right hb) h

lemma int.abs_mul_lt_abs_self {a b : ℤ} (h : abs (a * b) < abs b) : a = 0 :=
have h : abs a * abs b < abs b := by rwa [←abs_mul],
if h' : b = 0
then absurd (by simp [h']) (not_le_of_gt h)
else have _ := (mul_lt_iff_lt_one_left (abs_pos_iff.mpr h')).mp h,
  abs_eq_zero.mp (le_antisymm (le_of_not_gt (mt int.pos_iff_ge_one.mpr (not_le_of_gt this))) (abs_nonneg a))

end to_other_files

/-- We represent a quadratic form in `n` variables with a symmetric `n` by `n` matrix.

  The evaluation map for a form `M` sends a vector `x` to `xᵀ ⬝ M ⬝ x`.
-/
def quadratic_form (n : Type u) [fintype n] (α : Type v) := {M : matrix n n α // Mᵀ = M }

-- Shorter notation for the case with 2 variables and integer coefficients.
notation `M₂ℤ` := matrix (fin 2) (fin 2) ℤ
notation `SL₂ℤ` := matrix.special_linear_group (fin 2) ℤ
notation `QF₂ℤ` := quadratic_form (fin 2) ℤ

namespace quadratic_form
variables {n : Type u} [fintype n] {α : Type v}

def mk (M : matrix n n α) (hM : Mᵀ = M) : quadratic_form n α := ⟨M, hM⟩

def from_tuple (a b c : α) : quadratic_form (fin 2) α :=
⟨![ ![ a, b ], ![ b, c ] ], by { ext i j, fin_cases i; fin_cases j; refl }⟩

instance : has_coe_to_fun (quadratic_form n α) :=
⟨ λ _, n → n → α,
  λ M, M.1 ⟩

@[simp] lemma coe_fn_mk (M : matrix n n α) (hM : Mᵀ = M) :
  ⇑(mk M hM) = M :=
rfl

lemma coe_fn_symmetric (M : quadratic_form n α) (i j : n) : M i j = M j i :=
show Mᵀ j i = M j i, by { erw M.2, refl }

@[simp] lemma transpose_coe_fn (M : quadratic_form n α) : (⇑ M)ᵀ = M := M.2

@[ext]
lemma ext : Π (M N : quadratic_form n α), (∀ i j, M i j = N i j) → M = N :=
λ ⟨M, _⟩ ⟨N, _⟩ h, by { congr, ext, apply h }

@[simp] lemma mk_coe_fn (M : quadratic_form n α) (hM : (⇑M : matrix n n α)ᵀ = ⇑M) : mk (⇑M) hM = M :=
by { ext, refl }

/-- A primitive quadratic form has no common divisor among its coefficients. -/
def is_primitive [gcd_domain α] (M : quadratic_form n α) : Prop :=
(univ : finset (n × n)).fold gcd (1 : α) (λ ⟨i, j⟩, M i j) = 1

section eval
/--
  Evaluate the quadratic form as a function.

  This evaluation function is defined for all α for which the expression
  `ax^2 + bxy + ... + cy^2` makes sense.
-/
def eval [add_comm_monoid α] [has_mul α] (M : quadratic_form n α) (x : n → α) : α :=
(row x ⬝ M ⬝ col x) ⟨⟩ ⟨⟩

lemma eval_val [semiring α] {M : quadratic_form n α} {x : n → α} :
  eval M x = univ.sum (λ i : n, univ.sum (λ j : n, x j * M i j * x i)) :=
calc eval M x = univ.sum (λ i : n, (univ.sum (λ j : n, x j * M j i) * x i)) : rfl
          ... = univ.sum (λ i : n, univ.sum (λ j : n, x j * M i j * x i)) :
  by simp_rw [sum_mul, coe_fn_symmetric]

lemma eval_basis [semiring α] [decidable_eq n] (M : quadratic_form n α) (i : n) :
  eval M (λ j, if i = j then 1 else 0) = M i i :=
calc eval M (λ j, if i = j then 1 else 0)
    = finset.sum univ (λ i' : n, finset.sum univ (λ j : n, ite (i = i') (ite (i = j) (M i' j) 0) 0)) :
    by { simp [eval_val] }
... = finset.sum univ (λ i' : n, ite (i = i') (finset.sum univ (λ j : n, (ite (i = j) (M i' j) 0))) 0) :
    by { congr, ext i', split_ifs, { refl }, simp }
... = M i i : by simp

lemma eq_of_eval_eq_aux [semiring α] [decidable_eq n] (M : quadratic_form n α) {i j : n} (h : j ≠ i) :
  eval M (λ j', if i = j' ∨ j = j' then 1 else 0) = M i i + 2 * M i j + M j j :=
calc eval M (λ j', if i = j' ∨ j = j' then 1 else 0)
    = finset.sum univ (λ i' : n, finset.sum univ (λ j' : n, ite (i = i' ∨ j = i') (ite (i = j' ∨ j = j') (M i' j') 0) 0))
    : by simp [eval_val]
... = finset.sum univ (λ i' : n, ite (i = i' ∨ j = i') (finset.sum univ (λ j' : n, ite (i = j' ∨ j = j') (M i' j') 0)) 0)
    : by { congr, ext i', split_ifs, { refl }, simp }
... = finset.sum univ (λ (j' : n), ite (i = j' ∨ j = j') (M i j') 0) + finset.sum univ (λ (j' : n), ite (i = j' ∨ j = j') (M j j') 0)
    : by { erw [sum_ite _ _, filter_or, sum_union]; simp [filter_eq, h] }
... = M i i + M i j + M j i + M j j
    : by { erw [sum_ite _ _, sum_ite _ _, filter_or, sum_union, sum_union]; simp [filter_eq, h] }
... = M i i + 2 * M i j + M j j : by simp [two_mul, coe_fn_symmetric]

/-- Quadratic forms are defined uniquely by their evaluation. -/
lemma eq_of_eval_eq [ring α] [decidable_eq n] (M N : quadratic_form n α) (two_mul_cancel : ∀ x y : α, 2 * x = 2 * y → x = y) (h : ∀ x, eval M x = eval N x) : M = N :=
begin
  ext i j,
  have eq_ii : M i i = N i i := by rw [← eval_basis, ← eval_basis, h],
  have eq_jj : M j j = N j j := by rw [← eval_basis, ← eval_basis, h],
  by_cases hij : j = i,
  { rw [hij, eq_ii] },
  have eq' : M i i + 2 * M i j + M j j = N i i + 2 * N i j + N j j,
  { rw [← eq_of_eval_eq_aux M hij, ← eq_of_eval_eq_aux N hij, h] },
  rw [eq_ii, eq_jj] at eq',
  apply two_mul_cancel,
  apply add_left_cancel,
  apply add_right_cancel,
  exact eq'
end
end eval

section matrix_action

-- We need a `comm_ring` to make `M • f` symmetric.
variables [comm_ring α]

/--
  Matrices have an action on quadratic forms by multiplication on the input.

  For example, `f(x, y)` is mapped to `f(αx + βy, γx + δy)` by the matrix `((α β) (γ δ)).`
-/
instance : has_scalar (matrix n n α) (quadratic_form n α) :=
⟨ λ M N, mk (M ⬝ N ⬝ Mᵀ) (by simp [matrix.mul_assoc, transpose_coe_fn]) ⟩

lemma coe_fn_smul (M : matrix n n α) (f : quadratic_form n α) :
  ⇑(M • f) = M ⬝ f ⬝ Mᵀ
:= rfl

@[simp]
lemma neg_action (M : matrix n n α) (f : quadratic_form n α) : -M • f = M • f :=
by { ext, simp [coe_fn_smul] }

/--
  The action works by multiplying vectors with the matrix.
-/
@[simp] lemma eval_smul (M : matrix n n α) (f : quadratic_form n α) (x : n → α) :
  eval (M • f) x = eval f (M.vec_mul x) :=
by simp [eval, coe_fn_smul, row_vec_mul, col_vec_mul, matrix.mul_assoc]

instance [decidable_eq n] : mul_action (matrix n n α) (quadratic_form n α) :=
{ mul_smul := λ M N f, by { ext, simp [coe_fn_smul, matrix.mul_assoc] },
  one_smul := λ f, by { ext, simp },
  ..quadratic_form.has_scalar }

end matrix_action

section discr

variables [comm_ring α] [decidable_eq n]

/--
  The discriminant of a matrix representation is given by its determinant.
-/
def discr (M : quadratic_form n α) : α := matrix.det M

/--
  Matrices with determinant = 1 preserve the discriminant of a quadratic form.
-/
theorem discr_invariant_for_SL (f : quadratic_form n α) (M : special_linear_group n α) :
  discr (M.1 • f) = f.discr :=
by simp [coe_fn_smul, discr, M.2]

end discr

section dim_2
/-! Specialized lemmas for forms in two variables. -/

@[simp] lemma val_0_1 (f : QF₂ℤ) : f 0 1 = f 1 0 := coe_fn_symmetric f 0 1

@[simp] lemma smul_val_0_0 (M : M₂ℤ) (f : QF₂ℤ) :
  (M • f) 0 0 = f 0 0 * (M 0 0)^2 + 2 * f 1 0 * M 0 0 * M 0 1 + f 1 1 * (M 0 1)^2 :=
by { simp [coe_fn_smul, mul_val], ring }

@[simp] lemma smul_val_1_0 (M : M₂ℤ) (f : QF₂ℤ) :
  (M • f) 1 0 = (M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 0 0 + (M 1 0 * f 1 0 + M 1 1 * f 1 1) * M 0 1 :=
by { simp [coe_fn_smul, mul_val] }

@[simp] lemma smul_val_1_1 (M : M₂ℤ) (f : QF₂ℤ) :
  (M • f) 1 1 = f 0 0 * (M 1 0)^2 + 2 * f 1 0 * M 1 0 * M 1 1 + f 1 1 * (M 1 1)^2 :=
by { simp [coe_fn_smul, mul_val], ring }

end dim_2

-- TODO: better name!
def QF (d : ℤ) := {f : QF₂ℤ // f.discr = d}

namespace QF

variable {d : ℤ}

instance : has_coe (QF d) QF₂ℤ := ⟨ λ f, f.1 ⟩

instance : has_coe_to_fun (QF d) := ⟨ λ f, fin 2 → fin 2 → ℤ, λ f, f.1 ⟩

@[simp] lemma coe_fn_val (f : QF d) : ⇑f.val = ⇑f := rfl

@[simp] lemma coe_fn_coe (f : QF d) : ⇑(f : QF₂ℤ) = @coe_fn _ (QF.has_coe_to_fun) f := rfl

@[ext]
lemma ext {f g : QF d} (h : ∀ i j, f i j = g i j) : f = g :=
begin
  cases f,
  cases g,
  congr,
  ext,
  apply h
end

instance : has_scalar SL₂ℤ (QF d) :=
⟨λ M f, ⟨M.1 • f.1, trans (discr_invariant_for_SL f.1 M) f.2⟩⟩

lemma smul_def (M : SL₂ℤ) (f : QF d) :
  M • f = ⟨M.1 • f.1, trans (discr_invariant_for_SL f.1 M) f.2⟩ := rfl

@[simp] lemma coe_smul (M : SL₂ℤ) (f : QF d) :
  ↑(M • f) = (↑M : matrix (fin 2) (fin 2) ℤ) • (f : quadratic_form (fin 2) ℤ) := rfl

@[simp] lemma coe_fn_smul (M : SL₂ℤ) (f : QF d) :
  ⇑(M • f) = @has_scalar.smul _ _ quadratic_form.has_scalar M f := rfl

lemma coe_fn_symmetric (f : QF d) (i j : fin 2) : f i j = f j i := coe_fn_symmetric f i j

instance : mul_action SL₂ℤ (QF d) :=
⟨ λ f, by { ext, simp [quadratic_form.coe_fn_smul] },
  λ M N f, by { ext, simp [quadratic_form.coe_fn_smul, matrix.mul_assoc] } ⟩

instance : setoid (QF d) := mul_action.orbit_rel SL₂ℤ (QF d)

end QF

section class_number
variable {d : ℤ}

-- TODO: better name!
def Γ_infinity : set SL₂ℤ := { M | ∃ m, M 0 0 = 1 ∧ M 0 1 = m ∧ M 1 0 = 0 ∧ M 1 1 = 1 }

instance : is_submonoid Γ_infinity :=
⟨⟨0, by finish⟩, λ a b ⟨ma, ha⟩ ⟨mb, hb⟩, ⟨ma + mb, by { simp [matrix.mul_val, ha, hb, add_comm] } ⟩⟩
instance : is_subgroup Γ_infinity :=
⟨λ a ⟨ma, ha⟩, ⟨-ma, by { simp [adjugate_2x2, ha] } ⟩⟩

instance subset_has_scalar {α β} [has_scalar α β] (s : set α) : has_scalar s β := ⟨λ s b, s.1 • b⟩
def submonoid_mul_action {α β} [monoid α] [mul_action α β] (s : set α) [is_submonoid s] : mul_action s β :=
⟨one_smul α, λ x y, @_root_.mul_smul α _ _ _ x.1 y.1⟩

/-- Quadratic forms are considered equivalent if they share the same orbit modulo Γ_infinity. -/
def quadratic_class_group (d : ℤ) : Type :=
quotient (@mul_action.orbit_rel Γ_infinity (QF d) _ (submonoid_mul_action _))

end class_number

def is_positive_definite [ordered_semiring α] (f : quadratic_form n α) : Prop := ∀ x ≠ 0, 0 < eval f x

section is_positive_definite

variables [decidable_eq n] [linear_ordered_comm_ring α] {f g : quadratic_form n α}

lemma is_positive_definite.diagonal_pos (hpd : is_positive_definite f) (i : n) : 0 < f i i :=
begin
  convert hpd (λ j, if i = j then 1 else 0) _,
  { exact (eval_basis f i).symm },
  intro eq_0,
  simpa using congr_fun eq_0 i
end

lemma pos_def_smul_SL (M : special_linear_group n α) (h : is_positive_definite f) :
  is_positive_definite (M.val • f) :=
λ x hx, by simpa using h _ (λ he, hx (special_linear_group.vec_mul_injective (trans he (vec_mul_zero M).symm)))
end is_positive_definite

/-- A bundled version of `positive definite quadratic form with discriminant d'. -/
structure pos_def_QF₂ℤ (d : ℤ) :=
(form : QF₂ℤ)
(discr_eq : discr form = d)
(pos_def : is_positive_definite form)

variable {d : ℤ}

namespace pos_def_QF₂ℤ

instance : has_coe (pos_def_QF₂ℤ d) QF₂ℤ :=
⟨ λ f, f.form ⟩

instance : has_coe_to_fun (pos_def_QF₂ℤ d) :=
{ F := λ f, fin 2 → fin 2 → ℤ,
  coe := λ f, f.form }

@[ext]
lemma ext : Π (f g : pos_def_QF₂ℤ d), (∀ i j, f i j = g i j) → f = g :=
λ ⟨f, _, _⟩ ⟨g, _, _⟩ h, by { congr, ext, apply h }

instance : has_scalar SL₂ℤ (pos_def_QF₂ℤ d) :=
⟨ λ M f,
  ⟨ M.val • f.form,
    trans (discr_invariant_for_SL f.form M) f.discr_eq,
    pos_def_smul_SL M f.pos_def ⟩ ⟩

@[simp] lemma val_0_1 (f : pos_def_QF₂ℤ d) : f 0 1 = f 1 0 := coe_fn_symmetric f 0 1

@[simp] lemma coe_fn_coe (f : pos_def_QF₂ℤ d) : ⇑(f : QF₂ℤ) = f := rfl

@[simp] lemma coe_fn_smul (f : pos_def_QF₂ℤ d) (M : SL₂ℤ) :
  ⇑ (M • f) = @has_scalar.smul M₂ℤ QF₂ℤ _ M f := rfl

instance : mul_action SL₂ℤ (pos_def_QF₂ℤ d) :=
{ one_smul := λ f, by { ext, simp [quadratic_form.coe_fn_smul] },
  mul_smul := λ M N f, by { ext, simp [quadratic_form.coe_fn_smul, matrix.mul_assoc] },
  .. pos_def_QF₂ℤ.has_scalar }

instance : setoid (pos_def_QF₂ℤ d) :=
mul_action.orbit_rel SL₂ℤ (pos_def_QF₂ℤ d)

end pos_def_QF₂ℤ

structure is_reduced (f : pos_def_QF₂ℤ d) : Prop :=
(two_abs_b_le_a : 2 * abs (f 1 0) ≤ f 0 0)
(a_le_c : f 0 0 ≤ f 1 1)
(b_nonneg_left : 2 * abs (f 1 0) = f 0 0 → 0 ≤ f 1 0)
(b_nonneg_right : f 0 0 = f 1 1 → 0 ≤ f 1 0)

lemma is_reduced.two_b_eq_a_of_c_le_two_abs_b {f : pos_def_QF₂ℤ d} (hr : is_reduced f)
  (h : f 1 1 ≤ 2 * abs (f 1 0)) : 2 * f 1 0 = f 0 0 :=
have two_abs_b_eq : 2 * abs (f 1 0) = f 0 0 := le_antisymm hr.1 (le_trans hr.a_le_c h),
by simpa [abs_of_nonneg (hr.3 two_abs_b_eq)] using two_abs_b_eq

lemma is_reduced.abs_b_le_a {f : pos_def_QF₂ℤ d} (h : is_reduced f) : abs (f 1 0) ≤ f 0 0 :=
calc abs (f 1 0) = 1 * abs (f 1 0) : (one_mul _).symm
             ... ≤ 2 * abs (f 1 0) : mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
             ... ≤ f 0 0 : h.1

namespace reduced
/-! This namespace contains an order on quadratic forms, such that the minimum is a reduced form.

The proof that this minimum is a reduced form is done later.
-/

/-- Map the sign of an int to `fin 3` to order them with positive as the least, then zero, then negative. -/
def sign' : ℤ → fin 3
| (nat.succ n) := 0
| 0            := 1
| -[1+ n]      := 2

@[simp] lemma sign'_nat_add_one {n : ℕ} : sign' (↑n + 1) = 0 := rfl

lemma sign'_iff_zero : Π {a : ℤ}, sign' a = 1 ↔ a = 0
| (nat.succ n) := dec_trivial
| 0            := dec_trivial
| -[1+ n]      := dec_trivial

lemma sign'_iff_pos : Π {a : ℤ}, sign' a = 0 ↔ 0 < a
| (nat.succ n) := by { norm_cast, exact dec_trivial }
| 0            := dec_trivial
| -[1+ n]      := dec_trivial

lemma sign'_iff_nonneg : Π {a : ℤ}, sign' a ≤ 1 ↔ 0 ≤ a
| (nat.succ n) := dec_trivial
| 0            := dec_trivial
| -[1+ n]      := dec_trivial

lemma sign'_gt_zero : Π {a : ℤ}, 0 < sign' a ↔ a ≤ 0
| (nat.succ n) := dec_trivial
| 0            := dec_trivial
| -[1+ n]      := dec_trivial

lemma sign'_iff_nonpos : Π {a : ℤ}, 1 ≤ sign' a ↔ a ≤ 0
| (nat.succ n) := dec_trivial
| 0            := dec_trivial
| -[1+ n]      := dec_trivial

lemma sign'_iff_neg : Π {a : ℤ}, sign' a = 2 ↔ a < 0
| (nat.succ n) := dec_trivial
| 0            := dec_trivial
| -[1+ n]      := sorry -- TODO: should be automatic, no?

lemma sign'_lt_sign'_neg_self : Π {a : ℤ}, sign' a < sign' (-a) ↔ 0 < a
| (n+1:ℕ) := by { norm_cast, exact dec_trivial }
| 0       := dec_trivial
| -[1+ n] := dec_trivial

lemma sign'_neg_lt_sign'_self : Π {a : ℤ}, sign' (-a) < sign' a ↔ a < 0
| (n+1:ℕ) := dec_trivial
| 0       := dec_trivial
| -[1+ n] := sorry -- TODO: should be automatic, no?

-- TODO:
lemma sign'_lt_iff : Π {a b : ℤ}, sign' a < sign' b ↔ (0 < a ∧ b ≤ 0) ∨ (a = 0 ∧ b < 0) := sorry

lemma sign'_lt_iff_of_abs_eq {a b : ℤ} (hab : abs a = abs b) : sign' a < sign' b ↔ (b < 0 ∧ 0 < a) :=
iff.trans sign'_lt_iff
  ⟨ λ h, h.elim
    (λ ⟨ha, hb⟩, ⟨lt_of_le_of_ne hb (mt (eq.symm ∘ abs_eq_zero.mp ∘ trans hab ∘ abs_eq_zero.mpr) (ne_of_lt ha)), ha⟩)
    (λ ⟨ha, hb⟩, absurd ha (mt (abs_eq_zero.mp ∘ trans hab.symm ∘ abs_eq_zero.mpr) (ne_of_lt hb))),
    λ ⟨hb, ha⟩, or.inl ⟨ha, le_of_lt hb⟩ ⟩

def sign'_to_sign : fin 3 → ℤ
| ⟨0, _⟩ := 1
| ⟨1, _⟩ := 0
| _ := -1

@[simp]
lemma sign'_to_sign_of_sign' : ∀ a, sign'_to_sign (sign' a) = a.sign
| (n+1:ℕ) := rfl
| 0       := rfl
| -[1+ n] := rfl

/-- An embedding of quadratic forms into a well-founded order, such that reduced forms are minimal. -/
def key (f : pos_def_QF₂ℤ d) : lex ℕ (lex ℕ (lex (fin 3) ℕ)) :=
⟨(f 0 0).nat_abs, (f 1 0).nat_abs, sign' (f 1 0), (f 1 1).nat_abs⟩

lemma a_from_key (f : pos_def_QF₂ℤ d) : ↑(key f).fst = f 0 0 :=
int.nat_abs_of_pos (f.pos_def.diagonal_pos 0)

lemma abs_b_from_key (f : pos_def_QF₂ℤ d) : ↑(key f).snd.fst = abs (f 1 0) :=
int.coe_nat_abs_eq_abs

lemma sign_b_from_key (f : pos_def_QF₂ℤ d) : (key f).snd.snd.fst = sign' (f 1 0) :=
rfl

lemma b_from_key (f : pos_def_QF₂ℤ d) : sign'_to_sign (key f).snd.snd.fst * ↑(key f).snd.fst = f 1 0 :=
by { convert int.sign_mul_nat_abs (f 1 0), apply sign'_to_sign_of_sign' }

lemma c_from_key (f : pos_def_QF₂ℤ d) :
  ↑(key f).snd.snd.snd = f 1 1 :=
int.nat_abs_of_pos (f.pos_def.diagonal_pos 1)

lemma key_injective : function.injective (@key d) :=
begin
  intros f g h,
  ext,
  fin_cases i; fin_cases j,
  { rw [← a_from_key f, h, a_from_key g] },
  { rw [f.val_0_1, g.val_0_1, ← b_from_key f, h, b_from_key g] },
  { rw [← b_from_key f, h, b_from_key g] },
  { rw [← c_from_key f, h, c_from_key g] },
end

/-- An order of quadratic forms, such that reduced forms are minimal. -/
instance : has_lt (pos_def_QF₂ℤ d) :=
⟨function.on_fun (<) key⟩

/-- The `key` gives an order embedding from orbits to the well-order `ℕ × ℕ × fin 3 × ℕ`. -/
def orbit_embedding (f : pos_def_QF₂ℤ d) :
  order_embedding (subrel (<) (mul_action.orbit SL₂ℤ f)) ((<) : _ → lex ℕ (lex ℕ (lex (fin 3) ℕ)) → Prop) :=
{ to_fun := λ f, key f.1,
  inj := λ ⟨g, hg⟩ ⟨g', hg'⟩ h,
    by { congr,
         exact key_injective h },
  ord := λ _ _, iff.rfl }

/-- The order on quadratic forms is well-founded on these orbits. -/
instance (f : pos_def_QF₂ℤ d) : is_well_order _ (subrel (<) (mul_action.orbit SL₂ℤ f)) :=
@order_embedding.is_well_order _ _ _ _ (orbit_embedding f)
  (@prod.lex.is_well_order _ _ _ _ _
    (@prod.lex.is_well_order _ _ _ _ _
      (@prod.lex.is_well_order _ _ _ _ _ _)))

lemma lt_iff {f g : pos_def_QF₂ℤ d} :
  f < g ↔ f 0 0 < g 0 0 ∨
    (f 0 0 = g 0 0 ∧ (abs (f 1 0) < abs (g 1 0) ∨
      (abs (f 1 0) = abs (g 1 0) ∧ (sign' (f 1 0) < sign' (g 1 0) ∨
        (sign' (f 1 0) = sign' (g 1 0) ∧ f 1 1 < g 1 1))))) :=
begin
  refine iff.trans (prod.lex_def _ _) (or_congr _ (and_congr _ _)),
  { exact iff.trans int.coe_nat_lt.symm (by rw [a_from_key f, a_from_key g]) },
  { refine (iff.trans (function.injective.eq_iff @int.coe_nat_inj).symm _),
    rw [a_from_key f, a_from_key g] },
  refine iff.trans (prod.lex_def _ _) (or_congr _ (and_congr _ _)),
  { rw [←int.coe_nat_lt, abs_b_from_key f, abs_b_from_key g] },
  { rw [←int.coe_nat_inj', abs_b_from_key f, abs_b_from_key g] },
  refine iff.trans (prod.lex_def _ _) (or_congr (iff.refl _) (and_congr (iff.refl _) _)),
  apply iff.trans int.coe_nat_lt.symm,
  rw [c_from_key f, c_from_key g]
end

lemma a_le_of_lt {f g : pos_def_QF₂ℤ d} (h : f < g):
  f 0 0 ≤ g 0 0 :=
begin
  rcases lt_iff.mp h with ha | ⟨ha, _⟩,
  { exact le_of_lt ha },
  { exact le_of_eq ha }
end

lemma a_val_le_of_smul_lt {f : pos_def_QF₂ℤ d} {M : SL₂ℤ} (h : M • f < f):
  f 0 0 * (M 0 0)^2 + 2 * f 1 0 * M 0 0 * M 0 1 + f 1 1 * (M 0 1)^2 ≤ f 0 0 :=
by { simpa using a_le_of_lt h }

lemma not_lt_of_a_gt {f g : pos_def_QF₂ℤ d} (ha : f 0 0 < g 0 0) :
  ¬ g < f :=
λ h, not_lt_of_ge (a_le_of_lt h) ha

end reduced

section minimal

/-- A form is minimal if there is no smaller form in its orbit. -/
def minimal (f : pos_def_QF₂ℤ d) : Prop :=
∀ (g : pos_def_QF₂ℤ d), g ≈ f → ¬g < f

lemma minimal_iff {f : pos_def_QF₂ℤ d} : minimal f ↔ ∀ (M : SL₂ℤ), ¬ M • f < f :=
⟨λ min M, min (M • f) ⟨M, rfl⟩, (by { rintros min' _ ⟨M, rfl⟩, apply min' })⟩

/-- The first half of the proof: each class has a unique minimal element.

  Next, we will show that a form is minimal iff it is reduced,
  to conclude that each class has a unique reduced element.
-/
lemma exists_unique_min (f : pos_def_QF₂ℤ d) :
  ∃! (g : pos_def_QF₂ℤ d), g ≈ f ∧ minimal g :=
let ⟨⟨g, g_mem⟩, _, min⟩ := well_founded.has_min (reduced.is_well_order f).wf set.univ
  (set.nonempty_of_mem (set.mem_univ ⟨f, setoid.refl f⟩)) in
⟨ g,
  ⟨g_mem, λ h h_mem, min ⟨h, setoid.trans h_mem g_mem⟩ (set.mem_univ _)⟩,
  λ g' ⟨g'_mem, g'_min⟩, let t := (reduced.is_well_order f).trichotomous in -- TODO: inlining t doesn't work
    match t ⟨g', g'_mem⟩ ⟨g, g_mem⟩ with
    | or.inl g'_lt_g := absurd g'_lt_g (min _ (set.mem_univ _))
    | or.inr (or.inl g'_eq_g) := congr_arg subtype.val g'_eq_g
    | or.inr (or.inr g_lt_g') := absurd g_lt_g' (g'_min _ (setoid.trans g_mem (setoid.symm g'_mem)))
    end⟩

end minimal

/-- `swap_x_y` is a matrix whose action swaps the coefficient for `x²` and `y²` -/
def swap_x_y : SL₂ℤ := ⟨![![0, -1], ![1, 0]], rfl⟩

@[simp]
lemma coe_fn_swap : ⇑(swap_x_y) = ![![0, -1], ![1, 0]] := rfl

lemma swap_x_y_smul (f : pos_def_QF₂ℤ d) :
  ⇑(swap_x_y • f) = ![![0, -1], ![1, 0]] ⬝ f ⬝ ![![0, 1], ![-1, 0]] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma swap_x_y_smul_0_0 (f : pos_def_QF₂ℤ d) : (swap_x_y • f) 0 0 = f 1 1 :=
by simp [swap_x_y_smul]

lemma swap_x_y_smul_1_0 (f : pos_def_QF₂ℤ d) : (swap_x_y • f) 1 0 = - f 1 0 :=
by simp [swap_x_y_smul, f.val_0_1]

lemma swap_x_y_lt {f : pos_def_QF₂ℤ d} (hc : 0 < f 1 1) (h : f 1 1 < f 0 0) : (swap_x_y • f) < f :=
prod.lex.left _ _ (by simpa [abs_of_pos hc, abs_of_pos (lt_trans hc h), pow_two])

lemma swap_x_y_lt_of_eq_of_neg {f : pos_def_QF₂ℤ d} (hac : f 0 0 = f 1 1) (hb : f 1 0 < 0) : (swap_x_y • f) < f :=
reduced.lt_iff.mpr (or.inr
  ⟨ by rw [swap_x_y_smul_0_0, hac],
    or.inr
      ⟨ by rw [swap_x_y_smul_1_0, abs_neg],
        or.inl (by simpa using reduced.sign'_neg_lt_sign'_self.mpr hb)⟩⟩)

/-- `change_xy k` changes the coefficient for `xy` while keeping the coefficient for `x²` the same -/
def change_xy (k : ℤ) : SL₂ℤ := ⟨![![1, 0], ![k, 1]], by simp [det_2x2]⟩

lemma change_xy_smul (k : ℤ) (f : pos_def_QF₂ℤ d) :
  (⇑(change_xy k • f) : M₂ℤ) = ![![1, 0], ![k, 1]] ⬝ f ⬝ ![![1, k], ![0, 1]] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma change_xy_smul_0_0 (k : ℤ) (f : pos_def_QF₂ℤ d) :
  (change_xy k • f) 0 0 = f 0 0 :=
by { simp [change_xy_smul] }

lemma change_xy_smul_1_0 (k : ℤ) (f : pos_def_QF₂ℤ d) :
  (change_xy k • f) 1 0 = k * f 0 0 + f 1 0 :=
by { simp [change_xy_smul] }

lemma change_xy_smul_1_1 (k : ℤ) (f : pos_def_QF₂ℤ d) :
  (change_xy k • f) 1 1 = k^2 * f 0 0 + 2 * k * f 1 0 + f 1 1 :=
by { simp [change_xy_smul], ring }

lemma change_xy_lt_abs {f : pos_def_QF₂ℤ d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) < abs (f 1 0)) : (change_xy k • f) < f :=
reduced.lt_iff.mpr (or.inr
  ⟨ by rw [change_xy_smul_0_0 k f],
    or.inl (by rwa [change_xy_smul_1_0])⟩)

lemma change_xy_lt_sign {f : pos_def_QF₂ℤ d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) = abs (f 1 0)) (h2 : reduced.sign' (k * f 0 0 + f 1 0) < reduced.sign' (f 1 0)) : (change_xy k • f) < f :=
reduced.lt_iff.mpr (or.inr
  ⟨ by rw [change_xy_smul_0_0 k f],
    or.inr
      ⟨ by rwa [change_xy_smul_1_0],
        or.inl (by rwa [change_xy_smul_1_0]) ⟩ ⟩)

lemma a_le_c_of_min {f : pos_def_QF₂ℤ d} (min : minimal f) : f 0 0 ≤ f 1 1 :=
le_of_not_gt (λ c_lt_a, min (swap_x_y • f) ⟨_, rfl⟩ (swap_x_y_lt (f.pos_def.diagonal_pos 1) c_lt_a))

lemma b_le_a_of_min {f : pos_def_QF₂ℤ d} (min : minimal f) : 2 * abs (f 1 0) ≤ f 0 0 :=
begin
  have a_pos : 0 < f 0 0 := f.pos_def.diagonal_pos 0,
  apply le_of_not_gt,
  intro a_lt_b,
  rcases @trichotomous _ (<) _ 0 (f 1 0) with b_pos | b_zero | b_neg,
  { apply min (change_xy (-1) • f) ⟨_, rfl⟩,
    refine change_xy_lt_abs (abs_lt.mpr (and.intro _ _));
      rw [abs_of_pos b_pos] at *;
      linarith },
  { rw [←b_zero, abs_zero] at *, linarith },
  { apply min (change_xy 1 • f) ⟨_, rfl⟩,
    refine change_xy_lt_abs (abs_lt.mpr (and.intro _ _));
      rw [abs_of_neg b_neg] at *;
      linarith },
end

lemma abs_pow_two (a : ℤ) : (abs a)^2 = a^2 :=
begin
  by_cases a < 0,
  { rw abs_of_neg h, ring },
  { rw abs_of_nonneg (le_of_not_gt h) },
end

lemma min_of_reduced_aux_aux {a b c : ℤ} (m n : ℤ) (hba : 2 * abs b ≤ a) (hac : a ≤ c) :
  a * ((abs m - abs n)^2 + abs m * abs n) ≤ a * m^2 + 2 * b * m * n + c * n^2 :=
have abs_m_nonneg : _ := abs_nonneg m,
have abs_n_nonneg : _ := abs_nonneg n,
calc a * ((abs m - abs n)^2 + abs m * abs n) = a * (abs m)^2 - abs m * abs n * a + (abs n)^2 * a : by ring
   ... ≤ a * (abs m)^2 - abs m * abs n * (2 * abs b) + (abs n)^2 * c :
    add_le_add (sub_le_sub_left (mul_le_mul_of_nonneg_left hba (mul_nonneg (by linarith) abs_n_nonneg)) _)
      (mul_le_mul_of_nonneg_left hac (pow_two_nonneg _))
   ... = a * m^2 + -abs (2 * b * m * n) + c * n^2 : by { simp only [abs_mul, abs_pow_two], ring }
   ... ≤ a * m^2 + 2 * b * m * n + c * n^2 :
    add_le_add_right (add_le_add_left (neg_le.mp (neg_le_abs_self _)) _) _

lemma int.le_one_of_mul_le_one_of_pos_left {a b : ℤ} (hmul : a * b ≤ 1) (hpos : 0 < a) : b ≤ 1 :=
(mul_le_iff_le_one_right hpos).mp (le_trans hmul (int.pos_iff_ge_one.mp hpos))

lemma int.le_one_of_mul_le_one_of_pos_right {a b : ℤ} (hmul : a * b ≤ 1) (hpos : 0 < b) : a ≤ 1 :=
(mul_le_iff_le_one_left hpos).mp (le_trans hmul (int.pos_iff_ge_one.mp hpos))

lemma le_one_or_le_one_of_mul_le_one {a b : ℤ} : a * b ≤ 1 → a ≤ 1 ∨ b ≤ 1 :=
assume h, if h' : a ≤ 1 then or.inl h'
else or.inr ((mul_le_iff_le_one_right (lt_trans zero_lt_one (lt_of_not_ge h'))).mp (le_trans h (le_of_not_ge h')))

lemma le_one_of_pow_two_le_one {a : ℤ} (h : a ^ 2 ≤ 1) : a ≤ 1 :=
(le_one_or_le_one_of_mul_le_one h).elim (λ h, h) (λ (h : a^1 ≤ 1), by { convert h, simp })

lemma int.abs_eq_one_of_nonzero_of_le_one {a : ℤ} (nonzero : a ≠ 0) (le_one : abs a ≤ 1) : abs a = 1 :=
le_antisymm le_one (int.pos_iff_ge_one.mp (abs_pos_iff.mpr nonzero))

lemma abs_b_le_mul_a_add_b {a b k : ℤ} (h : 2 * abs b ≤ a) : abs b ≤ abs (k * a + b) :=
begin
  have : 0 ≤ abs b := abs_nonneg b,
  rcases @trichotomous _ (<) _ 0 k with k_pos | k_zero | k_neg,
  { refine le_max_iff.mpr (or.inl _),
    calc abs b = 1 * (2 * abs b) + - abs b : by ring
          ... ≤ 1 * (2 * abs b) + b : add_le_add_left (neg_le.mp (neg_le_abs_self _)) _
          ... ≤ k * a + b : add_le_add_right (mul_le_mul (int.pos_iff_ge_one.mp k_pos) h (by linarith) (le_of_lt k_pos)) _ },
    { simp [← k_zero] },
  { refine le_max_iff.mpr (or.inr _),
    have k_pos : 0 < -k := by linarith,
    calc abs b = 1 * (2 * abs b) + - abs b : by ring
          ... ≤ 1 * (2 * abs b) + - b : add_le_add_left (neg_le_neg (le_abs_self _)) _
          ... ≤ (-k) * a + - b :
          add_le_add_right (mul_le_mul (int.pos_iff_ge_one.mp k_pos) h (by linarith) (le_of_lt k_pos)) _
          ... = -(k * a + b) : by ring }
end

lemma abs_b_le_mul_a_sub_b {a b k : ℤ} (h : 2 * abs b ≤ a) : abs b ≤ abs (k * a - b) :=
by simpa using abs_b_le_mul_a_add_b (show 2 * abs (-b) ≤ a, by simpa)

lemma int.units_pow_two (a : units ℤ) : a^2 = 1 :=
calc a^2 = a * a : pow_two a
     ... = a * a⁻¹ : by rw [int.units_inv_eq_self]
     ... = 1 : mul_inv_self a

lemma int.coe_unit_pow_two (a : units ℤ) : (a : ℤ)^2 = 1 :=
by rw [←units.coe_pow, int.units_pow_two, units.coe_one]

@[simp] lemma zero_pow_two [semiring α] : (0 : α) ^ 2 = 0 := zero_mul _

lemma pow_two_pos {a : ℤ} (h : a ≠ 0) : 0 < a^2 :=
lt_of_le_of_ne (pow_two_nonneg a) (ne.symm (mt pow_eq_zero h))

lemma abs_m_eq_one_of_n_eq_zero {M : SL₂ℤ} (hn : M 0 1 = 0) : abs (M 0 0) = 1 :=
int.units_abs ⟨ M 0 0, M 1 1,
  by simp [←M.det_coe_fun, det_2x2, hn],
  by simp [←M.det_coe_fun, det_2x2, hn, mul_comm]⟩

lemma abs_n_eq_one_of_m_eq_zero {M : SL₂ℤ} (hm : M 0 0 = 0) : abs (M 0 1) = 1 :=
int.units_abs ⟨ M 0 1, -M 1 0,
  by simp [←M.det_coe_fun, det_2x2, hm],
  by simp [←M.det_coe_fun, det_2x2, hm, mul_comm]⟩

lemma abs_o_eq_one_of_m_eq_zero {M : SL₂ℤ} (hm : M 0 0 = 0) : abs (M 1 0) = 1 :=
int.units_abs ⟨ M 1 0, - M 0 1,
  by simp [←M.det_coe_fun, det_2x2, hm, mul_comm],
  by simp [←M.det_coe_fun, det_2x2, hm]⟩

lemma abs_p_eq_one_of_n_eq_zero {M : SL₂ℤ} (hn : M 0 1 = 0) : abs (M 1 1) = 1 :=
int.units_abs ⟨ M 1 1, M 0 0,
  by simp [←M.det_coe_fun, det_2x2, hn, mul_comm],
  by simp [←M.det_coe_fun, det_2x2, hn]⟩

lemma n_nonzero_of_m_eq_zero {M : SL₂ℤ} (hm : M 0 0 = 0) : M 0 1 ≠ 0 :=
λ h, one_ne_zero (trans (abs_n_eq_one_of_m_eq_zero hm).symm (abs_eq_zero.mpr h))

lemma sub_pow_two_add_mul_pos {m n : ℤ} (hmn : ¬ (m = 0 ∧ n = 0)) : 0 < (abs m - abs n)^2 + abs m * abs n :=
begin
  by_cases hm : m = 0; by_cases hn : n = 0,
  { tauto },
  { simpa [hm, hn] using pow_two_pos (mt abs_eq_zero.mp hn) },
  { simpa [hm, hn] using pow_two_pos (mt abs_eq_zero.mp hm) },
  { apply add_pos_of_nonneg_of_pos (pow_two_nonneg _),
    apply mul_pos (abs_pos_iff.mpr hm) (abs_pos_iff.mpr hn) }
end

lemma a_le_a_smul_of_reduced {f : pos_def_QF₂ℤ d} (hr : is_reduced f) (M : SL₂ℤ) :
  f 0 0 ≤ (M • f) 0 0 :=
begin
  simp only [f.coe_fn_smul, f.coe_fn_coe, smul_val_0_0],
  apply le_trans _ (min_of_reduced_aux_aux (M 0 0) (M 0 1) hr.1 hr.2),
  apply (le_mul_iff_one_le_right (f.pos_def.diagonal_pos 0)).mpr,
  apply int.pos_iff_ge_one.mp,
  apply sub_pow_two_add_mul_pos,
  rintro ⟨hm, hn⟩,
  simpa [det_2x2, hm, hn] using M.det_coe_fun
end

lemma abs_m_le_one_aux {f : pos_def_QF₂ℤ d} (hr : is_reduced f) (M : SL₂ℤ)
  (lt : M • f < f) : (abs (M 0 0) - abs (M 0 1))^2 + abs (M 0 0) * abs (M 0 1) ≤ 1 :=
(mul_le_iff_le_one_right (f.pos_def.diagonal_pos 0)).mp (le_trans
  (min_of_reduced_aux_aux (M 0 0) (M 0 1) hr.1 hr.2)
  (by simpa using reduced.a_le_of_lt lt))

lemma abs_m_le_one {f : pos_def_QF₂ℤ d} (hr : is_reduced f) {M : SL₂ℤ} (lt : M • f < f) :
  abs (M 0 0) ≤ 1 :=
if hm : M 0 0 = 0 then by simp [hm]
else if hn : M 0 1 = 0 then le_one_of_pow_two_le_one (by simpa [hn] using abs_m_le_one_aux hr M lt)
else calc abs (M 0 0) ≤ abs (M 0 0) * abs (M 0 1) :
  (le_mul_iff_one_le_right (abs_pos_iff.mpr hm)).mpr (int.pos_iff_ge_one.mp (abs_pos_iff.mpr hn))
                  ... ≤ (abs (M 0 0) - abs (M 0 1))^2 + abs (M 0 0) * abs (M 0 1) :
  le_add_of_nonneg_left' (pow_two_nonneg _)
                  ... ≤ 1 : abs_m_le_one_aux hr M lt

lemma abs_n_le_one {f : pos_def_QF₂ℤ d} (hr : is_reduced f) {M : SL₂ℤ} (lt : M • f < f) :
  abs (M 0 1) ≤ 1 :=
if hm : M 0 0 = 0 then le_one_of_pow_two_le_one (by simpa [hm] using abs_m_le_one_aux hr M lt)
else if hn : M 0 1 = 0 then by simp [hn]
else calc abs (M 0 1) ≤ abs (M 0 0) * abs (M 0 1) :
  (le_mul_iff_one_le_left (abs_pos_iff.mpr hn)).mpr (int.pos_iff_ge_one.mp (abs_pos_iff.mpr hm))
                  ... ≤ (abs (M 0 0) - abs (M 0 1))^2 + abs (M 0 0) * abs (M 0 1) :
  le_add_of_nonneg_left' (pow_two_nonneg _)
                  ... ≤ 1 : abs_m_le_one_aux hr M lt

lemma abs_m_eq_one_of_nonzero {f : pos_def_QF₂ℤ d} (hr : is_reduced f) {M : SL₂ℤ} (lt : M • f < f)
  (h : M 0 0 ≠ 0) : abs (M 0 0) = 1 :=
le_antisymm (abs_m_le_one hr lt) (int.pos_iff_ge_one.mp (abs_pos_iff.mpr h))

lemma abs_n_eq_one_of_nonzero {f : pos_def_QF₂ℤ d} (hr : is_reduced f) {M : SL₂ℤ} (lt : M • f < f)
  (h : M 0 1 ≠ 0) : abs (M 0 1) = 1 :=
le_antisymm (abs_n_le_one hr lt) (int.pos_iff_ge_one.mp (abs_pos_iff.mpr h))

lemma int.le_mul_self : Π (a : ℤ), a ≤ a * a
| 0 := by simp
| (nat.succ n) := (le_mul_iff_one_le_left (by norm_cast; apply nat.zero_lt_succ)).mpr (by norm_cast; exact nat.succ_le_succ bot_le)
| -[1+ n ] := by simp

lemma int.abs_le_mul_self (a : ℤ) : abs a ≤ a * a :=
if h : a < 0 then by simpa [abs_of_neg h] using int.le_mul_self (-a)
else by simpa [abs_of_nonneg (le_of_not_gt h)] using int.le_mul_self a

lemma abs_m_mul_n_le_m_pow_two {m n : ℤ} (h : abs n ≤ 1) : abs (m * n) ≤ m^2 :=
if hm : m = 0 then by simp [hm]
else calc abs (m * n) = abs m * abs n : abs_mul m n
       ... ≤ abs m : (mul_le_iff_le_one_right (abs_pos_iff.mpr hm)).mpr h
       ... ≤ m * m : int.abs_le_mul_self m
       ... = m^2 : (pow_two m).symm

lemma a_add_b_nonneg {a b m n : ℤ} (hab : 2 * abs b ≤ a) (hn : abs n ≤ 1) : 0 ≤ a * m^2 + 2 * b * m * n :=
calc 0 ≤ a * (m ^ 2 - abs (m * n)) : mul_nonneg (le_trans (mul_nonneg (by linarith) (abs_nonneg _)) hab) (sub_nonneg.mpr (abs_m_mul_n_le_m_pow_two hn))
   ... = a * m^2 - a * abs (m * n) : by simp [mul_sub, abs_mul]
   ... ≤ a * m^2 - 2 * abs b * abs (m * n) : sub_le_sub_left (mul_le_mul_of_nonneg_right hab (abs_nonneg _)) _
   ... = a * m^2 + - abs (2 * b * m * n) : by simp [sub_eq_add_neg, abs_mul, mul_assoc]
   ... ≤ a * m^2 + 2 * b * m * n : add_le_add_left (neg_le.mp (neg_le_abs_self _)) _

lemma a_eq_c_of_a_eq_smul_a_of_n_nonzero {f : pos_def_QF₂ℤ d} (hr : is_reduced f) {M : SL₂ℤ}
  (lt : M • f < f) (ha : (M • f) 0 0 = f 0 0) (hn : M 0 1 ≠ 0) : f 0 0 = f 1 1 :=
le_antisymm hr.2 $ calc
  f 1 1 ≤ f 1 1 * (M 0 1)^2 :
    (le_mul_iff_one_le_right (f.pos_def.diagonal_pos 1)).mpr
      (int.pos_iff_ge_one.mp (pow_two_pos hn))
    ... ≤ f 0 0 * (M 0 0)^2 + 2 * f 1 0 * M 0 0 * M 0 1 + f 1 1 * (M 0 1)^2 :
      le_add_of_nonneg_left' (a_add_b_nonneg hr.1 (abs_n_le_one hr lt))
    ... = (M • f) 0 0 : (smul_val_0_0 M f).symm
    ... = f 0 0 : ha

lemma two_b_eq_a_of_mn_nonzero {f : pos_def_QF₂ℤ d} (hr : is_reduced f) {M : SL₂ℤ}
  (lt : M • f < f) (hm : M 0 0 ≠ 0) (hn : M 0 1 ≠ 0) : 2 * f 1 0 = f 0 0 :=
hr.two_b_eq_a_of_c_le_two_abs_b $
begin
  apply sub_nonpos.mp,
  rw [sub_eq_add_neg, add_comm],
  apply add_le_iff_nonpos_right.mp,
  rw ←add_assoc,
  apply le_trans _ (reduced.a_val_le_of_smul_lt lt),
  apply add_le_add,
  { apply add_le_add,
  { simp [← abs_pow_two, abs_m_eq_one_of_nonzero hr lt hm, pow_two (1 : ℤ)] },
  apply neg_le.mp,
  convert neg_le_abs_self (2 * f 1 0 * M 0 0 * M 0 1) using 1,
  simp [abs_mul, abs_m_eq_one_of_nonzero hr lt hm, abs_n_eq_one_of_nonzero hr lt hn] },
  { simp [← abs_pow_two, abs_n_eq_one_of_nonzero hr lt hn, pow_two (1 : ℤ)] }
  end

lemma smul_SL_val_1_0 (M : SL₂ℤ) (f : pos_def_QF₂ℤ d) :
  (M • f) 1 0 = M 0 0 * M 1 0 * f 0 0 + (2 * M 0 1 * M 1 0 + 1) * f 1 0 + M 0 1 * M 1 1 * f 1 1 :=
have this : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 2 * M 0 1 * M 1 0 + 1,
by { rw [two_mul, ←M.det_coe_fun, det_2x2], ring },
calc (M • f) 1 0
    = M 0 0 * M 1 0 * f 0 0 + (M 0 0 * M 1 1 + M 0 1 * M 1 0) * f 1 0 + M 0 1 * M 1 1 * f 1 1 :
      by { simp, ring }
... = M 0 0 * M 1 0 * f 0 0 + (2 * M 0 1 * M 1 0 + 1) * f 1 0 + M 0 1 * M 1 1 * f 1 1 :
      by { rw this }

lemma smul_val_1_0_of_m_eq_zero (f : pos_def_QF₂ℤ d) {M : SL₂ℤ} (h : M 0 0 = 0) :
  (M • f) 1 0 = (M 1 1 * f 1 1 + M 1 0 * f 1 0) * M 0 1 :=
by simp [h, add_comm]

lemma smul_val_1_0_of_n_eq_zero (f : pos_def_QF₂ℤ d) {M : SL₂ℤ} (h : M 0 1 = 0) :
  (M • f) 1 0 = (M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 0 0 :=
by simp [h]

lemma abs_b_le_abs_b_smul_of_reduced_of_m_eq_zero {f : pos_def_QF₂ℤ d} (hr : is_reduced f)
  {M : SL₂ℤ} (hm : M 0 0 = 0) : abs (f 1 0) ≤ abs ((M • f) 1 0) :=
begin
  rw [smul_val_1_0_of_m_eq_zero f hm, abs_mul, abs_n_eq_one_of_m_eq_zero hm, mul_one],
  cases (abs_eq (show (0 : ℤ) ≤ 1, by norm_num)).mp (abs_o_eq_one_of_m_eq_zero hm),
  { simpa [h] using abs_b_le_mul_a_add_b (le_trans hr.1 hr.2) },
  { simpa [h] using abs_b_le_mul_a_sub_b (le_trans hr.1 hr.2) }
end

lemma abs_b_le_abs_b_smul_of_reduced_of_n_eq_zero {f : pos_def_QF₂ℤ d} (hr : is_reduced f)
  {M : SL₂ℤ} (hn : M 0 1 = 0) : abs (f 1 0) ≤ abs ((M • f) 1 0) :=
begin
  rw [smul_val_1_0_of_n_eq_zero f hn, abs_mul, abs_m_eq_one_of_n_eq_zero hn, mul_one],
  cases (abs_eq (show (0 : ℤ) ≤ 1, by norm_num)).mp (abs_p_eq_one_of_n_eq_zero hn),
  { simpa [h] using abs_b_le_mul_a_add_b hr.1 },
  { simpa [h] using abs_b_le_mul_a_sub_b hr.1 }
end

lemma abs_b_not_lt_abs_b_smul_of_reduced_of_mn_nonzero {f : pos_def_QF₂ℤ d} (hr : is_reduced f)
  {M : SL₂ℤ} (lt : M • f < f) (ha : (M • f) 0 0 = f 0 0) (hm : M 0 0 ≠ 0) (hn : M 0 1 ≠ 0) :
  ¬ abs ((M • f) 1 0) < abs (f 1 0) :=
begin
  intro h,
  suffices : (2 : ℤ) ≤ 1,
  { cases this },
  apply int.le_of_dvd (show (0 : ℤ) < 1, by norm_num),
  use -(M 1 0 * M 0 0 + M 1 0 * M 0 1 + M 1 1 * M 0 1),
  rw mul_neg_eq_neg_mul_symm,
  apply eq.symm,
  apply neg_eq_iff_add_eq_zero.mpr,
  apply @int.abs_mul_lt_abs_self _ (f 1 0),
  convert h,
  rw [smul_SL_val_1_0, ← a_eq_c_of_a_eq_smul_a_of_n_nonzero hr lt ha hn, ← two_b_eq_a_of_mn_nonzero hr lt hm hn],
  ring
end

lemma min_of_reduced {f : pos_def_QF₂ℤ d} (hr : is_reduced f) : minimal f :=
minimal_iff.mpr (λ M lt, begin
  rcases reduced.lt_iff.mp lt with ha | ⟨ha, habs | ⟨habs, hsgn | ⟨hsgn, hc⟩⟩⟩,
  { apply not_lt_of_ge (a_le_a_smul_of_reduced hr M) ha },
  { by_cases hm : M 0 0 = 0,
    { exact not_lt_of_ge (abs_b_le_abs_b_smul_of_reduced_of_m_eq_zero hr hm) habs },
    by_cases hn : M 0 1 = 0,
    { exact not_lt_of_ge (abs_b_le_abs_b_smul_of_reduced_of_n_eq_zero hr hn) habs },
    exact abs_b_not_lt_abs_b_smul_of_reduced_of_mn_nonzero hr lt ha hm hn habs },
  { obtain ⟨b_neg, smul_b_pos⟩ := (reduced.sign'_lt_iff_of_abs_eq habs).mp hsgn,
    rw [smul_SL_val_1_0] at smul_b_pos,
    by_cases hn : M 0 1 = 0,
    { by_cases M 1 0 = 0,
      { apply lt_asymm b_neg,
        simpa [h, hn] using smul_b_pos },
      apply not_lt_of_ge (hr.b_nonneg_left (le_antisymm hr.1 _)) b_neg,
      calc f 0 0 ≤ abs (M 1 0) * f 0 0 : (le_mul_iff_one_le_left (f.pos_def.diagonal_pos 0)).mpr (int.pos_iff_ge_one.mp (abs_pos_iff.mpr h))
             ... = abs (- M 1 0) * abs (f 0 0) : by { erw [abs_neg, abs_of_pos (f.pos_def.diagonal_pos 0)], refl }
             ... = abs (- M 1 0 * f 0 0) - abs (M 1 1 * f 1 0) + abs (f 1 0) : by { rw [abs_mul, abs_mul, abs_p_eq_one_of_n_eq_zero hn], ring }
             ... ≤ abs (- M 1 0 * f 0 0 - M 1 1 * f 1 0) + abs (f 1 0) : add_le_add_right (abs_sub_abs_le_abs_sub _ _) _
             ... = abs (-(M 1 0 * f 0 0 + M 1 1 * f 1 0)) + abs (f 1 0) : by { congr, ring }
             ... = abs (-((M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 0 0)) + abs (f 1 0) : by rw [abs_neg, abs_neg, abs_mul, abs_m_eq_one_of_n_eq_zero hn, mul_one]
             ... = 2 * abs (f 1 0) : by simp [←habs, hn, two_mul] },
    exact not_lt_of_ge (hr.b_nonneg_right (a_eq_c_of_a_eq_smul_a_of_n_nonzero hr lt ha hn)) b_neg },
  { apply not_lt_of_ge _ hc,
    by_cases hn : M 0 1 = 0,
    { have psq_eq_1 : (M 1 1)^2 = 1, { simp [←abs_pow_two, abs_p_eq_one_of_n_eq_zero hn, pow_two (1 : ℤ)] },
      by_cases M 1 0 = 0,
      { simp [h, psq_eq_1] },
      rw [f.coe_fn_smul, smul_val_1_1, psq_eq_1, mul_one],
      apply le_add_of_nonneg_left' _,
      have abs_k_pos : 0 < abs (M 1 0) := lt_of_le_of_ne (abs_nonneg (M 1 0)) (ne.symm (mt abs_eq_zero.mp h)),
      calc 0 ≤ abs (M 1 0) * (f 0 0 - 2 * abs (f 1 0)) :
        mul_nonneg (abs_nonneg (M 1 0)) (sub_nonneg.mpr hr.1)
        ... = abs (M 1 0) * (1 * f 0 0 - 2 * abs (f 1 0)) : by ring
        ... ≤ abs (M 1 0) * (abs (M 1 0) * f 0 0 - 2 * abs (f 1 0)) :
        mul_le_mul_of_nonneg_left (sub_le_sub_right
          (mul_le_mul_of_nonneg_right
          (int.pos_iff_ge_one.mp abs_k_pos)
          (le_of_lt (f.pos_def.diagonal_pos 0))) _) (abs_nonneg (M 1 0))
        ... = f 0 0 * (abs (M 1 0))^2 - 2 * abs (f 1 0) * abs (M 1 0) : by ring
        ... = f 0 0 * (M 1 0)^2 + - abs (2 * f 1 0 * M 1 0 * M 1 1) :
        by rw [abs_pow_two _, sub_eq_add_neg, abs_mul, abs_mul, abs_mul, abs_p_eq_one_of_n_eq_zero hn, mul_one, abs_of_nonneg (show (0 : ℤ) ≤ 2, by norm_num)]
        ... ≤ f 0 0 * (M 1 0)^2 + 2 * f 1 0 * M 1 0 * M 1 1 : add_le_add_left (neg_le.mp (neg_le_abs_self _)) _ },
    have a_eq_c := a_eq_c_of_a_eq_smul_a_of_n_nonzero hr lt ha hn,
    rw [f.coe_fn_smul, smul_val_1_1, f.coe_fn_coe, a_eq_c],
    refine le_trans _ (min_of_reduced_aux_aux (M 1 0) (M 1 1) (le_trans hr.1 hr.2) (le_refl (f 1 1))),
    apply (le_mul_iff_one_le_right (f.pos_def.diagonal_pos 1)).mpr,
    apply int.pos_iff_ge_one.mp,
    apply sub_pow_two_add_mul_pos,
    rintro ⟨hm, hn⟩,
    simpa [det_2x2, hm, hn] using M.det_coe_fun }
end)

lemma min_iff_reduced {f : pos_def_QF₂ℤ d} :
  minimal f ↔ is_reduced f :=
⟨ λ min,
  ⟨ b_le_a_of_min min,
    a_le_c_of_min min,
    λ h, le_of_not_gt (λ b_neg, minimal_iff.mp min (change_xy 1) (change_xy_lt_sign
        (calc abs (1 * f 0 0 + f 1 0) = abs (2 * -f 1 0 + f 1 0) : by simp [← h, abs_of_neg b_neg]
                                  ... = abs (- f 1 0) : by ring
                                  ... = abs (f 1 0) : abs_neg _ )
        (by { convert reduced.sign'_neg_lt_sign'_self.mpr b_neg, rw [←h, abs_of_neg b_neg], ring }))),
    λ h, le_of_not_gt (mt (swap_x_y_lt_of_eq_of_neg h) (minimal_iff.mp min swap_x_y))⟩,
  min_of_reduced⟩

/-- In each orbit, there is a unique reduced quadratic form -/
lemma exists_unique_reduced_equiv (f : pos_def_QF₂ℤ d) :
  ∃! g, g ≈ f ∧ is_reduced g :=
let ⟨g, ⟨e, m⟩, u⟩ := exists_unique_min f in
⟨ g, ⟨e, (min_iff_reduced).mp m⟩, λ g' ⟨e', r'⟩, u g' ⟨e', (min_iff_reduced).mpr r'⟩ ⟩

end quadratic_form

import data.int.gcd
import data.zsqrtd.basic
import data.matrix.basic
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

notation `M₂ℤ` := matrix (fin 2) (fin 2) ℤ
notation `SL₂ℤ` := matrix.special_linear_group (fin 2) ℤ

/-- We represent a quadratic form in `n` variables with a symmetric `n` by `n` matrix.

  The evaluation map for a form `M` sends a vector `x` to `xᵀ ⬝ M ⬝ x`.
-/
def quadratic_form (n : Type u) [fintype n] (α : Type v) := {M : matrix n n α // Mᵀ = M }

namespace quadratic_form
variables {n : Type u} [fintype n] {α : Type v}
open matrix

def mk (M : matrix n n α) (hM : Mᵀ = M) : quadratic_form n α := ⟨M, hM⟩

def from_tuple (a b c : α) : quadratic_form (fin 2) α :=
⟨![ ![ a, b ], ![ b, c ] ], by { ext i j, fin_cases i; fin_cases j; refl }⟩

instance : has_coe_to_fun (quadratic_form n α) :=
⟨ λ _, n → n → α,
  λ M, M.1 ⟩

@[simp] lemma coe_fn_mk (M : matrix n n α) (hM : Mᵀ = M) :
  ⇑(mk M hM) = M :=
rfl

lemma coe_fn_symmetric (M : quadratic_form n α) {i j : n} : M i j = M j i :=
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
    = sum univ (λ i' : n, sum univ (λ j : n, ite (i = i') (ite (i = j) (M i' j) 0) 0)) :
    by { simp [eval_val] }
... = sum univ (λ i' : n, ite (i = i') (sum univ (λ j : n, (ite (i = j) (M i' j) 0))) 0) :
    by { congr, ext i', split_ifs, { refl }, simp }
... = M i i : by simp

lemma eq_of_eval_eq_aux [semiring α] [decidable_eq n] (M : quadratic_form n α) {i j : n} (h : j ≠ i) :
  eval M (λ j', if i = j' ∨ j = j' then 1 else 0) = M i i + 2 * M i j + M j j :=
calc eval M (λ j', if i = j' ∨ j = j' then 1 else 0)
    = sum univ (λ i' : n, sum univ (λ j' : n, ite (i = i' ∨ j = i') (ite (i = j' ∨ j = j') (M i' j') 0) 0))
    : by simp [eval_val]
... = sum univ (λ i' : n, ite (i = i' ∨ j = i') (sum univ (λ j' : n, ite (i = j' ∨ j = j') (M i' j') 0)) 0)
    : by { congr, ext i', split_ifs, { refl }, simp }
... = sum univ (λ (j' : n), ite (i = j' ∨ j = j') (M i j') 0) + sum univ (λ (j' : n), ite (i = j' ∨ j = j') (M j j') 0)
    : by { erw [sum_ite _ _ (λ x, x), filter_or, sum_union]; simp [filter_eq, h] }
... = M i i + M i j + M j i + M j j
    : by { erw [sum_ite _ _ (λ x, x), sum_ite _ _ (λ x, x), filter_or, sum_union, sum_union]; simp [filter_eq, h] }
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
variables [comm_ring α]

/--
  Matrices have an action on quadratic forms by multiplication on the input.

  For example, `f(x, y)` is mapped to `f(αx + βy, γx + δy)` by the matrix `((α β) (γ δ)).`

  We don't instantiate a class instance yet since we will look primarily at the action of PSL₂,
  on quadratic forms with fixed discriminant.
-/
def matrix_action (M : matrix n n α) (N : quadratic_form n α) : quadratic_form n α :=
mk (M ⬝ N ⬝ Mᵀ) (by simp [matrix.mul_assoc, transpose_coe_fn])

local infixr ` · `:70 := matrix_action

lemma coe_fn_mul_action (M : matrix n n α) (f : quadratic_form n α) :
  ⇑(M · f) = M ⬝ f ⬝ Mᵀ
:= rfl

lemma neg_action (M : matrix n n α) (f : quadratic_form n α) : -M · f = M · f :=
by simp [matrix_action]

/--
  The action works by multiplying vectors with the matrix.
-/
@[simp] lemma eval_action (M : matrix n n α) (f : quadratic_form n α) (x : n → α) :
  eval (M · f) x = eval f (M.vec_mul x) :=
by simp [eval, matrix_action, row_vec_mul, col_vec_mul, matrix.mul_assoc]

@[simp] lemma matrix_action_identity [decidable_eq n] (f : quadratic_form n α) :
  matrix_action 1 f = f :=
by simp [matrix_action]

@[simp] lemma matrix_action_mul (M N : matrix n n α) (f : quadratic_form n α) :
  (M ⬝ N) · f = M · (N · f) :=
by { ext, simp [coe_fn_mul_action, matrix.mul_assoc] }

end matrix_action

section discr
open_locale matrix_action

variables [comm_ring α] [decidable_eq n]

/--
  The discriminant of a matrix representation is given by its determinant.
-/
def discr (M : quadratic_form n α) : α := matrix.det M

/--
  Matrices with determinant = 1 preserve the discriminant of a quadratic form.
-/
theorem det_invariant_for_SL (f : quadratic_form n α) (M : special_linear_group n α) :
  discr (matrix_action M.1 f) = f.discr :=
by simp [discr, matrix_action, M.2]
end discr

section class_number

variable {d : ℤ}

-- TODO: better name!
def QF (d : ℤ) := {f : quadratic_form (fin 2) ℤ // f.discr = d}

instance QF_to_form : has_coe (QF d) (quadratic_form (fin 2) ℤ) := ⟨ λ f, f.1 ⟩

instance QF_to_fn : has_coe_to_fun (QF d) := ⟨ λ f, fin 2 → fin 2 → ℤ, λ f, f.1 ⟩

-- Turn right action of M into a left action by replacing M with M⁻¹.
instance : has_scalar SL₂ℤ (QF d) :=
⟨λ M f, ⟨matrix_action M.1 f.1, trans (det_invariant_for_SL f.1 M) f.2⟩⟩

@[simp] lemma smul_val (M : SL₂ℤ) (f : QF d) : (M • f).val = matrix_action ↑M f.1 := rfl

@[simp] lemma coe_smul (M : SL₂ℤ) (f : QF d) : ↑(M • f) = matrix_action ↑M f.1 := rfl

@[simp] lemma coe_fn_smul (M : SL₂ℤ) (f : QF d) : ⇑(M • f) = matrix_action ↑M f.1 := rfl

instance : mul_action SL₂ℤ (QF d) :=
⟨ λ f, subtype.ext.mpr (matrix_action_identity f),
  λ M N f, subtype.ext.mpr (matrix_action_mul M N f) ⟩

-- TODO: better name!
def Γ_infinity : set SL₂ℤ := { M | ∃ m, M 0 0 = 1 ∧ M 0 1 = m ∧ M 1 0 = 0 ∧ M 1 1 = 1 }

@[simp] lemma fin.succ_zero {n : ℕ} (p : 0 < n) :
  fin.succ ⟨0, p⟩ = 1 :=
sorry

instance : is_submonoid Γ_infinity :=
⟨⟨0, by finish⟩, λ a b ⟨ma, ha⟩ ⟨mb, hb⟩, ⟨ma + mb, sorry ⟩⟩
instance : is_subgroup Γ_infinity :=
⟨λ a ⟨ma, ha⟩, ⟨-ma, sorry ⟩⟩

instance subset_has_scalar {α β} [monoid α] [has_scalar α β] (s : set α) : has_scalar s β := ⟨λ s b, s.1 • b⟩
def submonoid_mul_action {α β} [monoid α] [mul_action α β] (s : set α) [is_submonoid s] : mul_action s β :=
⟨one_smul α, λ x y, @_root_.mul_smul α _ _ _ x.1 y.1⟩

/-- Quadratic forms are considered equivalent if they share the same orbit modulo Γ_infinity. -/
def quadratic_class_group (d : ℤ) : Type :=
quotient (@mul_action.orbit_rel Γ_infinity (QF d) _ (submonoid_mul_action _))

end class_number

section reduced

variables {d : ℤ}

def is_positive_definite (f : QF d) : Prop := ∀ x ≠ 0, eval f.val x > 0

lemma val_0_0_pos (f : QF d) (h : is_positive_definite f) : 0 < f 0 0 :=
begin
  convert h (λ i, if i = 0 then 1 else 0) _,
  { exact (eval_basis f.val 0).symm },
  intro eq_0,
  simpa using congr_fun eq_0 0,
end

lemma special_linear_group.vec_mul_injective {A : SL₂ℤ} {v v' : fin 2 → ℤ} (h : vec_mul v A = vec_mul v' A) :
  v = v' :=
calc v = vec_mul v ↑(A * A⁻¹) : by simp [-vec_mul_succ, vec_mul_one]
   ... = vec_mul (vec_mul v A) ↑A⁻¹ : sorry
   ... = vec_mul v' ↑(A * A⁻¹) : sorry
   ... = v' : sorry

lemma is_positive_definite_smul (f : QF d) (M : SL₂ℤ) (h : is_positive_definite f) :
  is_positive_definite (M • f) :=
λ x hx, begin
  rw [smul_val, eval_action],
  apply h,
  intro hx',
  apply hx,
  apply special_linear_group.vec_mul_injective (trans hx' _),
  simp
end

def is_reduced (f : QF d) : Prop :=
abs (f 1 0) ≤ f 0 0 ∧ f 0 0 ≤ f 1 1 ∧ ((abs (f 1 0) = f 0 0 ∨ f 0 0 = f 1 1) → f 1 0 ≥ 0)

/-- A well-founded order of quadratic forms, such that reduced forms are minimal. -/
def reduced_order_key (f : QF d) : lex ℤ (lex ℤ ℤ) :=
⟨f 0 0, abs (f 1 0), f 1 1⟩

/-- A well-founded order of quadratic forms, such that reduced forms are minimal. -/
instance : has_lt (QF d) :=
⟨function.on_fun (<) reduced_order_key⟩

lemma well_founded_reduced_order : well_founded ((<) : QF d → QF d → Prop) :=
sorry

/-- `swap_x_y` is a matrix whose action swaps the coefficient for `x²` and `y²` -/
def swap_x_y : SL₂ℤ := ⟨![![0, -1], ![1, 0]], rfl⟩

lemma swap_x_y_smul (f : QF d) :
  (⇑(swap_x_y • f) : M₂ℤ) = ![![0, -1], ![1, 0]] ⬝ f ⬝ ![![0, 1], ![-1, 0]] :=
sorry

lemma swap_x_y_smul_0_0 (f : QF d) : (swap_x_y • f) 0 0 = f 1 1 :=
by { simp [swap_x_y_smul], refl }

lemma swap_x_y_lt {f : QF d} (h : f 1 1 < f 0 0) : (swap_x_y • f) < f :=
prod.lex.left _ _ _ (by { rw swap_x_y_smul_0_0 f, exact h })

/-- `change_xy k` changes the coefficient for `xy` while keeping the coefficient for `x²` the same -/
def change_xy (k : ℤ) : SL₂ℤ := ⟨![![1, 0], ![k, 1]], sorry⟩

lemma change_xy_smul (k : ℤ) (f : QF d) :
  (⇑(change_xy k • f) : M₂ℤ) = ![![1, 0], ![k, 1]] ⬝ f ⬝ ![![1, k], ![0, 1]] :=
sorry

lemma change_xy_smul_0_0 (k : ℤ) (f : QF d) : (change_xy k • f) 0 0 = f 0 0 :=
by { simp [change_xy_smul] }

lemma change_xy_smul_1_0 (k : ℤ) (f : QF d) : (change_xy k • f) 1 0 = k * f 0 0 + f 1 0 :=
by { simp [change_xy_smul], refl }

lemma change_xy_lt {f : QF d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) < abs (f 1 0)) : (change_xy k • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  change_xy_smul_0_0 k f,
  prod.lex.left _ _ _ (by { rw change_xy_smul_1_0 k f, exact h }) ⟩ )

lemma int.le_div_mul (a b : ℤ) : a - b ≤ (a / b) * b := sorry

/-- In each orbit, there is a unique reduced quadratic form -/
lemma unique_reduced_mem_orbit (M : QF d) (M_pos_def : is_positive_definite M) :
  ∃! f, f ∈ mul_action.orbit SL₂ℤ M ∧ is_reduced f :=
begin
  obtain ⟨f, ⟨N, hf⟩, min⟩ := well_founded.has_min well_founded_reduced_order (mul_action.orbit SL₂ℤ M) ⟨M, mul_action.orbit_eq_iff.mp rfl⟩,
  have f_pos_def : is_positive_definite f,
  { rw ←hf, apply is_positive_definite_smul, exact M_pos_def },
  use f,
  use ⟨N, hf⟩,
  have a_pos : f 0 0 > 0 := val_0_0_pos _ _,
  { by_cases c_lt_a : f 1 1 < f 0 0,
    { exfalso,
      have : swap_x_y • f ∈ mul_action.orbit SL₂ℤ M :=
      ⟨ swap_x_y * N, trans (_root_.mul_smul swap_x_y N M) (congr_arg _ hf) ⟩,
      apply min (swap_x_y • f) this,
      exact swap_x_y_lt c_lt_a },
    have a_le_c : f 0 0 ≤ f 1 1 := le_of_not_gt c_lt_a,

    by_cases a_lt_b : f 0 0 < abs (f 1 0),
    { exfalso,
      have : change_xy ((f 0 0 - f 1 0) / f 0 0) • f ∈ mul_action.orbit SL₂ℤ M :=
      ⟨ change_xy _ * N, trans (_root_.mul_smul (change_xy _) N M) (congr_arg _ hf) ⟩,
      apply min (change_xy _ • f) this,
      refine change_xy_lt (lt_of_le_of_lt (abs_le.mpr (and.intro _ _)) a_lt_b),
      { apply le_trans _ (add_le_add_right (int.le_div_mul _ _) _),
        apply le_of_lt,
        apply neg_lt.mp,
        apply lt_of_le_of_lt _ a_pos,
        linarith },
      { apply le_trans (add_le_add_right (int.div_mul_le _ (ne_of_gt a_pos)) _),
        norm_num } },
    have b_le_a : abs (f 1 0) ≤ f 0 0 := le_of_not_gt a_lt_b,

    use b_le_a,
    use le_of_not_gt c_lt_a,
    by_cases b_pos : 0 ≤ f 1 0,
    { intro,
      assumption },
    rintros (b_eq_a | a_eq_c),
    { sorry },
    sorry },

  exact f_pos_def,

  rintros g ⟨g_mem_orbit, g_is_reduced⟩,
  have := min g g_mem_orbit,
  sorry
end

end reduced

end quadratic_form

#lint

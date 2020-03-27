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

lemma coe_fn_matrix_action (M : matrix n n α) (f : quadratic_form n α) :
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
by { ext, simp [coe_fn_matrix_action, matrix.mul_assoc] }

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

lemma smul_def (M : SL₂ℤ) (f : QF d) :
  M • f = ⟨matrix_action M f, trans (det_invariant_for_SL f.1 M) f.2⟩ := rfl

@[simp] lemma smul_val (M : SL₂ℤ) (f : QF d) : (M • f).val = matrix_action M f := rfl

@[simp] lemma coe_smul (M : SL₂ℤ) (f : QF d) : ↑(M • f) = matrix_action M f := rfl

@[simp] lemma coe_fn_smul (M : SL₂ℤ) (f : QF d) : ⇑(M • f) = matrix_action M f := rfl

@[simp] lemma coe_fn_coe (f : QF d) : ⇑(f : quadratic_form (fin 2) ℤ) = f := rfl

lemma QF_coe_fn_symmetric (f : QF d) (i j : fin 2) : f i j = f j i := coe_fn_symmetric f

instance : mul_action SL₂ℤ (QF d) :=
⟨ λ f, subtype.ext.mpr (matrix_action_identity f),
  λ M N f, subtype.ext.mpr (matrix_action_mul M N f) ⟩

@[ext]
lemma QF.ext {f g : QF d} (h : ∀ i j, f i j = g i j) : f = g :=
begin
  cases f,
  cases g,
  congr,
  ext,
  apply h
end

-- TODO: better name!
def Γ_infinity : set SL₂ℤ := { M | ∃ m, M 0 0 = 1 ∧ M 0 1 = m ∧ M 1 0 = 0 ∧ M 1 1 = 1 }

@[simp] lemma fin.one : (fin.succ 0 : fin 2) = 1 := rfl
@[simp] lemma fin.default_one : (default (fin 1)) = 0 := rfl

@[simp] lemma smul_val_0_0 (M : SL₂ℤ) (f : QF d) :
  matrix_action M f 0 0 = f 0 0 * (M 0 0)^2 + 2 * f 1 0 * M 0 0 * M 0 1 + f 1 1 * (M 0 1)^2 :=
calc (matrix_action M f) 0 0 = (M ⬝ f ⬝ Mᵀ) 0 0 : rfl
             ... = (M 0 0 * f 0 0 + M 0 1 * f 1 0) * M 0 0 + (M 0 0 * f 1 0 + M 0 1 * f 1 1) * M 0 1 :
  by simp [mul_val, QF_coe_fn_symmetric f 0 1]
             ... = f 0 0 * (M 0 0)^2 + 2 * f 1 0 * M 0 0 * M 0 1 + f 1 1 * (M 0 1)^2 :
  by ring

@[simp] lemma smul_val_1_0 (M : SL₂ℤ) (f : QF d) :
  matrix_action M f 1 0 = (M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 0 0 + (M 1 0 * f 1 0 + M 1 1 * f 1 1) * M 0 1 :=
calc (M • f) 1 0 = (M ⬝ f ⬝ Mᵀ) 1 0 : rfl
             ... = (M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 0 0 + (M 1 0 * f 1 0 + M 1 1 * f 1 1) * M 0 1 :
  by simp [mul_val, QF_coe_fn_symmetric f 0 1]

@[simp] lemma smul_val_1_1 (M : SL₂ℤ) (f : QF d) :
  matrix_action M f 1 1 = f 0 0 * (M 1 0)^2 + 2 * f 1 0 * M 1 0 * M 1 1 + f 1 1 * (M 1 1)^2 :=
calc (M • f) 1 1 = (M ⬝ f ⬝ Mᵀ) 1 1 : rfl
             ... = (M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 1 0 + (M 1 0 * f 1 0 + M 1 1 * f 1 1) * M 1 1 :
  by simp [mul_val, QF_coe_fn_symmetric f 0 1]
             ... = f 0 0 * (M 1 0)^2 + 2 * f 1 0 * M 1 0 * M 1 1 + f 1 1 * (M 1 1)^2 :
  by ring

instance : is_submonoid Γ_infinity :=
⟨⟨0, by finish⟩, λ a b ⟨ma, ha⟩ ⟨mb, hb⟩, ⟨ma + mb, by { simp [matrix.mul_val, ha, hb, add_comm] } ⟩⟩
instance : is_subgroup Γ_infinity :=
⟨λ a ⟨ma, ha⟩, ⟨-ma, by { simp [adjugate_2x2, ha] } ⟩⟩

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

lemma is_positive_definite.a_pos {f : QF d} (h : is_positive_definite f) : 0 < f 0 0 :=
begin
  convert h (λ i, if 0 = i then 1 else 0) _,
  { exact (eval_basis f.val 0).symm },
  intro eq_0,
  simpa using congr_fun eq_0 0,
end

lemma val_0_0_pos {f : QF d} (h : is_positive_definite f) : 0 < f 0 0 := h.a_pos

lemma val_1_1_pos {f : QF d} (h : is_positive_definite f) : 0 < f 1 1 :=
begin
  convert h (λ i, if 1 = i then 1 else 0) _,
  { exact (eval_basis f.val 1).symm },
  intro eq_0,
  simpa [-matrix.zero_succ] using congr_fun eq_0 1
end

lemma special_linear_group.vec_mul_injective {A : SL₂ℤ} {v v' : fin 2 → ℤ} (h : vec_mul v A = vec_mul v' A) :
  v = v' :=
calc v = vec_mul v ⇑(A * A⁻¹) : by rw [mul_right_inv, special_linear_group.one_apply, vec_mul_one]
   ... = vec_mul (vec_mul v A) ⇑A⁻¹ : by rw [vec_mul_vec_mul, special_linear_group.mul_apply]
   ... = vec_mul (vec_mul v' A) ⇑A⁻¹ : by rw h
   ... = vec_mul v' ⇑(A * A⁻¹) : by rw [vec_mul_vec_mul, special_linear_group.mul_apply]
   ... = v' : by rw [mul_right_inv, special_linear_group.one_apply, vec_mul_one]

lemma is_positive_definite_smul {f : QF d} (M : SL₂ℤ) (h : is_positive_definite f) :
  is_positive_definite (M • f) :=
λ x hx, have hx' : vec_mul x ⇑M ≠ 0 :=
  λ he, hx (special_linear_group.vec_mul_injective (trans he (vec_mul_zero M).symm)),
by simpa [smul_val, eval_action] using h _ hx'

lemma pos_def_of_mem_orbit {f g : QF d}
  (hf : is_positive_definite f) (hg : g ∈ mul_action.orbit SL₂ℤ f) :
  is_positive_definite g :=
by { rcases hg with ⟨M, ⟨⟩⟩, exact is_positive_definite_smul M hf}

lemma a_pos_of_mem_orbit_pos_def {f g : QF d}
  (hf : is_positive_definite f) (hg : g ∈ mul_action.orbit SL₂ℤ f) : g 0 0 > 0 :=
val_0_0_pos (pos_def_of_mem_orbit hf hg)

lemma c_pos_of_mem_orbit_pos_def {f g : QF d}
  (hf : is_positive_definite f) (hg : g ∈ mul_action.orbit SL₂ℤ f) : g 1 1 > 0 :=
val_1_1_pos (pos_def_of_mem_orbit hf hg)

def is_reduced (f : QF d) : Prop :=
2 * abs (f 1 0) ≤ f 0 0 ∧ f 0 0 ≤ f 1 1 ∧ ((2 * abs (f 1 0) = f 0 0 ∨ f 0 0 = f 1 1) → 0 ≤ f 1 0)

lemma is_reduced.two_b_eq_a_of_c_le_two_abs_b {f : QF d} (hr : is_reduced f) (h : f 1 1 ≤ 2 * abs (f 1 0)) :
  2 * f 1 0 = f 0 0 :=
have two_abs_b_eq : 2 * abs (f 1 0) = f 0 0 := le_antisymm hr.1 (le_trans hr.2.1 h),
have b_nonneg : 0 ≤ f 1 0 := hr.2.2 (or.inl two_abs_b_eq),
by simpa [abs_of_nonneg b_nonneg] using two_abs_b_eq

lemma abs_b_le_a_of_reduced {f : QF d} (h : is_reduced f) : abs (f 1 0) ≤ f 0 0 :=
calc abs (f 1 0) = 1 * abs (f 1 0) : (one_mul _).symm
             ... ≤ 2 * abs (f 1 0) : mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
             ... ≤ f 0 0 : h.1

/-- Map the sign of an int to `fin 3` to order them with positive as the least, then zero, then negative. -/
def sign' : ℤ → fin 3
| (n+1:ℕ) := 0
| 0       := 1
| -[1+ n] := 2

lemma sign'_of_pos : Π {a : ℤ} (h : 0 < a), sign' a = 0
| (n+1:ℕ) h := rfl
| 0       h := by cases h
| -[1+ n] h := by cases h

lemma sign'_of_neg : Π {a : ℤ} (h : a < 0), sign' a = 2
| (n+1:ℕ) h := by cases h
| 0       h := by cases h
| -[1+ n] h := rfl

def sign'_to_sign : fin 3 → ℤ
| ⟨0, _⟩ := 1
| ⟨1, _⟩ := 0
| _ := -1

lemma sign'_to_sign_of_sign' : ∀ a, sign'_to_sign (sign' a) = a.sign
| (n+1:ℕ) := rfl
| 0       := rfl
| -[1+ n] := rfl

/-- A well-founded order of quadratic forms, such that reduced forms are minimal. -/
def reduced_order_key (f : QF d) : lex ℕ (lex ℕ (lex (fin 3) ℕ)) :=
⟨(f 0 0).nat_abs, (f 1 0).nat_abs, sign' (f 1 0), (f 1 1).nat_abs⟩

lemma int.nat_abs_of_pos {a : ℤ} (ha : 0 < a) : (↑(a.nat_abs) : ℤ) = a :=
calc (↑(a.nat_abs) : ℤ) = a.sign * a.nat_abs : by simp [int.sign_eq_one_of_pos ha]
                    ... = a : int.sign_mul_nat_abs a

lemma int.nat_abs_of_neg {a : ℤ} (ha : a < 0) : (↑(a.nat_abs) : ℤ) = -a :=
calc (↑(a.nat_abs) : ℤ) = -(a.sign * a.nat_abs) : by simp [int.sign_eq_neg_one_of_neg ha]
                    ... = -a : by rw int.sign_mul_nat_abs a

lemma int.nat_abs_le_of_pos {a b : ℤ} (ha : 0 < a) (h : a ≤ b) : a.nat_abs ≤ b.nat_abs :=
int.coe_nat_le.mp (by { convert h; apply int.nat_abs_of_pos; linarith })

lemma int.nat_abs_lt_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : a < b ↔ a.nat_abs < b.nat_abs :=
by { convert int.coe_nat_lt; apply eq.symm; apply int.nat_abs_of_pos; assumption }

lemma int.nat_abs_eq : Π {a b : ℤ}, a.nat_abs = b.nat_abs ↔ abs a = abs b :=
by simp [int.abs_eq_nat_abs]

lemma int.nat_abs_le {a b : ℤ} : abs a ≤ abs b ↔ a.nat_abs ≤ b.nat_abs :=
by simp [int.abs_eq_nat_abs]

lemma int.nat_abs_lt {a b : ℤ} : abs a < abs b ↔ a.nat_abs < b.nat_abs :=
by simp [int.abs_eq_nat_abs]

lemma key_fst_of_pos_def {f : QF d} (hf : is_positive_definite f) : ↑(reduced_order_key f).fst = f 0 0 :=
int.nat_abs_of_pos (val_0_0_pos hf)

lemma key_snd_snd_snd_of_pos_def {f : QF d} (hf : is_positive_definite f) :
  ↑(reduced_order_key f).snd.snd.snd = f 1 1 :=
int.nat_abs_of_pos (val_1_1_pos hf)

lemma key_injective_on_pos_def {f g : QF d} (hf : is_positive_definite f) (hg : is_positive_definite g) :
  reduced_order_key f = reduced_order_key g → f = g :=
begin
  intro h,
  cases f with f,
  cases g with g,

  have : f 1 0 = g 1 0 :=
  calc f 1 0 = (f 1 0).sign * (f 1 0).nat_abs : (int.sign_mul_nat_abs _).symm
         ... = sign'_to_sign (sign' (f 1 0)) * (f 1 0).nat_abs : by rw sign'_to_sign_of_sign'
         ... = sign'_to_sign (reduced_order_key ⟨f, _⟩).snd.snd.fst * (reduced_order_key ⟨f, _⟩).snd.fst : rfl
         ... = sign'_to_sign (reduced_order_key ⟨g, _⟩).snd.snd.fst * (reduced_order_key ⟨g, _⟩).snd.fst : by rw h
         ... = sign'_to_sign (sign' (g 1 0)) * (g 1 0).nat_abs : rfl
         ... = (g 1 0).sign * (g 1 0).nat_abs : by rw sign'_to_sign_of_sign'
         ... = g 1 0 : int.sign_mul_nat_abs _,
  congr,
  ext,
  fin_cases i; fin_cases j,
  { calc f 0 0 = (reduced_order_key ⟨f, _⟩).fst : (key_fst_of_pos_def hf).symm
           ... = (reduced_order_key ⟨g, _⟩).fst : by rw h
           ... = g 0 0 : key_fst_of_pos_def hg },
  { calc f 0 1 = f 1 0 : coe_fn_symmetric f
           ... = g 1 0 : this
           ... = g 0 1 : coe_fn_symmetric g },
  { exact this },
  { calc f 1 1 = (reduced_order_key ⟨f, _⟩).snd.snd.snd : (key_snd_snd_snd_of_pos_def hf).symm
           ... = (reduced_order_key ⟨g, _⟩).snd.snd.snd : by rw h
           ... = g 1 1 : key_snd_snd_snd_of_pos_def hg }
end

/-- An order of quadratic forms, such that reduced forms are minimal. -/
instance : has_lt (QF d) :=
⟨function.on_fun (prod.lex (<) (<)) reduced_order_key⟩

/-- An embedding from the reduced_order, to show it is well-founded. -/
def reduced_order_embedding {f : QF d} (hf : is_positive_definite f) :
  order_embedding (subrel (<) (mul_action.orbit SL₂ℤ f)) ((<) : _ → lex ℕ (lex ℕ (lex (fin 3) ℕ)) → Prop) :=
{ to_fun := λ f, reduced_order_key f.1,
  inj := λ ⟨g, hg⟩ ⟨g', hg'⟩ h, by { congr, exact key_injective_on_pos_def (pos_def_of_mem_orbit hf hg) (pos_def_of_mem_orbit hf hg') h },
  ord := λ _ _, iff.rfl }

/-- The order on quadratic forms is well-founded on positive definite classes. -/
def reduced_well_order {f : QF d} (hf : is_positive_definite f) :
  is_well_order _ (subrel (<) (mul_action.orbit SL₂ℤ f)) :=
@order_embedding.is_well_order _ _ _ _ (reduced_order_embedding hf)
  (@prod.lex.is_well_order _ _ _ _ _
    (@prod.lex.is_well_order _ _ _ _ _
      (@prod.lex.is_well_order _ _ _ _ _ _)))

lemma reduced_lt_iff_of_pos_def {f g : QF d} (hf : is_positive_definite f) (hg : is_positive_definite g) :
  f < g ↔ f 0 0 < g 0 0 ∨
    (f 0 0 = g 0 0 ∧ (abs (f 1 0) < abs (g 1 0) ∨
      (abs (f 1 0) = abs (g 1 0) ∧ (sign' (f 1 0) < sign' (g 1 0) ∨
        (sign' (f 1 0) = sign' (g 1 0) ∧ f 1 1 < g 1 1))))) :=
 begin
  refine iff.trans (prod.lex_def _ _) (or_congr _ (and_congr _ _)),
  { exact iff.trans int.coe_nat_lt.symm (by rw [key_fst_of_pos_def hf, key_fst_of_pos_def hg]) },
  { exact (iff.trans (function.injective.eq_iff @int.coe_nat_inj).symm (by rw [key_fst_of_pos_def hf, key_fst_of_pos_def hg]))},
  refine iff.trans (prod.lex_def _ _) (or_congr int.nat_abs_lt.symm (and_congr int.nat_abs_eq _)),
  refine iff.trans (prod.lex_def _ _) (or_congr (iff.refl _) (and_congr (iff.refl _) _)),
  apply iff.trans int.coe_nat_lt.symm,
  rw [key_snd_snd_snd_of_pos_def hf, key_snd_snd_snd_of_pos_def hg],
end

lemma a_le_of_lt_of_pos_def {f g : QF d} (hf : is_positive_definite f) (hg : is_positive_definite g) (h : f < g):
  f 0 0 ≤ g 0 0 :=
begin
  rcases (reduced_lt_iff_of_pos_def hf hg).mp h with ha | ⟨ha, _⟩,
  { exact le_of_lt ha },
  { exact le_of_eq ha }
end

lemma a_le_of_smul_lt_of_pos_def {f : QF d} (hf : is_positive_definite f) {M : SL₂ℤ} (h : M • f < f):
  (M • f) 0 0 ≤ f 0 0 :=
a_le_of_lt_of_pos_def (is_positive_definite_smul M hf) hf h

lemma a_val_le_of_smul_lt_of_pos_def {f : QF d} (hf : is_positive_definite f) {M : SL₂ℤ} (h : M • f < f):
  f 0 0 * (M 0 0)^2 + 2 * f 1 0 * M 0 0 * M 0 1 + f 1 1 * (M 0 1)^2 ≤ f 0 0 :=
by { simpa using a_le_of_smul_lt_of_pos_def hf h }

lemma not_lt_of_a_ge {f g : QF d} (hf : is_positive_definite f) (hg : is_positive_definite g) (ha : f 0 0 < g 0 0) :
  ¬ g < f :=
λ h, not_lt_of_ge (a_le_of_lt_of_pos_def hg hf h) ha

/-- `swap_x_y` is a matrix whose action swaps the coefficient for `x²` and `y²` -/
def swap_x_y : SL₂ℤ := ⟨![![0, -1], ![1, 0]], rfl⟩

@[simp]
lemma coe_fn_swap : ⇑(swap_x_y) = ![![0, -1], ![1, 0]] := rfl

lemma swap_x_y_smul (f : QF d) :
  (matrix_action swap_x_y f : M₂ℤ) = ![![0, -1], ![1, 0]] ⬝ f ⬝ ![![0, 1], ![-1, 0]] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma swap_x_y_smul_0_0 (f : QF d) : matrix_action swap_x_y f 0 0 = f 1 1 :=
by simp [swap_x_y_smul]

lemma swap_x_y_smul_1_0 (f : QF d) : (matrix_action swap_x_y f) 1 0 = - f 1 0 :=
by { simp [swap_x_y_smul, QF_coe_fn_symmetric f 0 1] }

lemma swap_x_y_lt {f : QF d} (hc : 0 < f 1 1) (h : f 1 1 < f 0 0) : (swap_x_y • f) < f :=
prod.lex.left _ _ _ (by { convert ((int.nat_abs_lt_of_pos hc (by linarith)).mp h), simp [swap_x_y_smul_0_0 f] })

lemma swap_x_y_lt_of_eq_of_neg {f : QF d} (hac : f 0 0 = f 1 1) (hb : f 1 0 < 0) : (swap_x_y • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  (by { simp [reduced_order_key, swap_x_y_smul_0_0, hac.symm] }),
  (prod.lex_def _ _).mpr (or.inr ⟨
    (by { simp [reduced_order_key, swap_x_y_smul_1_0] }),
    prod.lex.left _ _ _ (by { simp [swap_x_y_smul_1_0, sign'_of_neg hb, sign'_of_pos (neg_pos.mpr hb)], exact dec_trivial }) ⟩ ) ⟩ )

/-- `change_xy k` changes the coefficient for `xy` while keeping the coefficient for `x²` the same -/
def change_xy (k : ℤ) : SL₂ℤ := ⟨![![1, 0], ![k, 1]], by simp [det_2x2]⟩

lemma change_xy_smul (k : ℤ) (f : QF d) :
  (⇑(change_xy k • f) : M₂ℤ) = ![![1, 0], ![k, 1]] ⬝ f ⬝ ![![1, k], ![0, 1]] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma change_xy_smul_0_0 (k : ℤ) (f : QF d) : (change_xy k • f) 0 0 = f 0 0 :=
by { simp [change_xy_smul] }

lemma change_xy_smul_1_0 (k : ℤ) (f : QF d) : (change_xy k • f) 1 0 = k * f 0 0 + f 1 0 :=
by { simp [change_xy_smul] }

lemma change_xy_smul_1_1 (k : ℤ) (f : QF d) : (change_xy k • f) 1 1 = k^2 * f 0 0 + 2 * k * f 1 0 + f 1 1 :=
by { simp [change_xy_smul, QF_coe_fn_symmetric f 0 1], ring }

lemma change_xy_lt_abs {f : QF d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) < abs (f 1 0)) : (change_xy k • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  (by rw [reduced_order_key, reduced_order_key, change_xy_smul_0_0 k f]),
  prod.lex.left _ _ _ (by { convert int.nat_abs_lt.mp h, rw change_xy_smul_1_0 k f }) ⟩ )

lemma change_xy_lt_sign {f : QF d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) = abs (f 1 0)) (h2 : sign' (k * f 0 0 + f 1 0) < sign' (f 1 0)) : (change_xy k • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  (by rw [reduced_order_key, reduced_order_key, change_xy_smul_0_0 k f]),
  (prod.lex_def _ _).mpr (or.inr ⟨
    (by rw [reduced_order_key, reduced_order_key, change_xy_smul_1_0, int.nat_abs_eq, h]),
    prod.lex.left _ _ _ (by { rw change_xy_smul_1_0 k f, exact h2 }) ⟩ ) ⟩ )

lemma int.pos_iff_ge_one : ∀ {a : ℤ}, a > 0 ↔ a ≥ 1
| 0 := by split; intro ha; linarith
| (nat.succ n) := by split; intro ha; linarith
| -[1+ n ] := by split; intro ha; linarith

lemma a_le_c_of_min {f : QF d} (hf : is_positive_definite f) (min : ∀ (g : QF d), g ∈ mul_action.orbit (special_linear_group (fin 2) ℤ) f → ¬g < f) : f 0 0 ≤ f 1 1 :=
le_of_not_gt (λ c_lt_a, min (swap_x_y • f) ⟨_, rfl⟩ (swap_x_y_lt (val_1_1_pos hf) c_lt_a))

lemma b_le_a_of_min {f : QF d} (hf : is_positive_definite f) (min : ∀ (g : QF d), g ∈ mul_action.orbit (special_linear_group (fin 2) ℤ) f → ¬g < f) : 2 * abs (f 1 0) ≤ f 0 0 :=
begin
  have a_pos : 0 < f 0 0 := val_0_0_pos hf,
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

lemma abs_pos_of_nonzero {a : ℤ} (h : a ≠ 0) : 0 < abs a :=
lt_of_le_of_ne (abs_nonneg a) (λ h', h (abs_eq_zero.mp h'.symm))

lemma abs_b_le_multiple_a {a b k : ℤ} (h : 2 * abs b ≤ a) : abs b ≤ abs (k * a + b) :=
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

lemma pow_two_pos {a : ℤ} (h : a ≠ 0) : 0 < a^2 :=
lt_of_le_of_ne (pow_two_nonneg a) (ne.symm (mt pow_eq_zero h))

lemma sub_pow_two_add_mul_pos {m n : ℤ} (hmn : ¬ (m = 0 ∧ n = 0)) : 0 < (abs m - abs n)^2 + abs m * abs n :=
begin
  by_cases hm : m = 0; by_cases hn : n = 0;
    try {rw hm}; try {rw hn}; try {rw abs_zero},
  { tauto },
  { simpa using pow_two_pos (mt abs_eq_zero.mp hn) },
  { simpa using pow_two_pos (mt abs_eq_zero.mp hm) },
  { apply add_pos_of_nonneg_of_pos (pow_two_nonneg _),
  apply mul_pos (abs_pos_of_nonzero hm) (abs_pos_of_nonzero hn) }
end

lemma pow_two_add_mul_add_pow_two_pos {m n : ℤ} (hmn : ¬ (m = 0 ∧ n = 0)) : 0 < m^2 + m * n + n^2 :=
calc 0 < (abs m - abs n)^2 + abs m * abs n : sub_pow_two_add_mul_pos hmn
   ... = (abs m)^2 - abs m * abs n + (abs n)^2 : by ring
   ... = m^2 + - abs (m * n) + n^2 : by simp [abs_mul, abs_pow_two, sub_eq_add_neg]
   ... ≤ m^2 + m * n + n^2 : add_le_add_right (add_le_add_left (neg_le.mp (neg_le_abs_self _)) _) _

lemma min_of_reduced_aux {a b c m n : ℤ} (hmn : ¬ (m = 0 ∧ n = 0)) (hba : 2 * abs b ≤ a) (hac : a ≤ c) :
  a ≤ a * m^2 + 2 * b * m * n + c * n^2 :=
have ha : 0 ≤ a := le_trans (mul_nonneg (show (0 : ℤ) ≤ 2, by norm_num) (abs_nonneg b)) hba,
have 1 ≤ (abs m - abs n)^2 + abs m * abs n := int.pos_iff_ge_one.mp (sub_pow_two_add_mul_pos hmn),
le_trans (by simpa using (mul_le_mul_of_nonneg_left this ha)) (min_of_reduced_aux_aux m n hba hac)

lemma not_lt_of_n_eq_zero {f : QF d} (hpd : is_positive_definite f) (hr : is_reduced f) {M : SL₂ℤ} (hn : M 0 1 = 0) :
  ¬ M • f < f :=
begin
  intros hlt,
  have ga_eq : f 0 0 * (M 0 0)^2 = (M • f) 0 0,
  { simp [hn, pow_two] },

  have hmp : M 0 0 * M 1 1 = 1,
  { apply trans _ M.det_coe_fun,
    simp [det_2x2, hn] },

  have m_ne_zero : M 0 0 ≠ 0,
  { intro hm,
    apply zero_ne_one (trans _ hmp),
    simp [hm] },
  have p_ne_zero : M 1 1 ≠ 0,
  { intro hp,
    apply zero_ne_one (trans _ hmp),
    simp [hp] },

  have hm : M 0 0 = 1 ∨ M 0 0 = -1,
  { cases int.units_eq_one_or ⟨M 0 0, M 1 1, hmp, trans (mul_comm _ _) hmp⟩,
    { exact or.inl (congr_arg units.val h) },
    { exact or.inr (congr_arg units.val h) } },
  have hp : M 1 1 = 1 ∨ M 1 1 = -1,
  { cases int.units_eq_one_or ⟨M 1 1, M 0 0, trans (mul_comm _ _) hmp, hmp⟩,
    { exact or.inl (congr_arg units.val h) },
    { exact or.inr (congr_arg units.val h) } },

  have msq_eq_1 : (M 0 0)^2 = 1, { cases hm; rw hm; norm_num },
  have abs_m_eq_1 : abs (M 0 0) = 1, { cases hm; rw hm; norm_num },
  have abs_p_eq_1 : abs (M 1 1) = 1, { cases hp; rw hp; norm_num },

  rcases (reduced_lt_iff_of_pos_def (is_positive_definite_smul _ hpd) hpd).mp hlt with
    ha | ⟨ha, habs | ⟨habs, hsgn | ⟨hsgn, hc⟩⟩⟩,
  { apply ne_of_lt ha,
    rw [←ga_eq, msq_eq_1, mul_one] },
  { refine not_lt_of_ge _ habs,
    suffices : abs (f 1 0) ≤ abs (M 1 0 * f 0 0 + M 1 1 * f 1 0),
    { simpa [hn, abs_mul, abs_m_eq_1] },
    cases int.units_eq_one_or ⟨M 1 1, M 0 0, trans (by simp [det_2x2, hn, mul_comm]) M.det_coe_fun, trans (by simp [det_2x2, hn]) M.det_coe_fun⟩,
    { have h : M 1 1 = 1 := congr_arg units.val h,
      convert abs_b_le_multiple_a hr.1,
      simp [h] },
    { have h : M 1 1 = -1 := congr_arg units.val h,
      rw [←abs_neg (f 1 0), h, neg_one_mul],
      refine abs_b_le_multiple_a _,
      rw [abs_neg],
      exact hr.1 } },
  { rw [coe_fn_smul, smul_val_1_0, hn, mul_zero, add_zero] at *,
    by_cases (M 1 0) = 0,
    { apply lt_irrefl (sign' (f 1 0)),
      convert hsgn,
      calc f 1 0 = M 1 1 * f 1 0 * M 0 0 : by rw [mul_comm (M 1 1) (f 1 0), mul_assoc, mul_comm (M 1 1) (M 0 0), hmp, mul_one]
             ... = _ : by simp [h, hn] },
    have : 2 * abs (f 1 0) = f 0 0,
    { apply le_antisymm hr.1,
      calc f 0 0 ≤ abs (f 0 0) : le_abs_self _
             ... = 1 * abs (f 0 0) : (one_mul _).symm
             ... ≤ abs (- M 1 0) * abs (f 0 0) :
        mul_le_mul_of_nonneg_right (int.pos_iff_ge_one.mp (abs_pos_of_ne_zero (neg_ne_zero.mpr h))) (abs_nonneg _)
             ... = abs (- M 1 0 * f 0 0) - abs (M 1 1 * f 1 0) + abs (f 1 0) : by { rw [abs_mul, abs_mul, abs_p_eq_1], ring }
             ... ≤ abs (- M 1 0 * f 0 0 - M 1 1 * f 1 0) + abs (f 1 0) : add_le_add_right (abs_sub_abs_le_abs_sub _ _) _
             ... = abs (-(M 1 0 * f 0 0 + M 1 1 * f 1 0)) + abs (f 1 0) : by { congr, ring }
             ... = abs (-((M 1 0 * f 0 0 + M 1 1 * f 1 0) * M 0 0)) + abs (f 1 0) : by rw [abs_neg, abs_neg, abs_mul, abs_m_eq_1, mul_one]
             ... = abs (f 1 0) + abs (f 1 0) : by rw [abs_neg, habs]
             ... = 2 * abs (f 1 0) : (two_mul _).symm },
    have := hr.2.2 (or.inl this),
    by_cases 0 = f 1 0,
    { apply ne_of_lt hsgn,
      rw [← h, mul_zero, abs_zero, add_zero] at habs,
      rw [← h, mul_zero, add_zero, sign', abs_eq_zero.mp habs, sign'] },
    rw [sign'_of_pos (lt_of_le_of_ne this h)] at hsgn,
    cases hsgn },
  { rw [coe_fn_smul, smul_val_1_1] at *,
    refine not_lt_of_ge _ hc,
    by_cases M 1 0 = 0,
    { cases hp; simp [h, hp, pow_two] },
    have psq_eq_1 : (M 1 1)^2 = 1, { cases hp; simp [hp, pow_two] },
    rw [psq_eq_1, mul_one] at *,
    apply le_add_of_nonneg_left' _,
    have abs_k_pos : 0 < abs (M 1 0) := lt_of_le_of_ne (abs_nonneg (M 1 0)) (ne.symm (mt abs_eq_zero.mp h)),
    calc 0 ≤ abs (M 1 0) * (f 0 0 - 2 * abs (f 1 0)) :
      mul_nonneg (abs_nonneg (M 1 0)) (sub_nonneg.mpr hr.1)
       ... = abs (M 1 0) * (1 * f 0 0 - 2 * abs (f 1 0)) : by ring
       ... ≤ abs (M 1 0) * (abs (M 1 0) * f 0 0 - 2 * abs (f 1 0)) :
      mul_le_mul_of_nonneg_left (sub_le_sub_right
        (mul_le_mul_of_nonneg_right
        (int.pos_iff_ge_one.mp abs_k_pos)
        (le_of_lt (val_0_0_pos hpd))) _) (abs_nonneg (M 1 0))
       ... = f 0 0 * (abs (M 1 0))^2 - 2 * abs (f 1 0) * abs (M 1 0) : by ring
       ... = f 0 0 * (M 1 0)^2 + - abs (2 * f 1 0 * M 1 0 * M 1 1) :
      by rw [abs_pow_two _, sub_eq_add_neg, abs_mul, abs_mul, abs_mul, abs_p_eq_1, mul_one, abs_of_nonneg (show (0 : ℤ) ≤ 2, by norm_num)]
       ... ≤ f 0 0 * (M 1 0)^2 + 2 * f 1 0 * M 1 0 * M 1 1 : add_le_add_left (neg_le.mp (neg_le_abs_self _)) _
    }
end

lemma not_lt_of_m_eq_zero {f : QF d} (hpd : is_positive_definite f) (hr : is_reduced f) {M : SL₂ℤ} :
  M 0 0 = 0 → ¬ (M • f) < f :=
begin
  intros hm hlt,
  have ga_eq : f 1 1 * (M 0 1)^2 = (M • f) 0 0 ,
  { simp [hm, pow_two] },

  have hn : M 0 1 ≠ 0,
  { intro hn,
    apply zero_ne_one (trans _ M.det_coe_fun),
    simp [det_2x2, hm, hn] },

  have ho : M 1 0 ≠ 0,
  { intro ho,
    apply zero_ne_one (trans _ M.det_coe_fun),
    simp [det_2x2, hm, ho] },

  have a_eq_c : f 0 0 = f 1 1 := le_antisymm hr.2.1 (calc
  f 1 1 = f 1 1 * 1 : (mul_one _).symm
    ... ≤ f 1 1 * (M 0 1)^2 : mul_le_mul_of_nonneg_left (int.pos_iff_ge_one.mp (pow_two_pos hn)) (le_of_lt (val_1_1_pos hpd))
    ... = (M • f) 0 0 : ga_eq
    ... ≤ f 0 0 : a_le_of_smul_lt_of_pos_def hpd hlt),

  have b_nonneg := hr.2.2 (or.inr a_eq_c),

  have nsq_eq_1 : (M 0 1)^2 = 1,
  { apply (domain.mul_left_inj (ne_of_gt (val_1_1_pos hpd))).mp,
    apply eq.symm,
    apply le_antisymm (mul_le_mul_of_nonneg_left (int.pos_iff_ge_one.mp (pow_two_pos hn)) (le_of_lt (val_1_1_pos hpd))),
    calc f 1 1 * M 0 1^2 = (M • f) 0 0 : ga_eq
    ... ≤ f 0 0 : a_le_of_smul_lt_of_pos_def hpd hlt
    ... ≤ f 1 1 : hr.2.1
    ... = f 1 1 * 1 : (mul_one _).symm },
  have abs_n_eq_1 : abs (M 0 1) = 1,
  { cases int.units_eq_one_or ⟨M 0 1, M 0 1, (by rw [←pow_two, nsq_eq_1]), (by rw [←pow_two, nsq_eq_1])⟩,
     { have h : M 0 1 = 1 := congr_arg units.val h,
       rw [h],
       norm_num },
     { have h : M 0 1 = -1 := congr_arg units.val h,
       rw [h],
       norm_num } },

  rcases (reduced_lt_iff_of_pos_def (is_positive_definite_smul M hpd) hpd).mp hlt with
    ha | ⟨ha, habs | ⟨habs, hsgn | ⟨hsgn, hc⟩⟩⟩,
  { apply not_lt_of_ge _ ha,
    apply le_trans hr.2.1,
    convert mul_le_mul_of_nonneg_left (int.pos_iff_ge_one.mp (pow_two_pos hn)) (le_of_lt (val_1_1_pos hpd)),
    simp,
    exact ga_eq.symm },
  { apply not_lt_of_ge _ habs,
    suffices : abs (f 1 0) ≤ abs (M 1 1 * f 1 1 + M 1 0 * f 1 0),
    { simpa [hm, abs_mul, abs_n_eq_1, add_comm] using this },
    cases int.units_eq_one_or ⟨M 1 0, -M 0 1, trans (by simp [det_2x2, hm, mul_comm]) M.det_coe_fun, trans (by simp [det_2x2, hm]) M.det_coe_fun⟩,
    { have h : M 1 0 = 1 := congr_arg units.val h,
      convert abs_b_le_multiple_a (le_trans hr.1 hr.2.1),
      simp [h] },
    { have h : M 1 0 = -1 := congr_arg units.val h,
      rw [←abs_neg (f 1 0), h, neg_one_mul],
      refine abs_b_le_multiple_a (le_trans _ hr.2.1),
      rw [abs_neg],
      exact hr.1 },
    },
  { by_cases f 1 0 = 0,
    { rw [h, abs_eq_zero.mp (trans habs (abs_eq_zero.mpr h))] at hsgn, exact lt_irrefl _ hsgn },
    { rw [sign'_of_pos (lt_of_le_of_ne b_nonneg (ne.symm h))] at hsgn, cases hsgn } },
  { apply not_lt_of_ge _ hc,
    convert min_of_reduced_aux (λ hop, ho hop.1) (le_trans hr.1 hr.2.1) (le_refl _),
    simp [hm, a_eq_c] },
end

lemma le_of_add_le_of_nonneg_left {a b c : ℤ} (ha : 0 ≤ a) (h : a + b ≤ c) : b ≤ c :=
le_trans (le_add_of_nonneg_left' ha) h

lemma le_of_add_le_of_nonneg_right {a b c : ℤ} (hb : 0 ≤ b) (h : a + b ≤ c) : a ≤ c :=
le_trans (le_add_of_nonneg_right hb) h

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
le_antisymm le_one (int.pos_iff_ge_one.mp (abs_pos_of_nonzero nonzero))

lemma self_add_self_mul_nonneg_of_pos {a b : ℤ} (ha : 0 < a) : 0 ≤ a + a * b ↔ -1 ≤ b :=
calc 0 ≤ a + a * b ↔ 0 - (a * b) ≤ a : sub_le_iff_le_add.symm
               ... ↔ a * (-b) ≤ a : by simp
               ... ↔ -b ≤ 1 : mul_le_iff_le_one_right ha
               ... ↔ -1 ≤ b : neg_le

lemma self_mul_add_self_nonneg_of_pos {a b : ℤ} (ha : 0 < a) : 0 ≤ a * b + a ↔ -1 ≤ b :=
by rw [add_comm, self_add_self_mul_nonneg_of_pos ha]

lemma int.abs_mul_lt_abs_self {a b : ℤ} (h : abs (a * b) < abs b) : a = 0 :=
have h : abs a * abs b < abs b := by rwa [←abs_mul],
if h' : b = 0
then absurd (by simp [h']) (not_le_of_gt h)
else have _ := (mul_lt_iff_lt_one_left (abs_pos_of_nonzero h')).mp h,
abs_eq_zero.mp (le_antisymm (le_of_not_gt (mt int.pos_iff_ge_one.mpr (not_le_of_gt this))) (abs_nonneg a))

lemma min_of_reduced {f : QF d} (hf : is_positive_definite f) (f_red : is_reduced f) :
  ∀ (g : QF d), g ∈ mul_action.orbit SL₂ℤ f → ¬ g < f :=
begin
  rintros g ⟨N, rfl⟩ g_lt_f,
  have g_lt_f : N • f < f := g_lt_f,
  by_cases hm : N 0 0 = 0,
  { exact not_lt_of_m_eq_zero hf f_red hm g_lt_f },
  by_cases hn : N 0 1 = 0,
  { exact not_lt_of_n_eq_zero hf f_red hn g_lt_f },
  have : f 0 0 * ((abs (N 0 0) - abs (N 0 1))^2 + abs (N 0 0) * abs (N 0 1)) ≤ f 0 0,
  { apply le_trans (min_of_reduced_aux_aux (N 0 0) (N 0 1) f_red.1 f_red.2.1),
    convert a_le_of_smul_lt_of_pos_def hf g_lt_f using 1,
    simp },
  have := (mul_le_iff_le_one_right (val_0_0_pos hf)).mp this,
  have mul_le := le_of_add_le_of_nonneg_left (pow_two_nonneg _) this,
  have abs_m_eq_one : abs (N 0 0) = 1 :=
    int.abs_eq_one_of_nonzero_of_le_one hm (int.le_one_of_mul_le_one_of_pos_right mul_le (abs_pos_of_nonzero hn)),
  have abs_n_eq_one : abs (N 0 1) = 1 :=
    int.abs_eq_one_of_nonzero_of_le_one hn (int.le_one_of_mul_le_one_of_pos_left mul_le (abs_pos_of_nonzero hm)),
  have : f 0 0 * (N 0 0)^2 + 2 * f 1 0 * N 0 0 * N 0 1 + f 1 1 * (N 0 1)^2 ≤ f 0 0,
  { convert a_le_of_smul_lt_of_pos_def hf g_lt_f using 1,
    simp },
  have msq_eq_one : (N 0 0)^2 = 1,
  { rw [←abs_pow_two], simp [abs_m_eq_one] },
  have nsq_eq_one : (N 0 1)^2 = 1,
  { rw [←abs_pow_two], simp [abs_n_eq_one] },
  have neg_one_le_mn : -1 ≤ N 0 0 * N 0 1,
  { apply neg_le.mp,
    convert neg_le_abs_self _,
    simp [abs_mul, abs_m_eq_one, abs_n_eq_one] },
  have c_le_b : f 1 1 ≤ 2 * abs (f 1 0),
  { apply sub_nonpos.mp,
    rw [sub_eq_add_neg, add_comm],
    apply add_le_iff_nonpos_right.mp,
    rw ←add_assoc,
    apply le_trans _ (a_val_le_of_smul_lt_of_pos_def hf g_lt_f),
    apply add_le_add,
    { apply add_le_add,
      { simp [msq_eq_one] },
      apply neg_le.mp,
      convert neg_le_abs_self (2 * f 1 0 * N 0 0 * N 0 1) using 1,
      simp [abs_mul, abs_m_eq_one, abs_n_eq_one] },
    { simp [nsq_eq_one] } },
  have c_eq_a : f 1 1 = f 0 0 := le_antisymm (le_trans c_le_b f_red.1) f_red.2.1,
  have two_b_eq_a := f_red.two_b_eq_a_of_c_le_two_abs_b c_le_b,
  have b_pos : 0 < f 1 0,
  { apply lt_of_mul_lt_mul_left _ (show (0 : ℤ) ≤ 2, by norm_num),
    simpa [two_b_eq_a] using hf.a_pos },

  rcases (reduced_lt_iff_of_pos_def (is_positive_definite_smul N hf) hf).mp g_lt_f with
    ha | ⟨ha, habs | ⟨habs, hsgn | ⟨hsgn, hc⟩⟩⟩,
  { apply not_lt_of_ge _ ha,
    simpa [c_eq_a, msq_eq_one, nsq_eq_one, two_b_eq_a, mul_assoc, self_mul_add_self_nonneg_of_pos hf.a_pos] },
  { suffices : (2 : ℤ) ≤ 1,
    { cases this },
    apply int.le_of_dvd (show (0 : ℤ) < 1, by norm_num),
    have : 2 * (N 1 0 * N 0 1) = N 0 1 * N 1 0 + N 0 0 * N 1 1 - 1,
    { rw [two_mul, ←N.det_coe_fun, det_2x2], ring },
    use -(N 1 0 * N 0 0 + N 1 0 * N 0 1 + N 1 1 * N 0 1),
    rw mul_neg_eq_neg_mul_symm,
    apply eq.symm,
    apply neg_eq_iff_add_eq_zero.mpr,
    apply @int.abs_mul_lt_abs_self _ (f 1 0),
    convert habs,
    simp [c_eq_a, ←two_b_eq_a, mul_add, this],
    ring },
  { rw [sign'_of_pos b_pos] at hsgn, cases hsgn },
  { apply not_lt_of_ge _ hc,
    convert mul_le_mul (le_refl (f 0 0)) (_ : 1 ≤ (N 1 0)^2 + N 1 0 * N 1 1 + (N 1 1)^2) (show (0 : ℤ) ≤ 1, by norm_num) (le_of_lt hf.a_pos),
    { rw [coe_fn_smul, smul_val_1_1, c_eq_a, two_b_eq_a], ring },
    { simp [c_eq_a] },
    apply int.pos_iff_ge_one.mp,
    convert pow_two_add_mul_add_pow_two_pos _,
    rintros ⟨ho, hp⟩,
    apply @zero_ne_one int,
    rw [← N.det_coe_fun, det_2x2, ho, hp, mul_zero, mul_zero, sub_zero] }
end

/-- In each orbit, there is a unique reduced quadratic form -/
lemma unique_reduced_mem_orbit (f : QF d) (hf : is_positive_definite f) :
  ∃! f_min, f_min ∈ mul_action.orbit SL₂ℤ f ∧ is_reduced f_min :=
begin
  obtain ⟨⟨f_min, ⟨M, hM⟩⟩, _, min⟩ := well_founded.has_min (reduced_well_order hf).wf set.univ (set.nonempty_of_mem (set.mem_univ ⟨f, (mul_action.mem_orbit_self _)⟩)),
  have hf_min : is_positive_definite f_min,
  { rw ←hM, apply is_positive_definite_smul, exact hf },
  have min' : ∀ (g : QF d), g ∈ mul_action.orbit (special_linear_group (fin 2) ℤ) f_min → ¬g < f_min,
  { intros g hg, refine min ⟨g, _⟩ (set.mem_univ _), rw ← mul_action.orbit_eq_iff.mpr ⟨M, hM⟩, exact hg },

  have a_pos : 0 < f_min 0 0 := val_0_0_pos hf_min,
  have b_le_a : 2 * abs (f_min 1 0) ≤ f_min 0 0 := b_le_a_of_min hf_min min',
  have a_le_c : f_min 0 0 ≤ f_min 1 1 := a_le_c_of_min hf_min min',

  use f_min,
  use ⟨M, hM⟩,

  { use b_le_a,
    use a_le_c,
    rintros (abs_b_eq_a | a_eq_c); apply le_of_not_gt; intro b_neg,
    { have a_eq_neg_2_b : f_min 0 0 = -2 * f_min 1 0,
      { rw [← abs_b_eq_a, abs_of_neg b_neg], ring },
      have change_xy_eq : 1 * f_min 0 0 + f_min 1 0 = - f_min 1 0,
      { rw [a_eq_neg_2_b], ring },
      apply min' (change_xy 1 • f_min) ⟨_, rfl⟩,
      apply change_xy_lt_sign; rw [change_xy_eq],
      { rw [abs_neg] },
      rw [sign'_of_pos (neg_pos.mpr b_neg), sign'_of_neg b_neg],
      exact dec_trivial },

    apply min' (swap_x_y • f_min) ⟨_, rfl⟩,
    exact swap_x_y_lt_of_eq_of_neg a_eq_c b_neg },

  rintros g ⟨⟨N, hN⟩, g_red⟩,
  have hg : is_positive_definite g,
  { rw ←hN, apply is_positive_definite_smul, exact hf },
  have := (reduced_well_order hf).trichotomous,
  rcases this ⟨f_min, ⟨M, hM⟩⟩ ⟨g, ⟨N, hN⟩⟩ with f_lt_g | f_eq_g | f_gt_g,
  { exfalso,
    refine min_of_reduced hg g_red f_min _ f_lt_g,
    use M * N⁻¹,
    simp [← hM, ← hN, ← _root_.mul_smul] },
  { exact congr_arg subtype.val f_eq_g.symm },
  { exfalso,
    apply min ⟨g, ⟨N, hN⟩⟩ (set.mem_univ _) f_gt_g },
end

end reduced

end quadratic_form

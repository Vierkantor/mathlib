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

@[simp] lemma smul_val (M : SL₂ℤ) (f : QF d) : (M • f).val = matrix_action M f := rfl

@[simp] lemma coe_smul (M : SL₂ℤ) (f : QF d) : ↑(M • f) = matrix_action M f := rfl

@[simp] lemma coe_fn_smul (M : SL₂ℤ) (f : QF d) : ⇑(M • f) = matrix_action M f := rfl

@[simp] lemma coe_fn_coe (f : QF d) : ⇑(f : quadratic_form (fin 2) ℤ) = f := rfl

lemma QF_coe_fn_symmetric (f : QF d) (i j : fin 2) : f i j = f j i := coe_fn_symmetric f

instance : mul_action SL₂ℤ (QF d) :=
⟨ λ f, subtype.ext.mpr (matrix_action_identity f),
  λ M N f, subtype.ext.mpr (matrix_action_mul M N f) ⟩

-- TODO: better name!
def Γ_infinity : set SL₂ℤ := { M | ∃ m, M 0 0 = 1 ∧ M 0 1 = m ∧ M 1 0 = 0 ∧ M 1 1 = 1 }

@[simp] lemma fin.one : (fin.succ 0 : fin 2) = 1 := rfl

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

lemma val_0_0_pos {f : QF d} (h : is_positive_definite f) : 0 < f 0 0 :=
begin
  convert h (λ i, if 0 = i then 1 else 0) _,
  { exact (eval_basis f.val 0).symm },
  intro eq_0,
  simpa using congr_fun eq_0 0,
end

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
abs (f 1 0) ≤ f 0 0 ∧ f 0 0 ≤ f 1 1 ∧ ((abs (f 1 0) = f 0 0 ∨ f 0 0 = f 1 1) → f 1 0 ≥ 0)

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

lemma int.nat_abs_pos {a : ℤ} (ha : 0 < a) : (↑(a.nat_abs) : ℤ) = a :=
calc (↑(a.nat_abs) : ℤ) = a.sign * a.nat_abs : by simp [int.sign_eq_one_of_pos ha]
                    ... = a : int.sign_mul_nat_abs a

lemma int.nat_abs_of_neg {a : ℤ} (ha : a < 0) : (↑(a.nat_abs) : ℤ) = -a :=
calc (↑(a.nat_abs) : ℤ) = -(a.sign * a.nat_abs) : by simp [int.sign_eq_neg_one_of_neg ha]
                    ... = -a : by rw int.sign_mul_nat_abs a

lemma int.nat_abs_le_of_pos {a b : ℤ} (ha : 0 < a) (h : a ≤ b) : a.nat_abs ≤ b.nat_abs :=
int.coe_nat_le.mp (by { convert h; apply int.nat_abs_pos; linarith })

lemma int.nat_abs_lt_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : a < b ↔ a.nat_abs < b.nat_abs :=
by { convert int.coe_nat_lt; apply eq.symm; apply int.nat_abs_pos; assumption }

lemma int.nat_abs_eq : Π {a b : ℤ}, a.nat_abs = b.nat_abs ↔ abs a = abs b :=
by simp [int.abs_eq_nat_abs]

lemma int.nat_abs_lt {a b : ℤ} (h : abs a < abs b) : a.nat_abs < b.nat_abs :=
by simpa [int.abs_eq_nat_abs] using h

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
  { calc f 0 0 = (f 0 0).nat_abs : (int.nat_abs_pos (val_0_0_pos hf)).symm
           ... = (reduced_order_key ⟨f, _⟩).fst : rfl
           ... = (reduced_order_key ⟨g, _⟩).fst : by rw h
           ... = (g 0 0).nat_abs : rfl
           ... = g 0 0 : int.nat_abs_pos (val_0_0_pos hg) },
  { calc f 0 1 = f 1 0 : coe_fn_symmetric f
           ... = g 1 0 : this
           ... = g 0 1 : coe_fn_symmetric g },
  { exact this },
  { calc f 1 1 = (f 1 1).nat_abs : (int.nat_abs_pos (val_1_1_pos hf)).symm
           ... = (reduced_order_key ⟨f, _⟩).snd.snd.snd : rfl
           ... = (reduced_order_key ⟨g, _⟩).snd.snd.snd : by rw h
           ... = (g 1 1).nat_abs : rfl
           ... = g 1 1 : int.nat_abs_pos (val_1_1_pos hg) }
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

/-- `swap_x_y` is a matrix whose action swaps the coefficient for `x²` and `y²` -/
def swap_x_y : SL₂ℤ := ⟨![![0, -1], ![1, 0]], rfl⟩

lemma swap_x_y_smul (f : QF d) :
  (matrix_action swap_x_y f : M₂ℤ) = ![![0, -1], ![1, 0]] ⬝ f ⬝ ![![0, 1], ![-1, 0]] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma swap_x_y_smul_0_0 (f : QF d) : matrix_action swap_x_y f 0 0 = f 1 1 :=
by simp [swap_x_y_smul]

lemma swap_x_y_smul_1_0 (f : QF d) : (matrix_action swap_x_y f) 1 0 = - f 1 0 :=
by { simp [swap_x_y_smul, QF_coe_fn_symmetric f 0 1], refl }

lemma swap_x_y_lt {f : QF d} (hc : 0 < f 1 1) (h : f 1 1 < f 0 0) : (swap_x_y • f) < f :=
prod.lex.left _ _ _ (by { convert ((int.nat_abs_lt_of_pos hc (by linarith)).mp h), simp [swap_x_y_smul_0_0 f] })

lemma swap_x_y_lt_of_eq_of_neg {f : QF d} (hac : f 0 0 = f 1 1) (hb : f 1 0 < 0) : (swap_x_y • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  (by { simp [reduced_order_key, swap_x_y_smul_0_0, hac.symm] }),
  (prod.lex_def _ _).mpr (or.inr ⟨
    (by { simp [reduced_order_key, swap_x_y_smul_1_0] }),
    prod.lex.left _ _ _ (by { simp [swap_x_y_smul_1_0, sign'_of_neg hb, sign'_of_pos (neg_pos.mpr hb)], exact dec_trivial }) ⟩ ) ⟩ )

/-- `change_xy k` changes the coefficient for `xy` while keeping the coefficient for `x²` the same -/
def change_xy (k : ℤ) : SL₂ℤ := ⟨![![1, 0], ![k, 1]], sorry⟩

lemma change_xy_smul (k : ℤ) (f : QF d) :
  (⇑(change_xy k • f) : M₂ℤ) = ![![1, 0], ![k, 1]] ⬝ f ⬝ ![![1, k], ![0, 1]] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma change_xy_smul_0_0 (k : ℤ) (f : QF d) : (change_xy k • f) 0 0 = f 0 0 :=
by { simp [change_xy_smul] }

lemma change_xy_smul_1_0 (k : ℤ) (f : QF d) : (change_xy k • f) 1 0 = k * f 0 0 + f 1 0 :=
by { simp [change_xy_smul], refl }

lemma change_xy_lt_abs {f : QF d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) < abs (f 1 0)) : (change_xy k • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  (by rw [reduced_order_key, reduced_order_key, change_xy_smul_0_0 k f]),
  prod.lex.left _ _ _ (by { convert int.nat_abs_lt h, rw change_xy_smul_1_0 k f }) ⟩ )

lemma change_xy_lt_sign {f : QF d} {k : ℤ} (h : abs (k * f 0 0 + f 1 0) = abs (f 1 0)) (h2 : sign' (k * f 0 0 + f 1 0) < sign' (f 1 0)) : (change_xy k • f) < f :=
(prod.lex_def _ _).mpr (or.inr ⟨
  (by rw [reduced_order_key, reduced_order_key, change_xy_smul_0_0 k f]),
  (prod.lex_def _ _).mpr (or.inr ⟨
    (by rw [reduced_order_key, reduced_order_key, change_xy_smul_1_0, int.nat_abs_eq, h]),
    prod.lex.left _ _ _ (by { rw change_xy_smul_1_0 k f, exact h2 }) ⟩ ) ⟩ )

/-- Together with `div_mul_le`, we have that `(a / b) * b ∈ ]a-b, a]` -/
lemma int.lt_div_mul (a : ℤ) {b : ℤ} (hb : 0 < b) : a - b < (a / b) * b :=
calc a - b < a - a % b : sub_lt_sub_of_le_of_lt (le_refl a) (int.mod_lt_of_pos _ hb)
       ... = a - (a - b * (a / b)) : by rw int.mod_def
       ... = a / b * b : by ring

lemma a_le_c_of_min {f : QF d} (hf : is_positive_definite f) (min : ∀ (g : QF d), g ∈ mul_action.orbit (special_linear_group (fin 2) ℤ) f → ¬g < f) : f 0 0 ≤ f 1 1 :=
le_of_not_gt (λ c_lt_a, min (swap_x_y • f) ⟨_, rfl⟩ (swap_x_y_lt (val_1_1_pos hf) c_lt_a))

lemma b_le_a_of_min {f : QF d} (hf : is_positive_definite f) (min : ∀ (g : QF d), g ∈ mul_action.orbit (special_linear_group (fin 2) ℤ) f → ¬g < f) : abs (f 1 0) ≤ f 0 0 :=
have a_pos : 0 < f 0 0 := val_0_0_pos hf,
le_of_not_gt (λ a_lt_b, min (change_xy ((f 0 0 - f 1 0) / f 0 0) • f) ⟨_, rfl⟩ begin
  refine change_xy_lt_abs (abs_lt.mpr (and.intro _ _)),
  { apply lt_of_lt_of_le _ (add_le_add_right (le_of_lt (int.lt_div_mul _ a_pos)) _),
    linarith },
  { apply lt_of_le_of_lt (add_le_add_right (int.div_mul_le _ (ne_of_gt a_pos)) _),
    linarith }
end )

lemma int.ge_one_of_pos : ∀ {a : ℤ}, a > 0 → a ≥ 1
| 0 ha := by linarith
| (nat.succ n) ha := by linarith
| -[1+ n ] ha := by linarith

/-- Setting `x = 2 * m^2`, `y = 2 * n^2`, we have `sqrt (x * y) ≤ (x + y) / 2` -/
lemma int.am_gm_inequality (m n : ℤ) : 2 * abs m * abs n ≤ m^2 + n^2 :=
have pow_sub : 0 ≤ (m - n)^2 := pow_two_nonneg _,
have pow_add : 0 ≤ (m + n)^2 := pow_two_nonneg _,
begin
  cases le_total 0 m with hm hm; cases le_total 0 n with hn hn;
    rw [abs_of_nonneg hm] <|> rw [abs_of_nonpos hm];
    rw [abs_of_nonneg hn] <|> rw [abs_of_nonpos hn],
  { convert add_le_add_left pow_sub (2 * m * n) using 1; ring },
  { convert sub_le_sub_right pow_add (2 * m * n) using 1; ring },
  { convert sub_le_sub_right pow_add (2 * m * n) using 1; ring },
  { convert add_le_add_left pow_sub (2 * m * n) using 1; ring },
end

lemma abs_squared (a : ℤ) : (abs a)^2 = a^2 := sorry

lemma min_of_reduced_aux {a b c m n : ℤ} (hmn : abs m ≠ abs n) (ha : 0 ≤ a) (hba : abs b ≤ a) (hac : a ≤ c) :
  a ≤ a * m^2 + 2 * b * m * n + c * n^2 :=
have msq_nonneg : _ := pow_two_nonneg m,
have nsq_nonneg : _ := pow_two_nonneg n,
calc a = a * 1 : (mul_one _).symm
   ... ≤ a * (m^2 + n^2 - 2 * abs m * abs n) :
     mul_le_mul_of_nonneg_left (int.ge_one_of_pos begin
       convert lt_of_le_of_ne (pow_two_nonneg (abs m - abs n)) (pow_ne_zero 2 _).symm using 1,
       rw [← abs_squared m, ←abs_squared n],
     end) ha
   ... = a * (m^2 + n^2) - 2 * abs m * abs n * a : by ring
   ... ≤ a * (m^2 + n^2) - 2 * abs m * abs n * abs b :
     sub_le_sub_left (mul_le_mul_of_nonneg_left hba (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))) _
   ... = a * (m^2 + n^2) + - (2 * abs m * abs n * abs b) : sub_eq_add_neg _ _
   ... ≤ a * (m^2 + n^2) + 2 * m * n * b :
     begin
       apply add_le_add_left,
       cases le_total 0 m with hm hm; cases le_total 0 n with hn hn;
        cases le_total 0 b with hb hb;
        rw [abs_of_nonneg hm] <|> rw [abs_of_nonpos hm];
        rw [abs_of_nonneg hn] <|> rw [abs_of_nonpos hn];
        rw [abs_of_nonneg hb] <|> rw [abs_of_nonpos hb];
        sorry
     end
   ... = a * m^2 + 2 * b * m * n + a * n^2 : by ring
   ... ≤ a * m^2 + 2 * b * m * n + c * n^2 :
     add_le_add_left (mul_le_mul_of_nonneg_right hac nsq_nonneg) _

lemma min_of_reduced {f : QF d} (hf : is_positive_definite f) (f_red : is_reduced f) :
  ∀ (g : QF d), g ∈ mul_action.orbit (special_linear_group (fin 2) ℤ) f → ¬ g < f :=
begin
  cases f with f,
  rcases f_red with ⟨b_lt_a, a_lt_c, strict⟩,
  have fa_pos : 0 < f 0 0 := val_0_0_pos hf,
  have fc_pos : 0 < f 1 1 := val_1_1_pos hf,

  rintros ⟨g, _⟩ ⟨N, hN⟩ g_lt_f,
  have ga_pos : 0 < g 0 0 := a_pos_of_mem_orbit_pos_def hf ⟨N, hN⟩,
  have gc_pos : 0 < g 1 1 := c_pos_of_mem_orbit_pos_def hf ⟨N, hN⟩,

  have : matrix_action N f = g := congr_arg subtype.val hN,
  have : g 0 0 = f 0 0 * N 0 0 ^ 2 + 2 * f 1 0 * N 0 0 * N 0 1 + f 1 1 * N 0 1 ^ 2,
  { rw ← this, sorry },

  rcases (prod.lex_def _ _).mp g_lt_f with a_lt | ⟨a_eq, b_lt⟩,
  { have a_lt := (int.nat_abs_lt_of_pos ga_pos fa_pos).mpr a_lt,
    rw this at a_lt,
    by_cases N 0 0 = 0,
    { sorry },
    have : N 0 0 ≥ 1 := sorry,
    linarith },
  { sorry },
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
  have b_le_a : abs (f_min 1 0) ≤ f_min 0 0 := b_le_a_of_min hf_min min',
  have a_le_c : f_min 0 0 ≤ f_min 1 1 := a_le_c_of_min hf_min min',

  use f_min,
  use ⟨M, hM⟩,

  { use b_le_a,
    use a_le_c,
    rintros (abs_b_eq_a | a_eq_c); apply le_of_not_gt; intro b_neg,
    { have b_eq_neg_a : f_min 1 0 = - f_min 0 0,
      { rw [←abs_b_eq_a, abs_of_neg b_neg, neg_neg] },
      have change_xy_b_eq : 2 * f_min 0 0 + f_min 1 0 = f_min 0 0,
      { rw [b_eq_neg_a], ring },
      apply min' (change_xy _ • f_min) ⟨_, rfl⟩,
      apply change_xy_lt_sign; rw [change_xy_b_eq],
      { rw [abs_b_eq_a, abs_of_pos a_pos] },
      rw [sign'_of_pos a_pos, sign'_of_neg b_neg],
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

#lint

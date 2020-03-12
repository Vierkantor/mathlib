import data.int.gcd
import data.zsqrtd.basic
import data.matrix.basic
import group_theory.group_action
import group_theory.quotient_group
import linear_algebra.special_linear_group
import number_theory.class_group
import order.basic
import tactic.fin_cases
import tactic.linarith

/-! Computing the class number for quadratic number fields -/

universes u v

open_locale matrix
open finset

-- TODO: use nicer matrix notation
notation `M₂ℤ` := matrix (fin 2) (fin 2) ℤ
notation `SL₂ℤ` := matrix.special_linear_group (fin 2) ℤ
namespace matrix.special_linear_group
def α (M : SL₂ℤ) : ℤ := M.1 0 0
def β (M : SL₂ℤ) : ℤ := M.1 0 1
def γ (M : SL₂ℤ) : ℤ := M.1 1 0
def δ (M : SL₂ℤ) : ℤ := M.1 1 1

variables (M N : SL₂ℤ)

@[simp] lemma α_mul : (M * N).α = M.α * N.α + M.β * N.γ :=
by { have : (M * N).α = M.α * N.α + (M.β * N.γ + 0) := rfl, simp [this] }
@[simp] lemma β_mul : (M * N).β = M.α * N.β + M.β * N.δ :=
by { have : (M * N).β = M.α * N.β + (M.β * N.δ + 0) := rfl, simp [this] }
@[simp] lemma γ_mul : (M * N).γ = M.γ * N.α + M.δ * N.γ :=
by { have : (M * N).γ = M.γ * N.α + (M.δ * N.γ + 0) := rfl, simp [this] }
@[simp] lemma δ_mul : (M * N).δ = M.γ * N.β + M.δ * N.δ :=
by { have : (M * N).δ = M.γ * N.β + (M.δ * N.δ + 0) := rfl, simp [this] }

@[simp] lemma α_inv : (M⁻¹).α = M.δ :=
by { have : (M⁻¹).α = (1 * (1 * (M.δ * 1))) + (((-1) * (M.γ * 0)) + 0) := rfl, simp [this] }
@[simp] lemma β_inv : (M⁻¹).β = -M.β :=
by { have : (M⁻¹).β = (1 * (M.α * 0)) + (((-1) * (1 * (M.β * 1))) + 0) := rfl, simp [this] }
@[simp] lemma γ_inv : (M⁻¹).γ = -M.γ :=
by { have : (M⁻¹).γ = (1 * (0 * (M.δ * 1))) + (((-1) * (M.γ * 1)) + 0) := rfl, simp [this] }
@[simp] lemma δ_inv : (M⁻¹).δ = M.α :=
by { have : (M⁻¹).δ = (1 * (M.α * 1)) + (((-1) * (0 * (M.β * 1))) + 0) := rfl, simp [this] }

lemma det_2x2 {α} [comm_ring α] (M : matrix (fin 2) (fin 2) α) :
M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := calc
M.det = (0 + 1) * (M 0 0 * (M 1 1 * 1)) + ((- (0 + 1) * (M 1 0 * (M 0 1 * 1))) + 0) : refl _
... = M 0 0 * M 1 1 - M 0 1 * M 1 0 : by ring

end matrix.special_linear_group

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

/--
  The action of a matrix `M` is the same as the action of `-M`.
-/
lemma action_neg_invariant (M : matrix n n α) (f : quadratic_form n α) : -M · f = M · f :=
by simp [matrix_action]

/--
  The action works by multiplying vectors with the matrix.
-/
@[simp] lemma eval_action (M : matrix n n α) (f : quadratic_form n α) (x : n → α) :
  eval (M · f) x = eval f (M.vec_mul x) :=
by simp [eval, matrix_action, row_vec_mul, col_vec_mul, matrix.mul_assoc]

/--
  The identity matrix gives the identity action.
-/
@[simp] lemma matrix_action_identity [decidable_eq n] (f : quadratic_form n α) :
  matrix_action 1 f = f :=
by simp [matrix_action]

/--
  Applying the product of two matrices is the same as applying the matrices consecutively.
-/
@[simp]
lemma matrix_action_mul (M N : matrix n n α) (f : quadratic_form n α) :
  (M ⬝ N) · f = M · (N · f) :=
by simp [matrix_action, matrix.mul_assoc]

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

instance : mul_action SL₂ℤ (QF d) :=
⟨ λ f, subtype.ext.mpr (by rw [smul_val, special_linear_group.one_val, matrix_action_identity]),
λ M N f, subtype.ext.mpr (by { simp, refl }) ⟩

-- TODO: better name!
def Γ_infinity : set SL₂ℤ := { M | ∃ m, M.α = 1 ∧ M.β = m ∧ M.γ = 0 ∧ M.δ = 1 }

instance : is_submonoid Γ_infinity :=
⟨⟨0, by finish⟩, λ a b ⟨ma, ha⟩ ⟨mb, hb⟩, ⟨ma + mb, by { cases ha, cases hb, split; simp [add_comm, *] }⟩⟩
instance : is_subgroup Γ_infinity :=
⟨λ a ⟨ma, ha⟩, ⟨-ma, by { cases ha, split; simp * }⟩⟩

instance subset_has_scalar {α β} [monoid α] [has_scalar α β] (s : set α) : has_scalar s β := ⟨λ s b, s.1 • b⟩
def submonoid_mul_action {α β} [monoid α] [mul_action α β] (s : set α) [is_submonoid s] : mul_action s β :=
⟨one_smul α, λ x y, @_root_.mul_smul α _ _ _ x.1 y.1⟩

/-- Quadratic forms are considered equivalent if they share the same orbit modulo Γ_infinity. -/
def quadratic_class_group (d : ℤ) : Type :=
quotient (@mul_action.orbit_rel Γ_infinity (QF d) _ (submonoid_mul_action _))

end class_number

section reduced

variables [ordered_ring α] {d : ℤ}

def is_positive_definite (M : quadratic_form n α) : Prop := ∀ x ≠ 0, eval M x > 0

def is_reduced (f : quadratic_form (fin 2) ℤ) : Prop :=
abs (f 1 0) ≤ f 0 0 ∧ f 0 0 ≤ f 1 1 ∧ ((abs (f 1 0) = f 0 0 ∨ f 0 0 = f 1 1) → f 1 0 ≥ 0)

/-- In each orbit, there is a unique reduced quadratic form -/
lemma unique_reduced_mem_orbit (M : QF d) :
  ∃! (f : QF d), f ∈ mul_action.orbit SL₂ℤ M ∧ is_reduced f :=
begin
  have : well_founded (function.on_fun (<) (λ (f : QF d), f 0 0)),
  { sorry },
  obtain ⟨f, ⟨N, hf⟩, min⟩ := @well_founded.has_min _ (function.on_fun (<) (λ (f : QF d), f 0 0)) this (mul_action.orbit SL₂ℤ M) ⟨M, mul_action.orbit_eq_iff.mp rfl⟩,
  use f,
  use ⟨N, hf⟩,
  { by_cases c_lt_a : f 1 1 < f 0 0,
    { exfalso,
      let N' : SL₂ℤ := ⟨![![0, -1], ![1, 0]], sorry⟩,
      let f' : QF d := N' • f,
      have : f' ∈ mul_action.orbit SL₂ℤ M :=
      ⟨ N' * N, trans (_root_.mul_smul N' N M) (congr_arg _ hf) ⟩,
      apply min f' this,
      sorry },
    by_cases a_lt_b : f 0 0 < abs (f 1 0),
    { exfalso,
      sorry },
    split,
    { sorry },
    split,
    { apply le_of_not_gt c_lt_a },
    sorry },
  rintros g ⟨g_mem_orbit, g_is_reduced⟩,
  have := min g g_mem_orbit,
  sorry
end

end reduced

end quadratic_form

#lint

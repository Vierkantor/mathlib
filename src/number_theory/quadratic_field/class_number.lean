import algebra.gcd_domain
import data.zsqrtd.basic
import data.int.modeq
import data.matrix.notation
import data.nat.modeq
import group_theory.group_action
import group_theory.quotient_group
import linear_algebra.quadratic_form
import linear_algebra.special_linear_group
import order.lattice
import order.lexicographic
import tactic.fin_cases
import tactic.linarith
import tactic.omega

/-! Computing the class number for quadratic number fields -/

universes u v

open_locale matrix
open_locale rat
open finset
open matrix

section to_other_files

@[simp] lemma fin.one {n : ℕ} : (fin.succ 0 : fin n.succ.succ) = 1 := rfl
@[simp] lemma fin.default_one : (default (fin 1)) = 0 := rfl

lemma int.nat_abs_of_pos {a : ℤ} (ha : 0 < a) : (↑(a.nat_abs) : ℤ) = a :=
int.nat_abs_of_nonneg (le_of_lt ha)

@[norm_cast, simp]
lemma int.coe_nat_abs_eq_abs {a : ℤ} : (a.nat_abs : ℤ) = abs a :=
by rw [int.abs_eq_nat_abs]

lemma fin.one_of_two : (fin.succ 0 : fin 2) = 1 := rfl

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

@[simp] lemma int.units_abs (u : units ℤ) : abs (u : ℤ) = (1 : ℤ) :=
int.nat_abs_eq_iff_abs_eq.mp (int.units_nat_abs u)

section to_int_vector

variables {n : Type*} [fintype n]

def common_denom (x : n → ℚ) : ℤ := finset.univ.fold lcm 1 (λ (i : n), (x i).denom)

lemma common_denom_nonzero (x : n → ℚ) : common_denom x ≠ 0 :=
begin
  haveI : decidable_eq n := λ _ _, classical.prop_decidable _,
  apply @finset.induction _ (λ s, s.fold (@lcm ℤ _) 1 (λ i, (x i).denom) ≠ 0),
  { simp },
  intros i s hi hs h,
  rw fold_insert hi at h,
  obtain xi_zero | lcm_zero := (lcm_eq_zero_iff _ _).mp h,
  { apply ne_of_lt (x i).3,
    exact_mod_cast xi_zero.symm },
  exact hs lcm_zero,
end

lemma dvd_fold_lcm {t : finset n} (f : n → ℤ) {i : n} (hi : i ∈ t) : f i ∣ t.fold lcm 1 f :=
begin
  haveI : decidable_eq n := λ _ _, classical.prop_decidable _,
  convert dvd_lcm_left (f i) ((t.erase i).fold lcm 1 f),
  convert fold_insert (not_mem_erase _ _),
  exact (insert_erase hi).symm
end

def to_int_vector (x : n → ℚ) : n → ℤ := λ i, rat.num ((common_denom x : ℚ) * x i)

lemma denom_dvd_common_denom (x : n → ℚ) (i : n) :
  ↑(x i).denom ∣ common_denom x :=
dvd_fold_lcm _ (mem_univ _)

lemma gcd_common_denom_eq_self (x : n → ℚ) (i : n) :
  nat.gcd (int.nat_abs (common_denom x * (x i).num)) (x i).denom = (x i).denom :=
nat.gcd_eq_right (int.coe_nat_dvd.mp (int.dvd_nat_abs.mpr (dvd_mul_of_dvd_left (denom_dvd_common_denom _ _) _)))

lemma denom_eq_one (x : n → ℚ) (i : n) : ((common_denom x : ℚ) * x i).denom = 1 :=
by simp [rat.mul_denom, gcd_common_denom_eq_self, nat.div_self (x i).3]

@[simp]
lemma common_denom_mul_num_div_denom (x : n → ℚ) (i : n) :
  ↑(common_denom x * (x i).num / (x i).denom) = ↑(common_denom x) * x i :=
begin
  suffices : (↑(common_denom x * (x i).num / ↑((x i).denom)) : ℚ) = ↑(common_denom x) * ((x i).num /. (x i).denom),
  { rw [this, rat.num_denom] },
  rw [rat.coe_int_eq_mk, rat.coe_int_eq_mk, rat.mul_def, one_mul],
  apply (rat.mk_eq _ _).mpr,
  rw [mul_one, mul_comm (common_denom x), int.mul_div_assoc _ (denom_dvd_common_denom x i), mul_assoc],
  congr,
  apply int.div_mul_cancel (denom_dvd_common_denom x i),
  all_goals { norm_num },
  all_goals { exact ne.symm (ne_of_lt (x i).3) },
end

lemma num_eq_self (x : n → ℚ) (i : n) : ↑((common_denom x : ℚ) * x i).num = (common_denom x : ℚ) * x i :=
by simp [rat.mul_num, gcd_common_denom_eq_self]

lemma coe_to_int_vector (x : n → ℚ) : coe ∘ to_int_vector x = (common_denom x : ℚ) • x :=
by { ext i, simp [to_int_vector, num_eq_self] }

lemma eq_int_vector_div_denom (x : n → ℚ) :
  x = (common_denom x : ℚ)⁻¹ • (coe ∘ to_int_vector x) :=
begin
  ext i,
  rw [coe_to_int_vector, ←_root_.mul_smul, inv_mul_cancel, one_smul],
  exact_mod_cast common_denom_nonzero x
end

lemma to_int_vector_eq_zero {x : n → ℚ} {i : n} : to_int_vector x i = 0 ↔ x i = 0 :=
⟨ λ h, (mul_eq_zero.mp (rat.zero_iff_num_zero.mpr h)).elim (λ h, false.elim (common_denom_nonzero x (by exact_mod_cast h))) id,
  λ h, (by simp [to_int_vector, h]) ⟩
end to_int_vector

end to_other_files

/-
structure int_bin_quadratic_form :=
(val : quadratic_form ℚ (fin 2 → ℚ))
(is_int : ∀ x : fin 2 → ℚ, (∀ i, ∃ (y : ℤ), x i = y) → ∃ y : ℤ, val x = y )
-/

-- Shorter notation for the case with 2 variables and integer coefficients.
notation `M₂ℤ` := matrix (fin 2) (fin 2) ℤ
notation `SL₂ℤ` := matrix.special_linear_group (fin 2) ℤ
notation `SL₂ℚ` := matrix.special_linear_group (fin 2) ℚ
notation `QF₂ℤ` := quadratic_form ℤ (fin 2 → ℤ)

namespace quadratic_form

variables {n : Type u} [fintype n] {R : Type v} {R₁ : Type v} [comm_ring R₁]
open quadratic_form

/-
lemma eq_iff {Q Q' : QF₂ℤ} : Q = Q' ↔ Q.val = Q'.val :=
by { cases Q, cases Q', split; intro h; congr; exact h }
-/

lemma num_eq_self_of_is_int {a : ℚ} (h : ∃ b : ℤ, a = b) : ↑a.num = a :=
by { cases h, rw [h_h, rat.coe_int_num] }

lemma denom_eq_one_of_is_int {a : ℚ} (h : ∃ b : ℤ, a = b) : a.denom = 1 :=
by { cases h, rw [h_h, rat.coe_int_denom] }

/-
lemma apply_val_int (Q : QF₂ℤ) (x y : ℤ) : ↑(Q.val ![ x, y ]).num = Q.val ![ x, y ] :=
num_eq_self_of_is_int (Q.is_int _ (λ i, by fin_cases i; simp))

lemma eq_of_eq_on_int (Q Q' : quadratic_form ℚ (n → ℚ))
  (h : ∀ (x : n → ℤ), Q (coe ∘ x) = Q' (coe ∘ x)) : Q = Q' :=
ext $ λ x, calc Q x
    = Q ((common_denom x : ℚ)⁻¹ • _) : congr_arg _ (congr_arg _ (eq_int_vector_div_denom x))
... = (common_denom x : ℚ)⁻¹ * (common_denom x : ℚ)⁻¹ * Q (coe ∘ to_int_vector x) : map_smul _ _
... = (common_denom x : ℚ)⁻¹ * (common_denom x : ℚ)⁻¹ * Q' _ : congr_arg _ (h (to_int_vector x))
... = Q' ((common_denom x : ℚ)⁻¹ • _) : (map_smul _ _).symm
... = Q' x : by rw [←eq_int_vector_div_denom x]
-/

@[simp] lemma apply_neg (Q : QF₂ℤ) (x y : ℤ) : Q ![-x, -y] = Q ![x, y] :=
begin
  rw ← map_neg,
  congr,
  convert trans (neg_insert (-x : ℤ) ![-y]) _; simp -- TODO: fix instance diamnond preventing us from just using `simp` here
end

lemma vector_2_eq (v : fin 2 → R) : ![v 0, v 1] = v :=
by ext i; fin_cases i; refl

lemma vector_2_is_int (v : fin 2 → ℚ) (is_int : ∀ i, ∃ (y : ℤ), v i = y) :
  ∃ (x y : ℤ), v = ![ x, y ] :=
begin
  obtain ⟨x, hx⟩ := is_int 0,
  obtain ⟨y, hy⟩ := is_int 1,
  use x,
  use y,
  rw [←hx, ←hy, vector_2_eq]
end

@[ext] lemma int_ext (Q Q' : QF₂ℤ) (h : ∀ x y, Q ![x, y] = Q' ![x, y]) : Q = Q' :=
begin
  cases Q,
  cases Q',
  congr,
  ext xy,
  convert h (xy 0) (xy 1);
    rw [vector_2_eq xy]
end

section of_tuple

#check algebra_int
@[simp] lemma smul_eq_mul'  : @algebra.to_semimodule _ _ _ _ (algebra_int ℤ) = semiring.to_semimodule := sorry

set_option pp.all true
def of_tuple (a b c : ℤ) : QF₂ℤ :=
{ to_fun := λ xy, xy 0 * xy 0 * a + xy 0 * xy 1 * b + xy 1 * xy 1 * c,
  to_fun_smul := λ s xy, by { simp_rw [pi.smul_apply, smul_eq_mul'] }, }
set_option pp.all false

lemma of_tuple_apply (a b c x y : ℤ) :
  of_tuple a b c ![x, y] = x * x * a + x * y * b + y * y * c :=
rfl

end of_tuple

section coeff
def coeff_a (Q : QF₂ℤ) : ℤ :=
Q ![1, 0]

def coeff_c (Q : QF₂ℤ) : ℤ :=
Q ![0, 1]

def coeff_b (Q : QF₂ℤ) : ℤ :=
Q ![1, 1] - Q ![1, 0] - Q ![0, 1]

@[simp] lemma coeff_a_of_tuple (a b c : ℤ) : coeff_a (of_tuple a b c) = a :=
by simp [coeff_a, of_tuple_apply]

@[simp] lemma coeff_b_of_tuple (a b c : ℤ) : coeff_b (of_tuple a b c) = b :=
by simp [coeff_b, of_tuple_apply]

@[simp] lemma coeff_c_of_tuple (a b c : ℤ) : coeff_c (of_tuple a b c) = c :=
by simp [coeff_c, of_tuple_apply]

@[simp] lemma basis_0_eq {R} [has_one R] [has_zero R] : (λ (n : fin 2), ite (n = 0) (1 : R) 0) = ![ 1, 0 ] :=
by { ext n, fin_cases n; refl }

@[simp] lemma basis_1_eq {R} [has_one R] [has_zero R] : (λ (n : fin 2), ite (n = 1) (1 : R) 0) = ![ 0, 1 ] :=
by { ext n, fin_cases n; refl }

@[simp] lemma of_tuple_coeff (Q : QF₂ℤ) :
  of_tuple (coeff_a Q) (coeff_b Q) (coeff_c Q) = Q :=
begin
  ext x y,
  rw apply_eq_num_val,
  congr' 1,
  rw [←to_matrix_right_inverse Q.val, of_tuple_val],
  apply congr_fun,
  congr,
  ext i j,
  rw [quadratic_form.to_matrix_apply, coeff_a, coeff_b, coeff_c],
  fin_cases i; fin_cases j,
  { rw quadratic_form.map_add_self, simp, ring },
  { simp [int.cast_sub], ring },
  { simp [int.cast_sub], ring },
  { rw quadratic_form.map_add_self, simp, ring }
end

lemma apply_val (Q : QF₂ℤ) (x y : ℤ) :
  Q x y = x * x * coeff_a Q + x * y * coeff_b Q + y * y * coeff_c Q :=
by rw [←of_tuple_apply, of_tuple_coeff]

@[simp] lemma to_matrix_of_tuple (a b c : ℤ) : to_matrix (of_tuple a b c).val = ![![a, b/2], ![b/2, c]] :=
to_matrix_left_inverse (by { ext i j, fin_cases i; fin_cases j; refl })

@[simp] lemma to_matrix_val_0_0 (Q : QF₂ℤ) : to_matrix Q.val 0 0 = coeff_a Q :=
by { rw [←of_tuple_coeff Q, coeff_a_of_tuple, to_matrix_of_tuple], refl }

@[simp] lemma to_matrix_val_0_1 (Q : QF₂ℤ) : to_matrix Q.val 0 1 = coeff_b Q / 2 :=
by { rw [←of_tuple_coeff Q, coeff_b_of_tuple, to_matrix_of_tuple], refl }

@[simp] lemma to_matrix_val_1_0 (Q : QF₂ℤ) : to_matrix Q.val 1 0 = coeff_b Q / 2 :=
by { rw [←of_tuple_coeff Q, coeff_b_of_tuple, to_matrix_of_tuple], refl }

@[simp] lemma to_matrix_val_1_1 (Q : QF₂ℤ) : to_matrix Q.val 1 1 = coeff_c Q :=
by { rw [←of_tuple_coeff Q, coeff_c_of_tuple, to_matrix_of_tuple], refl }

lemma eq_of_coeffs_eq {Q Q' : QF₂ℤ} :
  coeff_a Q = coeff_a Q' → coeff_b Q = coeff_b Q' → coeff_c Q = coeff_c Q' → Q = Q' :=
begin
  intros,
  rw [←of_tuple_coeff Q, ←of_tuple_coeff Q'],
  congr; assumption
end

lemma eq_iff_coeffs_eq {Q Q' : QF₂ℤ} :
  Q = Q' ↔ (coeff_a Q = coeff_a Q' ∧ coeff_b Q = coeff_b Q' ∧ coeff_c Q = coeff_c Q') :=
⟨λ h, by repeat { split }; congr; assumption, λ ⟨ha, hb, hc⟩, eq_of_coeffs_eq ha hb hc ⟩

lemma of_tuple_congr {a a' b b' c c' : ℤ} :
  of_tuple a b c = of_tuple a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
iff.trans eq_iff_coeffs_eq (by simp)

end coeff

instance : decidable_eq QF₂ℤ :=
λ Q Q', decidable_of_decidable_of_iff infer_instance eq_iff_coeffs_eq.symm

section discr
/-- The traditional definition of the discriminant of a quadratic form -/
def discr' (Q : QF₂ℤ) : ℤ := coeff_b Q * coeff_b Q - 4 * coeff_a Q * coeff_c Q

@[simp] lemma discr'_of_tuple (a b c : ℤ) : discr' (of_tuple a b c) = b * b - 4 * a * c :=
by rw [discr', coeff_a_of_tuple, coeff_b_of_tuple, coeff_c_of_tuple]

lemma discr'_eq_discr (Q : QF₂ℤ) : (discr' Q : ℚ) = -4 * Q.val.discr :=
calc (discr' Q : ℚ) = ↑(coeff_b Q * coeff_b Q - 4 * coeff_a Q * coeff_c Q) : rfl
                ... = coeff_b Q * coeff_b Q - 4 * coeff_a Q * coeff_c Q : by norm_cast
                ... = -4 * (coeff_a Q * coeff_c Q - ((coeff_b Q / 2) * (coeff_b Q / 2))) : by ring
                ... = -4 * (Q.val.to_matrix).det : by simp [det_2x2]
                ... = -4 * Q.val.discr : rfl

/-- This edition of the discriminant arises from "completing the square". -/
lemma four_coeff_a_mul_apply_eq (Q : QF₂ℤ) (x y : ℤ) :
  4 * coeff_a Q * Q x y = (2 * coeff_a Q * x + coeff_b Q * y)^2 - discr' Q * y^2 :=
by rw [apply_val, discr']; ring

/-
/-- A primitive quadratic form has no common divisor among its coefficients. -/
def is_primitive [gcd_domain α] (M : quadratic_form α (n → α)) : Prop :=
(univ : finset (n × n)).fold gcd (1 : α) (λ ⟨i, j⟩, M i j) = 1
-/
end discr

section matrix_action
instance : has_scalar M₂ℤ QF₂ℤ :=
⟨ λ M Q, ⟨ @has_scalar.smul (matrix (fin 2) (fin 2) ℚ) _ _ (λ i j, (M i j : ℚ)) Q.val,
           λ v is_int, Q.is_int _ (λ i,
             let ⟨x, y, hxy⟩ := vector_2_is_int v is_int
             in ⟨x * M 0 i + y * M 1 i, by simp [hxy] ⟩ ) ⟩ ⟩

@[simp] lemma smul_val (Q : QF₂ℤ) (M : M₂ℤ) :
  (M • Q).val = @has_scalar.smul (matrix (fin 2) (fin 2) ℚ) _ _ (λ i j, (M i j : ℚ)) Q.val :=
rfl

@[simp] lemma coe_fn_smul (Q : QF₂ℤ) (M : M₂ℤ) (x y : ℤ) :
  (M • Q) x y = Q (x * M 0 0 + y * M 1 0) (x * M 0 1 + y * M 1 1) :=
by { apply congr_arg rat.num, rw smul_val, simp [←vector_2_eq (λ i, (M 0 i : ℚ))] }

@[norm_cast, simp] lemma matrix.coe_mul (M N : matrix (fin 2) (fin 2) ℤ) :
  (λ i j, (↑((M ⬝ N) i j) : ℚ)) = (λ i j, M i j) ⬝ (λ i j, N i j) :=
by { ext i j, simp [matrix.mul_val] }

@[norm_cast, simp] lemma matrix.coe_one :
  (λ i j, (↑((1 : M₂ℤ) i j) : ℚ)) = (1 : matrix (fin 2) (fin 2) ℚ) :=
by { ext i j, by_cases i = j; simp [matrix.one_val, h] }

instance : mul_action M₂ℤ QF₂ℤ :=
{ mul_smul := λ M N Q, eq_iff.mpr (by { convert _root_.mul_smul _ _ Q.val, simp }),
  one_smul := λ Q, eq_iff.mpr (by simp) }

@[simp] lemma smul_coeff_a (M : M₂ℤ) (Q : QF₂ℤ) :
  coeff_a (M • Q) = Q (M 0 0) (M 0 1) :=
by simp [coeff_a]

@[simp] lemma smul_coeff_c (M : M₂ℤ) (Q : QF₂ℤ) :
  coeff_c (M • Q) = Q (M 1 0) (M 1 1) :=
by simp [coeff_c]

@[simp] lemma smul_coeff_b (M : M₂ℤ) (Q : QF₂ℤ) :
  coeff_b (M • Q) = Q (M 0 0 + M 1 0) (M 0 1 + M 1 1) - coeff_a (M • Q) - coeff_c (M • Q) :=
by simp [coeff_b]
end matrix_action

-- TODO: better name!
def QF (d : ℤ) := {Q : QF₂ℤ // discr' Q = d}

namespace QF

variable {d : ℤ}

instance : has_coe (QF d) QF₂ℤ := ⟨ λ Q, Q.1 ⟩

instance : has_coe_to_fun (QF d) := ⟨ λ Q, ℤ → ℤ → ℤ, λ Q, ⇑Q.1 ⟩

@[simp] lemma coe_fn_val (Q : QF d) : ⇑Q.val = ⇑Q := rfl

@[simp] lemma coe_fn_coe (Q : QF d) : ⇑(Q : QF₂ℤ) = @coe_fn _ (QF.has_coe_to_fun) Q := rfl

@[ext]
lemma ext {Q Q' : QF d} (h : ∀ x y, Q x y = Q' x y) : Q = Q' :=
by { cases Q, cases Q', congr, ext, apply h }

instance SL₂ℤ_to_SL₂ℚ : has_coe SL₂ℤ (special_linear_group (fin 2) ℚ) :=
⟨ λ M, ⟨ λ i j, ↑(M i j), by { cases M with M hM, rw det_2x2 at ⊢ hM, exact_mod_cast hM } ⟩ ⟩

@[simp] lemma coe_apply (M : SL₂ℤ) :
  ⇑(M : special_linear_group (fin 2) ℚ) = (λ i j, (M i j : ℚ)) :=
by { ext i j, refl }

instance : has_scalar SL₂ℤ (QF d) :=
⟨λ M Q,
  ⟨ M.1 • Q.1,
  trans ((@int.cast_inj ℚ _ _ _ _ _).mp
    (by erw [discr'_eq_discr, discr'_eq_discr, discr_invariant_for_SL Q.1.val M]))
      Q.2⟩⟩

@[simp] lemma coe_smul (M : SL₂ℤ) (Q : QF d) :
  ↑(M • Q) = @has_scalar.smul (matrix (fin 2) (fin 2) ℤ) (QF₂ℤ) _ (⇑ M) Q := rfl

@[simp] lemma coe_fn_smul (M : SL₂ℤ) (Q : QF d) (x y : ℤ) :
  (⇑(M • Q) : ℤ → ℤ → ℤ) x y = @has_scalar.smul (matrix (fin 2) (fin 2) ℤ) (QF₂ℤ) _ (⇑ M) Q x y :=
rfl

instance : mul_action SL₂ℤ (QF d) :=
⟨ λ Q, by { ext, rw [coe_fn_smul, special_linear_group.one_apply, one_smul, coe_fn_coe] },
  λ M N Q, by { ext, erw [coe_fn_smul, special_linear_group.mul_apply, _root_.mul_smul], refl } ⟩

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

section is_positive_definite

variables {Q Q' : QF₂ℤ}

example {a b : ℚ} (ha : 0 < b) : 0 < a * b → 0 < a := (zero_lt_mul_right ha).mp

lemma pos_def_val_iff : pos_def Q.val ↔ (∀ x y, x ≠ 0 ∨ y ≠ 0 → 0 < Q x y) :=
begin
  split; intro hpd,
  { intros x y hxy,
    apply rat.num_pos_iff_pos.mpr,
    apply hpd ![x, y],
    simpa [-not_and, not_and_distrib] using hxy },
  { intros xy hxy,
    apply (zero_lt_mul_left (show 0 < (common_denom xy : ℚ) * (common_denom xy : ℚ), from mul_self_pos (by exact_mod_cast common_denom_nonzero xy))).mp,
    apply rat.num_pos_iff_pos.mp,
    convert hpd (to_int_vector xy 0) (to_int_vector xy 1) _,
    { rw [vector_2_eq (coe ∘ to_int_vector xy), coe_to_int_vector, map_smul] },
    rw [←vector_2_eq xy, insert_nonzero_iff, insert_nonzero_iff] at hxy,
    simpa [to_int_vector_eq_zero] using hxy }
end

lemma pos_def_iff_of_discr_neg (hd : discr' Q < 0) : pos_def Q.val ↔ 0 < coeff_a Q :=
iff.trans pos_def_val_iff $ begin
  split; intro h,
  { apply h 1 0,
    norm_num },
  intros x y hxy,
  by_cases hy : y = 0,
  { convert mul_pos (mul_self_pos (hxy.resolve_right (not_not_intro hy))) h,
    simp [apply_val, h, hy] },
  apply (zero_lt_mul_left h).mp,
  apply (zero_lt_mul_left (show (0 : ℤ) < 4, by norm_num)).mp,
  rw [←mul_assoc, four_coeff_a_mul_apply_eq, pow_two, pow_two, sub_eq_add_neg, neg_mul_eq_neg_mul],
  apply add_pos_of_nonneg_of_pos (mul_self_nonneg (2 * coeff_a Q * x + _)),
  exact mul_pos (neg_pos.mpr hd) (mul_self_pos hy),
end

lemma not_pos_def (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0) (hQ : Q x y = 0) :
  ¬ pos_def Q.val :=
λ h, ne_of_lt (pos_def_val_iff.mp h x y hxy) hQ.symm

def pos_def_decidable_of_discr_nonpos (hd : discr' Q ≤ 0) : decidable (pos_def Q.val) :=
if d_eq_0 : discr' Q = 0
then if a_eq_0 : coeff_a Q = 0
  then is_false (not_pos_def 1 0 (by norm_num) (by simp [apply_val, a_eq_0]))
  else have 4 * coeff_a Q * coeff_c Q = coeff_b Q * coeff_b Q := (eq_of_sub_eq_zero d_eq_0).symm,
    is_false (not_pos_def (-2 * coeff_b Q) (4 * coeff_a Q)
      (or.inr (by norm_num [a_eq_0]))
      (by { simp [apply_val, mul_assoc, this], ring }))
else decidable_of_iff _ (pos_def_iff_of_discr_neg (lt_of_le_of_ne hd d_eq_0)).symm

lemma coeff_a_pos (hpd : pos_def Q.val) : 0 < coeff_a Q :=
pos_def_val_iff.mp hpd 1 0 (by norm_num)

lemma coeff_c_pos (hpd : pos_def Q.val) : 0 < coeff_c Q :=
pos_def_val_iff.mp hpd 0 1 (by norm_num)

@[simp] lemma matrix.mul_vec_transpose {m} [fintype m] (M : matrix m n R₁) (x) :
  mul_vec Mᵀ x = vec_mul x M :=
by { ext i, unfold mul_vec vec_mul, simp_rw [transpose_val, dot_product_comm] }

lemma pos_def_smul_SL (M : SL₂ℤ) (h : pos_def Q.val) :
  pos_def (M.val • Q).val :=
λ x hx, h _ (λ (he : (to_lin (λ i j, (M.val i j : ℚ))ᵀ).to_fun x = 0), hx
  (special_linear_group.vec_mul_injective (show vec_mul x ↑M = vec_mul 0 ↑M, by simpa using he)) )
end is_positive_definite

/-- A bundled version of `positive definite integer binary quadratic form with discriminant d'. -/
structure pos_def_QF₂ℤ (d : ℤ) :=
(form : QF₂ℤ)
(discr_eq : discr' form = d)
(pos_def : pos_def form.val)

variable {d : ℤ}

namespace pos_def_QF₂ℤ

instance : has_coe (pos_def_QF₂ℤ d) QF₂ℤ :=
⟨ λ Q, Q.form ⟩

instance : has_coe_to_fun (pos_def_QF₂ℤ d) :=
{ F := λ Q, ℤ → ℤ → ℤ,
  coe := λ Q, ⇑(Q.form) }

@[ext]
lemma ext : Π (Q Q' : pos_def_QF₂ℤ d), (∀ x y, Q x y = Q' x y) → Q = Q' :=
λ ⟨Q, _, _⟩ ⟨Q', _, _⟩ h, by { congr, ext, exact h x y }

@[simp] lemma form_eq_coe (Q : pos_def_QF₂ℤ d) : Q.form = ↑Q := rfl

lemma discr_coe (Q : pos_def_QF₂ℤ d) : discr' Q = d := Q.discr_eq

instance : has_scalar SL₂ℤ (pos_def_QF₂ℤ d) :=
⟨ λ M Q,
  ⟨ M.val • Q.form,
    trans ((@int.cast_inj ℚ _ _ _ _ _).mp
            (by erw [discr'_eq_discr, discr'_eq_discr, discr_invariant_for_SL Q.form.val M]))
          Q.discr_eq,
    pos_def_smul_SL M Q.pos_def ⟩ ⟩

@[simp] lemma coe_fn_coe (Q : pos_def_QF₂ℤ d) : ⇑(Q : QF₂ℤ) = Q := rfl

@[simp] lemma coe_fn_smul (Q : pos_def_QF₂ℤ d) (M : SL₂ℤ) :
  ⇑ (M • Q) = @has_scalar.smul M₂ℤ QF₂ℤ _ M Q := rfl

instance : mul_action SL₂ℤ (pos_def_QF₂ℤ d) :=
{ one_smul := λ Q, by { ext, simp },
  mul_smul := λ M N Q, by { ext, rw [coe_fn_smul, special_linear_group.mul_apply, ←matrix.mul_eq_mul, _root_.mul_smul], refl } }

instance : setoid (pos_def_QF₂ℤ d) :=
mul_action.orbit_rel SL₂ℤ (pos_def_QF₂ℤ d)

lemma eq_of_coeffs_eq {Q Q' : pos_def_QF₂ℤ d} :
  coeff_a Q = coeff_a Q' → coeff_b Q = coeff_b Q' → coeff_c Q = coeff_c Q' → Q = Q' :=
begin
  intros ha hb hc,
  cases Q,
  cases Q',
  congr,
  apply eq_of_coeffs_eq; assumption
end

@[simp] lemma coe_smul (Q : pos_def_QF₂ℤ d) (M : SL₂ℤ) :
  (↑(M • Q) : QF₂ℤ) = @has_scalar.smul M₂ℤ QF₂ℤ _ ⇑M Q :=
rfl

lemma apply_val (Q : pos_def_QF₂ℤ d) (x y : ℤ) :
  Q x y = x * x * coeff_a Q + x * y * coeff_b Q + y * y * coeff_c Q :=
int_bin_quadratic_form.apply_val Q x y

end pos_def_QF₂ℤ

structure is_reduced (Q : QF₂ℤ) : Prop :=
(abs_b_le_a : abs (coeff_b Q) ≤ coeff_a Q)
(a_le_c : coeff_a Q ≤ coeff_c Q)
(b_nonneg_left : abs (coeff_b Q) = coeff_a Q → 0 ≤ coeff_b Q)
(b_nonneg_right : coeff_a Q = coeff_c Q → 0 ≤ coeff_b Q)

lemma is_reduced_iff (Q : QF₂ℤ) :
  is_reduced Q ↔ (abs (coeff_b Q) ≤ coeff_a Q ∧
                  coeff_a Q ≤ coeff_c Q ∧
                  (abs (coeff_b Q) = coeff_a Q → 0 ≤ coeff_b Q) ∧
                  (coeff_a Q = coeff_c Q → 0 ≤ coeff_b Q)) :=
⟨λ ⟨hba, hac, hbl, hbr⟩, ⟨hba, hac, hbl, hbr⟩, λ ⟨hba, hac, hbl, hbr⟩, ⟨hba, hac, hbl, hbr⟩⟩

lemma is_reduced_of_tuple_iff {a b c : ℤ} :
  is_reduced (of_tuple a b c) ↔ abs b ≤ a ∧ a ≤ c ∧ (abs b = a → 0 ≤ b) ∧ (a = c → 0 ≤ b) :=
iff.trans (is_reduced_iff _) (by simp)

instance : decidable_pred is_reduced :=
λ Q, decidable_of_decidable_of_iff infer_instance (is_reduced_iff Q).symm

lemma is_reduced.coeff_a_nonneg {Q : QF₂ℤ} (hr : is_reduced Q) :
  0 ≤ coeff_a Q :=
le_trans (abs_nonneg _) hr.abs_b_le_a

lemma is_reduced.coeff_c_nonneg {Q : QF₂ℤ} (hr : is_reduced Q) :
  0 ≤ coeff_c Q :=
le_trans hr.coeff_a_nonneg hr.a_le_c

lemma is_reduced.abs_b_le_c {Q : QF₂ℤ} (hr : is_reduced Q) :
  abs (coeff_b Q) ≤ coeff_c Q :=
le_trans hr.abs_b_le_a hr.a_le_c

lemma is_reduced.b_eq_a_of_c_le_abs_b {Q : QF₂ℤ} (hr : is_reduced Q)
  (h : coeff_c Q ≤ abs (coeff_b Q)) : coeff_b Q = coeff_a Q :=
have abs_b_eq : abs (coeff_b Q) = coeff_a Q := le_antisymm hr.1 (le_trans hr.a_le_c h),
by simpa [abs_of_nonneg (hr.3 abs_b_eq)] using abs_b_eq

lemma is_reduced.coeff_b_add_coeff_a_nonneg {Q : QF₂ℤ} (hr : is_reduced Q) :
  0 ≤ coeff_b Q + coeff_a Q :=
neg_le_iff_add_nonneg.mp (neg_le.mp (abs_le.mp hr.1).1)

lemma is_reduced_iff_of_a_eq_b {Q : QF₂ℤ} (h : coeff_a Q = coeff_b Q) :
  is_reduced Q ↔ (0 ≤ coeff_a Q ∧ coeff_a Q ≤ coeff_c Q) :=
⟨ λ hr, ⟨hr.coeff_a_nonneg, hr.a_le_c⟩,
  λ ⟨ha, hc⟩, ⟨by rwa [←h, abs_of_nonneg ha], hc, λ _, h ▸ ha, λ _, h ▸ ha⟩ ⟩

lemma is_reduced.of_tuple_abs_b_le_a {a b c : ℤ} (hr : is_reduced (of_tuple a b c)) :
  abs b ≤ a :=
by simpa using hr.abs_b_le_a

lemma is_reduced.of_tuple_a_le_c {a b c : ℤ} (hr : is_reduced (of_tuple a b c)) :
  a ≤ c :=
by simpa using hr.a_le_c

lemma is_reduced.a_ne_b_of_b_neg {Q : QF₂ℤ} (hr : is_reduced Q) (h : coeff_b Q < 0) :
  coeff_a Q ≠ coeff_b Q :=
λ hab, not_le_of_gt h (hab ▸ hr.coeff_a_nonneg)

lemma is_reduced.a_ne_neg_b_of_b_neg {Q : QF₂ℤ} (hr : is_reduced Q) (h : coeff_b Q < 0) :
  coeff_a Q ≠ - coeff_b Q :=
λ hab, not_le_of_gt h (hab ▸ hr.b_nonneg_left (trans (abs_of_neg h) hab.symm))

lemma is_reduced.a_ne_c_of_b_neg {Q : QF₂ℤ} (hr : is_reduced Q) (h : coeff_b Q < 0) :
  coeff_a Q ≠ coeff_c Q :=
λ hac, not_le_of_gt h (hr.b_nonneg_right hac)

namespace reduced
/-! This namespace contains an order on quadratic forms, such that the minimum is a reduced form.

The proof that this minimum is a reduced form is done later.
-/

/-- Map the sign of an int to `fin 3` to order them with positive as the least, then zero, then negative. -/
def sign' : ℤ → fin 3
| (nat.succ n) := 0
| 0            := 1
| -[1+ n]      := 2

lemma sign'_coe : Π (n : ℕ), sign' ↑n ≤ 1
| 0 := le_refl _
| (n+1) := dec_trivial

lemma sign'_neg_lt_sign'_self_of_neg : Π {a : ℤ}, a < 0 → sign' (-a) < sign' a
| (n+1:ℕ) h := by cases h
| 0       h := by cases h
| -[1+ n] h := by { simp [sign'], exact dec_trivial }

lemma sign'_le_two : Π (a : ℤ), sign' a ≤ 2
| (nat.succ n) := dec_trivial
| 0            := dec_trivial
| -[1+ n]      := dec_trivial

lemma sign'_lt_iff : Π {a b : ℤ}, sign' a < sign' b ↔ (0 < a ∧ b ≤ 0) ∨ (a = 0 ∧ b < 0)
| (n+1:ℕ) (m+1:ℕ) := ⟨λ h, (lt_irrefl _ h).elim, by rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩)⟩
| (n+1:ℕ) 0       := ⟨λ h, or.inl ⟨int.coe_nat_succ_pos n, le_refl _⟩, λ h, dec_trivial⟩
| (n+1:ℕ) -[1+ m] := ⟨λ h, or.inl ⟨int.coe_nat_succ_pos n, dec_trivial⟩, λ h, dec_trivial⟩
| 0       (n:ℕ)   := ⟨λ h, (not_lt_of_ge (sign'_coe n) h).elim, by rintro (⟨⟨⟩, _⟩ | ⟨_, ⟨⟩⟩)⟩
| 0       -[1+ n] := ⟨λ h, or.inr ⟨rfl, int.neg_succ_lt_zero n⟩, λ h, dec_trivial ⟩
| -[1+ n] b       := ⟨λ h, (not_lt_of_ge (sign'_le_two b) h).elim, by rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩)⟩

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
def key (Q : pos_def_QF₂ℤ d) : lex ℕ (lex ℕ (lex (fin 3) ℕ)) :=
⟨(coeff_a Q).nat_abs, (coeff_b Q).nat_abs, sign' (coeff_b Q), (coeff_c Q).nat_abs⟩

lemma a_from_key (Q : pos_def_QF₂ℤ d) : ↑(key Q).fst = coeff_a Q :=
int.nat_abs_of_pos (coeff_a_pos Q.pos_def)

lemma abs_b_from_key (Q : pos_def_QF₂ℤ d) : ↑(key Q).snd.fst = abs (coeff_b Q) :=
int.coe_nat_abs_eq_abs

lemma sign_b_from_key (Q : pos_def_QF₂ℤ d) : (key Q).snd.snd.fst = sign' (coeff_b Q) :=
rfl

lemma b_from_key (Q : pos_def_QF₂ℤ d) : sign'_to_sign (key Q).snd.snd.fst * ↑(key Q).snd.fst = coeff_b Q :=
by { convert int.sign_mul_nat_abs (coeff_b Q), apply sign'_to_sign_of_sign' }

lemma c_from_key (Q : pos_def_QF₂ℤ d) :
  ↑(key Q).snd.snd.snd = coeff_c Q :=
int.nat_abs_of_pos (coeff_c_pos Q.pos_def)

lemma key_injective : function.injective (@key d) :=
λ Q Q' h, pos_def_QF₂ℤ.eq_of_coeffs_eq
  (by { rw [← a_from_key Q, h, a_from_key Q'] })
  (by { rw [← b_from_key Q, h, b_from_key Q'] })
  (by { rw [← c_from_key Q, h, c_from_key Q'] })

/-- An order of quadratic forms, such that reduced forms are minimal. -/
instance : has_lt (pos_def_QF₂ℤ d) :=
⟨function.on_fun (<) key⟩

/-- The `key` gives an order embedding from orbits to the well-order `ℕ × ℕ × fin 3 × ℕ`. -/
def orbit_embedding (Q : pos_def_QF₂ℤ d) :
  order_embedding (subrel (<) (mul_action.orbit SL₂ℤ Q)) ((<) : _ → lex ℕ (lex ℕ (lex (fin 3) ℕ)) → Prop) :=
{ to_fun := λ Q, key Q.1,
  inj' := λ ⟨g, hg⟩ ⟨g', hg'⟩ h,
    by { congr, exact key_injective h },
  ord' := λ _ _, iff.rfl }

/-- The order on quadratic forms is well-founded on these orbits. -/
instance (Q : pos_def_QF₂ℤ d) : is_well_order _ (subrel (<) (mul_action.orbit SL₂ℤ Q)) :=
@order_embedding.is_well_order _ _ _ _ (orbit_embedding Q)
  (@prod.lex.is_well_order _ _ _ _ _
    (@prod.lex.is_well_order _ _ _ _ _
      (@prod.lex.is_well_order _ _ _ _ _ _)))

lemma lt_iff {Q g : pos_def_QF₂ℤ d} :
  Q < g ↔ coeff_a Q < coeff_a g ∨
    (coeff_a Q = coeff_a g ∧ (abs (coeff_b Q) < abs (coeff_b g) ∨
      (abs (coeff_b Q) = abs (coeff_b g) ∧ (sign' (coeff_b Q) < sign' (coeff_b g) ∨
        (sign' (coeff_b Q) = sign' (coeff_b g) ∧ coeff_c Q < coeff_c g))))) :=
begin
  refine iff.trans (prod.lex_def _ _) (or_congr _ (and_congr _ _)),
  { exact iff.trans int.coe_nat_lt.symm (by rw [a_from_key Q, a_from_key g]) },
  { refine (iff.trans (function.injective.eq_iff @int.coe_nat_inj).symm _),
    rw [a_from_key Q, a_from_key g] },
  refine iff.trans (prod.lex_def _ _) (or_congr _ (and_congr _ _)),
  { rw [←int.coe_nat_lt, abs_b_from_key Q, abs_b_from_key g] },
  { rw [←int.coe_nat_inj', abs_b_from_key Q, abs_b_from_key g] },
  refine iff.trans (prod.lex_def _ _) (or_congr (iff.refl _) (and_congr (iff.refl _) _)),
  apply iff.trans int.coe_nat_lt.symm,
  rw [c_from_key Q, c_from_key g]
end

lemma a_le_of_lt {Q g : pos_def_QF₂ℤ d} (h : Q < g):
  coeff_a Q ≤ coeff_a g :=
begin
  rcases lt_iff.mp h with ha | ⟨ha, _⟩,
  { exact le_of_lt ha },
  { exact le_of_eq ha }
end

lemma a_val_le_of_smul_lt {Q : pos_def_QF₂ℤ d} {M : SL₂ℤ} (h : M • Q < Q):
  M 0 0 * M 0 0 * coeff_a Q + M 0 0 * M 0 1 * coeff_b Q + M 0 1 * M 0 1 * coeff_c Q ≤ coeff_a Q :=
by { convert a_le_of_lt h, symmetry, erw [smul_coeff_a, apply_val], simp }

end reduced

section minimal

/-- A form is minimal if there is no smaller form in its orbit. -/
def minimal (Q : pos_def_QF₂ℤ d) : Prop :=
∀ (g : pos_def_QF₂ℤ d), g ≈ Q → ¬g < Q

lemma minimal_iff {Q : pos_def_QF₂ℤ d} : minimal Q ↔ ∀ (M : SL₂ℤ), ¬ M • Q < Q :=
⟨λ min M, min (M • Q) ⟨M, rfl⟩, (by { rintros min' _ ⟨M, rfl⟩, apply min' })⟩

/-- The first half of the proof: each class has a unique minimal element.

  Next, we will show that a form is minimal iff it is reduced,
  to conclude that each class has a unique reduced element.
-/
lemma exists_unique_min (Q : pos_def_QF₂ℤ d) :
  ∃! (g : pos_def_QF₂ℤ d), g ≈ Q ∧ minimal g :=
let ⟨⟨g, g_mem⟩, _, min⟩ := well_founded.has_min (reduced.is_well_order Q).wf set.univ
  (set.nonempty_of_mem (set.mem_univ ⟨Q, setoid.refl Q⟩)) in
⟨ g,
  ⟨g_mem, λ h h_mem, min ⟨h, setoid.trans h_mem g_mem⟩ (set.mem_univ _)⟩,
  λ g' ⟨g'_mem, g'_min⟩, let t := (reduced.is_well_order Q).trichotomous in -- TODO: inlining t doesn't work
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

lemma coeff_a_swap_x_y_smul (Q : pos_def_QF₂ℤ d) : coeff_a ↑(swap_x_y • Q) = coeff_c Q :=
by simp [pos_def_QF₂ℤ.apply_val Q 0 (-1)]

lemma coeff_b_swap_x_y_smul (Q : pos_def_QF₂ℤ d) : coeff_b ↑(swap_x_y • Q) = - coeff_b Q :=
by { simp [pos_def_QF₂ℤ.apply_val], ring }

lemma coeff_c_swap_x_y_smul (Q : pos_def_QF₂ℤ d) : coeff_c ↑(swap_x_y • Q) = coeff_a Q :=
by simp [pos_def_QF₂ℤ.apply_val Q 1 0]

lemma swap_x_y_lt {Q : pos_def_QF₂ℤ d} (hc : 0 < coeff_c Q) (h : coeff_c Q < coeff_a Q) : (swap_x_y • Q) < Q :=
prod.lex.left _ _ (by simpa [abs_of_pos hc, abs_of_pos (lt_trans hc h), pos_def_QF₂ℤ.apply_val])

lemma swap_x_y_lt_of_eq_of_neg {Q : pos_def_QF₂ℤ d} (hac : coeff_a Q = coeff_c Q) (hb : coeff_b Q < 0) : (swap_x_y • Q) < Q :=
reduced.lt_iff.mpr (or.inr
  ⟨ by rw [coeff_a_swap_x_y_smul, hac],
    or.inr
      ⟨ by rw [coeff_b_swap_x_y_smul, abs_neg],
        or.inl (by { convert reduced.sign'_neg_lt_sign'_self_of_neg hb, apply coeff_b_swap_x_y_smul })⟩⟩)

/-- `change_xy k` changes the coefficient for `xy` while keeping the coefficient for `x²` the same -/
def change_xy (k : ℤ) : SL₂ℤ := ⟨![![1, 0], ![k, 1]], by simp [det_2x2]⟩

@[simp]
lemma coe_fn_change_xy (k : ℤ): ⇑(change_xy k) = ![![1, 0], ![k, 1]] := rfl

lemma coeff_a_change_xy_smul (k : ℤ) (Q : pos_def_QF₂ℤ d) :
  coeff_a ↑(change_xy k • Q) = coeff_a Q :=
by simp [pos_def_QF₂ℤ.apply_val]

lemma coeff_b_change_xy_smul (k : ℤ) (Q : pos_def_QF₂ℤ d) :
  coeff_b ↑(change_xy k • Q) = 2 * k * coeff_a Q + coeff_b Q :=
by { simp [pos_def_QF₂ℤ.apply_val], ring }

lemma coeff_c_change_xy_smul (k : ℤ) (Q : pos_def_QF₂ℤ d) :
  coeff_c ↑(change_xy k • Q) = k * k * coeff_a Q + k * coeff_b Q + coeff_c Q :=
by { simp [pos_def_QF₂ℤ.apply_val] }

lemma change_xy_lt_abs {Q : pos_def_QF₂ℤ d} {k : ℤ} (h : abs (2 * k * coeff_a Q + coeff_b Q) < abs (coeff_b Q)) :
  (change_xy k • Q) < Q :=
reduced.lt_iff.mpr (or.inr
  ⟨ by rw [coeff_a_change_xy_smul k Q],
    or.inl (by rwa [coeff_b_change_xy_smul])⟩)

lemma change_xy_lt_sign {Q : pos_def_QF₂ℤ d} {k : ℤ} (h : abs (2 * k * coeff_a Q + coeff_b Q) = abs (coeff_b Q)) (h2 : reduced.sign' (2 * k * coeff_a Q + coeff_b Q) < reduced.sign' (coeff_b Q)) : (change_xy k • Q) < Q :=
reduced.lt_iff.mpr (or.inr
  ⟨ by rw [coeff_a_change_xy_smul k Q],
    or.inr
      ⟨ by rwa [coeff_b_change_xy_smul],
        or.inl (by rwa [coeff_b_change_xy_smul]) ⟩ ⟩)

lemma a_le_c_of_min {Q : pos_def_QF₂ℤ d} (min : minimal Q) : coeff_a Q ≤ coeff_c Q :=
le_of_not_gt (λ c_lt_a, min (swap_x_y • Q) ⟨_, rfl⟩ (swap_x_y_lt (coeff_c_pos Q.pos_def) c_lt_a))

lemma b_le_a_of_min {Q : pos_def_QF₂ℤ d} (min : minimal Q) : abs (coeff_b Q) ≤ coeff_a Q :=
begin
  have a_pos : 0 < coeff_a Q := coeff_a_pos Q.pos_def,
  apply le_of_not_gt,
  intro a_lt_b,
  rcases @trichotomous _ (<) _ 0 (coeff_b Q) with b_pos | b_zero | b_neg,
  { apply minimal_iff.mp min (change_xy (-1)),
    refine change_xy_lt_abs (abs_lt.mpr (and.intro _ _));
      rw [abs_of_pos b_pos] at *;
      linarith },
  { rw [←b_zero, abs_zero] at *, linarith },
  { apply minimal_iff.mp min (change_xy 1),
    refine change_xy_lt_abs (abs_lt.mpr (and.intro _ _));
      rw [abs_of_neg b_neg] at *;
      linarith },
end

lemma min_of_reduced_aux_aux {a b c : ℤ} (m n : ℤ) (hba : abs b ≤ a) (hac : a ≤ c) :
  a * ((abs m - abs n) * (abs m - abs n) + abs m * abs n) ≤ m * m * a + m * n * b + n * n * c :=
have abs_m_nonneg : _ := abs_nonneg m,
have abs_n_nonneg : _ := abs_nonneg n,
calc a * ((abs m - abs n) * (abs m - abs n) + abs m * abs n)
       = abs m * abs m * a - abs m * abs n * a + abs n * abs n * a : by ring
   ... ≤ abs m * abs m * a - abs m * abs n * abs b + abs n * abs n * c :
    add_le_add (sub_le_sub_left (mul_le_mul_of_nonneg_left hba (mul_nonneg (by linarith) abs_n_nonneg)) _)
      (mul_le_mul_of_nonneg_left hac (mul_self_nonneg _))
   ... = m * m * a + -abs (m * n * b) + n * n * c : by { simp only [abs_mul, abs_mul_abs_self], ring }
   ... ≤ m * m * a + m * n * b + n * n * c :
    add_le_add_right (add_le_add_left (neg_le.mp (neg_le_abs_self _)) _) _

lemma le_one_or_le_one_of_mul_le_one {a b : ℤ} : a * b ≤ 1 → a ≤ 1 ∨ b ≤ 1 :=
assume h, if h' : a ≤ 1 then or.inl h'
else or.inr ((mul_le_iff_le_one_right (lt_trans zero_lt_one (lt_of_not_ge h'))).mp (le_trans h (le_of_not_ge h')))

lemma le_one_of_mul_self_le_one {a : ℤ} (h : a * a ≤ 1) : a ≤ 1 :=
(le_one_or_le_one_of_mul_le_one h).elim id id

lemma a_le_even_mul_a_add_b {a b k : ℤ} (h : abs b ≤ a) (hk : k ≠ 0) : a ≤ abs (2 * k * a + b) :=
begin
  have : 0 ≤ abs b := abs_nonneg b,
  rcases @trichotomous _ (<) _ 0 k with k_pos | k_zero | k_neg,
  { refine le_max_iff.mpr (or.inl _),
    calc a = 2 * a + - a : by ring
       ... ≤ 2 * (k * a) + b : add_le_add ((mul_le_mul_left (by linarith)).mpr (le_mul_of_one_le_left' (le_trans this h) k_pos)) (neg_le.mp (le_trans (neg_le_abs_self _) h))
           ... = 2 * k * a + b : by rw [mul_assoc] },
  { cases hk k_zero.symm },
  { refine le_max_iff.mpr (or.inr _),
    have k_pos : 0 < -k := by linarith,
    calc a = 2 * a + - a : by ring
       ... ≤ 2 * ((-k) * a) + - b : add_le_add ((mul_le_mul_left (by linarith)).mpr (le_mul_of_one_le_left' (le_trans this h) k_pos)) (neg_le_neg (le_trans (le_abs_self _) h))
       ... = -(2 * k * a + b) : by ring }
end

lemma a_le_even_mul_a_sub_b {a b k : ℤ} (h : abs b ≤ a) (hk : k ≠ 0) : a ≤ abs (2 * k * a - b) :=
by simpa using a_le_even_mul_a_add_b (show abs (-b) ≤ a, by rwa [abs_neg]) hk

lemma a_le_even_mul_a_pm_b {a b k l : ℤ} (h : abs b ≤ a) (hk : k ≠ 0) (hl : abs l = 1) :
  a ≤ abs (2 * k * a + l * b) :=
((abs_eq (by norm_num)).mp hl).elim
  (λ hl, by simpa [hl] using a_le_even_mul_a_add_b h hk)
  (λ hl, by simpa [hl] using a_le_even_mul_a_sub_b h hk)

lemma abs_b_le_even_mul_a_add_b {a b k : ℤ} (h : abs b ≤ a) : abs b ≤ abs (2 * k * a + b) :=
if hk : k = 0 then by simp [hk] else le_trans h (a_le_even_mul_a_add_b h hk)

lemma abs_b_le_even_mul_a_sub_b {a b k : ℤ} (h : abs b ≤ a) : abs b ≤ abs (2 * k * a - b) :=
by simpa using abs_b_le_even_mul_a_add_b (show abs (-b) ≤ a, by rwa [abs_neg])

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

lemma sub_mul_self_add_mul_pos {m n : ℤ} (hmn : ¬ (m = 0 ∧ n = 0)) :
  0 < (abs m - abs n) * (abs m - abs n) + abs m * abs n :=
have abs_mul_abs_nonneg : 0 ≤ abs m * abs n := mul_nonneg (abs_nonneg _) (abs_nonneg _),
if h : abs m = abs n
then add_pos_of_nonneg_of_pos (mul_self_nonneg _) (lt_of_le_of_ne abs_mul_abs_nonneg
  (λ mul_zero, hmn (or.elim (mul_eq_zero.mp mul_zero.symm)
    (λ hm, ⟨abs_eq_zero.mp hm, abs_eq_zero.mp (trans h.symm hm)⟩)
    (λ hn, ⟨abs_eq_zero.mp (trans h hn), abs_eq_zero.mp hn⟩))))
else add_pos_of_pos_of_nonneg (mul_self_pos (mt sub_eq_zero.mp h)) abs_mul_abs_nonneg

lemma a_le_a_smul_of_reduced {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) (M : SL₂ℤ) :
  coeff_a Q ≤ coeff_a ↑(M • Q) :=
begin
  rw [Q.coe_smul, smul_coeff_a, apply_val],
  apply le_trans _ (min_of_reduced_aux_aux (M 0 0) (M 0 1) hr.1 hr.2),
  apply (le_mul_iff_one_le_right (coeff_a_pos Q.pos_def)).mpr,
  apply sub_mul_self_add_mul_pos,
  rintro ⟨hm, hn⟩,
  simpa [det_2x2, hm, hn] using M.det_coe_fun
end

lemma abs_m_le_one_aux {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) (M : SL₂ℤ) (lt : M • Q < Q) :
  (abs (M 0 0) - abs (M 0 1)) * (abs (M 0 0) - abs (M 0 1)) + abs (M 0 0) * abs (M 0 1) ≤ 1 :=
(mul_le_iff_le_one_right (coeff_a_pos Q.pos_def)).mp (le_trans
  (min_of_reduced_aux_aux (M 0 0) (M 0 1) hr.1 hr.2)
  (by simpa [Q.apply_val] using reduced.a_le_of_lt lt))

lemma abs_m_le_one {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) {M : SL₂ℤ} (lt : M • Q < Q) :
  abs (M 0 0) ≤ 1 :=
if hm : M 0 0 = 0 then by simp [hm]
else if hn : M 0 1 = 0 then le_one_of_mul_self_le_one (by simpa [hn] using abs_m_le_one_aux hr M lt)
else calc abs (M 0 0) ≤ abs (M 0 0) * abs (M 0 1) :
  (le_mul_iff_one_le_right (abs_pos_iff.mpr hm)).mpr (abs_pos_iff.mpr hn)
                  ... ≤ (abs (M 0 0) - abs (M 0 1)) * (abs (M 0 0) - abs (M 0 1)) + abs (M 0 0) * abs (M 0 1) :
  le_add_of_nonneg_left' (mul_self_nonneg _)
                  ... ≤ 1 : abs_m_le_one_aux hr M lt

lemma abs_n_le_one {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) {M : SL₂ℤ} (lt : M • Q < Q) :
  abs (M 0 1) ≤ 1 :=
if hm : M 0 0 = 0 then le_one_of_mul_self_le_one (by simpa [hm] using abs_m_le_one_aux hr M lt)
else if hn : M 0 1 = 0 then by simp [hn]
else calc abs (M 0 1) ≤ abs (M 0 0) * abs (M 0 1) :
  (le_mul_iff_one_le_left (abs_pos_iff.mpr hn)).mpr (abs_pos_iff.mpr hm)
                  ... ≤ (abs (M 0 0) - abs (M 0 1)) * (abs (M 0 0) - abs (M 0 1)) + abs (M 0 0) * abs (M 0 1) :
  le_add_of_nonneg_left' (mul_self_nonneg _)
                  ... ≤ 1 : abs_m_le_one_aux hr M lt

lemma abs_m_eq_one_of_nonzero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) {M : SL₂ℤ} (lt : M • Q < Q)
  (h : M 0 0 ≠ 0) : abs (M 0 0) = 1 :=
le_antisymm (abs_m_le_one hr lt) (abs_pos_iff.mpr h)

lemma abs_n_eq_one_of_nonzero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) {M : SL₂ℤ} (lt : M • Q < Q)
  (h : M 0 1 ≠ 0) : abs (M 0 1) = 1 :=
le_antisymm (abs_n_le_one hr lt) (abs_pos_iff.mpr h)

lemma int.le_mul_self : Π (a : ℤ), a ≤ a * a
| 0 := by simp
| (nat.succ n) := (le_mul_iff_one_le_left (by norm_cast; apply nat.zero_lt_succ)).mpr (by norm_cast; exact nat.succ_le_succ bot_le)
| -[1+ n ] := by simp

lemma int.abs_le_mul_self (a : ℤ) : abs a ≤ a * a :=
if h : a < 0 then by simpa [abs_of_neg h] using int.le_mul_self (-a)
else by simpa [abs_of_nonneg (le_of_not_gt h)] using int.le_mul_self a

lemma abs_m_mul_n_le_m_mul_m {m n : ℤ} (h : abs n ≤ 1) : abs (m * n) ≤ m * m :=
if hm : m = 0 then by simp [hm]
else calc abs (m * n) = abs m * abs n : abs_mul m n
       ... ≤ abs m : (mul_le_iff_le_one_right (abs_pos_iff.mpr hm)).mpr h
       ... ≤ m * m : int.abs_le_mul_self m

lemma a_add_b_nonneg {a b m n : ℤ} (hab : abs b ≤ a) (hn : abs n ≤ 1) : 0 ≤ m * m * a + m * n * b :=
calc 0 ≤ (m * m - abs (m * n)) * a : mul_nonneg (sub_nonneg.mpr (abs_m_mul_n_le_m_mul_m hn)) (le_trans (abs_nonneg _) hab)
   ... = m * m * a - abs (m * n) * a : sub_mul _ _ _
   ... ≤ m * m * a - abs (m * n) * abs b : sub_le_sub_left (mul_le_mul_of_nonneg_left hab (abs_nonneg _)) _
   ... = m * m * a + - abs (m * n * b) : by simp [sub_eq_add_neg, abs_mul, mul_assoc]
   ... ≤ m * m * a + m * n * b : add_le_add_left (neg_le.mp (neg_le_abs_self _)) _

lemma a_eq_c_of_a_eq_smul_a_of_n_nonzero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) {M : SL₂ℤ}
  (lt : M • Q < Q) (ha : coeff_a ↑(M • Q) = coeff_a Q) (hn : M 0 1 ≠ 0) : coeff_a Q = coeff_c Q :=
le_antisymm hr.2 $ calc
  coeff_c Q ≤ M 0 1 * M 0 1 * coeff_c Q :
    (le_mul_iff_one_le_left (coeff_c_pos Q.pos_def)).mpr
      (mul_self_pos hn)
    ... ≤ M 0 0 * M 0 0 * coeff_a Q + M 0 0 * M 0 1 * coeff_b Q + M 0 1 * M 0 1 * coeff_c Q :
      le_add_of_nonneg_left' (a_add_b_nonneg hr.1 (abs_n_le_one hr lt))
    ... = coeff_a ↑(M • Q) : by simp [Q.apply_val]
    ... = coeff_a Q : ha

lemma b_eq_a_of_mn_nonzero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) {M : SL₂ℤ}
  (lt : M • Q < Q) (hm : M 0 0 ≠ 0) (hn : M 0 1 ≠ 0) : coeff_b Q = coeff_a Q :=
hr.b_eq_a_of_c_le_abs_b $
begin
  apply sub_nonpos.mp,
  rw [sub_eq_add_neg, add_comm],
  apply add_le_iff_nonpos_right.mp,
  rw ←add_assoc,
  apply le_trans _ (reduced.a_val_le_of_smul_lt lt),
  apply add_le_add,
  { apply add_le_add,
    { rw [←abs_mul_self (M 0 0), abs_mul, abs_m_eq_one_of_nonzero hr lt hm, one_mul, one_mul] },
    apply neg_le.mp,
    convert neg_le_abs_self (M 0 0 * M 0 1 * coeff_b Q) using 1,
    simp [abs_mul, abs_m_eq_one_of_nonzero hr lt hm, abs_n_eq_one_of_nonzero hr lt hn] },
  { rw [←abs_mul_self (M 0 1), abs_mul, abs_n_eq_one_of_nonzero hr lt hn, one_mul, one_mul] }
end

lemma coeff_b_smul_of_m_eq_zero (Q : pos_def_QF₂ℤ d) {M : SL₂ℤ} (h : M 0 0 = 0) :
  coeff_b ↑(M • Q) = (2 * M 1 1 * coeff_c Q + M 1 0 * coeff_b Q) * M 0 1 :=
by { simp [h, Q.apply_val], ring }

lemma coeff_b_smul_of_n_eq_zero (Q : pos_def_QF₂ℤ d) {M : SL₂ℤ} (h : M 0 1 = 0) :
  coeff_b ↑(M • Q) = (2 * M 1 0 * coeff_a Q + M 1 1 * coeff_b Q) * M 0 0 :=
by { simp [h, Q.apply_val], ring }

lemma abs_b_le_abs_b_smul_of_reduced_of_m_eq_zero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q)
  {M : SL₂ℤ} (hm : M 0 0 = 0) : abs (coeff_b Q) ≤ abs (coeff_b ↑(M • Q)) :=
begin
  rw [coeff_b_smul_of_m_eq_zero Q hm, abs_mul, abs_n_eq_one_of_m_eq_zero hm, mul_one],
  cases (abs_eq (show (0 : ℤ) ≤ 1, by norm_num)).mp (abs_o_eq_one_of_m_eq_zero hm),
  { simpa [h] using abs_b_le_even_mul_a_add_b (le_trans hr.1 hr.2) },
  { simpa [h] using abs_b_le_even_mul_a_sub_b (le_trans hr.1 hr.2) }
end

lemma abs_b_le_abs_b_smul_of_reduced_of_n_eq_zero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q)
  {M : SL₂ℤ} (hn : M 0 1 = 0) : abs (coeff_b Q) ≤ abs (coeff_b ↑(M • Q)) :=
begin
  rw [coeff_b_smul_of_n_eq_zero Q hn, abs_mul, abs_m_eq_one_of_n_eq_zero hn, mul_one],
  cases (abs_eq (show (0 : ℤ) ≤ 1, by norm_num)).mp (abs_p_eq_one_of_n_eq_zero hn),
  { simpa [h] using abs_b_le_even_mul_a_add_b hr.1 },
  { simpa [h] using abs_b_le_even_mul_a_sub_b hr.1 }
end

lemma mp_eq (M : SL₂ℤ) : M 0 0 * M 1 1 = 1 + M 0 1 * M 1 0 :=
by { rw [←M.det_coe_fun, det_2x2], ring }

lemma abs_b_le_abs_b_smul_of_reduced_of_mn_nonzero {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q)
  {M : SL₂ℤ} (lt : M • Q < Q) (ha : coeff_a ↑(M • Q) = coeff_a Q) (hm : M 0 0 ≠ 0) (hn : M 0 1 ≠ 0) :
  abs (coeff_b Q) ≤ abs (coeff_b ↑(M • Q)) :=
begin
suffices : abs (coeff_b Q) ≤ abs ((2 * M 0 0 * M 1 0 + M 0 0 * M 1 1 + M 0 1 * M 1 0 + 2 * M 0 1 * M 1 1) * coeff_b Q),
  { convert this,
    simp [smul_coeff_b, smul_coeff_a, smul_coeff_c, Q.apply_val, Q.apply_val, Q.apply_val, ← a_eq_c_of_a_eq_smul_a_of_n_nonzero hr lt ha hn, ← b_eq_a_of_mn_nonzero hr lt hm hn],
    ring },
  rw [abs_mul],
  apply le_mul_of_one_le_left' (abs_nonneg (coeff_b Q)),
  apply lt_of_le_of_ne (abs_nonneg (_ + 2 * M 0 1 * M 1 1)),
  intro h,
  suffices : (2 : ℤ) ∣ 1, { norm_num at this },
  use -(M 0 0 * M 1 0 + M 0 1 * M 1 0 + M 0 1 * M 1 1),
  apply sub_eq_zero.mp,
  convert abs_eq_zero.mp h.symm,
  rw [mp_eq],
  ring
end

lemma min_of_reduced {Q : pos_def_QF₂ℤ d} (hr : is_reduced Q) : minimal Q :=
minimal_iff.mpr (λ M lt, begin
  rcases reduced.lt_iff.mp lt with ha | ⟨ha, habs | ⟨habs, hsgn | ⟨hsgn, hc⟩⟩⟩,
  { apply not_lt_of_ge (a_le_a_smul_of_reduced hr M) ha },
  { by_cases hm : M 0 0 = 0,
    { exact not_lt_of_ge (abs_b_le_abs_b_smul_of_reduced_of_m_eq_zero hr hm) habs },
    by_cases hn : M 0 1 = 0,
    { exact not_lt_of_ge (abs_b_le_abs_b_smul_of_reduced_of_n_eq_zero hr hn) habs },
    apply not_lt_of_le _ habs,
    exact abs_b_le_abs_b_smul_of_reduced_of_mn_nonzero hr lt ha hm hn },
  { obtain ⟨b_neg, smul_b_pos⟩ := (reduced.sign'_lt_iff_of_abs_eq habs).mp hsgn,
    by_cases hn : M 0 1 = 0,
    { have mp_eq_one : M 0 0 * M 1 1 = 1 := by simpa [hn] using mp_eq M,
      by_cases ho : M 1 0 = 0,
      { apply lt_asymm b_neg,
        simpa [ho, hn, mp_eq_one, Q.apply_val] using smul_b_pos },
      apply not_lt_of_ge (hr.b_nonneg_left (le_antisymm hr.1 _)) b_neg,
      convert a_le_even_mul_a_pm_b hr.1 ho (abs_p_eq_one_of_n_eq_zero hn) using 1,
      calc abs (coeff_b Q)
           = abs (coeff_b ↑(M • Q)) : habs.symm
       ... = abs ((2 * M 1 0 * coeff_a Q + M 1 1 * coeff_b Q) * M 0 0) : by { simp [Q.apply_val, hn], congr, ring }
       ... = abs (2 * M 1 0 * coeff_a Q + M 1 1 * coeff_b Q) : by simp [abs_mul, abs_m_eq_one_of_n_eq_zero hn] },
    exact not_lt_of_ge (hr.b_nonneg_right (a_eq_c_of_a_eq_smul_a_of_n_nonzero hr lt ha hn)) b_neg },
  { apply not_lt_of_ge _ hc,
    by_cases hn : M 0 1 = 0,
    { have psq_eq_1 : M 1 1 * M 1 1 = 1, { rw [←abs_mul_self (M 1 1), abs_mul, abs_p_eq_one_of_n_eq_zero hn, mul_one] },
      by_cases M 1 0 = 0,
      { simp [h, psq_eq_1, Q.apply_val] },
      rw [Q.coe_smul, smul_coeff_c, Q.coe_fn_coe, Q.apply_val, psq_eq_1, one_mul],
      apply le_add_of_nonneg_left' _,
      have abs_k_pos : 0 < abs (M 1 0) := lt_of_le_of_ne (abs_nonneg (M 1 0)) (ne.symm (mt abs_eq_zero.mp h)),
      calc 0 ≤ abs (M 1 0) * (coeff_a Q - abs (coeff_b Q)) :
        mul_nonneg (abs_nonneg (M 1 0)) (sub_nonneg.mpr hr.1)
        ... = abs (M 1 0) * (1 * coeff_a Q - abs (coeff_b Q)) : by ring
        ... ≤ abs (M 1 0) * (abs (M 1 0) * coeff_a Q - abs (coeff_b Q)) :
        mul_le_mul_of_nonneg_left (sub_le_sub_right
          (mul_le_mul_of_nonneg_right
          abs_k_pos
          (le_of_lt (coeff_a_pos Q.pos_def))) _) (abs_nonneg (M 1 0))
        ... = abs (M 1 0) * abs (M 1 0) * coeff_a Q - abs (M 1 0) * abs (coeff_b Q) : by ring
        ... = M 1 0 * M 1 0 * coeff_a Q + - abs (M 1 0 * M 1 1 * coeff_b Q) :
        by rw [abs_mul_abs_self, sub_eq_add_neg, abs_mul, abs_mul, abs_p_eq_one_of_n_eq_zero hn, mul_one]
        ... ≤ M 1 0 * M 1 0 * coeff_a Q + M 1 0 * M 1 1 * coeff_b Q : add_le_add_left (neg_le.mp (neg_le_abs_self _)) _ },
    have a_eq_c := a_eq_c_of_a_eq_smul_a_of_n_nonzero hr lt ha hn,
    rw [Q.coe_smul, smul_coeff_c, Q.coe_fn_coe, Q.apply_val, a_eq_c],
    refine le_trans _ (min_of_reduced_aux_aux (M 1 0) (M 1 1) (le_trans hr.1 hr.2) (le_refl (coeff_c Q))),
    apply (le_mul_iff_one_le_right (coeff_c_pos Q.pos_def)).mpr,
    apply sub_mul_self_add_mul_pos,
    rintro ⟨hm, hn⟩,
    simpa [det_2x2, hm, hn] using M.det_coe_fun }
end)

lemma min_iff_reduced {Q : pos_def_QF₂ℤ d} :
  minimal Q ↔ is_reduced Q :=
⟨ λ min,
  ⟨ b_le_a_of_min min,
    a_le_c_of_min min,
    λ h, le_of_not_gt (λ b_neg, minimal_iff.mp min (change_xy 1) (change_xy_lt_sign
        (calc abs (2 * 1 * coeff_a Q + coeff_b Q) = abs (2 * 1 * -coeff_b Q + coeff_b Q) :
          by simp [← h, abs_of_neg b_neg]
                                  ... = abs (- coeff_b Q) : by ring
                                  ... = abs (coeff_b Q) : abs_neg _ )
        (by { convert reduced.sign'_neg_lt_sign'_self_of_neg b_neg, rw [←h, abs_of_neg b_neg], ring }))),
    λ h, le_of_not_gt (mt (swap_x_y_lt_of_eq_of_neg h) (minimal_iff.mp min swap_x_y))⟩,
  min_of_reduced⟩

/-- In each orbit, there is a unique reduced quadratic form -/
theorem exists_unique_reduced_equiv (Q : pos_def_QF₂ℤ d) :
  ∃! g, g ≈ Q ∧ is_reduced g :=
let ⟨g, ⟨e, m⟩, u⟩ := exists_unique_min Q in
⟨ g, ⟨e, (min_iff_reduced).mp m⟩, λ g' ⟨e', r'⟩, u g' ⟨e', (min_iff_reduced).mpr r'⟩ ⟩

lemma coeff_a_bound {Q : QF₂ℤ} (h : is_reduced Q) (hd : discr' Q = d):
  3 * coeff_a Q * coeff_a Q ≤ -d :=
have a_nonneg : 0 ≤ coeff_a Q := h.coeff_a_nonneg,
le_neg.mp $ calc d = coeff_b Q * coeff_b Q - 4 * coeff_a Q * coeff_c Q : hd.symm
               ... = abs (coeff_b Q) * abs (coeff_b Q) - 4 * coeff_a Q * coeff_c Q
                   : by rw [abs_mul_abs_self]
               ... ≤ coeff_a Q * coeff_a Q - 4 * coeff_a Q * coeff_a Q
                   : sub_le_sub (mul_le_mul h.1 h.1 (abs_nonneg _) a_nonneg)
                                (mul_le_mul_of_nonneg_left h.2 (by linarith))
               ... = -(3 * coeff_a Q * coeff_a Q) : by ring

lemma reduced_of_coeff_a_bound {Q : QF₂ℤ} (ha : 4 * coeff_a Q * coeff_a Q < -discr' Q)
  (hab : -coeff_a Q < coeff_b Q) (hba : coeff_b Q ≤ coeff_a Q) : is_reduced Q :=
have abs_b_le_a : abs (coeff_b Q) ≤ coeff_a Q := abs_le.mpr ⟨le_of_lt hab, hba⟩,
have a_nonneg : 0 ≤ coeff_a Q := le_trans (abs_nonneg _) abs_b_le_a,
have a_lt_c : coeff_a Q < coeff_c Q := (mul_lt_mul_left (show 0 < 4 * coeff_a Q, by linarith)).mp $
  calc 4 * coeff_a Q * coeff_a Q
      < -(coeff_b Q * coeff_b Q - 4 * coeff_a Q * coeff_c Q) : ha
  ... = 4 * coeff_a Q * coeff_c Q - coeff_b Q * coeff_b Q : neg_sub _ _
  ... ≤ 4 * coeff_a Q * coeff_c Q : sub_le_self _ (mul_self_nonneg _),
⟨ abs_b_le_a,
  le_of_lt a_lt_c,
  λ h, ((abs_eq a_nonneg).mp h).elim (λ h, h.symm ▸ a_nonneg) (λ h, absurd h.symm (ne_of_lt hab)),
  λ h, absurd h (ne_of_lt a_lt_c) ⟩

lemma pos_def_QF₂ℤ.reduced_of_coeff_a_bound {Q : pos_def_QF₂ℤ d} (ha : 4 * coeff_a Q * coeff_a Q < -d)
  (hab : -coeff_a Q < coeff_b Q) (hba : coeff_b Q ≤ coeff_a Q) : is_reduced Q :=
reduced_of_coeff_a_bound (Q.discr_coe.symm ▸ ha) hab hba

instance {Q : QF₂ℤ} {d : ℕ} : decidable (discr' Q = -d ∧ pos_def Q.val ∧ is_reduced Q) :=
if hd : discr' Q = -d
then if hr : is_reduced Q
  then @dite _ (@pos_def_decidable_of_discr_nonpos Q (hd.symm ▸ neg_nonpos.mpr (int.coe_nat_nonneg d))) _
    (λ hpd, is_true (and.intro hd (and.intro hpd hr)))
    (λ hpd, is_false (λ h, hpd h.2.1))
  else is_false (λ h, hr h.2.2)
else is_false (λ h, hd h.1)

def reduced_forms (d : ℕ) : finset QF₂ℤ :=
((range (nat.sqrt (d / 3) + 1)).bind (λ a,
  (range (a * 2 + 1)).image (λ b,
    of_tuple a (b - a) (((b - a) * (b - a) + d) / (4 * a))))).filter
  (λ Q, discr' Q = -d ∧ pos_def Q.val ∧ is_reduced Q)

lemma mem_reduced_forms_iff {d : ℕ} {Q : QF₂ℤ} :
  Q ∈ reduced_forms d ↔ discr' Q = -d ∧ pos_def Q.val ∧ is_reduced Q :=
begin
  apply iff.trans mem_filter,
  split,
  { rintros ⟨_, h⟩, exact h },
  rintros ⟨hd, hpd, hr⟩,
  refine ⟨mem_bind.mpr ⟨(coeff_a Q).to_nat, _, _⟩, ⟨hd, hpd, hr⟩⟩,
  { apply finset.mem_range.mpr (nat.succ_le_succ (nat.le_sqrt.mpr _)),
    apply (nat.le_div_iff_mul_le' (show 0 < 3, by norm_num)).mpr,
    rw mul_comm,
    apply (@nat.cast_le ℤ _ _ _).mp,
    simpa [int.to_nat_of_nonneg hr.coeff_a_nonneg, mul_assoc] using coeff_a_bound hr hd },
  refine mem_image.mpr ⟨(coeff_b Q + coeff_a Q).to_nat, _, trans _ (of_tuple_coeff Q)⟩,
  { apply finset.mem_range.mpr (nat.succ_le_succ _),
    apply (@nat.cast_le ℤ _ _ _).mp,
    convert add_le_add_right (abs_le.mp hr.1).2 (coeff_a Q);
      simp [mul_two, int.to_nat_of_nonneg hr.coeff_b_add_coeff_a_nonneg, int.to_nat_of_nonneg hr.coeff_a_nonneg] },
  rw [int.to_nat_of_nonneg hr.coeff_b_add_coeff_a_nonneg, int.to_nat_of_nonneg hr.coeff_a_nonneg, add_sub_cancel],
  congr' 1,
  { rw [← neg_eq_iff_neg_eq.mp hd.symm, discr', neg_sub, ←add_sub_assoc, add_sub_cancel', mul_comm _ (coeff_c Q)],
    apply int.mul_div_cancel,
    suffices : coeff_a Q ≠ 0, by norm_num [this],
    exact (ne_of_lt (coeff_a_pos hpd)).symm },
end

/-- Count the reduced quadratic forms `of_tuple a (± b) c`, with `a * c = a_mul_c`. -/
def number_at (b a_mul_c a : ℕ) : ℕ :=
if a ∣ a_mul_c
then if a = b ∨ a * a = a_mul_c ∨ b = 0 then 1 else 2
else 0

def loop_a : Π (b a_mul_c a : ℕ), ℕ
| b a_mul_c 0 := 0
| b a_mul_c a@(a'+1) := if b ≤ a then number_at b a_mul_c a + loop_a b a_mul_c a' else 0

/-- Given `d = b * b - 4 * a * c`, determine `a * c`. -/
def a_mul_c (d b : ℕ) : ℕ :=
(d + b * b) / 4

def loop_b : Π (d b : ℕ), ℕ
| d b@(b'+2) := loop_a b (a_mul_c d b) (nat.sqrt (a_mul_c d b)) + loop_b d b'
| d b := loop_a b (a_mul_c d b) (nat.sqrt (a_mul_c d b))

def count_u (d : ℕ) : ℕ :=
nat.sqrt (d / 3)

def count_reduced_forms (d : ℕ) : ℕ :=
loop_b d (count_u d + ((d + count_u d) % 2))

/-- List the reduced quadratic forms `of_tuple a (± b) c`, with `a * c = a_mul_c`. -/
def forms_at (b a_mul_c a : ℕ) : list QF₂ℤ :=
if a ∣ a_mul_c
then if a = b ∨ a * a = a_mul_c ∨ b = 0
  then [of_tuple a b (a_mul_c / a)]
  else [of_tuple a b (a_mul_c / a), of_tuple a (-b) (a_mul_c / a)]
else []

lemma nat.div_add {b : ℕ} (a c : ℕ) (h : 0 < b) : a / b + c = (a + b * c) / b :=
by simp [nat.add_div h, nat.mul_div_right _ h, not_le_of_gt (nat.mod_lt _ h)]

@[simp] lemma a_mul_c_zero {d : ℕ} : a_mul_c d 0 = d / 4 := by simp [a_mul_c]
@[simp] lemma a_mul_c_one {d : ℕ} : a_mul_c d 1 = (d + 1) / 4 := by simp [a_mul_c]
@[simp] lemma a_mul_c_add_two {d b : ℕ} : a_mul_c d (b + 2) = (d + b * b) / 4 + b + 1 :=
calc a_mul_c d (b + 2) = (d + (b + 2) * (b + 2)) / 4 : rfl
                   ... = ((d + b * b) + 4 * (b + 1)) / 4 : by ring
                   ... = (d + b * b) / 4 + (b + 1) : (nat.div_add (d + b * b) (b + 1) (by norm_num)).symm

lemma coeff_a_of_mem_forms_at {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) : coeff_a Q = a :=
begin
  unfold forms_at at h,
  split_ifs at h;
    simp only [list.mem_cons_iff, list.mem_nil_iff, list.mem_singleton] at h;
    try {cases h};
    simpa using congr_arg coeff_a h
end

lemma coeff_b_of_mem_forms_at {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) : abs (coeff_b Q) = b :=
begin
  unfold forms_at at h,
  split_ifs at h;
    simp only [list.mem_cons_iff, list.mem_nil_iff, list.mem_singleton] at h;
    try { cases h };
    apply trans (congr_arg (abs ∘ coeff_b) h);
    simp
end

lemma coeff_b_of_mem_forms_at_of_a_eq_b {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) (a_eq_b : a = b) : coeff_b Q = b :=
begin
  unfold forms_at at h,
  simp only [if_true, eq_self_iff_true, true_or, a_eq_b] at h,
  split_ifs at h,
  { simpa using congr_arg coeff_b (list.mem_singleton.mp h) },
  { cases h }
end

lemma coeff_b_of_mem_forms_at_of_a_mul_a_eq {b a_mul_c a : ℕ} {Q : QF₂ℤ}
(h : Q ∈ forms_at b a_mul_c a) (a_eq_c : a * a = a_mul_c) : coeff_b Q = b :=
begin
  unfold forms_at at h,
  simp only [if_true, eq_self_iff_true, true_or, or_true, a_eq_c] at h,
  split_ifs at h,
  { simpa using congr_arg coeff_b (list.mem_singleton.mp h) },
  { cases h }
end

lemma coeff_c_of_mem_forms_at {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) : coeff_c Q = a_mul_c / a :=
begin
  unfold forms_at at h,
  split_ifs at h;
    simp only [list.mem_cons_iff, list.mem_nil_iff, list.mem_singleton] at h;
    try { cases h };
    apply trans (congr_arg coeff_c h);
    simp
end

lemma a_dvd_a_mul_c_of_mem_forms_at {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) : a ∣ a_mul_c :=
begin
  unfold forms_at at h,
  split_ifs at h; tidy
end

lemma coeff_a_mul_coeff_c_of_mem_forms_at {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) : coeff_a Q * coeff_c Q = a_mul_c :=
by { rw [coeff_a_of_mem_forms_at h, coeff_c_of_mem_forms_at h],
     exact_mod_cast nat.mul_div_cancel' (a_dvd_a_mul_c_of_mem_forms_at h) }

lemma coeff_b_of_mem_forms_at_of_a_mul_c_div_a_eq {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (h : Q ∈ forms_at b a_mul_c a) (a_eq_c : a_mul_c / a = a) : coeff_b Q = b :=
coeff_b_of_mem_forms_at_of_a_mul_a_eq h (trans
  (congr_arg ((*) a) a_eq_c.symm)
  (nat.mul_div_cancel' (by exact_mod_cast a_dvd_a_mul_c_of_mem_forms_at h)))

lemma mem_forms_at_pos {b a_mul_c a : ℕ} (h : a ∣ a_mul_c) :
  of_tuple a b (a_mul_c / a) ∈ forms_at b a_mul_c a :=
begin
  unfold forms_at,
  split_ifs; simp [if_pos h]
end

lemma mem_forms_at_pos' {b a_mul_c a : ℕ} {Q : QF₂ℤ} (h : a ∣ a_mul_c)
  (ha : coeff_a Q = a) (hb : coeff_b Q = b) (hc : coeff_c Q = a_mul_c / a) :
  Q ∈ forms_at b a_mul_c a :=
by { rw [←of_tuple_coeff Q, ha, hb, hc], exact mem_forms_at_pos h }

lemma mem_forms_at_neg {b a_mul_c a : ℕ} (hc : a ∣ a_mul_c)
  (a_ne_b : a ≠ b) (a_le_c : a * a ≠ a_mul_c) (b_pos : b ≠ 0) :
  of_tuple a (-b) (a_mul_c / a) ∈ forms_at b a_mul_c a :=
begin
  unfold forms_at,
  have : ¬ (a = b ∨ a * a = a_mul_c ∨ b = 0) := by tidy,
  simp [hc, this]
end

lemma mem_forms_at_neg' {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (hc : a ∣ a_mul_c) (a_ne_b : a ≠ b) (a_le_c : a * a ≠ a_mul_c) (b_pos : b ≠ 0)
  (ha : coeff_a Q = a) (hb : coeff_b Q = -b) (hc : coeff_c Q = a_mul_c / a) :
  Q ∈ forms_at b a_mul_c a :=
by { rw [←of_tuple_coeff Q, ha, hb, hc], apply mem_forms_at_neg; assumption }

lemma reduced_of_mem_forms_at {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (a_pos : 0 < a) (b_le_a : b ≤ a) (a_le_c : a * a ≤ a_mul_c)
  (hQ : Q ∈ forms_at b a_mul_c a) : is_reduced Q :=
begin
  split;
    simp only [coeff_a_of_mem_forms_at hQ, coeff_b_of_mem_forms_at hQ, coeff_c_of_mem_forms_at hQ],
  { exact int.coe_nat_le.mpr b_le_a },
  { apply int.le_div_of_mul_le; assumption_mod_cast },
  { intro h,
    convert int.coe_nat_nonneg b,
    exact coeff_b_of_mem_forms_at_of_a_eq_b hQ (int.coe_nat_inj h).symm },
  { intro h,
    convert int.coe_nat_nonneg b,
    apply coeff_b_of_mem_forms_at_of_a_mul_c_div_a_eq hQ,
    exact_mod_cast h.symm },
end

lemma distrib_and_or {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
⟨ λ ⟨p, qr⟩, qr.elim (λ q, or.inl ⟨p, q⟩) (λ r, or.inr ⟨p, r⟩),
  λ pq_pr, pq_pr.elim (λ ⟨p, q⟩, ⟨p, or.inl q⟩) (λ ⟨p, r⟩, ⟨p, or.inr r⟩) ⟩

lemma or_distrib_and {p q r : Prop} : (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) :=
  ⟨ λ ⟨pq, r⟩, pq.elim (λ p, or.inl ⟨p, r⟩) (λ q, or.inr ⟨q, r⟩),
  λ pr_qr, pr_qr.elim (λ ⟨p, r⟩, ⟨or.inl p, r⟩) (λ ⟨q, r⟩, ⟨or.inr q, r⟩) ⟩

lemma mem_forms_at_iff {b a_mul_c a : ℕ} {Q : QF₂ℤ}
  (a_pos : 0 < a) (b_le_a : b ≤ a) (a_le_c : a * a ≤ a_mul_c) :
  (Q ∈ forms_at b a_mul_c a) ↔
    (is_reduced Q ∧ coeff_a Q = a ∧ abs (coeff_b Q) = b ∧ coeff_a Q * coeff_c Q = a_mul_c) :=
begin
  split,
  { intro h,
    refine ⟨reduced_of_mem_forms_at a_pos b_le_a a_le_c h, _, _, _⟩,
    { simpa using coeff_a_of_mem_forms_at h },
    { simpa using coeff_b_of_mem_forms_at h },
    { simpa using coeff_a_mul_coeff_c_of_mem_forms_at h } },
  rintros ⟨hr, ha, hb, hc⟩,
  have a'_pos : (0 : ℤ) < coeff_a Q := ha.symm ▸ int.coe_nat_lt.mpr a_pos,
  have c'_eq : coeff_c Q = a_mul_c / a :=
    by rw [←hc, ha, mul_comm, int.mul_div_cancel _ (ne_of_gt (int.coe_nat_lt.mpr a_pos))],
  have a_dvd_a_mul_c : a ∣ a_mul_c := int.coe_nat_dvd.mp ⟨a_mul_c / a, (trans hc.symm (by rw [c'_eq, ha]))⟩,
  by_cases hb' : coeff_b Q < 0,
  { have hb : coeff_b Q = -b := (neg_eq_iff_neg_eq.mp (trans (abs_of_neg hb').symm hb)).symm,
    have b_nonzero : b ≠ 0 := ne_of_gt (int.coe_nat_lt.mp (neg_lt_zero.mp (hb ▸ hb'))),
    refine mem_forms_at_neg' a_dvd_a_mul_c _ _ b_nonzero ha hb c'_eq,
    { simpa [ha, hb] using hr.a_ne_neg_b_of_b_neg hb' },
    { intro h,
      apply hr.a_ne_c_of_b_neg hb' ((domain.mul_left_inj (ne_of_gt a'_pos)).mp _),
      convert congr_arg coe h; simp [ha, hc] } },
  { rw abs_of_nonneg (le_of_not_gt hb') at hb,
    refine mem_forms_at_pos' a_dvd_a_mul_c ha hb c'_eq }
end

lemma nodup_forms_at (b a_mul_c a : ℕ) : list.nodup (forms_at b a_mul_c a) :=
begin
  unfold forms_at,
  split_ifs,
  { apply list.nodup_singleton },
  { refine list.nodup_cons.mpr ⟨_, list.nodup_singleton _⟩,
    rw list.mem_singleton,
    contrapose! h_1,
    obtain ⟨_, hb, _⟩ := of_tuple_congr.mp h_1,
    apply or.inr (or.inr (int.coe_nat_eq_zero.mp _)),
    linarith },
  { exact list.nodup_nil }
end

lemma length_forms_at (b a_mul_c a : ℕ) :
  (forms_at b a_mul_c a).length = number_at b a_mul_c a :=
by { unfold forms_at number_at, split_ifs; refl }

def forms_a : Π (b a_mul_c a : ℕ), list QF₂ℤ
| b a_mul_c 0 := []
| b a_mul_c a@(a'+1) := if b ≤ a then forms_at b a_mul_c a ++ forms_a b a_mul_c a' else []

lemma coeff_a_of_mem_forms_a {b a_mul_c a : ℕ} {Q : QF₂ℤ} (h : Q ∈ forms_a b a_mul_c a) : coeff_a Q ≤ a :=
begin
  induction a,
  { cases h },
  unfold forms_a at h,
  split_ifs at h,
  { cases list.mem_append.mp h with h h,
    { exact coeff_a_of_mem_forms_at h ▸ (le_refl (coeff_a Q)) },
    { exact le_trans (a_ih h) (int.coe_nat_le.mpr (nat.le_succ _)) } },
  { cases h }
end

lemma coeff_b_of_mem_forms_a {b a_mul_c a : ℕ} {Q : QF₂ℤ} (h : Q ∈ forms_a b a_mul_c a) :
  abs (coeff_b Q) = b :=
begin
  induction a,
  { cases h },
  unfold forms_a at h,
  split_ifs at h,
  { cases list.mem_append.mp h with h h,
    { exact coeff_b_of_mem_forms_at h },
    { exact a_ih h } },
  { cases h }
end

lemma mem_forms_a_iff {b a_mul_c a : ℕ} {Q : QF₂ℤ} (a_le_c : a * a ≤ a_mul_c) :
  (Q ∈ forms_a b a_mul_c a) ↔ (is_reduced Q ∧ 0 < coeff_a Q ∧ coeff_a Q ≤ a ∧ abs (coeff_b Q) = b ∧ coeff_a Q * coeff_c Q = a_mul_c) :=
begin
  induction a; unfold forms_a,
  { tidy, linarith },
  split_ifs with hba,
  { have mem_at := @mem_forms_at_iff _ _ _ Q (nat.zero_lt_succ _) hba a_le_c,
    have mem_a := a_ih (le_trans (nat.mul_self_le_mul_self (nat.le_succ _)) a_le_c),
    simp only [list.mem_append, mem_at, mem_a, ←distrib_and_or],
    split; rintro ⟨hr, h⟩; use hr,
    { rcases h with ⟨ha', hb', hc'⟩ | ⟨a'_pos, ha', hb', hc'⟩,
      { exact ⟨ha'.symm ▸ int.coe_nat_lt.mpr (nat.zero_lt_succ a_n), le_of_eq ha', hb', hc'⟩ },
      refine ⟨a'_pos, le_trans ha' (by exact_mod_cast (nat.le_succ _)), hb', hc'⟩ },
    { rcases h with ⟨a_pos, ha', hb', hc'⟩,
      by_cases coeff_a Q = a_n.succ,
      { exact or.inl ⟨h, hb', hc'⟩ },
      { have : coeff_a Q < nat.succ a_n := lt_of_le_of_ne ha' h,
        exact or.inr ⟨a_pos, int.lt_add_one_iff.mp (by exact_mod_cast this), hb', hc'⟩ } } },
  { simp only [list.mem_nil_iff, false_iff, int.coe_nat_succ],
    rintro ⟨hr, a_pos, ha', hb', hc'⟩,
    linarith [hr.abs_b_le_a] },
end

lemma nodup_forms_a (b a_mul_c a : ℕ) : list.nodup (forms_a b a_mul_c a) :=
begin
  induction a; unfold forms_a,
  { exact list.nodup_nil },
  split_ifs,
  { refine list.nodup_append.mpr ⟨nodup_forms_at _ _ _, a_ih, _⟩,
    intros Q Q_mem_at Q_mem_a,
    refine not_le_of_gt (nat.lt_succ_self a_n) (int.coe_nat_le.mp _),
    convert coeff_a_of_mem_forms_a Q_mem_a,
    exact (coeff_a_of_mem_forms_at Q_mem_at).symm },
  { exact list.nodup_nil }
end

lemma length_forms_a : Π (b a_mul_c a : ℕ), (forms_a b a_mul_c a).length = loop_a b a_mul_c a
| b a_mul_c 0 := rfl
| b a_mul_c a@(a'+1) :=
by { unfold forms_a loop_a, split_ifs; simp [length_forms_at, length_forms_a b a_mul_c a'] }

/-- List the forms of determinant `-d` with given value for `abs b` -/
def forms_b : Π (d b : ℕ), list QF₂ℤ
| d b@0 := forms_a b (a_mul_c d b) (nat.sqrt (a_mul_c d b))
| d b@1 := forms_a b (a_mul_c d b) (nat.sqrt (a_mul_c d b))
| d b@(b'+2) := forms_a b (a_mul_c d b) (nat.sqrt (a_mul_c d b)) ++ forms_b d b'

lemma int.le_sqrt_of_mul_self_le {a b : ℤ} (h : a * a ≤ b) : a ≤ int.sqrt b :=
if ha : a < 0
then le_trans (le_of_lt ha) (int.sqrt_nonneg b)
else begin
  have a_nonneg : 0 ≤ a := le_of_not_gt ha,
  have b_nonneg : 0 ≤ b := le_trans (mul_self_nonneg _) h,
  rw [←int.to_nat_of_nonneg a_nonneg, ←int.to_nat_of_nonneg b_nonneg] at ⊢ h,
  exact int.coe_nat_le.mpr (nat.le_sqrt.mpr (by exact_mod_cast h))
end

lemma int.le_sqrt {a b : ℤ} (a_nonneg : 0 ≤ a) (b_nonneg : 0 ≤ b) : a ≤ int.sqrt b ↔ a * a ≤ b :=
begin
  rw [←int.to_nat_of_nonneg a_nonneg, ←int.to_nat_of_nonneg b_nonneg],
  apply iff.trans int.coe_nat_le,
  apply iff.trans nat.le_sqrt,
  norm_cast
end

lemma int.coe_nat_sqrt {n : ℕ} : (nat.sqrt n : ℤ) = int.sqrt n :=
rfl

@[simp] lemma nat.dvd_self_mul_add {a b c : ℕ} : a ∣ a * b + c ↔ a ∣ c :=
if a_zero : a = 0 then by rw [a_zero, zero_mul, zero_add]
else have a_pos : 0 < a := nat.pos_of_ne_zero a_zero,
⟨ λ ⟨d, h⟩, ⟨d - b, (by rw [nat.mul_sub_left_distrib, ←h, add_comm, nat.add_sub_cancel])⟩,
  λ ⟨d, h⟩, ⟨b + d, by rw [h, mul_add]⟩ ⟩

@[simp] lemma int.dvd_self_mul_add {a b c : ℤ} : a ∣ a * b + c ↔ a ∣ c :=
⟨ λ ⟨d, h⟩, ⟨d - b, (by rw [mul_sub, ←h, add_comm, add_sub_cancel])⟩,
  λ ⟨d, h⟩, ⟨b + d, by rw [h, mul_add]⟩ ⟩

@[simp] lemma nat.mul_add_mod_self_left (a b c : ℕ) : (a * b + c) % a = c % a :=
by rw [nat.add_mod, nat.mul_mod_right, zero_add, nat.mod_mod]

@[simp] lemma int.mul_add_mod_self_left (a b c : ℤ) : (a * b + c) % a = c % a :=
by rw [←int.mod_add_mod, int.mul_mod_right, zero_add]

@[simp] lemma nat.add_mod_mod {a b n : ℕ} : (a + b % n) % n = (a + b) % n :=
by rw [nat.add_mod, nat.mod_mod, ←nat.add_mod]

@[simp] lemma nat.mod_add_mod {a b n : ℕ} : (a % n + b) % n = (a + b) % n :=
by rw [nat.add_mod, nat.mod_mod, ←nat.add_mod]

lemma coeff_b_of_mem_forms_b : Π {d b : ℕ} {Q : QF₂ℤ}, Q ∈ forms_b d b → abs (coeff_b Q) ≤ b
| d 0 Q hQ := le_of_eq (coeff_b_of_mem_forms_a hQ)
| d 1 Q hQ := le_of_eq (coeff_b_of_mem_forms_a hQ)
| d b@(b'+2) Q hQ := (list.mem_append.mp hQ).elim
  (λ hQ, le_of_eq (coeff_b_of_mem_forms_a hQ))
  (λ hQ, le_trans (coeff_b_of_mem_forms_b hQ) (int.coe_nat_le.mpr (nat.le.intro rfl)))

lemma mem_forms_b_aux {Q : QF₂ℤ} (hr : is_reduced Q) :
  coeff_a Q ≤ int.sqrt ((-discr' Q + coeff_b Q * coeff_b Q) / 4) :=
int.le_sqrt_of_mul_self_le (le_trans
  (mul_le_mul_of_nonneg_left hr.a_le_c hr.coeff_a_nonneg)
  (int.le_div_of_mul_le (by norm_num)
                        (le_of_eq (by simp [discr', mul_assoc, mul_comm, mul_left_comm]))))

lemma mul_self_eq_of_abs_eq {a b : ℤ} (h : abs a = b) : a * a = b * b :=
by rw [←abs_mul_self, abs_mul, h]

lemma mem_forms_b_iff : Π {d b : ℕ} (hd : (4 : ℤ) ∣ d + b * b) {Q : QF₂ℤ},
  (Q ∈ forms_b d b) ↔ (is_reduced Q ∧ 0 < coeff_a Q ∧ abs (coeff_b Q) ≤ b ∧ discr' Q = -d)
| d 0 hd Q := (mem_forms_a_iff (nat.sqrt_le _)).trans
begin
  simp only [int.coe_nat_zero, abs_nonpos_iff, abs_eq_zero, a_mul_c_zero, int.coe_nat_div],
  split; rintros ⟨hr, a'_pos, h⟩; use hr; use a'_pos,
  { rcases h with ⟨ha, hb, hc⟩,
    refine ⟨hb, _⟩,
    simp [discr', hb, mul_assoc, hc, int.mul_div_cancel' (by simpa using hd)] },
  { rcases h with ⟨hb, hc⟩,
    refine ⟨_, hb, _⟩,
    { convert mem_forms_b_aux hr,
      simp [hc, hb],
      refl },
    { simp [eq_neg_of_eq_neg hc, discr', hb, mul_assoc, (show (4 : ℤ) ≠ 0, by norm_num)] } }
end
| d 1 hd Q := (mem_forms_a_iff (nat.sqrt_le _)).trans
begin
  simp only [a_mul_c_one, int.coe_nat_one, mul_one, int.coe_nat_div, int.coe_nat_add] at *,
  split; rintros ⟨hr, a'_pos, h⟩; use hr; use a'_pos,
  { rcases h with ⟨ha, hb, hc⟩,
    refine ⟨le_of_eq hb, _⟩,
    rw [discr', ←abs_mul_self (coeff_b Q), abs_mul, hb],
    simp [mul_assoc, hc, int.mul_div_cancel' (by simpa using hd), sub_eq_add_neg] },
  { rcases h with ⟨hb, hc⟩,
    by_cases h : abs (coeff_b Q) = 0,
    { exfalso,
      cases hd with d_div_4 hd,
      suffices : (- -(4 * coeff_a Q * coeff_c Q) + ↑1 * ↑1) % 4 = (4 * d_div_4) % 4,
      { convert this;
          try { rw [←int.mod_add_mod, mul_assoc] };
        norm_num },
      congr' 1,
      simpa [discr', eq_neg_of_eq_neg hc, abs_eq_zero.mp h] using hd },
    have hb : abs (coeff_b Q) = 1 := le_antisymm hb (lt_of_le_of_ne (abs_nonneg _) (ne.symm h)),
    refine ⟨_, hb, _⟩,
    { convert mem_forms_b_aux hr,
      rw [hc, mul_self_eq_of_abs_eq hb, neg_neg],
      refl },
    { simp [eq_neg_of_eq_neg hc, discr', mul_self_eq_of_abs_eq hb, mul_assoc, (show (4 : ℤ) ≠ 0, by norm_num)] } }
end
| d b@(nat.succ (nat.succ b_n)) hd Q := list.mem_append.trans
begin
  have hd_n : (4 : ℤ) ∣ d + b_n * b_n,
  { rcases hd with ⟨d_div_4, hd⟩,
    use d_div_4 - (b_n + 1),
    rw [eq_sub_of_add_eq hd, int.coe_nat_succ, int.coe_nat_succ],
    ring },
  simp only [mem_forms_a_iff (nat.sqrt_le _), mem_forms_b_iff hd_n, ←distrib_and_or, int.coe_nat_succ] at *,
  split; rintros ⟨hr, a'_pos, h⟩; use hr; use a'_pos,
  { rcases h with ⟨ha, hb, hc⟩ | ⟨hb, hc⟩,
    { refine ⟨le_of_eq hb, _⟩,
      erw [discr', mul_assoc, hc, mul_self_eq_of_abs_eq hb, a_mul_c, int.mul_div_cancel' hd],
      ring },
    { refine ⟨_, hc⟩,
      linarith } },
  { rcases h with ⟨hb, hc⟩,
    by_cases b'_le_b_n : abs (coeff_b Q) ≤ b_n,
    { exact or.inr ⟨b'_le_b_n, hc⟩ },
    by_cases b'_eq_succ_b_n : abs (coeff_b Q) = b_n + 1,
    { exfalso,
      obtain ⟨d, h⟩ := show 4 ∣ 2 * abs (coeff_b Q) + 1,
      by { apply (@int.dvd_self_mul_add _ (coeff_a Q * coeff_c Q) _).mp,
        convert hd using 1,
        rw [eq_neg_of_eq_neg hc, ←b'_eq_succ_b_n, discr', add_mul, mul_add, ←abs_mul, abs_mul_self],
        ring },
      cases (int.dvd_iff_mod_eq_zero _ _).mp (int.dvd_self_mul_add.mp ⟨2 * d, trans h (mul_assoc 2 2 d)⟩) },
    have b'_eq_succ_succ_b_n : abs (coeff_b Q) = b_n + 1 + 1 := le_antisymm hb
      (lt_of_le_of_ne (int.add_one_le_of_lt (lt_of_not_ge b'_le_b_n)) (ne.symm b'_eq_succ_b_n)),
    simp only [int.coe_nat_sqrt, a_mul_c, int.coe_nat_div, int.coe_nat_mul, int.coe_nat_add, int.coe_nat_succ, ←b'_eq_succ_succ_b_n, int.coe_nat_zero, zero_add, eq_neg_of_eq_neg hc, ←abs_mul, abs_mul_self],
    refine or.inl ⟨mem_forms_b_aux hr, rfl, _⟩,
    convert (int.mul_div_cancel_left (coeff_a Q * coeff_c Q) (show (4 : ℤ) ≠ 0, by norm_num)).symm,
    simp [discr', mul_assoc] },
end

lemma nodup_forms_b : Π (d b : ℕ), list.nodup (forms_b d b)
| d 0 := nodup_forms_a _ _ _
| d 1 := nodup_forms_a _ _ _
| d b@(b'+2) := begin
  refine list.nodup_append.mpr ⟨nodup_forms_a _ _ _, nodup_forms_b _ _, _⟩,
  intros Q Q_mem_a Q_mem_b,
  refine not_le_of_gt (show b' < b' + 2, by linarith) (int.coe_nat_le.mp _),
  convert coeff_b_of_mem_forms_b Q_mem_b,
  exact (coeff_b_of_mem_forms_a Q_mem_a).symm
end

lemma length_forms_b : Π (d b : ℕ), (forms_b d b).length = loop_b d b
| d b@0 := by simp [forms_b, loop_b, length_forms_a]
| d b@1 := by simp [forms_b, loop_b, length_forms_a]
| d b@(b'+2) := by simp [forms_b, loop_b, length_forms_a, length_forms_b d b']

def list_reduced_forms (d : ℕ) : list QF₂ℤ :=
forms_b d (count_u d + (d + count_u d) % 2)

lemma mem_list_reduced_forms_aux_left {a : ℕ} (b : ℕ) (ha : a % 4 = 0) :
  4 ∣ a + (b + (a + b) % 2) * (b + (a + b) % 2) :=
begin
  rw [←nat.mod_add_div a 4, ha, zero_add, nat.dvd_self_mul_add],
  suffices : 2 ∣ (b + (4 * (a / 4) + b) % 2),
  { exact mul_dvd_mul this this },
  apply (nat.dvd_iff_mod_eq_zero _ _).mpr,
  simp [(show 4 = 2 * 2, from rfl), mul_assoc, ←two_mul]
end

lemma mem_list_reduced_forms_aux_right {a : ℕ} (b : ℕ) (ha : a % 4 = 3) :
  4 ∣ a + (b + (a + b) % 2) * (b + (a + b) % 2) :=
begin
  rw [←nat.mod_add_div a 4, ha, add_comm 3 (4 * _), add_assoc, nat.dvd_self_mul_add],
  suffices : (4 : ℤ) ∣ (b + ((4 * (a / 4) + 3 + b) % 2)) * (b + ((4 * (a / 4) + 3 + b) % 2)) - 1,
  { have := dvd_add this (dvd_refl 4),
    apply int.coe_nat_dvd.mp,
    convert this using 1,
    simp,
    ring },
  suffices dvd_sub_one : (2 : ℤ) ∣ 1 + b + (4 * (a / 4) + 3 + b) % 2,
  { have dvd_add_one := dvd_add dvd_sub_one ⟨-1, rfl⟩,
    convert mul_dvd_mul dvd_sub_one dvd_add_one using 1,
    ring },
  have : ((4 : ℤ) * (a / 4) + 3 + b) % 2 = (1 + b) % 2,
  { rw [←int.mod_add_mod, bit0, ←two_mul, mul_assoc, int.mul_add_mod_self_left, bit1, int.add_mod_self_left, int.mod_add_mod] },
  apply (int.dvd_iff_mod_eq_zero _ _).mpr,
  rw [this, int.add_mod_mod, ←two_mul, int.mul_mod_right]
end

lemma mem_list_reduced_forms_iff {d : ℕ} {Q : QF₂ℤ} (hd : d ≡ 0 [MOD 4] ∨ d ≡ 3 [MOD 4]) :
  (Q ∈ list_reduced_forms d) ↔ (is_reduced Q ∧ 0 < coeff_a Q ∧ discr' Q = -d) :=
begin
  refine iff.trans (mem_forms_b_iff _) _,
  { exact int.coe_nat_dvd.mpr (hd.elim (mem_list_reduced_forms_aux_left _) (mem_list_reduced_forms_aux_right _)) },
  split,
  { exact λ ⟨hr, ha, _, hc⟩, ⟨hr, ha, hc⟩ },
  rintros ⟨hr, ha, hc⟩,
  refine ⟨hr, ha, le_trans hr.abs_b_le_a _, hc⟩,
  simp only [int.coe_nat_add, count_u, int.coe_nat_mul, int.coe_nat_sqrt, int.coe_nat_div, add_zero],
  apply le_trans _ (add_le_add_left (int.coe_nat_nonneg _) _),
  apply int.le_sqrt_of_mul_self_le,
  apply (int.le_div_iff_mul_le (show (0 : ℤ) < 3, by norm_num)).mpr,
  rw [mul_comm, ←mul_assoc],
  convert @coeff_a_bound (-d) _ hr _; simp [hc]
end

lemma mem_list_reduced_forms {d : ℕ} (hd : d ≡ 0 [MOD 4] ∨ d ≡ 3 [MOD 4]) (d_nonzero : d ≠ 0) {Q : QF₂ℤ} :
  Q ∈ list_reduced_forms d ↔ (discr' Q = -d ∧ pos_def Q.val ∧ is_reduced Q) :=
have discr' Q = -d → discr' Q < 0 :=
  λ hd, (by simpa [hd] using lt_of_le_of_ne (nat.zero_le d) d_nonzero.symm),
(mem_list_reduced_forms_iff hd).trans
  ⟨ λ ⟨hr, ha, hd⟩, ⟨hd, (pos_def_iff_of_discr_neg (this hd)).mpr ha, hr⟩,
    λ ⟨hd, hpd, hr⟩, ⟨hr, coeff_a_pos hpd, hd⟩ ⟩

lemma to_finset_list_reduced_forms {d : ℕ} (hd : d ≡ 0 [MOD 4] ∨ d ≡ 3 [MOD 4]) (d_nonzero : d ≠ 0) :
  list.to_finset (list_reduced_forms d) = reduced_forms d :=
finset.ext.mpr (λ Q, (list.mem_to_finset.trans
                     (mem_list_reduced_forms hd d_nonzero)).trans
                     mem_reduced_forms_iff.symm)

lemma nodup_list_reduced_forms (d : ℕ) : list.nodup (list_reduced_forms d) :=
nodup_forms_b _ _

lemma length_list_reduced_forms (d : ℕ) : (list_reduced_forms d).length = count_reduced_forms d :=
length_forms_b _ _

lemma list.card_to_finset_of_nodup {α} [decidable_eq α] {l : list α} (h : l.nodup): l.to_finset.card = l.length :=
congr_arg list.length (list.erase_dup_eq_self.mpr h)

theorem count_reduced_forms_correct {d : ℕ} (hd : d ≡ 0 [MOD 4] ∨ d ≡ 3 [MOD 4]) (d_nonzero : d ≠ 0) :
  count_reduced_forms d = (reduced_forms d).card :=
calc
count_reduced_forms d
    = (list_reduced_forms d).length : (length_list_reduced_forms d).symm
... = (list_reduced_forms d).to_finset.card : (list.card_to_finset_of_nodup (nodup_list_reduced_forms _)).symm
... = (reduced_forms d).card : congr_arg finset.card (to_finset_list_reduced_forms hd d_nonzero)

#eval count_reduced_forms 37

end int_bin_quadratic_form

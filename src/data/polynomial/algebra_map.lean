/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.induction
import data.polynomial.degree

/-!
# Theory of univariate polynomials

We show that `polynomial A` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `eval`.
-/

noncomputable theory

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

lemma C_mul' (a : R) (f : polynomial R) : C a * f = a • f :=
ext $ λ n, coeff_C_mul f

lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

end semiring

section comm_semiring
variables [comm_semiring R] {p q r : polynomial R}

variables [semiring A] [algebra R A]

/-- Note that this instance also provides `algebra R (polynomial R)`. -/
instance algebra_of_algebra : algebra R (polynomial A) := add_monoid_algebra.algebra

lemma algebra_map_apply (r : R) :
  algebra_map R (polynomial A) r = C (algebra_map R A r) :=
rfl

/--
When we have `[comm_ring R]`, the function `C` is the same as `algebra_map R (polynomial R)`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
lemma C_eq_algebra_map {R : Type*} [comm_ring R] (r : R) :
  C r = algebra_map R (polynomial R) r :=
rfl


@[simp]
lemma alg_hom_eval₂_algebra_map
  {R A B : Type*} [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B]
  (p : polynomial R) (f : A →ₐ[R] B) (a : A) :
  f (eval₂ (algebra_map R A) a p) = eval₂ (algebra_map R B) (f a) p :=
begin
  dsimp [eval₂, finsupp.sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast, alg_hom.commutes],
end

@[simp]
lemma eval₂_algebra_map_X {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (p : polynomial R) (f : polynomial R →ₐ[R] A) :
  eval₂ (algebra_map R A) (f X) p = f p :=
begin
  conv_rhs { rw [←polynomial.sum_C_mul_X_eq p], },
  dsimp [eval₂, finsupp.sum],
  simp only [f.map_sum, f.map_mul, f.map_pow, ring_hom.eq_int_cast, ring_hom.map_int_cast],
  simp [polynomial.C_eq_algebra_map],
end

@[simp]
lemma ring_hom_eval₂_algebra_map_int {R S : Type*} [ring R] [ring S]
  (p : polynomial ℤ) (f : R →+* S) (r : R) :
  f (eval₂ (algebra_map ℤ R) r p) = eval₂ (algebra_map ℤ S) (f r) p :=
alg_hom_eval₂_algebra_map p f.to_int_alg_hom r

@[simp]
lemma eval₂_algebra_map_int_X {R : Type*} [ring R] (p : polynomial ℤ) (f : polynomial ℤ →+* R) :
  eval₂ (algebra_map ℤ R) (f X) p = f p :=
-- Unfortunately `f.to_int_alg_hom` doesn't work here, as typeclasses don't match up correctly.
eval₂_algebra_map_X p { commutes' := λ n, by simp, .. f }

/- -- Move me!
section eval
variable {x : R}

@[simp] lemma eval_mul : (p * q).eval x = p.eval x * q.eval x := eval₂_mul _ _

instance eval.is_semiring_hom : is_semiring_hom (eval x) := eval₂.is_semiring_hom _ _

@[simp] lemma eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n := eval₂_pow _ _ _

lemma eval₂_hom [comm_semiring S] (f : R →+* S) (x : R) :
  p.eval₂ f (f x) = f (p.eval x) :=
polynomial.induction_on p
  (by simp)
  (by simp [f.map_add] {contextual := tt})
  (by simp [f.map_mul, eval_pow,
    f.map_pow, pow_succ', (mul_assoc _ _ _).symm] {contextual := tt})

lemma root_mul_left_of_is_root (p : polynomial R) {q : polynomial R} :
  is_root q a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

lemma root_mul_right_of_is_root {p : polynomial R} (q : polynomial R) :
  is_root p a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

end eval
-/

section comp

lemma eval₂_comp [comm_semiring S] (f : R →+* S) {x : S} :
  (p.comp q).eval₂ f x = p.eval₂ f (q.eval₂ f x) :=
by rw [comp, p.as_sum]; simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_finset_sum, eval₂_X]

/- Move me!
lemma eval_comp : (p.comp q).eval a = p.eval (q.eval a) := eval₂_comp _
-/

instance : is_semiring_hom (λ q : polynomial R, q.comp p) :=
by unfold comp; apply_instance

@[simp] lemma mul_comp : (p * q).comp r = p.comp r * q.comp r := eval₂_mul _ _

end comp

end comm_semiring


section eval
variables [comm_semiring R] {p : polynomial R}

-- TODO this could be generalized: there's no need for `A` to be commutative,
-- we just need that `x` is central.
variables [comm_semiring A] [algebra R A]
variables {B : Type*} [comm_semiring B] [algebra R B]
variables (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `eval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
def eval : polynomial R →ₐ[R] A :=
{ commutes' := λ r, eval₂_C _ _,
  ..eval₂_ring_hom (algebra_map R A) x }

theorem eval_def (p : polynomial R) : eval x p = eval₂ (algebra_map R A) x p := rfl

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial R) (a : R) : Prop := eval a p = 0

instance [decidable_eq R] : decidable (is_root p a) := by unfold is_root; apply_instance

@[simp] lemma is_root.def : is_root p a ↔ eval a p = 0 := iff.rfl

@[simp] lemma eval_X : eval x (X : polynomial R) = x := eval₂_X _ x

@[simp] lemma eval_C (r : R) : eval x (C r) = algebra_map R A r := eval₂_C _ x

theorem eval_unique (φ : polynomial R →ₐ[R] A) (p) :
  φ p = eval₂ (algebra_map R A) (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [φ.map_add, ih1, ih2, eval₂_add] },
  { intros n r ih,
    rw [pow_succ', ← mul_assoc, φ.map_mul, eval₂_mul (algebra_map R A), eval₂_X, ih] }
end

theorem eval_alg_hom (f : A →ₐ[R] B) (x : A) : eval (f x) = f.comp (eval x) :=
alg_hom.ext $ λ p, by rw [eval_unique (f.comp (eval x)), alg_hom.comp_apply, eval_X, eval_def]

theorem eval_alg_hom_apply (f : A →ₐ[R] B) (x : A) (p : polynomial R) :
  eval (f x) p = f (eval x p) :=
alg_hom.ext_iff.1 (eval_alg_hom f x) p

lemma coeff_zero_eq_eval_zero (p : polynomial R) : p.coeff 0 = eval 0 p :=
calc coeff p 0 = coeff p 0 * 0 ^ 0 : by simp
... = eval 0 p : eq.symm $
  finset.sum_eq_single _ (λ b _ hb, by simp [zero_pow (nat.pos_of_ne_zero hb)]) (by simp)

lemma pow_comp (p q : polynomial R) (k : ℕ) : (p ^ k).comp q = (p.comp q) ^ k :=
by { unfold comp, rw ← coe_eval₂_ring_hom, apply ring_hom.map_pow }

variables [comm_ring S] {f : R →+* S}

lemma is_root_of_eval₂_map_eq_zero
  (hf : function.injective f) {r : R} : eval₂ f (f r) p = 0 → p.is_root r :=
show eval₂ (f.comp (ring_hom.id R)) (f r) p = 0 → eval₂ (ring_hom.id R) r p = 0, begin
  intro h,
  apply hf,
  rw [hom_eval₂, h, f.map_zero]
end

lemma is_root_of_eval_algebra_map_eq_zero [algebra R S] {p : polynomial R}
  (inj : function.injective (algebra_map R S))
  {r : R} (hr : eval (algebra_map R S r) p = 0) : p.is_root r :=
is_root_of_eval₂_map_eq_zero inj hr

lemma dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : polynomial S} (i : ℕ)
  (dvd_eval : p ∣ eval z f) (dvd_terms : ∀ (j ≠ i), p ∣ f.coeff j * z ^ j) :
  p ∣ f.coeff i * z ^ i :=
begin
  by_cases hf : f = 0,
  { simp [hf] },
  by_cases hi : i ∈ f.support,
  { have dvd_eval : p ∣ ∑ (a : ℕ) in f.support, algebra_map S S (f.coeff a) * z ^ a := dvd_eval,
    rw [←finset.insert_erase hi, finset.sum_insert (finset.not_mem_erase _ _)] at dvd_eval,
    refine (dvd_add_left (finset.dvd_sum _)).mp dvd_eval,
    intros j hj,
    exact dvd_terms j (finset.ne_of_mem_erase hj) },
  { convert dvd_zero p,
    convert _root_.zero_mul _,
    exact finsupp.not_mem_support_iff.mp hi }
end

lemma dvd_term_of_is_root_of_dvd_terms {r p : S} {f : polynomial S} (i : ℕ)
  (hr : f.is_root r) (h : ∀ (j ≠ i), p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
dvd_term_of_dvd_eval_of_dvd_terms i (eq.symm hr ▸ dvd_zero p) h

end eval

section ring
variables [ring R]

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
lemma eval_mul_X_sub_C {p : polynomial R} (r : R) :
  eval r (p * (X - C r)) = 0 :=
begin
  simp only [eval, eval₂, ring_hom.id_apply],
  have bound := calc
    (p * (X - C r)).nat_degree
         ≤ p.nat_degree + (X - C r).nat_degree : nat_degree_mul_le
     ... ≤ p.nat_degree + 1 : add_le_add_left nat_degree_X_sub_C_le _
     ... < p.nat_degree + 2 : lt_add_one _,
  rw sum_over_range' _ _ (p.nat_degree + 2) bound,
  swap,
  { simp, },
  rw sum_range_succ',
  conv_lhs {
    congr, apply_congr, skip,
    rw [coeff_mul_X_sub_C, sub_mul, mul_assoc, ←pow_succ],
  },
  simp [sum_range_sub', coeff_single],
end

theorem not_is_unit_X_sub_C [nontrivial R] {r : R} : ¬ is_unit (X - C r) :=
λ ⟨⟨_, g, hfg, hgf⟩, rfl⟩, @zero_ne_one R _ _ $ by erw [← eval_mul_X_sub_C, hgf, eval_one]

end ring

end polynomial

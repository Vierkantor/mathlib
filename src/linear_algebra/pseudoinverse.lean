import data.matrix.basic
import linear_algebra.nonsingular_inverse
import tactic.linarith
import tactic.omega

/-! Pseudoinverse matrices -/

namespace matrix
universes u v
variables {m n : Type} [fintype m] [fintype n] {α : Type v} [field α]
open_locale matrix

-- Workaround for `omega` not liking `i.1` as element of the conditions.
lemma fin.sum_of_add_aux {a b c : ℕ} : ¬c < a → c < a + b → c - a < b := by omega

def fin.sum_of_add {a b : ℕ} : fin (a + b) → sum (fin a) (fin b) := λ i,
if h : i.1 < a then sum.inl ⟨i.1, h⟩ else sum.inr ⟨i.1 - a, fin.sum_of_add_aux h i.2⟩

def block {a b c d : ℕ} :
  matrix (fin a) (fin b) α → matrix (fin a) (fin d) α → matrix (fin c) (fin b) α → matrix (fin c) (fin d) α → matrix (fin (a + c)) (fin (b + d)) α :=
λ A B C D i j, match (fin.sum_of_add i, fin.sum_of_add j) with
| (sum.inl i, sum.inl j) := A i j
| (sum.inl i, sum.inr j) := B i j
| (sum.inr i, sum.inl j) := C i j
| (sum.inr i, sum.inr j) := D i j
end

/-- For a matrix `A` this is the pair `(E, P)` such that `E A P = block 1 0 0 0`. -/
def hermite_normal_form_factors (A : matrix m n α) : matrix m m α × matrix n n α := sorry

/--
  A {1}-inverse for a matrix.

  For a matrix `A`, a {1}-inverse is a matrix `X` such that:
  - `A ⬝ X ⬝ A = A` (1)

  The previous condition does not specify a unique `X` in general,
  If `A` is nonsingular, `X` will be unique and equal to the inverse of `A`.
  However, if `A` only has a left or right inverse, the equality does not necessarily hold.
-/
def inv_1 (A : matrix m n α) : matrix n m α :=
let EP := A.hermite_normal_form_factors
in EP.2 ⬝ block 1 0 0 0 ⬝ EP.1

/--
  A {1, 3}-inverse for a matrix.

  For a matrix `A`, a {1, 3}-inverse is a matrix `X` such that:
  - `A ⬝ X ⬝ A = A` (1)
  - `(A ⬝ X)ᵀ = A ⬝ X` (3)
-/
def inv_13 (A : matrix m n α) : matrix n m α := inv_1 (Aᵀ ⬝ A) ⬝ Aᵀ

/--
  A {1, 4}-inverse for a matrix.

  For a matrix `A`, a {1, 4}-inverse is a matrix `X` such that:
   - `A ⬝ X ⬝ A = A` (1)
   - `(X ⬝ A)ᵀ = X ⬝ A` (4)
-/
def inv_14 (A : matrix m n α) : matrix n m α := Aᵀ ⬝ inv_1 (A ⬝ Aᵀ)

/--
  The pseudoinverse, also known as the Moore-Penrose inverse,
  is a matrix that behaves like the inverse, but is (uniquely) defined for any matrix.
  In case a matrix is (left or right)-invertible, the pseudoinverse will coincide with the inverse.
-/
def pseudoinverse (A : matrix m n α) : matrix n m α :=
inv_14 A ⬝ A ⬝ inv_13 A

end matrix

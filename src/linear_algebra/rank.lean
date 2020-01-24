import linear_algebra.matrix

universes u
variables {m n : Type u} [fintype m] [fintype n]

namespace matrix
variables {K : Type u} [decidable_eq n] [discrete_field K] (A : matrix m n K)
open linear_map
open submodule
open_locale matrix

def std_basis_vec (K : Type u) [has_one K] [has_zero K] (i j : n) : K := if i = j then 1 else 0

@[simp] lemma std_basis_vec_def (i j : n) : std_basis_vec K i j = if i = j then 1 else 0 := rfl
@[simp] lemma std_basis_vec_same (i : n) : std_basis_vec K i i = 1 := if_pos rfl
@[simp] lemma std_basis_vec_eq {i j : n} (h : i = j) : std_basis_vec K i j = 1 := if_pos h
@[simp] lemma std_basis_vec_ne {i j : n} (h : i ≠ j) : std_basis_vec K i j = 0 := if_neg h

def std_basis_one_eq_std_basis_vec (j : n) :
  std_basis K (λ _ : n, K) j 1 = std_basis_vec K j :=
begin
  ext i, by_cases h : i = j,
  { rw [h, std_basis_same, std_basis_vec_same] },
  { rw [std_basis_ne K _ _ _ h, std_basis_vec_ne (λ p, h p.symm)] }
end

lemma mul_vec_val (i : m) (v : n → K) : A.mul_vec v i = finset.univ.sum (λ j, A i j * v j) := rfl
lemma to_lin_val (i : m) (v : n → K) : (A.to_lin : (n → K) → m → K) v i = finset.univ.sum (λ j, A i j * v j) := rfl

lemma mul_vec_std_basis_vec (i : m) (j : n) :
  A.mul_vec (std_basis_vec K j) i = A i j :=
by { simp_rw [mul_vec_val, std_basis_vec_def, mul_ite, finset.sum_ite_eq, if_pos (finset.mem_univ _)] }

lemma to_lin_std_basis_vec (j : n) :
  (A.to_lin : (n → K) → (m → K)) (std_basis_vec K j) = λ i, A i j :=
by { ext i, exact mul_vec_std_basis_vec A i j }

section col_row_space

/-- The set of columns of a matrix. -/
def column_set : set (m → K) := set.range (λ j i, A i j)
/-- The set of rows of a matrix. -/
def row_set : set (n → K) := set.range (λ i j, A i j)

/-- The space spanned by the columns of a matrix.

In the lemma `column_space_eq_range`, we will prove that this is equal to the range of the matrix.
-/
def column_space : submodule K (m → K) := span K (column_set A)
/-- The space spanned by the rows of a matrix. -/
def row_space : submodule K (n → K) := span K (row_set A)

lemma column_mem_column_space (j : n) : (λ i, A i j) ∈ column_space A := subset_span (set.mem_range.mpr ⟨j, rfl⟩)

/-- A basis for the column space. -/
def column_basis : set (column_space A) := classical.some (exists_is_basis K (column_space A))
def column_basis_is_basis : is_basis K (λ (i : (column_basis A : Type u)), i.val) :=
classical.some_spec (exists_is_basis K (column_space A))
/-- A basis for the row space. -/
def row_basis : set (row_space A) := classical.some (exists_is_basis K (row_space A))
def row_basis_is_basis := classical.some_spec (exists_is_basis K (row_space A))

/-
TODO: We should really have computable versions of these, then we could write:
def column_rank : ℕ := finset.card column_basis
def row_rank : ℕ := finset.card row_basis
-/

lemma finite_dim_column_space : vector_space.dim K (column_space A) < cardinal.omega :=
calc vector_space.dim K (column_space A) ≤ cardinal.mk (column_set A) : dim_span_le _
... ≤ cardinal.mk n : cardinal.mk_range_le
... = fintype.card n : cardinal.fintype_card n
... < cardinal.omega : cardinal.nat_lt_omega _

lemma card_column_basis_eq_dim_column_space :
  cardinal.mk (column_basis A) = vector_space.dim K (column_space A) :=
begin
  have := is_basis.mk_eq_dim (column_basis_is_basis A),
  simp only [cardinal.lift_id] at this,
  exact this
end

lemma finite_column_basis : cardinal.mk (column_basis A) < cardinal.omega :=
calc cardinal.mk (column_basis A) = vector_space.dim K (column_space A) : card_column_basis_eq_dim_column_space A
... < cardinal.omega : finite_dim_column_space A

noncomputable instance fintype_column_basis : fintype (column_basis A) :=
classical.choice (cardinal.lt_omega_iff_fintype.mp (finite_column_basis A))

/-- The matrix containing the basis of the matrix's column space. -/
def column_reduction : matrix m (column_basis A) K :=
λ i j, j.1.1 i

/-- The matrix containing the coordinate in the column basis for each of the matrix columns. -/
noncomputable def row_reduction : matrix (column_basis A) n K :=
λ i j, (is_basis.repr (column_basis_is_basis A)).to_fun
  ⟨(λ i, A i j), column_mem_column_space A j⟩ i

#check linear_independent.repr
#check finsupp

lemma column_reduction_mul_row_reduction : column_reduction A ⬝ row_reduction A = A :=
funext (λ i, funext (λ j, calc
  (column_reduction A ⬝ row_reduction A) i j
      = (finset.univ : finset (column_basis A)).sum (λ v, v.1.1 i * (is_basis.repr (column_basis_is_basis A)).to_fun ⟨(λ i, A i j), column_mem_column_space A j⟩ v) : rfl
  -- ... = A i j : by rw [is_basis.repr, cod_restrict, comp, linear_independent.repr]
  ... = (λ i, A i j) i : congr_fun $ is_basis.repr_total (column_basis_is_basis A) (finsupp.equiv_fun_on_fintype.inv_fun (λ i, A i j))
))

lemma row_rank_le_column_rank : vector_space.dim K (row_space A) ≤ vector_space.dim K (column_space A) :=
sorry

end col_row_space

lemma mem_range_to_lin (v : m → K) :
  v ∈ linear_map.range A.to_lin ↔ ∃ (w : n → K), v = finset.univ.sum (λ j i, w j * A i j) :=
iff.trans mem_range begin
  split; intro h; cases h; use h_w; ext i,
  { simp_rw [h_h.symm, pi.finset_sum_apply, λ c, mul_comm (h_w c) (A i c)],
    refl },
  { simp_rw [h_h, pi.finset_sum_apply, λ c, mul_comm (h_w c) (A i c)],
    refl }
end

lemma column_space_eq_range : column_space A = A.to_lin.range :=
span_eq_of_le A.to_lin.range
  (λ x hx, have ix : _ := classical.some_spec hx,
    linear_map.mem_range.mpr
      ⟨ std_basis_vec K (classical.some hx),
        trans (to_lin_std_basis_vec _ _) ix⟩)
  begin
    intros x hx,
    rw [classical.some_spec ((mem_range_to_lin A x).mp hx)],
    apply mem_span.mpr,
    intros p hp,
    apply sum_mem,
    intros j _,
    exact smul_mem p _ (hp (set.mem_range.mpr ⟨j, rfl⟩))
  end

lemma column_rank_eq_rank : vector_space.dim K (column_space A) = rank A.to_lin :=
by { rw [column_space_eq_range], refl }

/-- A matrix has a finite rank (as a linear map) -/
lemma finite_rank : rank A.to_lin < cardinal.omega :=
calc
  rank A.to_lin = vector_space.dim K (column_space A) : symm (column_rank_eq_rank A)
  ... < cardinal.omega : finite_dim_column_space A

end matrix

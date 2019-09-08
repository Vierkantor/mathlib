/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import set_theory.game.short
import tactic.norm_num
import tactic.linarith
import tactic.tidy

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape (possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development; in order to successfully analyse positions we would
need some more theorems. Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact the disjoint parts of the chessboard give sums of games.
-/

open pgame

namespace domineering_aux

/-- The embedding `(x, y) ↦ (x, y+1)`. -/
def shift_up : ℤ × ℤ ↪ ℤ × ℤ :=
⟨λ p : ℤ × ℤ, (p.1, p.2 + 1),
 have function.injective (λ (n : ℤ), n + 1) := λ _ _, (add_right_inj 1).mp,
 function.injective_prod function.injective_id this⟩
/-- The embedding `(x, y) ↦ (x+1, y)`. -/
def shift_right : ℤ × ℤ ↪ ℤ × ℤ :=
⟨λ p : ℤ × ℤ, (p.1 + 1, p.2),
 have function.injective (λ (n : ℤ), n + 1) := λ _ _, (add_right_inj 1).mp,
 function.injective_prod this function.injective_id⟩

/-- Left can play anywhere that a square and the square above it are open. -/
def left  (b : finset (ℤ × ℤ)) : Type := { p | p ∈ b ∩ b.map shift_up }
/-- Right can play anywhere that a square and the square to the right are open. -/
def right (b : finset (ℤ × ℤ)) : Type := { p | p ∈ b ∩ b.map shift_right }

def left_empty_equiv : left ∅ ≃ pempty := by tidy
def right_empty_equiv : right ∅ ≃ pempty := by tidy

instance fintype_left (b : finset (ℤ × ℤ)) : fintype (left b) :=
fintype.subtype _ (λ x, iff.refl _)

instance fintype_right (b : finset (ℤ × ℤ)) : fintype (right b) :=
fintype.subtype _ (λ x, iff.refl _)

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def move_left (b : finset (ℤ × ℤ)) (m : left b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1, m.val.2 - 1)
/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def move_right (b : finset (ℤ × ℤ)) (m : right b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1 - 1, m.val.2)

-- FIXME Ugh! So sad I can't find this in mathlib.
lemma int.succ_ne_self (n : ℤ) : n + 1 ≠ n :=
λ h, one_ne_zero ((add_left_inj n).mp (by { convert h, simp }))
lemma int.pred_ne_self (n : ℤ) : n - 1 ≠ n :=
λ h, one_ne_zero (neg_inj ((add_left_inj n).mp (by { convert h, simp })))

-- TODO Golf?
@[simp] lemma move_left_card (b : finset (ℤ × ℤ)) (m : left b) :
  finset.card (move_left b m) = finset.card b - 2 :=
begin
  erw finset.card_erase_of_mem,
  { erw finset.card_erase_of_mem,
    { refl },
    { exact finset.mem_of_mem_inter_left m.property, } },
  { apply finset.mem_erase_of_ne_of_mem,
    { exact λ h, int.pred_ne_self m.val.2 (congr_arg prod.snd h), },
    { have t := finset.mem_of_mem_inter_right m.property,
      dsimp [shift_up] at t,
      simp only [exists_prop, finset.mem_map, add_comm, function.embedding.coe_fn_mk, prod.exists] at t,
      rcases t with ⟨x,y,w,h⟩,
      rw ←h,
      convert w,
      simp, } }
end
@[simp] lemma move_right_card (b : finset (ℤ × ℤ)) (m : right b) :
  finset.card (move_right b m) = finset.card b - 2 :=
begin
  erw finset.card_erase_of_mem,
  { erw finset.card_erase_of_mem,
    { refl },
    { exact finset.mem_of_mem_inter_left m.property, } },
  { apply finset.mem_erase_of_ne_of_mem,
    { exact λ h, int.pred_ne_self m.val.1 (congr_arg prod.fst h), },
    { have t := finset.mem_of_mem_inter_right m.property,
      dsimp [shift_right] at t,
      simp only [exists_prop, finset.mem_map, add_comm, function.embedding.coe_fn_mk, prod.exists] at t,
      rcases t with ⟨x,y,w,h⟩,
      rw ←h,
      convert w,
      simp, } }
end

lemma move_left_smaller (b : finset (ℤ × ℤ)) (m : left b) :
  finset.card (move_left b m) < finset.card b :=
lt_of_le_of_lt finset.card_erase_le $
  finset.card_erase_lt_of_mem (finset.mem_of_mem_inter_left m.property)
lemma move_right_smaller (b : finset (ℤ × ℤ)) (m : right b) :
  finset.card (move_right b m) < finset.card b :=
lt_of_le_of_lt finset.card_erase_le $
  finset.card_erase_lt_of_mem (finset.mem_of_mem_inter_left m.property)

end domineering_aux

section
open domineering_aux

instance : has_well_founded (finset (ℤ × ℤ)) := ⟨measure finset.card, measure_wf finset.card⟩

def domineering' (n : ℕ) : Π (b : finset (ℤ × ℤ)), b.card = n → pgame :=
nat.strong_rec' (λ n IH b h,
  pgame.mk (left b) (right b)
    (λ m, IH _ (by rw ← h; apply move_left_smaller) (move_left b m) rfl)
    (λ m, IH _ (by rw ← h; apply move_right_smaller) (move_right b m) rfl)) n

/-- We construct a domineering game from any finite subset of `ℤ × ℤ`. -/
def domineering (b : finset (ℤ × ℤ)) : pgame :=
domineering' b.card b rfl

lemma domineering_def (b : finset (ℤ × ℤ)) :
  domineering b = pgame.mk
    (left b) (right b)
    (λ m, domineering (move_left b m))
    (λ m, domineering (move_right b m)) :=
by rw [domineering, domineering', nat.strong_rec']; refl

def domineering_left_moves (b : finset (ℤ × ℤ)) :
  (domineering b).left_moves ≃ left b :=
by { rw [domineering_def], refl }
def domineering_right_moves (b : finset (ℤ × ℤ)) :
  (domineering b).right_moves ≃ right b :=
by { rw [domineering_def], refl }

/-
In the "noncomputational" definition of domineering, I could prove the following
two lemmas. Now I can't, which is frustrating.
```
@[simp] lemma domineering_move_left (b : finset (ℤ × ℤ)) (i : left_moves (domineering b)) :
  (domineering b).move_left i = domineering (move_left b (domineering_left_moves b i)) := sorry
@[simp] lemma domineering_move_right (b : finset (ℤ × ℤ)) (j : right_moves (domineering b)) :
  (domineering b).move_right j = domineering (move_right b (by { convert j, simp })) := sorry
```
-/

instance fintype_left_moves' : Π (n : ℕ) (b : finset (ℤ × ℤ)) (h : b.card = n), fintype ((domineering' n b h).left_moves)
| 0 b h := domineering_aux.fintype_left b
| (n+1) b _ := domineering_aux.fintype_left b

instance fintype_left_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).left_moves) :=
by { dsimp [domineering], apply_instance }

instance fintype_right_moves' : Π (n : ℕ) (b : finset (ℤ × ℤ)) (h : b.card = n), fintype ((domineering' n b h).right_moves)
| 0 b h := domineering_aux.fintype_right b
| (n+1) b _ := domineering_aux.fintype_right b

instance fintype_right_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).right_moves) :=
by { dsimp [domineering], apply_instance }

/-- Domineering is always a short game, because the board is finite. -/
instance short_domineering' : Π (n : ℕ) (b : finset (ℤ × ℤ)) (h : b.card = n), short (domineering' n b h)
| 0 b h :=
  begin
    rw [domineering', nat.strong_rec'],
    dsimp,
    replace h : b = ∅ := finset.card_eq_zero.mp h,
    subst h,
    apply short_of_equiv_empty; dsimp,
    exact left_empty_equiv,
    exact right_empty_equiv,
  end
| (n+1) b h :=
  begin
    fsplit;
    { intro i,
      convert (have n - 1 < n + 1 := nat.sub_lt_succ n 1, short_domineering' (n-1) _ _),
      simp [h],
      exact nat.sub_lt_succ n 1,
      simp [h], },
  end

instance short_domineering (b : finset (ℤ × ℤ)) : short (domineering b) :=
by { dsimp [domineering], apply_instance }

def domineering.one := domineering ([(0,0), (0,1)].to_finset)

/-- The `L` shaped board, in which Left is exactly half a move ahead. -/
def domineering.L := domineering ([(0,2), (0,1), (0,0), (1,0)].to_finset)

instance : short domineering.one := by { dsimp [domineering.one], apply_instance }
instance : short domineering.L := by { dsimp [domineering.L], apply_instance }

-- The VM can play small games successfully:
-- #eval to_bool (domineering.one ≈ 1)
-- #eval to_bool (domineering.L + domineering.L ≈ 1)

-- dec_trivial can handle most of the dictionary of small games described in [conway2001]
example : domineering.one ≈ 1 := dec_trivial
example : domineering.L + domineering.L ≈ 1 := dec_trivial
example : domineering.L ≈ pgame.of_lists [0] [1] := dec_trivial
example : (domineering ([(0,0), (0,1), (0,2), (0,3)].to_finset) ≈ 2) := dec_trivial
example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) := dec_trivial.
example : (domineering ([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)].to_finset) ≈ pgame.of_lists [1] [-1]) := dec_trivial

-- But certainly not all! The 5x5 grid is actually 0, but this is too big even for the VM.
-- #eval to_bool (domineering ([
--   (0,0), (0,1), (0,2), (0,3), (0,4),
--   (1,0), (1,1), (1,2), (1,3), (1,4),
--   (2,0), (2,1), (2,2), (2,3), (2,4),
--   (3,0), (3,1), (3,2), (3,3), (3,4),
--   (4,0), (4,1), (4,2), (4,3), (4,4)
--   ].to_finset) ≈ 0)


end

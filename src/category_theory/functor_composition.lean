import category_theory.whiskering
import category_theory.currying
import category_theory.products.associator

open category_theory
namespace category_theory.functor

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variables (B : Type u₁) [ℬ : category.{v₁+1} B]
          (C : Type u₂) [𝒞 : category.{v₂+1} C]
          (D : Type u₃) [𝒟 : category.{v₃+1} D]
          (E : Type u₄) [ℰ : category.{v₄+1} E]
include 𝒞 𝒟 ℰ

@[simp] def composition : ((C ⥤ D) × (D ⥤ E)) ⥤ (C ⥤ E) :=
uncurry.obj (whiskering_left C D E)

include ℬ

@[simp] def left_assoc_composition : ((B ⥤ C) × (C ⥤ D) × (D ⥤ E)) ⥤ (B ⥤ E) :=
(prod.inverse_associator _ _ _) ⋙ (functor.prod (composition B C D) (𝟭 _)) ⋙ (composition B D E)

@[simp] def right_assoc_composition : ((B ⥤ C) × (C ⥤ D) × (D ⥤ E)) ⥤ (B ⥤ E) :=
(functor.prod (𝟭 _) (composition C D E)) ⋙ (composition B C E)

def associativity : left_assoc_composition B C D E ≅ right_assoc_composition B C D E :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ }, }.

-- which versions(s) do we want? one copy of the associator on either side? or both on one (which?) side?
lemma hcomp_assoc_1
  {C₁} [category.{v₁+1 u₁} C₁] {C₂} [category.{v₂+1 u₂} C₂]
  {C₃} [category.{v₃+1 u₃} C₃] {C₄} [category.{v₄+1 u₄} C₄]
  {F₁ G₁ : C₁ ⥤ C₂} (α₁ : F₁ ⟶ G₁) {F₂ G₂ : C₂ ⥤ C₃} (α₂ : F₂ ⟶ G₂) {F₃ G₃ : C₃ ⥤ C₄} (α₃ : F₃ ⟶ G₃) :
    (functor.associator F₁ F₂ F₃).inv ≫ (α₁ ◫ α₂) ◫ α₃ ≫ (functor.associator G₁ G₂ G₃).hom = α₁ ◫ (α₂ ◫ α₃) :=
begin
  convert nat_iso.naturality_1 (associativity C₁ C₂ C₃ C₄) ((α₁, α₂, α₃) : (F₁, F₂, F₃) ⟶ (G₁, G₂, G₃));
  ext; dsimp; simp,
  rw [←G₃.map_comp, ←α₂.naturality, G₃.map_comp],
end

end category_theory.functor

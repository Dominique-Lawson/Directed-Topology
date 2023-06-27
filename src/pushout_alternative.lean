import category_theory.limits.shapes.comm_sq

/-
  This file contains an alternative way for proving a commutative square in a category is a pushout.
-/

universe u

open category_theory

namespace pushout_alternative

variables {X X₁ X₂ X₀ : Cat.{u u}} {i₁: X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X} {j₂: X₂ ⟶ X}

lemma is_pushout_alternative (h_comm : i₁ ≫ j₁ = i₂ ≫ j₂)
  (h_uniq : ∀ (C : Cat.{u u}) (F₁ : X₁ ⟶ C) (F₂ : X₂ ⟶ C) (h_comm' : i₁ ≫ F₁ = i₂ ≫ F₂),
    ∃! (F : X ⟶ C), j₁ ≫ F = F₁ ∧ j₂ ≫ F = F₂) :
  is_pushout i₁ i₂ j₁ j₂ :=
begin
  let w : comm_sq i₁ i₂ j₁ j₂ := { w := h_comm },
  have : ∀ (s : limits.cocone (limits.span i₁ i₂)), i₁ ≫ limits.pushout_cocone.inl s = i₂ ≫ limits.pushout_cocone.inr s := limits.pushout_cocone.condition,
  let desc : Π (s : limits.pushout_cocone i₁ i₂), X ⟶ s.X := λ s, classical.some (h_uniq s.X _ _ (this s)),
  have fac_left : ∀ (s : limits.pushout_cocone i₁ i₂), j₁ ≫ desc s = s.inl := λ s, (classical.some_spec (h_uniq s.X _ _ (this s))).1.1,
  have fac_right : ∀ (s : limits.pushout_cocone i₁ i₂), j₂ ≫ desc s = s.inr := λ s, (classical.some_spec (h_uniq s.X _ _ (this s))).1.2,
  have uniq : ∀ (s : limits.pushout_cocone i₁ i₂) (m : X ⟶ s.X) (w : ∀ j : limits.walking_span, w.cocone.ι.app j ≫ m = s.ι.app j), m = desc s,
  {
    rintros s m h,
    apply (classical.some_spec (h_uniq s.X _ _ (this s))).right,
    split;
    { convert h _; refl },
  },

  exact is_pushout.of_is_colimit' w (limits.pushout_cocone.is_colimit_aux _ desc fac_left fac_right uniq),
end


end pushout_alternative
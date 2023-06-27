import category_theory.eq_to_hom
import category_theory.category.Cat

/-
  This file contains auxiliary equalities of objects morphisms in a category.
  These are used in the proof of the Van Kampen Theorem in directed_van_kampen.lean
-/

open category_theory

universe u
variables {C C' : category_theory.Cat.{u u}}

lemma eq_of_morphism {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}
  (hb : b₁ = b₀) (hf : f₀ = f₁ ≫ (eq_to_hom hb)) (hg : g₀ = (eq_to_hom hb.symm) ≫ g₁) :
  f₀ ≫ g₀ = f₁ ≫ g₁ :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw category.comp_id,
  rw category.id_comp,
end

lemma obj_eq_obj_of_eq {F₁ F₂ : C ⥤ C'} (h : F₁ = F₂) (x : C) : F₁.obj x = F₂.obj x := eq.subst h rfl

lemma map_eq_map_of_eq {F₁ F₂ : C ⥤ C'} (h : F₁ = F₂) {x y : C} (f : x ⟶ y) : F₁.map f =
  (category_theory.eq_to_hom (obj_eq_obj_of_eq h x)) ≫ F₂.map f ≫ (category_theory.eq_to_hom (obj_eq_obj_of_eq h y).symm) :=
begin
  subst_vars,
  simp,
end

lemma eq_of_functor_obj {F G : C ⟶ C'} (h : F = G) (x : C) : F.obj x = G.obj x := congr_fun (congr_arg category_theory.functor.obj h) x

lemma eq_of_functor_map {F G : C ⟶ C'} (h : F = G) {x y : C} (f : x ⟶ y) :
  F.map f = (eq_to_hom (eq_of_functor_obj h x)) ≫ G.map f ≫ (eq_to_hom (eq_of_functor_obj h y).symm) :=
begin
  subst_vars,
  simp,
end

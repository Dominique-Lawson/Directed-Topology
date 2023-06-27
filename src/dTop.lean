import constructions
import category_theory.concrete_category.bundled_hom
import category_theory.elementwise

/-
  This file contains the definition of `dTop`, the category of directed spaces.
  The structure of this file is based on the undirected version:
  https://github.com/leanprover-community/mathlib/blob/master/src/topology/category/Top/basic.lean
-/

open directed_map
open category_theory

universe u

def dTop : Type (u+1) := bundled directed_space

namespace dTop

instance bundled_hom : bundled_hom @directed_map :=
⟨@directed_map.to_fun, @directed_map.id, @directed_map.comp, @directed_map.coe_injective⟩

attribute [derive [large_category, concrete_category]] dTop

instance : has_coe_to_sort dTop Type* := bundled.has_coe_to_sort

instance directed_space_unbundled (x : dTop) : directed_space x := x.str

@[simp] lemma id_app (X : dTop.{u}) (x : X) :
  (𝟙 X : X → X) x = x := rfl

@[simp] lemma comp_app {X Y Z : dTop.{u}}  (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g : X → Z) x = g (f x) := rfl

/-- Construct a bundled `dTop` from the underlying type and the typeclass. -/
def of (X : Type u) [directed_space X] : dTop := ⟨X⟩

instance (X : dTop) : directed_space X := X.str

@[simp] lemma coe_of (X : Type u) [directed_space X] : (of X : Type u) = X := rfl

instance {X : dTop} : has_coe (set X) dTop := ⟨λ s, dTop.of s⟩

def directed_subtype_hom {X : dTop} (Y : set X) : ↑Y ⟶ X := directed_subtype_inclusion (λ x, x ∈ Y)
def directed_subset_hom {X : dTop} {Y₀ Y₁ : set X} (h : Y₀ ⊆ Y₁) : (dTop.of Y₀) ⟶ Y₁ := directed_subset_inclusion h

end dTop
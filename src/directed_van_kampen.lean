import category_theory.limits.shapes.comm_sq
import dihomotopy_cover
import pushout_alternative
import dihomotopy_to_path_dihomotopy
import morphism_aux

/-
  This file contains the directed version of the Van Kampen Theorem.
  The statement is as follows:
  Let `X : dTop` and `X₁ X₂ : set X` such that `X₁` and `X₂` are both open and `X₁ ∪ X₂ = X`.
  Let `i₁ : X₁ ∩ X₂ → X₁`, `i₂ : X₁ ∩ X₂ → X₂`, `j₁ : X₁ → X` and `j₂ : X₂ → X` be the inclusion maps in `dTop`.
  Then we have a pushout in `Cat`:
  dπₓ(X₁ ∩ X₂) ------ dπₘ i₁ -----> dπₓ(X₁)
       |                              |
       |                              |
       |                              |
     dπₘ i₂                         dπₘ j₁
       |                              |
       |                              |
       |                              |
    dπₓ(X₂) ------- dπₘ j₂ ------> dπₓ(X)

  The proof we give is constructive and is based on the proof given by
  Marco Grandis, Directed Homotopy Theory I, published in Cahiers de topologie et géométrie différentielle catégoriques, 44, no 4, pages 307-309, 2003.
-/
universes u v

open set
open_locale unit_interval classical fundamental_category

local attribute [instance] dipath.dihomotopic.setoid

noncomputable theory

namespace directed_van_kampen

open fundamental_category disubtype category_theory

variables {X : dTop.{u}} {X₁ X₂ : set X}
variables (hX : X₁ ∪ X₂ = set.univ)
variables (X₁_open : is_open X₁) (X₂_open : is_open X₂)


-- We will use a shorthand notation for the 4 morphisms in dTop:
-- i₁ : X₁ ∩ X₂ ⟶ X₁
localized "notation (name := inclusion₀₁)
  `i₁` := dTop.directed_subset_hom $ set.inter_subset_left X₁ X₂" in directed_van_kampen

-- i₁ : X₁ ∩ X₂ ⟶ X₂
localized "notation (name := inclusion₀₂)
  `i₂` := dTop.directed_subset_hom $ set.inter_subset_right X₁ X₂" in directed_van_kampen

-- j₁ : X₁ ⟶ X
localized "notation (name := inclusion₁)
  `j₁` := dTop.directed_subtype_hom X₁" in directed_van_kampen

-- j₂ : X₂ ⟶ X
localized "notation (name := inclusion₂)
  `j₂` := dTop.directed_subtype_hom X₂" in directed_van_kampen

namespace pushout_functor

open dipath dipath.covered dipath.covered_partwise auxiliary

variables {x y : X}
variables {C : category_theory.Cat.{u u}} (F₁ : (dπₓ (dTop.of X₁) ⟶ C)) (F₂ : (dπₓ (dTop.of X₂) ⟶ C))
variables (h_comm : (dπₘ i₁) ⋙ F₁ = ((dπₘ i₂) ⋙ F₂))

section functor_props

variables {Y : dTop.{u}} {Y₀ : set Y} {F : dπₓ (dTop.of Y₀) ⥤ C}

lemma subset_functor_trans {x y z : Y} {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ Y₀) :
  (F.map ⟦subtype_dipath γ₁ (subsets_of_trans_subset hγ).1⟧ ≫ F.map ⟦subtype_dipath γ₂ (subsets_of_trans_subset hγ).2⟧) =
    F.map ⟦subtype_dipath (γ₁.trans γ₂) hγ⟧ :=
begin
  rw ← subtype_trans hγ,
  rw dipath.dihomotopic.comp_lift,
  exact (F.map_comp _ _).symm,
end

lemma subset_functor_reparam {x y : Y} {γ : dipath x y} (hγ : range γ ⊆ Y₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
 F.map ⟦subtype_dipath (γ.reparam f hf₀ hf₁)
    (show range (γ.reparam f hf₀ hf₁) ⊆ Y₀, by exact (dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ)⟧ =
    F.map ⟦@subtype_dipath Y Y₀ x y γ hγ⟧ :=
begin
  congr' 1,
  rw subtype_reparam hγ hf₀ hf₁,
  symmetry,
  exact quotient.eq.mpr (dipath.dihomotopic.reparam (@subtype_dipath Y Y₀ x y γ hγ) f hf₀ hf₁),
end

lemma functor_cast {X : dTop} (F : (dπₓ X) ⥤ C) {x y x' y' : X} (γ : dipath x y) (hx : x' = x) (hy : y' = y) :
  F.map ⟦γ.cast hx hy⟧ = (category_theory.eq_to_hom (congr_arg F.obj hx)) ≫ F.map ⟦γ⟧ ≫ (category_theory.eq_to_hom (congr_arg F.obj hy).symm) :=
begin
  subst_vars,
  rw category_theory.eq_to_hom_refl,
  rw category_theory.eq_to_hom_refl,
  rw category_theory.category.id_comp,
  rw category_theory.category.comp_id,
  congr' 2,
  ext t,
  refl,
end

end functor_props

/-
  Given a category C and functors F₁ : dπₓ X₁ ⥤ C and F₂ : dπₓ X₂ ⥤ C, we will construct a functor F : dπₓ X ⥤ C
-/
include hX F₁ F₂


/- ### Functor on Objects -/

/-
- Define the behaviour on objects
-/
def functor_obj (x : dπₓ X) : C :=
or.by_cases ((set.mem_union x X₁ X₂).mp (filter.mem_top.mpr hX x)) (λ hx, F₁.obj ⟨x, hx⟩) (λ hx, F₂.obj ⟨x, hx⟩)

-- We will use the shorhand notation F_obj
localized "notation (name := functor_obj)
  `F_obj` := functor_obj hX F₁ F₂" in directed_van_kampen

/-
  Under the assumption that the square commutes, we can show how the functor behaves on objects
-/
variables {F₁ F₂}
include h_comm
lemma functor_obj_apply_one {x : X} (hx : x ∈ X₁) : F₁.obj ⟨x, hx⟩ = F_obj x := (dif_pos hx).symm

lemma functor_obj_apply_two {x : X} (hx₂ : x ∈ X₂) : F₂.obj ⟨x, hx₂⟩ = F_obj x :=
begin
  by_cases hx₁ : x ∈ X₁,
  {
    have hx₀ : x ∈ X₁ ∩ X₂ := ⟨hx₁, hx₂⟩,
    have : F₁.obj ((dπₘ i₁).obj ⟨x, hx₀⟩) = F₂.obj ((dπₘ i₂).obj ⟨x, hx₀⟩),
    {
      show ((dπₘ i₁) ⋙ F₁).obj ⟨x, hx₀⟩ = ((dπₘ i₂) ⋙ F₂).obj ⟨x, hx₀⟩,
      rw h_comm,
    },

  	have : F₁.obj ⟨x, hx₁⟩ = F₂.obj (⟨x, hx₂⟩),
    calc F₁.obj ⟨x, hx₁⟩ = F₁.obj ((dπₘ i₁).obj ⟨x, hx₀⟩) : rfl
                    ... = F₂.obj ((dπₘ i₂).obj ⟨x, hx₀⟩) : this
                    ... = F₂.obj (⟨x, hx₂⟩) : rfl,

    rw this.symm,
    exact (dif_pos hx₁).symm,
  },
  exact (dif_neg hx₁).symm,
end

/- ### Functor on Maps -/

/-
  Define the mapping behaviour on paths that are fully covered by one set
-/
def functor_map_aux_part_one {γ : dipath x y} (hγ : range γ ⊆ X₁) :
  F_obj x ⟶ F_obj y :=
    (eq_to_hom (functor_obj_apply_one hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
    (F₁.map ⟦subtype_dipath γ hγ⟧) ≫
    (eq_to_hom (functor_obj_apply_one hX h_comm (target_elt_of_image_subset hγ)))

def functor_map_aux_part_two {γ : dipath x y} (hγ : range γ ⊆ X₂) :
  F_obj x ⟶ F_obj y :=
    (eq_to_hom (functor_obj_apply_two hX h_comm (source_elt_of_image_subset hγ)).symm) ≫
    (F₂.map ⟦subtype_dipath γ hγ⟧) ≫
    (eq_to_hom (functor_obj_apply_two hX h_comm (target_elt_of_image_subset hγ)))

/-
  Show that these maps respect composition of paths
-/
lemma functor_map_aux_part_one_trans {x y z : X} {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₁) :
  functor_map_aux_part_one hX h_comm hγ =
    functor_map_aux_part_one hX h_comm (subsets_of_trans_subset hγ).1
  ≫ functor_map_aux_part_one hX h_comm (subsets_of_trans_subset hγ).2 :=
begin
  unfold functor_map_aux_part_one,
  rw (subset_functor_trans hγ).symm,
  simp,
end

lemma functor_map_aux_part_two_trans {x y z : X} {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₂) :
  functor_map_aux_part_two hX h_comm hγ =
    functor_map_aux_part_two hX h_comm (subsets_of_trans_subset hγ).1
  ≫ functor_map_aux_part_two hX h_comm (subsets_of_trans_subset hγ).2 :=
begin
  unfold functor_map_aux_part_two,
  rw (subset_functor_trans hγ).symm,
  simp,
end

/-
 Show that the maps respect reparametrization of paths
-/
lemma functor_map_one_reparam {x y : X} {γ : dipath x y} (hγ : range γ ⊆ X₁) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  functor_map_aux_part_one hX h_comm hγ = functor_map_aux_part_one hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) :=
begin
  unfold functor_map_aux_part_one,
  rw (subset_functor_reparam hγ hf₀ hf₁),
end
  
lemma functor_map_two_reparam {x y : X} {γ : dipath x y} (hγ : range γ ⊆ X₂) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  functor_map_aux_part_two hX h_comm hγ = functor_map_aux_part_two hX h_comm (reparam_subset_of_subset hγ hf₀ hf₁) :=
begin
  unfold functor_map_aux_part_two,
  rw (subset_functor_reparam hγ hf₀ hf₁),
end

/-
 Show that the maps respect reparametrization of paths
-/
lemma functor_map_one_refl {x : X} (hx : x ∈ X₁) :
  functor_map_aux_part_one hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj x) :=
begin
  unfold functor_map_aux_part_one,
  rw subtype_refl,
  rw ← id_eq_path_refl,
  rw F₁.map_id',
  simp,
end
  
lemma functor_map_two_refl {x : X} (hx : x ∈ X₂) :
  functor_map_aux_part_two hX h_comm (range_refl_subset_of_mem hx) = 𝟙 (F_obj x) :=
begin
  unfold functor_map_aux_part_two,
  rw subtype_refl,
  rw ← id_eq_path_refl,
  rw F₂.map_id',
  simp,
end

/-
  Show that for any path living in X₁ ∩ X₂, it does not matter whether we apply the first or second map
-/
lemma functor_map_aux_parts_equal {γ : dipath x y} (hγ₁ : range γ ⊆ X₁) (hγ₂ : range γ ⊆ X₂) :
  functor_map_aux_part_one hX h_comm hγ₁ = functor_map_aux_part_two hX h_comm hγ₂ :=
begin
  unfold functor_map_aux_part_one functor_map_aux_part_two,
  have hγ₀ : range γ ⊆ X₁ ∩ X₂ := subset_inter hγ₁ hγ₂,
  apply (eq_to_hom_comp_iff _ _ _).mpr,
  apply (comp_eq_to_hom_iff _ _ _).mpr,
  simp,
  convert map_eq_map_of_eq h_comm ⟦subtype_dipath γ hγ₀⟧,
end

/-
- ### Define the mapping behaviour on covered paths
-/
def functor_map_of_covered {γ : dipath x y} (hγ : covered γ hX) :
  F_obj x ⟶ F_obj y :=
or.by_cases hγ (λ hγ, functor_map_aux_part_one hX h_comm hγ) (λ hγ, functor_map_aux_part_two hX h_comm hγ)

localized "notation (name := functor_map_covered)
  `F₀` := functor_map_of_covered hX h_comm" in directed_van_kampen

section functor_map_covered_properties

lemma functor_map_of_covered_apply_left {γ : dipath x y} (hγ : range γ ⊆ X₁) :
  F₀ (or.inl hγ) = functor_map_aux_part_one hX h_comm hγ := dif_pos hγ

lemma functor_map_of_covered_apply_left' {γ : dipath x y} (hγ : range γ ⊆ X₁) :
  F₀ (covered_partwise_of_covered 0 (or.inl hγ)) = functor_map_aux_part_one hX h_comm hγ := functor_map_of_covered_apply_left _ _ _

lemma functor_map_of_covered_apply_right {γ : dipath x y} (hγ : range γ ⊆ X₂) :
  F₀ (or.inr hγ) = functor_map_aux_part_two hX h_comm hγ :=
begin
  by_cases hγ₁ : range γ ⊆ X₁,
  {
    rw functor_map_of_covered_apply_left hX h_comm hγ₁,
    exact functor_map_aux_parts_equal hX h_comm hγ₁ hγ
  },
  apply dif_neg hγ₁,
end

lemma functor_map_of_covered_equal {γ₁ γ₂ : dipath x y} (h : γ₁ = γ₂) (hγ₁ : covered γ₁ hX) (hγ₂ : covered γ₂ hX) :
  F₀ hγ₁ = F₀ hγ₂ :=
begin
  subst_vars,
end

lemma functor_map_of_covered_refl : F₀ (covered_refl x hX) = 𝟙 (F_obj x) :=
begin
  cases ((set.mem_union x X₁ X₂).mp (filter.mem_top.mpr hX x)) with hx₁ hx₂,
  {
    rw ← functor_map_one_refl,
    exact functor_map_of_covered_apply_left hX h_comm (disubtype.range_refl_subset_of_mem hx₁),
  },
  {
    rw ← functor_map_two_refl,
    exact functor_map_of_covered_apply_right hX h_comm (disubtype.range_refl_subset_of_mem hx₂),
  }
end

lemma functor_map_of_covered_apply_right' {γ : dipath x y} (hγ : range γ ⊆ X₂) :
  F₀ (covered_partwise_of_covered 0 (or.inr hγ)) = functor_map_aux_part_two hX h_comm hγ := functor_map_of_covered_apply_right _ _ _

lemma functor_map_of_covered_trans {x y z : X} {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ : covered (γ₁.trans γ₂) hX) :
  F₀ hγ = (F₀ (covered_trans hγ).1) ≫ (F₀ (covered_trans hγ).2) :=
begin
  cases hγ,
  { -- γ is covered by X₁
    rw functor_map_of_covered_apply_left _ _ hγ,
    rw functor_map_aux_part_one_trans,
    congr,
    exact (functor_map_of_covered_apply_left _ _ _).symm,
    exact (functor_map_of_covered_apply_left _ _ _).symm,
  },
  rw functor_map_of_covered_apply_right _ _ hγ,
  rw functor_map_aux_part_two_trans,
  congr,
  exact (functor_map_of_covered_apply_right _ _ (subsets_of_trans_subset hγ).1).symm,
  exact (functor_map_of_covered_apply_right _ _ (subsets_of_trans_subset hγ).2).symm,
end

lemma functor_map_of_covered_reparam {x y : X} {γ : dipath x y} (hγ : covered γ hX) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  F₀ hγ = F₀ ((covered_reparam_iff γ hX f hf₀ hf₁).mp hγ) :=
begin
  cases hγ,
  {
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₁,
    {
      rw dipath.range_reparam γ f hf₀ hf₁,
      exact hγ,
    },
    rw functor_map_of_covered_apply_left,
    rw functor_map_one_reparam hX h_comm hγ hf₀ hf₁,
    rw ← functor_map_of_covered_apply_left hX h_comm this,
    refl,
  },
  {
    have : range (γ.reparam f hf₀ hf₁) ⊆ X₂,
    {
      rw dipath.range_reparam γ f hf₀ hf₁,
      exact hγ,
    },
    rw functor_map_of_covered_apply_right,
    rw functor_map_two_reparam hX h_comm hγ hf₀ hf₁,
    rw ← functor_map_of_covered_apply_right hX h_comm this,
    refl,
  }

end
  
lemma functor_map_of_covered_cast {x y x' y' : X} {γ : dipath x y} (hγ : covered γ hX) (hx : x' = x) (hy : y' = y) :
  F₀ ((covered_cast_iff γ hX hx hy).mp hγ) =
    (eq_to_hom (show F_obj x' = F_obj x, by rw hx)) ≫ (F₀ hγ) ≫ (eq_to_hom (show F_obj y = F_obj y', by rw hy)) :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw eq_to_hom_refl,
  rw category.comp_id,
  rw category.id_comp,
  refl,
end

lemma functor_map_of_covered_cast_left {x y x' : X} {γ : dipath x y} (hγ : covered γ hX) (hx : x' = x) :
  F₀ ((covered_cast_iff γ hX hx rfl).mp hγ) =
    (eq_to_hom (show F_obj x' = F_obj x, by rw hx)) ≫ (F₀ hγ) :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw category.id_comp,
  refl,
end

lemma functor_map_of_covered_cast_right {x y y' : X} {γ : dipath x y} (hγ : covered γ hX) (hy : y' = y) :
  F₀ ((covered_cast_iff γ hX rfl hy).mp hγ) =
    (F₀ hγ) ≫ (eq_to_hom (show F_obj y = F_obj y', by rw hy)) :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw category.comp_id,
  refl,
end

lemma functor_map_of_covered_split_comp {x y : X} {γ : dipath x y} (hγ : covered γ hX) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  F₀ hγ = (F₀ (covered_split_path hT₀ hT₁ hγ).1) ≫ (F₀ (covered_split_path hT₀ hT₁ hγ).2) :=
begin
  have : covered ((split_dipath.first_part_dipath γ hT₀).trans (split_dipath.second_part_dipath γ hT₁)) hX,
  {
    rw split_dipath.first_trans_second_reparam_eq_self γ hT₀ hT₁ at hγ,
    exact (covered_reparam_iff _ hX _ _ _).mpr hγ,
  },
  rw ← functor_map_of_covered_trans hX h_comm this,
  rw functor_map_of_covered_reparam hX h_comm this
      (split_dipath.trans_reparam_map_zero hT₀ hT₁)
      (split_dipath.trans_reparam_map_one hT₀ hT₁),
  congr,
  apply split_dipath.first_trans_second_reparam_eq_self,
end

lemma functor_map_of_covered_dihomotopic {x y : X} {γ γ' : dipath x y} {F : dihomotopy γ γ'} (hF : dipath.dihomotopy.covered F hX) :
  F₀ (dipath.dihomotopy.covered_left_of_covered hF) = F₀ (dipath.dihomotopy.covered_right_of_covered hF) :=
begin
  cases hF,
  {
    have hγ := subset_trans (dipath.dihomotopy.range_left_subset F) hF,
    have hγ' := subset_trans (dipath.dihomotopy.range_right_subset F) hF,
    rw functor_map_of_covered_equal hX h_comm rfl _ (or.inl hγ),
    rw functor_map_of_covered_equal hX h_comm rfl _ (or.inl hγ'),
    rw functor_map_of_covered_apply_left hX h_comm hγ,
    rw functor_map_of_covered_apply_left hX h_comm hγ',
    unfold functor_map_aux_part_one,
    rw dihom_subtype_of_dihom_range_subset hγ hγ' hF,
  },
  {
    have hγ := subset_trans (dipath.dihomotopy.range_left_subset F) hF,
    have hγ' := subset_trans (dipath.dihomotopy.range_right_subset F) hF,
    rw functor_map_of_covered_equal hX h_comm rfl _ (or.inr hγ),
    rw functor_map_of_covered_equal hX h_comm rfl _ (or.inr hγ'),
    rw functor_map_of_covered_apply_right hX h_comm hγ,
    rw functor_map_of_covered_apply_right hX h_comm hγ',
    unfold functor_map_aux_part_two,
    rw dihom_subtype_of_dihom_range_subset hγ hγ' hF,
  }
end

end functor_map_covered_properties

/-
-  ### Define the behaviour on partwise covered paths
-/

def functor_map_of_covered_partwise {n : ℕ} : Π {x y : X} {γ : dipath x y} (hγ : covered_partwise hX γ n), F_obj x ⟶ F_obj y :=
nat.rec_on n
  (λ x y γ hγ, F₀ hγ)
  ( λ n ih x y γ hγ, (F₀ hγ.1) ≫ (ih hγ.2))

localized "notation (name := functor_map_of_covered_partwise)
  `Fₙ` := functor_map_of_covered_partwise hX h_comm" in directed_van_kampen

lemma functor_map_of_covered_partwise_apply_0 {x y : X} {γ : dipath x y} (hγ : covered_partwise hX γ 0) :
  Fₙ hγ = F₀ hγ := rfl

lemma functor_map_of_covered_partwise_apply_succ {n : ℕ} {x y : X} {γ : dipath x y} (hγ : covered_partwise hX γ n.succ) :
  Fₙ hγ = (F₀ hγ.left) ≫ (Fₙ hγ.right) := rfl

lemma functor_map_of_covered_partwise_equal {n : ℕ} {γ₁ γ₂ : dipath x y} (h : γ₁ = γ₂) (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
  Fₙ hγ₁ = Fₙ hγ₂ :=
begin
  subst_vars,
end

lemma functor_map_of_covered_partwise_equal' {n m : ℕ} {γ₁ γ₂ : dipath x y} (h₁ : γ₁ = γ₂) (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ m) :
  Fₙ hγ₁ = Fₙ hγ₂ :=
begin
  subst_vars,
end

lemma functor_map_of_covered_partwise_cast_params {n m : ℕ} {γ₁ γ₂ : dipath x y} (h₁ : γ₁ = γ₂) (h₂ : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
  Fₙ hγ₁ = Fₙ (covered_partwise_of_equal_params hX h₁ h₂ hγ₁) :=
begin
  subst_vars,
end


lemma functor_map_of_covered_partwise_cast {x y x' y' : X} {n : ℕ} {γ : dipath x y} (hγ : covered_partwise hX γ n) (hx : x' = x) (hy : y' = y) :
  Fₙ ((covered_partwise_cast_iff hX γ hx hy).mp hγ) =
    (eq_to_hom (show F_obj x' = F_obj x, by rw hx)) ≫ (Fₙ hγ) ≫ (eq_to_hom (show F_obj y = F_obj y', by rw hy)) :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw eq_to_hom_refl,
  rw category.comp_id,
  rw category.id_comp,
  apply functor_map_of_covered_partwise_equal,
  ext t,
  refl,
end

lemma functor_map_of_covered_partwise_cast_left {x y x' : X} {n : ℕ} {γ : dipath x y} (hγ : covered_partwise hX γ n) (hx : x' = x) :
  Fₙ ((covered_partwise_cast_iff hX γ hx rfl).mp hγ) = (eq_to_hom (show F_obj x' = F_obj x, by rw hx)) ≫ (Fₙ hγ) :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw category.id_comp,
  apply functor_map_of_covered_partwise_equal,
  ext t,
  refl,
end

lemma functor_map_of_covered_partwise_cast_right {x y y' : X} {n : ℕ} {γ : dipath x y} (hγ : covered_partwise hX γ n) (hy : y' = y) :
  Fₙ ((covered_partwise_cast_iff hX γ rfl hy).mp hγ) = (Fₙ hγ) ≫ (eq_to_hom (show F_obj y = F_obj y', by rw hy)) :=
begin
  rw functor_map_of_covered_partwise_cast hX h_comm hγ rfl hy,
  rw eq_to_hom_refl,
  rw category.id_comp,
end

lemma functor_map_of_covered_partwise_refine_of_covered (k : ℕ):
  Π {x y : X} {γ : dipath x y} (hγ : covered γ hX),
    Fₙ (covered_partwise_of_covered 0 hγ) = Fₙ (covered_partwise_of_covered k hγ) :=
begin
  induction k with k hk,
  { -- case k = 0
    intros x y γ hγ,
    refl,
  },
  {
    intros x y γ hγ,
    have : 1 < k + 2 := by linarith,
    rw functor_map_of_covered_partwise_apply_succ hX h_comm (covered_partwise_of_covered k.succ hγ),
    show (functor_map_of_covered hX h_comm hγ) = _,
    rw functor_map_of_covered_split_comp hX h_comm hγ (inv_I_pos (lt_trans zero_lt_one this)) (inv_I_lt_one this),
    congr,
    simp [functor_map_of_covered_partwise],
    apply hk,
    exact (covered_split_path (inv_I_pos (lt_trans zero_lt_one this)) (inv_I_lt_one this) hγ).2,
  }
end

/--
  When a path is partwise covered by n+1 paths, you can apply Fₙ to both parts of γ, when restricting to
  [0, (d+1)/(n+1)] and [(d+1)/(n+1)]. This lemma states that the composition of these two gives Fₙ γ
-/
lemma functor_map_of_covered_partwise_split {n : ℕ} :
  Π {d : ℕ} (hdn : n > d) {x y : X} {γ : dipath x y} (hγ : covered_partwise hX γ n),
 Fₙ hγ = Fₙ (covered_partwise_first_part_d hX (nat.succ_lt_succ hdn) hγ) ≫
        Fₙ (covered_partwise_second_part_d hX (nat.succ_lt_succ hdn) hγ) :=
begin
  induction n with n ih_n,
  { -- Case n = 0,
    intros d hd,
    linarith,
  },
  intros d hdn,
  induction d with d ih_d,
  { -- Case d = 0,
    intros x y γ hγ,
    refl,
  },
  intros x y γ hγ,
  rw functor_map_of_covered_partwise_apply_succ hX h_comm hγ,
  have : n > d := nat.succ_lt_succ_iff.mp hdn,
  rw ih_n this _,
  rw functor_map_of_covered_partwise_apply_succ hX h_comm _,
  rw category.assoc,
  show F₀ _ ≫ (Fₙ _ ≫ Fₙ _) =  F₀ _ ≫ (Fₙ _ ≫ Fₙ _),
  apply eq_of_morphism,
  {
    apply (comp_eq_to_hom_iff _ _ _).mp,
    rw ← functor_map_of_covered_cast_right,
    apply functor_map_of_covered_equal,
    rw split_properties.first_part_of_first_part γ (nat.succ_lt_succ hdn) (nat.succ_pos d.succ),
  },
  rw ← category.assoc,
  apply eq_of_morphism,
  {
    apply (comp_eq_to_hom_iff _ _ _).mp,
    apply (eq_to_hom_comp_iff _ _ _).mp,
    rw ← functor_map_of_covered_partwise_cast,
    apply functor_map_of_covered_partwise_equal,
    rw split_properties.first_part_of_second_part γ (hdn) (nat.succ_pos d),
  },
  rw ← functor_map_of_covered_partwise_cast_left,
  apply functor_map_of_covered_partwise_equal',
  rw split_properties.second_part_of_second_part γ (nat.lt_of_succ_lt_succ hdn),
  rw nat.succ_sub_succ,
end

/--
  If a path can be covered partwise by `(n+1) ≥ 2` parts, its refinement by covering it by `k*(n+1)` parts is equal to the composition
  of covering the first part in `k` parts and the second part in `k*n` parts.
-/
lemma functor_map_of_covered_partwise_refine_apply (n k : ℕ) {x y : X} {γ : dipath x y} (hγ : covered_partwise hX γ n.succ) :
  Fₙ (covered_partwise_refine hX n.succ k hγ) =
      (Fₙ $ covered_partwise_of_covered k hγ.left) ≫ (Fₙ $ covered_partwise_refine hX n k hγ.right) :=
begin
  have h₁ : (n+1+1)*(k+1) - 1 > (k + 1) - 1,
  {
    apply nat.pred_lt_pred (ne_of_gt (nat.succ_pos k)),
    show k + 1 < (n+1+1) * (k + 1),
    have : n + 1 + 1 > 1 := by linarith,
    convert nat.mul_lt_mul_of_pos_right (this) (nat.succ_pos k),
    exact (one_mul k).symm,
  },
  have h₂ := frac_eq_inv₁ (nat.succ_pos k) (le_of_lt (nat.succ_lt_succ h₁)),
  rw functor_map_of_covered_partwise_split hX h_comm h₁ (covered_partwise_refine hX n.succ k hγ),
  apply eq_of_morphism,
  {
    rw ← functor_map_of_covered_partwise_cast_right hX h_comm _ (congr_arg γ h₂.symm),
    apply functor_map_of_covered_partwise_equal hX h_comm,
    ext t,
    rw dipath.cast_apply,
    exact split_properties.first_part_eq_of_point_eq _ h₂.symm _ _,
  },
  rw ← functor_map_of_covered_partwise_cast_left hX h_comm _ (congr_arg γ h₂.symm),
  apply functor_map_of_covered_partwise_equal' hX h_comm,
  ext t,
  rw dipath.cast_apply,
  exact split_properties.second_part_eq_of_point_eq _ h₂.symm _ _,
  simp,
  rw nat.succ_mul,
  rw nat.sub.right_comm,
  rw nat.add_sub_cancel,
end

lemma functor_map_of_covered_partwise_refine {n : ℕ} (k : ℕ) :
  Π {x y : X} {γ : dipath x y} (hγ_n : covered_partwise hX γ n) ,
    Fₙ hγ_n = Fₙ (covered_partwise_refine hX n k hγ_n) :=
begin
  induction n with n h_ind,
  { -- Case n = 0
    apply functor_map_of_covered_partwise_refine_of_covered,
  },
  -- Case n > 0
  intros x y γ hγ,
  rw functor_map_of_covered_partwise_refine_apply hX h_comm n k hγ,
  rw ← functor_map_of_covered_partwise_refine_of_covered hX h_comm _ hγ.left,
  rw functor_map_of_covered_partwise_apply_succ hX h_comm hγ,
  rw h_ind hγ.right,
  congr,
end

lemma functor_map_of_covered_partwise_apply_right_side {x y : X} {γ : dipath x y} {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
  Fₙ hγ = Fₙ (covered_partwise_first_part_end_split hX hγ) ≫
          F₀ (covered_second_part_end_split hX hγ) :=
begin
  rw functor_map_of_covered_partwise_split hX h_comm (nat.lt_succ_self n),
  rw functor_map_of_covered_partwise_equal' hX h_comm rfl (nat.sub_self n.succ),
  rw functor_map_of_covered_partwise_apply_0,
end

lemma functor_map_of_covered_partwise_trans_case_0 {x y z : X} {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ₁ : covered_partwise hX γ₁ 0) (hγ₂ : covered_partwise hX γ₂ 0) :
  Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) :=
begin
  rw functor_map_of_covered_partwise_apply_0,
  rw functor_map_of_covered_partwise_apply_0,
  rw functor_map_of_covered_partwise_apply_succ,
  rw functor_map_of_covered_partwise_apply_0,
  rw functor_map_of_covered_equal hX h_comm (split_properties.first_part_trans γ₁ γ₂) _ ((covered_cast_iff γ₁ hX _ _).mp hγ₁),
  rw functor_map_of_covered_equal hX h_comm (split_properties.second_part_trans γ₁ γ₂) _ ((covered_cast_iff γ₂ hX _ _).mp hγ₂),
  rw functor_map_of_covered_cast_right,
  rw functor_map_of_covered_cast_left,
  simp,
end

lemma functor_map_of_covered_partwise_trans {n : ℕ} : 
  Π {x y z : X} {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n),
  Fₙ (covered_partwise_trans hγ₁ hγ₂) = (Fₙ hγ₁) ≫ (Fₙ hγ₂) :=
begin
  induction n with n ih,
  { -- Case n = 0
    intros x y z γ₁ γ₂ hγ₁ hγ₂,
    exact functor_map_of_covered_partwise_trans_case_0 hX h_comm hγ₁ hγ₂,
  }, -- Case n > 0
  intros x y z γ₁ γ₂ hγ₁ hγ₂,
  rw functor_map_of_covered_partwise_apply_succ hX h_comm,
  rw functor_map_of_covered_partwise_apply_succ hX h_comm hγ₁,
  rw category.assoc,
  apply eq_of_morphism,
  {
    rw ← functor_map_of_covered_cast_right,
    apply functor_map_of_covered_equal,
    ext t,
    rw dipath.cast_apply,
    exact split_properties.trans_first_part γ₁ γ₂ n.succ t,
    exact split_properties.trans_image_inv_eq_first γ₁ γ₂ n.succ,
  },
  rw functor_map_of_covered_partwise_apply_right_side hX h_comm hγ₂,
  rw functor_map_of_covered_partwise_cast_params hX h_comm rfl (nat.pred_succ n),
  rw ← category.assoc (Fₙ _) _ _,
  rw ← ih _ _,
  have : (n.succ + n.succ).succ - 1 = (n + n).succ.succ,
  {
    rw nat.sub_one,
    rw nat.pred_succ (n.succ + n.succ),
    rw nat.succ_add,
    rw nat.add_succ,
  },
  rw functor_map_of_covered_partwise_cast_params hX h_comm rfl this,
  rw ← category.assoc _ _,
  rw ← functor_map_of_covered_partwise_cast_left,
  rw functor_map_of_covered_partwise_apply_right_side hX h_comm _,
  apply eq_of_morphism,
  {
    rw ← functor_map_of_covered_partwise_cast_right,
    apply functor_map_of_covered_partwise_equal' hX h_comm _ rfl,
    ext t,
    rw dipath.cast_apply,
    rw dipath.cast_apply,
    exact split_properties.trans_first_part_of_second_part γ₁ γ₂ n t,
    exact split_properties.second_part_trans_image_inv_eq_second γ₁ γ₂ n,
  },
  {
    rw ← functor_map_of_covered_cast_left,
    apply functor_map_of_covered_equal,
    ext t,
    rw dipath.cast_apply,
    exact split_properties.trans_second_part_second_part γ₁ γ₂ n t,
    exact split_properties.second_part_trans_image_inv_eq_second γ₁ γ₂ n,
  },
  exact split_properties.trans_image_inv_eq_first γ₁ γ₂ n.succ,
end

lemma functor_map_of_covered_partwise_unique {n m : ℕ} {γ : dipath x y}
  (hγ_n : covered_partwise hX γ n)
  (hγ_m : covered_partwise hX γ m) :
  Fₙ hγ_n = Fₙ hγ_m :=
begin
  rw functor_map_of_covered_partwise_refine hX h_comm m hγ_n,
  rw functor_map_of_covered_partwise_refine hX h_comm n hγ_m,
  congr' 2,
  ring,
end

/-
-  ### Define the behaviour on all paths
-/

def functor_map_aux (γ : dipath x y) : F_obj x ⟶ F_obj y :=
  Fₙ (classical.some_spec (has_subpaths hX X₁_open X₂_open γ))

localized "notation (name := functor_map_aux)
  `F_map_aux` := functor_map_aux hX X₁_open X₂_open h_comm" in directed_van_kampen

lemma functor_map_aux_apply {n : ℕ} {γ : dipath x y} (hγ : covered_partwise hX γ n) :
  F_map_aux γ = Fₙ hγ := functor_map_of_covered_partwise_unique hX h_comm _ _

lemma functor_map_aux_refl {x : X} : F_map_aux (dipath.refl x) = 𝟙 (F_obj x) :=
begin
  have : covered_partwise hX (dipath.refl x) 0 := covered_refl x hX,
  rw functor_map_aux_apply _ _ _ _ this,
  rw functor_map_of_covered_partwise_apply_0,
  apply functor_map_of_covered_refl,
end

lemma functor_map_aux_cast {x y x' y' : X} (γ : dipath x y) (hx : x' = x) (hy : y' = y) :
  F_map_aux (γ.cast hx hy) = (eq_to_hom $ congr_arg F_obj hx) ≫ F_map_aux γ ≫ (eq_to_hom $ congr_arg F_obj hy.symm) :=
begin
  subst_vars,
  rw eq_to_hom_refl,
  rw eq_to_hom_refl,
  rw category.comp_id,
  rw category.id_comp,
  apply congr_arg,
  ext t,
  refl,
end

lemma functor_map_aux_trans {x y z : X} (γ₁ : dipath x y) (γ₂ : dipath y z) : F_map_aux (γ₁.trans γ₂) = F_map_aux γ₁ ≫ F_map_aux γ₂ :=
begin
  cases has_subpaths hX X₁_open X₂_open γ₁ with n hn,
  cases has_subpaths hX X₁_open X₂_open γ₂ with m hm,
  have hn' : covered_partwise hX γ₁ ((n + 1) * (m + 1) - 1) := covered_partwise_refine hX n m hn,
  have hm' : covered_partwise hX γ₂ ((n + 1) * (m + 1) - 1),
  {
    rw mul_comm,
    exact covered_partwise_refine hX m n hm,
  },
  rw functor_map_aux_apply hX X₁_open X₂_open h_comm hn',
  rw functor_map_aux_apply hX X₁_open X₂_open h_comm hm',
  rw functor_map_aux_apply hX X₁_open X₂_open h_comm (covered_partwise_trans hn' hm'),
  rw functor_map_of_covered_partwise_trans,
end

lemma functor_map_aux_split_of_covered_partwise {x y : X} {γ : dipath x y} {n : ℕ} (hγ : covered_partwise hX γ n.succ) :
  F_map_aux γ =  F_map_aux (split_dipath.first_part_dipath γ (frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le n.succ))))
    ≫ F_map_aux (split_dipath.second_part_dipath γ (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos n)))) :=
begin
  -- Rewrite L.H.S.
  rw functor_map_aux_apply hX _ _ h_comm hγ,
  rw functor_map_of_covered_partwise_apply_succ hX h_comm hγ,

  --Rewrite R.H.S.
  have : covered_partwise hX (split_dipath.first_part_dipath γ _) 0 := hγ.left,
  rw functor_map_aux_apply hX _ _ h_comm this,
  rw functor_map_of_covered_partwise_apply_0,
  rw functor_map_aux_apply hX _ _ h_comm hγ.right,
  refl,
end

lemma functor_map_aux_of_covered_dihomotopic {x y : X} {γ γ' : dipath x y} {F : dihomotopy γ γ'} (hF : dipath.dihomotopy.covered F hX) :
  F_map_aux γ = F_map_aux γ' :=
begin
  have : covered_partwise hX γ 0 := dipath.dihomotopy.covered_left_of_covered hF,
  rw functor_map_aux_apply _ _ _ _ this,
  rw functor_map_of_covered_partwise_apply_0,
  have : covered_partwise hX γ' 0 := dipath.dihomotopy.covered_right_of_covered hF,
  rw functor_map_aux_apply _ _ _ _ this,
  rw functor_map_of_covered_partwise_apply_0,
  exact functor_map_of_covered_dihomotopic hX h_comm hF,
end

lemma functor_map_aux_of_homotopic_dimaps_0 {f g : D(I, X)} {H : directed_map.dihomotopy f g} (hcov : directed_map.dihomotopy.covered_partwise H hX 0 0) :
  F_map_aux (dipath.of_directed_map f) ≫ F_map_aux (H.eval_at_right 1) = F_map_aux (H.eval_at_right 0) ≫ F_map_aux (dipath.of_directed_map g) :=
begin
  let Γ := dihom_to_path_dihom.dihom_to_path_dihom H,
  have Γ_cov : dipath.dihomotopy.covered Γ hX,
  {
    unfold dipath.dihomotopy.covered,
    cases directed_map.dihomotopy.covered_of_covered_partwise hcov,
    {
      left,
      exact subset_trans (dihom_to_path_dihom.dihom_to_path_dihom_range _) h,
    },
    {
      right,
      exact subset_trans (dihom_to_path_dihom.dihom_to_path_dihom_range _) h,
    },
  },
  have := functor_map_aux_of_covered_dihomotopic hX X₁_open X₂_open h_comm Γ_cov,

  calc F_map_aux (dipath.of_directed_map f) ≫ F_map_aux (H.eval_at_right 1)
              = (𝟙 (F_obj (f 0)) ≫ F_map_aux (of_directed_map f)) ≫ F_map_aux (H.eval_at_right 1)                          : by rw category.id_comp
          ... = (F_map_aux (dipath.refl (f 0)) ≫ F_map_aux (of_directed_map f)) ≫ F_map_aux (H.eval_at_right 1)            : by rw functor_map_aux_refl
          ... = F_map_aux ((dipath.refl (f 0)).trans (of_directed_map f)) ≫ F_map_aux (H.eval_at_right 1)                  : by rw functor_map_aux_trans
          ... = F_map_aux (((dipath.refl (f 0)).trans (of_directed_map f)).trans (H.eval_at_right 1))                       : by rw ← functor_map_aux_trans
          ... = F_map_aux (((H.eval_at_right 0).trans (of_directed_map g)).trans (refl (g 1)))                              : this
          ... = F_map_aux ((H.eval_at_right 0).trans (of_directed_map g)) ≫ F_map_aux (refl (g 1))                         : by rw functor_map_aux_trans
          ... = F_map_aux ((H.eval_at_right 0).trans (of_directed_map g)) ≫ 𝟙 (F_obj (g 1))                                : by rw functor_map_aux_refl
          ... = F_map_aux ((H.eval_at_right 0).trans (of_directed_map g))                                                   : by rw category.comp_id
          ... = F_map_aux (H.eval_at_right 0) ≫ F_map_aux (dipath.of_directed_map g)                                       : by rw functor_map_aux_trans,
end

lemma functor_map_aux_of_homotopic_dimaps {m : ℕ} :
  Π  {f g : D(I, X)} {H : directed_map.dihomotopy f g} (hcov : directed_map.dihomotopy.covered_partwise H hX 0 m),
  F_map_aux (dipath.of_directed_map f) ≫ F_map_aux (H.eval_at_right 1) = F_map_aux (H.eval_at_right 0) ≫ F_map_aux (dipath.of_directed_map g) :=
begin
  induction m with m ih,
  { -- Case m = 0
    exact λ f g H hcov, functor_map_aux_of_homotopic_dimaps_0 _ _ _ _ hcov,
  },
  intros f g H hcov,

  have f_cov : covered_partwise hX (dipath.of_directed_map f) m.succ :=
    directed_map.dihomotopy.path_covered_partiwse_of_dihomotopy_covered_partwise_left hcov,
  have g_cov : covered_partwise hX (dipath.of_directed_map g) m.succ :=
    directed_map.dihomotopy.path_covered_partiwse_of_dihomotopy_covered_partwise_right hcov,

  -- Split at 1/(m.succ + 1)
  let T := frac (nat.succ_pos m.succ) (nat.succ_le_succ (nat.zero_le m.succ)),
  have hT₀ : 0 < T := frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le m.succ)),
  have hT₁ : T < 1 := frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos m)),

  let f₁ := (split_dipath.first_part_dipath (dipath.of_directed_map f) hT₀),
  let f₂ := (split_dipath.second_part_dipath (dipath.of_directed_map f) hT₁),

  let g₁ := (split_dipath.first_part_dipath (dipath.of_directed_map g) hT₀),
  let g₂ := (split_dipath.second_part_dipath (dipath.of_directed_map g) hT₁),

  have h₁ : F_map_aux f₂ ≫ F_map_aux (H.eval_at_right 1) = F_map_aux (H.eval_at_right T) ≫ F_map_aux g₂,
  {
    have := ih (directed_map.dihomotopy.covered_partwise_second_hpart hcov),
    rw split_dihomotopy.second_part_horizontally_eval_0 at this,
    rw split_dihomotopy.second_part_horizontally_eval_1 at this,
    rw dipath.dipath_of_directed_map_of_to_dimap at this,
    rw dipath.dipath_of_directed_map_of_to_dimap at this,
    rw functor_map_aux_cast at this,
    rw functor_map_aux_cast at this,
    rw functor_map_aux_cast at this,
    rw functor_map_aux_cast at this,
    simp at this,
    have := (eq_to_hom_comp_iff _ _ _).mp this,
    rw ← category.assoc at this,
    have := (comp_eq_to_hom_iff _ _ _).mp this,
    rw this,
    simp,
  },
  have h₂ : F_map_aux f₁ ≫ F_map_aux (H.eval_at_right T) = F_map_aux (H.eval_at_right 0) ≫ F_map_aux g₁,
  {
    have := functor_map_aux_of_homotopic_dimaps_0 hX X₁_open X₂_open h_comm (directed_map.dihomotopy.covered_partwise_first_hpart hcov),
    rw split_dihomotopy.first_part_horizontally_eval_0 at this,
    rw split_dihomotopy.first_part_horizontally_eval_1 at this,
    rw dipath.dipath_of_directed_map_of_to_dimap at this,
    rw dipath.dipath_of_directed_map_of_to_dimap at this,
    rw functor_map_aux_cast at this,
    rw functor_map_aux_cast at this,
    rw functor_map_aux_cast at this,
    rw functor_map_aux_cast at this,
    simp at this,
    have := (eq_to_hom_comp_iff _ _ _).mp this,
    rw ← category.assoc at this,
    have := (comp_eq_to_hom_iff _ _ _).mp this,
    rw this,
    simp,
  },

  calc F_map_aux (dipath.of_directed_map f) ≫ F_map_aux (H.eval_at_right 1) = (F_map_aux f₁ ≫ F_map_aux f₂) ≫ F_map_aux (H.eval_at_right 1) : by rw functor_map_aux_split_of_covered_partwise _ _ _ _ f_cov
                  ... = F_map_aux f₁ ≫ (F_map_aux f₂ ≫ F_map_aux (H.eval_at_right 1)) : by rw category.assoc
                  ... = F_map_aux f₁ ≫ (F_map_aux (H.eval_at_right T) ≫ F_map_aux g₂) : by rw h₁
                  ... = (F_map_aux f₁ ≫ F_map_aux (H.eval_at_right T)) ≫ F_map_aux g₂ : by rw category.assoc
                  ... = (F_map_aux (H.eval_at_right 0) ≫ F_map_aux g₁) ≫ F_map_aux g₂ : by rw h₂
                  ... = F_map_aux (H.eval_at_right 0) ≫ (F_map_aux g₁ ≫ F_map_aux g₂) : by rw category.assoc
                  ... = F_map_aux (H.eval_at_right 0) ≫ F_map_aux (dipath.of_directed_map g) : by rw functor_map_aux_split_of_covered_partwise _ _ _ _ g_cov,
end

lemma functor_map_aux_of_covered_dihomotopic_zero_m {m : ℕ} {x y : X} {γ γ' : dipath x y} (h : dipath.dihomotopy.dipath_dihomotopic_covered γ γ' hX 0 m) : 
  F_map_aux γ = F_map_aux γ' :=
begin
  cases h with G HG,
  have h₁ : F_map_aux ((G.eval_at_right 0)) = (eq_to_hom $ congr_arg F_obj γ.source) ≫ (𝟙 (F_obj x)) ≫ (eq_to_hom $ congr_arg F_obj γ'.source.symm),
  {
    have : G.eval_at_right 0 = (dipath.refl x).cast γ.source γ'.source,
    {
      ext t,
      show G(t, 0) = x,
      simp,
    },
    rw this,
    rw functor_map_aux_cast,
    rw functor_map_aux_refl,
  },
  
  have h₂ : F_map_aux ((G.eval_at_right 1)) = (eq_to_hom $ congr_arg F_obj γ.target) ≫ (𝟙 (F_obj y)) ≫ (eq_to_hom $ congr_arg F_obj γ'.target.symm),
  {
    have : G.eval_at_right 1 = (dipath.refl y).cast γ.target γ'.target,
    {
      ext t,
      show G(t, 1) = y,
      simp,
    },
    rw this,
    rw functor_map_aux_cast,
    rw functor_map_aux_refl,
  },

  have := functor_map_aux_of_homotopic_dimaps hX X₁_open X₂_open h_comm HG,
  rw [h₁, h₂] at this,
  rw dipath.dipath_of_directed_map_of_to_dimap at this,
  rw dipath.dipath_of_directed_map_of_to_dimap at this,
  rw functor_map_aux_cast at this,
  rw functor_map_aux_cast at this,
  simp at this,
  have := (eq_to_hom_comp_iff _ _ _).mp this,
  have := (comp_eq_to_hom_iff _ _ _).mp this,
  simp at this,
  exact this,
end


lemma functor_map_aux_of_partwise_covered_dihomotopic :
  Π {n m : ℕ} {x y : X} {γ γ' : dipath x y} (h : dipath.dihomotopy.dipath_dihomotopic_covered γ γ' hX n m),
  F_map_aux γ = F_map_aux γ' :=
begin
  intros n m,
  induction n with n hn,
  { -- Case n = 0
    intros x y γ γ' h,
    exact functor_map_aux_of_covered_dihomotopic_zero_m hX X₁_open X₂_open h_comm h,
  },
  rintros x y γ γ' ⟨F, hF⟩,
  have := dipath.dihomotopy.dipath_dihomotopic_covered_split hX hF,
  rw functor_map_aux_of_covered_dihomotopic_zero_m hX X₁_open X₂_open h_comm this.1,
  apply hn,
  exact this.2,
end

lemma functor_map_aux_of_pre_dihomotopic {γ γ' : dipath x y} (h : γ.pre_dihomotopic γ') :
  F_map_aux γ = F_map_aux γ' :=
begin
  rcases dipath.dihomotopy.dipath_dihomotopic_covered_exists_of_pre_dihomotopic hX h X₁_open X₂_open with ⟨n, m, h⟩,
  exact functor_map_aux_of_partwise_covered_dihomotopic hX X₁_open X₂_open h_comm h,
end

lemma functor_map_aux_of_dihomotopic (γ γ' : dipath x y) (h : γ.dihomotopic γ') :
  F_map_aux γ = F_map_aux γ' :=
begin
  apply eqv_gen.rec_on h,
  exact λ _ _ h, functor_map_aux_of_pre_dihomotopic _ _ _ _ h,
  exact λ γ, rfl,
  exact λ _ _ _ h, h.symm,
  exact λ _ _ _ h₁ h₂, eq.trans,
end

/-
-  ### Define the behaviour on quotient of paths
-/

def functor_map {x y : dπₓ X} (γ : x ⟶ y) : F_obj x ⟶ F_obj y :=
 quotient.lift_on γ F_map_aux (functor_map_aux_of_dihomotopic hX X₁_open X₂_open h_comm)

localized "notation (name := functor_map)
  `F_map` := functor_map hX X₁_open X₂_open h_comm" in directed_van_kampen

lemma functor_map_apply (γ : dipath x y) :
  F_map ⟦γ⟧ = F_map_aux γ := rfl

lemma functor_map_trans {x y z : X} (γ₁ : dipath x y) (γ₂ : dipath y z) : F_map ⟦γ₁.trans γ₂⟧ = F_map ⟦γ₁⟧ ≫ F_map ⟦γ₂⟧ :=
begin
  repeat { rw functor_map_apply },
  exact functor_map_aux_trans hX X₁_open X₂_open h_comm γ₁ γ₂,
end

lemma functor_map_id (x : dπₓ X) : F_map (𝟙 x) = 𝟙 (F_obj x) :=
begin
  rw id_eq_path_refl,
  rw functor_map_apply,
  apply functor_map_aux_refl,
end

lemma functor_map_comp_path {x y z  : X} (γ₁ : dipath x y) (γ₂ : dipath y z) : F_map (⟦γ₁⟧ ≫ ⟦γ₂⟧) = F_map ⟦γ₁⟧ ≫ F_map ⟦γ₂⟧ :=
begin
  rw functor_map_apply,
  rw functor_map_apply,
  rw comp_eq,
  rw ← dipath.dihomotopic.comp_lift,
  exact functor_map_trans hX X₁_open X₂_open h_comm γ₁ γ₂,
end

lemma functor_map_comp {x y z  : dπₓ X} (γ₁ : x ⟶ y) (γ₂ : y ⟶ z) : F_map (γ₁ ≫ γ₂) = F_map γ₁ ≫ F_map γ₂ :=
begin
  have := functor_map_comp_path hX X₁_open X₂_open h_comm (γ₁.out) (γ₂.out),
  rw quotient.out_eq at this,
  rw quotient.out_eq at this,
  exact this,
end

/-
  ## Define the functor F : (dπₓ X) ⟶ C
-/
def functor : (dπₓ X) ⟶ C := {
  obj := F_obj,
  map := λ x y, F_map,
  map_id' := λ x, functor_map_id hX X₁_open X₂_open h_comm x,
  map_comp' := λ x y z γ₁ γ₂, functor_map_comp hX X₁_open X₂_open h_comm γ₁ γ₂
}

localized "notation (name := functor)
  `F` := functor hX X₁_open X₂_open h_comm" in directed_van_kampen

lemma functor_obj_def {x : dπₓ X} : (F).obj x = F_obj x := rfl
lemma functor_map_def {x y : dπₓ X} (f : x ⟶ y) : (F).map f = F_map f := rfl

lemma functor_comp_left_object (x : X₁) : (F).obj ((dπₘ j₁).obj x) = F₁.obj x :=
begin
  show F_obj (j₁ _) = _,
  rw ← functor_obj_apply_one hX h_comm,
  congr' 1,
  apply subtype.coe_inj.mp,
  simp,
  rw subtype_hom_eq_coe,
  rw subtype_hom_eq_coe,
  exact x.2,
end

lemma functor_comp_left_dipath {x y : X₁} (γ : dipath x y) : F_map ((dπₘ j₁).map ⟦γ⟧) =
    (eq_to_hom (functor_comp_left_object hX X₁_open X₂_open h_comm x)) ≫ (F₁.map ⟦γ⟧) ≫ 
    (eq_to_hom (functor_comp_left_object hX X₁_open X₂_open h_comm y).symm)
     :=
begin
  rw subtype_path_class_eq_map,
  rw functor_map_apply,
  have h₁ : range (γ.map (directed_subtype_inclusion X₁)) ⊆ X₁ := range_dipath_map_inclusion γ,
  have h₂ : covered_partwise hX (γ.map (directed_subtype_inclusion X₁)) 0 := or.inl h₁,
  rw functor_map_aux_apply hX X₁_open X₂_open h_comm h₂,
  rw functor_map_of_covered_partwise_apply_0,
  rw functor_map_of_covered_apply_left' hX h_comm h₁,
  rw functor_map_aux_part_one,
  rw subtype_dipath_of_included_dipath_eq,
  rw functor_cast F₁ γ,
  simp,
  refl,
end

/- Shpw that the two obtained triangles commute -/
lemma functor_comp_left : (dπₘ j₁) ⋙ F = F₁ :=
begin
  apply category_theory.functor.ext,
  intros x y f,
  show F_map _ = _,
  rw ← quotient.out_eq f,
  rw functor_comp_left_dipath hX X₁_open X₂_open h_comm f.out,
end

lemma functor_comp_right_object (x : X₂) : (F).obj ((dπₘ j₂).obj x) = F₂.obj x :=
begin
  show F_obj (j₂ _) = _,
  rw ← functor_obj_apply_two hX h_comm,
  congr' 1,
  apply subtype.coe_inj.mp,
  simp,
  rw subtype_hom_eq_coe,
  rw subtype_hom_eq_coe,
  exact x.2,
end

lemma functor_comp_right_dipath {x y : X₂} (γ : dipath x y) : F_map ((dπₘ j₂).map ⟦γ⟧) =
    (eq_to_hom (functor_comp_right_object hX X₁_open X₂_open h_comm x)) ≫ (F₂.map ⟦γ⟧) ≫ 
    (eq_to_hom (functor_comp_right_object hX X₁_open X₂_open h_comm y).symm)
     :=
begin
  rw subtype_path_class_eq_map,
  rw functor_map_apply,
  have h₁ : range (γ.map (directed_subtype_inclusion X₂)) ⊆ X₂ := range_dipath_map_inclusion γ,
  have h₂ : covered_partwise hX (γ.map (directed_subtype_inclusion X₂)) 0 := or.inr h₁,
  rw functor_map_aux_apply hX X₁_open X₂_open h_comm h₂,
  rw functor_map_of_covered_partwise_apply_0,
  rw functor_map_of_covered_apply_right' hX h_comm h₁,
  rw functor_map_aux_part_two,
  rw subtype_dipath_of_included_dipath_eq,
  rw functor_cast F₂ γ,
  simp,
  refl,
end

lemma functor_comp_right : (dπₘ j₂) ≫ F = F₂ :=
begin
  apply category_theory.functor.ext,
  intros x y f,
  show F_map _ = _,
  rw ← quotient.out_eq f,
  rw functor_comp_right_dipath hX X₁_open X₂_open h_comm f.out,
end

lemma functor_uniq_aux_obj (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) (x : X) :
  F'.obj x = (F).obj x :=
begin
  rw functor_obj_def,
  cases ((set.mem_union x X₁ X₂).mp (filter.mem_top.mpr hX x)) with hx₁ hx₂,
  {
    rw ← functor_obj_apply_one hX h_comm hx₁,
    rw eq_of_functor_obj h₁.symm,
    show F'.obj _ = F'.obj _,
    apply congr_arg,
    refl,
  },
  {
    rw ← functor_obj_apply_two hX h_comm hx₂,
    rw eq_of_functor_obj h₂.symm,
    show F'.obj _ = F'.obj _,
    apply congr_arg,
    refl,
  },
end

lemma functor_uniq_of_covered (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) {x y : X} {γ : dipath x y} (hγ : covered γ hX) :
  F'.map ⟦γ⟧ =
    (eq_to_hom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x)) ≫ (F).map ⟦γ⟧ ≫ (eq_to_hom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ y).symm) :=
begin
  rw functor_map_def,
  rw functor_map_apply,
  have : covered_partwise hX γ 0 := hγ,
  rw functor_map_aux_apply _ _ _ _ this,
  rw functor_map_of_covered_partwise_apply_0 _ _ this,
  cases hγ,
  {
    rw functor_map_of_covered_apply_left' _ _ hγ,
    unfold functor_map_aux_part_one,
    rw ← map_subtype_dipath_eq γ hγ,
    show ((dπₘ j₁) ≫ F').map _ = _,
    rw eq_of_functor_map h₁,
    simp,
    refl,
  },
  {
    rw functor_map_of_covered_apply_right' _ _ hγ,
    unfold functor_map_aux_part_two,
    rw ← map_subtype_dipath_eq γ hγ,
    show ((dπₘ j₂) ≫ F').map _ = _,
    rw eq_of_functor_map h₂,
    simp,
    refl,
  },
end

lemma functor_uniq_aux_map (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) {n : ℕ} :
  Π {x y : X} {γ : dipath x y} (hγ : covered_partwise hX γ n), F'.map ⟦γ⟧ =
    (eq_to_hom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ x)) ≫ (F).map ⟦γ⟧ ≫ (eq_to_hom (functor_uniq_aux_obj hX X₁_open X₂_open h_comm F' h₁ h₂ y).symm) :=
begin
  induction n with n ih,
  { -- Case n = 0
    intros x y γ hγ,
    exact functor_uniq_of_covered _ _ _ _ F' h₁ h₂ hγ,
  },
  -- Case n > 0
  intros x y γ hγ,
  let T := frac (nat.succ_pos n.succ) (nat.succ_le_succ (nat.zero_le n.succ)), -- T = 1/(n+1+1)
  have hT₀ : 0 < T := frac_pos (zero_lt_one) _,
  have hT₁ : T < 1 := frac_lt_one (zero_lt_one) (nat.succ_lt_succ (nat.succ_pos n)),
  rw split_dipath.first_trans_second_reparam_eq_self γ hT₀ hT₁,
  rw dipath.dihomotopic.quot_reparam,
  rw dipath.dihomotopic.comp_lift,
  rw ← comp_eq,
  rw category_theory.functor.map_comp,
  rw category_theory.functor.map_comp,
  rw functor_uniq_of_covered hX X₁_open X₂_open h_comm  F' h₁ h₂ hγ.left,
  rw ih hγ.right,
  simp,
end

lemma functor_uniq (F' : (dπₓ X) ⟶ C) (h₁ : (dπₘ j₁) ≫ F' = F₁) (h₂ : (dπₘ j₂) ≫ F' = F₂) : F' = F :=
begin
  apply category_theory.functor.ext,
  intros x y f,
  rw ← quotient.out_eq f,
  cases has_subpaths hX X₁_open X₂_open (quotient.out f) with n hn,
  exact functor_uniq_aux_map hX X₁_open X₂_open h_comm F' h₁ h₂ hn,
end

end pushout_functor

include hX X₁_open X₂_open

/--
  The Van Kampen Theorem: the fundamental category functor dπ induces a pushout in the category of categories.
-/
theorem directed_van_kampen {hX₁ : is_open X₁} {hX₂ : is_open X₂} {hX : X₁ ∪ X₂ = set.univ} :
  is_pushout (dπₘ i₁) (dπₘ i₂) (dπₘ j₁) (dπₘ j₂) :=
begin
  apply pushout_alternative.is_pushout_alternative,
  {
    rw ← functor.map_comp,
    rw ← functor.map_comp,
    exact congr_arg dπₘ rfl
  },
  intros C F₁ F₂ h_comm,
  use (pushout_functor.functor hX X₁_open X₂_open h_comm),
  split,
  {
    split,
    apply pushout_functor.functor_comp_left,
    apply pushout_functor.functor_comp_right
  },
  rintros F' ⟨h₁, h₂⟩,
  exact pushout_functor.functor_uniq hX X₁_open X₂_open h_comm F' h₁ h₂,
end

end directed_van_kampen
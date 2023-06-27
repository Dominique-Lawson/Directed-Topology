import fundamental_category

/-
  This file contains properties of dipaths contained in directed subspaces of a directed space.
  In particular, properties about their equivalence classes in the fundamental category.
-/

open set
open_locale fundamental_category unit_interval

local attribute [instance] dipath.dihomotopic.setoid

namespace disubtype

variables {X : dTop} {X₀ : set X}

lemma subtype_hom_eq_coe (x : X₀) : (dTop.directed_subtype_hom X₀) x = (x : X) := rfl

lemma range_dipath_map_inclusion {x y : X₀} (γ : dipath x y) : range (γ.map (directed_subtype_inclusion X₀)) ⊆ X₀ :=
begin
  rintros z ⟨t, ht⟩,
  rw ← ht,
  show (dTop.directed_subtype_hom X₀) (γ t) ∈ X₀,
  rw subtype_hom_eq_coe,
  exact subtype.mem (γ t),
end

lemma subtype_path_class_eq_map {x y : X₀} (γ : dipath x y) :
  (dπₘ (dTop.directed_subtype_hom X₀)).map ⟦γ⟧ = ⟦(γ.map (directed_subtype_inclusion X₀))⟧ := rfl


variables {x y z : X}

lemma source_elt_of_image_subset {γ : dipath x y} (hγ : range γ ⊆ X₀) : x ∈ X₀ := γ.source ▸ (hγ (mem_range_self 0))
lemma target_elt_of_image_subset {γ : dipath x y} (hγ : range γ ⊆ X₀) : y ∈ X₀ := γ.target ▸ (hγ (mem_range_self 1))

def subtype_path {γ : dipath x y} (hγ : range γ ⊆ X₀) :
  path (⟨x, source_elt_of_image_subset hγ⟩ : X₀) ⟨y, target_elt_of_image_subset hγ⟩ :=
{
  to_fun := λ t, ⟨γ t, hγ (mem_range_self t)⟩,
  source' := by simp,
  target' := by simp,
}

def subtype_dipath (γ : dipath x y) (hγ : range γ ⊆ X₀) :
  dipath (⟨x, source_elt_of_image_subset hγ⟩ : X₀) ⟨y, target_elt_of_image_subset hγ⟩ :=
{
  to_path := subtype_path hγ,
  dipath_to_path :=
    begin
      show is_dipath ((subtype_path hγ).map continuous_subtype_coe),
      convert γ.dipath_to_path,
      ext t,
      refl,
    end
}

lemma map_subtype_dipath_eq {x y : X} (γ : dipath x y) (hγ : range γ ⊆ X₀) :
  (dπₘ (dTop.directed_subtype_hom X₀)).map ⟦subtype_dipath γ hγ⟧ = ⟦γ⟧ :=
begin
  rw subtype_path_class_eq_map,
  congr' 1,
  ext t,
  refl,
end

lemma subtype_dipath_of_included_dipath_eq {x y : X₀} (γ : dipath x y) : subtype_dipath (γ.map (directed_subtype_inclusion X₀)) (range_dipath_map_inclusion γ) =
  γ.cast (by { ext, rw ← subtype_hom_eq_coe x, refl, }) (by { ext, rw ← subtype_hom_eq_coe y, refl, }) :=
begin
  ext t,
  refl,
end

lemma range_refl_subset_of_mem {x : X} (hx : x ∈ X₀) : range (dipath.refl x) ⊆ X₀ :=
begin
  rw dipath.refl_range,
  exact singleton_subset_iff.mpr hx,
end

lemma subtype_refl {x : X} (hx : x ∈ X₀) : (subtype_dipath (dipath.refl x) (range_refl_subset_of_mem hx)) = dipath.refl ⟨x, hx⟩ := rfl

lemma subsets_of_trans_subset {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₀) :
  range γ₁ ⊆ X₀ ∧ range γ₂ ⊆ X₀ :=
begin
  rw dipath.trans_range at hγ,
  exact ⟨subset_trans (subset_union_left _ _) hγ, subset_trans (subset_union_right _ _) hγ⟩
end

lemma trans_subset_of_subsets  {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ₁ : range γ₁ ⊆ X₀) (hγ₂ : range γ₂ ⊆ X₀) :
  range (γ₁.trans γ₂) ⊆ X₀ :=
begin
  rw dipath.trans_range,
  exact union_subset hγ₁ hγ₂,
end

lemma subtype_trans {γ₁ : dipath x y} {γ₂ : dipath y z} (hγ : range (γ₁.trans γ₂) ⊆ X₀) :
  (subtype_dipath γ₁ (subsets_of_trans_subset hγ).1).trans (subtype_dipath γ₂ (subsets_of_trans_subset hγ).2) = subtype_dipath (γ₁.trans γ₂) hγ :=
begin
  ext t,
  show _ = (γ₁.trans γ₂) t,
  rw dipath.trans_apply,
  rw dipath.trans_apply,
  split_ifs,
  refl,
  refl,
end

lemma subtype_reparam {γ : dipath x y} (hγ : range γ ⊆ X₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1):
  subtype_dipath (γ.reparam f hf₀ hf₁) (by exact (dipath.range_reparam γ f hf₀ hf₁).symm ▸ hγ) =
    (subtype_dipath γ hγ).reparam f hf₀ hf₁ := rfl

lemma reparam_subset_of_subset {γ : dipath x y} (hγ : range γ ⊆ X₀) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  range (γ.reparam f hf₀ hf₁) ⊆ X₀ :=
begin
  rw dipath.range_reparam,
  exact hγ,
end

def dihomotopy_of_subtype {γ γ' : dipath x y} (hγ : range γ ⊆ X₀) (hγ' : range γ' ⊆ X₀) {F : dipath.dihomotopy γ γ'} (hF : range F ⊆ X₀) :
  dipath.dihomotopy (subtype_dipath γ hγ) ((@subtype_dipath X X₀ x y γ' hγ')) :=
{
  to_fun := λ t, ⟨F t, hF (mem_range_self t)⟩,
  directed_to_fun := λ a b p hp, F.directed_to_fun _ hp,
  map_zero_left' :=
    begin
      intro t,
      simp,
      refl,
    end,
  map_one_left' :=
    begin
      intro t,
      simp,
      refl,
    end,
  prop' :=
    begin
      intros t p hp,
      have := F.prop' t p hp,
      split,
      { ext, show _ = (γ.to_directed_map) p, rw ← this.1, refl },
      { ext, show _ = (γ'.to_directed_map) p, rw ← this.2, refl },
    end
}

lemma dihom_subtype_of_dihom_range_subset {γ γ' : dipath x y} (hγ : range γ ⊆ X₀) (hγ' : range γ' ⊆ X₀) {F : dipath.dihomotopy γ γ'} (hF : range F ⊆ X₀) :
  ⟦subtype_dipath γ hγ⟧ = ⟦@subtype_dipath X X₀ x y γ' hγ'⟧ :=
quotient.eq.mpr (eqv_gen.rel _ _ ⟨dihomotopy_of_subtype hγ hγ' hF⟩)



end disubtype
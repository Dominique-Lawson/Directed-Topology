import constructions

/-
  This file contains the definition of the directed unit interval.
  The directedness is induced by the preorder it inherits from ℝ.
-/

open_locale unit_interval

universe u

namespace directed_unit_interval

/--
  Construct the directed unit interval by using the preorder inherited from ℝ
-/
instance : directed_space I := directed_space.preorder I

/--
  The identity on I as a path I → I.
-/
def identity_path : path (0 : I) (1 : I) :=
{
  to_fun := λ x, x,
  continuous_to_fun := by continuity,
  source' := by simp,
  target' := by simp,
}

/-- The identity path is a directed path. -/
lemma identity_dipath : is_dipath identity_path := λ a b hab, hab

/--
  If `γ` is path and the identity path on I composed with `γ` is a directed path, then `γ` is a directed path.
-/
lemma is_dipath_of_is_dipath_comp_id {X : Type u} [directed_space X] {x y : X} {γ : path x y} (h : is_dipath $ identity_path.map γ.continuous_to_fun) : is_dipath γ :=
begin
  convert is_dipath_cast (identity_path.map γ.continuous_to_fun) (by simp) (by simp) h,
  ext t,
  refl,
end

/-- A directed map from I to I is monotone -/
lemma monotone_of_directed (f : D(I, I)) : monotone f :=
  λ x y hxy, (f.directed_to_fun identity_path identity_dipath) hxy

/-- A continuous map from I to I that is monotone is directed -/
lemma directed_of_monotone (f : C(I, I)) (hf_mono : monotone f) : directed_map.directed f :=
  λ x y γ γ_dipath t₀ t₁ ht₀t₁, hf_mono (γ_dipath ht₀t₁)

/-- A directed path on I is bounded by its source and target -/
lemma directed_path_bounded {t₀ t₁ : I} {γ : path t₀ t₁} (γ_dipath : is_dipath γ) : ∀ {t : I}, t₀ ≤ γ t ∧ γ t ≤ t₁ :=
  λ t, monotone_path_bounded γ_dipath t

/-- The source of a directed path on I is `≤` than its target -/
lemma directed_path_source_le_target {t₀ t₁ : I} {γ : path t₀ t₁} (γ_dipath : is_dipath γ) : t₀ ≤ t₁ :=
  monotone_path_source_le_target γ_dipath

end directed_unit_interval

import dipath
import dTop

/-
  This file contains definitions about stretching a (directed) path in two ways:
    If its image is contained in `[0, 1/2]`, it can be stretched upwards
    If its image is contained in `[1/2, 1]`, it can be stretched downwards

  These cases can be determined by the endpoints of the directed path.
-/
open auxiliary
open_locale unit_interval

namespace dipath

/-### Stretching a path that only lives in the first half of the unit interval upwards -/

lemma double_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : 2 * (γ t : ℝ) ∈ I :=
  double_mem_I $ le_trans (monotone_path_bounded γ.dipath_to_path t).2 (ht₁)

def stretch_up_path {t₀ t₁ : I} (γ : dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : 
  path (⟨2 * ↑t₀, by {
    rw ←γ.source',
    exact double_mem_I_of_bounded 0 γ ht₁,
  }⟩ : I) ⟨2 * ↑t₁, double_mem_I ht₁⟩ :=
{
  to_fun := λ t, ⟨2 * (γ t), double_mem_I_of_bounded t γ ht₁⟩,
  source' := by simp [γ.source'],
  target' := by simp [γ.target'],
}

lemma stretch_up_is_dipath {t₀ t₁ : I} (γ : dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) :
  is_dipath (stretch_up_path γ ht₁) :=
begin
  intros x y hxy,
  unfold stretch_up_path,
  simp,
  exact γ.dipath_to_path hxy,
end

def stretch_up {t₀ t₁ : I} (γ : dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) :
  dipath (⟨2 * ↑t₀, by {
    rw ←γ.source',
    exact double_mem_I_of_bounded 0 γ ht₁,
  }⟩ : I) ⟨2 * ↑t₁, double_mem_I ht₁⟩ :=
{
  to_path := stretch_up_path γ ht₁,
  dipath_to_path := stretch_up_is_dipath γ ht₁,
}

/-### Stretching a path that only lives in the second half of the unit interval downwards -/

lemma double_sub_one_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀)
 : 2 * (γ t : ℝ) - 1 ∈ I :=
  double_sub_one_mem_I $ le_trans ht₀ (monotone_path_bounded γ.dipath_to_path t).1

def stretch_down_path {t₀ t₁ : I} (γ : dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : 
  path
    (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
    ⟨2 * ↑t₁ - 1, by { rw ←γ.target', exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ :=
{
  to_fun := λ t, ⟨2 * (γ t) - 1, double_sub_one_mem_I_of_bounded t γ ht₀⟩,
  source' := by simp [γ.source'],
  target' := by simp [γ.target'],
}

lemma stretch_down_is_dipath {t₀ t₁ : I} (γ : dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) :
  is_dipath (stretch_down_path γ ht₀) :=
begin
  intros x y hxy,
  unfold stretch_down_path,
  simp,
  exact γ.dipath_to_path hxy,
end

def stretch_down {t₀ t₁ : I} (γ : dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) :
  dipath
    (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
    ⟨2 * ↑t₁ - 1, by { rw ←γ.target', exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ :=
{
  to_path := stretch_down_path γ ht₀,
  dipath_to_path := stretch_down_is_dipath γ ht₀,
}

end dipath
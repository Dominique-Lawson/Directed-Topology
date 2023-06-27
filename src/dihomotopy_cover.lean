import path_cover
import split_dihomotopy

/-
  This file contains the definition of a (n, m)-covered (dipath) dihomotopy, covered by X₁ and X₂:
      It maps all subsquares  [i/n, (i+1)/n] × [j/m, (j+1)/m] into either X₁ or X₂
    
  Conditions for being (n, m)-covered are given.

  Two paths are called (n, m)-dihomotopic if a (n, m)-covered path dihomotopy between them exists.
-/

open set directed_map auxiliary
open_locale unit_interval

noncomputable theory

namespace directed_map
namespace dihomotopy

variables {X : dTop} {f g : D(I, X)} {X₀ X₁ : set X}

def covered (F : dihomotopy f g) (hX : X₀ ∪ X₁ = univ) : Prop := range F ⊆ X₀ ∨ range F ⊆ X₁

lemma mem_I_of_mem_interval {t : ℝ} {n i : ℕ} (hi : i < n.succ) (h : t ∈ Icc ((i:ℝ)/↑(n.succ)) (↑(i+1)/↑(n.succ))) : t ∈ I :=
begin
  split,
  exact le_trans (div_nonneg (nat.cast_nonneg i) (nat.cast_nonneg n.succ)) h.1,
  exact le_trans h.2 ((div_le_one (show (n.succ : ℝ) > 0, by exact nat.cast_pos.mpr (nat.succ_pos n))).mpr (nat.cast_le.mpr (nat.succ_le_of_lt hi))),
end

lemma mem_I_of_mem_interval_coed {t : ℝ} {n i : ℕ} (hi : i < n.succ) (h : t ∈ Icc ((i:ℝ)/(↑n+1)) ((↑i+1)/(↑n+1))) : t ∈ I :=
begin
  apply mem_I_of_mem_interval hi,
  convert h; exact nat.cast_succ _,
end

lemma mem_unit_subsquare {t₀ t₁ : ℝ} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ)
  (ht₀ : t₀ ∈ Icc ((i : ℝ)/↑(n.succ)) (↑(i+1)/↑(n.succ))) (ht₁ : t₁ ∈ Icc ((j : ℝ)/↑(m.succ)) (↑(j+1)/↑(m.succ))) :
    ((⟨t₀, mem_I_of_mem_interval hi ht₀⟩ : I), (⟨t₁, mem_I_of_mem_interval hj ht₁⟩ : I)) ∈ unit_subsquare hi hj :=
  ⟨⟨ht₀.1, ht₀.2⟩, ⟨ht₁.1, ht₁.2⟩⟩

/--
  A dihomotopy is covered partwise n m if it can be covered by rectangles (n+1 vertically, m+1 horizontally) such that each rectangle is covered by either X₀ or X₁
-/
def covered_partwise (F : dihomotopy f g) (hX : X₀ ∪ X₁ = univ) (n m : ℕ) : Prop :=
  ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < m.succ),
    F '' (unit_subsquare hi hj) ⊆ X₀ ∨ F '' (unit_subsquare hi hj) ⊆ X₁

lemma zero_le_of_frac_zero_le {t : I} (ht : (frac zero_lt_one zero_le_one) ≤ t) :
  0 ≤ t :=
begin
  convert ht,
  rw frac_zero,
end

lemma le_one_of_frac_self_le {t : I} {n : ℕ} (ht : t ≤ (frac (nat.succ_pos n) (le_refl _))) :
  t ≤ 1 :=
begin
  convert ht,
  rw frac_self,
end

lemma unit_interval_mul_le (a b : I) : a * b ≤ a :=
begin
  apply subtype.coe_le_coe.mp,
  rw Icc.coe_mul,
  convert mul_le_mul (le_refl _) b.2.2 b.2.1 a.2.1,
  rw mul_one,
  refl,
end

lemma mem_unit_square (t : I × I) : t ∈ unit_subsquare zero_lt_one zero_lt_one :=
begin
  unfold unit_subsquare,
  rw frac_zero,
  rw frac_self,
  exact ⟨⟨t.1.2.1, t.1.2.2⟩, ⟨t.2.2.1, t.2.2.2⟩⟩
end

lemma covered_of_covered_partwise {F : dihomotopy f g} {hX : X₀ ∪ X₁ = univ} (hF : covered_partwise F hX 0 0) : covered F hX :=
begin
  unfold covered,
  cases hF 0 0 zero_lt_one zero_lt_one,
  {
    left,
    rintros x ⟨⟨t₀, t₁⟩, ht⟩,
    rw ← ht,
    exact h ⟨(t₀, t₁), mem_unit_square _, rfl⟩,
  },
  {
    right,
    rintros x ⟨⟨t₀, t₁⟩, ht⟩,
    rw ← ht,
    exact h ⟨(t₀, t₁), mem_unit_square _, rfl⟩,
  },
end

lemma left_path_image_interval_subset_of_dihomotopy_subset (F : dihomotopy f g) (n : ℕ) {i m : ℕ} (hi : i < m.succ) :
  (dipath.of_directed_map f).to_path.extend '' Icc (↑i / (↑m + 1)) ((↑i + 1) / (↑m + 1)) ⊆ F ''  unit_subsquare (nat.succ_pos n) hi :=
begin
  rintros x ⟨t, ⟨ht, rfl⟩⟩,
  have tI : t ∈ I := mem_I_of_mem_interval_coed hi ht,
  rw path.extend_extends (dipath.of_directed_map f).to_path tI,
  use (0, ⟨t, tI⟩),
  split,
  {
    apply mem_unit_subsquare,
    split,
    norm_num,
    apply div_nonneg,
    norm_num,
    exact nat.cast_nonneg _,
    convert ht; exact nat.cast_succ _,
  },
  {
    simp,
    refl,
  }
end

lemma path_covered_partiwse_of_dihomotopy_covered_partwise_left {F : dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : covered_partwise F hX n m) :
  dipath.covered_partwise hX (dipath.of_directed_map f) m :=
begin
  apply dipath.covered_partwise.covered_partwise_of_covered_by_intervals,
  intros i hi,
  cases hF 0 i (nat.succ_pos n) hi,
  {
    left,
    exact subset_trans (left_path_image_interval_subset_of_dihomotopy_subset F n hi) h,
  },
  {
    right,
    exact subset_trans (left_path_image_interval_subset_of_dihomotopy_subset F n hi) h,
  },
end

lemma right_path_image_interval_subset_of_dihomotopy_subset (F : dihomotopy f g) (n : ℕ) {i m : ℕ} (hi : i < m.succ) :
  (dipath.of_directed_map g).to_path.extend '' Icc (↑i / (↑m + 1)) ((↑i + 1) / (↑m + 1)) ⊆ F ''  unit_subsquare (nat.lt_succ_self n) hi :=
begin
  rintros x ⟨t, ⟨ht, rfl⟩⟩,
  have tI : t ∈ I := mem_I_of_mem_interval_coed hi ht,
  rw path.extend_extends (dipath.of_directed_map g).to_path tI,
  use (1, ⟨t, tI⟩),
  split,
  {
    apply mem_unit_subsquare,
    {
      split,
      exact (div_le_one (show (n.succ : ℝ) > 0, by exact nat.cast_pos.mpr (nat.succ_pos n))).mpr (nat.cast_le.mpr (nat.le_succ n)),
      rw div_self,
      exact nat.cast_ne_zero.mpr (ne_of_gt (nat.succ_pos n)),
    },
    convert ht; exact nat.cast_succ _,
  },
  {
    simp,
    refl
  }
end

lemma path_covered_partiwse_of_dihomotopy_covered_partwise_right {F : dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : covered_partwise F hX n m) :
  dipath.covered_partwise hX (dipath.of_directed_map g) m :=
begin
  apply dipath.covered_partwise.covered_partwise_of_covered_by_intervals,
  intros i hi,
  cases hF n i (nat.lt_succ_self n) hi,
  {
    left,
    exact subset_trans (right_path_image_interval_subset_of_dihomotopy_subset F n hi) h,
  },
  {
    right,
    exact subset_trans (right_path_image_interval_subset_of_dihomotopy_subset F n hi) h,
  },
end

lemma covered_partwise_exists (F : dihomotopy f g) (hX : X₀ ∪ X₁ = univ) (X₀_open : is_open X₀) (X₁_open : is_open X₁) :
  ∃ (n m : ℕ), covered_partwise F hX n m :=
begin
  set c : ℕ → set (I × I) := λ i, if i = 0 then F ⁻¹' X₀ else F ⁻¹'  X₁ with c_def,
  have h₁ : ∀ i, is_open (c i),
  {
    intro i,
    rw c_def,
    by_cases i = 0; simp [h],
    exact F.continuous_to_fun.is_open_preimage X₀ X₀_open,
    exact F.continuous_to_fun.is_open_preimage X₁ X₁_open,
  },
  have h₂ : unit_square ⊆ (⋃ (i : ℕ), c i),
  {
    intros x hx,
    simp [c_def],
    have : F x ∈ X₀ ∪ X₁ := hX.symm ▸ (set.mem_univ $ F x),
    cases this with h h,
    { use 0, simp, exact h },
    { use 1, simp, exact h }
  },

  rcases (lebesgue_number_lemma_unit_square h₁ h₂) with ⟨n, hn⟩,
  use n,
  use n,
  intros i j hi hj,
  cases (hn i j hi hj) with ι hι,
  rw c_def at hι,
  simp at hι,
  by_cases ι = 0,
  { left, simp [h] at hι, exact set.image_subset_iff.mpr hι },
  { right, simp [h] at hι, exact set.image_subset_iff.mpr hι },
end

/--
  The image of a dihomotopy F of the square `[j/(m+1), (j+1)/(m+1)] × [0, 1/(n+2)]`
  contains the image of the first part of F vertically (split at 1/(n+2)) of `[j/(m+1), (j+1)/(m+1)] × [0, 1]`.
-/
lemma fpv_subsquare {x y : X} {γ₁ γ₂ : dipath x y} {F : dipath.dihomotopy γ₁ γ₂} {n m j : ℕ} (hj : j < m.succ) :
  (split_dihomotopy.first_part_vertically_dihomotopy F (frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le n.succ)))).to_dihomotopy '' (unit_subsquare zero_lt_one hj)
   ⊆ F '' (unit_subsquare (nat.zero_lt_succ n.succ) hj) :=
begin
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩,
  have : ((split_dihomotopy.first_part_vertically_dihomotopy F _).to_dihomotopy) (t₀, t₁) = 
          (split_dihomotopy.first_part_vertically_dihomotopy F (frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le n.succ)))) (t₀, t₁) := rfl,
  rw this at ht,
  rw split_dihomotopy.fpv_apply at ht,
  show ∃ a, a ∈ unit_subsquare _ hj ∧ F a = z,
  refine ⟨_, _, ht⟩,
  split,
  {
    split,
    {
      rw frac_zero,
      unit_interval,
    },
    {
      exact unit_interval_mul_le _ _,
    }
  },
  exact tI.2,
end

/--
  If F can be covered by `(n+1) × m` rectangles, then F.first_part_vertically_dihomotopy at T = 1/(n+1) is covered by `1 × m` rectangles.
-/
lemma covered_partwise_first_part {x y : X} {γ₁ γ₂ : dipath x y} {F : dipath.dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : covered_partwise F.to_dihomotopy hX n.succ m) :
  covered_partwise (split_dihomotopy.first_part_vertically_dihomotopy F (frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le n.succ)))).to_dihomotopy hX 0 m :=
begin
  unfold covered_partwise at hF,
  unfold covered_partwise,
  intros i j hi hj,
  obtain ⟨rfl⟩ : i = 0 := by linarith,
  cases (hF 0 j (nat.succ_pos n.succ) hj) with h h,
  { left, exact subset_trans (fpv_subsquare _) h },
  { right, exact subset_trans (fpv_subsquare _) h },
end

/--
  If i/(n+1) ≤ t, then (i+1)/(n+2) ≤ (σ q) * t + q, where q = 1/(n+2)
-/
lemma spv_aux₁_coed {t : ℝ} {n i : ℕ} (hi : i < n.succ) (ht : (i : ℝ)/(n.succ : ℝ) ≤ t) :
  (i+1 : ℝ) / (n+2 : ℝ) ≤ (1 - 1/(n+1+1)) * t + (1/(n+1+1)) :=
begin
  have h₀ : 0 ≤ (i : ℝ)/(n.succ : ℝ),
  {
    apply div_nonneg,
    exact nat.cast_nonneg i,
    exact nat.cast_nonneg n.succ,
  },
  have h₁ : 0 ≤ t := le_trans h₀ ht,
  have h₂ : (n.succ : ℝ) > 0 := nat.cast_pos.mpr (nat.succ_pos n),
  have h₃ : 0 ≤ (n : ℝ) + 1,
  {
    apply le_of_lt,
    convert h₂,
    exact (nat.cast_succ n).symm,
  },
  rw one_sub_inverse_of_add_one,
  rw mul_comm,
  rw mul_div,
  rw div_add_div_same,
  apply div_le_div,
  {
    linarith [mul_nonneg h₁ h₃],
  },
  {
    apply add_le_add_right,
    calc (i : ℝ) = ↑i * 1 : by rw mul_one
        ... = ↑i * ((↑n.succ)/(↑n.succ)) : by rw div_self (ne_of_gt h₂)
        ... = ↑i/(↑n.succ) * (↑n.succ) : by ring
        ... ≤ t * (↑n.succ) : mul_le_mul_of_le_of_le ht (le_refl _) h₀ (le_of_lt h₂)
        ... = t * (↑n+1) : by rw nat.cast_succ,
  },
  linarith,
  linarith,
  linarith,
end

/--
  If i/(n+1) ≤ t, then (i+1)/(n+2) ≤ (σ q) * t + q, where q = 1/(n+2)
-/
lemma spv_aux₁ {t : I} {n i : ℕ} (hi : i < n.succ) (ht : frac (nat.succ_pos n) (le_of_lt hi) ≤ t) :
  frac (nat.succ_pos n.succ) (le_of_lt (nat.succ_lt_succ hi)) ≤ (⟨_, interp_left_mem_I (frac (nat.succ_pos n.succ) (nat.succ_le_succ (nat.zero_le n.succ))) t⟩ : I) :=
begin
  apply subtype.coe_le_coe.mp,
  convert spv_aux₁_coed hi ht,
  rw frac_coe,
  congr' 1,
  rw nat.cast_succ,
  rw nat.cast_succ,
  rw nat.cast_succ,
  linarith,
  simp,
end

/--
  If t ≤ (i+1)/(n+1), then (σ q) * t + q ≤ (i+2)/(n+2), where q = 1/(n+2)
-/
lemma spv_aux₂_coed {t : ℝ} {n i : ℕ} (hi : i < n.succ) (ht₀ : 0 ≤ t) (ht : t ≤ (i.succ : ℝ)/(n.succ : ℝ)) :
  (1 - 1/(n+1+1 : ℝ)) * t + (1/(n+1+1 : ℝ)) ≤ (i+2 : ℝ) / (n+2 : ℝ) :=
begin
  have h₀ : (n.succ : ℝ) > 0 := nat.cast_pos.mpr (nat.succ_pos n),
  have h₁ : (n : ℝ) ≥ 0 := nat.cast_nonneg n,
  have h₂ : (i : ℝ) ≥ 0 := nat.cast_nonneg i,
  rw one_sub_inverse_of_add_one,
  rw mul_comm,
  rw mul_div,
  rw div_add_div_same,
  apply div_le_div,
  linarith,
  {
    rw ← one_add_one_eq_two,
    rw ← add_assoc,
    apply add_le_add_right,
    calc t * (n + 1 : ℝ) = t * (↑n.succ) : by rw nat.cast_succ
                  ... ≤ (↑i.succ)/(↑n.succ) * (↑n.succ) : mul_le_mul_of_le_of_le ht (le_refl _) ht₀ (le_of_lt h₀)
                  ... = (↑n.succ)/(↑n.succ) * (↑i.succ) : by ring
                  ... = 1 * (↑i.succ) : by rw div_self (ne_of_gt h₀)
                  ... = (↑i.succ) : one_mul _
                  ... = (↑i + 1) : by rw nat.cast_succ,
  },
  linarith,
  linarith,
  linarith,
end

/--
  If t ≤ (i+1)/(n+1), then (σ q) * t + q ≤ (i+2)/(n+2), where q = 1/(n+2)
-/
lemma spv_aux₂ {t : I} {n i : ℕ} (hi : i < n.succ) (ht : t ≤ frac (nat.succ_pos n) (nat.succ_le_of_lt hi)) :
  (⟨_, interp_left_mem_I (frac (nat.succ_pos n.succ) (nat.succ_le_succ (nat.zero_le n.succ))) t⟩ : I) ≤ frac (nat.succ_pos n.succ) (nat.succ_le_of_lt (nat.succ_lt_succ hi)) :=
begin
  apply subtype.coe_le_coe.mp,
  convert spv_aux₂_coed hi t.2.1 ht,
  simp,
  rw frac_coe,
  congr' 1; {
    rw nat.cast_succ,
    rw nat.cast_succ,
    linarith
  }
end

/--
  The image of a dihomotopy F of the square `[j/(m+1), (j+1)/(m+1)] × [(i+1)/(n+2), (i+2)/(n+2)]`
  contains the image of the second part of F vertically (split at 1/(n+2)) of `[j/(m+1), (j+1)/(m+1)] × [i/(n+1), (i+1)/(n+1)]`.
-/
lemma spv_subsquare {x y : X} {γ₁ γ₂ : dipath x y} {F : dipath.dihomotopy γ₁ γ₂} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) :
  (split_dihomotopy.second_part_vertically_dihomotopy F (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos n)))).to_dihomotopy '' (unit_subsquare hi hj)
   ⊆ F '' (unit_subsquare (nat.succ_lt_succ hi) hj) :=
begin
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩,
  have : ((split_dihomotopy.second_part_vertically_dihomotopy F (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos n)))).to_dihomotopy) (t₀, t₁) = 
          (split_dihomotopy.second_part_vertically_dihomotopy F (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos n)))) (t₀, t₁) := rfl,
  rw this at ht,
  rw split_dihomotopy.spv_apply at ht,
  show ∃ a, a ∈ unit_subsquare _ hj ∧ F a = z,
  refine ⟨_, _, ht⟩,
  split,
  split,
  exact spv_aux₁ hi tI.1.1,
  exact spv_aux₂ hi tI.1.2,
  exact tI.2,
end

/--
  If F can be covered by `n × (m+1)` rectangles (m ≥ 1), then F.second_part_vertically_dihomotopy at T = 1/(m+1) is covered by `n × m` rectangles.
-/
lemma covered_partwise_second_part {x y : X} {γ₁ γ₂ : dipath x y} {F : dipath.dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : covered_partwise F.to_dihomotopy hX n.succ m) :
  covered_partwise (split_dihomotopy.second_part_vertically_dihomotopy F (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos n)))).to_dihomotopy hX n m :=
begin
  unfold covered_partwise at hF,
  unfold covered_partwise,
  intros i j hi hj,
  cases (hF i.succ j (nat.succ_lt_succ hi) hj) with h h,
  { left, exact subset_trans (spv_subsquare _ _) h },
  { right, exact subset_trans (spv_subsquare _ _) h },
end

/--
  The image of a dihomotopy F of the square `[0, 1/(m+2)] × [i/(n+1), (i+1)/(n+1)]`
  contains the image of the first part of F horizontally (split at 1/(m+2)) of `[0, 1] × [i/(n+1), (i+1)/(n+1)]`.
-/
lemma fph_subsquare {f g : D(I, X)} {F : dihomotopy f g} {n m i : ℕ} (hi : i < n.succ) :
  (split_dihomotopy.first_part_horizontally_dihomotopy F (frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le m.succ)))) '' (unit_subsquare hi zero_lt_one)
   ⊆ F '' (unit_subsquare hi (nat.succ_pos m.succ)) :=
begin
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩,
  rw split_dihomotopy.fph_apply at ht,
  show ∃ a, a ∈ unit_subsquare hi _ ∧ F a = z,
  refine ⟨_, _, ht⟩,
  split,
  exact tI.1,
  split,
  {
    rw frac_zero,
    unit_interval,
  },
  {
    exact unit_interval_mul_le _ _,
  }
end

/--
  If F can be covered by `(n+1) × 1` rectangles (n ≥ 1), then F.first_part_horizontally_dihomotopy at T = 1/(n+1) is covered by `1 × 1` rectangle.
-/
lemma covered_partwise_first_hpart {f g : D(I, X)} {F : dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : covered_partwise F hX n m.succ) :
  covered_partwise (split_dihomotopy.first_part_horizontally_dihomotopy F (frac_pos zero_lt_one (nat.succ_le_succ (nat.zero_le m.succ)))) hX n 0 :=
begin
  unfold covered_partwise at hF,
  unfold covered_partwise,
  intros i j hi hj,
  obtain ⟨rfl⟩ : j = 0 := by linarith,
  cases (hF i 0 hi (nat.succ_pos m.succ)) with h h,
  { left, exact subset_trans (fph_subsquare _) h },
  { right, exact subset_trans (fph_subsquare _) h },
end

/--
  The image of a dihomotopy F of the square `[(j+1)/(m+2), (j+2)/(m+2)] × [i/(n+1), (i+1)/(n+1)]`
  contains the image of the second part of F horizontally (split at 1/(m+2)) of `[j/(m+1), (j+1)/(m+1)] × [i/(n+1), (i+1)/(n+1)]`.
-/
lemma sph_subsquare {f g : D(I, X)} {F : dihomotopy f g} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) :
  (split_dihomotopy.second_part_horizontally_dihomotopy F (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos m)))) '' (unit_subsquare hi hj)
   ⊆ F '' (unit_subsquare hi (nat.succ_lt_succ hj)) :=
begin
  rintro z ⟨⟨t₀, t₁⟩, ⟨tI, ht⟩⟩,
  rw split_dihomotopy.sph_apply at ht,
  show ∃ a, a ∈ unit_subsquare hi _ ∧ F a = z,
  refine ⟨_, _, ht⟩,
  split,
  exact tI.1,
  split,
  exact spv_aux₁ hj tI.2.1,
  exact spv_aux₂ hj tI.2.2,
end

/--
  If F can be covered by `(n+1) × 1` rectangles (n ≥ 1), then F.second_part_horizontally_dihomotopy at T = 1/(n+1) is covered by `n × 1` rectangles.
-/
lemma covered_partwise_second_hpart {f g : D(I, X)} {F : dihomotopy f g} {hX : X₀ ∪ X₁ = univ} {n m : ℕ} (hF : covered_partwise F hX n m.succ) :
  covered_partwise (split_dihomotopy.second_part_horizontally_dihomotopy F (frac_lt_one zero_lt_one (nat.succ_lt_succ (nat.succ_pos m)))) hX n m :=
begin
  unfold covered_partwise at hF,
  unfold covered_partwise,
  intros i j hi hj,
  cases (hF i j.succ hi (nat.succ_lt_succ hj)) with h h,
  { left, exact subset_trans (sph_subsquare _ _) h },
  { right, exact subset_trans (sph_subsquare _ _) h },
end

end dihomotopy
end directed_map

namespace dipath
namespace dihomotopy

variables {X : dTop} {X₀ X₁ : set X}

lemma range_left_subset {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} (F : dihomotopy γ₁ γ₂) :
  range γ₁ ⊆ range F :=
begin
  rintros x ⟨t, ht⟩,
  use (0 , t),
  rw ← ht,
  exact F.map_zero_left' t,
end
  
lemma range_right_subset {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} (F : dihomotopy γ₁ γ₂) :
  range γ₂ ⊆ range F :=
begin
  rintros x ⟨t, ht⟩,
  use (1 , t),
  rw ← ht,
  exact F.map_one_left' t,
end

def covered {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} (F : dihomotopy γ₁ γ₂) (hX : X₀ ∪ X₁ = univ) : Prop := range F ⊆ X₀ ∨ range F ⊆ X₁

lemma covered_left_of_covered {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} {F : dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} (hF : covered F hX) : dipath.covered γ₁ hX :=
  or.elim hF (λ hF, or.inl (subset_trans (range_left_subset F) hF)) (λ hF, or.inr (subset_trans (range_left_subset F) hF))
  
lemma covered_right_of_covered {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} {F : dihomotopy γ₁ γ₂} {hX : X₀ ∪ X₁ = univ} (hF : covered F hX) : dipath.covered γ₂ hX :=
  or.elim hF (λ hF, or.inl (subset_trans (range_right_subset F) hF)) (λ hF, or.inr (subset_trans (range_right_subset F) hF))

/--
  Two paths are `m × n`-dihomotopic if there is a dihomotopy between them that can be covered by `m × n` rectangles.
-/
def dipath_dihomotopic_covered {x₀ x₁ : X} (γ₁ γ₂ : dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (n m : ℕ) : Prop :=
  ∃ (F : dihomotopy γ₁ γ₂), directed_map.dihomotopy.covered_partwise F.to_dihomotopy hX n m

/--
  If `γ₁` and `γ₂` are two paths connected by a path-dihomotopy `F` that is covered by `m × (n + 1)` rectangles,
  then `γ₁` and `F.eval (1/(n+1))` are `m × 0`-dihomotopic and `F.eval (1/(n+1))` and `γ₂` are `m × n`-dihomotopic.
-/
lemma dipath_dihomotopic_covered_split {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} {F : dihomotopy γ₁ γ₂} (hX : X₀ ∪ X₁ = univ) {n m : ℕ} (hF : directed_map.dihomotopy.covered_partwise F.to_dihomotopy hX n.succ m) :
  dipath_dihomotopic_covered γ₁ (F.eval (frac (nat.succ_pos n.succ) (nat.succ_le_succ (nat.zero_le n.succ)))) hX 0 m ∧
  dipath_dihomotopic_covered (F.eval (frac (nat.succ_pos n.succ) (nat.succ_le_succ (nat.zero_le n.succ)))) γ₂ hX n m :=
begin
  split,
  exact ⟨_, directed_map.dihomotopy.covered_partwise_first_part hF⟩,
  exact ⟨_, directed_map.dihomotopy.covered_partwise_second_part hF⟩,
end

lemma dipath_dihomotopic_covered_exists_of_pre_dihomotopic {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} (hX : X₀ ∪ X₁ = univ) (h : γ₁.pre_dihomotopic γ₂)
  (X₀_open : is_open X₀) (X₁_open : is_open X₁) :
  ∃ (n m : ℕ), dipath_dihomotopic_covered γ₁ γ₂ hX n m :=
begin
  rcases (directed_map.dihomotopy.covered_partwise_exists h.some.to_dihomotopy hX X₀_open X₁_open) with ⟨n, m, hnm⟩,
  exact ⟨n, m, h.some, hnm⟩,
end


end dihomotopy
end dipath

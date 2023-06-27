import cover_lemma
import dipath_subtype

/-
  This file contains the definition of a directed path being n-covered by two subspaces X₁ and X₂:
  It maps any subinterval [i/n, (i+1)/n] into either X₁ or X₂.
  We give this definition inductively.
  This file contains properties about dipaths and parts of dipaths being n-covered. 
-/

open set auxiliary
open_locale unit_interval

noncomputable theory

namespace dipath

variables {X : dTop} {x₀ x₁ : X}
variables {X₀ X₁ : set X}

def covered (γ : dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) : Prop :=
  (range γ ⊆ X₀) ∨ (range γ ⊆ X₁)

namespace covered

lemma covered_refl (x : X) (hX : X₀ ∪ X₁ = univ) : covered (dipath.refl x) hX :=
begin
  cases ((set.mem_union x X₀ X₁).mp (filter.mem_top.mpr hX x)) with hx₀ hx₁,
  left, exact disubtype.range_refl_subset_of_mem hx₀,
  right, exact disubtype.range_refl_subset_of_mem hx₁,
end

lemma covered_of_extended_image_subset (γ : dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (hγ : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁) :
  covered γ hX :=
begin
  rw (dipath.range_eq_image γ).symm at hγ,
  exact hγ
end

lemma covered_trans {x₀ x₁ x₂ : X} {γ₁: dipath x₀ x₁} {γ₂ : dipath x₁ x₂} {hX : X₀ ∪ X₁ = univ} (hγ : covered (γ₁.trans γ₂) hX):
  (covered γ₁ hX ∧ covered γ₂ hX) :=
begin
  unfold covered at *,
  rw dipath.trans_range _ _ at hγ,
  cases hγ,
  exact ⟨or.inl $ subset_trans (subset_union_left (range γ₁) (range γ₂)) hγ, or.inl $ subset_trans (subset_union_right (range γ₁) (range γ₂)) hγ⟩,
  exact ⟨or.inr $ subset_trans (subset_union_left (range γ₁) (range γ₂)) hγ, or.inr $ subset_trans (subset_union_right (range γ₁) (range γ₂)) hγ⟩,
end

lemma covered_subparam {x₀ x₁ : X} {γ : dipath x₀ x₁} {hX : X₀ ∪ X₁ = univ} (hγ : covered γ hX) (f : D(I, I)) :
  covered (γ.subparam f) hX :=
begin
  cases hγ,
  { exact or.inl (subset_trans (dipath.subparam_range γ f) hγ) },
  { exact or.inr (subset_trans (dipath.subparam_range γ f) hγ) }
end

lemma covered_reparam_iff {x₀ x₁ : X} (γ : dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
 covered γ hX ↔ covered (γ.reparam f hf₀ hf₁) hX :=
begin
  unfold covered,
  rw dipath.range_reparam _ _,
end

lemma covered_cast_iff {x₀ x₁ x₀' x₁' : X}  (γ : dipath x₀ x₁) (hX : X₀ ∪ X₁ = univ) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) :
  covered γ hX ↔ covered (γ.cast hx₀ hx₁) hX := by refl

/--
 If γ is a dipath that is covered, then by splitting it into two parts [0, T] and [T, 1], both parts remain covered
-/
lemma covered_split_path {γ : dipath x₀ x₁} {hX : X₀ ∪ X₁ = set.univ} {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) (hγ : covered γ hX ):
  covered (split_dipath.first_part_dipath γ hT₀) hX ∧ covered (split_dipath.second_part_dipath γ hT₁) hX :=
begin
  apply covered_trans,
  apply (covered_reparam_iff _ hX (split_dipath.trans_reparam_map hT₀ hT₁) (split_dipath.trans_reparam_map_zero _ _) (split_dipath.trans_reparam_map_one _ _)).mpr,
  rw split_dipath.first_trans_second_reparam_eq_self γ hT₀ hT₁ at hγ,
  exact hγ,
end

end covered

open covered

/--
 We say that `covered_partwise hX γ n` if a dipath γ can be split into n+1 parts, each of which is covered by `X₁` or `X₂` 
-/
def covered_partwise (hX : X₀ ∪ X₁ = set.univ) : Π {x y : X}, dipath x y → ℕ → Prop
| x y γ 0 := covered γ hX
| x y γ (nat.succ n) :=
      covered (split_dipath.first_part_dipath γ (inv_I_pos (show 0 < (n.succ + 1), by norm_num))) hX ∧
      covered_partwise (split_dipath.second_part_dipath γ (inv_I_lt_one (show 1 < (n.succ + 1), by norm_num))) n

namespace covered_partwise

lemma covered_partwise_of_equal_params (hX : X₀ ∪ X₁ = set.univ) {x₀ x₁ : X} {γ₁ γ₂ : dipath x₀ x₁} {n m : ℕ} (h : γ₁ = γ₂) (h' : n = m) (hγ₁ : covered_partwise hX γ₁ n) :
  covered_partwise hX γ₂ m := by { subst_vars, exact hγ₁ }

/--
 If γ is a dipath that is fully covered, then it is also partwise covered for all n ∈ ℕ
-/
lemma covered_partwise_of_covered {hX : X₀ ∪ X₁ = set.univ} (n : ℕ) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁}, covered γ hX → covered_partwise hX γ n :=
begin
  induction n with n hn,
  { -- Case n = 0
    intros x₀ x₁ γ hγ,
    exact hγ,
  },
  { -- Case n > 0
    intros x₀ x₁ γ hγ,
    split,
    exact (covered_split_path _ (inv_I_lt_one (by norm_num)) hγ).left,
    apply hn,
    exact (covered_split_path (inv_I_pos _) _ hγ).right,
  }
end

lemma covered_partwise_cast_iff  (hX : X₀ ∪ X₁ = univ) {n : ℕ} :
  Π {x₀ x₁ x₀' x₁' : X}  (γ : dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁),
  covered_partwise hX γ n ↔ covered_partwise hX (γ.cast hx₀ hx₁) n :=
begin
  induction n with n ih,
  {
    intros x₀ x₁ x₀' x₁' γ hx₀ hx₁,
    apply covered_cast_iff,
  },
  intros x₀ x₁ x₀' x₁' γ hx₀ hx₁,
  unfold covered_partwise,
  rw split_properties.first_part_cast,
  rw split_properties.second_part_cast,
  split,
  {
    rintros ⟨hγ₁, hγ₂⟩,
    split,
    exact (covered_cast_iff _ _ _ _).mp hγ₁,
    exact (ih _ _ _).mp hγ₂,
  },
  {
    rintros ⟨hγ₁, hγ₂⟩,
    split,
    exact (covered_cast_iff _ _ _ _).mpr hγ₁,
    exact (ih _ _ _).mpr hγ₂,
  }
end

/--
 A dipath γ that can be covered with n+1 intervals can satisfied `covered_partwise _ γ n`
-/
lemma covered_partwise_of_covered_by_intervals {hX : X₀ ∪ X₁ = set.univ} (n : ℕ) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁}, (∀ (i : ℕ) (h : i < (n+1)),
    γ.extend '' set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₀ ∨
    γ.extend '' set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₁) → covered_partwise hX γ n :=
begin
  induction n with n hn,
  { -- Case n = 0
    intros x₀ x₁ γ hγ,
    have := hγ 0 (by linarith),
    unfold covered_partwise covered,
    rw dipath.range_eq_image,
    convert this; simp,
  },
  { -- Case n > 0
    intros x₀ x₁ γ hγ,
    split,
    {
      unfold covered,
      rw (split_properties.first_part_range_interval γ _),
      rw ← dipath.image_extend_eq_image,
      convert hγ 0 (by norm_num); norm_num,
    },
    apply hn,
    intros i hi,
    have : i + 1 < n + 2 := by linarith,
    have h := hγ (i+1) (this),
    suffices :
      (split_dipath.second_part_dipath γ _).extend '' set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₀ ∨
      (split_dipath.second_part_dipath γ _).extend '' set.Icc (↑i/(↑(n+1))) ((↑i+1)/(↑(n+1))) ⊆ X₁,
    {
      convert this; exact (nat.cast_succ n).symm,
    },
    rw (split_properties.second_part_range_interval_coe γ _ _),
    convert h; exact (nat.cast_succ i).symm,
    exact hi,
    exact nat.succ_pos n,
  }
end

/--
 A dipath γ that satisfies `covered_partwise _ γ n` can be covered with n+1 intervals 
-/
lemma covered_by_intervals_of_covered_partwise {hX : X₀ ∪ X₁ = set.univ} (n : ℕ) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁}, covered_partwise hX γ n → (∀ (i : ℕ) (h : i < (n+1)),
    γ.extend '' set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₀ ∨
    γ.extend '' set.Icc ((↑i)/(↑n+1)) ((↑i+1)/(↑n+1)) ⊆ X₁) :=
begin
  induction n with n hn,
  { -- Case n = 0
    intros x₀ x₁ γ hγ i hi,
    rw (show i = 0, by linarith),
    suffices : γ.extend '' I ⊆ X₀ ∨ γ.extend '' I ⊆ X₁,
    {
      convert this; simp,
    },
    rw ← dipath.range_eq_image γ,
    exact hγ,
  },
  { -- Case n > 0
    intros x₀ x₁ γ hγ i hi,
    by_cases h_i_eq_0 : i = 0,
    { -- Use the fact that the first part of γ is covered
      have hγ_first_cov := hγ.left,
      rw h_i_eq_0,
      have := split_properties.first_part_range_interval_coe γ (show 0 < n+2, by linarith),
      unfold covered at hγ_first_cov,
      rw this at hγ_first_cov,
      convert hγ_first_cov; simp,
      ring,
      ring,
    },
    suffices : γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₀ ∨
              γ.extend '' Icc ((↑(i-1) + 1)/(↑(n.succ) + 1)) ((↑(i-1) + 1 + 1)/(↑(n.succ) + 1)) ⊆ X₁,
    {
      convert this; { 
        have : 1 ≤ i := nat.pos_of_ne_zero h_i_eq_0,
        rw nat.cast_sub (this),
        simp,
      }
    },
    have : i - 1 < n.succ := nat.lt_of_succ_lt_succ ((nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero h_i_eq_0)).symm ▸ hi),
    rw ← split_properties.second_part_range_interval_coe γ (this) (by linarith),
    convert hn hγ.right (i-1) (this);  {
      exact (nat.cast_succ n)
    }
  }
end

/--
  Let γ be a dipath covered by n+1 parts. Let 0 < k < n+1 be given. Then the first part
  of γ, split by k/(n+1) is covered by k parts.
  Here, k = d.succ, so we don't need the requirement k > 0.
-/
lemma covered_partwise_first_part_d (hX : X₀ ∪ X₁ = set.univ)
  {n d : ℕ} (hd_n : d.succ < n.succ) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁} (hγ : covered_partwise hX γ n),
  covered_partwise hX (split_dipath.first_part_dipath γ $ frac_pos (nat.succ_pos d) (le_of_lt hd_n)) d :=
begin
  intros x y γ hγ,
  apply covered_partwise_of_covered_by_intervals,
  intros i hi,
  rw split_properties.first_part_range_interval_partial_coe γ hd_n hi,
  exact covered_by_intervals_of_covered_partwise n hγ i (lt_trans hi hd_n),
end

/--
  Input: (d+1) < (n+1) --> split at (d+1)/(n+1)
  Let γ be a dipath covered by n+1 parts. Let 0 < k < n+1 be given. Then the second part
  of γ, split by k/(n+1) is covered by n+1-k parts.
  Here, k = d.succ, so we don't need the requirement k > 0.
-/
lemma covered_partwise_second_part_d (hX : X₀ ∪ X₁ = set.univ)
  {n d : ℕ} (hd_n : d.succ < n.succ) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁} (hγ : covered_partwise hX γ n),
  covered_partwise hX (split_dipath.second_part_dipath γ $ frac_lt_one (nat.succ_pos d) (hd_n)) (n - d.succ) :=
begin
  intros x y γ hγ,
  apply covered_partwise_of_covered_by_intervals,
  intros i hi,
  rw ← nat.cast_succ,
  have hi_lt_n_sub_d : i < n - d,
  {
    convert hi,
    rw nat.sub_succ,
    exact (nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt (nat.lt_of_succ_lt_succ hd_n))).symm,
  },
  have : i + d.succ < n + 1,
  {
    rw nat.add_succ,
    apply nat.succ_lt_succ,
    exact lt_tsub_iff_right.mp hi_lt_n_sub_d,
  },
  have := covered_by_intervals_of_covered_partwise n hγ (i + d.succ) this,
  rw ← split_properties.second_part_range_partial_interval_coe γ hd_n hi_lt_n_sub_d at this,
  convert this;
  {
    have : (n-d.succ).succ = n - d,
    {
      rw nat.sub_succ,
      exact nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt (nat.lt_of_succ_lt_succ hd_n))
    },
    rw this,
    exact nat.cast_sub (le_of_lt $ nat.lt_of_succ_lt_succ hd_n),
  }
end

/--
  Let γ be a dipath covered by n+2 parts. Then the first part of γ, split by (n+1)/(n+2) is covered by n+1 parts.
-/
lemma covered_partwise_first_part_end_split (hX : X₀ ∪ X₁ = set.univ) {n : ℕ} {x₀ x₁ : X} {γ : dipath x₀ x₁} (hγ : covered_partwise hX γ n.succ) :
  covered_partwise hX (split_dipath.first_part_dipath γ $ frac_pos (nat.succ_pos n) (le_of_lt (nat.lt_succ_self n.succ))) n := covered_partwise_first_part_d hX _ hγ

/--
  Let γ be a dipath covered by n+2 parts. Then the second part of γ, split by (n+1)/(n+2) is covered
-/
lemma covered_second_part_end_split (hX : X₀ ∪ X₁ = set.univ) {n : ℕ} {x₀ x₁ : X} {γ : dipath x₀ x₁} (hγ : covered_partwise hX γ n.succ) :
  covered (split_dipath.second_part_dipath γ $ frac_lt_one (nat.succ_pos n) (nat.lt_succ_self n.succ)) hX :=
begin
  have := covered_partwise_second_part_d hX (nat.lt_succ_self n.succ) hγ,
  rw (nat.sub_self n.succ) at this,
  exact this,
end

/--
  Let γ be a dipath and n ≥ 2:
  If the first part [0, 1/(n+1)] can be covered with k intervals and the second part [1/(n+1), 1] can be covered with k*n intervals,
  then the entire path can be covered with k*(n+1) intervals.
-/
lemma covered_partwise_of_parts (hX : X₀ ∪ X₁ = set.univ) {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k > 0) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁},
    ((covered_partwise hX (split_dipath.first_part_dipath γ (inv_I_pos (show 0 < n.succ, by exact nat.succ_pos n))) (k - 1)) ∧
    (covered_partwise hX (split_dipath.second_part_dipath γ (inv_I_lt_one (show 1 < n.succ, by exact nat.succ_lt_succ hn))) (n * k - 1))) →
    (covered_partwise hX γ ((n + 1) * k - 1)) :=
begin
  rintros x₀ x₁ γ ⟨hγ_first, hγ_second⟩,
  apply covered_partwise_of_covered_by_intervals,
  intros i hi,
  have prod_pos : (n + 1) * k > 0 := mul_pos (nat.succ_pos n) hk,
  set d' := k - 1 with d_def,
  set n' := (n + 1) * k - 1 with n_def,
  have hd_eq_k : d'.succ = k,
  {
    rw d_def,
    rw ← nat.pred_eq_sub_one k,
    rw nat.succ_pred_eq_of_pos hk,
  },
  have h₁ : d'.succ < n'.succ,
  {
    rw n_def,
    rw hd_eq_k,
    rw ← nat.pred_eq_sub_one ((n + 1) * k),
    rw nat.succ_pred_eq_of_pos prod_pos,
    nth_rewrite 0 ← one_mul k,
    exact (mul_lt_mul_right hk).mpr (by linarith),
  },
  have : frac (nat.succ_pos n') (le_of_lt h₁) = inv_I (nat.succ_pos n),
  {
    simp [d_def, n_def],
    rw ← nat.cast_succ,
    rw ← nat.cast_succ,
    rw ← nat.pred_eq_sub_one k,
    rw nat.succ_pred_eq_of_pos hk,
    rw ← nat.pred_eq_sub_one ((n + 1) * k),
    rw nat.succ_pred_eq_of_pos prod_pos,
    rw mul_comm,
    rw nat.cast_mul,
    have : (k : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt hk),
    rw ← div_div,
    rw div_self this,
    rw nat.cast_succ,
    exact one_div _,
  },
  have h₃ : (n' : ℝ) - (d' : ℝ) = (↑(n * k - 1) : ℝ) + 1,
  {
    rw ← nat.cast_sub (le_of_lt $ nat.lt_of_succ_lt_succ h₁),
    rw ← nat.cast_succ,
    rw ← nat.pred_eq_sub_one (n * k),
    rw nat.succ_pred_eq_of_pos (nat.mul_pos hn hk),
    rw [n_def, d_def],
    rw nat.sub_sub,
    rw add_comm 1 (k-1),
    rw nat.add_one (k-1),
    rw nat.sub_one k,
    rw nat.succ_pred_eq_of_pos hk,
    rw add_mul,
    rw one_mul,
    rw nat.add_sub_assoc (le_refl k),
    rw nat.sub_self,
    refl,
  },
  by_cases h : i < k,
  { -- Use the covering of the first part of γ
    have h₂ : i < d'.succ,
    {
      rw [d_def, ←nat.pred_eq_sub_one k],
      rw nat.succ_pred_eq_of_pos hk,
      exact h,
    },
    rw ← split_properties.first_part_range_interval_partial_coe γ h₁ h₂,
    convert (covered_by_intervals_of_covered_partwise (k-1) hγ_first i (by linarith)),
  },
  {
    push_neg at h,
    set i' := i - d'.succ with i_def,
    have h₂ : i' < n' - d',
    {
      rw i_def,
      rw ← nat.succ_sub_succ n' d',
      have : d'.succ ≤ i := hd_eq_k.symm ▸ h,
      apply (tsub_lt_tsub_iff_right this).mpr _,
      convert hi,
    },
    have : i = i' + d'.succ,
    {
      rw i_def,
      rw nat.sub_add_cancel,
      exact hd_eq_k.symm ▸ h,
    },
    rw this,
    have : i - k < n * k - 1 + 1,
    {
      rw nat.sub_one (n * k),
      rw nat.add_one (n * k).pred,
      rw nat.succ_pred_eq_of_pos (mul_pos hn hk),
      apply (tsub_lt_iff_right h).mpr _,
      nth_rewrite 0 ← one_mul k,
      rw ← add_mul,
      rw ← nat.succ_pred_eq_of_pos prod_pos, 
      convert hi,
    },
    rw ← split_properties.second_part_range_partial_interval_coe γ h₁ h₂,
    convert (covered_by_intervals_of_covered_partwise (n * k - 1) hγ_second (i - k) this);
    {
      exact (hd_eq_k ▸ i_def) <|> exact h₃
    }
  }
end

/--
  If a dipath γ can be covered in n+1 parts, it can also be covered in (k+1) * (n+1) parts
-/
lemma covered_partwise_refine (hX : X₀ ∪ X₁ = set.univ) (n k : ℕ) :
  Π {x₀ x₁ : X} {γ : dipath x₀ x₁}, covered_partwise hX γ n → covered_partwise hX  γ ((n + 1) * (k + 1) - 1) :=
begin
  induction n with n hn,
  { -- Case n = 0
    intros x₀ x₁ γ hγ,
    exact covered_partwise_of_covered ((0+1)*(k+1)-1) hγ,
  },
  -- Case n > 0
  rintros x₀ x₁ γ ⟨hγ_cov_first, hγ_split_cov_second⟩,
  have : 0 < n.succ := nat.succ_pos n,
  apply covered_partwise_of_parts hX this (nat.succ_pos k),
  split,
  {
    exact covered_partwise_of_covered k hγ_cov_first,
  },
  {
    convert (hn hγ_split_cov_second),
  }
end

lemma covered_partwise_trans  {hX : X₀ ∪ X₁ = set.univ} {n : ℕ} {x₀ x₁ x₂ : X} {γ₁ : dipath x₀ x₁} {γ₂ : dipath x₁ x₂}
  (hγ₁ : covered_partwise hX γ₁ n) (hγ₂ : covered_partwise hX γ₂ n) :
  covered_partwise hX (γ₁.trans γ₂) (n + n).succ :=
begin
  apply covered_partwise_of_covered_by_intervals,
  intros i hi,
  have h_lt : n.succ < (n + n).succ.succ,
  {
    apply nat.succ_lt_succ,
    rw ← nat.add_succ,
    apply lt_add_of_pos_right,
    exact nat.succ_pos n,
  },
  have h₁ : frac (nat.succ_pos (n + n).succ) (le_of_lt h_lt) = frac (two_pos) (le_of_lt one_lt_two),
  {
    simp,
    rw ← one_div,
    apply (div_eq_div_iff _ _).mpr,
    ring,
    have : (n : ℝ) ≥ 0 := nat.cast_nonneg n,
    linarith,
    linarith,
  },
  by_cases h : i < n.succ,
  {
    rw ← split_properties.first_part_range_interval_partial_coe (γ₁.trans γ₂) h_lt h,
    rw split_properties.first_part_eq_of_split_point_eq (γ₁.trans γ₂) h₁ _ (frac_pos one_pos (le_of_lt one_lt_two)),
    rw split_properties.first_part_trans γ₁ γ₂,
    rw dipath.cast_image,
    rw dipath.cast_image,
    exact covered_by_intervals_of_covered_partwise n hγ₁ i h,
  },
  {
    set k := i - n.succ with k_def,
    push_neg at h,
    have : i = k + n.succ,
    {
      rw k_def,
      rw nat.sub_add_cancel,
      exact h,
    },
    rw this,
    have hn : (n + n).succ - n = n.succ,
    {
      rw nat.succ_sub,
      rw nat.add_sub_cancel,
      exact nat.le_add_right n n,
    },
    have hn' : (↑(n + n).succ : ℝ) - ↑n = ↑n + 1,
    {
      rw ← nat.cast_succ n,
      rw ← hn,
      rw nat.cast_sub,
      exact le_of_lt (nat.lt_of_succ_lt_succ h_lt),
    },
    have : i < n.succ + n.succ,
    {
      rw nat.succ_add,
      rw nat.add_succ,
      exact hi,
    },
    have hk : k < n.succ,
    {
      rw k_def,
      exact (tsub_lt_iff_left h).mpr this,
    },
    have hk' : k < (n + n).succ - n := hn.symm ▸ hk,
    rw ← split_properties.second_part_range_partial_interval_coe (γ₁.trans γ₂) h_lt hk',
    rw split_properties.second_part_eq_of_split_point_eq (γ₁.trans γ₂) h₁ _ (frac_lt_one one_pos one_lt_two),
    rw split_properties.second_part_trans γ₁ γ₂,
    rw dipath.cast_image,
    rw dipath.cast_image,
    rw hn',
    exact covered_by_intervals_of_covered_partwise n hγ₂ k hk,
  }
end

lemma has_interval_division {X₁ X₂ : set X} (hX : X₁ ∪ X₂ = set.univ) (X₁_open : is_open X₁) (X₂_open : is_open X₂) (γ : dipath x₀ x₁) :
  ∃ (n > 0), ∀ (i : ℕ) (h : i < n),
    set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) ⊆ γ.extend ⁻¹' X₁ ∨
    set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) ⊆ γ.extend ⁻¹' X₂ :=
begin
  -- set ι : list ℕ := [1, 2],
  set c : ℕ → set ℝ := λ i, if i = 0 then γ.extend ⁻¹' X₁ else γ.extend ⁻¹'  X₂ with c_def,
  have h₁ : ∀ i, is_open (c i),
  {
    intro i,
    rw c_def,
    by_cases i = 0; simp [h],
    exact (path.continuous_extend γ.to_path).is_open_preimage X₁ X₁_open,
    exact (path.continuous_extend γ.to_path).is_open_preimage X₂ X₂_open,
  },
  have h₂ : I ⊆ ⋃ (i : ℕ), c i,
  {
    intros x hx,
    simp [c_def],
    have : γ.extend x ∈ X₁ ∪ X₂ := hX.symm ▸ (set.mem_univ $ γ.extend x),
    cases this with h h,
    { use 0, simp, exact h },
    { use 1, simp, exact h }
  },
  rcases (lebesgue_number_lemma_unit_interval h₁ h₂) with ⟨n, n_pos, hn⟩,
  use n,
  split,
  { exact n_pos },
  intros i hi,
  cases (hn i hi) with j hj,
  rw c_def at hj,
  simp at hj,
  by_cases j = 0,
  { left, convert hj, simp [h] },
  { right, convert hj, simp [h] },
end

/--
  If `γ` is a dipath and a directed space `X` is covered by two opens `X₁` and `X₂`, then `γ` is n-covered for some `n`.
-/
lemma has_subpaths {X₁ X₂ : set X} (hX : X₁ ∪ X₂ = set.univ) (X₁_open : is_open X₁) (X₂_open : is_open X₂) (γ : dipath x₀ x₁) :
  ∃ (n : ℕ), covered_partwise hX γ n :=
begin
  have := has_interval_division hX X₁_open X₂_open γ,
  rcases this with ⟨n, n_pos, hn⟩,
  use (n-1),
  apply covered_partwise_of_covered_by_intervals,
  simp,
  intros i hi,
  have := hn i (by linarith),
  convert this;
  {
    have : n - 1 + 1 = n := nat.succ_pred_eq_of_pos n_pos,
    nth_rewrite 1 ←this,
    simp,
  }
end

end covered_partwise
end dipath
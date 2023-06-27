import interpolate

/-
  This file contains lemmas about splitting a (di)path into two parts,
  and how their concatenation relates to the original (di)path
-/

open auxiliary
open_locale unit_interval

noncomputable theory

universe u


variables {X : Type u} [directed_space X] {x₀ x₁ : X}

namespace split_path

/-- The part of a path on the interval [0, T] -/
def first_part (γ : path x₀ x₁) (T : I) : path x₀ (γ T) :=
{
  to_fun := λ t, γ ⟨(T : ℝ) * ↑t, unit_interval.mul_mem T.2 t.2⟩,
  source' := by simp [γ.source'],
  target' := by simp,
}

/-- The part of a path on the interval [T, 1] -/
def second_part (γ : path x₀ x₁) (T : I) : path (γ T) x₁ :=
{
  to_fun := λ t, γ ⟨(σ T : ℝ) * ↑t + ↑T, interp_left_mem_I T t⟩,
  source' := by simp,
  target' := by simp [γ.target'],
}

/--
  The map needed to reparametrize the concatenation of the first and second part of a path
  back into the original pat
-/
def trans_reparam (T t : I) : ℝ :=
if (t : ℝ) ≤ (T : ℝ) then
  t / (2 * T)
else
  (1 + t - 2*T) / (2 * (1-T))

@[continuity]
lemma continuous_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : continuous (trans_reparam T) :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _;
  [continuity, continuity, continuity, continuity, skip],
  intros x hx,
  apply (div_eq_div_iff (ne_of_gt (double_pos_of_pos hT₀)) (ne_of_gt (double_sigma_pos_of_lt_one hT₁))).mpr,
  simp [hx],
  ring,
end

lemma trans_reparam_mem_I (t : I) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1): trans_reparam T t ∈ I :=
begin
  unfold trans_reparam,
  split,
  {
    split_ifs,
    { exact div_nonneg t.2.1 (le_of_lt (double_pos_of_pos hT₀)) },
    { exact div_nonneg (by linarith [double_sigma_pos_of_lt_one hT₁]) (le_of_lt (double_sigma_pos_of_lt_one hT₁)) },
  },
  split_ifs,
  { exact (div_le_one (double_pos_of_pos hT₀)).mpr (by linarith [double_pos_of_pos hT₀]) },
  { exact (div_le_one (double_sigma_pos_of_lt_one hT₁)).mpr (by linarith [unit_interval.le_one t]) },
end

lemma trans_reparam_zero (T : I) : trans_reparam T 0 = 0 :=
begin
  unfold trans_reparam,
  simp,
  intro hT,
  linarith [unit_interval.nonneg T],
end

lemma trans_reparam_one {T : I} (hT₁ : T < 1): trans_reparam T 1 = 1 :=
begin
  unfold trans_reparam,
  simp [show  ¬(1 ≤ (T : ℝ)), by exact not_le.mpr hT₁],
  convert div_self (ne_of_gt (double_sigma_pos_of_lt_one hT₁)),
  ring,
end

lemma monotone_trans_reparam {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : monotone (trans_reparam T) :=
begin
  intros x y hxy,
  unfold trans_reparam,
  split_ifs with h₁ h₂,
  { exact (div_le_div_right (double_pos_of_pos hT₀)).mpr hxy },
  {
    apply (div_le_div_iff (double_pos_of_pos hT₀) (double_sigma_pos_of_lt_one hT₁)).mpr,
    have : 0 ≤ (T : ℝ) * (↑y - ↑T) := mul_nonneg T.2.1 (by linarith),
    calc (x : ℝ) * (2 * (1 - ↑T)) ≤  ↑T * (2 * (1 - ↑T))                    : (mul_le_mul_right (double_sigma_pos_of_lt_one hT₁)).mpr h₁
                            ...   ≤  ↑T * (2 * (1 - ↑T)) + ↑T * (↑y - ↑T)   : le_add_of_nonneg_right (mul_nonneg T.2.1 (by linarith))
                            ...   ≤ (1 + ↑y - 2 * ↑T)  * (2 * ↑T)           : by linarith
  },
  { linarith [subtype.coe_le_coe.mpr hxy] },
  {
    apply (div_le_div_right (double_sigma_pos_of_lt_one hT₁)).mpr,
    linarith [subtype.coe_le_coe.mpr hxy],
  },
end

lemma first_trans_second_reparam_eq_self_aux (γ : path x₀ x₁) (t : I) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  γ t = ((first_part γ T).trans (second_part γ T)).reparam
  (λ t, ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
  (by continuity)
  (subtype.ext $ trans_reparam_zero T) (subtype.ext $ trans_reparam_one hT₁) t :=
begin
  have hT_ne_zero : (T : ℝ) ≠ 0 := (lt_iff_le_and_ne.mp (subtype.coe_lt_coe.mpr hT₀)).2.symm,
  rw path.reparam,
  simp [path.trans_apply, first_part, second_part, trans_reparam],
  split_ifs with h₁,
  {
    simp [h₁],
    split_ifs with h₂,
    {
      congr,
      apply subtype.coe_inj.mp,
      simp,
      calc (t : ℝ) = ↑t * 1 : (mul_one ↑t).symm
          ... = ↑t * ((2 * ↑T) / (2 * ↑T)) : by rw (div_self (mul_ne_zero two_ne_zero hT_ne_zero))
          ... = ↑T * (2 * (↑t / (2 * ↑T))) : by ring
    },
    {
      exfalso,
      have hT_lt_t : ↑T < ↑t,
      {
        simp at h₂,
        calc (T : ℝ) = 1 * ↑T                     : (one_mul ↑T).symm
               ...   = (2⁻¹ * 2) * ↑T             : by norm_num
               ...   = 2⁻¹ * (2 * ↑T)             : by ring
               ...   < (↑t / (2 * ↑T)) * (2 * ↑T) : (mul_lt_mul_right $ double_pos_of_pos hT₀).mpr h₂
               ...   = ↑t * ((2 * ↑T) / (2 * ↑T)) : by ring
               ...   = ↑t * 1                     : by rw (div_self (mul_ne_zero two_ne_zero hT_ne_zero))
               ...   = ↑t                         : (mul_one ↑t)
      },
      exact not_le_of_lt (subtype.coe_lt_coe.mp hT_lt_t) h₁,
    },
  },
  
  simp [h₁],
  push_neg at h₁,
  have : (t : ℝ) > (T : ℝ) := h₁,
  split_ifs with h₂,
  {
    exfalso,
    have : (1 + (t : ℝ) - 2 * ↑T) ≤ (1 - ↑T),
    {
      rw div_le_iff (double_sigma_pos_of_lt_one hT₁) at h₂,
      convert h₂,
      ring,
    },
    linarith,
  },
  {
    congr,
    apply subtype.coe_inj.mp,
    simp,
    calc (t : ℝ) = (1 + ↑t - 2 * ↑T) - 1 + 2 * ↑T : by ring
            ... = (1 + ↑t - 2 * ↑T) * (2 * (1 - ↑T)) / (2 * (1 - ↑T)) - 1 + 2 * ↑T : by simp [mul_div_cancel (1 + ↑t - 2 * ↑T) (ne_of_gt (double_sigma_pos_of_lt_one hT₁))]
            ... = (1 - ↑T) * (2 * ((1 + ↑t - 2 * ↑T) / (2 * (1 - ↑T))) - 1) + ↑T : by ring,
  }
end

lemma first_trans_second_reparam_eq_self (γ : path x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
γ = ((first_part γ T).trans (second_part γ T)).reparam
  (λ t, ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩)
  (by continuity)
  (subtype.ext $ trans_reparam_zero T) (subtype.ext $ trans_reparam_one hT₁) := 
begin
  ext t,
  exact first_trans_second_reparam_eq_self_aux γ t hT₀ hT₁,
end

end split_path

namespace split_dipath

open split_path

lemma first_part_is_dipath {γ : path x₀ x₁} (γ_dipath : is_dipath γ) {T : I} (hT₀ : 0 < T) : is_dipath (first_part γ T) :=
begin
  let φ : path 0 T := {
    to_fun := λ t, ⟨(T : ℝ) * (t : ℝ), unit_interval.mul_mem T.2 t.2⟩,
    source' := by simp,
    target' := by simp,
  },

  have : first_part γ T = (φ.map γ.continuous_to_fun).cast γ.source.symm rfl := by { ext, refl },
  rw this,

  apply is_dipath_cast _ γ.source.symm rfl,
  exact is_dipath_reparam φ (λ x y hxy, (mul_le_mul_left (subtype.coe_lt_coe.mpr hT₀)).mpr hxy) γ_dipath,
end


lemma second_part_is_dipath {γ : path x₀ x₁} (γ_dipath : is_dipath γ) {T : I} (hT₁ : T < 1) : is_dipath (second_part γ T) :=
begin
  let φ : path T 1 := {
    to_fun := λ t, ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩,
    source' := by simp,
    target' := by simp,
  },

  have : second_part γ T = ((φ.map γ.continuous_to_fun).cast rfl γ.target.symm) := by { ext, refl },
  rw this,
  
  apply is_dipath_cast _ rfl γ.target.symm,
  refine is_dipath_reparam φ _ γ_dipath,
  intros x y hxy,
  simp,
  exact (mul_le_mul_left (sub_pos.mpr (subtype.coe_lt_coe.mpr hT₁))).mpr hxy,
end

def first_part_dipath (γ : dipath x₀ x₁) {T : I} (hT₀ : 0 < T) : dipath x₀ (γ T) :=
{
  to_path := first_part γ T,
  dipath_to_path := first_part_is_dipath γ.dipath_to_path hT₀,
} 

def second_part_dipath (γ : dipath x₀ x₁) {T : I} (hT₁ : T < 1) : dipath (γ T) x₁ :=
{
  to_path := second_part γ T,
  dipath_to_path := second_part_is_dipath γ.dipath_to_path hT₁,
}

lemma first_part_apply (γ : dipath x₀ x₁) {T : I} (hT₀ : 0 < T) (t : I) : (first_part_dipath γ hT₀) t = γ ⟨ T* t, unit_interval.mul_mem T.2 t.2⟩ := rfl
lemma second_part_apply (γ : dipath x₀ x₁) {T : I} (hT₁ : T < 1) (t : I) : (second_part_dipath γ hT₁) t = γ ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩ := rfl

def trans_reparam_map {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : D(I, I) :=
{  
  to_fun := λ t, ⟨trans_reparam T t, trans_reparam_mem_I t hT₀ hT₁⟩,
  directed_to_fun := directed_unit_interval.directed_of_monotone _ (monotone_trans_reparam hT₀ hT₁)
}

lemma trans_reparam_map_zero {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : trans_reparam_map hT₀ hT₁ 0 = 0 := subtype.ext (trans_reparam_zero T)
lemma trans_reparam_map_one {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : trans_reparam_map hT₀ hT₁ 1 = 1 := subtype.ext (trans_reparam_one hT₁)

lemma first_trans_second_reparam_eq_self (γ : dipath x₀ x₁) {T: I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  γ = ((first_part_dipath γ hT₀).trans (second_part_dipath γ hT₁)).reparam (trans_reparam_map hT₀ hT₁) (trans_reparam_map_zero _ _) (trans_reparam_map_one _ _) := 
begin
  ext t,
  exact first_trans_second_reparam_eq_self_aux γ t hT₀ hT₁,
end

end split_dipath


namespace split_properties

open split_dipath set

/-! ### General -/

lemma first_part_cast {x₀' x₁' : X} (γ : dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) {T : I} (hT₀ : T > 0) :
  (first_part_dipath (γ.cast hx₀ hx₁) hT₀) = (first_part_dipath γ hT₀).cast hx₀ rfl := rfl
  
lemma second_part_cast {x₀' x₁' : X} (γ : dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) {T : I} (hT₁ : T < 1) :
  (second_part_dipath (γ.cast hx₀ hx₁) hT₁) = (second_part_dipath γ hT₁).cast rfl hx₁ := rfl

lemma first_part_eq_of_split_point_eq (γ : dipath x₀ x₁) {T T' : I} (hT : T = T') (hT₀ : T > 0) (hT'₀ : T' > 0) :
  (first_part_dipath γ hT₀) = (first_part_dipath γ hT'₀).cast rfl (congr_arg γ hT) := by { subst_vars, refl }

lemma second_part_eq_of_split_point_eq (γ : dipath x₀ x₁) {T T' : I} (hT : T = T') (hT₁ : T < 1) (hT'₁ : T' < 1) :
  (second_part_dipath γ hT₁) = (second_part_dipath γ hT'₁).cast (congr_arg γ hT) rfl := by { subst_vars, refl }

lemma first_part_eq_of_point_eq (γ : dipath x₀ x₁) {T T': I} (h : T = T') (hT : 0 < T) (t : I) :
  (first_part_dipath γ hT) t = (first_part_dipath γ (show 0 < T', by exact (h ▸ hT))) t := by subst_vars

lemma second_part_eq_of_point_eq (γ : dipath x₀ x₁) {T T': I} (h : T = T') (hT : T < 1) (t : I) :
  (second_part_dipath γ hT) t = (second_part_dipath γ (show T' < 1, by exact (h ▸ hT))) t := by subst_vars


/-! ### First Part -/

lemma first_part_image (γ : dipath x₀ x₁) {T : I} (hT : 0 < T) (a b : I) :
  (first_part_dipath γ hT) '' Icc a b = γ '' Icc (T * a) (T * b) :=
begin
  ext z,
  split,
  {
    rintro ⟨t, t_a_b, ht⟩,
    rw first_part_apply at ht,
    use T * t,
    exact ⟨⟨subtype.coe_le_coe.mpr ((mul_le_mul_left (subtype.coe_lt_coe.mpr hT)).mpr t_a_b.1), subtype.coe_le_coe.mpr ((mul_le_mul_left (subtype.coe_lt_coe.mpr hT)).mpr t_a_b.2)⟩, ht⟩,
  },
  {
    rintro ⟨t, t_Ta_Tb, ht⟩,
    have h₁ : (a : ℝ) ≤ (t / T : ℝ),
    {
      apply (le_div_iff (subtype.coe_lt_coe.mpr hT)).mpr,
      rw mul_comm,
      exact (subtype.coe_le_coe.mpr t_Ta_Tb.1),
    },
    have h₂ : (t / T : ℝ) ≤ b,
    {
      apply (div_le_iff (subtype.coe_lt_coe.mpr hT)).mpr,
      rw mul_comm,
      exact (subtype.coe_le_coe.mpr t_Ta_Tb.2),
    },
    use ⟨t / T, le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩,

    split,
    { exact ⟨h₁, h₂⟩ },
    rw first_part_apply,
    convert ht,
    simp,
    apply subtype.coe_inj.mp,
    show (T : ℝ) * (t / T) = t,
    rw [mul_div_left_comm, div_self],
    exact mul_one ↑t,
    exact Icc.coe_ne_zero.mpr (ne_zero.of_pos hT).out,
  }
end

lemma first_part_range (γ : dipath x₀ x₁) {T : I} (hT : 0 < T) :
  range (first_part_dipath γ hT) = (γ '' Icc 0 T) :=
begin
  rw dipath.range_eq_image_I _,
  convert first_part_image γ hT 0 1; norm_num,
end

lemma first_part_range_interval (γ : dipath x₀ x₁) {n : ℕ} (h : 0 < n):
  range (first_part_dipath γ (inv_I_pos h)) = γ ''  Icc 0 (inv_I h) := first_part_range γ (inv_I_pos h)
  
lemma first_part_range_interval_coe (γ : dipath x₀ x₁) {n : ℕ} (h : 0 < n):
  range (first_part_dipath γ (inv_I_pos h)) = γ.extend ''  Icc 0 (1/(↑n)) :=
begin
  rw first_part_range_interval γ h,
  rw ← dipath.image_extend_eq_image,
  rw auxiliary.inv_I_coe,
  refl,
end

lemma first_part_range_interval_partial (γ : dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
  (first_part_dipath γ (frac_pos (nat.succ_pos d) (le_of_lt hd))) '' Icc
    (frac (nat.succ_pos d) (le_of_lt hi)) -- frac i/(d+1)
    (frac (nat.succ_pos d) (nat.succ_le_of_lt hi)) -- frac (i+1)/(d+1)
    = γ ''  Icc
    (frac (nat.succ_pos n) (le_of_lt (lt_trans hi hd))) -- frac i/(n+1)
    (frac (nat.succ_pos n) (nat.succ_le_of_lt (lt_trans hi hd))) -- frac (i+1)/(n+1)
  :=
begin
  convert first_part_image γ (frac_pos (nat.succ_pos d) (le_of_lt hd)) (frac (nat.succ_pos d) (le_of_lt hi)) (frac (nat.succ_pos d) (nat.succ_le_of_lt hi));
  {
    simp [frac],
    apply subtype.coe_inj.mp,
    simp,
    refine (frac_cancel' _).symm,
    rw ← nat.cast_succ,
    exact nat.cast_ne_zero.mpr (nat.succ_ne_zero d),
  },
end

lemma first_part_range_interval_partial_coe (γ : dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ) (hi : i < d.succ) :
  (first_part_dipath γ (frac_pos (nat.succ_pos d) (le_of_lt hd))).extend '' Icc (↑i/(↑d+1)) ((↑i+1)/(↑d+1))
    = γ.extend ''  Icc (↑i/(↑n+1)) ((↑i+1)/(↑n+1))
  :=
begin
  have := first_part_range_interval_partial γ hd hi,
  rw ← dipath.image_extend_eq_image at this,
  rw ← dipath.image_extend_eq_image at this,
  convert this; {
    exact (nat.cast_succ _).symm,
  }
end

/-! ### Second Part -/

lemma second_part_image (γ : dipath x₀ x₁) {T : I} (hT : T < 1) (a b : I) :
  (second_part_dipath γ hT) '' Icc a b = γ '' Icc
    ⟨σ T * a + T, interp_left_mem_I T a⟩
    ⟨σ T * b + T, interp_left_mem_I T b⟩ :=
begin
  ext z,
  split,
  {
    rintro ⟨t, t_a_b, ht⟩,
    rw second_part_apply at ht,
    use ⟨σ T * t + T, interp_left_mem_I T t⟩,  
    exact ⟨⟨interp_left_le_of_le T t_a_b.1, interp_left_le_of_le T t_a_b.2⟩, ht⟩,
  },
  {
    rintro ⟨t, t_Ta_Tb, ht⟩,
    have : (T : ℝ) < 1 := hT,
    have : (σ T : ℝ) > 0 := show (1 - T : ℝ) > 0, by linarith,
    have h₁ : (a : ℝ) ≤ ((t - T) / (σ T) : ℝ),
    {
      apply (le_div_iff this).mpr,
      rw mul_comm,
      have : (σ T : ℝ) * a  + T ≤ t := t_Ta_Tb.1,
      linarith,
    },
    have h₂ : ((t - T) / (1 - T) : ℝ) ≤ b,
    {
      apply (div_le_iff this).mpr,
      rw mul_comm,
      have : (t : ℝ) ≤ (σ T : ℝ) * b + T := t_Ta_Tb.2,
      linarith,
    },

    use ⟨(t - T) / (1 - T), le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩,

    split,
    { exact ⟨h₁, h₂⟩ },
    rw second_part_apply,
    convert ht,
    simp,
    apply subtype.coe_inj.mp,
    show (σ T : ℝ) * ((t-T)/(σ T)) + T = t,
    rw [mul_div_left_comm, div_self],
    ring,
    exact ne_of_gt this,
  }
end

lemma second_part_range (γ : dipath x₀ x₁) {T : I} (hT : T < 1) :
  range (second_part_dipath γ hT) = γ '' Icc T 1  :=
begin
  rw dipath.range_eq_image_I _,
  convert second_part_image γ hT 0 1; norm_num,
end

/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n].
-/
lemma second_part_range_interval (γ : dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
  (second_part_dipath γ (inv_I_lt_one (lt_of_le_of_lt hn (lt_add_one n)))) '' Icc (frac hn (le_of_lt hi)) (frac hn (nat.succ_le_of_lt hi)) =
  γ ''  Icc (frac (nat.succ_pos n) (show i+1 ≤ n+1, by exact (le_of_lt (nat.succ_lt_succ hi)))) (frac (nat.succ_pos n) (show i+2 ≤ n+1, by exact nat.succ_lt_succ (nat.succ_le_of_lt hi))) :=
begin
  have : (n : ℝ) * (↑n + 1)⁻¹ = (1 - (↑n + 1)⁻¹),
  {
    have : (n + 1 : ℝ) ≠ 0 := ne_of_gt (add_pos (nat.cast_pos.mpr hn) one_pos),
    nth_rewrite 1 (div_self this).symm,
    ring,
  },
  have : (n + 1 : ℝ)⁻¹ = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹,
  {
    calc (n + 1 : ℝ)⁻¹  = (↑n + 1)⁻¹ * ↑n / ↑n : (mul_div_cancel _ _).symm
                  ... = ↑n * (↑n + 1)⁻¹ * (↑n)⁻¹ : by ring
                  ... =  (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ : by rw this,
    exact (nat.cast_ne_zero.mpr (ne_of_gt hn))
  },
  convert second_part_image γ (inv_I_lt_one (lt_of_le_of_lt hn (lt_add_one n))) (frac hn (le_of_lt hi)) (frac hn (nat.succ_le_of_lt hi)),
  {
    simp,
    calc (i + 1 : ℝ)/(↑n + 1) = ↑i/(↑n + 1) + 1/(↑n+1)              : by ring
                    ... = ↑i/(↑n + 1) + (↑n + 1)⁻¹                  : by rw one_div
                    ... = (↑n + 1)⁻¹ * ↑i + (↑n + 1)⁻¹                  : by rw div_eq_inv_mul
                    ... = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ * (↑i) + (↑n + 1)⁻¹ : by rw ← this
                    ... = (1 - (↑n + 1)⁻¹) * ((↑n)⁻¹ * (↑i)) + (↑n + 1)⁻¹ : by ring
                    ... = (1 - (↑n + 1)⁻¹) * (↑i / ↑n) + (↑n + 1)⁻¹ : by rw ← div_eq_inv_mul ↑i ↑n
  },
  {
    simp,
    calc (i + 2 : ℝ)/(↑n + 1) = (↑i + 1)/(↑n + 1) + 1/(↑n+1)              : by ring
                    ... = (↑i + 1)/(↑n + 1) + (↑n + 1)⁻¹                  : by rw one_div
                    ... = (↑n + 1)⁻¹ * (↑i + 1) + (↑n + 1)⁻¹                  : by rw div_eq_inv_mul
                    ... = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ * (↑i + 1) + (↑n + 1)⁻¹ : by rw ← this
                    ... = (1 - (↑n + 1)⁻¹) * ((↑n)⁻¹ * (↑i + 1)) + (↑n + 1)⁻¹ : by ring
                    ... = (1 - (↑n + 1)⁻¹) * ((↑i + 1) / ↑n) + (↑n + 1)⁻¹ : by rw ← div_eq_inv_mul (i + 1 : ℝ) ↑n
  }
end

/--
  When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n].
  Version with interval of real numbers
-/
lemma second_part_range_interval_coe (γ : dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n):
  (second_part_dipath γ (inv_I_lt_one (lt_of_le_of_lt hn (lt_add_one n)))).extend '' Icc (↑i/↑n) ((↑i+1)/↑n) =
  γ.extend ''  Icc ((↑i+1)/(↑n+1)) ((↑i+1+1)/(↑n+1)) :=
begin
  have := second_part_range_interval γ hi hn,
  rw ← dipath.image_extend_eq_image at this,
  rw ← dipath.image_extend_eq_image at this,
  convert this,
  exact (nat.cast_succ i).symm,
  exact (nat.cast_succ i).symm,
  exact (nat.cast_succ n).symm,
  {
    rw ← nat.cast_succ i,
    rw ← nat.cast_succ i.succ,
  },
  exact (nat.cast_succ n).symm,
end

/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma second_part_range_partial_interval (γ : dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
  (second_part_dipath γ (frac_lt_one (nat.succ_pos d) hd)) '' Icc
    (frac (nat.sub_pos_of_lt (nat.lt_of_succ_lt_succ hd)) (le_of_lt hi)) -- i/(n-d)
    (frac (nat.sub_pos_of_lt (nat.lt_of_succ_lt_succ hd)) (nat.succ_le_of_lt hi)) -- (i+1)/(n-d)
    =
  γ ''  Icc
    (frac (nat.succ_pos n) (show i+d.succ ≤ n.succ, by {
      apply le_of_lt,
      have : i < n.succ - d.succ := (nat.succ_sub_succ n d).symm ▸ hi,
      exact lt_tsub_iff_right.mp this,
    })) -- (i+d.succ)/(n+1)
    (frac (nat.succ_pos n) (show i+d.succ + 1 ≤ n.succ, by {
      apply nat.succ_le_of_lt,
      have : i < n.succ - d.succ := (nat.succ_sub_succ n d).symm ▸ hi,
      exact lt_tsub_iff_right.mp this,
    })) -- (i+d.succ+1)/(n+1)
  :=
begin
  convert second_part_image γ (frac_lt_one (nat.succ_pos d) hd)
    (frac (nat.sub_pos_of_lt (nat.lt_of_succ_lt_succ hd)) (le_of_lt hi))
    (frac (nat.sub_pos_of_lt (nat.lt_of_succ_lt_succ hd)) (nat.succ_le_of_lt hi));
  {
    simp,
    have : d < n := nat.lt_of_succ_lt_succ hd,
    rw nat.cast_sub (le_of_lt this),
    try {
      rw add_assoc,
      rw add_comm (↑d + 1 : ℝ) 1,
      rw ← add_assoc,
    },
    refine frac_special _ _,
    exact (ne_of_lt (nat.cast_lt.mpr this)),
    rw ← nat.cast_succ,
    have : n.succ ≠ 0 := nat.succ_ne_zero n,
    exact ne_zero.ne ↑(nat.succ n),
  },
end

/--
  When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)] is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma second_part_range_partial_interval_coe (γ : dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ) (hi : i < n - d) :
  (second_part_dipath γ (frac_lt_one (nat.succ_pos d) hd)).extend '' Icc (↑i/(↑n-↑d)) ((↑i+1)/(↑n-↑d))
    = γ.extend ''  Icc ((↑(i+d.succ))/(↑n+1)) ((↑(i+d.succ) + 1)/(↑n+1)) :=
begin
  have := second_part_range_partial_interval γ hd hi,
  rw ← dipath.image_extend_eq_image at this,
  rw ← dipath.image_extend_eq_image at this,
  convert this;
  {
    { exact (nat.cast_sub (le_of_lt $ nat.lt_of_succ_lt_succ hd)).symm} <|>
    { exact (nat.cast_succ _).symm }
  }
end

/-! ### Mixed Parts -/

/-
  Splitting a dipath at k/n and then at 1/k is the same as splitting it at 1/n
-/
lemma first_part_of_first_part (γ : dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  first_part_dipath
    (first_part_dipath γ (frac_pos hk (le_of_lt hkn))) -- k/n
    (inv_I_pos hk) -- 1/k
  = (first_part_dipath γ (inv_I_pos $ lt_trans hk hkn)).cast rfl (show γ _ = γ _, by { congr' 1, rw ← frac_mul_inv hk (le_of_lt hkn), refl, }) -- 1/n
:=
begin
  ext,
  show γ _ = γ _,
  congr' 1,
  rw ← frac_mul_inv hk (le_of_lt hkn),
  simp,
  rw mul_assoc,
end

/--
  Splitting a dipath [0, (k+1)/(n+1)] and then [1/(k+1), 1] is the same as splitting it [1/(n+1), 1] and then [0, k/n]
-/
lemma first_part_of_second_part (γ : dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  second_part_dipath
    (first_part_dipath γ (frac_pos (nat.succ_pos k) (le_of_lt $ nat.succ_lt_succ hkn))) -- (k+1)/(n+1)
    (inv_I_lt_one (nat.succ_lt_succ hk)) -- 1/(k+1)
  =
  (
    first_part_dipath
      (second_part_dipath γ (inv_I_lt_one (nat.succ_lt_succ (lt_trans hk hkn)))) -- 1/(n+1)
      (frac_pos hk (le_of_lt hkn)) -- k/n
  ).cast
    (show γ _ = γ _, by { congr' 1, apply subtype.coe_inj.mp, rw ← frac_mul_inv_coe (nat.succ_pos k) (le_of_lt (nat.succ_lt_succ hkn)), refl }) 
    (show γ _ = γ _, by { congr' 1, simp, have : (n : ℝ) > 0 := nat.cast_pos.mpr (lt_trans hk hkn), rw [← one_div, one_sub_inverse_of_add_one, frac_cancel', ← add_div], linarith, linarith })
    :=
begin
  ext,
  show γ _ = γ _,
  congr' 1,
  simp,
  have : (k : ℝ) > 0 := nat.cast_pos.mpr hk,
  have : (n : ℝ) > 0 := nat.cast_pos.mpr (lt_trans hk hkn),
  repeat { rw ← one_div, rw one_sub_inverse_of_add_one _ },
  rw mul_comm ((k : ℝ)/(↑k + 1)) (x : ℝ),
  rw [mul_div, ← add_div, frac_cancel'],
  rw ← mul_assoc ((n : ℝ) / (n+1 : ℝ)) (↑k/↑n) ↑x,
  rw frac_cancel',
  rw mul_comm ((k : ℝ)/(↑n + 1)) (x : ℝ),
  rw [mul_div, ← add_div],
  repeat { linarith },
end

/--
  Splitting a dipath [(k+2)/(n+2), 1] is the same as splitting it [1/(n+2), 1] and then [(k+1)/(n+1), 1]
-/
lemma second_part_of_second_part (γ : dipath x₀ x₁) {n k : ℕ} (hkn : k < n) :
  second_part_dipath
    (second_part_dipath γ (inv_I_lt_one (nat.succ_lt_succ (nat.succ_pos n)))) -- 1/(n+2)
    (frac_lt_one (nat.succ_pos k) (nat.succ_lt_succ hkn)) -- (k+1)/(n+1)
  =
  (
    second_part_dipath γ (frac_lt_one (nat.succ_pos k.succ) (nat.succ_lt_succ (nat.succ_lt_succ hkn))) -- (k+2)/(n+2)
  ).cast
    (show γ _ = γ _, by { congr' 1, simp,  have : (n : ℝ) + 1> 0, { rw ← nat.cast_succ, exact nat.cast_pos.mpr (nat.succ_pos n) }, rw [← one_div, one_sub_inverse_of_add_one, frac_cancel', ← add_div], linarith, linarith }) 
    rfl :=
begin
  ext,
  show γ _ = γ _,
  congr' 1,
  simp,
  have : (n : ℝ) > 0 := nat.cast_pos.mpr (lt_of_le_of_lt (nat.zero_le k) hkn),
  -- Rewrite left side to ... / (n+1+1)
    rw ← one_div,
    rw one_sub_inverse_of_add_one _,
    rw one_sub_frac,
    rw one_sub_frac,
    rw mul_comm (((n : ℝ) - ↑k) / _) (x : ℝ),
    rw mul_div,
    rw ← add_div,
    rw frac_cancel',
    rw ← add_div,
  -- Rewrite right side to ... / (n+1+1)
    rw mul_comm _ (x : ℝ),
    rw mul_div,
    rw ← add_div,
  -- Show that numerators are equal
    congr' 1,
    ring,
  repeat { linarith },
end


/-! ### Trans Parts -/

variables {x₂ : X}

lemma first_part_trans (γ₁ : dipath x₀ x₁) (γ₂ : dipath x₁ x₂) :
  (first_part_dipath (γ₁.trans γ₂) (inv_I_pos zero_lt_two)) = γ₁.cast rfl (dipath.trans_eval_at_half γ₁ γ₂) :=
begin
  ext t,
  rw [first_part_apply, dipath.trans_apply],
  simp,
  intro h,
  exfalso,
  linarith [unit_interval.le_one t],
end

lemma second_part_trans (γ₁ : dipath x₀ x₁) (γ₂ : dipath x₁ x₂) :
  (second_part_dipath (γ₁.trans γ₂) (inv_I_lt_one one_lt_two)) = γ₂.cast (dipath.trans_eval_at_half γ₁ γ₂) rfl :=
begin
  ext t,
  rw [second_part_apply, dipath.trans_apply],
  have h_two : 2 * (2⁻¹ : ℝ) = 1 := by norm_num,
  have ht : 2 * (2⁻¹ * (t : ℝ) + 2⁻¹) - 1 = ↑t,
  {
    rw mul_add,
    rw ← mul_assoc,
    rw h_two,
    ring,
  },
  have : (1 - 2⁻¹ : ℝ) = 2⁻¹ := by norm_num,
  simp [this],
  by_cases h : 2⁻¹ * (t : ℝ) ≤ 0,
  {
    have : t = 0 := subtype.coe_inj.mp (show (t : ℝ) = 0, by linarith [unit_interval.nonneg t]),
    simp [h, this],
  },
  simp [h, ht],
end

lemma trans_first_part (γ₁: dipath x₀ x₁) (γ₂ : dipath x₁ x₂) (n : ℕ) (t : I) :
  (first_part_dipath (γ₁.trans γ₂) (inv_I_pos (nat.succ_pos (n + n).succ))) t =
    (first_part_dipath γ₁ (inv_I_pos (nat.succ_pos n))) t :=
begin
  rw first_part_apply,
  rw first_part_apply,
  rw dipath.trans_apply,
  simp,
  have : (n + n + 1 + 1 : ℝ) ≥ 2,
  {
    rw ← nat.cast_add,
    have : (↑(n + n) : ℝ) ≥ 0 := nat.cast_nonneg (n + n),
    linarith,
  },
  have h₁ : (n + n + 1 + 1 : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_inv_of_le zero_lt_two this,
  have h₂ : (t : ℝ) ≤ 1 := t.2.2,
  have : (n + n + 1 + 1 : ℝ)⁻¹ * ↑t ≤ 2⁻¹,
  {
    rw ← mul_one (2⁻¹ : ℝ),
    apply mul_le_mul h₁ h₂,
    exact t.2.1,
    norm_num,
  },
  rw dif_pos this,
  apply congr_arg,
  ext,
  simp,
  rw ← mul_assoc,
  congr' 1,
  have : (n + n + 1 + 1 : ℝ)  = (2 * (n + 1)) := by ring,
  rw this,
  rw mul_inv,
  rw ← mul_assoc,
  norm_num,
end

namespace aux_equalities
lemma h₁ (t : I) : 0 ≤ (t : ℝ) := t.2.1

lemma h₂ (n : ℕ) : 0 ≤ (n : ℝ) := nat.cast_nonneg n

lemma h₃ (n : ℕ) : (n + 1 + 1 : ℝ) ≠ 0 := by linarith [h₂ n]

lemma h₄ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) > 0 := by linarith [h₂ n]

lemma h₅ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) = 2 * (↑n + 1 + 1) := by ring

lemma h₆ (n : ℕ) : (↑n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) = 2⁻¹ :=
begin
  rw h₅ n,
  rw mul_comm,
  rw div_mul_eq_div_div,
  rw div_self (h₃ n),
  exact one_div _,
end

lemma h₇ (n : ℕ) : (n + n + 1 + 1 + 1: ℝ) ≠ 0 := by linarith [h₂ n]

lemma h₈ (n : ℕ) : (↑n + 1 + (↑n + 1) + 1 + 1 : ℝ) = (↑n + ↑n + 1 + 1 + 1 + 1) := by ring

lemma e₁ (n : ℕ) (t : I) : (1 - (n + 1 : ℝ) / (↑n + 1 + 1)) * ↑t + (↑n + 1) / (↑n + 1 + 1) = ((t : ℝ) + ↑n + 1) / (↑n + 1 + 1) :=
begin
  nth_rewrite 0 ← div_self (h₃ n),
  ring,
end

lemma e₂ (n : ℕ) (t : I) : ((1 - (n + n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1)) * ↑t + (↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1)) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1) :=
begin
  nth_rewrite 0 ← div_self (h₇ n),
  ring,
end

lemma e₃ (n : ℕ) : (1 - (n + 1 + (n + 1) + 1 + 1 : ℝ)⁻¹) = (↑n + ↑n + 1 + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) :=
begin
  nth_rewrite 0 ← div_self (ne_of_gt (h₄ n)),
  ring_nf,
end

lemma e₄ (n : ℕ) (t : I) : ((↑n + ↑n + 1 + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) * ((↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1))) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) :=
begin
  rw mul_comm,
  rw div_mul_div_cancel _ (h₇ n),
end

lemma e₅ (n : ℕ) (r : ℝ) : 2 * (r / (↑n + ↑n + 1 + 1 + 1 + 1) + (↑n + 1 + (↑n + 1) + 1 + 1)⁻¹) =
    (r + 1) / (↑n + 1 + 1) :=
begin
  rw h₈,
  rw ← one_div,
  rw div_add_div_same,
  rw h₅,
  rw mul_div,
  rw mul_comm,
  rw ← mul_div,
  rw div_mul_eq_div_div,
  rw div_self (show (2 : ℝ) ≠ 0, by norm_num),
  ring,
end

lemma e₆ (n : ℕ) (r : ℝ) : (1 - (n + 1 + 1 : ℝ)⁻¹) * r + (n + 1 + 1 : ℝ)⁻¹ = ((n + 1) * r + 1) / (n + 1 + 1) :=
begin
  nth_rewrite 0 ← div_self (h₃ n),
  ring,
end

end aux_equalities

open aux_equalities

lemma trans_first_part_of_second_part (γ₁: dipath x₀ x₁) (γ₂ : dipath x₁ x₂) (n : ℕ) (t : I) :
  (first_part_dipath
    (second_part_dipath (γ₁.trans γ₂) (inv_I_lt_one (nat.succ_lt_succ (nat.succ_pos (n.succ + n.succ)))))
    (frac_pos (nat.succ_pos (n + n).succ) (le_of_lt (nat.lt_succ_self _)))
   ) t
  =
    ((second_part_dipath γ₁ (inv_I_lt_one (nat.succ_lt_succ (nat.succ_pos n)))).trans
      (first_part_dipath γ₂ (frac_pos (nat.succ_pos n) (le_of_lt (nat.lt_succ_self _))))) t :=
begin
  rw first_part_apply,
  rw second_part_apply,
  rw dipath.trans_apply,
  rw dipath.trans_apply,
  split_ifs,
  {
    rw second_part_apply,
    apply congr_arg,
    simp,
    rw e₃,
    rw mul_comm _ (t : ℝ),
    rw mul_div,
    rw mul_comm (_/_) (_/_),
    rw div_mul_div_cancel _ (h₇ n),
    rw e₆,
    rw e₅,
    ring,
  },
  {
    -- Sould not be possible
    exfalso,
    revert h,
    apply not_le.mpr,
    simp,
    rw e₃,
    rw mul_comm _ (t : ℝ),
    rw mul_div,
    rw mul_comm (_/_) (_/_),
    rw div_mul_div_cancel _ (h₇ n),
    apply (mul_lt_mul_left (show 0 < (2 : ℝ), by norm_num)).mp,
    rw e₅,
    apply (lt_div_iff (show (n + 1 + 1 : ℝ) > 0, by linarith [h₂ n])).mpr,
    norm_num,
    push_neg at h_1,
    calc (n + 1 : ℝ) = 1 * (n + 1 : ℝ) : by rw one_mul
                ... = (2⁻¹ * 2) * (n + 1 : ℝ) : by rw inv_mul_cancel (show (2 : ℝ) ≠ 0, by norm_num)
                ... = 2⁻¹ * (n + n + 1 + 1 : ℝ) : by ring
                ... = 1/2 * (n + n + 1 + 1 : ℝ) : by rw one_div
                ... < t * (n + n + 1 + 1 : ℝ) : (mul_lt_mul_right (by linarith [h₂ n])).mpr h_1,
  },
  {
    -- Sould not be possible
    exfalso,
    revert h,
    apply imp_false.mpr,
    apply not_not.mpr,
    simp,
    rw e₃,
    rw mul_comm _ (t : ℝ),
    rw mul_div,
    rw mul_comm (_/_) (_/_),
    rw div_mul_div_cancel _ (h₇ n),
    apply (mul_le_mul_left (show 0 < (2 : ℝ), by norm_num)).mp,
    rw e₅,
    apply (div_le_iff (show (n + 1 + 1 : ℝ) > 0, by linarith [h₂ n])).mpr,
    norm_num,
    calc ↑t * (n + n + 1 + 1 : ℝ) ≤ 1/2 * (n + n + 1 + 1 : ℝ) : (mul_le_mul_right (by linarith [h₂ n])).mpr h_1
                            ... =  (1/2 * 2) * (n + 1 : ℝ) : by ring
                            ... = 1 * (n + 1 : ℝ) : by rw div_mul_cancel (1 : ℝ) (show (2 : ℝ) ≠ 0, by norm_num)
                            ... = (n + 1 : ℝ) : by rw one_mul
  },
  {
    rw first_part_apply,
    apply congr_arg,
    simp,
    rw e₃,
    rw mul_comm _ (t : ℝ),
    rw mul_div,
    rw mul_comm (_/_) (_/_),
    rw div_mul_div_cancel _ (h₇ n),
    rw e₅,
    nth_rewrite 5 ← div_self (h₃ n),
    ring,
  },
end

lemma trans_second_part_second_part (γ₁: dipath x₀ x₁) (γ₂ : dipath x₁ x₂) (n : ℕ) (t : I) :
  (second_part_dipath
    (second_part_dipath (γ₁.trans γ₂) (inv_I_lt_one (nat.succ_lt_succ (nat.succ_pos (n.succ + n.succ)))))
    (frac_lt_one (nat.succ_pos (n + n).succ) (nat.lt_succ_self _))
   ) t
  =
    (second_part_dipath γ₂ (frac_lt_one (nat.succ_pos n) (nat.lt_succ_self n.succ))) t :=
begin
  rw second_part_apply,
  rw second_part_apply,
  rw second_part_apply,
  rw dipath.trans_apply,
  simp,
  split_ifs with h h,
  {
    exfalso,
    rw e₂ at h,
    rw e₃ at h,
    rw e₄ at h,
    rw ← one_div at h,
    rw h₈ at h,
    rw div_add_div_same at h,
    have : (↑n + 1 + 1 : ℝ) < (↑t + ↑n + ↑n + 1 + 1 + 1) := by linarith [h₂ n, h₁ t],
    have := lt_of_lt_of_le (div_lt_div_of_lt (h₄ n) this) h,
    rw h₆ at this,
    exact lt_irrefl _ this,
  },
  apply congr_arg,
  simp,
  rw e₁,
  rw e₂,
  rw e₃,
  rw e₄,
  rw e₅,
  nth_rewrite 5 ← div_self (h₃ n),
  rw div_sub_div_same,
  ring,
end

lemma trans_image_inv_eq_first (γ₁: dipath x₀ x₁) (γ₂ : dipath x₁ x₂) (n : ℕ) :
  (γ₁.trans γ₂) (inv_I (nat.succ_pos (n + n).succ)) = γ₁ (inv_I (nat.succ_pos n)) :=
begin
  have := trans_first_part γ₁ γ₂ n 1,
  rw split_dipath.first_part_apply at this,
  rw split_dipath.first_part_apply at this,
  convert this,
  simp,
  simp,
end

lemma second_part_trans_image_inv_eq_second (γ₁: dipath x₀ x₁) (γ₂ : dipath x₁ x₂) (n : ℕ) :
  (second_part_dipath (γ₁.trans γ₂) (inv_I_lt_one (nat.succ_lt_succ (nat.succ_pos (n.succ + n.succ)))))
    (frac (nat.succ_pos (n+n).succ.succ) (le_of_lt (nat.lt_succ_self _)))
   = γ₂ (frac (nat.succ_pos (n.succ)) (le_of_lt (nat.lt_succ_self _))) :=
begin
  rw second_part_apply,
  rw dipath.trans_apply,
  rw dif_neg,
  {
    apply congr_arg,
    simp,
    rw e₃,
    rw mul_comm (_ / _) (_ / _),
    rw div_mul_div_cancel _ (h₇ n),
    rw e₅ n (↑n + ↑n + 1 + 1),
    nth_rewrite 5 ← div_self (h₃ n),
    ring,
  },
  simp,
  rw e₃,
  rw mul_comm,
  rw div_mul_div_cancel _ (h₇ n),
  rw h₈,
  rw ← one_div (n + n + 1 + 1 + 1 + 1 : ℝ),
  rw div_add_div_same,
  apply (lt_div_iff (h₄ n)).mpr,
  rw h₅,
  rw ← mul_assoc,
  norm_num,
  linarith [h₂ n],
end

end split_properties
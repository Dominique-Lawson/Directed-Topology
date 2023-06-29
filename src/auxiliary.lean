import topology.path_connected
import topology.homotopy.basic

/- This file contains some more general auxiliary definitions and lemmas, including:
  * Lemmas about monotone paths
  * Lemmas about conditions for terms of type ℝ being of subtype I
  * Definition and properties of fractions in I
-/

open_locale unit_interval
universe u

lemma monotone_path_bounded {α : Type u} {x y : α} [topological_space α] [preorder α] {a : path x y} (ha_mono : monotone a) (t : I) :
  x ≤ a.to_fun t ∧ a.to_fun t ≤ y :=
begin
  have h₁ : a 0 ≤ a t := ha_mono (show 0 ≤ t, by exact t.2.1),
  have h₂ : a t ≤ a 1 := ha_mono (show t ≤ 1, by exact t.2.2),
  rw a.source at h₁,
  rw a.target at h₂,
  exact ⟨h₁, h₂⟩,
end
  
lemma monotone_path_source_le_target {α : Type u} {x y : α} [topological_space α] [preorder α] {a : path x y} (ha_mono : monotone a) :
  x ≤ y :=
begin
  have h : a 0 ≤ a 1 := ha_mono (subtype.mk_le_mk.mpr zero_le_one),
  rw [a.source, a.target] at h,
  exact h,
end

namespace auxiliary

lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) := mul_pos zero_lt_two hT₀
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) := mul_pos zero_lt_two (by {simp, exact subtype.coe_lt_coe.mp hT₁})

lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I :=
begin
  split,
  exact mul_nonneg zero_le_two t.2.1,
  calc 2 * (t : ℝ) ≤ 2 * 2⁻¹ : (mul_le_mul_left zero_lt_two).mpr ht
              ...  = 1 : by norm_num
end

lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I :=
begin
  split,
  {
    calc 0 = 2 * (2⁻¹ : ℝ) - 1 : by norm_num
       ... ≤ 2 * ↑t - 1 : sub_le_sub_right ((mul_le_mul_left (by norm_num)).mpr ht) 1
  },
  {
    calc 2 * (t : ℝ) - 1 ≤ 2 * 1 - 1 : sub_le_sub_right ((mul_le_mul_left (by norm_num)).mpr t.2.2) 1
                     ... = 1 : by norm_num
  }
end

lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) : (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T :=
begin
  apply add_le_add_right,
  apply mul_le_mul,
  refl,
  exact hab,
  exact a.2.1,
  exact (σ T).2.1,
end

section

variables {X Y : Type*} [topological_space X] [topological_space Y]

lemma map_reparam_eq_reparam_map {x₀ x₁ : X} (γ : path x₀ x₁) {f : X → Y} (hf_cont : continuous f)
  {φ : I → I} (hφ_cont : continuous φ) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) (t : I) : 
((γ.map hf_cont).reparam φ hφ_cont hφ₀ hφ₁) t = ((γ.reparam φ hφ_cont hφ₀ hφ₁).map hf_cont) t :=
begin
  refl,
end

end

section

noncomputable theory

lemma half_mem_I : (2⁻¹ : ℝ) ∈ I :=
⟨inv_nonneg.mpr zero_le_two, inv_le_one one_le_two⟩

def half_I : I := ⟨(2⁻¹ : ℝ), half_mem_I⟩

lemma has_T_half {t₀ t₁ : I} (γ : path t₀ t₁) (ht₀ : ↑t₀ < (2⁻¹ : ℝ)) (ht₁ : ↑t₁ > (2⁻¹ : ℝ)) : 
  ∃ (T : I),  0 < T ∧ T < 1 ∧ (γ T) = half_I :=
begin
  have : γ.to_fun 0 ≤ half_I,
  {
    rw γ.source',
    exact subtype.coe_le_coe.mp (le_of_lt ht₀)
  }, 
  have h₀ : ∃ (t : I), γ t ≤ half_I := ⟨0, this⟩,
  
  have : half_I ≤ γ.to_fun 1,
  {
    rw γ.target',
    exact subtype.coe_le_coe.mp (le_of_lt ht₁)
  }, 
  have h₁ : ∃ (t : I), half_I ≤ γ t := ⟨1, this⟩,
  have hy := set.mem_range.mp (mem_range_of_exists_le_of_exists_ge γ.continuous_to_fun h₀ h₁),
  cases hy with T hT,
  use T,
  have hT₀ : 0 ≠ T,
  {
    rintro ⟨rfl⟩,
    apply lt_irrefl (t₀ : ℝ),
    calc (t₀ : ℝ) < 2⁻¹       : ht₀
              ... = (γ 0 : ℝ) : subtype.coe_inj.mpr hT.symm
              ... = ↑t₀       : subtype.coe_inj.mpr γ.source'
  },
  have hT₁ : T ≠ 1,
  {
    rintro ⟨rfl⟩,
    apply lt_irrefl (t₁ : ℝ),
    calc (t₁ : ℝ) = (γ 1 : ℝ) : subtype.coe_inj.mpr γ.target'.symm
              ... = half_I    : subtype.coe_inj.mpr hT
              ... < ↑t₁       : ht₁
  },
  exact ⟨lt_iff_le_and_ne.mpr ⟨T.2.1, hT₀⟩, lt_iff_le_and_ne.mpr ⟨T.2.2, hT₁⟩, hT⟩
end

end

section frac


@[reducible]
def frac {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : I := ⟨(i : ℝ)/(n : ℝ),
  ⟨div_nonneg (nat.cast_nonneg i) (nat.cast_nonneg n),
  (div_le_one ((@nat.cast_pos ℝ _ _ n).mpr hn)).mpr (nat.cast_le.mpr hi)⟩⟩

@[reducible]
def inv_I {n : ℕ} (hn : 0 < n) : I := frac hn (nat.succ_le_iff.mpr hn)

@[simp] lemma frac_coe {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : (frac hn hi : ℝ) = (i/n : ℝ) := rfl
@[simp] lemma inv_I_coe {n : ℕ} (hn : 0 < n) : ((inv_I hn) : ℝ) = (1/n : ℝ) := by simp

lemma frac_mul_inv {i n : ℕ} (i_pos : 0 < i) (hi_n : i ≤ n) : (frac (lt_of_lt_of_le i_pos hi_n) hi_n) * (inv_I i_pos) = (inv_I (lt_of_lt_of_le i_pos hi_n)) :=
begin
  unfold frac inv_I,
  apply subtype.coe_inj.mp,
  simp,
  have : (i : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_lt i_pos).symm, 
  have : (i : ℝ) * (↑i)⁻¹ = 1 := mul_inv_cancel this,
  calc (i : ℝ)/↑n * (↑i)⁻¹ = (↑i * (↑i)⁻¹)/↑n : div_mul_eq_mul_div ↑i ↑n (↑i)⁻¹
                       ... = 1/↑n : by rw this
                       ... = (↑n)⁻¹ : one_div ↑n
end

lemma frac_zero {n : ℕ} (hn : 0 < n) : frac hn (nat.zero_le n) = 0 :=
begin
  ext,
  rw frac_coe,
  simp,
end

lemma frac_self {n : ℕ} (hn : 0 < n) : frac hn (le_refl n) = 1 :=
begin
  ext,
  rw frac_coe,
  rw div_self,
  simp,
  exact nat.cast_ne_zero.mpr (ne_of_gt hn),
end

lemma frac_mul_inv_coe {i n : ℕ} (i_pos : 0 < i) (hi_n : i ≤ n) : (frac (lt_of_lt_of_le i_pos hi_n) hi_n : ℝ) * (inv_I i_pos : ℝ) = (inv_I (lt_of_lt_of_le i_pos hi_n) : ℝ) :=
begin
  rw ← frac_mul_inv i_pos hi_n,
  refl,
end

lemma frac_eq_inv₁ {i n : ℕ} (i_pos : 0 < i) (hi_n : (i - 1).succ ≤ ((n+1) * i - 1).succ)  : inv_I (nat.succ_pos n) = frac (nat.succ_pos _) hi_n :=
begin
  simp,
  have : (↑(i - 1) : ℝ) + 1 = ↑i,
  {
    nth_rewrite 1 ← nat.succ_pred_eq_of_pos i_pos,
    simp,
    refl,
  },
  rw this,
  have : (↑((n+1)* i - 1) : ℝ) + 1 = (↑n+1)*↑i,
  {
    rw ← (nat.cast_succ n),
    rw ← nat.cast_mul,
    nth_rewrite 1 ← nat.succ_pred_eq_of_pos (mul_pos (nat.succ_pos n) i_pos),
    simp,
    refl,
  },
  rw this,
  rw div_mul_left _,
  exact (one_div _).symm,
  exact ne_of_gt (nat.cast_pos.mpr i_pos),
end

lemma sigma_inv_eq_frac_pred {n : ℕ} (hn : 0 < n) : σ (inv_I (nat.succ_pos n)) = frac (nat.succ_pos n) (le_of_lt (lt_add_one n)) :=
begin
  apply subtype.coe_inj.mp,
  unfold inv_I frac,
  show 1 - (↑1 / (n.succ : ℝ)) = _,
  have : (n.succ : ℝ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt (nat.succ_pos n)),
  rw ← (div_self this),
  rw div_sub_div_same,
  simp,
end

lemma frac_pos {n i : ℕ} (hi : 0 < i) (hn : i ≤ n) : 0 < frac (lt_of_lt_of_le hi hn) hn :=
begin
  unfold frac,
  apply subtype.coe_lt_coe.mp,
  apply div_pos,
  exact nat.cast_pos.mpr hi,
  exact nat.cast_pos.mpr (lt_of_lt_of_le hi hn)
end

lemma frac_lt_one {n i : ℕ} (hi : 0 < i) (hn : i < n) : frac (lt_trans hi hn) (le_of_lt hn) < 1 :=
begin
  unfold frac,
  apply subtype.coe_lt_coe.mp,
  simp,
  apply (div_lt_one _).mpr,
  exact nat.cast_lt.mpr hn,
  exact nat.cast_pos.mpr (lt_trans hi hn),
end

lemma inv_I_pos {n : ℕ} (hn : 0 < n) : 0 < inv_I hn := frac_pos zero_lt_one (nat.succ_le_iff.mpr hn)

lemma inv_I_lt_one {n : ℕ} (hn : 1 < n) : inv_I (lt_trans zero_lt_one hn) < 1 := frac_lt_one zero_lt_one hn

end frac

section equalities

lemma one_sub_inverse_of_add_one {n : ℝ} (hn : n + 1 ≠ 0) : 1 - 1 / (n + 1) = n / (n + 1) :=
begin
  nth_rewrite 0 ← (div_self hn),
  rw div_sub_div_same,
  rw add_sub_cancel,
end

lemma frac_cancel {a b c : ℝ} (hb : b ≠ 0) : (a / b) * (b / c) = a / c :=
begin
  rw mul_div,
  rw div_mul_cancel,
  exact hb,
end

lemma frac_cancel' {a b c : ℝ} (hb : b ≠ 0) : (b / a) * (c / b) = c / a :=
begin
  rw mul_comm,
  exact frac_cancel hb,
end

lemma one_sub_frac {a b : ℝ} (hb : b + 1 ≠ 0) : (1 - (a + 1)/(b+1)) = (b - a) / (b + 1) :=
begin
  nth_rewrite 0 ← (div_self hb),
  rw div_sub_div_same,
  congr' 1,
  ring,
end

lemma frac_special {a b c : ℝ} (hbc : b ≠ c) (hc : c + 1 ≠ 0) : (a + (b + 1)) / (c + 1) = (1 - (b + 1) / (c + 1)) * (a / (c - b)) + (b + 1) / (c + 1) :=
begin
  rw one_sub_frac hc,
  rw frac_cancel',
  exact (div_add_div_same _ _ _).symm,
  exact sub_ne_zero_of_ne hbc.symm,
end

end equalities

namespace homotopy

variables {X Y : Type u} [topological_space X] [topological_space Y]
variables {f₀ f₁ f₂ : C(X, Y)}

lemma trans_apply_left (F : continuous_map.homotopy f₀ f₁) (G : continuous_map.homotopy f₁ f₂) (t : I × X) (ht : (t.1 : ℝ) ≤ 2⁻¹) :
  (F.trans G) t = F (⟨2 * (t.1 : ℝ), double_mem_I ht⟩, t.2) :=
begin
  rw continuous_map.homotopy.trans_apply F G t,
  simp [ht],
end

end homotopy

end auxiliary
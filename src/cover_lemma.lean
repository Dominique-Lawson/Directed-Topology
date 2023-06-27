import topology.metric_space.basic
import topology.unit_interval
import auxiliary

/-
  This file contains two applications of the Lebesgue Number Lemma:
  One concerns the unit interval and the other concerns the unit square.
-/

universe u

open auxiliary
open_locale unit_interval

/-! ### Auxiliary lemmas -/

lemma mid_point_Icc {i n : ℕ} (hn : n > 0) (hi : i < n) : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) :=
begin
    split; refine (div_le_div_iff _ _).mpr _; linarith [show (n : ℝ) > 0, by exact nat.cast_pos.mpr hn],
end

lemma mid_point_I {i n : ℕ} (hn : n > 0) (hi : i < n) : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I :=
begin
  have n_cast_pos : 0 < (n : ℝ) := nat.cast_pos.mpr hn,
  have : 2 * i + 1 ≤ 2 * n := by linarith,
  split,
  {
    apply div_nonneg,
    exact add_nonneg (mul_nonneg (by norm_num) (nat.cast_nonneg i)) (by norm_num),
    exact mul_nonneg (by norm_num) (nat.cast_nonneg n),
  },
  {
    refine (div_le_one (mul_pos (by norm_num) n_cast_pos)).mpr _,
    have : (↑(2 * i  + 1) : ℝ) ≤ ↑(2 * n) := nat.cast_le.mpr this,
    convert this; simp,
  }
end

/-! ### Covering lemma for the unit interval -/

theorem lebesgue_number_lemma_unit_interval {ι : Sort u} {c : ι → set ℝ} (hc₁ : ∀ (i : ι), is_open (c i)) (hc₂ : I ⊆ ⋃ (i : ι), c i) :
  ∃ (n > 0), ∀ (i : ℕ) (h : i < n), ∃ (j : ι), set.Icc (↑i/↑n) ((↑i+1)/↑n) ⊆ c j :=
begin
  rcases (lebesgue_number_lemma_of_metric (is_compact_Icc) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩,
  rcases real.archimedean.arch 2 δ_pos with ⟨n, hn⟩,
  use n,
  have n_pos : 0 < n,
  {
    by_contra,
    have : n = 0 := by linarith,
    rw this at hn,
    have : (2 : ℝ) ≤ 0 := hn,
    linarith,
  },
  have n_cast_pos : 0 < (n : ℝ) := nat.cast_pos.mpr n_pos,
  split,
  { exact n_pos },
  intros i hi,
  have mid_point_I : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := mid_point_I n_pos hi,
  have mid_point_Icc : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := mid_point_Icc n_pos hi,
  rcases (hδ ((2 * i + 1 : ℝ)/(2 * n : ℝ)) mid_point_I) with ⟨j, hj⟩,
  use j,
  apply subset_trans _ hj,
  intros x hx,
  show dist x ((2 * i + 1 : ℝ)/(2 * n : ℝ)) < δ,
  have : 1/(n : ℝ) < δ,
  {
    apply (div_lt_iff' n_cast_pos).mpr,
    have : (1 : ℝ) < (2 : ℝ) := by norm_num,
    convert lt_of_lt_of_le this hn,
    simp,
  },
  apply lt_of_le_of_lt _ this,
  convert real.dist_le_of_mem_Icc hx mid_point_Icc,
  rw div_sub_div_same,
  simp,
end

/-! ### Covering lemma for the unit square -/

def unit_square : set (I × I) := set.univ

lemma compact_unit_square : is_compact unit_square := is_compact_univ
  
/-- The square [i/n, (i+1)/n] × [j/m, (j+1)/m] in the unit interval. -/
def unit_subsquare {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) : set (I × I) := set_of $
  λ (a : I × I),
    ((frac (nat.succ_pos n) (le_of_lt hi)) ≤ a.1 ∧ a.1 ≤ (frac (nat.succ_pos n) (nat.succ_le_of_lt hi))) ∧
    (frac (nat.succ_pos m) (le_of_lt hj)) ≤ a.2 ∧ a.2 ≤ (frac (nat.succ_pos m) (nat.succ_le_of_lt hj))

theorem lebesgue_number_lemma_unit_square {ι : Sort u} {c : ι → set (I × I)} (hc₁ : ∀ (i : ι), is_open (c i)) (hc₂ : unit_square ⊆ (⋃ (i : ι), c i)) :
  ∃ (n : ℕ), ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < n.succ), ∃ (a : ι), unit_subsquare hi hj ⊆ c a :=
begin
  rcases (lebesgue_number_lemma_of_metric (compact_unit_square) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩,
  rcases real.archimedean.arch 2 δ_pos with ⟨n, hn⟩,
  use n,
  have n_pos : 0 < n.succ := nat.succ_pos n,
  have n_cast_pos : 0 < (n.succ : ℝ) := nat.cast_pos.mpr n_pos,
  intros i j hi hj,
  let mp_h : ℝ := (2 * i + 1 : ℝ)/(2 * n.succ : ℝ),
  let mp_v : ℝ := (2 * j + 1 : ℝ)/(2 * n.succ : ℝ),
  have mid_point_h_Icc : mp_h ∈ set.Icc ((i:ℝ)/(n.succ:ℝ)) ((i+1:ℝ)/(n.succ:ℝ)) := mid_point_Icc n_pos hi,
  have mid_point_h_I : mp_h ∈ I := mid_point_I n_pos hi,
  have mid_point_v_Icc : mp_v ∈ set.Icc ((j:ℝ)/(n.succ:ℝ)) ((j+1:ℝ)/(n.succ:ℝ)) := mid_point_Icc n_pos hj,
  have mid_point_v_I : mp_v ∈ I := mid_point_I n_pos hj,
  rcases hδ (⟨mp_h, mid_point_h_I⟩, ⟨mp_v, mid_point_v_I⟩) (set.mem_univ _) with ⟨a, ha⟩,
  use a,
  apply subset_trans _ ha,
  intros x hx,
  show dist x _ < δ,
  have : dist _ _ ≤ dist _ _ + dist _ _ := dist_triangle x (x.1, ⟨mp_v, mid_point_v_I⟩)  (⟨mp_h, mid_point_h_I⟩, ⟨mp_v, mid_point_v_I⟩),
  apply lt_of_le_of_lt this,
  have : 1/(n.succ : ℝ) < (δ/2),
  {
    apply (div_lt_iff' n_cast_pos).mpr,
    have : (1 : ℝ) < (2 : ℝ) := by norm_num,
    rw mul_div,
    have : (n : ℝ) * δ ≥ 2,
    {
      convert hn,
      simp,
    },
    have : (n.succ : ℝ) * δ > 2,
    {
      rw nat.cast_succ,
      rw add_mul,
      rw one_mul,
      exact lt_add_of_le_of_pos this δ_pos,
    },
    linarith,
  },
  have h₁ : dist x (x.1, ⟨mp_v, mid_point_v_I⟩) < (δ/2),
  {
    apply lt_of_le_of_lt _ this,
    have : x = (x.1, x.2),
    {
      ext; refl,
    },
    rw this,
    rw dist_prod_same_left,
    convert real.dist_le_of_mem_Icc hx.2 _,
    simp,
    rw div_sub_div_same,
    simp,
    convert mid_point_v_Icc,
    rw auxiliary.frac_coe,
    rw nat.cast_succ,
  },
  have h₂ : dist (x.1, (⟨mp_v, mid_point_v_I⟩ : I)) ((⟨mp_h, mid_point_h_I⟩ :I), (⟨mp_v, mid_point_v_I⟩ : I)) < (δ/2),
  {
    apply lt_of_le_of_lt _ this,
    rw dist_prod_same_right,
    convert real.dist_le_of_mem_Icc hx.1 _,
    simp,
    rw div_sub_div_same,
    simp,
    convert mid_point_h_Icc,
    rw auxiliary.frac_coe,
    rw nat.cast_succ,
  },
  linarith,
end
import dipath
import dTop

/-
  This file contains definitions about interpolating points in the directed unit interval 
  and contains conditions about when interpolating gives directed maps.
-/

open_locale unit_interval

universe u

section

lemma interp_mem_I (T a b : I) : (σ T : ℝ) * ↑a + ↑T * ↑b ∈ I :=
begin
    split,
    calc (0 : ℝ) = ↑(σ T) * 0 + ↑T * 0 : by simp
             ... ≤ ↑(σ T) * a + ↑T * 0 : add_le_add_right (mul_le_mul (le_refl (σ T : ℝ)) a.2.1 (le_refl 0) (σ T).2.1) (↑T * 0)
             ... ≤ ↑(σ T) * a + ↑T * b : add_le_add_left (mul_le_mul (le_refl ↑T) b.2.1 (le_refl 0) T.2.1) (↑(σ T) * ↑a),
    calc (σ T : ℝ) * ↑a + ↑T * ↑b ≤ ↑(σ T) * 1 + ↑T * ↑b : add_le_add_right (mul_le_mul (le_refl (σ T : ℝ)) a.2.2 a.2.1 (σ T).2.1) (↑T * ↑b)
                              ... ≤ ↑(σ T) * 1 + ↑T * 1 : add_le_add_left (mul_le_mul (le_refl ↑T) b.2.2 b.2.1 T.2.1) (↑(σ T) * 1)
                              ...  = 1 : by simp
end

lemma interp_left_mem_I (T a : I) : (σ T : ℝ) * ↑a + ↑T ∈ I :=
begin
  convert interp_mem_I T a 1,
  simp,
end

lemma interp_right_mem_I (T b : I) : (σ T : ℝ) + ↑T * ↑b ∈ I :=
begin
  convert interp_mem_I T 1 b,
  simp,
end

lemma interp_const_le_of_le_of_le {a b T₀ T₁ : I} (hab : a ≤ b) (hT : T₀ ≤ T₁) :
  ((σ T₀ : ℝ) * ↑a + ↑T₀ * ↑b) ≤ (σ T₁ : ℝ) * ↑a + ↑T₁ * ↑b :=
begin
  calc (1 - T₀ : ℝ) * (a : ℝ) + (T₀ : ℝ) * (b : ℝ) = ↑a + ↑T₀ * (b - a) : by ring
                ...  ≤ ↑a + ↑T₁ * (b - a) : add_le_add_left (mul_le_mul_of_nonneg_right hT (sub_nonneg_of_le hab)) ↑(a)
                ...  = (1 - T₁ : ℝ) * (a : ℝ) + (T₁ : ℝ) * (b : ℝ) : by ring
end

def interpolate_const (a b : I) : C(I, I) :=
{
  to_fun := λ t, ⟨_, interp_mem_I t a b⟩
}

def directed_interpolate_const {a b : I} (h : a ≤ b) : D(I, I) :=
{
  to_continuous_map := interpolate_const a b,
  directed_to_fun := λ x y γ hγ x y hxy, interp_const_le_of_le_of_le h (hγ hxy),
}

variables (f : C(I, I)) (g : C(I, I))

def interpolate : C(I × I, I) := {
  to_fun := λ t, ⟨(σ t.1 : ℝ) * (f t.2) + t.1 * (g t.2), interp_mem_I t.1 (f t.2) (g t.2)⟩
}

lemma interpolate_left : (interpolate f g).curry 0 = f :=
begin
  ext,
  simp [interpolate],
end

lemma interpolate_right : (interpolate f g).curry 1 = g :=
begin
  ext,
  simp [interpolate],
end

lemma interpolate_constant (t v : I) (hf : f t = v) (hg : g t = v)  : ∀ x, interpolate f g (x, t) = v :=
begin
  intro x,
  simp [interpolate, hf, hg],
  ring_nf,
  apply subtype.coe_inj.mp,
  refl,
end

end

section

variables (f : D(I, I)) (g : D(I, I))

lemma directed_interpolate (h : ∀ t, f t ≤ g t) : directed_map.directed (interpolate f g) :=
begin
  intros t₀ t₁ γ γ_dipath x y hxy,

  let a₀ := (γ x).1,
  let a₁ := (γ x).2,
  let b₀ := (γ y).1,
  let b₁ := (γ y).2,

  have hfab : (f a₁ : ℝ) ≤ f b₁ := directed_unit_interval.monotone_of_directed f (γ_dipath.2 hxy),
  have hgab : (g a₁ : ℝ) ≤ g b₁ := directed_unit_interval.monotone_of_directed g (γ_dipath.2 hxy),
  have : 0 ≤ (g a₁ : ℝ) - (f a₁ : ℝ) := by simp [h],

  apply subtype.coe_le_coe.mp,
  calc (interpolate f g (γ x) : ℝ) = (1 - a₀ : ℝ) * (f a₁ : ℝ) + (a₀ : ℝ) * (g a₁ : ℝ) : rfl
                          ...  = ↑(f a₁) + ↑a₀ * (g a₁ - f a₁) : by ring
                          ...  ≤ ↑(f a₁) + ↑b₀ * (g a₁ - f a₁) : add_le_add_left (mul_le_mul_of_nonneg_right (γ_dipath.1 hxy) this) ↑(f a₁)
                          ...  = (1 - b₀ : ℝ) * (f a₁ : ℝ) + (b₀ : ℝ) * (g a₁ : ℝ) : by ring
                          ...  ≤ (1 - b₀ : ℝ) * (f b₁ : ℝ) + (b₀ : ℝ) * (g a₁ : ℝ) : add_le_add_right (mul_le_mul_of_nonneg_left hfab (by unit_interval)) ((b₀ : ℝ) * (g a₁ : ℝ))
                          ...  ≤ (1 - b₀ : ℝ) * (f b₁ : ℝ) + (b₀ : ℝ) * (g b₁ : ℝ) : add_le_add_left (mul_le_mul_of_nonneg_left hgab (by unit_interval)) ((1 - b₀ : ℝ) * (f b₁ : ℝ))
                          ...  = (interpolate f g (γ y) : ℝ) : rfl
end

end
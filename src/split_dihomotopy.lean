import directed_path_homotopy

/-
  This file contains the definitions of splitting a (dipath) dihomotopy both vertically and horizontally.

  Take a dihomotopy `F : f ~ g`, with `f g : D(I, X)`:
   *----- g -----*
   |             |
   |             |
   |             |
   |             |
   *----- f -----*

  Splitting vertically at `T : I` gives us:
    *----- g -----*
    |             |
    |             |
    *-- F.eval T -*
  and
    *-- F.eval T -*
    |             |
    |             |
    *----- f -----*
  
  Splitting horizontally at `T : I` gives us:
   *-- g₁ --*     *-- g₂ --*
   |        |     |        |
   |        | and |        |
   |        |     |        |
   |        |     |        |
   *-- f₁ --*     *-- f₂ --*
  Here f₁, f₂, g₁ and g₂ are obtained from f and g by splitting them at T : I.

  In the case that F is a dipath dihomotopy (it fixes endpoints), then splitting it vertically gives two dipath dihomotopies.
-/

open directed_map
open_locale unit_interval

namespace split_dihomotopy


variables {X : dTop}

def directed_first {T : I} (hT : 0 < T) : D(I, I) :=
{
  to_fun := λ t, ⟨(T : ℝ) * ↑t, unit_interval.mul_mem T.2 t.2⟩,
  directed_to_fun := λ x y γ hγ a b hab, (mul_le_mul_left (subtype.coe_lt_coe.mpr hT)).mpr (hγ hab),
}

def directed_second {T : I} (hT : T < 1) : D(I, I) :=
{
  to_fun := λ t, ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩,
  directed_to_fun :=
    begin
      intros x y γ hγ a b hab,
      simp,
      have : 1 - (T : ℝ) > 0 := sub_pos.mpr hT,
      exact (mul_le_mul_left this).mpr (hγ hab),
    end
}

/- Splitting a dipath-dihomotopy vertically -/
def first_part_vertically_dihomotopy {x y : X} {γ₁ γ₂ : dipath x y} (F : dipath.dihomotopy γ₁ γ₂) {T : I} (hT : 0 < T) :
  dipath.dihomotopy γ₁ (F.eval T) :=
{
  to_directed_map := F.to_directed_map.comp (directed_map.prod_map_mk' (directed_first hT) (directed_map.id I)),
  map_zero_left' :=
    begin
      intro x,
      show F (⟨(T : ℝ) * 0, _⟩, x) = γ₁ x,
      simp,
    end,
  map_one_left' :=
    begin
      intro x,
      show F (⟨(T : ℝ) * 1, _⟩, x) = F (T, x),
      simp,
    end,
  prop' :=
    begin
      intros t z hz,
      split,
      {
        show F (⟨(T : ℝ) * t, _⟩, z) = γ₁ z,
        exact (F.prop' _ z hz).1,
      },
      {
        show F (⟨(T : ℝ) * t, _⟩, z) = F (T, z),
        have : F (T, z) = _ := (F.prop' T z hz).2,
        rw this,
        exact (F.prop' _ z hz).2,
      }
    end
}

lemma fpv_apply {x y : X} {γ₁ γ₂ : dipath x y} (F : dipath.dihomotopy γ₁ γ₂) {T : I} (hT : 0 < T) (s t : I) :
  first_part_vertically_dihomotopy F hT (s, t) = F (T * s, t) := rfl

/- Splitting a dipath-dihomotopy vertically -/
def second_part_vertically_dihomotopy {x y : X} {γ₁ γ₂ : dipath x y} (F : dipath.dihomotopy γ₁ γ₂) {T : I} (hT : T < 1) :
  dipath.dihomotopy (F.eval T) γ₂ :=
{
  to_directed_map := F.to_directed_map.comp (directed_map.prod_map_mk' (directed_second hT) (directed_map.id I)),
  map_zero_left' :=
    begin
      intro x,
      show F (⟨(σ T : ℝ) * 0 + (T : ℝ), _⟩, x) = F (T, x),
      simp,
    end,
  map_one_left' :=
    begin
      intro x,
      show F (⟨(σ T : ℝ) * 1 + (T : ℝ), _⟩, x) = γ₂ x,
      simp,
    end,
  prop' :=
    begin
      intros t z hz,
      split,
      {
        show F (⟨_, _⟩, z) = F (T, z),
        have : F (T, z) = _ := (F.prop' T z hz).2,
        rw this,
        exact (F.prop' _ z hz).2,
      },
      {
        show F (⟨_, _⟩, z) = γ₂ _,
        exact (F.prop' _ z hz).2,
      }
    end
}

lemma spv_apply {x y : X} {γ₁ γ₂ : dipath x y} (F : dipath.dihomotopy γ₁ γ₂) {T : I} (hT : T < 1) (s t : I) :
  second_part_vertically_dihomotopy F hT (s, t) = F (⟨(σ T : ℝ) * (s : ℝ) + (T : ℝ), interp_left_mem_I T s⟩, t) := rfl

/- Splitting a dihomotopy horizontally -/
def first_part_horizontally_dihomotopy {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : 0 < T) :
  dihomotopy (split_dipath.first_part_dipath (dipath.of_directed_map f) hT).to_directed_map (split_dipath.first_part_dipath (dipath.of_directed_map g) hT).to_directed_map :=
{
  to_directed_map := F.to_directed_map.comp (directed_map.prod_map_mk' (directed_map.id I) (directed_first hT)),
  map_zero_left' :=
    begin
      intro x,
      show F (0, ⟨(T : ℝ) * x, _⟩) = _,
      simp,
      rw split_dipath.first_part_apply,
      refl,
    end,
  map_one_left' :=
    begin
      intro x,
      show F (1, ⟨(T : ℝ) * x, _⟩) = _,
      simp,
      rw split_dipath.first_part_apply,
      refl,
    end,
}

lemma fph_apply {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : 0 < T) (s t : I) :
  first_part_horizontally_dihomotopy F hT (s, t) = F (s, T * t) := rfl

/- Splitting a dihomotopy horizontally -/
def second_part_horizontally_dihomotopy {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : T < 1) :
  dihomotopy (split_dipath.second_part_dipath (dipath.of_directed_map f) hT).to_directed_map  (split_dipath.second_part_dipath (dipath.of_directed_map g) hT).to_directed_map :=
{
  to_directed_map := F.to_directed_map.comp (directed_map.prod_map_mk' (directed_map.id I) (directed_second hT)),
  map_zero_left' :=
    begin
      intro x,
      show F (0, ⟨(σ T : ℝ) * (x : ℝ) + (T : ℝ), _⟩) = _,
      simp,
      rw split_dipath.second_part_apply,
      refl,
    end,
  map_one_left' :=
    begin
      intro x,
      show F (1, ⟨(σ T : ℝ) * (x : ℝ) + (T : ℝ), _⟩) = _,
      simp,
      rw split_dipath.second_part_apply,
      refl,
    end,
}

lemma sph_apply {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : T < 1) (s t : I) :
  second_part_horizontally_dihomotopy F hT (s, t) = F (s, ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩) := rfl

lemma first_part_horizontally_eval_0 {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : 0 < T) :
  (first_part_horizontally_dihomotopy F hT).eval_at_right 0 = (F.eval_at_right 0).cast (by simp) (by simp) :=
begin
  ext t,
  show F (t, T * 0) = F (t, 0),
  rw mul_zero,
end

lemma first_part_horizontally_eval_1 {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : 0 < T) :
  (first_part_horizontally_dihomotopy F hT).eval_at_right 1 = (F.eval_at_right T).cast (by { simp, refl }) (by { simp, refl }) :=
begin
  ext t,
  show F (t, T * 1) = F (t, T),
  rw mul_one,
end

lemma second_part_horizontally_eval_0 {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : T < 1) :
  (second_part_horizontally_dihomotopy F hT).eval_at_right 0 = (F.eval_at_right T).cast (by { simp, refl }) (by { simp, refl }) :=
begin
  ext t,
  show F (t, ⟨(σ T : ℝ) * 0 + (T : ℝ), interp_left_mem_I T 0⟩) = F (t, T),
  simp,
end

lemma second_part_horizontally_eval_1 {f g : D(I, X)} (F : dihomotopy f g) {T : I} (hT : T < 1) :
  (second_part_horizontally_dihomotopy F hT).eval_at_right 1 = (F.eval_at_right 1).cast (by simp) (by simp) :=
begin
  ext t,
  show F (t, ⟨(σ T : ℝ) * 1 + (T : ℝ), interp_left_mem_I T 1⟩) = F (t, 1),
  simp,
end

end split_dihomotopy
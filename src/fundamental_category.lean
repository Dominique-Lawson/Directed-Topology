import category_theory.category.basic
import category_theory.category.Cat
import directed_path_homotopy
import algebraic_topology.fundamental_groupoid.basic

/-
  This file contains the definition of the fundamental category of a directed space.
  We follow the structure of the undirected version found at:
  https://leanprover-community.github.io/mathlib_docs/algebraic_topology/fundamental_groupoid/basic.html#fundamental_groupoid
-/
open directed_map

universes u v
variables {X : Type u} {Y : Type v} [directed_space X] [directed_space Y] {x₀ x₁ : X}

open_locale unit_interval

noncomputable theory

namespace dipath

namespace dihomotopy

open path.homotopy

section assoc

lemma directed_trans_assoc_reparam_aux : directed_map.directed
  ({ to_fun := λ t, ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩} : C(I, I)) :=
begin
  apply directed_unit_interval.directed_of_monotone _,
  intros x y hxy,
  unfold trans_assoc_reparam_aux,
  simp,
  have : (x : ℝ) ≤ (y : ℝ) := hxy,
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅,
  { linarith, },
  { linarith, },
  {
    push_neg at h₂,
    have : 0 ≤ (y : ℝ) := le_trans (by norm_num) (le_of_lt h₂),
    have : 1 ≤ (y : ℝ) + 1 := by linarith,
    calc 2 * (x : ℝ) ≤ 2 * 4⁻¹ : (mul_le_mul_left (by norm_num)).mpr h₀
            ... = (2⁻¹ : ℝ) * 1 : by norm_num
            ... ≤ (2⁻¹ : ℝ) * (↑y + 1) : (mul_le_mul_left (by norm_num)).mpr this,
  },
  { linarith, },
  { linarith, },
  {
    push_neg at h₅,
    calc (x : ℝ) + (4⁻¹ : ℝ) ≤ 2⁻¹ + 4⁻¹ : add_le_add_right h₃ 4⁻¹
                      ... = 2⁻¹ * (2⁻¹ + 1) : by norm_num
                      ... ≤ 2⁻¹ * (↑y + 1) : (mul_le_mul_left (by norm_num)).mpr (add_le_add_right (le_of_lt h₅) 1)
  },
  { linarith, },
  { linarith, },
  {
    apply (mul_le_mul_left (show 0 < (2⁻¹ : ℝ), by norm_num)).mpr,
    apply add_le_add_right,
    exact hxy,
  },
end

def trans_assoc_reparam_aux_map : D(I, I) := {
  to_fun := λ t, ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩,
  directed_to_fun := directed_trans_assoc_reparam_aux
}

lemma trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : dipath x₀ x₁) (q : dipath x₁ x₂) (r : dipath x₂ x₃) :
  (p.trans q).trans r = (p.trans (q.trans r)).reparam
    trans_assoc_reparam_aux_map
    (subtype.ext trans_assoc_reparam_aux_zero)
    (subtype.ext trans_assoc_reparam_aux_one) :=
begin
  ext t,
  have : (p.trans q).trans r t =  (p.to_path.trans q.to_path).trans r.to_path t := rfl,
  rw this,
  rw trans_assoc_reparam p.to_path q.to_path r.to_path,
  refl,
end

/--
For any three dipaths `p q r`, `(p.trans q).trans r` is dihomotopic with `p.trans (q.trans r)`.
-/
def trans_assoc {x₀ x₁ x₂ x₃ : X} (p : dipath x₀ x₁) (q : dipath x₁ x₂) (r : dipath x₂ x₃) :
  ((p.trans q).trans r).dihomotopic (p.trans (q.trans r)) :=
begin
  have := dihomotopic.reparam (p.trans (q.trans r)) trans_assoc_reparam_aux_map (subtype.ext trans_assoc_reparam_aux_zero)
    (subtype.ext trans_assoc_reparam_aux_one),
  rw ←trans_assoc_reparam at this,
  exact dipath.dihomotopic.equivalence.2.1 this,
end

end assoc

end dihomotopy

end dipath

/-
 - Definition of the fundamental category and of the functor sending a directed space to its
 - fundamental category
-/

def fundamental_category (X : Type u) := X

namespace fundamental_category

instance {X : Type u} [h : inhabited X] : inhabited (fundamental_category X) := h

local attribute [reducible] fundamental_category
local attribute [instance] dipath.dihomotopic.setoid

instance : category_theory.category (fundamental_category X) :=
{
    hom := λ x y, dipath.dihomotopic.quotient x y,
    id := λ x, ⟦dipath.refl x⟧,
    comp := λ x y z, dipath.dihomotopic.quotient.comp,
    id_comp' := λ x y f, quotient.induction_on f
      (λ a, show ⟦(dipath.refl x).trans a⟧ = ⟦a⟧,
            from quotient.sound (eqv_gen.rel _ _ ⟨dipath.dihomotopy.refl_trans a⟩)),
    comp_id' := λ x y f, quotient.induction_on f
      (λ a, show ⟦a.trans (dipath.refl y)⟧ = ⟦a⟧,
            from quotient.sound (dipath.dihomotopic.equivalence.2.1 $ eqv_gen.rel _ _ ⟨dipath.dihomotopy.trans_refl a⟩)),
    assoc' := λ w x y z f g h, quotient.induction_on₃ f g h
      (λ p q r, show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧,
                from quotient.sound (dipath.dihomotopy.trans_assoc p q r)),
}

lemma comp_eq (x y z : fundamental_category X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.comp q := rfl

lemma id_eq_path_refl (x : fundamental_category X) : 𝟙 x = ⟦dipath.refl x⟧ := rfl

def fundamental_category_functor : dTop ⥤ category_theory.Cat :=
{
  obj := λ X, { α := fundamental_category X, },
  map := λ X Y f,
    { /- Functor from Π(X) to Π(Y) -/
      obj := f,
      map := λ x y p, p.map_fn f,
      map_id' := λ X, rfl,
      map_comp' := λ x y z p q, quotient.induction_on₂ p q $ λ a b,
        by simp [comp_eq, ← dipath.dihomotopic.map_lift, ← dipath.dihomotopic.comp_lift],
    },
  map_id':= begin
    intro X,
    change _ = (⟨_, _, _, _⟩ : fundamental_category X ⥤ fundamental_category X),
    congr',
    ext x y p,
    refine quotient.induction_on p (λ q, _),
    rw [← dipath.dihomotopic.map_lift],
    conv_rhs { rw [←q.map_id] },
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    congr',
    ext x y p,
    refine quotient.induction_on p (λ q, _),
    simp only [quotient.map_mk, dipath.map_map, quotient.eq],
    refl,
  end,
}

localized "notation (name := fundamental_category_functor)
  `dπ` := fundamental_category.fundamental_category_functor" in fundamental_category
localized "notation (name := fundamental_category_functor.obj)
  `dπₓ` := fundamental_category.fundamental_category_functor.obj" in fundamental_category
localized "notation (name := fundamental_category_functor.map)
  `dπₘ` := fundamental_category.fundamental_category_functor.map" in fundamental_category

lemma map_eq {X Y : dTop} {x₀ x₁ : X} (f : D(X, Y)) (p : dipath.dihomotopic.quotient x₀ x₁) :
  (dπₘ f).map p = p.map_fn f := rfl

/-- Help the typechecker by converting a point in the fundamental category back to a point in
the underlying directed space. -/
@[reducible]
def to_top {X : dTop} (x : dπₓ X) : X := x

/-- Help the typechecker by converting a point in a directed space to a
point in the fundamental category of that space -/
@[reducible]
def from_top {X : dTop} (x : X) : dπₓ X := x

/-- Help the typechecker by converting an arrow in the fundamental category of
a directed space back to a directed path in that space (i.e., `dipath.dihomotopic.quotient`). -/
@[reducible]
def to_path {X : dTop} {x₀ x₁ : dπₓ X} (p : x₀ ⟶ x₁) :
  dipath.dihomotopic.quotient x₀ x₁ := p

/-- Help the typechecker by convering a directed path in a directed space to an arrow in the
fundamental category of that space. -/
@[reducible]
def from_path {X : dTop} {x₀ x₁ : X} (p : dipath.dihomotopic.quotient x₀ x₁) : (x₀ ⟶ x₁) := p

end fundamental_category
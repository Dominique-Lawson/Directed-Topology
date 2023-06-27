import directed_homotopy
import trans_refl
import topology.homotopy.path

/-
  This file contains the definition of a directed path homotopy, or `dipath.dihomotopy`:
  It is a dihomotopy between two paths that keeps the endpoints fixed.

  We prove a few constructions and define the equivalence relation `dihomtopic` between two paths.
  We show that this relation is closed under reparametrizations, and that concatenation and directed maps respect it.

  Much of the structure of this file is based on the undirected version:
  https://github.com/leanprover-community/mathlib/blob/master/src/topology/homotopy/path.lean
-/
universes u v

open directed_unit_interval auxiliary

variables {X : Type u} {Y : Type v}
variables [directed_space X] [directed_space Y]
variables {x₀ x₁ x₂ x₃ : X}

noncomputable theory

open_locale unit_interval

namespace dipath

/--
The type of dihomotopies between two directed paths.
-/
abbreviation dihomotopy (p₀ p₁ : dipath x₀ x₁) :=
directed_map.dihomotopy_rel p₀.to_directed_map p₁.to_directed_map {0, 1}

namespace dihomotopy

section

variables {p₀ p₁ : dipath x₀ x₁}

instance : has_coe_to_fun (dihomotopy p₀ p₁) (λ _, I × I → X) := ⟨λ F, F.to_fun⟩

lemma coe_fn_injective : @function.injective (dihomotopy p₀ p₁) (I × I → X) coe_fn :=
directed_map.dihomotopy_with.coe_fn_injective

@[simp]
lemma source (F : dihomotopy p₀ p₁) (t : I) : F (t, 0) = x₀ :=
begin
  simp_rw [←p₀.source],
  rw ←dipath.coe_to_directed_map,
  apply directed_map.dihomotopy_rel.eq_fst,
  simp,
end

@[simp]
lemma target (F : dihomotopy p₀ p₁) (t : I) : F (t, 1) = x₁ :=
begin
  simp_rw [←p₁.target],
  rw ←dipath.coe_to_directed_map,
  apply directed_map.dihomotopy_rel.eq_snd,
  simp,
end

/-- A `F : homotopy ↑p₁ ↑p₂` between two dipaths `p₁ p₂ : dipath x₁ x₂` can be coerced into a dihomotopy,
  if it is directed -/
def hom_to_dihom (F : path.homotopy p₀.to_path p₁.to_path)
  (HF : directed_map.directed F.to_continuous_map) : dihomotopy p₀ p₁ :=
{
  to_fun := F.to_fun,
  continuous_to_fun := F.continuous_to_fun,
  directed_to_fun := HF,
  map_zero_left' := F.map_zero_left',
  map_one_left' := F.map_one_left',
  prop' := F.prop',
}

/-- A dihomotopy `F` between two dipaths `p₁ p₂` can be coerced into a homotopy between `p₀.to_path` 
 and `p₁.to_path`-/
def dihom_to_hom (F : dihomotopy p₀ p₁) : path.homotopy p₀.to_path p₁.to_path:=
{
  to_fun := F.to_fun,
  continuous_to_fun := F.continuous_to_fun,
  map_zero_left' := F.map_zero_left',
  map_one_left' := F.map_one_left',
  prop' := F.prop'
}

instance coe_dihom_to_hom : has_coe (dihomotopy p₀ p₁) (path.homotopy p₀.to_path p₁.to_path) := ⟨λ F, F.dihom_to_hom⟩


/--
Evaluating a dipath homotopy at an intermediate point, giving us a `dipath`.
-/
def eval (F : dihomotopy p₀ p₁) (t : I) : dipath x₀ x₁ :=
{
  to_fun := F.to_dihomotopy.curry t,
  source' := by simp,
  target' := by simp,
  dipath_to_path := directed_unit_interval.is_dipath_of_is_dipath_comp_id
    $ (F.to_dihomotopy.curry t).directed_to_fun directed_unit_interval.identity_path directed_unit_interval.identity_dipath
}

@[simp] lemma coe_eval (F : dihomotopy p₀ p₁) (t : I) : (⇑(F.eval t) : I → X)  = ⇑(F.to_dihomotopy.curry t) := rfl

@[simp]
lemma eval_zero (F : dihomotopy p₀ p₁) : F.eval 0 = p₀ :=
begin
  ext t,
  simp [eval],
end

@[simp]
lemma eval_one (F : dihomotopy p₀ p₁) : F.eval 1 = p₁ :=
begin
  ext t,
  simp [eval],
end

end

section
variables {p₀ p₁ p₂ : dipath x₀ x₁}

/--
Given a dipath `p`, we can define a `dihomotopy p p` by `F (t, x) = p x`
-/
@[simps]
def refl (p : dipath x₀ x₁) : dihomotopy p p :=
directed_map.dihomotopy_rel.refl p {0, 1}

/--
Given `dihomotopy p₀ p₁` and `dihomotopy p₁ p₂`, we can define a `dihomotopy p₀ p₂` by putting the first
dihomotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : dihomotopy p₀ p₁) (G : dihomotopy p₁ p₂) : dihomotopy p₀ p₂ :=
directed_map.dihomotopy_rel.trans F G

lemma trans_apply (F : dihomotopy p₀ p₁) (G : dihomotopy p₁ p₂) (x : I × I) :
  (F.trans G) x =
    if h : (x.1 : ℝ) ≤ 1/2 then
      F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
    else
      G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
directed_map.dihomotopy_rel.trans_apply _ _ _

/--
Casting a `dihomotopy p₀ p₁` to a `dihomotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
-- @[simps]
def cast {p₀ p₁ q₀ q₁ : dipath x₀ x₁} (F : dihomotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
  dihomotopy q₀ q₁ := directed_map.dihomotopy_rel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

end

section

variables {p₀ q₀ : dipath x₀ x₁} {p₁ q₁ : dipath x₁ x₂}

section hcomp_aux

variables (F : dihomotopy p₀ q₀) (G: dihomotopy p₁ q₁) (s t : I) (ht: t = half_I)

lemma hcomp_apply_half_left (ht: t = half_I) : (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = F (s, 1) :=
begin
  rw path.homotopy.hcomp_apply,
  have ht_coe : (t : ℝ) = 2⁻¹ := subtype.coe_inj.mpr ht,
  have : (t : ℝ) ≤ 2⁻¹ := by linarith,
  simp [this],
  simp [ht_coe],
end
  
lemma hcomp_apply_half_right (ht: t = half_I) : (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = G (s, 0) :=
begin
  rw path.homotopy.hcomp_apply,
  have ht_coe : (t : ℝ) = 2⁻¹ := subtype.coe_inj.mpr ht,
  split_ifs; simp [ht_coe]
end

lemma hcomp_apply_left (ht : (t : ℝ) ≤ 2⁻¹) :
  (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = F (s, ⟨2 * t, double_mem_I ht⟩) :=
begin
  rw path.homotopy.hcomp_apply,
  simp [ht],
  refl,
end

lemma hcomp_apply_right (ht : 2⁻¹ ≤ (t : ℝ)) :
  (dihom_to_hom F).hcomp (dihom_to_hom G) (s, t) = G (s, ⟨2 * t - 1, double_sub_one_mem_I ht⟩) :=
begin
  rw path.homotopy.hcomp_apply,
  simp [ht],
  split_ifs,
  {
    have : (t : ℝ) = 2⁻¹ := by linarith,
    simp [this],
  },
  refl,
end

lemma hcomp_first_case (F : dihomotopy p₀ q₀) (G : dihomotopy p₁ q₁) {a₀ a₁ : I × I} {γ : path a₀ a₁} (γ_dipath : is_dipath γ) (ht₁ : (a₁.2 : ℝ) ≤ 2⁻¹) :
  is_dipath (γ.map ((dihom_to_hom F).hcomp (dihom_to_hom G)).continuous_to_fun) :=
begin
  obtain ⟨s₀, t₀⟩ := a₀,
  obtain ⟨s₁, t₁⟩ := a₁,

  set Γ := (dihom_to_hom F).hcomp (dihom_to_hom G) with Γ_def,

  set γ₁ : dipath s₀ s₁ :=
    {
      to_path := γ.map continuous_fst,
      dipath_to_path := γ_dipath.1
    } with γ₁_def,

  set γ₂ : dipath t₀ t₁ :=
    {
      to_path := γ.map continuous_snd,
      dipath_to_path := γ_dipath.2
    } with γ₂_def,

  set p := dipath.dipath_product γ₁ (dipath.stretch_up γ₂ ht₁)  with p_def,
  set p' := p.map (F.to_directed_map) with p'_def,

  have h : ∀ (s t : I), ((t : ℝ) ≤ 2⁻¹) →
    Γ (s, t) = F (s, ⟨2 * (t : ℝ), double_mem_I ᾰ⟩),
  {
    intros s t ht,
    rw Γ_def,
    rw path.homotopy.hcomp_apply (dihom_to_hom F) (dihom_to_hom G) (s, t),
    simp [ht],
    refl,
  },
  
  have ht₀ : (t₀ : ℝ) ≤ 2⁻¹ := le_trans (subtype.coe_le_coe.mp (directed_path_source_le_target γ_dipath.2)) ht₁,
  convert (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_to_path,
  ext,
  simp,
  exact h _ _ (le_trans (directed_path_bounded γ_dipath.2).2 ht₁),
end

lemma hcomp_second_case (F : dihomotopy p₀ q₀) (G : dihomotopy p₁ q₁) {a₀ a₁ : I × I} {γ : path a₀ a₁} (γ_dipath : is_dipath γ) (ht₀ : 2⁻¹ ≤ (a₀.2 : ℝ)) :
  is_dipath (γ.map ((dihom_to_hom F).hcomp (dihom_to_hom G)).continuous_to_fun) :=
begin
  obtain ⟨s₀, t₀⟩ := a₀,
  obtain ⟨s₁, t₁⟩ := a₁,

  set Γ := (dihom_to_hom F).hcomp (dihom_to_hom G) with Γ_def,

  set γ₁ : dipath s₀ s₁ :=
    {
      to_path := γ.map continuous_fst,
      dipath_to_path := γ_dipath.1
    } with γ₁_def,

  set γ₂ : dipath t₀ t₁ :=
    {
      to_path := γ.map continuous_snd,
      dipath_to_path := γ_dipath.2
    } with γ₂_def,

      set p := dipath.dipath_product γ₁ (dipath.stretch_down γ₂ ht₀) with p_def,
      set p' := p.map G.to_directed_map with p'_def,
     
      have h : ∀ (s t : I), ((2⁻¹ : ℝ) ≤ ↑t) →
        Γ (s, t) = G (s, ⟨2 * (t : ℝ) - 1, double_sub_one_mem_I ᾰ⟩),
      {
        intros s t ht,
        rw Γ_def,
        rw path.homotopy.hcomp_apply (dihom_to_hom F) (dihom_to_hom G) (s, t),
        split_ifs with ht',
        {
          simp at ht',
          have : ↑t = (2⁻¹ : ℝ) := by linarith,
          simp [this],
        },
        refl,
      },

      have ht₁ : 2⁻¹ ≤ (t₁ : ℝ) := le_trans ht₀ (subtype.coe_le_coe.mp (directed_path_source_le_target γ_dipath.2)),
      convert (p'.cast (h s₀ t₀ ht₀) (h s₁ t₁ ht₁)).dipath_to_path,
      ext,
      simp,
      exact h (γ x).1 (γ x).2 (le_trans ht₀ (directed_path_bounded γ_dipath.2).1),
end

end hcomp_aux

/--
Suppose `p₀` and `q₀` are dipaths from `x₀` to `x₁`, `p₁` and `q₁` are dipaths from `x₁` to `x₂`.
Furthermore, suppose `F : dihomotopy p₀ q₀` and `G : dihomotopy p₁ q₁`. Then we can define a dihomotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : dihomotopy p₀ q₀) (G : dihomotopy p₁ q₁) : dihomotopy (p₀.trans p₁) (q₀.trans q₁) :=
begin
  set Fₕ := dihom_to_hom F with Fₕ_def,
  set Gₕ := dihom_to_hom G with Gₕ_def,
  set Γ := Fₕ.hcomp Gₕ with Γ_def,
  have : directed_map.directed Γ.to_continuous_map :=
    begin
      rintros ⟨s₀, t₀⟩ ⟨s₁, t₁⟩ γ γ_dipath,

      set γ_as_dipath : dipath (s₀, t₀) (s₁, t₁) :=
        {
          to_path := γ,
          dipath_to_path := γ_dipath
        } with γ_as_dipath_def,

      set γ₁ : dipath s₀ s₁ :=
        {
          to_path := γ.map continuous_fst,
          dipath_to_path := γ_dipath.1
        } with γ₁_def,

      set γ₂ : dipath t₀ t₁ :=
        {
          to_path := γ.map continuous_snd,
          dipath_to_path := γ_dipath.2
        } with γ₂_def,

    by_cases ht₁ : (↑t₁ : ℝ) ≤ 2⁻¹,
    { -- The entire path falls in the domain of F
      exact hcomp_first_case F G γ_dipath ht₁,
    },

    by_cases ht₀ : (↑t₀ : ℝ) < 2⁻¹,
    tactic.swap,
    { -- The entire path falls in the domain of G
      have ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀ := by linarith,
      exact hcomp_second_case F G γ_dipath ht₀,
    },
    
    {
    -- Complicated 
    push_neg at ht₁,
    cases has_T_half (γ.map continuous_snd) ht₀ ht₁ with T hT,
    obtain ⟨hT₀, ⟨hT₁, hT_half⟩⟩ := hT,

    /- Split γ into two parts (one with image in I × [0, 2⁻¹], the other with image in I × [2⁻¹, 1])-/
    set a₁ := split_dipath.first_part_dipath γ_as_dipath hT₀ with a₁_def,
    set a₂ := split_dipath.second_part_dipath γ_as_dipath hT₁ with a₂_def,

    /- Create two new paths, where the first coordinate is stretched and the second coordinate remains the same -/
    set p₁ := split_dipath.first_part_dipath γ₁ hT₀ with p₁_def,
    set p₂ := split_dipath.second_part_dipath γ₁ hT₁ with p₂_def,

    set p₁' := directed_map.dihomotopy.first_part_stretch γ₂ hT₀ hT₁ (le_of_lt ht₀) hT_half with p₁_def,
    set p₂' := directed_map.dihomotopy.second_part_stretch γ₂ hT₀ hT₁ (le_of_lt ht₁) hT_half with p₂_def,

    set q₁ := (dipath.dipath_product p₁ p₁').map F.to_directed_map with q₁_def,
    set q₂ := (dipath.dipath_product p₂ p₂').map G.to_directed_map with q₂_def,

    set φ := split_dipath.trans_reparam_map hT₀ hT₁ with φ_def,
    have φ₀ : φ 0 = 0 := subtype.ext (split_path.trans_reparam_zero T),
    have φ₁ : φ 1 = 1 := subtype.ext (split_path.trans_reparam_one hT₁),

    have hγT_le_half : ((γ T).2 : ℝ) ≤ 2⁻¹ := subtype.coe_le_coe.mpr (le_of_eq hT_half),
    have hγT_eq_half : ((γ T).2 : ℝ) = 2⁻¹ := subtype.coe_inj.mpr (hT_half),

    set r₁ := q₁.cast (hcomp_apply_left F G s₀ t₀ (le_of_lt ht₀)) (hcomp_apply_half_left F G (γ T).1 (γ T).2 hT_half),
    set r₂ := q₂.cast (hcomp_apply_half_right F G (γ T).1 (γ T).2 hT_half) (hcomp_apply_right F G s₁ t₁ (le_of_lt ht₁)),

    convert ((r₁.trans r₂).reparam φ φ₀ φ₁).dipath_to_path,
    ext t,

    have hr₁a₁ : r₁.to_path = a₁.to_path.map Γ.continuous_to_fun,
    {
      ext x,
      have : ((a₁ x).2 : ℝ) ≤ 2⁻¹ := le_trans (directed_path_bounded a₁.dipath_to_path.2).2 hγT_le_half,
      calc r₁ x = F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), double_mem_I this⟩) : rfl
        ... = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then F ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩)
                else G ((a₁ x).1, ⟨2 * ((a₁ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩)
              : by simp [this]
        ... = if h : ((a₁ x).2 : ℝ) ≤ 1/2
                then Fₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩
                else Gₕ.eval (a₁ x).1 ⟨2 * ((a₁ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩ : rfl
        ... = (Fₕ.hcomp Gₕ) (a₁ x) : (path.homotopy.hcomp_apply Fₕ Gₕ (a₁ x)).symm
        ... = Γ (a₁ x) : by rw Γ_def
        ... = (a₁.to_path.map Γ.continuous_to_fun) x : rfl
    },
    have hr₂a₂ : r₂.to_path = a₂.to_path.map Γ.continuous_to_fun,
    {
      ext,
      have : 2⁻¹ ≤ ((a₂ x).2 : ℝ),
      {
        calc (2⁻¹ : ℝ) = ↑(γ T).2 : subtype.coe_inj.mpr hT_half.symm
                   ... ≤  ↑(a₂ x).2 : (directed_path_bounded a₂.dipath_to_path.2).1
      },
      calc r₂.to_path x = G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1, double_sub_one_mem_I this⟩) : rfl
            ... = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                    then F ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩)
                    else G ((a₂ x).1, ⟨2 * ((a₂ x).2 : ℝ) - 1,  by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩) :
                      by {
                            split_ifs with h,
                            {
                              simp at h,
                              have ha₂x : ((a₂ x).2 : ℝ) = 2⁻¹ := by linarith,
                              simp [ha₂x],
                            },
                            refl,
                         }
            ... = if h : ((a₂ x).2 : ℝ) ≤ 1/2
                    then Fₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ), by { apply double_mem_I, convert h, norm_num }⟩
                    else Gₕ.eval (a₂ x).1 ⟨2 * ((a₂ x).2 : ℝ) - 1, by { apply double_sub_one_mem_I (le_of_lt _), convert h, norm_num }⟩ : rfl
            ... = (Fₕ.hcomp Gₕ) (a₂ x) : (path.homotopy.hcomp_apply Fₕ Gₕ (a₂ x)).symm
            ... = Γ (a₂ x) : by rw Γ_def
            ... = (a₂.to_path.map Γ.continuous_to_fun) x : rfl
    },
    calc (Γ ∘ γ) t = Γ (γ t) : rfl
          ...    = Γ (((a₁.trans a₂).reparam φ φ₀ φ₁) t) : by { rw ←split_dipath.first_trans_second_reparam_eq_self γ_as_dipath hT₀ hT₁, refl }
          ...    = ((a₁.trans a₂).to_path.map Γ.continuous_to_fun).reparam φ φ.continuous_to_fun φ₀ φ₁ t : by refl
          ...    = ((a₁.to_path.trans a₂.to_path).map Γ.continuous_to_fun).reparam φ φ.continuous_to_fun φ₀ φ₁ t : by refl
          ...    = ((a₁.to_path.map Γ.continuous_to_fun).trans (a₂.to_path.map Γ.continuous_to_fun)).reparam φ φ.continuous_to_fun φ₀ φ₁ t :
                                                                            by rw path.map_trans a₁.to_path a₂.to_path (Γ.continuous_to_fun)
          ...    = (r₁.to_path.trans r₂.to_path).reparam φ φ.continuous_to_fun φ₀ φ₁ t : by rw [hr₁a₁, hr₂a₂]
          ...    = (r₁.trans r₂).reparam φ φ₀ φ₁ t : by refl
    }
    end,
  exact hom_to_dihom Γ this,
end

lemma hcomp_apply (F : dihomotopy p₀ q₀) (G : dihomotopy p₁ q₁) (x : I × I) :
  F.hcomp G x =
  if h : (x.2 : ℝ) ≤ 1/2 then
    F.eval x.1 ⟨2 * x.2, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
  else
    G.eval x.1 ⟨2 * x.2 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
show ite _ _ _ = _, by split_ifs; exact path.extend_extends _ _

lemma hcomp_half (F : dihomotopy p₀ q₀) (G : dihomotopy p₁ q₁) (t : I) :
  F.hcomp G (t, ⟨1/2, by norm_num, by norm_num⟩) = x₁ :=
show ite _ _ _ = _, by norm_num

end

/--
Suppose `p` is a dipath, and `f g : D(I, I)` two monotonic subparametrizations. If `f` is dominated by `g`, i.e. `∀ t, f t ≤ g t`,
then we obtain a dihomotopy between the two subparametrization of `p` as the interpolation between the two becomes directed.
-/
def reparam (p : dipath x₀ x₁) (f : D(I, I)) (g : D(I, I)) (hf_le_g : ∀ (t : I), f t ≤ g t) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) (hg₀ : g 0 = 0) (hg₁ : g 1 = 1):
  dihomotopy (p.reparam f hf₀ hf₁) (p.reparam g hg₀ hg₁) :=
{ to_fun := p.comp (interpolate f g),
  map_zero_left' := λ x, by {unfold interpolate, norm_num},
  map_one_left' := λ x, by {unfold interpolate, norm_num},
  prop' := λ t x hx, 
    begin
      simp,
      cases hx,
      {
        have : g 0 = f 0 := hg₀.trans (hf₀.symm),
        rw hx,
        split,
        calc (p ((interpolate f g) (t, 0))) = p (f 0) : by rw (interpolate_constant f g 0 (f 0) rfl this t),
        calc (p ((interpolate f g) (t, 0))) = p (g 0) : by rw (interpolate_constant f g 0 (g 0) this.symm rfl t),
      },
      {
        have : g 1 = f 1 := hg₁.trans (hf₁.symm),
        rw set.mem_singleton_iff at hx,
        rw hx,
        split,
        calc (p ((interpolate f g) (t, 1))) = p (f 1) : by rw (interpolate_constant f g 1 (f 1) rfl this t),
        calc (p ((interpolate f g) (t, 1))) = p (g 1) : by rw (interpolate_constant f g 1 (g 1) this.symm rfl t),
      }
    end,
  directed_to_fun := λ t₀ t₁ γ γ_dipath,
    (p.to_directed_map).directed_to_fun (γ.map _) (directed_interpolate f g hf_le_g γ γ_dipath),
}

/--
For any `p : dipath x₀ x₁`, there is a dihomotopy from `p` to `p.trans (dipath.refl x₁)`.
-/
def trans_refl (p : dipath x₀ x₁) : dihomotopy p (p.trans (dipath.refl x₁)) :=
begin
  set f : D(I, I) := directed_map.id I with f_def,
  set g : D(I, I) := trans_refl_reparam_aux_map with g_def,
  have hf_le_g : ∀ (t : I), f t ≤ g t :=
    begin
      intro t,
      simp [g_def, trans_refl_reparam_aux_map, path.homotopy.trans_refl_reparam_aux],
      apply subtype.coe_le_coe.mp,
      show (t : ℝ) ≤ ite ((t : ℝ) ≤ 2⁻¹) (2 * ↑t) 1,
      split_ifs,
      {
        have : 0 ≤ (t : ℝ) := t.2.1,
        linarith,
      },
      { exact t.2.2 }
    end,
  have := reparam p f g hf_le_g (by simp) (by simp)
    (subtype.ext path.homotopy.trans_refl_reparam_aux_zero)
    (subtype.ext path.homotopy.trans_refl_reparam_aux_one),
  convert this,
  { ext, refl },
  { exact trans_refl_reparam p }
end

/--
For any `p : dipath x₀ x₁`, there is a dihomotopy from `(dipath.refl x₀).trans p` to `p`.
-/
def refl_trans (p : dipath x₀ x₁) : dihomotopy ((dipath.refl x₀).trans p) p :=
begin
  set f : D(I, I) := refl_trans_reparam_aux_map with f_def,
  set g : D(I, I) := directed_map.id I with g_def,
  have hf_le_g : ∀ (t : I), f t ≤ g t :=
    begin
      intro t,
      simp [f_def, refl_trans_reparam_aux_map, refl_trans_reparam_aux],
      apply subtype.coe_le_coe.mp,
      show ite ((t : ℝ) ≤ 2⁻¹) 0 (2 * ↑t - 1) ≤ (t : ℝ),
      split_ifs,
      {
        exact t.2.1
      },
      {
        have : (t : ℝ) ≤ 1 := t.2.2,
        linarith,
      }
    end,
  have := reparam p f g hf_le_g (subtype.ext refl_trans_reparam_aux_zero)
    (subtype.ext refl_trans_reparam_aux_one) (by simp) (by simp),
  convert this,
  { exact refl_trans_reparam_dipath p },
  { ext, refl }
end

/--
  For any `p : dipath x₀ x₁`, there is a homotopy from `(dipath.refl x₀).trans p` to `q.trans (dipath.refl x₁)`, where 
  `q` is any directed reparametrization of `p`.
-/
def refl_trans_to_reparam_trans_refl (p : dipath x₀ x₁) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) : 
  dihomotopy ((dipath.refl x₀).trans p) ((p.reparam f hf₀ hf₁).trans (dipath.refl x₁)) :=
begin
  set φ₁ : D(I, I) := refl_trans_reparam_aux_map with φ₁_def,
  set φ₂ : D(I, I) := f.comp trans_refl_reparam_aux_map with φ₂_def,

  have hφ₁_le_φ₂ : ∀ (t : I), φ₁ t ≤ φ₂ t :=
    begin
      intro t,
      simp [φ₁_def, refl_trans_reparam_aux_map, refl_trans_reparam_aux],
      simp [φ₂_def, trans_refl_reparam_aux_map, path.homotopy.trans_refl_reparam_aux],
      apply subtype.coe_le_coe.mp,
      show ite ((t : ℝ) ≤ 2⁻¹) 0 (2 * (t : ℝ) - 1) ≤ (f ⟨ite ((t : ℝ) ≤ 2⁻¹) (2 * t : ℝ) 1, _⟩ : ℝ),
      by_cases h : (t : ℝ) ≤ 2⁻¹; simp [h],
      {  exact (f _).2.1 },
      { have : (t : ℝ) ≤ 1 := t.2.2,
        simp [hf₁],
        linarith,
      }
    end,

  have hφ₂₀ : φ₂ 0 = 0,
  {
    simp [trans_refl_reparam_aux_map],
    show f ⟨path.homotopy.trans_refl_reparam_aux 0, _⟩ = 0,
    convert hf₀,
    exact path.homotopy.trans_refl_reparam_aux_zero,
  },
  have hφ₂₁ : φ₂ 1 = 1,
  {
    simp [trans_refl_reparam_aux_map],
    show f ⟨path.homotopy.trans_refl_reparam_aux 1, _⟩ = 1,
    convert hf₁,
    exact path.homotopy.trans_refl_reparam_aux_one,
  },

  have := reparam p φ₁ φ₂ hφ₁_le_φ₂ (subtype.ext refl_trans_reparam_aux_zero) (subtype.ext refl_trans_reparam_aux_one) hφ₂₀ hφ₂₁,
  convert this,
  { exact refl_trans_reparam_dipath p },
  {
    rw trans_refl_reparam (p.reparam f hf₀ hf₁),
    ext,
    refl,
  },
end


/--
Given `F : dihomotopy p q`, and `f : D(X, Y)`, there is a dihomotopy from `p.map f.continuous` to
`q.map f.continuous` given by `f ∘ F`.
-/
@[simps]
def map {p q : dipath x₀ x₁} (F : p.dihomotopy q) (f : D(X, Y)) :
  dihomotopy (p.map f) (q.map f) :=
{ to_fun := f ∘ F,
  map_zero_left' := by simp,
  map_one_left' := by simp,
  prop' := λ t x hx, begin
    unfold directed_map.prod_const_fst directed_map.prod_map_mk,
    cases hx,
    { simp [hx],
      calc (f (F (t ,0))) = (f x₀) : by simp,
    },
    { rw set.mem_singleton_iff at hx,
      simp [hx],
      calc (f (F (t ,1))) = (f x₁) : by simp,
    },
  end,
  directed_to_fun := (f.comp F.to_directed_map).directed_to_fun,
}

end dihomotopy


section

variables (p₀ p₁ : dipath x₀ x₁)
/--
Two dipaths `p₀` and `p₁` are `dipath.pre_dihomotopic` if there exists a `dihomotopy` from `p₀` to `p₁`.
-/
def pre_dihomotopic : Prop := nonempty (dihomotopy p₀ p₁)

/--
`dipath.dihomotopic` is the equivalence generated by `dipath.pre_dihomotopic`.
-/
def dihomotopic : Prop := eqv_gen pre_dihomotopic p₀ p₁

end

namespace dihomotopic

lemma equivalence : equivalence (@dihomotopic X _ x₀ x₁) := by apply eqv_gen.is_equivalence

/-- If `p` is dihomotopic with `q`, then `f ∘ p` is dihomotopic with `f ∘ q` for any directed map `f` -/
lemma map {p q : dipath x₀ x₁} (h : p.dihomotopic q) (f : D(X, Y)) :
  dihomotopic (p.map f) (q.map f) :=
begin
  apply eqv_gen.rec_on h,
  exact λ x y hxy, eqv_gen.rel _ _ (hxy.map (λ (F : dihomotopy x y),  F.map f)),
  exact λ x, equivalence.1 (x.map f),
  exact λ x y hxy h, equivalence.2.1 h,
  exact λ x y z hxy hyz hxfyf hyfzf, equivalence.2.2 hxfyf hyfzf,
end

lemma hcomp_aid_left {p₀ p₁ : dipath x₀ x₁} (q : dipath x₁ x₂) (hp : p₀.dihomotopic p₁) :
  (p₀.trans q).dihomotopic (p₁.trans q) :=
  begin
    apply eqv_gen.rec_on hp,
    exact λ _ _ h, eqv_gen.rel _ _ ⟨h.some.hcomp (dihomotopy.refl q)⟩,
    exact λ p, equivalence.1 (p.trans q),
    exact λ _ _ _ h, equivalence.2.1 h,
    exact λ _ _ _ _ _ h₁ h₂, equivalence.2.2 h₁ h₂
  end
  
lemma hcomp_aid_right (p : dipath x₀ x₁) {q₀ q₁ : dipath x₁ x₂} (hq : q₀.dihomotopic q₁) :
  (p.trans q₀).dihomotopic (p.trans q₁) :=
  begin
    apply eqv_gen.rec_on hq,
    exact λ _ _ h, eqv_gen.rel _ _ ⟨(dihomotopy.refl p).hcomp h.some⟩,
    exact λ q, equivalence.1 (p.trans q),
    exact λ _ _ _ h, equivalence.2.1 h,
    exact λ _ _ _ _ _ h₁ h₂, equivalence.2.2 h₁ h₂
  end


/--
Suppose we have`p₀ p₁ : dipath x₀ x₁` and `q₀ q₁ : dipath x₁ x₂`.
If `p₀` is dihomotopic with `p₁` and `q₀` is dihomotopic with `q₁`, then `p₀.trans q₀` is dihomotopic with `p₁.trans q₁`.
-/
lemma hcomp {p₀ p₁ : dipath x₀ x₁} {q₀ q₁ : dipath x₁ x₂} (hp : p₀.dihomotopic p₁)
  (hq : q₀.dihomotopic q₁) : (p₀.trans q₀).dihomotopic (p₁.trans q₁) :=
  begin
  apply eqv_gen.rec_on hp,
  {
    intros p₀ p₁ hp₀p₁,
    have F := hp₀p₁.some,
    apply eqv_gen.rec_on hq,
    exact λ q₀ q₁ hq₀q₁, eqv_gen.rel _ _ ⟨F.hcomp hq₀q₁.some⟩,
    exact λ q, eqv_gen.rel _ _ ⟨F.hcomp (dihomotopy.refl q)⟩,
    exact λ q₀ q₁ hq₀q₁ hp₀q₀p₁q₁, by {
      have h₁ : (p₀.trans q₁).dihomotopic (p₁.trans q₁) := hcomp_aid_left q₁ (eqv_gen.rel _ _ hp₀p₁),
      have h₂ : (p₁.trans q₁).dihomotopic (p₀.trans q₀) := equivalence.2.1 hp₀q₀p₁q₁,
      have h₃ : (p₀.trans q₀).dihomotopic (p₁.trans q₀) := hcomp_aid_left q₀ (eqv_gen.rel _ _ hp₀p₁),
      exact equivalence.2.2 (equivalence.2.2 h₁ h₂) h₃,
    },
    exact λ q₀ q₁ q₂ hq₀q₁ hq₁q₂ hp₀q₀p₁q₁ hp₀q₁p₁q₂, by {
      have h₁ : (p₀.trans q₀).dihomotopic (p₀.trans q₁) := hcomp_aid_right p₀ hq₀q₁,
      have h₂ : (p₀.trans q₁).dihomotopic (p₀.trans q₂) := hcomp_aid_right p₀ hq₁q₂,
      have h₃ : (p₀.trans q₂).dihomotopic (p₁.trans q₂) := hcomp_aid_left q₂ (eqv_gen.rel _ _ hp₀p₁),
      exact equivalence.2.2 (equivalence.2.2 h₁ h₂) h₃,
    },
  },
  {
    intro p,
    apply eqv_gen.rec_on hq,
    exact λ q₀ q₁ hq₀q₁, hcomp_aid_right p (eqv_gen.rel _ _ hq₀q₁),
    exact λ q, equivalence.1 (p.trans q),
    exact λ q₀ q₁ hq₀q₁ hpq₀pq₁, equivalence.2.1 hpq₀pq₁,
    exact λ q₀ q₁ q₂ hq₀q₁ hq₁q₂ hpq₀pq₁ hpq₁pq₂, equivalence.2.2 hpq₀pq₁ hpq₁pq₂,
  },
  {
    intros p₀ p₁ hp₀p₁ _,
    apply eqv_gen.rec_on hq,
    exact λ q₀ q₁ hq₀q₁, by {
      have hp₁p₀ := equivalence.2.1 hp₀p₁,
      have hp₁q₀p₀q₀ : (p₁.trans q₀).dihomotopic (p₀.trans q₀) := hcomp_aid_left q₀ hp₁p₀,
      have hp₀q₀p₀q₁ : (p₀.trans q₀).dihomotopic (p₀.trans q₁) := hcomp_aid_right p₀ (eqv_gen.rel _ _ hq₀q₁),
      exact equivalence.2.2 hp₁q₀p₀q₀ hp₀q₀p₀q₁,
    },
    exact λ q, hcomp_aid_left q (equivalence.2.1 hp₀p₁),
    exact λ q₀ q₁ hq₀q₁ hp₁q₀p₀q₁, by { 
      have hp₁q₁p₁q₀ : (p₁.trans q₁).dihomotopic (p₁.trans q₀) := hcomp_aid_right p₁ (equivalence.2.1 hq₀q₁),
      have hp₁q₀p₀q₀ : (p₁.trans q₀).dihomotopic (p₀.trans q₀) := hcomp_aid_left q₀ (equivalence.2.1 hp₀p₁),
      exact equivalence.2.2 hp₁q₁p₁q₀ hp₁q₀p₀q₀,
    },
    exact λ q₀ q₁ q₂ hq₀q₁ hq₁q₂ hp₁q₀p₀q₁ hp₁q₁p₀q₂, by {
      have hp₀q₁p₁q₁ : (p₀.trans q₁).dihomotopic (p₁.trans q₁) := hcomp_aid_left q₁ hp₀p₁,
      exact equivalence.2.2 (equivalence.2.2 hp₁q₀p₀q₁ hp₀q₁p₁q₁) hp₁q₁p₀q₂,
    },
  },
  {
    intros p₀ p₁ p₂ hp₀p₁ hp₁p₂ _ _,
    apply eqv_gen.rec_on hq,
    exact λ q₀ q₁ hq₀q₁, by {
      have h₁ : (p₀.trans q₀).dihomotopic (p₁.trans q₀) := hcomp_aid_left q₀ hp₀p₁,
      have h₂ : (p₁.trans q₀).dihomotopic (p₂.trans q₀) := hcomp_aid_left q₀ hp₁p₂,
      have h₃ : (p₂.trans q₀).dihomotopic (p₂.trans q₁) := hcomp_aid_right p₂ (eqv_gen.rel _ _ hq₀q₁),
      exact equivalence.2.2 (equivalence.2.2 h₁ h₂) h₃,
    },
    exact λ q, by {
      have h₁ : (p₀.trans q).dihomotopic (p₁.trans q) := hcomp_aid_left q hp₀p₁,
      have h₂ : (p₁.trans q).dihomotopic (p₂.trans q) := hcomp_aid_left q hp₁p₂,
      exact equivalence.2.2 h₁ h₂,
    },
    exact λ q₀ q₁ hq₀q₁ hp₀q₀p₂q₁, by {
      have h₀ := equivalence.2.1 hq₀q₁,
      have h₁ : (p₀.trans q₁).dihomotopic (p₀.trans q₀) := hcomp_aid_right p₀ h₀,
      have h₂ : (p₂.trans q₁).dihomotopic (p₂.trans q₀) := hcomp_aid_right p₂ h₀,
      exact equivalence.2.2 (equivalence.2.2 h₁ hp₀q₀p₂q₁) h₂,
    },
    exact λ q₀ q₁ q₂ hq₀q₁ hq₁q₂ hp₀q₀p₂q₁ hp₀q₁p₂q₂,
    by {
      have hp₂p₀ := equivalence.2.1 (equivalence.2.2 hp₀p₁ hp₁p₂),
      have hp₂q₂p₀q₁ : (p₂.trans q₁).dihomotopic (p₀.trans q₁) := hcomp_aid_left q₁ hp₂p₀,
      exact equivalence.2.2 (equivalence.2.2 hp₀q₀p₂q₁ hp₂q₂p₀q₁) hp₀q₁p₂q₂,
    },
  },
end

/--
If `p` is a dipath, then it is dihomotopic with any monotonic subparametrization.
-/
lemma reparam (p : dipath x₀ x₁) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  p.dihomotopic (p.reparam f hf₀ hf₁) :=
begin
  set p' := p.reparam f hf₀ hf₁ with p'_def,
  have h₁ : ((dipath.refl x₀).trans p).pre_dihomotopic p := ⟨dihomotopy.refl_trans p⟩,
  have h₂ : ((dipath.refl x₀).trans p).pre_dihomotopic (p'.trans (refl x₁)) :=
    ⟨dihomotopy.refl_trans_to_reparam_trans_refl p f hf₀ hf₁⟩,
  have h₃ : p'.pre_dihomotopic (p'.trans (dipath.refl x₁)) := ⟨dihomotopy.trans_refl p'⟩,

  exact equivalence.2.2
    (equivalence.2.2
      (equivalence.2.1 $ eqv_gen.rel _ _ h₁)
      (eqv_gen.rel _ _ h₂))
    (equivalence.2.1 $ eqv_gen.rel _ _ h₃),
end

/--
The setoid on `dipath`s defined by the equivalence relation `dipath.dihomotopic`. That is, two paths are
equivalent if there is a chain of `dihomotopies` starting in one and ending in the other.
-/
protected def setoid (x₀ x₁ : X) : setoid (dipath x₀ x₁) := ⟨dihomotopic, equivalence⟩

/--
The quotient on `dipath x₀ x₁` by the equivalence relation `dipath.dihomotopic`.
-/
protected def quotient (x₀ x₁ : X) := quotient (dihomotopic.setoid x₀ x₁)

local attribute [instance] dihomotopic.setoid

/- The composition of dipath dihomotopy classes. This is `dipath.trans` descended to the quotient. -/
def quotient.comp (P₀ : dipath.dihomotopic.quotient x₀ x₁) (P₁ : dipath.dihomotopic.quotient x₁ x₂) :
  dipath.dihomotopic.quotient x₀ x₂ :=
quotient.map₂ dipath.trans (λ (p₀ : dipath x₀ x₁) p₁ hp (q₀ : dipath x₁ x₂) q₁ hq, (hcomp hp hq)) P₀ P₁

lemma comp_lift (P₀ : dipath x₀ x₁) (P₁ : dipath x₁ x₂) : ⟦P₀.trans P₁⟧ = quotient.comp ⟦P₀⟧ ⟦P₁⟧ := rfl

/- The image of a dipath dihomotopy class `P₀` under a directed map `f`.
    This is `dipath.dimap` descended to the quotient -/
def quotient.map_fn (P₀ : dipath.dihomotopic.quotient x₀ x₁) (f : D(X, Y)) :
  dipath.dihomotopic.quotient (f x₀) (f x₁) :=
quotient.map (λ (q : dipath x₀ x₁), q.map f) (λ p₀ p₁ h, dipath.dihomotopic.map h f) P₀

lemma map_lift (P₀ : dipath x₀ x₁) (f : D(X, Y)) :
  ⟦P₀.map f⟧ = quotient.map_fn ⟦P₀⟧ f := rfl

lemma quot_reparam (γ : dipath x₀ x₁) {f : D(I, I)} (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  ⟦γ.reparam f hf₀ hf₁⟧ = ⟦γ⟧ :=
begin
  symmetry,
  exact quotient.eq.mpr (dipath.dihomotopic.reparam γ f hf₀ hf₁),
end

lemma hpath_hext {p₁ : dipath x₀ x₁} {p₂ : dipath x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) : ⟦p₁⟧ == ⟦p₂⟧ :=
begin
  obtain rfl : x₀ = x₂ := by { convert hp 0; simp, },
  obtain rfl : x₁ = x₃ := by { convert hp 1; simp, },
  rw heq_iff_eq, congr, ext t, exact hp t,
end

end dihomotopic

end dipath
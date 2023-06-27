import directed_map
import auxiliary

/-
  This file contains constructions of directed spaces such as:
  * The directed space induced by a preorder on a topological space.
  * The directed space induced by a continuous map from a topological space to a directed space.
  * The product of two directed spaces.

  This file also contains lemmas about directed maps from/to these spaces.
-/

open directed_map

open_locale unit_interval

universes u v

/--
  Any space with a preorder can be equiped with a directedness, by allowing all monotone paths
  as directed paths
-/
def directed_space.preorder (α : Type u) [topological_space α] [preorder α] :
  directed_space α :=
{
  is_dipath := λ x y γ, monotone γ,

  is_dipath_constant := λ x a b hab, le_refl x,

  is_dipath_concat :=
    begin
      intros x y z γ₁ γ₂ hγ₁ hγ₂ a b hab,
      rw path.trans_apply,
      rw path.trans_apply,
      split_ifs,
      {
        -- a ≤ 1/2 and b ≤ 1/2, so use monotonicity of γ₁
        apply hγ₁,
        simp,
        exact hab
      },
      {
        -- a ≤ 1/2 and b > 1/2, so use that γ₁ ≤ y ≤ γ₂
        exact le_trans (monotone_path_bounded hγ₁ _).2 (monotone_path_bounded hγ₂ _).1
      },
      {
        -- Impossible, as 1/2 < a and b ≤ 1/2 and a ≤ b
        exact false.elim (h (le_trans hab h_1))
      },
      {
        -- a > 1/2 and b > 1/2, so use monotonicity of γ₂
        apply hγ₂,
        simp,
        exact hab
      }
    end,

  is_dipath_reparam := λ x y γ t₀ t₁ f hf_mono hγ_mono a b hab, hγ_mono (hf_mono hab)
}


/--
  A continuous map `f : α → β` with α an (undirected) topological space and β a directed topological space
  creates a directed structure on α by pulling back paths. 
-/
def directed_space.induced {α : Type u} {β : Type v} [topological_space α] [hβ : directed_space β] (f : α → β) (hf : continuous f) :
  directed_space α :=
{
  is_dipath := λ x y γ, is_dipath (γ.map hf),

  is_dipath_constant := λ x, is_dipath_constant (f x),

  is_dipath_concat := 
    begin
      rintros x y z γ₁ γ₂ φ₁_dipath φ₂_dipath,
      rw path.map_trans γ₁ γ₂ hf,
      exact is_dipath_concat φ₁_dipath φ₂_dipath,
    end,

  is_dipath_reparam := λ x y γ t₀ t₁ φ hφ_mono hγ_f, is_dipath_reparam φ hφ_mono hγ_f,
}

instance directed_subspace {α : Type u} {p : α → Prop} [t : directed_space α] :
  directed_space (subtype p) :=
  directed_space.induced (coe : subtype p → α) continuous_subtype_coe

section subtype

lemma is_directed_subtype_coe {α : Type u} {p : α → Prop} [t : directed_space α] :
  directed_map.directed { to_fun := (coe : subtype p → α), continuous_to_fun := continuous_subtype_coe} :=
λ x y γ γ_dipath, γ_dipath

def directed_subtype_inclusion  {α : Type u} (p : α → Prop) [t : directed_space α] : D(subtype p, α) :=
{
  to_fun := (coe : subtype p → α),
  continuous_to_fun := continuous_subtype_coe,
  directed_to_fun := is_directed_subtype_coe
}

lemma is_directed_subset_inclusion {α : Type u} [t : directed_space α] {X Y : set α} {h : X ⊆ Y} :
  directed_map.directed { to_fun := set.inclusion h, continuous_to_fun := continuous_inclusion h } :=
begin
  intros x y γ γ_dipath,
  have cont_X : continuous (coe : {x // x ∈ X} → α) := continuous_subtype_coe,
  have cont_Y : continuous (coe : {x // x ∈ Y} → α) := continuous_subtype_coe,
  have cont_X_Y : continuous (set.inclusion h) := continuous_inclusion h,
  show is_dipath ((γ.map cont_X_Y).map cont_Y),
  have :  (γ.map cont_X) = ((γ.map cont_X_Y).map cont_Y) := by { ext, refl },
  rw ←this,
  exact γ_dipath
end

def directed_subset_inclusion {α : Type u} [t : directed_space α] {X Y : set α} (h : X ⊆ Y) : D(X, Y) := {
  to_fun := (set.inclusion h),
  continuous_to_fun := continuous_inclusion h,
  directed_to_fun := is_directed_subset_inclusion,
}

instance directed_space_subtype {X : Type*} {Y : set X} [directed_space X] : directed_space Y :=
  directed_space.induced (λ x, x : Y → X) continuous_subtype_coe

end subtype


instance directed_product {α : Type u} {β : Type v} [t₁ : directed_space α] [t₂ : directed_space β] : directed_space (α × β) :=
{
  is_dipath := λ x y γ, (is_dipath (γ.map continuous_fst) ∧ is_dipath (γ.map continuous_snd)),

  is_dipath_constant := λ ⟨x₁, x₂⟩, ⟨is_dipath_constant x₁, is_dipath_constant x₂⟩,

  is_dipath_concat :=
    begin
      rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩ p q ⟨p₁_dipath, p₂_dipath⟩ ⟨q₁_dipath, q₂_dipath⟩,
      convert (and.intro (is_dipath_concat p₁_dipath q₁_dipath) (is_dipath_concat p₂_dipath q₂_dipath)); rw path.map_trans,
    end,

  is_dipath_reparam := λ a b γ t₀ t₁ φ hφ_mono ⟨γ₁_dipath, γ₂_dipath⟩,
      ⟨is_dipath_reparam φ hφ_mono γ₁_dipath, is_dipath_reparam φ hφ_mono γ₂_dipath⟩,
}

/-- The projection map `α × β → α` -/
def directed_fst {α β : Type*} [directed_space α] [directed_space β] : D(α × β, α) :=
{
  to_fun := λ x, x.1,
  directed_to_fun := λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ γ ⟨hγ₁, hγ₂⟩, hγ₁,
}

/-- The projection map `α × β → β` -/
def directed_snd {α β : Type*} [directed_space α] [directed_space β] : D(α × β, β) :=
{
  to_fun := λ x, x.2,
  directed_to_fun := λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ γ ⟨hγ₁, hγ₂⟩, hγ₂,
}

section prod

variables  {α β γ δ : Type*}  [directed_space α] [directed_space β] [directed_space γ] [directed_space δ]

/--
  Two dimaps `f : α → β` and `g : α → γ` can be turned into a dimap `α → β × γ` by mapping 
  `a : α` to `(f a, g a)`.
-/
protected def directed_map.prod_map_mk (f : D(α, β)) (g : D(α, γ)) : D(α, β × γ) :=
{
  to_fun := λ x, (f x, g x),
  directed_to_fun := λ x y γ γ_dipath, ⟨f.directed_to_fun γ γ_dipath, g.directed_to_fun γ γ_dipath⟩
}

/--
  Two dimaps `f : α → γ` and `g : β → δ` can be turned into a dimap `α × β → β × γ` by mapping
  `(a, b) : α × β` to `(f a, g b)`.
-/
protected def directed_map.prod_map_mk' (f : D(α, γ)) (g : D(β, δ)) : D(α × β, γ × δ) :=
{
  to_fun := λ x, (f x.1, g x.2),
  directed_to_fun := λ x y γ γ_dipath, ⟨f.directed_to_fun _ γ_dipath.1, g.directed_to_fun _ γ_dipath.2⟩
}

/- For every `t : α`, we can convert a directed map `F : α × β → γ` to a directed map `β → γ` by sending `b` to `F(t, b)` -/
def directed_map.prod_const_fst (F : D(α × β, γ)) (a : α) : D(β, γ) :=
  F.comp (directed_map.prod_map_mk (directed_map.const β a) (directed_map.id β))

@[simp] lemma directed_map.prod_const_fst_apply (F : D(α × β, γ)) (a : α) (b : β) :
  directed_map.prod_const_fst F a b = F (a, b) := rfl 

/- For every `t : β`, we can convert a directed map `F : α × β → γ` to a directed map `α → γ` by sending `a` to `F(a, t)` -/
def directed_map.prod_const_snd (F : D(α × β, γ)) (t : β) : D(α, γ) :=
  F.comp (directed_map.prod_map_mk (directed_map.id α) (directed_map.const α t))

@[simp] lemma directed_map.prod_const_snd_apply (F : D(α × β, γ)) (b : β) (a : α) :
  directed_map.prod_const_snd F b a = F (a, b) := rfl

end prod
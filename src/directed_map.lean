import directed_space

/-
  # Definition of directed maps
  This file defines the directed map between two directed spaces `X` and `Y` :
  it is a continuous map from `X` to `Y` that is also `directed`, i.e. it maps any dipath in `X` to a dipath in `Y`.
  We give the definitions of:
  * Constant maps
  * Identities
  * Composition of directed maps
-/

namespace directed_map

/--
  A continuous map between two directed spaces is `directed` if it maps dipaths to dipaths. 
-/
def directed {α β : Type*} [directed_space α] [directed_space β] (f : C(α, β)) : Prop :=
  ∀ ⦃x y : α⦄ (γ : path x y), is_dipath γ → is_dipath (γ.map f.continuous_to_fun)

end directed_map

/--
  Define the type of a directed map
-/
structure directed_map (α β : Type*) [directed_space α] [directed_space β] extends continuous_map α β :=
  (directed_to_fun : directed_map.directed to_continuous_map)

/- Notation `D(X,Y)` for directed maps from `X` to `Y` -/
notation `D(` α `, ` β `)` := directed_map α β

section
set_option old_structure_cmd true

class directed_map_class (F : Type*) (α β : out_param $ Type*) [directed_space α] [directed_space β]
  extends continuous_map_class F α β :=
(map_directed (f : F) : directed_map.directed (f : C(α, β)))

end

section directed_map_class

variables {F α β : Type*} [directed_space α] [directed_space β] [hF : directed_map_class F α β]

instance : has_coe_t F D(α, β) := ⟨λ f, {
    to_continuous_map := (f : C(α, β)),
    directed_to_fun := hF.map_directed f
  }⟩

end directed_map_class

variables {α β γ δ : Type*}
variables [directed_space α] [directed_space β] [directed_space γ] [directed_space δ]

namespace directed_map

/- To bypass the conversion to continuous_map -/
def to_fun : (D(α, β)) → α → β := λ f, f.to_fun

instance : directed_map_class D(α, β) α β :=
{
  coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  map_directed := λ f, f.directed_to_fun,
}

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (D(α, β)) (λ _, α → β) := fun_like.has_coe_to_fun

/-- A directed map can be coerced into a continuous map -/
instance : has_coe D(α, β) C(α, β) := ⟨λ f, f.to_continuous_map⟩

@[simp] lemma to_fun_eq_coe {f : D(α, β)} : f.to_fun = (f : α → β) := rfl
@[simp] lemma coe_to_continuous_map (f : D(α, β)) : ⇑f.to_continuous_map = f := rfl

@[ext] theorem ext {f g : D(α, β)} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h


variables (α)

/-- The identity map is directed -/
protected def id : directed_map α α :=
{
  to_fun := λ x, x,
  directed_to_fun := λ x y γ γ_path, by { convert γ_path, ext, refl },
}

@[simp] lemma coe_id : ⇑(directed_map.id α) = id := rfl

/-- Constant maps are directed -/
def const (b : β) : D(α, β) := {
  to_fun := λ a, b,
  directed_to_fun := λ x y γ hγ, is_dipath_constant b,
}
@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl

variables {α}

/-- The composition of directed maps is directed -/
def comp (f : D(β, γ)) (g : D(α, β)) : D(α, γ) := {
  to_fun := f ∘ g,
  directed_to_fun := λ x y p hp, f.directed_to_fun (p.map g.continuous_to_fun) (g.directed_to_fun p hp)
}

@[simp] lemma id_apply (a : α) : directed_map.id α a = a := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl
@[simp] lemma coe_comp (f : D(β, γ)) (g : D(α, β)) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : D(β, γ)) (g : D(α, β)) (a : α) : f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : D(γ, δ)) (g : D(β, γ)) (h : D(α, β)) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma id_comp (f : D(α, β)) : (directed_map.id β).comp f = f := ext $ λ a, rfl
@[simp] lemma comp_id (f : D(α, β)) : f.comp (directed_map.id α) = f := ext $ λ a, rfl
@[simp] lemma const_comp (c : γ) (f : D(α, β)) : (const β c).comp f = const α c := ext $ λ a, rfl
@[simp] lemma comp_const (f : D(β, γ)) (b : β) : f.comp (const α b) = const α (f b) := ext $ λ a, rfl

lemma coe_injective : @function.injective (D(α, β)) (α → β) coe_fn := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' }

end directed_map
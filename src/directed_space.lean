import topology.path_connected

/-
  # Definition of directed spaces
  This file defines the directed space, an extension of a topological space where
  some of its paths are considered directed paths.
-/

universe u

open_locale unit_interval


/-- Definition of a directed topological space.

    Dipaths are closed under:
    * Constant paths,
    * Concatenation of paths,
    * Monotone reparametrization of paths
 -/
class directed_space (α : Type u) extends topological_space α :=
  (is_dipath : ∀ {x y}, path x y → Prop)
  (is_dipath_constant : ∀ (x : α), is_dipath (path.refl x))
  (is_dipath_concat : ∀ {x y z} {γ₁ : path x y} {γ₂ : path y z}, is_dipath γ₁ → is_dipath γ₂ → is_dipath (path.trans γ₁ γ₂))
  (is_dipath_reparam : ∀ {x y} {γ : path x y} {t₀ t₁ : I} {f : path t₀ t₁}, monotone f → is_dipath γ → is_dipath (f.map (γ.continuous_to_fun)))

section directed_space

variable {α : Type*}
variables {x y : α}

def is_dipath [directed_space α] (γ : path x y) : Prop :=
  @directed_space.is_dipath α ‹_› x y γ

def is_dipath_constant (x : α) [directed_space α] : is_dipath (path.refl x) :=
  @directed_space.is_dipath_constant α ‹_› x

def is_dipath_concat {x y z : α} [directed_space α] {γ : path x y} {γ' : path y z} (hγ : is_dipath γ) (hγ' : is_dipath γ') :
  is_dipath (γ.trans γ') :=
  @directed_space.is_dipath_concat α ‹_› x y z γ γ' hγ hγ'

def is_dipath_reparam {x y : α} [directed_space α] {γ : path x y} {t₀ t₁ : I} (f : path t₀ t₁) (hfmono : monotone f) (hγ : is_dipath γ) :
  is_dipath (f.map γ.continuous_to_fun) :=
  @directed_space.is_dipath_reparam α ‹_› x y γ t₀ t₁ f hfmono hγ

/-- Casting a path that is directed into another path gives another directed path -/
lemma is_dipath_cast {x y x' y' : α} [directed_space α] (γ : path x y) (hx : x' = x) (hy : y' = y) :
  is_dipath γ → is_dipath (γ.cast hx hy) :=
begin
  intro γ_dipath,
  subst_vars,
  convert γ_dipath,
  ext,
  refl,
end

end directed_space
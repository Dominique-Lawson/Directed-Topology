import directed_unit_interval

/-
  This file contains the definition of a dipath in a directed space:
  A path between two points paired with the proof that it is a dipath.
  The following dipath constructions are given:
  * refl : the constant dipath
  * trans : the concatenation of dipaths
  * map : the image of a dipath under a directed map
  * subparam : the monotonic subparametrization of a dipath

  This file follows the structure of https://github.com/leanprover-community/mathlib/blob/master/src/topology/path_connected.lean
-/

noncomputable theory

open directed_map set
open_locale unit_interval

universe u
variables {X : Type u} [directed_space X] {x y z : X}

/-- A dipath is a path together with a proof that that path "is a dipath" -/
structure dipath (x y : X) extends path x y :=
  (dipath_to_path : is_dipath to_path)

instance : has_coe_to_fun (dipath x y) (λ _, I → X) := ⟨λ γ, γ.to_fun⟩
instance : has_coe (dipath x y) (C(I, X)) := ⟨λ γ, γ.to_continuous_map⟩
instance : has_coe (dipath x y) (path x y) := ⟨λ γ, γ.to_path⟩

namespace dipath

lemma is_directed (γ : dipath x y) : directed_map.directed γ.to_continuous_map :=
  λ t₀ t₁ φ φ_dipath, is_dipath_reparam φ φ_dipath γ.dipath_to_path

def to_directed_map (γ : dipath x y) : D(I, X) :=
{
  directed_to_fun := dipath.is_directed γ,
  to_fun := γ.to_fun,
  ..γ
}

/-- To bypass the conversion to continuous_map -/
def to_fun : (dipath x y) → I → X := λ f, f.to_fun

instance : directed_map_class (dipath x y) I X :=
{
  coe := λ γ, γ.to_fun,
  coe_injective' := λ γ γ' h, by { obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ, obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := γ', congr' },
  map_continuous := λ γ, γ.continuous_to_fun,
  map_directed := λ γ, is_directed γ,
}

end dipath

instance : has_coe (dipath x y) (D(I, X)) := ⟨λ γ, γ.to_directed_map⟩

@[ext] protected lemma dipath.ext : ∀ {γ₁ γ₂ : dipath x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂
| ⟨⟨⟨x, h10⟩, h11, h12⟩, h13⟩ ⟨⟨⟨.(x), h20⟩, h21, h22⟩, h23⟩ rfl := rfl

namespace dipath

def of_is_dipath {γ : path x y} (hγ : is_dipath γ) : dipath x y := {
  to_path := γ,
  dipath_to_path := hγ,
}

/-- An directed map from I to a directed space can be turned into a dipath -/
def of_directed_map (f : D(I, X)) : dipath (f 0) (f 1) := {
  to_continuous_map := (f : C(I, X)),
  source' := by simp,
  target' := by simp,
  dipath_to_path := directed_unit_interval.is_dipath_of_is_dipath_comp_id
    $ f.directed_to_fun directed_unit_interval.identity_path directed_unit_interval.identity_dipath
}

@[simp] lemma coe_mk (f : I → X) (h₀ h₁ h₂ h₃) : ⇑(mk ⟨⟨f, h₀⟩, h₁, h₂⟩ h₃ : dipath x y) = f := rfl

variable (γ : dipath x y)

@[continuity]
protected lemma continuous : continuous γ :=
  γ.continuous_to_fun

@[simp] protected lemma source : γ 0 = x :=
  γ.source'

@[simp] protected lemma target : γ 1 = y :=
  γ.target'

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X := γ

initialize_simps_projections dipath (to_path_to_continuous_map_to_fun → simps.apply, -to_path_to_continuous_map)

@[simp] lemma coe_to_continuous_map : ⇑γ.to_continuous_map = γ := rfl
@[simp] lemma coe_to_directed_map : ⇑γ.to_directed_map = γ := rfl


/-- Any function `φ : Π (a : α), dipath (x a) (y a)` can be seen as a function `α × I → X`. -/
instance has_uncurry_dipath {X α : Type*} [directed_space X] {x y : α → X} :
  function.has_uncurry (Π (a : α), dipath (x a) (y a)) (α × I) X :=
⟨λ φ p, φ p.1 p.2⟩


/-! ### Properites about the range of dipaths -/

@[simp] lemma coe_range (γ : dipath x y) : range γ = range γ.to_path := rfl
@[simp] lemma range_eq_image (γ : dipath x y) : range γ = γ.extend '' I := 
  set.ext (λ z, ⟨λ ⟨t, ht⟩, mem_image_iff_bex.mpr ⟨t, ⟨t.2, by { simp, exact ht }⟩⟩, λ ⟨t, t_mem_I, ht⟩, ⟨⟨t, t_mem_I⟩, (path.extend_extends γ.to_path t_mem_I ▸ ht)⟩⟩)

@[simp] lemma range_eq_image_I (γ : dipath x y) : range γ = γ '' Icc 0 1 := 
  set.ext (λ z, ⟨λ ⟨t, ht⟩, mem_image_iff_bex.mpr ⟨t, ⟨t.2, ht⟩⟩, λ ⟨t, t_mem_I, ht⟩, ⟨⟨t, t_mem_I⟩, by {
    convert ht,
    exact (subtype.coe_inj.mp rfl),
  }⟩⟩)

lemma image_extend_eq_image (γ : dipath x y) (a b : I) : γ.extend '' Icc ↑a ↑b = γ '' Icc a b :=
begin
  ext y,
  split,
  {
    rintro ⟨t, t_ab, ht⟩,
    use ⟨t, ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩⟩,
    rw ← ht,
    rw path.extend_extends γ.to_path _,
    refine ⟨t_ab, rfl⟩,
  },
  {
    rintro ⟨t, t_ab, ht⟩,
    use t,
    refine ⟨t_ab, _⟩,
    rw ← ht,
    convert path.extend_extends γ.to_path ⟨le_trans a.2.1 t_ab.1, le_trans t_ab.2 b.2.2⟩,
    exact (subtype.coe_inj.mp rfl),
  }
end

/-! ### Reflexive dipaths -/

/-- The constant dipath from a point to itself -/
@[refl, simps] def refl (x : X) : dipath x x :=
{ 
  dipath_to_path := is_dipath_constant x
  ..path.refl x
}

@[simp] lemma refl_range {a : X} : range (dipath.refl a) = {a} := path.refl_range

/-! ### Concatenation of dipaths -/

/-- Directed paths can be concatenated -/
@[trans] def trans (γ : dipath x y) (γ' : dipath y z) : dipath x z :=
{
  dipath_to_path := is_dipath_concat γ.dipath_to_path γ'.dipath_to_path,
  ..((γ.to_path.trans γ'.to_path))
}

@[simp] lemma trans_to_path (γ : dipath x y) (γ' : dipath y z) :
  γ.to_path.trans γ'.to_path = (γ.trans γ').to_path := 
begin
  ext,
  refl,
end

lemma trans_apply (γ : dipath x y) (γ' : dipath y z) (t : I) : (γ.trans γ') t =
  if h : (t : ℝ) ≤ 1/2 then
    γ ⟨2 * t, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
  else
    γ' ⟨2 * t - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
path.trans_apply (γ.to_path) (γ'.to_path) t

lemma trans_range (γ : dipath x y) (γ' : dipath y z) : range (γ.trans γ') = range γ ∪ range γ' :=
  path.trans_range γ.to_path γ'.to_path

lemma trans_eval_at_half (γ : dipath x y) (γ' : dipath y z) :
  (γ.trans γ') (auxiliary.inv_I two_pos) = y :=
begin
  rw dipath.trans_apply,
  simp,
end

/-! ### Mapping dipaths -/

/-- Image of a dipath from `x` to `y` by a directed map -/
def map (γ : dipath x y) {Y : Type*} [directed_space Y] (f : D(X, Y)) : dipath (f x) (f y) :=
{
  dipath_to_path := f.directed_to_fun γ.to_path γ.dipath_to_path,
  ..(γ.to_path.map f.continuous_to_fun)
}

@[simp] lemma map_coe (γ : dipath x y) {Y : Type*} [directed_space Y] (f : D(X, Y)) : 
  (γ.map f : I → Y) = f ∘ γ :=
by { ext t, refl }

@[simp] lemma map_trans (γ : dipath x y) (γ' : dipath y z) {Y : Type*} [directed_space Y] (f : D(X, Y)) :
  (γ.trans γ').map f = (γ.map f).trans (γ'.map f) := 
by { ext t, rw [trans_apply, map_coe, function.comp_app, trans_apply], split_ifs; refl }

@[simp] lemma map_id (γ : dipath x y) : γ.map (directed_map.id X) = γ := by { ext, refl }

@[simp] lemma map_map (γ : dipath x y) {Y : Type*} [directed_space Y] {Z : Type*} [directed_space Z] (f : D(X, Y)) (g : D(Y, Z)) :
  (γ.map f).map g = γ.map (g.comp f) := by { ext, refl }

/-! ### Casting dipaths -/

/-- Casting a dipath from `x` to `y` to a dipath from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) : dipath x' y' :=
{ to_fun := γ,
  continuous_to_fun := γ.continuous,
  dipath_to_path := is_dipath_cast γ.to_path hx hy γ.dipath_to_path,
  source' := by simp [hx],
  target' := by simp [hy]
}

lemma cast_apply (γ : dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (t : I):
  (γ.cast hx hy) t = γ t := rfl

@[simp] lemma trans_cast {X : Type*} [directed_space X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
  (γ : dipath a₂ b₂) (γ' : dipath b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl

@[simp] lemma cast_coe (γ : dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  (γ.cast hx hy : I → X) = γ := rfl

lemma cast_range (γ : dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  range (γ.cast hx hy) = range γ := rfl

lemma cast_image (γ : dipath x y) {x' y'} (hx : x' = x) (hy : y' = y) (a b : ℝ) :
  (γ.cast hx hy).extend '' Icc a b = γ.extend '' Icc a b := rfl

lemma dipath_of_directed_map_of_to_dimap (γ : dipath x y) :
  dipath.of_directed_map (γ.to_directed_map) = γ.cast γ.source' γ.target' :=
begin
  ext t,
  refl,
end

/-! ### Reparametrising a path -/

def subparam (γ : dipath x y) (f : D(I, I)) : dipath (γ (f 0)) (γ (f 1)) :=
{
  to_fun := γ ∘ f,
  continuous_to_fun := by continuity,
  source' := rfl,
  target' := rfl,
  dipath_to_path :=
    begin
      set p : path (f 0) (f 1) :=
        { to_fun := f,
          continuous_to_fun := f.continuous_to_fun,
          source' := rfl,
          target' := rfl
        },
      have := is_dipath_reparam p (directed_unit_interval.monotone_of_directed f) γ.dipath_to_path,
      convert this; simp
    end,
}

lemma subparam_range (γ : dipath x y) (f : D(I, I)) :
  range (γ.subparam f) ⊆ range γ := λ t ⟨a, ha⟩, ⟨f a, ha⟩

/--
Given a dipath `γ` and a dimap `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
dipath defined by `γ ∘ f`.
-/
def reparam (γ : dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  dipath x y :=
(subparam γ f).cast (hf₀.symm ▸ γ.source.symm) (hf₁.symm ▸ γ.target.symm)

@[simp]
lemma coe_to_fun (γ : dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  ⇑(γ.reparam f hf₀ hf₁) = γ ∘ f := rfl

@[simp]
lemma reparam_id (γ : dipath x y) : γ.reparam (directed_map.id I) rfl rfl = γ :=
by { ext, refl }

lemma range_reparam (γ : dipath x y) (f : D(I, I)) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  range (γ.reparam f hf₀ hf₁) = range γ :=
path.range_reparam γ.to_path f.continuous_to_fun hf₀ hf₁

variables {Y : Type*} [directed_space Y] {x₀ x₁ : X} {y₀ y₁ : Y}

/-- Two dipaths together form a dipath in the product space -/
def dipath_product (γ₁ : dipath x₀ x₁) (γ₂ : dipath y₀ y₁) : dipath (x₀, y₀) (x₁, y₁) :=
{
  to_fun := λ t, (γ₁ t, γ₂ t),
  source' := by { simp [γ₁.source', γ₂.source'] },
  target' := by { simp [γ₁.target', γ₂.target'] },
  dipath_to_path :=
    begin
      split,
      { convert γ₁.dipath_to_path, ext, refl },
      { convert γ₂.dipath_to_path, ext, refl }
    end
}

end dipath
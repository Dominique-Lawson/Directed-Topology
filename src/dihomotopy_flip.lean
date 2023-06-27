import directed_homotopy

/-
  If we have a dihomotopy `F` from `f : D(I, X)` to `g : D(I, X)`:
    C----- g -----D
    |             |
    |             |
    |             |
    |             |
    A----- f -----B
  Then we can flip it diagonally to obtain a new homotopy:
    B--- F.eval_at_right 1 -----D
    |                           |
    f                           g
    |                           |
    |                           |
    A----F.eval_at_right 0 -----C

  We then use that to compose two homotopies F
    D----- q₀ -----E
    |              |
    |              |
    |              |
    |              |
    A----- p₀ -----B
  and G
    E----- q₁ -----F
    |              |
    |              |
    |              |
    |              |
    B----- p₁ -----C
  that agree on the common side B ----- E to
    D----- q₀.trans q₁ -----F
    |                       |
    |                       |
    |                       |
    |                       |
    A----- p₀.trans p₁ -----C

  This is a variation of dipath.dihomotopy.hcomp of dihomotopies that are not necessarily dipath dihomotopies.
-/



universes u v

open directed_space directed_unit_interval auxiliary directed_map
open_locale unit_interval

noncomputable theory

namespace directed_map
namespace dihomotopy

variables {X : dTop}
variables {f g : D(I, X)}

def flip (F : dihomotopy f g) : dihomotopy (F.eval_at_right 0).to_directed_map (F.eval_at_right 1).to_directed_map :=
{
  to_fun := λ t, F (t.2, t.1),
  directed_to_fun :=
    begin
      rintros ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ γ ⟨h₁, h₂⟩,
      let γ' : dipath (y₀, x₀) (y₁, x₁) := {
        to_fun := λ t, ((γ t).2, (γ t).1),
        source' := by simp,
        target' := by simp,
        dipath_to_path := ⟨h₂, h₁⟩,
      },
      exact F.directed_to_fun γ'.to_path γ'.dipath_to_path,
    end,
  map_zero_left' := λ x, rfl,
  map_one_left' := λ x, rfl,
}

lemma flip_apply (F : dihomotopy f g) (t₀ t₁ : I) :
  F.flip (t₀, t₁) = F (t₁, t₀) := rfl

variables {x₀ x₁ x₂ y₀ y₁ y₂ : X}
variables {p₀ : dipath x₀ x₁} {p₁ : dipath x₁ x₂} {q₀ : dipath y₀ y₁} {q₁ : dipath y₁ y₂}

/--
Suppose the following are given:
* `p₀ : dipath x₀ x₁`
* `p₁ : dipath x₁ x₂`
* `q₀ : dipath y₀ y₁`
* `q₁ : dipath y₁ y₂`
* `F : dihomotopy p₀.to_directed_map q₀.to_directed_map`
* `G : dihomotopy p₁.to_directed_map p₁.to_directed_map`
* `h : F.eval_at_right 1 = G.eval_at_right 0`
Then we can compose these horizontaly to obtain:
  `dihomotopy (p₀.trans p₁).to_directed_map (q₀.trans q₁).to_directed_map`
-/
def hcomp' (F : dihomotopy p₀.to_directed_map q₀.to_directed_map) (G : dihomotopy p₁.to_directed_map q₁.to_directed_map)
  (h : (F.eval_at_right 1).to_directed_map = (G.eval_at_right 0).to_directed_map) :
  dihomotopy (p₀.trans p₁).to_directed_map (q₀.trans q₁).to_directed_map :=
  ((F.flip.cast rfl h).trans G.flip).flip.cast
    (by {
        ext t,
        show ((F.flip.cast rfl h).trans G.flip) (t, 0) = (p₀.trans p₁) t,
        rw trans_apply,
        rw dipath.trans_apply,
        split_ifs,
        { rw cast_apply, rw flip_apply, exact F.map_zero_left' _ },
        { rw flip_apply, exact G.map_zero_left' _ }
      }
    )
    (by {
        ext t,
        show ((F.flip.cast rfl h).trans G.flip) (t, 1) = (q₀.trans q₁) t,
        rw trans_apply,
        rw dipath.trans_apply,
        split_ifs,
        { rw cast_apply, rw flip_apply, exact F.map_one_left' _ },
        { rw flip_apply, exact G.map_one_left' _ }
      }
    )

lemma hcomp'_apply (F : dihomotopy p₀.to_directed_map q₀.to_directed_map) (G : dihomotopy p₁.to_directed_map q₁.to_directed_map)
  (h : (F.eval_at_right 1).to_directed_map = (G.eval_at_right 0).to_directed_map) (t₁ t₂ : I) :
  (hcomp' F G h) (t₁, t₂) =
  if h : (t₂ : ℝ) ≤ 1/2 then
    F.eval_at_left t₁ ⟨2 * t₂, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨t₂.2.1, h⟩⟩
  else
    G.eval_at_left t₁ ⟨2 * t₂ - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t₂.2.2⟩⟩ :=
begin
  unfold hcomp',
  rw cast_apply,
  rw flip_apply,
  rw trans_apply,
  split_ifs,
  { 
    rw cast_apply,
    rw flip_apply,
    refl,
  },
  {
    rw flip_apply,
    refl,
  }
end

lemma hcomp'_apply_zero_right (F : dihomotopy p₀.to_directed_map q₀.to_directed_map) (G : dihomotopy p₁.to_directed_map q₁.to_directed_map)
  (h : (F.eval_at_right 1).to_directed_map = (G.eval_at_right 0).to_directed_map) (x : I) : (hcomp' F G h) (x, 0) = F (x, 0) :=
begin
  rw hcomp'_apply,
  split_ifs with h h,
  {
    show F (x, _) = F (x, 0),
    apply congr_arg,
    ext,
    refl,
    simp,
  },
  exfalso,
  apply h,
  show (0 : ℝ) ≤ 1/2,
  linarith,
end

lemma hcomp'_apply_one_right (F : dihomotopy p₀.to_directed_map q₀.to_directed_map) (G : dihomotopy p₁.to_directed_map q₁.to_directed_map)
    (h : (F.eval_at_right 1).to_directed_map = (G.eval_at_right 0).to_directed_map) (x : I) :
  (hcomp' F G h) (x, 1) = G (x, 1) :=
begin
  rw hcomp'_apply,
  split_ifs with h h,
  {
    exfalso,
    have : ¬ ((1 : ℝ) ≤ 1/2) := by linarith,
    apply this,
    exact h,
  },
  {
    show G (x, _) = G (x, 1),
    apply congr_arg,
    ext,
    refl,
    simp,
    norm_num,
  },
end

lemma hcomp'_range (F : dihomotopy p₀.to_directed_map q₀.to_directed_map) (G : dihomotopy p₁.to_directed_map q₁.to_directed_map)
    (h : (F.eval_at_right 1).to_directed_map = (G.eval_at_right 0).to_directed_map) :
  set.range (hcomp' F G h) ⊆ set.range F ∪ set.range G :=
begin
  rintros z ⟨⟨t₁, t₂⟩, ht⟩, 
  rw hcomp'_apply at ht,
  split_ifs at ht,
  { left, use ⟨_, ht⟩ },
  { right, use ⟨_, ht⟩ },
end


end dihomotopy
end directed_map
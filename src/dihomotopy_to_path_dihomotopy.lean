import fundamental_category
import dihomotopy_flip

/-
  This file contains the construction of the following statement:

  Let a dihomotopy `F : f ~ g`, with `f g : D(I, X)` be  given:
   C----- g -----D
   |             |
   |             |
   |             |
   |             |
   A----- f -----B
  Then there is a path-dihomotopy between the paths
    A --refl A--> A --f--> B --F.eval_at_right 1--> D
  and
    A --F.eval_at_right 0--> C --g--> D --refl D--> D
-/

universe u

open directed_map
open_locale unit_interval

noncomputable theory

namespace directed_map
namespace dihomotopy

variables {X : dTop} {x y : X} (γ : dipath x y)

def min_directed : D(I × I, I) := {
  to_fun := λ t, min t.1 t.2,
  directed_to_fun := λ t₀ t₁ γ ⟨h₁, h₂⟩ a b hab, le_min (min_le_of_left_le (h₁ hab)) (min_le_of_right_le (h₂ hab)),
}

def max_directed : D(I × I, I) := {
  to_fun := λ t, max t.1 t.2,
  directed_to_fun := λ t₀ t₁ γ ⟨h₁, h₂⟩ a b hab, max_le (le_max_of_le_left (h₁ hab)) (le_max_of_le_right (h₂ hab)),
}

def source_to_path : dihomotopy (dipath.refl x).to_directed_map γ.to_directed_map := {
  to_directed_map := γ.to_directed_map.comp min_directed,
  map_zero_left' :=
    begin
      intro t,
      show γ (min 0 t) = _,
      have : min 0 t = 0 := min_eq_left t.2.1,
      rw this,
      rw γ.source,
      refl,
    end,
  map_one_left' :=
    begin
      intro t,
      show γ (min 1 t) = _,
      have : min 1 t = t := min_eq_right t.2.2,
      rw this,
      refl,
    end
}

lemma source_to_path_apply (s t : I) : source_to_path γ (s, t) = γ (min s t) := rfl

lemma source_to_path_range : set.range (source_to_path γ) = set.range γ :=
begin
  ext z,
  split,
  {
    rintros ⟨t, ht⟩,
    use min t.1 t.2,
    rw ← ht,
    exact (source_to_path_apply γ t.1 t.2).symm
  },
  {
    rintros ⟨t, ht⟩,
    use (t, t),
    rw ← ht,
    rw source_to_path_apply,
    exact congr_arg γ (min_self t)
  }
end

def path_to_target : dihomotopy γ.to_directed_map (dipath.refl y).to_directed_map := {
  to_directed_map := γ.to_directed_map.comp max_directed,
  map_zero_left' :=
    begin
      intro t,
      show γ (max 0 t) = _,
      have : max 0 t = t := max_eq_right t.2.1,
      rw this,
      refl
    end,
  map_one_left' :=
    begin
      intro t,
      show γ (max 1 t) = _,
      have : max 1 t = 1 := max_eq_left t.2.2,
      rw this,
      rw γ.target,
      refl
    end
}

lemma path_to_target_apply (s t : I) : path_to_target γ (s, t) = γ (max s t) := rfl

lemma path_to_target_range : set.range (path_to_target γ) = set.range γ :=
begin
  ext z,
  split,
  {
    rintros ⟨t, ht⟩,
    use max t.1 t.2,
    rw ← ht,
    exact (path_to_target_apply γ t.1 t.2).symm
  },
  {
    rintros ⟨t, ht⟩,
    use (t, t),
    rw ← ht,
    rw path_to_target_apply,
    exact congr_arg γ (max_self t)
  }
end

end dihomotopy
end directed_map

namespace dihom_to_path_dihom

variables {X : dTop} {f g : D(I, X)}

def dihom_to_dihom_of_paths (F : dihomotopy f g) :
  directed_map.dihomotopy (dipath.of_directed_map f).to_directed_map (dipath.of_directed_map g).to_directed_map :=
{
  to_directed_map := F.to_directed_map,
  map_zero_left' :=
    begin
      intro x,
      rw F.map_zero_left',
      refl,
    end,
  map_one_left' :=
    begin
      intro x,
      rw F.map_one_left',
      refl,
    end,
}

/--
  Let a dihomotopy `F : f ~ g`, with `f g : D(I, X)` be  given:
    C----- g -----D
    |             |
    |             |
    |             |
    |             |
    A----- f -----B
  Then there is a path-dihomotopy between the paths
    A --refl A--> A --f--> B --F.eval_at_right 1--> D
  and
    A --F.eval_at_right 0--> C --g--> D --refl D--> D
-/
def dihom_to_path_dihom (F : dihomotopy f g) : dipath.dihomotopy
    (((dipath.refl (f 0)).trans (dipath.of_directed_map f)).trans (F.eval_at_right 1))
    (((F.eval_at_right 0).trans (dipath.of_directed_map g)).trans (dipath.refl (g 1))) :=
{
  to_dihomotopy :=
      dihomotopy.hcomp'
      (
      dihomotopy.hcomp'
        (directed_map.dihomotopy.source_to_path (F.eval_at_right 0))
        (dihom_to_dihom_of_paths F)
        (by {
          ext s,
          show F ((min s 1), 0) = F (s, 0),
          rw min_eq_left,
          exact s.2.2,
        })
      )
      (directed_map.dihomotopy.path_to_target (F.eval_at_right 1))
      (
        by {
          ext s,
          show (dihomotopy.hcomp' _ _ _) (s, 1) = _,
          rw dihomotopy.hcomp'_apply_one_right,
          show F (s, _ ) = F ((max s 0), 1),
          rw max_eq_left,
          exact s.2.1,
        }
      ),
  prop' :=
    begin
      intros t x hx,
      cases hx,
      { -- x = 0
        subst hx,
        split; {
          show (dihomotopy.hcomp' _ _ _) (t, 0) = _,
          rw dihomotopy.hcomp'_apply_zero_right,
          rw dihomotopy.hcomp'_apply_zero_right,
          simp,
          show F (min t 0, 0) = f 0,
          rw min_eq_right,
          simp,
          exact t.2.1,
        }
      },
      { -- x = 1
        rw set.mem_singleton_iff at hx,
        subst hx,
        split; {
          show (dihomotopy.hcomp' _ _ _) (t, 1) = _,
          rw dihomotopy.hcomp'_apply_one_right,
          simp,
          show F (max t 1, 1) = g 1,
          rw max_eq_right,
          simp,
          exact t.2.2,
        }
      }
    end,
}

lemma dihom_to_path_dihom_range (F : dihomotopy f g) :
  set.range (dihom_to_path_dihom F) ⊆ set.range F :=
begin
  unfold dihom_to_path_dihom,
  let A := directed_map.dihomotopy.source_to_path (F.eval_at_right 0),
  let B := dihom_to_dihom_of_paths F,
  let C := directed_map.dihomotopy.path_to_target (F.eval_at_right 1),

  have hA : set.range A ⊆ set.range F,
  {
    dsimp [A],
    rw directed_map.dihomotopy.source_to_path_range,
    rintros x ⟨t, ht⟩,
    use (t, 0),
    exact ht,
  },
  have hB : set.range B ⊆ set.range F := λ x h, h,
  have hC : set.range C ⊆ set.range F,
  {
    dsimp [C],
    rw directed_map.dihomotopy.path_to_target_range,
    rintros x ⟨t, ht⟩,
    use (t, 1),
    exact ht,
  },

  have : set.range (A.hcomp' B _) ⊆ set.range F := subset_trans (dihomotopy.hcomp'_range A B _) (set.union_subset hA hB),
  exact subset_trans (dihomotopy.hcomp'_range (A.hcomp' B _) C _) (set.union_subset this hC),
end

end dihom_to_path_dihom

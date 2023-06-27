import algebraic_topology.fundamental_groupoid.basic
import directed_homotopy

/-
  Auxiliary lemmas for the refl_trans and trans_refl definitions in directed_path_homotopy.lean.
  These two are definitions are dihomotopies related to a `p : dipath x₀ x₁`:
    refl_trans : from `(refl x₀).trans p` to `p`
    trans_refl : from `p` to `p.trans (refl x₁)`

  Those for trans_refl can be based on the auxiliary lemmas found in algebraic_topology.fundamental_groupoid.basic.
  They use symmetry for refl_trans which is not possible in the directed case, so we have to define them manually.
-/

open directed_space directed_map
open_locale unit_interval

universes u v

variables {X : Type u} {Y : Type v}
variables [directed_space X] [directed_space Y]
variables {x₀ x₁ : X}

noncomputable theory

namespace dipath

namespace dihomotopy

open path.homotopy

section trans_refl

lemma directed_trans_refl_reparam_aux : directed_map.directed
  ({ to_fun := λ t, ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩} : C(I, I)) :=
begin
  apply directed_unit_interval.directed_of_monotone _,
  intros x y hxy,
  unfold trans_refl_reparam_aux,
  simp,
  have : (x : ℝ) ≤ (y : ℝ) := hxy,
  split_ifs with h₁ h₂,
  { linarith, },
  {
    calc 2 * (x : ℝ)  ≤ 2 * 2⁻¹ : (mul_le_mul_left (by norm_num)).mpr h₁
              ...     = 1       : by simp
  },
  { linarith, },
  { linarith, },
end

def trans_refl_reparam_aux_map : D(I, I) := {
  to_fun := λ t, ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩,
  directed_to_fun := directed_trans_refl_reparam_aux
}

lemma trans_refl_reparam (p : dipath x₀ x₁) : p.trans (dipath.refl x₁) =
  p.reparam trans_refl_reparam_aux_map
  (subtype.ext trans_refl_reparam_aux_zero) (subtype.ext trans_refl_reparam_aux_one) :=
begin
  ext t,
  have : (p.trans (dipath.refl x₁)) t = p.to_path.trans (path.refl x₁) t := rfl,
  rw this,
  rw path.homotopy.trans_refl_reparam p.to_path,
  refl,
end

end trans_refl

section refl_trans

/-- Auxilliary function for `refl_trans_reparam` -/
def refl_trans_reparam_aux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/2 then
  0
else
  2 * t - 1

@[continuity]
lemma continuous_refl_trans_reparam_aux : continuous refl_trans_reparam_aux :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _;
  [continuity, continuity, continuity, continuity, skip],
  intros x hx,
  norm_num [hx]
end

lemma refl_trans_reparam_aux_mem_I (t : I) : refl_trans_reparam_aux t ∈ I :=
begin
  unfold refl_trans_reparam_aux,
  split_ifs; split; linarith [unit_interval.le_one t, unit_interval.nonneg t]
end

lemma refl_trans_reparam_aux_zero : refl_trans_reparam_aux 0 = 0 :=
by norm_num [refl_trans_reparam_aux]

lemma refl_trans_reparam_aux_one : refl_trans_reparam_aux 1 = 1 :=
by norm_num [refl_trans_reparam_aux]


lemma directed_refl_trans_reparam_aux : directed_map.directed
  ({ to_fun := λ t, ⟨refl_trans_reparam_aux t, refl_trans_reparam_aux_mem_I t⟩} : C(I, I)) :=
begin
  apply directed_unit_interval.directed_of_monotone _,
  intros x y hxy,
  unfold refl_trans_reparam_aux,
  simp,
  have : (x : ℝ) ≤ (y : ℝ) := hxy,
  split_ifs with h₁ h₂,
  { linarith, },
  {
    calc (0 : ℝ)  = (2 : ℝ) * (2⁻¹ : ℝ) - (1 : ℝ) : by norm_num
          ...     ≤ 2 * (y : ℝ) - 1 : le_of_lt $ sub_lt_sub_right ((mul_lt_mul_left (by norm_num)).mpr (lt_of_not_le h₂)) 1
  },
  { linarith, },
  { linarith, },
end

def refl_trans_reparam_aux_map : D(I, I) := {
  to_fun := λ t, ⟨refl_trans_reparam_aux t, refl_trans_reparam_aux_mem_I t⟩,
  directed_to_fun := directed_refl_trans_reparam_aux
}

lemma refl_trans_reparam (p : path x₀ x₁) : (path.refl x₀).trans p =
  p.reparam (λ t, ⟨refl_trans_reparam_aux t, refl_trans_reparam_aux_mem_I t⟩) (by continuity)
  (subtype.ext refl_trans_reparam_aux_zero) (subtype.ext refl_trans_reparam_aux_one) :=
begin
  ext,
  unfold refl_trans_reparam_aux,
  simp [path.trans_apply, not_le, coe_to_fun, function.comp_app],
  split_ifs,
  { simp },
  { refl }
end

lemma refl_trans_reparam_dipath (p : dipath x₀ x₁) : (dipath.refl x₀).trans p =
  p.reparam refl_trans_reparam_aux_map
  (subtype.ext refl_trans_reparam_aux_zero) (subtype.ext refl_trans_reparam_aux_one) :=
begin
  ext t,
  have : ((dipath.refl x₀).trans p) t =  (path.refl x₀).trans p.to_path t := rfl,
  rw this,
  rw refl_trans_reparam p.to_path,
  refl,
end

end refl_trans

end dihomotopy

end dipath
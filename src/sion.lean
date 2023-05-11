
import .semicontinuous
import .concavexity

import analysis.convex.topology
import data.real.ereal
import topology.instances.ereal 

/-! # Formalization of the von Neumann Sion theorem 

## Statements

`sion_exists` : Let X and Y be convex subsets of topological vector spaces E and F, X being moreover compact, and let
f : X × Y → ℝ be a function such that 
- for all x, f(x, ⬝) is upper semicontinuous and quasiconcave
- for all y, f(⬝, y) is lower semicontinuous and quasiconvex
Then inf_x sup_y f(x,y) = sup_y inf_x f(x,y). 

The classical case of the theorem assumes that f is continuous,
f(x, ⬝) is concave, f(⬝, y) is convex.

As a particular case, one get the von Neumann theorem where
f is bilinear and E, F are finite dimensional.

We follow the proof of Komiya (1988). 

## References

- Neumann, John von (1928). « Zur Theorie der Gesellschaftsspiele ». Mathematische Annalen 100 (1): 295‑320. https://doi.org/10.1007/BF01448847.

- Sion, Maurice (1958). « On general minimax theorems ». Pacific Journal of Mathematics 8 (1): 171‑76.

- Komiya, Hidetoshi (1988). « Elementary Proof for Sion’s Minimax Theorem ». Kodai Mathematical Journal 11 (1). https://doi.org/10.2996/kmj/1138038812.


## Comments on the proof

For the moment, the proof is made difficult by the absence of results in mathlib
pertaining to semicontinuous functions, and possibly to continuity properties of convex functions.

One option would be to first do the proof for continuous functions 
by `sorry`ing all the results that we need in the semicontinuous case. 


-/


/- ereal is missing the `densely_ordered` instance ! -/

lemma ereal.exists_between {a b : ereal} (h : a < b) : ∃ (c : ereal), a < c ∧ c < b := 
sorry

variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [topological_add_group E][has_continuous_smul ℝ E]
variables 
 {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] [topological_add_group F] [has_continuous_smul ℝ F]
variables (X : set E) (ne_X : X.nonempty) (cX : convex ℝ X) (kX : is_compact X)
variables (Y : set F) (ne_Y : Y.nonempty) (cY : convex ℝ Y)

def is_saddle_point_on {β : Type*} [preorder β] (f : E → F → β) {a : E} (ha : a ∈ X) {b : F} (hb : b ∈Y) :=
(∀ x ∈ X, f a b ≤ f x b) ∧ (∀ y ∈ Y, f a y ≤ f a b) 

section ereal

namespace ereal_sion 

variable (f : E → F → ereal) 

/-- The trivial minimax inequality -/
lemma sup_inf_le_inf_sup : 
supr (λ y : Y, infi (λ x : X, f x y)) ≤ infi (λ x : X, supr (λ y : Y, f x y)) := 
begin
  rw supr_le_iff,
  rintro ⟨y, hy⟩,
  rw le_infi_iff,
  rintro ⟨x, hx⟩,
  exact le_trans (infi_le _ (⟨x,hx⟩ : X)) (le_supr (f x ∘ coe) (⟨y, hy⟩ : Y)),
end

variables (hfx : ∀ x ∈ X, upper_semicontinuous_on (λ y : F, f x y) Y) (hfx' : ∀ x ∈ X, quasiconcave_on ℝ Y (λ y, f x y))
variables (hfy : ∀ y ∈ Y, lower_semicontinuous_on (λ x : E, f x y) X) (hfy' : ∀ y ∈ Y, quasiconvex_on ℝ X (λ x, f x y))

include hfx hfx' ne_X cX kX hfy hfy' ne_Y cY

lemma exists_lt_infi_of_lt_infi_of_two {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y )
  {t : ℝ} (ht : (t : ereal) < infi (λ x : X,  (f x y1) ⊔ (f x y2))) :
  ∃ y0 ∈ Y, (t : ereal) < infi (λ x : X, f x y0) := 
begin
  by_contradiction hinfi_le,
  push_neg at hinfi_le,
  obtain ⟨t' : ereal, htt' : (t : ereal) < t', ht' : t' < infi (λ x : X, f x y1 ⊔ f x y2)⟩
    := ereal.exists_between ht,
--  let Z := segment ℝ y1 y2,
  let C : ereal → F → set E := λ u z, { x ∈ X | f x z ≤ u }, 
  --  λ u z, set.preimage (λ x, f x z)  (set.Iic u) ∩ X, 
  have hC : ∀ u v z, u ≤ v →  C u z ⊆ C v z, 
  { intros u v z h,
    simp only [C], 
    intro x, simp only [set.mem_sep_iff],
    rintro ⟨hx, hxu⟩, exact ⟨hx, le_trans hxu h⟩, } ,
  have hC_closed : ∀ u, ∀ {z}, z ∈ Y → is_closed (set.preimage coe (C u z) : set X), 
  { intros u z hz, simp only [C],
    specialize hfy z hz, 
    rw lower_semicontinuous_on_iff_restrict at hfy, 
    rw lower_semicontinuous_iff_is_closed_preimage at hfy, 
    convert hfy u,
    ext ⟨x, hx⟩,
    simp only [set.mem_preimage, hx, subtype.coe_mk, set.mem_sep_iff, true_and, set.restrict_apply, set.mem_Iic], },
  have hC_convex : ∀ u, ∀ {z}, z ∈ Y → convex ℝ (C u z), 
  { intros u z hz, 
    simp only [C],
    simp only [quasiconvex_on] at hfy',
    exact hfy' z hz u, },
  have hC_empty_inter : (C t' y1 ∩ C t' y2) = ∅, 
  { ext x, simp only [set.mem_inter_iff, set.mem_sep_iff, set.mem_empty_iff_false, iff_false, not_and, and_imp], 
    intros hx hx1 _ hx2,
    rw ← not_le at ht', apply ht', 
    refine le_trans (infi_le _ ⟨x, hx⟩) _,
    rw sup_le_iff,
    simp only [subtype.coe_mk], 
    exact ⟨hx1, hx2⟩, },
  have hC_subset : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∪ C t' y2, 
  { intros z hz, 
    rintros x ⟨hx, hx'⟩,
    simp only [set.mem_union, set.mem_sep_iff, hx, true_and],
    specialize hfx' x hx,
    simp only [quasiconcave_on] at hfx',
    specialize hfx' (f x y1 ⊓ f x y2),
    rw convex_iff_segment_subset at hfx', 
    specialize @hfx' y1 _ y2 _ z hz,
    { rw set.mem_sep_iff, split, exact hy1, exact inf_le_left, },
    { rw set.mem_sep_iff, split, exact hy2, exact inf_le_right, },
    rw set.mem_sep_iff at hfx', 
    rw ← inf_le_iff,
    exact le_trans hfx'.2 hx', },
  have hC_subset_or : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∨ C t' z ⊆ C t' y2, 
  { intros z hz, -- il faut un coup de coercion…
    suffices : is_preconnected (C t' z), 
    rw is_preconnected_iff_subset_of_disjoint_closed at this,
    -- rw is_preconnected_closed_iff at this,
    apply this (C t' y1) (C t' y2) (hC_closed t' hy1) (hC_closed t' hy2) (hC_subset z hz),
    rw [hC_empty_inter, set.inter_empty], 
    exact convex.is_preconnected (hC_convex t' z), },

  let J1 := { z in segment ℝ y1 y2 | C t z ⊆  C t' y1},
  have hJ1 : is_closed (J1), sorry,
  have hy1_mem_J1 : y1 ∈ J1, 
  { simp only [J1, set.mem_sep_iff], 
    split, 
    exact left_mem_segment ℝ y1 y2,
    apply hC, exact le_of_lt htt', },
  let J2 := { z in segment ℝ y1 y2 | C t z ⊆  C t' y2},
  have hy2_mem_J2 : y2 ∈ J2,
  { simp only [J1, set.mem_sep_iff], split, exact right_mem_segment ℝ y1 y2, 
    exact hC _ _ _ (le_of_lt htt'), },
  have hJ2 : is_closed (J2), sorry, 
  have hJ1J2 : J1 ∩ J2 = ∅, sorry,
  have hJ1_union_J2 : segment ℝ y1 y2 ⊆ J1 ∪ J2, sorry,
  suffices : is_preconnected (segment ℝ y1 y2),
  { rw is_preconnected_iff_subset_of_disjoint_closed at this,
    specialize this J1 J2 hJ1 hJ2 hJ1_union_J2,
    cases this _ with h1 h2, 
    { rw set.eq_empty_iff_forall_not_mem at hJ1J2, 
      apply hJ1J2 y2, 
      rw set.mem_inter_iff,
      split, apply h1, apply right_mem_segment, exact hy2_mem_J2, },
    { rw set.eq_empty_iff_forall_not_mem at hJ1J2, 
      apply hJ1J2 y1, 
      rw set.mem_inter_iff,
      split, exact hy1_mem_J1, apply h2, apply left_mem_segment, },
    rw [hJ1J2, set.inter_empty], },
  
  exact convex.is_preconnected (convex_segment y1 y2),
end

example (s : set E) (hs : s = ∅) (a : E) (ha : a ∈ s) : false :=
begin
exact set.eq_empty_iff_forall_not_mem.mp hs a ha
end

lemma exists_lt_infi_of_lt_infi_of_finite {s : set F} (hs : s.finite) {t : ℝ} (ht : (t : ereal) < infi (λ x : X, supr (λ y : s, f x y))) : 
  ∃ y0 ∈ Y,  (t : ereal) < infi (λ x : X, f x y0) := sorry

theorem minimax : 
infi (λ x : X, supr (λ y : Y, f x y)) = supr (λ y : Y, infi (λ x : X, f x y)) := sorry

end ereal_sion
end ereal

section real 

namespace sion 

variable (f : E → F → ℝ) 

lemma is_bdd_above : bdd_above (set.range (λ (xy : X × Y), f xy.1 xy.2))  := sorry

lemma is_bdd_below : bdd_below (set.range (λ (xy : X × Y), f xy.1 xy.2)) := sorry 

/- The theorem is probably wrong without the additional hypothesis
that Y is compact. Indeed, if the image of (λ y, f x y) is not bounded above,
then supr is defined as 0, while the theorem should interpret it as infinity.

Possibilities : 

- add hypotheses that guarantee the bdd_above condition
- replace the infimum on (x : X) by the infimum on the subtype of X
consisting of x such that (λ y, f x y) is bounded above.
(If that subtype is empty, the left hand side is +infinity for mathematicians,
but 0 for Lean… what about the rhs?)

-/

theorem minimax : 
infi (λ x : X, supr (λ y : Y, f x y)) = supr (λ y : Y, infi (λ x : X, f x y)) := sorry

/- Here, one will need compactness on Y — otherwise, no hope that
the saddle point exists… -/
/-- The minimax theorem, in the saddle point form -/
theorem exists_saddle_point : ∃ (a : E) (ha : a ∈ X) (b : F) (hb : b ∈ Y),
  is_saddle_point_on X Y f ha hb := sorry

-- There are some `sorry` because we need to add the proof that the
-- function is bounded on X Y 
/-- The minimax theorem, in the inf-sup equals sup-inf form -/
theorem minimax' : 
infi (λ x : X, supr (λ y : Y, f x y)) = supr (λ y : Y, infi (λ x : X, f x y)) := 
begin
  haveI : nonempty X := ne_X.coe_sort,
  haveI : nonempty Y := ne_Y.coe_sort,
  obtain ⟨m, hm⟩ := sion.is_bdd_below X ne_X cX kX Y ne_Y cY f hfx hfx' hfy hfy',
  obtain ⟨M, hM⟩ := sion.is_bdd_above X ne_X cX kX Y ne_Y cY f hfx hfx' hfy hfy',
  simp only [lower_bounds, upper_bounds, set.mem_range, prod.exists, set_coe.exists, subtype.coe_mk, exists_prop,
  forall_exists_index, and_imp, set.mem_set_of_eq] at hm hM,
  apply le_antisymm,

  { obtain ⟨a, ha, b, hb, hax, hby⟩ := sion.exists_saddle_point X ne_X cX kX Y ne_Y cY f hfx hfx' hfy hfy',
    suffices : f a b ≤ supr (λ y : Y, infi (λ x : X, f x y)), 
    apply le_trans _ this,
    refine le_trans (cinfi_le _ (⟨a, ha⟩ : X)) _, 
    -- bdd_below is not automatic :-(
    { dsimp only [bdd_below, lower_bounds],
      use m,
      simp only [set.mem_range, set_coe.exists, subtype.coe_mk, forall_exists_index, forall_apply_eq_imp_iff₂, set.mem_set_of_eq], 
      intros x hx,
      refine le_trans _ (le_csupr _ ⟨b, hb⟩),
      exact hm x hx b hb rfl, 
      dsimp only [bdd_above, upper_bounds],
      use M,
      simp only [set.mem_range, set_coe.exists, subtype.coe_mk, forall_exists_index, forall_apply_eq_imp_iff₂, set.mem_set_of_eq],
      intros y hy, exact hM x hx y hy rfl, },
    apply csupr_le, 
    rintro ⟨y, hy⟩, exact hby y hy,
    refine le_trans _ (le_csupr _ (⟨b, hb⟩ : Y)),
    apply le_cinfi,
    rintro ⟨x, hx⟩, exact hax x hx,
    -- bdd_above is not automatic :-( 
    sorry, },

  { apply csupr_le, rintro ⟨y, hy⟩,
    apply le_cinfi, rintro ⟨x, hx⟩, 
    refine le_trans (cinfi_le _ (⟨x, hx⟩ : X)) _,
    sorry, -- bdd_below is not automatic
--    rw subtype.coe_mk,
    refine @le_csupr _ _ _  (λ t : Y, f x t)  _ (⟨y, hy⟩ : Y),
    sorry, -- bdd_above is not automatic 
    }, 
  
end

end sion 

end sion

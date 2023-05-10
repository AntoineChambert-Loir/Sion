
import .semicontinuous
import .concavexity

import data.real.ereal


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


variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variables 
 {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] [has_continuous_add F] [has_continuous_smul ℝ F]
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
  refine le_trans (infi_le _ (⟨x,hx⟩ : X)) _, 
  -- je ne comprends pas pourquoi le_supr ne permet pas de conclure
  refine le_trans _ (le_supr _ (⟨y, hy⟩: Y)),
  exact le_refl (f x y),
end

variables (hfx : ∀ x ∈ X, upper_semicontinuous_on (λ y : F, f x y) Y) (hfx' : ∀ x ∈ X, quasiconcave_on ℝ Y (λ y, f x y))
variables (hfy : ∀ y ∈ Y, lower_semicontinuous_on (λ x : E, f x y) X) (hfy' : ∀ y ∈ Y, quasiconvex_on ℝ X (λ x, f x y))

include hfx hfx' ne_X cX kX hfy hfy' ne_Y cY

lemma exists_lt_infi_of_lt_infi_of_two {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y )
  {t : ℝ} (ht : (t : ereal) < infi (λ x : X,  (f x y1) ⊔ (f x y2))) :
  ∃ y0 ∈ Y, (t : ereal) < infi (λ x : X, f x y0) := sorry

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

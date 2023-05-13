
import .semicontinuous
import .concavexity
import for_mathlib.misc

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

- Neumann, John von (1928). « Zur Theorie der Gesellschaftsspiele ». Mathematische Annalen 100 (1): 295‑320. 
https://doi.org/10.1007/BF01448847.

- Sion, Maurice (1958). « On general minimax theorems ». Pacific Journal of Mathematics 8 (1): 171‑76.

- Komiya, Hidetoshi (1988). « Elementary Proof for Sion’s Minimax Theorem ». Kodai Mathematical Journal 11 (1). 
https://doi.org/10.2996/kmj/1138038812.


## Comments on the proof

For the moment, the proof is made difficult by the absence of results in mathlib
pertaining to semicontinuous functions, and possibly to continuity properties of convex functions.

One option would be to first do the proof for continuous functions 
by `sorry`ing all the results that we need in the semicontinuous case. 


-/

open set

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

include hfy cY hfy' hfx cX hfx'

-- Question pour Antoine : Y-a-t'il une raison pour utiliser `⨅ (x : X), foo x` au lieu de `⨅ x ∈ X, foo x`
-- (le deuxième évite des coercions) ? Dans `ℝ` ce sera important de faire la distinction parce 
-- que ça ne donne pas le même résultat (`⨅ x ∈ X, foo x` devient `⨅ (x : E), ⨅ (hx : x ∈ X), foo x` et
-- l'inf sur l'ensemble vide ne donne rien sur `ℝ`), mais autant profiter à fond de `ereal`, non ?

set_option trace.simp_lemmas true

lemma exists_lt_infi_of_lt_infi_of_two {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y )
  {t : ℝ} (ht : (t : ereal) < ⨅ (x : X), (f x y1) ⊔ (f x y2)) :
  ∃ y0 ∈ Y, (t : ereal) < infi (λ x : X, f x y0) := 
begin
  by_contra' hinfi_le,
  obtain ⟨t' : ereal, htt' : ↑t < t', ht' : t' < ⨅ (x : X), f x y1 ⊔ f x y2⟩ := 
    exists_between ht,
--  let Z := segment ℝ y1 y2,
--  have hsegment_le : segment ℝ y1 y2 ⊆ Y := cY.segment_subset hy1 hy2, 

  let C : ereal → F → set X := λ u z, ((λ x, f x z) ∘ coe) ⁻¹' (Iic u), 
  have mem_C_iff : ∀ u z (x : X), x ∈ C u z ↔ f x z ≤ u,
  { intros u z x, refl, },
  --  λ u z, set.preimage (λ x, f x z)  (set.Iic u) ∩ X, 
  /- On se bagarre entre la topologie ambiante
  et les topologies induites sur X (compact convexe) ou sur segment ℝ y1 y2 
  L'une ou l'autre des définitions est confortable.
  -/
  have hC : ∀ u v z, u ≤ v → C u z ⊆ C v z, 
  { intros u v z h,
    -- C'est cosmétique, pas besoin de déplier les définitions
    -- simp only [C], 
    -- intro x, simp only [set.mem_sep_iff],
    rintro x hxu, exact (le_trans hxu h) } ,

    -- Uses compactness of X !
  have hC_ne : ∀ z ∈ Y, (C t z).nonempty,
  sorry,

  have hC_closed : ∀ u, ∀ {z}, z ∈ Y → is_closed (C u z), 
  { intros u z hz, simp only [C],
    specialize hfy z hz, 
    rw lower_semicontinuous_on_iff_restrict at hfy, 
    rw lower_semicontinuous_iff_is_closed_preimage at hfy, 
    exact hfy u },
  have hC_preconnected : ∀ u, ∀ {z}, z ∈ Y → is_preconnected (C u z), 
  { intros u z hz, 
    exact (hfy' z hz).is_preconnected_preimage },
  have hC_disj : disjoint (C t' y1) (C t' y2), 
    from set.disjoint_iff.mpr (λ x hx, not_lt_of_le 
      (infi_le_of_le x $ sup_le_iff.mpr hx) ht'),
  have hC_subset : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∪ C t' y2, 
  { intros z hz x hx, 
    simp only [set.mem_union, mem_C_iff, ← inf_le_iff], 
-- was AD:    change (_ ≤ _) ∨ (_ ≤ _), rw ← inf_le_iff,
    specialize hfx' x x.2 (f x y1 ⊓ f x y2),
    rw convex_iff_segment_subset at hfx', 
    specialize hfx' ⟨hy1, inf_le_left⟩ ⟨hy2, inf_le_right⟩ hz,
    exact le_trans hfx'.2 hx },
  have hC_subset_or : ∀ z ∈ segment ℝ y1 y2, C t' z ⊆ C t' y1 ∨ C t' z ⊆ C t' y2, 
  { intros z hz, 
  /-    exact (hC_preconnected _ (cY.segment_subset hy1 hy2 hz)).subset_or_subset_of_closed 
      (hC_closed _ hy1) (hC_closed _ hy2) hC_disj (hC_subset _ hz), -/
      apply is_preconnected_iff_subset_of_disjoint_closed.mp (hC_preconnected _ (cY.segment_subset hy1 hy2 hz)) _ _
      (hC_closed _ hy1) (hC_closed _ hy2) (hC_subset _ hz),
      rw [set.disjoint_iff_inter_eq_empty.mp hC_disj, set.inter_empty], },

  let J1 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y1},
  -- do we really need this ? (I can't do without it)
  have mem_J1_iff : ∀ (z : segment ℝ y1 y2), z ∈ J1 ↔ C t z ⊆ C t' y1,
  { intro z, refl, },
  
  have hJ1 : is_closed J1, 
  { rw is_closed_iff_cluster_pt, 
    intros y h x hx, 

/- y = lim yn, yn ∈ J1 
   comme x ∈ C t y, on a f x y ≤ t < t', 
   comme (f x ⬝) est usc, f x yn < t' pour n assez grand
   donc x ∈ C t' yn pour n assez grand
   
   pour z ∈ J1 tel que x ∈ C t' z
   On prouve C t' z ⊆ C t' y1
   Par hypothèse, C t z ⊆ C t' y1
   Sinon, C t' z ⊆ C t' y2 (hC_subset_or)
   Donc x ∈ C t' y1 ∩ C t' y2 = ∅, contradiction

   En particulier, x ∈ C yt' y1 

-/

    suffices : ∃ z ∈ J1, x ∈ C t' (z : F), 
    obtain ⟨z, hz, hxz⟩ := this, 
    suffices : C t' z ⊆ C t' y1, exact this hxz, 

    apply or.resolve_right (hC_subset_or z z.2),
    intro hz2, 

    apply set.nonempty.not_subset_empty (hC_ne z  ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2)),
    rw ← (disjoint_iff_inter_eq_empty.mp hC_disj), 
    apply set.subset_inter hz, 
    exact subset_trans (hC t t' z (le_of_lt htt')) hz2, 

    -- This is a rewriting of h in a nicer form, there must be a better way to do
    have h' : ∃ᶠ (z : F) in nhds ↑y, ∃ (hz : z ∈ segment ℝ y1 y2), 
      (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1,
    { simp only [cluster_pt_principal_iff_frequently, 
        (inducing_coe).nhds_eq_comap, subtype.coe_mk,
        set.mem_preimage, filter.frequently_comap, subtype.coe_prop, 
        exists_prop] at h, 
      suffices : _, 
      exact (filter.frequently_congr this).mp h, 
      apply filter.eventually_of_forall,
      intro z,
      split,
      { rintro ⟨⟨z', hz'⟩, h⟩, 
        suffices hz : z ∈ segment ℝ y1 y2, use hz, 
        convert h.2, rw [← h.1, subtype.coe_mk],
        rw ← h.1, exact hz', },
      { rintro ⟨hz, h⟩,
        use ⟨z, hz⟩, exact ⟨rfl, h⟩, }, },

    -- Now, the goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [upper_semicontinuous_on, upper_semicontinuous_within_at] at hfx,
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt'),



    -- and to conclude using that if ∀ᶠ sth holds, then ∃ᶠ sth holds.
    -- using  frequently.mp 
    
    -- needs to have h' in terms of nhds y
    
  sorry },

  have hy1_mem_J1 : (⟨y1, left_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J1, 
  { rw mem_J1_iff, apply hC, exact le_of_lt htt', },

  let J2 := { z : segment ℝ y1 y2 | C t z ⊆  C t' y2},
  -- bizarrely, this is necessary to add this lemma, 
  -- rien du genre  rw set.mem_sep_iff ne marche…
  have mem_J2_iff : ∀ (z : segment ℝ y1 y2), z ∈ J2 ↔ C t z ⊆ C t' y2,
  { intro z, refl, },
  have hy2_mem_J2 : (⟨y2, right_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J2,
  { rw mem_J2_iff, apply hC, exact le_of_lt htt', },
  
  have hJ2 : is_closed J2, sorry, 

  have hJ1J2 : J1 ∩ J2 = ∅, sorry,
  have hJ1_union_J2 : J1 ∪ J2 = set.univ, sorry,

  suffices this : is_preconnected (set.univ : set (segment ℝ y1 y2)),
  { rw is_preconnected_iff_subset_of_disjoint_closed at this,
    specialize this _ _ hJ1 hJ2 (eq.subset hJ1_union_J2.symm) _,
    { rw [hJ1J2, set.inter_empty], },
    rw set.eq_empty_iff_forall_not_mem at hJ1J2, 
    cases this with h1 h2, 
    { apply hJ1J2, 
      rw set.mem_inter_iff,
      exact ⟨h1 (set.mem_univ _), hy2_mem_J2⟩, },
    { apply hJ1J2, 
      rw set.mem_inter_iff,
      exact ⟨hy1_mem_J1, h2 (set.mem_univ _)⟩, }, },
  
  rw ←(inducing_coe).is_preconnected_image, 
  simp only [image_univ, subtype.range_coe_subtype, set_of_mem_eq], 
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

include ne_X ne_Y

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

end real
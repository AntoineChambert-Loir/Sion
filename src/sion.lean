
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
lemma supr₂_infi₂_le_infi₂_supr₂ : 
(⨆ y ∈ Y, ⨅ x ∈ X, f x y) ≤ (⨅ x ∈ X, ⨆ y ∈ Y, f x y) :=
begin
  rw supr₂_le_iff, intros y hy,
  rw le_infi₂_iff, intros x hx, 
  exact infi₂_le_of_le x hx (le_supr₂_of_le y hy (le_refl _)),
end

variables (hfx : ∀ x ∈ X, upper_semicontinuous_on (λ y : F, f x y) Y) (hfx' : ∀ x ∈ X, quasiconcave_on ℝ Y (λ y, f x y))
variables (hfy : ∀ y ∈ Y, lower_semicontinuous_on (λ x : E, f x y) X) (hfy' : ∀ y ∈ Y, quasiconvex_on ℝ X (λ x, f x y))

include hfy cY hfy' hfx ne_X cX hfx'

-- Question pour Antoine : Y-a-t-il une raison pour utiliser `⨅ (x : X), foo x` au lieu de `⨅ x ∈ X, foo x`
-- (le deuxième évite des coercions) ? Dans `ℝ` ce sera important de faire la distinction parce 
-- que ça ne donne pas le même résultat (`⨅ x ∈ X, foo x` devient `⨅ (x : E), ⨅ (hx : x ∈ X), foo x` et
-- l'inf sur l'ensemble vide ne donne rien sur `ℝ`), mais autant profiter à fond de `ereal`, non ?

-- Réponse : a priori, aucune, je ne sais même pas pourquoi j'entre l'une et pas l'autre. 

-- Question : quelle est la différence dans ℝ ?
-- (à part que l'inf sur l'ensemble vide est alors 0 et pas + infini !)

include kX

lemma exists_lt_infi_of_lt_infi_of_two {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y )
  {t : ereal} (ht : t < ⨅ (x : X), (f x y1) ⊔ (f x y2)) :
  ∃ y0 ∈ Y, t < infi (λ x : X, f x y0) := 
begin
  by_contra' hinfi_le,
  obtain ⟨t' : ereal, htt' : t < t', ht' : t' < ⨅ (x : X), f x y1 ⊔ f x y2⟩ := 
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

    -- Uses that X is compact and nonempty !
  have hC_ne : ∀ z ∈ Y, (C t z).nonempty,
  { intros z hz,
    obtain ⟨x, hx, hx_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX (hfy z hz), 
    use ⟨x, hx⟩,
    rw [mem_C_iff, subtype.coe_mk],
    refine le_trans _ (hinfi_le z hz),
    rw le_infi_iff, 
    rintro ⟨x', hx'⟩, exact hx_le x' hx', },

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
      apply is_preconnected_iff_subset_of_disjoint_closed.mp (hC_preconnected _ (cY.segment_subset hy1 hy2 hz)) _ _
      (hC_closed _ hy1) (hC_closed _ hy2) (hC_subset _ hz),
      rw [set.disjoint_iff_inter_eq_empty.mp hC_disj, set.inter_empty], },


  let J1 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y1},
  -- do we really need this ? (I can't do without it)
  have mem_J1_iff : ∀ (z : segment ℝ y1 y2), z ∈ J1 ↔ C t z ⊆ C t' y1,
  { intro z, refl, },
  
  have hJ1_closed : is_closed J1, 
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

    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [upper_semicontinuous_on, upper_semicontinuous_within_at] at hfx,
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt'),
    -- We rewrite h into an ∃ᶠ form
    rw filter.cluster_pt_principal_subtype_iff_frequently
      (cY.segment_subset hy1 hy2) at h, 

    suffices this : ∀ᶠ (z : F) in nhds_within y Y,
      (∃ (hz : z ∈ segment ℝ y1 y2), (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1) → (∃ (hz : z ∈ segment ℝ y1 y2), x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1), 
    obtain ⟨z, hz,  hxz, hxz'⟩ := filter.frequently.exists (filter.frequently.mp h this), 
    exact ⟨⟨z, hz⟩, ⟨hxz', hxz⟩⟩,

    { -- this
      apply filter.eventually.mp hfx, 
      apply filter.eventually_of_forall,
      intros z hzt',
      rintro ⟨hz, hz'⟩,
      exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩, }, },

  have hy1_mem_J1 : (⟨y1, left_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J1, 
  { rw mem_J1_iff, apply hC, exact le_of_lt htt', },

  let J2 := { z : segment ℝ y1 y2 | C t z ⊆  C t' y2},
  -- bizarrely, this is necessary to add this lemma, 
  -- rien du genre  rw set.mem_sep_iff ne marche…
  have mem_J2_iff : ∀ (z : segment ℝ y1 y2), z ∈ J2 ↔ C t z ⊆ C t' y2,
  { intro z, refl, },
  have hy2_mem_J2 : (⟨y2, right_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J2,
  { rw mem_J2_iff, apply hC, exact le_of_lt htt', },
  
  have hJ2_closed : is_closed J2, 
  { rw is_closed_iff_cluster_pt, 
    intros y h x hx, 

    suffices : ∃ z ∈ J2, x ∈ C t' (z : F), 
    obtain ⟨z, hz, hxz⟩ := this, 
    suffices : C t' z ⊆ C t' y2, exact this hxz, 

    apply or.resolve_left (hC_subset_or z z.2),
    intro hz2, 

    apply set.nonempty.not_subset_empty (hC_ne z  ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2)),
    rw ← (disjoint_iff_inter_eq_empty.mp hC_disj), 
    refine set.subset_inter (subset_trans (hC t t' z (le_of_lt htt')) hz2) hz, 

    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [upper_semicontinuous_on, upper_semicontinuous_within_at] at hfx,
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt'),
    -- We rewrite h into an ∃ᶠ form
    rw filter.cluster_pt_principal_subtype_iff_frequently
      (cY.segment_subset hy1 hy2) at h, 

    suffices this : ∀ᶠ (z : F) in nhds_within y Y,
      (∃ (hz : z ∈ segment ℝ y1 y2), (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2) → (∃ (hz : z ∈ segment ℝ y1 y2), x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2), 
    obtain ⟨z, hz,  hxz, hxz'⟩ := filter.frequently.exists (filter.frequently.mp h this), 
    exact ⟨⟨z, hz⟩, ⟨hxz', hxz⟩⟩,

    { -- this
      apply filter.eventually.mp hfx, 
      apply filter.eventually_of_forall,
      intros z hzt',
      rintro ⟨hz, hz'⟩,
      exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩, }, },

-- On fait presque deux fois la même chose, il faut unifier les deux trucs.

  have hJ1J2 : J1 ∩ J2 = ∅, 
  { rw set.eq_empty_iff_forall_not_mem, 
    rintros z ⟨hz1, hz2⟩,
    rw mem_J1_iff at hz1, rw mem_J2_iff at hz2,
    apply set.nonempty.not_subset_empty (hC_ne z (cY.segment_subset hy1 hy2 z.prop)), 
    rw [set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self],
    exact set.disjoint_of_subset hz1 hz2 hC_disj, },

  have hJ1_union_J2 : J1 ∪ J2 = set.univ, 
  { rw ← set.top_eq_univ, rw eq_top_iff, intros z hz,
    rw set.mem_union, rw mem_J1_iff, rw mem_J2_iff, 
    cases hC_subset_or z z.prop with h1 h2,
    left, exact set.subset.trans (hC t t' z (le_of_lt htt')) h1,
    right, exact set.subset.trans (hC t t' z (le_of_lt htt')) h2, },

  suffices this : is_preconnected (set.univ : set (segment ℝ y1 y2)),
  { rw is_preconnected_iff_subset_of_disjoint_closed at this,
    specialize this _ _ hJ1_closed hJ2_closed (eq.subset hJ1_union_J2.symm) _,
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


lemma exists_lt_infi_of_lt_infi_of_two' {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y )
  {t : ereal} (ht : t < ⨅ x ∈ X, (f x y1 ⊔ f x y2)) :
  ∃ y0 ∈ Y, t < ⨅ x ∈ X, f x y0 := 
begin
  by_contra' hinfi_le,
  obtain ⟨t' : ereal, htt' : t < t', ht' : t' < ⨅ x ∈ X, f x y1 ⊔ f x y2⟩ := 
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

    -- Uses that X is compact and nonempty !
  have hC_ne : ∀ z ∈ Y, (C t z).nonempty,
  { intros z hz,
    obtain ⟨x, hx, hx_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX (hfy z hz), 
    use ⟨x, hx⟩,
    rw [mem_C_iff, subtype.coe_mk],
    refine le_trans _ (hinfi_le z hz),
    rw le_infi₂_iff, intros x' hx', exact hx_le x' hx', },

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
  { --  from set.disjoint_iff.mpr (λ x hx, not_lt_of_le (infi_le_of_le x $ sup_le_iff.mpr hx) ht'),
    -- marchait avant que je change en ⨅ x ∈ X…… 
    rw set.disjoint_iff, 
    rintro ⟨x, hx⟩, 
    simp only [mem_inter_iff, mem_preimage, function.comp_app, subtype.coe_mk, mem_Iic, mem_empty_iff_false, and_imp],
    intros hxy1 hxy2, 
    rw ← not_le at ht', apply ht', 
    refine infi₂_le_of_le x hx _, 
    simp only [sup_le_iff], 
    exact ⟨hxy1, hxy2⟩, },
  
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
      apply is_preconnected_iff_subset_of_disjoint_closed.mp (hC_preconnected _ (cY.segment_subset hy1 hy2 hz)) _ _
      (hC_closed _ hy1) (hC_closed _ hy2) (hC_subset _ hz),
      rw [set.disjoint_iff_inter_eq_empty.mp hC_disj, set.inter_empty], },


  let J1 := {z : segment ℝ y1 y2 | C t z ⊆ C t' y1},
  -- do we really need this ? (I can't do without it)
  have mem_J1_iff : ∀ (z : segment ℝ y1 y2), z ∈ J1 ↔ C t z ⊆ C t' y1,
  { intro z, refl, },
  
  have hJ1_closed : is_closed J1, 
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

    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [upper_semicontinuous_on, upper_semicontinuous_within_at] at hfx,
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt'),
    -- We rewrite h into an ∃ᶠ form
    rw filter.cluster_pt_principal_subtype_iff_frequently
      (cY.segment_subset hy1 hy2) at h, 

    suffices this : ∀ᶠ (z : F) in nhds_within y Y,
      (∃ (hz : z ∈ segment ℝ y1 y2), (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1) → (∃ (hz : z ∈ segment ℝ y1 y2), x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J1), 
    obtain ⟨z, hz,  hxz, hxz'⟩ := filter.frequently.exists (filter.frequently.mp h this), 
    exact ⟨⟨z, hz⟩, ⟨hxz', hxz⟩⟩,

    { -- this
      apply filter.eventually.mp hfx, 
      apply filter.eventually_of_forall,
      intros z hzt',
      rintro ⟨hz, hz'⟩,
      exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩, }, },

  have hy1_mem_J1 : (⟨y1, left_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J1, 
  { rw mem_J1_iff, apply hC, exact le_of_lt htt', },

  let J2 := { z : segment ℝ y1 y2 | C t z ⊆  C t' y2},
  -- bizarrely, this is necessary to add this lemma, 
  -- rien du genre  rw set.mem_sep_iff ne marche…
  have mem_J2_iff : ∀ (z : segment ℝ y1 y2), z ∈ J2 ↔ C t z ⊆ C t' y2,
  { intro z, refl, },
  have hy2_mem_J2 : (⟨y2, right_mem_segment ℝ y1 y2⟩ : segment ℝ y1 y2) ∈ J2,
  { rw mem_J2_iff, apply hC, exact le_of_lt htt', },
  
  have hJ2_closed : is_closed J2, 
  { rw is_closed_iff_cluster_pt, 
    intros y h x hx, 

    suffices : ∃ z ∈ J2, x ∈ C t' (z : F), 
    obtain ⟨z, hz, hxz⟩ := this, 
    suffices : C t' z ⊆ C t' y2, exact this hxz, 

    apply or.resolve_left (hC_subset_or z z.2),
    intro hz2, 

    apply set.nonempty.not_subset_empty (hC_ne z  ((convex_iff_segment_subset.mp cY) hy1 hy2 z.2)),
    rw ← (disjoint_iff_inter_eq_empty.mp hC_disj), 
    refine set.subset_inter (subset_trans (hC t t' z (le_of_lt htt')) hz2) hz, 

    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
    simp only [upper_semicontinuous_on, upper_semicontinuous_within_at] at hfx,
    specialize hfx x.val x.prop y (cY.segment_subset hy1 hy2 y.prop) t' (lt_of_le_of_lt hx htt'),
    -- We rewrite h into an ∃ᶠ form
    rw filter.cluster_pt_principal_subtype_iff_frequently
      (cY.segment_subset hy1 hy2) at h, 

    suffices this : ∀ᶠ (z : F) in nhds_within y Y,
      (∃ (hz : z ∈ segment ℝ y1 y2), (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2) → (∃ (hz : z ∈ segment ℝ y1 y2), x ∈ C t' z ∧ (⟨z, hz⟩ : segment ℝ y1 y2) ∈ J2), 
    obtain ⟨z, hz,  hxz, hxz'⟩ := filter.frequently.exists (filter.frequently.mp h this), 
    exact ⟨⟨z, hz⟩, ⟨hxz', hxz⟩⟩,

    { -- this
      apply filter.eventually.mp hfx, 
      apply filter.eventually_of_forall,
      intros z hzt',
      rintro ⟨hz, hz'⟩,
      exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩, }, },

-- On fait presque deux fois la même chose, il faut unifier les deux trucs.

  have hJ1J2 : J1 ∩ J2 = ∅, 
  { rw set.eq_empty_iff_forall_not_mem, 
    rintros z ⟨hz1, hz2⟩,
    rw mem_J1_iff at hz1, rw mem_J2_iff at hz2,
    apply set.nonempty.not_subset_empty (hC_ne z (cY.segment_subset hy1 hy2 z.prop)), 
    rw [set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self],
    exact set.disjoint_of_subset hz1 hz2 hC_disj, },

  have hJ1_union_J2 : J1 ∪ J2 = set.univ, 
  { rw ← set.top_eq_univ, rw eq_top_iff, intros z hz,
    rw set.mem_union, rw mem_J1_iff, rw mem_J2_iff, 
    cases hC_subset_or z z.prop with h1 h2,
    left, exact set.subset.trans (hC t t' z (le_of_lt htt')) h1,
    right, exact set.subset.trans (hC t t' z (le_of_lt htt')) h2, },

  suffices this : is_preconnected (set.univ : set (segment ℝ y1 y2)),
  { rw is_preconnected_iff_subset_of_disjoint_closed at this,
    specialize this _ _ hJ1_closed hJ2_closed (eq.subset hJ1_union_J2.symm) _,
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


/- lemma exists_lt_infi_of_lt_infi_of_finite {s : set F} (hs : s.finite) {t : ℝ} (ht : (t : ereal) < infi (λ x : X, supr (λ y : s, f x y))) :
  s ⊆ Y → ∃ y0 ∈ Y,  (t : ereal) < infi (λ x : X, f x y0) :=
begin
  revert X, 
--  
--  revert ht,
  apply hs.induction_on, 
  { -- empty case 
    intros X ne_X cX kX hfx hfx' hfy hfy', 
    haveI : nonempty X := nonempty.coe_sort ne_X,  
    simp only [csupr_of_empty, cinfi_const, not_lt_bot, is_empty.forall_iff], },

  intros b s has hs hrec X ne_X cX kX hfx hfx' hfy hfy' ht hs'Y, 
  have hb : b ∈ Y := hs'Y (mem_insert b s), 
  -- obtain ⟨t' : ereal, htt', ht'_lt_infi_supr⟩ :=  exists_between ht, 
  let X' := { x ∈ X | f x b ≤ t },
  cases set.eq_empty_or_nonempty X' with X'_e X'_ne,
  { -- X' = ∅, 
    use b, split, apply hs'Y, exact mem_insert b s,

/-    apply lt_of_lt_of_le htt',  
  rw le_infi_iff,
    
    rintro ⟨x, hx⟩,
    suffices : x ∉ X', 
    simp only [mem_sep_iff, not_and, not_le] at this,
    exact le_of_lt (this hx), 
    rw X'_e, exact not_mem_empty x, -/
  
    -- version d'avant, lorsqu'on avait t'=t
    rw ← not_le,
    intro h, 
    rw set.eq_empty_iff_forall_not_mem  at X'_e,
    
    obtain ⟨x, hx, hx_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX (hfy b hb), 
    specialize X'_e x, 
    apply X'_e, simp only [set.mem_sep_iff], 
    apply and.intro hx, 
    refine le_trans _ h,
    rw le_infi_iff, 
    rintro ⟨x, hx⟩, exact hx_le x hx, },
  
  suffices kX' : is_compact X',
  suffices cX' : convex ℝ X', 
  suffices hX'X : X' ⊆ X, 
  suffices lt_of : ∀ (f g : E → ereal) (hg : lower_semicontinuous_on g X)
    (hf_le_g : ∀ x ∈ X, f x ≤ g x), ⨅ x ∈ X', f x  < ⨅ x ∈ X, g x, 

  { 
    specialize hrec X' X'_ne cX' kX', 
    obtain ⟨y1, hy1, hty1⟩ := hrec _ _ _ _ _ _,
    { refine exists_lt_infi_of_lt_infi_of_two X ne_X cX kX Y cY f hfx hfx' hfy hfy' hb hy1 _, 

      suffices : lower_semicontinuous_on (λ x, f x b ⊔ f x y1) X,
      obtain ⟨a, ha, hfa_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX this,
      suffices : infi (λ x : X, f x b ⊔ f x y1) = f a b ⊔ f a y1,
      rw this,
      by_cases ha' : a ∈ X',
      { refine lt_of_lt_of_le hty1 _, 
        refine le_trans _ (le_sup_right),
        refine infi_le _ (⟨a, ha'⟩ : X'), },
      { simp only [mem_sep_iff, not_and, not_le] at ha', 
        exact lt_of_lt_of_le (ha' ha) (le_sup_left), },
      
      { apply le_antisymm, 
        apply infi_le _ (⟨a, ha⟩ : X),
        rw le_infi_iff, rintros ⟨x, hx⟩, exact hfa_le x hx, },
      { apply lower_semicontinuous_on_sup, 
        exact hfy b hb, exact hfy y1 hy1, }, },
    { intros x hx', exact hfx x (hX'X hx'), },
    { intros x hx', exact hfx' x (hX'X hx'), },
    { intros y hy, apply lower_semicontinuous_on.mono (hfy y hy) hX'X, },
    { intros y hy, exact cX'.quasiconvex_on_restrict (hfy' y hy) hX'X, },
    { suffices : lower_semicontinuous_on (λ x, ⨆ y ∈ s, f x y) X',
      obtain ⟨a, ha, hfa_le⟩:= lower_semicontinuous.exists_infi_of_is_compact X'_ne kX' this,

    sorry,
    sorry, },
    { apply subset.trans (subset_insert b s) hs'Y, }, },
  sorry, -- peut-être à virer
  { intros x, simp only [mem_sep_iff], exact and.elim_left, },

  { sorry, },
  { sorry, },
end
 -/

lemma exists_lt_infi_of_lt_infi_of_finite {s : set F} (hs : s.finite) {t : ereal} (ht : t < ⨅ x ∈ X, ⨆ y ∈ s, f x y) :
  s ⊆ Y → ∃ y0 ∈ Y,  t < ⨅ x ∈ X, f x y0 :=
begin
  revert X, 
--  
--  revert ht,
  apply hs.induction_on, 
  { -- empty case 
    intros X ne_X cX kX hfx hfx' hfy hfy', 
    haveI : nonempty X := nonempty.coe_sort ne_X,
    -- intro ht, exfalso,
    simp only [binfi_const ne_X, mem_empty_iff_false, csupr_false, csupr_const, not_lt_bot, is_empty.forall_iff], },

  intros b s has hs hrec X ne_X cX kX hfx hfx' hfy hfy' ht hs'Y, 
  have hb : b ∈ Y := hs'Y (mem_insert b s), 
  -- obtain ⟨t' : ereal, htt', ht'_lt_infi_supr⟩ :=  exists_between ht, 
  let X' := { x ∈ X | f x b ≤ t },
  cases set.eq_empty_or_nonempty X' with X'_e X'_ne,
  { -- X' = ∅, 
    use b, split, apply hs'Y, exact mem_insert b s,
    rw ← not_le,
    intro h, 
    rw set.eq_empty_iff_forall_not_mem  at X'_e,
    
    obtain ⟨x, hx, hx_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_X kX (hfy b hb), 
    specialize X'_e x, 
    apply X'_e, simp only [set.mem_sep_iff], 
    exact ⟨hx, le_trans (le_infi₂_iff.mpr hx_le) h⟩, },
  
  suffices hX'X : X' ⊆ X, 
  suffices kX' : is_compact X',
  have cX' : convex ℝ X' := hfy' b hb t, 
  --suffices lt_of : ∀ (f g : E → ereal) (hg : lower_semicontinuous_on g X)(hf_le_g : ∀ x ∈ X, f x ≤ g x), ⨅ x ∈ X', f x  < ⨅ x ∈ X, g x, 

  { 
    specialize hrec X' X'_ne cX' kX', 
    obtain ⟨y1, hy1, hty1⟩ := hrec _ _ _ _ _ _,
    { refine exists_lt_infi_of_lt_infi_of_two' X ne_X cX kX Y cY f hfx hfx' hfy hfy' hb hy1 _, 

      suffices : lower_semicontinuous_on (λ x, f x b ⊔ f x y1) X,
      obtain ⟨a, ha, hfa_eq_inf⟩ := lower_semicontinuous.exists_infi_of_is_compact ne_X kX this,
      rw ← hfa_eq_inf, 
      by_cases ha' : a ∈ X',
      { refine lt_of_lt_of_le hty1 _, 
        refine le_trans _ (le_sup_right),
        refine (infi₂_le_of_le a ha') (le_refl _), },
      { simp only [mem_sep_iff, not_and, not_le] at ha', 
        exact lt_of_lt_of_le (ha' ha) (le_sup_left), },
      { apply lower_semicontinuous_on.sup, 
        exact hfy b hb, exact hfy y1 hy1, }, },
    { intros x hx', exact hfx x (hX'X hx'), },
    { intros x hx', exact hfx' x (hX'X hx'), },
    { intros y hy, apply lower_semicontinuous_on.mono (hfy y hy) hX'X, },
    { intros y hy, exact cX'.quasiconvex_on_restrict (hfy' y hy) hX'X, },
    { /- sinon, si  infi x ∈ X', supr y ∈ s f x y ≤ t
        pour tout t' > t, il existe x ∈ X', supr y ∈ s f x y ≤ t',
        comme x ∈ X' et t ≤ t', on  a supr y ∈ insert b s f x y  ≤ t', 
        donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t',
        donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t    
      -/
      rw [← not_le, infi₂_le_iff] at ht ⊢,
      push_neg at ht ⊢, 
      obtain ⟨t', ht', htt'⟩ := ht,
      use t', apply and.intro _ htt',
      intros x hx, 
      specialize ht' x (hX'X hx),
      simp only [set.insert_eq] at ht', 
      rw supr_union at ht', 
      simp only [mem_singleton_iff, supr_supr_eq_left, le_sup_iff] at ht', 
      apply or.resolve_left ht', 
      rw not_le,
      apply lt_of_le_of_lt _ htt',
      exact hx.2, },
    { apply subset.trans (subset_insert b s) hs'Y, }, },
  
  
  { suffices this : X' = coe '' (coe ⁻¹' X' : set X), 
    rw this, rw (inducing_coe).is_compact_iff, 
    haveI : compact_space ↥X := is_compact_iff_compact_space.mp kX,
    apply is_closed.is_compact, 
    rw (inducing_coe).is_closed_iff,

    specialize hfy b hb, 
    rw lower_semicontinuous_on_iff_preimage_Iic at hfy,
    obtain ⟨v, hv, hv'⟩ := hfy t, 
    use v, 
    apply and.intro hv, 
    rw subtype.preimage_coe_eq_preimage_coe_iff,
    rw ← hv',
    ext x,simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_sep_iff, and.congr_left_iff, iff_and_self],
    exact λ w z, w, 

    rw set.image_preimage_eq_inter_range,
    simp only [subtype.range_coe_subtype, set_of_mem_eq],
    rw set.inter_eq_self_of_subset_left hX'X, },

  { intros x, simp only [mem_sep_iff], exact and.elim_left, },
end

example {a b : ℝ} : a ≤ b ↔  ∀ (c : ℝ), c < a → c < b :=
begin
exact forall_lt_iff_le.symm,
end

theorem minimax : (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := 
begin
  apply le_antisymm,
  { rw ← forall_lt_iff_le, 
    intros t ht, 
    let X' : F → set E := λ y, { x ∈ X | f x y ≤ t },
 --   suffices kX' : ∀ y ∈ Y, is_compact (X' y),
    suffices hs : ∃ (s : set F), s ⊆ Y ∧ s.finite ∧ (⨅ y ∈ s, X' y) = ∅, 
    obtain ⟨s, hsY, hs, hes⟩ := hs, 
    suffices hst : t < ⨅ (x : E) (H : x ∈ X), ⨆ (y : F) (H : y ∈ s), f x y,
    obtain ⟨y0, hy0, ht0⟩ :=  exists_lt_infi_of_lt_infi_of_finite 
      X ne_X cX kX Y cY f hfx hfx' hfy hfy' hs hst hsY,
    apply lt_of_lt_of_le ht0,
    apply le_supr₂_of_le y0 hy0 (le_refl _),

    { -- hst
      suffices hlsc : lower_semicontinuous_on (λ x, ⨆ y ∈ s, f x y) X, 
      obtain ⟨a, ha, ha'⟩ := lower_semicontinuous.exists_infi_of_is_compact ne_X kX hlsc,
      rw ← ha', dsimp, 
      rw ← not_le, 
      rw supr₂_le_iff, 
      intro hes', 
      rw set.eq_empty_iff_forall_not_mem  at hes,
      apply hes a, 
      simp only [infi_eq_Inter, mem_Inter, mem_sep_iff],
      intros y hy, 
      exact ⟨ha, hes' y hy⟩,

      apply lower_semicontinuous_on_supr₂ hs (λ i hi, hfy i (hsY hi)), },
    suffices eX' : (⨅ y ∈ Y, (X' y)) = ∅,

    /- eX' : intersection de fermés du compact X est vide -/
    suffices hfyt : ∀ y : Y, ∃ v : set E, is_closed v ∧ X' y = v ∩ X,
    let v : Y → set E := λ y, (hfyt y).some,
    obtain ⟨s, hs⟩ := kX.elim_finite_subfamily_closed v (λ y, (hfyt y).some_spec.1) _,
    have hs_ne : s.nonempty, 
    { rw finset.nonempty_iff_ne_empty, intro hs_e, 
      simp only [hs_e, finset.not_mem_empty, Inter_of_empty, Inter_univ, inter_univ] at hs, 
      rw set.nonempty_iff_ne_empty at ne_X, exact ne_X hs, },

    use (coe : Y → F) '' ↑s,
    split, exact subtype.coe_image_subset Y ↑s,
    split, exact (coe '' ↑s).to_finite,
    rw set.eq_empty_iff_forall_not_mem at hs ⊢,
    intros x hx, 
    simp only [mem_image, finset.mem_coe, set_coe.exists, subtype.coe_mk,
      exists_and_distrib_right, exists_eq_right, infi_eq_Inter,
      Inter_exists, mem_Inter, mem_sep_iff] at hx, 
    apply hs x,
    simp only [Inter_coe_set, mem_inter_iff, mem_Inter],
    split,
    obtain ⟨⟨j, hj⟩, hjs⟩ := hs_ne, 
    exact (hx j hj hjs).1,

    intros y hy hy',
    apply set.inter_subset_left,
    rw ← (hfyt (⟨y, hy⟩ : Y)).some_spec.2,
    simp only [subtype.coe_mk, mem_sep_iff],
    exact hx y hy hy',
    
    rw set.eq_empty_iff_forall_not_mem at eX' ⊢,
    intros x hx,
    simp only [subtype.coe_mk, mem_inter_iff] at hx, 
    apply eX' x, 
    simp only [infi_eq_Inter, mem_Inter],
    intros y hy, 
    rw ← subtype.coe_mk y hy,
    rw (hfyt (⟨y, hy⟩ : Y)).some_spec.2,
    apply and.intro _ hx.1,
    apply (Inter_subset (λ i, Exists.some (hfyt i))),
    exact hx.2, 

    rintro ⟨y, hy⟩,
    specialize hfy y hy,
    simp_rw lower_semicontinuous_on_iff_preimage_Iic at hfy,
    obtain ⟨v, v_closed, hv⟩ := hfy t,
    use v, apply and.intro v_closed,
    rw ← hv, 
    ext x, simp only [subtype.coe_mk, mem_sep_iff, mem_inter_iff, mem_preimage, mem_Iic], rw and_comm,

    rw ← not_le at ht,
    rw set.eq_empty_iff_forall_not_mem,
    intros x hx,
    simp only [infi_eq_Inter, mem_Inter, mem_sep_iff] at hx, 
    apply ht, 
    apply infi₂_le_of_le x _ _, 
    
    suffices : Y.nonempty,
    obtain ⟨j, hj⟩ := this,
    exact (hx j hj).1,
    rw set.nonempty_iff_ne_empty, intro hY_e, 
    apply ht, rw hY_e, simp only [mem_empty_iff_false, csupr_false, csupr_const], 
    obtain ⟨i, hi⟩ := ne_X,
    apply infi₂_le_of_le i hi _, exact bot_le,

    rw supr₂_le_iff, exact λ i hi, (hx i hi).2, },
  { exact supr₂_infi₂_le_infi₂_supr₂ X Y f, },
end

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
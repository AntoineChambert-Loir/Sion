
import analysis.convex.basic
import topology.semicontinuous
import analysis.convex.quasiconvex
import topology.order.lower_topology

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

section semicontinuity

/- 

- `lower_semicontinuous.is_compact.exists_forall_le` : We prove that lower semicontinuous functions attain their lower bound on a nonempty compact set.

- `lower_semicontinuous.bdd_below_on.is_compact` : As a consequence, a lower semicontinuous function on a compact set is bounded below. 

We then prove the opposite results for upper semicontinuous functions :

- `upper_semicontinuous.is_compact.exists_forall_ge`

- `bdd_above_on.is_compact` 

The proofs follow Bourbaki, *General Topology*, chapter 4, §6, n°2. 
I do them twice (copy paste worked well), without trying to get ones
from the other by passing to the opposite order on `β`. 

However, they could also be done using the general machinery already in mathlib,
namely proving that a function `f: α → β` is upper semicontinuous iff it is continuous 
when `β` is endowed with `with_lower_topology β`, and characterizing
the compact sets of `with_lower_topology β` as those which have a maximal element. 

I tried to do so but quickly bumped on missing instances, 
such as `complete_linear_order_topology (with_lower_topology β)`. 

In any case, `with_upper_topology` is missing, so we should also play with
the opposite order.  

Another difficulty is the type of order we want to impose on β.
Ultimately, it has to be `conditionally_complete_linear_order β`, to allow for `ℝ`,
but it would simplify the proofs to do it for `complete_linear_order β`,
and adding `⊤` and `⊥` at the end if needed. 
Inded, for `conditionally_complete_linear_order β`, the `supr` and `infi` only
do what one expects under additional `bdd_above` or `bdd_below` assumptions
which are painful to check each time.
(Moreover, the `simp` lemmas may be missing. )

-/

variables {α : Type*} [topological_space α]
variables  {β : Type*}
  [topological_space β] [conditionally_complete_linear_order β] [order_topology β] 
variable {f : α → β}

section lower_semicontinuous

/-- A lower semicontinuous function attains its lowers bound on a nonempty compact set -/
theorem lower_semicontinuous.is_compact.exists_forall_le {s : set α} 
  (ne_s : s.nonempty) (hs : is_compact s)
  (hf : lower_semicontinuous_on f s) : 
  ∃ (a ∈ s), ∀ x ∈ s, f a ≤ f x := 
begin
  suffices : filter.is_basis s (λ a, s ∩ f ⁻¹' (set.Iic (f a))),
  let ℱ := this.filter,
  haveI : this.filter.ne_bot, 
  { rw filter.ne_bot_iff, 
    intro h,
    suffices : ∅ ∈ this.filter, 
    rw filter.is_basis.mem_filter_iff at this,
    obtain ⟨a, ha, ha'⟩ := this,
    rw set.subset_empty_iff at ha',
    apply set.not_mem_empty a, rw ← ha',  
    split, exact ha, 
    rw set.mem_preimage, rw set.mem_Iic,
    rw h, exact filter.mem_bot, },

  suffices that : this.filter ≤ filter.principal s, 
  obtain ⟨a, ha, h⟩ := hs that, 
  
  use a, use ha, 
  rw cluster_pt_iff at h,
  intros x hx,
  by_contradiction hax, simp only [not_le] at hax,
  suffices hU : sᶜ ∪ (f ⁻¹' (set.Ioi (f x))) ∈ nhds a,  
  suffices hV : s ∩ (f ⁻¹' (set.Iic (f x))) ∈ this.filter,
  obtain ⟨y, hy, ⟨hys, hy'⟩⟩ := h hU hV,
  rw [set.mem_preimage, set.mem_Iic] at hy', 
  cases hy with hy hy,
  { exact hy hys, },
  rw [set.mem_preimage, set.mem_Ioi] at hy,
  exact not_le.mpr hy hy',
  { -- hV 
  rw filter.is_basis.mem_filter_iff,
  use x, use hx, },
  { -- hU 
    dsimp [lower_semicontinuous_on, lower_semicontinuous_within_at] at hf,
    specialize hf a ha _ hax, 
    obtain ⟨𝒩, h𝒩, t, ht, hh⟩ := hf, 
    simp at ht, 
    apply filter.mem_of_superset h𝒩, 
    rw set.union_comm, rw set.subset_union_compl_iff_inter_subset, 
    refine set.subset.trans (set.inter_subset_inter_right 𝒩 ht) _,
    rw ← hh,
    apply eq.subset,
    refl,},
  { -- that: this.filter ≤ filter.principal s
    simp only [filter.le_principal_iff],
    rw filter.is_basis.mem_filter_iff ,
    obtain ⟨a, ha⟩ := ne_s, 
    exact ⟨a, ha, set.inter_subset_left s _⟩, },
  { -- this: filter.is_basis
    apply filter.is_basis.mk,
    exact ne_s, 
    intros a a' ha ha', 
    cases le_total (f a) (f a'), 
    { use a, use ha, 
      apply eq.subset, apply symm,
      rw set.inter_eq_left_iff_subset,
      apply set.inter_subset_inter_right, 
      apply set.preimage_mono,
      rw set.Iic_subset_Iic, exact h, }, 
    { use a', use ha', 
      apply eq.subset, apply symm, 
      rw set.inter_eq_right_iff_subset ,
      apply set.inter_subset_inter_right, 
      apply set.preimage_mono,
      rw set.Iic_subset_Iic, exact h, }, },
end

/-- A lower semicontinuous function is bounded above on a compact set. -/
lemma lower_semicontinuous.bdd_below_on.is_compact [nonempty β] {s : set α} (hs : is_compact s) (hf : lower_semicontinuous_on f s): 
  bdd_below (f '' s) := 
begin
  cases s.eq_empty_or_nonempty,
  { rw h, simp only [set.image_empty],
    have : ∃ (b : β), true, exact (exists_const β).mpr trivial, 
    obtain ⟨b,_⟩ := this,
    use b, simp only [lower_bounds_empty], },
  obtain ⟨a, ha, has⟩ := lower_semicontinuous.is_compact.exists_forall_le h hs hf, 
  use f a, rintros b ⟨x, hx, rfl⟩, exact has x hx,
end


end lower_semicontinuous

section upper_semicontinuous


/-- An upper semicontinuous function attains its upper bound on a nonempty compact set -/
theorem upper_semicontinuous.is_compact.exists_forall_ge 
{s : set α} (hs : is_compact s) (ne_s : s.nonempty) (hf : upper_semicontinuous_on f s): 
  ∃ (a ∈ s), ∀ x ∈ s, f x ≤ f a := 
begin
  suffices : filter.is_basis s (λ a, s ∩ f ⁻¹' (set.Ici (f a))),
  let ℱ := this.filter,
  haveI : this.filter.ne_bot, 
  { rw filter.ne_bot_iff, 
    intro h,
    suffices : ∅ ∈ this.filter, 
    rw filter.is_basis.mem_filter_iff at this,
    obtain ⟨a, ha, ha'⟩ := this,
    rw set.subset_empty_iff at ha',
    apply set.not_mem_empty a, rw ← ha',  
    split, exact ha, 
    rw set.mem_preimage, rw set.mem_Ici,
    rw h, exact filter.mem_bot, },

  suffices that : this.filter ≤ filter.principal s, 
  obtain ⟨a, ha, h⟩ := hs that, 
  
  use a, use ha, 
  rw cluster_pt_iff at h,
  intros x hx,
  by_contradiction hax, simp only [not_le] at hax,
  suffices hU : sᶜ ∪ (f ⁻¹' (set.Iio (f x))) ∈ nhds a,  
  suffices hV : s ∩ (f ⁻¹' (set.Ici (f x))) ∈ this.filter,
  obtain ⟨y, hy, ⟨hys, hy'⟩⟩ := h hU hV,
  rw [set.mem_preimage, set.mem_Ici] at hy', 
  cases hy with hy hy,
  { exact hy hys, },
  rw [set.mem_preimage, set.mem_Iio] at hy,
  exact not_le.mpr hy hy',
  { -- hV 
  rw filter.is_basis.mem_filter_iff,
  use x, use hx, },
  { -- hU 
    dsimp [upper_semicontinuous_on, upper_semicontinuous_within_at] at hf,
    specialize hf a ha _ hax, 
    obtain ⟨𝒩, h𝒩, t, ht, hh⟩ := hf, 
    simp at ht, 
    apply filter.mem_of_superset h𝒩, 
    rw set.union_comm, rw set.subset_union_compl_iff_inter_subset, 
    refine set.subset.trans (set.inter_subset_inter_right 𝒩 ht) _,
    rw ← hh,
    apply eq.subset,
    refl,},
  { -- that: this.filter ≤ filter.principal s
    simp only [filter.le_principal_iff],
    rw filter.is_basis.mem_filter_iff ,
    obtain ⟨a, ha⟩ := ne_s, 
    exact ⟨a, ha, set.inter_subset_left s _⟩, },
  { -- this: filter.is_basis
    apply filter.is_basis.mk,
    exact ne_s, 
    intros a a' ha ha', 
    cases le_total (f a) (f a'), 
    { use a', use ha', 
      apply eq.subset, apply symm, 
      rw set.inter_eq_right_iff_subset ,
      apply set.inter_subset_inter_right, 
      apply set.preimage_mono,
      rw set.Ici_subset_Ici, exact h, },
    { use a, use ha, 
      apply eq.subset, apply symm,
      rw set.inter_eq_left_iff_subset,
      apply set.inter_subset_inter_right, 
      apply set.preimage_mono,
      rw set.Ici_subset_Ici, exact h, }, },
end

/-- An upper semicontinuous function is bounded above on a compact set. -/
lemma bdd_above_on.is_compact [nonempty β] {s : set α}
  (hf : upper_semicontinuous_on f s) (hs : is_compact s): 
  bdd_above (f '' s) := 
begin
  cases s.eq_empty_or_nonempty,
  { rw h, simp only [set.image_empty],
    have : ∃ (b : β), true, exact (exists_const β).mpr trivial, 
    obtain ⟨b,_⟩ := this,
    use b, simp only [upper_bounds_empty], },
  
  obtain ⟨a, ha, has⟩ := upper_semicontinuous.is_compact.exists_forall_ge hs h hf, 
  use f a, rintros b ⟨x, hx, rfl⟩, exact has x hx,
end

end upper_semicontinuous

end semicontinuity

section quasiconcave

/- We prove that a lsc quasiconcave function on a nonempty compact convex set 
is bounded above and attains its upper bound. 

Maybe the result is false, I don't know. 

-/
variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variable {f : E → ℝ}

/-- A quasiconcave and lower semicontinuous function attains its upper bound on a nonempty compact set -/
lemma is_compact.exists_forall_ge_of_quasiconcave {s : set E}
  (ne_s : s.nonempty) (hs : is_compact s) 
  (hfs : lower_semicontinuous_on f s) (hfc : quasiconcave_on ℝ s f):
  ∃ (a ∈ s), ∀ x ∈ s, f x ≤ f a := sorry  

/-- A quasiconcave and lower semicontinuous function is bounded above on a compact set -/
lemma bdd_above_on.is_compact_of_quasiconcave  {s : set E} (hs : is_compact s)
  (hfs : lower_semicontinuous_on f s)(hfc : quasiconcave_on ℝ s f) : 
  bdd_above (f '' s) := 
begin
  cases s.eq_empty_or_nonempty with e_s ne_s,
  { rw e_s, simp only [set.image_empty, bdd_above_empty], },
  { obtain ⟨a, ha, hax⟩ := is_compact.exists_forall_ge_of_quasiconcave ne_s hs hfs hfc,
    use f a, rintros t ⟨x, hx, rfl⟩, exact hax x hx, },
end

end quasiconcave


section quasiconvex


/- We prove that a usc quasiconvex function on a nonempty compact convex set 
is bounded below and attains its lower bound. 

Maybe the result is false, I don't know. 

-/

variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variable {f : E → ℝ}

/-- A quasiconvex and upper semicontinuous function attains its lower bound on a nonempty compact set -/
lemma is_compact.exists_forall_le_of_quasiconvex {s : set E}
  (ne_s : s.nonempty) (hs : is_compact s)
  (hfs : upper_semicontinuous_on f s) (hfc : quasiconvex_on ℝ s f):
  ∃ (a ∈ s), ∀ x ∈ s, f a ≤ f x := sorry  

/-- A quasiconvex and upper semicontinuous function is bounded below on a compact set -/
lemma bdd_below_on.is_compact_of_quasiconvex  {s : set E}
  (hs : is_compact s)
  (hfs : upper_semicontinuous_on f s) (hfc : quasiconvex_on ℝ s f): bdd_below (f '' s) := 
begin
  cases s.eq_empty_or_nonempty with e_s ne_s,
  { rw e_s, simp only [set.image_empty, bdd_below_empty], },
  { obtain ⟨a, ha, hax⟩ := is_compact.exists_forall_le_of_quasiconvex ne_s hs hfs hfc,
    use f a, rintros t ⟨x, hx, rfl⟩, exact hax x hx, },
end

end quasiconvex

section sion 

variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variables 
 {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] [has_continuous_add F] [has_continuous_smul ℝ F]
variables (X : set E) (ne_X : X.nonempty) (cX : convex ℝ X) (kX : is_compact X)
variables (Y : set F) (ne_Y : Y.nonempty) (cY : convex ℝ Y)

variable (f : E → F → ℝ) 

def is_saddle_point_on {a : E} (ha : a ∈ X) {b : F} (hb : b ∈Y) :=
(∀ x ∈ X, f a b ≤ f x b) ∧ (∀ y ∈ Y, f a y ≤ f a b) 

namespace sion 

variables (hfx : ∀ x ∈ X, upper_semicontinuous_on (λ y : F, f x y) Y) (hfx' : ∀ x ∈ X, quasiconcave_on ℝ Y (λ y, f x y))
variables (hfy : ∀ y ∈ Y, lower_semicontinuous_on (λ x : E, f x y) X) (hfy' : ∀ y ∈ Y, quasiconvex_on ℝ X (λ x, f x y))

include hfx hfx' ne_X cX kX hfy hfy' ne_Y cY

lemma is_bdd_above : bdd_above (set.range (λ (xy : X × Y), f xy.1 xy.2))  := sorry

lemma is_bdd_below : bdd_below (set.range (λ (xy : X × Y), f xy.1 xy.2)) := sorry 

/-- The minimax theorem, in the saddle point form -/
theorem exists_saddle_point : ∃ (a : E) (ha : a ∈ X) (b : F) (hb : b ∈ Y),
  is_saddle_point_on X Y f ha hb := sorry

end sion 

variables (hfx : ∀ x ∈ X, upper_semicontinuous_on (λ y : F, f x y) Y) (hfx' : ∀ x ∈ X, quasiconcave_on ℝ Y (λ y, f x y))
variables (hfy : ∀ y ∈ Y, lower_semicontinuous_on (λ x : E, f x y) X) (hfy' : ∀ y ∈ Y, quasiconvex_on ℝ X (λ x, f x y))

include hfx hfx' ne_X cX kX hfy hfy' ne_Y cY

example (s t : set ℝ) (h : s ⊆ t) (ht : bdd_below t): bdd_below s :=
bdd_below.mono h ht

-- There are some `sorry` because we need to add the proof that the
-- function is bounded on X Y 
/-- The minimax theorem, in the inf-sup equals sup-inf form -/
theorem sion : 
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

section junk

/- 
Attempts to do the job without reproving anything

but one gets to prove [complete_linear_order_topology (with_lower_topology β)]
-/

variables {α β : Type*} [topological_space α] [preorder β] [topological_space β] [order_topology β]

variable (f : α → β)

open with_lower_topology
namespace with_lower_topology

lemma to_lower_continous : 
  continuous (to_lower : β → with_lower_topology β):= sorry

lemma of_lower_upper_semicontinous : 
  upper_semicontinuous (of_lower : with_lower_topology β → β):= sorry

lemma upper_semicontinuous_iff_to_lower_comp_continuous_at {a : α} :
  upper_semicontinuous_at f a ↔ continuous_at (to_lower ∘ f) a := 
sorry

lemma upper_semicontinuous_iff_to_lower_comp_continuous :
  upper_semicontinuous f ↔ continuous (to_lower ∘ f) := sorry

lemma upper_semicontinuous_iff_to_lower_comp_continuous_on {s : set α} :
  upper_semicontinuous_on f s ↔ continuous_on (to_lower ∘ f) s := sorry

end with_lower_topology


end junk
import topology.semicontinuous

import topology.order.lower_topology

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

lemma lower_semicontinuous_on_iff_restrict {s : set α} : 
  lower_semicontinuous_on f s ↔
  lower_semicontinuous (s.restrict f) := sorry

lemma lower_semicontinuous_on_iff_preimage_Ioi {s : set α} :
  lower_semicontinuous_on f s ↔ 
  ∀ x ∈ s, ∀ b, b < f x →  
  ∃ (u : set α), is_open u ∧ f ⁻¹' (set.Ioi b) ∩ s = u ∩ s :=
sorry

lemma lower_semicontinuous_on_iff_preimage_Iic {s : set α} :
  lower_semicontinuous_on f s ↔ 
  ∀ b, ∃ (v : set α), is_closed v ∧ f ⁻¹' (set.Iic b) ∩ s = v ∩ s :=
sorry

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
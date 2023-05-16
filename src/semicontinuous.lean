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
And indeed, `with_lower_topology β` does ***not*** satisfy `order_topology` !

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

open_locale filter topology
open set filter

lemma is_total.directed {α : Type*} {ι : Sort*} (r : α → α → Prop) [is_total α r] (f : ι → α) :
  directed r f :=
λ i j, or.cases_on (total_of r (f i) (f j)) (λ h, ⟨j, h, refl _⟩) (λ h, ⟨i, refl _, h⟩)

section linear_order

variables {β α : Type*} [topological_space α] [topological_space β] {f : α → β}
variables [linear_order β] [order_closed_topology β] 

section lower_semicontinuous

lemma lower_semicontinuous_within_at_sup {g : α → β} (s : set α) (a : α)
  (hf : lower_semicontinuous_within_at f s a) (hg : lower_semicontinuous_within_at g s a) :
  lower_semicontinuous_within_at (λ x, f x ⊔ g x) s a :=
begin
  intros b hb, 
  simp only [lt_sup_iff] at hb ⊢,  
  cases hb with hb hb, 
  refine eventually.mp (hf b hb) (eventually_of_forall (λ x hx, or.intro_left _ hx)), 
  refine eventually.mp (hg b hb) (eventually_of_forall (λ x hx, or.intro_right _ hx)), 
end

lemma lower_semicontinuous_at_sup {g : α → β} (a : α)
  (hf : lower_semicontinuous_at f a) (hg : lower_semicontinuous_at g a) :
  lower_semicontinuous_at (λ x, f x ⊔ g x) a :=
begin
  intros b hb, 
  simp only [lt_sup_iff] at hb,  
  cases hb with hb hb, 
  refine eventually.mp (hf b hb) (eventually_of_forall
    (λ x hx, lt_of_lt_of_le hx (le_sup_left))), 
  refine eventually.mp (hg b hb) (eventually_of_forall
    (λ x hx, lt_of_lt_of_le hx (le_sup_right))),
end

lemma lower_semicontinuous_on_sup {s : set α} {g : α → β}
  (hf : lower_semicontinuous_on f s) (hg : lower_semicontinuous_on g s) :
  lower_semicontinuous_on (λ x, f x ⊔ g x) s :=  λ a ha, lower_semicontinuous_within_at_sup s a (hf a ha) (hg a ha)

lemma lower_semicontinuous_sup {g : α → β}
  (hf : lower_semicontinuous f) (hg : lower_semicontinuous g) :
  lower_semicontinuous (λ x, f x ⊔ g x) := 
λ a, lower_semicontinuous_at_sup a (hf a) (hg a)

lemma lower_semicontinuous_within_at_inf {g : α → β} (s : set α) (a : α)
  (hf : lower_semicontinuous_within_at f s a) (hg : lower_semicontinuous_within_at g s a) :
   lower_semicontinuous_within_at (λ x, f x ⊓ g x) s a :=
begin
  intros b hb, 
  simp only [lt_inf_iff] at hb ⊢, 
  exact eventually.and (hf b hb.1) (hg b hb.2),
end

lemma lower_semicontinuous_at_inf {g : α → β} (a : α)
  (hf : lower_semicontinuous_at f a) (hg : lower_semicontinuous_at g a) :
   lower_semicontinuous_at (λ x, f x ⊓ g x) a :=
begin
  intros b hb,
  simp only [lt_inf_iff] at hb ⊢,
  exact eventually.and (hf b hb.1) (hg b hb.2),
end

lemma lower_semicontinuous_on_inf {g : α → β} (s : set α)
  (hf : lower_semicontinuous_on f s) (hg : lower_semicontinuous_on g s) :
   lower_semicontinuous_on (λ x, f x ⊓ g x) s :=
λ a ha, lower_semicontinuous_within_at_inf s a (hf a ha) (hg a ha)

lemma lower_semicontinuous_inf {g : α → β} 
  (hf : lower_semicontinuous f) (hg : lower_semicontinuous g) :
   lower_semicontinuous (λ x, f x ⊓ g x) :=
λ a, lower_semicontinuous_at_inf a (hf a) (hg a)

-- TODO : add same for upper_semicontinuous

lemma lower_semicontinuous_on_iff_restrict {s : set α} : 
  lower_semicontinuous_on f s ↔
  lower_semicontinuous (s.restrict f) := sorry

lemma lower_semicontinuous_on_iff_preimage_Ioi {s : set α} :
  lower_semicontinuous_on f s ↔ 
  ∀ x ∈ s, ∀ b, b < f x →  
  ∃ (u : set α), is_open u ∧ f ⁻¹' (set.Ioi b) ∩ s = u ∩ s :=
sorry

/- This is ridiculously difficult ! -/
lemma lower_semicontinuous_on_iff_preimage_Iic {s : set α} :
  lower_semicontinuous_on f s ↔ 
  ∀ b, ∃ (v : set α), is_closed v ∧ f ⁻¹' (set.Iic b) ∩ s = v ∩ s :=
begin
  split,
  { intro hf, 
    intro b, 
    use closure (f ⁻¹' Iic b ∩ s),
    simp only [is_closed_closure, true_and],
    apply subset.antisymm,
    rintros a ha, exact ⟨subset_closure ha, ha.2⟩, 
    
    rintros a ⟨hab, has⟩,
    apply and.intro _ has,
    simp only [mem_preimage, mem_Iic], 
     simp only [lower_semicontinuous_on, lower_semicontinuous_within_at] at hf, 
    rw ← not_lt, intro hb,
    simp only [mem_closure_iff_frequently, mem_preimage, mem_Iic, mem_inter_iff] at hab,
    apply hab,
    dsimp, 
    specialize hf a has b hb,
    simp only [filter.eventually] at hf ⊢,
    simp only [nhds_within, filter.mem_inf_iff] at hf, 
    obtain ⟨u, hu, v, hv, huv⟩ := hf, 
    simp only [mem_principal] at hv, 
    simp_rw [not_and_distrib, not_le],
    rw set.set_of_or, rw huv, 
    apply filter.mem_of_superset hu, 
    intros x hx,
    by_cases hx' : x ∈ s,
    left, exact ⟨hx, hv hx'⟩,
    right, exact hx', },
  { intro hf, 
    simp only [lower_semicontinuous_on, lower_semicontinuous_within_at], 
    intros a ha b hb,
    simp only [filter.eventually, nhds_within, filter.mem_inf_iff],
    
    obtain ⟨v, hv_closed, hv⟩ := hf b, 
    simp only [filter.mem_principal],
    use (vᶜ ∪ sᶜ),
    split,
    apply filter.mem_of_superset,

    apply is_open.mem_nhds , 
    { rw is_open_compl_iff, exact hv_closed, },
    { simp only [mem_compl_iff], intro hav, 
      rw ← not_le at hb, apply hb, 
      rw ← mem_Iic, rw ← set.mem_preimage, 
      apply set.inter_subset_left,
      rw hv, exact ⟨hav, ha⟩, },
    exact vᶜ.subset_union_left sᶜ,

    use ({ x : α | b < f x} ∪ s), 
    split, 
    apply set.subset_union_right,

    rw ← compl_inj_iff,
    simp only [set.compl_inter, set.compl_union, compl_compl], 

    rw ← hv, 
    suffices : f ⁻¹' Iic b = { x : α | b < f x }ᶜ,
    rw this, 
    rw set.inter_union_compl,
    ext x, simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_set_of_eq, not_lt], },
end

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set -/
theorem lower_semicontinuous.exists_forall_le_of_is_compact {s : set α} 
  (ne_s : s.nonempty) (hs : is_compact s)
  (hf : lower_semicontinuous_on f s) : 
  ∃ (a ∈ s), ∀ x ∈ s, f a ≤ f x := 
begin
  haveI : nonempty α := ⟨ne_s.some⟩,
  haveI : nonempty s := ⟨⟨ne_s.some, ne_s.some_spec⟩⟩,

  let φ : β → filter α := λ b, 𝓟 (s ∩ f ⁻¹' (Iic b)),
  let ℱ : filter α := ⨅ a : s, φ (f a), 
  haveI : ℱ.ne_bot,
  { refine infi_ne_bot_of_directed _ _,
    { refine directed.mono_comp ge (λ b₁ b₂ hb, _) (is_total.directed _ _), 
      refine principal_mono.mpr (inter_subset_inter_right _ (preimage_mono $ Iic_subset_Iic.mpr hb)) },
    { intro x,
      have : (pure x : filter α) ≤ φ (f x) := le_principal_iff.mpr ⟨x.2, le_refl (f x)⟩,
      exact ne_bot_of_le this } },

  have hℱs : ℱ ≤ 𝓟 s,
    from infi_le_of_le ⟨ne_s.some, ne_s.some_spec⟩ (principal_mono.mpr $ inter_subset_left _ _),

  have hℱ : ∀ x ∈ s, ∀ᶠ y in ℱ, f y ≤ f x,
    from λ x hx, mem_infi_of_mem ⟨x, hx⟩ (inter_subset_right _ _), 
  
  obtain ⟨a, ha, h⟩ := hs hℱs, 
  letI : (𝓝 a ⊓ ℱ).ne_bot := h,
  refine ⟨a, ha, λ x hx, le_of_not_lt $ λ hxa, _⟩,
  suffices : ∀ᶠ x in 𝓝 a ⊓ ℱ, false,
    by rwa eventually_const at this,
  filter_upwards [(hf a ha (f x) hxa).filter_mono (inf_le_inf_left _ hℱs),
    (hℱ x hx).filter_mono (inf_le_right : 𝓝 a ⊓ ℱ ≤ ℱ)] 
    using λ y h₁ h₂, not_le_of_lt h₁ h₂,
end

/-- A lower semicontinuous function is bounded above on a compact set. -/
lemma lower_semicontinuous.bdd_below_of_is_compact [nonempty β] {s : set α} (hs : is_compact s) (hf : lower_semicontinuous_on f s): 
  bdd_below (f '' s) := 
begin
  cases s.eq_empty_or_nonempty,
  { rw h, simp only [set.image_empty],
    exact bdd_below_empty },
  { obtain ⟨a, ha, has⟩ := lower_semicontinuous.exists_forall_le_of_is_compact h hs hf, 
    use f a, rintros b ⟨x, hx, rfl⟩, exact has x hx },
end

end lower_semicontinuous

section upper_semicontinuous

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set -/
theorem upper_semicontinuous.exists_forall_ge_of_is_compact {s : set α} 
  (ne_s : s.nonempty) (hs : is_compact s)
  (hf : upper_semicontinuous_on f s): 
  ∃ (a ∈ s), ∀ x ∈ s, f x ≤ f a := 
@lower_semicontinuous.exists_forall_le_of_is_compact (βᵒᵈ) _ _ _ _ _ _ s ne_s hs hf

/-- An upper semicontinuous function is bounded above on a compact set. -/
lemma upper_semicontinuous.bdd_above_of_is_compact [nonempty β] {s : set α}
  (hf : upper_semicontinuous_on f s) (hs : is_compact s): 
  bdd_above (f '' s) := 
@lower_semicontinuous.bdd_below_of_is_compact (βᵒᵈ) _ _ _ _ _ _ _ s hs hf

end upper_semicontinuous

end linear_order

section complete_linear_order

variables {β α : Type*} [topological_space α] [topological_space β] {f : α → β}
variables [complete_linear_order β] [order_closed_topology β] 

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set -/
theorem lower_semicontinuous.exists_infi_of_is_compact {s : set α} 
  (ne_s : s.nonempty) (hs : is_compact s)
  (hf : lower_semicontinuous_on f s) : 
  ∃ (a ∈ s), f a = ⨅ x ∈ s, f x := 
begin
  obtain ⟨a, ha, ha_le⟩ := lower_semicontinuous.exists_forall_le_of_is_compact ne_s hs hf,
  use a, apply and.intro ha,
  apply le_antisymm, 
  rw le_infi₂_iff, intros x hx, exact ha_le x hx,
  exact infi₂_le a ha,
end

theorem lower_semicontinuous_within_at_infi₂ {ι : Type*} {f : ι → α → β} {s : set α} {a : α} {I : set ι}
  (hf : ∀ i ∈ I, lower_semicontinuous_within_at (f i) s a) :
  lower_semicontinuous_within_at (λ x, ⨅ i ∈ I, f i x) s a :=
  sorry

theorem lower_semicontinuous_on_infi₂ {ι : Type*} {f : ι → α → β} {s : set α} {I : set ι}
  (hf : ∀ i, lower_semicontinuous_on (f i) s) :
  lower_semicontinuous_on (λ x, ⨅ i ∈ I, f i x) s :=
  sorry

theorem lower_semicontinuous_at_infi₂ {ι : Type*} {f : ι → α → β} {a : α} {I : set ι}
  (hf : ∀ i, lower_semicontinuous_at (f i) a) :
  lower_semicontinuous_at (λ x, ⨅ i ∈ I, f i x) a :=
  sorry

theorem lower_semicontinuous_infi₂ {ι : Type*} {f : ι → α → β} {I : set ι}
  (hf : ∀ i, lower_semicontinuous (f i)) :
  lower_semicontinuous (λ x, ⨅ i ∈ I, f i x) :=
  sorry

theorem lower_semicontinuous_within_at_supr₂ {ι : Type*} {f : ι → α → β} {s : set α} {a : α} {I : set ι}
  (hI : I.finite) (hf : ∀ i ∈ I, lower_semicontinuous_within_at (f i) s a) :
  lower_semicontinuous_within_at (λ x, ⨆ i ∈ I, f i x) s a :=
begin
  revert hf,
  apply hI.induction_on,
  { intro hf,
    simp only [mem_empty_iff_false, csupr_false, supr_bot], 
    exact lower_semicontinuous_within_at_const, },
  intros j J hjJ hJ hrec hf,
  suffices : ∀ x, (⨆ (i : ι) (H : i ∈ insert j J), f i x) = (f j x) ⊔ (⨆ i ∈ J, f i x), 
  rw funext this,
  apply lower_semicontinuous_within_at_sup s a (hf j (set.mem_insert j J)),
  apply hrec,
  intros i hi, exact hf i (set.mem_insert_of_mem j hi),
  intro x,
  simp only [set.insert_eq],
  rw supr_union,
  apply congr_arg2 _ _ rfl,
  simp only [mem_singleton_iff, supr_supr_eq_left],
end

theorem lower_semicontinuous_on_supr₂ {ι : Type*} {f : ι → α → β} {s : set α} {I : set ι} (hI : I.finite)
  (hf : ∀ i ∈ I, lower_semicontinuous_on (f i) s) :
  lower_semicontinuous_on (λ x, ⨆ i ∈ I, f i x) s := λ a ha,
lower_semicontinuous_within_at_supr₂ hI (λ i hi, hf i hi a ha)

theorem lower_semicontinuous_at_supr₂ {ι : Type*} {f : ι → α → β} {a : α} {I : set ι} (hI : I.finite)
  (hf : ∀ i, lower_semicontinuous_at (f i) a) :
  lower_semicontinuous_at (λ x, ⨆ i ∈ I, f i x) a :=
  sorry

theorem lower_semicontinuous_supr₂ {ι : Type*} {f : ι → α → β} {I : set ι} (hI : I.finite)
  (hf : ∀ i, lower_semicontinuous (f i)) :
  lower_semicontinuous (λ x, ⨆ i ∈ I, f i x) :=
  sorry

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set -/
theorem upper_semicontinuous.exists_supr_of_is_compact {s : set α} 
  (ne_s : s.nonempty) (hs : is_compact s)
  (hf : upper_semicontinuous_on f s) : 
  ∃ (a ∈ s), f a = ⨆ x ∈ s, f x := 
@lower_semicontinuous.exists_infi_of_is_compact (βᵒᵈ) _ _ _ _ _ _ _ ne_s hs hf


theorem upper_semicontinuous_within_at_supr₂ {ι : Type*} {f : ι → α → β} {s : set α} {a : α} {I : set ι}
  (hf : ∀ i, upper_semicontinuous_within_at (f i) s a) :
  upper_semicontinuous_within_at (λ x, ⨅ i ∈ I, f i x) s a :=
  sorry

theorem upper_semicontinuous_on_supr₂ {ι : Type*} {f : ι → α → β} {s : set α} {I : set ι}
  (hf : ∀ i, upper_semicontinuous_on (f i) s) :
  upper_semicontinuous_on (λ x, ⨅ i ∈ I, f i x) s :=
  sorry

theorem upper_semicontinuous_at_supr₂ {ι : Type*} {f : ι → α → β} {a : α} {I : set ι}
  (hf : ∀ i, upper_semicontinuous_at (f i) a) :
  upper_semicontinuous_at (λ x, ⨅ i ∈ I, f i x) a :=
  sorry

theorem upper_semicontinuous_supr₂ {ι : Type*} {f : ι → α → β} {I : set ι}
  (hf : ∀ i, upper_semicontinuous (f i)) :
  upper_semicontinuous (λ x, ⨅ i ∈ I, f i x) :=
  sorry



end complete_linear_order

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
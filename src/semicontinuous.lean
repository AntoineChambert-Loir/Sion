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
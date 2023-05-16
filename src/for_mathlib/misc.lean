import data.real.ereal
import topology.connected

/-! 

# Miscellaneous lemmas to add to mathlib

-/

-- order.complete_lattice
lemma infi₂_le_iff {α β : Type*} [complete_lattice β] {f : α → β} {s : set α} {b : β} :
  ((⨅ x ∈ s, f x) ≤ b)  ↔ ∀ b', (∀ x ∈ s, b' ≤ f x) → b' ≤ b :=
begin
  rw infi_le_iff, apply forall_congr, 
  intro b', simp_rw le_infi_iff,
end

lemma le_supr₂_iff {α β : Type*} [complete_lattice β] {f : α → β} {s : set α} {b : β} :
  (b ≤ (⨆ x ∈ s, f x))  ↔ ∀ b', (∀ x ∈ s, f x ≤ b') → b ≤ b' :=
@infi₂_le_iff α (βᵒᵈ) _ _ _ _ 

-- data.real.ereal
instance : densely_ordered ereal := with_bot.densely_ordered

-- topology.connected
-- This is essentially `is_preconnected_iff_subset_of_disjoint_closed`
lemma is_preconnected.subset_or_subset_of_closed {α : Type*} [topological_space α] 
  {s u v : set α} (hu : is_closed u) (hv : is_closed v) (huv : disjoint u v)
  (hsuv : s ⊆ u ∪ v) (hs : is_preconnected s) :
  s ⊆ u ∨ s ⊆ v :=
begin
  apply (is_preconnected_iff_subset_of_disjoint_closed.mp hs) u v hu hv hsuv, 
  rw [set.disjoint_iff_inter_eq_empty.mp huv , set.inter_empty],
end

-- filter
variable {α : Type*}
namespace filter

lemma frequently.congr {f : filter α} {p q : α → Prop} (h' : ∃ᶠ x in f, p x)
  (h : ∀ᶠ x in f, p x ↔ q x) : ∃ᶠ x in f, q x :=
h'.mp (h.mono $ λ x hx, hx.mp)

lemma frequently_congr {f : filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
  (∃ᶠ x in f, p x) ↔ (∃ᶠ x in f, q x) :=
⟨λ hp, hp.congr h, λ hq, hq.congr $ by simpa only [iff.comm] using h⟩

lemma frequently_congr' {α : Type*} (f : filter α) (p q : α → Prop)
  (h : ∀ᶠ (a : α) in f, p a ↔ q a) : (∃ᶠ a in f, p a) ↔ (∃ᶠ a in f, q a) := 
begin
  dsimp only [filter.frequently], 
  rw not_iff_not, 
  apply filter.eventually_congr,
  simp_rw not_iff_not, exact h,
end


lemma cluster_pt_principal_subtype_iff_frequently {α : Type*} [topological_space α] {s t : set α} (hst : s ⊆ t) {J : set s} {a : ↥s} : cluster_pt a (filter.principal J) ↔ ∃ᶠ x in nhds_within a t, ∃ (h : x ∈ s), (⟨x, h⟩ : s) ∈ J  := 
begin
  rw [nhds_within_eq_map_subtype_coe (hst a.prop), filter.frequently_map,
    cluster_pt_principal_iff_frequently, (inducing_coe).nhds_eq_comap,
    filter.frequently_comap, (inducing_coe).nhds_eq_comap,
    filter.frequently_comap, subtype.coe_mk],
  apply frequently_congr,
  apply eventually_of_forall,
  intro x,
  simp only [subtype.coe_mk, set_coe.exists, exists_and_distrib_left, exists_eq_left],
  exact ⟨λ ⟨h, hx⟩, ⟨hst h, h, hx⟩, λ ⟨h, hx⟩, hx⟩,
end

-- Ancienne version
example {α : Type*} [topological_space α] {s t : set α} (hst : s ⊆ t) {J : set s} {a : ↥s} : cluster_pt a (filter.principal J) ↔ ∃ᶠ x in nhds_within a t, ∃ (h : x ∈ s), (⟨x, h⟩ : s) ∈ J  := 
begin
  simp only [cluster_pt_principal_iff_frequently, filter.frequently, not_iff_not, filter.eventually, mem_nhds_iff, mem_nhds_within],
  simp only [exists_prop, not_exists],
  split,
  { rintro ⟨v, hv_subset, hv_open, hav⟩,
    obtain ⟨u, hu, hut⟩ := (inducing_coe).is_open_iff.mp hv_open, 
    use u, 
    apply and.intro hu,
    simp only [←hut, set.mem_preimage] at hav, 
    apply and.intro hav, 
    intros x hx, 
    simp only [set.mem_set_of_eq], 
    intro hxs, 
    apply hv_subset, 
    rw ← hut,  
    rw set.mem_preimage,
    rw set.mem_inter_iff at hx, exact hx.1, },
  { rintro ⟨u, hu_open, hat, hut_subset⟩,
    use coe ⁻¹' u,
    split, 
    rintros ⟨x, hx⟩ hx', rw set.mem_preimage at hx', 
    apply hut_subset, 
    exact ⟨hx', hst hx⟩, 
    exact ⟨is_open_induced hu_open, hat⟩, },
end

-- Essayons de faire plus simple (pas convaincant!)
example {α : Type*} [topological_space α] (s t : set α) (hst : s ⊆ t) (J : set s) (a : ↥s) : cluster_pt a (filter.principal J) ↔ ∃ᶠ x in nhds_within a t, ∃ (h : x ∈ s), (⟨x, h⟩ : s) ∈ J  := 
begin
  simp only [cluster_pt_principal_iff_frequently, filter.frequently, not_iff_not, filter.eventually, mem_nhds_iff, mem_nhds_within],
  simp only [exists_prop, not_exists],
  
  simp_rw (inducing_coe).is_open_iff, 
  simp_rw and.comm, simp_rw ← and.assoc, 
  simp_rw ← exists_and_distrib_left ,  
  rw exists_comm, 
  apply exists_congr, intro u,
  simp_rw and.comm, simp_rw and.assoc, simp_rw exists_and_distrib_left,
  rw and.congr_right_iff,
  intro hu_open,
  split,
  { rintro ⟨x, hux, hax, hx⟩,
    simp only [←hux, set.mem_preimage] at hax,  
    apply and.intro hax, 
    intros y hyut hys, 
    apply hx, simp only [← hux, set.mem_preimage], exact hyut.1, },
  { rintros ⟨hau, hut⟩, 
    use coe ⁻¹' u, 
    apply and.intro rfl,
    rw set.mem_preimage, apply and.intro hau,
    intro y, rw set.mem_preimage, intro hy, 
    simp, rw ← subtype.coe_eta y y.prop,
    apply hut, 
    exact ⟨hy, hst y.prop⟩, },
end


-- si on enlève le grand ensemble (c'est pas mieux)
lemma cluster_pt_principal_subtype_iff_frequently' {α : Type*} [topological_space α] (s : set α) (J : set s) (a : ↥s) : cluster_pt a (filter.principal J) ↔ ∃ᶠ (x : α) in nhds_within a s, ∃ (h : x ∈ s), (⟨x, h⟩ : s) ∈ J := 
begin
  simp only [cluster_pt_principal_iff_frequently, filter.frequently, not_iff_not, filter.eventually, mem_nhds_iff, mem_nhds_within],
  simp only [exists_prop, not_exists],
  split,
  { rintro ⟨v, hv_subset, hv_open, hav⟩,
    obtain ⟨u, hu, hut⟩ := (inducing_coe).is_open_iff.mp hv_open, 
    use u, 
    apply and.intro hu,
    simp only [←hut, set.mem_preimage] at hav, 
    apply and.intro hav, 
    intros x hx, 
    simp only [set.mem_set_of_eq], 
    intro hxs, 
    apply hv_subset, 
    rw ← hut,  
    rw set.mem_preimage,
    rw set.mem_inter_iff at hx, exact hx.1, },
  { rintro ⟨u, hu_open, hat, hut_subset⟩,
    use coe ⁻¹' u,
    split, 
    rintros ⟨x, hx⟩ hx', rw set.mem_preimage at hx', 
    apply hut_subset, 
    exact ⟨hx', hx⟩, 
    exact ⟨is_open_induced hu_open, hat⟩, },
end

end filter


-- Not needed actually...

-- TODO: which file ?
lemma min_mem_of_mem {α : Type*} [linear_order α] {a b : α} {s : set α} (ha : a ∈ s)
  (hb : b ∈ s) : min a b ∈ s :=
by rw [min_def]; split_ifs; assumption

-- TODO: which file ?
lemma max_mem_of_mem {α : Type*} [linear_order α] {a b : α} {s : set α} (ha : a ∈ s)
  (hb : b ∈ s) : max a b ∈ s :=
by rw [max_def]; split_ifs; assumption

-- TODO: which file ?
lemma inf_mem_of_mem {α : Type*} [linear_order α] {a b : α} {s : set α} (ha : a ∈ s)
  (hb : b ∈ s) : a ⊓ b ∈ s :=
by rw [inf_eq_min]; exact min_mem_of_mem ha hb

-- TODO: which file ?
lemma sup_mem_of_mem {α : Type*} [linear_order α] {a b : α} {s : set α} (ha : a ∈ s)
  (hb : b ∈ s) : a ⊔ b ∈ s :=
by rw [sup_eq_max]; exact max_mem_of_mem ha hb
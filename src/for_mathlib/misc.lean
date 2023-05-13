import data.real.ereal
import topology.connected

/-! 

# Miscellaneous lemmas to add to mathlib

-/

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


example {α : Type*} [topological_space α] (s t : set α) (hst : s ⊆ t) (J : set s) (a : ↥s) : cluster_pt a (filter.principal J) ↔ ∃ᶠ x in nhds_within a t, ∃ (h : x ∈ s), (⟨x, h⟩ : s) ∈ J  := 
begin
rw cluster_pt_principal_iff_frequently,
simp only [filter.frequently, not_iff_not,
filter.eventually],
rw mem_nhds_iff,
rw mem_nhds_within,
split,
intro H,
simp,
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
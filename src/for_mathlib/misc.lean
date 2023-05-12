import data.real.ereal
import topology.connected

/-! 

# Miscellaneous lemmas to add to mathlib

-/

-- data.real.ereal
instance : densely_ordered ereal := with_bot.densely_ordered

-- topology.connected
lemma is_preconnected.subset_or_subset_of_closed {α : Type*} [topological_space α] 
  {s u v : set α} (hu : is_closed u) (hv : is_closed v) (huv : disjoint u v)
  (hsuv : s ⊆ u ∪ v) (hs : is_preconnected s) :
  s ⊆ u ∨ s ⊆ v :=
begin
  rcases hs.subset_or_subset hu.is_open_compl hv.is_open_compl _ _;
  sorry
end

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
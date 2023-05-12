import analysis.convex.topology
import analysis.convex.quasiconvex
import topology.semicontinuous
import data.real.ereal

open set

section quasiconcave

/- We prove that a lsc quasiconcave function on a nonempty compact convex set 
is bounded above and attains its upper bound. 

Maybe the result is false, I don't know. 

-/
variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [topological_add_group E] [has_continuous_smul ℝ E]
variable {f : E → ereal}

/-- A quasiconcave and lower semicontinuous function attains its upper bound on a nonempty compact set -/
lemma is_compact.exists_forall_ge_of_quasiconcave {s : set E}
  (ne_s : s.nonempty) (hs : is_compact s) 
  (hfs : lower_semicontinuous_on f s) (hfc : quasiconcave_on ℝ s f):
  ∃ (a ∈ s), ∀ x ∈ s, f x ≤ f a := sorry  
/- 
let T = sup f x, for x ∈ s, 
assume f does not attain its upper bound
consider the sets  U t := f ⁻¹' (set.Ici t), for t < T.
Since f is lower semicontinuous, U t is closed

-/
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

lemma quasiconcave_on.is_preconnected_preimage {s : set E} {t : ereal} (hfc : quasiconcave_on ℝ s f) : 
  is_preconnected ((f ∘ coe) ⁻¹' (Ici t) : set s) :=
begin
  rw [preimage_comp, ← inducing_coe.is_preconnected_image, image_preimage_eq_inter_range,
      subtype.range_coe, inter_comm],
  exact (hfc t).is_preconnected
end

end quasiconcave


section quasiconvex


/- We prove that a usc quasiconvex function on a nonempty compact convex set 
is bounded below and attains its lower bound. 

Maybe the result is false, I don't know. 

-/

variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [topological_add_group E] [has_continuous_smul ℝ E]
variable {f : E → ereal}

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

lemma quasiconvex_on.is_preconnected_preimage {s : set E} {t : ereal} (hfc : quasiconvex_on ℝ s f) : 
  is_preconnected ((f ∘ coe) ⁻¹' (Iic t) : set s) :=
begin
  rw [preimage_comp, ← inducing_coe.is_preconnected_image, image_preimage_eq_inter_range,
      subtype.range_coe, inter_comm],
  exact (hfc t).is_preconnected
end

end quasiconvex

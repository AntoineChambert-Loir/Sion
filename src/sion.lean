/- # Formalization of the von Neumann Sion theorem 

## Statement

Let X and Y be compact convex subsets of topological vector spaces E and F, 
f : X × Y → ℝ be a function such that 
- for all x, f(x, ⬝) is upper semicontinuous and quasiconcave
- for all y, f(⬝, y) is lower semicontinuous and quasiconvex
Then inf_x sup_y f(x,y) = sup_y inf_x f(x,y). 

The classical case of the theorem assumes that f is continuous,
f(x, ⬝) is concave, f(⬝, y) is convex.

As a particular case, one get the von Neumann theorem where
f is bilinear and E, F are finite dimensional.

We follow the proof of Komiya (1988)
## References

- Neumann, John von (1928). « Zur Theorie der Gesellschaftsspiele ». Mathematische Annalen 100 (1): 295‑320. https://doi.org/10.1007/BF01448847.

- Sion, Maurice (1958). « On general minimax theorems ». Pacific Journal of Mathematics 8 (1): 171‑76.

- Komiya, Hidetoshi (1988). « Elementary Proof for Sion’s Minimax Theorem ». Kodai Mathematical Journal 11 (1). https://doi.org/10.2996/kmj/1138038812.

-/

import analysis.convex.basic
import topology.semicontinuous
import analysis.convex.quasiconvex
import topology.order.lower_topology

section lower_semicontinous
variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variables {X : set E} (hX : is_compact X)
variables {f : E → ℝ} (hf : lower_semicontinuous_on f X)

namespace lower_semicontinuous

include hf hX

/-- A lower semicontinuous function is bounded above on a compact set. -/
lemma bdd_below_on.is_compact : bdd_below (f '' X) := sorry

/-- A lower semicontinuous function attains its lowers bound on a nonempty compact set -/
lemma is_compact.exists_forall_le [nonempty X]: 
  ∃ (a ∈ X), ∀ x ∈ X, f a ≤ f x := sorry 

/-- A quasiconcave and lower semicontinuous function attains its upper bound on a nonempty compact set -/
lemma is_compact.exists_forall_ge_of_quasiconcave 
  (ne_X : X.nonempty) (hfc : quasiconcave_on ℝ X f):
  ∃ (a ∈ X), ∀ x ∈ X, f x ≤ f a := sorry  

/-- A quasiconcave and lower semicontinuous function is bounded above on a compact set -/
lemma bdd_above_on.is_compact_of_quasiconcave 
  (hfc : quasiconcave_on ℝ X f) : bdd_above (f '' X) := 
begin
  cases X.eq_empty_or_nonempty with e_X ne_X,
  { rw e_X, simp only [set.image_empty, bdd_above_empty], },
  { obtain ⟨a, ha, hax⟩ := is_compact.exists_forall_ge_of_quasiconcave hX hf ne_X hfc,
    use f a, rintros t ⟨x, hx, rfl⟩, exact hax x hx, },
end


end lower_semicontinuous
end lower_semicontinous

section upper_semicontinuous
variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variables {X : set E} (hX : is_compact X)
variables {f : E → ℝ} (hf : upper_semicontinuous_on f X)

namespace upper_semicontinuous

include hf hX

/-- An upper semicontinuous function is bounded above on a compact set. -/
lemma bdd_above_on.is_compact : bdd_above (f '' X) := sorry

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set -/
lemma is_compact.exists_forall_ge  [nonempty X]: 
  ∃ (a ∈ X), ∀ x ∈ X, f x ≤ f a := sorry 

/-- A quasiconvex and upper semicontinuous function attains its lower bound on a nonempty compact set -/
lemma is_compact.exists_forall_le_of_quasiconvex 
  (ne_X : X.nonempty) (hfc : quasiconvex_on ℝ X f):
  ∃ (a ∈ X), ∀ x ∈ X, f a ≤ f x := sorry  

/-- A quasiconvex and upper semicontinuous function is bounded below on a compact set -/
lemma bdd_below_on.is_compact_of_quasiconvex 
  (hfc : quasiconvex_on ℝ X f) : bdd_below (f '' X) := 
begin
  cases X.eq_empty_or_nonempty with e_X ne_X,
  { rw e_X, simp only [set.image_empty, bdd_below_empty], },
  { obtain ⟨a, ha, hax⟩ := is_compact.exists_forall_le_of_quasiconvex hX hf ne_X hfc,
    use f a, rintros t ⟨x, hx, rfl⟩, exact hax x hx, },
end


end upper_semicontinuous
end upper_semicontinuous

namespace sion

variables 
 {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
variables 
 {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] [has_continuous_add F] [has_continuous_smul ℝ F]
variables (X : set E) (ne_X : X.nonempty) (cX : convex ℝ X) (kX : is_compact X)
variables (Y : set F) (ne_Y : Y.nonempty) (cY : convex ℝ Y) (kY : is_compact Y)

variable (f : E → F → ℝ) 
variables (hfx : ∀ x ∈ X, upper_semicontinuous_on (λ y : F, f x y) Y) (hfx' : ∀ x ∈ X, quasiconcave_on ℝ Y (λ y, f x y))
variables (hfy : ∀ y ∈ Y, lower_semicontinuous_on (λ x : E, f x y) X) (hfy' : ∀ y ∈ Y, quasiconvex_on ℝ X (λ x, f x y))

include hfx hfx' ne_X cX kX hfy hfy' ne_Y cY kY

theorem sion_exists : ∃ (a ∈ X) (b ∈ Y),
f a b = infi (λ x : X, supr (λ y : Y, f x y)) 
∧ f a b = supr (λ y : Y, infi (λ x : X, f x y)) := 
sorry

example  : bdd_below ((λ x, supr (λ y : Y, f x y)) '' X) := 
begin
  obtain ⟨b, hb⟩ := ne_Y, 
  suffices : bdd_below ((λ x, f x b) '' X),
  obtain ⟨m, hm⟩ := this, rw mem_lower_bounds at hm,
  simp_rw set.mem_image at hm, 
  use m,
  rintros t ⟨x, hx, rfl⟩,
  dsimp,
  suffices : m ≤ f x ↑(⟨b, hb⟩ : Y), 
  refine le_trans this _, 

sorry 
end

example : upper_semicontinuous_on (λ x, supr (λ y : Y, f x y)) X := sorry


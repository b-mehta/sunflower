import algebra.big_operators.ring
import probability.density
import probability.independence
import probability.conditional_expectation
import probability.notation
import probability.cond_count

open finset set measure_theory probability_theory
open_locale big_operators measure_theory ennreal probability_theory

variables {α : Type*} [fintype α] [decidable_eq α]
variables {𝒮 : finset (finset α)} {G : finset (finset α)} {U : finset α} {t : ℕ}

def shadow (G : finset (finset α)) (U : finset α) : finset (finset α) := G.filter (λ Y, Y ⊆ U)

lemma shadow_subset : shadow G U ⊆ G :=
begin
  unfold shadow,
  simp only [finset.filter_subset],
  -- rw finset.subset_iff,
  -- intros x h,
  -- refine finset.mem_of_mem_filter _ h,
end

-- defined for uniform distribution
def spread (ε : ℝ) (U : finset (finset α)) : Prop :=
∀ (Z : finset α), (finset.card (U.filter (λ u, Z ⊆ u)) : ℝ) ≤ ε ^ Z.card * U.card

lemma spread_iff_ratio (ε : ℝ) (U : finset (finset α)) :
  spread ε U ↔ ∀ (Z : finset α), (finset.card (U.filter (λ u, Z ⊆ u)) : ℝ) / U.card ≤ ε ^ Z.card :=
begin
  sorry
end

def to_antichain (G : finset (finset α)) : finset (finset α) :=
G.filter (λ A, ∀ B ∈ G, B ⊆ A → B = A)

lemma ssubset_thing {β : Type*} {X Y : finset β} : (¬ Y ⊂ X) ↔ (Y ⊆ X → Y = X) :=
begin
  split,
  { intros hY hYX,
    by_contra h,
    have hp : Y ⊂ X,
    { rw finset.ssubset_iff_subset_ne, split, exact hYX, exact h, },
    apply hY,
    exact hp, },
  { intros hY hYX,
    cases hYX with h1 h2,
    specialize hY h1,
    finish, },
end

lemma to_antichain_eq : to_antichain G = G.filter (λ A, ∀ B ∈ G, ¬ B ⊂ A) :=
begin
  simpa only [ssubset_thing],
end

lemma to_antichain_subset : to_antichain G ⊆ G :=
begin
  apply finset.filter_subset,
end

lemma is_antichain_to_antichain : is_antichain (⊆) (to_antichain G : set (finset α)) :=
begin
  sorry
end


-- mathematically solvable by induction on cardinality of A
lemma contains_subset {A} (hA : A ∈ G) : ∃ B ∈ to_antichain G, B ⊆ A :=
begin
  set n := finset.card A with h,
  clear_value n,
  induction n using nat.strong_induction_on with n ih generalizing A,
  -- for n being zero, empty set A must be in G' as there is no proper subset of an empty set
  -- have hA' : A = ∅,
  -- { rw ← finset.card_eq_zero, linarith, },
  -- use A,
  -- split,
  -- { unfold to_antichain,
  --   rw finset.mem_filter,
  --   split, exact hA,
  --   intros B hB hBA,
  --   suffices : B = ∅,
  --   rw hA', exact this,
  --   rw hA' at hBA,
  --   rwa finset.subset_empty at hBA, },
  -- { simp only [subset_refl], },
  -- for inductive step, we consider two cases, A in G' or otherwise
  have q : A ∈ to_antichain G ∨ A ∉ to_antichain G := by finish,
  cases q with h1 h2,
  -- for A in G', use A and done
  use A,
  split, exact h1,
  simp only [subset_refl],
  -- for A in G, there exists a proper subset of A in G, named A', |A'| < |A|, apply inductive hypothesis
  have p : ∃ (C : finset α), C ∈ G ∧ C ⊂ A,
  { by_contra hp,
    push_neg at hp,
    apply h2,
    unfold to_antichain,
    rw finset.mem_filter,
    split, exact hA,
    intros B hB,
    rw ← ssubset_thing,
    specialize hp B hB,
    exact hp, },
  rcases p with ⟨C, ⟨p1, p2⟩⟩,
  have hC : C.card < n,
  { rw h,
    refine finset.card_lt_card p2, },
  suffices : ∃ (B : finset α) (H : B ∈ to_antichain G), B ⊆ C,
  { rcases this with ⟨B, ⟨hB1, hB2⟩⟩,
    use B,
    split, exact hB1,
    refine subset_trans hB2 _,
    rw subset_iff_ssubset_or_eq,
    left, exact p2, },
  { specialize ih C.card hC p1,
    simp only [eq_self_iff_true, exists_prop, forall_true_left] at ih,
    cases ih with B hB,
    use B,
    exact hB, },
end

variables {W : ℕ → finset α} {i : ℕ}

-- WARNING! : INDEXED DIFFERENTLY FROM THE PDF
-- we only care about this definition for 0 ≤ i < t
def the_partial_function (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) : ℕ → finset (finset α)
| i := to_antichain $
          (𝒮.filter $
            λ S, 2 ^ (t - i) ≤ (S \ (finset.range (i+1)).bUnion W).card ∧
            ∀ j < i, ∀ X ∈ the_partial_function j, ¬ X ⊆ S).image $
          λ S, S \ (finset.range (i+1)).bUnion W

@[derive decidable]
def good_set (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) (i : ℕ) (S : finset α) : Prop :=
2 ^ (t - i) ≤ (S \ (finset.range (i+1)).bUnion W).card ∧
  ∀ j < i, ∀ X ∈ the_partial_function W 𝒮 t j, ¬ X ⊆ S

lemma the_partial_function_eq (t : ℕ) : ∀ i,
  the_partial_function W 𝒮 t i =
    to_antichain ((𝒮.filter (good_set W 𝒮 t i)).image (λ S, S \ (finset.range (i+1)).bUnion W))
| i := by { rw [the_partial_function], refl }

def the_function (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) :=
(finset.range t).bUnion (the_partial_function W 𝒮 t)

lemma part_two_a_helper (ht : 1 ≤ t) (S) (h : ¬ S ⊆ (finset.range t).bUnion W) :
  ∃ i ∈ finset.range t, 2 ^ (t - i) ≤ (S \ (finset.range (i + 1)).bUnion W).card :=
begin
  sorry
end

lemma part_two_a_helper' (ht : 1 ≤ t) (S) (h : ¬ S ⊆ (finset.range t).bUnion W) :
  ((finset.range t).filter
    (λ i, 2 ^ (t - i) ≤ (S \ (finset.range (i + 1)).bUnion W).card)).nonempty :=
begin
  sorry
end

lemma part_two (t : ℕ) :
  (∃ S ∈ 𝒮, S ⊆ (finset.range t).bUnion W) ∨
    ∀ S ∈ 𝒮, ∃ X ∈ the_function W 𝒮 t, X ⊆ S :=
begin
  sorry
end

lemma part_one_one_easy_bit (R : finset α) (h : ¬ ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R) :
  ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
begin
  sorry
end

-- lemma part_one_one_hard_bit_first_step (R : finset α)
--   (h : ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R) :
--   ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
-- begin
--   sorry
-- end

lemma part_one_one (R : finset α) :
  ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
begin
  sorry
end

variables {Ω : Type*} [measurable_space Ω] {μ : measure Ω}

instance {α : Type*} : measurable_space (finset α) := ⊤

def spread_distribution (μ : measure Ω) (ε : ℝ) (UU : Ω → finset α) : Prop :=
∀ Z : finset α, (μ {ω | Z ⊆ UU ω}).to_real ≤ ε ^ Z.card

lemma spread_iff_uniform (ε : ℝ) (U : finset (finset α)) (UU : Ω → finset α)
  (hUU : pdf.is_uniform UU (U : set (finset α)) μ measure.count) :
  spread ε U ↔ spread_distribution μ ε UU :=
by sorry -- TODO: Bhavik

lemma exists_uniform {E : Type*} [measurable_space E] (s : set E) (μ : measure E) [sigma_finite μ]
  (hs : measurable_set s) :
  pdf.is_uniform id s (μ[|s]) μ :=
begin
  haveI : has_pdf (id : E → E) (μ[|s]) μ,
  { refine ⟨⟨measurable_id, s.indicator ((μ s)⁻¹ • 1), _, _⟩⟩,
    { refine measurable.indicator _ hs,
      refine measurable_one.const_smul _ },
    rw [with_density_indicator hs, with_density_smul _ measurable_one, with_density_one,
      measure.map_id],
    refl },
  change _ =ᵐ[_] _,
  apply ae_eq_of_forall_set_lintegral_eq_of_sigma_finite,
  { apply measurable_pdf },
  { exact (measurable_one.const_smul _).indicator hs },
  intros A hA hA',
  rw [←map_eq_set_lintegral_pdf (id : E → E) (μ[|s]) μ hA],
  rw lintegral_indicator _ hs,
  rw measure.map_id,
  simp only [pi.smul_apply, pi.one_apply, algebra.id.smul_eq_mul, mul_one, lintegral_const,
    measure.restrict_apply, measurable_set.univ, set.univ_inter],
  rw [cond_apply _ hs, measure.restrict_apply hs],
end

lemma exists_uniform' (ε : ℝ) (U : finset (finset α)) : ∃ (μ : measure (finset α))
  (UU : finset α → finset α), pdf.is_uniform UU (U : set (finset α)) μ measure.count :=
⟨_, _, exists_uniform _ _ measurable_space.measurable_set_top⟩

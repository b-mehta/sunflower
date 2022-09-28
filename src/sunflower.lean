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
  -- an alternative is
  -- rw finset.subset_iff,
  -- intros x h,
  -- refine finset.mem_of_mem_filter _ h,
end

-- defined for uniform distribution
def spread (ε : ℝ) (U : finset (finset α)) : Prop :=
∀ (Z : finset α), (finset.card (U.filter (λ u, Z ⊆ u)) : ℝ) ≤ ε ^ Z.card * U.card

def spr_1 (a b c : ℝ ) (hc : 0 < c ): (a≤ b) → (a/c ≤  b / c) :=
begin
  intros h, exact (div_le_div_right hc).mpr h,
end

lemma zer_zerco : 0 = ((0:ℕ ): ℝ )  := by simp
----------------------------------------------

lemma spread_iff_ratio (ε : ℝ) (U : finset (finset α)) {he : 0 ≤ ε } :
  spread ε U ↔ ∀ (Z : finset α), (finset.card (U.filter (λ u, Z ⊆ u)) : ℝ) / U.card ≤ ε ^ Z.card :=
begin
  split,
  {
    unfold spread,
    intros h Z,
    cases nat.eq_zero_or_pos U.card, --patter match wrt U.card

    { --When U.card = 0
    have zz  : ∀ r : ℝ ,  r / (0: ℝ ) = 0 := λ r, div_zero r,
    rw h_1,

    rw ← zer_zerco,
    rw zz,
    exact pow_nonneg he Z.card,
    },

    { -- When U.card > 0
    specialize h Z,

    have hUcard : 0 < (U.card : ℝ ), exact nat.cast_pos.mpr h_1,

    convert spr_1 ↑((filter (λ (u : finset α), Z ⊆ u) U).card)  (ε^(Z.card) * ↑(U.card)) ↑(U.card) (nat.cast_pos.mpr h_1) h,
    symmetry,
    apply mul_div_cancel,
    exact ne_of_gt ( nat.cast_pos.mpr h_1),
    }
  },

  {
    unfold spread,
    intros h Z,
    specialize h Z,

    have hUcard : 0 ≤ (U.card : ℝ ) :=
    begin
      rw zer_zerco,
      exact nat.cast_le.mpr(zero_le (U.card )),
    end,

    have H := mul_le_mul_of_nonneg_right h hUcard,

    cases nat.eq_zero_or_pos U.card,
    { -- When U.card = 0
      have fil_zero : (filter (λ (u : finset α), Z ⊆ u) U).card =0,
      {
        apply nat.eq_zero_of_le_zero,
        rw ← h_1,
        apply finset.card_le_of_subset,
        apply finset.filter_subset,
      },

      rw fil_zero, rw h_1, simp,
    },

    { -- When U.card > 0
      rw div_mul_cancel ↑((filter (λ (u : finset α), Z ⊆ u) U).card) at H,
      exact H,
      exact ne_of_gt ( nat.cast_pos.mpr h_1),
    }



  }
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

lemma exists_subset_minimal {S : finset (finset α)} (hS : S.nonempty) :
  ∃ X ∈ S, ∀ Y ∈ S, Y ⊆ X → Y = X :=
begin
  -- set M : finset (finset α) := S.filter(λ X : finset α, ∀ Y : finset α, Y ∈ S → X.card ≤ Y.card),
  set T : finset (finset α) := to_antichain S,
  -- claim T is non-empty
  have hT : T.nonempty,
  { have := finset.nonempty.bex hS,
    cases this with A hA,
    have := contains_subset hA,
    rcases this with ⟨B, ⟨hB1, hB2⟩⟩,
    simp only [finset.nonempty],
    use B,
    exact hB1, },
  have := finset.nonempty.bex hT,
  cases this with X hX,
  -- use X ∈ T
  use X,
  simp only [T] at hX,
  unfold to_antichain at hX,
  rw finset.mem_filter at hX,
  exact hX,
end

variables {W : ℕ → finset α} {i : ℕ}

-- WARNING! : INDEXED DIFFERENTLY FROM THE PDF
-- we only care about this definition for 0 ≤ i < t
-- this is 𝒢
def the_partial_function (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) : ℕ → finset (finset α)
| i := to_antichain $
          (𝒮.filter $
            λ S, 2 ^ (t - i - 1) ≤ (S \ (finset.range (i+1)).bUnion W).card ∧
            ∀ j < i, ∀ X ∈ the_partial_function j, ¬ X ⊆ S).image $
          λ S, S \ (finset.range (i+1)).bUnion W

@[derive decidable]
def good_set (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) (i : ℕ) (S : finset α) : Prop :=
2 ^ (t - i - 1) ≤ (S \ (finset.range (i+1)).bUnion W).card ∧
  ∀ j < i, ∀ X ∈ the_partial_function W 𝒮 t j, ¬ X ⊆ S

-- this is 𝒢'
def the_partial_function' (W : ℕ → finset α) (𝒮 : finset (finset α)) (t i : ℕ) :
  finset (finset α) :=
(𝒮.filter (good_set W 𝒮 t i)).image (λ S, S \ (finset.range (i+1)).bUnion W)

lemma the_partial_function_eq (t i : ℕ) :
  the_partial_function W 𝒮 t i = to_antichain (the_partial_function' W 𝒮 t i) :=
by { rw [the_partial_function], refl }

def the_function (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) :=
(finset.range t).bUnion (the_partial_function W 𝒮 t)

lemma part_one_one_easy_bit (R : finset α) (h : ¬ ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R) :
  ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
begin
  rw [finset.filter_false_of_mem, card_empty],
  { apply nat.zero_le _ },
  rintro T hT rfl,
  exact h ⟨T, hT, subset_union_left _ _⟩,
end

lemma part_one_one_other_easy_bit (R : finset α) (hR : ¬ W i ⊆ R) :
  ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
begin
  rw [finset.filter_false_of_mem, card_empty],
  { apply nat.zero_le _ },
  rintro T hT rfl,
  exact hR (subset_union_right _ _),
end

lemma part_one_one_hard_bit_first_step {R : finset α} (hR : W i ⊆ R)
  (h : ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R) :
  (𝒮.filter (λ S, S \ (finset.range i).bUnion W ⊆ R ∧
    S \ (finset.range (i + 1)).bUnion W ∈ the_partial_function' W 𝒮 t i)).nonempty :=
begin
  obtain ⟨T, hT₁, hT₂⟩ := h,
  rw [the_partial_function_eq] at hT₁,
  replace hT₁ := to_antichain_subset hT₁,
  simp only [the_partial_function', mem_filter, finset.mem_image, exists_prop, and_assoc,
    finset.nonempty] at hT₁ ⊢,
  obtain ⟨S, hS₁, hS₂, rfl⟩ := hT₁,
  refine ⟨S, hS₁, _, S, hS₁, hS₂, rfl⟩,
  rw [range_succ, finset.bUnion_insert, sdiff_union_distrib] at hT₂,
  intros x hx,
  by_cases x ∈ W i,
  { apply hR h },
  apply hT₂,
  simp only [finset.mem_inter, mem_sdiff, finset.mem_bUnion, finset.mem_range, exists_prop,
    not_exists, not_and] at hx ⊢,
  tauto
end

lemma part_one_one (R : finset α)  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) :
  ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
begin
  by_cases h₁ : W i ⊆ R,
  { by_cases h₂ : ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R,
    { apply part_one_one_hard_bit _ h₁ hS h₂ },
    apply part_one_one_easy_bit _ h₂ },
  apply part_one_one_other_easy_bit _ h₁,
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

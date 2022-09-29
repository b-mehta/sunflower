import algebra.big_operators.ring
import data.finset.finsupp
import probability.density
import probability.independence
import probability.conditional_expectation
import probability.notation
import probability.cond_count

open finset measure_theory probability_theory
open_locale big_operators measure_theory ennreal

variables {α : Type*} [decidable_eq α]
variables {𝒮 : finset (finset α)} {G : finset (finset α)} {U : finset α} {t : ℕ}

section partition

  def tuples_on (s : finset α) (m t : ℕ) : finset (ℕ → finset α) :=
  (finset.pi (range t) (λ _, s.powerset_len m)).map $
    { to_fun := λ f i, if h : i < t then f i (by simpa using h) else ∅,
      inj' :=
      begin
        rintro f g h,
        ext x hx : 2,
        simpa [dif_pos (finset.mem_range.1 hx)] using function.funext_iff.1 h x,
      end }

  lemma mem_tuples_on {m t : ℕ} {s : finset α} (f : ℕ → finset α) :
    f ∈ tuples_on s m t ↔ (∀ i < t, f i ⊆ s ∧ (f i).card = m) ∧ ∀ i ≥ t, f i = ∅ :=
  begin
    simp only [tuples_on, finset.mem_map, finset.mem_range, finset.mem_pi,
      function.embedding.coe_fn_mk, exists_prop, ge_iff_le, mem_powerset_len],
    split,
    { rintro ⟨f, hf₁, rfl⟩,
      refine ⟨λ i hi, _, λ i hi, _⟩,
      { simpa [dif_pos hi] using hf₁ _ hi },
      simp only [dif_neg hi.not_lt] },
    rintro ⟨hf₁, hf₂⟩,
    refine ⟨λ i _, f i, hf₁, _⟩,
    ext i : 1,
    split_ifs,
    { refl },
    rw hf₂ _ (le_of_not_lt h),
  end

  -- We view s,m,t- partitions as ordered sequences W0, W1, W2, ... with the conditions:
  --   Wj for j ≥ t is empty
  --      (essentially this says W is defined up to but not including t)
  --   Wj for j < t is a subset of s
  --   Wj for j < t has cardinality m
  --   the collection {Wj for j < t} is pairwise disjoint
  -- In most cases we will have `s` as our entire finite universe
  -- NOTE the union of the Wj might not be s

  -- This is not a standard way of defining partitions, but it is *vital* for ours to be ordered
  -- so I use this version
  -- `partitions_on s m t` is the finite set of these partitions
  -- its Lean definition isn't very helpful, but `mem_partitions_on` says it does what it's meant to.
  -- So when proving things about `partitions_on`, you almost always want to be using this lemma
  -- rather than the definition (or `mem_partitions_on'` which is logically equivalent but sometimes
  -- may be more useful)

  def partitions_on (s : finset α) (m t : ℕ) : finset (ℕ → finset α) :=
  (tuples_on s m t).filter (λ f, ∀ i j < t, i ≠ j → disjoint (f i) (f j))

  lemma mem_partitions_on {m t : ℕ} {s : finset α} (f : ℕ → finset α) :
    f ∈ partitions_on s m t ↔
      (∀ i < t, f i ⊆ s ∧ (f i).card = m) ∧ (∀ i ≥ t, f i = ∅) ∧
      ∀ i j < t, i ≠ j → disjoint (f i) (f j) :=
  by simp only [partitions_on, mem_filter, mem_tuples_on, and_assoc]

  lemma mem_partitions_on' {m t : ℕ} {s : finset α} (f : ℕ → finset α) :
    f ∈ partitions_on s m t ↔
      (∀ i < t, (f i).card = m) ∧
      (∀ i ≥ t, f i = ∅) ∧
      (∀ i, f i ⊆ s) ∧
      ∀ i j, i ≠ j → disjoint (f i) (f j) :=
  begin
    rw mem_partitions_on,
    split,
    { rintro ⟨hf₁, hf₂, hf₃⟩,
      refine ⟨λ i hi, (hf₁ _ hi).2, hf₂, λ i, _, _⟩,
      { cases lt_or_le i t,
        { apply (hf₁ _ ‹_›).1 },
        rw hf₂ _ h,
        simp },
      intros i j h,
      wlog : i ≤ j using i j,
      { cases lt_or_le j t,
        { exact hf₃ i (case.trans_lt h_1) j ‹_› h },
        rw hf₂ j h_1,
        apply disjoint_empty_right },
      exact (this h.symm).symm },
    { rintro ⟨hf₁, hf₂, hf₃, hf₄⟩,
      exact ⟨λ i hi, ⟨hf₃ _, hf₁ _ hi⟩, hf₂, λ i _ j _, hf₄ i j⟩ }
  end

  lemma partitions_on_zero {s : finset α} {m : ℕ} :
    partitions_on s m 0 = {λ _, ∅} :=
  begin
    sorry
  end

  lemma subset_of_mem_partitions_on {m t : ℕ} {s : finset α} {f : ℕ → finset α}
    (hf : f ∈ partitions_on s m t) :
    (range t).bUnion f ⊆ s :=
  begin
    simp only [bUnion_subset, finset.mem_range],
    intros i hi,
    exact (((mem_partitions_on f).1 hf).1 i hi).1,
  end

  lemma card_bUnion_of_mem_partitions_on {m t : ℕ} {s : finset α} {f : ℕ → finset α}
    (hf : f ∈ partitions_on s m t) :
    ((range t).bUnion f).card = m * t :=
  begin
    rw mem_partitions_on at hf,
    rw [card_bUnion, mul_comm, finset.sum_const_nat, card_range],
    { intros i hi,
      exact (hf.1 i (by simpa using hi)).2 },
    simpa only [mem_range] using hf.2.2,
  end

  def split_partition (f : ℕ → finset α) : (ℕ → finset α) × finset α := (λ i, f (i+1), f 0)
  lemma split_partition_bij :
    function.bijective (split_partition : (ℕ → finset α) → (ℕ → finset α) × finset α) :=
  begin
    split,
    { intros f₁ f₂ h,
      ext n : 1,
      simp only [split_partition, prod.mk.inj_iff] at h,
      cases n,
      { exact h.2 },
      have := function.funext_iff.1 h.1 n,
      exact this },
    rintro ⟨f₁, f₂⟩,
    exact ⟨λ n, nat.cases_on n f₂ f₁, rfl⟩,
  end

  lemma split_partition_strong_surj {s : finset α} {m t} (f₁ : ℕ → finset α) (f₂ : finset α)
    (hf₁ : f₁ ∈ partitions_on s m t) (hf₂ : f₂ ⊆ s \ (range t).bUnion f₁)
    (hf₃ : f₂.card = m) :
    ∃ f : ℕ → finset α, f ∈ partitions_on s m (t + 1) ∧
      (split_partition f).fst = f₁ ∧ (split_partition f).snd = f₂ :=
  begin
    refine ⟨λ n, nat.cases_on n f₂ f₁, _, rfl, rfl⟩,
    sorry
  end

  -- state and prove that if `f ∈ partitions_on s m t`, then these three are true
  -- (split_partition f).1 ∈ partitions_on s m t
  -- (split_partition f).2 ⊆ s \ (range t).bUnion (split_partition f).1
  -- (split_partition f).2.card = m

  lemma card_partitions_on {s : finset α} {m t : ℕ} :
    (partitions_on s m t).card = ∏ i in range t, (s.card - m * i).choose m :=
  begin
    induction t with t ih,
    { rw [finset.range_zero, finset.prod_empty, partitions_on_zero, finset.card_singleton] },
    rw [finset.prod_range_succ, ←ih],
    let extension : finset (Σ (i : ℕ → finset α), finset α) :=
      (partitions_on s m t).sigma (λ f, (s \ (range t).bUnion f).powerset_len m),
    have : extension.card = (partitions_on s m t).card * (s.card - m * t).choose m,
    { simp only [finset.card_sigma, finset.card_powerset_len],
      have : ∀ f ∈ partitions_on s m t,
        (s \ (range t).bUnion f).card.choose m = (s.card - m * t).choose m,
      { intros f hf,
        have : (range t).bUnion f ⊆ s,
        { apply subset_of_mem_partitions_on hf },
        rw [card_sdiff this, card_bUnion_of_mem_partitions_on hf] },
      rw [sum_congr rfl this, sum_const, smul_eq_mul] },
    rw ←this,
    refine card_congr (λ f _, ⟨(split_partition f).1, (split_partition f).2⟩) _ _ _,
    { intros f hf,
      rw mem_partitions_on' at hf,
      simp only [extension, mem_sigma, mem_powerset_len],
      sorry },
    { rintro f₁ f₂ hf₁ hf₂,
      simp only [heq_iff_eq, and_imp],
      intros h₁ h₂,
      refine split_partition_bij.1 _,
      ext : 1; assumption },
    rintro ⟨f₁, f₂⟩,
    simp only [mem_sigma, sigma.mk.inj_iff, heq_iff_eq, exists_prop, and_imp,
      mem_powerset_len],
    apply split_partition_strong_surj,
  end

  -- ((partitions_on s m t).filter (λ f : ℕ → finset α, f 0 = V)).card = sorry :=

end partition

#exit

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
  intros A h1 B h2 h3 h4,
  unfold to_antichain at h1,
  rw finset.mem_coe at h1,
  rw finset.mem_filter at h1,
  cases h1 with h5 h6,
  specialize h6 B,
  unfold to_antichain at h2,
  rw finset.mem_coe at h2,
  rw finset.mem_filter at h2,
  cases h2 with h7 h8,
  specialize h8 A,
  have h9 := h8(h5),
  have h11 := h9(h4),
  apply h3,
  exact h11,
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
-- this is 𝒢 the function
def the_partial_function (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) : ℕ → finset (finset α)
| i :=
    finset.image (λ S, S \ (finset.range (i+1)).bUnion W) $
    @finset.filter _
      (λ S, 2 ^ (t - i - 1) ≤ (S \ (finset.range (i+1)).bUnion W).card ∧
            (∀ j < i, ∀ X ∈ the_partial_function j, ¬ X ⊆ S) ∧
            ∀ S' ∈ 𝒮, S' \ (finset.range (i+1)).bUnion W ⊂ S \ (finset.range (i+1)).bUnion W →
              ¬ ∀ (j < i), ∀ (X ∈ the_partial_function j), ¬ X ⊆ S')
      (λ S, @and.decidable _ _ _ (@and.decidable _ _ _ finset.decidable_dforall_finset))
      -- this decidability detour is *really weird*, it indicates something is bad in mathlib
      -- I think...
    𝒮

def the_function (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) :=
(finset.range t).bUnion (the_partial_function W 𝒮 t)

lemma bUnion_indep {i : ℕ} (W₁ W₂ : ℕ → finset α) (h : ∀ j ≤ i, W₁ j = W₂ j) :
  (range (i+1)).bUnion W₁ = (range (i+1)).bUnion W₂ :=
begin
  ext x,
  simp only [finset.mem_range_succ_iff, finset.mem_bUnion],
  refine bex_congr (λ j hj, _),
  rw h _ hj
end

lemma the_partial_function_indep {𝒮 : finset (finset α)} {t i : ℕ} (W₁ W₂ : ℕ → finset α)
  (h : ∀ j ≤ i, W₁ j = W₂ j) :
  the_partial_function W₁ 𝒮 t i = the_partial_function W₂ 𝒮 t i :=
begin
  induction i using nat.strong_induction_on with i ih,
  -- change finset.image _ _ = finset.image _ _,
  -- -- induction i,
  rw [the_partial_function.equations._eqn_1 W₂, the_partial_function],
  rw [bUnion_indep W₁ W₂ h],
  have : ∀ (p : finset α → Prop), (∀ j < i, ∀ X ∈ the_partial_function W₁ 𝒮 t j, p X) ↔
    (∀ j < i, ∀ X ∈ the_partial_function W₂ 𝒮 t j, p X),
  { intro p,
    refine ball_congr (λ j hj, _),
    rw ih j hj (λ k hk, h _ (hk.trans hj.le)) },
  congr' 2,
  ext S,
  simp only [this],
end

lemma thm1_part_two (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) (ht : 1 ≤ t) :
  (∃ S ∈ 𝒮, S ⊆ (range t).bUnion W) ∨ ∀ S ∈ 𝒮, ∃ X ∈ the_function W 𝒮 t, X ⊆ S :=
begin
  sorry
end

def sample_space (α : Type*) [fintype α] [decidable_eq α] (m t : ℕ) :=
partitions_on (finset.univ : finset α) m t

def finset.expectation {α M : Type*} [field M] (s : finset α) (f : α → M) : M :=
(∑ x in s, f x) / s.card

local notation (name := finset.expectation)
  `𝔼` binders ` in ` s `, ` r:(scoped:67 f, finset.expectation s f) := r

lemma expectation_eq {α M : Type*} [field M] {s : finset α} {f : α → M} :
  𝔼 x in s, f x = ∑ x in s, f x / s.card :=
by rw [finset.expectation, sum_div]

variables [fintype α]

lemma thm1_part_one {m t : ℕ} {𝒮 : finset (finset α)} {U : finset (finset α)} {ε : ℝ}
  (hm : 1 ≤ m) (ht : 1 ≤ t) (hε : 0 < ε)
  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) (hU : spread ε U)
  (h : ∀ (R : finset α) i < t,
    (((sample_space α m t).filter (λ (W : ℕ → finset α), W i ⊆ R)).card : ℝ) ≤
      ((64 * ε) ^ (m - R.card) / (fintype.card α).choose R.card) * (sample_space α m t).card) :
  𝔼 W in sample_space α m t, 𝔼 u in U, ((shadow (the_function W 𝒮 t) u).card : ℝ) < 1 / 8 :=
begin
  sorry
end

lemma cor1 {m t : ℕ} {𝒮 : finset (finset α)} {U : finset (finset α)} {ε : ℝ}
  (hm : 1 ≤ m) (ht : 1 ≤ t) (hε : 0 < ε) (hn : ε ≤ m / 64 * fintype.card α)
  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) (hU : spread ε U) :
  𝔼 W in finset.univ.powerset_len (m * t),
    𝔼 Ws in partitions_on W m t,
      𝔼 u in U, ((shadow (the_function Ws 𝒮 t) u).card : ℝ) < 1 / 8 ∧
  ∀ W, (∃ S ∈ 𝒮, S ⊆ W) ∨ ∀ Ws ∈ partitions_on W m t, ∀ S ∈ 𝒮, ∃ X ∈ the_function Ws 𝒮 t, X ⊆ S :=
begin
  sorry
end

-- the things from here down are Bhavik's proofs of stuff which is now (probably) not necessary
-- but I'm keeping them just in case they turn out useful

-- lemma part_one_one_easy_bit (R : finset α) (h : ¬ ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R) :
--   ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
-- begin
--   rw [finset.filter_false_of_mem, card_empty],
--   { apply nat.zero_le _ },
--   rintro T hT rfl,
--   exact h ⟨T, hT, subset_union_left _ _⟩,
-- end

-- lemma part_one_one_other_easy_bit (R : finset α) (hR : ¬ W i ⊆ R) :
--   ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
-- begin
--   rw [finset.filter_false_of_mem, card_empty],
--   { apply nat.zero_le _ },
--   rintro T hT rfl,
--   exact hR (subset_union_right _ _),
-- end

-- lemma part_one_one_hard_bit_first_step {R : finset α} (hR : W i ⊆ R)
--   (h : ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R) :
--   (𝒮.filter (λ S, S \ (finset.range i).bUnion W ⊆ R ∧
--     S \ (finset.range (i + 1)).bUnion W ∈ the_partial_function' W 𝒮 t i)).nonempty :=
-- begin
--   obtain ⟨T, hT₁, hT₂⟩ := h,
--   rw [the_partial_function_eq] at hT₁,
--   replace hT₁ := to_antichain_subset hT₁,
--   simp only [the_partial_function', mem_filter, finset.mem_image, exists_prop, and_assoc,
--     finset.nonempty] at hT₁ ⊢,
--   obtain ⟨S, hS₁, hS₂, rfl⟩ := hT₁,
--   refine ⟨S, hS₁, _, S, hS₁, hS₂, rfl⟩,
--   rw [range_succ, finset.bUnion_insert, sdiff_union_distrib] at hT₂,
--   intros x hx,
--   by_cases x ∈ W i,
--   { apply hR h },
--   apply hT₂,
--   simp only [finset.mem_inter, mem_sdiff, finset.mem_bUnion, finset.mem_range, exists_prop,
--     not_exists, not_and] at hx ⊢,
--   tauto
-- end


-- #check cond_count
-- #check matrix.vec_cons
-- lemma part_one_one (R : finset α)  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) :
--   ((the_partial_function W 𝒮 t i).filter (λ T, R = T ∪ W i)).card ≤ 2 ^ (2 ^ (t - i)) :=
-- begin
--   -- by_cases h₁ : W i ⊆ R,
--   -- { by_cases h₂ : ∃ T ∈ the_partial_function W 𝒮 t i, T ⊆ R,
--   --   { apply part_one_one_hard_bit _ h₁ hS h₂ },
--   --   apply part_one_one_easy_bit _ h₂ },
--   -- apply part_one_one_other_easy_bit _ h₁,
-- end

-- variables {Ω : Type*} [measurable_space Ω] {μ : measure Ω}

-- instance {α : Type*} : measurable_space (finset α) := ⊤

-- def spread_distribution (μ : measure Ω) (ε : ℝ) (UU : Ω → finset α) : Prop :=
-- ∀ Z : finset α, (μ {ω | Z ⊆ UU ω}).to_real ≤ ε ^ Z.card

-- lemma spread_iff_uniform (ε : ℝ) (U : finset (finset α)) (UU : Ω → finset α)
--   (hUU : pdf.is_uniform UU (U : set (finset α)) μ measure.count) :
--   spread ε U ↔ spread_distribution μ ε UU :=
-- by sorry -- TODO: Bhavik

-- lemma exists_uniform {E : Type*} [measurable_space E] (s : set E) (μ : measure E) [sigma_finite μ]
--   (hs : measurable_set s) :
--   pdf.is_uniform id s (μ[|s]) μ :=
-- begin
--   haveI : has_pdf (id : E → E) (μ[|s]) μ,
--   { refine ⟨⟨measurable_id, s.indicator ((μ s)⁻¹ • 1), _, _⟩⟩,
--     { refine measurable.indicator _ hs,
--       refine measurable_one.const_smul _ },
--     rw [with_density_indicator hs, with_density_smul _ measurable_one, with_density_one,
--       measure.map_id],
--     refl },
--   change _ =ᵐ[_] _,
--   apply ae_eq_of_forall_set_lintegral_eq_of_sigma_finite,
--   { apply measurable_pdf },
--   { exact (measurable_one.const_smul _).indicator hs },
--   intros A hA hA',
--   rw [←map_eq_set_lintegral_pdf (id : E → E) (μ[|s]) μ hA],
--   rw lintegral_indicator _ hs,
--   rw measure.map_id,
--   simp only [pi.smul_apply, pi.one_apply, algebra.id.smul_eq_mul, mul_one, lintegral_const,
--     measure.restrict_apply, measurable_set.univ, set.univ_inter],
--   rw [cond_apply _ hs, measure.restrict_apply hs],
-- end

-- lemma exists_uniform' (ε : ℝ) (U : finset (finset α)) : ∃ (μ : measure (finset α))
--   (UU : finset α → finset α), pdf.is_uniform UU (U : set (finset α)) μ measure.count :=
-- ⟨_, _, exists_uniform _ _ measurable_space.measurable_set_top⟩

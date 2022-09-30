import algebra.big_operators.ring
import data.finset.finsupp
import probability.density
import probability.independence
import probability.conditional_expectation
import probability.notation
import probability.cond_count
import analysis.special_functions.log.base
import data.nat.basic
import data.finset.basic

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
    ext,
    split,
    { rw mem_partitions_on,
      intro h,
      rcases h with ⟨h1, h2, h3⟩,
      norm_num,
      ext1,
      have hx : 0 ≤ x := by linarith,
      exact h2 x hx, },
    { intro h,
      rw mem_partitions_on,
      refine ⟨_, _, _⟩,
      { intros i hi,
        norm_num at h,
        simp only [h, empty_subset, card_empty, true_and],
        linarith, },
      { intros i hi,
        norm_num at h,
        rw h, },
      { intros i hi j hj hij,
        norm_num at h,
        simp only [h, disjoint_empty_right], }, },
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
    rw mem_partitions_on,
    refine ⟨_, _, _⟩,
    { intros i hi,
      refine ⟨_, _⟩,
      { cases i,
        { dsimp only,
          exact subset_trans hf₂ (finset.sdiff_subset s _), },
        { dsimp only,
          have hit : i < t,
          { rw nat.succ_eq_add_one at hi,
            linarith, },
          rw mem_partitions_on at hf₁,
          rcases hf₁ with ⟨h1, h2, h3⟩,
          exact (h1 i hit).1, }, },
      { cases i,
        { dsimp only,
          exact hf₃, },
        { dsimp only,
          have hit : i < t,
          { rw nat.succ_eq_add_one at hi, linarith, },
          rw mem_partitions_on at hf₁,
          rcases hf₁ with ⟨h1, h2, h3⟩,
          exact (h1 i hit).2, }, }, },
    { intros i hi,
      cases i,
      { dsimp only,
        exfalso,
        linarith, },
      { dsimp only,
        have hit : i ≥ t,
        { rw nat.succ_eq_add_one at hi, linarith, },
        rw mem_partitions_on at hf₁,
        rcases hf₁ with ⟨h1, h2, h3⟩,
        exact h2 i hit, }, },
    { intros i hi j hj hij,
      rw mem_partitions_on at hf₁,
      rcases hf₁ with ⟨h1, h2, h3⟩,
      cases i,
      { cases j,
        { exfalso,
          norm_cast at hij, },
        { dsimp only,
          have hjt : j < t,
          { rw nat.succ_eq_add_one at hj, linarith, },
          suffices : disjoint f₂ ((range t).bUnion f₁),
          { have h : f₁ j ⊆ (range t).bUnion f₁,
            { apply finset.subset_bUnion_of_mem,
              exact mem_range.mpr hjt, },
            apply finset.disjoint_of_subset_right h,
            exact this, },
          { apply finset.disjoint_of_subset_left hf₂,
            exact finset.sdiff_disjoint, }, }, },
      { cases j,
        { dsimp only,
          have hit : i < t,
          { rw nat.succ_eq_add_one at hi, linarith, },
          suffices : disjoint ((range t).bUnion f₁) f₂,
          { have h : f₁ i ⊆ (range t).bUnion f₁,
            { apply finset.subset_bUnion_of_mem,
              exact mem_range.mpr hit, },
            apply finset.disjoint_of_subset_left h,
            exact this, },
          { apply finset.disjoint_of_subset_right hf₂,
            exact finset.disjoint_sdiff, }, },
        { dsimp only,
          have hij' : i ≠ j,
          { simpa only [ne.def, add_left_inj] using hij, },
          have hi' : i < t,
          { rw nat.succ_eq_add_one at hi, linarith, },
          have hj' : j < t,
          { rw nat.succ_eq_add_one at hj, linarith, },
          exact h3 i hi' j hj' hij', }, }, },
  end

  -- state and prove that if `f ∈ partitions_on s m (t+1)`, then these three are true
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
      refine ⟨_, _, _⟩,
      { rcases hf with ⟨hf1, hf2, hf3⟩,
        rw mem_partitions_on,
        refine ⟨_, _, _⟩,
        { intros i hi,
          refine ⟨_, _⟩,
          { apply hf3.1, },
          { apply hf1,
            exact nat.succ_lt_succ hi, }, },
        { intros i hi,
          apply hf2,
          exact nat.succ_le_succ hi, },
        { intros i hi j hj hij,
          apply hf3.2,
          exact (add_ne_add_left 1).mpr hij, }, },
      { change f 0 ⊆ s \ (range t).bUnion (split_partition f).fst,
        rw finset.subset_iff,
        intros x hx,
        rw finset.mem_sdiff,
        have hfs : f 0 ⊆ s,
        { apply hf.2.2.1, },
        simp only [finset.mem_of_subset hfs hx, mem_bUnion, mem_range, exists_prop, not_exists, not_and, true_and],
        intros i hi,
        by_contra c,
        have hfd : disjoint (f 0) ((split_partition f).fst i),
        { apply hf.2.2.2,
          linarith, },
        rw finset.disjoint_iff_ne at hfd,
        specialize hfd x hx x c,
        apply hfd, refl, },
      { apply hf.1,
        exact ne_zero.pos (nat.succ t), }, },
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

  lemma card_partition_fix_first {s : finset α} {m t : ℕ} {V : finset α}
    (hV : V.card = m) (hV' : V ⊆ s) :
    ((partitions_on s m (t + 1)).filter (λ f : ℕ → finset α, f 0 = V)).card =
      (partitions_on (s \ V) m t).card :=
  begin
    refine card_congr (λ f _, (split_partition f).1) _ _ _,
    { simp only [mem_filter, and_imp],
      rintro f hf rfl,
      rw [mem_partitions_on'] at hf ⊢,
      refine ⟨λ i hi, hf.1 _ (by simpa using hi), λ i hi, hf.2.1 _ (by simpa using hi),
        _, λ i j h, hf.2.2.2 (i+1) (j+1) (by simpa using h)⟩,
      intros i x hx,
      rw [mem_sdiff],
      exact ⟨hf.2.2.1 _ hx, disjoint_left.1 (hf.2.2.2 (i+1) 0 (nat.succ_ne_zero _)) hx⟩ },
    { simp only [mem_filter, and_imp],
      intros f₁ f₂ hf₁ h₁ hf₂ h₂ h,
      refine split_partition_bij.1 _,
      ext : 1,
      { exact h },
      rw [split_partition, split_partition],
      exact h₁.trans h₂.symm },
    { simp only [mem_filter, exists_prop],
      intros f hf,
      refine ⟨λ n, nat.cases_on n V f, ⟨_, rfl⟩, rfl⟩,
      rw [mem_partitions_on'],
      sorry -- xialu
      },
  end

  lemma partition_swap {s : finset α} {m t : ℕ} {f : ℕ → finset α} (hf : f ∈ partitions_on s m t)
    {i j : ℕ} (hi : i < t) (hj : j < t) :
    f ∘ equiv.swap i j ∈ partitions_on s m t :=
  begin
    rw mem_partitions_on' at hf ⊢,
    refine ⟨λ k hk, hf.1 _ _, λ k hk, hf.2.1 _ _, λ k, hf.2.2.1 _, λ _ _ h, hf.2.2.2 _ _ _⟩,
    { rcases eq_or_ne k i with rfl | ik,
      { rwa equiv.swap_apply_left },
      rcases eq_or_ne k j with rfl | jk,
      { rwa equiv.swap_apply_right },
      rwa equiv.swap_apply_of_ne_of_ne ik jk },
    { rwa equiv.swap_apply_of_ne_of_ne (hi.trans_le hk).ne' (hj.trans_le hk).ne' },
    { simpa using h },
  end

  lemma card_partition_fix_swap {s : finset α} {m t : ℕ} {V : finset α} {i j : ℕ}
    (hi : i < t) (hj : j < t) :
    ((partitions_on s m t).filter (λ f : ℕ → finset α, f i = V)).card =
      ((partitions_on s m t).filter (λ f : ℕ → finset α, f j = V)).card :=
  begin
    refine card_congr (λ f _, f ∘ equiv.swap i j) _ _ _,
    { simp only [mem_filter, function.comp_app, equiv.swap_apply_right, and_imp],
      intros f hf hf',
      refine ⟨_, hf'⟩,
      apply partition_swap hf hi hj },
    { intros f₁ f₂ _ _ h,
      refine function.surjective.injective_comp_right _ h,
      apply equiv.surjective },
    intros f hf,
    simp only [mem_filter, exists_prop, and_assoc] at hf ⊢,
    refine ⟨f ∘ equiv.swap i j, partition_swap hf.1 hi hj, _, _⟩,
    { simpa using hf.2 },
    ext x : 1,
    simp [equiv.swap_apply_self],
  end

  lemma card_partition_fix' {s : finset α} {m t : ℕ} {V : finset α}
    (hV : V.card = m) (hV' : V ⊆ s) {i : ℕ} (hi : i < t + 1) :
    ((partitions_on s m (t + 1)).filter (λ f : ℕ → finset α, f i = V)).card *
      s.card.choose m =
      (partitions_on s m (t + 1)).card :=
  begin
    rw [card_partition_fix_swap hi nat.succ_pos', card_partition_fix_first hV hV',
      card_partitions_on, card_partitions_on, card_sdiff hV', hV, finset.prod_range_succ', mul_zero,
      nat.sub_zero],
    simp only [mul_add_one, nat.sub_sub, add_comm],
  end

  lemma card_partition_fix {s : finset α} {m t : ℕ} {V : finset α}
    (hV : V.card = m) (hV' : V ⊆ s) {i : ℕ} (hi : i < t) :
    ((partitions_on s m t).filter (λ f : ℕ → finset α, f i = V)).card * s.card.choose m =
      (partitions_on s m t).card :=
  begin
    cases t,
    { simpa using hi },
    apply card_partition_fix' hV hV' hi,
  end

end partition

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

----- Lemmas for spred_iff_ratio ---------------------
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
  apply filter_subset,
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

lemma part_two_a_helper (ht : 1 ≤ t) (S) (h : ¬ S ⊆ (finset.range t).bUnion W) :
  2 ^ (t-1 - (t-1)) ≤ (S \ (finset.range (t-1 + 1)).bUnion W).card :=
begin
  have proof_subset : ∀ x : finset α, ∀ y : finset α, (x \ y).card = 0 → x ⊆ y,
    {intros hx hy card,
    have proof_empty : hx \ hy = ∅ := iff.elim_left finset.card_eq_zero card,
    have proof_final : hx ⊆ hy,
      {have temp1 := iff.elim_left finset.eq_empty_iff_forall_not_mem proof_empty,
      intros hx2 assump1,
      have assump2:hx2 ∉ hx \ hy := temp1 hx2,
      by_contra hnp,
      refine assump2 _,
      exact iff.elim_right (finset.mem_sdiff) (and.intro assump1 hnp),},
    exact proof_final,},
  have proof_card_zero : ∀ x:ℕ, (¬ 1 ≤ x ) → x = 0,
    {intro x,
    intro ineq,
    linarith,},
  have bound_simp : 1 ≤ (S \ (finset.range (t)).bUnion W).card,
    {by_contra bound2,
    exact h (proof_subset S ((finset.range (t)).bUnion W) (proof_card_zero (S \ (finset.range (t)).bUnion W).card bound2)),},
  have final : 2 ^ (t-1 - (t-1)) ≤ (S \ (finset.range (t-1 + 1)).bUnion W).card,
    {simp,
    have equality:t-1+1 = t, {linarith},
    rw equality,
    exact bound_simp,},
  exact final,
end
/-
lemma thm1_part_two (W : ℕ → finset α) (𝒮 : finset (finset α)) (t : ℕ) (ht : 1 ≤ t) :
  (∃ S ∈ 𝒮, S ⊆ (range t).bUnion W) ∨ ∀ S ∈ 𝒮, ∃ X ∈ the_function W 𝒮 t, X ⊆ S :=
begin
  by_contra,
  have h := not_or_distrib.1 h,
  have not_sub_w := h.1,
  apply h.2,
  intros hs el_s,
  let set_s' := finset.filter (λ Y, Y \ ((range t).bUnion W) ⊆ hs \ ((range t).bUnion W) ∧ (∀ (j:ℕ), j< t-1 → ∀ X:finset α, X ∈ the_partial_function W 𝒮 t j → ¬ X ⊆ Y)) 𝒮,
  by_contra assump,
  have non_empt : (∃ x:finset α, x ∈ set_s'),
    {use hs,
    rw finset.mem_filter,
    split, {exact el_s,},
      {split, {apply finset.subset_of_eq, refl,},
        {intros j bound X in_g,
        by_contra,
        have assump_pf:∃ x2 ∈ the_function W 𝒮 t, x2 ⊆ hs,
          {use X,
          split,
            {rw the_function,
            rw finset.mem_bUnion,
            use j,
            split,
              {rw finset.mem_range,
              linarith,},
              {exact in_g,}},{exact h,}},
        exact assump assump_pf,}}},
  let rem_w := λ (x:finset α), x \ (range t).bUnion W,
  let set_s'_map := finset.image rem_w set_s',
  have non_empt_im:set_s'_map.nonempty := finset.nonempty.image non_empt rem_w,
  have ex_min := exists_subset_minimal non_empt_im,
  cases ex_min with X ex_min,
  cases ex_min with X_el ex_min,
  apply assump,
  use X,
  have X_w := finset.mem_image.1 X_el,
  cases X_w with a aw_eq_x,
  cases aw_eq_x with a_in_s' func_a_x,
  have rw_X:a\(range t).bUnion W = X,{exact func_a_x,},
  have equality:t-1+1 = t, {rw nat.sub_add_cancel ht},
  have a_in_s := finset.mem_of_mem_filter a a_in_s',
  split,
    {rw the_function,
    rw finset.mem_bUnion,
    use t-1,
    rw finset.mem_range,
    split, {linarith,},
      {rw the_partial_function,
      rw finset.mem_image,
      use a,
      split,
        {rw finset.mem_filter,
        refine ⟨_,_,_,_⟩,
          {exact a_in_s,},
          {have rw_not_sub_w,
            {have el_imply := ((not_exists.1 not_sub_w) a),
            have el_imply_clean := not_exists.1 el_imply,
            exact el_imply_clean a_in_s,},
          have pow2_eq : ∀ (vr:ℕ), vr ≥ 1 → 2 ^ (vr-(vr-1)-1) = 2 ^ (vr-1 - (vr-1)),
          { intros vr ineq,
            rw [nat.sub_self, nat.sub_sub, nat.sub_add_cancel ineq, nat.sub_self] },
          rw (pow2_eq t ht),
          exact part_two_a_helper ht a rw_not_sub_w,},
          {exact (finset.mem_filter.1 a_in_s').2.2,},
          {rw equality,
          intros hs' hs'_in_s hs'_sub,
          have strict_sub_hs := finset.ssubset_of_ssubset_of_subset hs'_sub (finset.mem_filter.1 a_in_s').2.1,
          by_contra minset_prop,
          have sub_hs := (finset.ssubset_iff_subset_ne.1 strict_sub_hs).1,
          have fulfills_minset_prop := and.intro sub_hs minset_prop,
          have hs'_in_minset:hs' ∈ set_s' := finset.mem_filter.2 (and.intro hs'_in_s fulfills_minset_prop),
          have hs'_w_in_minset_map:hs'\ (range t).bUnion W ∈ set_s'_map,{apply finset.mem_image.2,use hs',use hs'_in_minset,},
          have s'_is_minset:hs'\ (range t).bUnion W = a\ (range t).bUnion W,
            {rw rw_X,
            have hs'_sub_x:hs'\ (range t).bUnion W ⊆ X,
              {rw eq.symm rw_X,
              exact (finset.ssubset_iff_subset_ne.1 hs'_sub).1,},
            exact ex_min (hs'\ (range t).bUnion W) hs'_w_in_minset_map hs'_sub_x,},
          exact (finset.ssubset_iff_subset_ne.1 hs'_sub).2 s'_is_minset,}},
        {rw equality,exact func_a_x,},},},
    {rw eq.symm rw_X,
    have a_w_sub_hs_w:a\ (range t).bUnion W ⊆ hs\ (range t).bUnion W := (finset.mem_filter.1 a_in_s').2.1,
    have hs_w_sub_hs: hs\ (range t).bUnion W ⊆ hs := finset.sdiff_subset hs ((range t).bUnion W),
    exact finset.subset.trans a_w_sub_hs_w hs_w_sub_hs,}
end-/


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

lemma filter_const {α : Type*} (p : Prop) [decidable p] (s : finset α) :
  s.filter (λ _, p) = if p then s else ∅ :=
begin
  by_cases p,
  { rw [filter_true_of_mem (λ _ _, h), if_pos h] },
  { rw [filter_false_of_mem (λ _ _, h), if_neg h] },
end

lemma powerset_filter_subset {α : Type*} [decidable_eq α] (n : ℕ) (s t : finset α) :
  (powerset_len n s).filter (λ i, i ⊆ t) = (powerset_len n (s ∩ t)) :=
by { ext x, simp [mem_powerset_len, subset_inter_iff, and.right_comm] }

open_locale classical

lemma partitions_on_eq {s : finset α} {m t} :
  partitions_on s m t = (s.powerset_len (m * t)).bUnion (λ W, partitions_on W m t) :=
begin
  ext f,
  simp only [mem_bUnion, exists_prop, mem_powerset_len, and_assoc],
  split,
  { rintro hf,
    refine ⟨(range t).bUnion f, subset_of_mem_partitions_on hf, card_bUnion_of_mem_partitions_on hf,
      _⟩,
    simp only [mem_partitions_on],
    simp only [mem_partitions_on'] at hf,
    exact ⟨λ i hi, ⟨subset_bUnion_of_mem _ (by simpa using hi), hf.1 _ hi⟩, hf.2.1,
      λ _ _ _ _ h, hf.2.2.2 _ _ h⟩ },
  rintro ⟨W, hW, hW', hf⟩,
  simp only [mem_partitions_on'] at hf ⊢,
  exact ⟨hf.1, hf.2.1, λ i, (hf.2.2.1 _).trans hW, hf.2.2.2⟩,
end

lemma partitions_on_inj_on {m t : ℕ} {W₁ W₂ : finset α}
  (hW₁ : W₁.card = m * t) (hW₂ : W₂.card = m * t) {f} :
  f ∈ partitions_on W₁ m t → f ∈ partitions_on W₂ m t → W₁ = W₂ :=
begin
  intros hf₁ hf₂,
  rw [←eq_of_subset_of_card_le (subset_of_mem_partitions_on hf₁),
      ←eq_of_subset_of_card_le (subset_of_mem_partitions_on hf₂)],
  { rw [hW₂, card_bUnion_of_mem_partitions_on hf₂] },
  { rw [hW₁, card_bUnion_of_mem_partitions_on hf₁] },
end

lemma random_partition (R : finset α) {m i : ℕ} (hi : i < t) :
  (fintype.card α).choose m *
    ((sample_space α m t).filter (λ Ws : ℕ → finset α, Ws i ⊆ R)).card =
      R.card.choose m * (sample_space α m t).card :=
begin
  have : ∀ (Ws : ℕ → finset α), Ws ∈ sample_space α m t →
    Ws i ∈ powerset_len m (univ : finset α),
  { simp only [mem_powerset_len_univ_iff, sample_space, mem_partitions_on', and_imp],
    intros f hf _ _ _,
    apply hf _ hi },
  have := @finset.bUnion_filter_eq_of_maps_to _ _ _ _ (sample_space α m t)
    (univ.powerset_len m) (λ f, f i) this,
  conv_lhs {rw ←this},
  rw [filter_bUnion, finset.card_bUnion],
  { have : ∀ x ∈ powerset_len m (univ : finset α),
      (((sample_space α m t).filter (λ (Ws : ℕ → finset α), Ws i = x)).filter
        (λ (Ws : ℕ → finset α), Ws i ⊆ R)).card =
      (((sample_space α m t).filter (λ (Ws : ℕ → finset α), Ws i = x)).filter
        (λ _, x ⊆ R)).card,
    { intros x hx,
      rw [filter_filter, filter_filter],
      congr' 2,
      ext f,
      simp { contextual := tt } },
    rw [sum_congr rfl this],
    simp only [filter_const, apply_ite finset.card, card_empty, sample_space],
    rw [←sum_filter],
    have : ∑ (a : finset α) in filter (λ (a : finset α), a ⊆ R) (powerset_len m univ),
      (fintype.card α).choose m *
        (filter (λ (Ws : ℕ → finset α), Ws i = a) (partitions_on univ m t)).card =
      ∑ (a : finset α) in powerset_len m R, (partitions_on univ m t).card,
    { apply finset.sum_congr _ _,
      { convert (powerset_filter_subset m univ R).trans _,
        rw univ_inter },
      intros x hx,
      rw [mul_comm, ←card_univ, card_partition_fix _ (subset_univ _) hi],
      rw mem_powerset_len at hx,
      exact hx.2 },
    rw [mul_sum, this, sum_const, smul_eq_mul, card_powerset_len] },
  simp only [mem_powerset_len_univ_iff],
  intros W₁ hW₁ W₂ hW₂ h,
  rw finset.disjoint_left,
  simp only [mem_filter, not_and, and_imp],
  rintro f _ rfl _ _ rfl,
  cases h rfl
end

lemma cor1 {m t : ℕ} {𝒮 : finset (finset α)} {U : finset (finset α)} {ε : ℝ}
  (hm : 1 ≤ m) (ht : 1 ≤ t) (hε : 0 < ε) (hn : ε ≤ m / 64 * fintype.card α)
  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) (hU : spread ε U) :
  𝔼 Ws in sample_space α m t,
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

--#exit
/-
-- variables {Ω : Type*} [measurable_space Ω] {μ : measure Ω}

lemma exists_uniform' (ε : ℝ) (U : finset (finset α)) : ∃ (μ : measure (finset α))
  (UU : finset α → finset α), pdf.is_uniform UU (U : set (finset α)) μ measure.count :=
⟨_, _, exists_uniform _ _ measurable_space.measurable_set_top⟩


--notation X ` ⊈ ` Y := ¬ (X ⊆ Y)
-/
-------------------------------------------------------------------------

-- noncomputable def lhs_sample_space (m t : ℕ) (U : finset (finset α)) :=
-- U.product
--   (finset.sigma (((finset.univ : finset α).powerset_len (m * t)).bUnion (λ W, partitions_on W m t)) $
--     (λ Ws, the_function Ws 𝒮 t))

--   #check lhs_sample_space

lemma lem2_part1 {m t : ℕ} {𝒮 : finset (finset α)} {U : finset (finset α)} {ε : ℝ}   (hm : 1 ≤ m)
  (ht : 1 ≤ t) (hε : 0 < ε) (hn : ε ≤ m / 64 * fintype.card α)
  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) (hU : spread ε U) :
  (((sample_space α m t).filter
      (λ Ws, ∀ S ∈ 𝒮, (shadow (the_function Ws 𝒮 t) S).nonempty)).card : ℝ) /
    (sample_space α m t).card ≤
  𝔼 Ws in sample_space α m t, 𝔼 u in U, ((shadow (the_function Ws 𝒮 t) u).card : ℝ) :=
begin
  sorry
end

lemma lem2_part2 {m t : ℕ} {𝒮 : finset (finset α)} {U : finset (finset α)} {ε : ℝ}   (hm : 1 ≤ m)
  (ht : 1 ≤ t) (hε : 0 < ε) (hn : ε ≤ m / 64 * fintype.card α)
  (hS : ∀ S ∈ 𝒮, finset.card S ≤ 2 ^ t) (hU : spread ε U) :
  (card (((univ : finset α).powerset_len (m * t)).filter (λ w, ∀T ∈ 𝒮, ¬ T ⊆ w)) : ℝ) /
    ((fintype.card α).choose (m*t)) ≤
  (((sample_space α m t).filter
    (λ Ws, ∀ S ∈ 𝒮, (shadow (the_function Ws 𝒮 t) S).nonempty)).card : ℝ) /
  (sample_space α m t).card :=
begin
  have : ∀ (Ws : ℕ → finset α),
    Ws ∈ sample_space α m t → (∀ S ∈ 𝒮, ¬ S ⊆ (range t).bUnion Ws) →
      ∀ S ∈ 𝒮, (shadow (the_function Ws 𝒮 t) S).nonempty,
  { intros Ws h h' S hS',
    obtain ⟨X, hX, hX'⟩ := ((cor1 hm ht hε hn hS hU).2 ((range t).bUnion Ws)).resolve_left
      (by simpa using h') Ws _ _ hS',
    { refine ⟨X, _⟩,
      simp only [shadow, mem_filter, hX, hX', and_self] },
    sorry },
  sorry
end

theorem Lem2 (S : finset (finset α)) (W : finset(finset α) ) (t m: ℕ )
(hel : ∀T ∈ S, (finset.card T:ℝ ) ≤ (2^t:ℝ ) ) (h_sp : spread (m*64⁻¹ / (fintype.card α )⁻¹) S):
  (finset.card ((univ.powerset_len (m * t)).filter (λ w, ∀T ∈ S, ¬ (T ⊆ w) )) : ℝ) ≤
    (nat.choose (fintype.card α) (m*t)) / 8 :=
begin
  sorry
end

theorem Cor2_easyver (S : finset (finset α) )(n k w m:ℕ )(hSk : ∀T∈S, finset.card T = k) (hk : 2 ≤ k)
(hn : n = 2*w*m*t) ( ε:ℝ ) (he : 0 ≤ ε ) (hspr : spread ε S) :
 ∃(T : finset (finset α ) ),  (T ⊆ S) ∧  (∀ B₁  B₂ ∈ T, B₁ ≠ B₂ →  disjoint B₁ B₂ )
 ∧ (2^(-9 : ℝ )*ε⁻¹/(real.logb  2 k) ≤ T.card ) :=
begin
  set t:= nat.ceil (real.logb 2 k) with ht,
  have h_t_le : real.logb 2 k ≤ t,
  {
    rw ht, exact nat.le_ceil (real.logb 2 ↑k),
  },


  sorry

end


theorem Cor2 (S : finset (finset α) )( k:ℕ )(hSk : ∀T∈S, finset.card T = k)
( ε:ℝ ) (he : 0 ≤ ε ) (hspr : spread ε S) : 2 ≤ k →  ∃(T : finset (finset α ) ),
 (T ⊆ S) ∧  (∀ B₁  B₂ ∈ T, B₁ ≠ B₂ →  disjoint B₁ B₂ ) ∧  (2^(-9 : ℝ )*ε⁻¹/(real.logb  2 k) ≤ T.card ) :=
begin
  set t:= nat.ceil (real.logb 2 k) with ht,
  have h_t_le : real.logb 2 k ≤ t := nat.le_ceil (real.logb 2 ↑k),


--Choose random partiiton of [n]

--Lemma2 is applicable

--Apply Lemma 2

--Expectation > w implies actual such case

--use the right T

--split,

sorry
end

--Using different index. We use w+1 , k+1 for w, k in the paper. Then we can have induction from k=1,
--and we don't need the prooves that 1 ≤ w,k.

def sunflower {α : Type*}[decidable_eq α ] (S : finset (finset α )) (num_petal: ℕ ) : Prop :=
  (finset.card S = num_petal) ∧ (∃(C : finset α), ∀ P₁ P₂ ∈ S, P₁ ≠ P₂ →  P₁ ∩ P₂ = C)

def Thm3 (w : ℕ)(k: ℕ ){S: finset (finset α )} (hT : ∀ T ∈ S, finset.card T = k+1)
: Prop :=  ∃r : ℝ , r ≤  (2:ℝ)^(10:ℝ)*(w+1 : ℝ )*(real.logb 2 (k+1)) ∧ (r^(k+1) ≤ S.card → ∃F⊆S, ( sunflower F (w+1)))


def smaller_sunflower {α : Type*}[decidable_eq α ] (S : finset (finset α )) (Z : finset α) : finset (finset α ) :=
S.image (λ s, s \ Z)

lemma sunflower_iff_smaller {S : finset (finset α)} {Z : finset α} (n: ℕ) (h : ∀ s ∈ S, Z ⊆ s) :
  sunflower S n ↔ sunflower (smaller_sunflower S Z) n :=
begin
  have injective : set.inj_on (λ s, s \ Z) S,
  { intros a ha b hb hab,
    dsimp at hab,
    have hZa : Z ⊆ a := h a ha,
    have hZb : Z ⊆ b := h b hb,
    suffices : (a \ Z) ∪ Z = (b \ Z) ∪ Z,
    { 
      sorry,
    },
    { rw hab, }
  },
  split,
  { intro hS,
    cases hS with hS1 hS2,
    refine ⟨_, _⟩,
    { 
      sorry
    },
    {
      sorry
    },
  },
  {
  sorry
  },
end


theorem Thm3' {w : ℕ}(k : ℕ ){r: ℝ}{S: finset (finset α )}  (hT : ∀ T ∈ S, finset.card T = k+1) 
: (w+1 : ℝ) = r → (real.logb 2 (k+1) = r * (2^9)⁻¹ * (w+1)⁻¹ ) →  (r^(k+1) ≤ finset.card S) → ∃F⊆S, ( sunflower F (w+1)) :=
-- I think r can be equal to 2^9 * w * log(k+1) and w+1 = r
begin
  induction k using nat.case_strong_induction_on with k ih generalizing S,
  {
    simp at *,
    intros hwr h_log hrkS, --- I dont understand k=0 case.
    have hU : ∃U ⊆ S, (finset.card U  = w+1) ∧ (∀ P₁ P₂ ∈ U, P₁ ≠ P₂ →  disjoint P₁ P₂),
    {
      rw ← hwr at hrkS, norm_cast at hrkS, --push_cast
      have tmp := exists_smaller_set S (w+1) hrkS,
      cases tmp, use tmp_w,
      split,
      { exact tmp_h.1 },
      {split, exact tmp_h.2,
        intros P1 hP1 P2 hP2 h12,
        have h_sing : ∀P ∈ tmp_w, finset.card P = 1 :=
        begin
          rw subset_iff at tmp_h, intros P hPP,
          have hSS := tmp_h.1 hPP, exact hT P hSS,
        end,
        obtain ⟨p1, rfl ⟩ := finset.card_eq_one.1 (h_sing P1 hP1),
        obtain ⟨p2, rfl ⟩:= finset.card_eq_one.1 (h_sing P2 hP2),
        simp,
        intro P12,
        exact h12 (finset.singleton_inj.2 P12),
      },
    },

    rcases hU with ⟨U,hU1,hU2,hU3⟩,
    use U, split, exact hU1,
    split, exact hU2,
    use ∅,
    simp only [ finset.disjoint_iff_inter_eq_empty] at hU3,
    exact hU3,
  },

  {
    intros hwr hn hrkS,
    by_contra, simp at h,

    -- S is not (r⁻¹)-spread
    have h_S_nspread : ¬(spread r⁻¹ S ),
    {
      by_contra htmp,
      have k2tmp : 2 ≤ k + 2 := by linarith,
      have rinv_pos : 0 ≤ r⁻¹ := begin rw ← hwr, apply le_of_lt, rw inv_pos, exact w.cast_add_one_pos,  end,
      have COR2:= Cor2 S (k+2) hT r⁻¹ rinv_pos htmp k2tmp,
      rcases COR2 with ⟨Ttmp,hTT1, hTT2, hTT3⟩,
      have hTtmpcard : (w+1) ≤ finset.card Ttmp,
      {
        simp at hn, simp at hTT3,
        sorry,
      },
      have Ttmptmp := exists_smaller_set Ttmp (w+1) hTtmpcard,
      rcases Ttmptmp with ⟨C, hC1, hC2 ⟩,
      specialize h C (subset_trans hC1 hTT1),
      apply h,
      split, exact hC2,
      use ∅,
      intros P1 hP1 P2 hP2 h12, 
      simp only [ finset.disjoint_iff_inter_eq_empty] at hTT2,
      apply hTT2 P1 (subset_iff.1 hC1 hP1) P2 ( subset_iff.1 hC1 hP2) h12,
    },

    -- Construction of Z and S'
    have hZ : ∃(Z:finset α), (finset.card (S.filter (λ s, Z ⊆ s)) : ℝ) > r^(k- finset.card Z),
    {
      by_contra h_con, simp at h_con,
      apply h_S_nspread, 
      unfold spread,
      intros Z, 
      specialize h_con Z, 
      have temp : r ^ (k - Z.card) ≤ r⁻¹ ^ Z.card * ↑(S.card),
      {
        --use hrKS and hwr
        sorry
      },
      convert (le_trans h_con temp),
    },
    rcases hZ with ⟨Z,hZ⟩,
    --define S'
    let S' := S.filter (λ s, Z ⊆ s), 

    -- S'' is the sunflower
    have hSmall :  sunflower (smaller_sunflower S' Z) (w+1), --change that some subset of S' is a sunflower
    {
      sorry --nontrivial sorry but not hard
    },
    --S is the sunflower
    have h_contains_Z :  ∀ s ∈ S', Z ⊆ s,
    {
      intros s, rw finset.mem_filter, intros hs, exact hs.2,
    },
    have hSprime : sunflower S' (w+1) := (sunflower_iff_smaller (w+1) h_contains_Z).2 hSmall,
    apply h S' (finset.filter_subset (λ s, Z ⊆ s) S) hSprime,
  }
end





/-theorem Thm3 {w k : ℕ}{S: finset (finset α )} (hw : 1 ≤ w) ( hk : 1 ≤ k) (hT : ∀ T ∈ S, finset.card T = k)
: ∃r : ℝ , r ≤  (2:ℝ)^(10:ℝ)*(w : ℝ )*(real.logb 2 k) ∧
(r^k ≤ S.card → ∃F⊆S, ( sunflower F w)) :=
begin

sorry

end -/

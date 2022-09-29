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

open finset set measure_theory probability_theory
open_locale big_operators measure_theory ennreal

variables {α : Type*} [fintype α] [decidable_eq α]
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

--#exit
/-
-- variables {Ω : Type*} [measurable_space Ω] {μ : measure Ω}

lemma exists_uniform' (ε : ℝ) (U : finset (finset α)) : ∃ (μ : measure (finset α))
  (UU : finset α → finset α), pdf.is_uniform UU (U : set (finset α)) μ measure.count :=
⟨_, _, exists_uniform _ _ measurable_space.measurable_set_top⟩


--notation X ` ⊈ ` Y := ¬ (X ⊆ Y)
-/
-------------------------------------------------------------------------
theorem Lem2 (S : finset (finset α)) (W : finset(finset α) ) (t m: ℕ )
(hel : ∀T ∈ S, (finset.card T:ℝ ) ≤ (2^t:ℝ ) ) (h_sp : spread (m*64⁻¹ / (fintype.card α )⁻¹) S):
--(hW  : finset.card W = m * t) :
  (finset.card (W.filter (λ w, ∀T ∈ S, ¬ (T ⊆  w) )) : ℝ) ≤ (nat.choose (fintype.card α) (m*t)) / 8:=
-- having trouble in `uniformly random set of size mt` W part
-- I don't know why (λ w, ∀T ∈ S, T ⊈ W ) has an error
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

--#check finset.card_eq_one


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
      have Ttmptmp := exists_smaller_set Ttmp (w+1) tTtmpcard,
      --apply (h T hTT1),
      unfold sunflower,

      sorry,
    },



    -- Construction of Z and S'

    -- S'' is the sunflower

    --S is the sunflower

  


    sorry
  }
end

theorem Thm3_equiv {w : ℕ}(k: ℕ ){r: ℝ}(S: finset (finset α )) (hw : 1 ≤ w) ( hk : 1 ≤ k) (hT : ∀ T ∈ S, finset.card T = k+1):  (Thm3 w k hT) :=
begin
end




/-theorem Thm3 {w k : ℕ}{S: finset (finset α )} (hw : 1 ≤ w) ( hk : 1 ≤ k) (hT : ∀ T ∈ S, finset.card T = k) 
: ∃r : ℝ , r ≤  (2:ℝ)^(10:ℝ)*(w : ℝ )*(real.logb 2 k) ∧ 
(r^k ≤ S.card → ∃F⊆S, ( sunflower F w)) :=
begin

sorry

end -/ 

import Mathlib

/-
A set of positive integers is called a multiplicative Sidon set if the equation
`a * b = c * d` with `a, b, c, d` in the set implies `{a, b} = {c, d}`. In this
file, we study the gaps in multiplicative Sidon sets. We define `gapMulSidon n`
to be the minimum value `g` such that there exists a multiplicative Sidon subset
`A ⊆ {0, ..., n}` where every sub-interval of length `g` contains an element of
`A`.

Theorem gap_bound below gives `gapMulSidon n = O(n^α)` for every `α > 1/3`.

In order to state a more general theorem that is formalized here, let us write
`Adm(α, ℓ)` for the property that for every `ρ > 0`, the Lebesgue measure of the
set of `x ∈ [0, n]` such that `(x, x + x^α]` contains fewer than `5^{1/α}`
primes is less than `n^{ℓ+ρ}`, for all sufficiently large `n`. We then show that
if `Adm(α, ℓ)` holds for some `ℓ < 3α`, then `gapMulSidon n = O(n^α)`. For more
details, see the paper "Gaps in multiplicative Sidon sets II" by Quanyu Tang and
I, which was based on an initial write-up by GPT 5.5-Pro.

The formalization below was obtained by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun).

Lean version: leanprover/lean4:v4.28.0
-/

open scoped BigOperators Real Nat Classical Pointwise
open Filter Finset MeasureTheory ProbabilityTheory

set_option maxHeartbeats 16000000
set_option maxRecDepth 4000
set_option grind.warning false

noncomputable section

/-- A set `C` of naturals is multiplicative Sidon if `a*b = c*d` with
    `a,b,c,d ∈ C` implies `{a,b} = {c,d}`. -/
def IsMulSidon (C : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ C → b ∈ C → c ∈ C → d ∈ C →
    a * b = c * d → ({a, b} : Finset ℕ) = {c, d}

/-- `gapMulSidon n` is the minimum value `g` such that there exists a multiplicative
    Sidon subset `A ⊆ {0, ..., n}` where every sub-interval of length `g` contains
    an element of `A`. -/
def gapMulSidon (n : ℕ) : ℕ :=
  sInf {g : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ IsMulSidon A ∧
    ∀ i : ℕ, i + g ≤ n → ∃ a ∈ A, i ≤ a ∧ a ≤ i + g}

/-- Prime threshold parameter `L_α := ⌈5^{1/α}⌉`. -/
def primeThresholdL (alpha : ℝ) : ℕ := ⌈(5 : ℝ) ^ (1 / alpha)⌉₊

/-- The prime-poor set `P_{α,n}`: reals `x ∈ [0, n]` such that `(x, x + x^α]`
    contains fewer than `L_α` primes. -/
def primePoorSet (alpha : ℝ) (n : ℕ) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ x ≤ (n : ℝ) ∧
    ((Finset.range (n + 1)).filter (fun p =>
      Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ alpha)).card
    < primeThresholdL alpha}

/-- Admissible prime-poor exponent: `Adm(α, ℓ)` holds if `ℓ ≥ 0` and for every `ρ > 0`,
    for all sufficiently large `n`, `Leb(P_{α,n}) < n^{ℓ+ρ}`. -/
def Adm (alpha ell : ℝ) : Prop :=
  0 ≤ ell ∧ ∀ rho : ℝ, 0 < rho → ∀ᶠ n in atTop,
    MeasureTheory.volume (primePoorSet alpha n) <
      ENNReal.ofReal ((n : ℝ) ^ (ell + rho))

/-- The block size parameter `H_{α,n} := 2 * ⌈n^α⌉`. -/
def blockSizeH (alpha : ℝ) (n : ℕ) : ℕ := 2 * ⌈(n : ℝ) ^ alpha⌉₊

/-- The "none-event" `None(A, T) = ⋂_{i ∈ T} Aᵢᶜ`: the event that none of the
    events indexed by `T` occurs. -/
def NoneEvent {Ω : Type*} {I : Type*} (A : I → Set Ω) (T : Finset I) : Set Ω :=
  ⋂ i ∈ T, (A i)ᶜ

/-- A simple graph `G` on `I` is a **dependency graph** for the event family `A`
    (w.r.t. measure `μ`) if, for every `i` and every `T ⊆ I \ ({i} ∪ Γ(i))`,
    the events `A i` and `NoneEvent A T` are independent. -/
def IsDependencyGraph {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    [DecidableEq I]
    (μ : Measure Ω) (A : I → Set Ω) (G : SimpleGraph I) [DecidableRel G.Adj] : Prop :=
  ∀ i : I, ∀ T : Finset I,
    (∀ j ∈ T, j ≠ i ∧ ¬G.Adj i j) →
    μ (A i ∩ NoneEvent A T) = μ (A i) * μ (NoneEvent A T)

/-
NoneEvent basic properties.
-/
@[simp]
lemma noneEvent_empty {Ω I : Type*} (A : I → Set Ω) :
    NoneEvent A ∅ = Set.univ := by
  simp [NoneEvent]

lemma noneEvent_measurableSet {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (S : Finset I) :
    MeasurableSet (NoneEvent A S) := by
  exact MeasurableSet.biInter ( Finset.countable_toSet S ) fun i hi => MeasurableSet.compl ( hA i )

lemma noneEvent_univ_eq {Ω I : Type*} [Fintype I] [DecidableEq I] (A : I → Set Ω) :
    NoneEvent A Finset.univ = ⋂ i, (A i)ᶜ := by
  unfold NoneEvent; aesop;

/-
Measure decomposition for NoneEvent.
-/
lemma measure_noneEvent_add {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {S : Finset I} {a : I} (_ha : a ∉ S) :
    μ (NoneEvent A (insert a S)) + μ (A a ∩ NoneEvent A S) = μ (NoneEvent A S) := by
  rw [ add_comm, ← MeasureTheory.measure_union ];
  · congr with x ; simp +contextual [ NoneEvent ];
    tauto;
  · simp +contextual [ Set.disjoint_left, NoneEvent ];
  · exact noneEvent_measurableSet _ ( fun i => hA i ) _

lemma toReal_noneEvent_insert {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {S : Finset I} {a : I} (ha : a ∉ S) :
    (μ (NoneEvent A (insert a S))).toReal =
    (μ (NoneEvent A S)).toReal - (μ (A a ∩ NoneEvent A S)).toReal := by
  rw [ eq_sub_iff_add_eq', ← ENNReal.toReal_add ] <;> norm_num [ hA, measure_noneEvent_add ];
  rw [ add_comm, measure_noneEvent_add ];
  · assumption;
  · exact ha

/-
One-step extension.
-/
lemma one_step_extension {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (x : I → ℝ) {S : Finset I} {a : I} (ha : a ∉ S)
    (hbound : (μ (A a ∩ NoneEvent A S)).toReal ≤ x a * (μ (NoneEvent A S)).toReal) :
    (μ (NoneEvent A (insert a S))).toReal ≥ (1 - x a) * (μ (NoneEvent A S)).toReal := by
  linarith [ toReal_noneEvent_insert μ A hA ha ]

/-
Iterated extension.
-/
lemma iterated_extension {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (x : I → ℝ) (hx1 : ∀ i, x i < 1)
    {C S : Finset I} (hCS : C ⊆ S)
    (hcond : ∀ U : Finset I, C ⊆ U → U ⊂ S → ∀ a ∈ S \ U,
      (μ (A a ∩ NoneEvent A U)).toReal ≤ x a * (μ (NoneEvent A U)).toReal) :
    (μ (NoneEvent A S)).toReal ≥ (μ (NoneEvent A C)).toReal * ∏ j ∈ S \ C, (1 - x j) := by
  induction' n : Finset.card ( S \ C ) using Nat.strong_induction_on with n ih generalizing S C;
  by_cases hS : S = C;
  · simp +decide [ hS ];
  · obtain ⟨a, haS, haC⟩ : ∃ a ∈ S, a ∉ C := by
      exact Finset.exists_of_ssubset ( lt_of_le_of_ne hCS ( Ne.symm hS ) );
    set S' : Finset I := S.erase a;
    have h_ind : (μ (NoneEvent A S')).toReal ≥ (μ (NoneEvent A C)).toReal * ∏ j ∈ S' \ C, (1 - x j) := by
      apply ih (Finset.card (S' \ C));
      · rw [ ← n, ← Finset.insert_erase haS, Finset.sdiff_eq_filter, Finset.sdiff_eq_filter ];
        rw [ Finset.filter_insert ] ; aesop;
      · exact fun i hi => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact haC hi ) ( hCS hi );
      · grind;
      · rfl;
    have h_one_step : (μ (NoneEvent A S)).toReal ≥ (1 - x a) * (μ (NoneEvent A S')).toReal := by
      have h_one_step : (μ (NoneEvent A (insert a S'))).toReal ≥ (1 - x a) * (μ (NoneEvent A S')).toReal := by
        apply one_step_extension μ A hA x;
        · exact Finset.notMem_erase _ _;
        · grind;
      rwa [ Finset.insert_erase haS ] at h_one_step;
    rw [ show S \ C = insert a ( S' \ C ) from ?_, Finset.prod_insert ];
    · nlinarith [ a, hx1 a ];
    · grind +revert;
    · grind

/-- The combined inductive property for the LLL. -/
abbrev LLLProp {Ω : Type*} [MeasurableSpace Ω] {I : Type*}
    (μ : Measure Ω) (A : I → Set Ω) (x : I → ℝ) (S : Finset I) : Prop :=
  (μ (NoneEvent A S)).toReal ≥ ∏ j ∈ S, (1 - x j) ∧
  ∀ i, i ∉ S → (μ (A i ∩ NoneEvent A S)).toReal ≤ x i * (μ (NoneEvent A S)).toReal

lemma lll_step_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (x : I → ℝ) (hx1 : ∀ i, x i < 1)
    (S : Finset I)
    (ih : ∀ T : Finset I, T ⊂ S → LLLProp μ A x T) :
    (μ (NoneEvent A S)).toReal ≥ ∏ j ∈ S, (1 - x j) := by
  rcases S.eq_empty_or_nonempty with ( rfl | ⟨ i, hi ⟩ ) <;> simp_all +decide [ LLLProp ];
  rw [ ← Finset.insert_erase hi, Finset.prod_insert ( Finset.notMem_erase _ _ ) ];
  refine' le_trans _ ( one_step_extension μ A hA x _ _ );
  · exact mul_le_mul_of_nonneg_left ( ih _ ( Finset.erase_ssubset hi ) |>.1 ) ( sub_nonneg.2 ( le_of_lt ( hx1 i ) ) );
  · simp +decide;
  · exact ih _ ( Finset.erase_ssubset hi ) |>.2 _ ( Finset.notMem_erase _ _ )

lemma lll_step_cond_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hDep : IsDependencyGraph μ A G)
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hxb : ∀ i, μ (A i) ≤
      ENNReal.ofReal (x i * ∏ j ∈ Finset.univ.filter (G.Adj i), (1 - x j)))
    (S : Finset I) (i : I) (hi : i ∉ S)
    (ih : ∀ T : Finset I, T ⊂ S → LLLProp μ A x T) :
    (μ (A i ∩ NoneEvent A S)).toReal ≤ x i * (μ (NoneEvent A S)).toReal := by
  have h_step1 : (μ (A i ∩ NoneEvent A S)).toReal ≤ (μ (A i)).toReal * (μ (NoneEvent A (S.filter (fun j => ¬G.Adj i j)))).toReal := by
    have h_step1 : μ (A i ∩ NoneEvent A S) ≤ μ (A i ∩ NoneEvent A (S.filter (fun j => ¬G.Adj i j))) := by
      refine' MeasureTheory.measure_mono _;
      simp +contextual [ Set.subset_def, NoneEvent ];
    have := hDep i ( S.filter ( fun j => ¬G.Adj i j ) );
    rw [ ← ENNReal.toReal_mul ];
    exact ENNReal.toReal_mono ( by aesop ) ( h_step1.trans ( this ( by aesop ) ▸ le_rfl ) );
  have h_step2 : (μ (A i)).toReal ≤ x i * ∏ j ∈ S.filter (G.Adj i), (1 - x j) := by
    refine' le_trans ( ENNReal.toReal_mono _ ( hxb i ) ) _;
    · exact ENNReal.ofReal_ne_top;
    · rw [ ENNReal.toReal_ofReal ];
      · rw [ ← Finset.prod_sdiff ( show Finset.filter ( fun j => G.Adj i j ) S ⊆ Finset.filter ( fun j => G.Adj i j ) Finset.univ from Finset.filter_subset_filter _ ( Finset.subset_univ _ ) ) ];
        exact mul_le_mul_of_nonneg_left ( mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 ( le_of_lt ( hx1 _ ) ) ) ( Finset.prod_le_one ( fun _ _ => sub_nonneg.2 ( le_of_lt ( hx1 _ ) ) ) fun _ _ => sub_le_self _ ( hx0 _ ) ) ) ( hx0 _ );
      · exact mul_nonneg ( hx0 i ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 ( le_of_lt ( hx1 _ ) ) );
  have h_step3 : (μ (NoneEvent A S)).toReal ≥ (μ (NoneEvent A (S.filter (fun j => ¬G.Adj i j)))).toReal * ∏ j ∈ S.filter (G.Adj i), (1 - x j) := by
    convert iterated_extension μ A hA x hx1 _ _ using 1;
    congr! 1;
    · rcongr j ; aesop;
    · exact Finset.filter_subset _ _;
    · exact fun U hU₁ hU₂ a ha => ih U hU₂ |>.2 a ( by aesop );
  nlinarith [ hx0 i, hx1 i, show 0 ≤ ( μ ( NoneEvent A ( { j ∈ S | ¬G.Adj i j } ) ) |> ENNReal.toReal ) from ENNReal.toReal_nonneg ]

theorem lll_inductive_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hDep : IsDependencyGraph μ A G)
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hxb : ∀ i, μ (A i) ≤
      ENNReal.ofReal (x i * ∏ j ∈ Finset.univ.filter (G.Adj i), (1 - x j)))
    (S : Finset I) : LLLProp μ A x S := by
  induction' S using Finset.strongInduction with S ih;
  exact ⟨ lll_step_lower_bound μ A hA x hx1 S ih, fun i hi => lll_step_cond_bound μ A hA G hDep x hx0 hx1 hxb S i hi ih ⟩

/-- **Asymmetric Lovász Local Lemma** .

    If `G` is a dependency graph for the events `(A i)_{i ∈ I}` and there exist
    weights `x : I → [0,1)` satisfying the LLL condition
    `ℙ(A i) ≤ x i · ∏_{j ∈ Γ(i)} (1 - x j)`,
    then `ℙ(⋂ᵢ Aᵢᶜ) > 0`. -/
theorem lovasz_local_lemma
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Set Ω) (hA_meas : ∀ i, MeasurableSet (A i))
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (hDep : IsDependencyGraph μ A G)
    (x : I → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_lt_one : ∀ i, x i < 1)
    (hx_bound : ∀ i, μ (A i) ≤
      ENNReal.ofReal (x i * ∏ j ∈ Finset.univ.filter (G.Adj i), (1 - x j))) :
    μ (⋂ i, (A i)ᶜ) > 0 := by
  have h_lower_bound : (μ (NoneEvent A Finset.univ)).toReal ≥ ∏ j ∈ Finset.univ, (1 - x j) := by
    apply lll_inductive_bounds μ A hA_meas G hDep x hx_nonneg hx_lt_one hx_bound Finset.univ |>.left;
  contrapose! h_lower_bound;
  rw [ show NoneEvent A Finset.univ = ⋂ i, ( A i ) ᶜ from noneEvent_univ_eq _ ] ;
  exact lt_of_le_of_lt ( ENNReal.toReal_mono ( by aesop ) h_lower_bound )
    ( Finset.prod_pos fun i _ => sub_pos.mpr ( hx_lt_one i ) )

lemma linear_two_power (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ n ih =>
    calc n + 1 + 1 ≤ 2 * (n + 1) := by omega
    _ ≤ 2 * 2 ^ n := by linarith
    _ = 2 ^ (n + 1) := by ring

lemma linear_exponential {q : ℝ} (hq : 1 < q) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ a : ℕ, (a : ℝ) + 1 ≤ A * q ^ a := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 ≤ r ∧ 2 ≤ q ^ r := by
    rcases pow_unbounded_of_one_lt 2 hq with ⟨ r, hr ⟩ ; exact ⟨ r, Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at hr ), hr.le ⟩;
  refine' ⟨ r, mod_cast hr.1, fun a => _ ⟩;
  obtain ⟨b, s, hs⟩ : ∃ b s : ℕ, a = b * r + s ∧ s < r := by
    exact ⟨ a / r, a % r, by rw [ Nat.div_add_mod' ], Nat.mod_lt _ hr.1 ⟩;
  have h1 : (a + 1 : ℝ) ≤ r * (b + 1) := by
    norm_cast; linarith;
  have h2 : (b + 1 : ℝ) ≤ 2 ^ b := by
    exact mod_cast Nat.recOn b ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ;
  exact h1.trans ( mul_le_mul_of_nonneg_left ( h2.trans <| by rw [ hs.1 ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) hr.2 _ ) <| by rw [ ← pow_mul ] ; exact pow_le_pow_right₀ hq.le <| by nlinarith ) <| by positivity )

lemma large_prime_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℕ, 2 ≤ B ∧ (2 : ℝ) ≤ (B : ℝ) ^ δ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ δ > 2 := by
    exact ⟨ ⌈ ( 2 : ℝ ) ^ ( 1 / δ ) ⌉₊ + 1, fun n hn => lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_lt_rpow ( by positivity ) ( Nat.lt_of_ceil_lt hn ) ( by positivity ) ) ⟩;
  exact ⟨ N + 2, by linarith, le_of_lt ( hN _ ( by linarith ) ) ⟩

lemma rpow_factorization_prod {m : ℕ} (hm : m ≠ 0) (δ : ℝ) :
    ∏ p ∈ m.primeFactors, (p : ℝ) ^ (δ * m.factorization p) = (m : ℝ) ^ δ := by
  have h_exp : (∏ p ∈ m.primeFactors, (p : ℝ) ^ (m.factorization p)) ^ δ = (m : ℝ) ^ δ := by
    exact congr_arg ( · ^ δ ) ( mod_cast Nat.factorization_prod_pow_eq_self hm );
  convert h_exp using 1;
  rw [ ← Real.finset_prod_rpow _ _ fun p hp => by positivity ] ; congr ; ext ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;

lemma factor_bound_large_prime {δ : ℝ} {p : ℕ} (hp : (2 : ℝ) ≤ (p : ℝ) ^ δ) (a : ℕ) :
    (a : ℝ) + 1 ≤ (p : ℝ) ^ (δ * a) := by
  rw [ Real.rpow_mul ( by positivity ) ];
  exact_mod_cast le_trans ( by norm_cast; linarith [ linear_two_power a ] ) ( pow_le_pow_left₀ ( by positivity ) hp a )

lemma tau_power_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 0 < m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ := by
  obtain ⟨ B, hB₁, hB₂ ⟩ := large_prime_cutoff hδ;
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, (∀ p, Nat.Prime p → p < B → ∀ a : ℕ, (a : ℝ) + 1 ≤ A p * (p : ℝ) ^ (δ * a)) ∧ (∀ p, Nat.Prime p → p < B → 1 ≤ A p) := by
    have hA : ∀ p, Nat.Prime p → p < B → ∃ A_p : ℝ, 1 ≤ A_p ∧ ∀ a : ℕ, (a : ℝ) + 1 ≤ A_p * ((p : ℝ) ^ δ) ^ a := by
      intro p hp hpB
      have hq : 1 < (p : ℝ) ^ δ := by
        exact Real.one_lt_rpow ( mod_cast hp.one_lt ) hδ
      exact linear_exponential hq;
    choose! A hA₁ hA₂ using hA;
    exact ⟨ A, fun p hp hp' a => by simpa [ Real.rpow_mul ( Nat.cast_nonneg _ ) ] using hA₂ p hp hp' a, hA₁ ⟩;
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 0 < m → (∏ p ∈ Nat.primeFactors m |> Finset.filter (fun p => p < B), (Nat.factorization m p + 1 : ℝ)) ≤ C * (∏ p ∈ Nat.primeFactors m |> Finset.filter (fun p => p < B), (p : ℝ) ^ (δ * Nat.factorization m p)) := by
    refine' ⟨ ∏ p ∈ Finset.filter Nat.Prime ( Finset.range B ), A p, _, _ ⟩;
    · exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun p hp => hA.2 p ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_range.mp ( Finset.mem_filter.mp hp |>.1 ) ) );
    · intro m hm; rw [ ← Finset.prod_sdiff <| show m.primeFactors.filter ( fun p => p < B ) ⊆ Finset.filter Nat.Prime ( Finset.range B ) from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Finset.mem_filter.mp hp |>.2, Nat.prime_of_mem_primeFactors <| Finset.mem_filter.mp hp |>.1 ⟩ ] ;
      rw [ mul_assoc ];
      refine' le_trans _ ( le_mul_of_one_le_left _ _ );
      · rw [ ← Finset.prod_mul_distrib ] ; exact Finset.prod_le_prod ( fun _ _ => by positivity ) fun p hp => by simpa using hA.1 p ( Nat.prime_of_mem_primeFactors <| Finset.mem_filter.mp hp |>.1 ) ( Finset.mem_filter.mp hp |>.2 ) _;
      · exact mul_nonneg ( Finset.prod_nonneg fun p hp => le_trans zero_le_one ( hA.2 p ( Nat.prime_of_mem_primeFactors ( Finset.mem_filter.mp hp |>.1 ) ) ( Finset.mem_filter.mp hp |>.2 ) ) ) ( Finset.prod_nonneg fun p hp => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
      · exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun p hp => hA.2 p ( Finset.mem_filter.mp ( Finset.mem_sdiff.mp hp |>.1 ) |>.2 ) ( Finset.mem_range.mp ( Finset.mem_filter.mp ( Finset.mem_sdiff.mp hp |>.1 ) |>.1 ) ) );
  have h_large_prime : ∀ m : ℕ, 0 < m → (∏ p ∈ Nat.primeFactors m |> Finset.filter (fun p => p ≥ B), (Nat.factorization m p + 1 : ℝ)) ≤ (∏ p ∈ Nat.primeFactors m |> Finset.filter (fun p => p ≥ B), (p : ℝ) ^ (δ * Nat.factorization m p)) := by
    intros m hm_pos
    apply Finset.prod_le_prod;
    · exact fun _ _ => by positivity;
    · intros p hp
      have h_large_prime_bound : (p : ℝ) ^ δ ≥ 2 := by
        exact le_trans hB₂ ( Real.rpow_le_rpow ( by positivity ) ( mod_cast Finset.mem_filter.mp hp |>.2 ) ( by positivity ) );
      exact factor_bound_large_prime h_large_prime_bound (m.factorization p);
  have h_combined : ∀ m : ℕ, 0 < m → (∏ p ∈ Nat.primeFactors m, (Nat.factorization m p + 1 : ℝ)) ≤ C * (∏ p ∈ Nat.primeFactors m, (p : ℝ) ^ (δ * Nat.factorization m p)) := by
    intro m hm; convert mul_le_mul ( hC.2 m hm ) ( h_large_prime m hm ) ( Finset.prod_nonneg fun _ _ => by positivity ) ( by nlinarith [ show 0 ≤ ∏ p ∈ m.primeFactors with p < B, ( p : ℝ ) ^ ( δ * m.factorization p ) by exact Finset.prod_nonneg fun _ _ => by positivity ] ) using 1 ; simp +decide [ Finset.prod_filter ] ; ring_nf;
    · simpa only [ ← Finset.prod_mul_distrib ] using Finset.prod_congr rfl fun x hx => by split_ifs <;> linarith;
    · rw [ mul_assoc, ← Finset.prod_union ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ) ] ; congr ; ext ; by_cases h : ‹ℕ› < B <;> aesop;
  refine' ⟨ C, hC.1, fun m hm => le_trans _ ( le_trans ( h_combined m hm ) _ ) ⟩;
  · rw_mod_cast [ Nat.card_divisors hm.ne' ];
  · rw [ rpow_factorization_prod hm.ne' ]

lemma absorb_constant {α : ℝ} (hα : 0 < α) {C : ℝ} (hC : 0 < C) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → C < (n : ℝ) ^ α := by
  exact ⟨ ⌊C ^ ( 1 / α ) ⌋₊ + 1, by linarith, fun n hn => lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one ] ) ( Real.rpow_lt_rpow ( by positivity ) ( Nat.lt_of_floor_lt hn ) ( by positivity ) ) ⟩

/-- **Uniform divisor bound** .
    For every `η > 0`, for all sufficiently large `n`,
    every positive integer `m ≤ n²` satisfies `τ(m) < n^η`. -/
theorem uniform_divisor_bound {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, (1 ≤ C ∧ ∀ m : ℕ, (0 < m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ (eta / 4))) := by
    convert tau_power_bound ( show 0 < eta / 4 by positivity ) using 6;
  have h_absorb : ∃ N : ℕ, (1 ≤ N ∧ ∀ n : ℕ, (N ≤ n → C < (n : ℝ) ^ (eta / 2))) := by
    apply absorb_constant (by linarith) (by linarith);
  obtain ⟨ N, hN₁, hN₂ ⟩ := h_absorb; filter_upwards [ Filter.eventually_ge_atTop N ] with n hn m hm₁ hm₂; specialize hC ; have := hC.2 m hm₁; refine lt_of_le_of_lt this ?_ ; refine lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by positivity ) hm₂ ( by positivity ) ) ?_ ) ?_;
  · linarith;
  · convert mul_lt_mul_of_pos_right ( hN₂ n hn ) ( Real.rpow_pos_of_pos ( by norm_cast; nlinarith : 0 < ( n:ℝ ) ^ 2 ) ( eta / 4 ) ) using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf

/-
    For a finite set `J` and reals `0 ≤ uⱼ ≤ 1`,
    `∏_{j ∈ J} (1 - uⱼ) ≥ 1 - ∑_{j ∈ J} uⱼ`.
-/
theorem prod_one_sub_le {ι : Type*} {J : Finset ι} {u : ι → ℝ}
    (hu_nonneg : ∀ j ∈ J, 0 ≤ u j) (hu_le_one : ∀ j ∈ J, u j ≤ 1) :
    1 - ∑ j ∈ J, u j ≤ ∏ j ∈ J, (1 - u j) := by
      induction J using Finset.induction <;> norm_num at *;
      simp_all +decide [ Finset.prod_insert, Finset.sum_insert ];
      · nlinarith [ show ∏ j ∈ ‹Finset ι›, ( 1 - u j ) ≤ 1 from Finset.prod_le_one ( fun _ _ => sub_nonneg.2 ( hu_le_one.2 _ ‹_› ) ) fun _ _ => sub_le_self _ ( hu_nonneg.2 _ ‹_› ) ];

/-- Abstract union-bound existence lemma: if the union of "bad" subsets of a
    finite set S is strictly smaller than S, then some element avoids all bad sets. -/
lemma exists_not_mem_biUnion_of_card_lt {α : Type*} [DecidableEq α]
    {S : Finset α} {R : Finset ρ} {bad : ρ → Finset α}
    (h : (R.biUnion bad).card < S.card) :
    ∃ s ∈ S, ∀ r ∈ R, s ∉ bad r := by
  by_contra h_all
  push_neg at h_all
  have : S ⊆ R.biUnion bad := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := h_all s hs
    exact Finset.mem_biUnion.mpr ⟨r, hr, hrs⟩
  exact Nat.lt_irrefl _ (lt_of_lt_of_le h (Finset.card_le_card this))

/-
Among all choice functions in a product of finite sets,
    the number selecting ≥ T elements from a dangerous set D is at most 2^|D| · L^(N-T).

    Here I is the index set, Q gives the finite sets, L is their common size,
    D is the dangerous subset of the union, and T is the threshold.
-/
lemma pi_filter_count_bound
    (I : Finset ℕ) (Q : ℕ → Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hQ_card : ∀ i ∈ I, (Q i).card = L)
    (hQ_disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Q i) (Q j))
    (D : Finset ℕ) (T : ℕ) (hT : T ≤ I.card) :
    ((I.pi Q).filter (fun f =>
      T ≤ (I.filter (fun i => ∃ h : i ∈ I, f i h ∈ D)).card)).card
    ≤ 2 ^ D.card * L ^ (I.card - T) := by
      -- By definition of $D$, we know that for each $i \in I$, $D \cap Q_i$ is a subset of $Q_i$.
      have hD_subset_Q : ∀ i ∈ I, D ∩ Q i ⊆ Q i := by
        exact fun i hi => Finset.inter_subset_right;
      -- By definition of $D$, we know that for each $i \in I$, $D \cap Q_i$ is a subset of $Q_i$ and has cardinality at most $L$.
      have hD_subset_Q_card : ∑ i ∈ I, #(D ∩ Q i) ≤ #D := by
        rw [ ← Finset.card_biUnion ];
        · exact Finset.card_le_card fun x hx => by aesop;
        · exact fun i hi j hj hij => Disjoint.mono inf_le_right inf_le_right ( hQ_disj i hi j hj hij );
      -- By definition of $D$, we know that for each $i \in I$, $D \cap Q_i$ is a subset of $Q_i$ and has cardinality at most $L$. Therefore, the number of ways to choose elements from $D$ is at most $2^{|D|}$.
      have hD_choose : ∏ i ∈ I, (1 + #(D ∩ Q i)) ≤ 2 ^ #D := by
        refine' le_trans _ ( pow_le_pow_right₀ ( by decide ) hD_subset_Q_card );
        rw [ ← Finset.prod_pow_eq_pow_sum ] ; exact Finset.prod_le_prod' fun i hi => by induction' #( D ∩ Q i ) with k hk <;> simp +decide [ *, pow_succ' ] ; nlinarith;
      -- For each $i \in I$, the number of ways to choose elements from $Q_i$ such that at least $T$ elements are in $D$ is at most $(1 + #(D ∩ Q_i)) * L^{I.card - T}$.
      have h_choose : ∀ S ⊆ I, S.card ≥ T → #({f ∈ Finset.pi I Q | ∀ i ∈ S, ∃ h, f i h ∈ D}) ≤ (∏ i ∈ S, #(D ∩ Q i)) * L ^ (I.card - S.card) := by
        intros S hS_sub hS_card
        have h_choose : #({f ∈ Finset.pi I Q | ∀ i ∈ S, ∃ h, f i h ∈ D}) ≤ (∏ i ∈ S, #(D ∩ Q i)) * (∏ i ∈ I \ S, L) := by
          have h_choose : #({f ∈ Finset.pi I Q | ∀ i ∈ S, ∃ h, f i h ∈ D}) ≤ (∏ i ∈ S, #(D ∩ Q i)) * (∏ i ∈ I \ S, #(Q i)) := by
            have h_choose : Finset.filter (fun f => ∀ i ∈ S, ∃ h, f i h ∈ D) (Finset.pi I Q) ⊆ Finset.image (fun f => fun i hi => if hiS : i ∈ S then f.1 i (by
            assumption) else f.2 i (by
            aesop)) (Finset.pi S (fun i => D ∩ Q i) ×ˢ Finset.pi (I \ S) (fun i => Q i)) := by
              intro f hf; simp_all +decide [ Finset.subset_iff ] ;
              exact ⟨ fun i hi => f i ( hS_sub hi ), fun i hi => f i ( Finset.mem_sdiff.mp hi |>.1 ), ⟨ fun i hi => ⟨ hf.2 i hi, hf.1 i ( hS_sub hi ) ⟩, fun i hi hi' => hf.1 i hi ⟩, funext fun i => by aesop ⟩
            refine le_trans ( Finset.card_le_card h_choose ) ?_;
            refine' Finset.card_image_le.trans _;
            simp +decide [ Finset.card_pi ];
          exact h_choose.trans ( Nat.mul_le_mul_left _ ( Finset.prod_le_prod' fun i hi => hQ_card i ( Finset.mem_sdiff.mp hi |>.1 ) ▸ le_rfl ) );
        simp_all +decide [ Finset.card_sdiff ];
        rwa [ Finset.inter_eq_left.mpr hS_sub ] at h_choose;
      -- By summing over all subsets $S$ of $I$ with $|S| \geq T$, we get the desired bound.
      have h_sum : #({f ∈ Finset.pi I Q | T ≤ #({i ∈ I | ∃ h, f i h ∈ D})}) ≤ ∑ S ∈ Finset.powerset I, if S.card ≥ T then (∏ i ∈ S, #(D ∩ Q i)) * L ^ (I.card - S.card) else 0 := by
        have h_sum : {f ∈ Finset.pi I Q | T ≤ #({i ∈ I | ∃ h, f i h ∈ D})} ⊆ Finset.biUnion (Finset.powerset I) (fun S => if S.card ≥ T then {f ∈ Finset.pi I Q | ∀ i ∈ S, ∃ h, f i h ∈ D} else ∅) := by
          grind +splitImp;
        refine le_trans ( Finset.card_le_card h_sum ) ?_;
        exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun x hx => by aesop );
      refine le_trans h_sum ?_;
      refine le_trans ?_ ( Nat.mul_le_mul_right _ hD_choose );
      simp +decide [ add_comm 1, Finset.prod_add ];
      rw [ Finset.sum_mul _ _ _ ];
      gcongr;
      split_ifs <;> [ exact Nat.mul_le_mul_left _ ( pow_le_pow_right₀ hL ( Nat.sub_le_sub_left ‹_› _ ) ) ; exact Nat.zero_le _ ]

/-
If sets A, B in a product of finite types depend on disjoint coordinate
sets T₁, T₂, then |A ∩ B| · |Ω| = |A| · |B|.
-/
lemma card_independence_of_disjoint_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, DecidableEq (S i)]
    {T₁ T₂ : Finset ι} (hT : Disjoint T₁ T₂)
    (A B : Finset ((i : ι) → S i))
    (hA : ∀ f g : (i : ι) → S i, (∀ i ∈ T₁, f i = g i) → (f ∈ A ↔ g ∈ A))
    (hB : ∀ f g : (i : ι) → S i, (∀ i ∈ T₂, f i = g i) → (f ∈ B ↔ g ∈ B)) :
    (A ∩ B).card * Fintype.card ((i : ι) → S i) = A.card * B.card := by
  have h_card_A : #A = # (Finset.image (fun f => fun i : T₁ => f i) A) * ∏ i ∈ Finset.univ \ T₁, Fintype.card (S i) := by
    have h_card_A : ∀ f ∈ A, Finset.card (Finset.filter (fun g => (fun i : T₁ => g i) = (fun i : T₁ => f i)) A) = ∏ i ∈ Finset.univ \ T₁, Fintype.card (S i) := by
      intro f hf
      have h_card_A : Finset.card (Finset.filter (fun g => (fun i : T₁ => g i) = (fun i : T₁ => f i)) A) = Finset.card (Finset.univ : Finset (Π i : {i : ι // i ∈ Finset.univ \ T₁}, S i)) := by
        refine' Finset.card_bij ( fun g hg => fun i => g i ) _ _ _ <;> simp +decide [ funext_iff ] at *;
        · grind;
        · intro b; use fun i => if hi : i ∈ T₁ then f i else b ⟨ i, by aesop ⟩ ; aesop;
      simp_all +decide [ Finset.card_univ ];
      conv_rhs => rw [ ← Finset.prod_attach ] ;
    have h_card_A : ∑ f ∈ Finset.image (fun f => fun i : T₁ => f i) A, Finset.card (Finset.filter (fun g => (fun i : T₁ => g i) = f) A) = #A := by
      rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop;
    rw [ ← h_card_A, Finset.sum_const_nat ];
    intro x hx; obtain ⟨ f, hf, rfl ⟩ := Finset.mem_image.mp hx; solve_by_elim;
  have h_card_B : #B = # (Finset.image (fun f => fun i : T₂ => f i) B) * ∏ i ∈ Finset.univ \ T₂, Fintype.card (S i) := by
    have h_card_B : ∀ b ∈ Finset.image (fun f : (i : ι) → S i => fun i : T₂ => f i) B, # (Finset.filter (fun f => (fun i : T₂ => f i) = b) B) = ∏ i ∈ Finset.univ \ T₂, Fintype.card (S i) := by
      intro b hb
      have h_filter : Finset.filter (fun f => (fun i : T₂ => f i) = b) B = Finset.image (fun f : (i : {x : ι // x ∉ T₂}) → S i => fun i => if hi : i ∈ T₂ then b ⟨i, hi⟩ else f ⟨i, hi⟩) (Finset.univ : Finset ((i : {x : ι // x ∉ T₂}) → S i)) := by
        ext f; simp;
        constructor <;> intro h;
        · exact ⟨ fun i => f i, funext fun i => by aesop ⟩;
        · grind;
      rw [ h_filter, Finset.card_image_of_injective ];
      · simp +decide [ Finset.card_univ ];
        refine' Finset.prod_bij ( fun i hi => i ) _ _ _ _ <;> simp +decide;
      · intro f g hfg; ext i; replace hfg := congr_fun hfg i; aesop;
    have h_card_B : #B = ∑ b ∈ Finset.image (fun f : (i : ι) → S i => fun i : T₂ => f i) B, # (Finset.filter (fun f => (fun i : T₂ => f i) = b) B) := by
      rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop;
    rw [ h_card_B, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ]
  have h_card_AB : #(A ∩ B) = # (Finset.image (fun f => fun i : T₁ => f i) A) * # (Finset.image (fun f => fun i : T₂ => f i) B) * ∏ i ∈ Finset.univ \ (T₁ ∪ T₂), Fintype.card (S i) := by
    have h_card_AB : Finset.card (A ∩ B) = Finset.sum (Finset.image (fun f => fun i : T₁ => f i) A ×ˢ Finset.image (fun f => fun i : T₂ => f i) B) (fun p => Finset.card (Finset.filter (fun f : (i : ι) → S i => (fun i : T₁ => f i) = p.1 ∧ (fun i : T₂ => f i) = p.2) (Finset.univ : Finset ((i : ι) → S i)))) := by
      rw [ ← Finset.card_biUnion ];
      · congr with f ; simp +decide [ Finset.mem_biUnion ];
        constructor <;> intro h;
        · exact ⟨ ⟨ f, h.1, rfl ⟩, ⟨ f, h.2, rfl ⟩ ⟩;
        · exact ⟨ hA _ _ ( fun i hi => by have := congr_fun h.1.choose_spec.2 ⟨ i, hi ⟩ ; aesop ) |>.1 h.1.choose_spec.1, hB _ _ ( fun i hi => by have := congr_fun h.2.choose_spec.2 ⟨ i, hi ⟩ ; aesop ) |>.1 h.2.choose_spec.1 ⟩;
      · intro p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ] ;
        lia;
    -- For each pair (p.1, p.2) in the product of the images, the number of functions f that satisfy the conditions is the product of the cardinalities of the sets S_i for i not in T₁ ∪ T₂.
    have h_card_filter : ∀ p ∈ Finset.image (fun f => fun i : T₁ => f i) A ×ˢ Finset.image (fun f => fun i : T₂ => f i) B, Finset.card (Finset.filter (fun f : (i : ι) → S i => (fun i : T₁ => f i) = p.1 ∧ (fun i : T₂ => f i) = p.2) (Finset.univ : Finset ((i : ι) → S i))) = ∏ i ∈ Finset.univ \ (T₁ ∪ T₂), Fintype.card (S i) := by
      intro p hp
      have h_filter : Finset.filter (fun f : (i : ι) → S i => (fun i : T₁ => f i) = p.1 ∧ (fun i : T₂ => f i) = p.2) (Finset.univ : Finset ((i : ι) → S i)) = Finset.image (fun g : (i : {x : ι // x ∉ T₁ ∪ T₂}) → S i => fun i => if hi : i ∈ T₁ ∪ T₂ then if hi₁ : i ∈ T₁ then p.1 ⟨i, hi₁⟩ else p.2 ⟨i, by
        exact Or.resolve_left ( Finset.mem_union.mp hi ) hi₁⟩ else g ⟨i, hi⟩) (Finset.univ : Finset ((i : {x : ι // x ∉ T₁ ∪ T₂}) → S i)) := by
        ext f; simp [Finset.mem_image];
        constructor;
        · rintro ⟨ h₁, h₂ ⟩;
          use fun i => f i;
          grind;
        · rintro ⟨ g, rfl ⟩ ; simp +decide [ funext_iff ] ;
          exact fun i hi₁ hi₂ => False.elim ( Finset.disjoint_left.mp hT hi₂ hi₁ )
      generalize_proofs at *;
      rw [ h_filter, Finset.card_image_of_injective ];
      · simp +decide [ Finset.card_univ ];
        refine' Finset.prod_bij ( fun i _ => i ) _ _ _ _ <;> simp +decide;
      · intro g₁ g₂ h_eq;
        ext ⟨ i, hi ⟩ ; replace h_eq := congr_fun h_eq i ; aesop;
    rw [ h_card_AB, Finset.sum_congr rfl h_card_filter, Finset.sum_const, Finset.card_product, smul_eq_mul, mul_assoc ]
  simp_all +decide ;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm];
  simp +decide [ ← mul_assoc, ← Finset.prod_sdiff ( Finset.subset_univ T₁ )];
  simp +decide [ mul_assoc ];
  rw [ ← Finset.prod_union ];
  · exact Or.inl <| Or.inl <| Or.inl <| by rw [ show T₁ ∪ univ \ ( T₁ ∪ T₂ ) = univ \ T₂ by ext i; by_cases hi₁ : i ∈ T₁ <;> by_cases hi₂ : i ∈ T₂ <;> simp_all +decide [ Finset.disjoint_left ] ] ;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₂ |>.2 ( Finset.mem_union_left _ hx₁ )

/-
Given a product of finite nonempty types `S i`, "bad" events indexed by `J` where
each event j requires specific values `val j i` for coordinates `i ∈ supp j`,
a dependency graph `G` with non-adjacent events having disjoint supports,
and LLL weights satisfying the LLL condition,
there exists an element avoiding all bad events.
-/
theorem product_lll_singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, DecidableEq (S i)]
    {J : Type*} [Fintype J] [DecidableEq J]
    (supp : J → Finset ι)
    (val : J → ((i : ι) → S i))
    (G : SimpleGraph J) [DecidableRel G.Adj]
    (h_dep : ∀ j₁ j₂ : J, j₁ ≠ j₂ → ¬G.Adj j₁ j₂ → Disjoint (supp j₁) (supp j₂))
    (x : J → ℝ) (hx_nn : ∀ j, 0 ≤ x j) (hx_lt : ∀ j, x j < 1)
    (h_lll : ∀ j, (∏ i ∈ supp j, ((Fintype.card (S i) : ℝ)⁻¹)) ≤
      x j * ∏ k ∈ Finset.univ.filter (G.Adj j), (1 - x k)) :
    ∃ f : (i : ι) → S i, ∀ j : J, ∃ i ∈ supp j, f i ≠ val j i := by
  -- Set up measurable spaces (⊤ on each factor, so all sets are measurable)
  letI inst_ms : ∀ i, MeasurableSpace (S i) := fun _ => ⊤
  haveI inst_msc : ∀ i, MeasurableSingletonClass (S i) := fun _ =>
    { measurableSet_singleton := fun _ => MeasurableSpace.measurableSet_top }
  -- Uniform probability measure on each factor
  set μ : (i : ι) → Measure (S i) := fun i =>
    (↑(Fintype.card (S i)) : ENNReal)⁻¹ • @Measure.count _ (inst_ms i) with hμ_def
  haveI inst_prob : ∀ i, IsProbabilityMeasure (μ i) := by
    intro i; constructor
    simp only [hμ_def, Measure.smul_apply, smul_eq_mul]
    rw [@Measure.count_apply_finite _ (inst_ms i) (inst_msc i) _ Set.finite_univ]
    simp
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
      (ENNReal.natCast_ne_top _)
  -- Product measure (automatically a probability measure)
  let μ_prod : Measure ((i : ι) → S i) := Measure.pi μ
  haveI : IsProbabilityMeasure μ_prod := inferInstance
  -- Define bad events: A j = {f | ∀ i ∈ supp j, f i = val j i}
  let A : J → Set ((i : ι) → S i) := fun j =>
    {f | ∀ i ∈ supp j, f i = val j i}
  -- All sets are measurable on finite types
  have hA_meas : ∀ j, MeasurableSet (A j) := fun _ =>
    (Set.toFinite _).measurableSet
  -- IsDependencyGraph: events with disjoint supports are independent
  have hDep : IsDependencyGraph μ_prod A G := by
    intro j T hT_disjoint
    set T' := Finset.biUnion T supp with hT'_def
    have h_dep_T : Disjoint (supp j) T' := by
      exact Finset.disjoint_left.mpr fun i hi₁ hi₂ => by obtain ⟨ k, hk₁, hk₂ ⟩ := Finset.mem_biUnion.mp hi₂; exact Finset.disjoint_left.mp ( h_dep j k ( by specialize hT_disjoint k hk₁; tauto ) ( by specialize hT_disjoint k hk₁; tauto ) ) hi₁ hk₂;
    -- By the properties of the product measure, we can write
    have h_prod_measure : ∀ (A B : Finset ((i : ι) → S i)), (∀ f g : (i : ι) → S i, (∀ i ∈ supp j, f i = g i) → (f ∈ A ↔ g ∈ A)) → (∀ f g : (i : ι) → S i, (∀ i ∈ T', f i = g i) → (f ∈ B ↔ g ∈ B)) → μ_prod (SetLike.coe A ∩ SetLike.coe B) = μ_prod (SetLike.coe A) * μ_prod (SetLike.coe B) := by
      intro A B hA hB
      have h_card : (SetLike.coe A ∩ SetLike.coe B).toFinset.card * (Fintype.card ((i : ι) → S i)) = A.card * B.card := by
        convert card_independence_of_disjoint_support h_dep_T A B hA hB using 1;
        simp +decide ;
      have h_measure : ∀ (A : Finset ((i : ι) → S i)), μ_prod (SetLike.coe A) = ENNReal.ofReal (A.card / Fintype.card ((i : ι) → S i)) := by
        intro A
        have h_measure : μ_prod (SetLike.coe A) = ∑ f ∈ A, ∏ i, (μ i {f i}) := by
          rw [ show (SetLike.coe A) = ⋃ f ∈ A, { f } by ext; simp +decide, MeasureTheory.measure_biUnion_finset ];
          · simp +zetaDelta at *;
          · exact fun x hx y hy hxy => Set.disjoint_singleton.2 hxy;
          · exact fun _ _ => MeasurableSet.singleton _;
        simp +zetaDelta at *;
        rw [ h_measure, ENNReal.ofReal_div_of_pos ] <;> norm_num;
        · rw [ ENNReal.ofReal_prod_of_nonneg fun _ _ => Nat.cast_nonneg _ ] ; norm_num [ div_eq_mul_inv ];
          rw [ ENNReal.prod_inv_distrib ];
          exact fun i _ j _ hij => Or.inl <| Nat.cast_ne_zero.mpr <| Fintype.card_ne_zero;
        · exact Finset.prod_pos fun i _ => Nat.cast_pos.mpr ( Fintype.card_pos );
      convert congr_arg ( fun x : ℕ => ENNReal.ofReal ( x / Fintype.card ( ( i : ι ) → S i ) ^ 2 ) ) h_card using 1;
      · grind +suggestions;
      · rw [ h_measure, h_measure, ← ENNReal.ofReal_mul ( by positivity ) ] ; push_cast ; ring_nf;
    convert h_prod_measure ( Finset.univ.filter fun f => ∀ i ∈ supp j, f i = val j i ) ( Finset.univ.filter fun f => ∀ k ∈ T, ¬∀ i ∈ supp k, f i = val k i ) _ _ using 1 <;> simp +decide [ NoneEvent ];
    · congr with f ; simp +decide [ A ];
    · congr! 2;
      ext f; simp [A];
    · grind;
    · grind +suggestions
  -- Probability bound
  have h_bound : ∀ j, μ_prod (A j) ≤
      ENNReal.ofReal (x j * ∏ k ∈ Finset.univ.filter (G.Adj j), (1 - x k)) := by
        intro j
        have h_measure : μ_prod (A j) = ENNReal.ofReal (∏ i ∈ supp j, (Fintype.card (S i) : ℝ)⁻¹) := by
          have h_measure : μ_prod (A j) = ∏ i, μ i {f : S i | (if i ∈ supp j then f = val j i else True)} := by
            convert MeasureTheory.Measure.pi_pi _ _;
            · ext; aesop;
            · exact fun i => IsFiniteMeasure.toSigmaFinite (μ i);
          rw [ h_measure, Finset.prod_congr rfl fun i hi => ?_ ];
          rotate_left;
          use fun i => if i ∈ supp j then ( Fintype.card ( S i ) : ENNReal ) ⁻¹ else 1;
          · split_ifs <;> simp +decide [ *, MeasureTheory.Measure.smul_apply ];
          · rw [ ENNReal.ofReal_prod_of_nonneg ] <;> norm_num [ Finset.prod_ite ];
            exact Finset.prod_congr rfl fun _ _ => by rw [ ENNReal.ofReal_inv_of_pos ( Nat.cast_pos.mpr ( Fintype.card_pos ) ) ] ; norm_num;
        rw [h_measure];
        exact ENNReal.ofReal_le_ofReal ( h_lll j )
  -- Apply the Lovász Local Lemma
  have h_pos := lovasz_local_lemma μ_prod A hA_meas G hDep x hx_nn hx_lt h_bound
  -- Extract element from positive measure set
  obtain ⟨f, hf⟩ : (⋂ j, (A j)ᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at h_pos
  exact ⟨f, fun j => by
    have hfj := Set.mem_iInter.mp hf j
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, A] at hfj
    push_neg at hfj
    exact hfj⟩

/-- A **pair label** is a tuple `(u, v, a, b)` where `u ≤ v`, `a ∈ S u`, `b ∈ S v`,
    and if `u = v` then `a = b`. -/
structure PairLabel (I : Finset ℕ) (S : ℕ → Finset ℕ) where
  u : ℕ
  v : ℕ
  a : ℕ
  b : ℕ
  hu : u ∈ I
  hv : v ∈ I
  huv : u ≤ v
  ha : a ∈ S u
  hb : b ∈ S v
  hdiag : u = v → a = b

/-
No bad label gives Sidon.
-/
theorem no_bad_label_gives_sidon {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (_hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (c : ℕ → ℕ) (_hc : ∀ i ∈ I, c i ∈ S i)
    (hno_bad : ∀ i j k l : ℕ, i ∈ I → j ∈ I → k ∈ I → l ∈ I →
      i ≤ j → k ≤ l → c i * c j = c k * c l →
      (i, j, c i, c j) ≠ (k, l, c k, c l) → False) :
    IsMulSidon (I.image c) := by
      intro x y u v hx hy hu hv hxy; simp_all +decide [ Finset.mem_image ] ;
      obtain ⟨ i, hi, rfl ⟩ := hx; obtain ⟨ j, hj, rfl ⟩ := hy; obtain ⟨ k, hk, rfl ⟩ := hu; obtain ⟨ l, hl, rfl ⟩ := hv;
      by_cases hij : i ≤ j <;> by_cases hkl : k ≤ l;
      · specialize hno_bad i j k l hi hj hk hl hij hkl hxy; aesop;
      · specialize hno_bad i j l k hi hj hl hk hij ( le_of_not_ge hkl ) ( by linarith ) ; aesop;
      · specialize hno_bad j i k l hj hi hk hl ( by linarith ) hkl ( by linarith ) ; aesop;
      · specialize hno_bad j i l k hj hi hl hk ( by linarith ) ( by linarith ) ( by linarith ) ; aesop

lemma eventually_nat_rpow_ge (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∀ᶠ (n : ℕ) in atTop, K ≤ (n : ℝ) ^ c :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
    |>.eventually_ge_atTop K

lemma eventually_nat_rpow_lt_one (c : ℝ) (hc : 0 < c) :
    ∀ᶠ (n : ℕ) in atTop, 2 * (n : ℝ) ^ (-(3 * c)) < (1 : ℝ) := by
  have : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ) ^ (-(3 * c)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by positivity : 0 < 3 * c)).comp
        tendsto_natCast_atTop_atTop)
  exact this.eventually (gt_mem_nhds zero_lt_one)

/-
Pair label instances
-/
@[ext]
lemma PairLabel.ext' {I : Finset ℕ} {S : ℕ → Finset ℕ} {p q : PairLabel I S}
    (hu : p.u = q.u) (hv : p.v = q.v) (ha : p.a = q.a) (hb : p.b = q.b) :
    p = q := by
  cases p; cases q; subst hu; subst hv; subst ha; subst hb; rfl

instance instFintypePairLabel (I : Finset ℕ) (S : ℕ → Finset ℕ) :
    Fintype (PairLabel I S) :=
  Fintype.ofInjective
    (fun p : PairLabel I S =>
      ((⟨p.u, p.hu⟩ : ↥I), (⟨p.v, p.hv⟩ : ↥I),
       (⟨p.a, Finset.mem_biUnion.mpr ⟨p.u, p.hu, p.ha⟩⟩ : ↥(I.biUnion S)),
       (⟨p.b, Finset.mem_biUnion.mpr ⟨p.v, p.hv, p.hb⟩⟩ : ↥(I.biUnion S))))
    (fun _p _q h => PairLabel.ext'
      (congr_arg (fun x => (Prod.fst x).val) h)
      (congr_arg (fun x => x.2.1.val) h)
      (congr_arg (fun x => x.2.2.1.val) h)
      (congr_arg (fun x => x.2.2.2.val) h))

instance instDecidableEqPairLabel (I : Finset ℕ) (S : ℕ → Finset ℕ) :
    DecidableEq (PairLabel I S) := fun p q =>
  if h : p.u = q.u ∧ p.v = q.v ∧ p.a = q.a ∧ p.b = q.b then
    .isTrue (PairLabel.ext' h.1 h.2.1 h.2.2.1 h.2.2.2)
  else
    .isFalse (fun heq => h ⟨heq ▸ rfl, heq ▸ rfl, heq ▸ rfl, heq ▸ rfl⟩)

/-
Consistent bad labels
-/
def IsConsistentBadLabel {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (p q : PairLabel I S) : Prop :=
  p.a * p.b = q.a * q.b ∧
  (p.u ≠ q.u ∨ p.v ≠ q.v ∨ p.a ≠ q.a ∨ p.b ≠ q.b) ∧
  (p.u = q.u → p.a = q.a) ∧ (p.u = q.v → p.a = q.b) ∧
  (p.v = q.u → p.b = q.a) ∧ (p.v = q.v → p.b = q.b)

instance {I : Finset ℕ} {S : ℕ → Finset ℕ} (p q : PairLabel I S) :
    Decidable (IsConsistentBadLabel p q) := by
  unfold IsConsistentBadLabel; infer_instance

def CBL (I : Finset ℕ) (S : ℕ → Finset ℕ) :=
  { pq : PairLabel I S × PairLabel I S // IsConsistentBadLabel pq.1 pq.2 }

instance (I : Finset ℕ) (S : ℕ → Finset ℕ) : Fintype (CBL I S) := by
  unfold CBL; infer_instance

instance (I : Finset ℕ) (S : ℕ → Finset ℕ) : DecidableEq (CBL I S) := by
  unfold CBL; infer_instance

/-
Support, value function, dependency graph
-/
def cblSupp {I : Finset ℕ} {S : ℕ → Finset ℕ} (j : CBL I S) : Finset ↥I :=
  {⟨j.val.1.u, j.val.1.hu⟩, ⟨j.val.1.v, j.val.1.hv⟩,
   ⟨j.val.2.u, j.val.2.hu⟩, ⟨j.val.2.v, j.val.2.hv⟩}

def cblVal {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hne : ∀ i ∈ I, (S i).Nonempty)
    (j : CBL I S) (i : ↥I) : ↥(S i.val) :=
  if h₁ : i.val = j.val.1.u then ⟨j.val.1.a, h₁ ▸ j.val.1.ha⟩
  else if h₂ : i.val = j.val.1.v then ⟨j.val.1.b, h₂ ▸ j.val.1.hb⟩
  else if h₃ : i.val = j.val.2.u then ⟨j.val.2.a, h₃ ▸ j.val.2.ha⟩
  else if h₄ : i.val = j.val.2.v then ⟨j.val.2.b, h₄ ▸ j.val.2.hb⟩
  else ⟨(S i.val).min' (hne i.val i.prop), (S i.val).min'_mem _⟩

def cblGraph (I : Finset ℕ) (S : ℕ → Finset ℕ) : SimpleGraph (CBL I S) where
  Adj j₁ j₂ := j₁ ≠ j₂ ∧ ¬Disjoint (cblSupp j₁) (cblSupp j₂)
  symm := fun {_j₁} {_j₂} h => ⟨h.1.symm, fun hd => h.2 (Disjoint.symm hd)⟩
  loopless := ⟨fun _j h => h.1 rfl⟩

instance (I : Finset ℕ) (S : ℕ → Finset ℕ) : DecidableRel (cblGraph I S).Adj := by
  intro j₁ j₂; unfold cblGraph SimpleGraph.Adj; infer_instance

lemma cblGraph_dep {I : Finset ℕ} {S : ℕ → Finset ℕ} :
    ∀ j₁ j₂ : CBL I S, j₁ ≠ j₂ → ¬(cblGraph I S).Adj j₁ j₂ →
    Disjoint (cblSupp j₁) (cblSupp j₂) := by
  intro j₁ j₂ hne hnadj; by_contra h; exact hnadj ⟨hne, h⟩

/-
For any coord in cblSupp, f agrees with cblVal when pair label values match f.
-/
lemma cblVal_matches_f {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hne : ∀ i ∈ I, (S i).Nonempty)
    {f : (i : ↑I) → ↑(S i.val)}
    (j : CBL I S) (coord : ↑I)
    (hmem : coord = ⟨j.val.1.u, j.val.1.hu⟩ ∨ coord = ⟨j.val.1.v, j.val.1.hv⟩ ∨
            coord = ⟨j.val.2.u, j.val.2.hu⟩ ∨ coord = ⟨j.val.2.v, j.val.2.hv⟩)
    (hfa : j.val.1.a = (f ⟨j.val.1.u, j.val.1.hu⟩).val)
    (hfb : j.val.1.b = (f ⟨j.val.1.v, j.val.1.hv⟩).val)
    (hfa2 : j.val.2.a = (f ⟨j.val.2.u, j.val.2.hu⟩).val)
    (hfb2 : j.val.2.b = (f ⟨j.val.2.v, j.val.2.hv⟩).val) :
    f coord = cblVal hne j coord := by
  rcases hmem with ( rfl | rfl | rfl | rfl ) <;> unfold cblVal <;> split_ifs <;> simp_all +decide only [Subtype.ext_iff];
  all_goals congr! 2;
  all_goals simp_all +decide

/-
The support of any consistent bad label has at least 3 elements, assuming
    elements are positive (0 ∉ S i) and S sets are pairwise disjoint.
-/
lemma cblSupp_card_ge_three {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (j : CBL I S) : 3 ≤ (cblSupp j).card := by
  rcases j with ⟨ ⟨ p, q ⟩, hpq ⟩;
  obtain ⟨ hp₁, hp₂ ⟩ := hpq;
  by_cases huv : p.u = p.v <;> by_cases huv' : q.u = q.v <;> simp_all +decide [ cblSupp ];
  · have := p.hdiag huv; have := q.hdiag huv'; simp_all +decide ;
    have := p.ha; have := q.ha; simp_all +decide [ Finset.disjoint_left ] ;
    by_cases h : p.v = q.v <;> simp_all +decide [ Finset.card_insert_of_notMem ];
    · grind +ring;
    · exact hS_disj _ _ p.hv q.hv h ( by simpa [ show p.b = q.b by nlinarith ] using ‹p.b ∈ S p.v› ) this;
  · by_cases h : p.v = q.u <;> by_cases h' : p.v = q.v <;> simp_all +decide [ Finset.card_insert_of_notMem ];
    · have := p.ha; have := p.hb; have := q.ha; have := q.hb; simp_all +decide [ Finset.disjoint_left ] ;
      cases hp₁ <;> simp_all +decide [ PairLabel.hdiag ];
      · exact hS_disj _ _ q.hv q.hu ( Ne.symm huv' ) this ‹_›;
      · exact hS_pos _ q.hu ‹_›;
    · have := hp₂.2.2.2.2 h'; simp_all +decide [ PairLabel.hdiag ] ;
      cases hp₁ <;> have := q.ha <;> have := q.hb <;> simp_all +decide [ Finset.disjoint_left ];
      · exact hS_disj _ _ q.hu q.hv ( by tauto ) ‹_› ‹_›;
      · exact hS_pos _ q.hv this;
  · by_cases h : p.u = q.v <;> simp_all +decide [ Finset.card_insert_of_notMem ];
    · have h_contra : p.b = q.a := by
        have := q.hdiag; simp_all +decide [ Finset.disjoint_left ] ;
        exact hp₁.resolve_right fun h => hS_pos _ q.hv <| h ▸ q.hb;
      have h_contra : q.a ∈ S p.v ∧ q.a ∈ S q.v := by
        exact ⟨ h_contra ▸ p.hb, by simpa [ huv' ] using q.ha ⟩;
      exact False.elim <| Finset.disjoint_left.mp ( hS_disj _ _ p.hv q.hv <| by tauto ) h_contra.1 h_contra.2;
    · rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide [ *, Subtype.ext_iff ];
      intro H; simp_all +decide [ Finset.disjoint_left ] ;
      have := p.hb; have := q.hb; simp_all +decide [ PairLabel.hdiag ] ;
      grind +suggestions;
  · by_cases huv'' : p.u = q.u <;> by_cases huv''' : p.u = q.v <;> by_cases huv'''' : p.v = q.u <;> by_cases huv''''' : p.v = q.v <;> simp_all +decide [ Finset.card_insert_of_notMem ];
    · grind;
    · have := p.huv; have := q.huv; simp_all +decide [ PairLabel.huv ] ;
      exact huv ( le_antisymm this ( by linarith [ q.huv ] ) )

/-
For valid CBLs with disjoint S and 0 ∉ S, no index appears in both pairs.
-/
lemma cbl_no_cross_index {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (k : CBL I S) :
    k.val.1.u ≠ k.val.2.u ∧ k.val.1.u ≠ k.val.2.v ∧
    k.val.1.v ≠ k.val.2.u ∧ k.val.1.v ≠ k.val.2.v := by
  refine' ⟨ _, _, _, _ ⟩ <;> intro h <;> have := k.2.1 <;> simp_all +decide [ IsConsistentBadLabel ];
  · have := k.2.2.2.1; simp_all +decide [ IsConsistentBadLabel ] ;
    cases ‹ ( k.val.1.b = k.val.2.b ∨ k.val.2.a = 0 ) › <;> have := k.2.2.1 <;> simp_all +decide [ IsConsistentBadLabel ];
    · have h_contradiction : (k.val.1.b ∈ S (k.val.1.v)) ∧ (k.val.1.b ∈ S (k.val.2.v)) := by
        exact ⟨ k.val.1.hb, by simpa [ * ] using k.val.2.hb ⟩;
      exact Finset.disjoint_left.mp ( hS_disj _ _ ( k.1.1.hv ) ( k.1.2.hv ) this ) h_contradiction.1 h_contradiction.2;
    · exact hS_pos _ k.val.1.hu ( by simpa [ * ] using k.val.1.ha );
  · -- By consistency, p.a = q.b.
    have h_consistent : (k.val.1.a : ℕ) = (k.val.2.b : ℕ) := by
      exact k.2.2.2.2.1 h;
    -- By consistency, p.b = q.a.
    have h_consistent2 : (k.val.1.b : ℕ) = (k.val.2.a : ℕ) := by
      have h_consistent2 : (k.val.1.a : ℕ) * (k.val.1.b : ℕ) = (k.val.2.a : ℕ) * (k.val.1.a : ℕ) := by
        aesop;
      exact mul_left_cancel₀ ( show ( k.val.1.a : ℕ ) ≠ 0 from fun h => hS_pos _ k.val.1.hu <| by simpa [ h ] using k.val.1.ha ) <| by linarith;
    have h_eq : (k.val.1.u : ℕ) = (k.val.2.v : ℕ) ∧ (k.val.1.v : ℕ) = (k.val.2.u : ℕ) := by
      have h_eq : (k.val.1.b : ℕ) ∈ S (k.val.1.v) ∧ (k.val.1.b : ℕ) ∈ S (k.val.2.u) := by
        exact ⟨ k.val.1.hb, h_consistent2.symm ▸ k.val.2.ha ⟩;
      contrapose! hS_disj;
      exact ⟨ _, _, k.val.1.hv, k.val.2.hu, hS_disj h, Finset.not_disjoint_iff.mpr ⟨ _, h_eq.1, h_eq.2 ⟩ ⟩;
    have := k.val.1.huv; have := k.val.2.huv; simp_all +decide ;
    have := k.2.2; simp_all +decide [ IsConsistentBadLabel ] ;
    grind;
  · have h_eq : k.val.1.b = k.val.2.a := by
      exact k.2.2.2.2.2.1 h;
    have h_eq : k.val.1.a = k.val.2.b := by
      by_cases h : k.val.2.a = 0 <;> simp_all +decide [ mul_comm ];
      · exact False.elim <| hS_pos _ k.val.1.hv <| h_eq ▸ k.val.1.hb;
      · exact mul_left_cancel₀ h <| by linarith;
    have h_eq : k.val.1.u = k.val.2.v := by
      have h_eq : (k.val.1.a ∈ S k.val.1.u) ∧ (k.val.1.a ∈ S k.val.2.v) := by
        exact ⟨ k.1.1.ha, h_eq.symm ▸ k.1.2.hb ⟩;
      exact Classical.not_not.1 fun h => Finset.disjoint_left.mp ( hS_disj _ _ ( k.val.1.hu ) ( k.val.2.hv ) h ) h_eq.1 h_eq.2;
    have h_eq : k.val.1.u = k.val.1.v := by
      linarith [ k.1.1.huv, k.1.2.huv ];
    grind;
  · -- Since $p.v = q.v$, we have $p.b = q.b$ by the consistency condition.
    have hpb_eq_qb : k.val.1.b = k.val.2.b := by
      grind +revert;
    have hpa_eq_qa : k.val.1.a = k.val.2.a := by
      by_cases h : ( k.val.1.b : ℕ ) = 0 <;> simp_all +decide
      exact False.elim <| hS_pos _ k.val.2.hv <| hpb_eq_qb ▸ k.val.2.hb;
    have := k.2.2.1; simp_all +decide [ IsConsistentBadLabel ] ;
    have := k.1.1.ha; have := k.1.2.ha; simp_all +decide [ Finset.disjoint_left ] ;
    exact hS_disj _ _ ( k.1.1.hu ) ( k.1.2.hu ) ( by aesop ) ‹_› ‹_›

lemma local_mass_numerical {n : ℕ} {eta : ℝ} (hn : 0 < n)
    (h768 : (768 : ℝ) ≤ (n : ℝ) ^ eta) :
    12 * (n : ℝ) ^ (-eta) ≤ 1 / 16 := by
  rw [ Real.rpow_neg ( by positivity ) ] ; nlinarith [ mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ^ eta ≠ 0 ) ] ;

/-
Arithmetic step: 12*|I|*n^(η-2α) ≤ 12*n^(-η).
-/
lemma local_mass_arith {n : ℕ} {alpha beta eta : ℝ} {I : Finset ℕ}
    (hn : 0 < n) (heta_def : eta = (2 * alpha - beta) / 2)
    (hcard : (↑I.card : ℝ) ≤ (n : ℝ) ^ beta) :
    12 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) ≤
    12 * (n : ℝ) ^ (-eta) := by
  exact le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hcard ( by positivity ) ) ( by positivity ) ) ( by rw [ mul_assoc, ← Real.rpow_add ( by positivity ) ] ; rw [ heta_def ] ; ring_nf; norm_num )

/-
For CBLs with the same p-part and same q.a, they are equal.
-/
lemma cbl_qa_inj {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (k₁ k₂ : CBL I S)
    (hpu : k₁.val.1 = k₂.val.1)
    (hqa : k₁.val.2.a = k₂.val.2.a) :
    k₁ = k₂ := by
  -- Since k₁.val.1 = k₂.val.1, we have p₁ = p₂ (same p-part). So p₁.a * p₁.b = p₂.a * p₂.b.
  have hp_eq : k₁.val.2.a * k₁.val.2.b = k₂.val.2.a * k₂.val.2.b := by
    have := k₁.2.1; have := k₂.2.1; aesop;
  have hq_eq : k₁.val.2.b = k₂.val.2.b := by
    have hq_eq : k₁.val.2.a ≠ 0 := by
      exact fun h => hS_pos _ k₁.val.2.hu <| h ▸ k₁.val.2.ha;
    aesop;
  have hq_u_eq : k₁.val.2.u = k₂.val.2.u := by
    have hq_u_eq : k₁.val.2.a ∈ S k₁.val.2.u ∧ k₂.val.2.a ∈ S k₂.val.2.u := by
      exact ⟨ k₁.1.2.ha, k₂.1.2.ha ⟩;
    grind +suggestions
  have hq_v_eq : k₁.val.2.v = k₂.val.2.v := by
    contrapose! hq_eq;
    exact fun h => Finset.disjoint_left.mp ( hS_disj _ _ k₁.val.2.hv k₂.val.2.hv hq_eq ) ( h ▸ k₁.val.2.hb ) k₂.val.2.hb;
  exact Subtype.ext <| Prod.ext hpu <| PairLabel.ext' hq_u_eq hq_v_eq hqa hq_eq

/-
The number of CBLs with a given p-part is at most τ(p.a * p.b).
-/
lemma cbl_fiber_card_le_tau {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (p : PairLabel I S) :
    (Finset.univ.filter (fun k : CBL I S => k.val.1 = p)).card ≤
    (p.a * p.b).divisors.card := by
  refine' le_trans _ ( Finset.card_le_card _ );
  any_goals exact Finset.image ( fun k : CBL I S => k.val.2.a ) ( Finset.filter ( fun k : CBL I S => k.val.1 = p ) Finset.univ );
  · rw [ Finset.card_image_of_injOn ];
    intro k hk l hl hkl; have := cbl_qa_inj hS_disj hS_pos k l; aesop;
  · intro; simp +decide [ IsConsistentBadLabel ] ;
    rintro ⟨ k₁, k₂ ⟩ hk₁ hk₂; have := k₂.2.1; simp_all +decide ;
    have := k₂.1; simp_all +decide [ IsConsistentBadLabel ] ;
    exact ⟨ fun h => hS_pos _ p.hu <| by simpa [ h ] using p.ha, fun h => hS_pos _ p.hv <| by simpa [ h ] using p.hb ⟩

/-
The product over cblSupp is at most the product over the p-part times n^{-2α},
    when q is non-diagonal (q.u ≠ q.v).
-/
lemma cbl_product_bound_qnondiag {n : ℕ} {alpha : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n)
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (k : CBL I S) (hq : k.val.2.u ≠ k.val.2.v) :
    ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ ≤
    (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I),
      ((S i.val).card : ℝ)⁻¹) * (n : ℝ) ^ (-(2 * alpha)) := by
  obtain ⟨k₁, k₂⟩ := k;
  -- By cbl_no_cross_index, all four indices are distinct.
  have h_distinct : k₁.1.u ≠ k₁.2.u ∧ k₁.1.u ≠ k₁.2.v ∧ k₁.1.v ≠ k₁.2.u ∧ k₁.1.v ≠ k₁.2.v := by
    apply cbl_no_cross_index hS_disj hS_pos ⟨k₁, k₂⟩;
  rw [ show cblSupp ⟨ k₁, k₂ ⟩ = { ⟨ k₁.1.u, k₁.1.hu ⟩, ⟨ k₁.1.v, k₁.1.hv ⟩ } ∪ { ⟨ k₁.2.u, k₁.2.hu ⟩, ⟨ k₁.2.v, k₁.2.hv ⟩ } from ?_, Finset.prod_union ];
  · refine' mul_le_mul_of_nonneg_left _ ( Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ );
    rw [ Finset.prod_pair ] <;> norm_num [ Real.rpow_neg, hn.ne' ];
    · rw [ ← mul_inv, two_mul, Real.rpow_add ( by positivity ) ];
      exact inv_anti₀ ( by positivity ) ( mul_le_mul ( hS_size _ k₁.2.hu ) ( hS_size _ k₁.2.hv ) ( by positivity ) ( by positivity ) );
    · tauto;
  · simp +decide [ *, Finset.disjoint_left ];
  · grind +locals

/-
Sum of pair label p-products for p with p.u = t is at most |I|+1.
    For non-diagonal p: \sum |S_t|^{-1} |S_v|^{-1} = \sum_v |S_t| |S_v| / (|S_t| |S_v|) = \sum_v 1.
    For diagonal p: \sum |S_t|^{-1} = |S_t|/|S_t| = 1.
-/
lemma pair_label_ppart_sum {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (t : ℕ) (ht : t ∈ I) :
    ∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.u = t),
      ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹ ≤
    (I.card : ℝ) + 1 := by
  -- Split the sum into diagonal and non-diagonal parts.
  have h_split : ∑ p ∈ Finset.filter (fun p => p.u = t) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) =
                 ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.u = p.v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) +
                 ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.u ≠ p.v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) := by
                   rw [ ← Finset.sum_union ] ; congr ; ext ; by_cases h : ‹PairLabel I S›.u = ‹PairLabel I S›.v <;> aesop;
                   exact Finset.disjoint_filter.mpr ( by aesop );
  -- The sum over non-diagonal p is at most |I|.
  have h_non_diag : ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.u ≠ p.v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ (I.card : ℝ) := by
    -- For each non-diagonal pair (t, v), the sum over a and b is (S t).card * (S v).card * (S t).card⁻¹ * (S v).card⁻¹ = 1.
    have h_non_diag_pair : ∀ v ∈ I, v ≠ t → ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.v = v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ 1 := by
      intro v hv hv_ne_t
      have h_card : Finset.card (Finset.filter (fun p => p.u = t ∧ p.v = v) (Finset.univ : Finset (PairLabel I S))) ≤ (S t).card * (S v).card := by
        have h_card : Finset.card (Finset.filter (fun p => p.u = t ∧ p.v = v) (Finset.univ : Finset (PairLabel I S))) ≤ Finset.card (Finset.image (fun p => (p.a, p.b)) (Finset.filter (fun p => p.u = t ∧ p.v = v) (Finset.univ : Finset (PairLabel I S)))) := by
          rw [ Finset.card_image_of_injOn ];
          intro p hp q hq; aesop;
        refine le_trans h_card ?_;
        refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
        exact Finset.product ( S t ) ( S v );
        · simp +contextual [ Finset.mem_product ];
          exact fun p hp₁ hp₂ => ⟨ hp₁ ▸ p.ha, hp₂ ▸ p.hb ⟩;
        · erw [ Finset.card_product ];
      refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) _;
      use fun p => ( ( S t |> Finset.card : ℝ ) ⁻¹ * ( S v |> Finset.card : ℝ ) ⁻¹ );
      · grind;
      · simp +zetaDelta at *;
        rw [ ← mul_inv, mul_comm ];
        rw [ inv_mul_le_iff₀ ] <;> norm_cast <;> nlinarith [ Finset.card_pos.mpr ( hS_ne t ht ), Finset.card_pos.mpr ( hS_ne v hv ) ];
    have h_non_diag_sum : ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.u ≠ p.v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ ∑ v ∈ I.erase t, ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.v = v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) := by
      rw [ ← Finset.sum_biUnion ];
      · refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
        · simp +contextual [ Finset.subset_iff ];
          exact fun p hp₁ hp₂ => ⟨ Ne.symm hp₂, p.hv ⟩;
        · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
    exact h_non_diag_sum.trans ( le_trans ( Finset.sum_le_sum fun x hx => h_non_diag_pair x ( Finset.mem_of_mem_erase hx ) ( Finset.ne_of_mem_erase hx ) ) ( by norm_num [ Finset.card_erase_of_mem ht ] ) );
  -- The sum over diagonal p is at most 1.
  have h_diag : ∑ p ∈ Finset.filter (fun p => p.u = t ∧ p.u = p.v) (Finset.univ : Finset (PairLabel I S)), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ 1 := by
    rw [ show ( Finset.filter ( fun p : PairLabel I S => p.u = t ∧ p.u = p.v ) Finset.univ ) = Finset.image ( fun a : { a : ℕ // a ∈ S t } => ⟨ t, t, a.val, a.val, ht, ht, le_rfl, a.2, a.2, by aesop ⟩ ) ( Finset.univ : Finset { a : ℕ // a ∈ S t } ) from ?_ ];
    · rw [ Finset.sum_image ] <;> norm_num;
      · exact div_self_le_one _;
      · intro a b; aesop;
    · ext ⟨u, v, a, b, hu, hv, huv, ha, hb, hdiag⟩; simp;
      lia;
  grind +splitImp

/-
Variant of pair_label_ppart_sum for p.v = t.
-/
lemma pair_label_ppart_sum_v {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (t : ℕ) (ht : t ∈ I) :
    ∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t),
      ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹ ≤
    (I.card : ℝ) + 1 := by
  -- We'll use the fact that the sum can be split into two parts: one where $p.u = t$ and one where $p.u \neq t$.
  have h_split : (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t), ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤
                (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u = t), ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) +
                (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u ≠ t), ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) := by
                  rw [ ← Finset.sum_union ] ; exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by by_cases hx' : x.u = t <;> aesop ) fun _ _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.mpr <| Nat.cast_nonneg _;
                  exact Finset.disjoint_filter.mpr ( by aesop );
  -- The diagonal part (p.u = t) contributes at most 1.
  have h_diag : (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u = t), ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ 1 := by
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) _;
    exact Finset.biUnion ( Finset.filter ( fun x => x ∈ S t ) ( S t ) ) fun x => Finset.filter ( fun p : PairLabel I S => p.u = t ∧ p.v = t ∧ p.a = x ∧ p.b = x ) Finset.univ;
    · simp +contextual [ Finset.subset_iff ];
      exact fun p hp₁ hp₂ => ⟨ by simpa [ hp₁ ] using p.hb, by simpa [ hp₁, hp₂ ] using p.hdiag ( by simp [ hp₁, hp₂ ] ) ⟩;
    · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
    · rw [ Finset.sum_biUnion ];
      · refine' le_trans ( Finset.sum_le_sum fun x hx => _ ) _;
        use fun x => ( 1 : ℝ ) / ( S t |> Finset.card );
        · rw [ Finset.sum_eq_single ⟨ t, t, x, x, ht, ht, by linarith, by aesop, by aesop, by aesop ⟩ ] <;> simp +decide [ Finset.prod_singleton ];
          exact fun p hp₁ hp₂ hp₃ hp₄ hp₅ => False.elim <| hp₅ <| by cases p; aesop;
        · norm_num [ Finset.filter_true_of_mem ];
          exact div_self_le_one _;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
  -- The non-diagonal part (p.u ≠ t) contributes at most |I| - 1.
  have h_non_diag : (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u ≠ t), ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ (I.card - 1 : ℝ) := by
    -- For each $u \in I \setminus \{t\}$, the sum over $p$ with $p.v = t$ and $p.u = u$ is at most 1.
    have h_non_diag_u : ∀ u ∈ I \ {t}, (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u = u), ∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) ≤ 1 := by
      intros u hu
      have h_pair_count : (Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u = u)).card ≤ (S u).card * (S t).card := by
        have h_pair_count : (Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u = u)).card ≤ (Finset.image (fun p : ℕ × ℕ => (p.1, p.2)) (S u ×ˢ S t)).card := by
          have h_pair_count : Finset.image (fun p : PairLabel I S => (p.a, p.b)) (Finset.univ.filter (fun p : PairLabel I S => p.v = t ∧ p.u = u)) ⊆ Finset.image (fun p : ℕ × ℕ => (p.1, p.2)) (S u ×ˢ S t) := by
            simp +decide [ Finset.subset_iff ];
            rintro a b x hx₁ hx₂ rfl rfl; exact ⟨ by simpa [ hx₂ ] using x.ha, by simpa [ hx₁ ] using x.hb ⟩ ;
          convert Finset.card_le_card h_pair_count using 1;
          rw [ Finset.card_image_of_injOn ];
          intro p hp q hq; aesop;
        exact h_pair_count.trans ( Finset.card_image_le.trans ( by rw [ Finset.card_product ] ) );
      refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) _;
      use fun p => ( ( S u |> Finset.card : ℝ ) ⁻¹ * ( S t |> Finset.card : ℝ ) ⁻¹ );
      · grind +revert;
      · simp +zetaDelta at *;
        rw [ ← mul_inv, mul_comm ];
        rw [ inv_mul_le_iff₀ ] <;> norm_cast <;> nlinarith [ Finset.card_pos.mpr ( hS_ne u hu.1 ), Finset.card_pos.mpr ( hS_ne t ht ) ];
    convert Finset.sum_le_sum h_non_diag_u using 1;
    · rw [ ← Finset.sum_biUnion ];
      · refine' Finset.sum_bij ( fun p hp => p ) _ _ _ _ <;> simp +contextual [ Finset.mem_biUnion ];
        exact fun p hp₁ hp₂ => p.hu;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
    · simp +decide [ Finset.card_sdiff, * ];
      rw [ Nat.cast_pred ( Finset.card_pos.mpr ⟨ t, ht ⟩ ) ];
  linarith

/-
For each CBL with q non-diagonal, the product ≤ n^{-3α}.
-/
lemma cbl_q_nondiag_sum {n : ℕ} {alpha eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n) (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k ∈ Finset.univ.filter (fun k : CBL I S =>
        (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u ≠ k.val.2.v),
      ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ ≤
    ((I.card : ℝ) + 1) * (n : ℝ) ^ (eta - 2 * alpha) := by
  refine' le_trans ( Finset.sum_le_sum fun x hx => cbl_product_bound_qnondiag hn hS_size hS_disj hS_pos _ _ ) _;
  · grind;
  · have h_sum : (∑ k : CBL I S, (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if ⟨k.val.1.u, k.val.1.hu⟩ = t ∧ k.val.2.u ≠ k.val.2.v then 1 else 0)) ≤ (I.card + 1) * (n : ℝ) ^ eta := by
      have h_sum : (∑ k : CBL I S, (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if ⟨k.val.1.u, k.val.1.hu⟩ = t ∧ k.val.2.u ≠ k.val.2.v then 1 else 0)) ≤ (∑ p : PairLabel I S, ((p.a * p.b).divisors.card : ℝ) * (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if p.u = t.val then 1 else 0)) := by
        have h_sum : (∑ k : CBL I S, (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if ⟨k.val.1.u, k.val.1.hu⟩ = t ∧ k.val.2.u ≠ k.val.2.v then 1 else 0)) ≤ (∑ p : PairLabel I S, (∑ k ∈ Finset.univ.filter (fun k : CBL I S => k.val.1 = p), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if p.u = t.val ∧ k.val.2.u ≠ k.val.2.v then 1 else 0))) := by
          simp +decide only [sum_filter];
          rw [ Finset.sum_comm ];
          refine' Finset.sum_le_sum fun x _ => _;
          rw [ Finset.sum_eq_single ( x.val.1 ) ] <;> aesop;
        refine le_trans h_sum ?_;
        refine Finset.sum_le_sum fun p hp => ?_;
        split_ifs <;> simp_all +decide [ Finset.sum_ite ];
        gcongr;
        refine' le_trans _ ( cbl_fiber_card_le_tau hS_disj hS_pos p );
        exact Finset.card_filter_le _ _;
      refine le_trans h_sum ?_;
      have h_sum : (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.u = t.val), ((p.a * p.b).divisors.card : ℝ) * (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹)) ≤ (I.card + 1) * (n : ℝ) ^ eta := by
        refine' le_trans ( Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ( show ( # ( p.a * p.b |> Nat.divisors ) : ℝ ) ≤ n ^ eta from _ ) <| Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) _;
        · refine' le_of_lt ( hdiv _ _ _ );
          · exact mul_pos ( Nat.pos_of_ne_zero fun h => hS_pos _ p.hu <| by simpa [ h ] using p.ha ) ( Nat.pos_of_ne_zero fun h => hS_pos _ p.hv <| by simpa [ h ] using p.hb );
          · norm_cast;
            exact le_trans ( Nat.mul_le_mul ( Finset.mem_range_succ_iff.mp ( hS_sub _ p.hu p.ha ) ) ( Finset.mem_range_succ_iff.mp ( hS_sub _ p.hv p.hb ) ) ) ( by nlinarith );
        · have := pair_label_ppart_sum hS_ne t.val t.prop;
          rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn ) eta ];
      simpa [ Finset.sum_ite ] using h_sum;
    convert mul_le_mul_of_nonneg_right h_sum ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( - ( 2 * alpha ) ) ) using 1 <;> norm_num [ Real.rpow_sub ( Nat.cast_pos.mpr hn ) ] ; ring_nf;
    · rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.sum_filter ] ; congr ; ext ; ring_nf;
      split_ifs <;> ring;
    · rw [ Real.rpow_neg ( by positivity ), div_eq_mul_inv ] ; ring

/-
When q is diagonal and p.u = t, p must be non-diagonal, so ∏_{pPart} ≤ n^{-2α}.
    Combined with the q-part = |S_{q.u}|^{-1}, this gives
    ∏_{cblSupp} ≤ n^{-2α} · |S_{q.u}|^{-1}.
-/
lemma cbl_product_bound_qdiag_explicit {n : ℕ} {alpha : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n)
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (k : CBL I S) (hq : k.val.2.u = k.val.2.v) :
    ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ ≤
    (n : ℝ) ^ (-(2 * alpha)) * ((S (k.val.2.u)).card : ℝ)⁻¹ := by
  refine' le_trans _ ( mul_le_mul_of_nonneg_right _ <| inv_nonneg.mpr <| Nat.cast_nonneg _ );
  rotate_left;
  exact ( ∏ i ∈ ( { ⟨ k.val.1.u, k.val.1.hu ⟩, ⟨ k.val.1.v, k.val.1.hv ⟩ } : Finset I ), ( ( S i.val ).card : ℝ ) ⁻¹ );
  · by_cases h : k.val.1.u = k.val.1.v <;> simp_all +decide [ Real.rpow_neg ];
    · exact absurd ( cblSupp_card_ge_three hS_disj hS_pos k ) ( by
        unfold cblSupp; simp +decide [ h, hq ] ;
        exact lt_of_le_of_lt ( Finset.card_insert_le _ _ ) ( by norm_num ) );
    · rw [ mul_comm, ← mul_inv ];
      gcongr;
      convert mul_le_mul ( hS_size _ _ ) ( hS_size _ _ ) ( by positivity ) ( by positivity ) using 1 ; rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf;
      · exact k.1.1.hu;
      · exact k.1.1.hv;
  · rw [ show cblSupp k = { ⟨ k.val.1.u, k.val.1.hu ⟩, ⟨ k.val.1.v, k.val.1.hv ⟩ } ∪ { ⟨ k.val.2.u, k.val.2.hu ⟩ } from ?_ ];
    · rw [ Finset.prod_union ] <;> norm_num [ hq ];
      exact ⟨ by have := cbl_no_cross_index hS_disj hS_pos k; aesop, by have := cbl_no_cross_index hS_disj hS_pos k; aesop ⟩;
    · ext; simp [cblSupp];
      grind

/-
Count of CBLs with p.u = t, q.u = q.v = w, and q.a = c is at most τ(c²).
-/
lemma cbl_qdiag_fiber_count {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) (w : ℕ) (hw : w ∈ I) (c : ℕ) (hc : c ∈ S w) :
    (Finset.univ.filter (fun k : CBL I S =>
      (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧
      k.val.2.u = w ∧ k.val.2.v = w ∧
      k.val.2.a = c)).card ≤
    (c * c).divisors.card := by
  have h_fib_card : Finset.card (Finset.image (fun k : CBL I S => k.val.1.a) (Finset.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w ∧ k.val.2.a = c) Finset.univ)) ≤ (c * c).divisors.card := by
    refine Finset.card_le_card ?_;
    intro x hx;
    simp +zetaDelta at *;
    rcases hx with ⟨ a, ⟨ rfl, hu, hv, ha ⟩, rfl ⟩ ; have := a.2.1 ; simp_all +decide [ IsConsistentBadLabel ] ;
    have := a.2.2; simp_all +decide [ PairLabel.hdiag ] ;
    exact ⟨ ‹ ( a.val.1.a : ℕ ) * ( a.val.1.b : ℕ ) = c * c › ▸ dvd_mul_right _ _, by specialize hS_pos w hw; aesop ⟩;
  rwa [ Finset.card_image_of_injOn ] at h_fib_card;
  intros k₁ hk₁ k₂ hk₂ h_eq;
  apply cbl_qa_inj hS_disj hS_pos;
  · have h_eq_b : k₁.val.1.b = k₂.val.1.b := by
      have h_eq_b : k₁.val.1.a * k₁.val.1.b = c * c ∧ k₂.val.1.a * k₂.val.1.b = c * c := by
        have := k₁.2.1; have := k₂.2.1; simp_all +decide [ PairLabel.hdiag ] ;
        have := k₁.1.2.hdiag; have := k₂.1.2.hdiag; aesop;
      by_cases hc : c = 0 <;> simp_all +decide ;
      exact mul_left_cancel₀ ( show ( k₂.val.1.a : ℕ ) ≠ 0 from fun h => by have := k₂.val.1.ha; aesop ) ( by linarith );
    apply PairLabel.ext';
    · grind;
    · have h_eq_v : k₁.val.1.b ∈ S k₁.val.1.v ∧ k₂.val.1.b ∈ S k₂.val.1.v := by
        exact ⟨ k₁.1.1.hb, k₂.1.1.hb ⟩;
      exact Classical.not_not.1 fun h => Finset.disjoint_left.mp ( hS_disj _ _ ( k₁.val.1.hv ) ( k₂.val.1.hv ) h ) h_eq_v.1 ( h_eq_b ▸ h_eq_v.2 );
    · exact h_eq;
    · exact h_eq_b;
  · grind

/-
For each CBL with q diagonal (q.u = q.v), the product has 3 factors.
    By reorganizing the sum (summing over (w,c) where c = q.a ∈ S_w first),
    we get a bound of |I| * n^{η-2α}.
-/
lemma cbl_q_diag_sum {n : ℕ} {alpha eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k ∈ Finset.univ.filter (fun k : CBL I S =>
        (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = k.val.2.v),
      ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ ≤
    (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) := by
  -- Apply the bound from cbl_product_bound_qdiag_explicit to each term in the sum.
  have h_term_bound : ∀ k : CBL I S, k.val.2.u = k.val.2.v → ∏ i ∈ cblSupp k, (1 / (S i.val).card : ℝ) ≤ (n : ℝ) ^ (-(2 * alpha)) * (1 / (S (k.val.2.u)).card : ℝ) := by
    intro k hk; have := cbl_product_bound_qdiag_explicit hn hS_size hS_disj hS_pos k hk; aesop;
  -- By grouping terms by (w,c) where c = q.a ∈ S_w, we can bound the sum.
  have h_group_bound :
    ∑ k ∈ Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = k.val.2.v), (1 / (S (k.val.2.u)).card : ℝ) ≤ (I.card : ℝ) * (n : ℝ) ^ eta := by
      have h_group_bound :
        ∀ w ∈ I, ∑ k ∈ Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w), (1 / (S w).card : ℝ) ≤ (n : ℝ) ^ eta := by
          intros w hw
          have h_card_bound : (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w)).card ≤ (S w).card * (n : ℝ) ^ eta := by
            have h_card_bound : (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w)).card ≤ ∑ c ∈ S w, (c * c).divisors.card := by
              have h_card_bound : ∀ c ∈ S w, (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w ∧ k.val.2.a = c)).card ≤ (c * c).divisors.card := by
                intros c hc
                apply cbl_qdiag_fiber_count hS_disj hS_pos t w hw c hc;
              refine' le_trans _ ( Finset.sum_le_sum h_card_bound );
              rw [ ← Finset.card_biUnion ];
              · refine' Finset.card_le_card _;
                simp +contextual [ Finset.subset_iff ];
                exact fun k hk₁ hk₂ hk₃ => hk₂ ▸ k.1.2.ha;
              · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun k hkx hky => hxy <| by aesop;
            refine' le_trans ( Nat.cast_le.mpr h_card_bound ) _;
            push_cast;
            refine' le_trans ( Finset.sum_le_sum fun x hx => le_of_lt ( hdiv _ _ _ ) ) _;
            · exact Nat.mul_pos ( Nat.pos_of_ne_zero fun h => hS_pos w hw <| h ▸ hx ) ( Nat.pos_of_ne_zero fun h => hS_pos w hw <| h ▸ hx );
            · norm_cast ; nlinarith [ Finset.mem_range.mp ( hS_sub w hw hx ) ];
            · norm_num;
          simp +zetaDelta at *;
          rwa [ ← div_eq_mul_inv, div_le_iff₀' ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| hS_ne w hw ) ];
      have h_group_bound : ∑ w ∈ I, ∑ k ∈ Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w), (1 / (S w).card : ℝ) ≤ (I.card : ℝ) * (n : ℝ) ^ eta := by
        exact le_trans ( Finset.sum_le_sum h_group_bound ) ( by norm_num );
      convert h_group_bound using 1;
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun k hk => ⟨ k.val.2.u, k ⟩ ) _ _ _ _ <;> simp +decide;
      · exact fun k hk₁ hk₂ => ⟨ k.val.2.hu, hk₁, hk₂.symm ⟩;
      · grind;
  refine' le_trans ( Finset.sum_le_sum fun x hx => by simpa using h_term_bound x <| by aesop ) _;
  convert mul_le_mul_of_nonneg_left h_group_bound ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( - ( 2 * alpha ) ) ) using 1 <;> norm_num [ Real.rpow_sub ( Nat.cast_pos.mpr hn ) ] ; ring_nf;
  · rw [ Finset.mul_sum _ _ _ ];
  · rw [ Real.rpow_neg ( by positivity ) ] ; ring

/-
Per-position bound: ∑_{k : ⟨p.u⟩ = t} w(k) ≤ 3|I| n^{η-2α}.
-/
lemma cbl_mass_per_position {n : ℕ} {alpha eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n) (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k : CBL I S, (if (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t then
      (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ)) ≤
    3 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) := by
  rw [ Finset.sum_ite ];
  refine' le_trans ( add_le_add ( show ∑ x ∈ Finset.filter ( fun x : CBL I S => ( ⟨ x.val.1.u, x.val.1.hu ⟩ : I ) = t ) Finset.univ, ∏ i ∈ cblSupp x, ( ↑ ( # ( S ↑i ) ) : ℝ ) ⁻¹ ≤ ( I.card + 1 ) * n ^ ( eta - 2 * alpha ) + I.card * n ^ ( eta - 2 * alpha ) from _ ) le_rfl ) _;
  · refine' le_trans _ ( add_le_add ( cbl_q_nondiag_sum hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t ) ( cbl_q_diag_sum hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t ) );
    rw [ ← Finset.sum_union ];
    · exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by by_cases h : x.val.2.u = x.val.2.v <;> aesop ) fun _ _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
    · exact Finset.disjoint_filter.mpr ( by aesop );
  · norm_num ; nlinarith [ show ( 1 :ℝ ) ≤ I.card from mod_cast Finset.card_pos.mpr ⟨ t, t.2 ⟩, Real.rpow_pos_of_pos ( show 0 < ( n :ℝ ) by positivity ) ( eta - 2 * alpha ) ] ;

/-
IsConsistentBadLabel is symmetric: swapping p and q preserves consistency.
-/
lemma IsConsistentBadLabel.symm {I : Finset ℕ} {S : ℕ → Finset ℕ}
    {p q : PairLabel I S} (h : IsConsistentBadLabel p q) :
    IsConsistentBadLabel q p := by
  constructor <;> simp_all +decide [ IsConsistentBadLabel ];
  grind

/-- Swap p and q in a CBL. -/
def cblSwap {I : Finset ℕ} {S : ℕ → Finset ℕ} (k : CBL I S) : CBL I S :=
  ⟨(k.val.2, k.val.1), k.prop.symm⟩

/-
cblSwap is an involution.
-/
lemma cblSwap_involutive {I : Finset ℕ} {S : ℕ → Finset ℕ} :
    Function.Involutive (cblSwap (I := I) (S := S)) := by
  intro k; exact Subtype.ext ( by exact Prod.ext ( by tauto ) ( by tauto ) ) ;

/-- Variant of cbl_q_nondiag_sum for p.v = t. -/
lemma cbl_q_nondiag_sum_pv {n : ℕ} {alpha eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n) (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k ∈ Finset.univ.filter (fun k : CBL I S =>
        (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u ≠ k.val.2.v),
      ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ ≤
    ((I.card : ℝ) + 1) * (n : ℝ) ^ (eta - 2 * alpha) := by
  refine' le_trans ( Finset.sum_le_sum fun x hx => cbl_product_bound_qnondiag hn hS_size hS_disj hS_pos _ _ ) _;
  · grind;
  · have h_sum : (∑ k : CBL I S, (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if ⟨k.val.1.v, k.val.1.hv⟩ = t ∧ k.val.2.u ≠ k.val.2.v then 1 else 0)) ≤ (I.card + 1) * (n : ℝ) ^ eta := by
      have h_sum : (∑ k : CBL I S, (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if ⟨k.val.1.v, k.val.1.hv⟩ = t ∧ k.val.2.u ≠ k.val.2.v then 1 else 0)) ≤ (∑ p : PairLabel I S, ((p.a * p.b).divisors.card : ℝ) * (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if p.v = t.val then 1 else 0)) := by
        have h_sum : (∑ k : CBL I S, (∏ i ∈ ({⟨k.val.1.u, k.val.1.hu⟩, ⟨k.val.1.v, k.val.1.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if ⟨k.val.1.v, k.val.1.hv⟩ = t ∧ k.val.2.u ≠ k.val.2.v then 1 else 0)) ≤ (∑ p : PairLabel I S, (∑ k ∈ Finset.univ.filter (fun k : CBL I S => k.val.1 = p), (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹) * (if p.v = t.val ∧ k.val.2.u ≠ k.val.2.v then 1 else 0))) := by
          simp +decide only [sum_filter];
          rw [ Finset.sum_comm ];
          refine' Finset.sum_le_sum fun x _ => _;
          rw [ Finset.sum_eq_single ( x.val.1 ) ] <;> aesop;
        refine le_trans h_sum ?_;
        refine Finset.sum_le_sum fun p hp => ?_;
        split_ifs <;> simp_all +decide [ Finset.sum_ite ];
        gcongr;
        refine' le_trans _ ( cbl_fiber_card_le_tau hS_disj hS_pos p );
        exact Finset.card_filter_le _ _;
      refine le_trans h_sum ?_;
      have h_sum : (∑ p ∈ Finset.univ.filter (fun p : PairLabel I S => p.v = t.val), ((p.a * p.b).divisors.card : ℝ) * (∏ i ∈ ({⟨p.u, p.hu⟩, ⟨p.v, p.hv⟩} : Finset ↥I), ((S i.val).card : ℝ)⁻¹)) ≤ (I.card + 1) * (n : ℝ) ^ eta := by
        refine' le_trans ( Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ( show ( # ( p.a * p.b |> Nat.divisors ) : ℝ ) ≤ n ^ eta from _ ) <| Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) _;
        · refine' le_of_lt ( hdiv _ _ _ );
          · exact mul_pos ( Nat.pos_of_ne_zero fun h => hS_pos _ p.hu <| by simpa [ h ] using p.ha ) ( Nat.pos_of_ne_zero fun h => hS_pos _ p.hv <| by simpa [ h ] using p.hb );
          · norm_cast;
            exact le_trans ( Nat.mul_le_mul ( Finset.mem_range_succ_iff.mp ( hS_sub _ p.hu p.ha ) ) ( Finset.mem_range_succ_iff.mp ( hS_sub _ p.hv p.hb ) ) ) ( by nlinarith );
        · have := pair_label_ppart_sum_v hS_ne t.val t.prop;
          rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn ) eta ];
      simpa [ Finset.sum_ite ] using h_sum;
    convert mul_le_mul_of_nonneg_right h_sum ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( - ( 2 * alpha ) ) ) using 1 <;> norm_num [ Real.rpow_sub ( Nat.cast_pos.mpr hn ) ] ; ring_nf;
    · rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.sum_filter ] ; congr ; ext ; ring_nf;
      split_ifs <;> ring;
    · rw [ Real.rpow_neg ( by positivity ), div_eq_mul_inv ] ; ring

/-
Fiber count for p.v = t variant.
-/
lemma cbl_qdiag_fiber_count_pv {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) (w : ℕ) (hw : w ∈ I) (c : ℕ) (hc : c ∈ S w) :
    (Finset.univ.filter (fun k : CBL I S =>
      (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧
      k.val.2.u = w ∧ k.val.2.v = w ∧
      k.val.2.a = c)).card ≤
    (c * c).divisors.card := by
  have h_fiber_count : (Finset.card (Finset.image (fun k : CBL I S => k.val.1.b) (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w ∧ k.val.2.a = c)))) ≤ (c * c).divisors.card := by
    refine Finset.card_le_card ?_;
    intro x hx;
    simp +zetaDelta at *;
    rcases hx with ⟨ a, ⟨ rfl, hu, hv, ha ⟩, rfl ⟩ ; have := a.2 ; simp_all +decide [ IsConsistentBadLabel ] ;
    have h_div : (a.val.1.b : ℕ) ∣ c * c := by
      have h_eq : (a.val.1.a : ℕ) * (a.val.1.b : ℕ) = c * c := by
        grind +suggestions
      exact h_eq ▸ dvd_mul_left _ _;
    grind;
  rwa [ Finset.card_image_of_injOn ] at h_fiber_count;
  intros k₁ hk₁ k₂ hk₂ h_eq;
  have h_eq_a : k₁.val.1.a = k₂.val.1.a := by
    have h_eq_a : k₁.val.1.a * k₁.val.1.b = k₂.val.1.a * k₂.val.1.b := by
      have := k₁.2.1; have := k₂.2.1; simp_all +decide [ IsConsistentBadLabel ] ;
      grind +suggestions;
    simp +zetaDelta at *;
    rw [ h_eq ] at h_eq_a;
    exact mul_right_cancel₀ ( show ( k₂.val.1.b : ℕ ) ≠ 0 from fun h => hS_pos _ k₂.val.1.hv <| by simpa [ h ] using k₂.val.1.hb ) h_eq_a;
  apply cbl_qa_inj hS_disj hS_pos;
  · apply PairLabel.ext';
    · have h_eq_u : k₁.val.1.a ∈ S k₁.val.1.u ∧ k₂.val.1.a ∈ S k₂.val.1.u := by
        exact ⟨ k₁.val.1.ha, k₂.val.1.ha ⟩;
      exact Classical.not_not.1 fun h => Finset.disjoint_left.mp ( hS_disj _ _ ( k₁.val.1.hu ) ( k₂.val.1.hu ) h ) ( h_eq_u.1 ) ( h_eq_a ▸ h_eq_u.2 );
    · grind;
    · exact h_eq_a;
    · exact h_eq;
  · grind

/-- Variant of cbl_q_diag_sum for p.v = t. -/
lemma cbl_q_diag_sum_pv {n : ℕ} {alpha eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k ∈ Finset.univ.filter (fun k : CBL I S =>
        (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = k.val.2.v),
      ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ ≤
    (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) := by
  have h_term_bound : ∀ k : CBL I S, k.val.2.u = k.val.2.v → ∏ i ∈ cblSupp k, (1 / (S i.val).card : ℝ) ≤ (n : ℝ) ^ (-(2 * alpha)) * (1 / (S (k.val.2.u)).card : ℝ) := by
    intro k hk; have := cbl_product_bound_qdiag_explicit hn hS_size hS_disj hS_pos k hk; aesop;
  have h_group_bound :
    ∑ k ∈ Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = k.val.2.v), (1 / (S (k.val.2.u)).card : ℝ) ≤ (I.card : ℝ) * (n : ℝ) ^ eta := by
      have h_group_bound :
        ∀ w ∈ I, ∑ k ∈ Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w), (1 / (S w).card : ℝ) ≤ (n : ℝ) ^ eta := by
          intros w hw
          have h_card_bound : (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w)).card ≤ (S w).card * (n : ℝ) ^ eta := by
            have h_card_bound : (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w)).card ≤ ∑ c ∈ S w, (c * c).divisors.card := by
              have h_card_bound : ∀ c ∈ S w, (Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w ∧ k.val.2.a = c)).card ≤ (c * c).divisors.card := by
                intros c hc
                apply cbl_qdiag_fiber_count_pv hS_disj hS_pos t w hw c hc;
              refine' le_trans _ ( Finset.sum_le_sum h_card_bound );
              rw [ ← Finset.card_biUnion ];
              · refine' Finset.card_le_card _;
                simp +contextual [ Finset.subset_iff ];
                exact fun k hk₁ hk₂ hk₃ => hk₂ ▸ k.1.2.ha;
              · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun k hkx hky => hxy <| by aesop;
            refine' le_trans ( Nat.cast_le.mpr h_card_bound ) _;
            push_cast;
            refine' le_trans ( Finset.sum_le_sum fun x hx => le_of_lt ( hdiv _ _ _ ) ) _;
            · exact Nat.mul_pos ( Nat.pos_of_ne_zero fun h => hS_pos w hw <| h ▸ hx ) ( Nat.pos_of_ne_zero fun h => hS_pos w hw <| h ▸ hx );
            · norm_cast ; nlinarith [ Finset.mem_range.mp ( hS_sub w hw hx ) ];
            · norm_num;
          simp +zetaDelta at *;
          rwa [ ← div_eq_mul_inv, div_le_iff₀' ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| hS_ne w hw ) ];
      have h_group_bound : ∑ w ∈ I, ∑ k ∈ Finset.univ.filter (fun k : CBL I S => (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t ∧ k.val.2.u = w ∧ k.val.2.v = w), (1 / (S w).card : ℝ) ≤ (I.card : ℝ) * (n : ℝ) ^ eta := by
        exact le_trans ( Finset.sum_le_sum h_group_bound ) ( by norm_num );
      convert h_group_bound using 1;
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun k hk => ⟨ k.val.2.u, k ⟩ ) _ _ _ _ <;> simp +decide;
      · exact fun k hk₁ hk₂ => ⟨ k.val.2.hu, hk₁, hk₂.symm ⟩;
      · grind;
  refine' le_trans ( Finset.sum_le_sum fun x hx => by simpa using h_term_bound x <| by aesop ) _;
  convert mul_le_mul_of_nonneg_left h_group_bound ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( - ( 2 * alpha ) ) ) using 1 <;> norm_num [ Real.rpow_sub ( Nat.cast_pos.mpr hn ) ] ; ring_nf;
  · rw [ Finset.mul_sum _ _ _ ];
  · rw [ Real.rpow_neg ( by positivity ) ] ; ring

/-- Per-position bound for p.v = t.
    Same proof structure as cbl_mass_per_position, using symmetric divisor bound. -/
lemma cbl_mass_per_position_pv {n : ℕ} {alpha eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hn : 0 < n) (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k : CBL I S, (if (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t then
      (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ)) ≤
    3 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) := by
  rw [ Finset.sum_ite ];
  refine' le_trans ( add_le_add ( show ∑ x ∈ Finset.filter ( fun x : CBL I S => ( ⟨ x.val.1.v, x.val.1.hv ⟩ : I ) = t ) Finset.univ, ∏ i ∈ cblSupp x, ( ↑ ( # ( S ↑i ) ) : ℝ ) ⁻¹ ≤ ( I.card + 1 ) * n ^ ( eta - 2 * alpha ) + I.card * n ^ ( eta - 2 * alpha ) from _ ) le_rfl ) _;
  · refine' le_trans _ ( add_le_add ( cbl_q_nondiag_sum_pv hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t ) ( cbl_q_diag_sum_pv hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t ) );
    rw [ ← Finset.sum_union ];
    · exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by by_cases h : x.val.2.u = x.val.2.v <;> aesop ) fun _ _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
    · exact Finset.disjoint_filter.mpr ( by aesop );
  · norm_num ; nlinarith [ show ( 1 :ℝ ) ≤ I.card from mod_cast Finset.card_pos.mpr ⟨ t, t.2 ⟩, Real.rpow_pos_of_pos ( show 0 < ( n :ℝ ) by positivity ) ( eta - 2 * alpha ) ] ;

/-
The local mass is bounded by 12|I| * n^(η-2α).
-/
lemma local_mass_combinatorial {n : ℕ} {alpha beta eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (heta : 0 < eta) (hn : 0 < n)
    (heta_def : eta = (2 * alpha - beta) / 2)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (h768 : (768 : ℝ) ≤ (n : ℝ) ^ eta)
    (hcard : (↑I.card : ℝ) ≤ (n : ℝ) ^ beta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k : CBL I S, (if t ∈ cblSupp k then
      (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ)) ≤
    12 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) := by
  -- Let's split the sum into four parts based on the position of t in the supports.
  have h_split : (∑ k : CBL I S, (if t ∈ cblSupp k then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) ≤
    (∑ k : CBL I S, (if (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) +
    (∑ k : CBL I S, (if (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) +
    (∑ k : CBL I S, (if (⟨k.val.2.u, k.val.2.hu⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) +
    (∑ k : CBL I S, (if (⟨k.val.2.v, k.val.2.hv⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) := by
      rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ];
      gcongr;
      split_ifs <;> norm_num;
      any_goals positivity;
      unfold cblSupp at *; aesop;
  -- Apply the bounds from cbl_mass_per_position and cbl_mass_per_position_pv to each part.
  have h_bounds : (∑ k : CBL I S, (if (⟨k.val.1.u, k.val.1.hu⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) ≤ 3 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) ∧
                 (∑ k : CBL I S, (if (⟨k.val.1.v, k.val.1.hv⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) ≤ 3 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) ∧
                 (∑ k : CBL I S, (if (⟨k.val.2.u, k.val.2.hu⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) ≤ 3 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) ∧
                 (∑ k : CBL I S, (if (⟨k.val.2.v, k.val.2.hv⟩ : ↥I) = t then (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ))) ≤ 3 * (I.card : ℝ) * (n : ℝ) ^ (eta - 2 * alpha) := by
                   refine' ⟨ cbl_mass_per_position hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t, cbl_mass_per_position_pv hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t, _, _ ⟩;
                   · convert cbl_mass_per_position hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t using 1;
                     apply Finset.sum_bij (fun k _ => cblSwap k);
                     · exact fun _ _ => Finset.mem_univ _;
                     · exact fun x _ y _ h => cblSwap_involutive.injective h;
                     · exact fun x _ => ⟨ cblSwap x, Finset.mem_univ _, cblSwap_involutive x ⟩;
                     · simp +decide [ cblSwap, cblSupp ];
                       grind;
                   · convert cbl_mass_per_position_pv hn hdiv hS_sub hS_size hS_disj hS_ne hS_pos t using 1;
                     apply Finset.sum_bij (fun k _ => cblSwap k);
                     · exact fun _ _ => Finset.mem_univ _;
                     · exact fun x _ y _ h => cblSwap_involutive.injective h;
                     · exact fun x _ => ⟨ cblSwap x, Finset.mem_univ _, cblSwap_involutive x ⟩;
                     · simp +decide [ cblSwap, cblSupp ];
                       grind;
  grind +revert

/-- Algebraic bound on the local mass. -/
lemma local_mass_algebraic {n : ℕ} {alpha beta eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (heta : 0 < eta) (hn : 0 < n)
    (heta_def : eta = (2 * alpha - beta) / 2)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (h768 : (768 : ℝ) ≤ (n : ℝ) ^ eta)
    (hcard : (↑I.card : ℝ) ≤ (n : ℝ) ^ beta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k : CBL I S, (if t ∈ cblSupp k then
      (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ)) ≤
    12 * (n : ℝ) ^ (-eta) :=
  le_trans (local_mass_combinatorial heta hn heta_def hdiv h768 hcard hS_sub hS_size hS_disj hS_ne hS_pos t)
    (local_mass_arith hn heta_def hcard)

/-
The local mass M_t: sum of event probabilities over all CBLs containing index t.
-/
lemma local_mass_bound {n : ℕ} {alpha beta eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (heta : 0 < eta) (hn : 0 < n)
    (heta_def : eta = (2 * alpha - beta) / 2)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (h768 : (768 : ℝ) ≤ (n : ℝ) ^ eta)
    (hcard : (↑I.card : ℝ) ≤ (n : ℝ) ^ beta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i)
    (t : ↥I) :
    ∑ k : CBL I S, (if t ∈ cblSupp k then
      (∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹ : ℝ) else (0 : ℝ)) ≤ 1 / 16 :=
  le_trans (local_mass_algebraic heta hn heta_def hdiv h768 hcard hS_sub hS_size hS_disj hS_ne hS_pos t)
    (local_mass_numerical hn h768)

lemma cbl_lll_condition {n : ℕ} {alpha beta eta : ℝ}
    {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (heta : 0 < eta) (hn : 0 < n)
    (heta_def : eta = (2 * alpha - beta) / 2)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (h768 : (768 : ℝ) ≤ (n : ℝ) ^ eta)
    (hxlt : 2 * (n : ℝ) ^ (-(3 * alpha)) < 1)
    (halpha_ge : (1 : ℝ) ≤ (n : ℝ) ^ alpha)
    (hcard : (↑I.card : ℝ) ≤ (n : ℝ) ^ beta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_ne : ∀ i ∈ I, (S i).Nonempty)
    (hS_pos : ∀ i ∈ I, 0 ∉ S i) :
    let x : CBL I S → ℝ := fun j =>
      2 * ∏ i ∈ cblSupp j, ((S i.val).card : ℝ)⁻¹
    (∀ j : CBL I S, 0 ≤ x j) ∧
    (∀ j : CBL I S, x j < 1) ∧
    (∀ j : CBL I S,
      (∏ i ∈ cblSupp j, ((Fintype.card ↥(S i.val) : ℝ)⁻¹)) ≤
      x j * ∏ k ∈ Finset.univ.filter ((cblGraph I S).Adj j), (1 - x k)) := by
  refine' ⟨ _, _, _ ⟩;
  · exact fun j => mul_nonneg zero_le_two <| Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
  · intro j
    have h_prod_bound : ∏ i ∈ cblSupp j, ((S i.val).card : ℝ)⁻¹ ≤ (n ^ alpha : ℝ)⁻¹ ^ 3 := by
      have h_prod_bound : ∏ i ∈ cblSupp j, ((S i.val).card : ℝ)⁻¹ ≤ (n ^ alpha : ℝ)⁻¹ ^ (cblSupp j).card := by
        exact le_trans ( Finset.prod_le_prod ( fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) fun _ _ => inv_anti₀ ( by positivity ) <| hS_size _ <| by aesop ) <| by norm_num;
      exact h_prod_bound.trans ( pow_le_pow_of_le_one ( by positivity ) ( inv_le_one_of_one_le₀ halpha_ge ) ( cblSupp_card_ge_three hS_disj hS_pos j ) );
    norm_num [ Real.rpow_neg ( by positivity : 0 ≤ ( n : ℝ ) ) ] at *;
    exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left h_prod_bound zero_le_two ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] at *; ring_nf at *; linarith );
  · intro j
    have h_sum : ∑ k ∈ Finset.univ.filter (fun k => (cblGraph I S).Adj j k), (2 * ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹) ≤ 1 / 2 := by
      have h_sum_bound : ∑ k ∈ Finset.univ.filter (fun k => (cblGraph I S).Adj j k), (2 * ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹) ≤ ∑ t ∈ cblSupp j, ∑ k : CBL I S, (if t ∈ cblSupp k then (2 * ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹) else 0) := by
        rw [ Finset.sum_comm ];
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        rotate_left;
        exact Finset.univ.filter fun k => ( cblGraph I S ).Adj j k;
        · exact Finset.subset_univ _;
        · exact fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity;
        · refine' Finset.sum_le_sum fun k hk => _;
          simp_all +decide;
          exact le_mul_of_one_le_left ( by positivity ) ( mod_cast Finset.card_pos.mpr ⟨ Classical.choose ( Finset.not_disjoint_iff.mp hk.2 ), Finset.mem_inter.mpr ⟨ Classical.choose_spec ( Finset.not_disjoint_iff.mp hk.2 ) |>.1, Classical.choose_spec ( Finset.not_disjoint_iff.mp hk.2 ) |>.2 ⟩ ⟩ );
      refine le_trans h_sum_bound ?_;
      refine' le_trans ( Finset.sum_le_sum fun t ht => _ ) _;
      use fun t => 2 * ( 1 / 16 );
      · have := local_mass_bound heta hn heta_def hdiv h768 hcard hS_sub hS_size hS_disj hS_ne hS_pos t; simp_all +decide [ Finset.sum_ite ] ;
        rw [ ← Finset.mul_sum _ _ _ ] ; linarith;
      · norm_num [ cblSupp ];
        rw [ mul_one_div, div_le_div_iff₀ ] <;> norm_cast;
        grind;
    have h_prod : ∏ k ∈ Finset.univ.filter (fun k => (cblGraph I S).Adj j k), (1 - 2 * ∏ i ∈ cblSupp k, ((S i.val).card : ℝ)⁻¹) ≥ 1 / 2 := by
      refine' le_trans _ ( prod_one_sub_le _ _ );
      · convert sub_le_sub_left h_sum 1 using 1 ; ring;
      · exact fun _ _ => mul_nonneg zero_le_two <| Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
      · intro k hk;
        refine' le_trans _ ( le_trans h_sum _ );
        · exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => mul_nonneg zero_le_two <| Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) hk );
        · norm_num;
    simp_all +decide;
    nlinarith [ inv_nonneg.2 ( show 0 ≤ ∏ x ∈ cblSupp j, ( # ( S x.val ) : ℝ ) from Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) ]

/-
Existence of Sidon set
-/
lemma sidon_selection_from_bounds {n : ℕ} {alpha beta eta : ℝ}
    (heta : 0 < eta) (hn : 0 < n)
    (heta_def : eta = (2 * alpha - beta) / 2)
    (hdiv : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (n : ℝ) ^ 2 →
        (m.divisors.card : ℝ) < (n : ℝ) ^ eta)
    (h768 : (768 : ℝ) ≤ (n : ℝ) ^ eta)
    (hxlt : 2 * (n : ℝ) ^ (-(3 * alpha)) < 1)
    (halpha_ge : (1 : ℝ) ≤ (n : ℝ) ^ alpha)
    (I : Finset ℕ) (S : ℕ → Finset ℕ)
    (hcard : (↑I.card : ℝ) ≤ (n : ℝ) ^ beta)
    (hS_sub : ∀ i ∈ I, S i ⊆ Finset.range (n + 1))
    (hS_size : ∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card)
    (hS_disj : ∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j))
    (hS_pos : ∀ i ∈ I, 0 ∉ S i) :
    ∃ c : ℕ → ℕ, (∀ i ∈ I, c i ∈ S i) ∧ IsMulSidon (I.image c) := by
  by_cases hI_empty : I = ∅
  · exact ⟨fun _ => 0, fun i hi => by simp [hI_empty] at hi,
      fun a b c d ha => by simp [hI_empty] at ha⟩
  have hS_ne : ∀ i ∈ I, (S i).Nonempty := by
    intro i hi; by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have := hS_size i hi; simp [h_empty] at this; linarith
  haveI : ∀ i : ↥I, Nonempty ↥(S i.val) := fun i =>
    Finset.Nonempty.coe_sort (hS_ne i.val i.prop)
  obtain ⟨hx_nn, hx_lt, h_lll⟩ := cbl_lll_condition heta hn heta_def
    hdiv h768 hxlt halpha_ge hcard hS_sub hS_size hS_disj hS_ne hS_pos
  obtain ⟨f, hf⟩ := product_lll_singleton
    cblSupp (cblVal hS_ne) (cblGraph I S) cblGraph_dep _ hx_nn hx_lt h_lll
  set c : ℕ → ℕ := fun i => if hi : i ∈ I then (f ⟨i, hi⟩).val else 0 with hc_def
  have hc_mem : ∀ i, i ∈ I → c i ∈ S i := by
    intro i hi; show (if h : i ∈ I then (f ⟨i, h⟩).val else 0) ∈ S i
    rw [dif_pos hi]; exact (f ⟨i, hi⟩).prop
  have hc_eq : ∀ (i : ℕ) (hi : i ∈ I), c i = (f ⟨i, hi⟩).val := by
    intro i hi; show (if h : i ∈ I then (f ⟨i, h⟩).val else 0) = _
    rw [dif_pos hi]
  refine ⟨c, hc_mem, ?_⟩
  apply no_bad_label_gives_sidon hS_disj c hc_mem
  intro i j k l hi hj hk hl hij hkl hprod hne
  let p : PairLabel I S :=
    ⟨i, j, c i, c j, hi, hj, hij, hc_mem i hi, hc_mem j hj, fun h => by subst h; rfl⟩
  let q : PairLabel I S :=
    ⟨k, l, c k, c l, hk, hl, hkl, hc_mem k hk, hc_mem l hl, fun h => by subst h; rfl⟩
  have hcbl : IsConsistentBadLabel p q := by
    refine ⟨hprod, ?_, fun h => congr_arg c h, fun h => congr_arg c h,
           fun h => congr_arg c h, fun h => congr_arg c h⟩
    by_contra hall; push_neg at hall
    exact hne (Prod.ext hall.1 (Prod.ext hall.2.1 (Prod.ext hall.2.2.1 hall.2.2.2)))
  let bl : CBL I S := ⟨(p, q), hcbl⟩
  obtain ⟨coord, hcoord_mem, hcoord_ne⟩ := hf bl
  apply hcoord_ne
  simp only [cblSupp, Finset.mem_insert, Finset.mem_singleton] at hcoord_mem
  refine cblVal_matches_f hS_ne bl coord hcoord_mem ?_ ?_ ?_ ?_ <;>
    (dsimp only [bl, p, q]; exact hc_eq _ _)

theorem random_multiplicative_sidon_selection' {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta_alpha : beta < 2 * alpha) :
    ∀ᶠ (n : ℕ) in atTop, ∀ (I : Finset ℕ) (S : ℕ → Finset ℕ),
      (↑I.card : ℝ) ≤ (n : ℝ) ^ beta →
      (∀ i ∈ I, S i ⊆ Finset.range (n + 1)) →
      (∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card) →
      (∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j)) →
      (∀ i ∈ I, 0 ∉ S i) →
      ∃ c : ℕ → ℕ, (∀ i ∈ I, c i ∈ S i) ∧
        IsMulSidon (I.image c) := by
  set eta := (2 * alpha - beta) / 2 with heta_def
  have heta_pos : 0 < eta := by linarith
  filter_upwards [uniform_divisor_bound heta_pos,
    eventually_nat_rpow_ge eta heta_pos 768,
    eventually_nat_rpow_lt_one alpha halpha,
    eventually_nat_rpow_ge alpha halpha 1] with n hdiv h768 hxlt halpha_ge
  intro I S hcard hS_sub hS_size hS_disj hS_pos
  by_cases hI_empty : I = ∅
  · subst hI_empty
    exact ⟨fun _ => 0, fun i hi => by simp at hi, fun a b c d ha => by simp at ha⟩
  have hn_pos : 0 < n := by
    by_contra h; push_neg at h; interval_cases n
    simp [Real.zero_rpow (ne_of_gt heta_pos)] at h768; linarith
  exact sidon_selection_from_bounds heta_pos hn_pos heta_def
    hdiv h768 hxlt halpha_ge I S hcard hS_sub hS_size hS_disj hS_pos

/-- Random multiplicative Sidon selection theorem :
    If we have ≤ n^β pairwise disjoint sets of size ≥ n^α in [n] with β < 2α,
    and all elements are positive (0 ∉ S i), we can pick one element
    from each to form a multiplicative Sidon set. -/
theorem random_multiplicative_sidon_selection {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta_alpha : beta < 2 * alpha) :
    ∀ᶠ (n : ℕ) in atTop, ∀ (I : Finset ℕ) (S : ℕ → Finset ℕ),
      (↑I.card : ℝ) ≤ (n : ℝ) ^ beta →
      (∀ i ∈ I, S i ⊆ Finset.range (n + 1)) →
      (∀ i ∈ I, (n : ℝ) ^ alpha ≤ ↑(S i).card) →
      (∀ i j : ℕ, i ∈ I → j ∈ I → i ≠ j → Disjoint (S i) (S j)) →
      (∀ i ∈ I, 0 ∉ S i) →
      ∃ c : ℕ → ℕ, (∀ i ∈ I, c i ∈ S i) ∧
        IsMulSidon (I.image c) :=
  random_multiplicative_sidon_selection' halpha hbeta_alpha

/-
For every δ > 0, we have g(n) ≪_δ n^{1/3+δ}.
-/
theorem gap_bound {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (n : ℕ) in atTop,
      (gapMulSidon n : ℝ) ≤ C * (n : ℝ) ^ (1/3 + delta) := by
        by_cases hδ : delta < 2 / 3;
        · -- Set α = 1/3 + δ, β = 2/3 - δ. Then 0 < β < 2α.
          set alpha := 1 / 3 + delta
          set beta := 2 / 3 - delta
          have halpha_pos : 0 < alpha := by
            positivity
          have hbeta_pos : 0 < beta := by
            exact sub_pos_of_lt hδ
          have hbeta_alpha : beta < 2 * alpha := by
            grind;
          obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ IsMulSidon A ∧ (∀ i : ℕ, i + 2 * Nat.ceil ((n : ℝ) ^ alpha) ≤ n → ∃ a ∈ A, i ≤ a ∧ a ≤ i + 2 * Nat.ceil ((n : ℝ) ^ alpha)) := by
            have := random_multiplicative_sidon_selection halpha_pos hbeta_alpha;
            obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp this;
            use N + 1;
            intro n hn
            obtain ⟨c, hc⟩ := hN n (by linarith) (Finset.range (Nat.floor ((n : ℝ) / Nat.ceil ((n : ℝ) ^ alpha)))) (fun i => Finset.Icc (i * Nat.ceil ((n : ℝ) ^ alpha) + 1) ((i + 1) * Nat.ceil ((n : ℝ) ^ alpha))) (by
            norm_num +zetaDelta at *;
            refine' le_trans ( Nat.floor_le <| by positivity ) _;
            rw [ div_le_iff₀ ] <;> norm_num;
            · exact le_trans ( by rw [ ← Real.rpow_add ( by norm_cast; linarith ) ] ; norm_num ) ( mul_le_mul_of_nonneg_left ( Nat.le_ceil _ ) ( by positivity ) );
            · exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _) (by
            intro i hi x hx; simp_all +decide [ Finset.subset_iff ] ;
            rw [ Nat.lt_iff_add_one_le, Nat.le_floor_iff ( by positivity ), le_div_iff₀ ] at hi <;> norm_cast at * <;> nlinarith [ Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) alpha ) ]) (by
            simp +zetaDelta at *;
            intro i hi; rw [ Nat.cast_sub ( by nlinarith ) ] ; push_cast; ring_nf;
            exact Nat.le_ceil _) (by
            intro i j hi hj hij; rw [ disjoint_iff_inf_le ] ; simp +decide [ Finset.subset_iff ] ;
            intro x hx₁ hx₂ hx₃; contrapose! hij; nlinarith;) (by
            -- Positivity: 0 ∉ Icc (i * ⌈n^α⌉ + 1) ((i + 1) * ⌈n^α⌉), since all elements ≥ 1
            intro i _hi; simp [Finset.mem_Icc]);
            refine' ⟨ _, _, hc.2, _ ⟩;
            · simp +zetaDelta at *;
              intro x hx; obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp hx; specialize hc; have := hc.1 i ( Finset.mem_range.mp hi ) ; norm_num at * ;
              rw [ Nat.lt_iff_add_one_le, Nat.le_floor_iff ( by positivity ), le_div_iff₀ ] at * <;> norm_cast at * <;> nlinarith [ Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) ( 1 / 3 + delta ) ) ];
            · intro i hi
              obtain ⟨j, hj⟩ : ∃ j ∈ Finset.range (Nat.floor ((n : ℝ) / Nat.ceil ((n : ℝ) ^ alpha))), i ≤ j * Nat.ceil ((n : ℝ) ^ alpha) + 1 ∧ j * Nat.ceil ((n : ℝ) ^ alpha) + 1 ≤ i + Nat.ceil ((n : ℝ) ^ alpha) := by
                refine' ⟨ ( i + ⌈ ( n : ℝ ) ^ alpha⌉₊ - 1 ) / ⌈ ( n : ℝ ) ^ alpha⌉₊, _, _, _ ⟩ <;> norm_num;
                · rw [ Nat.div_lt_iff_lt_mul <| Nat.ceil_pos.mpr <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ];
                  rw [ tsub_lt_iff_left ];
                  · have := Nat.lt_floor_add_one ( ( n : ℝ ) / ⌈ ( n : ℝ ) ^ alpha⌉₊ );
                    rw [ div_lt_iff₀ ] at this <;> norm_cast at * <;> nlinarith [ Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) alpha ) ];
                  · linarith [ Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) alpha ) ];
                · linarith [ Nat.div_add_mod ( i + ⌈ ( n : ℝ ) ^ alpha⌉₊ - 1 ) ⌈ ( n : ℝ ) ^ alpha⌉₊, Nat.mod_lt ( i + ⌈ ( n : ℝ ) ^ alpha⌉₊ - 1 ) ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) alpha ) ), Nat.sub_add_cancel ( show 1 ≤ i + ⌈ ( n : ℝ ) ^ alpha⌉₊ from by linarith [ Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) alpha ) ] ) ];
                · linarith [ Nat.div_mul_le_self ( i + ⌈ ( n : ℝ ) ^ alpha⌉₊ - 1 ) ⌈ ( n : ℝ ) ^ alpha⌉₊, Nat.sub_add_cancel ( show 1 ≤ i + ⌈ ( n : ℝ ) ^ alpha⌉₊ from by linarith [ Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith : 0 < n ) ) alpha ) ] ) ];
              exact ⟨ c j, Finset.mem_image_of_mem _ hj.1, by linarith [ Finset.mem_Icc.mp ( hc.1 j hj.1 ) ], by linarith [ Finset.mem_Icc.mp ( hc.1 j hj.1 ) ] ⟩;
          have h_bound : ∀ᶠ n in atTop, gapMulSidon n ≤ 2 * Nat.ceil ((n : ℝ) ^ alpha) := by
            filter_upwards [ Filter.eventually_ge_atTop N ] with n hn;
            exact Nat.sInf_le <| by obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := hN n hn; exact ⟨ A, hA₁, hA₂, hA₃ ⟩ ;
          use 4;
          simp +zetaDelta at *;
          obtain ⟨ M, hM ⟩ := h_bound; use Max.max M 1; intro n hn; specialize hM n ( le_trans ( le_max_left _ _ ) hn ) ; norm_cast;
          exact le_trans ( Nat.cast_le.mpr hM ) ( by norm_num; linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( n : ℝ ) ^ ( 3⁻¹ + delta ) by positivity ), show ( n : ℝ ) ^ ( 3⁻¹ + delta ) ≥ 1 by exact Real.one_le_rpow ( mod_cast by linarith [ le_max_right M 1 ] ) ( by positivity ) ] );
        · -- For $\delta \geq 2/3$, we can use the fact that $g(n) \leq n$.
          have h_le_n : ∀ n : ℕ, 0 < n → gapMulSidon n ≤ n := by
            intro n hn; refine' Nat.sInf_le _; use { 0 } ; simp +decide ;
            intro a b c d ha hb hc hd habcd; aesop;
          refine' ⟨ 1, zero_lt_one, _ ⟩;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using le_trans ( Nat.cast_le.mpr ( h_le_n n hn ) ) ( by simpa using Real.rpow_le_rpow_of_exponent_le ( mod_cast hn ) ( show ( 1 / 3 + delta ) ≥ 1 by linarith ) )

/-- The `i`-th full block `J_i = ((i-1)*H, i*H] ∩ ℕ` for `i ≥ 1`.
    We represent it as a `Finset ℕ`. -/
def fullBlock (H : ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range (i * H + 1)).filter (fun m => (i - 1) * H < m)

/-- A full block `J_i` is **good** if `i ≥ 2` and `J_i` contains at least `L_α`
    primes `p` with `p > H`. -/
def isGoodBlock (alpha : ℝ) (n : ℕ) (i : ℕ) : Prop :=
  2 ≤ i ∧
  primeThresholdL alpha ≤
    ((fullBlock (blockSizeH alpha n) i).filter
      (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n)).card

/-- Exceptional block count: under Adm(α, ℓ) with ℓ < 3α and 0 < α < 1,
    for sufficiently large n, if badCount * n^α ≤ volume(P_{α,n}),
    then badCount ≤ n^{α + ℓ/3}. -/
lemma exceptional_block_count {alpha ell : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hadm : Adm alpha ell) (hell : ell < 3 * alpha) :
    ∀ᶠ (n : ℕ) in atTop,
    ∀ (badCount : ℕ),
      (badCount : ℝ) * (n : ℝ) ^ alpha ≤
        ENNReal.toReal (MeasureTheory.volume (primePoorSet alpha n)) →
      (badCount : ℝ) ≤ (n : ℝ) ^ (alpha + ell / 3) := by
  set eta : ℝ := alpha - ell / 3 with heta_def
  have heta_pos : 0 < eta := by linarith
  have h_volume_bound : ∀ᶠ n in atTop,
      (MeasureTheory.volume (primePoorSet alpha n)).toReal <
        (n : ℝ) ^ (alpha + 2 * ell / 3) := by
    convert hadm.2 eta heta_pos using 1
    ext; rw [ENNReal.lt_ofReal_iff_toReal_lt]; ring_nf
    · rw [show alpha + ell * (2 / 3) = ell + eta by ring]
    · exact ne_of_lt (lt_of_le_of_lt
        (MeasureTheory.measure_mono
          (show primePoorSet alpha _ ⊆ Set.Icc 0 (↑‹ℕ› : ℝ) from
            fun x hx => ⟨hx.1, hx.2.1⟩))
        (by simp +decide [Real.volume_Icc]))
  filter_upwards [h_volume_bound, Filter.eventually_gt_atTop 0] with n hn hn'
  intro badCount hbadCount
  have hbadCount_le : (badCount : ℝ) < (n : ℝ) ^ (2 * ell / 3) := by
    rw [Real.rpow_add] at hn <;> norm_num at * <;>
      nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) alpha]
  exact hbadCount_le.le.trans
    (Real.rpow_le_rpow_of_exponent_le (mod_cast hn') (by linarith))

/-
Large-prime divisor count in a block
-/
lemma large_prime_divisor_count {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ m : ℕ, m ≤ n → m ≠ 0 →
        ((m.primeFactors).filter (fun p => blockSizeH alpha n < p)).card
          ≤ Nat.floor (1 / alpha) := by
            have h_large_n : ∀ᶠ n in atTop, ∀ m ≤ n, m ≠ 0 → ∀ p ∈ m.primeFactors, blockSizeH alpha n < p → p ≥ (n : ℝ) ^ alpha := by
              refine' Filter.eventually_atTop.mpr ⟨ 2, fun n hn m hm₁ hm₂ p hp₁ hp₂ => _ ⟩ ; norm_num [ blockSizeH ] at *;
              exact le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith );
            filter_upwards [ h_large_n, Filter.eventually_gt_atTop 1 ] with n hn hn';
            intros m hm hm_ne_zero
            have h_prod : (n : ℝ) ^ (alpha * (Finset.filter (fun p => blockSizeH alpha n < p) (Nat.primeFactors m)).card) ≤ m := by
              have h_prod : (∏ p ∈ Finset.filter (fun p => blockSizeH alpha n < p) (Nat.primeFactors m), p : ℝ) ≤ m := by
                rw [ ← Nat.cast_prod ] ; exact mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero hm_ne_zero ) ( Nat.prod_primeFactors_dvd _ |> dvd_trans ( by apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.filter_subset ] ) ) ;
              refine le_trans ?_ h_prod;
              rw [ Real.rpow_mul ] <;> norm_num;
              exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun x hx => hn m hm hm_ne_zero x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) );
            have h_alpha_r_le_one : alpha * (Finset.filter (fun p => blockSizeH alpha n < p) (Nat.primeFactors m)).card ≤ 1 := by
              contrapose! h_prod;
              exact lt_of_le_of_lt ( Nat.cast_le.mpr hm ) ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr hn' ) h_prod );
            exact Nat.le_floor <| by rwa [ le_div_iff₀' halpha ] ;

/-- The number of large primes dividing elements of a finset is bounded. -/
lemma primes_dividing_block_elements {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ (J : Finset ℕ), J.card ≤ blockSizeH alpha n →
        (∀ m ∈ J, m ≤ n ∧ m ≠ 0) →
        ((J.biUnion (fun m => m.primeFactors)).filter
          (fun p => blockSizeH alpha n < p)).card
          ≤ blockSizeH alpha n * Nat.floor (1 / alpha) := by
  filter_upwards [large_prime_divisor_count halpha] with n hn J hJ hJ'
  refine le_trans ?_ (Nat.mul_le_mul_right _ hJ)
  rw [Finset.filter_biUnion]
  exact le_trans Finset.card_biUnion_le
    (Finset.sum_le_card_nsmul _ _ _ fun x hx => hn x (hJ' x hx).1 (hJ' x hx).2)

/-
prime > H divides at most one element per block
-/
lemma prime_gt_H_divides_at_most_one {H : ℕ} {p : ℕ} (hp : H < p) (_hp_prime : Nat.Prime p)
    {i : ℕ} (hi : 1 ≤ i) :
    ((fullBlock H i).filter (fun m => p ∣ m)).card ≤ 1 := by
      rw [ Finset.card_le_one_iff ];
      simp_all +decide [ fullBlock ];
      intro a b ha₁ ha₂ ha₃ hb₁ hb₂ hb₃; obtain ⟨ k, hk ⟩ := ha₃; obtain ⟨ l, hl ⟩ := hb₃; nlinarith [ show k = l by nlinarith [ Nat.sub_add_cancel hi ] ] ;

lemma damage_bound_any_choice {H : ℕ}
    (goodBlocks : Finset ℕ) (choice : ℕ → ℕ)
    (hchoice_prime : ∀ g ∈ goodBlocks, Nat.Prime (choice g))
    (hchoice_large : ∀ g ∈ goodBlocks, H < choice g)
    {r : ℕ} (hr : 2 ≤ r) :
    ((fullBlock H r).filter
      (fun m => ∃ g ∈ goodBlocks, choice g ∣ m)).card
    ≤ goodBlocks.card := by
      have h_filter_le : (Finset.filter (fun m => ∃ g ∈ goodBlocks, choice g ∣ m) (fullBlock H r)).card ≤ ∑ g ∈ goodBlocks, (Finset.filter (fun m => choice g ∣ m) (fullBlock H r)).card := by
        exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le );
      exact h_filter_le.trans ( le_trans ( Finset.sum_le_sum fun _ _ => prime_gt_H_divides_at_most_one ( hchoice_large _ ‹_› ) ( hchoice_prime _ ‹_› ) ( by linarith ) ) ( by norm_num ) )

/-- Case 1: when goodBlocks.card < H/2, any valid choice works. -/
lemma non_ruining_prime_choice_small {alpha : ℝ}
    (_halpha : 0 < alpha) (_halpha1 : alpha < 1)
    {n : ℕ} (_hn : 2 ≤ n)
    (goodBlocks badBlocks : Finset ℕ)
    (Q : ℕ → Finset ℕ)
    (hQ : ∀ g ∈ goodBlocks, Q g ⊆ (fullBlock (blockSizeH alpha n) g).filter
      (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n))
    (hQ' : ∀ g ∈ goodBlocks, (Q g).card = primeThresholdL alpha)
    (hbad : ∀ r ∈ badBlocks, 2 ≤ r ∧ r * blockSizeH alpha n ≤ n)
    (hsmall : goodBlocks.card < blockSizeH alpha n / 2) :
    ∃ (choice : ℕ → ℕ),
      (∀ g ∈ goodBlocks, choice g ∈ Q g) ∧
      (∀ r ∈ badBlocks,
        ((fullBlock (blockSizeH alpha n) r).filter
          (fun m => ∃ g ∈ goodBlocks, choice g ∣ m)).card
        < blockSizeH alpha n / 2) := by
  have hQ_nonempty : ∀ g ∈ goodBlocks, (Q g).Nonempty := by
    intro g hg; rw [Finset.nonempty_iff_ne_empty]; intro h
    have := hQ' g hg; rw [h, Finset.card_empty] at this
    have : primeThresholdL alpha > 0 := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 5) _)
    omega
  set choice := fun g => if hg : g ∈ goodBlocks then (Q g).min' (hQ_nonempty g hg) else 0
  have hchoice_mem : ∀ g ∈ goodBlocks, choice g ∈ Q g := by
    intro g hg; simp only [choice, dif_pos hg]; exact Finset.min'_mem _ _
  have hchoice_prime : ∀ g ∈ goodBlocks, Nat.Prime (choice g) := by
    intro g hg; exact ((Finset.mem_filter.mp (hQ g hg (hchoice_mem g hg))).2).1
  have hchoice_large : ∀ g ∈ goodBlocks, blockSizeH alpha n < choice g := by
    intro g hg; exact ((Finset.mem_filter.mp (hQ g hg (hchoice_mem g hg))).2).2.1
  refine ⟨choice, hchoice_mem, ?_⟩
  intro r hr
  exact lt_of_le_of_lt
    (damage_bound_any_choice goodBlocks choice hchoice_prime hchoice_large (hbad r hr).1)
    hsmall

/-
Exponential decay: for large n, n * (2/√5)^(H·⌊1/α⌋) < 1.
-/
private lemma exp_decay_for_prime_choice {alpha : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ) * (2 / Real.sqrt 5) ^ (blockSizeH alpha n * Nat.floor (1 / alpha)) < 1 := by
  -- We will show that $n * r^{-2n^α} < 1$ for large $n$.
  have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (Real.sqrt 5 / 2) ^ (-2 * (n : ℝ) ^ alpha * (Nat.floor (1 / alpha) : ℝ))) Filter.atTop (nhds 0) := by
    -- We'll use the exponential property to simplify the expression. Note that $(\sqrt{5}/2)^{-2n^\alpha \lfloor 1/\alpha \rfloor} = \exp(-2n^\alpha \lfloor 1/\alpha \rfloor \ln(\sqrt{5}/2))$.
    suffices h_exp : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-2 * (n : ℝ) ^ alpha * (Nat.floor (1 / alpha) : ℝ) * Real.log (Real.sqrt 5 / 2))) Filter.atTop (nhds 0) by
      convert h_exp using 2 ; rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
    -- Let $y = n^\alpha$, therefore the expression becomes $y^{1/\alpha} \exp(-2y \lfloor 1/\alpha \rfloor \ln(\sqrt{5}/2))$.
    suffices h_y : Filter.Tendsto (fun y : ℝ => y ^ (1 / alpha) * Real.exp (-2 * y * (Nat.floor (1 / alpha)) * Real.log (Real.sqrt 5 / 2))) Filter.atTop (nhds 0) by
      have := h_y.comp ( tendsto_rpow_atTop ( by positivity : 0 < alpha ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, ← Real.rpow_mul ( Nat.cast_nonneg _ ), mul_one_div_cancel ( ne_of_gt halpha ), Real.rpow_one ] );
    -- Let $z = 2y \lfloor 1/\alpha \rfloor \ln(\sqrt{5}/2)$, therefore the expression becomes $z^{1/\alpha} \exp(-z)$.
    suffices h_z : Filter.Tendsto (fun z : ℝ => z ^ (1 / alpha) * Real.exp (-z)) Filter.atTop (nhds 0) by
      have h_subst : Filter.Tendsto (fun y : ℝ => (2 * y * (Nat.floor (1 / alpha)) * Real.log (Real.sqrt 5 / 2)) ^ (1 / alpha) * Real.exp (-2 * y * (Nat.floor (1 / alpha)) * Real.log (Real.sqrt 5 / 2))) Filter.atTop (nhds 0) := by
        convert h_z.comp ( show Filter.Tendsto ( fun y : ℝ => 2 * y * ⌊1 / alpha⌋₊ * Real.log ( Real.sqrt 5 / 2 ) ) Filter.atTop Filter.atTop from ?_ ) using 2;
        · norm_num;
        · exact Filter.Tendsto.atTop_mul_const ( Real.log_pos <| by rw [ lt_div_iff₀ ] <;> norm_num [ Real.lt_sqrt ] ) <| Filter.Tendsto.atTop_mul_const ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by rw [ le_div_iff₀ halpha ] ; linarith ) <| Filter.tendsto_id.const_mul_atTop zero_lt_two;
      have h_subst : Filter.Tendsto (fun y : ℝ => (2 * (Nat.floor (1 / alpha)) * Real.log (Real.sqrt 5 / 2)) ^ (1 / alpha) * y ^ (1 / alpha) * Real.exp (-2 * y * (Nat.floor (1 / alpha)) * Real.log (Real.sqrt 5 / 2))) Filter.atTop (nhds 0) := by
        refine h_subst.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with y hy using by rw [ show ( 2 * y * ⌊1 / alpha⌋₊ * Real.log ( Real.sqrt 5 / 2 ) ) = ( 2 * ⌊1 / alpha⌋₊ * Real.log ( Real.sqrt 5 / 2 ) ) * y by ring, Real.mul_rpow ( by exact mul_nonneg ( mul_nonneg zero_le_two <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ) hy.le ] ;
      convert h_subst.div_const ( ( 2 * ⌊1 / alpha⌋₊ * Real.log ( Real.sqrt 5 / 2 ) ) ^ ( 1 / alpha ) ) using 2 <;> ring_nf;
      rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( mul_pos ( mul_pos ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by nlinarith [ inv_mul_cancel₀ halpha.ne' ] ) <| Real.log_pos <| by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ) zero_lt_two ) _ ) ) ];
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ( ⌈1 / alpha⌉₊ : ℕ );
    refine' squeeze_zero_norm' _ this;
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by simpa using Real.rpow_le_rpow_of_exponent_le hx.le <| Nat.le_ceil _ ) <| by positivity;
  filter_upwards [ h_lim.eventually ( gt_mem_nhds zero_lt_one ), Filter.eventually_ge_atTop 1 ] with n hn hn';
  refine' lt_of_le_of_lt _ hn;
  rw [ show ( 2 / Real.sqrt 5 ) = ( Real.sqrt 5 / 2 ) ⁻¹ by rw [ inv_div ], ← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
  gcongr;
  · nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
  · exact le_trans ( mul_le_mul_of_nonneg_left ( Nat.le_ceil _ ) zero_le_two ) ( by norm_num [ blockSizeH ] )

/-
The damage to a bad block is bounded by the number of hitting blocks:
    each prime p > H divides at most 1 element of any interval of length H.
-/
private lemma damage_le_hitting_count {H : ℕ}
    (goodBlocks : Finset ℕ) (choice : ℕ → ℕ)
    (hchoice_prime : ∀ g ∈ goodBlocks, Nat.Prime (choice g))
    (hchoice_large : ∀ g ∈ goodBlocks, H < choice g)
    {r : ℕ} (hr : 2 ≤ r) :
    ((fullBlock H r).filter (fun m => ∃ g ∈ goodBlocks, choice g ∣ m)).card
    ≤ (goodBlocks.filter (fun g => ∃ m ∈ fullBlock H r, choice g ∣ m)).card := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.biUnion ( Finset.filter ( fun g => ∃ m ∈ fullBlock H r, choice g ∣ m ) goodBlocks ) fun g => Finset.filter ( fun m => choice g ∣ m ) ( fullBlock H r );
      · intro m hm; aesop;
      · refine' le_trans ( Finset.card_biUnion_le ) _;
        refine' le_trans ( Finset.sum_le_sum fun x hx => show #_ ≤ 1 from _ ) _ <;> norm_num;
        convert prime_gt_H_divides_at_most_one ( hchoice_large x ( Finset.filter_subset _ _ hx ) ) ( hchoice_prime x ( Finset.filter_subset _ _ hx ) ) ( by linarith ) using 1

/-
For large n we have n · 2^K / L^T ≤ n · (2/√5)^K < 1.
-/
private lemma decay_bound_nat {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∀ᶠ (n : ℕ) in atTop,
      (n : ℕ) * 2 ^ (blockSizeH alpha n * Nat.floor (1 / alpha))
        < (primeThresholdL alpha) ^ (blockSizeH alpha n / 2) := by
          -- Apply the exponential decay bound to conclude the proof.
          have h_exp_decay : ∀ᶠ (n : ℕ) in Filter.atTop, (n : ℝ) * (2 / Real.sqrt 5) ^ (blockSizeH alpha n * Nat.floor (1 / alpha)) < 1 := by
            convert exp_decay_for_prime_choice halpha halpha1 using 1;
          filter_upwards [ h_exp_decay, Filter.eventually_gt_atTop 0 ] with n hn hn';
          -- Since $primeThresholdL \alpha \geq 5^{1/\alpha}$, we have $(primeThresholdL \alpha)^{blockSizeH \alpha n / 2} \geq 5^{blockSizeH \alpha n / (2\alpha)}$.
          have h_primeThresholdL_ge : (primeThresholdL alpha : ℝ) ^ (blockSizeH alpha n / 2) ≥ 5 ^ (blockSizeH alpha n * Nat.floor (1 / alpha) / 2 : ℝ) := by
            have h_primeThresholdL_ge : (primeThresholdL alpha : ℝ) ≥ 5 ^ (1 / alpha) := by
              exact Nat.le_ceil _;
            refine le_trans ?_ ( pow_le_pow_left₀ ( by positivity ) h_primeThresholdL_ge _ );
            rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
            rw [ Nat.cast_div ] <;> norm_num;
            · nlinarith [ Nat.floor_le ( inv_nonneg.2 halpha.le ), show ( blockSizeH alpha n : ℝ ) ≥ 0 by positivity ];
            · exact dvd_mul_right _ _;
          contrapose! hn;
          convert one_le_div ( by positivity : 0 < ( 5 : ℝ ) ^ ( ( blockSizeH alpha n : ℝ ) * ⌊1 / alpha⌋₊ / 2 ) ) |>.2 h_primeThresholdL_ge |> le_trans <| ?_ using 1;
          convert div_le_div_of_nonneg_right ( Nat.cast_le.mpr hn ) ( by positivity : ( 0 :ℝ ) ≤ 5 ^ ( ( blockSizeH alpha n : ℝ ) * ⌊1 / alpha⌋₊ / 2 ) ) using 1 ; norm_num [ Real.div_rpow ] ; ring_nf;
          norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul, ← Real.rpow_neg ] ; ring_nf;
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; push_cast ; ring_nf

/-
Q_g sets for different good blocks are disjoint (since they are subsets of disjoint fullBlocks).
-/
private lemma Q_pairwise_disjoint {alpha : ℝ} {n : ℕ}
    (goodBlocks : Finset ℕ) (Q : ℕ → Finset ℕ)
    (hQ : ∀ g ∈ goodBlocks, Q g ⊆ (fullBlock (blockSizeH alpha n) g).filter
      (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n)) :
    ∀ i ∈ goodBlocks, ∀ j ∈ goodBlocks, i ≠ j → Disjoint (Q i) (Q j) := by
      intros i hi j hj hij;
      refine' Disjoint.mono ( hQ i hi ) ( hQ j hj ) _;
      refine' Finset.disjoint_left.mpr _;
      simp +contextual [ fullBlock ];
      intro a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆; contrapose! hij;
      nlinarith [ Nat.sub_add_cancel ( show 1 ≤ i from Nat.pos_of_ne_zero ( by aesop_cat ) ), Nat.sub_add_cancel ( show 1 ≤ j from Nat.pos_of_ne_zero ( by aesop_cat ) ) ]

/-- The large case of the non-ruining prime choice, with explicit bounds. -/
private lemma non_ruining_prime_choice_large {alpha : ℝ}
    {n : ℕ} (hn : 2 ≤ n)
    (h_decay : n * 2 ^ (blockSizeH alpha n * Nat.floor (1 / alpha)) <
               (primeThresholdL alpha) ^ (blockSizeH alpha n / 2))
    (goodBlocks badBlocks : Finset ℕ)
    (Q : ℕ → Finset ℕ)
    (hQ : ∀ g ∈ goodBlocks, Q g ⊆ (fullBlock (blockSizeH alpha n) g).filter
      (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n))
    (hQ' : ∀ g ∈ goodBlocks, (Q g).card = primeThresholdL alpha)
    (hbad : ∀ r ∈ badBlocks, 2 ≤ r ∧ r * blockSizeH alpha n ≤ n)
    (hlarge : blockSizeH alpha n / 2 ≤ goodBlocks.card)
    (hD_bound : ∀ r ∈ badBlocks, ∀ (D : Finset ℕ),
      D ⊆ goodBlocks.biUnion Q →
      (∀ p ∈ D, ∃ m ∈ fullBlock (blockSizeH alpha n) r, p ∣ m) →
      D.card ≤ blockSizeH alpha n * Nat.floor (1 / alpha)) :
    ∃ (choice : ℕ → ℕ),
      (∀ g ∈ goodBlocks, choice g ∈ Q g) ∧
      (∀ r ∈ badBlocks,
        ((fullBlock (blockSizeH alpha n) r).filter
          (fun m => ∃ g ∈ goodBlocks, choice g ∣ m)).card
        < blockSizeH alpha n / 2) := by
  set H := blockSizeH alpha n with hH_def
  set L := primeThresholdL alpha with hL_def
  have hL : 0 < L := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 5) _)
  have hQ_disj := Q_pairwise_disjoint goodBlocks Q hQ
  -- Define D_r and bad_r
  set D := fun r => (goodBlocks.biUnion Q).filter (fun p => ∃ m ∈ fullBlock H r, p ∣ m)
  set bad := fun r => (goodBlocks.pi Q).filter (fun f =>
    H / 2 ≤ (goodBlocks.filter (fun g => ∃ h : g ∈ goodBlocks, f g h ∈ D r)).card)
  -- Card of pi
  have h_card_pi : (goodBlocks.pi Q).card = L ^ goodBlocks.card := by
    rw [Finset.card_pi]; exact Finset.prod_eq_pow_card (fun g hg => hQ' g hg)
  -- Card bound for each r
  have h_bad_card : ∀ r ∈ badBlocks, (bad r).card ≤
      2 ^ (H * Nat.floor (1 / alpha)) * L ^ (goodBlocks.card - H / 2) := by
    intro r hr
    have h1 := pi_filter_count_bound goodBlocks Q L hL hQ' hQ_disj (D r) (H / 2) hlarge
    exact le_trans h1 (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num) (hD_bound r hr (D r)
        (Finset.filter_subset _ _) (fun p hp => (Finset.mem_filter.mp hp).2))))
  -- badBlocks.card ≤ n
  have h_bad_le_n : badBlocks.card ≤ n := by
    have hH_pos : 0 < H := Nat.mul_pos (by norm_num) (Nat.ceil_pos.mpr
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by linarith)) _))
    have hH_ge2 : 2 ≤ H := le_trans (by norm_num) (Nat.mul_le_mul_left 2
      (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by linarith)) _)))
    have : ∀ x ∈ badBlocks, x < n := by
      intro x hx; have := (hbad x hx); nlinarith
    exact le_trans (Finset.card_le_card (fun x hx => Finset.mem_range.mpr (this x hx)))
      (by simp [Finset.card_range])
  -- Total bad < total
  have h_lt : (badBlocks.biUnion bad).card < (goodBlocks.pi Q).card := by
    rw [h_card_pi]
    calc (badBlocks.biUnion bad).card
        ≤ ∑ r ∈ badBlocks, (bad r).card := Finset.card_biUnion_le
      _ ≤ badBlocks.card * (2 ^ (H * ⌊1 / alpha⌋₊) * L ^ (goodBlocks.card - H / 2)) :=
          Finset.sum_le_card_nsmul _ _ _ (fun r hr => h_bad_card r hr)
      _ ≤ n * (2 ^ (H * ⌊1 / alpha⌋₊) * L ^ (goodBlocks.card - H / 2)) :=
          Nat.mul_le_mul_right _ h_bad_le_n
      _ = n * 2 ^ (H * ⌊1 / alpha⌋₊) * L ^ (goodBlocks.card - H / 2) := by ring
      _ < L ^ (H / 2) * L ^ (goodBlocks.card - H / 2) :=
          Nat.mul_lt_mul_of_pos_right h_decay (pow_pos hL _)
      _ = L ^ goodBlocks.card := by rw [← pow_add, Nat.add_sub_cancel' hlarge]
  -- Extract good choice
  obtain ⟨f, hf_mem, hf_good⟩ := exists_not_mem_biUnion_of_card_lt
    h_lt
  -- Convert to ℕ → ℕ
  set choice := fun g => if hg : g ∈ goodBlocks then f g hg else 0
  have hf_pi : ∀ (g : ℕ) (hg : g ∈ goodBlocks), f g hg ∈ Q g := fun g hg => Finset.mem_pi.mp hf_mem g hg
  refine ⟨choice, fun g hg => by simp [choice, hg]; exact hf_pi g hg, ?_⟩
  intro r hr
  -- Show damage < H/2 by contradiction
  by_contra h_ge
  push_neg at h_ge
  -- damage ≥ H/2, so hitting count ≥ H/2
  have h_prime : ∀ g ∈ goodBlocks, Nat.Prime (choice g) := by
    intro g hg; simp [choice, hg]
    exact ((Finset.mem_filter.mp (hQ g hg (hf_pi g hg))).2).1
  have h_large : ∀ g ∈ goodBlocks, H < choice g := by
    intro g hg; simp [choice, hg]
    exact ((Finset.mem_filter.mp (hQ g hg (hf_pi g hg))).2).2.1
  have h_hitting := le_trans h_ge
    (damage_le_hitting_count goodBlocks choice h_prime h_large (hbad r hr).1)
  -- Each hitting block g has choice g ∈ D r, link to f
  have h_sub : goodBlocks.filter (fun g => ∃ m ∈ fullBlock H r, choice g ∣ m) ⊆
      goodBlocks.filter (fun g => ∃ h : g ∈ goodBlocks, f g h ∈ D r) := by
    intro g hg
    simp only [Finset.mem_filter] at hg ⊢
    refine ⟨hg.1, hg.1, ?_⟩
    simp only [D, Finset.mem_filter]
    constructor
    · exact Finset.mem_biUnion.mpr ⟨g, hg.1, hf_pi g hg.1⟩
    · obtain ⟨m, hm1, hm2⟩ := hg.2
      exact ⟨m, hm1, by simp [choice, hg.1] at hm2; exact hm2⟩
  have := le_trans h_hitting (Finset.card_le_card h_sub)
  -- So f ∈ bad r, contradicting hf_good
  exact hf_good r hr (Finset.mem_filter.mpr ⟨hf_mem, this⟩)

/-
Non-ruining prime choice.
-/
lemma non_ruining_prime_choice {alpha : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ (goodBlocks : Finset ℕ) (badBlocks : Finset ℕ)
        (Q : ℕ → Finset ℕ),
        (∀ g ∈ goodBlocks, Q g ⊆ (fullBlock (blockSizeH alpha n) g).filter
          (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n)) →
        (∀ g ∈ goodBlocks, (Q g).card = primeThresholdL alpha) →
        (∀ r ∈ badBlocks, 2 ≤ r ∧ r * blockSizeH alpha n ≤ n) →
        ∃ (choice : ℕ → ℕ),
          (∀ g ∈ goodBlocks, choice g ∈ Q g) ∧
          (∀ r ∈ badBlocks,
            ((fullBlock (blockSizeH alpha n) r).filter
              (fun m => ∃ g ∈ goodBlocks, choice g ∣ m)).card
            < blockSizeH alpha n / 2) := by
              filter_upwards [ Filter.eventually_gt_atTop 1, decay_bound_nat halpha halpha1, primes_dividing_block_elements halpha, Filter.eventually_ge_atTop 2 ] with n hn hn' hn'' hn''';
              intro goodBlocks badBlocks Q hQ hQ' hbad
              by_cases hsmall : goodBlocks.card < blockSizeH alpha n / 2;
              · apply_rules [ non_ruining_prime_choice_small ];
              · apply_rules [ non_ruining_prime_choice_large ];
                · linarith;
                · intro r hr D hD hD';
                  refine' le_trans _ ( hn'' _ _ _ );
                  rotate_left;
                  exact ( fullBlock ( blockSizeH alpha n ) r );
                  · refine' le_trans ( Finset.card_le_card _ ) _;
                    exact Finset.Icc ( ( r - 1 ) * blockSizeH alpha n + 1 ) ( r * blockSizeH alpha n );
                    · exact fun x hx => Finset.mem_Icc.mpr ⟨ Nat.succ_le_of_lt ( Finset.mem_filter.mp hx |>.2 ), Nat.le_of_lt_succ ( Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ) ⟩;
                    · simp +arith +decide;
                      nlinarith [ Nat.sub_add_cancel ( by linarith [ hbad r hr ] : 1 ≤ r ) ];
                  · intro m hm; simp_all +decide [ fullBlock ] ;
                    grind +splitIndPred;
                  · refine' Finset.card_le_card _;
                    grind +locals

/-- Every interval `[a, a + 2H]` contains all elements of the block with
    index `j = a/H + 2 ≥ 2`. -/
lemma interval_covers_block (H : ℕ) (hH : 0 < H) (a n : ℕ) (han : a + 2 * H ≤ n) :
    let j := a / H + 2
    2 ≤ j ∧ j * H ≤ n ∧
      ∀ m : ℕ, (j - 1) * H < m → m ≤ j * H → a ≤ m ∧ m ≤ a + 2 * H := by
  set j := a / H + 2
  refine ⟨Nat.le_add_left 2 _, ?_, ?_⟩
  · calc j * H = a / H * H + 2 * H := by ring
      _ ≤ a + 2 * H := Nat.add_le_add_right (Nat.div_mul_le_self a H) _
      _ ≤ n := han
  · intro m hm1 hm2
    have h_low : a < a / H * H + H := @Nat.lt_div_mul_add a H hH
    have h_div_le : a / H * H ≤ a := Nat.div_mul_le_self a H
    have hj_sub : j - 1 = a / H + 1 := by simp [j]
    have h_jm1 : (a / H + 1) * H = a / H * H + H := by ring
    have h_j : j * H = a / H * H + 2 * H := by simp [j]; ring
    rw [hj_sub, h_jm1] at hm1
    rw [h_j] at hm2
    exact ⟨by linarith, by linarith⟩

/-- Full blocks of different indices are disjoint. -/
lemma fullBlock_disjoint {H : ℕ} {i j : ℕ} (hij : i ≠ j) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    Disjoint (fullBlock H i) (fullBlock H j) := by
  rw [Finset.disjoint_left]
  intro m hm₁ hm₂
  simp [fullBlock] at hm₁ hm₂
  have : i < j ∨ j < i := by omega
  rcases this with h | h <;> nlinarith [Nat.sub_add_cancel hi, Nat.sub_add_cancel hj]

/-- Any set consisting entirely of primes is multiplicative Sidon. -/
lemma primes_mul_sidon {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    IsMulSidon S := by
      intro a b c d ha hb hc hd habcd
      have h_eq : a = c ∧ b = d ∨ a = d ∧ b = c := by
        have h_eq : a ∣ c ∨ a ∣ d := by
          exact Nat.Prime.dvd_mul ( hS a ha ) |>.1 ( habcd ▸ dvd_mul_right _ _ );
        have h_eq_cases : a = c ∨ a = d := by
          simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
        cases h_eq_cases <;> simp_all +decide [ Nat.Prime.ne_zero ];
        exact Or.inr ( mul_left_cancel₀ ( Nat.Prime.ne_zero ( hS _ hd ) ) <| by linarith );
      aesop

/-- If B consists of distinct primes, C is multiplicative Sidon, and no element of C
    is divisible by any prime in B, then B ∪ C is multiplicative Sidon. -/
lemma isMulSidon_primes_union_coprime {B C : Finset ℕ}
    (hB_prime : ∀ p ∈ B, Nat.Prime p)
    (hC_sidon : IsMulSidon C)
    (hC_coprime : ∀ c ∈ C, ∀ p ∈ B, ¬ p ∣ c)
    (hBC_disj : Disjoint B C) :
    IsMulSidon (B ∪ C) := by
      intro x y u v hx hy hu hv hxyuv
      by_cases hx_B : x ∈ B
      by_cases hy_B : y ∈ B;
      · by_cases hu_B : u ∈ B <;> by_cases hv_B : v ∈ B <;> simp_all +decide [ Finset.ext_iff ];
        · have := Nat.Prime.dvd_mul ( hB_prime x hx_B ) |>.1 ( hxyuv ▸ dvd_mul_right _ _ ) ; ( have := Nat.Prime.dvd_mul ( hB_prime y hy_B ) |>.1 ( hxyuv ▸ dvd_mul_left _ _ ) ; ( have := Nat.Prime.dvd_mul ( hB_prime u hu_B ) |>.1 ( hxyuv.symm ▸ dvd_mul_right _ _ ) ; ( have := Nat.Prime.dvd_mul ( hB_prime v hv_B ) |>.1 ( hxyuv.symm ▸ dvd_mul_left _ _ ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ; ) ) );
          grind;
        · have hx_div_u_or_v : x ∣ u ∨ x ∣ v := by
            exact Nat.Prime.dvd_mul ( hB_prime x hx_B ) |>.1 ( hxyuv ▸ dvd_mul_right _ _ );
          cases hx_div_u_or_v <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
          cases hxyuv <;> simp_all +decide ;
          exact absurd ( hB_prime 0 hu_B ) ( by norm_num );
        · have := congr_arg ( ·.factorization ( x : ℕ ) ) hxyuv; norm_num at this;
          rw [ Nat.factorization_mul, Nat.factorization_mul ] at this <;> simp_all +decide [ Nat.Prime.ne_zero];
          · rw [ Finsupp.single_apply, Finsupp.single_apply ] at this;
            split_ifs at this <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd];
            simp_all +decide [ mul_comm x, Nat.Prime.ne_zero ( hB_prime _ hx_B ) ];
          · intro H; specialize hC_coprime u hu x hx_B; aesop;
        · have h_div : x ∣ u * v ∧ y ∣ u * v := by
            exact ⟨ hxyuv ▸ dvd_mul_right _ _, hxyuv ▸ dvd_mul_left _ _ ⟩;
          simp_all +decide [ Nat.Prime.dvd_mul ];
      · by_cases hu_B : u ∈ B <;> by_cases hv_B : v ∈ B <;> simp_all +decide [ Finset.ext_iff ];
        · have h_div : x ∣ u * v := by
            exact hxyuv ▸ dvd_mul_right _ _;
          simp_all +decide [ Nat.Prime.dvd_mul ];
          cases h_div <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
          · cases hxyuv <;> simp_all +decide [ Finset.disjoint_left ];
            exact absurd ( hB_prime 0 hu_B ) ( by norm_num );
          · simp_all +decide [mul_comm, Nat.Prime.ne_zero (hB_prime _ hv_B)];
        · have hxu : x = u := by
            have hxu : x ∣ u * v := by
              exact hxyuv ▸ dvd_mul_right _ _;
            have := Nat.Prime.dvd_mul ( hB_prime x hx_B ) |>.1 hxu; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
            exact Nat.prime_dvd_prime_iff_eq ( hB_prime x hx_B ) ( hB_prime u hu_B ) |>.1 ( Nat.Prime.dvd_iff_not_coprime ( hB_prime x hx_B ) |>.2 this ) ▸ rfl
          have hyv : y = v := by
            nlinarith [ Nat.Prime.one_lt ( hB_prime x hx_B ) ]
          aesop;
        · have h_div : x ∣ u ∨ x ∣ v := by
            exact Nat.Prime.dvd_mul ( hB_prime x hx_B ) |>.1 ( hxyuv ▸ dvd_mul_right _ _ );
          cases h_div <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
          simp_all +decide [ mul_comm, Nat.Prime.ne_zero ( hB_prime _ hv_B ) ];
          tauto;
        · have h_not_div : ¬(x ∣ u) ∧ ¬(x ∣ v) := by
            exact ⟨ hC_coprime u hu x hx_B, hC_coprime v hv x hx_B ⟩;
          exact False.elim <| h_not_div.1 <| Or.resolve_right ( Nat.Prime.dvd_mul ( hB_prime x hx_B ) |>.1 <| hxyuv ▸ dvd_mul_right _ _ ) h_not_div.2;
      · by_cases hy_B : y ∈ B <;> simp_all +decide [ Finset.disjoint_left ];
        · by_cases hu_B : u ∈ B <;> by_cases hv_B : v ∈ B <;> simp_all +decide [ Finset.ext_iff ];
          · have h_div : x ∣ u * v := by
              exact hxyuv ▸ dvd_mul_right _ _;
            rw [ Nat.dvd_mul ] at h_div;
            rcases h_div with ⟨ k₁, k₂, hk₁, hk₂, rfl ⟩ ; simp_all +decide [ Nat.dvd_prime ] ;
            cases hk₁ <;> cases hk₂ <;> simp_all +decide ;
            · exact absurd ( hB_prime _ hy_B ) ( by rw [ Nat.prime_mul_iff ] ; aesop );
            · by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp_all +decide [ Nat.Prime.ne_zero ];
              exact absurd ( hB_prime 1 hy_B ) ( by norm_num );
          · have hy_div_uv : y ∣ u * v := by
              exact hxyuv ▸ dvd_mul_left _ _;
            have := Nat.Prime.dvd_mul ( hB_prime y hy_B ) |>.1 hy_div_uv; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
            grind +suggestions;
          · have hy_div_uv : y ∣ u * v := by
              exact hxyuv ▸ dvd_mul_left _ _
            have hv_div_xy : v ∣ x * y := by
              aesop;
            have := Nat.Prime.dvd_mul ( hB_prime y hy_B ) |>.1 hy_div_uv; ( have := Nat.Prime.dvd_mul ( hB_prime v hv_B ) |>.1 hv_div_xy; simp_all +decide [ Nat.Prime.dvd_mul ] ; );
            simp_all +decide [ Nat.prime_dvd_prime_iff_eq ( hB_prime _ hy_B ) ( hB_prime _ hv_B ) ];
            cases hxyuv <;> simp_all +decide ;
            exact absurd ( hB_prime 0 hv_B ) ( by norm_num );
          · have hy_div_uv : y ∣ u ∨ y ∣ v := by
              exact Nat.Prime.dvd_mul ( hB_prime y hy_B ) |>.1 ( hxyuv ▸ dvd_mul_left _ _ );
            grind;
        · have hu_C : u ∈ C := by
            cases hu <;> simp_all +decide ;
            exact hC_coprime _ hx _ ‹_› ( Nat.Prime.dvd_mul ( hB_prime _ ‹_› ) |>.1 ( hxyuv.symm ▸ dvd_mul_right _ _ ) |> Or.rec ( fun h => by aesop ) fun h => by aesop )
          have hv_C : v ∈ C := by
            cases hv <;> simp_all +decide ;
            exact hC_coprime _ hx _ ‹_› ( Nat.Prime.dvd_mul ( hB_prime _ ‹_› ) |>.1 ( hxyuv.symm ▸ dvd_mul_left _ _ ) |> Or.resolve_right <| by aesop );
          exact hC_sidon x y u v hx hy hu_C hv_C hxyuv

/-
If an interval [i, i+H] in [0,n] contains no prime, then the sub-interval
    [i, i+H/2] is contained in the prime-poor set P_{α,n}.
-/
lemma primeless_interval_subset_poor {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1)
    {n : ℕ} (_hn : 2 ≤ n) {i : ℕ} (hi : i + blockSizeH alpha n ≤ n)
    (hno_prime : ∀ p : ℕ, Nat.Prime p → ¬(i ≤ p ∧ p ≤ i + blockSizeH alpha n)) :
    Set.Icc (i : ℝ) (i + ↑(blockSizeH alpha n) / 2) ⊆ primePoorSet alpha n := by
      intro x hx; refine ⟨ ?_, ?_, ?_ ⟩ <;> norm_cast at *;
      · linarith [ hx.1 ];
      · linarith [ hx.2, show ( i : ℝ ) + blockSizeH alpha n ≤ n by exact_mod_cast hi, show ( blockSizeH alpha n : ℝ ) / 2 ≤ blockSizeH alpha n by linarith [ show ( blockSizeH alpha n : ℝ ) ≥ 0 by positivity ] ];
      · refine' lt_of_eq_of_lt ( Finset.card_eq_zero.mpr _ ) _;
        · refine' Finset.eq_empty_of_forall_notMem fun p hp => _;
          refine' hno_prime p ( Finset.mem_filter.mp hp |>.2.1 ) ⟨ _, _ ⟩ <;> norm_num at *;
          · exact_mod_cast hx.1.trans hp.2.2.1.le;
          · -- Since $x \leq i + \lceil n^\alpha \rceil$, we have $x^\alpha \leq n^\alpha$.
            have hx_alpha_le_n_alpha : x ^ alpha ≤ (n : ℝ) ^ alpha := by
              gcongr;
              · grind +revert;
              · linarith [ show ( i : ℝ ) + blockSizeH alpha n ≤ n by norm_cast ];
            exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( ( n : ℝ ) ^ alpha ), show ( blockSizeH alpha n : ℝ ) = 2 * ⌈ ( n : ℝ ) ^ alpha⌉₊ by exact_mod_cast rfl ] ;
        · exact Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( by norm_num ) _ )

/-
Under Adm(α, ℓ) with ℓ < α and 0 < α < 1, for large n, every interval of
    length blockSizeH α n contains a prime.
-/
lemma adm_implies_prime_weak {alpha ell : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hadm : Adm alpha ell) (hell : ell < alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ i : ℕ, i + blockSizeH alpha n ≤ n →
        ∃ p, Nat.Prime p ∧ i ≤ p ∧ p ≤ i + blockSizeH alpha n := by
          obtain ⟨rho, hrho⟩ : ∃ rho > 0, ell + rho < alpha := by
            exact ⟨ ( alpha - ell ) / 2, by linarith, by linarith ⟩;
          have h_measure : ∀ᶠ n in atTop, MeasureTheory.volume (primePoorSet alpha n) < ENNReal.ofReal ((n : ℝ) ^ (ell + rho)) := by
            exact hadm.2 rho hrho.1;
          filter_upwards [ h_measure, Filter.eventually_gt_atTop 1 ] with n hn hn';
          contrapose! hn;
          obtain ⟨ i, hi₁, hi₂ ⟩ := hn;
          refine' le_trans _ ( MeasureTheory.measure_mono <| primeless_interval_subset_poor halpha halpha1 hn' hi₁ _ );
          · norm_num [ blockSizeH ];
            exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hn'.le ) hrho.2.le ) ( Nat.le_ceil _ );
          · exact fun p hp hp' => not_lt_of_ge hp'.2 ( hi₂ p hp hp'.1 )

/-- Under Adm(α, ℓ) with ℓ < α and 0 < α < 1, for large n, every interval of
    length blockSizeH α n contains a prime. -/
lemma adm_implies_prime_in_every_interval {alpha ell : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hadm : Adm alpha ell) (hell : ell < alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∀ i : ℕ, i + blockSizeH alpha n ≤ n →
        ∃ p, Nat.Prime p ∧ i ≤ p ∧ p ≤ i + blockSizeH alpha n :=
  adm_implies_prime_weak halpha halpha1 hadm hell

/-- The primes-only construction for the ℓ < α case. -/
lemma construction_exists_primes {alpha ell : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hadm : Adm alpha ell)
    (hell : ell < alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ IsMulSidon A ∧
        ∀ i : ℕ, i + blockSizeH alpha n ≤ n →
          ∃ a ∈ A, i ≤ a ∧ a ≤ i + blockSizeH alpha n := by
  have h_primes := adm_implies_prime_in_every_interval halpha halpha1 hadm hell
  filter_upwards [h_primes] with n hn
  refine ⟨(Finset.range (n + 1)).filter Nat.Prime, Finset.filter_subset _ _,
    primes_mul_sidon (fun p hp => (Finset.mem_filter.mp hp).2), fun i hi => ?_⟩
  obtain ⟨p, hp_prime, hp_ge, hp_le⟩ := hn i hi
  exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime⟩, hp_ge, hp_le⟩

/-
For i ≥ 1 and H > 0, fullBlock H i has exactly H elements.
-/
lemma fullBlock_card {H : ℕ} (_hH : 0 < H) {i : ℕ} (hi : 1 ≤ i) :
    (fullBlock H i).card = H := by
      -- By definition of fullBlock, we have that fullBlock H i = (Finset.range (i * H + 1)).filter (fun m => (i - 1) * H < m).
      have h_fullBlock_def : fullBlock H i = Finset.Ioc ((i - 1) * H) (i * H) := by
        ext m
        simp [fullBlock, Finset.mem_Ioc];
        tauto;
      cases i <;> simp_all +decide [ Nat.succ_mul ]

/-
Bad blocks contribute to the prime-poor set: for a bad block index i (not good, 2 ≤ i,
    i*H ≤ n), the real interval [(i-1)*H, (i-1)*H + H/2] ⊆ P_{α,n} for large n.
-/
lemma bad_block_subset_poor {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (i : ℕ), 2 ≤ i → i * blockSizeH alpha n ≤ n → ¬isGoodBlock alpha n i →
      Set.Icc ((i - 1 : ℕ) * blockSizeH alpha n : ℝ)
              ((i - 1 : ℕ) * blockSizeH alpha n + (blockSizeH alpha n : ℝ) / 2)
      ⊆ primePoorSet alpha n := by
        refine' Filter.eventually_atTop.mpr ⟨ 8, fun n hn i hi hle hbad => _ ⟩;
        -- For x in [(i-1)*H, (i-1)*H + H/2], we have x + x^α ≤ i*H.
        have h_bound : ∀ x : ℝ, (i - 1) * blockSizeH alpha n ≤ x → x ≤ (i - 1) * blockSizeH alpha n + blockSizeH alpha n / 2 → x + x ^ alpha ≤ i * blockSizeH alpha n := by
          intros x hx_lower hx_upper
          have h_x_alpha : x ^ alpha ≤ (blockSizeH alpha n) / 2 := by
            refine' le_trans ( Real.rpow_le_rpow ( _ ) ( show x ≤ ( n : ℝ ) by nlinarith [ show ( i : ℝ ) * blockSizeH alpha n ≤ n by exact_mod_cast hle ] ) ( by positivity ) ) _;
            · exact le_trans ( mul_nonneg ( sub_nonneg.2 <| Nat.one_le_cast.2 <| by linarith ) <| Nat.cast_nonneg _ ) hx_lower;
            · unfold blockSizeH; norm_num; linarith [ Nat.le_ceil ( ( n : ℝ ) ^ alpha ) ] ;
          linarith;
        intro x hx; simp_all +decide [ primePoorSet ] ;
        refine' ⟨ _, _, _ ⟩;
        · exact le_trans ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) hx.1;
        · exact le_trans ( hx.2 ) ( by rw [ Nat.cast_pred ( by linarith ) ] ; nlinarith [ ( by norm_cast : ( i :ℝ ) * blockSizeH alpha n ≤ n ) ] );
        · refine' lt_of_le_of_lt _ ( not_le.mp fun h => hbad ⟨ hi, h ⟩ );
          refine' Finset.card_mono _;
          intro p hp; simp_all +decide [ fullBlock ] ;
          refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
          · exact_mod_cast ( by linarith [ h_bound x ( by cases i <;> norm_num at * ; linarith ) ( by cases i <;> norm_num at * ; linarith ) ] : ( p : ℝ ) ≤ i * blockSizeH alpha n );
          · exact_mod_cast hx.1.trans_lt hp.2.2.1;
          · rcases i with ( _ | _ | i ) <;> norm_num at *;
            exact_mod_cast ( by nlinarith [ h_bound x hx.1 hx.2 ] : ( blockSizeH alpha n : ℝ ) < p )

/-
The volume of the bad-block poor intervals sums to at least badCount * n^α.
-/
lemma bad_blocks_volume_bound {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (badBlks : Finset ℕ),
      (∀ r ∈ badBlks, 2 ≤ r ∧ r * blockSizeH alpha n ≤ n ∧ ¬isGoodBlock alpha n r) →
      (badBlks.card : ℝ) * (n : ℝ) ^ alpha ≤
        ENNReal.toReal (MeasureTheory.volume (primePoorSet alpha n)) := by
          filter_upwards [ bad_block_subset_poor halpha, Filter.eventually_gt_atTop 0 ] with n hn hn' badBlks hbadBlks;
          -- Since the intervals are pairwise disjoint, we can sum their lengths.
          have h_sum : (Finset.sum badBlks (fun r => ENNReal.ofReal ((blockSizeH alpha n : ℝ) / 2))) ≤ (MeasureTheory.volume (primePoorSet alpha n)) := by
            have h_sum : (Finset.sum badBlks (fun r => MeasureTheory.volume (Set.Icc ((r - 1 : ℕ) * blockSizeH alpha n : ℝ) ((r - 1 : ℕ) * blockSizeH alpha n + (blockSizeH alpha n : ℝ) / 2)))) ≤ (MeasureTheory.volume (primePoorSet alpha n)) := by
              rw [ ← MeasureTheory.measure_biUnion_finset ];
              · exact MeasureTheory.measure_mono ( Set.iUnion₂_subset fun i hi => hn i ( hbadBlks i hi |>.1 ) ( hbadBlks i hi |>.2.1 ) ( hbadBlks i hi |>.2.2 ) );
              · intros r hr s hs hrs; simp_all +decide [ Set.disjoint_left ] ;
                intro a ha₁ ha₂ ha₃; contrapose! hrs; rcases r with ( _ | _ | r ) <;> rcases s with ( _ | _ | s ) <;> norm_num at * ;
                any_goals linarith [ hbadBlks _ hr, hbadBlks _ hs ];
                exact Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( blockSizeH alpha n : ℝ ) > 0 from Nat.cast_pos.mpr <| Nat.mul_pos zero_lt_two <| Nat.ceil_pos.mpr <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn' ) _ ] } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( blockSizeH alpha n : ℝ ) > 0 from Nat.cast_pos.mpr <| Nat.mul_pos zero_lt_two <| Nat.ceil_pos.mpr <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn' ) _ ] } );
              · exact fun _ _ => measurableSet_Icc;
            convert h_sum using 2 ; norm_num [ Real.volume_Icc ];
          refine' le_trans _ ( ENNReal.toReal_mono _ h_sum );
          · norm_num [ blockSizeH ];
            exact mul_le_mul_of_nonneg_left ( Nat.le_ceil _ ) ( Nat.cast_nonneg _ );
          · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
            exacts [ Set.Icc 0 ( n : ℝ ), fun x hx => ⟨ hx.1, hx.2.1 ⟩, by simp +decide ]

/-
If the damage is < H/2, then the block has ≥ H/2 ≥ n^α surviving elements.
-/
lemma surviving_elements_large {alpha : ℝ} :
    ∀ᶠ (n : ℕ) in Filter.atTop,
    ∀ (H : ℕ), H = blockSizeH alpha n →
    ∀ (r : ℕ) (B : Finset ℕ),
      1 ≤ r →
      ((fullBlock H r).filter (fun m => ∃ g ∈ B, g ∣ m)).card < H / 2 →
      (n : ℝ) ^ alpha ≤ ↑((fullBlock H r).filter (fun m => ∀ p ∈ B, ¬(p ∣ m))).card := by
        refine Filter.eventually_atTop.mpr ?_;
        use 1;
        intro b hb H hH r B hr hdamage
        have h_survived : (fullBlock H r).card - (fullBlock H r |>.filter (fun m => ∃ g ∈ B, g ∣ m)).card ≥ (H : ℝ) / 2 := by
          rw [ fullBlock_card ] <;> norm_num [ hH ];
          · rw [ div_le_iff₀ ] <;> norm_cast;
            rw [ Int.subNatNat_eq_coe ] ; push_cast [ hH ] at * ; omega;
          · exact mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hb ) _ ) );
          · linarith;
        convert h_survived.le.trans' _ using 1;
        · rw [ eq_sub_iff_add_eq', ← Nat.cast_add, ← Finset.card_union_of_disjoint ];
          · congr with x ; by_cases hx : ∃ g ∈ B, g ∣ x <;> aesop;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
        · rw [ hH, blockSizeH ] ; ring_nf ;
          norm_num ; linarith [ Nat.le_ceil ( ( b : ℝ ) ^ alpha ) ]

/-
Under Adm(α, ℓ) with ℓ < 3α, for sufficiently large n, there exists a
multiplicative Sidon set A ⊆ [n] that intersects every interval
of length `2 * blockSizeH`.
-/
lemma construction_exists_full {alpha ell : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hadm : Adm alpha ell)
    (hell : ell < 3 * alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ IsMulSidon A ∧
        ∀ i : ℕ, i + 2 * blockSizeH alpha n ≤ n →
          ∃ a ∈ A, i ≤ a ∧ a ≤ i + 2 * blockSizeH alpha n := by
            obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ n ≥ N₁, ∀ (goodBlocks badBlocks : Finset ℕ) (Q : ℕ → Finset ℕ),
              (∀ g ∈ goodBlocks, Q g ⊆ (fullBlock (blockSizeH alpha n) g).filter
                (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n)) →
              (∀ g ∈ goodBlocks, (Q g).card = primeThresholdL alpha) →
              (∀ r ∈ badBlocks, 2 ≤ r ∧ r * blockSizeH alpha n ≤ n) →
              ∃ (choice : ℕ → ℕ),
                (∀ g ∈ goodBlocks, choice g ∈ Q g) ∧
                (∀ r ∈ badBlocks,
                  ((fullBlock (blockSizeH alpha n) r).filter
                    (fun m => ∃ g ∈ goodBlocks, choice g ∣ m)).card
                  < blockSizeH alpha n / 2) := by
                    exact Filter.eventually_atTop.mp ( non_ruining_prime_choice halpha halpha1 ) |> fun ⟨ N₁, hN₁ ⟩ => ⟨ N₁, fun n hn => hN₁ n hn ⟩;
            obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ n ≥ N₂, ∀ (badBlks : Finset ℕ),
              (∀ r ∈ badBlks, 2 ≤ r ∧ r * blockSizeH alpha n ≤ n ∧ ¬isGoodBlock alpha n r) →
                (badBlks.card : ℝ) * (n : ℝ) ^ alpha ≤
                  ENNReal.toReal (MeasureTheory.volume (primePoorSet alpha n)) →
                (badBlks.card : ℝ) ≤ (n : ℝ) ^ (alpha + ell / 3) := by
                  exact Filter.eventually_atTop.mp ( exceptional_block_count halpha halpha1 hadm hell ) |> fun ⟨ N₂, hN₂ ⟩ => ⟨ N₂, fun n hn badBlks hbadBlks hbadBlks' => hN₂ n hn _ hbadBlks' ⟩;
            have := @random_multiplicative_sidon_selection ( alpha := alpha ) ( beta := alpha + ell / 3 ) ?_ ?_;
            · filter_upwards [ this, Filter.eventually_gt_atTop N₁, Filter.eventually_gt_atTop N₂, Filter.eventually_gt_atTop 1, bad_blocks_volume_bound halpha, surviving_elements_large ] with n hn hn₁ hn₂ hn₃ hn₄ hn₅;
              -- Define the good and bad blocks.
              set goodBlocks := Finset.filter (fun j => 2 ≤ j ∧ j * blockSizeH alpha n ≤ n ∧ isGoodBlock alpha n j) (Finset.range (n / blockSizeH alpha n + 1))
              set badBlocks := Finset.filter (fun j => 2 ≤ j ∧ j * blockSizeH alpha n ≤ n ∧ ¬isGoodBlock alpha n j) (Finset.range (n / blockSizeH alpha n + 1));
              -- Define the sets Q_g for each good block g.
              obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → Finset ℕ, (∀ g ∈ goodBlocks, Q g ⊆ (fullBlock (blockSizeH alpha n) g).filter (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n)) ∧ (∀ g ∈ goodBlocks, (Q g).card = primeThresholdL alpha) := by
                have hQ : ∀ g ∈ goodBlocks, ∃ Q_g : Finset ℕ, Q_g ⊆ (fullBlock (blockSizeH alpha n) g).filter (fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n) ∧ Q_g.card = primeThresholdL alpha := by
                  intro g hg;
                  have := Finset.exists_subset_card_eq ( show primeThresholdL alpha ≤ Finset.card ( Finset.filter ( fun p => Nat.Prime p ∧ blockSizeH alpha n < p ∧ p ≤ n ) ( fullBlock ( blockSizeH alpha n ) g ) ) from ?_ );
                  · exact this;
                  · exact Finset.mem_filter.mp hg |>.2.2.2.2;
                choose! Q hQ₁ hQ₂ using hQ;
                use Q;
              obtain ⟨choice, hchoice⟩ := hN₁ n (by linarith) goodBlocks badBlocks Q hQ.left hQ.right (by
              exact fun r hr => ⟨ Finset.mem_filter.mp hr |>.2.1, Finset.mem_filter.mp hr |>.2.2.1 ⟩);
              -- Define the sets S_r for each bad block r.
              set S : ℕ → Finset ℕ := fun r => (fullBlock (blockSizeH alpha n) r).filter (fun m => ∀ p ∈ goodBlocks.image choice, ¬(p ∣ m));
              obtain ⟨c, hc⟩ := hn badBlocks S (by
              grind +splitImp) (by
              simp +zetaDelta at *;
              intro i hi₁ hi₂ hi₃ hi₄ m hm; simp_all +decide [ fullBlock ] ;
              linarith) (by
              intro r hr;
              convert hn₅ ( blockSizeH alpha n ) rfl r ( goodBlocks.image choice ) ( by linarith [ Finset.mem_filter.mp hr ] ) _ using 1;
              convert hchoice.2 r hr using 1;
              simp +decide [ Finset.mem_image ]) (by
              intros i j hi hj hij;
              rw [ Finset.disjoint_left ];
              simp +zetaDelta at *;
              intro a ha₁ ha₂ ha₃;
              exact False.elim <| fullBlock_disjoint hij ( by linarith ) ( by linarith ) |> fun h => Finset.disjoint_left.mp h ha₁ ha₃) (by
              -- Positivity: 0 ∉ S r, since elements of fullBlock for r ≥ 2 are > 0
              intro r hr; simp [S, Finset.mem_filter, fullBlock]);
              refine' ⟨ goodBlocks.image choice ∪ badBlocks.image c, _, _, _ ⟩;
              · simp +decide [ Finset.subset_iff ];
                rintro x ( ⟨ g, hg, rfl ⟩ | ⟨ r, hr, rfl ⟩ );
                · grind +suggestions;
                · simp +zetaDelta at *;
                  exact le_trans ( Finset.mem_filter.mp ( hc.1 r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 |>.1 ) |>.1 |> Finset.mem_range_succ_iff.mp ) ( by nlinarith [ Nat.div_mul_le_self n ( blockSizeH alpha n ) ] );
              · apply isMulSidon_primes_union_coprime;
                · grind +qlia;
                · exact hc.2;
                · grind;
                · simp +decide [ Finset.disjoint_left ];
                  intro g hg r hr; specialize hc; have := hc.1 r hr; simp +decide [ S ] at this;
                  exact fun h => this.2 g hg <| h.symm ▸ dvd_rfl;
              · intro i hi;
                -- By interval_covers_block, the block with index j = i / blockSizeH alpha n + 2 has j * blockSizeH alpha n ≤ n and all elements in [i, i + 2 * blockSizeH alpha n].
                obtain ⟨j, hj⟩ : ∃ j, 2 ≤ j ∧ j * blockSizeH alpha n ≤ n ∧ ∀ m, (j - 1) * blockSizeH alpha n < m → m ≤ j * blockSizeH alpha n → i ≤ m ∧ m ≤ i + 2 * blockSizeH alpha n := by
                  use i / blockSizeH alpha n + 2;
                  exact interval_covers_block _ ( Nat.pos_of_ne_zero ( by
                    exact ne_of_gt ( mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ) ) ) _ _ hi;
                by_cases hj_good : j ∈ goodBlocks;
                · use choice j;
                  simp +zetaDelta at *;
                  refine' ⟨ Or.inl ⟨ j, hj_good, rfl ⟩, _ ⟩;
                  have := hchoice.1 j hj_good.1 hj_good.2.1 hj_good.2.2.1 hj_good.2.2.2;
                  have := hQ.1 j hj_good.1 hj_good.2.1 hj_good.2.2.1 hj_good.2.2.2 this; simp +zetaDelta at *;
                  exact hj.2.2 _ ( Finset.mem_filter.mp this.1 |>.2 ) ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp this.1 |>.1 ) );
                · use c j;
                  simp +zetaDelta at *;
                  refine' ⟨ Or.inr ⟨ j, ⟨ _, _, _, _ ⟩, rfl ⟩, _ ⟩;
                  · rw [ Nat.le_div_iff_mul_le ] <;> nlinarith [ show 0 < blockSizeH alpha n from Nat.mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ];
                  · linarith;
                  · linarith;
                  · exact hj_good ( Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero ( by
                      exact ne_of_gt ( mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ) ) ) |>.2 ( by linarith ) ) hj.1 hj.2.1;
                  · exact hj.2.2 _ ( Finset.mem_filter.mp ( hc.1 j ( by
                      rw [ Nat.le_div_iff_mul_le ] <;> nlinarith [ show 0 < blockSizeH alpha n from mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ] ) hj.1 hj.2.1 ( hj_good ( by
                      rw [ Nat.le_div_iff_mul_le ] <;> nlinarith [ show 0 < blockSizeH alpha n from mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ] ) hj.1 hj.2.1 ) |>.1 ) |>.2 ) ( Finset.mem_filter.mp ( hc.1 j ( by
                      rw [ Nat.le_div_iff_mul_le ] <;> nlinarith [ show 0 < blockSizeH alpha n from mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ] ) hj.1 hj.2.1 ( hj_good ( by
                      rw [ Nat.le_div_iff_mul_le ] <;> nlinarith [ show 0 < blockSizeH alpha n from mul_pos zero_lt_two ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ) ] ) hj.1 hj.2.1 ) |>.1 ) |>.1 |> Finset.mem_range_succ_iff.mp );
            · linarith;
            · linarith;

/-- Under Adm(α, ℓ) with ℓ < 3α, a multiplicative Sidon set
    covering every interval of length `2 * blockSizeH` exists. -/
lemma construction_exists {alpha ell : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hadm : Adm alpha ell)
    (hell : ell < 3 * alpha) :
    ∀ᶠ (n : ℕ) in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ IsMulSidon A ∧
        ∀ i : ℕ, i + 2 * blockSizeH alpha n ≤ n →
          ∃ a ∈ A, i ≤ a ∧ a ≤ i + 2 * blockSizeH alpha n := by
  by_cases hell' : ell < alpha
  · -- ℓ < α: primes cover every interval of size blockSizeH, hence also 2*blockSizeH
    have h := construction_exists_primes halpha halpha1 hadm hell'
    filter_upwards [h] with n hn
    obtain ⟨A, hA_sub, hA_sidon, hA_cover⟩ := hn
    refine ⟨A, hA_sub, hA_sidon, fun i hi => ?_⟩
    obtain ⟨a, ha_mem, ha_ge, ha_le⟩ := hA_cover i (by linarith)
    exact ⟨a, ha_mem, ha_ge, by linarith⟩
  · exact construction_exists_full halpha halpha1 hadm hell

lemma gapMulSidon_le {n g : ℕ} {A : Finset ℕ}
    (hA_sub : A ⊆ Finset.range (n + 1))
    (hA_sidon : IsMulSidon A)
    (hA_cover : ∀ i : ℕ, i + g ≤ n → ∃ a ∈ A, i ≤ a ∧ a ≤ i + g) :
    gapMulSidon n ≤ g :=
  Nat.sInf_le ⟨A, hA_sub, hA_sidon, hA_cover⟩

lemma gapMulSidon_le_self (n : ℕ) : gapMulSidon n ≤ n := by
  refine Nat.sInf_le ?_
  use {0}
  unfold IsMulSidon; aesop

lemma gap_bound_alpha_ge_one {alpha : ℝ} (halpha1 : 1 ≤ alpha) :
    ∀ᶠ (n : ℕ) in atTop, (gapMulSidon n : ℝ) ≤ 5 * (n : ℝ) ^ alpha := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  calc (gapMulSidon n : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr (gapMulSidon_le_self n)
    _ ≤ (n : ℝ) ^ alpha := by
        simpa using Real.rpow_le_rpow_of_exponent_le (mod_cast hn) halpha1
    _ ≤ 5 * (n : ℝ) ^ alpha := by linarith [Real.rpow_nonneg (Nat.cast_nonneg n) alpha]

lemma two_blockSizeH_le {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ (n : ℕ) in atTop, (2 * blockSizeH alpha n : ℝ) ≤ 5 * (n : ℝ) ^ alpha := by
  simp only [blockSizeH]
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_nat_rpow_ge alpha halpha 4] with n hn hn4
  have h1 : (0 : ℝ) ≤ (n : ℝ) ^ alpha := by positivity
  have h2 : (⌈(n : ℝ) ^ alpha⌉₊ : ℝ) ≤ (n : ℝ) ^ alpha + 1 :=
    Nat.ceil_lt_add_one h1 |>.le
  push_cast
  nlinarith

/-- If `Adm(α, ℓ)` holds for some `ℓ < 3α`, then `g(n) ≤ 5 · n^α` eventually. -/
theorem main_theorem
    {alpha : ℝ} (halpha : 0 < alpha)
    (h : ∃ ell : ℝ, Adm alpha ell ∧ ell < 3 * alpha) :
    ∀ᶠ (n : ℕ) in atTop, (gapMulSidon n : ℝ) ≤ 5 * (n : ℝ) ^ alpha := by
  obtain ⟨ell, hadm, hell⟩ := h
  by_cases halpha1 : 1 ≤ alpha
  · exact gap_bound_alpha_ge_one halpha1
  · push_neg at halpha1
    have h1 := construction_exists halpha halpha1 hadm hell
    have h2 := two_blockSizeH_le halpha
    filter_upwards [h1, h2] with n hn1 hn2
    obtain ⟨A, hA_sub, hA_sidon, hA_cover⟩ := hn1
    calc (gapMulSidon n : ℝ)
        ≤ (2 * blockSizeH alpha n : ℝ) := by
          exact_mod_cast gapMulSidon_le hA_sub hA_sidon hA_cover
      _ ≤ 5 * (n : ℝ) ^ alpha := hn2

#print axioms main_theorem

end

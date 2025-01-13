
import Mathlib

open Function

section Metrizability_lemma

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
variable (fs : ∀ n, X → E n)
variable (fs_continuous : ∀ n, Continuous (fs n))
variable (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y))

private noncomputable def minDistMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * min (dist (fs n x) (fs n y)) 1

variable {fs}

lemma minDistMetric_bdd {x y} : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * min (dist (fs n x) (fs n y)) 1) i‖
  ≤ (fun n ↦ (1 / 2) ^ n) i) := by
  intro i
  simp only [one_div, inv_pow, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, Nat.abs_ofNat, inv_pos,
    Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right]
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right (dist (fs i x) (fs i y)) 1

lemma summable_if_bounded {x y} : Summable fun n ↦ (1 / 2) ^ n * min (dist (fs n x) (fs n y)) 1 :=
  Summable.of_norm_bounded (fun n ↦ (1 / 2) ^ n) summable_geometric_two (minDistMetric_bdd)

lemma minDistMetric_self_iff : ∀ {x y : X}, minDistMetric fs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [minDistMetric] at sum
    have sum_zero : ∑' n, (1/2)^n * min (dist (fs n x) (fs n y)) 1 = 0 →
       ∀ n, (1/2)^n * min (dist (fs n x) (fs n y)) 1 = 0 := by
      have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
          ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
        calc
          _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
          _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
          _ ↔ _ := Function.funext_iff
      intro sum
      let f := fun n ↦ (1/2)^n * min (dist (fs n x) (fs n y)) 1
      have terms_pos n : f n >= 0 := by positivity
      apply (tsum_zero (fun n ↦ (1/2)^n * min (dist (fs n x) (fs n y)) 1) (terms_pos)
          summable_if_bounded).mp
      exact sum
    apply sum_zero at sum
    simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      ne_eq, false_and, norm_eq_zero, sub_eq_zero, false_or] at sum
    contrapose! sum
    specialize fs_sep sum
    obtain ⟨a, fs_neq⟩ := fs_sep
    use a
    by_contra h
    cases' le_or_lt (dist (fs a x) (fs a y)) 1 with h1 h2
    · simp only [min_eq_left_iff.mpr h1, dist_eq_zero, one_div, inv_pow, mul_eq_zero, inv_eq_zero,
        pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *
      exact fs_neq h
    · linarith [min_eq_right_iff.mpr (LT.lt.le h2)]

  · intro x_eq_y
    simp [minDistMetric, one_div, inv_pow, x_eq_y, sub_self, norm_zero, mul_zero, tsum_zero]


lemma minDistMetric_comm : ∀ x y : X, minDistMetric fs x y = minDistMetric fs y x := by
  intro x y
  unfold minDistMetric
  rw [tsum_congr]
  intro b
  rw [dist_comm]

lemma minDistMetric_triangle {x y z} : minDistMetric fs x z ≤ minDistMetric fs x y + minDistMetric fs y z := by
  unfold minDistMetric
  have tri_ineq n : (1/2)^n * min (dist (fs n x) (fs n z)) 1
      ≤ (1/2)^n * min (dist (fs n x) (fs n y)) 1 + (1/2)^n * min (dist (fs n y) (fs n z)) 1 := by
    rw [← mul_add, mul_le_mul_left]
    simp only [ne_eq, min_le_iff]
    cases' (min_cases (dist (fs n x) (fs n z)) 1)
    · cases' (min_cases (dist (fs n x) (fs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (fs n x) (fs n y) (fs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]

    · cases' (min_cases (dist (fs n x) (fs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (fs n x) (fs n y) (fs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (fs n y) (fs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
    · positivity
  rw [← tsum_add]
  apply tsum_le_tsum
  · exact fun i ↦ tri_ineq i
  · exact summable_if_bounded
  · simpa [mul_add] using Summable.add summable_if_bounded summable_if_bounded
  exact summable_if_bounded
  exact summable_if_bounded
/-
noncomputable def ourMetricSpace : MetricSpace X where
  dist := minDistMetric fs
  dist_self := by
    intro x
    exact (minDistMetric_self_iff fs_sep ).mpr rfl
  dist_comm := minDistMetric_comm
  dist_triangle x y z := minDistMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]
  eq_of_dist_eq_zero := by
    intro x y
    exact (minDistMetric_self_iff fs_sep).mp
-/

def metricCopy (X :Type*) (fs : ∀n, X → E n) (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y))
    := X

noncomputable instance : MetricSpace (metricCopy X fs fs_sep) where
  dist := minDistMetric fs
  dist_self := by
    intro x
    exact (minDistMetric_self_iff fs_sep ).mpr rfl
  dist_comm := minDistMetric_comm
  dist_triangle x y z := minDistMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]
  eq_of_dist_eq_zero := by
    intro x y
    exact (minDistMetric_self_iff fs_sep).mp

def metricCopy.mk (X :Type*) (fs : ∀n, X → E n) (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) :
    X → metricCopy X fs fs_sep := id

def metricCopy.toOriginal (X :Type*) (fs : ∀n, X → E n) (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) :
    metricCopy X fs fs_sep → X := id

--example (f : X → ℝ) (g : X → ℝ) (hf : Continuous f) (hg : Continuous g) : Continuous ((f + g) : X × X → ℝ ) := by sorry
lemma continuous_minDistMetric (fs_continuousinuous : ∀ n, Continuous (fs n)) :
    Continuous (fun (p : X × X) ↦ minDistMetric fs p.1 p.2) := by
  unfold minDistMetric
  refine continuous_tsum (by fun_prop) summable_geometric_two ?_
  simp only [one_div, inv_pow, abs_mul, abs_inv, abs_pow, Real.norm_eq_abs, Nat.abs_ofNat,
    inv_pos, Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right, Prod.forall]
  intro n a b
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right _ _

lemma continuous_minDistMetric' (fs_continuous : ∀ (n : ℕ), Continuous (fs n)) : Continuous (fun (p : X × X) ↦
    dist (metricCopy.mk X fs fs_sep p.1) (metricCopy.mk X fs fs_sep p.2)) :=
  continuous_minDistMetric fs_continuous

example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : X × Y → Z) (x : X) (hphi : Continuous ϕ) : Continuous (fun y ↦ ϕ ⟨x, y⟩ ) := by
  exact Continuous.along_snd hphi

lemma continuous_metricCopy_mk (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)) (fs_continuous : ∀ n, Continuous (fs n)) :
    Continuous (metricCopy.mk X fs fs_sep) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have continuous_dist : Continuous (fun y ↦ dist (metricCopy.mk X fs fs_sep y)
      (metricCopy.mk X fs fs_sep x)) := by
    apply Continuous.along_fst (continuous_minDistMetric' fs_sep fs_continuous)
  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  have := @IsOpen.mem_nhds X x _ _ (continuous_dist.isOpen_preimage _ interval_open) (by simpa using hε)
  filter_upwards [this] with y hy using hy

lemma continuous_metricCopy_toOriginal (fs_continuous : ∀ n, Continuous (fs n)) :
    Continuous (metricCopy.toOriginal X fs fs_sep) := by
  have symm : ∀ (M : Set X), metricCopy.toOriginal X fs fs_sep ⁻¹' M = metricCopy.mk X fs fs_sep '' M := by
    exact fun M ↦ Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have closed_impl : ∀ (M : Set X), IsClosed M → IsClosed (metricCopy.toOriginal X fs fs_sep ⁻¹' M) := by
    intro M M_closed
    have M_cpt_X := IsClosed.isCompact M_closed
    rw [isCompact_iff_finite_subcover] at M_cpt_X
    have open_preimage M : IsOpen M → IsOpen (metricCopy.mk X fs fs_sep ⁻¹' M) :=
      continuous_def.mp (continuous_metricCopy_mk fs_sep fs_continuous) M
    have closed_preimage_M: IsClosed (metricCopy.toOriginal X fs fs_sep ⁻¹' M) := by
      have M_image_cpt : IsCompact (metricCopy.mk X fs fs_sep '' M) := by
        apply isCompact_of_finite_subcover
        intro _ Us Usi_open
        simp only [metricCopy.mk, id_eq, Set.image_id']
        exact fun a ↦ M_cpt_X Us (fun i ↦ open_preimage (Us i) (Usi_open i)) a
      simpa [symm M] using IsCompact.isClosed M_image_cpt
    exact closed_preimage_M
  exact continuous_iff_isClosed.mpr closed_impl



noncomputable def homeomorph_minDistMetric :
  X ≃ₜ metricCopy X fs fs_sep where
    toFun := metricCopy.mk X fs fs_sep
    invFun := metricCopy.toOriginal X fs fs_sep
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := continuous_metricCopy_mk fs_sep fs_continuous
    continuous_invFun := continuous_metricCopy_toOriginal fs_sep fs_continuous


lemma X_metrizable' (fs : ∀ n, X → E n) (fs_continuous : ∀ n, Continuous (fs n))
    (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)):
    TopologicalSpace.MetrizableSpace X := by

  exact (homeomorph_minDistMetric fs_continuous fs_sep).embedding.metrizableSpace


/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma TopologicalSpace.metrizableSpace_of_compact_separatesPoints (fs : ∀ n, X → E n) (fs_continuous : ∀ n, Continuous (fs n))
    (fs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y)): --(fs_bdd : ∀ n x, ‖fs n x‖ ≤ 1) : --fs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X :=
    (homeomorph_minDistMetric fs_continuous fs_sep).embedding.metrizableSpace

end Metrizability_lemma


section Seq_Banach_Alaoglu
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual 𝕜 V)) (K_cpt : IsCompact K)


/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_fs : ∃ (fs : ℕ → (WeakDual 𝕜 V) → 𝕜),
    (∀ n, Continuous (fs n)) ∧ (∀ ⦃x y⦄, x≠y → ∃ n, fs n x ≠ fs n y) := by
  set vs := TopologicalSpace.denseSeq V
  set fs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n)
  use (fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n))
  constructor
  · exact fun n ↦ WeakDual.eval_continuous (vs n)
  · intro w y w_ne_y
    contrapose! w_ne_y
    have : Set.EqOn (⇑w) (⇑y) (Set.range vs) := by
      simpa [Set.eqOn_range] using (Set.eqOn_univ (⇑w ∘ vs) (⇑y ∘ vs)).mp fun ⦃x⦄ _ ↦ w_ne_y x
    exact DFunLike.coe_fn_eq.mp (Continuous.ext_on (TopologicalSpace.denseRange_denseSeq V)
      (map_continuous w) (map_continuous y) this)

/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma TopologicalSpace.metrizableSpace_of_weakDual_compact : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨fs, fs_continuous, fs_sep⟩ := exists_fs 𝕜 V K
  let hs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ fs n (ϕ : WeakDual 𝕜 V)
  apply TopologicalSpace.metrizableSpace_of_compact_separatesPoints (E := fun _ ↦ 𝕜) hs
  · intro n
    exact Continuous.comp (fs_continuous n) continuous_subtype_val
  · intro x y x_ne_y
    apply fs_sep
    exact Subtype.coe_ne_coe.mpr x_ne_y

/- Any closed and norm-bounded subset of the dual V* of a separable space V is metrizable. -/
theorem WeakDual.isSeqCompact_of_isClosed_of_isBounded {s : Set (WeakDual 𝕜 V)}
    (hb : Bornology.IsBounded (NormedSpace.Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsSeqCompact s := by
  --have b_isCompact : IsCompact s := isCompact_of_bounded_of_closed hb hc
  have b_isCompact' : CompactSpace s := isCompact_iff_compactSpace.mp (isCompact_of_bounded_of_closed hb hc)
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
    TopologicalSpace.metrizableSpace_of_weakDual_compact 𝕜 V s (isCompact_of_bounded_of_closed hb hc)
  have seq_continuous_phi : SeqContinuous (fun φ : s ↦ (φ : WeakDual 𝕜 V)) :=
    continuous_iff_seqContinuous.mp continuous_subtype_val
  convert IsSeqCompact.range seq_continuous_phi
  simp [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual 𝕜 V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) :=
  WeakDual.isSeqCompact_of_isClosed_of_isBounded 𝕜 V Metric.isBounded_closedBall (isClosed_closedBall x' r)


end Seq_Banach_Alaoglu

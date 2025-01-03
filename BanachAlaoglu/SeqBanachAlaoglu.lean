
import BanachAlaoglu.Metrizability
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Defs.Filter

open Topology
section Seq_Banach_Alaoglu
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual 𝕜 V)) (K_cpt : IsCompact K)

/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual 𝕜 V) → 𝕜),
    (∀ n, Continuous (gs n)) ∧ (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y) := by
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ (ϕ : WeakDual 𝕜 V) (vs n)
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
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_gs 𝕜 V K
  let hs : ℕ → K → 𝕜 := fun n ↦ fun ϕ ↦ gs n (ϕ : WeakDual 𝕜 V)
  apply X_metrizable (E := fun _ ↦ 𝕜) hs
  · intro n
    exact Continuous.comp (gs_cont n) continuous_subtype_val
  · intro x y x_ne_y
    apply gs_sep
    exact Subtype.coe_ne_coe.mpr x_ne_y

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f g : E →SL[σ₁₂] F) (x y z : E)
variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [RingHomIsometric σ₁₂]

theorem ContinuousLinearMap.isSeqCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : Bornology.IsBounded s) : IsSeqCompact (closure (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) := by

  sorry

  /-have : ∀ x, IsSeqCompact (closure (apply' F σ₁₂ x '' s)) := by
    exact fun x => ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (Set.image_subset_iff.2 fun _ hg _ => subset_closure <| Set.mem_image_of_mem _ hg)
-/

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual 𝕜 V)) (K_cpt : IsCompact K)


theorem isSeqCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : Bornology.IsBounded s) (hc : IsClosed (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s)) :
    IsSeqCompact (((↑) : (E' →SL[σ₁₂] F) → E' → F) '' s) := by
  --exact hc.closure_eq ▸ ContinuousLinearMap.isSeqCompact_closure_image_coe_of_bounded hb
  sorry


theorem WeakDual.isSeqCompact_of_isClosed_of_isBounded {s : Set (WeakDual 𝕜 V)}
    (hb : Bornology.IsBounded (NormedSpace.Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsSeqCompact s := by
  --let b := (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
  have b_isCompact : IsCompact s := by
    exact isCompact_of_bounded_of_closed hb hc
  have b_isCompact' : CompactSpace s :=
    isCompact_iff_compactSpace.mp b_isCompact
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
    subset_metrizable 𝕜 V s b_isCompact
  have seq_cont_phi : SeqContinuous (fun φ : s ↦ (φ : WeakDual 𝕜 V)) :=
    continuous_iff_seqContinuous.mp continuous_subtype_val
  convert IsSeqCompact.range seq_cont_phi
  simp [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]

theorem WeakDual.isSeqCompact_polar [ProperSpace 𝕜] {s : Set V} (s_nhd : s ∈ 𝓝 (0 : V)) :
    IsSeqCompact (polar 𝕜 s) :=
  WeakDual.isSeqCompact_of_isClosed_of_isBounded (s := polar 𝕜 s) (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhd) (isClosed_polar _ _)

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual 𝕜 V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) :=
  --@WeakDual.isSeqCompact_of_isClosed_of_isBounded 𝕜 _ _ V _ _ _ (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) Metric.isBounded_closedBall (isClosed_closedBall x' r)
  WeakDual.isSeqCompact_of_isClosed_of_isBounded 𝕜 V Metric.isBounded_closedBall (isClosed_closedBall x' r)


end Seq_Banach_Alaoglu

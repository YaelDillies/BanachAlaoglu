
import Mathlib
set_option maxHeartbeats 1000000

section assumption_on_the_normed_field
open Function
class IsSensiblyNormed (𝕜: Type*) [NormedField 𝕜] where
  squeeze' : 𝕜 → 𝕜
  cont : Continuous squeeze'
  inj : Injective squeeze'
  bdd : ∀ c : 𝕜, ‖squeeze' c‖ ≤ 1
variable (𝕜: Type*) [NormedField 𝕜] [IsSensiblyNormed 𝕜]
def squeeze (c : 𝕜) : 𝕜 :=
    ‹IsSensiblyNormed 𝕜›.squeeze' c

lemma cont_squeeze : Continuous (squeeze 𝕜) := by
  exact ‹IsSensiblyNormed 𝕜›.cont

lemma inj_squeeze : Injective (squeeze 𝕜) := by
  exact ‹IsSensiblyNormed 𝕜›.inj

lemma bdd_squeeze (c : 𝕜) : ∀ c : 𝕜, ‖squeeze 𝕜 c‖ ≤ 1 := by
  exact ‹IsSensiblyNormed 𝕜›.bdd

--example (a b : ℝ) (h1 : 0 ≤ a) (h2 : 0 ≤ b) (h3 : a ≤ b) : a / b ≤ 1 := by
  --exact div_le_one_of_le h3 h2
--example (a : ℝ) (h1 : a ≤ 1) (h2 : 0 ≤ a) : |a| ≤ 1 := by




noncomputable instance : IsSensiblyNormed ℝ where
  squeeze' : ℝ → ℝ := (fun a ↦ a / (1 + ‖a‖))
  cont := by
    have foo : Continuous (fun a : ℝ ↦ ‖a‖) := by exact continuous_norm
    have foo2 : Continuous (fun a : ℝ ↦ (1 + ‖a‖)) := by
      exact Continuous.add (by exact continuous_const) (by exact foo)
    --have : Continuous (fun a:ℝ  ↦ 1) := by exact?

    have nonzero : (∀ (x : ℝ), (fun a ↦ 1 + ‖a‖) x ≠ 0) := by
      intro x
      have lt : ∀ a : ℝ, 0 < 1 + ‖a‖ := by
        simp [add_comm, add_pos_of_nonneg_of_pos]
      have : ∀ a : ℝ, 1 + ‖a‖ ≠ 0 := by
        intro a
        specialize lt a
        have : 0 < 1 + ‖a‖ → 1 + ‖a‖ ≠ 0 := by exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        exact this lt
      apply this
    have : Continuous (fun a : ℝ ↦ a) := continuous_id
    exact @Continuous.div ℝ ℝ _ _ _ _ (fun a ↦ a) (fun a : ℝ ↦ (1 + ‖a‖)) _ this foo2 nonzero

  inj := by
    have foo : ∀ x y: ℝ, x/(1 + ‖x‖) = y/(1 + ‖y‖) → (x = y) := by
      intro x y
      intro h
      simp at h
      have lt : ∀ a : ℝ, 0 < 1 + ‖a‖ := by
        simp [add_comm, add_pos_of_nonneg_of_pos]
      have : ∀ a : ℝ, 1 + ‖a‖ ≠ 0 := by
        intro a
        specialize lt a
        have : 0 < 1 + ‖a‖ → 1 + ‖a‖ ≠ 0 := by exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        exact this lt
      --contrapose! h
      have xnz : (1 + |x|) ≠ 0 := by exact this x
      have ynz : (1 + |y|) ≠ 0 := by exact this y
      have := @mul_eq_mul_of_div_eq_div ℝ _ (1 + |x|) (1 + |y|) x y xnz ynz h
      --have := @div_eq_iff_eq_mul ℝ _ --x (1 + |x|) (y/(1 + |y|))
      --have := (@div_eq_div_iff_mul_eq_mul ℝ _ x (1 + |x|) y (1 + |y|))


      sorry
    exact foo
 --#check CommGroup ℝ
  bdd := by
    have h : ∀ x : ℝ, x / (1 + ‖x‖) ≤ 1 := by
      intro x
      have : x ≤ 1 + ‖x‖ := by
        simp only [Real.norm_eq_abs]
        apply le_add_of_nonneg_of_le
        · linarith
        · exact le_abs_self x
      have : x / (1 + ‖x‖) ≤ 1 := by
        apply div_le_one_of_le
        · exact this
        · exact @add_nonneg ℝ _ _ _ 1 ‖x‖ (by linarith) (by norm_num)
      exact this

    intro c
    have : ∀ x : ℝ , ‖x / (1 + ‖x‖)‖ ≤ 1 := by
      intro x
      simp only [Real.norm_eq_abs, norm_inv]
      have : |x / (1 + |x|)| ≤ 1 := by
        have le_one : x / (1 + |x|) ≤ 1 := by exact h x
        have ge_minus_one : -1 ≤ x / (1 + |x|) := by
          have : x ≤ 1 + |x| := by
            apply le_add_of_nonneg_of_le
            · linarith
            · exact le_abs_self x



          sorry
        simp only [abs_le]
        exact ⟨ge_minus_one, h x⟩
      exact this
    exact this c

noncomputable instance : IsSensiblyNormed ℂ where
  squeeze' : ℂ → ℂ := (fun a ↦ a / (1 + ‖a‖))
  cont := by
    have foo : Continuous (fun a : ℂ ↦ ‖a‖) := by exact continuous_norm
    have foo2 : Continuous (fun a : ℂ ↦ (1 + ‖a‖)) := by
      exact Continuous.add (by exact continuous_const) (by exact foo)
    --have : Continuous (fun a:ℝ  ↦ 1) := by exact?
    have nonzero : (∀ (x : ℂ), (fun a ↦ 1 + ‖a‖) x ≠ 0) := by
      intro x
      have lt : ∀ a : ℂ, 0 < 1 + ‖a‖ := by
        simp only [Complex.norm_eq_abs]
        intro a
        apply lt_add_of_lt_of_nonneg
        · linarith
        · exact AbsoluteValue.nonneg Complex.abs a

      have : ∀ a : ℂ, 1 + ‖a‖ ≠ 0 := by
        intro a
        specialize lt a
        have : 0 < 1 + ‖a‖ → 1 + ‖a‖ ≠ 0 := by exact fun a_1 ↦ Ne.symm (ne_of_lt lt)
        exact this lt
      apply this
    have : Continuous (fun a : ℂ ↦ a) := continuous_id

    --have := @Continuous.div ℂ ℂ _ _ _ _ (fun a ↦ a) (fun a : ℂ ↦ (1 + ‖a‖)) _ this foo2 nonzero

    sorry


  inj := by
    intro x y x_eq_y
    norm_num at x_eq_y
    sorry
  bdd := by
    intro c
    norm_num
    have foo2 : ∀ x : ℂ, 0 ≤ Complex.abs (1 + ↑(Complex.abs x)) := by
      norm_num
    have foo4 : ∀ x : ℂ, Complex.abs x ≤ Complex.abs (1 + ↑(Complex.abs x)) := by
      sorry
    apply div_le_one_of_le
    · exact foo4 c
    · exact foo2 c



end assumption_on_the_normed_field

section Seq_cpt_continuity

#check Exists.choose
#check Exists.choose_spec
--variable (ys : ℕ → f '' K)

lemma IsSeqCompact.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : SeqContinuous f) {K : Set X} (hK : IsSeqCompact K) : IsSeqCompact (f '' K) := by
  rw [IsSeqCompact]
  intro ys hy
  simp [Set.mem_image] at hy
  let xs := fun n ↦ Exists.choose (hy n)
  have hxs : ∀ n, xs n ∈ K ∧ f (xs n) = ys n := fun n ↦ Exists.choose_spec (hy n)
  simp [forall_and] at hxs
  obtain ⟨hxl, hxr⟩ := hxs
  have hx :  ∀ x : ℕ → X, (∀ (n : ℕ), x n ∈ K) → ∃ a ∈ K, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds a) := by
    exact fun ⦃x⦄ a ↦ hK a
  specialize hx xs hxl
  simp only [Set.mem_image, exists_exists_and_eq_and]
  obtain ⟨a, ha, phi, hx⟩ := hx
  use a, ha, phi
  constructor
  · exact hx.1
  · have : Filter.Tendsto (xs ∘ phi) Filter.atTop (nhds a) ↔ Filter.Tendsto (ys ∘ phi) Filter.atTop (nhds (f a)) := by
      constructor
      · exact fun a_1 ↦ Filter.Tendsto.congr (fun x ↦ hxr (phi x)) (hf a_1)
      · intro h
        exact hx.2
    rw [← this]
    exact hx.2


#check Filter.tendsto_of_seq_tendsto
#check forall_const
--#check Filter.Tendsto (ys ∘ φ) Filter.atTop (nhds a)
--#check
--have hy5 := hy 5
  --let x5 := Exists.choose hy5
  --have hx5 : x5 ∈ K ∧ f x5 = ys 5 := Exists.choose_spec hy5
  --have hyn := fun n ↦ hy n

example {X : Type*} [TopologicalSpace X] [SeqCompactSpace X] : IsSeqCompact (Set.univ : Set X) := by
  exact (seqCompactSpace_iff X).mp ‹SeqCompactSpace X›

lemma SeqCompactSpace.range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeqCompactSpace X]
    (f : X → Y) (hf : SeqContinuous f) : IsSeqCompact (Set.range f) := by
  have := (@seqCompactSpace_iff X _ ).mp ‹SeqCompactSpace X›
  have foo : Set.range f = (f '' Set.univ) := by exact Eq.symm Set.image_univ
  rw[foo]
  apply IsSeqCompact.image f hf this


#check SeqCompactSpace
#check IsSeqCompact
#check @SeqCompactSpace.tendsto_subseq
#check @IsSeqCompact.subseq_of_frequently_in
#check Set.mem_image_iff_bex

--#check fun n ↦ (xs n)

end Seq_cpt_continuity



section Metrizability_lemma
--set_option diagnostics true

variable {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X] [NormedField 𝕜]
--variable (g : X → ℝ) (g_cont : Continuous g)
variable (gs : ℕ → X → 𝕜)
variable (gs_cont : ∀ n, Continuous (gs n))
variable (gs_sep : Set.SeparatesPoints (Set.range gs))
variable (gs_bdd : ∀ n : ℕ, ∀ x : X, ‖gs n x‖  ≤ 1)

noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * ‖gs n x - gs n y‖


lemma ourMetric_self_iff : ∀ {x y : X}, ourMetric gs x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro sum
    rw [ourMetric] at sum

    have sum_zero : ∑' n, (1/2)^n * ‖gs n x - gs n y‖  = 0 → ∀ n, (1/2)^n * ‖gs n x - gs n y‖  = 0 := by
      have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
          ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
        calc
          _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
          _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
          _ ↔ _ := Function.funext_iff

      intro sum
      let f := fun n ↦ (1/2)^n * ‖gs n x - gs n y‖
      have summable_metric : Summable f := by
        have norm_bdd : ∀ n, ‖gs n x - gs n y‖  ≤ 1 + 1 := by
          exact fun n ↦ norm_sub_le_of_le (gs_bdd n x) (gs_bdd n y)
        ring_nf at norm_bdd

        have summable_geom := summable_geometric_two

        have f_mul_summable : Summable (fun n ↦ 2 * ((1:ℝ) / 2) ^ n) := by
          exact @Summable.mul_left ℕ ℝ _ _ _ (fun n ↦ (1 / 2 )^ n) 2 summable_geom

        have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
            (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) (fun n ↦ 2 * (1 / 2) ^ n) f_mul_summable

        have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) i‖
            ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
          intro i
          simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm]
          rw [mul_comm]
          simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
          exact norm_bdd i

        exact summable_if_bounded this

      have terms_pos : ∀ n : ℕ, f n >= 0 := by
        have : ∀ n : ℕ, ‖gs n x - gs n y‖ >= 0 := by
          intro n
          apply norm_nonneg
        intro n
        refine mul_nonneg ?ha (this n)
        norm_num

      have := (tsum_zero (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) terms_pos summable_metric).mp
      apply this
      exact sum

    apply sum_zero at sum
    simp at sum
    simp_rw [sub_eq_zero] at sum
    contrapose! sum

    have : (∃ f ∈ Set.range gs, f x ≠ f y) → ∃ a, gs a ↑x ≠ gs a ↑y := by
      simp only [Set.mem_range, ne_eq, exists_exists_eq_and, imp_self]
    apply this
    apply gs_sep
    exact sum

  · intro x_eq_y
    rw [ourMetric, x_eq_y]
    simp

example (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
    ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
  calc
    _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
    _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
    _ ↔ _ := Function.funext_iff

#check tsum_eq_zero_iff
#check HasSum.summable
#check HasSum
#check mul_eq_zero
#check @pow_pos ℝ _ (1/2)
#check gs_sep


lemma ourMetric_comm : ∀ x y : X, ourMetric gs x y = ourMetric gs y x := by
  intro x y
  rw [ourMetric, ourMetric]
  have abs_eq : ∀ n, ‖gs n x - gs n y‖ = ‖gs n y - gs n x‖  := by
    intro n
    exact norm_sub_rev (gs n x) (gs n y)
  rw [tsum_congr]
  intro b
  rw [abs_eq]

lemma ourMetric_triangle : ∀ x y z : X, ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  intro x y z
  rw [ourMetric, ourMetric, ourMetric]

  have plusminus_eq_self : ∀ n, ‖gs n x - gs n z‖  = ‖gs n x + (gs n y - gs n y) - gs n z‖  := by
    intro n
    simp [sub_self (gs n y)]

  simp_rw [plusminus_eq_self]

  have tri_ineq : ∀ n, (1/2)^n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ (1/2)^n * ‖gs n x - gs n y‖ + (1/2)^n * ‖gs n y - gs n z‖  := by
    intro n
    rw [← add_comm_sub, add_sub_assoc (gs n x - gs n y) (gs n y) (gs n z) , ← mul_add]
    refine (mul_le_mul_left ?_).mpr ?_
    · refine pow_pos ?refine_1.H n
      linarith
    · exact norm_add_le (gs n x - gs n y) (gs n y - gs n z)

  have tsum_tri_ineq : ∑' (n : ℕ), (1 / 2) ^ n * ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤
      ∑' (n : ℕ), ((1 / 2) ^ n * ‖gs n x - gs n y‖ + (1 / 2) ^ n * ‖gs n y - gs n z‖) := by

    apply tsum_le_tsum
    · exact tri_ineq
    · have abs_plus : ∀ n, ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ ‖gs n x‖  + ‖gs n z‖ := by
        intro n
        simp [norm_sub_le (gs n x) (gs n z)]

      have norm_sum_bdd : ∀ n, ‖gs n x‖ + ‖gs n z‖  ≤ 1 + 1 := by
        intro n
        have gs_bdd' := gs_bdd
        specialize gs_bdd n x
        specialize gs_bdd' n z
        exact add_le_add gs_bdd gs_bdd'

      have norm_bdd : ∀ n, ‖gs n x + (gs n y - gs n y) - gs n z‖  ≤ 1 + 1 := by
        exact fun n ↦
          Preorder.le_trans ‖gs n x + (gs n y - gs n y) - gs n z‖ (‖gs n x‖ + ‖gs n z‖) (1 + 1)
            (abs_plus n) (norm_sum_bdd n)
      ring_nf at norm_bdd

      have summable_geom := summable_geometric_two

      have f_mul_summable : Summable (fun n ↦ 2 * ((1:ℝ) / 2) ^ n) := by
        exact @Summable.mul_left ℕ ℝ _ _ _ (fun n ↦ (1 / 2 )^ n) 2 summable_geom

      have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
          (fun n ↦ (1/2)^n * ‖gs n x + (gs n y - gs n y) - gs n z‖) (fun n ↦ 2 * (1 / 2) ^ n) f_mul_summable

      have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x + (gs n y - gs n y) - gs n z‖) i‖
          ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
        intro i
        simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm]
        rw [mul_comm]
        simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        exact norm_bdd i

      exact summable_if_bounded this

    · apply Summable.add
      · have norm_bdd : ∀ n, ‖gs n x - gs n y‖  ≤ 1 + 1 := by
          exact fun n ↦ norm_sub_le_of_le (gs_bdd n x) (gs_bdd n y)
        ring_nf at norm_bdd

        have summable_geom := summable_geometric_two

        have f_mul_summable : Summable (fun n ↦ 2 * ((1:ℝ) / 2) ^ n) := by
          exact @Summable.mul_left ℕ ℝ _ _ _ (fun n ↦ (1 / 2 )^ n) 2 summable_geom

        have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
          (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) (fun n ↦ 2 * (1 / 2) ^ n) f_mul_summable

        have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) i‖
            ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
          intro i
          simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
            RCLike.norm_ofNat, norm_norm]
          rw [mul_comm]
          simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
          exact norm_bdd i

        exact summable_if_bounded this

      · have norm_bdd : ∀ n, ‖gs n y - gs n z‖  ≤ 1 + 1 := by
          exact fun n ↦ norm_sub_le_of_le (gs_bdd n y) (gs_bdd n z)
        ring_nf at norm_bdd

        have summable_geom := summable_geometric_two

        have f_mul_summable : Summable (fun n ↦ 2 * ((1:ℝ) / 2) ^ n) := by
          exact @Summable.mul_left ℕ ℝ _ _ _ (fun n ↦ (1 / 2 )^ n) 2 summable_geom

        have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
            (fun n ↦ (1/2)^n * ‖gs n y - gs n z‖) (fun n ↦ 2 * (1 / 2) ^ n) f_mul_summable

        have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n y - gs n z‖) i‖
            ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
          intro i
          simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
            RCLike.norm_ofNat, norm_norm]
          rw [mul_comm]
          simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
          exact norm_bdd i

        exact summable_if_bounded this

  have pm : ∀ n : ℕ, ‖gs n x + -gs n y‖ = ‖gs n x -gs n y‖ := by simp[sub_eq_add_neg]

  have fsummable : Summable fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖ := by
    have norm_bdd : ∀ n, ‖gs n x - gs n y‖  ≤ 1 + 1 := by
        exact fun n ↦ norm_sub_le_of_le (gs_bdd n x) (gs_bdd n y)
    ring_nf at norm_bdd

    have summable_geom := summable_geometric_two

    have f_mul_summable : Summable (fun n ↦ 2 * ((1:ℝ) / 2) ^ n) := by
      exact @Summable.mul_left ℕ ℝ _ _ _ (fun n ↦ (1 / 2 )^ n) 2 summable_geom

    have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
        (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) (fun n ↦ 2 * (1 / 2) ^ n) f_mul_summable

    have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n x - gs n y‖) i‖
          ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
        intro i
        simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm]
        rw [mul_comm]
        simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        exact norm_bdd i

    exact summable_if_bounded this

  have gsummable : Summable fun n ↦ (1 / 2) ^ n * ‖gs n y - gs n z‖ := by
    have norm_bdd : ∀ n, ‖gs n y - gs n z‖  ≤ 1 + 1 := by
        exact fun n ↦ norm_sub_le_of_le (gs_bdd n y) (gs_bdd n z)
    ring_nf at norm_bdd

    have summable_geom := summable_geometric_two

    have f_mul_summable : Summable (fun n ↦ 2 * ((1:ℝ) / 2) ^ n) := by
        exact @Summable.mul_left ℕ ℝ _ _ _ (fun n ↦ (1 / 2 )^ n) 2 summable_geom

    have summable_if_bounded := @Summable.of_norm_bounded ℕ ℝ _ _
          (fun n ↦ (1/2)^n * ‖gs n y - gs n z‖) (fun n ↦ 2 * (1 / 2) ^ n) f_mul_summable

    have : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * ‖gs n y - gs n z‖) i‖
          ≤ (fun n ↦ 2 * (1 / 2) ^ n) i)  := by
        intro i
        simp only [one_div, inv_pow, sub_self, add_zero, norm_mul, norm_inv, norm_pow,
          RCLike.norm_ofNat, norm_norm, mul_comm, gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        --rw [mul_comm]
        --simp only [gt_iff_lt, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_right]
        exact norm_bdd i

    exact summable_if_bounded this

  have tsum_add_ineq : ∑' (n : ℕ), ((1 / 2) ^ n * ‖gs n x - gs n y‖ + (1 / 2) ^ n * ‖gs n y - gs n z‖) =
      ∑' (n : ℕ), (1 / 2) ^ n * ‖gs n x - gs n y‖ + ∑' (n : ℕ), (1 / 2)^ n * ‖gs n y - gs n z‖ := by
    rw [tsum_add fsummable gsummable]

  rw [tsum_add_ineq] at tsum_tri_ineq
  exact tsum_tri_ineq

--#check le_trans
#check Summable.of_norm_bounded
#check @summable_geometric_iff_norm_lt_one
#check Summable.const_smul
#check tsum_add



noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self := by
    intro x
    exact (@ourMetric_self_iff X 𝕜 _ gs gs_sep gs_bdd x x ).mpr rfl
  dist_comm := by
    intro x y
    exact (@ourMetric_comm X 𝕜 _ gs x y)
  dist_triangle := by
    intro x y z
    exact (@ourMetric_triangle X 𝕜 _ gs gs_bdd x y z)
  edist_dist := by simp [← ENNReal.ofReal_coe_nnreal]
  eq_of_dist_eq_zero := by
    intro x y
    exact (@ourMetric_self_iff X 𝕜 _ gs gs_sep gs_bdd x y).mp

def kopio (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) := X

def kopio.mk (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    X → kopio  X gs gs_sep gs_bdd := id

def kopio.toOrigin (X :Type*) (gs : ℕ → X → 𝕜) (gs_sep : Set.SeparatesPoints (Set.range gs))
    (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    kopio X gs gs_sep gs_bdd → X := id

noncomputable instance : MetricSpace (kopio X gs gs_sep gs_bdd) := ourMetricSpace gs gs_sep gs_bdd

lemma cont_ourMetric (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    ourMetric gs p.1 p.2) := by
  have : ∀ x y, Continuous (fun n ↦ ‖gs n x - gs n y‖) := by
    exact fun x y ↦ { isOpen_preimage := fun s a ↦ trivial }
  have : ∀ x y, Continuous (fun n ↦ (1/2)^n * ‖gs n x - gs n y‖) := by
    exact fun x y ↦ { isOpen_preimage := fun s a ↦ trivial }
  have : Continuous (fun (x, y) ↦ ourMetric gs x y) := by

    sorry
  sorry

lemma cont_ourMetric' (gs_cont : ∀ (n : ℕ), Continuous (gs n)) : Continuous (fun (p : X × X) ↦
    dist (kopio.mk X gs gs_sep gs_bdd p.1) (kopio.mk X gs gs_sep gs_bdd p.2)) := by
  exact cont_ourMetric gs gs_cont

--#check @continuous_tsum ℕ X 𝕜 _ _
#check continuous_generateFrom
#check Metric.nhds_basis_ball
#check continuous_iff_continuousAt
#check continuous_generateFrom
#check Metric.continuous_iff'
#check Continuous.isOpen_preimage
#check IsOpen.mem_nhds
--#check @continuous_tsum ℕ X 𝕜 _ _ (fun n ↦ 1/(2 ^ (n-1))) _ gs

--#check

--example (Y : Type*) [MetricSpace Y] (f : X → Y) (x : X) (h : ∀ r > 0, IsOpen (f ⁻¹' Metric.ball (f x) r)) :
    --ContinuousAt f x := by sorry

example (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ϕ : X × Y → Z) (x : X) (hphi : Continuous ϕ) : Continuous (fun y ↦ ϕ ⟨x, y⟩ ) := by
  exact Continuous.along_snd hphi

lemma cont_kopio_mk (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜)
    (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1)
    (gs_cont : ∀ n, Continuous (gs n)) :
    Continuous (kopio.mk X gs gs_sep gs_bdd) := by
  apply Metric.continuous_iff'.mpr
  intro x ε hε
  have cont_dist : Continuous (fun y ↦ dist (kopio.mk X gs gs_sep gs_bdd y)
      (kopio.mk X gs gs_sep gs_bdd x)) := by
    have := cont_ourMetric' gs gs_sep gs_bdd gs_cont
    apply Continuous.along_fst this

  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  have := cont_dist.isOpen_preimage _ interval_open
  have := @IsOpen.mem_nhds X x _ _ this ?_
  · filter_upwards [this] with y hy using hy
  · simpa using hε

lemma cont_kopio_toOrigin (X :Type*) [TopologicalSpace X] [CompactSpace X] (gs : ℕ → X → 𝕜)
    (gs_sep : Set.SeparatesPoints (Set.range gs)) (gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) :
    Continuous (kopio.toOrigin X gs gs_sep gs_bdd) := by
    rw [kopio.toOrigin]
    refine continuous_id_of_le ?_
    refine le_of_nhds_le_nhds ?h
    intro hk

    sorry

#check continuous_id
#check TopologicalSpace.coinduced id ‹TopologicalSpace X›
#check UniformSpace.toTopologicalSpace
#check @UniformSpace.toTopologicalSpace_mono X

noncomputable def homeomorph_OurMetric :
  X ≃ₜ kopio X gs gs_sep gs_bdd where
    toFun := kopio.mk X gs gs_sep gs_bdd
    invFun := kopio.toOrigin X gs gs_sep gs_bdd
    left_inv := by exact congrFun rfl
    right_inv := by exact congrFun rfl
    continuous_toFun := by exact cont_kopio_mk X gs gs_sep gs_bdd gs_cont
    continuous_invFun := by exact cont_kopio_toOrigin X gs gs_sep gs_bdd

--#check X ≃ₜ ourMetricSpace gs
#check ourMetricSpace gs
#check BoundedContinuousFunction.mkOfCompact
#check ContinuousMap.mk
#check Continuous.comp

/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (X 𝕜 : Type*) [NormedField 𝕜] [IsSensiblyNormed 𝕜] [TopologicalSpace X]
    [CompactSpace X] (gs : ℕ → X → 𝕜) (gs_cont : ∀ n, Continuous (gs n))
    (gs_sep : Set.SeparatesPoints (Set.range gs)): --(gs_bdd : ∀ n x, ‖gs n x‖ ≤ 1) : --gs_bdd ei pitäisi tarvita
    TopologicalSpace.MetrizableSpace X := by
  --refine ⟨?_⟩

  let hs := fun (n : ℕ) ↦ squeeze 𝕜 ∘ gs n
  have hs_sep : Set.SeparatesPoints (Set.range hs) := by
    intro x y x_ne_y
    unfold_let
    simp only [Set.mem_range, exists_exists_eq_and, Function.comp_apply]
    specialize gs_sep x_ne_y
    simp at gs_sep
    obtain ⟨a⟩ := gs_sep
    have inj := inj_squeeze 𝕜
    have : ∀ x y : 𝕜, x ≠ y → squeeze 𝕜 x ≠ squeeze 𝕜 y := by
      exact fun x y a a_1 ↦ a (inj a_1)
    use a
    apply this
    assumption
  have hs_bdd : ∀ (n : ℕ) (x : X), ‖hs n x‖ ≤ 1 := by
    exact fun n x ↦ bdd_squeeze 𝕜 (gs n x) (gs n x)

  have hs_cont : ∀ n : ℕ, Continuous (hs n) := by
    exact fun n ↦ @Continuous.comp X 𝕜 𝕜 _ _ _ (gs n) (squeeze 𝕜) (cont_squeeze 𝕜) (gs_cont n)

  have hom := @homeomorph_OurMetric X 𝕜 _ _ _ hs hs_cont hs_sep hs_bdd

  have induced_eq := @Homeomorph.induced_eq X (kopio X hs hs_sep hs_bdd) _ _ hom
  have induced := @inducing_induced X (kopio X hs hs_sep hs_bdd) _ hom
  --have psm := @TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace (kopio X hs hs_sep hs_bdd) _ _
  --have := @Inducing.pseudoMetrizableSpace X (kopio X hs hs_sep hs_bdd) _ _ _ hom


  --apply this at psm

  --have foo := @Inducing.pseudoMetrizableSpace X
  --let MetrizableSpace X := @TopologicalSpace.metrizableSpaceMetric X
  rw [induced_eq] at induced
  refine ⟨?_⟩

  --rw [Homeomorph.inducing this]
  --#check @TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace (kopio X gs gs_sep gs_bdd) _ _
  --#check @Inducing.pseudoMetrizableSpace -- X (kopio X gs gs_sep gs_bdd) _ _ _ hom
  sorry
/-
letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  (homeomorph_probabilityMeasure_levyProkhorov (Ω := X)).inducing.pseudoMetrizableSpace
-/

#check Set.range gs
#check Set.SeparatesPoints (Set.range gs)
#check X_metrizable
variable (x y : X)
#check @tsum ℝ _ _ ℕ (fun n ↦ 1/2^n * ‖gs n x - gs n y‖)
#check tsum (fun n ↦ 1/2^n * ‖gs n x - gs n y‖)
#check @ENNReal.tsum_eq_zero
#check IsAbsoluteValue.abv_sub
#check TopologicalSpace.MetrizableSpace
#check TopologicalSpace.MetrizableSpace X
#check MeasureTheory.LevyProkhorov
#check @Inducing.pseudoMetrizableSpace X (kopio X gs gs_sep gs_bdd) _ _ _
#check Homeomorph.induced_eq


end Metrizability_lemma

section Seq_Banach_Alaoglu

--variable (𝕜 : Type*)
variable (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℂ V]
variable [TopologicalSpace.SeparableSpace V]
variable (K : Set (WeakDual ℂ V)) (K_cpt : IsCompact K)
/-
example (ϕ : WeakDual ℂ V) (v : V) : False := by
  set a := ϕ v

  sorry-/
/- There exists a sequence of continuous functions that separates points on V*. -/
lemma exists_gs : ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs) := by
  set vs := TopologicalSpace.denseSeq V
  set gs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  --have ⟨h1, h2, h3⟩ := ∃ (gs : ℕ → (WeakDual ℂ V) → ℂ), (∀ n, Continuous (gs n)) ∧ Set.SeparatesPoints (Set.range gs)
  set gs2 : ℕ → WeakDual ℂ V → ℂ := fun n ↦ fun ϕ ↦ (ϕ : WeakDual ℂ V) (vs n)
  use gs2
  constructor
  · exact fun n ↦ WeakDual.eval_continuous (vs n)
  · intro w y w_ne_y

    sorry


  /-refine Exists.intro ?w ?h
  · exact fun a a ↦ Complex.I
  · refine ⟨?h.left, ?h.right⟩
    · exact fun n ↦ continuous_const
    · intro x y x_ne_y
      sorry
-/
#check @TopologicalSpace.exists_countable_dense (WeakDual ℂ V) _
#check @DenseRange.equalizer
--#check Continuous.comp (WeakDual.eval_continuous (vs n)) continuous_subtype_val



/- A compact subset of the dual V* of a separable space V is metrizable. -/
lemma subset_metrizable : TopologicalSpace.MetrizableSpace K := by
  have k_cpt' : CompactSpace K := by exact isCompact_iff_compactSpace.mp K_cpt
  have := exists_gs V K
  obtain ⟨gs, gs_cont, gs_sep⟩ := this
  let hs : ℕ → K → ℂ := fun n ↦ fun ϕ ↦ gs n (ϕ : WeakDual ℂ V)
  apply X_metrizable K ℂ hs
  · intro n
    exact Continuous.comp (gs_cont n) continuous_subtype_val
  · intro x y x_ne_y
    refine exists_exists_eq_and.mpr ?intro.intro.gs_sep.a
    unfold_let
    have subst : ∀ a : ℕ, (fun n ϕ ↦ gs n ↑ϕ) a x ≠ (fun n ϕ ↦ gs n ↑ϕ) a y → gs a x ≠ gs a y := by
      exact fun a a ↦ a
    simp only [subst]
    have : (∃ f ∈ Set.range gs, f x ≠ f y) → ∃ a, gs a ↑x ≠ gs a ↑y := by
        simp only [Set.mem_range, ne_eq, exists_exists_eq_and, imp_self]
    apply this
    apply gs_sep
    exact Subtype.coe_ne_coe.mpr x_ne_y

#check X_metrizable
#check Continuous.restrict
#check @WeakDual.toNormedDual ℂ _ V _ _
#check Subalgebra.SeparatesPoints

/- The closed unit ball is sequentially compact in V* if V is separable. -/
theorem WeakDual.isSeqCompact_closedBall (x' : NormedSpace.Dual ℂ V) (r : ℝ) :
    IsSeqCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by

  have b_isCompact : IsCompact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    apply WeakDual.isCompact_closedBall
  have b_isCompact' : CompactSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact isCompact_iff_compactSpace.mp b_isCompact

  have b_isMetrizable : TopologicalSpace.MetrizableSpace (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) := by
    exact subset_metrizable V (⇑toNormedDual ⁻¹' Metric.closedBall x' r) b_isCompact

  have seq_cpt_space := @FirstCountableTopology.seq_compact_of_compact (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
      _ _ b_isCompact'
  --have seq_cpt := (@seqCompactSpace_iff (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) _ ).mp seq_cpt_space

  have seq_cont_phi : SeqContinuous (fun φ : (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r) ↦ (φ : WeakDual ℂ V)) := by
    refine continuous_iff_seqContinuous.mp ?_
    exact continuous_subtype_val

  have seq_incl := @SeqCompactSpace.range (WeakDual.toNormedDual ⁻¹' Metric.closedBall x' r)
                  (WeakDual ℂ V) _ _ _ (fun φ ↦ φ) seq_cont_phi
  convert seq_incl

  simp only [Subtype.range_coe_subtype, Set.mem_preimage, coe_toNormedDual, Metric.mem_closedBall]
  rfl
  --sorry




#check Continuous.seqContinuous
#check IsSeqCompact
#check Module.Dual
#check WeakDual ℂ V
#check Set (WeakDual ℂ V)
#check IsCompact
#check @UniformSpace.isCompact_iff_isSeqCompact
#check IsCompact.isSeqCompact
#check TopologicalSpace.exists_countable_dense
#check subset_metrizable

end Seq_Banach_Alaoglu
/-
section inducing
variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
theorem _root_.Inducing.MetrizableSpace [TopologicalSpace.MetrizableSpace Y] {f : X → Y}
    (hf : Inducing f) : TopologicalSpace.MetrizableSpace X := by

    sorry
end inducing
-/

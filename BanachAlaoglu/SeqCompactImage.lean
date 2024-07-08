--import Mathlib
--import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Sequences

theorem IsSeqCompact.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) : IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  let xs := fun n ↦ Exists.choose (ys_in_fK n)
  obtain ⟨xs_in_K, fxs_eq_ys⟩ : (∀ n, xs n ∈ K) ∧ ∀ n, f (xs n) = ys n :=
    forall_and.mp fun n ↦ Exists.choose_spec (ys_in_fK n)
  simp only [Set.mem_image, exists_exists_and_eq_and]
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨a, a_in_K, phi, phi_mono, ?_⟩
  exact Filter.Tendsto.congr (fun x ↦ fxs_eq_ys (phi x)) (f_cont xs_phi_lim)


theorem isSeqCompact_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeqCompactSpace X]
    (f : X → Y) (hf : SeqContinuous f) : IsSeqCompact (Set.range f) := by
  rw [← Set.image_univ]
  exact IsSeqCompact.image f hf ((seqCompactSpace_iff X).mp ‹SeqCompactSpace X›)


lemma IsSeqCompact.image_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (f_cont : Continuous f) {K : Set X} (K_cpt : IsSeqCompact K) : IsSeqCompact (f '' K) :=
  IsSeqCompact.image f (Continuous.seqContinuous f_cont) K_cpt


lemma SeqCompactSpace.range_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeqCompactSpace X]
    (f : X → Y) (f_cont : Continuous f) : IsSeqCompact (Set.range f) :=
  isSeqCompact_range f (Continuous.seqContinuous f_cont)

import Mathlib
import LeanCondensed.Projects.Pullbacks

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  ChosenFiniteProducts


lemma IsClosedThingy {T : LightProfinite} (f : T ⟶ ℕ∪{∞}) (s : ℕ → Set T)
  (hs : ∀ n (x : s n), f x = n) (hs' : ∀ n, IsClosed (s n)) : IsClosed ({t | f t = ∞} ∪ ⋃ n, s n) := by
  apply IsClosed.mk
  let fibre : ℕ → Set T := fun n ↦ f ⁻¹' {OnePoint.some n}
  have clopen : ∀ n, IsClopen (fibre n) := by
    intro n
    refine IsClopen.preimage ⟨isClosed_singleton, ?_⟩ f.1.continuous
    rw [isOpen_def]
    refine ⟨fun h ↦ by simp at h, trivial⟩
  have : ({t | f t = ∞} ∪ ⋃ n, s n)ᶜ = ⋃ n, (s n)ᶜ ∩ fibre n := by
    ext x
    simp only [Set.compl_union, Set.compl_iUnion, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ⟨h, h'⟩
      obtain ⟨n', hn⟩ := Option.ne_none_iff_exists'.mp h
      exact ⟨n', h' n', hn⟩
    · intro ⟨n, hn, hn'⟩
      refine ⟨?_, ?_⟩
      rw [hn']
      simp
      intro i
      by_cases h : i = n
      rw [h]
      exact hn
      intro h'
      have := hs i ⟨x, h'⟩
      apply h
      simp [fibre] at hn'
      rw [hn'] at this
      rw [OnePoint.coe_eq_coe] at this
      symm
      exact this
  rw [this]
  refine isOpen_iUnion (fun i ↦ ?_)
  apply IsOpen.inter
  exact (hs' i).1
  exact (clopen i).2

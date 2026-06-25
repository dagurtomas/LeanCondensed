import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic

/-!
# Algebra for the proof that `ℤ` is solid

This file contains the finite-support sequence calculation used in the proof that the light
condensed abelian group of integers is solid.  The finite-difference operator
`a ↦ (fun n => a n - a (n + 1))` is an automorphism of finitely supported integer sequences, with
inverse given by finite tail sums.
-/

open scoped BigOperators

noncomputable section

namespace LightCondensed.Solid.IntProof

/-- Finitely supported integer sequences. -/
abbrev SeqZ := ℕ →₀ ℤ

/-- Left shift of finitely supported sequences: `(aₙ) ↦ (aₙ₊₁)`. -/
def seqShift : SeqZ →ₗ[ℤ] SeqZ :=
  (Finsupp.comapDomain.addMonoidHom (f := fun n : ℕ => n + 1) (by
    intro a b h
    exact Nat.succ.inj h)).toIntLinearMap

@[simp]
lemma seqShift_apply (a : SeqZ) (n : ℕ) :
    seqShift a n = a (n + 1) := by
  simp [seqShift, Finsupp.comapDomain_apply]

/-- Finite difference of finitely supported sequences: `(aₙ) ↦ (aₙ - aₙ₊₁)`. -/
def seqDiff : SeqZ →ₗ[ℤ] SeqZ :=
  LinearMap.id - seqShift

@[simp]
lemma seqDiff_apply (a : SeqZ) (n : ℕ) :
    seqDiff a n = a n - a (n + 1) := by
  simp [seqDiff]

/-- The finite tail sum function underlying `seqTailSum`. -/
def tailFun (b : SeqZ) (n : ℕ) : ℤ :=
  b.sum fun i z => if n ≤ i then z else 0

lemma tailFun_eq_sum_filter (b : SeqZ) (n : ℕ) :
    tailFun b n = ∑ i ∈ b.support.filter (fun i => n ≤ i), b i := by
  simp [tailFun, Finsupp.sum, Finset.sum_filter]

/-- Tail sums of finitely supported sequences, as an additive homomorphism. -/
def seqTailSumAddHom : SeqZ →+ SeqZ where
  toFun b :=
    Finsupp.onFinset (b.support.biUnion fun i => Finset.range (i + 1))
      (fun n => tailFun b n)
      (by
        intro n hn
        by_contra hmem
        have hzero : tailFun b n = 0 := by
          rw [tailFun_eq_sum_filter]
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_filter] at hi
          have : n ∈ b.support.biUnion (fun i => Finset.range (i + 1)) := by
            rw [Finset.mem_biUnion]
            refine ⟨i, hi.1, ?_⟩
            rw [Finset.mem_range]
            omega
          exact False.elim (hmem this)
        exact hn hzero)
  map_zero' := by
    ext n
    simp [tailFun]
  map_add' b c := by
    ext n
    simp only [Finsupp.coe_onFinset]
    dsimp [tailFun]
    rw [Finsupp.sum_add_index']
    · intro i
      by_cases h : n ≤ i <;> simp [h]
    · intro i x y
      by_cases h : n ≤ i <;> simp [h]

/-- Tail sums of finitely supported sequences. -/
def seqTailSum : SeqZ →ₗ[ℤ] SeqZ :=
  seqTailSumAddHom.toIntLinearMap

@[simp]
lemma seqTailSum_apply (b : SeqZ) (n : ℕ) :
    seqTailSum b n = ∑ i ∈ b.support.filter (fun i => n ≤ i), b i := by
  change tailFun b n = _
  exact tailFun_eq_sum_filter b n

lemma filter_ge_eq_insert_filter_gt (b : SeqZ) {n : ℕ} (hn : n ∈ b.support) :
    b.support.filter (fun i => n ≤ i) = insert n (b.support.filter (fun i => n < i)) := by
  ext i
  by_cases hin : i = n
  · subst i
    simp [hn]
  · simp [hin]
    intro _
    constructor <;> intro hi <;> omega

lemma filter_ge_eq_filter_gt (b : SeqZ) {n : ℕ} (hn : n ∉ b.support) :
    b.support.filter (fun i => n ≤ i) = b.support.filter (fun i => n < i) := by
  ext i
  by_cases hin : i = n
  · subst i
    simp [hn]
  · simp
    intro _
    constructor <;> intro hi <;> omega

lemma tailFun_sub_succ (b : SeqZ) (n : ℕ) :
    tailFun b n - tailFun b (n + 1) = b n := by
  rw [tailFun_eq_sum_filter, tailFun_eq_sum_filter]
  simp only [Nat.add_one_le_iff]
  by_cases hn : n ∈ b.support
  · rw [filter_ge_eq_insert_filter_gt b hn]
    rw [Finset.sum_insert]
    · abel
    · simp
  · rw [filter_ge_eq_filter_gt b hn]
    rw [Finsupp.notMem_support_iff.mp hn]
    abel

lemma seqDiff_seqTailSum (b : SeqZ) :
    seqDiff (seqTailSum b) = b := by
  ext n
  simp only [seqDiff_apply, seqTailSum_apply]
  rw [← tailFun_eq_sum_filter, ← tailFun_eq_sum_filter, tailFun_sub_succ]

lemma seqDiff_eq_zero {a : SeqZ} (h : seqDiff a = 0) : a = 0 := by
  by_contra ha
  obtain ⟨N, hN⟩ := Finsupp.support_nonempty_iff.mpr ha
  let M := a.support.max' ⟨N, hN⟩
  have hM : M ∈ a.support := Finset.max'_mem _ _
  have hMsucc : M + 1 ∉ a.support := by
    intro hmem
    have hle := Finset.le_max' a.support (M + 1) hmem
    omega
  have heval : seqDiff a M = (0 : SeqZ) M := by rw [h]
  simp [Finsupp.notMem_support_iff.mp hMsucc] at heval
  exact Finsupp.mem_support_iff.mp hM heval

lemma seqTailSum_seqDiff (a : SeqZ) :
    seqTailSum (seqDiff a) = a := by
  have hzero : seqDiff (seqTailSum (seqDiff a) - a) = 0 := by
    calc
      seqDiff (seqTailSum (seqDiff a) - a)
          = seqDiff (seqTailSum (seqDiff a)) - seqDiff a := by simp
      _ = seqDiff a - seqDiff a := by rw [seqDiff_seqTailSum]
      _ = 0 := by simp
  have h := seqDiff_eq_zero hzero
  exact sub_eq_zero.mp h

/-- Finite difference is an automorphism of finitely supported integer sequences. -/
noncomputable def seqDiffEquiv : SeqZ ≃ₗ[ℤ] SeqZ where
  toLinearMap := seqDiff
  invFun := seqTailSum
  left_inv := seqTailSum_seqDiff
  right_inv := seqDiff_seqTailSum

example : Function.Bijective seqDiff :=
  seqDiffEquiv.bijective

end LightCondensed.Solid.IntProof

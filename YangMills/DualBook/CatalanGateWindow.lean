/-
  PROVENANCE: YangMills.DualBook.CatalanGateWindow (R231)
  Built by Gen, Papa's hands only, in the R231 window (Tue 2026-11-24 evening CT),
  on the certified stone read byte-faithful from YangMills.DualBook.CatalanGate
  (Papa's master, the R-recipe bring-forward chain).
  SCOPE: THIS ARITHMETIC only. The proof is a pure parity reindex: Dirichlet
  character chi_{-4} evaluated on the naturals is zero on evens and (-1)^m on
  odd indices 2m+1, so the L(2, chi_{-4}) sum over n >= 1 reindexed onto the
  even sublattice is the Catalan series sum_m (-1)^m / (2m+1)^2, exactly the
  book's constant. Standard real analysis, Mathlib's own tsum reindexing
  receipts (tsum_subtype, Equiv.tsum_eq, tsum_congr) cashed at the book's
  constants. Nothing else is claimed: no functional equation, no analytic
  continuation, no Clay claim of any kind; the bench stays frozen.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.CatalanGate

namespace YangMills.DualBook

open Set

/-! ## The parity spine -/

/-- On odd naturals `2 * m + 1` the character `chiMinusFour` is exactly `(-1) ^ m`. -/
private theorem chi_odd (m : ℕ) :
    chiMinusFour ((2 * m + 1 : ℕ) : ℤ) = (-1 : ℝ) ^ m := by
  rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · -- Even m unpacks as m = t + t in this vintage; normalize to 2 * t
    rw [← Nat.two_mul t]
    have h1 : (((2 * (2 * t) + 1 : ℕ) : ℤ)) % 4 = 1 := by push_cast; omega
    have h2 : (-1 : ℝ) ^ (2 * t) = 1 := by simp [pow_mul]
    simp only [chiMinusFour]
    rw [if_pos h1]
    rw [h2]
  · -- Odd m unpacks as m = 2 * t + 1
    have h0 : (((2 * (2 * t + 1) + 1 : ℕ) : ℤ)) % 4 ≠ 1 := by push_cast; omega
    have h3 : (((2 * (2 * t + 1) + 1 : ℕ) : ℤ)) % 4 = 3 := by push_cast; omega
    have h4 : (-1 : ℝ) ^ (2 * t + 1) = -1 := by simp [pow_add, pow_mul]
    simp only [chiMinusFour]
    rw [if_neg h0, if_pos h3]
    rw [h4]

/-- On even naturals the character `chiMinusFour` vanishes. -/
private theorem chi_zero (k : ℕ) :
    chiMinusFour ((2 * k : ℕ) : ℤ) = 0 := by
  have h0 : 2 * ((k : ℕ) : ℤ) % 4 ≠ 1 := by omega
  have h3 : 2 * ((k : ℕ) : ℤ) % 4 ≠ 3 := by omega
  simp [chiMinusFour, h0, h3]

/-- The even-index equivalence `m ↦ 2 * m`, used to reindex the subtype sum. -/
private def evenEquiv : ℕ ≃ {n : ℕ // n % 2 = 0} :=
  { toFun := fun m => ⟨2 * m, by omega⟩
    invFun := fun n => n / 2
    left_inv := by intro m; simp only; omega
    right_inv := by
      intro n
      have h := n.2
      apply Subtype.ext
      simp only
      omega }

/-! ## The gate -/

-- heartbeats raised for the whnf-heavy reindex chain (R231 battery, honest note)
set_option maxHeartbeats 4000000 in
/-- `L(2, χ₋₄) = G`: the `chi_{-4}` Dirichlet L-series at 2 equals the Catalan
constant, by the parity reindex. Both summabilities are already in the book. -/
theorem catalanGate_paid : catalanGate := by
  unfold catalanGate leTwoChiMinusFour catalan
  set s : Set ℕ := {n | n % 2 = 0} with hs
  -- the cast dance that moves the book's `↑n + 1` (a ℤ-sum) onto the cast of a ℕ-sum
  have hsub : ∀ m : ℕ, ((m : ℕ) : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := fun m => by push_cast; rfl
  -- the subtype sum equals the indicator sum equals the plain sum
  have hA : ∑' (x : ↑s),
      chiMinusFour ((↑(x : ℕ) : ℤ) + 1) / ((↑((x : ℕ) + 1) : ℝ)) ^ 2
      = ∑' n,
        s.indicator (fun n => chiMinusFour ((↑n : ℤ) + 1) / ((↑(n + 1) : ℝ)) ^ 2) n :=
    tsum_subtype s (fun n => chiMinusFour ((↑n : ℤ) + 1) / ((↑(n + 1) : ℝ)) ^ 2)
  -- pointwise the indicator IS the summand: on s by definition, off s both vanish
  have hv : ∀ n, s.indicator
      (fun n => chiMinusFour ((↑n : ℤ) + 1) / ((↑(n + 1) : ℝ)) ^ 2) n
      = chiMinusFour ((↑n : ℤ) + 1) / ((↑(n + 1) : ℝ)) ^ 2 := by
    intro n
    by_cases hn : n ∈ s
    · exact Set.indicator_of_mem hn _
    · have hn' : n % 2 ≠ 0 := fun h => hn h
      rw [Set.indicator_apply, if_neg hn]
      rw [hsub n]
      rw [show n + 1 = 2 * ((n + 1) / 2) from by omega]
      rw [chi_zero]
      simp
  have hB : ∑' n,
        s.indicator (fun n => chiMinusFour ((↑n : ℤ) + 1) / ((↑(n + 1) : ℝ)) ^ 2) n
      = ∑' n,
        chiMinusFour ((↑(n : ℕ) : ℤ) + 1) / ((↑((n : ℕ) + 1) : ℝ)) ^ 2 :=
    tsum_congr hv
  -- plain sum = even-sublattice sum
  have h1 : ∑' (n : ℕ),
        chiMinusFour ((↑(n : ℕ) : ℤ) + 1) / ((↑((n : ℕ) + 1) : ℝ)) ^ 2
      = ∑' (x : ↑s),
        chiMinusFour ((↑(x : ℕ) : ℤ) + 1) / ((↑((x : ℕ) + 1) : ℝ)) ^ 2 :=
    (hA.trans hB).symm
  -- summand equality on the even sublattice
  have hsum : ∀ m : ℕ,
      chiMinusFour ((↑(2 * m) : ℤ) + 1) / ((↑(2 * m + 1) : ℝ)) ^ 2
      = (-1 : ℝ) ^ m / ((↑(2 * m + 1) : ℝ)) ^ 2 := by
    intro m
    rw [hsub (2 * m), chi_odd m]
  -- even-sublattice reindex and the summand congr, hoisted out of the calc
  have h2 : ∑' (x : ↑s),
        chiMinusFour ((↑(x : ℕ) : ℤ) + 1) / ((↑((x : ℕ) + 1) : ℝ)) ^ 2
      = ∑' (m : ℕ),
        chiMinusFour ((↑(2 * m) : ℤ) + 1) / ((↑(2 * m + 1) : ℝ)) ^ 2 :=
    (evenEquiv.tsum_eq
      (fun x => chiMinusFour ((↑(x : ℕ) : ℤ) + 1) / ((↑((x : ℕ) + 1) : ℝ)) ^ 2)).symm
  have h3 : ∑' (m : ℕ),
        chiMinusFour ((↑(2 * m) : ℤ) + 1) / ((↑(2 * m + 1) : ℝ)) ^ 2
      = ∑' (m : ℕ), (-1 : ℝ) ^ m / ((↑(2 * m + 1) : ℝ)) ^ 2 :=
    tsum_congr hsum
  -- the chain
  calc ∑' (n : ℕ), chiMinusFour ((↑(n : ℕ) : ℤ) + 1) / ((↑((n : ℕ) + 1) : ℝ)) ^ 2
      = ∑' (x : ↑s),
        chiMinusFour ((↑(x : ℕ) : ℤ) + 1) / ((↑((x : ℕ) + 1) : ℝ)) ^ 2 := h1
    _ = ∑' (m : ℕ), chiMinusFour ((↑(2 * m) : ℤ) + 1) / ((↑(2 * m + 1) : ℝ)) ^ 2 := h2
    _ = ∑' (m : ℕ), (-1 : ℝ) ^ m / ((↑(2 * m + 1) : ℝ)) ^ 2 := h3
    _ = ∑' (n : ℕ), (-1 : ℝ) ^ n / ((↑(2 * n + 1) : ℝ)) ^ 2 := rfl

end YangMills.DualBook

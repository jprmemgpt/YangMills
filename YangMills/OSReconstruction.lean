import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.OsterwalderSchrader

/-!
# Module 12: OSReconstruction (Lean 4 + Mathlib4)
Formalizes the Osterwalder–Schrader Hilbert-space reconstruction core and transfer-matrix
mass gap contraction theorem:
1. Positive semidefinite OS2 bilinear form `OSBilinearSpace`, exact Cauchy–Schwarz
   inequality (`os_cauchy_schwarz`), and null-space characterization (`os_null_iff_orthog`).
2. Construction of the physical quotient pre-Hilbert space `OSQuotient` with lifted inner
   product `osInner` and strict positive definiteness (`osInner_eq_zero_iff`).
3. Symmetric time-translation transfer semigroup `OSTransferSemigroup` and the iterated
   Cauchy–Schwarz inequality (`os_iterated_cauchy_schwarz`).
4. Exact OS contraction theorem (`os_transfer_contraction`): every uniformly bounded
   symmetric transfer operator satisfies `‖T x‖² ≤ ‖x‖²` and preserves the OS null space.
5. Exact physical Hilbert-space mass gap (`os_clustering_implies_transfer_gap`):
   OS4 exponential clustering `‖T^n x‖² ≤ C exp(-2 m₀ n)` implies `‖T x‖² ≤ exp(-2 m₀) ‖x‖²`.
-/

namespace YangMills

/-! ## 1. OS2 Bilinear Space, Cauchy–Schwarz, and Physical Quotient Pre-Hilbert Space -/

/-- Real vector space of positive-time observables equipped with the OS2 reflection-positive
    symmetric bilinear form `B(F, G) = ⟨Θ F, G⟩`. -/
structure OSBilinearSpace (V : Type*) where
  zero : V
  add : V → V → V
  neg : V → V
  smul : ℝ → V → V
  B : V → V → ℝ
  symm : ∀ x y, B x y = B y x
  add_left : ∀ x y z, B (add x y) z = B x z + B y z
  neg_left : ∀ x y, B (neg x) y = -B x y
  smul_left : ∀ c x y, B (smul c x) y = c * B x y
  zero_left : ∀ y, B zero y = 0
  pos_semidef : ∀ x, 0 ≤ B x x

namespace OSBilinearSpace

variable {V : Type*} (S : OSBilinearSpace V)

/-- Difference `x - y := x + (-y)` in `V`. -/
def sub (x y : V) : V := S.add x (S.neg y)

theorem add_right (x y z : V) : S.B x (S.add y z) = S.B x y + S.B x z := by
  rw [S.symm, S.add_left, S.symm y x, S.symm z x]

theorem neg_right (x y : V) : S.B x (S.neg y) = -S.B x y := by
  rw [S.symm, S.neg_left, S.symm y x]

theorem smul_right (c : ℝ) (x y : V) : S.B x (S.smul c y) = c * S.B x y := by
  rw [S.symm, S.smul_left, S.symm y x]

theorem zero_right (x : V) : S.B x S.zero = 0 := by
  rw [S.symm, S.zero_left]

theorem sub_left (x y z : V) : S.B (S.sub x y) z = S.B x z - S.B y z := by
  unfold sub
  rw [S.add_left, S.neg_left]
  ring

theorem sub_right (x y z : V) : S.B x (S.sub y z) = S.B x y - S.B x z := by
  unfold sub
  rw [S.add_right, S.neg_right]
  ring

theorem quad_expand (a b : ℝ) (x y : V) :
    S.B (S.add (S.smul a x) (S.smul b y)) (S.add (S.smul a x) (S.smul b y)) =
      a ^ 2 * S.B x x + 2 * a * b * S.B x y + b ^ 2 * S.B y y := by
  rw [S.add_left, S.add_right, S.add_right, S.smul_left, S.smul_left, S.smul_left, S.smul_left,
    S.smul_right, S.smul_right, S.smul_right, S.smul_right, S.symm y x]
  ring

/-- Exact Cauchy–Schwarz inequality from OS2 reflection positivity: `B(x, y)² ≤ B(x, x) B(y, y)`. -/
theorem os_cauchy_schwarz (x y : V) : S.B x y ^ 2 ≤ S.B x x * S.B y y := by
  have hy := S.pos_semidef y
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · have hxy0 : S.B x y = 0 := by
      by_contra hne
      have h2ne : 2 * S.B x y ≠ 0 := mul_ne_zero two_ne_zero hne
      let b : ℝ := -(S.B x x + 1) / (2 * S.B x y)
      have hpos := S.pos_semidef (S.add (S.smul 1 x) (S.smul b y))
      rw [S.quad_expand] at hpos
      have hmid : 2 * 1 * b * S.B x y = -(S.B x x + 1) := by
        calc
          2 * 1 * b * S.B x y = (-(S.B x x + 1) / (2 * S.B x y)) * (2 * S.B x y) := by
            dsimp only [b]; ring
          _ = -(S.B x x + 1) := div_mul_cancel₀ _ h2ne
      rw [← hy0] at hpos
      linarith
    rw [hxy0, ← hy0]
    norm_num
  · have hpos := S.pos_semidef (S.add (S.smul (S.B y y) x) (S.smul (-S.B x y) y))
    rw [S.quad_expand] at hpos
    have hfac :
        S.B y y ^ 2 * S.B x x + 2 * S.B y y * -S.B x y * S.B x y + (-S.B x y) ^ 2 * S.B y y =
          S.B y y * (S.B x x * S.B y y - S.B x y ^ 2) := by ring
    rw [hfac] at hpos
    nlinarith

/-- Null-space characterization: `B(x, x) = 0` iff `x` is orthogonal to every `y ∈ V`. -/
theorem os_null_iff_orthog (x : V) : S.B x x = 0 ↔ ∀ y, S.B x y = 0 := by
  constructor
  · intro hx y
    have hcs := S.os_cauchy_schwarz x y
    rw [hx, zero_mul] at hcs
    have hsq : S.B x y ^ 2 = 0 := le_antisymm hcs (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsq
  · intro hall
    exact hall x

/-- OS null equivalence relation: `x ≈ y` iff `B(x - y, x - y) = 0`. -/
def osEquiv (x y : V) : Prop := S.B (S.sub x y) (S.sub x y) = 0

theorem osEquiv_refl (x : V) : S.osEquiv x x := by
  unfold osEquiv
  rw [S.sub_left]
  ring

theorem osEquiv_symm {x y : V} (h : S.osEquiv x y) : S.osEquiv y x := by
  unfold osEquiv at h ⊢
  have h1 : S.B (S.sub y x) (S.sub y x) = S.B (S.sub x y) (S.sub x y) := by
    rw [S.sub_left, S.sub_right, S.sub_right, S.sub_left, S.sub_right, S.sub_right, S.symm y x]
    ring
  rw [h1, h]

theorem osEquiv_trans {x y z : V} (h1 : S.osEquiv x y) (h2 : S.osEquiv y z) : S.osEquiv x z := by
  have hxy := (S.os_null_iff_orthog (S.sub x y)).mp h1
  have hyz := (S.os_null_iff_orthog (S.sub y z)).mp h2
  unfold osEquiv
  have heq : S.B (S.sub x z) (S.sub x z) =
      S.B (S.sub x y) (S.sub x z) + S.B (S.sub y z) (S.sub x z) := by
    rw [S.sub_left, S.sub_left, S.sub_left]
    ring
  rw [heq, hxy, hyz, add_zero]

/-- Setoid of OS null equivalence classes. -/
def osSetoid : Setoid V where
  r := S.osEquiv
  iseqv := ⟨S.osEquiv_refl, fun h => S.osEquiv_symm h, fun h1 h2 => S.osEquiv_trans h1 h2⟩

end OSBilinearSpace

/-- The reconstructed physical pre-Hilbert quotient space `ℋ₀ = ℰ₊ / 𝒩`. -/
def OSQuotient {V : Type*} (S : OSBilinearSpace V) := Quotient S.osSetoid

/-- Lifted physical inner product on `OSQuotient S`. -/
def osInner {V : Type*} (S : OSBilinearSpace V) : OSQuotient S → OSQuotient S → ℝ :=
  Quotient.lift₂ S.B (by
    intro x₁ y₁ x₂ y₂ hx hy
    have hx0 := (S.os_null_iff_orthog (S.sub x₁ x₂)).mp hx
    have hy0 := (S.os_null_iff_orthog (S.sub y₁ y₂)).mp hy
    have hdiff : S.B x₁ y₁ - S.B x₂ y₂ = S.B (S.sub x₁ x₂) y₁ + S.B x₂ (S.sub y₁ y₂) := by
      rw [S.sub_left, S.sub_right]
      ring
    rw [hx0 y₁, S.symm x₂ (S.sub y₁ y₂), hy0 x₂, add_zero] at hdiff
    linarith)

theorem osInner_symm {V : Type*} (S : OSBilinearSpace V) (ψ φ : OSQuotient S) :
    osInner S ψ φ = osInner S φ ψ := by
  refine Quotient.inductionOn₂ ψ φ ?_
  intro x y
  exact S.symm x y

theorem osInner_nonneg {V : Type*} (S : OSBilinearSpace V) (ψ : OSQuotient S) :
    0 ≤ osInner S ψ ψ := by
  refine Quotient.inductionOn ψ ?_
  intro x
  exact S.pos_semidef x

/-- Strict positive definiteness of the reconstructed physical inner product on `OSQuotient S`:
    `⟨ψ, ψ⟩ = 0 ↔ ψ = 0`. -/
theorem osInner_eq_zero_iff {V : Type*} (S : OSBilinearSpace V) (ψ : OSQuotient S) :
    osInner S ψ ψ = 0 ↔ ψ = Quotient.mk S.osSetoid S.zero := by
  refine Quotient.inductionOn ψ ?_
  intro x
  constructor
  · intro h
    change S.B x x = 0 at h
    apply Quotient.sound
    change S.B (S.sub x S.zero) (S.sub x S.zero) = 0
    rw [S.sub_left, S.sub_right, S.sub_right, S.zero_left, S.zero_left, S.zero_right]
    linarith
  · intro h
    have heq : S.B (S.sub x S.zero) (S.sub x S.zero) = 0 := Quotient.exact h
    rw [S.sub_left, S.sub_right, S.sub_right, S.zero_left, S.zero_left, S.zero_right] at heq
    change S.B x x = 0
    linarith

/-! ## 2. Transfer-Matrix Semigroup, Contraction, and Physical Mass Gap -/

/-- Bernoulli's inequality: `1 + n δ ≤ (1 + δ)^n` for `δ ≥ 0`. -/
theorem bernoulli_ineq (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    1 + (n : ℝ) * δ ≤ (1 + δ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hmul : (1 + (n : ℝ) * δ) * (1 + δ) ≤ (1 + δ) ^ n * (1 + δ) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hsq : 0 ≤ (n : ℝ) * δ ^ 2 := by positivity
    nlinarith

/-- Elementary growth bound: `k ≤ 2^k` for every `k : ℕ`. -/
theorem nat_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- If `r ≥ 0` satisfies `r^(2^k) ≤ M` for every `k : ℕ`, then `r ≤ 1`. -/
theorem le_one_of_two_pow_bounded {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hb : ∀ k : ℕ, r ^ (2 ^ k) ≤ M) : r ≤ 1 := by
  by_contra hnot
  have hr1 : 1 < r := lt_of_not_ge hnot
  set δ : ℝ := r - 1
  have hδ : 0 < δ := by linarith
  set k : ℕ := Nat.floor (M / δ) + 1
  have hk : M / δ < (k : ℝ) := by simpa [k] using Nat.lt_floor_add_one (M / δ)
  have hMlt : M < (k : ℝ) * δ := by
    have h1 := mul_lt_mul_of_pos_right hk hδ
    rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at h1
  have hpow : (k : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast nat_le_two_pow k
  have hbern := bernoulli_ineq δ (le_of_lt hδ) (2 ^ k)
  have hr_eq : 1 + δ = r := by dsimp only [δ]; ring
  rw [hr_eq] at hbern
  have hbk := hb k
  have hkd : (k : ℝ) * δ ≤ ((2 ^ k : ℕ) : ℝ) * δ :=
    mul_le_mul_of_nonneg_right hpow (le_of_lt hδ)
  linarith

/-- Symmetric discrete time-translation transfer semigroup `T(n)` on an OS2 bilinear space. -/
structure OSTransferSemigroup {V : Type*} (S : OSBilinearSpace V) where
  T : ℕ → V → V
  T_zero : ∀ x, T 0 x = x
  T_add : ∀ s t x, T (s + t) x = T s (T t x)
  T_symm : ∀ t x y, S.B (T t x) y = S.B x (T t y)

/-- Single-step OS squaring inequality: `‖T^m x‖⁴ ≤ ‖x‖² · ‖T^(2m) x‖²`. -/
theorem os_transfer_step_sq {V : Type*} {S : OSBilinearSpace V}
    (G : OSTransferSemigroup S) (m : ℕ) (x : V) :
    S.B (G.T m x) (G.T m x) ^ 2 ≤ S.B x x * S.B (G.T (2 * m) x) (G.T (2 * m) x) := by
  have heq : S.B (G.T m x) (G.T m x) = S.B x (G.T (2 * m) x) := by
    rw [G.T_symm, ← G.T_add, two_mul]
  rw [heq]
  exact S.os_cauchy_schwarz x (G.T (2 * m) x)

/-- Iterated Osterwalder–Schrader Cauchy–Schwarz inequality for all `k : ℕ`:
    `‖T x‖^(2^(k+1)) ≤ ‖x‖^(2^(k+1) - 2) · ‖T^(2^k) x‖²`. -/
theorem os_iterated_cauchy_schwarz {V : Type*} {S : OSBilinearSpace V}
    (G : OSTransferSemigroup S) (x : V) (k : ℕ) :
    S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) ≤
      S.B x x ^ (2 ^ k - 1) * S.B (G.T (2 ^ k) x) (G.T (2 ^ k) x) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h1 : 0 ≤ S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) :=
      pow_nonneg (S.pos_semidef _) _
    have hsq := mul_self_le_mul_self h1 ih
    have hstep := os_transfer_step_sq G (2 ^ k) x
    have hb_nonneg : 0 ≤ S.B x x ^ (2 ^ k - 1) := pow_nonneg (S.pos_semidef _) _
    have hexp_lhs :
        S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) * S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) =
          S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ (k + 1)) := by
      rw [← pow_add, pow_succ, mul_two]
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hpow_nat : (2 ^ k - 1) + (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
      rw [pow_succ]; omega
    have h2m : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
    calc
      S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ (k + 1))
        = S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) * S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) :=
            hexp_lhs.symm
      _ ≤ (S.B x x ^ (2 ^ k - 1) * S.B (G.T (2 ^ k) x) (G.T (2 ^ k) x)) *
            (S.B x x ^ (2 ^ k - 1) * S.B (G.T (2 ^ k) x) (G.T (2 ^ k) x)) := hsq
      _ = (S.B x x ^ (2 ^ k - 1) * S.B x x ^ (2 ^ k - 1)) *
            S.B (G.T (2 ^ k) x) (G.T (2 ^ k) x) ^ 2 := by ring
      _ ≤ (S.B x x ^ (2 ^ k - 1) * S.B x x ^ (2 ^ k - 1)) *
            (S.B x x * S.B (G.T (2 * 2 ^ k) x) (G.T (2 * 2 ^ k) x)) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hb_nonneg hb_nonneg)
      _ = S.B x x ^ ((2 ^ k - 1) + (2 ^ k - 1) + 1) *
            S.B (G.T (2 * 2 ^ k) x) (G.T (2 * 2 ^ k) x) := by
          rw [pow_add, pow_add, pow_one]; ring
      _ = S.B x x ^ (2 ^ (k + 1) - 1) * S.B (G.T (2 ^ (k + 1)) x) (G.T (2 ^ (k + 1)) x) := by
          rw [hpow_nat, h2m]

/-- Exact Osterwalder–Schrader contraction theorem: any uniformly bounded symmetric transfer
    operator automatically satisfies `‖T x‖² ≤ ‖x‖²` (`‖T‖ ≤ 1`, i.e., Hamiltonian `H ≥ 0`). -/
theorem os_transfer_contraction {V : Type*} {S : OSBilinearSpace V}
    (G : OSTransferSemigroup S) (x : V) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, S.B (G.T n x) (G.T n x) ≤ C) :
    S.B (G.T 1 x) (G.T 1 x) ≤ S.B x x := by
  have hx := S.pos_semidef x
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · have h1 := os_transfer_step_sq G 1 x
    rw [← hx0, zero_mul] at h1
    have hzero : S.B (G.T 1 x) (G.T 1 x) = 0 :=
      sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
    rw [hzero, ← hx0]
  · set r : ℝ := S.B (G.T 1 x) (G.T 1 x) / S.B x x
    have hr : 0 ≤ r := div_nonneg (S.pos_semidef _) (le_of_lt hxpos)
    have hM : 0 ≤ C / S.B x x := div_nonneg hC (le_of_lt hxpos)
    have hb : ∀ k : ℕ, r ^ (2 ^ k) ≤ C / S.B x x := by
      intro k
      have hiter := os_iterated_cauchy_schwarz G x k
      have hbk := hbound (2 ^ k)
      have hpow_pos : 0 < S.B x x ^ (2 ^ k) := pow_pos hxpos _
      have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hsplit : S.B x x ^ (2 ^ k) = S.B x x ^ (2 ^ k - 1) * S.B x x := by
        rw [← pow_succ, Nat.sub_add_cancel h2k]
      rw [div_pow, div_le_div_iff₀ hpow_pos hxpos]
      have h1 : S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) ≤ S.B x x ^ (2 ^ k - 1) * C :=
        le_trans hiter (mul_le_mul_of_nonneg_left hbk (pow_nonneg (le_of_lt hxpos) _))
      calc
        S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) * S.B x x
          ≤ (S.B x x ^ (2 ^ k - 1) * C) * S.B x x :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hxpos)
        _ = C * (S.B x x ^ (2 ^ k - 1) * S.B x x) := by ring
        _ = C * S.B x x ^ (2 ^ k) := by rw [← hsplit]
    have hr1 : r ≤ 1 := le_one_of_two_pow_bounded hr hM hb
    exact (div_le_one hxpos).mp hr1

/-- Null-space invariance: `T` maps OS null vectors to OS null vectors, so it descends
    canonically to the physical Hilbert space `OSQuotient S`. -/
theorem os_transfer_preserves_null {V : Type*} {S : OSBilinearSpace V}
    (G : OSTransferSemigroup S) (x : V) (hx : S.B x x = 0) :
    S.B (G.T 1 x) (G.T 1 x) = 0 := by
  have h1 := os_transfer_step_sq G 1 x
  rw [hx, zero_mul] at h1
  exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))

/-- Exact physical Hilbert-space mass gap from OS4 exponential clustering:
    if `‖T^n x‖² ≤ C exp(-2 m₀ n)` for all `n : ℕ`, then `‖T x‖² ≤ exp(-2 m₀) ‖x‖²`
    (equivalently `H ≥ m₀` on the cyclic subspace generated by `x`). -/
theorem os_clustering_implies_transfer_gap {V : Type*} {S : OSBilinearSpace V}
    (G : OSTransferSemigroup S) (x : V) (C m0 : ℝ) (hC : 0 ≤ C)
    (hclust : ∀ n : ℕ, S.B (G.T n x) (G.T n x) ≤ C * Real.exp (-2 * m0 * (n : ℝ))) :
    S.B (G.T 1 x) (G.T 1 x) ≤ Real.exp (-2 * m0) * S.B x x := by
  have hx := S.pos_semidef x
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · have hzero := os_transfer_preserves_null G x hx0.symm
    rw [hzero, ← hx0, mul_zero]
  · set r : ℝ := Real.exp (2 * m0) * S.B (G.T 1 x) (G.T 1 x) / S.B x x
    have hr : 0 ≤ r :=
      div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) (S.pos_semidef _)) (le_of_lt hxpos)
    have hM : 0 ≤ C / S.B x x := div_nonneg hC (le_of_lt hxpos)
    have hb : ∀ k : ℕ, r ^ (2 ^ k) ≤ C / S.B x x := by
      intro k
      have hiter := os_iterated_cauchy_schwarz G x k
      have hbk := hclust (2 ^ k)
      have hpow_pos : 0 < S.B x x ^ (2 ^ k) := pow_pos hxpos _
      have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hsplit : S.B x x ^ (2 ^ k) = S.B x x ^ (2 ^ k - 1) * S.B x x := by
        rw [← pow_succ, Nat.sub_add_cancel h2k]
      have hexp_pow : Real.exp (2 * m0) ^ (2 ^ k) = Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) := by
        rw [← Real.exp_natCast_mul]
        congr 1; ring
      have hexp_cancel :
          Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) * Real.exp (-2 * m0 * ((2 ^ k : ℕ) : ℝ)) = 1 := by
        rw [← Real.exp_add]
        have hzero : 2 * m0 * ((2 ^ k : ℕ) : ℝ) + -2 * m0 * ((2 ^ k : ℕ) : ℝ) = 0 := by ring
        rw [hzero, Real.exp_zero]
      rw [div_pow, mul_pow, hexp_pow, div_le_div_iff₀ hpow_pos hxpos]
      have h1 : S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) ≤
          S.B x x ^ (2 ^ k - 1) * (C * Real.exp (-2 * m0 * ((2 ^ k : ℕ) : ℝ))) :=
        le_trans hiter (mul_le_mul_of_nonneg_left hbk (pow_nonneg (le_of_lt hxpos) _))
      have h2 :
          Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) * S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) ≤
            S.B x x ^ (2 ^ k - 1) * C := by
        calc
          Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) * S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k)
            ≤ Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) *
                (S.B x x ^ (2 ^ k - 1) * (C * Real.exp (-2 * m0 * ((2 ^ k : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
          _ = S.B x x ^ (2 ^ k - 1) * C *
                (Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) *
                  Real.exp (-2 * m0 * ((2 ^ k : ℕ) : ℝ))) := by ring
          _ = S.B x x ^ (2 ^ k - 1) * C := by rw [hexp_cancel, mul_one]
      calc
        Real.exp (2 * m0 * ((2 ^ k : ℕ) : ℝ)) * S.B (G.T 1 x) (G.T 1 x) ^ (2 ^ k) * S.B x x
          ≤ (S.B x x ^ (2 ^ k - 1) * C) * S.B x x :=
            mul_le_mul_of_nonneg_right h2 (le_of_lt hxpos)
        _ = C * (S.B x x ^ (2 ^ k - 1) * S.B x x) := by ring
        _ = C * S.B x x ^ (2 ^ k) := by rw [← hsplit]
    have hr1 : r ≤ 1 := le_one_of_two_pow_bounded hr hM hb
    have hmul : Real.exp (2 * m0) * S.B (G.T 1 x) (G.T 1 x) ≤ S.B x x :=
      (div_le_one hxpos).mp hr1
    have hinv : Real.exp (-2 * m0) * Real.exp (2 * m0) = 1 := by
      rw [← Real.exp_add]
      have h0 : -2 * m0 + 2 * m0 = 0 := by ring
      rw [h0, Real.exp_zero]
    calc
      S.B (G.T 1 x) (G.T 1 x)
        = (Real.exp (-2 * m0) * Real.exp (2 * m0)) * S.B (G.T 1 x) (G.T 1 x) := by
            rw [hinv, one_mul]
      _ = Real.exp (-2 * m0) * (Real.exp (2 * m0) * S.B (G.T 1 x) (G.T 1 x)) := by ring
      _ ≤ Real.exp (-2 * m0) * S.B x x :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt (Real.exp_pos _))

end YangMills

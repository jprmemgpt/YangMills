import YangMills.YangMillsMaster

namespace YangMills

section GapDischarge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

noncomputable def vacOrthogProj (L : LinearOSBilinearSpace V)
    (Ω ψ : PhysicalOSHilbertSpace L) : PhysicalOSHilbertSpace L :=
  ψ - inner ℝ Ω ψ • Ω

theorem vacOrthogProj_continuous (L : LinearOSBilinearSpace V)
    (Ω : PhysicalOSHilbertSpace L) :
    Continuous (vacOrthogProj L Ω) :=
  by
    unfold vacOrthogProj
    have h1 : Continuous (fun ψ : PhysicalOSHilbertSpace L => inner ℝ Ω ψ) := continuous_const.inner continuous_id
    exact continuous_id.sub (h1.smul continuous_const)

theorem vacOrthogProj_eq_self (L : LinearOSBilinearSpace V)
    (Ω ψ : PhysicalOSHilbertSpace L) (hψ : ψ ∈ VacuumOrthog Ω) :
    vacOrthogProj L Ω ψ = ψ := by
  have h0 : inner ℝ Ω ψ = 0 := by
    unfold VacuumOrthog at hψ
    exact hψ
  simp [vacOrthogProj, h0]

theorem osMk_sub_smul_coe (L : LinearOSBilinearSpace V) (x vac : V) (c : ℝ) :
    ((osMk L (x - c • vac) : LinearOSQuotient L) : PhysicalOSHilbertSpace L) =
      ((osMk L x : LinearOSQuotient L) : PhysicalOSHilbertSpace L) -
        c • ((osMk L vac : LinearOSQuotient L) : PhysicalOSHilbertSpace L) := by
  have hq : osMk L (x - c • vac) = osMk L x - c • osMk L vac := by rw [sub_eq_add_neg, sub_eq_add_neg]; rfl
  rw [hq]
  change (UniformSpace.Completion.coe' (osMk L x - c • osMk L vac) : PhysicalOSHilbertSpace L) = _
  rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul]

theorem discharge_hgap_from_connected_os4
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (T : ℕ → V → V)
    (T_zero : ∀ x, T 0 x = x)
    (T_add : ∀ s t x, T (s + t) x = T s (T t x))
    (T_add_vec : ∀ t x y, T t (x + y) = T t x + T t y)
    (T_smul_vec : ∀ t (c : ℝ) x, T t (c • x) = c • T t x)
    (T_symm : ∀ n t x y, (Lseq n).B (T t x) y = (Lseq n).B x (T t y))
    (hb : (continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm).UniformlyBounded)
    (vac : V) (m0 : ℝ)
    (hclust_conn : ∀ x : V, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t : ℕ, (Lseq n).B (T t (x - Binf vac x • vac)) (T t (x - Binf vac x • vac)) ≤
        C * Real.exp (-2 * m0 * (t : ℝ))) :
    let Lc := continuumOSBilinearSpace Lseq Binf htend
    let Gc := continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm
    let Ω : PhysicalOSHilbertSpace Lc := (osMk Lc vac : LinearOSQuotient Lc)
    ∀ ψ ∈ VacuumOrthog Ω,
      ‖Gc.physicalTransferOp hb ψ‖ ≤ Real.exp (-m0) * ‖ψ‖ := by
  intro Lc Gc Ω ψ hψ
  have hdense : ∀ φ : PhysicalOSHilbertSpace Lc,
      ‖Gc.physicalTransferOp hb (vacOrthogProj Lc Ω φ)‖ ≤
        Real.exp (-m0) * ‖vacOrthogProj Lc Ω φ‖ := by
    have hclosed : IsClosed {φ : PhysicalOSHilbertSpace Lc |
        ‖Gc.physicalTransferOp hb (vacOrthogProj Lc Ω φ)‖ ≤
          Real.exp (-m0) * ‖vacOrthogProj Lc Ω φ‖} := by
      have hcontL : Continuous (fun φ => ‖Gc.physicalTransferOp hb (vacOrthogProj Lc Ω φ)‖) :=
        ((liftOperator_continuous (Gc.quotientTransferOp hb)).comp
          (vacOrthogProj_continuous Lc Ω)).norm
      have hcontR : Continuous (fun φ => Real.exp (-m0) * ‖vacOrthogProj Lc Ω φ‖) :=
        continuous_const.mul (vacOrthogProj_continuous Lc Ω).norm
      exact isClosed_le hcontL hcontR
    refine fun φ =>
      UniformSpace.Completion.denseRange_coe.induction_on φ hclosed (fun q => ?_)
    refine Quotient.inductionOn q (fun x => ?_)
    have hproj : vacOrthogProj Lc Ω ((osMk Lc x : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc) =
        ((osMk Lc (x - Binf vac x • vac) : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc) := by
      unfold vacOrthogProj
      rw [osMk_sub_smul_coe]
      have hinner : inner ℝ Ω ((osMk Lc x : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc) =
          Binf vac x := physicalOSHilbert_inner_mk Lc vac x
      rw [hinner]
    change ‖Gc.physicalTransferOp hb
        (vacOrthogProj Lc Ω ((osMk Lc x : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc))‖ ≤
      Real.exp (-m0) * ‖vacOrthogProj Lc Ω
        ((osMk Lc x : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc)‖
    rw [hproj]
    obtain ⟨C, hC, hc⟩ := hclust_conn x
    have hqgap := continuum_transfer_mass_gap Lseq Binf htend T T_zero T_add T_add_vec
      T_smul_vec T_symm hb (x - Binf vac x • vac) C m0 hC hc
    change ‖liftOperator (Gc.quotientTransferOp hb)
        ((osMk Lc (x - Binf vac x • vac) : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc)‖ ≤
      Real.exp (-m0) * ‖((osMk Lc (x - Binf vac x • vac) : LinearOSQuotient Lc) : PhysicalOSHilbertSpace Lc)‖
    rw [liftOperator_coe, hilbertCompletion_embed_isometry, hilbertCompletion_embed_isometry]
    exact hqgap
  have hself := vacOrthogProj_eq_self Lc Ω ψ hψ
  have hbound := hdense ψ
  rwa [hself] at hbound

theorem yang_mills_master_discharged
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (T : ℕ → V → V)
    (T_zero : ∀ x, T 0 x = x)
    (T_add : ∀ s t x, T (s + t) x = T s (T t x))
    (T_add_vec : ∀ t x y, T t (x + y) = T t x + T t y)
    (T_smul_vec : ∀ t (c : ℝ) x, T t (c • x) = c • T t x)
    (T_symm : ∀ n t x y, (Lseq n).B (T t x) y = (Lseq n).B x (T t y))
    (hb : (continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm).UniformlyBounded)
    (L K : ℕ) (hL : 3 ≤ L)
    (δ : ℕ → ℝ) (a0 κ₀ b0 gStarSq LambdaRG : ℝ)
    (hκ₀ : (61516 : ℝ) / 10000 ≤ κ₀)
    (hδ0 : ∀ j : ℕ, 0 ≤ δ j) (ha0 : 0 ≤ a0)
    (hstep : ∀ j : ℕ, δ j ≤ a0 * ((1 : ℝ) / 4) ^ j)
    (ha0_peierls : a0 ≤ (3 : ℝ) / 4 * (Real.exp (-((L * L : ℕ) : ℝ)) / (1 - Real.exp (-1))))
    (hb0 : 0 < b0) (hgStar : 0 < gStarSq) (hLambda : 0 < LambdaRG)
    (vac : V)
    (hvac : (continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm).physicalTransferOp hb
      ((osMk (continuumOSBilinearSpace Lseq Binf htend) vac : LinearOSQuotient (continuumOSBilinearSpace Lseq Binf htend)) :
        PhysicalOSHilbertSpace (continuumOSBilinearSpace Lseq Binf htend)) =
      ((osMk (continuumOSBilinearSpace Lseq Binf htend) vac : LinearOSQuotient (continuumOSBilinearSpace Lseq Binf htend)) :
        PhysicalOSHilbertSpace (continuumOSBilinearSpace Lseq Binf htend)))
    (hclust_conn : ∀ x : V, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t : ℕ, (Lseq n).B (T t (x - Binf vac x • vac)) (T t (x - Binf vac x • vac)) ≤
        C * Real.exp (-2 * (corridorMassFloor κ₀ b0 gStarSq LambdaRG) * (t : ℝ))) :
    let Lc := continuumOSBilinearSpace Lseq Binf htend
    let Gc := continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm
    let Ω : PhysicalOSHilbertSpace Lc := (osMk Lc vac : LinearOSQuotient Lc)
    let epsCum := ∑ j ∈ Finset.range K, δ j
    let m0 := corridorMassFloor κ₀ b0 gStarSq LambdaRG
    (∃ g h : SU2, g * h ≠ h * g) ∧
    (∃ g h : SU3, g * h ≠ h * g) ∧
    0 < neumannGapFloor L ∧
    InKPCorridor κ₀ epsCum ∧
    0 < m0 ∧
    CompleteSpace (PhysicalOSHilbertSpace Lc) ∧
    (∀ ψ φ : PhysicalOSHilbertSpace Lc,
      inner ℝ (Gc.physicalTransferOp hb ψ) φ = inner ℝ ψ (Gc.physicalTransferOp hb φ)) ∧
    (∀ ψ : PhysicalOSHilbertSpace Lc,
      ‖Gc.physicalTransferOp hb ψ‖ ≤ ‖ψ‖) ∧
    (∀ ψ ∈ VacuumOrthog Ω, Gc.physicalTransferOp hb ψ ∈ VacuumOrthog Ω) ∧
    (∀ (E : ℝ), E < m0 → ∀ ψ ∈ VacuumOrthog Ω,
      (Real.exp (-E) - Real.exp (-m0)) * ‖ψ‖ ≤
        ‖Gc.physicalTransferOp hb ψ - Real.exp (-E) • ψ‖) := by
  intro Lc Gc Ω epsCum m0
  have hgap := discharge_hgap_from_connected_os4 Lseq Binf htend T T_zero T_add T_add_vec
    T_smul_vec T_symm hb vac m0 hclust_conn
  exact yang_mills_existence_and_mass_gap_master Lseq Binf htend T T_zero T_add T_add_vec
    T_smul_vec T_symm hb L K hL δ a0 κ₀ b0 gStarSq LambdaRG hκ₀ hδ0 ha0 hstep ha0_peierls
    hb0 hgStar hLambda Ω hvac hgap

end GapDischarge

end YangMills

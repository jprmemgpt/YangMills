
/-! ## 2. Pre-Hilbert Space Structure on `LinearOSQuotient` -/

section QuotientPreHilbert

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (L : LinearOSBilinearSpace V)

/-- Abbreviation for the underlying `OSBilinearSpace V`. -/
abbrev osSpace : OSBilinearSpace V := L.toOSBilinearSpace

/-- Abbreviation for the OS quotient `V / 𝒩`. -/
abbrev LinearOSQuotient := OSQuotient (osSpace L)

theorem osEquiv_add {x₁ x₂ y₁ y₂ : V}
    (hx : (osSpace L).osEquiv x₁ x₂) (hy : (osSpace L).osEquiv y₁ y₂) :
    (osSpace L).osEquiv (x₁ + y₁) (x₂ + y₂) := by
  have hx0 := ((osSpace L).os_null_iff_orthog ((osSpace L).sub x₁ x₂)).mp hx
  have hy0 := ((osSpace L).os_null_iff_orthog ((osSpace L).sub y₁ y₂)).mp hy
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B ((x₁ + y₁) + -(x₂ + y₂)) ((x₁ + y₁) + -(x₂ + y₂)) = 0
  have hsplit : (x₁ + y₁) + -(x₂ + y₂) = (x₁ + -x₂) + (y₁ + -y₂) := by abel
  rw [hsplit, L.add_left]
  exact add_eq_zero.mpr ⟨hx0 _, hy0 _⟩

theorem osEquiv_neg {x₁ x₂ : V} (hx : (osSpace L).osEquiv x₁ x₂) :
    (osSpace L).osEquiv (-x₁) (-x₂) := by
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B (-x₁ + -(-x₂)) (-x₁ + -(-x₂)) = 0
  have hsplit : -x₁ + -(-x₂) = -(x₁ + -x₂) := by abel
  rw [hsplit, (osSpace L).neg_left, (osSpace L).neg_right]
  change -(-L.B (x₁ + -x₂) (x₁ + -x₂)) = 0
  rw [hx]
  ring

theorem osEquiv_smul (c : ℝ) {x₁ x₂ : V} (hx : (osSpace L).osEquiv x₁ x₂) :
    (osSpace L).osEquiv (c • x₁) (c • x₂) := by
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B (c • x₁ + -(c • x₂)) (c • x₁ + -(c • x₂)) = 0
  have hsplit : c • x₁ + -(c • x₂) = c • (x₁ + -x₂) := by rw [smul_add, smul_neg]
  rw [hsplit, L.smul_left, (osSpace L).smul_right]
  change c * (c * L.B (x₁ + -x₂) (x₁ + -x₂)) = 0
  rw [hx]
  ring

/-- Addition on `LinearOSQuotient L`. -/
def osQuotientAdd : LinearOSQuotient L → LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map₂ (· + ·) (fun _ _ hx _ _ hy => osEquiv_add L hx hy)

/-- Zero element on `LinearOSQuotient L`. -/
def osQuotientZero : LinearOSQuotient L :=
  Quotient.mk (osSpace L).osSetoid 0

/-- Negation on `LinearOSQuotient L`. -/
def osQuotientNeg : LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map (- ·) (fun _ _ hx => osEquiv_neg L hx)

/-- Real scalar multiplication on `LinearOSQuotient L`. -/
def osQuotientSMul (c : ℝ) : LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map (c • ·) (fun _ _ hx => osEquiv_smul L c hx)

instance instAddCommGroupLinearOSQuotient : AddCommGroup (LinearOSQuotient L) where
  add := osQuotientAdd L
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun x y z => ?_
    exact Quotient.sound (by rw [add_assoc]; exact (osSpace L).osEquiv_refl _)
  zero := osQuotientZero L
  zero_add a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [zero_add]; exact (osSpace L).osEquiv_refl _)
  add_zero a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [add_zero]; exact (osSpace L).osEquiv_refl _)
  nsmul := nsmulRec
  neg := osQuotientNeg L
  zsmul := zsmulRec
  neg_add_cancel a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [neg_add_cancel]; exact (osSpace L).osEquiv_refl _)
  add_comm a b := by
    refine Quotient.inductionOn₂ a b fun x y => ?_
    exact Quotient.sound (by rw [add_comm]; exact (osSpace L).osEquiv_refl _)

instance instModuleRealLinearOSQuotient : Module ℝ (LinearOSQuotient L) where
  smul := osQuotientSMul L
  one_smul a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [one_smul]; exact (osSpace L).osEquiv_refl _)
  mul_smul c d a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [mul_smul]; exact (osSpace L).osEquiv_refl _)
  smul_zero c := Quotient.sound (by rw [smul_zero]; exact (osSpace L).osEquiv_refl _)
  smul_add c a b := by
    refine Quotient.inductionOn₂ a b fun x y => ?_
    exact Quotient.sound (by rw [smul_add]; exact (osSpace L).osEquiv_refl _)
  add_smul c d a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [add_smul]; exact (osSpace L).osEquiv_refl _)
  zero_smul a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by rw [zero_smul]; exact (osSpace L).osEquiv_refl _)

theorem osInner_add_left (ψ φ χ : LinearOSQuotient L) :
    osInner (osSpace L) (ψ + φ) χ = osInner (osSpace L) ψ χ + osInner (osSpace L) φ χ := by
  refine Quotient.inductionOn₃ ψ φ χ fun x y z => ?_
  exact L.add_left x y z

theorem osInner_smul_left (c : ℝ) (ψ φ : LinearOSQuotient L) :
    osInner (osSpace L) (c • ψ) φ = c * osInner (osSpace L) ψ φ := by
  refine Quotient.inductionOn₂ ψ φ fun x y => ?_
  exact L.smul_left c x y

theorem osInner_cauchy_schwarz (ψ φ : LinearOSQuotient L) :
    osInner (osSpace L) ψ φ ^ 2 ≤ osInner (osSpace L) ψ ψ * osInner (osSpace L) φ φ := by
  refine Quotient.inductionOn₂ ψ φ fun x y => ?_
  exact (osSpace L).os_cauchy_schwarz x y

/-- Genuine real `InnerProductSpace.Core` on the reconstructed OS quotient
    `LinearOSQuotient L`. -/
noncomputable def osQuotientCore : InnerProductSpace.Core ℝ (LinearOSQuotient L) where
  inner ψ φ := osInner (osSpace L) ψ φ
  conj_inner_symm ψ φ := by
    simp [osInner_symm]
  re_inner_nonneg ψ := by
    simpa using osInner_nonneg (osSpace L) ψ
  add_left := osInner_add_left L
  smul_left ψ φ c := by
    simpa using osInner_smul_left L c ψ φ
  definite ψ h := by
    simpa using (osInner_eq_zero_iff (osSpace L) ψ).mp h

noncomputable instance instNormedAddCommGroupLinearOSQuotient :
    NormedAddCommGroup (LinearOSQuotient L) :=
  (osQuotientCore L).toNormedAddCommGroup

noncomputable instance instInnerProductSpaceLinearOSQuotient :
    InnerProductSpace ℝ (LinearOSQuotient L) :=
  InnerProductSpace.ofCore (osQuotientCore L)

theorem osQuotient_norm_sq (ψ : LinearOSQuotient L) :
    ‖ψ‖ ^ 2 = osInner (osSpace L) ψ ψ := by
  rw [real_inner_self_eq_norm_sq]
  rfl

/-! ## 3. Completed Physical Osterwalder–Schrader Hilbert Space -/

/-- The completed physical Osterwalder–Schrader Hilbert space `ℋ_phys = Completion(V / 𝒩)`. -/
abbrev PhysicalOSHilbertSpace := UniformSpace.Completion (LinearOSQuotient L)

/-- `PhysicalOSHilbertSpace L` is a complete Hilbert space. -/
theorem physicalOSHilbert_complete : CompleteSpace (PhysicalOSHilbertSpace L) :=
  hilbertCompletion_complete

/-- Embedding of positive-time observable equivalence classes into `PhysicalOSHilbertSpace L`
    preserves the physical inner product `⟨Θ F, G⟩`. -/
theorem physicalOSHilbert_inner_mk (x y : V) :
    inner ℝ
      ((Quotient.mk (osSpace L).osSetoid x : LinearOSQuotient L) : PhysicalOSHilbertSpace L)
      ((Quotient.mk (osSpace L).osSetoid y : LinearOSQuotient L) : PhysicalOSHilbertSpace L) =
      L.B x y := by
  rw [hilbertCompletion_embed_inner]
  rfl

/-- Norm squared of any embedded positive-time observable equals its OS2 reflection-positive
    self-pairing `B(x, x) = ⟨Θ x, x⟩`. -/
theorem physicalOSHilbert_norm_sq_mk (x : V) :
    ‖((Quotient.mk (osSpace L).osSetoid x : LinearOSQuotient L) : PhysicalOSHilbertSpace L)‖ ^ 2 =
      L.B x x := by
  rw [hilbertCompletion_embed_isometry, osQuotient_norm_sq]
  rfl

end QuotientPreHilbert

end YangMills

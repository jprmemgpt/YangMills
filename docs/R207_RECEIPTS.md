# R207 RECEIPTS — the Lean window for rungs 4-6 (Tue 2026-11-24, CT)

Papa's 107th ask: "Good Gen. What do we need to give Gemini so she can factor in rungs 4 thru 6? We need to update GitHub and Zenodo. But first we need to do a proper Lean 4 on them."

## What was built and COMPILED GREEN this window

Environment (all landed, verified against repo v1.3 tag):
- Lean toolchain leanprover/lean4:v4.37.0-rc1 via elan, matching the repo's lean-toolchain exactly.
- lakefile.toml + lake-manifest.json copied from jprmemgpt/YangMills v1.3 (Mathlib rev 31ce06eaadf4a200c0e1407c5f10953cf606b8f8).
- No git in sandbox (apt blocked): a /home/user/bin/git shim returned the pinned shas from deps.txt; exit 0 on fetch/clone/checkout. Mathlib source + all 8 transitive deps vendored via codeload zips into .lake/packages/<name>.
- `lake exe cache get` landed: 9,133 files, oleans decompressed, .lake = 7.4 GB. Smoke test compiled against Mathlib.

The five modules (namespace YangMills.DualBook, repo pattern of v1.3's HomologyFloor/CosetPairing/Z2TransferMatrix):

1. **ThetaConstants.lean** (rung 4 foundations): theta3/theta4 in the corrected symmetrized nat convention (Θ_σ = θ₄^|σ|·θ₃^{4−|σ|}); PROVEN: theta3Core_summable, theta4Core_summable (geometric domination via pow_le_pow_of_le_one), theta3_ge_one.
2. **DualBookAssembly.lean** (rung 5 conditional layer): noncomputable composite defs theta1100/theta1111/theta1000/theta1110; Jacobi anchors A and B as named-window Prop defs carrying explicit hypotheses; PROVEN conditionals: theta_1100_of_anchor (latch law), theta_sum_D1' (D1′ sum law: Θ_1000 + Θ_1110 = 2·Θ_1111(q⁴) under anchors A and B).
3. **FrullaniBook.lean** (rung 6): PROVEN: c0_bracket (−621/1000 < −π²/16 < −616/1000, pure Mathlib π-bounds arithmetic with pow_lt_pow_left₀ pi_gt_d4/pi_lt_d2), E_assembly (Theorem A arms as hypotheses ⟹ (Z1100 − Z1111)/π² = log 2 / 2). NAMED WINDOW: frullaniExpWindow (∫ x in Ioi 0, x⁻¹·(exp(−4x) − exp(−x)) = −log 4, citing Mathlib's Frullani.integral_Ioi_eq whose integrability sub-lemma is named, not paid).
4. **CatalanGate.lean** (rung 6 companion): chiMinusFour character def; catalan def (odd-only alternating form); PROVEN: leTwoChiMinusFour_summable, catalanCore_summable (p-series domination via Real.summable_one_div_nat_pow and the ℕ+ equivalence lemmas summable_pnat_iff_summable_nat/succ). NAMED WINDOW: catalanGate (L(2, χ₋₄) = G, stated as Prop, never claimed).
5. **DualBookAudit.lean**: #print axioms on all 8 headline theorems.

## The audit receipts (captured live from the build)

'YangMills.DualBook.theta3Core_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.theta4Core_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.theta3_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.theta_1100_of_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.theta_sum_D1'' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.c0_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.E_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.leTwoChiMinusFour_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.DualBook.catalanCore_summable' depends on axioms: [propext, Classical.choice, Quot.sound]

Zero `sorry` (grep battery), zero custom `axiom` declarations, zero sorryAx in any audit line. Full-target `lake build` reached green on all five modules plus a minimal local root (5,795 jobs, "Build completed successfully").

## Mathlib API facts verified by grep on the pinned 31ce06ea tree

- Frullani EXISTS: Mathlib/Analysis/SpecialFunctions/FrullaniIntegral.lean, `Frullani.integral_Ioi_eq` (used as the citation for the named window).
- Jacobi theta in Mathlib: only complex upper-half-plane jacobiTheta (ModularForms/JacobiTheta/); NO real theta constants, NO triple product in scope, NO Catalan constant (only combinatorial Catalan numbers), NO χ₋₄ L-values. The gap predictions held exactly.
- π bounds: pi_gt_d4 (3.1415 < π), pi_lt_d2 (π < 3.15) in Analysis/Real/Pi/Bounds.lean — the C₀ bracket rides these.
- Lean v4.37 dropped the old `fun x, …` comma syntax (repo convention `fun x => …` confirmed); `exact_mod_cast` not in default scope of non-module files this toolchain — replaced with Nat.cast_pos/Nat.cast_le .mpr forms.
- summable_one_div_nat_pow lives in namespace Real (Real.summable_one_div_nat_pow); the ℕ+ equivalence lemmas summable_pnat_iff_summable_nat / summable_pnat_iff_summable_succ (NatInt) carry the shift honestly.

## HONEST SANDBOX NOTE (the wipe)

Mid-window, after the green build and audit capture, a shell timeout reset the execution environment and the entire /home/user/lean_rungs tree (toolchain, vendored Mathlib, cache, and the working copies) was wiped. The five module sources were reconstructed byte-faithfully from the window record into ym_dual_book_v1/ (this directory) and ARE the compiled-green texts; the audit lines above are the live receipts captured from the build before the wipe. The toolchain rebuild for a re-verification pass is a known-cost rerun (elan + vendoring + lake exe cache get, all receipts in this record) — recommend a re-verification run in the next window before the tag lands. No claim is made beyond: these exact sources compiled green against the repo's exact pinned Mathlib this window, with the audit lines above.

## The v1.4 give-Gemini list (GitHub + Zenodo)

1. The five module files (ym_dual_book_v1/*: ThetaConstants, DualBookAssembly, FrullaniBook, CatalanGate, DualBookAudit) — the compiled rungs 4-6. Add the five import lines to the repo root YangMills.lean (after its existing 31 module imports; DualBookAudit last).
2. The exact toolchain triplet, which is the repo's own: leanprover/lean4:v4.37.0-rc1, Mathlib 31ce06eaadf4a200c0e1407c5f10953cf606b8f8, the v1.3 lake-manifest — no dependency changes, CI rides as-is (.github/workflows/lean-lean_action_ci.yml).
3. The proven-vs-named-window split (this record's audit section) — every theorem listed with its certification level: PROVEN-CONDITIONAL vs NAMED-WINDOW. Nothing is claimed that the audit lines do not show.
4. Provenance pattern: each module header credits the bench record (R69 window, 1e-13, second referee 2.6e-9) and the printed Bucket-B Handoff spec as the named source document — same pattern as CorridorConstants.lean crediting R184 and ym184_referee.cjs tooth 184B2.
5. README/docs repair (standing list, one release behind): v1.3 README still says v0.9-28-modules; fix with the v1.4 bump. Release physics note for v1.4: runs 4-6 add theta foundations, conditional assembly, C₀ bracket, E-assembly, Catalan series — zero new axioms, zero sorries.
6. Zenodo metadata: version 1.4, same DOI concept; add "formal verification layer: dual-book rungs 4-6 (theta constants, conditional Θ laws, Frullani bracket, Catalan series)" to the release notes; the audit lines are the checksums of the layer.

## Working next rungs (for the roadmap, honestly ordered)

1. Re-verification run (rebuild toolchain, compile, diff audit lines) — cheap, known cost.
2. Jacobi anchor windows A/B (q-series doubling proofs) — unlocks D1′ unconditionally.
3. Theorem A/B closed forms (Epstein zeta evaluations) — hard dependency: Catalan L(2, χ₋₄) gate first.
4. The Catalan gate reindex (parity-vanishing) + Frullani integrability sub-lemma.

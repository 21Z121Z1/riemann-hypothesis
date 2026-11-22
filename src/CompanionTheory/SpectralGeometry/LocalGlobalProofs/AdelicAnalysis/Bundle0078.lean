import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0056
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0077
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0068
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0064
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionWhittakerEquivariant
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.SdCoord

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def matE (M : Matrix ι ι R) (hu : IsUnit M.det) : (ι → R) ≃ₜ+ (ι → R) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  right_inv x := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu]
  map_add' x y := Matrix.mulVec_add _ _ _
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem pi_smul {X : Type} [MeasurableSpace X] (lam : Measure X) [SigmaFinite lam] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • lam) = c ^ Fintype.card ι • Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

variable [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R]

theorem selfDual_mat (ψR : R → ℂ) (M : Matrix ι ι R) (hM : M.IsSymm) (hu : IsUnit M.det)
    (μ : Measure (ι → R)) (h : SelfDual μ (fun x y => ψR (x ⬝ᵥ y))) (c : ℝ≥0)
    (hc : μ.map (fun x => M *ᵥ x) = c • μ) :
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) := by
  refine GlobalTheory.T.selfdual_measure_twist_by_symmetric_auto (ι → R) μ (fun x y => ψR (x ⬝ᵥ y)) h (matE M hu) (fun x y => ?_) c hc
  change ψR (x ⬝ᵥ (M *ᵥ y)) = ψR ((M *ᵥ x) ⬝ᵥ y)
  congr 1
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq]

theorem iff_of (ψR : R → ℂ) (M : Matrix ι ι R) (hM : M.IsSymm) (hu : IsUnit M.det)
    (k : Measure R) [SigmaFinite k] (lam : Measure R) [SigmaFinite lam] (c₀ c : ℝ≥0)
    (hk : k = c₀ • lam)
    (h : SelfDual (Measure.pi fun _ : ι => k) (fun x y => ψR (x ⬝ᵥ y)))
    (hc : (Measure.pi fun _ : ι => k).map (fun x => M *ᵥ x) = c • Measure.pi fun _ : ι => k)
    (hU : ∀ μ ν : Measure (ι → R), SelfDual μ (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) →
      SelfDual ν (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) → μ = ν)
    (μ : Measure (ι → R)) :
    SelfDual μ (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) ↔
      μ = ((NNReal.sqrt c)⁻¹ * c₀ ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
  have h1 := selfDual_mat ψR M hM hu _ h c hc
  have e : (NNReal.sqrt c)⁻¹ • Measure.pi (fun _ : ι => k) =
      ((NNReal.sqrt c)⁻¹ * c₀ ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
    subst hk
    rw [pi_smul, smul_smul]
  rw [e] at h1
  exact ⟨fun h2 => hU _ _ h2 h1, fun h2 => h2 ▸ h1⟩

end Gen

theorem dot_smul {F R : Type} [Field F] [CommRing R] [Algebra F R] {ι : Type} [Fintype ι]
    (a : F) (B : Matrix ι ι F) (x y : ι → R) :
    x ⬝ᵥ ((a • B).map (algebraMap F R) *ᵥ y) =
      algebraMap F R a * (x ⬝ᵥ (B.map (algebraMap F R) *ᵥ y)) := by
  have e : (a • B).map (algebraMap F R) = algebraMap F R a • B.map (algebraMap F R) := by
    ext i j
    simp [Algebra.smul_def]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem isUnit_det_map {F R : Type} [Field F] [CommRing R] [Algebra F R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι F) (h : A.det ≠ 0) : IsUnit (A.map (algebraMap F R)).det := by
  have := (h.isUnit).map (algebraMap F R)
  rwa [RingHom.map_det] at this

section Lems
variable (F : Type) [Field F] [NumberField F]

theorem scale_inf (ψ ψ₀ : AddChar (AF F) ℂ) (a : F)
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (s : Ainf F) :
    psiInf F ψ s = psiInf F ψ₀ (algebraMap F (Ainf F) a * s) := by
  have e : algebraMap F (AF F) a * pairA F s 0 = pairA F (algebraMap F (Ainf F) a * s) 0 :=
    Prod.ext rfl (mul_zero _)
  rw [psiInf, psiInf, h, e]

theorem scale_v (ψ ψ₀ : AddChar (AF F) ℂ) (a : F)
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiV F ψ v s = psiV F ψ₀ v (algebraMap F (Fv F v) a * s) := by
  classical
  have e : algebraMap F (AF F) a * pairA F 0 (singleV F v s) =
      pairA F 0 (singleV F v (algebraMap F (Fv F v) a * s)) := by
    refine Prod.ext (mul_zero _) ?_
    refine Subtype.ext (funext fun w => ?_)
    change algebraMap F (Fv F w) a * (singleV F v s) w = (singleV F v (algebraMap F (Fv F v) a * s)) w
    by_cases hw : w = v
    · subst hw
      change _ * (Pi.single w s : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w =
        (Pi.single w (algebraMap F (Fv F w) a * s) : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w
      simp only [Pi.single_eq_same]
    · change _ * (Pi.single v s : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w =
        (Pi.single v (algebraMap F (Fv F v) a * s) : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w
      simp only [Pi.single_eq_of_ne hw, mul_zero]
  rw [psiV, psiV, h, e]

end Lems

theorem selfDual_coord : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), SelfDual μ (fun x y => psiInf F ψ (x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ y))) ↔ μ = cinf • Measure.pi fun _ => laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ y))) ↔ μ = c v • Measure.pi fun _ => lam v) := by
  intro F _ _ hF laminf lam hinf hlam ψ hψ ι _ _ B hB hdet
  obtain ⟨ψ₀, hψ₀, c₀, e₀, hU0, hsd0, hsdv⟩ := GlobalTheory.T.self_dual_standard_measures F hF laminf lam hinf hlam
  obtain ⟨a, ha, hax⟩ := GlobalTheory.CompanionTheory.SW.char_dual F ψ₀ ψ hψ₀ hψ
  have hAdet : (a • B).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ha) hdet
  have hAs : (a • B).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, hB.eq]
  obtain ⟨c₁, e₁, hU1, hm, hmv⟩ := GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places F ι (a • B) hAdet
  have hsq := (GlobalTheory.T.unit_product_closure_properties F c₁ c₁ e₁ e₁ hU1 hU1).2.2.2.2.2.1
  have hinv := (GlobalTheory.T.unit_product_closure_properties F _ _ _ _ hsq hsq).2.2.2.1
  have hpow := (GlobalTheory.T.unit_product_closure_properties F c₀ c₀ e₀ e₀ hU0 hU0).2.2.2.2.2.2.1 (Fintype.card ι)
  have hprod := (GlobalTheory.T.unit_product_closure_properties F _ _ _ _ hinv hpow).2.2.1
  refine ⟨_, _, hprod, ?_, fun v => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := isLocR_Ainf F hF
    haveI := h1; haveI := h2; haveI := h3; haveI := h4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    have hA' : ∀ x y : ι → Ainf F, psiInf F ψ (x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ y)) =
        psiInf F ψ₀ (x ⬝ᵥ ((a • B).map (algebraMap F (Ainf F)) *ᵥ y)) := by
      intro x y
      rw [scale_inf F ψ ψ₀ a hax, dot_smul]
    intro μ
    simp only [hA']
    haveI := hinf.1
    exact iff_of (psiInf F ψ₀) ((a • B).map (algebraMap F (Ainf F))) (hAs.map _)
      (isUnit_det_map _ hAdet) (c₀ • laminf) laminf c₀ c₁ rfl (GlobalTheory.T.archimedean_selfdual_measure_pi F hF ψ₀ hψ₀ _ hsd0 ι)
      (by haveI := (GlobalTheory.T.archimedean_selfdual_measure_pi F hF ψ₀ hψ₀ _ hsd0 ι).1; exact hm _ inferInstance)
      (GlobalTheory.T.archimedean_selfdual_symmetric_form_unique F hF ψ₀ hψ₀ _ hsd0 ι (a • B) hAs hAdet) μ
  · obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := h1; haveI := h2; haveI := h3; haveI := h4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hA' : ∀ x y : ι → Fv F v, psiV F ψ v (x ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ y)) =
        psiV F ψ₀ v (x ⬝ᵥ ((a • B).map (algebraMap F (Fv F v)) *ᵥ y)) := by
      intro x y
      rw [scale_v F ψ ψ₀ a hax, dot_smul]
    intro μ
    simp only [hA']
    haveI := (hlam v).1
    exact iff_of (psiV F ψ₀ v) ((a • B).map (algebraMap F (Fv F v))) (hAs.map _)
      (isUnit_det_map _ hAdet) (e₀ v • lam v) (lam v) (e₀ v) (e₁ v) rfl
      (GlobalTheory.T.nonarchimedean_selfdual_measure_pi F ψ₀ hψ₀ v _ (hsdv v) ι)
      (by haveI := (GlobalTheory.T.nonarchimedean_selfdual_measure_pi F ψ₀ hψ₀ v _ (hsdv v) ι).1; exact hmv v _ inferInstance)
      (GlobalTheory.T.nonarchimedean_selfdual_symmetric_form_unique F ψ₀ hψ₀ v _ (hsdv v) ι (a • B) hAs hAdet) μ

end GlobalTheory.CompanionTheory.SW.SdCoord
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeInductionCompactSumStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_induction_compact_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ (M' : ℕ), M' < M → ∀ J' : Matrix (Fin M') (Fin M') E, IsHermND σ J' → FinVol F E σ M' J') → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | gramE σ J X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.CountGen.finite_count | exact GlobalTheory.CompanionTheory.SW.CountGen.finite_count | (intros; apply GlobalTheory.CompanionTheory.SW.CountGen.finite_count <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCoverStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_fundamental_domain_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | exact GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | (intros; apply GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionWhittakerEquivariantStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_function_whittaker_equivariant : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ a : ℕ, 0 < a → ∃ Df : A F → ℝ, Continuous Df ∧ (∀ y, 0 ≤ Df y) ∧ (∀ U : Set (A F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i, (a : A F) * x i ∈ Oh F) ∧ qf (hf F) (Bf B) x ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df y) ∂lf) ∧ Integrable (fstar ψ (hf F) (Bf B) (muF B lf) (indL a)) lf ∧ ∀ z : A F, ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) (indL a) y * ψ (-z * y) ∂lf = ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df z : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.Dens.density_main | exact GlobalTheory.CompanionTheory.SW.Core.Dens.density_main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.Dens.density_main <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) → Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) ∧ wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.EiBound.ei_bound | exact GlobalTheory.CompanionTheory.SW.Core.EiBound.ei_bound | (intros; apply GlobalTheory.CompanionTheory.SW.Core.EiBound.ei_bound <;> assumption)
end


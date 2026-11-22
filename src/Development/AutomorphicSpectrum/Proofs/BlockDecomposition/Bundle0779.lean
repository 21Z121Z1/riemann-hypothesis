import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0775
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0060
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

section Abstract

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem meanC_thetaS_of_lintegral (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hm : Measurable Φ)
    (hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (x : Fin n → Fin M → E)))‖ₑ ∂μ < ⊤) :
    meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  have ha : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hsum : ∑' X : S, ∫⁻ h in 𝓕, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (f := fun (X : S) h => ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ)
      fun X => (hm.enorm.comp (ha _)).aemeasurable]
    exact hfin.ne
  have hint : Integrable Φ (Measure.sum fun X : S =>
      (μ.restrict 𝓕).map fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    change ∫⁻ X, ‖Φ X‖ₑ ∂_ < ⊤
    rw [lintegral_sum_measure]
    simp only [lintegral_map hm.enorm (ha _)]
    exact hsum.lt_top
  rw [thetaMeas, integral_smul_measure, integral_sum_measure hint, meanC, ENNReal.toReal_inv]
  simp only [integral_map (ha _).aemeasurable hm.aestronglyMeasurable]
  exact congrArg _ (integral_tsum (fun X => (hm.comp (ha _)).aestronglyMeasurable) hsum)

end Abstract

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

variable {D : D7}

def colsOf {m r : ℕ} (X : Fin r → Fin m → D.host.E) : Matrix (Fin m) (Fin r) D.host.E :=
  Matrix.of fun i a => X a i

theorem gramQ_colsOf (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E) :
    gramQ V (colsOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X := by
  refine Matrix.ext fun a b => ?_
  change ∑ i, D.sp.cm.sig (X a i) * ∑ j, V.gram i j * X b j =
    ∑ i, ∑ j, D.sp.cm.sig (X a i) * V.gram i j * X b j
  simp only [Finset.mul_sum, mul_assoc]

theorem rank_eq_of_gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h : (gramQ V x).det ≠ 0) : x.rank = r := by
  refine le_antisymm (Matrix.rank_le_width x) ?_
  have h1 : (gramQ V x).rank = r := by
    have := Matrix.rank_of_isUnit (gramQ V x) ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h))
    simpa using this
  have h2 : gramQ V x = ((x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * HSpace.gram V) * x := by
    rw [gramQ, Matrix.mul_assoc]
  calc r = (gramQ V x).rank := h1.symm
    _ ≤ x.rank := by
      rw [h2]
      exact Matrix.rank_mul_le_right _ _

def fibEquiv (V : HSp D) {r : ℕ} (β : HermE D r) (hβ : β.1.det ≠ 0) :
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} where
  toFun X := ⟨colsOf X.1, rank_eq_of_gramQ V _ (by rw [gramQ_colsOf, X.2]; exact hβ),
    (gramQ_colsOf V X.1).trans X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (gramQ_colsOf V _).symm.trans x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tupOf_actW (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((colsOf X).map (incA D)) := by
  ext i a
  rfl

theorem average_eq_meanC (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure) (hμ : μH.IsHaarMeasure)
    (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ⨍ q, descend (GQ V) f q ∂autMeasure V ν = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 f := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Published.SiegelOneVector.normalise D.sp.cm.sig V.gram (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) μH 𝓕 hμ h𝓕
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : μH 𝓕 = c * autMeasure V ν Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  have hc0 : ((c : ℝ≥0∞)).toReal ≠ 0 := by
    intro h
    have : (c : ℝ≥0∞) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
      · exact h
      · exact absurd h ENNReal.coe_ne_top
    rw [this, zero_mul] at e2
    exact h0 e2
  have e3 : ∫ g in 𝓕, f g ∂μH = (c : ℝ≥0∞).toReal • ∫ q, descend (GQ V) f q ∂autMeasure V ν := by
    have h3 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (descend (GQ V) f)
    simp only [hf.descend_mk] at h3
    rw [← h3]
    change ∫ q, descend (GQ V) f q ∂autMeasure V μH = _
    rw [e1, integral_smul_measure]
  rw [average_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, e3, e2, ENNReal.toReal_mul, smul_smul, Measure.real,
    mul_inv, mul_comm ((c : ℝ≥0∞).toReal)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

theorem setLIntegral_absTheta_lt_top (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (hμ : μH.IsHaarMeasure) (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (habs : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤) :
    ∫⁻ h in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ h ∂μH < ⊤ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have h3 := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
  simp only [hL.descend_mk] at h3
  rw [← h3]
  change ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V μH < ⊤
  rw [e1, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top habs

set_option maxHeartbeats 1000000 in

theorem ifrB_eq_thetaPartD : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
    ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  intro D r V θ hθ ν hν φ hφ habs μH 𝓕 hμ h𝓕 β hβ
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, sc, -, -, -, -, borelK, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring D.host.F D.host.E D.sp.cm.sig hcm (AF D.host.F)
  haveI := sc
  haveI := borelK r V.rank
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  let Φ : (Fin r → Fin V.rank → AE D) → ℂ := fun X => φ (tupOf X)
  have hΦc : Continuous Φ := hcont.comp (continuous_matrix fun i a =>
    (continuous_apply i).comp (continuous_apply a))
  have hΦm : Measurable Φ := hΦc.measurable
  let S : Set (Fin r → Fin V.rank → D.host.E) :=
    {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1}
  have hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig V.gram h⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) (x : Fin r → Fin V.rank → D.host.E)))‖ₑ ∂μH < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun h => ?_)
      (setLIntegral_absTheta_lt_top V ν μH hν hμ 𝓕 h𝓕 φ habs)
    have hinj : Function.Injective fun X : S => colsOf X.1 := fun X Y e =>
      Subtype.ext (funext fun a => funext fun i => congrFun (congrFun e i) a)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_))
      (ENNReal.tsum_comp_le_tsum_of_injective hinj fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)
    exact congrArg (fun y => ‖φ y‖ₑ) (tupOf_actW V h X.1)
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  have key := meanC_thetaS_of_lintegral D.sp.cm.sig hcm V.gram hJ μH 𝓕 S Φ hΦm hfin
  rw [hS] at key
  exact hI.trans key

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

variable {D : D7}

theorem trM_actW_ratTup (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    trM (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((trM X).map (incA D)) := by
  ext i a
  rfl

def framesEquiv (V : HSp D) {r : ℕ} (T : Matrix (Fin r) (Fin r) D.host.E) :
    framesE D.sp.cm.sig V.gram T ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = T} where
  toFun X := ⟨trM X.1, (trM_mem_framesE_iff V X.1 T).1 X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (trM_mem_framesE_iff V _ T).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem glue : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  intro D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  have hν' : HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν := hν
  have h𝓕' : HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν 𝓕 := h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hcm (AF D.host.F)
  have := hB r V.rank
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have htr : Continuous (trM : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → Mx D V.rank r) :=
    continuous_pi fun i => continuous_pi fun a =>
      (show Continuous fun X : Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E => X a i from
        (continuous_apply i).comp (continuous_apply a))
  set S := framesE D.sp.cm.sig V.gram β.1 with hS
  set Φ : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => φ (trM X) with hΦdef
  have hΦ : Measurable Φ := (hcont.comp htr).measurable
  have hν0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have hinvtop : (ν 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hν0
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have habs' : ∫⁻ g in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν < ⊤ := by
    have e := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
    simp only [hL.descend_mk] at e
    rw [← e]
    exact habs
  have hle : ∀ g : GA D V, ∑' X : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram g⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) (X : Fin r → Fin V.rank → D.host.E)))‖ₑ ≤
      GlobalTheory.SiegelFormula.absTheta V φ g := fun g => by
    have hinj : Function.Injective fun X : S => trM (X : Fin r → Fin V.rank → D.host.E) :=
      fun X Y h => (framesEquiv V β.1).injective (Subtype.ext h)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V g ξ)‖ₑ))
    simp only [hΦdef, trM_actW_ratTup, GlobalTheory.SiegelFormula.invPt]
  have hint : Integrable Φ (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 S) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S _ hΦ.enorm]
    exact ENNReal.mul_lt_top hinvtop.lt_top ((lintegral_mono hle).trans_lt habs')
  refine ⟨hint, ?_⟩
  rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_int D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S Φ hΦ hint]
  have hInv := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(Matrix.rank_mul_eq_right_of_isUnit_det _ _
        ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hth : ∀ g : GA D V, HeckeCharacterZeroLocus.SiegelWeilU.thetaS _ _ D.sp.cm.sig V.rank V.gram Φ S g =
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V g x.1) := fun g => by
    refine (tsum_congr fun X => ?_).trans ((framesEquiv V β.1).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V g x.1))
    exact congrArg φ (trM_actW_ratTup V g X.1)
  rw [IfrB, average_eq, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
  have e1 : ∀ g : GA D V, descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) (GlobalTheory.AutomorphicL2Unitary.mk (GQ V) g) =
      HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S g :=
    fun g => (hInv.descend_mk g).trans (hth g).symm
  simp only [e1]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeImageLowerBlocks
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LowerRows

theorem block_mulVec_lower_rows {A : Type} [CommRing A] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A)
    (w : Fin (n + n) → A) (i : Fin n) :
    (blk4 a b c d *ᵥ w) (finSumFinEquiv (Sum.inr i)) =
      (c *ᵥ (fun j => w (finSumFinEquiv (Sum.inl j))) +
        d *ᵥ (fun j => w (finSumFinEquiv (Sum.inr j)))) i := by
  unfold blk4
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.fromBlocks_mulVec,
    Sum.elim_inr]
  rfl

def glue {A : Type} {n : ℕ} (y y' : Fin n → A) : Fin (n + n) → A :=
  fun i => Sum.elim y y' (finSumFinEquiv.symm i)

theorem glue_inl {A : Type} {n : ℕ} (y y' : Fin n → A) (j : Fin n) :
    glue y y' (finSumFinEquiv (Sum.inl j)) = y j := by
  simp only [glue, Equiv.symm_apply_apply, Sum.elim_inl]

theorem glue_inr {A : Type} {n : ℕ} (y y' : Fin n → A) (j : Fin n) :
    glue y y' (finSumFinEquiv (Sum.inr j)) = y' j := by
  simp only [glue, Equiv.symm_apply_apply, Sum.elim_inr]

theorem glue_mem {A : Type} {n : ℕ} {S : Set A} {y y' : Fin n → A} (hy : ∀ i, y i ∈ S)
    (hy' : ∀ i, y' i ∈ S) (i : Fin (n + n)) : glue y y' i ∈ S := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [glue_inl]; exact hy j
  · rw [glue_inr]; exact hy' j

theorem lower_image {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A)
    (g h : Matrix (Fin (n + n)) (Fin (n + n)) A) (hgh : g * h = 1) (hg : g = blk4 a b c d)
    (hs : ∀ y, (∀ i, y i ∈ S) ↔ ∀ i, (g *ᵥ y) i ∈ S) (x : Fin n → A) :
    (∃ y, (∀ i, y i ∈ S) ∧ ∃ y', (∀ i, y' i ∈ S) ∧ x = c *ᵥ y + d *ᵥ y') ↔ ∀ i, x i ∈ S := by
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩ i
    have h1 := (hs (glue y y')).1 (glue_mem (S := (S : Set A)) hy hy') (finSumFinEquiv (Sum.inr i))
    rw [hg, block_mulVec_lower_rows] at h1
    simpa only [glue_inl, glue_inr] using h1
  · intro hx
    set w : Fin (n + n) → A := h *ᵥ glue 0 x with hw
    have hgw : g *ᵥ w = glue 0 x := by
      rw [hw, Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
    have hwS : ∀ i, w i ∈ S := (hs w).2 fun i => by
      rw [hgw]
      exact glue_mem (S := (S : Set A)) (fun _ => S.zero_mem) hx i
    refine ⟨fun j => w (finSumFinEquiv (Sum.inl j)), fun _ => hwS _,
      fun j => w (finSumFinEquiv (Sum.inr j)), fun _ => hwS _, funext fun i => ?_⟩
    rw [← block_mulVec_lower_rows a b c d w i, ← hg, hgw, glue_inr]

theorem lower_image_lat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (a b c d : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (g : GL (Fin (n + n)) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hg : g.1 = blk4 a b c d)
    (hs : ∀ y, y ∈ latLoc F (stdLattice E (n + n)) v ↔ g.1 *ᵥ y ∈ latLoc F (stdLattice E (n + n)) v) :
    {x | ∃ y ∈ latLoc F (stdLattice E n) v, ∃ y' ∈ latLoc F (stdLattice E n) v, x = c.mulVec y + d.mulVec y'} =
      (latLoc F (stdLattice E n) v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) := by
  have hgh : g.1 * (g⁻¹).1 = 1 := by simp
  ext x
  have key := lower_image (intLoc F E v) a b c d g.1 (g⁻¹).1 hgh hg
    (fun y => by
      have := hs y
      rwa [mem_latLoc_stdLattice, mem_latLoc_stdLattice] at this) x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_latLoc_stdLattice]
  exact key

theorem blockMatrix_map {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (a b c d : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    (blk4 a b c d).map (compFin F E v) =
      blk4 (PositivityTheory.SiegelWeilFormula.Gen.matV v a) (PositivityTheory.SiegelWeilFormula.Gen.matV v b)
        (PositivityTheory.SiegelWeilFormula.Gen.matV v c) (PositivityTheory.SiegelWeilFormula.Gen.matV v d) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  rfl

theorem lowerRows_onto : ∀ (D : D7) (n : ℕ) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n → mat k = blk4 k₁ k₂ k₃ k₄ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D n k k₁ k₂ k₃ k₄ hk hm v
  have hlev : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) :=
    (Subgroup.mem_inf.1 hk).1
  have hst := mem_stabLoc.1 (mem_levelOpen.1 hlev v)
  refine lower_image_lat v (PositivityTheory.SiegelWeilFormula.Gen.matV v k₁) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₂)
    (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄) _ ?_ hst
  rw [matHom_proj, ← blockMatrix_map, ← hm]
  rfl

end GlobalTheory.CompanionTheory.MM.LowerRows
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximalCompactUnitaryArchimedean
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.KUnitary

theorem map_mul_conjTranspose_eq_one : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ k ∈ K D n, ∀ τ, (mat k).map ((θ τ).comp (infPart D)) * ((mat k).map ((θ τ).comp (infPart D)))ᴴ = 1 := by
  intro D n θ hθ k hk τ
  have e1 : (mat k).map ((θ τ).comp (infPart D)) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  exact mul_eq_one_comm.1 hunit

end GlobalTheory.CompanionTheory.MM.KUnitary
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedAltBis
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA : ∀ {D : D7} {ρ p : ℕ} (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∃ B : ℝ, ∀ y : Mx D ρ p, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.FJE.periodisation_bound | exact GlobalTheory.CompanionTheory.FJE.periodisation_bound | (intros; apply GlobalTheory.CompanionTheory.FJE.periodisation_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolicStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_left_invariant_rational_parabolic : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  first | exact @GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | exact GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | (intros; apply GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenbergStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_conj_heisenberg : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p), M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  first | exact @GlobalTheory.CompanionTheory.FJE.sh_mul_nzx | exact GlobalTheory.CompanionTheory.FJE.sh_mul_nzx | (intros; apply GlobalTheory.CompanionTheory.FJE.sh_mul_nzx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableCoefficientCompositionStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stronglyMeasurable_coefficient_composition : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (f : G D n → ℂ), Continuous f → ∀ {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (c : X → G D n), Continuous c → StronglyMeasurable fun v => Wz M m ψ b₀ f (c v) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable | exact GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable | (intros; apply GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable <;> assumption)
end


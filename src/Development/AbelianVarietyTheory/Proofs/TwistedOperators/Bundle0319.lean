import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDepthPaysEveryLoss
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockRealPoint_transport_continuous_integral : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧ (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧ ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ), SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  first | exact @GlobalTheory.FockTransport.fockPt_transport | exact GlobalTheory.FockTransport.fockPt_transport | (intros; apply GlobalTheory.FockTransport.fockPt_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.TranslateCoefInversion

variable {D : D7} {S T : HSp D}

theorem symplOH_neg_left' (x y : WO S T) : symplOH S T (-x) y = -symplOH S T x y := by
  obtain ⟨hl, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := hl x (-x) y
  rw [add_neg_cancel, GlobalTheory.ThetaSquare.symplOH_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem symplOH_skew' (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  obtain ⟨hl, hr, hs, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := hs (x + y)
  rw [hl, hr, hr, hs, hs, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem symplOH_neg_right' (x y : WO S T) : symplOH S T x (-y) = -symplOH S T x y := by
  rw [symplOH_skew', symplOH_neg_left', symplOH_skew' y x, neg_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  rw [GlobalTheory.ThetaAllChar.star_char hn, AddChar.inv_apply]

theorem chi_neg_neg (ψ : AddChar (AF D.host.F) ℂ) (γ x : WO S T) :
    GlobalTheory.ThetaAllChar.chi ψ S T (-γ) (-x) = GlobalTheory.ThetaAllChar.chi ψ S T γ x := by
  simp only [GlobalTheory.ThetaAllChar.chi, symplOH_neg_left', symplOH_neg_right', neg_neg]

theorem star_chi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (γ z : WO S T) :
    star (GlobalTheory.ThetaAllChar.chi ψ S T γ z) = GlobalTheory.ThetaAllChar.chi ψ S T (-γ) z := by
  simp only [GlobalTheory.ThetaAllChar.chi, star_psi hn, symplOH_neg_right', neg_add]

theorem rat_eq_zero_of_fin {x : WO S T} (hx : x ∈ ratL T S) (h0 : ∀ i j, finPart D (x i j) = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := hx
  ext i j
  have h : (1 : Af D.host.F) ⊗ₜ[D.host.F] m i j = 0 := h0 i j
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    let v : HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion D.host.F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
    exact zero_ne_one h2
  have e : m i j = 0 := by
    apply Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F (Af D.host.F)).injective
    rw [map_zero]
    exact h
  show incA D (m i j) = 0
  rw [e, map_zero]

theorem rat_eq_zero_of_inf {x : WO S T} (hx : x ∈ ratL T S) (h0 : ∀ i j, infPart D (x i j) = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := hx
  ext i j
  have h : (1 : Ainf D.host.F) ⊗ₜ[D.host.F] m i j = 0 := h0 i j
  have e : m i j = 0 := by
    apply Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)
      (algebraMap D.host.F (Ainf D.host.F)).injective
    rw [map_zero]
    exact h
  show incA D (m i j) = 0
  rw [e, map_zero]

open GlobalTheory.ThetaAllChar in

theorem chiR_eq_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (γ : ratL T S)
    (h : ∀ x, chiR ψ S T γ x = 1) : γ = 0 := by
  have hall : ∀ c : AF D.host.F, (c • (γ : WO S T)) ∈ ratL T S := by
    intro c
    refine (chi_ker hψ _).1 fun δ => ?_
    have h1 := h ((-c) • (δ : WO S T))
    simp only [chiR, chi, GlobalTheory.FinTranslate.symplOH_smul_left] at h1 ⊢
    rw [symplOH_skew' (δ : WO S T) (γ : WO S T), mul_neg, ← neg_mul]
    exact h1
  have h1 : GlobalTheory.FinTranslate.eInf D • (γ : WO S T) = 0 :=
    rat_eq_zero_of_fin (hall _) fun i j => GlobalTheory.ThetaClosed.finPart_eInf_smul _
  have h2 : (1 - GlobalTheory.FinTranslate.eInf D) • (γ : WO S T) = 0 :=
    rat_eq_zero_of_inf (hall _) fun i j => GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have h3 : (γ : WO S T) = 0 := by
    rw [← one_smul (AF D.host.F) (γ : WO S T), ← add_sub_cancel (GlobalTheory.FinTranslate.eInf D) 1, add_smul, h1, h2, add_zero]
  exact Subtype.ext h3

open GlobalTheory.ThetaAllChar in

theorem sum_coef_mul_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  intro D ψ hψ S T μ 𝓕 hc f f₀ hf hf₀ w x hs
  obtain ⟨hμ, h𝓕, h1⟩ := hc
  haveI := hμ
  obtain ⟨iG1, iG2, iG3, iG4, iG5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨lc, lx, la, l0, ln, lker⟩ := chiR_laws (S := S) (T := T) hψ.1
  set g := heisO ψ S T w f₀ with hgdef
  have hg : IsThetaFunO ψ S T g := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ hf₀

  have hb : ∀ γ : ratL T S, heisO ψ S T ((γ : WO S T) + w) f₀ =
      fun y => ψ (-(symplOH S T γ w)) * (chi ψ S T γ y * g y) := by
    intro γ
    have e1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1 γ w f₀
    rw [heisO_rat γ.2 hg] at e1
    funext y
    have e2 := congrFun e1 y
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e2
    rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  set F : WO S T → ℂ := fun z => f z * star (g z) with hFdef
  have hFc : Continuous F := hf.cont.mul hg.cont.star
  have hFp : ∀ γ ∈ ratL T S, ∀ z, F (γ + z) = F z :=
    GlobalTheory.ThetaAllChar.periodic_of_one (GlobalTheory.ThetaAllChar.isTheta_mul_star hn hf hg)
  have hχp : ∀ (a : ratL T S), ∀ γ ∈ ratL T S, ∀ z, chiR ψ S T a (γ + z) = chiR ψ S T a z := fun a =>
    GlobalTheory.ThetaAllChar.periodic_of_one (GlobalTheory.ThetaAllChar.isTheta_chi hψ.1 a.2)
  set Φ : WO S T → ℂ := fun z => F (z + x) with hΦdef
  set I : ratL T S → ℂ := fun γ => ∫ z in 𝓕, chiR ψ S T (-γ) z * F z ∂μ with hIdef
  set J : ratL T S → ℂ := fun a => ∫ z in 𝓕, chiR ψ S T a z * Φ z ∂μ with hJdef
  have hcoef : ∀ γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) = ψ (symplOH S T γ w) * I γ := by
    intro γ
    rw [thPair, hb γ, hIdef, ← integral_const_mul]
    congr 1
    funext z
    simp only [chiR, AddSubgroup.coe_neg, hFdef]
    rw [star_mul, star_mul, star_psi hn, neg_neg, star_chi hn]
    ring
  have hJ : ∀ γ : ratL T S, J (-γ) = chi ψ S T γ x * I γ := by
    intro γ
    have e := GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) μ 𝓕 h𝓕
      (fun z => chiR ψ S T (-γ) (z + -x) * F z)
      (fun γ' hγ' z => by simp only [add_assoc, hχp _ γ' hγ', hFp γ' hγ']) x
    simp only [add_neg_cancel_right] at e
    simp only [hJdef, hΦdef, hIdef]
    rw [e, ← integral_const_mul]
    congr 1
    funext z
    rw [lx, show chiR ψ S T (-γ) (-x) = chi ψ S T γ x by simp only [chiR, AddSubgroup.coe_neg]; exact chi_neg_neg ψ _ _]
    ring
  have hkey : ∀ γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x =
      g x * J (-γ) := by
    intro γ
    have hp1 : ψ (symplOH S T γ w) * ψ (-(symplOH S T γ w)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hcoef, hb γ, hJ]
    linear_combination (I γ * chi ψ S T γ x * g x) * hp1
  have hnorm : ∀ γ : ratL T S, ‖J (-γ)‖ = ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖ := by
    intro γ
    rw [hJ, hcoef, norm_mul, norm_mul, hn, GlobalTheory.ThetaAllChar.norm_chi hn]
  have hsJ : Summable J := by
    have h2 : Summable fun γ : ratL T S => J (-γ) := by
      refine Summable.of_norm ?_
      simp only [hnorm]
      exact hs
    exact (Equiv.neg (ratL T S)).summable_iff.1 h2
  have hinv := GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero (WO S T) (ratL T S) K hK hcov
    (ratL T S) (chiR ψ S T) lc lx la l0 ln lker (fun a ha => chiR_eq_zero hψ.1 a ha) μ 𝓕 hμ h𝓕 h1 Φ
    (hFc.comp (continuous_add_right x)) (fun γ hγ z => by simp only [hΦdef, add_assoc, hFp γ hγ]) hsJ
  simp only [hkey]
  have hre : ∑' γ : ratL T S, J (-γ) = ∑' a, J a := by
    have e := (Equiv.neg (ratL T S)).tsum_eq J
    simp only [Equiv.neg_apply] at e
    exact e
  rw [tsum_mul_left, hre, show (∑' a, J a) = Φ 0 from hinv]
  simp only [hΦdef, hFdef, zero_add]
  ring

end GlobalTheory.TranslateCoefInversion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierInversion_zero_compactQuotient_summable : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ) → ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ = Φ 0 := by
  first | exact @GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero | exact GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero | (intros; apply GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  first | exact @GlobalTheory.FockMoment.gaussMoment | exact GlobalTheory.FockMoment.gaussMoment | (intros; apply GlobalTheory.FockMoment.gaussMoment <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectorsStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl_relations_on_k_finite_vectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → IsGKSub ε ρ (kFinVec ε ρ) → ∃ A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε ρ), (∀ X ∈ lieSet ε, ∀ v, ((A X v : kFinVec ε ρ) : H) = dRep ρ X v) ∧ (∀ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P → GlRel (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) ∧ ∀ k : ℕ, etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) k = etr (fun a b => A (Matrix.single a b 1)) k) ∧ (∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ), actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1)) p v : kFinVec ε ρ) : H)) ∧ (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((etr (fun a b => A (Matrix.single a b 1)) k w : kFinVec ε ρ) : H) = ρ κ ((etr (fun a b => A (Matrix.single a b 1)) k v : kFinVec ε ρ) : H)) ∧ ∀ χ : Fin n → ℂ, HasInfChar ε χ ρ → ∀ (k : ℕ) v, etr (fun a b => A (Matrix.single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  first | exact @GlobalTheory.GKLie.kFin_glModule | exact GlobalTheory.GKLie.kFin_glModule | (intros; apply GlobalTheory.GKLie.kFin_glModule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.LiftOntoGood

theorem mem_range_of_fixed {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (hsa : LinearMap.adjoint e = e) (hid : e * e = e) (hfix : ∀ y, e (th y) = th y)
    (hinj : ∀ v, e v = v → LinearMap.adjoint th v = 0 → v = 0) (x : Y) (hx : e x = x) : x ∈ LinearMap.range th := by
  have hcomp : e ∘ₗ th = th := LinearMap.ext hfix
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range th)]
  intro v hv
  have hv0 : LinearMap.adjoint th v = 0 := by
    refine ext_inner_left ℂ fun z => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact hv _ (LinearMap.mem_range_self _ z)
  have h1 : LinearMap.adjoint th (e v) = 0 := by
    have e2 : LinearMap.adjoint th (e v) = LinearMap.adjoint (e ∘ₗ th) v := by
      rw [LinearMap.adjoint_comp, hsa, LinearMap.comp_apply]
    rw [e2, hcomp, hv0]
  have h2 : e (e v) = e v := by rw [← Module.End.mul_apply, hid]
  have h3 : e v = 0 := hinj (e v) h2 h1
  rw [← hx, ← LinearMap.adjoint_inner_left, hsa, h3, inner_zero_left]

set_option maxHeartbeats 1000000 in

theorem goodW_le_range : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp _ _ hU j
  have hM : R.toRealDat.IsModels := hC.base.models
  have hC3 := RealDat3.characterisation_of_weak hC hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hsa : LinearMap.adjoint (GlobalTheory.Hk3.eH R.toRealDat j) = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.LiftScalarL.adjoint_eH R.toRealDat hM hX j
  have hc : ∀ g, ∑ a, RealDat.eC (A := A3.A) (sg0 D A3.A) a * RealDat.eC (A := A3.A) (sg0 D A3.A) (a⁻¹ * g) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g := fun g => GlobalTheory.Hk3.conv_map_idem _ (idemOf_mul_self A3.A.X hX) (sg0 D A3.A) g
  have hidem : GlobalTheory.Hk3.eH R.toRealDat j * GlobalTheory.Hk3.eH R.toRealDat j = GlobalTheory.Hk3.eH R.toRealDat j :=
    GlobalTheory.Hk3.sum_rep_idem _ _ hc
  have hinj := (hM.HW j (sg0 D A3.A)).1
  have hrange := (hM.HW j (sg0 D A3.A)).2.1
  have hfixth : ∀ y, GlobalTheory.Hk3.eH R.toRealDat j (R.thG j A3.A.μ0 y) = R.thG j A3.A.μ0 y := by
    intro y
    have hm := hC3.thP.thF_mem j A3.A.μ0 y
    rw [← hrange] at hm
    obtain ⟨x0, hx0⟩ := hm
    have e1 : R.thG j A3.A.μ0 y = GlobalTheory.Hk3.eH R.toRealDat j x0 := by
      apply hinj
      rw [hC3.thP.thG j A3.A.μ0 y, ← hx0, GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j x0]
    rw [e1, ← Module.End.mul_apply, hidem]
  have key := mem_range_of_fixed (R.thG j A3.A.μ0) (GlobalTheory.Hk3.eH R.toRealDat j) hsa hidem hfixth (hUp j A3.A.μ0)
  intro w hw
  have hw' : w ∈ LinearMap.range ((R.toCx3 F).w0C false j) := hw
  rw [GlobalTheory.LevelRange.range_w0C_eq R F hOk hC hU false j] at hw'
  obtain ⟨x, rfl⟩ : ∃ x : (R.HW j (sg0 D A3.A)).H, Tw.mk (twAt D.what₂.embLL A3.A.v0) x = w := ⟨w, rfl⟩
  have hgood : (R.HW j (sg0 D A3.A)).e x ∈
      R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := hw'
  have hfix : GlobalTheory.Hk3.eH R.toRealDat j x = x := by
    apply hinj
    rw [GlobalTheory.LiftScalarL.e_eH R.toRealDat hM j]
    exact GlobalTheory.LiftScalarCompare.postOn_of_good hgood
  obtain ⟨y, hy⟩ := key _ hfix
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hC.phase j).1, norm_zero] at this
    exact one_ne_zero this
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y), ?_⟩
  show cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.μ0 ((cj (twAt D.what₂.embLL A3.A.v0) (R.phs j))⁻¹ • y) = x
  rw [map_smul, smul_inv_smul₀ hne, hy]

end GlobalTheory.LiftOntoGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDepthPaysEveryLossStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridDepth_pays_every_loss : DepthPays := by
  first | exact @GlobalTheory.SepPer.depth_pays | exact GlobalTheory.SepPer.depth_pays | (intros; apply GlobalTheory.SepPer.depth_pays <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.HaarCoords

theorem haar_coords : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure ∧ lB.IsAddHaarMeasure ∧ lC.IsAddHaarMeasure ∧ SFinite μ ∧ SFinite lB ∧ SFinite lC ∧ Measurable (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∧ ∃ ν₀ : Measure (flagN d), ν₀.IsHaarMeasure ∧ ν₀.map Subtype.val = (μ.prod (lB.prod lC)).map (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d
  obtain ⟨iU1, iU2, iU3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨-, familyMassSecondLine, iM3, iM4, -⟩ := lattice_Mx D ρ S₀.rank
  obtain ⟨-, indexCSecond, iC3, iC4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨iN1, iN2, iN3, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have hcl : IsClosed ((skewA D ρ : Set (Mx D ρ ρ))) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : T2Space (skewA D ρ) := inferInstance
  let μ : Measure (UX D ρ) := Measure.haar
  let lB : Measure (Mx D ρ S₀.rank) := Measure.addHaar
  let lC : Measure (skewA D ρ) := Measure.addHaar
  obtain ⟨e, he⟩ := GlobalTheory.MixPer.flagCoord_homeo D S S₀ ρ d
  have hΦ : (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
      Subtype.val ∘ e := funext fun p => (he p).symm
  have hem : Measurable e := e.continuous.measurable
  refine ⟨μ, lB, lC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hΦ]; exact (continuous_subtype_val.comp e.continuous).measurable
  refine ⟨(μ.prod (lB.prod lC)).map e, ?_, ?_⟩
  · haveI := Measure.IsFiniteMeasureOnCompacts.map (μ.prod (lB.prod lC)) e
    haveI : ((μ.prod (lB.prod lC)).map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
    suffices h : ((μ.prod (lB.prod lC)).map e).IsMulLeftInvariant from ⟨⟩
    refine ⟨fun g => ?_⟩
    obtain ⟨p₀, hp₀⟩ := e.surjective g
    have hg : (g : GA D S) = d.levi p₀.1.1 * (d.nB p₀.2.1 * d.nC p₀.2.2) := by rw [← hp₀, he]
    obtain ⟨⟨u', hu'⟩, b', c'⟩ := p₀
    obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.HaarCoords.transl_nB_preserves D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance b'
    obtain ⟨Tc, hTc, hTc'⟩ := GlobalTheory.HaarCoords.transl_nC D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance c'
    let Ta : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) :=
      Prod.map (fun u => ⟨u', hu'⟩ * u) id
    have hTa : MeasurePreserving Ta (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) :=
      (measurePreserving_mul_left μ _).prod (MeasurePreserving.id _)
    have hT := hTa.comp (hTb.comp hTc)
    have key : (fun x => g * x) ∘ e = e ∘ (Ta ∘ Tb ∘ Tc) := by
      funext p
      apply Subtype.ext
      have h3 : ∀ q, d.levi (Ta q).1.1 * (d.nB (Ta q).2.1 * d.nC (Ta q).2.2) =
          d.levi u' * (d.levi q.1.1 * (d.nB q.2.1 * d.nC q.2.2)) := fun q => by
        simp only [Ta, Prod.map_fst, Prod.map_snd, id, Subgroup.coe_mul, map_mul, mul_assoc]
      simp only [Function.comp_apply, Subgroup.coe_mul, he]
      rw [h3, hTb', hTc', hg]
      simp only [mul_assoc]
    rw [Measure.map_map (measurable_const_mul g) hem, key, ← Measure.map_map hem hT.measurable, hT.map_eq]
  · rw [Measure.map_map continuous_subtype_val.measurable hem, hΦ]

end GlobalTheory.HaarCoords

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfAdelicHomDecomposeIsotropicMiddleComplementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfAdelicHom_decompose_isotropic_middle_complement : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  first | exact @GlobalTheory.HalfDecomp.half_decomp | exact GlobalTheory.HalfDecomp.half_decomp | (intros; apply GlobalTheory.HalfDecomp.half_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParamStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  first | exact @GlobalTheory.TermDeriv.hasDerivAt_coef_oneP | exact GlobalTheory.TermDeriv.hasDerivAt_coef_oneP | (intros; apply GlobalTheory.TermDeriv.hasDerivAt_coef_oneP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExpStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ), HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ)) (Complex.exp (∑ k, x k)) := by
  first | exact @GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp | exact GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp | (intros; apply GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (G : VCx ι a b → ℂ), Differentiable ℂ G → ∀ z₀ : VCx ι a b, HasSum (fun m : DVar ι a b →₀ ℕ => (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) (G z₀) := by
  first | exact @GlobalTheory.FockTaylor.hasSum_derivAt0 | exact GlobalTheory.FockTaylor.hasSum_derivAt0 | (intros; apply GlobalTheory.FockTaylor.hasSum_derivAt0 <;> assumption)
end


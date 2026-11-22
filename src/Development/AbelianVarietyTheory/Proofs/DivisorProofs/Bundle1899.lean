import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntertwinerUnique
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical
namespace GlobalTheory.ArchInvForm

theorem trace_half {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (⅟(2 : mixedEmbedding.mixedSpace F) * z) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z / 2 := by
  have h : (2 : ℝ) • (⅟(2 : mixedEmbedding.mixedSpace F) * z) = z := by
    rw [Algebra.smul_def, map_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have h2 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h
  rw [map_smul, smul_eq_mul] at h2
  linarith

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w φ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ) w φ := by
  funext x
  simp only [schr, GlobalTheory.ArchUniq.schrF, hψ]
  congr 3
  rw [map_add, trace_half]
  rfl

theorem int_phase_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @Measure V (borel V)) (hμ : @Measure.IsAddHaarMeasure V _ _ (borel V) μ)
    (u v p : V → ℂ) (hp : ∀ x, ‖p x‖ = 1) (a : V) :
    @integral V ℂ _ _ (borel V) μ (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) =
      @integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (v x)) := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have e : (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) = fun x => u (x + a) * starRingEnd ℂ (v (x + a)) := by
    funext x
    have h1 : p x * starRingEnd ℂ (p x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp x]; simp
    rw [map_mul]
    linear_combination (u (x + a) * starRingEnd ℂ (v (x + a))) * h1
  rw [e]
  exact integral_add_right_eq_self (μ := μ) (fun x => u x * starRingEnd ℂ (v x)) a

theorem const_of_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  intro _ F _ _ _ κ _ ψ hψ T A hT
  have hP := GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) κ
  have hnorm : ∀ t, ‖ψ t‖ = 1 := by
    intro t
    rw [hψ, show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t : ℝ) : ℂ) =
      ((-(2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hK : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w (f f₁ g g₁ : SInf F κ), (f₁ : _ → ℂ) = schr ψ w f → (g₁ : _ → ℂ) = schr ψ w g →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ w f f₁ g g₁ hf hg
    have e1 := hT w f f₁ hf
    have e2 := hT w g g₁ hg
    have e : (fun x => T f₁ x * starRingEnd ℂ (T g₁ x)) = fun x =>
        (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) * T f (x + (A w).1)) *
          starRingEnd ℂ (ψ (x ⬝ᵥ (A w).2 + ⅟(2 : mixedEmbedding.mixedSpace F) * ((A w).1 ⬝ᵥ (A w).2)) *
            T g (x + (A w).1)) := by
      funext x
      rw [show T f₁ x = schr ψ (A w) (T f) x from congrFun e1 x, show T g₁ x = schr ψ (A w) (T g) x from congrFun e2 x]
      rfl
    rw [e]
    exact int_phase_shift μ hμ _ _ _ (fun x => hnorm _) _
  have hmod : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f f' g g' : SInf F κ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ L f f' g g' hf hg
    obtain ⟨b, hb⟩ := GlobalTheory.ArchUniqStd.exists_right hP ((-(1 / (2 * Real.pi))) • L)
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = Complex.exp (Complex.I * (L x : ℂ)) * u x) →
        (u' : _ → ℂ) = schr ψ (0, b) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      rw [hu x]
      simp only [GlobalTheory.ArchUniq.schrF]
      rw [add_zero, hP.zero_left, zero_div, add_zero, hb, ContinuousLinearMap.smul_apply, smul_eq_mul]
      congr 2
      push_cast
      field_simp
    exact hK μ hμ (0, b) f f' g g' (hw f f' hf) (hw g g' hg)
  have htr : ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ (a : κ → mixedEmbedding.mixedSpace F) (f f' g g' : SInf F κ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @integral _ ℂ _ _ (borel _) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T g x)) := by
    intro μ hμ a f f' g g' hf hg
    have hw : ∀ (u u' : SInf F κ), (∀ x, u' x = u (x + a)) → (u' : _ → ℂ) = schr ψ (a, 0) u := by
      intro u u' hu
      rw [schr_eq_schrF ψ hψ]
      funext x
      simp [GlobalTheory.ArchUniq.schrF, hu, hP.zero_right]
    exact hK μ hμ (a, 0) f f' g g' (hw f f' hf) (hw g g' hg)
  letI mV : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  set μ₀ : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar with hμ₀
  have hμ₀H : μ₀.IsAddHaarMeasure := by rw [hμ₀]; infer_instance
  obtain ⟨c, hc⟩ := GlobalTheory.T.translation_invariant_form_const_l2 _ μ₀ hμ₀H T (htr μ₀ hμ₀H) (GlobalTheory.T.translation_character_invariant_form _ μ₀ hμ₀H T (hmod μ₀ hμ₀H))
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.ArchUniqStd.exists_one (V := κ → mixedEmbedding.mixedSpace F)
  have hself : ∀ h : SInf F κ, ∫ x, h x * starRingEnd ℂ (h x) ∂μ₀ = ((∫ x, ‖h x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) :=
    fun h => GlobalTheory.WrongSignGauss.ip_self μ₀ h
  have hint : Integrable (fun x => ‖Φ x‖ ^ 2) μ₀ := by
    refine (GlobalTheory.WrongSignGauss.integrable_ip μ₀ Φ Φ).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  have hn : 0 < ∫ x, ‖Φ x‖ ^ 2 ∂μ₀ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
    have ho : IsOpen (Function.support fun x => ‖Φ x‖ ^ 2) := (Φ.continuous.norm.pow 2).isOpen_support
    exact ho.measure_pos μ₀ ⟨0, by simp [hΦ]⟩
  have hm : 0 ≤ ∫ x, ‖T Φ x‖ ^ 2 ∂μ₀ := integral_nonneg fun x => sq_nonneg _
  have hcΦ := hc Φ Φ
  change ∫ x, T Φ x * starRingEnd ℂ (T Φ x) ∂μ₀ = c * ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ₀ at hcΦ
  rw [hself, hself] at hcΦ
  have hcc : c = (((∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀) : ℝ) : ℂ) := by
    have hn' : ((∫ x, ‖Φ x‖ ^ 2 ∂μ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    rw [eq_div_iff hn', hcΦ]
  refine ⟨(∫ x, ‖T Φ x‖ ^ 2 ∂μ₀) / (∫ x, ‖Φ x‖ ^ 2 ∂μ₀), div_nonneg hm hn.le, fun μ hμ f f' => ?_⟩
  haveI : μ.IsAddHaarMeasure := hμ
  have hs : μ = Measure.addHaarScalarFactor μ μ₀ • μ₀ := Measure.isAddLeftInvariant_eq_smul μ μ₀
  have hcf := hc f f'
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ₀ = c * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ₀ at hcf
  change ∫ x, T f x * starRingEnd ℂ (T f' x) ∂μ = _ * ∫ x, f x * starRingEnd ℂ (f' x) ∂μ
  rw [hs, integral_smul_nnreal_measure, integral_smul_nnreal_measure, hcf, ← hcc]
  simp only [NNReal.smul_def, smul_eq_mul, Complex.real_smul]
  ring

end GlobalTheory.ArchInvForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.FunObj

theorem routeBig_kerBig_integrableOn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ g : GA D (G.V (.grid i (j + 1))), IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := by
  intro D T L sc G hWC μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁ g
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt W t i j hT M hM
  have key : ∀ d ∈ Θ.support, Integrable (fun u => Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁)) ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := by
    intro d hd
    obtain ⟨ε, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, he⟩ := GlobalTheory.T.routeBigVertex_kernelProduct_eq_const_mul_thetaKernel hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
    obtain ⟨N, C, hmi⟩ := hWC D W.ψ W.θ W.θ_is ε _ X χ χ' ω hω p hsig (hX ▸ hrk) _ _ hHF Φ hΦ
    refine Integrable.const_mul ?_ _
    simp_rw [he]
    exact ((hmi h).1).const_mul c
  have e : kerBig W Θ g g₁ = fun u => ∑ d ∈ Θ.support, Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁) := by
    funext u; rfl
  rw [IntegrableOn, e]
  exact integrable_finsetSum _ key

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelNormLeConstMulThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRouteIdent

open GlobalTheory.RouteSeesaw

theorem kerBig_norm_le_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ (ε : Bool) (ω : GlobalTheory.Grid.WRep (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))))
      (χ χ' : (AE D)ˣ →* Circle) (Φ : WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ) (C₀ : ℝ),
      GlobalTheory.Grid.IsWeil W.ψ ε _ _ χ χ' ω ∧ IsThetaFunO W.ψ (GlobalTheory.Grid.sgn ε (G.V (.grid (i + 1) (j + 1)))) _ Φ ∧
      ∀ g u, ‖kerBig W Θ g g₁ u‖ ≤ C₀ * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hd := GlobalTheory.T.isThetaFunO_of_matchedSquare_bigRoute hL W B ρ t i j Θ Θ' hΘ
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, χa, χb, hω₂, hadj⟩ := GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree W.ψ W.ψ_std _ _ _ _ _ h2
  obtain ⟨ω', χ, χ', c, hω', hc, hbox⟩ := GlobalTheory.T.seesaw_oneSource_orthogonalSumTargets W.ψ W.ψ_std _ _ _ _ _ _ _ _ ω₂ h1 hω₂
  let S := G.V (.grid (↑i + 1) (↑j + 1))
  let A := G.V (.grid (↑i) (↑j + 1))
  let Bs := G.V (.grid (↑i + 1) ↑j)
  let Φ : WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ :=
    Θ.sum fun d a => a • box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))
  have hth : ∀ d ∈ Θ.support, IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs)
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) := fun d hdm =>
    (hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).1
  have e : ∀ u g, ∀ d ∈ Θ.support, thetaKO ω' (negGA S u) (GlobalTheory.SquareComm.blk A Bs (g, g₁))
      (box2 (S := negSp S) (A := A) (B := Bs) d.1.2 (fun y => d.2 (adjM S Bs y))) =
      c (negGA S u) g g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁) := fun u g d hdm => by
    rw [(hbox _ _ (hd d hdm).1 ((hadj _ (hd d hdm).2).1)).2, (hadj _ (hd d hdm).2).2]
    rfl
  refine ⟨true, ω'.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)), χ, χ', Φ, 1, hω', ?_, ?_⟩
  · let U : Submodule ℂ (WO (negSp S) (GlobalTheory.Doubling.hsum A Bs) → ℂ) :=
      { carrier := {g | IsThetaFunO W.ψ (negSp S) (GlobalTheory.Doubling.hsum A Bs) g}
        add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
        zero_mem' := GlobalTheory.OrientedHeis.theta_zero
        smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
    show Φ ∈ U
    exact U.sum_mem fun d hdm => U.smul_mem _ (hth d hdm)
  · intro g u
    have key : ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0 = c (negGA S u) g g₁ * kerBig W Θ g g₁ u := by
      simp only [Φ, kerBig, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hdm => ?_
      have := e u g d hdm
      simp only [thetaKO] at this
      rw [this]; ring
    refine le_of_eq ?_
    show ‖kerBig W Θ g g₁ u‖ = 1 * ‖ω' (negGA S u, GlobalTheory.SquareComm.blk A Bs (g, g₁)) Φ 0‖
    rw [key, norm_mul, hc, one_mul, one_mul]

end GlobalTheory.BigRouteIdent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigSeesaw

open GlobalTheory.RouteSeesaw

theorem swap_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω)
    {ω₀ : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hω₀ : IsWeilDatumO ψ S' T' χT χS ω₀)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (g : GA D S) (h : GA D T) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt S g).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt T h⁻¹).submatrix e₂ e₂)ᵀ) :
    ω₀ (g', h') (fun u => f (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D))) 0 = ω (g, h) f 0 := by
  obtain ⟨φ', c1, q1, m1, s1, d1⟩ := GlobalTheory.GrpConj.exists_conj_equiv D S T' e₁ hT'
  obtain ⟨φ, c2, q2, m2, s2, d2⟩ := GlobalTheory.InvTransposeIso.grp_contra D T S' e₂ hS'
  obtain ⟨L, hL, hLs, cL, cL', rL, iL, fL⟩ := GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D S T S' T' e₁ e₂
  have m1' : ∀ h, Formalism.L2.Theta.mt T' h = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D)).submatrix e₁ e₁ := fun h => by
    ext i j
    have t3 := congrArg (cA D) (congrFun (congrFun (m1 h) i) j)
    simp only [Matrix.map_apply, Formalism.L2.Theta.cA_cA] at t3
    exact t3.symm
  have hact : ∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x) := by
    intro g h x
    have u1 : ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ * S.gram.map (incA D) =
        S.gram.map (incA D) * Formalism.L2.Theta.mt S (φ' h)⁻¹ := by
      have k := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram S (φ' h)
      have k2 : Formalism.L2.Theta.mt S (φ' h) * Formalism.L2.Theta.mt S (φ' h)⁻¹ = 1 := by
        simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
      have k3 := congrArg (· * Formalism.L2.Theta.mt S (φ' h)⁻¹) k
      simp only [Matrix.mul_assoc, k2, Matrix.mul_one] at k3
      exact k3
    have u2 : Formalism.L2.Theta.mt T (φ g) = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ.submatrix e₂.symm e₂.symm := by
      rw [← m2]; simp
    have u3 : (Formalism.L2.Theta.mt T' h)ᵀ.submatrix e₁.symm e₁.symm = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ := by
      rw [m1']; simp
    rw [hL]
    unfold actO
    rw [hL, u2, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ e₂.symm,
      ← Matrix.submatrix_mul_equiv _ _ _ e₁.symm, u3]
    simp only [Matrix.mul_assoc, u1]
  have hs : ∀ x y, symplO S T (L x) (L y) = symplO S' T' x y := fun x y => by
    rw [hL, hL]; exact GlobalTheory.DarbouxSymp.symplO_darboux D S T S' T' e₁ e₂ hT' hS' x y
  obtain ⟨ω', hw, hω'⟩ := GlobalTheory.SwapWeil.isWeilDatumO_swap D ψ S T S' T' (by simpa using Fintype.card_congr e₂)
    (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom
    φ'.toMonoidHom cL cL' rL hs iL fL c2 c1 q2 q1 hact s2 s1 d2 d1 χS χT ω hω
  have th : IsThetaFunO ψ S' T' (fun w => f (L w)) :=
    GlobalTheory.SwapWeil.theta_pull L cL (fun x hx => (rL x).2 hx) hs (fun x hx => (iL x).2 hx) (fun x hx => (fL x).2 hx) hf
  have a1 : φ' h' = g := by
    have k : h' = φ'.symm g := GlobalTheory.MixModel.mt_injective T' (by rw [hh, m1', MulEquiv.apply_symm_apply])
    rw [k, MulEquiv.apply_symm_apply]
  have a2 : φ g' = h := by
    have k : g' = φ.symm h := GlobalTheory.MixModel.mt_injective S' (by
      have := m2 (φ.symm h)⁻¹
      rw [inv_inv, map_inv, MulEquiv.apply_symm_apply] at this
      rw [hg, this, Matrix.transpose_transpose])
    rw [k, MulEquiv.apply_symm_apply]
  have k9 := congrFun (hω' g' h' f) 0
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, a1, a2, map_zero] at k9
  simp only [← hL]
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hω.std S' T' χT χS ω₀ ω' hω₀ hw (g', h') _ th]
  exact k9

theorem adjM_mul_neg {D : D7} (S B : HSp D) (y : Matrix (Fin S.rank) (Fin B.rank) (AE D)) :
    adjM S B (HMul.hMul yᵀ ((negSp S).gram.map (incA D)) : Matrix (Fin B.rank) (Fin S.rank) (AE D)) =
      -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG B (y.map (cA D)) := by
  have h2 := GlobalTheory.RouteCoords.inv_mul_gram S
  have h3 : (((negSp S).gram.map (incA D)).map (cA D))ᵀ = -(S.gram.map (incA D)) := by
    rw [GlobalTheory.RouteCoords.gram_conj_transpose, negSp_gram, Matrix.map_neg _ (map_neg _)]
  unfold adjM
  rw [Matrix.map_mul, transpose_mul, h3, transpose_map, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_neg, h2,
    Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]
  rfl

set_option maxHeartbeats 1000000 in

theorem seesaw_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : IsTripleOf W M t i j e Bs Γ X) (hTr : IsTriple Bs Γ X om om')
    (hT₁ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).IsSymm) (hT₂ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).Nondegenerate)
    (LT : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E)) (hLT : LT.IsLattice D.host.E)
    (hUT : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ) LT) (sgT : (D.host.E →+* ℂ) → ℕ × ℕ)
    (hS₁ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).IsSymm)
    (hS₂ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).Nondegenerate)
    (LS : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E)) (hLS : LS.IsLattice D.host.E)
    (hUS : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)) LS) (sgS : (D.host.E →+* ℂ) → ℕ × ℕ)
    (ω : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) × GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) →*
      Module.End ℂ (WO (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) → ℂ))
    (hω : IsWeilDatumO W.ψ (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS)
      (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) (X.β / X.α) X.β ω)
    (g : GA D (spV G i j)) (g₁ : GA D (spV₁ G i j)), ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ (f₁ : WO (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) → ℂ)
      (f₂ : WO (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) → ℂ),
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) f₁ →
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) f₂ →
      ∀ (u : GA D (spW G i j)) (g' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS))
        (h' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)),
      Formalism.L2.Theta.mt _ h' = (conjU (spW G i j) 1 h.JW u).1.1 → Formalism.L2.Theta.mt _ g' = ((blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))⁻¹).1.1ᵀ →
      W.kerA (.right i (j + 1)) f₁ g u * W.kerA (.down t (i + 1) j) f₂ u g₁ =
        ξ * ω (g', h') (fun x => f₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ) *
          f₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x)) 0 := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr hT₁ hT₂ LT hLT hUT sgT hS₁ hS₂ LS hLS hUS sgS ω hω g g₁
  have hi := i.2
  have hj := j.2
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := GlobalTheory.SquareDict.ExactBig.adjoint_exact h2
  have hcard : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
    simpa using Fintype.card_congr e
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    have hev := hTr.geo.even
    rw [← hcard, Nat.even_iff] at hev
    simp only [spV, spV₁] at hev
    omega
  have cT : X.β / X.α = G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    rw [h.α, h.β]
    simp only [GridData.chrT, GridData.chrS, GridData.chr, GlobalTheory.SquareDict.ExactBig.attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (negSp (spW G i j))
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) X.β (G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT (hecke_mul' h1.hecT hω₂.hecT) hω.resT
    (resEta_mul h1.resT hω₂.resT)
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g₁
  refine ⟨(((G.chrS (.chi i (j + 1)) / X.β) x : Circle) : ℂ) * ((((G.chrT (.mu t (i + 1) j))⁻¹ / X.β) y : Circle) : ℂ),
    mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _), fun f₁ f₂ hf₁ hf₂ u g' h' hh hg => ?_⟩
  have k := GlobalTheory.SquareDict.ExactBig.seesaw_exact h1 hω₂ hA hf₁ (hadj _ hf₂).1 (negGA _ u) g g₁ hx hy
  rw [(hadj _ hf₂).2] at k
  refine k.trans ?_
  congr 1
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hJu : IsUnit Γ.W.J.det := by
    rw [hJ, det_smul, det_submatrix_equiv_self, det_transpose]
    exact (IsUnit.mk0 _ (pow_ne_zero _ hξ)).mul (GlobalTheory.MixModel.gram_isUnit_det _)
  have e0 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT).gramᵀ =
      -((negSp (spW G i j)).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf, negSp_gram]
    show Γ.V.J = - -(spW G i j).gram
    rw [h.JW, one_smul, neg_neg]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e0.trans ?_
    rw [hJ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]
  have hbox : IsThetaFunO W.ψ (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
      (box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) f₁
        (fun y => f₂ (adjM (spW G i j) (spV₁ G i j) y))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec _ _).isThetaFunO_boxT hf₁ (hadj _ hf₂).1
  have hω' := hω
  rw [cT] at hω'
  have key := swap_eq (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
    (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)
    (Equiv.refl (Fin (spW G i j).rank)) e₂ hT' hS' hA hω'
    hbox (negGA _ u) (GlobalTheory.SquareComm.blk _ _ (g, g₁)) g' h' hh (by
      rw [hg, ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine key.symm.trans (congrArg (fun F => ω (g', h') F 0) ?_)
  funext z
  have k1 : ∀ a, e₂.symm (Fin.castAdd _ a) = e (.inl a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_castAdd a)
  have k2 : ∀ a, e₂.symm (Fin.natAdd _ a) = e (.inr a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_natAdd a)
  refine congrArg₂ (· * ·) (congrArg f₁ ?_) (congrArg f₂ ?_)
  · ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k1 a)
  · refine Eq.trans (congrArg (adjM (spW G i j) (spV₁ G i j)) ?_)
      (adjM_mul_neg (spW G i j) (spV₁ G i j) (z.submatrix id fun k => e (.inr k)))
    ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k2 a)

end GlobalTheory.BigSeesaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroupStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_mul_of_unipotent_cover_discreteSubgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  first | exact @GlobalTheory.SphEis.card_le_mul_of_unip_cover | exact GlobalTheory.SphEis.card_le_mul_of_unip_cover | (intros; apply GlobalTheory.SphEis.card_le_mul_of_unip_cover <;> assumption)
end


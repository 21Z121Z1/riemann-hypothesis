import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0888
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DblVacAtInhabited
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0892
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0896
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
noncomputable section

namespace GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem superDiag_blockGL {R : Type} [CommRing R] {j n : ℕ} (hj : j ≤ n) (g : GL (Fin j) R) :
    GlobalTheory.Whittaker.superDiag (blockGL hj g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  simp only [Finset.sum_filter]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
  · intro i hi
    have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · rw [coe_blockGL, blockMat_apply, dif_neg hij, if_neg]
      intro h; rw [h] at hb; omega
    · rfl
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro b hb
      have hbj : ¬ (b : ℕ) < j := fun h => hb ⟨⟨b, h⟩, rfl⟩
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dif_pos (by simp), dif_neg hbj]
      · rfl
    · intro b
      simp only [Fin.coe_castLE]
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dif_pos (by simp), dif_pos (by simp)]
        rfl
      · rfl

variable {E : Type} [Field E] [NumberField E]

theorem psiN_blockGL {j n : ℕ} (hj : j ≤ n) (g : GA E j) :
    GlobalTheory.JSW.psiN (blockGL hj g : GA E n) = GlobalTheory.JSW.psiN g := by
  unfold GlobalTheory.JSW.psiN
  rw [superDiag_blockGL]

theorem norm_psiN {a : ℕ} (u : GA E a) : ‖GlobalTheory.JSW.psiN u‖ = 1 := by
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem blockGL_mem_NA {j n : ℕ} (hj : j ≤ n) {u : GA E j} (hu : u ∈ GlobalTheory.JSW.NA E j) :
    (blockGL hj u : GA E n) ∈ GlobalTheory.JSW.NA E n := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb hc
    · exact h1 _ _ (by rw [Fin.lt_def] at hik ⊢; exact hik)
    · rfl
    · exact absurd hik (by rw [hc]; exact lt_irrefl _)
    · rfl
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb
    · exact h2 _
    · rfl
    · exact absurd rfl hb

theorem detAbs_unip {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GlobalTheory.RSnm.detAbs u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  rw [GlobalTheory.RSnm.detAbs, hd, map_one]; rfl

end GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL) in

theorem GlobalTheory.RSnmUnfProps.uIntNM_props : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) →
    Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)) ∧
    Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) ∧
    (∀ x : ℝ, Measurable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x)) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (u * g))‖ = ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ∧
      ‖GlobalTheory.JSW.whit φ' (u * g)‖ = ‖GlobalTheory.JSW.whit φ' g‖ ∧
      GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g ∧ GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g ∧
      ∀ x : ℝ, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (u * g) = GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g) ∧
    ∀ (x : ℝ) (g : GA E (m + 1)), ‖GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g‖ ≤
      (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) +
        ‖GlobalTheory.JSW.whit φ' g‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x) / 2 := by
  intro E _ _ _ m r S φ φ' F hW hW' hl hl' hF
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  have cW : Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (blockGL hmn g)) :=
    hW.comp (GlobalTheory.RSnm.continuous_blockGL hmn)
  have cF : Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) :=
    hF.comp GlobalTheory.ZUnfTheta.continuous_lastRow
  have cD : ∀ y : ℂ, Continuous (fun g : GA E (m + 1) => ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ y) := fun y =>
    (Complex.continuous_ofReal.comp GlobalTheory.RSnm.continuous_detAbs).cpow continuous_const
      fun h => Complex.ofReal_mem_slitPlane.2 (GlobalTheory.RSnm.detAbs_pos h)
  have hwu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      GlobalTheory.JSW.whit φ (blockGL hmn (u * g)) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ (blockGL hmn g) := by
    intro u hu g
    have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    rw [map_mul, hl _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu'), GlobalTheory.RSnmUnfProps.psiN_blockGL]
  refine ⟨cW, cF, fun x => ?_, fun u hu g => ?_, fun x g => ?_⟩
  · unfold GlobalTheory.RSnmUnf.uIntNM
    exact (((cW.mul (Complex.continuous_conj.comp hW')).mul cF).mul (cD _)).measurable
  · have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    have hlr := GlobalTheory.ZEulProps.lastRow_unip hu g
    have hd : GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g := by
      rw [GlobalTheory.RSnm.detAbs_mul, GlobalTheory.RSnmUnfProps.detAbs_unip hu, one_mul]
    refine ⟨?_, ?_, hlr, hd, fun x => ?_⟩
    · rw [hwu u hu g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · rw [hl' u hu' g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · unfold GlobalTheory.RSnmUnf.uIntNM
      rw [hwu u hu g, hl' u hu' g, hlr, hd, map_mul]
      have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
      linear_combination (GlobalTheory.JSW.whit φ (blockGL hmn g) * conj (GlobalTheory.JSW.whit φ' g) *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)) * h1

  · have hdp := GlobalTheory.RSnm.detAbs_pos g
    have hre : ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2).re = (x - ((r : ℝ) + 1)) / 2 + x / 2 := by
      push_cast
      simp only [Complex.sub_re, Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
        Complex.one_re, Complex.natCast_im, Complex.one_im, Complex.add_im, Complex.ofReal_im]
      norm_num
      ring
    unfold GlobalTheory.RSnmUnf.uIntNM
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hdp, hre,
      Real.rpow_add hdp]
    have hA : GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) = (GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    have hB : GlobalTheory.RSnm.detAbs g ^ x = (GlobalTheory.RSnm.detAbs g ^ (x / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    rw [hA, hB]
    set a := ‖GlobalTheory.JSW.whit φ (blockGL hmn g)‖
    set b := ‖GlobalTheory.JSW.whit φ' g‖
    set c := ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖
    set α := GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)
    set β := GlobalTheory.RSnm.detAbs g ^ (x / 2)
    have hc : 0 ≤ c := norm_nonneg _
    nlinarith [mul_nonneg hc (sq_nonneg (a * α - b * β))]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SwSection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWPairProof

open GlobalTheory.RawLift

variable {D : D7}

theorem kernel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om →
    ∃ omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χV omh ∧
      ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsThetaFunO ψ (GlobalTheory.Doubling.dblSp W) V (dbl V W f₁ f₂) ∧
        ∀ h, thetaKO omh 1 h (dbl V W f₁ f₂) = thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) := by
  intro D ψ V W χV χW om hw
  have hS := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std V W
  have hom' := GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V W χV χW om hw
  have hr : ResEta D 1 (GlobalTheory.Doubling.dblSp W).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D W.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp W) V 1 χV hw.std
    ⟨continuous_const, fun _ => rfl⟩ hw.hecS hr hw.resS
  refine ⟨omh, homh, fun f₁ f₂ h₁ h₂ => ?_⟩
  have TC := GlobalTheory.DoublingTheta.thetaClause D ψ W V χW χV (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) omh hom' homh
  obtain ⟨hth, hrest⟩ := TC (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) (hS.theta _ h₂) (hS.theta _ h₁)
  refine ⟨hth, fun h => ?_⟩
  have e := (hrest 1 1 h).2
  have dd : ∀ f : WO V W → ℂ, GlobalTheory.PairLift.dag W V (GlobalTheory.PairLift.dag V W f) = f := fun f => by
    funext y; simp only [GlobalTheory.PairLift.dag, hS.invol, Complex.conj_conj]
  have d0 : GlobalTheory.PairLift.adjO V W 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have k : ∀ f : WO V W → ℂ, thetaKO (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) 1 h (GlobalTheory.PairLift.dag V W f) =
      starRingEnd ℂ (thetaKO om h 1 f) := fun f => by
    simp only [thetaKO, GlobalTheory.ConjAdjWeil.conjAdjoint_apply, dd]
    simp only [GlobalTheory.PairLift.dag, d0]
  have i1 : GlobalTheory.Doubling.io W (1, 1) = 1 := map_one _
  rw [i1, k, k, Complex.conj_conj] at e
  simp only [map_one, inv_one, Circle.coe_one, mul_one] at e
  rw [show dbl V W f₁ f₂ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) from rfl, e]
  simp only [Complex.star_def]
  ring

theorem terms : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
    ∀ (χ : (AE D)ˣ →* Circle) (omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ)),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χ omh →
    ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' →
      ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q,
        GlobalTheory.Eis.term (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W))
          (GlobalTheory.SiegelFormula.swSection W V ν 𝓖' omh (dbl V W f₁ f₂)) 1 q = lagTerm μ 𝓕 (fr (e q)) f₁ f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χ omh hω ν 𝓖' hν
  obtain ⟨omh', -, hK⟩ := kernel D ψ V W χV χW om hs.weil
  have hF := (hK f₁ f₂ h₁ h₂).1
  obtain ⟨e, he⟩ := GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ ν 𝓖' hν
  refine ⟨e, fun q => ?_⟩
  obtain ⟨C, hC, hq⟩ := he q
  rw [← GlobalTheory.T.doubled_lagrangian_term_frame_independent D ψ V W μ 𝓕 hs.covol hs.weil.std f₁ f₂ h₁ h₂ (e q) C (fr (e q)) hC (hs.frame _), ← hq]
  simp only [GlobalTheory.Eis.term, mul_one, GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero]
  congr 1
  funext y
  exact GlobalTheory.T.rational_source_acts_on_orientedTheta_by_substitution D ψ _ V 1 χ omh hω _ hF _ (q.out : GQ (GlobalTheory.Doubling.dblSp W)).2 _

theorem swPair (hW : GlobalTheory.Published.WeilSiegelFormulaUnitary) (D : D7) : SWPair D := by
  intro ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂
  rcases Nat.eq_zero_or_pos W.rank with h0 | hr
  · exact Model.swPair_rank_zero hs h0 f₁ f₂
  obtain ⟨omh, hω, hK⟩ := kernel D ψ V W χV χW om hs.weil
  obtain ⟨hF, hθ⟩ := hK f₁ f₂ h₁ h₂
  haveI := hs.haarV
  have hwitt : Formalism.MainNotions.SchurIrreducible.wittIdx V = 0 := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]
    exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef hs.sigOK hs.pos)
  obtain ⟨ν, 𝓖', hν⟩ := GlobalTheory.Size.exists_isCovolOne W V
  have P := (hW D W V νV hs.haarV hr (Or.inl hwitt)).2 ψ χV omh hω (dbl V W f₁ f₂) hF
  obtain ⟨-, hconv⟩ := P.2 hs.big ν 𝓖' hν
  obtain ⟨hc, hsum⟩ := hconv 1
  obtain ⟨e, he⟩ := terms D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χV omh hω ν 𝓖' hν
  have H1 := hc.hasSum
  rw [hsum] at H1
  have H2 : HasSum (fun Y : Lag W => lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    refine e.hasSum_iff.1 ?_
    convert H1 using 1
    funext q
    simp [he]
  have A : (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) =
      ⨍ h in 𝓗, thetaKO omh 1 h (dbl V W f₁ f₂) ∂νV :=
    GlobalTheory.ThetaMean.thetaMean_eq hω hF hs.fdV 1
  have vol := GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V νV 𝓗 ⟨hs.haarV, hs.fdV⟩
  have hv : ((νV 𝓗).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.2 vol)
  have key : ∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV = ((νV 𝓗).toReal : ℂ) *
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    rw [A, setAverage_eq, Complex.real_smul, Measure.real, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    simp_rw [hθ]
  rw [key]
  exact H2.mul_left _

end GlobalTheory.SWPairProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariant
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacTypeVec

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock GlobalTheory.JacBlockTwo ValuativeRel Matrix

theorem exists_irreducible_subquotient_rel (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
          ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y :=
  _root_.GlobalTheory.QuotientGenerator.exists_irreducible_subquotient G V ρ x hx

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mulSingle_false_mem_KO {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (a : Bool) :
    (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) a ∈ KO F (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_same]; exact hg
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _

theorem deltaHalf_mulSingle_false {r t : ℕ} {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) :
    deltaHalf F (Two (Fin r) (Fin t)) (Pi.mulSingle false g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow F _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_false_mem_KO (t := t) hg a)

theorem emb₂_one_eq {r t : ℕ} (g : GL (Fin r) F) :
    emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) =
      leviEmb F (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
  unfold emb₂
  rw [MonoidHom.comp_apply]
  congr 1
  funext a
  cases a <;> rfl

theorem jac_mulSingle_false {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin (r + t)) F) W) {g : GL (Fin r) F} (hg : g ∈ KO F (Fin r)) (v : W) :
    jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle false g) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v) := by
  rw [jac_mk, deltaHalf_mulSingle_false hg, inv_one, Units.val_one, one_smul, emb₂_one_eq]

theorem act_mulSingle_false_KOne {r t : ℕ} {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) F) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin r) F} (hg : g ∈ KOne F (Fin r)) :
    π (emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1)) v = v := by
  set h := emb₂ F (stdSum (rfl : r + t = r + t)) (g, 1) with hdef
  have hval : ∀ i j, h.val i j = Matrix.reindex (stdSum (rfl : r + t = r + t)) (stdSum (rfl : r + t = r + t))
      (Matrix.fromBlocks g.val 0 0 (1 : GL (Fin t) F).val) i j := fun i j => by
    rw [hdef, val_emb₂]
  have hKO : h ∈ KO F (Fin (r + t)) := by
    have hg' : g ∈ KO F (Fin r) := GlobalTheory.StepData.KOne_le_KO hg
    have e : h = leviEmb F (two (stdSum (rfl : r + t = r + t)))
        (Pi.mulSingle false g : Levi F (Two (Fin r) (Fin t))) := by
      rw [hdef, emb₂_one_eq]
    rw [e]
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_false_mem_KO hg' a), ?_⟩
    rw [← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_false_mem_KO hg' a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [hval, ← stdSum_inr', ← stdSum_inl']
    simp
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = g.val i j := fun i j => by
    rw [hval, ← stdSum_inl', ← stdSum_inl']
    simp
  have h2 : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, hval, ← stdSum_inr', ← stdSum_inr']
    simp
  have hg1 := GlobalTheory.StepData.mem_KOne.1 hg
  have key := hv h hKO (fun i j => by simp [h0]) (fun i j => by
      rw [h1]; have := hg1 i j; simpa [Matrix.sub_apply, Matrix.one_apply] using this) 1
    (by rw [h2, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

end Local

theorem exists_subquot_typeVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  intro hP F _ _ _ _ p _ r t χ W _ _ π z y ℓ hp hsm hirr hχ hy0 hy hℓ hz
  obtain ⟨hx0, hxt⟩ := jacquet_ne_zero_of_isBlockVec_two hP F r t χ W π y hsm hirr hχ hy0 hy
  set x : Jacquet π (unipRad F (two (stdSum (rfl : r + t = r + t)))) := Submodule.Quotient.mk y with hxdef
  obtain ⟨Y, _, _, τ, w, hτ, hsq, hw0, hrel⟩ :=
    exists_irreducible_subquotient_rel _ _ (jac (two (stdSum (rfl : r + t = r + t))) π) x hx0
  refine ⟨Y, inferInstance, inferInstance, τ, hτ, hsq, w, hw0, fun g hg => ?_, ?_, ℓ, hℓ, ?_⟩
  · have := hrel Unit {()} (fun _ => Pi.mulSingle true g) (fun _ => 1) _ (by
      simpa using hxt g hg)
    simpa using this
  · intro h hh
    have := hrel Unit {()} (fun _ => Pi.mulSingle false h) (fun _ => 1) 1 (by
      simp only [Finset.sum_singleton, one_smul]
      rw [hxdef, jac_mulSingle_false π (GlobalTheory.StepData.KOne_le_KO hh), act_mulSingle_false_KOne hy hh])
    simpa using this
  · have hsum : ∑ g ∈ z.coeff.support, z.coeff g • jac (two (stdSum (rfl : r + t = r + t))) π
        (Pi.mulSingle false (ℓ g)) x = (1 : ℂ) • x := by
      rw [one_smul, hxdef]
      have e : ∀ g ∈ z.coeff.support, z.coeff g • jac (two (stdSum (rfl : r + t = r + t))) π
          (Pi.mulSingle false (ℓ g)) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (z.coeff g • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) :=
        fun g _ => by rw [jac_mulSingle_false π ((hℓ g).mem_KO hp), Submodule.Quotient.mk_smul]
      rw [Finset.sum_congr rfl e]
      conv_rhs => rw [← hz, Finsupp.sum]
      exact (map_sum (Submodule.mkQ _) _ _).symm
    have := hrel _ z.coeff.support (fun g => Pi.mulSingle false (ℓ g)) z.coeff 1 hsum
    rw [one_smul] at this
    intro h0
    apply hw0
    rw [← this, ← h0, Finsupp.sum]
    rfl

end GlobalTheory.JacTypeVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWildStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneDualTransport_monodromy_dim_wild : ∀ (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧
    ((∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) → x.inePol σ = (X - 1) ^ x.lpDim) →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w'), σ ∈ wildSet D.nd (D.nd.plOm.1 w') → x'.inePol σ = (X - 1) ^ x'.lpDim) := by
  first | exact @GlobalTheory.WeilDeligne.ConjDual.mono_dim_wild | exact GlobalTheory.WeilDeligne.ConjDual.mono_dim_wild | (intros; apply GlobalTheory.WeilDeligne.ConjDual.mono_dim_wild <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRootsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneLabel_transportDual_inverseRoots : ∀ (D : D7) (k : Fin 2) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    ∀ γ γ' : GE D.nd, (∀ y, γ' (c y) = c (γ y)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ' x') =
      (Formalism.CyclotomicNorms.rootsBar (GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ x)).map (·⁻¹) := by
  first | exact @GlobalTheory.WeilDeligne.LabTransport.main | exact GlobalTheory.WeilDeligne.LabTransport.main | (intros; apply GlobalTheory.WeilDeligne.LabTransport.main <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.EigenSplitStrings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetRowOfGaloisRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0868

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PtStringAllOfHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtString

open GlobalTheory.SphPar GlobalTheory.SphGal GlobalTheory.Hk3 GlobalTheory.CuspRep GlobalTheory.IndefiniteRowSideFullHecke.EigenSplitStrings Formalism.UG Polynomial
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {D : D7}

theorem isSplit_iff_conj (P : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  rw [GlobalTheory.LFun.isSplit_iff, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · rintro ⟨w, w', hne, h, h'⟩ e
    have e' : Formalism.DivisionValues.conjPl P = P := HeightOneSpectrum.ext e
    have a := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have b := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h'
    rw [e', or_self] at a b
    exact hne (a.trans b.symm)
  · intro h
    exact ⟨P, Formalism.DivisionValues.conjPl P, fun e => h (congrArg HeightOneSpectrum.asIdeal e).symm, rfl,
      (GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)).symm⟩

section Sizes

variable {c q r t : ℕ} {m d : Fin c → ℕ} {B : Fin c → Multiset ℂˣ}

end Sizes

def HasParts (V : HSp D) (μ : D.what₂.Tau → Fin V.rank → ℝ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : GlobalTheory.DownLift.Sys D) : Prop :=
  haveI := host_isCMField D.host
  ∃ (r : ℕ) (m d : Fin r → ℕ) (π : ∀ i, CuspSub D.host.E (m i)),
    (∀ i, 1 ≤ m i ∧ 1 ≤ d i ∧ (π i).IsCsd) ∧ ∑ i, m i * d i = V.rank ∧
    (∀ τ, ∃ A A' : Fin r → Multiset ℂ,
      (∀ i, (π i).HasInfChar (tauE D τ) (A i) ∧ (π i).HasInfChar (ComplexEmbedding.conjugate (tauE D τ)) (A' i)) ∧
      ∑ i, spehInf (d i) (A i) = Finset.univ.val.map (fun a => (μ τ a : ℂ)) ∧
      ∑ i, spehInf (d i) (A' i) = Finset.univ.val.map (fun a => -(μ τ a : ℂ))) ∧
    ∀ P, OffS D S P → ∃ B : Fin r → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL P ((π i).locRep P) (B i)) ∧
      IsPar P V.rank (IsLab V P) (c P) (∑ i, spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i))

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

open GlobalTheory.DownLift GlobalTheory.DownLift.Params GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

def parV (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a : Fin (Vc D i).rank) : ℝ :=
  (((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℤ) : ℝ) + ((rhoVec (Vc D i).rank a : ℚ) : ℝ)

end Real

end GlobalTheory.PtString

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate Matrix

namespace GlobalTheory.ZUnfTheta

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem continuous_secRow {n : ℕ} :
    Continuous (fun y : Fin n → Cinf E => secRow y) := by
  refine continuous_matrix fun i j => ?_
  simp only [secRow, Matrix.of_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

theorem continuousOn_secInv {n : ℕ} :
    ContinuousOn (fun y : Fin n → Cinf E => secInv y) {y | IsUnit (secRow y).det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        ((secInv y.1 : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = (secRow y.1)⁻¹ := fun y => by
      rw [secInv, dif_pos (show IsUnit (secRow y.1).det from y.2), Matrix.coe_units_inv]
      rfl
    have hc : Continuous fun y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow y.1 :=
      continuous_secRow.comp continuous_subtype_val
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hinv : ContinuousAt Ring.inverse (secRow y.1).det := by
      have := NormedRing.inverse_continuousAt y.2.unit
      simpa using this
    have h2 : ContinuousAt (fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => (secRow z.1)⁻¹) y :=
      (continuousAt_matrix_inv _ hinv).comp (f := fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1)
        hc.continuousAt
    convert h2 using 1
    funext z
    exact h1 z
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        (((secInv y.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = secRow y.1 := fun y => by
      rw [secInv, dif_pos (show IsUnit (secRow y.1).det from y.2), inv_inv]
      rfl
    convert (continuous_secRow.comp continuous_subtype_val :
      Continuous fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1) using 1
    funext z
    exact h1 z

variable {m : ℕ}

theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  have h : natLat E N =
      (fun u : Af E => (N : Af E) * u) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [h]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

theorem continuous_lastRow : Continuous fun g : GA E (m + 1) => GlobalTheory.ZEul.lastRow g :=
  continuous_pi fun j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem (Fin.last m) j

theorem continuous_yInfRow : Continuous fun g : GA E (m + 1) => fun i => pInf E (GlobalTheory.ZEul.lastRow g i) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_lastRow)

theorem measurable_mulSec :
    Measurable fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
  have hy := continuous_yInfRow (E := E) (m := m)
  set s := {g : GA E (m + 1) | IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g i)).det} with hsdef
  have hs : IsOpen s := Units.isOpen.preimage ((continuous_secRow.comp hy).matrix_det)
  refine measurable_of_restrict_of_restrict_compl hs.measurableSet ?_ ?_
  · have hc : ContinuousOn (fun g : GA E (m + 1) =>
        g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) s :=
      continuousOn_id.mul (GlobalTheory.ConstTermSmooth.continuous_infGL.comp_continuousOn
        (continuousOn_secInv.comp hy.continuousOn fun g hg => hg))
    exact hc.restrict.measurable
  · convert (measurable_subtype_coe : Measurable (Subtype.val : (sᶜ : Set (GA E (m + 1))) → GA E (m + 1))) using 1
    funext g
    have hg : ¬ IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)).det := g.2
    show g.1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)) = g.1
    rw [secInv, dif_neg hg, map_one, mul_one]

theorem measurable_integrand {φ φ' : GA E (m + 1) → ℂ} (hφ : Measurable φ) (hφ' : Measurable φ')
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) (N : ℕ) (x : ℝ) :
    Measurable fun g : GA E (m + 1) => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) := by
  have hh := measurable_mulSec (E := E) (m := m)
  have hy := continuous_yInfRow (E := E) (m := m)
  have hI : Measurable fun g : GA E (m + 1) => indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    have hS : IsClosed {g : GA E (m + 1) | ∀ i : Fin (m + 1),
        GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => (isClosed_natLat N).preimage
        (((continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp ((continuous_apply i).comp continuous_lastRow)).sub
          continuous_const)
    unfold indN
    exact Measurable.ite hS.measurableSet measurable_const measurable_const
  have hD : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ) := by
    unfold detPow chiDet
    exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.comp
      ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det)))
  unfold Psi
  exact ((((hφ.comp hh).mul (Complex.continuous_conj.measurable.comp (hφ'.comp hh))).mul
    (hΦ.measurable.comp hy.measurable)).mul hI).mul hD.measurable

end GlobalTheory.ZUnfTheta

theorem GlobalTheory.ZUnfTheta.zint_eq_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  intro E _ _ _ m μ _ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hφm hφ'm hφ hφ' N Φ hΦ x hfin
  set l : Fin (m + 1) := Fin.last m with hl
  let F : GA E (m + 1) → (Fin (m + 1) → Ad E) → ℂ := fun g y => Psi φ φ' Φ N g y * (detPow E (m + 1) x g : ℂ)
  have hv : (Pi.single l 1 : Fin (m + 1) → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin (m + 1)) E,
      γ ∈ mirU E (m + 1) m ↔ (Pi.single l 1 : Fin (m + 1) → E) ᵥ* γ.val = Pi.single l 1 := fun γ => by
    rw [mem_mirU_last, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
    exact Iff.rfl
  have he : ∀ g : GA E (m + 1),
      (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E)) ᵥ* g.val = GlobalTheory.ZEul.lastRow g := fun g => by
    have h1 : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E) = Pi.single l 1 := by
      funext j
      simp only [Function.comp_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [h1, Matrix.single_one_vecMul]
    rfl
  have hF : ∀ γ g y, F (ratGL E (m + 1) γ * g) y = F g y := fun γ g y => by
    simp only [F, Psi, mul_assoc (ratGL E (m + 1) γ) g, hφ, hφ', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  have hm : Measurable fun g => F g (GlobalTheory.ZEul.lastRow g) := GlobalTheory.ZUnfTheta.measurable_integrand hφm hφ'm hΦ N x
  have h𝓕P' : IsFundamentalDomain ((mirU E (m + 1) m).map (ratGL E (m + 1))) 𝓕P μ := h𝓕P
  have hlin := GlobalTheory.ThetaUnfold.lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' (fun g y => ‖F g y‖ₑ)
    (fun γ g y => by simp only [hF]) (by simp only [he]; exact hm.enorm.aemeasurable)
  have hfin' : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0},
      ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤ := by
    rw [hlin]
    simpa only [he] using hfin
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.ThetaUnfold.integral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' F hF
    (by simp only [he]; exact hm.aestronglyMeasurable) hfin'
  simp only [he] at hint
  unfold Zint thetaSum
  rw [← hint]
  congr 1
  funext g
  rw [← tsum_mul_right]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeIndex_splitPlace_eq_mul : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  first | exact @GlobalTheory.SplitLatIdx.latIndex_split | exact GlobalTheory.SplitLatIdx.latIndex_split | (intros; apply GlobalTheory.SplitLatIdx.latIndex_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLatticeConditionOfSeriesComparisonUniversal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem thetaLatticeCondition_of_seriesComparison_universalChar {D : D7} {ρ : Setup D.ntw} {hρ : ρ.Good} {rd : Rds D.nexp ρ} (T : Comparison₂ hρ rd)
    (hY : GlobalTheory.UnivChar.IsUnivChar D.nexp) (hR : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatTwist hρ (rd i j b)) :
    Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp := by
  intro i hi j hj b k Q M χ hψ a hQa
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := T i j' b
  by_cases hoff : InRange D.ntw i Q ∧ ∀ a', ρ.xi i j' b D.nexp Q M (T.cls a) (T.coef a) a' ∈ Set.range (rd i j' b)
  · choose x hx using hoff.2
    rw [T.thU_eq Q M a hoff.1 x hx]
    obtain ⟨z, hz, hzr⟩ := exists_mem_thPsi_of_mem_span T (hR i hi j' b) hψ hoff.1.2.1 a
      (f := specXi ρ D.nexp i j' b k Q M χ (T.cls a) (T.coef a))
      (by
        rw [GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries ρ hρ D.nexp hY i j' b k Q M χ hψ]
        exact GlobalTheory.T.twistedSeries_specialisedUniversalDatum_mem_span ρ hρ D.nexp hY i j' b k Q M χ hψ hoff.1 _ _ _ (T.dat a)
          fun v hv h => Finset.disjoint_left.1 hQa hv ((T.lev_iff a v).2 h))
    have e : z = Formalism.MainNotions.IntegralHeckeForms.specU D.nexp i ((j' : ℕ) + 1) b Q M k χ (grpSum D.nexp (ρ.ch i) Q M x) := by
      refine T.injective_rdK k (hzr.trans ?_)
      rw [rdK_specU_grpSum hρ (rd i j' b) k Q M χ x, specXi]
      exact Finset.sum_congr rfl fun a' _ => by rw [hx a']
    rw [← e]
    exact hz
  · rw [T.thU_off Q M a hoff, map_zero]
    exact zero_mem _

theorem thetaLatticeCondition_of_fullSeriesComparison : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    GlobalTheory.TwInputs.Laws hρ rd → Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp :=
  fun _ _ _ _ F L => thetaLatticeCondition_of_seriesComparison_universalChar F.tie F.univ fun i hi j b => (L.rat i hi j b).2.1

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

end GlobalTheory.SeriesTie
end
end


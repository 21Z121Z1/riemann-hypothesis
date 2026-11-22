import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0863
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0964
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0963
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarUnitarySubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.RealFockActionFree

open GlobalTheory.ExportSeries
open scoped ComplexOrder

theorem om_ptP_inf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t u hu
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hW := hC.thP.ωP i t
  have hθ : IsInfFam R.θ := hC.models.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hC.models.BV i τ)
  have hS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  have one : ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one (Wc D i) _
  let BU : GLR D (Vc D i).rank := fun τ => (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ)).unit
  let U : GLR D (Vc D i).rank := inBasis BU (realGL R.θ (Vc D i) u)
  have eu : ∀ τ, (U τ).val = (R.BV i τ)⁻¹ * compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) u) * R.BV i τ := fun τ => by
    show _ = ((BU τ).val)⁻¹ * _ * (BU τ).val
    rw [← Matrix.coe_units_inv]
    rfl
  have hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ := fun τ => by
    rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Vc D i) u τ)
  have hle : ∀ τ, ((Wc D i).sig (tauE D τ)).1 ≤ (Wc D i).rank := fun τ => by
    have hs : (Wc D i).SigOK := D.sp.W_sig _
    obtain ⟨e, -⟩ := hs (tauE D τ)
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hev : Even (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2) ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  have hη := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hC.lev.eta R.C.isEta _ _ _ hW.resS hW.resT
    (hev.add_odd ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2) ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (Vc D i) (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot (Wc D i) 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨c, hc⟩ : ∃ c : ℂ, R.ωP i t (u, 1) (R.vP i t) = c • R.vP i t :=
    ⟨_, GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D R.ψ hW.std (Vc D i) (Wc D i) R.θ hθ _ _ (R.ωP i t) _ hη hW (fun _ => 1)
      (cart (R.MW i (sg0 D A))) hS hT u hu 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy _ hf hv⟩
  refine ⟨fun τ => ((Wc D i).sig (tauE D τ)).1, c, U, hU, fun P => ?_⟩
  unfold RealDat.ptP
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (fun _ => 1) (R.BV i)
    (fun τ => R.BV i τ * (U τ).val) (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A)))
    (onb (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ))), Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, hc, GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := fun τ => ((Wc D i).sig (tauE D τ)).1) hW.std hθ hS hT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)) (hle τ)).1)
      _ _ hU hf, LinearMap.map_smul]

end GlobalTheory.RealFockActionFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceIdempotentEqCompletionEmbeddingOne
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.IdemIota

set_option maxHeartbeats 800000 in

theorem toCompl_map_mem {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ intAE D) :
    GlobalTheory.LFun.toCompl h (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) z)
      ∈ w.adicCompletionIntegers D.host.E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, rfl⟩ := hz
    have e2 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)
        (b ⊗ₜ[D.host.F] (x : D.host.E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q b ⊗ₜ[D.host.F] (x : D.host.E) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [e2]
    exact GlobalTheory.LFun.InertChart.toCompl_mem h (GlobalTheory.AdelicU.tmul_mem_intLoc (hb q) x)
  | zero =>
    rw [map_zero (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_zero (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).zero_mem
  | add y y' _ _ h1 h2 =>
    rw [map_add (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_add (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).add_mem _ _ h1 h2
  | neg y _ h1 =>
    rw [map_neg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_neg (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).neg_mem _ h1

theorem cw_mem_integers {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) {a : AE D} (ha : finPart D a ∈ intAE D) :
    GlobalTheory.Core.Rk.SWQ.cw h a ∈ w.adicCompletionIntegers D.host.E := by
  have e : GlobalTheory.Core.Rk.SWQ.cw h a = GlobalTheory.LFun.toCompl h
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) (finPart D a)) := by
    show GlobalTheory.LFun.toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E q a) = _
    congr 1
    clear ha
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e]
  exact toCompl_map_mem h _ ha

theorem idemAt_eq_iota_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P →
    ∀ ι : P.adicCompletion D.host.E →+ AE D,
      GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  intro D P e he ι hι
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := hι
  have hq : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hee : e * e = e := he.1.1
  have hec : e * cA D e = 0 := he.1.2.1
  have hne : e ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (he.2 x hx0).1 hx
    rw [h0, zero_mul, map_zero] at this
    exact this (zero_mem _)
  have idem01 : ∀ a : AE D, a * a = a → GlobalTheory.Core.Rk.SWQ.cw hq a = 0 ∨ GlobalTheory.Core.Rk.SWQ.cw hq a = 1 := fun a ha =>
    IsIdempotentElem.iff_eq_zero_or_one.mp
      (by show GlobalTheory.Core.Rk.SWQ.cw hq a * GlobalTheory.Core.Rk.SWQ.cw hq a = GlobalTheory.Core.Rk.SWQ.cw hq a; rw [← map_mul, ha])
  have he' := GlobalTheory.ExportSeries.LatHalf.isIdemAt_conjPl he
  have hPP : Formalism.L2.DIV.conjPl P ≠ P := by
    intro hP
    rw [hP] at he'
    have h1 := GlobalTheory.Tow.idemAt_unique he' he
    apply hne
    rw [← hee]
    nth_rewrite 2 [← h1]
    exact hec
  obtain ⟨x, hxP, hxP'⟩ : ∃ x ∈ P.asIdeal, x ∉ (Formalism.L2.DIV.conjPl P).asIdeal := by
    by_contra hc
    push Not at hc
    exact hPP (HeightOneSpectrum.ext (P.isMaximal.eq_of_le (Formalism.L2.DIV.conjPl P).isPrime.ne_top hc)).symm
  have hx0 : x ≠ 0 := by rintro rfl; exact hxP' (Formalism.L2.DIV.conjPl P).asIdeal.zero_mem
  have hint : finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hxP' ((he'.2 x hx0).2 hc)
  have hc0 : GlobalTheory.Core.Rk.SWQ.cw hq (cA D e) = 0 := by
    have hm := cw_mem_integers hq hint
    rw [map_mul, GlobalTheory.Core.Rk.SecPar.cw_incA] at hm
    rcases idem01 (cA D e) (by rw [← map_mul, hee]) with h | h
    · exact h
    · exfalso
      have hv : Valued.v ((algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P)) ((x : D.host.E))⁻¹)
          = HeightOneSpectrum.valuation D.host.E P ((x : D.host.E))⁻¹ :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
      rw [h, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, hv] at hm
      have hv0 : HeightOneSpectrum.valuation D.host.E P (x : D.host.E) ≠ 0 := by simpa using hx0
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← not_lt,
        HeightOneSpectrum.valuation_lt_one_iff_mem] at hm
      exact hm hxP
  have he0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin (P.under (𝓞 D.host.F)) 1)) =
      e + cA D e := by
    rw [Formalism.IndefR.Fin.below_of_idemAt he]
    show _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (Formalism.IndefR.Fin.sglV _ 1))
    have hb : Formalism.IndefR.Fin.belowPl P = P.under (𝓞 D.host.F) := HeightOneSpectrum.ext rfl
    rw [hb]
    congr 2
  have h6e := h6 e
  rw [he0, add_mul, hee, mul_comm (cA D e) e, hec, add_zero, hc0, map_zero, map_zero, add_zero] at h6e
  rcases idem01 e hee with h | h
  · rw [h, map_zero] at h6e
    exact absurd h6e hne
  · rw [h] at h6e
    exact h6e

end GlobalTheory.IdemIota

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialTwistBaseLevelEqTupleParahoric
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

theorem GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q →
    ∀ x : GL (Fin (Vc D j).rank) (Lev.EAf D),
      (x ∈ lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
        x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) ∧
          X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U) ∧
      ∀ (hx : x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t))
        (hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U),
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x : ℂˣ) : ℂ) =
          ((levFn (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x : ℂˣ) : ℂ) *
            Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  classical
  intro D X E Y i j b t h1 h2 x
  have hB := Y.Z.good.base i j b
  have hbo := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  have hQe : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hce : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := by
    have g0 := Twist.triv_good (D := D) (A := Circle) splitSet_empty
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hce]; exact g0.isOpen
    · rw [hce]; exact g0.rat
    · rw [hce]; exact g0.real
    · rw [hQe]; exact g0.split
    · rw [hce, hQe]; exact g0.unram
    · rw [hQe]; intro PP hPP; exact absurd hPP (Finset.notMem_empty _)
  have hAdm : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by
    rw [hQe]
    exact ⟨by rw [Finset.union_empty]; exact hB.places, Finset.disjoint_empty_right _⟩
  have ht : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hce, mul_one]; exact h1, by rw [hQe, Finset.union_empty]; exact h2⟩
  obtain ⟨hPg, hQ, hcg, hxq⟩ := GlobalTheory.ConjTwist.Test.levS_chars hbo hL hB hψ hAdm ht
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have htW : (Vc D j).rank - (Wc D j).rank = D.R.t := by omega
  have eβ : (Y.Z.ρ.B i j b).F.βS = X.R.βV j := hbo.βS
  have ebo : blkOf ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).t =
      blkOf (n := (Vc D j).rank) (X.R.datVt j t).r (X.R.datVt j t).t := by
    show blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) = blkOf D.R.r D.R.t
    rw [htW, rW]
  have eb2 : blk2 (n := (Vc D j).rank) ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r = blk2 (X.R.datVt j t).r := by
    show blk2 (Wc D j).rank = blk2 D.R.r
    rw [rW]
  have hpar : ∀ y, y ∈ parLev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
      y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) := by
    intro y
    rw [mem_parLev, mem_parLev, eβ, ebo, eb2, hPg, hQ]

  have hrt : ∀ y (hy : y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t)),
      rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) y =
        Y.Z.ρ.eG i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) y)) := by
    intro y hy
    have hy' := (hpar y).2 hy
    funext PP
    obtain ⟨P, hP⟩ := PP
    have h' : P ∈ X.R.Pg := by rw [← hbo.Pg]; exact hP
    apply Units.ext
    ext a c
    have hg := Y.Z.pin.grp i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) y)) P hP h' a c
    refine Eq.trans ?_ hg.symm
    have m1 := blockTri_blkOf_le _ _ (parLev_g hy' hP)
    have m2 := blockTri_blkOf_le _ _ (parLev_g hy h')
    have hz := X.cG.symm_apply_apply (rTup (X.R.βV j) (X.R.datVt j t) y)
    rw [hz]
    simp only [rTup]
    rw [upper_block_val_submatrix _ m1, upper_block_val_submatrix _ m2]
    simp only [Matrix.submatrix_apply]
    rw [eβ]
    rfl

  refine ⟨?_, ?_⟩
  · rw [mem_lev, hpar x]
    constructor
    · rintro ⟨hx, hr⟩
      refine ⟨hx, ?_⟩
      rw [hrt x hx] at hr
      exact ((Y.Z.tie i j b).U_eq _).1 hr
    · rintro ⟨hx, hu⟩
      refine ⟨hx, ?_⟩
      rw [hrt x hx]
      exact ((Y.Z.tie i j b).U_eq _).2 hu
  · intro hx hu
    have hmem : Y.Z.ρ.eG i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) x)) ∈ (Y.Z.ρ.B i j b).G.P.H :=
      ((Y.Z.tie i j b).U_eq _).2 hu
    have hmem' : rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x ∈
        ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.H := by
      rw [hrt x hx]; exact hmem
    have f1 : ext1 ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.H ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.chi
        (rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x) =
        (Y.Z.ρ.B i j b).G.P.chi ⟨_, hmem⟩ := by
      rw [extendOne_of_mem _ hmem']
      congr 1
      exact Subtype.ext (hrt x hx)
    have f1' : ext1 (Lev.flagL (X.R.datVt j t)).P.H (Lev.flagL (X.R.datVt j t)).P.chi
        (rTup (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x) = 1 := by
      rw [extendOne_of_mem _ (show _ ∈ (Lev.flagL (X.R.datVt j t)).P.H from Subgroup.mem_top _)]
      rfl
    have f2 : (∏ PP ∈ ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).Pg,
        ∏ c ∈ Finset.range ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).s,
          ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).cg (c + 1) PP
            (dBlk (blkOf ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).t) (c + 1)
              (redFn (Y.Z.ρ.B i j b).F.βS PP x))) =
        ∏ PP ∈ (Lev.flagL (X.R.datVt j t)).Pg, ∏ c ∈ Finset.range (Lev.flagL (X.R.datVt j t)).s,
          (Lev.flagL (X.R.datVt j t)).cg (c + 1) PP
            (dBlk (blkOf (Lev.flagL (X.R.datVt j t)).r (Lev.flagL (X.R.datVt j t)).t) (c + 1) (redFn (X.R.βV j) PP x)) := by
      refine Finset.prod_congr hPg fun PP hP => Finset.prod_congr rfl fun c _ => ?_
      have h' : PP ∈ X.R.Pg := hP
      rw [hcg _ PP h', ebo, eβ]
      rfl
    have f3 : (∏ PP ∈ ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).Q,
          ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).xq PP
            (dBlk (blk2 ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r) 1 (redFn (Y.Z.ρ.B i j b).F.βS PP x))) =
        ∏ PP ∈ (Lev.flagL (X.R.datVt j t)).Q,
          (Lev.flagL (X.R.datVt j t)).xq PP (dBlk (blk2 (Lev.flagL (X.R.datVt j t)).r) 1 (redFn (X.R.βV j) PP x)) := by
      refine Finset.prod_congr hQ fun PP hP => ?_
      have h' : PP ∈ X.R.Q t := hP
      rw [hxq PP h', eb2, eβ]
      rfl
    unfold levFn
    rw [f1, f1', f2, f3, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_one,
      (Y.Z.tie i j b).psiU_eq ⟨_, hu⟩ hmem]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSumsStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  first
  | exact @GlobalTheory.RSCell.lintegral_unfolded_eq
  | exact GlobalTheory.RSCell.lintegral_unfolded_eq
  | (intros; apply GlobalTheory.RSCell.lintegral_unfolded_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatibleStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → IsDict C.U₂ (Wc D i) (rank_Wc i) (castDict hV C.dict₂) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ FrameTie C.U₂ (Wc D i) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) ∧ (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  first | exact @GlobalTheory.LevelSeries.cover_dict_frameTie | exact GlobalTheory.LevelSeries.cover_dict_frameTie | (intros; apply GlobalTheory.LevelSeries.cover_dict_frameTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumReadingConstantsLevelCoverRelateCoreStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumReadingConstants_levelCover_relate_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D (T.V j σ) →* Module.End ℂ (WO V (T.V j σ) → ℂ)), IsPair ψ θ V (T.V j σ) χV χW om → ∀ hr : (T.V j σ).rank = D.R.r, (∀ k, IsMod (T.V j σ) hr ((T.U j σ).X k)) → ∀ (h : GA D (T.V j σ)) (δ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ γ : GA D (T.V j σ), (∀ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt (T.V j σ) γ) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) → ∀ (hx₁ : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom) (hx₂ : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom), IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2 → ∀ (F₁ F₂ : WO V (T.V j σ) → ℂ) (m₁ m₂ : ℂ), (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (C.U₂.X (C.dict₂ h).1).Λ) (idx : Fin g ≃ (C.U₂.X (C.dict₂ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl (C.U₂.X (C.dict₂ h).1) bas → IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads C.U₂ (C.dict₂ h).1 bas idx e ⟨(C.dict₂ h).2, hx₂⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₁ w = m₁ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (C.U₂.X (C.dict₂ h).1) bas idx (C.dict₂ h).2 (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b) (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) → (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((T.U j σ).X (T.dict j σ h).1).Λ) (idx : Fin g ≃ ((T.U j σ).X (T.dict j σ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl ((T.U j σ).X (T.dict j σ h).1) bas → IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads (T.U j σ) (T.dict j σ h).1 bas idx e ⟨(T.dict j σ h).2, hx₁⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₂ w = m₂ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx ((T.U j σ).X (T.dict j σ h).1) bas idx (T.dict j σ h).2 (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b) (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) → (∀ w, F₂ (actO V (T.V j σ) 1 γ w) = F₁ w) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a V.rank, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank, C.IsPull f f₂ → m₁ * rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = m₂ * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  first | exact @GlobalTheory.CoverConstMove.const_cover | exact GlobalTheory.CoverConstMove.const_cover | (intros; apply GlobalTheory.CoverConstMove.const_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslateSumConjugateHalfNeZero
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.VacTransNe

theorem sum_heisO_conjHalf_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → ∑ y ∈ Y, heisO ψ V W y f₀ ≠ 0 := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT _ _ _ Y hY hYd hYc h0
  obtain ⟨y₀, hy₀, -⟩ := hYc 0 (fun i j => mul_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  obtain ⟨p, hp⟩ := hP.2.2.2.2.2.2.2.2.2.norm.1
  have h := GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y
    (fun y hy => (hY y hy).1) hYd p.1 p.2 hp
  rw [h0] at h
  have hz : nrm2 p.1 p.2 (0 : WO V W → ℂ) = 0 := by
    unfold nrm2
    simp
  rw [hz] at h
  have hc : Y.card = 0 := by exact_mod_cast h.symm
  exact Finset.card_ne_zero_of_mem hy₀ hc

end GlobalTheory.VacTransNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepCentralActsByDilationUnitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_central_acts_by_dilation_unit : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) κ ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  first | exact @GlobalTheory.TupDil.om_model_eq_unit_smul_dilate | exact GlobalTheory.TupDil.om_model_eq_unit_smul_dilate | (intros; apply GlobalTheory.TupDil.om_model_eq_unit_smul_dilate <;> assumption)
end


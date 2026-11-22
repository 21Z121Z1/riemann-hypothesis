import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0503
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0509
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.ZeroCongr
open Formalism.UG

theorem adFun_of_same {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (Ψ) (hΨ : Ψ ∈ AdFun S' (embT D)) : Ψ ∈ AdFun S (embT D) := by
  intro γ hγ x x' κ h y y' hy
  rw [hchi κ ⟨κ.1, (hU _).1 κ.2⟩ rfl]
  exact hΨ γ hγ x x' ⟨κ.1, (hU _).1 κ.2⟩ h y y' hy

set_option maxHeartbeats 1000000 in

theorem rdS_congr (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (hn : V.rank = n)
    (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    {cl cl' : Type} (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (yc' : cl' → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hb' : Function.Bijective (fun c => (Quotient.mk'' (yc' c) : Cls S')))
    (lam : D.what₂.Tau → DomWeight n) (φ) (φ') (hφ' : φ' ∈ FiC S' (embT D) lam yc')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (hrep : ∀ c, ∃ c', ∃ κ : S.U, (yc' c').1 = (yc c).1 * κ.1 ∧ S.chi κ = 1 ∧ φ c = φ' c')
    (y : Frames (gramC J (embT D))) (g : GA D V) :
    rdS θ V hn S yc φ y g = rdS θ V hn S' yc' φ' y g := by
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ'
  have hA' := (Submodule.mem_inf.1 hΨ).1
  have hA := adFun_of_same S S' hU hchi Ψ hA'
  have e : φ = fun c => Ψ (yc c) := by
    funext c z
    obtain ⟨c', κ, hy, hχ, hφc⟩ := hrep c
    rw [hφc]
    have h1 : IsTr (atInf (embT D) ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) z z := fun τ => by
      show z.1 τ = _ * z.1 τ
      simp [atInf]
    have e3 := hA 1 (Subgroup.one_mem _) (yc c) (yc' c') κ (by rw [map_one, one_mul]; try exact hy) z z h1
    show Ψ (yc' c') z = Ψ (yc c) z
    rw [e3, hχ, Units.val_one, one_mul]
  subst e
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T f bad S cl yc hb Ψ hA y g
  obtain ⟨-, -, hv'⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T' f' bad' S' cl' yc' hb' Ψ hA' y g
  let z : Frames (gramC J (embT D)) :=
    ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hu τ).mul (y.2 τ)⟩
  exact (hv x z hx (fun τ => rfl)).trans (hv' x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.ZeroCongr

namespace GlobalTheory.Fam

set_option maxHeartbeats 4000000 in

theorem rd_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ θ hθ ψ₀ hψ y
  unfold GlobalTheory.AdForm.TwDat.rd GlobalTheory.AdForm.Chart.rd GlobalTheory.Core.Mi.chart0
  dsimp only
  have hfr : ((C.forms u).to0.val0.eY y) = (⟨y.1, y.2⟩ : Frames (gramC (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (embT (I.rec7 l Z)))) :=
    Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y)
  rw [hfr]
  funext g
  refine GlobalTheory.AdForm.ZeroCongr.rdS_congr (I.rec7 l Z) θ hθ _ _ _ _ ?hJ _ _ _ _ (A.K 0 (Nat.zero_le _) β).y_bij ((C.forms u).to0.cls0.toChart.y_bij) (lamT u 0) _ _ ?hφ ?hU ?hchi ?hrep _ g
  case hJ => rfl
  case hφ => exact ((C.forms u).to0.val0.Fi ψ₀).1 (((I.rec7 l Z).fm u).Fi_zero ▸ hψ.1)
  case hU => exact GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member I hI hP l Z C hC u a Ch A hA β hβ
  case hchi => exact GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase I hI hP l Z C hC u a Ch A hA β hβ
  case hrep =>
    intro c
    obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.stepZero_representative_differs_by_level I hI hP l Z C hC u a Ch A hA β hβ c
    refine ⟨(I.eCls0 l u a).symm c.1, κ, h1, h2, ?_⟩
    funext z
    have hz : (C.forms u).to0.val0.eY.symm z = ⟨z.1, z.2⟩ := by
      apply (C.forms u).to0.val0.eY.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) _).symm
    rw [hz]
    rfl

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

namespace GlobalTheory.StabSetFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stab_fix_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT hS hT P hP f hf κ κ' hκ hκ'
  have hloc := ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ S T χS χT om hW LS LT hS hT P (fun v hv => (hP v hv).1) f).1.1 hf)
  have one_inK : ∀ (V : HSp D) (L : Lat V) (v : Pl D), InK V L (· = v) 1 := by
    intro V L v
    refine ⟨one_mem _, fun y _ => ?_⟩
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.one_mulVec]
  have single : ∀ v, P v → ∀ y y', InK S LS (· = v) y → InK T LT (· = v) y' → om (y, y') f = f :=
    fun v hv y y' hy hy' => GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW (hP v hv).2.1 (hP v hv).2.2 LS LT hS hT f
      hloc.1 (hloc.2 v hv).2 y y' (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D S LS v y hS hy) (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D T LT v y' hT hy')
  have listS : ∀ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S LS (· = v) y) → om (l.prod, 1) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : ((y * l.prod, (1 : GA D T)) : GA D S × GA D T) = (y, 1) * (l.prod, 1) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv y 1 hy (one_inK T LT v)]
  have listT : ∀ l : List (GA D T), (∀ y ∈ l, ∃ v, P v ∧ InK T LT (· = v) y) → om (1, l.prod) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : (((1 : GA D S), y * l.prod) : GA D S × GA D T) = (1, y) * (1, l.prod) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv 1 y (one_inK S LS v) hy]
  choose lS hlS hiS hinS houtS using GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet D S LS P κ hS hκ
  choose lT hlT hiT hinT houtT using GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet D T LT P κ' hT hκ'
  have tS := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D S κ (fun Fs => (lS Fs).prod) hiS hinS houtS
  have tT := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D T κ' (fun Fs => (lT Fs).prod) hiT hinT houtT
  funext w
  have hc := ((hW.om_cont f hloc.1 w).tendsto (κ, κ')).comp (tS.prodMk_nhds tT)
  have heq : ∀ Fs, f w = ((fun p : GA D S × GA D T => om p f w) ∘ fun Fs => ((lS Fs).prod, (lT Fs).prod)) Fs := by
    intro Fs
    have e : (((lS Fs).prod, (lT Fs).prod) : GA D S × GA D T) = ((lS Fs).prod, 1) * (1, (lT Fs).prod) := by simp
    simp only [Function.comp_apply]
    rw [e, map_mul, Module.End.mul_apply, listT _ (hlT Fs), listS _ (hlS Fs)]
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr heq)

end GlobalTheory.StabSetFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem sw_doubled_of_std : GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelWeilUnitaryConvergent := by
  intro hP D ψ A B hAB hB2 hW χB omh hWe a hMaj _ θ sS sB hθ hsS hsB hK mW 𝓨 hcov ν hν f hf
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hMaj κ hκ
  obtain ⟨lam, hlam, hψ', l, hl, hlabs⟩ := GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters D ψ hWe.std θ hθ m0 hm0
  obtain ⟨omS, hT⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A B χB omh hWe mW 𝓨 hcov θ hθ κ
  obtain ⟨s', hs'std, hs'⟩ := GlobalTheory.T.compactCommuting_cartanInvolution_moved_standard D A m0 hm0 κ hκ a p hp θ hθ sS hsS hK
  have hf' : IsFockVec ψ θ (dblSp A) B s' sB (omh ((p : GA D (dblSp A))⁻¹, 1) f) :=
    GlobalTheory.T.isPolynomialFockThetaVector_weilOperator_cartan D ψ (dblSp A) B 1 χB omh hWe θ hθ sS s' sB _ hs' f hf
  have hschw := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B mW 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f),
      ((hschw ψ hWe.std θ hθ A B mW 𝓨 hcov).1 _ hf'.1)⟩
  have hΦ : Φ.1 ∈ fockA θ B A.rank l sB :=
    GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ hWe.std θ hθ A B mW 𝓨 hcov m0 hm0 s' sB hs'std hsB l hlabs _ hf'
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χB B.rank hWe.hecT hWe.resT
  have hWS : IsWeilSch (shift ψ lam) χB⁻¹ θ B mW omS :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam⟩
  have hH := GlobalTheory.T.standardUnitaryHeight_isSiegelHeightFunction D A m0 hm0 κ hκ a p hp
  obtain ⟨hInt, hEis, hHol⟩ := hP D A.rank B hAB hB2 hW (shift ψ lam) hψ' χB⁻¹ hχ.1 hχ.2 θ hθ mW 𝓨 hcov omS hWS
    (hgtStd A a κ p) hH l hl sB hsB ν hν Φ hΦ
  obtain ⟨h0, hflat, hact⟩ := GlobalTheory.T.doubledFlatSection_eq_translate_standardSection D ψ A B χB omh hWe mW 𝓨 hcov θ hθ m0 hm0 κ hκ omS hT lam hlam a p f hf.1 Φ rfl
  have hth : ∀ g : GA D (dblSp A), theta omS Φ (κ (g * p)) = fun h => thetaKO omh g h f := fun g => by
    funext h
    rw [GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction D ψ A B χB omh hWe mW 𝓨 hcov f hf.1 g h, theta, hact g]
  have hmean : ∀ g : GA D (dblSp A), GlobalTheory.ThetaMean.thetaMean omh ν f g = thetaInt omS ν Φ (κ (g * p)) := fun g => by
    rw [thetaInt, hth g]; rfl
  have hP' := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A m0 hm0 κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A m0 hm0 κ hκ
  have Heisenberg₂ := fun (z : ℂ) (hz : (A.rank : ℝ) / 2 < z.re) =>
    GlobalTheory.T.cosetSum_along_mulEquiv_subgroups _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG'
      (sect omS (hgtStd A a κ p) Φ z) (p : GA D (dblSp A)) (npow (absA D (aP A p)) (sZero A B - z))
      (flat A a (swSec A B omh mW 𝓨 f) (sZero A B) z) (fun g => hflat z g) (hEis z hz).1
  refine ⟨fun g => ?_, ⟨fun z hz => ⟨(Heisenberg₂ z hz).1, fun g => ((Heisenberg₂ z hz).2 g).1 ((hEis z hz).2 _)⟩, fun g => ?_⟩⟩
  · rw [← hth g]; exact hInt _
  · have hr : 0 < absA D (aP A p) := hom_pos _ _
    have := GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor (fun z => GlobalTheory.Eis.cosetSum (P D A.rank) (GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) (κ (g * p)))
      (GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh mW 𝓨 f) (sZero A B)) g) (s0 B A.rank) _ (absA D (aP A p))
      ((A.rank : ℝ) / 2) hr (hHol (κ (g * p))) (fun z hz => by
        rw [h0]; exact ((Heisenberg₂ z hz).2 g).2)
    rw [h0] at this
    rw [hmean g]
    exact this

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverSwap

variable {D : D7}

theorem eq_zero_of_two {v v' : Pl D} (hne : v ≠ v') {z : AE D} (h : z ∈ idAt D (· = v))
    (h' : z ∈ idAt D (· = v')) : z = 0 := by
  have hc : compAt D v z = 0 := by
    unfold idAt at h'
    exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 h').2 ⟨v, hne⟩
  rw [GlobalTheory.FinPl.Model.eq_single h, hc]
  exact (GlobalTheory.AdelicU.Supp.singleTens D.host.E v).map_zero'

theorem cA_mem_idAt {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem symplO_eq_zero_of_ne {v v' : Pl D} (hne : v ≠ v') {S T : HSp D} {x y : WO S T} (hx : MxAt (· = v) x)
    (hy : MxAt (· = v') y) : symplO S T x y = 0 := by
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * x d a = 0 :=
      eq_zero_of_two hne (Ideal.mul_mem_left _ _ (hx d a)) (Ideal.mul_mem_right _ _ (cA_mem_idAt (hy c b)))
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a
        = incA D (S.gram⁻¹ a b) * incA D (T.gram c d) * (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem comb_comm {v v' : Pl D} (hne : v ≠ v') (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {c c' : WO S T →₀ ℂ}
    (hc : CombAt (· = v) c) (hc' : CombAt (· = v') c') (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f) = GlobalTheory.SeeSaw.comb ψ S T c' (GlobalTheory.SeeSaw.comb ψ S T c f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.1 c c' (fun x hx y hy => symplO_eq_zero_of_ne hne (hc x hx) (hc' y hy)) f

end GlobalTheory.FinPl.OverSwap

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.OverSwap in

theorem overSwap : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  intro D k _ _ _ _ p p' n n' m m' _ _ _ _ _ _ _ _ ψ hψ hp hp' hne S T α β α' β' LS LT f₀ g h Ψ Ψ' hv' hO1 hO2
  obtain ⟨hLS, hLT, hf₀, hΨ, -⟩ := id hO1
  obtain ⟨-, -, hg, hΨ', -⟩ := id hO2
  obtain ⟨c, hc, hcO⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p n n' ψ hψ hp S T α β LS LS LT LT hLS hLT hLS hLT).2 Ψ hΨ
  obtain ⟨c', hc', hcO'⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k p' m m' ψ hψ hp' S T α' β' LS LS LT LT hLS hLT hLS hLT).2 Ψ' hΨ'
  have eg : g = GlobalTheory.SeeSaw.comb ψ S T c f₀ :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ S T α β LS LT hLS hLT f₀ hf₀).1 Ψ hΨ).unique hO1 (hcO f₀ hf₀)
  have eh : h = GlobalTheory.SeeSaw.comb ψ S T c' g :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT g hg).1 Ψ' hΨ').unique hO2 (hcO' g hg)
  have hO3 := hcO' f₀ hv'
  have hvac : Vac ψ S T LS LT (· = p.v) (GlobalTheory.SeeSaw.comb ψ S T c' f₀) :=
    ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p' m m' ψ hψ S T α' β' LS LT hLS hLT f₀ hv').2.1 Ψ' _ hO3).2 LS LT (· = p.v)
      (fun e => hne e.symm) hf₀
  refine ⟨_, hO3, ?_⟩
  have e : h = GlobalTheory.SeeSaw.comb ψ S T c (GlobalTheory.SeeSaw.comb ψ S T c' f₀) := by
    rw [eh, eg, comb_comm hne ψ hc hc']
  rw [e]
  exact hcO _ hvac

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctiona
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.StdPairCoord

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_lat_iff {D : D7} {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (x : Fin S.rank → k) :
    x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
  exact forall_congr' fun r =>
    ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm

theorem hasVal_mulVec {n : ℕ} (Q : Pair k (Fin n)) (b' : Matrix (Fin n) (Fin n) k) (s : Fin n → 𝒪[k])
    (h : ∀ r, Q.HasVal (b' *ᵥ Pi.single r 1) (residue 𝒪[k] (s r))) (y : Fin n → 𝒪[k]) :
    Q.HasVal (b' *ᵥ fun r => (y r : k)) (∑ r, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := by
  have h1 : ∀ t : Finset (Fin n), Q.HasVal (∑ r ∈ t, y r • (b' *ᵥ Pi.single r 1))
      (∑ r ∈ t, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := fun t => by
    induction t using Finset.induction_on with
    | empty => exact ⟨by simp, by simp only [Finset.sum_empty]; exact map_zero Q.fn⟩
    | insert r t hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr]
      exact ((h r).smul _).add ih
  convert h1 Finset.univ using 1
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AdForm.StdPairCoord

open GlobalTheory.AdForm.StdPairCoord in

theorem GlobalTheory.AdForm.stdT_pair_coords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ i (r₀ : Fin ((I.rec7 l Z).sp.X j).rank), r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∀ (x : Fin ((I.rec7 l Z).sp.X j).rank → k) (a : 𝓀[k]), (Q j i).HasVal x a ↔ ∃ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (∀ r, (y r : k) = ((β j i).b *ᵥ x) r) ∧ ∃ s : 𝒪[k], (s : k) = (p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) ∧ a = residue 𝒪[k] (s * y r₀) := by
  intro B X I l Z u k _ _ _ _ ι p β Q L hS j hj i r₀ hr₀ x a
  obtain ⟨-, hT⟩ := hS
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, hfn⟩ := hT' i
  have hmem := mem_lat_iff hL (β j i) hlat
  have hs : ∀ r, ∃ s : 𝒪[k], (s : k) = (if r = r₀ then (p i).pr (incA (I.rec7 l Z)
      (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) else 0) ∧
      (Q j i).HasVal ((β j i).b' *ᵥ Pi.single r 1) (residue 𝒪[k] s) := fun r => by
    have hz : (Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) ∈ L j := (hL _).2 fun t => by
      rw [Pi.single_apply]
      split_ifs
      exacts [isIntegral_one, isIntegral_zero]
    obtain ⟨s, hs1, hs2⟩ := hfn _ hz r₀ hr₀
    have e : (fun r' => (p i).pr (incA (I.rec7 l Z) ((Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) r'))) =
        Pi.single r 1 := funext fun r' => by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      · rw [map_one, map_one]
      · rw [map_zero, map_zero]
    rw [e] at hs2
    refine ⟨s, ?_, hs2⟩
    rw [hs1, Pi.single_apply]
    by_cases h : r₀ = r
    · subst h
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero, map_zero, map_zero]
  choose s hs using hs
  have key : ∀ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (Q j i).HasVal ((β j i).b' *ᵥ fun r => (y r : k))
      (residue 𝒪[k] (s r₀ * y r₀)) := fun y => by
    have h1 := hasVal_mulVec (Q j i) (β j i).b' s (fun r => (hs r).2) y
    convert h1 using 1
    rw [Finset.sum_eq_single r₀ (fun r _ hr => ?_) (fun h => (h (Finset.mem_univ _)).elim), map_mul, mul_comm]
    have : s r = 0 := Subtype.ext ((hs r).1.trans (if_neg hr))
    rw [this, map_zero, mul_zero]
  constructor
  · intro h
    have hx := (hmem x).1 h.mem
    refine ⟨fun r => ⟨_, hx r⟩, fun r => rfl, s r₀, (hs r₀).1.trans (if_pos rfl), h.unique ?_⟩
    have := key fun r => ⟨_, hx r⟩
    rwa [show ((β j i).b' *ᵥ fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = x by
      rw [show (fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = (β j i).b *ᵥ x from rfl, Matrix.mulVec_mulVec, (β j i).b'b,
        Matrix.one_mulVec]] at this
  · rintro ⟨y, hy, s', hs', rfl⟩
    obtain rfl : s' = s r₀ := Subtype.ext (hs'.trans ((hs r₀).1.trans (if_pos rfl)).symm)
    have hx : x = (β j i).b' *ᵥ fun r => (y r : k) := by
      rw [show (fun r => (y r : k)) = (β j i).b *ᵥ x from funext hy, Matrix.mulVec_mulVec, (β j i).b'b, Matrix.one_mulVec]
    rw [hx]
    exact key y

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentityStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_majorant_average_identity : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (om' : WRep S T'), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T' χS χT om' → ∀ b : GL (Fin T.rank) (AE D), IsMaj T b → ∀ ν : Measure (Kmax T b), IsProbabilityMeasure ν → ∀ (μ₁ : Measure (Mx D t S.rank)) (𝓕₁ : Set (Mx D t S.rank)), IsCovolOne (ratMx D t S.rank) μ₁ 𝓕₁ → (∀ φ, IsThetaFunO ψ S T φ → IsThetaFunO ψ S T (projK om ν φ)) → (∀ φ, IsThetaFunO ψ S T φ → ∀ g, ikeda ψ d μ₁ 𝓕₁ (projK om ν (om (g, 1) φ)) = om' (g, 1) (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ))) ∧ ∀ (K : Subgroup (GA D S)) φ, IsThetaFunO ψ S T φ → IsKFinVec om K φ → IsKFinVec om' K (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ)) := by
  first | exact @GlobalTheory.IkedaK.ikeda_projK_intertwine | exact GlobalTheory.IkedaK.ikeda_projK_intertwine | (intros; apply GlobalTheory.IkedaK.ikeda_projK_intertwine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  first | exact @GlobalTheory.Unf.sum_term_bound | exact GlobalTheory.Unf.sum_term_bound | (intros; apply GlobalTheory.Unf.sum_term_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_trivial_after_flagUnipotentFixing : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  first | exact @GlobalTheory.Unf.transv_trivial_after_Nfix | exact GlobalTheory.Unf.transv_trivial_after_Nfix | (intros; apply GlobalTheory.Unf.transv_trivial_after_Nfix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryPsiValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_psi_value : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ (i : Fin a.n) (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (F0 W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) → ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) : ℂ) = (F0 W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  first | exact @GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero | exact GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero | (intros; apply GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero <;> assumption)
end


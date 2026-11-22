import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0408
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  first | exact @GlobalTheory.ExchLatPf.exchLat | exact GlobalTheory.ExchLatPf.exchLat | (intros; apply GlobalTheory.ExchLatPf.exchLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenbergStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointExchange_laws_thetaHeisenberg : ∀ D : D7, ExchLaw D := by
  first | exact @GlobalTheory.ExchPf.exchLaw | exact GlobalTheory.ExchPf.exchLaw | (intros; apply GlobalTheory.ExchPf.exchLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmoothStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | exact GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | (intros; apply GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelUnfoldingCharacterAndFlatMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FromBes

theorem conjBessel_isTh (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (ρ : ℕ) (B : BesL D ρ) (W : HSp D)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx₀ : gramQ W x₀ = 0) :
    IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  have hC := GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  set z := vecB B.o B.ζ with hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp ((hC.1 z).comp continuous_subtype_val)
  · intro γ hγ hγN n hn
    rw [psiBes_mul B.d ψ 1 z hγN hn, hC.2.1 z γ hγ, one_mul]
  · intro c n hn
    rw [psiBes_mul B.d ψ 1 z (B.d.nC_mem_NFlag c) hn, psiBes_nC, one_mul,
      GlobalTheory.Unf.CutChar.psi_qS_eq_one D ψ hψ B.V B.V₀ ρ B.d W x₀ hx₀ c, star_one, one_mul]
  · intro j a haj hai _
    obtain ⟨s, hs⟩ := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
    have key : ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer B.V (B.d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum B.d z u = s := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.2) with h | h
      · exact GlobalTheory.T.exists_transvection_fixing_first_vectors_sum D B.V B.V₀ ρ B.d z j a haj hai h s
      · exact GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum D B.V B.V₀ ρ B.d z (GlobalTheory.Unf.CutChar.vecB_norm_ne D B.V₀ B.A B.L B.o B.ζ B.line) j a haj hai h s
    obtain ⟨v, hv0, hvT, hv⟩ := key
    obtain ⟨u, hu⟩ := GlobalTheory.T.transvection_isUnitaryAdelic D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hv0
    obtain ⟨hfix, hus⟩ := hv u hu
    have huN : u ∈ Nfix B.d j :=
      ⟨GlobalTheory.T.transvection_strictUpper_mem_flagUnipotentRadical D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hvT u hu, Subgroup.mem_iInf.2 hfix⟩
    have hval : psiBes ψ B.d 1 z u = psiE ψ s := by
      rw [psiBes, hus, map_one, one_mul]
    refine ⟨v, u, star (psiE ψ s), hv0, hu, huN, ?_, ?_⟩
    · intro h1
      apply hs
      have := congrArg star h1
      rwa [star_star, star_one] at this
    · intro n hn n' hn'
      have huF : u ∈ flagN B.d := huN.1
      rw [psiBes_mul B.d ψ 1 z (mul_mem hn huF) hn', psiBes_mul B.d ψ 1 z hn huF, hval,
        psiBes_mul B.d ψ 1 z hn hn']
      simp only [star_mul']
      ring

theorem fl_eq_flBF (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flBF flatS flatAt
  congr 1
  funext u
  simp only [flFun, flatFun, evalAt, HypDec.mixT]
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact GlobalTheory.Unf.StepFour.integrand_eq hψ B.d J.d _ _ (hf _) b

theorem isTh_and_fl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), IsTh ψ B.d J.W J.d.e (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) ∧ ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  intro D ψ ρ B J s
  exact ⟨conjBessel_isTh D ψ s.weil.std ρ B J.W J.d.e (gramQ_e J.d), fun Ψ hΨ => fl_eq_flBF D ψ ρ B J s Ψ hΨ⟩

end GlobalTheory.Asc.FromBes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIntertwinerMapValuesIsCuspFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCusp

theorem isCuspFun_iota (D : D7) (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] [SigmaFinite μf] (ψ : I.GA → ℂ) (hc : Continuous ψ)
    (hi : ∀ γ ∈ I.GFset, ∀ y, ψ (γ * y) = ψ y) (hcusp : I.IsCuspFn (I.muA μf) ψ) :
    IsCuspFun (D.sp.Y 0) (fun g => ψ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) g)) := by
  subst h
  intro r C hC μ 𝓕 hμ h𝓕 g
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (Formalism.IndefR.RationalEmbedding.iota_rat D) _ hW (GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical D C hC) ψ hc hi).2 (hcusp _ hW) μ 𝓕 hμ h𝓕 g
  exact key

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hConj hInt Φ hΦ hRep u
  change IsCuspFun (D.sp.Y 0) _
  obtain ⟨-, -, -, -, -, -, hSL⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hDS
  obtain ⟨hd, hl, hb, hh, hph, -⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨-, -, ⟨T0, hT0⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds X.B X.dv hd hph
  have hw := GlobalTheory.RowCusp.row_isCuspFn hSL X.B X.dv _ hd hg hh hl hb T0 hT0 Φ hΦ
  have hcH := GlobalTheory.RowLev.isCuspHom_of_cusp_lowest X.B X.ds (fun v => (X.low v).1) Φ hΦ hw
  obtain ⟨ψ, hψ⟩ := hRep u
  have he := (GlobalTheory.ExtContRep.ext_ae_eq_contRep X.B _ ψ hψ).1
  have hcψ : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ :=
    (GlobalTheory.IntertwMult.contRep_facts X.B.I X.B.μf X.B.fund X.B.R X.B.fund_spec X.B.R_spec _ ψ hψ.1 hψ.2.1
      (he.mono fun x hx => hx.symm)).2.1 (hcH _)
  have hY := isCuspFun_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hcψ
  set t' : GA D (D.sp.Y 0) := t with ht'
  have hfun : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u = fun y => star (ψ (iotaX X h (y * t'⁻¹))) := by
    funext y
    exact congrArg star (congrFun (GlobalTheory.ConjRowMult.contRepL_spec X hψ) _)
  rw [hfun]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have key := hY r C hC μ 𝓕 hμ h𝓕 (g * t'⁻¹)
  have e : ∀ n : NI (D.sp.Y 0) C, ((n : GA D (D.sp.Y 0)) * g * t'⁻¹) = (n : GA D (D.sp.Y 0)) * (g * t'⁻¹) :=
    fun n => mul_assoc _ _ _
  have hs : ∀ z : ℂ, star z = starRingEnd ℂ z := fun _ => rfl
  simp only [e, hs]
  rw [integral_conj]
  exact (congrArg (starRingEnd ℂ) key).trans (map_zero _)

end GlobalTheory.ConjCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftIdeal

def conjO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv

theorem coe_conjO (D : D7) (x : 𝓞 D.host.E) :
    ((conjO D x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) := rfl

theorem conjO_conjO (D : D7) (x : 𝓞 D.host.E) : conjO D (conjO D x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO]
  simp

theorem star_eq (D : D7) (x : D.host.E) : star x = IsCMField.complexConj D.host.E x := rfl

theorem conjI_eq_map (D : D7) (I : Ideal (𝓞 D.host.E)) :
    conjI I = I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, RingOfIntegers.ext ?_⟩
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem map_map_conjO (D : D7) (I : Ideal (𝓞 D.host.E)) :
    (I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = I := by
  rw [Ideal.map_map]
  have : ((conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).comp (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = RingHom.id _ :=
    RingHom.ext fun x => conjO_conjO D x
  rw [this, Ideal.map_id]

end GlobalTheory.LiftIdeal

end

noncomputable section

namespace GlobalTheory.LiftIdeal

open GlobalTheory.LiftLevel

theorem isMaximal_map (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) :
    (PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := by
  haveI := PP.isMaximal
  exact Ideal.map_isMaximal_of_equiv (conjO D)

theorem liftI_eq (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    liftI Pg Q = ∏ PP ∈ Pg ∪ Q, PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold liftI
  exact Finset.prod_congr rfl fun PP _ => conjI_eq_map D _

theorem conjI_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    conjI (liftI Pg Q) = ∏ PP ∈ Pg ∪ Q, PP.asIdeal := by
  rw [conjI_eq_map, liftI_eq]
  have := map_prod (Ideal.mapHom (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
    (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (Pg ∪ Q)
  simp only [Ideal.mapHom_apply] at this
  rw [this]
  exact Finset.prod_congr rfl fun PP _ => map_map_conjO D _

theorem map_ne {D : D7} {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ S) (hP' : PP' ∈ S) :
    PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ PP'.asIdeal := by
  intro h
  refine GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP' fun c hc => ?_
  refine ⟨conjO D c, h ▸ Ideal.mem_map_of_mem _ hc, ?_⟩
  rw [coe_conjO, star_eq]

theorem liftI_props : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) →
    GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  intro D Pg Q e hne h2 he
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P0, hP0⟩ := hne
    intro htop
    have hle : liftI Pg Q ≤ P0.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [liftI_eq]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hP0))
    rw [htop] at hle
    exact (isMaximal_map D P0).ne_top (top_le_iff.1 hle)
  · rw [liftI_eq, ← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
    rw [Ne, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (f := (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (conjO D).injective]
    exact PP.ne_bot
  · rw [conjI_liftI, liftI_eq]
    refine IsCoprime.prod_left fun PP hP => IsCoprime.prod_right fun PP' hP' => ?_
    exact Ideal.isCoprime_iff_sup_eq.2
      ((isMaximal_map D PP).coprime_of_ne PP'.isMaximal (map_ne he hP hP'))
  · rw [liftI_eq]
    refine IsCoprime.prod_left fun PP hP => Ideal.isCoprime_iff_sup_eq.2 ?_
    have h2' : (2 : 𝓞 D.host.E) ∉ PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, map_ofNat]
      exact h2 PP (Finset.mem_union.1 hP)
    exact (isMaximal_map D PP).out.2 _ (left_lt_sup.2 fun hle => h2' (hle (Ideal.mem_span_singleton_self 2)))

end GlobalTheory.LiftIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffPoincareSumOverRationalHomRealDirections
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSmooth

variable {D : D7}

theorem finite_rat_mem (m n : ℕ) (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem contDiff_of_additive {k : ℕ} (f : (Fin k → ℝ) → ℂ) (h0 : f 0 = 0) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hc : Continuous f) : ContDiff ℝ ∞ f :=
  GlobalTheory.WeilVacMove.contDiff_additive (⟨⟨f, h0⟩, hadd⟩ : (Fin k → ℝ) →+ ℂ) hc

def rmul {m n p : ℕ} (Q : Mx D n p) : Mx D m n →+ Mx D m p where
  toFun x := x ⬝ Q
  map_zero' := Matrix.zero_mul _
  map_add' x y := Matrix.add_mul _ _ _

theorem continuous_rmul {m n p : ℕ} (Q : Mx D n p) : Continuous (rmul (m := m) Q) :=
  continuous_id.matrix_mul continuous_const

theorem contDiff_psi_symplOH {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {k : ℕ}
    (A B : (Fin k → ℝ) →+ WO S T) (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ t, (A t).map (finPart D) = 0) (hB0 : ∀ t, (B t).map (finPart D) = 0) (c c' : WO S T) :
    ContDiff ℝ ∞ fun t => ψ (symplOH S T (c + A t) (c' + B t)) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hadd1 := GlobalTheory.WeilVacMove.symplOH_add_left S T
  have hadd2 := GlobalTheory.WeilVacMove.symplOH_add_right S T
  have hz1 := GlobalTheory.WeilVacMove.symplOH_zero_left S T
  have hz2 := GlobalTheory.WeilVacMove.symplOH_zero_right S T
  have h1 : ContDiff ℝ ∞ fun t => lam (symplOH S T c (B t)) :=
    contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add, hadd2, map_add])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have h2 : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) c') :=
    contDiff_of_additive _ (by rw [map_zero, hz1, map_zero]) (fun x y => by rw [map_add, hadd1, map_add])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const))
  have hQ : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) (B t)) := by
    let φ : (Fin k → ℝ) → ((Fin k → ℝ) →+ ℂ) := fun t =>
      { toFun := fun s => lam (symplOH S T (A s) (B t))
        map_zero' := by rw [map_zero, hz1, map_zero]
        map_add' := fun x y => by rw [map_add, hadd1, map_add] }
    have hφ : ∀ t, Continuous (φ t) := fun t =>
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const)
    have e : (fun t => lam (symplOH S T (A t) (B t))) =
        fun t => ∑ i, t i • lam (symplOH S T (A fun j => if i = j then 1 else 0) (B t)) := by
      funext t
      exact LinearMap.pi_apply_eq_sum_univ ((φ t).toRealLinearMap (hφ t) : (Fin k → ℝ) →ₗ[ℝ] ℂ) t
    rw [e]
    refine ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).smul ?_
    exact contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add, hadd2, map_add])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have e : ∀ t, ψ (symplOH S T (c + A t) (c' + B t)) = ψ (symplOH S T c c') *
      Complex.exp (lam (symplOH S T c (B t)) + lam (symplOH S T (A t) c') + lam (symplOH S T (A t) (B t))) := by
    intro t
    have hs : sndA D.host.F (symplOH S T c (B t) + symplOH S T (A t) c' + symplOH S T (A t) (B t)) = 0 := by
      rw [map_add, map_add, GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inr (hB0 t)),
        GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)), GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)),
        add_zero, add_zero]
    rw [hadd1, hadd2, hadd2, show ∀ a b c d : AF D.host.F, a + b + (c + d) = a + (b + c + d) from fun _ _ _ _ => by abel,
      AddChar.map_add_eq_mul, hlam _ hs, map_add, map_add]
  rw [show (fun t => ψ (symplOH S T (c + A t) (c' + B t))) = _ from funext e]
  exact contDiff_const.mul ((h1.add h2).add hQ).cexp

end GlobalTheory.BumpMixSmooth

namespace GlobalTheory.BumpMixSmooth

theorem poinX_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
    (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => poinX ψ d T β (w + L t) := by
  intro D ψ hψ S S₀ T ρ d β hβ k L hL hL0 w
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have hx : Continuous fun t => (w + L t) ⬝ d.jX := (continuous_const.add hL).matrix_mul continuous_const
  let lX := (rmul (m := T.rank) d.jX).comp L
  let lY := (rmul (m := T.rank) d.jY).comp L
  have hlX : Continuous lX := (continuous_rmul _).comp hL
  have hlY : Continuous lY := (continuous_rmul _).comp hL
  have hlX0 : ∀ t, (lX t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  have hlY0 : ∀ t, (lY t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  let A := (d.extX T).comp lX
  let B := (d.extY T).comp lY
  have hA : Continuous A := show Continuous fun t => lX t ⬝ d.pX from hlX.matrix_mul continuous_const
  have hB : Continuous B := show Continuous fun t => lY t ⬝ d.pY from hlY.matrix_mul continuous_const
  have hA0 : ∀ t, (A t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlX0 t) d.pX
  have hB0 : ∀ t, (B t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlY0 t) d.pY
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ContDiff ℝ ∞ fun t =>
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) := by
    intro γ
    have e : ∀ t, ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ) = ψ (symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ) + A t)
          (d.extY T (w ⬝ d.jY) + B t)) * β ((w ⬝ d.jX + rat γ) + lX t) := by
      intro t
      have hx' : (w + L t) ⬝ d.jX = w ⬝ d.jX + lX t := Matrix.add_mul _ _ _
      have hy' : (w + L t) ⬝ d.jY = w ⬝ d.jY + lY t := Matrix.add_mul _ _ _
      have e1 : d.extX T (w ⬝ d.jX + lX t + 2 • rat γ) = d.extX T (w ⬝ d.jX + 2 • rat γ) + A t := by
        rw [add_right_comm, map_add]; rfl
      have e2 : d.extY T (w ⬝ d.jY + lY t) = d.extY T (w ⬝ d.jY) + B t := map_add _ _ _
      rw [hx', hy', ← d.symplOH_extX_extY T, e1, e2, add_right_comm (w ⬝ d.jX)]
    rw [show (fun t => ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ)) = _ from funext e]
    exact (contDiff_psi_symplOH hψ A B hA hB hA0 hB0 _ _).mul (hβ.smooth k lX hlX hlX0 _)
  rw [contDiff_iff_contDiffAt]
  intro t₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds t₀
  have hC : IsCompact ((fun p : Mx D T.rank ρ × Mx D T.rank ρ => p.1 - p.2) ''
      (tsupport β ×ˢ ((fun t => (w + L t) ⬝ d.jX) '' K))) :=
    (hβ.supp.isCompact.prod (hK.image hx)).image (continuous_fst.sub continuous_snd)
  have hF := finite_rat_mem T.rank ρ _ hC
  have hsum : ContDiff ℝ ∞ fun t => ∑ γ ∈ hF.toFinset,
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) :=
    ContDiff.sum fun γ _ => hterm γ
  refine hsum.contDiffAt.congr_of_eventuallyEq (Filter.eventually_of_mem hKn fun t ht => ?_)
  show poinX ψ d T β (w + L t) = _
  rw [poinX]
  refine tsum_eq_sum fun γ hγ => ?_
  have h0 : β ((w + L t) ⬝ d.jX + rat γ) = 0 := by
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨((w + L t) ⬝ d.jX + rat γ, (w + L t) ⬝ d.jX),
      ⟨subset_tsupport β hne, t, ht, rfl⟩, add_sub_cancel_left _ _⟩)
  rw [h0, mul_zero]

end GlobalTheory.BumpMixSmooth

end
end


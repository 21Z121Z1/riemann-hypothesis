import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0807
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0808
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSeparate
section
section
namespace UpperTheory.Lit
open GlobalTheory.SepRows
theorem bessel_separate_of_step_gap (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hT : RowTower) :
    SizeGap → GoodRows → RowConv → WeakSep → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  Bur.separate_of_burGapPos burGapPos GlobalTheory.T.dualCoefSpace_isTensorOverRealPlaces (_root_.GlobalTheory.T.theta_lifts_separate_points P) hT
end UpperTheory.Lit
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipRun
theorem cuspStep_of_large_flipRun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  intro hLC hP
  have hS := _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps hLC hP
  refine (GlobalTheory.RowClaim.Big.and (_root_.GlobalTheory.T.cusp_transition_rightward hS hP) (_root_.GlobalTheory.T.flipRun_descending_cusp_transition hS hP)).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t M hM a ha e' he φ f hf Q F' hF => ?_⟩
  have H := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact H.1 t M hM _ (Or.inl ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
  · exact H.2 t M hM _ (Or.inr ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipRun_cusp_transition : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  first | exact @_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | exact _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | (intros; apply _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealData
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
namespace GlobalTheory.LowRowAdel
theorem adelC_of_siegelWeil_of_doubling_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  intro hCusp hWS _hSWc hDbl hUnr hBZ hFD D G _ _ Pl0 T A Ks _ _ _ R F hL hStd
  have hHM : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule :=
    GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hLoc : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock := GlobalTheory.SingleBlock.localIntegralSingleBlock
  have hPM : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.T.adelicLift_scalar_of_innerProductFormula R F (GlobalTheory.T.adelicLift_mem_cuspForm_multiplicitySpace hCusp R F) (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law hLoc R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS (_root_.ResidueKilled.sec_of_dm hDbl) R F hL)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM) (deltaNorm_all D)
    (GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL R F (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUnr R F)) (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula hLoc R F hPM)
    (GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames D hStd) (GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra hFD R F)
end GlobalTheory.LowRowAdel
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  first | exact @_root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt | exact _root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt | (intros; apply _root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweConditionActionCoinvariantsFock
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
namespace GlobalTheory.HoweFockReal
theorem howe_condition_action_coinvariants_fock : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  GlobalTheory.RealQuot.HoweCond (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) (GlobalTheory.RealQuot.coinv ε A B eT) := by
  intro hH hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨Xs, Ws, Mo, ψ', χX, χW, om, τ, hcm, hstd, hX, hXd, hWs, hWd, hrX, hrW, hhX, hhW, hwe, hcX, hcW,
    Φ, hinj, hran, hLT, hKT, hLS, hKS⟩ := _root_.GlobalTheory.T.twist_real_place_correspondence hP D ψ θ hψ hθ ε M X A B χS χT ω eS eT hW hE
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH D.host.F D.host.E D.sp.cm.sig hcm M.rank X.rank Xs Ws Mo ψ' χX χW om hstd hX hXd hWs hWd
    hrX hrW hhX hhW hwe τ hcX hcW
  have key : ∀ N : Submodule ℂ (PolF D X.rank M.rank),
      GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
      GlobalTheory.RealQuot.coinv ε A B eT ≤ N → GlobalTheory.Published.ThetaSubInf Mo ψ' τ om (N.map Φ) := by
    intro N hs hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hran]
      exact LinearMap.map_le_range
    · intro γ hγ f hf f₁ h
      exact Submodule.map_mono hc (hLS γ hγ f hf f₁ h)
    · intro k hk f hf f₁ h
      exact Submodule.map_mono hc (hKS k hk f hf f₁ h)
    · intro γ hγ f hf f₁ h
      exact hLT N hs γ hγ f hf f₁ h
    · intro k hk f hf f₁ h
      exact hKT N hs k hk f hf f₁ h
  have hne : ∀ N : Submodule ℂ (PolF D X.rank M.rank), N ≠ ⊤ → N.map Φ ≠ Mo.Pol ψ' τ := by
    intro N hN h
    apply hN
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, hran]
  refine ⟨⟨L, fun m N hN hk => hL m (fun i => (N i).map Φ) ?_ fun i => key _ (hk i).1 (hk i).2⟩, ?_⟩
  · intro i j hij
    exact (Submodule.map_strictMono_of_injective hinj) (hN hij)
  · intro N N' hs hc hN hs' hc' hN' hsup
    apply hsum _ _ (key N hs hc) (key N' hs' hc') (hne N hN) (hne N' hN')
    rw [← Submodule.map_sup, hsup, Submodule.map_top, hran]
end GlobalTheory.HoweFockReal
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  GlobalTheory.RealQuot.HoweCond (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) (GlobalTheory.RealQuot.coinv ε A B eT) := by
  first | exact @_root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock | exact _root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock | (intros; apply _root_.GlobalTheory.HoweFockReal.howe_condition_action_coinvariants_fock <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedTranslateEqAlgebraicCombination
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedAlg
theorem moved_translate_eq_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t x hx h hh u hu
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) := fun u v hu hv =>
    GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 _ _ u v hu hv
  obtain ⟨N, hN, hlev⟩ := _root_.GlobalTheory.T.vacuum_vector_at_level_mem_fockAlgebraic hP hI hL hX t
  obtain ⟨γ, hγ, a, ha, s, hs, k, hk, hx', hkc, hss⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D A N hN x
  obtain ⟨γ', hγ', a', ha', s', hs', k', hk', hh', hkc', hss'⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D WW N hN h
  have hga : γ * a ∈ GfC A := by
    have e : γ * a = x * k⁻¹ * s⁻¹ := by rw [hx']; group
    rw [e]
    exact mul_mem (mul_mem hx (inv_mem hk)) (inv_mem hs)
  have hga' : γ' * a' ∈ GfC WW := by
    have e : γ' * a' = h * k'⁻¹ * s'⁻¹ := by rw [hh']; group
    rw [e]
    exact mul_mem (mul_mem hh (inv_mem hk')) (inv_mem hs')
  have hpair : ((x, h) : GA D A × GA D WW) = (γ * a, γ' * a') * ((s, s') * (k, k')) := by
    rw [hx', hh']
    simp only [Prod.mk_mul_mk, mul_assoc]
  obtain ⟨ζ, hζ, hkv⟩ := hlev k hk k' hk' hkc hkc'
  have h1 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (s, s') X.vac) :=
    _root_.GlobalTheory.T.moved_support_theta_algebraic hP hI hL hX t N hN s hs s' hs' hss hss'
  have h2 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t ((s, s') * (k, k')) X.vac) := by
    rw [map_mul, Module.End.mul_apply, hkv, map_smul]
    exact h1.smul hζ
  have h3 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (γ * a, γ' * a') X.vac) :=
    _root_.GlobalTheory.T.exists_rat_real_algebraic_combination_twist hP hI hL hX t γ hγ a ha γ' hγ' a' ha' hga hga'
  have h4 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac) := by
    rw [hpair, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t _ _ h3 h2
  have h5 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) :=
    ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩
  exact om_algComb hX hψ t x h h4 h5
end GlobalTheory.MovedAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_moved_translate_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.MovedAlg.moved_translate_eq_algebraic_combination | exact _root_.GlobalTheory.MovedAlg.moved_translate_eq_algebraic_combination | (intros; apply _root_.GlobalTheory.MovedAlg.moved_translate_eq_algebraic_combination <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeDictionaryOfLocalBounds
section
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumSize
theorem sum_size_dictionary_of_local_bounds (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) : DictK := by
  obtain ⟨CF0, h⟩ := _root_.GlobalTheory.T.twisted_dictionary_correspondence hP hI
  refine ⟨CF0, fun CF hCF => ⟨0, fun ε C _ => ?_⟩⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ =>
    hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt⟩
end GlobalTheory.SumSize
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @_root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | exact _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | (intros; apply _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds <;> assumption)
end
end


import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0849
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0850
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0818
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3549

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBareFormOfSaturation
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
namespace GlobalTheory.Mem.R3.Rw.Bare
set_option maxHeartbeats 4000000 in
theorem bare_form_saturated : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → DatExt0 → StepW Start fun K B f T w => ∃ (P : Pre2 K w) (x : St P), (T = TwDat.untw B T.pl → ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0 := by
  intro hA hH hE
  have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW
  have holdsL : LowerUnitaryCaseCondition := _root_.GlobalTheory.T.lu_of_multiplicity_equal hH.h1 hH.h3 hH.multL
  have datS : DatExS := GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have hW := GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field hH.h1.q12 datS holdsL hE
  have hPr := GlobalTheory.T.constructionStartingChoices_of_fine_adelicData hA.a8 hA.a9 hA.a10 hA.a6 holdsW
  have pS : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have iS : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have s1 : StepW Start fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) := by
    refine (iS.and ((pS.trans hW).and hPr)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
    obtain ⟨⟨hPin, hSupp, -⟩, hU, hP⟩ := h
    by_cases hT : T = TwDat.untw B T.pl
    · obtain ⟨Z, hX, z, g, gr, ga, ka, hF, hsub, hpsi, hsat⟩ := hU hT
      obtain ⟨P, hZ, hWt, -⟩ := hP Z hX z g gr ga ka hF hsub hpsi
      refine ⟨hPin, P, fun _ => ?_⟩
      rw [hWt, hZ]
      exact hsat
    · rcases hSupp with h | hG
      · exact absurd h hT
      obtain ⟨Z, hX, z, g, gr, ga, ka, ex, ig, core, std, hsub, hpsi⟩ := hG
      obtain ⟨P, -, -, -⟩ := hP Z hX z g gr ga ka ⟨ex, ig, core, std⟩ hsub hpsi
      exact ⟨hPin, P, fun h => absurd h hT⟩
  have hQ : StepW (fun K B f T w => Pinned K B f T w ∧ ∃ P : Pre2 K w, (T = TwDat.untw B T.pl →
      ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt)) (pinAnd HasPk) :=
    StepW.of_all fun _ _ _ _ _ _ _ h => ⟨h.1, ⟨h.2.choose⟩⟩
  refine s1.trans ((StepW.of_all fun _ _ _ _ _ _ _ h => h).and (hQ.trans GlobalTheory.T.localizationFreeStage_trueGroup_columnChoiceStep) |>.trans
    (StepW.of_all fun K B f T w hO _ h => ?_))
  obtain ⟨⟨-, P, hsat⟩, hN⟩ := h
  obtain ⟨N, hEm, hG, hN⟩ := hN P
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk B w.C (Gc B w.px) P.q.p P.q.e P.q.W₀ P.q.n (fun _ _ => 0)
    (fun _ _ => le_rfl) (frames_unit P.q.t) (fun u => ((w.C.fm u).lat 0).L) (fun _ => 0) (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l P.hX) (rows_le P.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hA.a8 hA.a9 hA.a10 hA.a6 K B f T w P ⟨_, _, V, S, N, P.Z₀.G⟩
    ⟨hV, hG, (hN V S P.Z₀.G).1, (hN V S P.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  refine ⟨P, x, hsat, ?_⟩
  exact Eq.mpr (congrArg (fun o : P.q.Over => IsEmpty o.N.nd.Loc ∧ ∀ j v, o.η j v = 0) hx) ⟨hEm, fun _ _ => rfl⟩
end GlobalTheory.Mem.R3.Rw.Bare
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bare_form_of_saturation : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → DatExt0 → StepW Start fun K B f T w => ∃ (P : Pre2 K w) (x : St P), (T = TwDat.untw B T.pl → ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt) ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0 := by
  first | exact @_root_.GlobalTheory.Mem.R3.Rw.Bare.bare_form_saturated | exact _root_.GlobalTheory.Mem.R3.Rw.Bare.bare_form_saturated | (intros; apply _root_.GlobalTheory.Mem.R3.Rw.Bare.bare_form_saturated <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareCommutesWithAll
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
end GlobalTheory.SquareComm
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
theorem square_commutes_with_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
      ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  intro hPr hWC hK
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ t i j => ?_⟩⟩
  exact commutesWith_of_isSquareConst hWC hK hPr.cuspDecayBound s.core.lev
    (squareStanding_of_setting s s.size.2.1.eleven_le ch.G t) (hch.const i j t)
end GlobalTheory.SquareComm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_square_commutes : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  first | exact @_root_.GlobalTheory.SquareComm.square_commutes_with_all | exact _root_.GlobalTheory.SquareComm.square_commutes_with_all | (intros; apply _root_.GlobalTheory.SquareComm.square_commutes_with_all <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ThetaFinRelDef
open GlobalTheory.SquareComm
open scoped ComplexOrder
theorem theta_integral_finite_relation_eq_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  intro _ D ψ θ hψ hθ M X A B χ χ' ω hω hsig ν 𝓕 hF
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hpd : ∀ τ, (gramAt D M τ).PosDef := fun τ => GlobalTheory.Core.CoefGram.posDef_of_hasSignature _ (hsig τ)
  have hcc : GlobalTheory.Unf.CoCpt M := (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D M).2 hpd
  have hth : ∀ Φ ∈ algF ψ θ false A B, IsThetaFunO ψ M X Φ := fun Φ hΦ =>
    GlobalTheory.SquareComm.ThetaLeft.isThetaFunO_of_mem_algF hψ hθ A B hΦ
  have hleft := GlobalTheory.SquareComm.ThetaLeft.main D ψ θ hθ M X A B χ χ' ω hω
  have hsub : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ - Ψ) = thetaKO ω g k Φ - thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_sub]
  have hadd : ∀ g k (Φ Ψ : WO M X → ℂ), thetaKO ω g k (Φ + Ψ) = thetaKO ω g k Φ + thetaKO ω g k Ψ := by
    intros; simp [thetaKO, map_add]
  have hsmul : ∀ g k (c : ℂ) (Φ : WO M X → ℂ), thetaKO ω g k (c • Φ) = c * thetaKO ω g k Φ := by
    intros; simp [thetaKO, map_smul]
  have hzero : ∀ g k, thetaKO ω g k (0 : WO M X → ℂ) = 0 := by
    intros; simp [thetaKO]
  have hint : ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
    intro Φ hΦ h
    exact (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D M hcc _
      ⟨fun γ hγ g => hleft Φ hΦ γ hγ g h, (hω'.om_cont Φ (hth Φ hΦ) 0).comp (Continuous.prodMk_left h)⟩).2.2
      ⟨ν, 𝓕, hF.1, hF.2⟩
  intro Φ hΦ
  suffices key : (∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) ∧ thetaInt ω ν 𝓕 Φ = 0 from key.2
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, -, Ψ, hΨ, rfl⟩ := hx
    have e : ∀ g k, thetaKO ω g k (ω (u, 1) Ψ) = thetaKO ω (g * u) k Ψ := fun g k => by
      unfold thetaKO
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    have tr := fun k => integral_rightTranslate hF (f := fun g => thetaKO ω g k Ψ)
      (fun γ hγ g => hleft Ψ hΨ γ hγ g k) u
    have i1 : ∀ k, IntegrableOn (fun g => thetaKO ω g k (ω (u, 1) Ψ)) 𝓕 ν := fun k => by
      simp only [e]; exact (tr k).1.2 (hint Ψ hΨ k)
    refine ⟨fun k => ?_, ?_⟩
    · simp only [hsub]; exact (i1 k).sub (hint Ψ hΨ k)
    · funext k
      simp only [thetaInt, hsub, Pi.zero_apply]
      rw [integral_sub (i1 k) (hint Ψ hΨ k)]
      simp only [e]
      rw [(tr k).2, sub_self]
  | zero =>
    exact ⟨fun k => by simp only [hzero]; exact integrableOn_zero, by funext k; simp [thetaInt, hzero]⟩
  | add x y _ _ hx hy =>
    refine ⟨fun k => by simp only [hadd]; exact (hx.1 k).add (hy.1 k), ?_⟩
    funext k
    have := integral_add (hx.1 k) (hy.1 k)
    have ex := congrFun hx.2 k
    have ey := congrFun hy.2 k
    simp only [thetaInt, Pi.zero_apply] at ex ey
    simp only [thetaInt, hadd, Pi.zero_apply, this, ex, ey, add_zero]
  | smul c x _ hx =>
    refine ⟨fun k => by simp only [hsmul]; exact (hx.1 k).const_mul c, ?_⟩
    funext k
    have ex := congrFun hx.2 k
    simp only [thetaInt, Pi.zero_apply] at ex
    simp only [thetaInt, hsmul, Pi.zero_apply, integral_const_mul, ex, mul_zero]
end GlobalTheory.ThetaFinRelDef
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X), GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0) → ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 → ∀ Φ ∈ finRel ω (algF ψ θ false A B), thetaInt ω ν 𝓕 Φ = 0 := by
  first | exact @_root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | exact _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero | (intros; apply _root_.GlobalTheory.ThetaFinRelDef.theta_integral_finite_relation_eq_zero <;> assumption)
end
end


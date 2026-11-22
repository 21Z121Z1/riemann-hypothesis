import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0176

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotentialStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointRowWeight_antitone_of_maxPotential : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → ∀ τ, Antitone (w τ) := by
  first | exact @GlobalTheory.HighWt.antitone_of_pot_max | exact GlobalTheory.HighWt.antitone_of_pot_max | (intros; apply GlobalTheory.HighWt.antitone_of_pot_max <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightBoundsDualWeylModuleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointRowWeight_bounds_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ), GlobalTheory.HighWt.JointWt O N lam Gm w → ∀ τ, ∑ a : Fin N, w τ a = ∑ a : Fin N, lam τ a ∧ ∀ a : Fin N, lam τ (N - 1) ≤ w τ a ∧ w τ a ≤ lam τ 0 := by
  first | exact @GlobalTheory.HighWt.jointWt_bounds | exact GlobalTheory.HighWt.jointWt_bounds | (intros; apply GlobalTheory.HighWt.jointWt_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_at_small_place : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @GlobalTheory.FrameOf.kapSt | exact GlobalTheory.FrameOf.kapSt | (intros; apply GlobalTheory.FrameOf.kapSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypesStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes : TraceRat := by
  first | exact @GlobalTheory.TraceRatPf.traceRat | exact GlobalTheory.TraceRatPf.traceRat | (intros; apply GlobalTheory.TraceRatPf.traceRat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThirdStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_third : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.mumaxTop | exact GlobalTheory.mumaxTop | (intros; apply GlobalTheory.mumaxTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hlam Gm _ _ _ _ _ hH hS hSQ mu hmu hemb m _ θ0 h0e h0b h0o hns
  obtain ⟨θ, hθe, hθo⟩ := GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor l ι P.Nr F W.lam mu jK ϖ hF hJ hϖ Gm hH hemb m hns
  obtain ⟨θ', hθ'e, -, hc⟩ := GlobalTheory.T.exists_galoisConj_eigenSystem_congruent l ι P.Nr F mu hF θ θ0 m hθe hθo h0o
  have hB : BlockFor Ω inc P W mu :=
    GlobalTheory.T.blockData_of_congruent_heckeSystem hCheb E Ω l ι inc P W F Bk hG mu θ' θ0 (fun τ => (hmu τ).1) hθ'e h0e h0b hc
  have hnt : Nontrivial Gm := IsSimpleModule.nontrivial (alg F.O P.Nr W.lam) Gm
  have hlnk := GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction F.O P.Nr ι W.lam mu l ϖ (Fact.out) hϖ hϖl hlam (fun τ => (hmu τ).1) Gm hnt hSQ hemb
  exact hlink mu (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2, hlnk τ⟩) hB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservedByComponentStabilizerStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserved_by_component_stabilizer : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  first | exact @GlobalTheory.ShareOn.sub_mem_half_smul_latP | exact GlobalTheory.ShareOn.sub_mem_half_smul_latP | (intros; apply GlobalTheory.ShareOn.sub_mem_half_smul_latP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabiliserVacuumEigenvalueOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  first | exact @GlobalTheory.DblVacV.eigen_eq_one | exact GlobalTheory.DblVacV.eigen_eq_one | (intros; apply GlobalTheory.DblVacV.eigen_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafLevelSquareBoundStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leaf_level_square_bound : AtRec fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  first | exact @GlobalTheory.BigOn.levelSq_yBound_atRec | exact GlobalTheory.BigOn.levelSq_yBound_atRec | (intros; apply GlobalTheory.BigOn.levelSq_yBound_atRec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionEquivariantAtFrameConstantsOfClausesStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_equivariant_at_frameConstants_of_clauses : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, O.EquivAt (κ i) (u • cc) := by
  first | exact @GlobalTheory.FrameConstMoveCore.equivAt_of_ccIs_core | exact GlobalTheory.FrameConstMoveCore.equivAt_of_ccIs_core | (intros; apply GlobalTheory.FrameConstMoveCore.equivAt_of_ccIs_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeUnitriangularUnipotentModPlaceStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  first | exact @GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place | exact GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place | (intros; apply GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMul
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_const_of_forall_unit_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {O : Set V} (hO : IsOpen O) (hc : IsPreconnected O) (hne : O.Nonempty) {ι : Type} (P Q : ι → V → ℂ)
    (hP : ∀ j, DifferentiableOn ℂ (P j) O) (hQ : ∀ j, DifferentiableOn ℂ (Q j) O)
    (h : ∀ x ∈ O, ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ j, P j x = u * Q j x) :
    ∃ c : ℂˣ, ∀ j, ∀ x ∈ O, P j x = c * Q j x := by
  by_cases h0 : ∃ j, ∃ x₁ ∈ O, Q j x₁ ≠ 0
  · obtain ⟨j₀, x₁, hx₁, hq⟩ := h0
    obtain ⟨u₁, hu₁, hPu⟩ := h x₁ hx₁
    have hu0 : u₁ ≠ 0 := by
      intro e
      rw [e, norm_zero] at hu₁
      exact zero_ne_one hu₁

    have step : ∀ j, ∀ x ∈ O, P j x + (1 - Q j x₁) / Q j₀ x₁ * P j₀ x =
        u₁ * (Q j x + (1 - Q j x₁) / Q j₀ x₁ * Q j₀ x) := by
      intro j
      set μ : ℂ := (1 - Q j x₁) / Q j₀ x₁ with hμ
      obtain ⟨-, c', hc'⟩ := GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq V Unit O hO hc hne
        (fun x => P j x + μ * P j₀ x) (fun _ x => Q j x + μ * Q j₀ x)
        ((hP j).add ((hP j₀).const_smul μ))
        (fun _ => (hQ j).add ((hQ j₀).const_smul μ))
        (fun x hx => by
          obtain ⟨u, hu, hPx⟩ := h x hx
          refine ⟨(), ?_⟩
          simp only [hPx, ← mul_add, mul_left_comm μ u, norm_mul, hu, one_mul])
      have hQ1 : Q j x₁ + μ * Q j₀ x₁ = 1 := by
        rw [hμ, div_mul_cancel₀ _ hq]
        ring
      have hc1 : c' = u₁ := by
        have e := hc' x₁ hx₁
        rw [hQ1, mul_one, hPu j, hPu j₀, mul_left_comm μ u₁, ← mul_add, hQ1, mul_one] at e
        exact e.symm
      intro x hx
      rw [hc' x hx, hc1]
    have h₀ : ∀ x ∈ O, P j₀ x = u₁ * Q j₀ x := by
      intro x hx
      have e := step j₀ x hx
      have hne' : 1 + (1 - Q j₀ x₁) / Q j₀ x₁ ≠ 0 := by
        rw [add_div' _ _ _ hq]
        simp [hq]
      have : (1 + (1 - Q j₀ x₁) / Q j₀ x₁) * (P j₀ x - u₁ * Q j₀ x) = 0 := by
        linear_combination e
      rcases mul_eq_zero.1 this with h1 | h1
      · exact (hne' h1).elim
      · exact sub_eq_zero.1 h1
    refine ⟨Units.mk0 u₁ hu0, fun j x hx => ?_⟩
    have e := step j x hx
    rw [Units.val_mk0]
    linear_combination e - (1 - Q j x₁) / Q j₀ x₁ * h₀ x hx
  · push_neg at h0
    refine ⟨1, fun j x hx => ?_⟩
    obtain ⟨u, -, hPx⟩ := h x hx
    rw [hPx j, h0 j x hx, mul_zero, mul_zero]

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem transp_reads_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  intro D L hT Gi Gl Kc Y cX eX Csz p hp r h hr i v ψ γ k k' a ht
  obtain ⟨hm, hb, -⟩ := ht
  have hl := h.laws v
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  have hU : IsUnf (uAt r v i) := hl.p.unf _ hj _ hσ
  have hpins := hl.p.pins
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpins.2.2.2 _ hj).1, (hpins.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D (r.used v).full.Q ((i : ℕ) + 1) hpq hpins.2.1.2
  have hsecF : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      F.1 ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    ((mem_cusp _ _ _ _ _ _).1 (Submodule.mem_inf.1 F.2).1).1
  have hsecG : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1 ∈
        sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ (hsecF F)
  have P1 : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom)
      (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _)
      (hbt : FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩)
        (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩)))
      (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t : CAt (r.used v).full.σ₀) *
          rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx hy t hbt F
    have e1 : rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (evR _ _ (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1)
          ((uAt r v i).un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) =
        toC (evR _ _ F.1 ((uAt r v i).un k' ⟨_, hy⟩)) := dif_pos hy
    have e3 := evalAt_actL hL (hl.p.evalWD _ hj) frMap_trans_id γ (hsecF F).1 ((uAt r v i).un k ⟨x, hx⟩)
    have e4 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ _).2.2.2.2.2.2 (CAt _)
      (inferInstanceAs (IsReduced ℂ)) _ _ F.1 (hsecF F) t _ _ hbt
    rw [e1, e2]
    exact congrArg toC (e3.trans e4)
  have hUf : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) := hU
  have hσf : Formalism.L2.PjFree.GoodEmb (r.used v).full.Q.c (r.used v).full.σ₀ := hσ
  have hr1 : 1 ≤ D.R.r := hU.1 ▸ hpq
  have hxi : ∀ k k' (τ : D.host.E →+* ℂ), ‖τ ((uAt r v i).X k).ξ0‖ = ‖τ ((uAt r v i).X k').ξ0‖ :=
    fun k k' τ => (hl.p.xiAbs _ hj _ hσ k τ).trans (hl.p.xiAbs _ hj _ hσ k' τ).symm
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf
  have hsk : ∀ (f : Rul ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c),
      f ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n → ∀ k,
      ((uAt r v i).X k).IsSec (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) (rdU (uAt r v i) f k) :=
    fun f hf k => hU.2.2.2.2.1 _ _ (dom_wtA _) f hf k
  have key : ∀ x ∈ ((uAt r v i).X k).dom, ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
        rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
          u * rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx
    obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀'⟩, -⟩ := hun1 k ⟨x, hx⟩
    have e₀ : x₀.1 = rmul x b₀ := e₀'
    obtain ⟨hy₀, t₀, hbt₀⟩ := hb x₀.1 x₀.2
    obtain ⟨ρ, ν, -, -, hmv⟩ := mvPt_spec hL.total γ ((uAt r v i).un k x₀)
    have hx₀' : GlobalTheory.FrameNorm.IsUnitFr ((uAt r v i).X k') (castFrame hm.psi (lact a x₀.1)) := fun τ j => by
      exact (congrArg norm (hm.dmin_eq x₀.1 τ j)).trans (hx₀ _ _)
    obtain ⟨-, -, -, -, -, -, ht1⟩ := GlobalTheory.LevelCusp.exists_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf hr1
      hxi (x := x₀) (x' := ⟨castFrame hm.psi (lact a x₀.1), hy₀⟩) hmv hbt₀ hx₀ hx₀'
    refine ⟨toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀), ?_, fun F => ?_⟩
    · have : toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀) =
          ∏ j, toC (t₀ j : CAt (r.used v).full.σ₀) ^ ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n j := rfl
      rw [this, norm_prod]
      exact Finset.prod_eq_one fun j _ => by
        rw [norm_pow, show ‖toC (t₀ j : CAt (r.used v).full.σ₀)‖ = 1 from ht1 j, one_pow]
    · have A := P1 x₀.1 x₀.2 hy₀ t₀ hbt₀ F
      have B := (hsk _ (hsecG F) k).2.1 x hx b₀ hb₀
      have C := (hsk _ (hsecF F) k').2.1 _ (hb x hx).1 _ (GlobalTheory.Dict.Pull.cast_bor hm.psi hb₀)
      have e5 : castFrame hm.psi (lact a x₀.1) = rmul (castFrame hm.psi (lact a x)) (GlobalTheory.Dict.castFr hm.psi b₀) := by
        rw [e₀]
        exact (congrArg (castFrame hm.psi) (GlobalTheory.Dict.Extend.lact_rmul a x b₀)).trans (GlobalTheory.Dict.Pull.cast_rmul hm.psi _ _)
      have e6 : bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k') (GlobalTheory.Dict.castFr hm.psi b₀) =
          bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) b₀ :=
        GlobalTheory.Dict.Pull.cast_bchar hm.psi (GlobalTheory.LevelCusp.laU_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hm _ _) b₀
      rw [e5, C, e6, e₀, B] at A
      have hβ := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne ((uAt r v i).X k) (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) hb₀
      apply mul_left_cancel₀ hβ
      rw [A]
      ring
  obtain ⟨c, hc⟩ := exists_const_of_forall_unit_mul (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).isPreconnected
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x)
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)))
    (fun F => (hsk _ (hsecG F) k).1)
    (fun F => (hsk _ (hsecF F) k').1.comp
      ((GlobalTheory.Dict.Pull.cast_diff hm.psi).comp (GlobalTheory.Dict.Extend.differentiable_lact a)).differentiableOn
      (fun x hx => (hb x hx).1))
    key
  refine ⟨c, fun F x hx h2 => ?_⟩
  exact hc F x hx

end GlobalTheory.ShareOn
end
end


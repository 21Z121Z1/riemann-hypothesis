import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0429
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0190
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1025
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3437
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0008
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIs
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem com_is_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (_root_.GlobalTheory.BaseChain.com_z W).Is := by
  intro D L hT Gi Gl Kc Yd cX ex W hP
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have h2 := D.R.two_le_m
  exact GlobalTheory.SeeSaw.ComCols.com_is_of_levCh (levAt_is hC.lev) (_root_.GlobalTheory.BaseChain.com_z W) hC.models.inf
    (hC.chain.ωY W.P.A3.A.μ0 0 (by omega)).std rfl (chrEq_mu_base hC.lev) hC.lev.eta hC.lev.chi
end GlobalTheory.BaseChain
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DescentEVMemLevel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem descent_eV_mem_level_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.GlobalTheory.MiS.LevelHypothesis W → (∀ t F, (_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB hLv t F
  obtain ⟨-, -, -, hC, -⟩ := hB.hyp
  obtain ⟨⟨s, hs⟩, hRZ, gE, hU, hG, h2, hl0, hl1⟩ := hLv
  have hK := RealDat3.kFormR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hJ := RealDat3.jIsoR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hDn := Formalism.IndefR.CxPass.descent_of_types hs hK hJ hRZ hU hG h2 hl0 hl1 true
  have hE := Formalism.IndefR.Links.EvTie.evTie_real ⟨s, hs⟩ W.Q.Rl W.Q.F
  have hV : (_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).V0C W.Q.F.cv true t :=
    Submodule.subset_span ⟨_, hE.1 t F, rfl⟩
  exact hDn t (Submodule.mem_map_of_mem hV)
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip
open GlobalTheory.Mem.Chr hiding HChar
namespace GlobalTheory.CuspRep.ParLaws
section Group
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end Group
section Local
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Par
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
theorem reciprocity_unramified_iff_spherical (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) (σ : IrrRep (GL (Fin a) (w.adicCompletion E))) :
    (rc (cls σ)).unr ↔ IsSpherical σ.ρ := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  rw [← H.sph]
  exact ⟨fixed_ne_bot_of_equiv (equivRep σ).symm, fixed_ne_bot_of_equiv (equivRep σ)⟩
theorem reciprocity_eq_diagonal_inv_of_has_satake (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ}
    (hα : HasSatake σ.ρ α) : rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := H
  have φ := equivRep σ
  exact H.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
variable [IsTotallyComplex E]
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
theorem local_parameter_eq_reciprocity_of_is_local_component {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ)
    (h : IsPlaceOver A w) : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls (toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [_root_.GlobalTheory.CuspRep.ParLawsT.locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl
theorem dim_local_parameter_eq_rank (π : CG E a) (h : IsPlaceOver A w) : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpDim = a := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
include hF in
theorem eventually_unramified_local_parameter (π : CG E a) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).unr := by
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  refine (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h).symm ▸ (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) _).2 ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm
theorem local_parameter_of_hecke_character_eq_reciprocity (χ : HChar E) (h : IsPlaceOver A w) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (.ofChar (χ.loc w) (isSmoothChar_loc χ w)) :=
  _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (CG.isLoc_ofChar χ w) h
end Par
section Conj
end Conj
section Host
end Host
end GlobalTheory.CuspRep.ParLaws
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAutSpecStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_rational_level_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb) := by
  first | exact @_root_.GlobalTheory.AutPart.exists_autSpec_alt | exact _root_.GlobalTheory.AutPart.exists_autSpec_alt | (intros; apply _root_.GlobalTheory.AutPart.exists_autSpec_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportAtOfBundlesStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_of_published_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → IsGalois ℚ ↥D.LL0 → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  first | exact @_root_.GlobalTheory.ExportClose.exportAt_of_bundles_alt | exact _root_.GlobalTheory.ExportClose.exportAt_of_bundles_alt | (intros; apply _root_.GlobalTheory.ExportClose.exportAt_of_bundles_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfReadingStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  first | exact @_root_.GlobalTheory.BigOn.exportSt_of_reading_alt | exact _root_.GlobalTheory.BigOn.exportSt_of_reading_alt | (intros; apply _root_.GlobalTheory.BigOn.exportSt_of_reading_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAboveOfAlgebraicCharacterWDAl
section
set_option synthInstance.maxHeartbeats 200000

section
namespace GlobalTheory
theorem heckeLAdicParameterAbove_of_algebraicCharacterWD_alt (H : GlobalTheory.Published.AlgebraicCharacterWD) :
    _root_.GlobalTheory.Published.HeckeLAdicParameterAboveAlt := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A h O _ _ _ Bw hj ξ hξ rc hrc
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, L⟩ := hOpn) | obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [H E Ω l P AI hT ι art hart χ n μ hχ hμ hL w A h O Bw hj ξ hξ a ha]
  exact (L.one ξ hξ.1).symm
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelTameCharacter
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace DiscreteGroups.sglob.DzType.Rt
open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel GlobalTheory.TameCharLabel
theorem label_reduction_alt : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u := by
  intro H hL D Γ k v χ hχ u htame hlab
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hp : resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k := by
    haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨h1, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    exact (GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1
  refine ⟨hp, fun L hteich hgen => ?_⟩
  obtain ⟨θ, hθ⟩ := exists_charLift hp htame
  set x := _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    (GlobalTheory.LocLanglands.cls (IrrRep.det (Fin 1) χ hχ)) with hx
  have hlab' : GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) x = X - C u := hlab
  refine ⟨θ, hθ, fun hu0 => ?_, fun u' hu' => ?_⟩
  · have := GlobalTheory.WeilDeligne.WD.lab_coeff_zero_ne_zero (D.ntypes.teichC k) (D.ntypes.tg k v) x
    rw [hlab', hu0] at this
    simp at this
  · obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
    obtain ⟨P, hP, hPe⟩ := exists_label L θ u' hu'
    have hT : Formalism.L2.NT.TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (Γ.kv k v) (D.ntypes.tg k v) L.gen := by
      rw [hgen]; exact Γ.tg_tame k v
    have h1 := H D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
      (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) (I.i k v) (I.cont k v) (Γ.kv k v) L _ (D.ntypes.tg_mem k v) hT 1 (Or.inl rfl)
      (IrrRep.det (Fin 1) χ hχ) (GlobalTheory.LocGL.IrrGL.isCusp_ofChar χ hχ) (tauOne θ) P hP
      (inflates_det (I.i k v) (I.cont k v) hχ hθ)
    rw [hPe] at h1
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    have hdim : x.lpDim = 1 := hl.dim _
    have h2 := GlobalTheory.WeilDeligne.WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (D.ntypes.tg k v) x
      (by rw [hlab', hdim, natDegree_X_sub_C])
    have hr : Formalism.CyclotomicNorms.rootsBar (X - C u) = {algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) u} := by
      simp [Formalism.CyclotomicNorms.rootsBar]
    rw [hlab', hr, h1] at h2
    have h3 := congrArg (fun q => q.coeff 0) h2
    simp at h3
    rw [hteich]
    exact h3
set_option maxHeartbeats 1000000 in
theorem labAt_ofDet_tame_eq_X_sub_C : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u :=
  _root_.DiscreteGroups.sglob.DzType.Rt.label_reduction_alt
end DiscreteGroups.sglob.DzType.Rt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LpDimLocRec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
theorem lpDim_locRec_alt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E))) : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls τ)).lpDim = n := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact H.dim _
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
def weilDeligneParameterOfLocalDatum {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  p.2.1 ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 p.1.1.w) (cls p.1.2)
def weilDeligneParameterAtPlace (σ : D.what₂.FT) (w : PlE D.host) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) := by
  classical
  exact if h : Nonempty (LocAt D rep σ w) then _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep h.some else (unrW D).par σ w
theorem parameter_of_local_datum_eq_reciprocity {σ : D.what₂.FT} {w : PlE D.host} (p : LocAt D rep σ w) (s : SplitPlace D.host.E) (hs : s.w = w)
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterOfLocalDatum hL D rep p = hs ▸ _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
  subst hs
  obtain rfl := splitPlace_eq_of_isLocS _ _ s s0 hw τ τ0 hτ hl
  show _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ0) =
    _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 _) (GlobalTheory.LocLanglands.cls τ)
  rw [show GlobalTheory.LocLanglands.cls τ0 = GlobalTheory.LocLanglands.cls τ from
    congrArg (Sigma.mk _) (cl_eq_of_isLocS (rep σ) _ τ0 τ hl hτ)]
theorem parameter_at_place_eq_reciprocity_of_local_component (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ) :
    _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ s.w = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls τ) := by
  classical
  have h : Nonempty (LocAt D rep σ s.w) := ⟨⟨⟨s, τ⟩, rfl, hτ⟩⟩
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  rw [dif_pos h]
  exact _root_.GlobalTheory.RowPar.parameter_of_local_datum_eq_reciprocity hL D rep _ s rfl τ hτ
theorem dim_parameter_at_place_eq_rank (σ : D.what₂.FT) (w : PlE D.host) : (_root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace hL D rep σ w).lpDim = D.R.r := by
  classical
  unfold _root_.GlobalTheory.RowPar.weilDeligneParameterAtPlace
  by_cases h : Nonempty (LocAt D rep σ w)
  · rw [dif_pos h]
    generalize h.some = p
    obtain ⟨⟨s0, τ0⟩, hw, hl⟩ := p
    subst hw
    exact _root_.GlobalTheory.RowPar.lpDim_locRec_alt hL _ τ0
  · rw [dif_neg h]
    exact (unrW D).dim σ w
end Loc
end GlobalTheory.RowPar
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LpSumSegmentsNu
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
noncomputable section
namespace GlobalTheory.NuShift
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end GlobalTheory.NuShift
namespace GlobalTheory
open GlobalTheory.NuShift
theorem lpSum_segments_nu_alt : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)) =
        (sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨a, ha, ε, L⟩ := hOpn) | obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [← sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [L.nu_eq, WD.lpTw_add, add_comm, ← WD.lpTw_add, lpChar_lpTw]
  rfl
end GlobalTheory
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadTwisted
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAUpper.Read
section Record
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
end Record
end GlobalTheory.ThmAUpper.Read
namespace GlobalTheory.ThmAUpper
open Read GlobalTheory.ToricDenom GlobalTheory.FunObj.SqNum in
theorem read_twisted_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit _ hF w hw i j s hs1 hs2 T₀ ψc T _ h0 _ hψ hT'
  obtain ⟨_, _, -, hb, -⟩ := hF
  obtain ⟨-, ι, hι, -, hall⟩ := hfit.1.list _ (hfit.1.setting.inW1 hw)
  refine ⟨ι, hι, fun b => ?_⟩
  have hi := i.2
  let a : Fin D.R.m := ⟨D.R.m - i - 1, by omega⟩
  have ha : a.1 + 1 = D.R.m - i := by simp only [a]; omega
  have hsN : s ≤ BlochKatoReduction.Gen.NFun D.R + 1 := by
    have h3 : halfRank D i j ≤ GlobalTheory.ChiGrid.bigN D := by
      have a : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) ≤ GlobalTheory.ChiGrid.bigN D := by
        have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
        have h2 : (i + 1) * GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ i.2
        simp only [GlobalTheory.ChiGrid.rankV, GlobalTheory.ChiGrid.bigN, Ranks.r, mul_add] at *
        omega
      have e : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) = GlobalTheory.ChiGrid.rankV D i j + D.R.t + GlobalTheory.ChiGrid.sLen D := by
        simp only [GlobalTheory.ChiGrid.rankV]; ring
      unfold halfRank; omega
    have h12 : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.ChiGrid.bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
    omega
  obtain ⟨lam, hlam, -, hth⟩ := hall j a s b hs1 hsN
  have e1 : GlobalTheory.LamTie.cond0 D.host (lamOf d.G).w0 = condF d.G.pl := cond0_eq d.G hb
  have e2 : (lamOf d.G).lam0 (D.ntw.l (ex.nch.twI w)) j a =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    rw [lambdaGrid_apply, ha, ex.nch.twI_l, nuH, xiH_base p, mul_one, div_mul_eq_mul_div]
  have e3 : GlobalTheory.LamTie.phi D.host ∘ D.eTau = cmPhi D := rfl
  have e4 : (lamOf d.G).kap j a s ∘ D.eTau = kap D 1 i j s := by
    funext τ
    simp only [Function.comp, GlobalTheory.LamTie.LamDat.kap, lamOf, kap, Formalism.L2.Host.eExp, Equiv.symm_apply_apply, ha]
    have : (GlobalTheory.ChiGrid.num D 1 τ).e (j + 1) = ⌊(D.hc τ).e j⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e (j + 1) = _
      simp [GlobalTheory.SignedHC.GridData.extend]
    rw [this]
  rw [e1, e2] at hth
  obtain ⟨u, -, hth⟩ := hth
  obtain ⟨_, π, t, hπ, ht, hδ⟩ := hth _ (hfit.1.cond w hw)
  obtain ⟨_, π0, t0, -, ht0, hδ0⟩ := hth ∅ ⟨by simp, by simp, by simp⟩
  replace ht := fun q => isClassTerm_reindex D.eTau (ht q)
  replace ht0 := fun q => isClassTerm_reindex D.eTau (ht0 q)
  rw [e3, e4] at ht ht0
  have e5 : condQ (condF d.G.pl) (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = condF d.G.pl := by
    simp [condQ, belowSet]
  have s0 := sum_th_eq ht0 hδ0 (t := T₀) (by rw [e5]; exact h0)
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb D.ntw (ex.nch.twI w) (ex.nch.k' w)
  obtain ⟨e, he, hchar⟩ := exists_pow_char hfit.1.psi hw (hp.ties.psiVal w hw) (atSide D.ntw b ι) J
  have hc : condQ (condF d.G.pl) (belowSet (ex.nch.Q w)) ≠ ⊥ :=
    mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have key : ∀ a : ℤ, J (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (ex.nch.psi' w ^ a)) =
      u * atSide D.ntw b ι (T (ψc ^ (e * a))) := fun a => by
    refine thEval_eq_twisted hJ (fun q => ?_) ht hδ (hT' _)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hchar hc π hπ y
    have h2 : ∀ (x : (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))ˣ), J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ (x ^ a : _ˣ)) =
        J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ x) ^ a := fun x => by
      have := congrArg Units.val (map_zpow (Units.map (J.comp
        (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _)).toMonoidHom) x a)
      rw [Units.val_zpow_eq_zpow_val] at this
      exact this
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, h2, ← h1, hψ, zpow_mul, Units.val_zpow_eq_zpow_val _ a, map_zpow₀]
  refine ⟨lam, J, if b then e else -e, hlam, by cases b <;> simp [he, he.neg_left], RingHom.ext hJ, fun a => ?_⟩
  rw [hJ, s0, hlam]
  cases b
  · have : BlochKatoReduction.Gen.psiAt false (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ (-a) := by simp [BlochKatoReduction.Gen.psiAt]
    rw [this, key]
    simp only [Bool.false_eq_true, if_false, mul_neg, neg_mul]
    ring
  · have : BlochKatoReduction.Gen.psiAt true (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ a := rfl
    rw [this, key]
    simp only [if_true]
    ring
end GlobalTheory.ThmAUpper
end
end
end


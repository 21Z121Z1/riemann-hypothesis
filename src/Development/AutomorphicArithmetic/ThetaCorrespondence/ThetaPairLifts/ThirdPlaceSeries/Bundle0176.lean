import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0152
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0121
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0832
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0174
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0175
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0096
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0103
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0118
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0130
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspFormBoundedOnFrames
section
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.ThinTwist
theorem twist_thin_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := by
  intro hP _ _ hS hFD
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have F := _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD
  have Q := _root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (F.and Q)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, -, hj, -⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  intro u1 hq Z σ hσ _ _ f hf
  obtain ⟨-, -, -, -, -, -, -, -, hG⟩ := hC i hi u1 hq
  rw [hG] at hf ⊢
  exact _root_.GlobalTheory.ThinTwist.exists_constant_twist_of_thin_divisor hP p.T _ Y _ _ hL hj hY.1 hFl u1 _ _ Z σ hσ hf
end GlobalTheory.ThinTwist
theorem _root_.GlobalTheory.T.cusp_form_bounded_on_frames_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := _root_.GlobalTheory.ThinTwist.twist_thin_alt_alt
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DistinguishedSectionBoundaryValuationVanishes
section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KeyValZero
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem covers_distinguished_section_valuation_eq_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g _ hpt hZ => ?_⟩
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := twSec_keyRoot_val _ _ _ _ _ _ _ Y.U (xiR (Fm.D x ι)) hY.1.unf hY.1.xiAbs hY.1.geo hL.pos hL.good Z
  refine ⟨t, ht T io y' (fun a => ?_) hZ⟩
  letI := io.toAlgebra
  have h1 := ptY_str TF.X y'.1
  rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
  obtain ⟨b, hb⟩ := Spec.map_surjective
    (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
  rw [← hb, ← Spec.map_comp] at h1
  exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
end GlobalTheory.KeyValZero
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.distinguished_section_boundary_valuation_eq_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  first | exact @_root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero | exact _root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero | (intros; apply _root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAdStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cenLoc_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := by
  first | exact @_root_.GlobalTheory.CenLocAt.cenLoc_at_member | exact _root_.GlobalTheory.CenLocAt.cenLoc_at_member | (intros; apply _root_.GlobalTheory.CenLocAt.cenLoc_at_member <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinE
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem WPt.exists_recPinE_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) →
      Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : _root_.Formalism.L2.RecTAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R := by
  intro hA hW hR hL p K q hLT hZe hE
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.T.exists_spectral_data_compatible hA hW hL p K q hLT hZe
  obtain ⟨t, hK, hstd, hrd⟩ := GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie p.s K q hE
  obtain ⟨T, hTS, hTk, hcrd, hpin, hj, ⟨⟨hw⟩⟩⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses hL p K q S t hS hK
  have hp := GlobalTheory.Mem.Top.Bl.hostPins_wpt hR p.s K q
  subst hTS hTk
  obtain ⟨hd, -⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hA _ _ _ _ _ _ _ _ q.O.ex T.toTiedDataS hp q.x.pin.d3b
  exact ⟨⟨T, hpin, hj, ⟨hd⟩, hw⟩, ⟨⟨hS, hK, hcrd⟩, hE, hstd, hrd⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.expAlg_of_serAlg_alt (_root_.GlobalTheory.BigOn.Exp.serAlg_of_serRef_scaleRoot (_root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat h1 h2 h3 h4) (_root_.GlobalTheory.T.scale_root_of_reciprocity_inputs h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpOneLevel
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem expOne_level_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) :=
  _root_.GlobalTheory.SerSmall.one_expansion_alt
end GlobalTheory.BigOn.Exp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatExistsAtCore
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefFlat
theorem flatExistsAt_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → FlatExistsAt (p.T.U ((i : ℕ) + 1)) (xiR D) (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  obtain ⟨hDC, -, -, -⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A M hR hi hG hW hH hF
  intro Z τ
  refine ⟨GlobalTheory.FlatLine.Definite.nonempty_flatSec _ _ hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ, fun s => ?_⟩
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component _ _ _ _ _ _ _ _ _ hDC Z
  have h1 := (GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s
  have h2 := _root_.GlobalTheory.T.degLie_eq_neg_flatDegVal_at_last_index p i PP A M hR hi hG hW hH hF Z P τ
  rw [neg_neg]
  linarith
end GlobalTheory.DefFlat
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobMatchRho
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem frobMatch_rhoS_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π C.isEta.unitary.inv) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (D.ntw.rhoS i s)
      (-((D.R.t : ℝ) / 2) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  obtain ⟨h1, h2⟩ := twBy_unr S C.isEta.unitary.inv (h.unr_of_notMem hP) (C.isEta.unr P).inv
  refine (h.charpoly_frob ha (fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) hB hg).trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv, Units.val_inv_eq_inv_val]
  congr 2
  rw [mul_inv]
  ring
end Triple
end GlobalTheory.TripleLocal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobMatchT
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem frobMatch_Tgl_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hχ : IsChars C art ρ) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (Tgl i s)
      (((D.R.r : ℝ) / 2 + -((D.R.t : ℝ) / 2)) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  have hk : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)
  have hμ := mu_unr C (jIdx s) hk fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  obtain ⟨h1, h2⟩ := twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv
  obtain ⟨n, hn⟩ := hχ.chiS
  have h3 := hn.frob ha (Or.inl hl) (fun x hx => by
    rw [blockChar, GlobalTheory.GalChar.block_loc (C.isEta.unr P) hx]; exact hμ x hx) hB hg
  have h4 := h.charpoly_frob ha hl hk hB hg
  rw [← Matrix.charpoly_map] at h4
  have h5 : (Tmat i s g).map ρ.toC = (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) •
      ((D.ntw.rhoS i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map ρ.toC := by
    ext x y
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_units_inv]
    rw [ρ.toC_apply ((chiS i s g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), h3, inv_inv]
  have h6 := charpoly_smul_of_prod _ (((D.naut.frobEig (D.naut.locG π P)).map fun a =>
    a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹))
    (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) (by rw [h4, Multiset.map_map]; rfl)
  rw [← h5, Matrix.charpoly_map] at h6
  rw [Tgl_coe]
  refine h6.trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, blockChar_val, cpow_add_real, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv,
    Units.val_inv_eq_inv_val]
  congr 2
  have := (C.eta.val P).ne_zero
  have := cpow_ne_zero' P (((D.R.t : ℝ) / 2 : ℝ) : ℂ)
  field_simp
end Triple
end GlobalTheory.TripleLocal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightOfSteps
section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
end Point
theorem height_of_meanAll_bound : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovHt.ShortAlt → _root_.GlobalTheory.CovHt.GeometricCondition → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Y.d.l₂.M'.primeFactors.card ≤ 15 → MeanAll Y.U (xiR D) (ell D) C) →
    _root_.GlobalTheory.CovTop.HeightCondition := by
  intro hPX hP hDG hSz hDg hSh hGe hMu hBu hDS
  obtain ⟨C0, h0, hDS⟩ := hDS
  refine Closed.imp ((((((hDG.and hSz).and hDg).and hSh).and hGe).and hMu).and hBu) ?_
  intro eps Fm CH _ hF
  obtain ⟨⟨⟨⟨⟨⟨⟨C1, -, a1⟩, ⟨C2, -, a2⟩⟩, ⟨C3, -, a3⟩⟩, ⟨C4, c4, a4⟩⟩, ⟨C5, -, a5⟩⟩, ⟨C6, c6, a6⟩⟩, ⟨C7, c7, a7⟩⟩ := hF
  refine ⟨C4 + C6 + C7 + C0 * C7, by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((((((a1.and a2).and a3).and a4).and a5).and a6).and a7)
  refine ⟨x0, fun x hx hle ι p hp i hm Y hY u1 hq => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hall x hx hle ι p hp
  have hDGa := b1 i hm Y hY
  obtain ⟨hb1, hbE, -, -, -, -, hρ⟩ := b2 i
  have hU : 0 ≤ unitE p := by linarith
  have hρ1 : rhoB (dat p i) u1 < 1 := ((hρ hm).2 u1 hq).2.2.1
  have hBu := b7 i hm Y hY u1 hq
  exact _root_.GlobalTheory.CovHt.HtTopG.heightAt_eq_of_cover hPX hP hY.1 (_root_.GlobalTheory.CovHt.cover_height_comparison hP _ _ _ _ _ _) h0 c4 c6 c7 hU
    (hDS _ p.T p.fw.laws (Formalism.BasicNotions.ParameterChoice'.m_sq_le_k (Fm.params x hx ι)) ((i : ℕ) + 1) (by omega) hm Y _ _ hY.1 hBu.1) hDGa.2.2.2.2.2.2.1 hρ1
    (b3 i hm Y hY u1 hq) (b4 i hm Y hY u1 hq) (b5 i hm Y hY u1 hq) (b6 i hm Y hY u1 hq) hBu
end GlobalTheory.CovHt.HtTopG
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkOfBuilt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.JoinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}
variable {G : Type} [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw}
  {YS : NExpRealS R cG S} {cf : CharFrame D}
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
variable {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
def twistInputsOfBaseTuples {hH hV hs} (Y : SerSide (realOf t hH hV hs) (twEOf xd))
    (hS : Y.S = ratDatR t.r.z.R t.r.z.cG c.row.kKs c.row.hk) (hY : HEq Y.YS c.row.nexp) (g : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7)
    (h1 : g.cf = TC.cf w.I w.l Z) (h2 : g.lam.C = TC.cf w.I w.l Z) (hF : FieldOk (realOf t hH hV hs))
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (w.st Z).toD7 g.wd)
    (hb : T = TwDat.untw B T.pl → ∀ v, (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 → BaseTup Y (nch.twI v)) :
    _root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c :=
  ⟨realOf t hH hV hs, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, Y, hS, hY, g,
    h1, h2, t.r.z.lev.C, hF, cg, hb⟩
def heckeSeriesOfRealHeight {hH hV hs} (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
    (H : NExpRealH t.r.z.R t.r.z.cG _ c.row.nexp) (hr : GlobalTheory.ExportPin.Reads t.r.z.R t.r.z.cG _ c.row.nexp H.hL)
    (hd : ∀ i b P, P ∉ (w.D Z).ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G (w.D Z).host.E (w.D Z).nd.Om,
      Formalism.ConjugateSelfDual.IsFrob (F := (w.D Z).host.E) ((w.D Z).nd.plOm.1 P) (Formalism.ConjugateSelfDual.normV P) σ →
      H.cHk i b 1 P = algebraMap ((w.D Z).ntw.O i) (FractionRing ((w.D Z).ntw.O i)) (algebraMap ((w.D Z).ntw.O0 i) ((w.D Z).ntw.O i)
        ((if b then (w.D Z).ntw.delta i σ else ((w.D Z).ntw.delta i σ)⁻¹ : ((w.D Z).ntw.O0 i)ˣ) : (w.D Z).ntw.O0 i)))
    (hk_emb : ∀ i j b k P (x : (w.D Z).ntw.B i j b), 1 ≤ j → j ≤ B.R.m → IntegralHeckeForms.HkIdx i k P →
      (w.D Z).nexp.embB i j b ((w.D Z).ntw.hk i j b k P x) = (w.D Z).nexp.hkF i j b k P ((w.D Z).nexp.embB i j b x))
    (hz : ∀ i (s : (w.D Z).ntw.Sig i) P, (w.D Z).ntw.hEig i s 0 P = 1) : SerSide (realOf t hH hV hs) (twEOf xd) where
  S := _
  YS := c.row.nexp
  sup := e.ser.sup
  H := H
  reads := hr
  del := hd
  Z := e.ser.ex
  U_eq g := (c.row.grp.lvl0 g).symm
  psi_eq := psi_of_grp c.row.grp e.ser.ex
  low := low_of_tied c.a.all.tw (q_dvd_discr _)
  Sb i P hP := by
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.D Z).ntw.placesOver_subset_exceptional i k hk
  B_range i _ j _ b := c.a.all.tw.B_range i j b
  hk_emb := hk_emb
  hk_split i _ j _ b k P h := by
    obtain ⟨s, hs⟩ := c.a.all.tw.hk_split i j b k P h.2.2.2
    exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
      exact Polynomial.Splits.X_sub_C a
  off i _ := ⟨fun j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), hz i⟩
  all i j hj b a := by
    have := e.xd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    change a ∈ xd.xd0 i j b
    rw [this]; trivial
theorem exists_wdTie_cgTrue_labTrue_of_built {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) :
    ∃ wd : GlobalTheory.RowTie.WDTie D.nd D.naut, Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D wd) ∧ LabTrue D wd := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨{ A.wdT with }, ⟨{ cg with }⟩, A.lab⟩
theorem exists_galSide_of_rank_ge_hundred (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) (h3 : _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z)) (hr : 100 ≤ B.R.r)
    (hg : ∀ k, 2 * B.R.r ≤ B.host.g k) : ∃ g : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, g.cf = TC.cf w.I w.l Z ∧ g.lam.C = TC.cf w.I w.l Z ∧
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL (w.st Z).toD7 g.wd) := by
  obtain ⟨wd, cg, lab⟩ := _root_.GlobalTheory.TwInputs.JoinModel.exists_wdTie_cgTrue_labTrue_of_built c.a.nt.toNBuilt
  exact ⟨⟨wd, lab, TC.cf w.I w.l Z, { c.a.chrN with }, h3, e.ser.lam, e.ser.lam_ok, fun i hi => (e.ser.lam_tie i hi).imp id (Exists.imp fun _ h => ⟨h.1, h.2.1⟩), hr, hg⟩, rfl, e.ser.lam_C, cg⟩
theorem embB_hk_commute_and_hEig_zero_of_built {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) :
    (∀ i j s k P (x : D.ntw.B i j s), 1 ≤ j → j ≤ D.R.m → IntegralHeckeForms.HkIdx i k P →
      D.nexp.embB i j s (D.ntw.hk i j s k P x) = D.nexp.hkF i j s k P (D.nexp.embB i j s x)) ∧
    ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1 := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨fun i j s k P x h1 h2 h => Bs.hk_emb i j s k P x h1 h2 h.2.2.2 h.2.2.1 h.2.1, Bs.hEig_zero⟩
end Rows
end GlobalTheory.TwInputs.JoinModel
end
end
end


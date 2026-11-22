import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0191
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0198
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0998
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0152
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0196
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0003
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0993
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0199
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodRef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocRecUnrFrobEigLe
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands
theorem reciprocity_unramified_and_norm_frobenius_eigenvalue_le (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {n : ℕ} (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (hs : GlobalTheory.SmGL.IsSpherical σ.ρ)
    (hu : GlobalTheory.SmGL.IsUnitarisable σ.ρ) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr ∧
      ∀ α ∈ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).frobEig, ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have H := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have hunr : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H σ).2 hs
  refine ⟨hunr, ?_⟩
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hunr
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  have h1 := GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake E w n (GlobalTheory.SplitRead.Irr.ofIrrRep σ) α hα hu
  have h2 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n
      ((Finset.univ.val.map fun i => (α i : ℂ)).map (·⁻¹)) := by
    have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv _ _ _ _ h1
  intro b hb
  apply h2.norm_le
  simpa [Multiset.map_map, Function.comp_def] using hb
end GlobalTheory.RowSphSmall
section FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalConjExpansionAtPlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)
theorem GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  intro _ D X X0 Y S YS Z c w j _ τ _ ζ Φ Φ' hC n a f hΦ
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) X.geo.fw
  have hso : (X.geo.O j).s0 = res X.core (sg0 _ X.A3.A) :=
    (sOv_eq X.core.toCore (X.geo.O j).c' (X.geo.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.PlaceRead.evaluates_of_lunif X.geo.fw X.unif j (sg0 _ X.A3.A) hb.2.1 hb.2.2
  let cf : NX.FmK S ((j : ℕ) + 1) → X.core.cuspA ((j : ℕ) + 1) (wtA (X.geo.κ j)) (X.geo.κ j).n := fun g =>
    (X.geo.fw.e j).symm ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩
  have hread : ∀ (g : NX.FmK S ((j : ℕ) + 1)) h,
      (lieFac (X.core.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (X.geo.κ j)) : ℂ) *
      (X.geo.O j).phi (X.core.cE ((j : ℕ) + 1) (X.geo.O j).s0) (cf g : X.core.R ((j : ℕ) + 1)) h =
        evW YS X.geo.v₀ j g.val h := by
    intro g h
    rw [phi_cE X.core X.R.toRealDat X.geo.O j]
    refine Eq.trans ?_ ((congrFun (hev (cf g)) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr X.core hso (X.geo.O j).hV hb.2.2 _ _) h
    · have he : X.geo.fw.e j (cf g) = ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩ := LinearEquiv.apply_symm_apply _ _
      exact congrArg (fun x : (X.R.FW j).WK => (X.R.HW j (sg0 D X.A3.A)).e ((X.R.FW j).j (sg0 D X.A3.A) x.val)
        (X.geo.v₀ j (sg0 D X.A3.A)) h) he
  have h1 : Expands (X.geo.O j) (X.geo.κ j) Φ a fun k => cf (f k) := fun h => by
    rw [hΦ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (hread _ _).symm
  have h2 := hC.2 n a _ h1
  funext h
  rw [h2 h, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact (congrArg (fun z => ζ * τ (a k) * z) (hread (f k) h)).trans (mul_assoc _ _ _)
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_conj_expansion_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  first | exact @_root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | exact _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | (intros; apply _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalFixedPointAtPlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceFix
theorem fixed_at_place_of_local_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → FixBase X.core X.R.toRealDat j τ ∧ FixDat (baseOf Z c w j) τ := by
  intro hP D X X0 Y S YS Z c w j H τ hτ
  have hC := X.char
  have hτ' : ∀ z ∈ (embLL0 D).fieldRange, τ z = z := by
    rintro _ ⟨y, rfl⟩
    exact hτ y
  have hTie : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have hFB : FixBase X.core X.R.toRealDat j τ :=
    GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hP.rayF X.core X.R X.cG S YS X.F.lv2 X.geo.κ X.geo.v₀ X.geo.fw.laws
      ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ ⟨X.geo.fw⟩ hTie H.field.galois
      H.field.vals H.field.ray H.field.roots j τ hτ'
  refine ⟨hFB, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := de_chi_eq Z.good (c.twI w) j (c.sd w) y
    change τ (((Z.ρ.B _ j _).de.chi y : Circle) : ℂ) = _
    rw [hσ]
    refine GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values Z.ρ Z.good _ j _ (X.R.C.delAt (D.ntw.l (c.twI w))) (Z.pin.delta _ j _) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [H.field.vals.del', H.field.vals.del]
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective q
    obtain ⟨g, rfl⟩ := (X.R.eG.trans X.cG).surjective y
    have hU : X.cG (X.R.eG g) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 hq
    have hg : g ∈ X.F.P0 := (H.U_eq g).1 hU
    have e1 := (Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hU⟩ hq
    have e2 := H.psi_eq (c.twI w) (c.sd w) ⟨g, hg⟩ hU
    obtain ⟨y, hy⟩ := H.pins.keep.levKs.1 ⟨g, hg⟩
    have e3 := e1.trans e2
    change τ ((((Z.ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _
    have e4 : D.what₂.embLL (X.F.ψ0 ⟨g, hg⟩ : D.what₂.LLˣ) = embLL0 D (S.kKs ((YS.fi j).eK.symm y)) := by
      change _ = D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm y) : ↥D.LL0) : D.what₂.LL)
      rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
      exact congrArg _ hy.symm
    rw [e4] at e3
    refine (congrArg τ e3).trans (Eq.trans ?_ e3.symm)
    rw [map_inv₀, hτ]
  · exact (GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC.lev Z.good Z.pin _ j _).fix_mu hC.lev (Z.good.base _ j _) hFB.chi
end GlobalTheory.PlaceFix
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fixed_point_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → FixBase X.core X.R.toRealDat j τ ∧ FixDat (baseOf Z c w j) τ := by
  first | exact @_root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt | exact _root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt | (intros; apply _root_.GlobalTheory.PlaceFix.fixed_at_place_of_local_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGaloisPsiLevelAtPlace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.GalLoc.PsiLvl
theorem localGalois_psi_level_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := by
  intro _ _ hL
  refine _root_.GlobalTheory.GalLoc.PsiLvl.atMem_of_forall' fun K B f T w Z Wt p0 t nch n c => ?_
  obtain ⟨θ, hθ, hR⟩ := exists_theta_of_eq c.a.nt.eq c.a.nt.θ (_root_.GlobalTheory.GalLoc.PsiLvl.psiRead_withLoc_alt c.a.nt.toNBuilt)
  refine ⟨θ, hθ, fun g => ?_, fun u hu => ?_⟩
  · exact (c.row.grp.lvl0 g).trans (SetLike.ext_iff.mp c.a.all.exp.U_eq _)
  · have hu0 : (t.r.z.R.eG.trans t.r.z.cG) u ∈ (w.D Z).nexp.U := (c.row.grp.lvl0 u).1 u.2
    obtain ⟨i⟩ : Nonempty (w.D Z).ntw.Tw := by
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 (w.D Z).what₂.LL)
      exact ⟨nch.twI ((w.D Z).plEq.symm
        ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩)⟩
    obtain ⟨x, hx, hx'⟩ := c.row.grp.psi0 u hu0 i true
    have h2 := hR i _ hu0 hu
    have h3 : IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i) ((w.D Z).ntw.emb0 i x) =
        IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i) ((w.D Z).ntw.emb0 i
          ((psiUOf (w.D Z).nd (NX.xiRed (w.D Z)) θ ⟨(t.r.z.R.eG.trans t.r.z.cG) u, hu⟩ : (↥(w.D Z).LL0)ˣ) : ↥(w.D Z).LL0)) :=
      hx'.symm.trans h2
    have h4 := (IsFractionRing.map (A := (w.D Z).ntw.O0 i) (B := (w.D Z).ntw.O i) (K := FractionRing ((w.D Z).ntw.O0 i))
          (L := FractionRing ((w.D Z).ntw.O i)) ((w.D Z).ntw.O_inj i)).injective h3
    have h5 := ((w.D Z).ntw.emb0 i).injective h4
    exact (congrArg (fun z : ↥(w.D Z).LL0 => (z : (w.D Z).what₂.LL)) h5).symm.trans hx
end GlobalTheory.GalLoc.PsiLvl
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_heq_lvlPsi_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := by
  first | exact @_root_.GlobalTheory.GalLoc.PsiLvl.localGalois_psi_level_at_place_alt | exact _root_.GlobalTheory.GalLoc.PsiLvl.localGalois_psi_level_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.PsiLvl.localGalois_psi_level_at_place_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalAboveEllOfCusp
section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.GalOfCusp
theorem local_global_above_ell_of_cusp_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → _root_.UpperTheory.GalS.CarUAlt :=
  fun H => H.car.regAlg H.clo
end GlobalTheory.GalOfCusp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerLeftValuationEqZeroAllStages
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem lowerLeftValuation_eq_zero_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  exact valLL0_colW w x.o.Z
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valLL0_cfOf_at_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MArtinTr
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
theorem GlobalTheory.LocLanglands.artin_transport_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  intro hL E Ω _ _ _ _ _ A A' w w' h h' c j i hcA hcj hi hij a ha ε H a' ha' ε' H' ξ hξ σ σ' hσ
  set iU : (w.adicCompletion E)ˣ →* (w'.adicCompletion E)ˣ := Units.map i.toRingHom.toMonoidHom with hiU
  have hcont : Continuous iU := Units.continuous_map hi
  have hs : IsSmoothChar (ξ.comp iU) := hξ.comp iU hcont
  obtain ⟨b, b', hb, hb', -, hρ⟩ := _root_.UpperTheory.One.M.New.field hL
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h') c j i hcA hcj hi hij 1
    (IrrRep.det (Fin 1) (ξ.comp iU) hs) (IrrRep.det (Fin 1) ξ hξ) (LinearEquiv.refl ℂ ℂ) (by
      intro g v
      have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g) =
          iU (Matrix.GeneralLinearGroup.det g) := by
        ext
        simp [hiU, RingHom.map_det]
      show (LinearEquiv.refl ℂ ℂ) ((ξ.comp iU (Matrix.GeneralLinearGroup.det g) : ℂ) • v) = _
      show _ = ((ξ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g)) : ℂ) • v)
      rw [hd]
      rfl) (UpperTheory.One.M.good_ofChar _ hs)
  have e1 : WD.mk b = WD.lpOfChar h ((ξ.comp iU).comp a) (ha.smooth hs) := hb.trans (H.one _ hs)
  have e2 : WD.mk b' = WD.lpOfChar h' (ξ.comp a') (ha'.smooth hξ) := hb'.trans (H'.one _ hξ)
  have k := congrFun (congrArg (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1)) (hρ σ σ' hσ)) 0
  simp only [b.rho_apply_of_mk_eq_lpOfChar _ _ e1, b'.rho_apply_of_mk_eq_lpOfChar _ _ e2] at k
  simp at k
  exact Units.ext (by simpa [hiU] using k)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.One.M.good_cls_of_isLocS_av {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (s : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) s σ) : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ) :=
  GlobalTheory.AVGood.members_good UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz D P.M P.tp.tup P.H.av P.H.level
    (GlobalTheory.AVGood.tameAtG_of_tupTied D P.cf P.tp) i Q s σ hσ
theorem UpperTheory.One.M.cls_eq_of_locV_eq' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E)
    (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' :=
  _root_.UpperTheory.One.M.local_component_class_eq_of_good hL D P i Q Q' sp σ σ' hσ hσ' he (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i Q' sp σ' hσ')
end
section
namespace GlobalTheory.ConjPlaceDual
end GlobalTheory.ConjPlaceDual
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MBlockParamH
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.One.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.SplitRead.BlockParam GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne (WD Weil ineIncl)
section Local
variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
theorem charPol_unr_twist' {rc : ∀ n, Irr k n → WD h} (hrc : _root_.UpperTheory.One.M.RecLawsH rc) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (σ : Ine (F := E) B) (c : ℂ) (hc : (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C c)
    (n : ℕ) (π : Irr k n) (hn : n = 1) (α : ℂˣ)
    (e : Nonempty (π.π.Equiv (detRep (Fin n) (χ * unrChar k α)))) :
    (rc n π).charPol (ineIncl h σ) = X - C c := by
  subst hn
  let u : Irr k 1 := detIrr 1 (unrChar k α) (isSmoothChar_of_isUnram (isUnram_unrChar k α))
  have he : detRep (Fin 1) (χ * unrChar k α) = twist u.π (detChar (Fin 1) χ) := by
    show _ = twist (detRep (Fin 1) (unrChar k α)) (detChar (Fin 1) χ)
    unfold detRep ofChar
    rw [twist_twist]
    rfl
  have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc 1 χ (detIrr 1 χ hχ) u π (good_of_one _ rfl) ⟨.refl _⟩ (he ▸ e)
  rw [h1, charPol_lpChar_of_unr _ _ ((hrc.sph 1 u).2 (isSpherical_detRep (isUnram_unrChar k α))) σ c hc,
    hrc.dim, pow_one]
theorem split_local_of_blockVec {rc : ∀ n, Irr k n → WD h} (hB : BlockSplit k) (hrc : _root_.UpperTheory.One.M.RecLawsH rc) (hs : RecSupp rc)
    {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (ht : IsTame χ) (π : Irr k (r + t)) (v : π.V) (hv : v ≠ 0)
    (hvb : IsBlockVec χ π.π v) (c : Ine (F := E) B → ℂ)
    (hc : ∀ σ, (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C (c σ)) (γ : Ine (F := E) B)
    (hm : ((rc _ π).charPol (ineIncl h γ)).rootMultiplicity (c γ) ≤ t) :
    ∃ a b : WD h, rc _ π = a.lpSum b ∧ a.lpDim = r ∧ b.lpDim = t ∧ b.mono0 ∧
      ∀ σ, b.charPol (ineIncl h σ) = (X - C (c σ)) ^ t := by
  classical
  rcases hB r t χ π v hχ ht hv hvb with ⟨π₁, π₂, hsph, e⟩ | ⟨s, d, σ, hsupp, hcard⟩
  · have hg : GoodI π₂ := GlobalTheory.AVGood.good_of_isSpherical GlobalTheory.T.bernstein_zelevinsky_finiteness _
      (fixed_ne_bot_of_equiv (equivRep ⟨π₂.V, π₂.π, π₂.smooth, π₂.irr⟩) hsph)
    have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc t χ (detIrr 1 χ hχ) π₂ (twistIrr π₂ χ hχ) hg ⟨.refl _⟩ ⟨.refl _⟩
    have hu := (hrc.sph t π₂).2 hsph
    refine ⟨rc r π₁, rc t (twistIrr π₂ χ hχ), hrc.prod r t π₁ _ π e, hrc.dim _ _, hrc.dim _ _, ?_, fun σ => ?_⟩
    · rw [h1, WD.monomial_char_iff _ _ (hrc.dim _ _)]
      exact WD.unr_mono0 _ hu
    · rw [h1, charPol_lpChar_of_unr _ _ hu σ _ (hc σ), hrc.dim]
  · exfalso
    set U := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} with hU
    have hdvd : (X - C (c γ)) ^ U.toFinset.card ∣ (rc _ π).charPol (ineIncl h γ) := by
      rw [hs _ s π d σ hsupp, ← Finset.prod_const]
      refine dvd_trans (dvd_of_eq (Finset.prod_congr rfl fun a ha => ?_))
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ U.toFinset))
      obtain ⟨h1, α, e⟩ := Set.mem_toFinset.1 ha
      exact (_root_.UpperTheory.One.M.charPol_unr_twist' hrc hχ γ _ (hc γ) _ _ h1 α e).symm
    have := (le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero).2 hdvd
    rw [Set.ncard_eq_toFinset_card'] at hcard
    omega
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem split_param_of_typeBlock : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), BlockSplitAll H.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → TypeBlock S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t → ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hB hL hS hT hchi P hm
  haveI : CharZero (w.adicCompletion H.E) := charZero_compl w
  obtain ⟨v, hv, hvb⟩ := hT.2 P
  have hμ := (S i w hw).mu_ok.1
  rw [T.inePol w _ _ (N.locNd_chebotarevPlace_mem i w), (S i w hw).locV, WD.inePol_of_mem_Ine _ (N.locNd_chebotarevPlace_mem i w)] at hm
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := _root_.UpperTheory.One.M.split_local_of_blockVec (hB w) (hL i w hw) (hS i w hw) hμ hT.1 _ v hv hvb
    (fun σ => iotaO N A i (chi1 N i σ.1)) (fun σ => by
      rw [← hchi σ.1 σ.2, T.inePol w _ _ σ.2, (S i w hw).locMu (detIrr 1 _ hμ) ⟨.refl _⟩,
        WD.inePol_of_mem_Ine _ σ.2]) ⟨_, N.locNd_chebotarevPlace_mem i w⟩ hm
  obtain ⟨a, rfl⟩ := (T.e w).surjective a
  obtain ⟨b, rfl⟩ := (T.e w).surjective b
  refine ⟨a, b, (T.e w).injective ?_, ?_, ?_, (T.mono0 w b).2 h4, fun σ hσ => ?_⟩
  · rw [(S i w hw).locV, h1, T.sum]
  · rw [← T.dim, h2]
  · rw [← T.dim, h3]
  · rw [T.inePol w _ _ hσ, WD.inePol_of_mem_Ine _ hσ, h5]
end UpperTheory.One.M
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M.B
end UpperTheory.One.M.B
open UpperTheory.One.M.B in
theorem UpperTheory.One.M.goodRef_alt :
    _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → UpperTheory.One.M.GoodAU (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS) := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine GlobalTheory.LiftRef.overRows_and_mono levSplit levSplit (fun K B f T w Z Wt hX z p0 Y h' _ => ?_)
  intro Rw a M tup Q hMA _ j h1 h2 S hS hne s σ hσ
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f', hf', hf0', hff'⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧ TrivOutside {s.v} κ ∧ (s.v ∈ gPl (w.st Z).toD7 → IsPrincipalCongruenceAt s κ)} hy hry
    (fun κ hκ => GlobalTheory.SphInertRef.rt_real_eq_of_lev hMA i y κ (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).1
      (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).2)
  exact good_of_fix _ S hS s (fun hg => GlobalTheory.SplitTypeCompl.exists_padic_equiv _ s hg) f' hf' hf0'
    (fun κ a b c => hff' κ ⟨a, b, c⟩) σ hσ
end
end
end


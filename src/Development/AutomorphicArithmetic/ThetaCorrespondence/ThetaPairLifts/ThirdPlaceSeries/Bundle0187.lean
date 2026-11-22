import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0025
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0130
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1022
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0171
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0175
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0176
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0186

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNonzeroSectionWeightBound
section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSteep
section Tau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end Tau
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
end Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_theta_section_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  intro h1 h2 h3 h4
  refine (((_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 h1 h2 h3 h4).and h4).and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C, hC, x0, hx0⟩, ⟨C₁, -, x1, hx1⟩⟩, ⟨C₂, -, x2, hx2⟩⟩ := h
  refine ⟨C, hC, max x0 (max x1 x2), fun x hx hle ι p hp i hi Y hY Z TF => ?_⟩
  have l0 : x0 ≤ x := (le_max_left _ _).trans hle
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hdeg := hx0 x hx l0 ι p hp i hi Y hY Z TF
  have hfl := hx1 x hx l1 ι p hp i hi Y hY
  have hnum := hx2 x hx l2 ι p hp i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact Dvd.dvd.mul_left ((pow_dvd_pow_of_dvd (by norm_num) 4).trans (pow_dvd_pow 15 (four_le_expL hnum.big.2.1))) _
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have := hnum.f8
    have := hnum.deg
    omega
  obtain ⟨θ, hθ, hb⟩ := _root_.GlobalTheory.ThetaSteep.exists_section_of_theta_datum Z h1 hL hM TF (fun τ => (hfl Z τ).1.some) hdeg
  exact ⟨θ, hθ, fun la _ f hf' => vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF la
    (mul_mem_vanBd TF.X Z _ θ ((GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _).space_le hf')),
    fun y _ ν hν φ hφ j hj m hm => hb y ν hν φ hφ j hj m hm⟩
end GlobalTheory.ThetaSteep
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
theorem _root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))) ⊤, θ ≠ 0 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ f ∈ space TF.X Z Y.U (la - ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))), ((common₀ TF.X Z).addChart (add_sub_cancel ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i)) la)).mul θ f ∈ space TF.X Z Y.U la) ∧ ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ (j : (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).ι) (hj : y ∈ (L₀ TF.X Z ((8 * (((dat p i).p + (dat p i).q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt (dat p i))).U j) (m : ℤ), ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → 8 * φ / 625 ≤ (m : ℝ) := by
  first | exact @_root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt | exact _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt | (intros; apply _root_.GlobalTheory.ThetaSteep.exists_theta_section_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonemptyTwOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {D : D7}
theorem exists_frob_unit_and_hkF_zero_eq_of_built {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) (h0 : ∀ j P, b.hL j 0 P = 1) :
    (∃ u, IsFrobUnit D u) ∧
      ∀ i j s P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j s 0 P x = x := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  have h := hkF_zero_of_sideB (D := D0) Bs h0
  exact ⟨⟨Bs.cHk, Bs.cHk_del⟩, fun i j s P x => h i j s P x⟩
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
theorem nonempty_twOf_of_hecke_stable_reads {hH hV hs} (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) (hF : FieldOk (realOf t hH hV hs))
    (hG : ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = TC.cf w.I w.l Z ∧ G.lam.C = TC.cf w.I w.l Z ∧ Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd))
    (hR : ∀ (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S),
      ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
        (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL) :
    Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  obtain ⟨g, h1, h2, ⟨cg⟩⟩ := hG
  obtain ⟨k1, k2⟩ := _root_.GlobalTheory.TwInputs.JoinModel.embB_hk_commute_and_hEig_zero_of_built c.a.nt.toNBuilt
  obtain ⟨⟨u, hu⟩, hz⟩ := _root_.GlobalTheory.TwInputs.AtLayer.exists_frob_unit_and_hkF_zero_eq_of_built c.a.nt.toNBuilt (c.a.ratIn_hL ▸ c.a.ratIn.hL_zero)
  obtain ⟨f', s1, s2, s3⟩ := hR _ (realOf t hH hV hs) _ c.row.nexp
  obtain ⟨H, r1, r2⟩ := exists_hecke (realOf t hH hV hs) _ c.row.nexp e.ser.ex f' s1 s2 s3 u hu hz
  exact ⟨_root_.GlobalTheory.TwInputs.JoinModel.twistInputsOfBaseTuples (_root_.GlobalTheory.TwInputs.JoinModel.heckeSeriesOfRealHeight e H r1 r2 k1 k2) rfl HEq.rfl g h1 h2 hF cg fun hT v hv => base_of_untw _ hT v hv⟩
end Rows
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
end GlobalTheory.TwInputs.AtLayer
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadTwWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem readTw_withLoc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (a : (withLoc b.L).nd.Loc) :
    ReadTw (withLoc b.L) a := by
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  refine ⟨(castQ hpq).symm.toRingHom.comp (((withLoc b.L).naut.iotaQ a).comp
      (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))),
    (castQ hpq).trans ((withLoc b.L).naut.iotaQC a), ?_, ?_, ?_⟩
  · intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  · intro x
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
        ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
        (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
      fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
        (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  · intro y
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y))))) = _
    rw [RingEquiv.apply_symm_apply, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    rfl
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sideB_built_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (ψ : D'.nd.Loc → NC.HC D'.host.E) (hψ : ∀ a, NC.ReadC D'.nd.plOm.1 (D'.ntw.psiL a) (NC.iotaC D' a) (ψ a) 0)
    (cf : CharFrame D') (hcf : HEq cf (cfL b.L b.cf))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host) (hPq : HEq Pq b.Pq)
    (S : RatDat D'.ntw) (hS : HEq S (ratL b.L b.S))
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S.WL j)) (hhL : HEq hL' b.hL)
    (eig : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (heig : HEq eig b.eig)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq θ b.θ) :
    ∃ Rw : RowSide D', HEq Rw.locR b.A.row.locR ∧ Nonempty (SideB D' cf Rw b.low Pq S hL' eig θ) ∧
      (∀ a σ v, IsSplitPl D'.host v → D'.naut.locW a σ v = Rw.locR σ v) := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hcf
  obtain rfl := eq_of_heq hPq
  obtain rfl := eq_of_heq hS
  obtain rfl : hL0 = hL' := (eq_of_heq hhL).symm
  obtain rfl : eig0 = eig := (eq_of_heq heig).symm
  obtain rfl : θ0 = θ := (eq_of_heq hθ).symm
  obtain ⟨Rw, hRw, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf0 A.row low Pq S0 hL0 eig0 θ0 Bs L ψ hψ
  refine ⟨Rw, hRw, ⟨Bs'⟩, fun a σ v _ => ?_⟩
  have e : Rw.locR = A.row.locR := eq_of_heq hRw
  rw [e]
  exact Au.locW a σ v
set_option maxHeartbeats 4000000 in
theorem isKsForm_of_built_heq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (S : RatDat D'.ntw)
    (hS : HEq (ratL b.L b.S) S) (h : ∀ j, 1 ≤ j → j ≤ b.D.R.m → (b.S.A j).IsKsForm) :
    ∀ j, 1 ≤ j → j ≤ D'.R.m → (S.A j).IsKsForm := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hS
  exact h
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
end GlobalTheory.RowTriple.Lay
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfStepsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.ConjugateTwist := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints | exact _root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints <;> assumption)
end
end


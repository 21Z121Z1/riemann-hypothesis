import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0080
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0204
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0217
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0205
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0155
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0208
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0215
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1011
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0219
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0207
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0202
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0196
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0209
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0548
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0218
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0214

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalComponentAtPlaceDetermined
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
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceRead
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}
end GlobalTheory.PlaceRead
namespace GlobalTheory.PlaceRead
variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} {Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0} {S : NX.RatDat D.ntw}
  {YS : NX.NExpRealS X.R X.cG S} {Z : ExportTie YS X.geo.v₀} {c : NChoice D} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem exists_local_component_at_place_alt (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (H : AtPlace Y Z c w j) {ε : KE c w →+* ℂ} (hε : Extends Z.ρ ε) :
    ∃ (Ψ : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[ε.comp (c.embW w)] Amb D j) (N : ℕ) (z₁ : ℂ),
      (∀ (I : Type) (b : I → D.what₂.MtL (D.what₂.muTw w) (j.1 + 1)),
        LinearIndependent ℂ (fun k => D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (b k)) → LinearIndependent ℂ fun k => Ψ (b k)) ∧
      ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia Z.ρ ε) : Set (Amb D j)) =
        Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)) ∧
      IsUnit (N : c.Oe w) ∧ UnitOff N z₁ ∧
      ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
        (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
          Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
        (baseOf Z c w j).classSum (Z.ρ.om (c.twI w) j (c.sd w) (twVia Z.ρ ε).chi) (twVia Z.ρ ε)
          (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) (Ψ x) =
          z₁ • (Z.ν (c.twI w) j (c.sd w))⁻¹ • ∑ k, ε (c.embW w (a k)) • evW YS X.geo.v₀ j (f k).val := by
  obtain ⟨τ, hτ0⟩ := GlobalTheory.BigOn.Exp.TwConj.exists_aut_on D.what₂.embLL (ε.comp (c.embW w))
    (GlobalTheory.BigOn.Exp.TwConj.countable_alg D.what₂.embLL)
  have hτ : ∀ x, τ (D.what₂.embLL x) = ε (c.embW w x) := fun x =>
    hτ0 x ((Algebra.IsAlgebraic.isAlgebraic x).algHom D.what₂.embLL.toRatAlgHom)
  have hfix : ∀ a, τ (embLL0 D a) = embLL0 D a := fun a => (hτ a).trans (H.emb ε hε a)
  obtain ⟨ι, hιε⟩ : ∃ ι : KE c w →+* ℂ, (τ : ℂ →+* ℂ).comp ι = ε :=
    ⟨(τ.symm : ℂ →+* ℂ).comp ε, RingHom.ext fun y => τ.apply_symm_apply _⟩
  have hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x := fun x => τ.injective ((RingHom.congr_fun hιε _).trans (hτ x).symm)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo : BaseOf X.R.toRealDat j (baseOf Z c w j) :=
    GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, hcc⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  obtain ⟨hg', ha', -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ε
  have hcj : ConjChar τ (twVia Z.ρ ι) (twVia Z.ρ ε) := hιε ▸ hcc τ
  obtain ⟨u, cc, κ, hu, hc, hκ, hval, hfn, hs, hν⟩ := GlobalTheory.T.exists_scale_twisted_place_coefficient_map D X X0 Y S YS Z c w j H
  obtain ⟨hfb, hfd⟩ := _root_.GlobalTheory.T.local_fixed_point_of_third_layer hP D X X0 Y S YS Z c w j H τ hfix
  obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist D j _ hB hBo.lam (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ hκ hval hfn τ hfix _ _ hg hg' hcj hfd
  have hω := Z.good.weil (c.twI w) j (c.sd w) _ hg
  have hω' := Z.good.weil (c.twI w) j (c.sd w) _ hg'
  have hcl' := Z.good.classes (c.twI w) j (c.sd w) _ hg' ha'
  have hcl : IsClassSystem (Vc D j) ((baseOf Z c w j).levJ (twVia Z.ρ ι)) (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) := by
    rw [← levJ_congr (baseOf Z c w j) hcj.1]
    exact hcl'
  refine (GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum D X j _ hB hBo _ _ hg ha (H.tup ι hι) _ hω _ _ hcl u).elim fun z hz => hz.elim fun a₀ hz => ?_
  obtain ⟨hz, ha₀, hth⟩ := hz
  refine (GlobalTheory.T.classSums_conjugate_twists_conjugate_expansions D X j _ hB _ _ hg hg' ha (_root_.GlobalTheory.T.exists_local_tuple_of_discrete_series_read hCo hCW hHM hP D X X0 Y S YS Z c w j H ι hι τ hfix _ hg' hcj) u cc κ hu hc hκ τ hfb hfd
    hcj _ _ hω hω').elim fun ζ hζ => ?_
  obtain ⟨hζ, hcs⟩ := hζ
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u hu
  have hmem : ∀ y, fockOf Y (used_of_tw H.tw) j u y ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι) := fun y =>
    hrange.le (LinearMap.mem_range_self _ y)
  have hΦv : ∀ y h, trOf H u κ z y h ∈ (baseOf Z c w j).valSpace := fun y h =>
    Submodule.smul_mem _ κ⁻¹ (((baseOf Z c w j).mem_formsC.1 (hmem y)).1 _)
  have hN := (GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι).2.2
  refine ⟨semiComp τ (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) (trOf H u κ z) C (ε.comp (c.embW w)) hτ, _, _, fun I b hb => ?_, ?_, hN, unitOff_conj τ ha₀ hζ hν, fun x hx n a f hf => ?_⟩
  · exact indep_conj τ (trOf H u κ z) C (fun y hy => trOf_eq_zero H hκ hinj y ((hC1 _ (hΦv y)).2 hy)) hb
  · have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
      rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
    have e2 := hC2 _ (coefficient_ring_of_integral_le (intLL_le hι))
    rw [e1] at e2
    exact span_conj H hι hιε hu hκ hs hz C _ e2
  · have h1 := expansion_eq H hu hκ ha₀.1 _ hx (hth _ (hmem (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) hf
    have h2 := _root_.GlobalTheory.T.local_conj_expansion_of_third_layer hP D X X0 Y S YS Z c w j H τ hfix ζ _ _
      (hcs _ _ hcl'.fin _ _ (hC1 _ (hΦv (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))).1) n _ f h1
    exact rescale_conj τ hκ (Z.scalar (c.twI w) j (c.sd w)).ne (fun k => hτ (a k)) h2
theorem exists_basisAt_latAt_thetaAt_of_atPlace (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (H : AtPlace Y Z c w j) :
    ∃ (e : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[c.embW w] Tgt c w (j.1 + 1)) (u : (FractionRing (c.Oe w))ˣ),
      BasisAt c w (j.1 + 1) e ∧ LatAt c w (j.1 + 1) e (u : FractionRing (c.Oe w)) ∧ ThetaAt Y YS c w j e (u : FractionRing (c.Oe w)) := by
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField D c w Z.ρ Z.good).1
  refine (_root_.GlobalTheory.PlaceRead.exists_local_component_at_place_alt hCo hCW hHM hP H hε).elim fun Ψ h => h.elim fun N h => h.elim fun z₁ h => ?_
  obtain ⟨hind, hlat, hN, hz, hth⟩ := h
  obtain ⟨hinj, hmt⟩ := GlobalTheory.T.definiteFormReading_injective_lattice_integralForms D c w Z.ρ Z.good j _ (Z.tie (c.twI w) j (c.sd w)) ε hε H.ok H.field.roots
  have hsub : ∀ F ∈ Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)), ∃ y ∈ latT c w (j.1 + 1),
      rdE (Z.tie (c.twI w) j (c.sd w)) hε y = F := fun F hF => (hmt F).1 (hlat.ge hF)
  obtain ⟨e, he⟩ := exists_lift (c.embW w) ε _ hinj Ψ (GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)) fun x hx =>
    (hsub _ (Submodule.subset_span ⟨x, hx, rfl⟩)).imp fun _ h => h.2
  have hL : Submodule.span (c.Oe w) (e '' latS w (j.1 + 1)) = latT c w (j.1 + 1) := by
    have h1 := image_span (ε.comp (algebraMap (c.Oe w) (KE c w))) (ringOf ε) rfl
      (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom
      (fun r v => (congrArg _ (algebraMap_smul (KE c w) r v).symm).trans ((rdE (Z.tie (c.twI w) j (c.sd w)) hε).map_smulₛₗ _ v)) (e '' latS w (j.1 + 1))
    have h2 : (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom '' (e '' latS w (j.1 + 1)) = Ψ '' latS w (j.1 + 1) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ => he x
    rw [h2] at h1
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨y', hy', e1⟩ := hsub _ (h1.le ⟨y, hy, rfl⟩)
      exact hinj e1 ▸ hy'
    · obtain ⟨y', hy', e1⟩ := h1.ge (hlat.le ((hmt _).2 ⟨y, hy, rfl⟩))
      exact hinj e1 ▸ hy'
  have hb : BasisAt c w (j.1 + 1) e := fun b => by
    refine ⟨indep_of_read ε (rdE (Z.tie (c.twI w) j (c.sd w)) hε) ?_, top_unique ?_⟩
    · simp only [he]
      exact hind _ b (D.what₂.jMt_basis _ _ b).1
    · rw [← span_latT, ← hL]
      refine Submodule.span_le.2 fun y hy => ?_
      refine (Submodule.span_le (p := (Submodule.span (KE c w) (Set.range fun i => e (b i))).restrictScalars (c.Oe w))).2 ?_ hy
      rintro _ ⟨x, -, rfl⟩
      exact mem_span_basis e b x
  have hfa : Faithful (Z.rd (c.twI w) j (c.sd w)) :=
    GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ X.R X.cG S YS X.geo.v₀ Z.ρ Z.good _ j _ _ (Z.scalar _ j _).ne X.unif
      X.char.models.HW (Z.vec j) H.ks
  have hrat := GlobalTheory.T.class_sums_twisted_definite_forms_rational D Z.ρ Z.good _ j _ _ (Z.tie (c.twI w) j (c.sd w)) (Z.rat H.rat).2.1 H.field.roots _ _ _ H.ok H.cls
  have key : ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
      (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
        Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
      rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (NChoice.thPe D c w (j.1 + 1) (e x)) =
        z₁ • rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (j.1 + 1) (c.sd w) (Nat.le_add_left _ _) j.2).symm ((1 : NX.KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) := by
    intro x hx n a f hf
    have h1 := hth x hx n a f hf
    rw [hε.twVia_eq] at h1
    refine (rdF_thPe _ hε H.ok hrat _).trans ((congrArg _ (he x)).trans (h1.trans (congrArg (z₁ • ·) ?_)))
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rdF_tmul, smul_comm]
    refine congrArg (ε (c.embW w (a k)) • ·) ?_
    refine Eq.trans ?_ (realRd_tmul YS X.geo.v₀ Z.good (c.twI w) j (c.sd w) _ 1 (f k)).symm
    rw [show Z.ρ.e (c.twI w) (c.sd w) (1 : NX.KB S (c.twI w) (c.sd w)) = 1 from map_one _, mul_one]
  have hco := fun x hx n a f hf => GlobalTheory.T.chosenField_forms_proportional_of_readings D c w Z.ρ Z.good j _ hfa ε hε _ _ z₁ (key x hx n a f hf)
  obtain ⟨o, ho⟩ : ∃ o : (c.Oe w)ˣ, ThetaAt Y YS c w j e (algebraMap (c.Oe w) (KE c w) o) := by
    by_cases hex : ∃ t : KE c w, ε t = z₁
    · obtain ⟨t, ht⟩ := hex
      obtain ⟨o, rfl⟩ := GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding (c.Oe w) ε N t hN (ht ▸ hz)
      refine ⟨o, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', e1⟩ := h1 hB
      exact e1.trans (congrArg (· • _) (ε.injective (ht'.trans ht.symm)))
    · refine ⟨1, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', -⟩ := h1 hB
      exact absurd ⟨t', ht'⟩ hex
  exact ⟨e, Units.map (algebraMap (c.Oe w) (KE c w)).toMonoidHom o, hb, hL.trans (span_smul_latT _ o).symm, ho⟩
end GlobalTheory.PlaceRead
namespace GlobalTheory.PlaceRead
open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem exists_local_map_at_place_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  intro hCo hCW hHM hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ _ _ _ w => ∀ (Z : w.Lt) (X : RealSide (w.st Z).toD7), X.R.C = TC.cf w.I w.l Z → FieldOk X :=
    EvG.imp (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP) fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp _ _ w _ Z => (H kp T w Z).1
  refine (((((_root_.GlobalTheory.T.ratRow_of_levelB2_nonzero_index hP hS hL).and (_root_.GlobalTheory.T.clsQ_of_choiceSide_twOK_at_state hP hL)).and (_root_.GlobalTheory.T.series_character_eq_inv_emb_psi0 hL)).and hF).and
    ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev))).trans
    (StepW.of_all fun K B f T w hO _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok v hv i
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H
  obtain ⟨hHo, -⟩ := h5 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h6 (w.st x.o.Z) hO
  let X := RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo (Finite.of_injective _ (ixOf_injective w.I _)) hHo hStd hSize
  have hf : FieldOk X := h4 x.o.Z X x.m.z.lev.C
  obtain ⟨k1, k2⟩ := h2 P x l ch tp hxi hpsi hQ hk hside v hv (hok v hv)
  obtain ⟨k3, k4⟩ := h3 P x l
  obtain ⟨ψ0, -, k5, -⟩ := hside.nct.psi_eq
  exact _root_.GlobalTheory.PlaceRead.exists_basisAt_latAt_thetaAt_of_atPlace (X := X) (Y := x.r.Y) (YS := l.b.YS) (Z := l.b.ser.ex) hCo hCW hHM hP
    { pins := x.m.z.pins, intersectionNumber_baseChange := x.m.intersectionNumber_baseChange, field := hf, tw := hv, ok := hok v hv, cls := k1
      emb := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField _ ch v _ l.b.ser.ex.good).2 hside.nct
      val := fun σ => ⟨_, (k5 v σ).trans (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
      U_eq := k3, psi_eq := k4, ks := l.rat.In.ks _ (Nat.le_add_left _ _) i.2
      rat := h1 P x l _ (GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ ch hside.nct hf.galois v hv) i _
      tup := k2 i }
end GlobalTheory.PlaceRead
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_at_place_determined_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  first | exact @_root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt | exact _root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt | (intros; apply _root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalComponentMatchesOfHoweDuality
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
noncomputable section
namespace UpperTheory.One.M
theorem localComponent_matches_of_howeDuality_alt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
 (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {cf : CharFrame D}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {Rw : RowSide D} (a : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (P : NG.AutRep D.host.E D.R.nV) (μ : D.naut.CG 1)
    (hμ : (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩) (s : SplitPlace D.host.E)
    (π : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hπ : IsLocS (n := D.R.nV) P.S s π)
    (hτ : IsLocS (rep σ).S s τ) (hU : IsUnitarisable τ.ρ)
    (hP : ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ
      (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))))
    (hgπ₀ : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls π)) :
    D.nbc.locAU j (a.A.cls j h1 h2 P) s.w =
      D.naut.lpChar (D.naut.lpSum (Rw.locR σ s.w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ s.w))
        (D.naut.locG D.naut.etaTinv s.w) := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have L : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w) := (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)).recLaws
  set χ := cf.mu0 ⟨j - 1, by omega⟩ with hχ
  have hμc : IsComp χ s.w (χ.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ s.w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, hunit⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ s.w
  have hχu : χ.IsUnitary := hμ ▸ (a.chr.e1 μ).2
  have hμU : IsUnitaryChar (χ.loc s.w) := fun x => by
    rw [huniq _ hμc]; exact hunit hχu x
  have hηc : IsComp cf.eta s.w (cf.eta.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc cf.eta s.w, fun _ => rfl⟩
  have hηi : IsComp (a.chr.e1 D.naut.etaTinv).1 s.w ((cf.eta⁻¹).loc s.w) := by
    rw [a.chr.etaTinv]
    exact ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc _ s.w, fun _ => rfl⟩
  have hinv : (cf.eta⁻¹).loc s.w = (cf.eta.loc s.w)⁻¹ := MonoidHom.ext (HChar.loc_inv _ _)
  have hrt : D.R.r < D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  let π₀ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t) := Irr.ofIrrRep π
  let π' := GlobalTheory.SplitPairLift.twistIrr π₀ hηc.1
  let τ₀ : Irr (s.w.adicCompletion D.host.E) D.R.r := Irr.ofIrrRep τ
  let cμ := GlobalTheory.SplitPairLift.detIrr 1 hμc.1
  let τμ := GlobalTheory.SplitPairLift.detIrr D.R.t hμc.1
  let cη := Irr.ofDet 1 ((cf.eta⁻¹).loc s.w) hηi.1
  have e1 : Nonempty (π'.π.Equiv (prod₂ τ₀.π τμ.π)) :=
    _root_.GlobalTheory.T.theta_lift_general_linear hBZ hB _ D.R.r D.R.t _ _ _ τ.ρ π'.π hrt hμc.1 hμU τ.smooth τ.irr hU π'.smooth π'.irr hP
  have e2 := L.prod _ _ τ₀ τμ π' e1
  have e3 := L.det D.R.t _ cμ τμ ⟨.refl _⟩ ⟨.refl _⟩
  have hgπ : GoodI π' := by
    have e : GlobalTheory.LocLanglands.cls (⟨π'.V, π'.π, π'.smooth, π'.irr⟩ : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) =
        (GlobalTheory.LocLanglands.cls (⟨π₀.V, π₀.π, π₀.smooth, π₀.irr⟩ : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))).tw (cf.eta.loc s.w) hηc.1 :=
      (GlobalTheory.LocGL.IrrGL.tw_of π₀.π π₀.smooth π₀.irr (cf.eta.loc s.w) hηc.1).symm
    show UpperTheory.Zero.LLC.Good _
    rw [e]
    exact (GlobalTheory.RecT.good_tw_iff _ _ _).2 hgπ₀
  have e4 := _root_.UpperTheory.One.M.RecLawsH.twist L _ (cf.eta.loc s.w)⁻¹ cη π' π₀ hgπ (by rw [← hinv]; exact ⟨.refl _⟩) (by
    show Nonempty (π₀.π.Equiv (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist π₀.π (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w))) (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w)⁻¹)))
    rw [GlobalTheory.SplitPairLift.twist_twist_inv]
    exact ⟨.refl _⟩)
  have eμ := _root_.GlobalTheory.LiftSplitLoc.locG_rankOne_alt a.T a.cg a.chr μ s.w (χ.loc s.w) (hμ ▸ hμc)
  have eη := _root_.GlobalTheory.LiftSplitLoc.locG_rankOne_alt a.T a.cg a.chr D.naut.etaTinv s.w _ hηi
  have hau : a.T.e s.w (D.nbc.locAU j (a.A.cls j h1 h2 P) s.w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w _ π₀ := a.au j h1 h2 P s π hπ
  have hrow : a.T.e s.w (Rw.locR σ s.w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w _ τ₀ := a.row.1 σ s τ hτ
  have h7 : D.naut.lpDim (D.naut.locG D.naut.etaTinv s.w) = 1 := by
    rw [← a.T.dim, eη, L.dim]
  apply (a.T.e s.w).injective
  rw [a.T.char _ _ _ h7, a.T.sum, GlobalTheory.SplitPairLift.e_spehLoc, hau, hrow, e4, e2, e3, eη, eμ]
  rfl
set_option maxHeartbeats 1000000 in
theorem liftSplitLocal_of_howeDuality_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  intro hP hL
  have hA := _root_.GlobalTheory.T.split_reference_pair_of_trivial_mu_alt hP hL
  have hB := _root_.GlobalTheory.T.exists_unitarisable_local_component_at_split hP hL
  have hC := _root_.UpperTheory.One.M.goodRef_alt hP hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hA hB hC ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono (GlobalTheory.LiftRef.overRows_and_mono hA hB fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b) hC fun K B f T w Z Wt hX z p0 Y HAB HC Rw a M tup Q hM hI j h1 h2 σ S hS hpair μ hμ v hv => ?_
  obtain ⟨HA, HB⟩ := HAB
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w _ v hv
  have hne : (w.st Z).toD7.what₂.isot j σ ≠ ⊥ := by
    obtain ⟨y, hy, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hy
    apply hF
    rw [hy, map_zero, inner_zero_right]
  obtain ⟨τ, hτ, hU⟩ := HB Rw a M tup Q hM hI j σ hne s
  obtain ⟨π, hπ⟩ := GlobalTheory.LocCompSplit.exists_isLocS (GlobalTheory.LiftRef.autOf (M _ j h1 h2) S hS) s
  have hne' : (NG.isoTyp (M _ j h1 h2).wt.ρ S).comap (M _ j h1 h2).real ≠ ⊥ := by
    obtain ⟨y, hy, F, hF, hF0⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hF
    subst hF
    exact hF0 (inner_zero_left _)
  exact _root_.UpperTheory.One.M.localComponent_matches_of_howeDuality_alt hP.what₂.bz hP.what₂.bern hL a j h1 h2 σ _ μ hμ s π τ hπ hτ hU
    (HA Rw a M tup Q hM hI j h1 h2 σ S hS hpair s π τ hπ hτ) (HC Rw a M tup Q hM hI j h1 h2 S hS hne' s π hπ)
end UpperTheory.One.M
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NOProd
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace UpperTheory.GalN
open GlobalTheory.ParLawsBare GlobalTheory.RowTie GlobalTheory.NPin Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem tempered_of_true_cuspidal_alt (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7}
    {T : WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (h1 : RankOneUnitary T) : AllCuspidalOpenBound D.nd D.naut := by
  intro a π ha _ _ w
  have := GlobalTheory.CuspRep.host_isCMField D.host
  refine ⟨fun e => tempered_of_rank_le_one D T h1 a π e.le w, fun hu α hα => ?_⟩
  obtain ⟨-, hU, hS⟩ := _root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C
  obtain ⟨B, hB, e⟩ := hS a π w ha hu
  rw [e] at hα
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hα
  have k : OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ) := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E a _ (hU a π ha) w B hB b hb
  rw [Units.val_inv_eq_inv_val]
  exact k.inv (one_lt_q w)
theorem allCuspidalOpenBound_of_cuspU_character_choice : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), AllCuspidalOpenBound D.nd D.naut :=
  fun hF _ hL D P => _root_.UpperTheory.GalN.tempered_of_true_cuspidal_alt hF P.cg (_root_.GlobalTheory.TempGal.rankOneUnitary_of_charSide hF hL D P)
theorem allCuspidalOpenBound_of_parIn (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {rep Rw}
    (X : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw) : AllCuspidalOpenBound D.nd D.naut :=
  _root_.UpperTheory.GalN.tempered_of_true_cuspidal_alt hP.what₂.fin X.cg (_root_.GlobalTheory.ParLawsBare.rankOneUnitary_of_charSide X.T X.cg X.chr)
theorem par_laws_bare : _root_.GlobalTheory.ParLawsBare.mainTheorem := by
  intro hP hL D cf rep Rw hE X
  have hrig : IsobaricRigid D.nd D.naut := by
    have := GlobalTheory.CuspRep.host_isCMField D.host
    exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hP.what₂.js.1 (_root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hP.what₂.fin X.cg)
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D X.T, tieAut_of_side X.chr hE, tieGal_bare hE⟩
  exact ⟨htie0, ha5, _root_.UpperTheory.GalN.allCuspidalOpenBound_of_parIn hP X, tieLab_of_lab X.T X.lab, heckeSplitOne_of_side X.chr, cancel_of_tie X.T,
    fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩
end UpperTheory.GalN
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankOneGaloisClosureGeometric
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.GalClose
open GlobalTheory.CuspRep
theorem rankOne_galois_closure_geometric_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (π : D.naut.CG 1) (hr : D.naut.ralg π) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i)))) ∧ IsSSRep ρ ∧
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - ((1 : ℕ) : ℝ)) / 2) ∧ D.naut.tempered (D.naut.locG π w)) ∧
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧
        (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧
        D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG π w) ((1 - ((1 : ℕ) : ℝ)) / 2)) := by
  have h0 : (1 - ((1 : ℕ) : ℝ)) / 2 = 0 := by norm_num
  obtain ⟨ρ, hc, h1, h2⟩ := _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt hPr.fin hPr.art hPr.chA hPr.chP hL D P i π 0 (fun τ z hz => by
    obtain ⟨n, hn⟩ := ((D.naut.ralg_def π).1 hr τ).2 z hz
    exact ⟨n, by rw [hn]; simp⟩)
  refine ⟨ρ, hc, isSSRep_rankOne ρ, fun w hw => ⟨by rw [h0]; exact h1 w hw, ?_⟩, fun w hw => ⟨(h2 w hw).1, fun τ hτ => ?_, by rw [h0]; exact (h2 w hw).2.1⟩⟩
  · exact GlobalTheory.RowTie.tempered_of_rank_le_one D P.T (_root_.GlobalTheory.TempClose.rankOneUnitary_of_charSide hPr.fin hL D P) 1 π le_rfl w
  · apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(h2 w hw).2.2 τ hτ, D.naut.jumpsInf_def i π τ hr]
    simp
end GlobalTheory.GalClose
end
end
section
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtensionStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_value_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | exact _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | (intros; apply _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SCuspOfParSt
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SCuspRows
theorem sCusp_of_parSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL := by
  intro hP hL hPar hRat
  refine allSt_mono' (allSt_and' (allSt_and' hPar hRat) (_root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt hP)) ?_
  rintro K B f T w P x ⟨⟨hp, he⟩, hv⟩ l j hj1 hj2 σ hσ hg
  obtain ⟨π, hc, hr, hs, -, -, -⟩ := hp l j hj1 hj2 σ hσ hg
  obtain ⟨n⟩ := he l
  obtain ⟨Sb, hn⟩ := _root_.GlobalTheory.SCuspRows.exists_eigTrue_alt l n
  refine ⟨π, hc, hr, hs, ?_⟩
  have h2 := GlobalTheory.CuspFrobSplit.galPol_lifts_ae (Dof x) (cfOf x) l.a.A.row Sb n.In.eig hv hn j hj1 hj2 σ hσ hg π hc hs
  have h4 := _root_.GlobalTheory.GalAllPlaces.galPol_lpTw_mem_lifts_eventually hL hP.what₂.fin hP.what₂.gal hP.what₂.cheb (Dof x) l.a.A.wdT l.a.cg _ (embLL0 (Dof x)) π hc hr h2
  exact (GlobalTheory.TwistLift.galPol_lifts_tw_etaTinv (Dof x) (cfOf x) l.a.A.chr hv π h4).mono fun w hw => (Polynomial.mem_lifts _).1 hw
end GlobalTheory.SCuspRows
end
end
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolating
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobi
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DegreeInfimum.PlaceDegreeSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolatingStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  first | exact @GlobalTheory.AnAtFrame.exists_anArc_onOrbit | exact GlobalTheory.AnAtFrame.exists_anArc_onOrbit | (intros; apply GlobalTheory.AnAtFrame.exists_anArc_onOrbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPointStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La : ℝ) (lam : Fin (r - 2) → Fin r → E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La (hX ▸ x) lam → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → ∀ hB : AbDat H A DB tyB eB, ∃ Z : GlobalTheory.CM.CMLat hB.2.2.2.2 DB.p DB.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  first | exact @GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart | exact GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart | (intros; apply GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPointStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_sectionValue_arc_framedPoint : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) := by
  first | exact @GlobalTheory.ArcQ.hasSum_evR_arc | exact GlobalTheory.ArcQ.hasSum_evR_arc | (intros; apply GlobalTheory.ArcQ.hasSum_evR_arc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToCompClm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isHolTo_comp_clm {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo Set.univ y) (φ : V' →L[ℂ] V) :
    IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  exact ⟨h1.preimage φ.continuous, h2.comp φ.differentiable.differentiableOn fun _ hz => hz⟩

theorem nonempty_holArc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), C.Φ.Rational → (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → Nonempty (HolArc Y bF a χ W Fu) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib
  obtain ⟨hadd, honto, hlin⟩ := ex0_additive_surjective_equivariant hL hL2 E H D l c O β _ a Λ
  obtain ⟨hb, hchi⟩ := analyticDictionaryExp_holomorphic_over_unif E H D l c O β _ a Λ
  obtain ⟨hker, hiota, htor, -⟩ := GtKer.ker_iota_torus E H D l c O β _ a Λ
  have hfin : AnFin Λ.A := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.1
  have hrie := gtAn_orth_ker_iff hL hL2 E H D l c O β _ a Λ
  have hpt := ArcPoint.point_sumsAt E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K
  have hdiff := GlobalTheory.T.exponentialFamily_deriv_sumsAt_period hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin hrat
  obtain ⟨T₂, hth⟩ := GlobalTheory.T.arc_levelOne_section_eq_kappa_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  have hrep := GlobalTheory.T.exists_latticeVector_rep_and_shift hL hL2 E H D l c O β _ a Λ
  have hsm : ∀ (s : ℂ) (v : Λ.A.V), K.h.symm (s • K.h v) = s • v := fun s v => by
    rw [map_smul, K.h.symm_apply_apply]
  refine ⟨{
    i := K.i
    T := max K.T T₂
    P₀ := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.P0).comp K.gam.toAddEquiv.toAddMonoidHom
    N := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.N).comp K.gam.toAddEquiv.toAddMonoidHom
    Pw := K.Pw
    Pw_eq := fun w v => ?_
    y := Λ.ε.toLinearMap ∘ₗ Λ.A.yLin ∘ₗ K.gam.toLinearMap
    y_onto := Λ.ε.surjective.comp (Λ.A.yLin_surjective.comp K.gam.surjective)
    ex₀ := fun z => Λ.ex0 (K.h.symm z)
    period := fun w hw => K.period w (lt_of_le_of_lt (le_max_left _ _) hw)
    add := fun z z' => ?_
    onto := honto.comp K.h.symm.surjective
    lin := fun x z => ?_
    hol_b := isHolTo_comp_clm hb (K.h.symm : (Fin g → ℂ) →L[ℂ] Λ.A.V)
    hol_chi := fun x j => (hchi x j).1.comp K.h.symm.differentiable.differentiableOn fun _ hz => hz
    ker := fun z => ?_
    iota := fun v => ?_
    shift := fun w v => ?_
    levelA := fun v => ?_
    levelM := fun v hv => ?_
    riemann := fun v => ?_
    point := hpt
    diff := fun z₀ ν v V f h1 h2 h3 => hdiff z₀ ν v V f ⟨h1, h2, h3⟩
    theta := fun th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ h1 h2 h3 =>
      hth _ (le_max_right _ _) th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ ⟨h1, h2, h3⟩ }⟩
  · show K.Pw w v = K.h (Λ.A.P0 (K.gam v)) + w • K.h (Λ.A.N (K.gam v))
    rw [K.Pw_eq, AnArc.Pw_apply, map_add, map_smul]
  · rw [map_add]; exact hadd _ _
  · have : K.h.symm (fun k => ty k (x : E) * z k) = Λ.A.actV x (K.h.symm z) := by
      apply K.h.injective
      funext k
      rw [K.h_act, K.h.apply_symm_apply, K.h.apply_symm_apply]
    rw [this]
    exact hlin x _
  · refine (hker _).trans ⟨?_, ?_⟩
    · rintro ⟨la, h0, hz⟩
      obtain ⟨v, rfl⟩ := K.gam.surjective la
      refine ⟨v, ?_, ?_⟩
      · show Λ.ε (K.gam v).y = 0
        rw [h0, map_zero]
      · show z = K.h (Λ.A.P0 (K.gam v))
        rw [← hz, K.h.apply_symm_apply]
    · rintro ⟨v, h0, hz⟩
      refine ⟨K.gam v, (map_eq_zero_iff _ Λ.ε.injective).1 h0, ?_⟩
      rw [hz]
      exact K.h.symm_apply_apply _
  · show Out.GtPtF.IsIota (Λ.ε (K.gam v).y) (Λ.ex0 (K.h.symm (K.h (Λ.A.P0 (K.gam v)))))
    rw [K.h.symm_apply_apply]
    exact hiota _
  · show IsTorusPt (Λ.ex0 (K.h.symm (w • K.h (Λ.A.N (K.gam v))))) (fun x => eTwoPi (w * a.be (Λ.ε (K.gam v).y) x))
    have h1 : w • Λ.A.N (K.gam v) = ((w • Λ.A.N (K.gam v)).1, 0) := Prod.ext rfl (by simp)
    rw [hsm, h1]
    convert htor (w • Λ.A.N (K.gam v)).1 using 3 with x
    show _ = w * ((Λ.A.be (K.gam v).y (Λ.ε.symm x) : ℤ) : ℂ)
    rw [Λ.be_eq, Λ.ε.apply_symm_apply]
  · obtain ⟨e, he⟩ := K.levA v
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.A l.A_pos).2 _ _ e (hA v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · obtain ⟨e, he⟩ := K.levM v hv
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.M (le_trans (by norm_num) l.three_le)).2 _ _ e (hM v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · show (∀ v', Λ.ε (K.gam v').y = 0 → (Fu.Di K.i).EF v v' = 0) ↔ (Λ.ε (K.gam v).y = 0 ∧ ∀ s : ℂ, ∃ x,
      IsTorusPt (Λ.ex0 (K.h.symm (s • K.h (Λ.A.P0 (K.gam v))))) x ∧
        ∀ v', x (Λ.ε (K.gam v').y) = eTwoPi (-(s * (Fu.Di K.i).EF v v')))
    simp only [hsm, ← K.EF_eq]
    have := hrie (K.gam v)
    simp only [K.gam.surjective.forall] at this
    exact this

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArcStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTauCanonicalTrivialisation_iff_normalised_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* ℂ) (a : ArcIn Dw l β ℂ b) (Λ : GtAn₀ a) (n : ℕ), letI := H.starRing; (TauCan a.D₀ n ↔ NormAn Λ.A n) := by
  first | exact @GlobalTheory.KappaAn.tauCan_iff_normAn | exact GlobalTheory.KappaAn.tauCan_iff_normAn | (intros; apply GlobalTheory.KappaAn.tauCan_iff_normAn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobiStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), InR D j → j < D.R.m → ∀ F : (recB h).Cusp j ka, (∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA ka) ka.n k)) ∧ (F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka ↔ ∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) := by
  first | exact @GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish | exact GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish | (intros; apply GlobalTheory.LowCoeff.mem_iff_low_coeff_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem ndeg_eq_places {K : Type} [Field K] [NumberField K] (N : MLine K) (hN : N.Good)
    (hc : ∀ σ : K →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) :
    ((∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) -
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding)) / (Module.finrank ℚ K : ℝ) = N.ndeg := by
  have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) =
      -Real.log ((FractionalIdeal.absNorm N.I : ℚ) : ℝ) := by
    simp_rw [neg_mul]
    rw [finsum_neg_distrib, PlaceDegreeSums.sum_count_log_norm _ hN.1]
  have h2 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding) =
      ∑ τ : K →+* ℂ, Real.log (N.n τ) := by
    rw [PlaceDegreeSums.sum_infinite_places_mult (fun σ => Real.log (N.n σ.embedding))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]
    · rw [h]
      exact congrArg Real.log (hc τ)
  rw [h1, h2, MLine.ndeg, MLine.deg]

theorem qbridge_of_numGood : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ch Ah Cc Ac Tt cc : ℝ) (be : HeightOneSpectrum (𝓞 B.KO) → ℝ) (Carch Bdeg : ℝ), Submodule.IsLattice B.KO (B.Mlat j ka) → (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) → WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg + Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ F : B.Cusp j ka, F ∉ WeightFamilies.MggK B CR Tt cc j ka → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁) (φ : B.Cusp j ka →ₗ[B.KO] K₁), WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧ φ F ≠ 0 ∧ NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ) → QBridgeAt large₂ B j ka CR Ch Ah Cc Ac Tt cc := by
  intro D large₂ B j ka CR Ch Ah Cc Ac Tt cc be Carch Bdeg hlat hbe hbefin hbesum hconj hroom hdet
  classical
  obtain ⟨K₁, _, _, _, ρ, g, cf, hfam, hcf, hker, hdim⟩ := kerCore_holds B.KO (B.Cusp j ka)
    (WeightFamilies.MggK B CR Tt cc j ka)
    (fun K₁ _ _ _ φ => WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧
      NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ)
    (fun _ _ _ _ _ h => h.1)
    (fun v hv => by
      by_contra hn
      obtain ⟨K₁, _, _, _, φ, h1, h2, h3⟩ := hdet v hn
      exact h2 (hv K₁ φ ⟨h1, h3⟩))
    (fun K' K₁ _ _ _ _ _ _ e f hf => ⟨e.toLinearMap.comp f, ⟨fun v hv => by
      have := LinearMap.mem_ker.1 (hf.1 hv)
      simp [LinearMap.mem_ker, this], GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension _ _ _ _ _ _ _ K' K₁ e f hf.2⟩, fun _ => rfl⟩)
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg hlat.span_eq_top (WeightFamilies.MggK B CR Tt cc j ka)
  have hρ : ρ = WeightFamilies.rhoP B CR Tt cc j ka := by omega
  subst hρ
  choose N hG hd hc hint harch using fun i => (hfam i).2
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, cf, be,
    fun i w => -(FractionalIdeal.count K₁ w (N i).I : ℝ), fun i σ => Real.log ((N i).n σ.embedding), Carch, Bdeg,
    hker, hbe, hbefin, hbesum, fun i => ?_, fun la w hw i F hF hne => ?_, hconj, fun σ i F hF hne => ?_,
    fun i => ?_, hroom⟩
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (N i).I)).subset fun w hw h => hw ?_
    simp [h]
  · rw [hcf] at hne ⊢
    exact (hint i la w hw F hF hne).trans_eq (sub_eq_add_neg _ _)
  · rw [hcf] at hne ⊢
    rw [← InfinitePlace.norm_embedding_eq]
    exact harch i σ.embedding F hF hne
  · rw [ndeg_eq_places (N i) (hG i) (hc i)]
    exact hd i

end GlobalTheory.ArcCM
end


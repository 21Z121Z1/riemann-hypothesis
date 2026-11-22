import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySubsingletonCohAmplePsEff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem TwistConeVanishing.of_isZero {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {F : X.Modules} (hF : IsZero F) : TwistConeVanishing A N F :=
  ⟨0, fun j m _ _ p _ => cohOn.subsingleton_of_isZero
    ((isZero_twist_iff (isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m))).2 hF) ⊤ p⟩

theorem TwistConeVanishing.of_shortExact {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : TwistConeVanishing A N S.X₁)
    (h₃ : TwistConeVanishing A N S.X₃) : TwistConeVanishing A N S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun j m hj hm p hp => ?_⟩
  have hT := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  exact cohOn.subsingleton₂ (Twist.shortExact_map hT hS) ⊤ p
    (ha j m (le_of_max_le_left hj) hm p hp) (hb j m (le_of_max_le_right hj) hm p hp)

theorem TwistConeVanishing.of_generic (k : Type) [Field k] {V : Scheme.{0}} [IsIntegral V]
    (f : V ⟶ Sp k) (hf : IsProjOver f) (A N : LB V) (hA : IsAmpleLB A) (hN : IsPsEff N)
    (G : V.Modules) [IsFiniteQC G]
    (h : ∀ E : V.Modules, IsFiniteQC E → genericPoint V ∉ support E → TwistConeVanishing A N E) :
    TwistConeVanishing A N G := by
  have : AlgebraicGeometry.IsNoetherian V := isNoetherian_of_isProjOver hf
  obtain ⟨r, hr, s, hs⟩ := hN.exists_hasNonzeroSec hA (m := 2) (by norm_num)
  have hM : (lbPow (tens (lbPow N 2) A) r).IsLB :=
    isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB 2) hA.isLB) r
  have hgen : genericPoint V ∈ Out.nonzeroLocus s := (sec_ne_zero_iff s).1 hs
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' k f hf A N hA hN.isLB G (2 * r)
  have hCf : IsFiniteQC (cokernel (cutHom G hM s)) := ((cut_by_regular_section.{0} G hM).1 s).2.2.1
  have hCs : support (cokernel (cutHom G hM s)) = support G \ ↑(Out.nonzeroLocus s) :=
    ((cut_by_regular_section.{0} G hM).1 s).2.2.2.1
  haveI : IsFiniteQC (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) :=
    isFiniteQC_twist (isLB_lbZPow hM (-1))
  refine GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor A N hA.isLB hN.isLB r hr hM s G ⟨j₁, hj₁⟩ (h _ inferInstance ?_)
    (h _ hCf ?_)
  · exact GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing hM s G _ hgen
  · rw [hCs]
    exact fun h' => h'.2 hgen

end GlobalTheory

namespace GlobalTheory

theorem eventually_subsingleton_coh_ample_psEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → ∀ F : X.Modules, IsFiniteQC F → ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p → Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ X f hf A N hA hN hpe F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  refine devissage X (TwistConeVanishing A N) (fun _ h => .of_isZero hA.isLB hN h)
    (fun _ hS _ _ h₁ h₃ => .of_shortExact hA.isLB hN hS h₁ h₃) ?_ F hF
  intro Z hZ hsmall G hG
  haveI := hG
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN G).1 ?_
  refine TwistConeVanishing.of_generic k (redι Z ≫ f)
    (ProjSpace.isProjOver_comp_of_isClosedImmersion _ hf) _ _ hAV (hpe Z hZ) G ?_
  intro E hE hη
  haveI := hE
  have hE' : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj E) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV E
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN E).2 (hsmall _ hE' ?_)
  have hsub := GlobalTheory.T.support_pushforward_subset_image (redι Z) E
  refine ⟨hsub.trans ((Set.image_subset_range _ _).trans (range_redι Z).le), fun hle => hη ?_⟩
  have hηZ : (redι Z) (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ∈ (Z : Set X) :=
    (range_redι Z).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyη⟩ := hsub (hle hηZ)
  rwa [(redι Z).isClosedEmbedding.injective hyη] at hy

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CuspRep.GASplit
variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

theorem continuous_infEq_symm : Continuous (infEq E).symm := by
  refine continuous_pi fun w => ?_
  exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    (continuous_apply w)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_infEq_symm E).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_sInf : Continuous (sInf E) :=
  (continuous_infEq E).prodMk continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  continuous_const.prodMk continuous_id

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

def splitMulEquiv : GA E a ≃* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toFun g := (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g)
  invFun p := infGL E a p.1 * finGL E a p.2
  left_inv g := infGL_mul_finGL g
  right_inv p := by
    obtain ⟨y, k⟩ := p
    refine Prod.ext ?_ ?_ <;> simp
  map_mul' g h := by simp

def splitEquiv : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toMulEquiv := splitMulEquiv E a
  continuous_toFun :=
    ((continuous_glMap a (pInf E) (continuous_pInf E))).prodMk (continuous_glMap a (pFin E) (continuous_pFin E))
  continuous_invFun :=
    ((continuous_cornerGL a (sInf E) (continuous_sInf E)).comp continuous_fst).mul
      ((continuous_cornerGL a (sFin E) (continuous_sFin E)).comp continuous_snd)

theorem exists_split : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E),
      ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) :=
  fun E _ _ _ a => ⟨splitEquiv E a, fun _ => rfl⟩

end GlobalTheory.CuspRep.GASplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedeanStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧ ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.exists_embRet | exact GlobalTheory.DefU.exists_embRet | (intros; apply GlobalTheory.DefU.exists_embRet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧ ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.LocRet.exists_ret | exact GlobalTheory.DefU.LocRet.exists_ret | (intros; apply GlobalTheory.DefU.LocRet.exists_ret <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharacters
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

section Change

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ} {V : HSp D}
  {X : Comp → Data E r} {rd : C →ₛₗ[σ] FDSec X} {dict : GA D V → Σ c, Frame (X c).Ψ r} {mu mu' : GA D V → ℂ}

theorem norm_jFn_eq_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (f : C) (q : AutQ V) :
    ‖jFn V σ rd dict mu' f q‖ = ‖jFn V σ rd dict mu f q‖ := by
  show ‖mu' q.out * rd f (dict q.out).1 (dict q.out).2‖ = ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖
  rw [norm_mul, norm_mul, h.2.1, h'.2.1]

theorem jMemL2_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hc : Continuous mu)
    (hc' : Continuous mu') (hL : JMemL2 V σ rd dict mu) : JMemL2 V σ rd dict mu' := by
  intro f
  have hne : ∀ g, mu g ≠ 0 := fun g h0 => by
    have := h.2.1 g
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => mu' g / mu g) (γ * g) = (fun g => mu' g / mu g) g := by
    intro γ hγ g
    show mu' (γ * g) / mu (γ * g) = mu' g / mu g
    rw [h.1, h'.1, h.2.2.1 γ hγ, h'.2.2.1 γ hγ, one_mul, one_mul]
  have hm : AEStronglyMeasurable (onQ V (fun g => mu' g / mu g)) (muQ1 V) := by
    haveI : BorelSpace (GA D V) := ⟨rfl⟩
    rw [onQ_eq_lift _ hinv]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_from_quotient.2 (hc'.div hc hne).measurable
  have he : jFn V σ rd dict mu' f = onQ V (fun g => mu' g / mu g) * jFn V σ rd dict mu f := by
    funext q
    show mu' q.out * rd f (dict q.out).1 (dict q.out).2 =
      mu' q.out / mu q.out * (mu q.out * rd f (dict q.out).1 (dict q.out).2)
    rw [← mul_assoc, div_mul_cancel₀ _ (hne _)]
  refine (hL f).congr_norm ?_ (Filter.Eventually.of_forall fun q => (norm_jFn_eq_of_muUnit h h' f q).symm)
  rw [he]
  exact hm.mul (hL f).aestronglyMeasurable

theorem peterson_norm_independent_of_unitary_character (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hL : JMemL2 V σ rd dict mu)
    (hL' : JMemL2 V σ rd dict mu') (f : C) : l2NormAlt V σ rd dict mu' hL' f = l2NormAlt V σ rd dict mu hL f := by
  show ‖(hL' f).toLp _‖ = ‖(hL f).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => norm_jFn_eq_of_muUnit h h' f q)]

end Change

theorem exists_mu_reCore : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  intro D T chiW hJ hC hchi
  have hex : ∀ j σ, ∃ mu : GA D (T.V j σ) → ℂ, InR D j → GoodEmb T.Q.c σ →
      MuVal (T.V j σ) (chiW j σ) mu ∧ MuUnit (T.V j σ) (T.dict j σ) mu ∧ Continuous mu := by
    intro j σ
    by_cases h : InR D j ∧ GoodEmb T.Q.c σ
    · obtain ⟨mu, h1, h2, h3, h4, h5⟩ := GlobalTheory.Member.exists_muVal D (T.V j σ) (chiW j σ) (hchi j h.1 σ h.2).1
        (hchi j h.1 σ h.2).2.1
      exact ⟨mu, fun hj hσ => ⟨h1, ⟨h2, h3, h4, (hJ.muUnit j hj σ hσ).2.2.2⟩, h5⟩⟩
    · exact ⟨fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
  choose mu hmu using hex
  have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (mu j σ) :=
    fun j hj σ hσ a n hd => jMemL2_of_muUnit (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.muCont j hj σ hσ)
      (hmu j σ hj hσ).2.2 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
  have hLM : LawsM (reCore T T.dict mu chiW T.x₀ T.cE).toCore :=
    { pins := hJ.pins
      half := hJ.half
      evalWD := hJ.evalWD
      unf := hJ.unf
      unTest := hJ.unTest
      chiTriv := hJ.chiTriv
      dictU := hJ.dictU
      spaceW := hJ.spaceW
      levelK := hJ.levelK
      xiAbs := hJ.xiAbs
      muUnit := fun j hj σ hσ => (hmu j σ hj hσ).2.1
      muCont := fun j hj σ hσ => (hmu j σ hj hσ).2.2
      finVol := hJ.finVol
      cuspFD := hJ.cuspFD
      supDef := hJ.supDef
      cuspidalL2Subspace := hL
      l2Def := fun j hj σ hσ a n hd f h0 => hJ.l2Def j hj σ hσ a n hd f
        ((peterson_norm_independent_of_unitary_character (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
          (hL j hj σ hσ a n hd) f).symm.trans h0)
      unitIndep := hJ.unitIndep
      ptNe := hJ.ptNe }
  refine ⟨mu, ?_, ?_⟩
  · exact
      { toLawsM := hLM
        cUnit := hJ.cUnit
        muVal := fun j hj σ hσ => (hmu j σ hj hσ).1
        muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
        intAll := hJ.intAll
        modelW := hJ.modelW
        familyUniformisationBasePointOrthogonal := hJ.familyUniformisationBasePointOrthogonal
        kfHalf := hJ.kfHalf
        adPin := hJ.adPin }
  · exact
      { toLawsM := hLM
        cuspMul := hC.cuspMul
        latZ := hC.latZ
        cuNe := hC.cuNe
        expo := hC.expo }

end GlobalTheory.RealGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamil
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InfSurj

theorem list_prod_single {G ι : Type} [Monoid G] [DecidableEq ι] (v : ι) (a : G) :
    ∀ l : List ι, l.Nodup → v ∈ l → (l.map fun u => if u = v then a else 1).prod = a
  | [], _, h => absurd h List.not_mem_nil
  | u :: l, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.prod_cons]
    by_cases hu : u = v
    · subst hu
      have : (l.map fun w => if w = u then a else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun w hw => if_neg fun (e : w = u) => hn.1 (e ▸ hw)
      rw [if_pos rfl, this, List.prod_map_one, mul_one]
    · rw [if_neg hu, one_mul]
      exact list_prod_single v a l hn.2 ((List.mem_cons.1 h).resolve_left (Ne.symm hu))

end GlobalTheory.InfSurj

theorem GlobalTheory.InfSurj.exists_infU_cAll_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  intro E _ _ _ n g hg
  classical
  have he := fun v : InfinitePlace E => GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
  choose e he using he
  let y : InfinitePlace E → UA E n := fun v => ((e v).symm ⟨(g v : Matrix (Fin n) (Fin n) ℂ), hg v⟩ : embU n v.embedding)
  have hy : ∀ v, y v ∈ embU n v.embedding := fun v => ((e v).symm _).2
  have hyv : ∀ v, cEmb v.embedding (y v) = g v := fun v => by
    rw [← he v, ContinuousMulEquiv.apply_symm_apply]
    ext i j
    rfl
  have hyu : ∀ u v, u ≠ v → cEmb v.embedding (y u) = 1 := fun u v huv => by
    have h := (Subgroup.mem_inf.1 (hy u)).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h v.embedding
    rw [Subgroup.mem_iInf] at h2
    exact h2 (by rw [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]; exact Ne.symm huv)
  refine ⟨(Finset.univ.toList.map y).prod, ?_, ?_⟩
  · refine (infU E n).list_prod_mem fun z hz => ?_
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact (Subgroup.mem_inf.1 (hy u)).1
  · funext v
    change cEmb v.embedding _ = g v
    rw [map_list_prod, List.map_map]
    have : (Finset.univ.toList.map (cEmb v.embedding ∘ y)) = Finset.univ.toList.map fun u => if u = v then g v else 1 :=
      List.map_congr_left fun u _ => by
        by_cases h : u = v
        · subst h; simp [hyv]
        · simp [h, hyu u v h]
    rw [this]
    exact GlobalTheory.InfSurj.list_prod_single v (g v) _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ v))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivStageStandIn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

theorem exists_divStage_standIn : ∀ (B : Base) (C : Cols B) (W : RowsRest B C), StandIn W →
    ∀ η : ℝ, ∃ V : DivStage B C W, V.div.etaF = η := by
  intro B C W _ η
  obtain ⟨V, -, -, -, -, -, -, -, hη, -⟩ := GlobalTheory.Mem.exists_divStage B C W W.Drows W.onb.toBasis (fun _ => 1)
    (fun _ => by simp) ⊤ (fun u => ((C.fm u).lat 0).L) (fun _ => 0) (fun _ => 0) η
  exact ⟨V, hη⟩

end GlobalTheory.Mem.Df
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory

theorem ambSpace_map_eq_sum {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} (A : HLat K)
    {W : Type} [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W) (x : A.V) :
    j x = ∑ i, σ (A.b.repr x i) • j (A.b i) := by
  conv_lhs => rw [← A.b.sum_repr x]
  rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

private lemma exists_linearEquiv_euclidean_norm_eq_mulVec {ι W : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup W]
    [Module ℂ W] (bW : Module.Basis ι ℂ W) (N : Matrix ι ι ℂ) (hN : IsUnit N.det) :
    ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ w, ‖g w‖ = Real.sqrt (∑ i, ‖(N.mulVec (bW.equivFun w)) i‖ ^ 2) := by
  letI := Matrix.invertibleOfIsUnitDet N hN
  let e₂ : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) := Matrix.toLinearEquiv' N this
  let e₃ : (ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ ι := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  let e₄ : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, bW.equivFun.trans (e₂.trans (e₃.trans e₄.toLinearEquiv)), fun w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  rfl

theorem exists_equiv_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  intro K _ _ _ σ A W _ _ j hX hli hsp
  let bW : Module.Basis A.ι ℂ W := Module.Basis.mk hli (by rw [hsp])
  have hc : ∀ x, bW.equivFun (j x) = fun i => σ (A.b.repr x i) := by
    intro x
    have hx : j x = bW.equivFun.symm (fun i => σ (A.b.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply, ambSpace_map_eq_sum]
      simp [bW, Module.Basis.mk_apply]
    rw [hx, LinearEquiv.apply_symm_apply]
  have hU : IsUnit ((A.X (InfinitePlace.mk σ))⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX _)
  have hv : ∀ x, Formalism.HermitianLatticesTheory.vecAt A.b (InfinitePlace.mk σ) x =
      fun i => (InfinitePlace.mk σ).embedding (A.b.repr x i) := fun x => rfl
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (A.X (InfinitePlace.mk σ))⁻¹ hU
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
  · have hU' : IsUnit (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det := by
      have e : (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det =
          starRingEnd ℂ ((A.X (InfinitePlace.mk σ))⁻¹).det := (RingHom.map_det _ _).symm
      rw [e]
      exact hU.map _
    obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)) hU'
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1
    simp [Matrix.mulVec, dotProduct, map_sum, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem exists_finU_mul_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : UA E n),
    ∃ k ∈ finU E n, ∃ x ∈ infU E n, g = k * x := by
  intro E _ _ _ n g
  let k : UA E n := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1), ClassFin.finGL_mem_UA _ (ClassFin.cT_pFin g)⟩
  have hk : k ∈ finU E n := pInf_finGL _
  refine ⟨k, hk, k⁻¹ * g, ?_, (mul_inv_cancel_left k g).symm⟩
  change GeneralLinearGroup.map (pFin E) (k⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) k.1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlockStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type) (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω), A₀ ∈ S.S (genericPoint M.Z) → ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  first | exact @GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | exact GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | (intros; apply GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfCommutingEndAlgHomStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinearMap_of_commuting_endAlgHom : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V), (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) → ∃ F : MultilinearMap ℂ Wv V, F w = y ∧ ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u), Φ v A (F x) = F (Function.update x v (A (x v))) := by
  first | exact @GlobalTheory.exists_multilinear_of_commuting_endAlgHom | exact GlobalTheory.exists_multilinear_of_commuting_endAlgHom | (intros; apply GlobalTheory.exists_multilinear_of_commuting_endAlgHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModelsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  first | exact @GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | exact GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | (intros; apply GlobalTheory.RealGeo.BaseFrame.exists_baseFrame <;> assumption)
end


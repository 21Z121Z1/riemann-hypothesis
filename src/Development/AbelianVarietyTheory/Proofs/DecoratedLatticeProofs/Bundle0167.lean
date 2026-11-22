import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.NegWeil

variable {D : D7}

theorem symplOH_neg_neg (S T : HSp D) (x y : WO S T) : symplOH S T (-x) (-y) = symplOH S T x y := by
  have h : hO S T (-x) (-y) = hO S T x y := by
    unfold hO
    simp only [Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]
  unfold symplOH symplO
  rw [h]

theorem heisO_refl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    (fun x => heisO ψ S T u f (-x)) = heisO ψ S T (-u) (fun x => f (-x)) := by
  funext x
  unfold heisO
  simp only [← symplOH_neg_neg S T x (-u), neg_neg, neg_add]

theorem ratW_neg (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S (-γ) = -ratW T S γ := by
  ext i j
  simp [ratW]

theorem actO_neg (S T : HSp D) (g : GA D S) (h : GA D T) (w : WO S T) : actO S T g h (-w) = -actO S T g h w := by
  unfold actO
  rw [Matrix.mul_neg, Matrix.neg_mul]

theorem theta_refl {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T fun x => f (-x) := by
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp continuous_neg, fun k L hL hL0 w => ?_⟩
  · have := hf.quasi (-γ) (-w)
    rw [ratW_neg] at this
    have e : symplOH S T (-ratW T S γ) (-w) = symplOH S T (ratW T S γ) w := symplOH_neg_neg S T _ _
    rw [e] at this
    rw [← this, neg_add]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    have h0 : (-u).map (infPart D) = 0 := by
      rw [Matrix.map_neg _ (map_neg (infPart D)), hu0, neg_zero]
    have := heisO_refl ψ S T (-u) f
    rw [neg_neg, h (-u) (U.neg_mem hu) h0] at this
    exact this.symm
  · have := hf.smooth k (-L) hL.neg (fun t => by
      rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (map_neg (finPart D)), hL0, neg_zero]) (-w)
    simpa only [AddMonoidHom.neg_apply, neg_add] using this

theorem theta_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (c : ℂ) :
    IsThetaFunO ψ S T (c • f) := by
  refine ⟨fun γ w => ?_, ?_, hf.cont.const_smul c, fun k L hL hL0 w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]
    ring
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    have := congrFun (h u hu hu0) w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    ring
  · exact (hf.smooth k L hL hL0 w).const_smul c

noncomputable def reflEnd (X : Type) [AddGroup X] : Module.End ℂ (X → ℂ) →* Module.End ℂ (X → ℂ) where
  toFun L :=
    { toFun := fun f x => L (fun y => f (-y)) (-x)
      map_add' := fun f f' => by
        have : (fun y => (f + f') (-y)) = (fun y => f (-y)) + fun y => f' (-y) := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c f => by
        have : (fun y => (c • f) (-y)) = c • fun y => f (-y) := rfl
        rw [this, map_smul]; rfl }
  map_one' := LinearMap.ext fun f => funext fun x => by
    show f (- -x) = f x
    rw [neg_neg]
  map_mul' L L' := LinearMap.ext fun f => funext fun x => by
    show L (L' fun y => f (-y)) (-x) = L (fun z => L' (fun y => f (-y)) (- -z)) (-x)
    simp only [neg_neg]

noncomputable def reflRep {S T : HSp D} (om : WRep S T) : WRep S T := (reflEnd (WO S T)).comp om

theorem reflRep_apply {S T : HSp D} (om : WRep S T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    reflRep om p f = fun x => om p (fun y => f (-y)) (-x) := rfl

theorem weil_refl {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hw : IsWeilDatumO ψ S T χS χT om) : IsWeilDatumO ψ S T χS χT (reflRep om) := by
  refine ⟨hw.std, hw.hecS, hw.hecT, hw.resS, hw.resT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p f hf
    exact theta_refl (hw.om_pres p _ (theta_refl hf))
  · intro g h w₀ f hf
    rw [reflRep_apply, reflRep_apply, heisO_refl, hw.om_heis _ _ _ _ (theta_refl hf), heisO_refl, actO_neg, neg_neg]
  · intro γ hγ γ' hγ' f hf
    rw [reflRep_apply]
    show om (γ, γ') (fun y => f (-y)) (-0) = f 0
    rw [neg_zero, hw.om_aut γ hγ γ' hγ' _ (theta_refl hf), neg_zero]
  · intro f hf w
    exact hw.om_cont _ (theta_refl hf) (-w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    let dE : WO S T ≃+ WO S T := AddEquiv.neg _
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ continuous_neg continuous_neg
    have hfm : Measurable (fun x : WO S T => -x) := continuous_neg.measurable
    have hmp : MeasurePreserving (fun x : WO S T => -x) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hfm)]
      have : (fun x : WO S T => -x) ∘ dE = id := funext fun w => neg_neg w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (fun x : WO S T => -x) := (Homeomorph.neg (WO S T)).measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) ((fun x : WO S T => -x) ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := fun γ : ratL T S => -γ) neg_bijective ?_
      intro γ x
      show -(-(γ : WO S T) + x) = (γ : WO S T) + -x
      rw [neg_add, neg_neg]
    calc ∫⁻ w in 𝓕, ‖reflRep om p f w‖ₑ ^ 2 ∂μ
        = ∫⁻ z in (fun x : WO S T => -x) ⁻¹' 𝓕, ‖reflRep om p f (-z)‖ₑ ^ 2 ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖reflRep om p f w‖ₑ ^ 2) 𝓕).symm
      _ = ∫⁻ z in (fun x : WO S T => -x) ⁻¹' 𝓕, ‖om p (fun y => f (-y)) z‖ₑ ^ 2 ∂ν := by
          simp only [reflRep_apply, neg_neg]
      _ = ∫⁻ z in (fun x : WO S T => -x) ⁻¹' 𝓕, ‖f (-z)‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd p _ (theta_refl hf)
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => ℓ fun z => F (-z)
        map_add' := fun a b => by rw [← map_add]; rfl
        map_smul' := fun c a => by rw [← map_smul]; rfl }
    have h1 : ℓ (fun z => om (g, h) (fun y => f (-y)) (-z)) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ (fun z => f (- -z)) :=
      H ℓ' (fun u hu F hF => by
        show ℓ (fun z => heisO ψ S T u F (-z)) = ℓ fun z => F (-z)
        rw [heisO_refl]
        exact hℓ (-u) (fun i j => by rw [Matrix.neg_apply, mul_neg, hu]) _ (theta_refl hF)) _ (theta_refl hf)
    simp only [neg_neg] at h1
    exact h1

theorem det_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (ε : R) (M : Matrix n n R)
    (h : ∀ i j, ε * (M - 1) i j = (M - 1) i j) : ∃ t, t * ε = M.det - 1 := by
  rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq, map_one, RingHom.map_det]
  have : (Ideal.Quotient.mk (Ideal.span {ε})).mapMatrix M = (Ideal.Quotient.mk (Ideal.span {ε})).mapMatrix 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, ← Matrix.sub_apply, ← h i j]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [this, map_one, Matrix.det_one]

theorem idem_identity {R : Type} [CommRing R] {e e' d d' t : R} (e1 : e * e = e) (e2 : e * e' = 0) (e3 : e' * e' = e')
    (h1 : d' * d = 1) (ht : t * (e + e') = d - 1) : d * (e' * d' + (1 - e')) = e * d + (1 - e) := by
  linear_combination e' * h1 - (1 - e - e') * ht - t * e1 - 2 * t * e2 - t * e3

theorem conj_det_mul (V : HSp D) (g : GA D V) : cA D (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g).det = 1 := by
  rw [← GlobalTheory.ConjAdjWeil.det_inv_eq, ← Matrix.det_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.det_one]

theorem detA_val (V : HSp D) (g : GA D V) : ((detA V g : (AE D)ˣ) : AE D) = (Formalism.L2.Theta.mt V g).det := rfl

theorem conj_detAt {e : AE D} {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    cA D (x : AE D) = cA D e * cA D (Formalism.L2.Theta.mt V g).det + (1 - cA D e) := by
  rw [hx, map_add, map_mul, map_sub, map_one]

theorem conj_idem {e : AE D} (he : IsSplitIdem D e) : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]

theorem det_sub_one_of_suppAt {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    ∃ t, t * (e + cA D e) = (Formalism.L2.Theta.mt V g).det - 1 := det_sub_one _ _ hg

theorem det_mul_conj {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : detA V g * Units.map (cA D).toMonoidHom x = x := by
  obtain ⟨t, ht⟩ := det_sub_one_of_suppAt hg
  have h3 := idem_identity he.1 he.2.1 (conj_idem he) (conj_det_mul V g) ht
  rw [← conj_detAt hx] at h3
  have h4 : (Formalism.L2.Theta.mt V g).det * cA D (x : AE D) = x := h3.trans (Eq.symm hx)
  apply Units.ext
  rw [Units.val_mul, detA_val, Units.coe_map]
  exact h4

theorem chi_det {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) {e : AE D} (he : IsSplitIdem D e) {V : HSp D}
    {g : GA D V} (hg : SuppAt e V g) {x : (AE D)ˣ} (hx : IsDetAt e V g x) : χ (detA V g) = χ x * χ x := by
  have := congrArg χ (det_mul_conj he hg hx)
  rw [map_mul, GlobalTheory.ConjAdjWeil.chi_conj hR] at this
  exact mul_inv_eq_iff_eq_mul.1 this

noncomputable def twistRep {S T : HSp D} (χ : (AE D)ˣ →* Circle) (om : WRep S T) : WRep S T where
  toFun p := (((χ (detA S p.1))⁻¹ : Circle) : ℂ) • om p
  map_one' := by simp
  map_mul' p q := by
    rw [map_mul, smul_mul_smul_comm, Prod.fst_mul, map_mul, map_mul, mul_inv, Circle.coe_mul]

theorem twistRep_apply {S T : HSp D} (χ : (AE D)ˣ →* Circle) (om : WRep S T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    twistRep χ om p f = (((χ (detA S p.1))⁻¹ : Circle) : ℂ) • om p f := rfl

theorem weil_twist {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hH : IsHeckeChar D χT) (hR : ResEta D χT T.rank)
    (hw : IsWeilDatumO ψ S T χS χT⁻¹ om) : IsWeilDatumO ψ S T χS χT (twistRep χT om) := by
  refine ⟨hw.std, hw.hecS, hH, hw.resS, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p f hf
    exact theta_smul (hw.om_pres p f hf) _
  · intro g h w₀ f hf
    rw [twistRep_apply, twistRep_apply, hw.om_heis _ _ _ _ hf]
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  · intro γ hγ γ' hγ' f hf
    rw [twistRep_apply, GlobalTheory.Eis.apply_detA hH hγ, Pi.smul_apply, hw.om_aut γ hγ γ' hγ' f hf]
    simp
  · intro f hf w
    have hc : Continuous fun p : GA D S × GA D T => (((χT (detA S p.1))⁻¹ : Circle) : ℂ) :=
      continuous_subtype_val.comp ((hH.1.comp (GlobalTheory.Eis.continuous_detA.comp continuous_fst)).inv)
    exact hc.mul (hw.om_cont f hf w)
  · intro μ 𝓕 hμ hF p f hf
    rw [← hw.om_unit μ 𝓕 hμ hF p f hf]
    congr 1
    funext w
    rw [twistRep_apply, Pi.smul_apply, smul_eq_mul, enorm_mul, ← ofReal_norm_eq_enorm (((χT (detA S p.1))⁻¹ : Circle) : ℂ),
      Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hfac : splitFacO χS χT x y = (χT (detA S g))⁻¹ * splitFacO χS χT⁻¹ x y := by
      rw [chi_det hR he hg hx]
      simp only [splitFacO, MonoidHom.inv_apply, inv_inv]
      group
    rw [twistRep_apply, map_smul, H ℓ hℓ f hf, hfac, Circle.coe_mul, smul_eq_mul]
    ring

theorem exists_neg_datum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → (∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → IsThetaFunO ψ (negSp A) B fun x => conj (f (-x))) ∧ ∃ om' : WRep (negSp A) B, IsWeilDatumO ψ (negSp A) B χA⁻¹ χB om' ∧ ∀ (g : GA D (negSp A)) (h : GA D B) (f : WO A B → ℂ), IsThetaFunO ψ A B f → om' (g, h) (fun x => conj (f (-x))) = fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) * conj (om (negEquiv A g, h) f (-x)) := by
  intro D ψ A B χA χB om hw
  refine ⟨fun f hf => ?_, ?_⟩
  · exact ((GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std A B).1 (fun x => f (-x))).2.2 (theta_refl hf)
  · have h1 : IsWeilDatumO ψ (negSp A) B χA⁻¹ χB⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) :=
      GlobalTheory.ConjWeil.weil_conjSource D ψ A B χA χB om hw
    refine ⟨_, weil_twist hw.hecT hw.resT (weil_refl h1), fun g h f _ => ?_⟩
    have e : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (fun y : WO A B => conj (f (- -y))) = f := by
      funext y
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    show (fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) *
      conj (om (negEquiv A g, h) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (fun y : WO A B => conj (f (- -y)))) (-x))) = _
    rw [e]

end GlobalTheory.NegWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsParamVecOne
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.TrivCoef

open GlobalTheory.LFun GlobalTheory.PRep
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section Lin

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def trivParGL : Fin n → ℂˣ := fun i =>
  Units.mk0 ((Formalism.UG.qV E w : ℂ) ^ (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
    (by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => qV_ne_zero w (by exact_mod_cast h.1))

theorem chiDelta_trivParGL (b : GL (Fin n) (w.adicCompletion E)) :
    Formalism.UG.chiDelta E w (fun i => (trivParGL w n i : ℂ)) b = 1 := by
  unfold Formalism.UG.chiDelta
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : (Formalism.UG.qV E w : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  simp only [trivParGL, Units.val_mk0]
  rw [← Complex.cpow_int_mul, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem isSatVecGL_one :
    IsSatVecGL w (1 : Representation ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) 1
      (Finset.univ.val.map (trivParGL w n)) := by
  have hs : Formalism.UG.IsSpherical E w (fun i => (trivParGL w n i : ℂ))
      (fun _ : GL (Fin n) (w.adicCompletion E) => (1 : ℂ)) := fun b g k _ _ => by
    rw [chiDelta_trivParGL, one_mul]
  have h := isSatVecGL_of_isSpherical hs (fun h0 => one_ne_zero (congrFun h0 1))
  exact IsSatVecGL.of_map (LinearMap.pi fun _ => LinearMap.id) (fun g y => rfl)
    (fun a b hab => congrFun hab 1) h

end Lin

section Unit

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (q n : ℕ)

def trivParU (hq : q ≠ 0) : Fin (n / 2) → ℂˣ := fun i =>
  Units.mk0 ((q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) (zpow_ne_zero _ (by exact_mod_cast hq))

variable [CompleteSpace L]

end Unit

section Global

variable {D : D7}

end Global

end GlobalTheory.Core.Rk.TrivCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

namespace GlobalTheory.KerInert

open scoped TensorProduct

theorem npow_zpow {q : ℕ} (hq : q ≠ 0) (r : ℝ≥0) (m : ℤ) (hr : (r : ℝ) = (q : ℝ) ^ (-(2 * m))) (t : ℂ) :
    GlobalTheory.Doubling.npow r t = (q : ℂ) ^ (-(2 * (m : ℂ) * t)) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have h1 : ((r : ℝ) : ℂ) ≠ 0 := by rw [hr]; exact_mod_cast (zpow_pos h0 _).ne'
  rw [GlobalTheory.Doubling.npow, Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hq),
    ← Complex.ofReal_log r.coe_nonneg, hr, Real.log_zpow, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem exists_isSphSec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (μ : (AF F ⊗[F] E)ˣ →* Circle)
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (hq : qV F v ≠ 0) {s : ℂ} {φ : GLoc σ Q v → ℂ} (h1 : φ ∈ degPSFin σ Q L v (charAt μ v) s)
    (h2 : ∀ k ∈ KFin σ Q L v, ∀ g, φ (g * k) = φ g) (h3 : φ 1 = 1)
    {c : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU c n} (he : IsInertChart σ J L h c e) :
    ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV F v) n (locChar μ w) s Φ ∧
      ∀ y, φ (ioH _ σ hQ (y, 1)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) := by
  obtain ⟨f, hK, hio, hP, ha⟩ := GlobalTheory.T.exists_doubling_chart_inert_place F E σ hc n J hJ Q hQ L v w h hw c e he
  refine ⟨fun g => φ (f.symm g), fun p k hk => ?_, fun y => ?_⟩
  · have hp : f.symm p ∈ siegelH (Fv F v) σ Q := (hP _).2 (by rw [f.apply_symm_apply]; exact p.2)
    have hk' : f.symm k ∈ KFin σ Q L v := (hK _).2 (by rwa [f.apply_symm_apply])
    have e1 := (mem_degPSH.1 h1).1 ⟨_, hp⟩ 1
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n p = Units.map (GlobalTheory.LFun.toCompl h).toMonoidHom (aH _ σ Q ⟨_, hp⟩) :=
      (congrArg _ (Subtype.ext (f.apply_symm_apply _).symm)).trans (ha ⟨_, hp⟩ ((hP _).1 hp))
    rw [mul_one, h3, mul_one, GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert F E μ v w h hw, npow_zpow hq _ _ (GlobalTheory.AbsInert.absEv_inert F E σ hc v w h hw _)] at e1
    show φ (f.symm (p * k)) = _
    rw [map_mul, h2 _ hk', e3]
    exact e1
  · show _ = φ (f.symm _)
    rw [← hio y, f.symm_apply_apply]

theorem sphSec_inert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ (v : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χ w → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : (w.adicCompletion D.host.E)ˣ) (e : Gv A v ≃* GU c A.rank), IsUnramInv (ϖ : w.adicCompletion D.host.E) c (qV D.host.F v) → IsInertChart D.sp.cm.sig A.gram L h c e → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr (locChar χ⁻¹ w) ∧ locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ ∧ ((locChar χ⁻¹ w ϖ : ℂˣ) : ℂ) = (-1) ^ b ∧ ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV D.host.F v) A.rank (locChar χ⁻¹ w) s Φ ∧ ∀ y, φ (ioAt A v y) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c A.rank (e y)) := by
  intro D A L hL χ b hχ v w h hw hu s φ hφ c ϖ e hU he
  have h2 : locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ :=
    (hu.inv.locChar_eq_val hU.2.2.2.1).trans (GlobalTheory.LFun.val_inv χ w)
  have hq : qV D.host.F v ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  refine ⟨hu.inv, h2, ?_, exists_isSphSec (isCMExt_host D) (isHermND_gram A) (gram_hdbl A) L hL.1 χ⁻¹ h hw hq
    hφ.1 hφ.2.1 hφ.2.2 he⟩
  rw [h2, ((GlobalTheory.LFun.resEta_iff χ b).1 hχ).val_of_isInertAt (isCMExt_host D).2.2.1 hw hu, ← inv_pow, inv_neg_one]
  simp

end GlobalTheory.KerInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.ItNe

open GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

theorem exists_ne_zero_inclK : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  classical
  intro hHC D V W S S' M M' θ ω pt It hIt h'
  by_contra hcon
  push_neg at hcon
  apply hIt.ne
  have key : ∀ φ (w : ∀ τ, M.H τ) (s : Finset D.what₂.Tau) (v : M'.Vec),
      (∀ τ ∉ s, (v τ : M'.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ) →
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) = 0 := by
    intro φ w s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have e : PiTensorProduct.tprod ℂ v =
          GlobalTheory.Chain.IoLift.inclK h' (PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩) := by
        rw [GlobalTheory.Chain.IoLift.inclK, PiTensorProduct.map_tprod]; rfl
      rw [e, hcon, map_zero, map_zero]
    | insert τ s hτ ih =>
      intro v hv
      obtain ⟨c, hc⟩ := hIt.bdd φ w
      let ℓ₀ : M'.sm τ →ₗ[ℂ] ℂ :=
        (ellT M w ∘ₗ inclT M ∘ₗ It φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
      obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
      have hℓv : ∀ y : M'.sm τ, ℓ (y : M'.H τ) =
          ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := fun y => by
        have := LinearMap.congr_fun hℓ y
        simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
      have hsob : Formalism.L2.Theta.Sobolev₂ (lieAt W τ) (M'.rep τ) ℓ := by
        refine ⟨[[]], c * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, by simp, fun u hu => ?_⟩
        have hy : u ∈ M'.sm τ := Submodule.subset_span hu
        have h1 := hc (Function.update v τ ⟨u, hy⟩)
        rw [← hℓv ⟨u, hy⟩] at h1
        have h2 : ∏ ρ, ‖((Function.update v τ ⟨u, hy⟩ ρ : M'.sm ρ) : M'.H ρ)‖ =
            ‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖ := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun ρ hρ => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
        rw [h2] at h1
        simp only [List.map_cons, List.map_nil, List.foldr_nil, List.sum_cons, List.sum_nil, add_zero]
        calc ‖ℓ u‖ ≤ c * (‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) := h1
          _ = c * (∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) * ‖u‖ := by ring
      have hk : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ, ℓ u = 0 := by
        intro u hu
        have hy : u ∈ M'.sm τ := h' τ hu
        rw [show u = ((⟨u, hy⟩ : M'.sm τ) : M'.H τ) from rfl, hℓv]
        refine ih _ fun ρ hρ => ?_
        by_cases e : ρ = τ
        · subst e; rw [Function.update_self]; exact hu
        · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
      have h0 := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D W S' M' τ ℓ hsob hk (v τ) (v τ).2
      rwa [hℓv, Function.update_eq_self] at h0
  refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
  simp only [LinearMap.zero_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul]
    have h0 : It φ (PiTensorProduct.tprod ℂ v) = 0 := by
      refine (tensorLaw D V S M).inj ?_
      rw [map_zero]
      exact (tensorLaw D V S M).sep _ fun w => key φ w Finset.univ v (by simp)
    rw [h0, smul_zero]
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

end GlobalTheory.Chain.IoLift.ItNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVacStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFockVec_ptOf_of_isVacVec : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  first | exact @GlobalTheory.FockVecOfVac.fock_of_vac | exact GlobalTheory.FockVecOfVac.fock_of_vac | (intros; apply GlobalTheory.FockVecOfVac.fock_of_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineRowTranslationHeisenbergSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineRow_translation_heisenberg_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  first | exact @GlobalTheory.LineRowFrame.line_row | exact GlobalTheory.LineRowFrame.line_row | (intros; apply GlobalTheory.LineRowFrame.line_row <;> assumption)
end


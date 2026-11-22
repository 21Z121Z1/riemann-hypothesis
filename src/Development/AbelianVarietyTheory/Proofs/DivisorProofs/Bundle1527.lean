import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem latEmb_model_of_eq (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ) (hj : InR D j)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD)
    (hp : Dw.p = (D.R.sigW j).1) (hq : Dw.q = (D.R.sigW j).2) (V : HSp D) (hV : V = D.sp.W j) (r : ℕ)
    (hr : V.rank = r) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hL : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (hI : LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀)) :
    Function.Injective ι₀ ∧ Submodule.span D.host.E (Set.range ι₀) = ⊤ ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
        herm (GlobalTheory.RecDict.gmW V hr) (ι₀ x) (ι₀ y)) := by
  subst hV
  subst hr
  have hL' : LatEmb (D.sp.W j) ι₀ := hL
  obtain ⟨ε, hε⟩ : LatIsom (D.sp.W j) Dw.EF ι₀ := hI
  have hsp : Submodule.span D.host.E (Set.range ι₀) = ⊤ := by
    rw [← LinearMap.coe_range, hL'.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D (D.sp.W j) 1).2.1
  let f := ((D.sp.W j).frame.equivFun.symm.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hsp' : Submodule.span D.host.E (Set.range (f ∘ₗ ι₀)) = ⊤ := by
    have : Set.range (f ∘ₗ ι₀) = (D.sp.W j).frame.equivFun.symm.toLinearMap '' Set.range ι₀ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  have h1 : ε = 1 := GlobalTheory.Member.sign_eq_one D H Dw j hj hrt hrt0 hp hq (f ∘ₗ ι₀) ε
    ((D.sp.W j).frame.equivFun.symm.injective.comp hL'.1) hsp' hε
  subst h1
  refine ⟨hL'.1, hsp, (GlobalTheory.Member.isom_iff_model Dw (D.sp.W j) rfl ι₀).1 fun x y => ?_⟩
  rw [hε x y, Units.val_one, Int.cast_one, _root_.one_mul]

set_option maxHeartbeats 2000000 in

theorem model_space_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∀ τ : D.host.E →+* ℂ, τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 → (τ ((T.U j σ).X k).ξ0).im < 0) ∧ ∃ φD : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), Function.Injective φD ∧ Submodule.span D.host.E (Set.range φD) = ⊤ ∧ ∀ x y, (((T.Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm (φD x) (φD y)) := by
  intro D T h j hj σ hσ k
  obtain ⟨hr, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨-, hrt, hrt0, -⟩ := h.pins.1
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨hr', -, -, -, -, -, -, hL, hI, -⟩ := h.adPin j hj σ hσ
  refine ⟨fun τ hτ => ?_, T.iota j, ?_⟩
  · rw [(hW k).2]
    exact GlobalTheory.Member.hostCMType_neg_constant_im_neg D τ (by rw [← hrt0, ← hrt, hτ])
  · rw [(hW k).1, (hW k).2]
    exact latEmb_model_of_eq D T.Q.H (T.Q.Dw j) j hj hrt hrt0 hp hq (T.V j σ) (h.spaceW j hj σ hσ) D.R.r hr
      (T.iota j) hL hI

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSections
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem flatAt_of_simpleAt : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F),
      (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E),
        aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) →
      ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  intro hQ F _ _ X Λ₀ hX δ f Q hS s hs
  have hF : SimpleAt X.toTuple δ f F s := hS F s (by simpa [MvPolynomial.coe_aeval_eq_eval] using hs)
  obtain ⟨E, iE, nE, iFE, iEE, htow, hsp⟩ := GlobalTheory.HSCore.exists_split F X.toTuple F s hF.good
  have heq : (fun i k => @algebraMap F E _ _ iEE (s i k)) = fun i k => @algebraMap F E _ _ iFE (s i k) := by
    funext i k
    rw [@IsScalarTower.algebraMap_apply F F E _ _ _ _ iEE iFE htow (s i k)]
    rfl
  rw [heq] at hsp
  clear heq htow iEE
  have hval : aeval (fun p : Fin X.D × Fin X.N => algebraMap F E (s p.1 p.2)) Q =
      algebraMap F E (eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q) := by
    exact (MvPolynomial.eval₂_comp_left (algebraMap F E) (RingHom.id F) _ Q).symm
  have hSE : SimpleAt X.toTuple δ f E (fun i k => algebraMap F E (s i k)) :=
    hS E _ (by rw [hval]; exact (map_ne_zero _).2 hs)
  have hgood : (X.baseChange E).IsGood (fun i k => algebraMap F E (s i k)) := Geo.isGood_baseChange_iff.2 hSE.good
  obtain ⟨Co, c, hc, hspec⟩ := GlobalTheory.T.exists_coordinates_specialisedForm_prod_linearForms F X.toGeo E _ hgood δ f hsp hSE
  have hnef₂ := nef_big_second_baseChange F X E hX.nef₂ hX.big₂
  have hnefA := GlobalTheory.HSCore.nef_big_baseChange F X E hX.nef hX.big
  have hms : (X.baseChange E).MulStable :=
    (GlobalTheory.HilbertSamuel.Data.complexify_statement F X (fun _ => X.beta) hX.totallyComplex
      (fun _ => one_pos.trans_le X.one_le_beta) hX.mulStable hX.mulBound).2 E
  have hFM : FilMono := GlobalTheory.HSCore.filMono_of_kerRes (GlobalTheory.HSKerRes.kerRes hQ)
  obtain ⟨hind, hmul, hspan⟩ := GlobalTheory.T.hilbertSamuelSectionBaseChange_properties F X Λ₀ E
  obtain ⟨hcomm, -, -⟩ := GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial E (X.toGeo.baseChange E)
  have honto := GlobalTheory.T.hilbertSamuelDegreeZeroResidues_range_eq_top hQ E (X.baseChange E) _ hgood δ Co hnef₂.1 hnef₂.2
  have hker := totFil_totSym_ker E (X.baseChange E) _ hgood δ Co
  have hmono := GlobalTheory.T.hilbertSamuelFiltrationSymbol_monomial_product E (X.baseChange E) _ hgood δ Co hms
  have hdiv := GlobalTheory.T.hilbertSamuelVanishingFiltration_deepest_step_span hFM E (X.baseChange E) _ hgood hnefA.1 hnefA.2 hms
  let Φ : (sysOf X Λ₀).Flat E (Tot (X.toGeo.baseChange E)) (fun i k => algebraMap F E (s i k)) δ :=
    { ι := totExt X.toGeo E
      indep := hind
      mul := shift (X.toGeo.baseChange E)
      comm := hcomm
      mul_ι := hmul
      y := Co.y
      y_ne := Co.y_ne
      res := totRes (X := X.baseChange E) Co
      onto := by rw [hspan 0]; exact honto
      U := totFil (X.baseChange E) (fun i k => algebraMap F E (s i k))
      sym := totSym (X := X.baseChange E) Co
      le := fun a ha => (hker a ha).1
      ker := fun a ha => (hker a ha).2
      mono := fun a ha α l m hm => hmono a ha α l m (by rw [hspan 0] at hm; exact hm)
      div := by rw [hspan]; exact hdiv }
  exact ⟨E, Tot (X.toGeo.baseChange E), inferInstance, inferInstance, inferInstance, inferInstance, Φ, c, hc, hspec⟩

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
section
set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

noncomputable section

namespace GlobalTheory.FactorDepth.Extension

attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tanEquiv {V : Type} [CommRing V] {X0 : Scheme.{0}} {t : SAB H X0} {x : Sp V ⟶ X0} {G : SAB H (Sp V)}
    (m : SABMap G t x) :
    ∃ B : (epsOver V V ⟶ G.G) ≃* (tEpsG x ⟶ t.G), (∀ v, (B v).left = v.left ≫ m.φ) ∧
      (∀ v, IsTanAtG t x (B v).left ↔ IsTan v) ∧
      (∀ v (a : 𝓞 E) (r : V), (B v).left ≫ (t.act.act a).left = spMap (epsMul r) ≫ (B v).left ↔
        (v ≫ G.act.act a).left = spMap (epsMul r) ≫ v.left) ∧
      ∀ (n : ℕ) (v : Fin n → (epsOver V V ⟶ G.G)) a w,
        IsCombAtG t x (fun i => (B (v i)).left) a (B w).left ↔ IsComb v a w := by
  have h := m.cart
  have hid : spMap (algebraMap V V) = 𝟙 _ := Spec.map_id _
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h
    (spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)))
    (spMap (algebraMap V (DualNumber V)) ≫ x) rfl
  obtain ⟨A, hA⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (spMap (algebraMap V V)) x
    (by rw [hid, Category.id_comp])
  have hw : ∀ v : epsOver V V ⟶ G.G, v.left ≫ G.G.hom = spMap (algebraMap V (DualNumber V)) := fun v => Over.w v
  have sc : ∀ (a : V) (u v : epsOver V V ⟶ G.G),
      (B u).left = spMap (epsMul a) ≫ (B v).left ↔ u.left = spMap (epsMul a) ≫ v.left := by
    intro a u v
    rw [hB, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [e, Category.assoc]) ?_, fun e => by rw [e, Category.assoc]⟩
    rw [Category.assoc, hw, hw, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
  have prod : ∀ (n : ℕ) (u : Fin n → (epsOver V V ⟶ G.G)),
      B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
    intro n u
    rw [map_list_prod, List.map_ofFn]
    rfl
  refine ⟨B, hB, fun v => ?_, fun v a r => ?_, fun n v a w => ?_⟩
  · unfold IsTanAtG IsTan
    refine (and_iff_right (Over.w (B v))).trans ?_
    rw [← map_one A, hA, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [← e, Category.assoc]) ?_, fun e => by rw [← e, Category.assoc]⟩
    rw [Category.assoc, hw, GlobalTheory.Exist.FlagBaseChange.fst_over]
    exact ((Over.w (1 : ptOver V V ⟶ G.G)).trans hid).symm
  · have e : (B v).left ≫ (t.act.act a).left = (B (v ≫ G.act.act a)).left := by
      rw [hB, hB, Over.comp_left, Category.assoc, Category.assoc, m.act]
    rw [e]
    exact sc _ _ _
  · constructor
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => B.symm (u i), fun i => (sc _ _ _).1 (by rw [B.apply_symm_apply]; exact hu i), B.injective ?_⟩
      rw [prod, ← Over.OverMorphism.ext e]
      simp
    · rintro ⟨u, hu, e⟩
      exact ⟨fun i => B (u i), fun i => (sc _ _ _).2 (hu i), by rw [e, prod]⟩

end GlobalTheory.FactorDepth.Extension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
section
noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev locAt (w : HeightOneSpectrum (𝓞 K)) (g : GA K n) : GL (Fin n) (w.adicCompletion K) :=
  GeneralLinearGroup.map (pLoc K w) (gFin g)

theorem continuous_locAt (w : HeightOneSpectrum (𝓞 K)) : Continuous (locAt (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp
    (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin K))))

theorem isClopen_Ov (w : HeightOneSpectrum (𝓞 K)) : IsClopen (Formalism.UG.Ov K w : Set (w.adicCompletion K)) :=
  ⟨GroundTheory.Global.isClosed_adicCompletionIntegers w, GroundTheory.Global.isOpen_adicCompletionIntegers w⟩

theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

theorem isClopen_KGL_entries (w : HeightOneSpectrum (𝓞 K)) :
    IsClopen {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} := by
  have : {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} =
      ⋂ i, ⋂ j, (fun g : GA K n => (locAt w g).val i j) ⁻¹' (Formalism.UG.Ov K w : Set (w.adicCompletion K)) := by
    ext g; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    (isClopen_Ov w).preimage ((continuous_apply_apply i j).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion K))).comp (continuous_locAt w)))

theorem isClopen_KGL_inv_entries (w : HeightOneSpectrum (𝓞 K)) :
    IsClopen {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} := by
  have : {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} =
      ⋂ i, ⋂ j, (fun g : GA K n => ((locAt w g)⁻¹).val i j) ⁻¹' (Formalism.UG.Ov K w : Set (w.adicCompletion K)) := by
    ext g; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    (isClopen_Ov w).preimage ((continuous_apply_apply i j).comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (w.adicCompletion K))).comp (continuous_locAt w)))

theorem isClopen_KGL (w : HeightOneSpectrum (𝓞 K)) :
    IsClopen {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} := by
  have : {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} =
      {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} ∩
        {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} := by
    ext g; exact mem_KGL_iff w _
  rw [this]
  exact (isClopen_KGL_entries w).inter (isClopen_KGL_inv_entries w)

theorem finite_not_KGL (g : GA K n) : {w : HeightOneSpectrum (𝓞 K) | locAt w g ∉ GlobalTheory.LFun.KGL w n}.Finite := by
  let y := gFin g
  have hf : ∀ x : Af K, {w : HeightOneSpectrum (𝓞 K) | ¬ x w ∈ w.adicCompletionIntegers K}.Finite :=
    fun x => Filter.eventually_cofinite.1 x.2
  refine ((Set.finite_iUnion fun i => Set.finite_iUnion fun j => (hf (y.val i j)).union (hf ((y⁻¹).val i j)))).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, not_exists, not_or, not_not] at hc
  apply hw
  rw [mem_KGL_iff]
  refine ⟨fun i j => (hc i j).1, fun i j => ?_⟩
  rw [← map_inv]
  exact (hc i j).2

theorem det_mem_Ov (w : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) (w.adicCompletion K))
    (h : ∀ i j, M i j ∈ Formalism.UG.Ov K w) : M.det ∈ Formalism.UG.Ov K w := by
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h i j⟩
  have hM : M'.map (Formalism.UG.Ov K w).subtype = M := by ext i j; rfl
  have e : (M'.map (Formalism.UG.Ov K w).subtype).det = (Formalism.UG.Ov K w).subtype M'.det :=
    (RingHom.map_det (Formalism.UG.Ov K w).subtype M').symm
  rw [← hM, e]
  exact (M'.det).2

theorem mul_mem_Ov (w : HeightOneSpectrum (𝓞 K)) (M N : Matrix (Fin n) (Fin n) (w.adicCompletion K))
    (hM : ∀ i j, M i j ∈ Formalism.UG.Ov K w) (hN : ∀ i j, N i j ∈ Formalism.UG.Ov K w) :
    ∀ i j, (M * N) i j ∈ Formalism.UG.Ov K w := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

theorem norm_eq_inv_pow (w : HeightOneSpectrum (𝓞 K)) {x : w.adicCompletion K} (h0 : x ≠ 0)
    (hx : x ∈ Formalism.UG.Ov K w) : ∃ k : ℕ, ‖x‖ = ((Ideal.absNorm w.asIdeal : ℝ) ^ k)⁻¹ := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hle : Valued.v x ≤ 1 := hx
  have he : Valued.v x = ((Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero hv)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := by
    rw [ofAdd_toAdd, WithZero.coe_unzero]
  have hm : Multiplicative.toAdd (WithZero.unzero hv) ≤ 0 := by
    rw [he] at hle
    exact_mod_cast hle
  refine ⟨(-Multiplicative.toAdd (WithZero.unzero hv)).toNat, ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow, NNReal.coe_natCast,
    ← zpow_natCast, ← _root_.zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]

theorem norm_eq_one_of_mem_KGL (w : HeightOneSpectrum (𝓞 K)) {a : GL (Fin n) (w.adicCompletion K)}
    (ha : a ∈ GlobalTheory.LFun.KGL w n) : ‖a.val.det‖ = 1 := by
  obtain ⟨h1, h2⟩ := (mem_KGL_iff w a).1 ha
  have d1 : ‖a.val.det‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (det_mem_Ov w _ h1)
  have d2 : ‖(a⁻¹).val.det‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (det_mem_Ov w _ h2)
  have hp : ‖a.val.det‖ * ‖(a⁻¹).val.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  nlinarith [norm_nonneg a.val.det, norm_nonneg (a⁻¹).val.det]

theorem shell_mul_of (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (y a b : GL (Fin n) (w.adicCompletion K))
    (ha : a ∈ GlobalTheory.LFun.KGL w n) (hb : b ∈ GlobalTheory.LFun.KGL w n) (hy : y ∈ Shell w n k) : a * y * b ∈ Shell w n k := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact mul_mem_Ov w _ _ (mul_mem_Ov w _ _ ((mem_KGL_iff w a).1 ha).1 hy.1) ((mem_KGL_iff w b).1 hb).1
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
      norm_eq_one_of_mem_KGL w ha, norm_eq_one_of_mem_KGL w hb, one_mul, mul_one]
    exact hy.2

theorem shell_exists_unique (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K))
    (hy : ∀ i j, y.val i j ∈ Formalism.UG.Ov K w) : ∃! k, y ∈ Shell w n k := by
  obtain ⟨k, hk⟩ := norm_eq_inv_pow w (Matrix.isUnits_det_units y).ne_zero (det_mem_Ov w _ hy)
  refine ⟨k, ⟨hy, hk⟩, fun k' hk' => ?_⟩
  have e := hk'.2.symm.trans hk
  rw [_root_.inv_inj, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_inj] at e
  exact Nat.pow_right_injective (HeightOneSpectrum.one_lt_absNorm w) e

theorem main : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ),
    (∀ g h : GA K n, absDet (g * h) = absDet g * absDet h) ∧ (∀ g : GA K n, 0 < absDet g) ∧
    Continuous (absDet : GA K n → ℝ) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), IsClopen {g : GA K n | IntAt w (gFin g)} ∧
      IsClopen {g : GA K n | GeneralLinearGroup.map (pLoc K w) (gFin g) ∈ GlobalTheory.LFun.KGL w n}) ∧
    (∀ S : Set (HeightOneSpectrum (𝓞 K)), IsClosed {g : GA K n | UnitOff S (gFin g)}) ∧
    (∀ g : GA K n, {w | GeneralLinearGroup.map (pLoc K w) (gFin g) ∉ GlobalTheory.LFun.KGL w n}.Finite) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)),
      (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) → ∃! k, y ∈ Shell w n k) ∧
    ∀ (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (y a b : GL (Fin n) (w.adicCompletion K)),
      a ∈ GlobalTheory.LFun.KGL w n → b ∈ GlobalTheory.LFun.KGL w n → (a * y * b ∈ Shell w n k ↔ y ∈ Shell w n k) := by
  intro K _ _ n
  refine ⟨fun g h => ?_, fun g => (Reduction.detModule K n g).2, ?_, fun w => ⟨isClopen_KGL_entries w, isClopen_KGL w⟩,
    fun S => ?_, finite_not_KGL, shell_exists_unique, fun w k y a b ha hb => ⟨fun h => ?_, shell_mul_of w k y a b ha hb⟩⟩
  · simp only [absDet, map_mul, Positive.val_mul]
  · exact continuous_subtype_val.comp Reduction.continuous_detModule
  · have : {g : GA K n | UnitOff S (gFin g)} = ⋂ w, ⋂ (_ : w ∉ S), {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} := by
      ext g; simp only [UnitOff, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun w => isClosed_iInter fun _ => (isClopen_KGL w).isClosed
  · have e := shell_mul_of w k (a * y * b) a⁻¹ b⁻¹ (inv_mem ha) (inv_mem hb) h
    rwa [show a⁻¹ * (a * y * b) * b⁻¹ = y by group] at e

end GlobalTheory.HenQ.Basic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

def sz (u v : ℕ) (i j : Bool) : ℕ := cond i (cond j v 1) (cond j u 0)

def sigTwo (b : Bool → ℕ) (x y : ℕ) (h0 : b false = x) (h1 : b true = y) :
    (Σ j, Fin (b j)) ≃ Σ j, Two (Fin x) (Fin y) j :=
  Equiv.sigmaCongrRight fun j => match j with
    | false => finCongr h0
    | true => finCongr h1

def rowPart (u v : ℕ) : ∀ i, (Σ j, Fin (sz u v i j)) ≃ Two (Fin u) (Fin (v + 1)) i
  | false => (sigTwo (sz u v false) 0 u rfl rfl).trans (two (stdSum (Nat.zero_add u)))
  | true => (sigTwo (sz u v true) 1 v rfl rfl).trans (two (stdSum (Nat.add_comm 1 v)))

def colPart (u v : ℕ) : ∀ j, (Σ i, Fin (sz u v i j)) ≃ Two (Fin 1) (Fin (u + v)) j
  | false => (sigTwo (fun i => sz u v i false) 0 1 rfl rfl).trans (two (stdSum (Nat.zero_add 1)))
  | true => (sigTwo (fun i => sz u v i true) u v rfl rfl).trans (two (stdSum rfl))

theorem eq_sz {u v : ℕ} (b : Bool → Bool → ℕ)
    (hb : (∀ i, ∑ j, b i j = Fintype.card (Two (Fin u) (Fin (v + 1)) i)) ∧
      ∀ j, ∑ i, b i j = Fintype.card (Two (Fin 1) (Fin (u + v)) j)) (h : b true false = 1) :
    b = sz u v := by
  have r0 := hb.1 false
  have r1 := hb.1 true
  have c0 := hb.2 false
  have c1 := hb.2 true
  simp only [Fintype.sum_bool] at r0 r1 c0 c1
  have e0 : Fintype.card (Two (Fin u) (Fin (v + 1)) false) = u := Fintype.card_fin u
  have e1 : Fintype.card (Two (Fin u) (Fin (v + 1)) true) = v + 1 := Fintype.card_fin _
  have e2 : Fintype.card (Two (Fin 1) (Fin (u + v)) false) = 1 := Fintype.card_fin _
  have e3 : Fintype.card (Two (Fin 1) (Fin (u + v)) true) = u + v := Fintype.card_fin _
  rw [e0] at r0
  rw [e1] at r1
  rw [e2] at c0
  rw [e3] at c1
  funext i j
  cases i <;> cases j <;> simp only [sz, cond_true, cond_false] <;> omega

def extTensorEquiv {G H V W V' W' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W} {ρ' : Representation ℂ G V'}
    {σ' : Representation ℂ H W'} (φ : ρ.Equiv ρ') (ψ : σ.Equiv σ') :
    (extTensor ρ σ).Equiv (extTensor ρ' σ') :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (ψ.toIntertwiningMap.isIntertwining _ _ g.2 w)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def colChar (v : ℕ) (χ₂ : kˣ →* ℂˣ) (j : Bool) : kˣ →* ℂˣ :=
  χ₂ * absPow k (cond j (1 / 2) (-(v : ℂ) / 2))

def colRep (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (j : Bool) :
    Representation ℂ (Levi k fun i => Fin (sz u v i j)) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (sz u v false j)) χ₁) (detRep (Fin (sz u v true j)) (colChar v χ₂ j))).comp
    ((Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) false).prod
      (Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) true))

theorem isSmooth_colRep {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ) (j : Bool) :
    IsSmooth (colRep χ₁ χ₂ u v j) := by
  refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 (h₂.mul (GlobalTheory.LocGL.isSmoothChar_absPow _)).detChar)) _ ?_
  exact (continuous_apply false).prodMk (continuous_apply true)

end GlobalTheory.SmGL.RowOneCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwoPlaneFrame
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.PlaneTwo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def IsTwoPlaneFrame {n n₁ n₂ : ℕ} (Y : Spc F E n) (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (c : E) {r : ℕ} (h1 : 1 < r)
    (Xf Yf : Matrix (Fin n) (Fin r) E) : Prop :=
  IsWittFrame σ (c • Y.J.map σ) Xf Yf ∧ (fun k => Xf k ⟨0, by omega⟩) = H₁.x ∧ (fun k => Xf k ⟨1, h1⟩) = xTwo H₁ H₂ ∧
    (fun k => Yf k ⟨0, by omega⟩) = c⁻¹ • H₁.y ∧ (fun k => Yf k ⟨1, h1⟩) = c⁻¹ • yTwo H₁ H₂

end GlobalTheory.ThK.DescB.PlaneTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumPolynomialBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_polynomial_bound : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (q : ℕ) (blk : Fin q → Finset κ)
    (A N₀ : ℕ) (c : ℝ), 0 < c → ∃ (N : ℕ) (C : ℝ) (K : ℕ), ∀ (m : ℕ) (t : Fin q → ℝ), 1 ≤ m → (∀ i, c ≤ t i) →
      Summable (latG (F := F) blk A N m t) ∧ (∑' ξ, latG (F := F) blk A N m t ξ) * (1 + ∏ i, t i) ^ N₀ ≤ C * (m : ℝ) ^ K := by
  first | exact @GlobalTheory.ThKTorusLatSum.latG_tsum_le | exact GlobalTheory.ThKTorusLatSum.latG_tsum_le | (intros; apply GlobalTheory.ThKTorusLatSum.latG_tsum_le <;> assumption)
end


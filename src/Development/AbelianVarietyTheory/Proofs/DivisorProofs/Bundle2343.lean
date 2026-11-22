import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvrStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralEigenBasis_transport_pullback_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (G : SAB H (Sp T.V)) (S : Scheme.{0}) (t : SAB H S) (x : Sp T.V ⟶ S) (n : SABMap G t x) (τ : E →+* ℂ) (k : ℕ) (ub : Fin k → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i, IsEigV c io G τ (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin k → T.V, IsComb ub a w) → ∃ v : Fin k → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt x ⟶ t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis t.act x (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (v i).left = (ub i).left ≫ n.φ := by
  first | exact @GlobalTheory.IntEigTransport.transport | exact GlobalTheory.IntEigTransport.transport | (intros; apply GlobalTheory.IntEigTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelDomainOverInclusionStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_domain_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → (∀ a : c'.V W, a ≠ 0 → IsUnit (β a)) → ∀ (T₀ : CDVR) (α : A →+* T₀.V), Function.Injective α → ∀ yy₀ : Sp T₀.Fr ⟶ Xo'.XF c', yy₀ ≫ Y.j = spMap ((algebraMap T₀.V T₀.Fr).comp α) ≫ ξ → ∃ (T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr), (∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) ∧ Function.Injective i ∧ IsLocalHom i ∧ ∃ (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = spMap iF ≫ yy₀ ≫ r) := by
  first | exact @GlobalTheory.ModelIntFr.exists_intFr_of_modelPt | exact GlobalTheory.ModelIntFr.exists_intFr_of_modelPt | (intros; apply GlobalTheory.ModelIntFr.exists_intFr_of_modelPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelEmbeddingFirst
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.EigLift

theorem one_left_comp {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk _ hw
  have h2 := h.2 T 1 1 x₀ x₀ rfl rfl
  have h3 : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one]
    rfl
  have h4 : x₀ = 1 := by simpa using h3
  exact congrArg CommaMorphism.left h4

theorem comp_prod {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (z : X ⟶ Y) (L : List (Y ⟶ G)) :
    z ≫ L.prod = (L.map (z ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one z
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem sp_fst_alg (K : Type) [CommRing K] :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
  rw [← sp_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
    ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  simp [spMap]

theorem sp_fst_eps {K : Type} [CommRing K] (q : K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsMul q) = spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
  rw [← sp_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (epsMul q) = (TrivSqZeroExt.fstHom K K K).toRingHom := by
    apply RingHom.ext; intro x
    show (epsMul q x).fst = x.fst
    simp [epsMul]
  rw [this]

theorem sp_eps_alg {K : Type} [CommRing K] (q : K) :
    spMap (epsMul q) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
  rw [← sp_comp]
  have : (epsMul q).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber K) := by
    apply RingHom.ext; intro x
    show epsMul q (algebraMap K (DualNumber K) x) = _
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]

end GlobalTheory.FlatModel.EigLift

namespace GlobalTheory.FlatModel.EigLift

theorem char_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l' : Level H}
    {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F) (hI : OverIncl r hle)
    (σ : E →+* ℂ) {A : Type} [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A) (hβ : ξ ≫ Y.s = spMap β)
    {K : Type} [CommRing K] (φ : A →+* K) (io : c.F →+* K) (yy : Sp K ⟶ Xo'.XF c')
    (hyy : yy ≫ Y.j = spMap φ ≫ ξ) (hio : yy ≫ r ≫ pullback.snd _ _ = spMap io) (a : 𝓞 E) :
    φ (β (embV c' W σ a)) = io (embK c σ a) := by
  set κ : c'.F →+* K := (Spec.preimage (yy ≫ pullback.snd _ _)).hom with hκdef
  have hκ : spMap κ = yy ≫ pullback.snd _ _ := by
    simp only [spMap, hκdef, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : spMap (κ.comp (c'.V W).subtype) = spMap (φ.comp β) := by
    rw [sp_comp, sp_comp, hκ, Category.assoc, ← hjs, ← Category.assoc, hyy, Category.assoc, hβ]
  have h2 : spMap (κ.comp (IntermediateField.inclusion hle).toRingHom) = spMap io := by
    rw [sp_comp, hκ, Category.assoc, ← hI, hio]
  have k1 : κ.comp (c'.V W).subtype = φ.comp β := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h1)
    simpa using this
  have k2 : κ.comp (IntermediateField.inclusion hle).toRingHom = io := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h2)
    simpa using this
  calc φ (β (embV c' W σ a)) = κ ((embV c' W σ a : c'.V W) : c'.F) := (RingHom.congr_fun k1 _).symm
    _ = κ (IntermediateField.inclusion hle (embK c σ a)) := congrArg κ (Subtype.ext rfl)
    _ = io (embK c σ a) := RingHom.congr_fun k2 _

end GlobalTheory.FlatModel.EigLift

namespace GlobalTheory.FlatModel

open EigLift in

theorem lift_tan_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g m : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U : Fin m → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ (k : Fin m) (w : Sp (DualNumber K) ⟶ Y.oF.t.G.left), IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U k b)) (w ≫ Y.m.φ) → (letI := io.toAlgebra; IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hI σ A _ ξ β hβ g m e U hB hEig K _ φ io y yy hyy hpt k w hw
  letI := io.toAlgebra
  haveI : IsOpenImmersion Y.j := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  have hc := Y.m.cart.1
  have hcw : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := hc.w
  have hνw : ν.φ ≫ Xo.univ.t.G.hom = Y.oF.t.G.hom ≫ r ≫ pullback.fst _ _ := ν.cart.1.w
  have hx : y.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt, GlobalTheory.AllWt.ptF, pullback.lift_fst]
  have hio : yy ≫ r ≫ pullback.snd _ _ = spMap io := by
    rw [← Category.assoc, ← hpt, GlobalTheory.AllWt.ptF, pullback.lift_snd]
  have hχ : ∀ a, φ (β (embV c' W σ a)) = io (embK c σ a) := fun a =>
    char_eq Y r hle hI σ ξ β hβ φ io yy hyy hio a
  obtain ⟨u, hu, hwu⟩ := hw
  have hwb : w ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ yy := by
    rw [← cancel_mono Y.j, Category.assoc, ← hcw, ← Category.assoc, ← hwu, Over.w, Category.assoc]
    rfl
  have hT : ∀ i, IsTanAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e i) := by
    rw [hyy]
    exact (isTanBasis_bc hB φ).1
  have hz : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (tEpsG (yy ≫ Y.j)).hom = (Over.mk (yy ≫ Y.j)).hom := by
    show spMap _ ≫ spMap (algebraMap K (DualNumber K)) ≫ yy ≫ Y.j = yy ≫ Y.j
    rw [← Category.assoc, sp_fst_alg, Category.id_comp]
  let z : Over.mk (yy ≫ Y.j) ⟶ tEpsG (yy ≫ Y.j) := Over.homMk _ hz
  have hzu : ∀ i, z ≫ u i = 1 := fun i => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hu i, ← Category.assoc]
    show (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsMul _)) ≫ _ = _
    rw [sp_fst_eps]
    exact (hT i).2
  have hprod : z ≫ (List.ofFn u).prod = 1 := by
    rw [comp_prod, List.map_ofFn]
    have : ((z ≫ ·) ∘ u) = fun _ => 1 := funext hzu
    rw [this]
    simp
  have h0 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w ≫ Y.m.φ = (1 : Over.mk (yy ≫ Y.j) ⟶ Y.t.G).left := by
    rw [← hwu, ← hprod]
    rfl
  have hw0 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left := by
    apply hc.hom_ext
    · rw [Category.assoc, h0, one_left_comp Y.m.cart (Over.mk yy)]
      rfl
    · rw [Category.assoc, hwb, ← Category.assoc, sp_fst_alg, Category.id_comp, Over.w]
      rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hνw, ← Category.assoc, hwb, hx]
    simp only [Category.assoc]
  · rw [← Category.assoc, hw0, one_left_comp ν.cart (Over.mk yy), hx]
  · intro a
    have hE : IsEigG Y.t (φ.comp (β.comp (embV c' W σ))) (w ≫ Y.m.φ) :=
      hEig K φ k (w ≫ Y.m.φ) (by rw [← hyy]; exact ⟨u, hu, hwu⟩)
    have key : w ≫ (Y.oF.t.act.act a).left = spMap (epsMul (io (embK c σ a))) ≫ w := by
      apply hc.hom_ext
      · rw [Category.assoc, Category.assoc, Y.m.act a, ← Category.assoc, hE a]
        simp only [RingHom.comp_apply, hχ a, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w, hwb, ← Category.assoc, sp_eps_alg]
    show w ≫ ν.φ ≫ _ = spMap (epsMul (io (embK c σ a))) ≫ w ≫ ν.φ
    rw [← ν.act a, ← Category.assoc, key, Category.assoc]

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerFrameStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power_frame : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∃ (ta : Fin N → P.T) (w₁ : Fin (Dw.mult τ.1) → P.V) (w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V)
        (σ : Equiv.Perm (Ind Dw τ.1)),
        (∀ m, ((ta m).lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left) ∧
        (∀ k, w₁ k ∈ htLat c P τ.1 ∧ w₁ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₁ k ∈ P.eigV (embInt c P.integers τ.1)) ∧
        (∀ k, w₂ k ∈ htLat c P (conjEmb τ.1) ∧ w₂ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₂ k ∈ P.eigV (embInt c P.integers (conjEmb τ.1))) ∧
        ‖(Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 ∧
        ‖(Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 := by
  first | exact @GlobalTheory.FlatModel.htAt_dualFam_frame | exact GlobalTheory.FlatModel.htAt_dualFam_frame | (intros; apply GlobalTheory.FlatModel.htAt_dualFam_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapCompatibilityStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_compatibility : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v → SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v' → v = v' := by
  first | exact @GlobalTheory.FlatModel.secValAt_unique_generic | exact GlobalTheory.FlatModel.secValAt_unique_generic | (intros; apply GlobalTheory.FlatModel.secValAt_unique_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapOverInclusion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_discr_smul_eigen_mem_span_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
      ∃ x : Fin g → LieG P.Gt, (∀ b, ITie P π (x b) (e b)) ∧
        ∀ (σ : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ)) e U →
        ∀ x' : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x' →
        ∃ M : Fin g → 𝓞_ℂ_[p], ((discr E : ℤ) : ℂ_[p]) • P.bLie x' =
          ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
  intro E _ _ _ H Dw p _ _ l l' Xo Xo' c c' W Y r ν hle hOI _ yb yy P π ψ y hHT β hβ g e hB
  have hPt : PtOn Y yb yy P π ψ := hHT.1
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.p_adic_point_pairing_compatible E H Dw p l' Xo' c' W Y yb yy P π ψ hPt
  choose x hx using fun b => (h1 (e b) (hB.1 b)).exists
  refine ⟨x, hx, ?_⟩
  intro σ U hEig x' hx'
  obtain ⟨u', hu'T, hu'X⟩ := h2 x'
  have hemb := GlobalTheory.FlatModel.htAt_embV_eq E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p yb yy P π ψ y hHT β hβ σ
  have hEG : IsEigG Y.t (β.comp (embV c' W σ)) u' := by
    rw [hemb]
    exact (h4 _ x' u' hu'T hu'X).2 hx'
  have hid : spMap (RingHom.id 𝓞_ℂ_[p]) ≫ yb = yb := by
    rw [show spMap (RingHom.id 𝓞_ℂ_[p]) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  have hdual : (fun i => spMap (dualMap (RingHom.id 𝓞_ℂ_[p])) ≫ e i) = e := by
    have : dualMap (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
      ext s <;> simp [dualMap]
    funext i
    rw [this, show spMap (RingHom.id (DualNumber 𝓞_ℂ_[p])) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨w, hw, -⟩ := hB.2 𝓞_ℂ_[p] (RingHom.id _) u' (by rw [hid]; exact hu'T)
  rw [hid, hdual] at hw
  have hL := h3 g e x w u' x' hB.1 hx hw hu'X
  have hmem := hEig.2 w u' hw hEG
  obtain ⟨M, hM⟩ := (Submodule.mem_span_range_iff_exists_fun 𝓞_ℂ_[p]).1 hmem
  refine ⟨M, ?_⟩
  have hcoord : ∀ b, ((discr E : ℤ) : 𝓞_ℂ_[p]) * w b = ∑ k, M k * U k b := by
    intro b
    have := congrFun hM b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  rw [hL, Finset.smul_sum]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) (hcoord b)
  exact_mod_cast this

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherianStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_open_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X), IsOpenImmersion ξ → IsNoetherianRing A := by
  first | exact @GlobalTheory.ModelNoeth.isNoetherianRing_of_isOpenImmersion | exact GlobalTheory.ModelNoeth.isNoetherianRing_of_isOpenImmersion | (intros; apply GlobalTheory.ModelNoeth.isNoetherianRing_of_isOpenImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPointOverInclusion
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.GenChartAlg

theorem exists_algebra_of_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L), (yL ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c L ∧
      (∀ z : FrPt Xo c L, z.x = yL ≫ r ≫ pullback.fst _ _ → ptF z = yL ≫ r) ∧
      ∀ (σ : E →+* ℂ) (a : 𝓞 E), algebraMap c.F L (embK c σ a) = io (β (embV c' W σ a)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r hle hr A _ ξ β hβ L _ io yL hyL
  obtain ⟨f', hf'⟩ : ∃ f' : c'.F →+* L, yL ≫ pullback.snd _ _ = spMap f' :=
    ⟨(Spec.preimage (yL ≫ pullback.snd _ _)).hom, by simp [spMap]⟩
  letI alg : Algebra c.F L := (f'.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hsnd : yL ≫ r ≫ pullback.snd _ _ = spMap (algebraMap c.F L) := by
    rw [hr, ← Category.assoc, hf']
    simp only [spMap, ← Spec.map_comp]
    rfl
  have e1 : yL ≫ Y.j ≫ Y.s = spMap (io.comp β) := by
    rw [← Category.assoc, hyL, Category.assoc, hβ]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have e2 : yL ≫ Y.j ≫ Y.s = spMap (f'.comp (c'.V W).subtype) := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hf']
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : f'.comp (c'.V W).subtype = io.comp β := by
    have h := e2.symm.trans e1
    simp only [spMap] at h
    have h2 := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨alg, ?_, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc r, ← Category.assoc yL, hsnd]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  · intro z hz
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hz, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hsnd]
  · intro σ a
    exact RingHom.congr_fun key (embV c' W σ a)

end GlobalTheory.GenChartAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_mul_sumI | exact GlobalTheory.MBLow.TanExp.value_mul_sumI | (intros; apply GlobalTheory.MBLow.TanExp.value_mul_sumI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (q : W.Z ⟶ Y.X) [IsDominant q] (y : Fin (Y.dim + 1) → CartierDiv W.Z) (e : Fin (Y.dim + 1) → Y.Dv), (∀ i, IsPull q (y i) (e i)) → W.num y = 0 := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull | exact GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull | (intros; apply GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  first | exact @GlobalTheory.loc_units_eq | exact GlobalTheory.loc_units_eq | (intros; apply GlobalTheory.loc_units_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensionalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  first | exact @GlobalTheory.RestrictDVR.main | exact GlobalTheory.RestrictDVR.main | (intros; apply GlobalTheory.RestrictDVR.main <;> assumption)
end


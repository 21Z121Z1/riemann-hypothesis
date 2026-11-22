import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.RecSpan

open GlobalTheory.HTLat.OmegaRank

theorem exists_eigenbasis {V O : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing O]
    [Algebra V O] [Module.Flat V O] (G : Over (Sp V)) [GrpObj G] [Smooth G.hom] {Λ : Type} (act : Λ → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (χ : Λ → V) {m : ℕ} (u : Fin m → (epsOver V V ⟶ G)) (ht : ∀ i, IsTan (u i))
    (he : ∀ i a, (u i ≫ act a).left = spMap (epsMul (χ a)) ≫ (u i).left)
    (hb : ∀ w : epsOver V V ⟶ G, IsTan w → (∀ a, (w ≫ act a).left = spMap (epsMul (χ a)) ≫ w.left) →
      ∃! c : Fin m → V, IsComb u c w)
    {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (spMap (algebraMap V O)) π)
    (act' : Λ → (G' ⟶ G')) (ha : ∀ a, (act' a).left ≫ π = π ≫ (act a).left) :
    ∃ u' : Fin m → (specO O (DualNumber O) ⟶ G'),
      (∀ i, (u' i).left ≫ π = spMap (dualMap (algebraMap V O)) ≫ (u i).left) ∧
      ∀ w : LieG G', (∀ a, w.1 ≫ act' a = ptMap (dualScale (algebraMap V O (χ a))) ≫ w.1) →
        ∃ c : Fin m → O, w.1 = (List.ofFn fun i => ptMap (dualScale (c i)) ≫ u' i).prod := by
  obtain ⟨u', -, -, h3, h4⟩ := PlaceInt.Ext.exists_eigenbasis_pullback (V' := O) G act χ u ht he hb
  obtain ⟨e, he, he'⟩ := grpPullback_iso hπ (isGrpPullback_pullback G _)
  refine ⟨fun i => u' i ≫ e.inv, fun i => ?_, fun w hw => ?_⟩
  · rw [← he', ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact h4 i
  · have hc : ∀ a, e.hom ≫ (Over.pullback (spMap (algebraMap V O))).map (act a) = act' a ≫ e.hom := fun a => by
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      have A : ((Over.pullback (spMap (algebraMap V O))).map (act a)).left ≫ pullback.fst G.hom _ =
        pullback.fst G.hom _ ≫ (act a).left := pullback.lift_fst _ _ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, A, he', ha, ← Category.assoc, he']
    obtain ⟨c, ⟨y, hy, hy'⟩, -⟩ := h3 (w.1 ≫ e.hom) (by
      have h := congrArg (fun z => (z ≫ e.hom).left) w.2
      simp only [Category.assoc, IsMonHom.one_hom] at h
      exact h) fun a => by
        have h := congrArg (fun z => (z ≫ e.hom).left) (hw a)
        simp only [Category.assoc, ← hc] at h
        exact h
    refine ⟨c, ?_⟩
    have h := congrArg (IsMonHom.monoidHom e.inv _) hy'
    rw [map_list_prod, List.map_ofFn] at h
    refine Eq.trans ?_ (h.trans ?_)
    · exact ((Category.assoc _ _ _).trans (by rw [e.hom_inv_id, Category.comp_id])).symm
    · congr 2
      funext i
      exact (congrArg (· ≫ e.inv) (show y i = ptMap (dualScale (c i)) ≫ u' i from Over.OverMorphism.ext (hy i))).trans
        (Category.assoc _ _ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [StarRing (𝓞 E)] {P : Point p v O (𝓞 E)}

theorem exists_map_to_model {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {x₀ : Sp F ⟶ Xo.X} {k : F →+* C} {kO : V →+* O} {ψ : P.A.A.left ⟶ Xo.univ.t.G.left}
    (h : PointOver P x₀ k kO ψ) {G : SAB H (Sp V)} {t : SAB H (Sp F)} (n₁ : SABMap t Xo.univ.t x₀)
    (n₂ : SABMap t G (spMap (algebraMap V F))) :
    ∃ (π : P.G.left ⟶ G.G.left) (φ : P.A.A.left ⟶ t.G.left), IsGrpPullback P.G G.G (spMap kO) π ∧
      (∀ a, (P.oG.act a).left ≫ π = π ≫ (G.act.act a).left) ∧ φ ≫ t.G.hom = P.A.A.hom ≫ spMap k ∧
      φ ≫ n₂.φ = P.gen ≫ π ∧ φ ≫ n₁.φ = ψ := by
  obtain ⟨-, G', t', m₁, m₂, π, φ, h1, h2, h3, h4, rfl, -⟩ := h
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso m₁.cart n₁.cart
  obtain ⟨e, he, he'⟩ := LocModelLie.exists_iso_of_models HomExtExamples.homExtSt_holds V F G'.G G.G G'.semi G.semi t'.G
    m₂.cart (((isGrpPullback_of_iso a).comp n₂.cart).congr (Category.id_comp _) rfl)
  have c₁ : ∀ b, (t'.act.act b).left ≫ a.hom.left = a.hom.left ≫ (t.act.act b).left := fun b =>
    n₁.cart.1.hom_ext (by rw [Category.assoc, Category.assoc, n₁.act, ha', m₁.act, ← Category.assoc, ha'])
      (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w])
  have c₂ : ∀ b, (G'.act.act b).left ≫ e.hom.left = e.hom.left ≫ (G.act.act b).left := fun b => by
    haveI := G.semi.separated
    haveI := G'.semi.smooth
    haveI : IsSchemeTheoreticallyDominant (spMap (algebraMap V F)) :=
      schDom_spec_map _ (IsFractionRing.injective V F)
    haveI : IsSchemeTheoreticallyDominant m₂.φ := .of_isPullback m₂.cart.1.flip
    refine ext_of_schDom G.G.hom (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w]) m₂.φ ?_
    rw [← Category.assoc, ← m₂.act, Category.assoc, he', ← Category.assoc, c₁, ← Category.assoc m₂.φ, he',
      Category.assoc, Category.assoc, n₂.act]
  refine ⟨π ≫ e.hom.left, φ ≫ a.hom.left, (h1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl,
    fun b => ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h2, Category.assoc, Category.assoc, c₂]
  · rw [Category.assoc, Over.w, h3.1.w]
  · rw [Category.assoc, ← he', ← Category.assoc, h4, Category.assoc]
  · rw [Category.assoc, ha']

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    (dualMap f).comp (dualMap g) = dualMap (f.comp g) := by
  ext s <;> simp [dualMap]

theorem dualMap_alg {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem ext_generic {y y' : specO O (DualNumber O) ⟶ P.G}
    (h : spMap (dualMap (algebraMap O C)) ≫ y.left = spMap (dualMap (algebraMap O C)) ≫ y'.left) : y = y' := by
  haveI : IsSchemeTheoreticallyDominant (spMap (dualMap (algebraMap O C))) :=
    (schemeDominant_specMap_iff _).2 fun a b hab => TrivSqZeroExt.ext
      (P.integers.hom_inj (by simpa [dualMap] using congrArg TrivSqZeroExt.fst hab))
      (P.integers.hom_inj (by simpa [dualMap, Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd hab))
  haveI := P.semi.separated
  exact Over.OverMorphism.ext (ext_of_schDom P.G.hom ((Over.w y).trans (Over.w y').symm) _ h)

theorem span_bLie_eq_wRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec (embInt c P.integers τ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨x j, (hx j).isEig hP (z.eig τ j)⟩, rfl⟩
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨G, t, n₁, n₂, ⟨ub, u₁, u₂, u₃, u₄⟩, -⟩ := y₀.2.2
  obtain ⟨π, φ, h1, h2, h3, h4, h5⟩ := exists_map_to_model hP n₁ n₂
  letI := kO.toAlgebra
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have inj : Function.Injective (algebraMap T.V O) := fun a b h => IsFractionRing.injective T.V T.Fr
    (k.toRingHom.injective ((hP.1 a).symm.trans ((congrArg _ h).trans (hP.1 b))))
  haveI : FaithfulSMul T.V O := (faithfulSMul_iff_algebraMap_injective _ _).2 inj
  haveI : Module.Flat T.V O := inferInstance
  haveI := G.semi.smooth
  haveI := G.act.hom
  choose χ hχ using fun a => int_val c T io τ a
  have hχ' : ∀ a, algebraMap T.V O (χ a) = embInt c P.integers τ a := fun a => P.integers.hom_inj (by
    rw [algebraMap_embInt, ← k.commutes]
    exact (hP.1 _).trans (congrArg k (hχ a)))
  obtain ⟨u', v₁, v₂⟩ := exists_eigenbasis G.G G.act.act χ (ub τ) (u₁ τ) (fun i a => u₂ τ i a _ (hχ a))
    (fun w hw he => u₃ τ w hw fun a z hz => by
      obtain rfl : z = χ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ a).symm)
      exact he a) h1 P.oG.act h2
  have hc : ∀ j, Corr P (x j).1 (u' j) := fun j => by
    obtain ⟨xG, s, s₁, s₂, s₃⟩ := hx j
    obtain ⟨r, r₁, r₂⟩ := u₄ τ j
    have r₃ : r ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
      have : Mono (spMap (algebraMap T.V T.Fr)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
      refine (cancel_mono (spMap (algebraMap T.V T.Fr))).1 ?_
      have k : (ub τ j).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ j)
      rw [Category.assoc, ← n₂.cart.1.w, ← Category.assoc, r₂]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k).trans (dualMap_alg _))
    have e₁ : s.left ≫ φ = spMap (dualMap k.toRingHom) ≫ r := n₁.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, r₁, h5, s₂, hz.2.1])
      (by rw [Category.assoc, Category.assoc, r₃, h3, dualMap_alg, ← Category.assoc, Over.w s]; rfl)
    have e₂ : xG.1 = u' j := ext_generic (h1.1.hom_ext ?_ (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w]))
    · exact e₂ ▸ s₁
    have e₃ : k.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap O C).comp (algebraMap T.V O) :=
      RingHom.ext fun a => (hP.1 a).symm
    rw [← s₃, Category.assoc, ← h4, ← Category.assoc, e₁, Category.assoc, r₂, Category.assoc, v₁, ← Category.assoc,
      ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_comp, dualMap_comp, e₃]
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hl := existsUnique_left (P := P) hp (isAdicComplete_dualNumber p)
  have hr := existsUnique_right (P := P) hp (isAdicComplete_dualNumber p)
  obtain ⟨y, hy, -⟩ := hr w.1
  have y₁ := hy.comp (TrivSqZeroExt.fstHom O O O)
  rw [w.2] at y₁
  obtain ⟨a, ha⟩ := v₂ ⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique y₁ Corr.one⟩ fun a =>
    (hr _).unique (corr_act hy a) (by
      rw [hχ', show w.1 ≫ P.oGt.act a = _ from congrArg Subtype.val (hw a)]
      exact hy.comp _)
  let S : Submonoid (specO O (DualNumber O) ⟶ P.G) :=
    { carrier := {y | ∃ w : LieG P.Gt, Corr P w.1 y ∧ P.bLie w ∈ Submodule.span O (Set.range fun j => P.bLie (x j))}
      mul_mem' := by
        rintro _ _ ⟨a, a₁, a₂⟩ ⟨b, b₁, b₂⟩
        exact ⟨lieAdd a b, a₁.mul b₁, P.bLie_add a b ▸ Submodule.add_mem _ a₂ b₂⟩
      one_mem' := ⟨lieZero P.Gt, Corr.one, P.bLie_zero ▸ Submodule.zero_mem _⟩ }
  obtain ⟨w', w₁, w₂⟩ : y ∈ S := by
    rw [show y = _ from ha]
    refine S.list_prod_mem fun s hs => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hs
    exact ⟨AvDefs.lieScale P.Gt (a j) (x j), (hc j).comp _,
      P.bLie_scale (a j) (x j) ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
  obtain rfl : w = w' := Subtype.ext ((hl y).unique hy w₁)
  exact w₂

end GlobalTheory.CompHt.RecSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.VmTwo

theorem twoSided_goodInert : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hL hW hE hS P hG hc
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  exact GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hL hcore hS _ P hG hc (GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place R F hW hE _ P hG hc)

end GlobalTheory.VmTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPointStatement
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pdiv_group_for_point : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ ∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x := by
  first | exact @GlobalTheory.RaynaudPDiv.exists_pDivGroup_raynaud | exact GlobalTheory.RaynaudPDiv.exists_pDivGroup_raynaud | (intros; apply GlobalTheory.RaynaudPDiv.exists_pDivGroup_raynaud <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTowerStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarization_torsion_tower : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralFinite P → ∀ (G : PDivGroup p O) (tw : G.TorsionTower P.Gt), ∃ φ : G ⟶ G.dual, ∀ (s s' : G.Tate) (n : ℕ), algebraMap O C (muRoot (pairing G O s (tateMap G G.dual O φ s')) n) = (weil P.A (p ^ n) (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n)) (P.toA (GlobalTheory.DeRham.spOver (s'.pt n) ≫ tw.y n)) : C) := by
  first | exact @GlobalTheory.WeilPhi.exists_hom_weil | exact GlobalTheory.WeilPhi.exists_hom_weil | (intros; apply GlobalTheory.WeilPhi.exists_hom_weil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotInertPlaceOfMem
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.SqNum

theorem conj_smul_int {D : D7} (x : 𝓞 D.host.E) : (D.host.conj • x : 𝓞 D.host.E) = Formalism.L2.Col.cO _ x := by
  apply RingOfIntegers.ext
  rw [show ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) from rfl,
    Formalism.BasicNotions.bridge_star_holds D.R D.host]
  rfl

theorem exists_prime_notInert_place : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ P.S0 → ∃ q : ℕ, q.Prime ∧ ¬ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D T L P v hv
  obtain ⟨e, he⟩ := P.w_split v hv
  have hunder := P.w_over v hv
  obtain ⟨q, hq, hqv⟩ : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have := v.isMaximal
    have : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    letI := Ideal.Quotient.field v.asIdeal
    refine ⟨ringChar (𝓞 D.host.F ⧸ v.asIdeal), CharP.char_is_prime (𝓞 D.host.F ⧸ v.asIdeal) _, ?_⟩
    exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 D.host.F ⧸ v.asIdeal) (ringChar _))
  refine ⟨q, hq, fun hin => ?_, hqv⟩
  have hqQ : ((q : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
    have h1 : ((q : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by rw [hunder]; exact hqv
    simpa [HeightOneSpectrum.under] using h1
  have hfix := hin (P.w v).asIdeal (P.w v).isPrime (P.w v).ne_bot hqQ
  have hf : ∀ x, x ∈ (P.w v).asIdeal → Formalism.L2.Col.cO _ x ∈ (P.w v).asIdeal := fun x hx => by
    rw [← conj_smul_int, ← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  have hmem : ∀ x, x ∈ (P.w v).asIdeal ↔ Formalism.L2.Col.cO _ x ∈ (P.w v).asIdeal := fun x =>
    ⟨hf x, fun hx => by simpa [Formalism.L2.Col.cO_cO] using hf _ hx⟩
  have hc := GlobalTheory.MovedIdem.isIdemAt_conj he hmem
  have e1 : e = Formalism.L2.Theta.cA D e := (GlobalTheory.ExportSeries.idemAt_eq he).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hc)
  have e0 : e = 0 := by
    calc e = e * e := he.1.1.symm
      _ = e * Formalism.L2.Theta.cA D e := by rw [← e1]
      _ = 0 := he.1.2.1
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (P.w v).ne_bot
  have h2 := (he.2 x hx0).1 hxQ
  rw [e0, zero_mul, map_zero] at h2
  exact h2 (zero_mem _)

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpanStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_projection_section_isotropicSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  first | exact @GlobalTheory.rational_proj_section_of_span | exact GlobalTheory.rational_proj_section_of_span | (intros; apply GlobalTheory.rational_proj_section_of_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitMove

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.UnRep.FullReps GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (v : Fin n → E) :
    (fun j => IsCMField.complexConj E (IsCMField.complexConj E (v j))) = v :=
  funext fun j => IsCMField.complexConj_apply_apply E (v j)

theorem unimod_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} (hU : Λ.Unimod) :
    (conjLat H Λ.La).Unimod := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨H.bar a, H.bar_eq a⟩
  intro v
  rw [mem_conjLat, hU]
  constructor
  · intro hv w hw
    have := hr _ (hv _ hw)
    simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this
  · intro hv w hw
    have := hr _ (hv (fun j => IsCMField.complexConj E (w j)) (by rw [mem_conjLat, conj_conj]; exact hw))
    simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this

theorem trivAt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} {N : ℕ} (hT : Λ.TrivAt N) :
    (conjLat H Λ.La).TrivAt N := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk, conjLat_le H (by rw [← H.bar_eq, map_natCast])
    ⟨(Move.span_smul_le _ _ _).1 h1, (Move.span_smul_le _ _ _).1 h2⟩⟩

theorem congAt_of_congAtA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    {N M : ℕ} (hM : 0 < M) {γ : Matrix (Fin n) (Fin n) E} (h : CongAtA F L N M (fm F γ)) :
    GlobalTheory.UnRep.CongAt L N M γ := by
  obtain ⟨t, ht, h⟩ := h
  have hrat := (hat_rational_points_and_approx F E n L hfg hsp).1
  refine ⟨t, ht, fun v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := h _ ((hrat v).2 hv)
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have key : t • (γ *ᵥ v - v) = M • ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) := by
    rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
  refine ⟨_, ?_, key⟩
  rw [← hrat]
  have e' : fv F ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) = w := by
    refine Move.nsmul_cancel _ hM ?_
    rw [← cap_fv_nsmul, ← key, cap_fv_nsmul, Move.fv_sub, Move.fv_mulVec, e]
  rw [e']
  exact hw

theorem exists_move_matrix (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (N : ℕ) (hN : 0 < N) (Λ : GenLat E n)
    (hU : Λ.Unimod) (hT : Λ.TrivAt N) :
    ∃ (γ : Matrix (Fin n) (Fin n) E) (h : GL (Fin n) (RA (maximalRealSubfield E) E))
      (Lh : Submodule (𝓞 E) (Fin n → E)), IsUnitaryM γ ∧
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) ∧
      IsUnA (IsCMField.complexConj E) 1 h.1 ∧ SuppSplit (IsCMField.complexConj E) N h.1 ∧
      (Lh : Set (Fin n → E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield E) h.1 (stdLat E n) ∧
      actLat γ Λ = conjLat H Lh := by
  obtain ⟨hherm, hrk, hfg, hsp, -, -, -, hun⟩ := StdInhab.main E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate E H n N _ hN (unimod_conj H hU)
    (trivAt_conj H hT)
  obtain ⟨γ, h, k, hγ, hh, -, e, hs, hk, hk'⟩ := GlobalTheory.UnRep.exists_rep_suppSplit (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g N hg hN
  obtain ⟨Lh, hLh, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp
  have hu : adjM γ.1 * γ.1 = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← (hun _).1 hγ i j]
    rfl
  have hu' : γ.1 * adjM γ.1 = 1 := mul_eq_one_comm.1 hu
  have hδ : adjM γ.1ᵀ * γ.1ᵀ = 1 := by
    rw [show adjM γ.1ᵀ = (adjM γ.1)ᵀ from rfl, ← Matrix.transpose_mul, hu', Matrix.transpose_one]
  have hδ' : γ.1ᵀ * adjM γ.1ᵀ = 1 := mul_eq_one_comm.1 hδ
  have ck : CongAtA (maximalRealSubfield E) (stdLat E n) N N (k⁻¹).1 := by
    refine ⟨1, Nat.coprime_one_left _, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hk _ (hk' z hz)
    refine ⟨-w, neg_mem hw, ?_⟩
    rw [one_smul, smul_neg, ← e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub]
  have ch : CongAtA (maximalRealSubfield E) (stdLat E n) N N (h⁻¹).1 := by
    obtain ⟨ε, -, -, he, hcut⟩ := hs
    obtain ⟨t, ht, hb⟩ := (idempotent_adeles_small_matrices (maximalRealSubfield E) E n (stdLat E n) hfg hsp).2.2.2.1
      N N ε ((h⁻¹).1 - 1) hN fun v hv => by
        by_contra h0
        exact (he v h0).2 hv
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hb z hz
    rw [cut_inv h _ hcut, Matrix.sub_mulVec, Matrix.one_mulVec] at e
    exact ⟨w, hw, e⟩
  have eγ : fm (maximalRealSubfield E) γ.1 = g.1 * (k⁻¹).1 * (h⁻¹).1 := by
    rw [e, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have cγ : GlobalTheory.UnRep.CongAt (stdLat E n) N N γ.1 := by
    refine congAt_of_congAtA (F := maximalRealSubfield E) _ hfg hsp hN ?_
    rw [eγ]
    exact LatForm.congAtA_mul _ _ _ _ _ (LatForm.congAtA_mul _ _ _ _ _ (hgc N hN) ck) ch
  have hmove : ∀ u, u ∈ Lh ↔ γ.1 *ᵥ u ∈ (conjLat H Λ.La).La := by
    intro u
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (p := (conjLat H Λ.La).La), hΛ, hLh]
    constructor
    · rintro ⟨z, hz, ez⟩
      refine ⟨_, hk' z hz, ?_⟩
      rw [Move.fv_mulVec, ← ez, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Units.mul_inv_cancel_right]
    · rintro ⟨z, hz, ez⟩
      refine ⟨k.1 *ᵥ z, ?_, ?_⟩
      · obtain ⟨w, hw, e⟩ := hk z hz
        rw [sub_eq_iff_eq_add.1 e]
        exact add_mem (nsmul_mem hw _) hz
      · have := congrArg (fun x => fm (maximalRealSubfield E) (γ⁻¹).1 *ᵥ x) ez
        rw [← Move.fv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, e,
          ← mul_assoc, ← mul_assoc, ← FullReps.fm_mul, Units.inv_mul, FullReps.fm_one, one_mul] at this
        rw [Matrix.mulVec_mulVec, this]
  refine ⟨γ.1ᵀ, h, Lh, hδ, fun j => ?_, hh, hs, hLh, congrArg GenLat.mk (Submodule.ext fun v => ?_)⟩
  · obtain ⟨t, ht, hc⟩ := cγ
    refine ⟨t, ht, fun i => ?_⟩
    obtain ⟨w, hw, ew⟩ := hc _ (StdInhab.single_mem n i)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hw j trivial)
    refine ⟨b, ?_⟩
    have := congrFun ew j
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← hb, Pi.sub_apply,
      Matrix.mulVec_single_one] at this
    refine Eq.trans ?_ this
    congr 2
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Pi.single_apply, Ne.symm hij]
  · have hc : (fun j => IsCMField.complexConj E ((γ.1 *ᵥ fun j => IsCMField.complexConj E (v j)) j)) =
        adjM γ.1ᵀ *ᵥ v := by
      funext j
      simp [Matrix.mulVec, dotProduct, adjM]
    change v ∈ (actLat γ.1ᵀ Λ).La ↔ v ∈ (conjLat H Lh).La
    rw [mem_conjLat, hmove, mem_conjLat, hc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change adjM γ.1ᵀ *ᵥ (γ.1ᵀ *ᵥ u) ∈ Λ.La
      rw [Matrix.mulVec_mulVec, hδ, Matrix.one_mulVec]
      exact hu
    · intro hv
      refine ⟨_, hv, ?_⟩
      change γ.1ᵀ *ᵥ (adjM γ.1ᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hδ', Matrix.one_mulVec]

end General

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_move_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  intro D V hg hL H N hN Λ hU hT
  obtain ⟨γ, h', Lh, h1, h2, h3, h4, h5, h6⟩ := exists_move_matrix H N hN Λ hU hT
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨h, hh, eh⟩ := lift h' (by
    rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc]
    exact h3)
  refine ⟨γ, h, h1, h2, hh, ?_, ?_⟩
  · rw [eh, hc]; exact h4
  · rw [GlobalTheory.SplitReps.hLat_one] at hL
    rw [GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Lh (by
      rw [hL]
      change _ = GlobalTheory.AdLat.latOf D.host.F (finHom V h).1 _
      rw [eh]
      exact h5)]
    exact h6

end GlobalTheory.SplitMove
end
end


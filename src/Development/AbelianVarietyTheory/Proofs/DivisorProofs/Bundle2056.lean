import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquot
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulRkKChiLatLeRankW
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.CovolRank

theorem comap_val_finite {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) [FiniteDimensional K C] :
    FiniteDimensional K (C.comap A.val.toLinearMap) ∧
      Module.finrank K (C.comap A.val.toLinearMap) ≤ Module.finrank K C := by
  let f : C.comap A.val.toLinearMap →ₗ[K] C :=
    LinearMap.codRestrict C (A.val.toLinearMap ∘ₗ (C.comap A.val.toLinearMap).subtype)
      fun y => Submodule.mem_comap.1 y.2
  have hf : Function.Injective f := fun a b hab => by
    have h := congrArg (fun z : C => (z : B)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : FiniteDimensional K (C.comap A.val.toLinearMap) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

theorem finrank_span_le_of_map {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) (hC : C ≤ Subalgebra.toSubmodule A) {O : Type} [CommRing O] [Module O C]
    (L : Submodule O C) (N : Submodule K A) [FiniteDimensional K N]
    (hL : ∀ F ∈ L, (⟨(F : B), hC F.2⟩ : A) ∈ N) :
    Module.finrank K (Submodule.span K (L : Set C)) ≤ Module.finrank K N := by
  let Φ : C →ₗ[K] A := LinearMap.codRestrict (Subalgebra.toSubmodule A) C.subtype fun y => hC y.2
  have hΦ : Function.Injective Φ := fun a b hab => by
    have h := congrArg (fun z : A => (z : B)) hab
    exact Subtype.ext h
  have hle : Submodule.span K (L : Set C) ≤ N.comap Φ := by
    rw [Submodule.span_le]
    intro F hF
    exact hL F hF
  let ψ : Submodule.span K (L : Set C) →ₗ[K] N :=
    LinearMap.codRestrict N (Φ ∘ₗ (Submodule.span K (L : Set C)).subtype) fun y => hle y.2
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext (hΦ (congrArg Subtype.val hab))
  exact LinearMap.finrank_le_finrank_of_injective hψ

end GlobalTheory.CovolRank

namespace GlobalTheory.CovolRank

theorem card_mul_rkK_chiLat_le_rankW : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E), Even G.2 → Even W.2 → KeepsCusp U G → KeepsCusp U W → GoodW U x V dict G → GoodW U x V dict (G + W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ rankW U (G + W) := by
  classical
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hKG hKW hgG hgGW χ u hdet
  have hsec : ∀ G' : WTZ E, cuspW Xo c U G' ≤ Subalgebra.toSubmodule (secRing Xo c) :=
    fun G' f hf => GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ G' hf)
  have hfin : ∀ G' : WTZ E, GlobalTheory.AllWt.GoodW U x V dict G' → FiniteDimensional c.F (cuspW Xo c U G') := by
    intro G' hg
    obtain ⟨n, ⟨b, _⟩, _⟩ := hg.1.some
    exact Module.Finite.of_basis b
  haveI := hfin G hgG
  haveI := hfin (G + W) hgGW
  obtain ⟨hVs, -⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U G)
  obtain ⟨hVp, hVp'⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U (G + W))
  let uR : secRing Xo c := ⟨u, hsec W u.2⟩
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) uR).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have hc := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA uR
    refine mem_nonZeroDivisors_iff_left.mpr fun y hy => ?_
    apply Subtype.ext
    have h0 : levDet Xo c S u * (y : Rul Xo c) = 0 := by
      rw [← hc]; exact congrArg Subtype.val hy
    exact hdet _ y.2 h0

  let ι : secRing Xo c →ₗ[c.F] Rul Xo c := (secRing Xo c).val.toLinearMap
  let N : Submodule c.F (secRing Xo c) :=
    (cuspW Xo c U G).comap ι ⊓ GlobalTheory.LevDesc.eigen (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) χ
  have key := (GlobalTheory.finrank_le_card_mul_finrank_eigenspace_le S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ uR hdet'
    ⊥ ((cuspW Xo c U G).comap ι) ((cuspW Xo c U (G + W)).comap ι) N
    (fun h y hy => hKG h _ hy)
    (fun h y hy => by
      rw [Submodule.mem_bot] at hy
      subst hy
      rw [zero_mul]; exact Submodule.zero_mem _)
    (fun h y hy => GlobalTheory.SlopeRec.mul_mem_cuspW hG hW hy (hKW h _ u.2))
    (fun y => Submodule.mem_inf)).2
  haveI : FiniteDimensional c.F N := Submodule.finiteDimensional_of_le inf_le_left
  have h1 : Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ Module.finrank c.F N :=
    finrank_span_le_of_map (secRing Xo c) (cuspW Xo c U G) (hsec G) _ N fun F hF =>
      ⟨F.2, fun h => Subtype.ext (hF.2 h)⟩
  have e : rankW U (G + W) = Module.finrank c.F (cuspW Xo c U (G + W)) := by
    rw [rankW, Formalism.HN.rkK, hgGW.2.2, finrank_top]
  calc Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ)
      ≤ Fintype.card S * Module.finrank c.F N := Nat.mul_le_mul_left _ h1
    _ ≤ Module.finrank c.F ((cuspW Xo c U (G + W)).comap ι) := key
    _ ≤ rankW U (G + W) := e ▸ hVp'

end GlobalTheory.CovolRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedAlmostAllPlaces
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

theorem eventually_unrAt_of_isHecke {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (χ : Chr F E) (hχ : IsHecke F E χ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, UnrAt χ w := by
  obtain ⟨H, hloc, -⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ hcm χ hχ
  refine (GlobalTheory.HeckeSplit.eventually_unrAt H.1 H.2.1).mono fun w hw x hx => ?_
  rw [← hloc w x]
  exact ((GlobalTheory.HeckeSplit.unrAt_iff E H w).1 hw) x hx

theorem eventually_unrAt_chiX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
      ∀ᶠ v in Filter.cofinite, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have h := eventually_unrAt_of_isHecke σ hP.base.cm χX hP.hX
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw, hu⟩ := hv
  exact ⟨w, hu, hw⟩

end GlobalTheory.PairVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClosedPointIsCentreOfPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem centre_place : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
    ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  intro k K _ _ _ _ _ C _ x hx c hc
  obtain ⟨hC, hg, hstr⟩ := hx
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  haveI := hC.1
  haveI : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  haveI := hg.2
  set p : Sp K := IsLocalRing.closedPoint K with hp
  have hη : x p = genericPoint C := by
    have hd : Dense (Set.range x) := hg.1.denseRange
    have hr : Set.range x = {x p} := by
      ext y
      exact ⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩
    rw [hr] at hd
    exact (IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))
  have hco : Order.coheight c = 1 := by
    have hne : Order.coheight c ≠ 0 := by
      intro h0
      have hm : IsMax c := Order.coheight_eq_zero.1 h0
      have h3 : genericPoint C ⤳ c := genericPoint_specializes c
      apply hc
      rw [hη]
      exact ((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq
    have hle : (Order.coheight c : WithBot ℕ∞) ≤ 1 := by
      haveI : Nonempty C := ⟨c⟩
      have hd := GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1
      have h1 := (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
      rw [topologicalKrullDim] at hd
      rw [hd] at h1
      exact h1
    have hle' : Order.coheight c ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)
  haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco

  set A := C.presheaf.stalk c
  let P : IsDedekindDomain.HeightOneSpectrum A := IsDiscreteValuationRing.maximalIdeal A
  let ic := C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  let ψ : C.functionField →+* K := (ic.hom ≫ Scheme.stalkClosedPointTo x).hom
  have hψ : Function.Bijective ψ := by
    refine ⟨RingHom.injective ψ, ?_⟩
    have h1 : Function.Surjective ic.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2
    have h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
      have h3 := x.stalkMap_surjective p
      have h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom :=
        ((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2
      exact h4.comp h3
    exact h2.comp h1
  let e : C.functionField ≃+* K := RingEquiv.ofBijective ψ hψ
  let φ : A →+* K := ψ.comp (algebraMap A C.functionField)
  have hφ : spMap φ ≫ C.fromSpecStalk c = x := by
    have h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom := by
      show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _
      change (C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _
      rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
      erw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [h1]
    change Spec.map (CommRingCat.ofHom _) ≫ _ = x
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a := by
    intro a
    have : e.symm (φ a) = algebraMap A C.functionField a := e.symm_apply_apply _
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a

  have hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t)) := by
    have h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤))) := by
      rw [← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    have h2 := Spec.map_injective (hstr.symm.trans h1)
    intro t
    exact congrArg (fun f => f.hom t) h2
  let vK : Valuation K (WithZero (Multiplicative ℤ)) := (P.valuation C.functionField).comap e.symm.toRingHom
  have hvφ : ∀ a, vK (φ a) = P.intValuation a := fun a => hval a
  have hunit : ∀ a : A, IsUnit a → P.intValuation a = 1 := by
    intro a ha
    refine le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)
  let v : Place k K := ⟨vK, fun g => by
      obtain ⟨y, hy⟩ := P.valuation_surjective C.functionField g
      exact ⟨e y, by
        change P.valuation C.functionField (e.symm (e y)) = g
        rw [e.symm_apply_apply]; exact hy⟩,
    fun t ht => by
      rw [hk, hvφ]
      exact hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩
  have hle : ∀ a : A, φ a ∈ v.O := fun a => by
    show vK (φ a) ≤ 1
    rw [hvφ]; exact P.intValuation_le_one a
  let ψO : A →+* v.O := φ.codRestrict v.O hle
  have hPm : P.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI : IsLocalHom ψO := ⟨fun a ha => by
    by_contra hna
    have hm : a ∈ P.asIdeal := by rw [hPm]; exact hna
    have hlt : vK (φ a) < 1 := by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm
    obtain ⟨u, hu⟩ := ha
    let w : v.O := ((u⁻¹ : v.Oˣ) : v.O)
    have hinv : vK (w : K) ≤ 1 := w.2
    have h1 : φ a * (w : K) = 1 := by
      have := congrArg (fun z : v.O => (z : K)) u.mul_inv
      have e1 : φ a = ((u : v.O) : K) := by rw [hu]; rfl
      rw [e1]
      exact this
    have h2 := congrArg vK h1
    rw [map_mul, map_one] at h2
    have : vK (φ a) * vK (w : K) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt
    exact absurd h2 this.ne⟩
  refine ⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← hφ]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · have : spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint ψO
    change C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c
    rw [this, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddings
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifAll

theorem span_range_le {F U H : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H] {σ : F →+* ℂ}
    (j : U →ₛₗ[σ] H) {n : ℕ} (b : Module.Basis (Fin n) F U) :
    Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
  rw [Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  rw [← b.sum_repr u, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_top {F U H H' : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] {σ σ' : F →+* ℂ} (j : U →ₛₗ[σ] H) (j' : U →ₛₗ[σ'] H') {n : ℕ}
    (b : Module.Basis (Fin n) F U) (c : H ≃ₗ⋆[ℂ] H') (hi : LinearIndependent ℂ fun k => j (b k))
    (hs : Submodule.span ℂ (Set.range j') = ⊤) : Submodule.span ℂ (Set.range j) = ⊤ := by
  have h1 : Submodule.span ℂ (Set.range fun k => j' (b k)) = ⊤ := top_le_iff.1 (hs ▸ span_range_le j' b)
  have h2 : Submodule.span ℂ (Set.range fun k => c.symm (j' (b k))) = ⊤ := by
    have h3 := congrArg (Submodule.map (c.symm : H' →ₗ⋆[ℂ] H)) h1
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3
  haveI : Module.Finite ℂ H := ⟨h2 ▸ Submodule.fg_span (Set.finite_range _)⟩
  have h4 : Module.finrank ℂ H ≤ n := by simpa using finrank_le_of_span_eq_top h2
  have h5 : Fintype.card (Fin n) = Module.finrank ℂ H :=
    le_antisymm hi.fintype_card_le_finrank (by simpa using h4)
  refine top_le_iff.1 ((hi.span_eq_top_of_card_eq_finrank' h5).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨b k, rfl⟩

theorem indep_of_conj {H X : Type} [AddCommGroup H] [Module ℂ H] {m : ℕ} (ev : H → X → ℂ)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x) (w : Fin m → H)
    (φ : Fin m → X → ℂ) (hφ : LinearIndependent ℂ φ) (h : ∀ k g, ev (w k) g = starRingEnd ℂ (φ k g)) :
    LinearIndependent ℂ w := by
  let E : H →ₗ[ℂ] (X → ℂ) := { toFun := ev, map_add' := hadd, map_smul' := hsmul }
  rw [Fintype.linearIndependent_iff] at hφ ⊢
  intro a ha k
  have h1 : ∑ k, starRingEnd ℂ (a k) • φ k = 0 := by
    funext g
    have h2 := congrFun (congrArg E ha) g
    rw [map_sum, map_zero, Finset.sum_apply] at h2
    have h3 := congrArg (starRingEnd ℂ) h2
    rw [map_sum, Pi.zero_apply, map_zero] at h3
    rw [Finset.sum_apply, Pi.zero_apply, ← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    show _ = starRingEnd ℂ (a k * ev (w k) g)
    rw [h, map_mul, Complex.conj_conj]
    rfl
  simpa using hφ _ h1 k

theorem unif_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp hκ hn i σ
  have good := GlobalTheory.T.uniformisation_goodEmbedding_independent_readings h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp hκ hn i
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good σ hσ
  obtain ⟨hc, hb⟩ := GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM hT
  have hbar := hb (GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp)
  have hg := good_resC T hσ
  have hV := hT.laws.spaceW _ (inR i) _ hg
  obtain ⟨v, -, hv⟩ := jTop_bar T R κ v₀ hσ hV (hbar i σ hσ hV)
  have ind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb =>
    indep_of_conj (evAt R i σ v) (fun x y => by simp only [evAt, map_add]; rfl)
      (fun a x => by simp only [evAt, map_smul]; rfl) _ _
      (GlobalTheory.PhiIndep.phiC_indep D T κ hT.laws i _ hg hV m b hb) fun k g => congrFun (hv (b k)) g
  refine ⟨ind, ?_⟩
  obtain ⟨c⟩ := hc i σ hσ
  obtain ⟨b⟩ := hasB_nTop T hT.laws κ i
  exact span_top _ _ b c (ind _ _ b.linearIndependent) (good ((starRingEnd ℂ).comp σ) hg).2

end GlobalTheory.UnifAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspPhMemChiLat
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LevDesc

theorem cuspPh_mem_chiLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W), (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U (G + W) → g ∈ latW U (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), u ∈ latW U W → ∀ f : cuspW Xo c U G, f ∈ latW U G → ∀ h : S, GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h ∈ GlobalTheory.LevDesc.chiLat S U (G + W) χ := by
  intro E _ _ _ H Dw l Xo c r U S hpq hA G W hG hW hK hKW hGW hWW χ u hu f hf h
  rw [GlobalTheory.LevDesc.mem_chiLat]
  refine ⟨?_, fun g => ?_⟩
  · have hint : ∀ g : S, IsIntegral ℤ ((((χ g)⁻¹ : (c.F)ˣ) : c.F)) := fun g => by
      refine IsIntegral.of_pow (Fintype.card_pos (α := S)) ?_
      rw [← Units.val_pow_eq_pow_val, ← map_inv, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
      exact isIntegral_one
    have hmem : ∀ g : S, pull Xo c g ((f : Rul Xo c) * pull Xo c h u) ∈ cuspW Xo c U (G + W) := fun g =>
      hK _ _ (GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2))
    have hlat : ∀ g : S, (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) ∈ latW U (G + W) := fun g => by
      have hu' : (⟨pull Xo c h u, hKW _ _ u.2⟩ : cuspW Xo c U W) ∈ latW U W := hWW h u _ rfl hu
      have hm : (f : Rul Xo c) * pull Xo c h u ∈ cuspW Xo c U (G + W) := GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2)
      exact hGW g ⟨_, hm⟩ _ rfl (GlobalTheory.AllWt.mul_mem_supLat hf hu' hm)
    have he : GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h =
        ∑ g : S, (⟨_, hint g⟩ : 𝓞 c.F) • (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) := by
      apply Subtype.ext
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul (c.F)]
      rfl
    rw [he]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hlat g)
  · rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply]
    exact (GlobalTheory.LevDesc.mem_levEigen.1 (GlobalTheory.LevDesc.levTr_mem_levEigen hpq hA χ _)) g

end GlobalTheory.LevDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.BotSameRig.const_of_sameRig | exact GlobalTheory.BotSameRig.const_of_sameRig | (intros; apply GlobalTheory.BotSameRig.const_of_sameRig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRationalHomPointsIdealCompletionStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_rationalHomPoints_idealCompletion : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), r ≠ 0 → I ≠ 0 →
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : WO S T, HatPt r I u →
  ∃ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) ∧ u - finPt (S := S) (T := T) rfl rfl r z ∈ U := by
  first | exact @GlobalTheory.CosetOrthDens.exists_finPt_sub_mem | exact GlobalTheory.CosetOrthDens.exists_finPt_sub_mem | (intros; apply GlobalTheory.CosetOrthDens.exists_finPt_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumConditionStableLatticeStabilizerIneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ₁)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ₁))) := by
  first | exact @GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD | exact GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD | (intros; apply GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquotStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient : ∀ (p q : ℕ) (α β α' β' : ℂ), ∃ B : ℚ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, N < N' → Stab act N → Stab act N' → QuadMod act α β α' β' N N' → ∃ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) ∧ ∃ v ∈ N', v ∈ hwSub act μ ∧ v ∉ N := by
  first | exact @GlobalTheory.HoweR.exists_hwSub_of_quadMod | exact GlobalTheory.HoweR.exists_hwSub_of_quadMod | (intros; apply GlobalTheory.HoweR.exists_hwSub_of_quadMod <;> assumption)
end


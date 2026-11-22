import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautBaseChangeTripleLiftLeft
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalNoetherianCoverFractionFieldEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.LocExt

theorem exists_finite_normal_cover_of_finiteDimensional : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'), Function.Injective ρ ∧ ρ.Finite ∧ ((τ.comp (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  intro R _ _ _ _ hcomp K' _ _ _
  have hnorm : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hCN : IsCN R := ⟨inferInstance, hnorm, hcomp, inferInstance⟩
  let K := FractionRing R
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K K' := inferInstance
  let C := integralClosure R K'
  haveI hCf : Module.Finite R C := IsIntegralClosure.finite R K K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRC : Function.Injective (algebraMap R C) := fun x y h => hRK' (congrArg Subtype.val h)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρ, hρf, -, hσρ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) hCN hRC
      (RingHom.finite_algebraMap.2 hCf)
  obtain ⟨hnoeth', hnorm', -, -⟩ := hCN'
  letI : Algebra C R' := σ.toAlgebra
  letI : Algebra R R' := ρ.toAlgebra
  haveI : IsScalarTower R C R' := IsScalarTower.of_algebraMap_eq (fun r => (RingHom.congr_fun hσρ r).symm)
  haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hker : RingHom.ker σ = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := R)
      ext r
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro h
        apply hρ
        rw [map_zero, ← h]
        exact (RingHom.congr_fun hσρ r).symm
      · rintro rfl; simp
    have : c ∈ RingHom.ker σ := hc
    rw [hker] at this
    exact this
  have hσ' : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσ
  let τ : K' →+* FractionRing R' := IsFractionRing.lift (A := C) hσ'
  refine ⟨R', inferInstance, inferInstance, hnoeth', hnorm', inferInstance, ρ, τ, hρ, hρf, ?_⟩
  ext r
  simp only [RingHom.comp_apply]
  have h1 : algebraMap K K' (algebraMap R K r) = algebraMap C K' (algebraMap R C r) := rfl
  rw [h1]
  simp only [τ, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  rw [← RingHom.comp_apply σ, hσρ]

end GlobalTheory.LocExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open GlobalTheory.Toroidal (gen genι genStr)

theorem exists_rel_of_mem_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hbar K _ p hp

  obtain ⟨yF, hyF, hcar⟩ := GlobalTheory.Mean4O.CompModel.exists_flagPt C p

  haveI := Y.jQ_open
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hp s
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hys : y ≫ pullback.snd _ _ = spMap yF.fK := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hyF]
    exact yF.y_over

  obtain ⟨P, hPy, hPw⟩ := GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y K yF.fK y
    (yF.y ≫ genι Y) yF.frame hys (by rw [← Category.assoc, hy, hyF])
  letI : Algebra c.F K := yF.fK.toAlgebra
  have hPX : GlobalTheory.FlagMod.frX P = y := hPy
  have hl := X.lies_ptY P
  have hxg : X.ptY P ≫ X.π = yF.y ≫ genι Y := by
    rw [hl.1, hPX, Model.j, ← Category.assoc, hy, hyF]

  have hr₀ : Set.range (X.ptY P) ⊆ Set.range (GlobalTheory.CompHS.inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    show X.π (X.ptY P s) ∈ GlobalTheory.CompHS.barComp Y Z
    have e : X.π (X.ptY P s) = genι Y (j (f (p s))) := by
      rw [← Scheme.Hom.comp_apply, hxg, ← hyF, hπ]
      rfl
    rw [e]
    exact (hbar _).2 ⟨f (p s), rfl⟩
  let z := IsOpenImmersion.lift (GlobalTheory.CompHS.inc₀ X Z) (X.ptY P) hr₀
  have hz : z ≫ GlobalTheory.CompHS.inc₀ X Z = X.ptY P := IsOpenImmersion.lift_fac _ _ _
  refine ⟨z, ?_⟩
  rw [hz]

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P)
  have hφ : X.ptY P ≫ X.π ≫ Y.s = spMap yF.fK := GlobalTheory.CompHS.ptY_str X P
  obtain ⟨g₂, hg₂⟩ := hFE K yF.fK (X.ptY P) k hk hφ
  refine ⟨yF.fK, k, hk, g₂, hφ, hg₂, ?_⟩

  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have ht' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).2.2.1 _ _ _ ht
  have hPx : GlobalTheory.FlagMod.frX P ≫ Y.j = X.ptY P ≫ X.π := hl.1.symm
  choose b hb hdiag hsum using fun τ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (X.F.M k).toMChart) (X.F.inM hk rfl) hPx hQ.over ht' τ

  have hgv : ∀ τ i, yF.frame.v τ i = (tv (GlobalTheory.FlagMod.frVec Y P hPx τ i)).left := by
    intro τ i
    obtain ⟨w, hw1, hw2, hw3⟩ := hPw τ i
    rw [← hPX] at hw1
    have hL : w = GlobalTheory.FlagMod.liftTan Y (GlobalTheory.FlagMod.frX P) ((GlobalTheory.FlagMod.frX_fst P).symm ▸ P.tan τ i) :=
      Y.m0.cart.1.hom_ext (hw2.trans (GlobalTheory.FlagMod.liftTan_univ _ _).symm)
        (hw1.trans (GlobalTheory.FlagMod.liftTan_over _ _).symm)
    show yF.frame.v τ i = _
    rw [← hw3, hL]
    rfl
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  have hd : yF.frame.Tri (RingHom.id K) g₂ (fun τ i => (t⁻¹) (some ⟨τ, i⟩)) := by
    refine ⟨by rw [h2, Category.id_comp, hxg], rfl, fun τ i => ⟨fun m => b τ m i, hdiag τ i,
      fun m hm => hb τ hm, ?_⟩⟩
    simp only [h1, Category.id_comp]
    have e : (fun m => yF.frame.v τ m) = fun m => (tv (GlobalTheory.FlagMod.frVec Y P hPx τ m)).left := funext (hgv τ)
    rw [e, hg₂ τ i, GlobalTheory.LieMet.isComb_iff, ← hQ.frVec_eq rfl hQ.over τ]
    exact hsum τ i
  exact carries_of_tri C hd hcar

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SpreadModel

open TopologicalSpace

theorem gen_specializes {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp O} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap O K))) : j (genericPoint Y) ⤳ genericPoint X := by
  have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  have hx : (p (genericPoint X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (j (genericPoint Y))).map p.continuous))).trans (hp _).le)
  have hr : genericPoint X ∈ Set.range j := by
    rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint K, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap O K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  obtain ⟨y, hy⟩ := hr
  exact hy ▸ (genericPoint_specializes y).map j.continuous

theorem app_algX {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k'} {j : Y ⟶ X} (w : j ≫ p = q ≫ spMap σ) (a : k) :
    j.app ⊤ (algX p ⊤ a) = algX q ⊤ (σ a) := by
  have e₁ : j.app ⊤ (algX p ⊤ a) = algX (j ≫ p) ⊤ a := by
    simp [algX, Scheme.Hom.appLE]
    rfl
  rw [e₁, w]
  have e₂ := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₂
  simp only [algX, RingHom.comp_apply]
  rw [e₂]
  simp [Scheme.Hom.appLE]
  rfl

theorem exists_spread : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
    IsProjOver q → topologicalKrullDim Y = D → (⨆ k, nonzeroLocus (t k) = ⊤) → Function.Bijective ψ →
    (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i), ψ (y k) * fnOf _ h ((t l).f i) = ψ (y l) * fnOf _ h ((t k).f i)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X.functionField),
      g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) := by
  intro K Ω _ _ _ _ D m y Y _ q B hB t ψ hq hD ht hψ hK hy
  let c := q ≫ spMap (algebraMap (𝓞 K) K)
  obtain ⟨X, π, j, hX, hπ, hfl, H, hg⟩ := IntModel.exists_flat_model (O := 𝓞 K) q hq
    (fun _ : Unit => PSpace (𝓞 K) m) (fun _ => PSpace.str (𝓞 K) m) (fun _ => ProjSpace.toProj c t ht)
    (fun _ => ⟨m, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)
  obtain ⟨g, hg₁, hg₂⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 K)).2 inferInstance
  have har : IsArithVar π D := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField K) H hD⟩
  have hη := gen_specializes H
  have hpre : IsPreimmersion j :=
    have := IsPreimmersion.of_isLocalization (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))
    MorphismProperty.of_isPullback H.flip this
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (SmallSec.fnMap j hη)
    ⟨(SmallSec.fnMap j hη).injective, SmallSec.fnMap_surjective j hη⟩
  have he (u) : e u = SmallSec.fnMap j hη u := rfl
  have he' (a : Ω) : e ((e.symm.toRingHom.comp ψ) a) = ψ a := e.apply_symm_apply _
  refine ⟨X, hX, π, g, e.symm.toRingHom.comp ψ, hg₂, har, e.symm.bijective.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · apply e.injective
    rw [he', hK, he, SmallSec.fnMap_fnOf j hη _ (Opens.mem_top _), app_algX H.w]
    rfl
  · apply e.injective
    have h' : genericPoint Y ∈ j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := hη.mem_open (Opens.isOpen _) h
    have hU₀ : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤ (j ≫ g) ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) :=
      fun x hx => (pull_U _ g i).le hx
    have hU : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤
        ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) := hg₁ ▸ hU₀
    have hf (a) : j.app _ ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i) =
        ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (i PUnit.unit) hU a := by
      refine Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 K) m (i PUnit.unit) a))
        (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g i).le le_rfl)
    obtain ⟨n, hn⟩ := exists_chart hB (genericPoint Y)
    have key (a) := congrArg (fnOf _ (memInf h' hn)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (i PUnit.unit) a n
      (W := _ ⊓ B.U n) (inf_le_left.trans hU) inf_le_right)
    have hne : fnOf _ hn ((t (i PUnit.unit)).f n) ≠ 0 := by
      have hu := (ProjSpace.isUnit_resG_sec (t (i PUnit.unit)) n (W := _ ⊓ B.U n)
        (inf_le_left.trans (hU.trans (ProjSpace.toProj_preimage_chart c t ht _).le)) inf_le_right).map
          (fnOf _ (memInf h' hn))
      rw [fnOf_resG] at hu
      exact hu.ne_zero
    have key' (a) : fnOf _ hn ((t a).f n) = e (fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) *
        fnOf _ hn ((t (i PUnit.unit)).f n) := by
      have e₁ := key a
      rw [map_mul, fnOf_resG, fnOf_resG, ← ProjSpace.resG_pullRatio (hi := hU) inf_le_left, fnOf_resG] at e₁
      rw [he, SmallSec.fnMap_fnOf j hη h h', hf]
      exact e₁
    have h₀ := hy k l n hn
    rw [key' k, key' l, ← mul_assoc, ← mul_assoc] at h₀
    rw [map_mul, map_mul, he', he']
    exact mul_right_cancel₀ hne h₀

end GlobalTheory.SpreadModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc.Sep
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx

section Chart

variable {Y Y' : Scheme.{0}}

theorem chartPull_le {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (p : B'.ι × A'.ι) : B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def isoPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (chartPull_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_isoPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((isoPull a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (chartPull_le a b p) hz _).trans (gm_pull r h z _ (chartPull_le a b p hz) _)

theorem isoPull_isGen {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) (hw : w.IsGen) : (isoPull a b w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((isoPull a b w).s p) =
        gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) := fun p hp =>
    (gm_isoPull a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2)) :=
    ⟨chartPull_le a b p hy.1, chartPull_le a b q hy.2⟩
  have e := congrArg (gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2))))
    (hw (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hm) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val p hy.1)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div A' B' (𝟙 Y') y p q hy).trans ?_)
    ((gm_res (𝟙 Y') y _ hy _).trans (val q hy.2)))
  rw [a.g y _ _ hy.1.2 hy.2.2, b.g y _ _ hy.1.1 hy.2.1]

end Chart

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

def sq : (G2 (Bp T N)).left ⟶ (G2 T.B).left :=
  (lift (pushPt (cart T N).1.w (fst (Bp T N) (Bp T N))) (pushPt (cart T N).1.w (snd (Bp T N) (Bp T N)))).left

theorem lamφ_sq (I : ULift.{0} (Finset (Fin 2))) :
    lamφ (Bp T N) I ≫ pullback.fst T.B.hom (fC N) = sq T N ≫ lamφ T.B I :=
  psum_push (cart T N) _ _ (lift (pushPt (cart T N).1.w (fst (Bp T N) (Bp T N)))
    (pushPt (cart T N).1.w (snd (Bp T N) (Bp T N)))) (fun i => by fin_cases i <;> simp [x2]) I.down

end Base

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Iso

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

def w0 : LB.Iso (abelian₂ T.B T.M.L) (abelian₂ T.B T.M.L) := ⟨fun p => (abelian₂ T.B T.M.L).g p.1 p.2⟩

def wT : LB.Iso (abelian₂ (Bp T N) (Mp T N).L) ((abelian₂ T.B T.M.L).pull (sq T N)) :=
  isoPull (chartPullLinComb T.M.L (pullback.fst T.B.hom (fC N)) (lamφ (Bp T N)) (lamφ T.B) lamε (sq T N)
    (lamφ_sq T N)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ T.B T.M.L) (sq T N) (sq T N) rfl) (w0 T)

end Iso

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Val

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Val

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Main

end GlobalTheory.PolDeg.TautFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalActRankOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section
variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}}

def Near.pull (π : S ⟶ Sp R) (G : Over (Sp R)) [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    Near π ((Over.pullback π).obj G) where
  U := G
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  u := 𝟙 _
  isOpen := inferInstanceAs (IsOpenImmersion (𝟙 (pullback G.hom π)))
  u_over := Category.id_comp _
  all := fun g _ => ⟨g, rfl⟩

end

open GlobalTheory.TorsionFormCompare in

theorem isPullUnif_refl {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre) (hid : IsIdPull hD)
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) : IsPullUnif (RingHom.id R) hD bc U U := by
  obtain ⟨hx, he, hw⟩ := hid
  have hs := specOf_id R
  have heG : eSec G ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = specOf (RingHom.id R) ≫ eSec G := by
    rw [hbc, hs, Category.comp_id]; exact (Category.id_comp _).symm
  refine (GlobalTheory.isPullUnif_iff_stalks R R I I _ D D hD A A G G bc U U).2
    ⟨isoPullId (Geo.Tor.idIso U.LG.L) hbc, (isGen_iff _).2 (isoPullId_pgen (idIso_isGen U.LG.isLB) hbc), heG,
      isoPullId_maps (idIso_maps U.LG) hbc hs heG, fun e => ⟨𝟙 _, by rw [hbc, Category.id_comp, Category.comp_id],
      ⟨by rw [he, Category.id_comp, Category.comp_id], fun x => ?_⟩, ?_⟩⟩
  · rw [hx x]
    exact ⟨fun κ => by rw [he, Category.id_comp, Category.comp_id],
      pmaps_self_of_tautological he hD.w hw _ _ _ ((U.gt e).t_gen x)⟩
  · intro Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have h₁' : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM := by rw [he] at h₁; exact h₁
    have h₃' : (fstG I e G).left (r z) ∈ U.LG.L.U jL := by rw [hbc] at h₃; exact h₃
    rw [Category.comp_id, gw_isoPullId _ hbc _ z jL jL' h₃' h₄, hw Z (r ≫ (U.gt e).pG.left) z jM jM' h₁' h₂]
    have H := (isGen_iff (U.w e)).1 (U.w_gen e) Z r z jM jM' (fun _ => jL) (fun _ => jL') h₁' h₂
      (mem_pull.2 h₃') (mem_pull.2 h₄)
    have hp : r z ∈ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL') :=
      ⟨mem_pull.2 h₃', mem_pull.2 h₄⟩
    have e₂ : gm r z _ ((U.LG.L.pull (fstG I e G).left).g (fun _ => jL) (fun _ => jL')) =
        gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL') := by
      show gm r z _ (∏ _k : PUnit, (res _ (pullU _ _ (U.LG.L.g jL jL'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res r z _ hp _).trans (gm_pull r _ z (U.LG.L.U jL ⊓ U.LG.L.U jL') ⟨h₃', h₄⟩ _)
    rw [H, e₂]
    show _ = _ * gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL')
    rw [mul_right_comm _ _⁻¹, inv_mul_cancel_right]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  first | exact @GlobalTheory.Poinc.GenFibre.exists_generic_pullback | exact GlobalTheory.Poinc.GenFibre.exists_generic_pullback | (intros; apply GlobalTheory.Poinc.GenFibre.exists_generic_pullback <;> assumption)
end


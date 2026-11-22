import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secIsMul_cancel : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  intro R _ _ X p hp L q hq s t t' h h'
  haveI := hp
  have key : ∀ j, t.f j = t'.f j := by
    intro j
    refine fn_ext fun x hx => ?_
    have e1 := GlobalTheory.secIsMul_gs h (𝟙 X) x j hx
    have e2 := GlobalTheory.secIsMul_gs h' (𝟙 X) x j hx
    rw [Category.id_comp] at e1 e2
    have h0 : cst p x q * (gs (𝟙 X) x (L.U j) (t.f j) - gs (𝟙 X) x (L.U j) (t'.f j)) = 0 := by
      rw [mul_sub, ← e1, ← e2, sub_self]
    obtain ⟨u, hu⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero p x (a := q) (b := 0)
      (fun c hc => by
        rcases mul_eq_zero.1 hc with h1 | h1
        · exact absurd h1 hq
        · rw [h1]) h0
    have hz : cst p x (0 : R) = 0 := by
      rw [cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]
    rw [hz, zero_mul, sub_eq_zero] at hu
    exact hu
  cases t; cases t'
  congr 1
  exact funext key

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.HypSExt

open GlobalTheory.CechPic

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C} {h : A →+* C}
    (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_model {R : Type} [CommRing R] (P : PolAV (Sp R)) :
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : P.A.left ⟶ B.left) (L : LB B.left),
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback P.A B (spMap S.subtype) φ ∧ L.IsLB ∧
      Rigidified B L ∧ LBIso P.L (L.pull φ) := by
  obtain ⟨R₀, A₀, _, φ₀, -, ft₀, ab₀, -, H₀⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R P.g P.A ∅ P.isAb P.smoothDim
  have := ab₀.proper
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R R₀ _ _ P.A.hom A₀.hom φ₀ P.L H₀.1 P.isLB
  obtain ⟨R₁, h₁, s₁, ft₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R R₀ F₁ ft₀
  obtain ⟨A₁, _, φ₁, π₁, e₁, G₁, H₁⟩ := GlobalTheory.KeyTf.exists_model_of_le h₁ P.A A₀ φ₀ H₀
  obtain ⟨L₁, lb₁, iso₁⟩ := hF₁ R₁ h₁ s₁ _ A₁.hom π₁ φ₁ G₁.1 e₁ H₁.1.w
  have ab₁ := PolPull.isAbelianScheme_of_isGrpPullback ab₀ G₁
  let e : Sp R₁ ⟶ A₁.left := eSec A₁
  let e' : Sp R ⟶ P.A.left := eSec P.A
  have he : e ≫ A₁.hom = 𝟙 _ := Over.w η[A₁]
  have hee : e' ≫ φ₁ = spMap R₁.subtype ≫ e := PolBaseChange.eSec_comm H₁
  have hc : cls P.L P.isLB = pull φ₁ (cls L₁ lb₁) := (cls_eq_iff P.isLB (pull_isLB lb₁ φ₁)).2 iso₁
  have h0 : pull e' (cls P.L P.isLB) = 0 := (GlobalTheory.RigSymSubring.rigidified_iff P.isLB).1 P.rigid
  obtain ⟨L, hL, eL⟩ := cls_surj (cls L₁ lb₁ - pull A₁.hom (pull e (cls L₁ lb₁)))
  refine ⟨R₁, A₁, inferInstance, φ₁, L, ft₁, ab₁, H₁, hL, (GlobalTheory.RigSymSubring.rigidified_iff hL).2 ?_,
    (cls_eq_iff P.isLB (pull_isLB hL φ₁)).1 ?_⟩
  · change pull e (cls L hL) = 0
    rw [eL, map_sub, ← pull_comp, he, pull_id, sub_self]
  · rw [cls_pull hL, eL, map_sub, ← hc, ← pull_comp, H₁.1.w, pull_comp, ← pull_comp (spMap R₁.subtype), ← hee,
      pull_comp, ← hc, h0, map_zero, sub_zero]

theorem exists_hom_descend {S Ω : Type} [CommRing S] [CommRing Ω] (q : S →+* Ω) (hinj : Function.Injective q)
    {X X₀ : Scheme.{0}} (f : X ⟶ Sp Ω) (f₀ : X₀ ⟶ Sp S) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀]
    [LocallyOfFinitePresentation f₀] (φ : X ⟶ X₀) (H : IsPullback π f f₀ (spMap q)) (hφ : φ ≫ f₀ = π ≫ f₀) :
    ∃ F : Finset Ω, ∀ (K : Type) [CommRing K] (κ : S →+* K) (i : K →+* Ω), Function.Injective i → i.comp κ = q →
      (F : Set Ω) ⊆ Set.range i → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp K) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁),
        IsPullback π₁ f₁ f₀ (spMap κ) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap i →
        ∃ ψ : X₁ ⟶ X₀, j ≫ ψ = φ ∧ ψ ≫ f₀ = π₁ ≫ f₀ := by
  have iso : ∀ {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B), IsIso (spMap e.toRingHom) := fun e =>
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  let e : q.range ≃+* S := (RingEquiv.ofBijective q.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), q.rangeRestrict_surjective⟩).symm
  have he : q.comp e.toRingHom = q.range.subtype := RingHom.ext fun x =>
    congrArg Subtype.val (e.symm_apply_apply x)
  have := iso e
  obtain ⟨F, hF⟩ := GlobalTheory.morphism_descends_to_subring Ω q.range X X₀ X₀ f (f₀ ≫ spMap e.toRingHom)
    (f₀ ≫ spMap e.toRingHom) π φ (by
      have s : IsPullback (spMap q) (𝟙 _) (spMap e.toRingHom) (spMap q.range.subtype) :=
        IsPullback.of_vert_isIso ⟨by rw [spMap_comp_eq he, Category.id_comp]⟩
      have s' := H.paste_vert s
      rwa [Category.comp_id] at s') (by rw [reassoc_of% hφ])
  refine ⟨F, fun K _ κ i hi hc hK X₁ f₁ π₁ j H₁ hj hj' => ?_⟩
  let e' : i.range ≃+* K := (RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩).symm
  have he' : i.comp e'.toRingHom = i.range.subtype := RingHom.ext fun x =>
    congrArg Subtype.val (e'.symm_apply_apply x)
  have := iso e'
  have hle : q.range ≤ i.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨κ x, by rw [← hc]; rfl⟩
  have hsq : spMap κ ≫ spMap e.toRingHom = spMap e'.toRingHom ≫ spMap (Subring.inclusion hle) := by
    rw [spMap_comp_eq rfl, spMap_comp_eq rfl]
    congr 1
    refine RingHom.ext fun x => hi ?_
    exact ((RingHom.congr_fun hc _).trans (RingHom.congr_fun he x)).trans
      (RingHom.congr_fun he' (Subring.inclusion hle x)).symm
  obtain ⟨ψ, h₁, h₂⟩ := hF i.range hle hK X₁ (f₁ ≫ spMap e'.toRingHom) π₁ j
    (H₁.paste_vert (IsPullback.of_vert_isIso ⟨hsq⟩)) hj
    (by rw [reassoc_of% hj', spMap_comp_eq he'])
  exact ⟨ψ, h₁, (cancel_mono (spMap e.toRingHom)).1 (by simpa only [Category.assoc] using h₂)⟩

theorem exists_normal_noetherian {R Ω : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω]
    [IsFractionRing R Ω] (S : Subring R) (hS : Algebra.FiniteType ℤ S) (F : Finset Ω) :
    ∃ (D K : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsNoetherianRing D) (_ : IsIntegrallyClosed D) (_ : Field K)
      (_ : Algebra D K) (_ : IsFractionRing D K) (σ : S →+* D) (τ : D →+* R) (i : K →+* Ω),
      τ.comp σ = S.subtype ∧ i.comp (algebraMap D K) = (algebraMap R Ω).comp τ ∧ (F : Set Ω) ⊆ Set.range i := by
  classical
  choose a b hb hab using fun x : Ω => IsFractionRing.div_surjective R x
  obtain ⟨C, hSC, hF, hC⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S (F.image a ∪ F.image b) hS
  have hN : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing ℤ C
  have hfin := GlobalTheory.finite_integralClosure_of_essFiniteType_int C
  have hinj : Function.Injective ((algebraMap R Ω).comp C.subtype) :=
    (IsFractionRing.injective R Ω).comp C.subtype_injective
  let i : FractionRing C →+* Ω := IsFractionRing.lift hinj
  have hi : ∀ c : C, i (algebraMap C _ c) = algebraMap R Ω c := fun c => IsFractionRing.lift_algebraMap hinj c
  let D := integralClosure C (FractionRing C)
  have hD : ∀ x : D, ∃ r : R, algebraMap R Ω r = i x := fun x => by
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ?_
    exact IsIntegral.map_of_comp_eq C.subtype i (RingHom.ext fun c => (hi c).symm) x.2
  let j : D →+* Ω := i.comp D.val.toRingHom
  let eR : R ≃+* (algebraMap R Ω).range := RingEquiv.ofBijective (algebraMap R Ω).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective R Ω (congrArg Subtype.val h), (algebraMap R Ω).rangeRestrict_surjective⟩
  let τ : D →+* R := eR.symm.toRingHom.comp (j.codRestrict (algebraMap R Ω).range hD)
  have hτ : ∀ x : D, algebraMap R Ω (τ x) = i x := fun x =>
    congrArg Subtype.val (eR.apply_symm_apply (j.codRestrict (algebraMap R Ω).range hD x))
  refine ⟨D, FractionRing C, inferInstance, inferInstance, IsNoetherianRing.of_finite C D,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing C), inferInstance, inferInstance,
    IsIntegralClosure.isFractionRing_of_finite_extension C (FractionRing C) (FractionRing C) D,
    (algebraMap C D).comp (Subring.inclusion hSC), τ, i, RingHom.ext fun s => ?_, RingHom.ext fun x => (hτ x).symm,
    fun x hx => ?_⟩
  · apply IsFractionRing.injective R Ω
    exact (hτ _).trans (hi (Subring.inclusion hSC s))
  · have ha : a x ∈ C := hF (by simp; exact Or.inl ⟨x, hx, rfl⟩)
    have hb : b x ∈ C := hF (by simp; exact Or.inr ⟨x, hx, rfl⟩)
    exact ⟨algebraMap C _ ⟨_, ha⟩ / algebraMap C _ ⟨_, hb⟩, by rw [map_div₀, hi, hi]; exact hab x⟩

theorem hypS_noetherian {D K : Type} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D] [Field K]
    [Algebra D K] [IsFractionRing D K] (G : Over (Sp D)) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G)
    (L : LB G.left) (hL : L.IsLB) (hr : Rigidified G L)
    (h : HypS ((Over.pullback (spMap (algebraMap D K))).obj G) (L.pull (pullback.fst G.hom (spMap (algebraMap D K))))) :
    HypS G L := by
  have hn := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec D
  have : IsPreimmersion (spMap (algebraMap D K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors D)
  have : Flat (spMap (algebraMap D K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors D))
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap D K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap D K)) :=
    ExtUnique.spec_fractionRing D K
  have := hG.smooth
  have := hG.geomConnected
  have hs := GlobalTheory.isSemiAbelian_of_isAbelianScheme G hG
  obtain ⟨t, ht⟩ := hr
  exact GlobalTheory.ZH.EndoExtend.hypS_of_densePart (spMap (algebraMap D K)) hn G ⟨L, t, hL, ht⟩
    (fun f _ => GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds D K G G hs hs f) h

theorem hypS_normal {R Ω : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω]
    [IsFractionRing R Ω] (P : PolAV (Sp R)) (Q : PolAV (Sp Ω)) (a : Q.A.left ⟶ P.A.left)
    (ha : IsGrpPullback Q.A P.A (spMap (algebraMap R Ω)) a) (hb : LBIso Q.L (P.L.pull a)) (h : HypS Q.A Q.L) :
    HypS P.A P.L := by
  classical
  obtain ⟨w, wd, hw, hwd, hs, hp, hq⟩ := h
  obtain ⟨S, B, _, φ, L, ft, ab, H, hL, hr, iso⟩ := exists_model P
  have := ab.proper
  have := ab.smooth
  have := ab.comm
  let q : S →+* Ω := (algebraMap R Ω).comp S.subtype
  have hq : Function.Injective q := (IsFractionRing.injective R Ω).comp S.subtype_injective
  have HQ : IsGrpPullback Q.A B (spMap q) (a ≫ φ) := (ha.comp H).congr (spMap_comp_eq rfl) rfl
  have hv : ∀ v : Q.A ⟶ Q.A, (v.left ≫ a ≫ φ) ≫ B.hom = (a ≫ φ) ≫ B.hom := fun v => by
    rw [Category.assoc, HQ.1.w, Over.w_assoc]
  obtain ⟨F₁, hF₁⟩ := exists_hom_descend q hq Q.A.hom B.hom (a ≫ φ) _ HQ.1 (hv w)
  obtain ⟨F₂, hF₂⟩ := exists_hom_descend q hq Q.A.hom B.hom (a ≫ φ) _ HQ.1 (hv wd)
  obtain ⟨D, K, _, _, _, _, _, _, _, σ, τ, i, hσ, hi, hF⟩ := exists_normal_noetherian S ft (F₁ ∪ F₂)
  rw [Finset.coe_union, Set.union_subset_iff] at hF
  let G := (Over.pullback (spMap σ)).obj B
  have HG : IsGrpPullback G B (spMap σ) (pullback.fst B.hom (spMap σ)) := isGrpPullback_pullback B _
  have abG := PolPull.isAbelianScheme_of_isGrpPullback ab HG
  have := abG.comm
  let A := (Over.pullback (spMap (algebraMap D K))).obj G
  have HA : IsGrpPullback A G (spMap (algebraMap D K)) (pullback.fst G.hom _) := isGrpPullback_pullback G _
  have abA := PolPull.isAbelianScheme_of_isGrpPullback abG HA
  let κ : S →+* K := (algebraMap D K).comp σ
  have hκ : i.comp κ = q := by
    rw [← RingHom.comp_assoc, hi, RingHom.comp_assoc, hσ]
  let π : A.left ⟶ B.left := pullback.fst G.hom (spMap (algebraMap D K)) ≫ pullback.fst B.hom (spMap σ)
  have HAB : IsGrpPullback A B (spMap κ) π := (HA.comp HG).congr (spMap_comp_eq rfl) rfl
  have w₁ : (a ≫ φ) ≫ B.hom = (Q.A.hom ≫ spMap i) ≫ spMap κ := by
    rw [Category.assoc Q.A.hom, spMap_comp_eq hκ, HQ.1.w]
  let j : Q.A.left ⟶ A.left := HAB.1.lift _ _ w₁
  have j₁ : j ≫ π = a ≫ φ := HAB.1.lift_fst _ _ w₁
  have j₂ : j ≫ A.hom = Q.A.hom ≫ spMap i := HAB.1.lift_snd _ _ w₁
  have HQA : IsGrpPullback Q.A A (spMap i) j := HAB.cancel (HQ.congr (spMap_comp_eq hκ).symm j₁.symm) j₂
  have endo : ∀ v : Q.A ⟶ Q.A, (∃ ψ : A.left ⟶ B.left, j ≫ ψ = v.left ≫ a ≫ φ ∧ ψ ≫ B.hom = π ≫ B.hom) →
      ∃ v₀ : A ⟶ A, j ≫ v₀.left = v.left ≫ j := by
    rintro v ⟨ψ, h₁, h₂⟩
    refine ⟨Over.homMk (HAB.1.lift ψ A.hom (h₂.trans HAB.1.w)) (HAB.1.lift_snd _ _ _), HAB.1.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, j₁, h₁]
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, j₂, Over.w_assoc]
  obtain ⟨w₀, e₁⟩ := endo w (hF₁ K κ i i.injective hκ hF.1 _ A.hom π j HAB.1 j₁ j₂)
  obtain ⟨wd₀, e₂⟩ := endo wd (hF₂ K κ i i.injective hκ hF.2 _ A.hom π j HAB.1 j₁ j₂)
  have hLG := pull_isLB hL (pullback.fst B.hom (spMap σ))
  have hLA := pull_isLB hLG (pullback.fst G.hom (spMap (algebraMap D K)))
  have hc : cls P.L P.isLB = pull φ (cls L hL) := (cls_eq_iff P.isLB (pull_isLB hL φ)).2 iso
  have hc' : cls Q.L Q.isLB = pull a (cls P.L P.isLB) := (cls_eq_iff Q.isLB (pull_isLB P.isLB a)).2 hb
  have hA : HypS A _ := GlobalTheory.SymLevelDescent.hypS_descend i abA HQA hLA Q.isLB
    ((cls_eq_iff Q.isLB (pull_isLB hLA j)).1 (by
      rw [hc', hc, ← pull_comp, ← j₁, pull_comp, pull_comp]
      rfl)) e₁ e₂ hw hwd hs hp ‹_›
  have hG : HypS G _ := hypS_noetherian G abG _ hLG (PolBaseChange.rigidified_pull HG hr) hA
  have w₂ : φ ≫ B.hom = (P.A.hom ≫ spMap τ) ≫ spMap σ := by
    rw [Category.assoc, spMap_comp_eq hσ, H.1.w]
  have k₁ := HG.1.lift_fst _ _ w₂
  refine SymBaseChange.hypS_baseChange _ _ G P.A (spMap τ) (HG.1.lift _ _ w₂) _ _ hLG P.isLB
    (HG.cancel (H.congr (spMap_comp_eq hσ).symm k₁.symm) (HG.1.lift_snd _ _ w₂)) ?_ hG
  exact GlobalTheory.KeyTf.lbIso_pull_pull_of_comp P.isLB hL k₁ iso

end GlobalTheory.Poinc.HypSExt

theorem GlobalTheory.Poinc.hypS_of_generic_ringOn : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → GlobalTheory.IsNormalScheme M.Z → ∀ (R₀ : Type) [CommRing R₀] (P : PolAV (Sp R₀)) (P' : PolAV (Sp (M.ringOn U))) (P₀ : PolAV (Sp Ω)) (f : R₀ →+* Ω) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap f) a → IsGrpPullback P₀.A P'.A (spMap (M.ringOn U).val.toRingHom) a' → LBIso P₀.L (P.L.pull a) → LBIso P₀.L (P'.L.pull a') → HypS P.A P.L → HypS P'.A P'.L := by
  intro o Ω _ _ _ M U hU hne hN R₀ _ P P' P₀ f a a' ha ha' hL hL' h
  have := RatModel.isFractionRing_ringOn hU hne
  have : IsIntegrallyClosed (M.ringOn U) := by
    refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, ?_⟩, rfl⟩
    refine Algebra.mem_iInf.2 fun z => Algebra.mem_iInf.2 fun hz => ?_
    have := RatModel.isIntegrallyClosed_O (GlobalTheory.IsNormalScheme.pred M.Z) z
    have hle : M.ringOn U ≤ M.O z := iInf₂_le z hz
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := M.O z) (K := Ω)
      (IsIntegral.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id Ω) rfl hx)
    exact y.2
  exact HypSExt.hypS_normal P' P₀ a' ha' hL'
    (SymBaseChange.hypS_baseChange _ _ _ _ _ a _ _ P.isLB P₀.isLB ha hL h)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

section Descent

variable {X Y : Scheme.{0}}

lemma appLE_eq_of_eq_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

lemma opens_toTop_bijective (U : X.Opens) : Function.Bijective (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  have e : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso U.topIso.inv

example (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens) :
    Flat (p ∣_ V) ∧ Surjective (p ∣_ V) ∧ IsAffineHom (p ∣_ V) :=
  ⟨inferInstance, IsZariskiLocalAtTarget.restrict ‹_› V, by first | exact HasAffineProperty.restrict ‹_› V | exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V | exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict p V).flip ‹_›) | exact (inferInstance : IsAffineHom (p.resLE V (p ⁻¹ᵁ V) le_rfl))⟩

lemma restrict_appTop_toTop (p : X ⟶ Y) (V : Y.Opens) (a : Γ(Y, V)) :
    (p ∣_ V).appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge a) =
      (p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge (p.app V a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg _ (appLE_eq_of_eq_hom (morphismRestrict_ι p V) _ _ _)

lemma restrict_props (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens) :
    Flat (p ∣_ V) ∧ Surjective (p ∣_ V) ∧ IsAffineHom (p ∣_ V) :=
  ⟨inferInstance, IsZariskiLocalAtTarget.restrict ‹_› V, by first | exact HasAffineProperty.restrict ‹_› V | exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V | exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict p V).flip ‹_›) | exact (inferInstance : IsAffineHom (p.resLE V (p ⁻¹ᵁ V) le_rfl))⟩

lemma appTop_toTop (V : X.Opens) {Z : Scheme.{0}} (y : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    y.appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge s) =
      (y ≫ V.ι).appLE V ⊤ (fun z _ => (y z).2) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem exists_app_eq_of_invariant (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens)
    (s : Γ(X, p ⁻¹ᵁ V))
    (hs : ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (h₁ : ⊤ ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ V))
      (h₂ : ⊤ ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ V)), y₁.appLE _ ⊤ h₁ s = y₂.appLE _ ⊤ h₂ s) :
    ∃ a : Γ(Y, V), p.app V a = s := by
  obtain ⟨h1, h2, h3⟩ := restrict_props p V
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen (p ∣_ V)
    ((p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge s) (fun y₁ y₂ h => by
      rw [appTop_toTop, appTop_toTop]
      refine hs _ _ _ ?_ _ _
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, h, Category.assoc])
  obtain ⟨a, rfl⟩ := (opens_toTop_bijective V).2 v
  refine ⟨a, (opens_toTop_bijective (p ⁻¹ᵁ V)).1 ?_⟩
  rw [← restrict_appTop_toTop]
  exact hv

lemma app_map_homOfLE (p : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    p.app V (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (fun _ hx => h hx : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U)).op (p.app U a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

end Descent

open ReciprocityTheory.ChartRestriction.G.DVR.TG in

theorem triv_of_isPullGen_of_invariant : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  intro X Y p _ _ _ M e he hinv
  have hval : ∀ (k : M.ι) (u : Γ(X, p ⁻¹ᵁ M.U k)ˣ), (u = e k ∨ u = (e k)⁻¹) →
      ∃ a : Γ(Y, M.U k), p.app _ a = u := by
    intro k u hu
    refine exists_app_eq_of_invariant p (M.U k) u ?_
    intro Z y₁ y₂ hy h₁ h₂
    have H := hinv Z y₁ y₂ hy k ⊤ h₁ h₂
    rcases hu with rfl | rfl
    · exact congrArg Units.val H
    · have H' := congrArg (fun x => x⁻¹) H
      simp only [← map_inv] at H'
      exact congrArg Units.val H'
  choose f hf using fun k => hval k (e k) (Or.inl rfl)
  choose f' hf' using fun k => hval k (e k)⁻¹ (Or.inr rfl)
  have inj := fun V => app_injective_of_flat_surj p V
  have hmul : ∀ k, f k * f' k = 1 := fun k =>
    inj _ (by rw [map_mul, map_one, hf, hf', Units.mul_inv])
  let fu : ∀ k, Γ(Y, M.U k)ˣ := fun k => ⟨f k, f' k, hmul k, by rw [mul_comm]; exact hmul k⟩
  refine ⟨⟨fu⟩, fun i j => Units.ext (inj _ ?_)⟩
  have H := congrArg Units.val
    (he i j (p ⁻¹ᵁ (M.U i ⊓ M.U j)) (fun _ hx => hx.1) (fun _ hx => hx.2) le_rfl)
  have eX : ∀ {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ),
      ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eY : ∀ {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)ˣ),
      ((res h a : Γ(Y, V)ˣ) : Γ(Y, V)) = Y.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eP : ((pullU p (M.U i ⊓ M.U j) (M.g i j) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))ˣ) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))) =
      p.app _ (M.g i j) := rfl
  have eid : X.presheaf.map (homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ p ⁻¹ᵁ (M.U i ⊓ M.U j))).op =
      𝟙 _ := by
    rw [show homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ _) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  simp only [Units.val_mul, eX, eP] at H
  rw [eid, CommRingCat.id_apply] at H
  simp only [Units.val_mul, map_mul, eY, app_map_homOfLE]
  show X.presheaf.map _ (p.app _ (f i)) = _ * X.presheaf.map _ (p.app _ (f j))
  rw [hf, hf]
  exact H

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVani
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.CotIndep

open IsLocalRing TensorProduct

theorem tmul_D_eq_zero_of_mem_sq (k P : Type*) [CommRing k] [CommRing P] [IsLocalRing P]
    [Algebra k P] {x : P} (hx : x ∈ maximalIdeal P ^ 2) :
    (1 : ResidueField P) ⊗ₜ[P] KaehlerDifferential.D k P x = 0 := by
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := ker_residue
  have hx' : x ∈ RingHom.ker (algebraMap P (ResidueField P)) := by
    rw [hker]; exact Ideal.pow_le_self two_ne_zero hx
  have h0 : (RingHom.ker (algebraMap P (ResidueField P))).toCotangent ⟨x, hx'⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    change x ∈ _ ^ 2
    rw [hker]; exact hx
  have := congrArg (KaehlerDifferential.kerCotangentToTensor k P (ResidueField P)) h0
  rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero] at this

theorem linearIndependent_toCotangent {k A P : Type*} [CommRing k] [CommRing A] [CommRing P]
    [IsLocalRing P] (α : k →+* A) (ρ : A →+* P)
    (hρ : letI := ρ.toAlgebra; Algebra.FormallyEtale A P) {n : ℕ} (z : Fin n → A)
    (hω : IsFreeGen A (dForm α z)) (J : Finset (Fin n))
    (hz : ∀ j : J, ρ (z j) ∈ maximalIdeal P) :
    LinearIndependent (ResidueField P)
      (fun j : J => ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P)) := by
  classical
  have h1 : IsFreeGen P (dForm (ρ.comp α) fun i => ρ (z i)) := by
    have := MorJac.isFreeGen_formMap (D := n) hρ rfl hω
    rwa [formMap_dForm] at this
  letI := (ρ.comp α).toAlgebra
  set κ := ResidueField P
  let φ : Omega (ρ.comp α) →ₗ[P] κ ⊗[P] Omega (ρ.comp α) := TensorProduct.mk P κ _ 1
  have h2 := h1.of_isBaseChange
    (isBaseChange_exteriorPower (TensorProduct.isBaseChange P (Omega (ρ.comp α)) κ) n)
  rw [dForm_eq, exteriorPowerMapOver_ιMulti] at h2
  have h3 : exteriorPower.ιMulti κ n (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact one_ne_zero (h2.1 (a₁ := (1 : κ)) (a₂ := 0) (by simp))
  have h4 : LinearIndependent κ (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) := by
    by_contra h
    exact h3 (AlternatingMap.map_linearDependent _ _ h)
  have h5 := h4.comp (Subtype.val : J → Fin n) Subtype.val_injective
  rw [Fintype.linearIndependent_iff] at h5 ⊢
  intro g hg i
  choose b hb using fun j => residue_surjective (R := P) (g j)
  have hsq : ∑ j : J, b j * ρ (z j) ∈ maximalIdeal P ^ 2 := by
    have e : ∑ j : J, g j • ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P) =
        (maximalIdeal P).toCotangent (∑ j : J, b j • (⟨ρ (z j), hz j⟩ : maximalIdeal P)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hb j, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rw [e, Ideal.toCotangent_eq_zero] at hg
    simpa [Submodule.coe_sum] using hg
  have h0 := tmul_D_eq_zero_of_mem_sq k P hsq
  have htk : ∀ j : J, algebraMap P κ (ρ (z j)) = 0 := fun j => by
    rw [ResidueField.algebraMap_eq]; exact (residue_eq_zero_iff _).2 (hz j)
  refine h5 g ?_ i
  rw [← h0, map_sum, tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
    Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, ← hb j, ← ResidueField.algebraMap_eq]
  change (algebraMap P κ (b j)) • ((1 : κ) ⊗ₜ[P] KaehlerDifferential.D k P (ρ (z j))) = _
  rw [smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.CotIndep

namespace GlobalTheory.CotIndep

theorem linearIndependent_cotangent_of_isFrame : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (y : Y) (hy : y ∈ U) (J : Finset (Fin n)) (hz : ∀ j : J, Y.presheaf.germ U y hy (z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : J => Y.presheaf.germ U y hy (z j)) j, hz j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hf y hy J hz
  exact linearIndependent_toCotangent (algX q U) (Y.presheaf.germ U y hy).hom
    (MorJac.formallyEtale_germ hf.affine y hy) z hf.gen J hz

end GlobalTheory.CotIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ratio_upper_bound : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) → Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, 0 < ratAt p i ∧ Real.log (ratAt p i) ≤ K * unitE p := by
  first | exact @GlobalTheory.CovTop.MeasRd.ratAt_upper | exact GlobalTheory.CovTop.MeasRd.ratAt_upper | (intros; apply GlobalTheory.CovTop.MeasRd.ratAt_upper <;> assumption)
end


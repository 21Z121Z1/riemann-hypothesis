import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFrames
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KeyFam

theorem GeomInt.mvPolynomial {k S : Type} [Field k] [CommRing S] [Algebra k S] (σ : Type) [Finite σ]
    (h : GeomInt k S) : GeomInt k (MvPolynomial σ S) := by
  have h₀ := h.1
  have h₁ : Algebra.Smooth S (MvPolynomial σ S) := ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.Smooth.comp k S _, fun K _ _ => ?_⟩
  have := h.2 K
  let e₁ : K ⊗[k] MvPolynomial σ S ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ((MvPolynomial.algebraTensorAlgEquiv k S).symm.restrictScalars k)
  let e₂ : (K ⊗[k] S) ⊗[k] MvPolynomial σ k ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.assoc k k k K S (MvPolynomial σ k)
  let e₃ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k (K ⊗[k] S)
  exact ((e₁.trans e₂.symm).toMulEquiv.trans e₃.toMulEquiv).isDomain _

theorem exists_univ_scalars {k S : Type} [Field k] [CommRing S] [Algebra k S] (h : GeomInt k S) (s : S →+* ℂ)
    (s₀ : S →ₐ[k] k) (n : ℕ) (a : ℂˣ) (N : Matrix (Fin n) (Fin n) ℂ) (hN : IsUnit N.det) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k)
      (b : S'ˣ) (M : Matrix (Fin n) (Fin n) S'), GeomInt k S' ∧ s'.comp j.toRingHom = s ∧ s₀'.comp j = s₀ ∧
      IsUnit M.det ∧ s' b = a ∧ ∀ i l, s' (M i l) = N i l := by
  let T := MvPolynomial (Option (Fin n × Fin n)) S
  let M₀ : Matrix (Fin n) (Fin n) T := fun i l => MvPolynomial.X (some (i, l))
  let r : T := MvPolynomial.X none * M₀.det
  have key : ∀ {L : Type} [CommRing L] (f : S →+* L) (c : L) (B : Matrix (Fin n) (Fin n) L),
      ∃ F : T →+* L, (∀ z, F (MvPolynomial.C z) = f z) ∧ F (MvPolynomial.X none) = c ∧
        (∀ i l, F (M₀ i l) = B i l) ∧ F r = c * B.det := by
    intro L _ f c B
    let F : T →+* L := MvPolynomial.eval₂Hom f (fun o => o.elim c fun p => B p.1 p.2)
    have h₁ : F (MvPolynomial.X none) = c := MvPolynomial.eval₂Hom_X' _ _ _
    have h₂ : ∀ i l, F (M₀ i l) = B i l := fun i l => MvPolynomial.eval₂Hom_X' _ _ _
    refine ⟨F, fun z => MvPolynomial.eval₂Hom_C _ _ _, h₁, h₂, ?_⟩
    rw [map_mul, h₁, RingHom.map_det]
    congr 2
    ext i l
    exact h₂ i l
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄⟩ := key s a N
  obtain ⟨G, hG₁, -, -, hG₄⟩ := key s₀.toRingHom 1 1
  have uF : IsUnit (F r) := hF₄ ▸ a.isUnit.mul hN
  have uG : IsUnit (G r) := by rw [hG₄]; simp
  have hr : r ≠ 0 := fun e => uG.ne_zero (by rw [e, map_zero])
  let S' := Localization.Away r
  have ur : IsUnit (algebraMap T S' r) := IsLocalization.Away.algebraMap_isUnit r
  rw [map_mul, IsUnit.mul_iff] at ur
  obtain ⟨⟨b, hb⟩, uM⟩ := ur
  let j : S →ₐ[k] S' := (IsScalarTower.toAlgHom k T S').comp (IsScalarTower.toAlgHom k S T)
  have hj : ∀ z, j z = algebraMap T S' (MvPolynomial.C z) := fun _ => rfl
  let g₀ : S' →+* k := IsLocalization.Away.lift r uG
  have hg : ∀ z, g₀ (j z) = s₀ z := fun z => by
    rw [hj, IsLocalization.Away.lift_eq, hG₁]; rfl
  refine ⟨S', inferInstance, inferInstance, j, IsLocalization.Away.lift r uF,
    { g₀ with commutes' := fun c => ?_ }, b, (algebraMap T S').mapMatrix M₀,
    (GlobalTheory.KeyFam.geomInt_baseChange_and_away k k T (h.mvPolynomial _)).2 r hr, RingHom.ext fun z => ?_, AlgHom.ext hg, ?_, ?_, fun i l => ?_⟩
  · change g₀ _ = _
    rw [← j.commutes, hg, s₀.commutes]
  · change IsLocalization.Away.lift r uF (j z) = _
    rw [hj, IsLocalization.Away.lift_eq, hF₁]
  · rwa [← RingHom.map_det]
  · rw [hb, IsLocalization.Away.lift_eq, hF₂]
  · change IsLocalization.Away.lift r uF (algebraMap T S' (M₀ i l)) = _
    rw [IsLocalization.Away.lift_eq, hF₃]

theorem exists_polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := h
  exact ⟨φ, hp, hg, w, hw⟩

theorem exists_univ_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  intro hL k S _ _ _ y x s φ s₀ hS hφ
  obtain ⟨Q, hg, rig', hr', th', hth', v', hv'⟩ := x
  dsimp only at φ hφ
  obtain ⟨rig, hr, th, hth, v, hv, H⟩ := KeyTf.exists_keyPB_on S ℂ s y Q φ hg hφ.2.1 hφ.1 hφ.2.2
  obtain ⟨a, t, ht, hat, Hid⟩ := (KeyOnPol.main hL ℂ).2 ⟨Q, hg, rig, hr, th, hth, v, hv⟩ rig' hr' th' hth' v' hv'
  choose N hN using fun i => (hv.2 _ (hv'.1 i)).exists
  have := Q.isAb.comm
  have uN : IsUnit (Matrix.det (N : Matrix _ _ ℂ)) :=
    ((LieComb.lieComb_algebra ℂ Q.A Q.g v hv.1).2.2.2.2 N v' hv hN).1 hv'
  obtain ⟨S', _, _, j, s', s₀', b, M, hS', hs, hs₀, uM, hb, hM⟩ := exists_univ_scalars hS s s₀ Q.g a N uN
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y j.toRingHom
  have H₂ := KeyCancel.keyPB_cancel _ _ _ y y₁ _ _ s' H₁ (hs ▸ H)
  obtain ⟨ψ, hψ⟩ := exists_polPB_of_keyPB H₁
  have e : Q.g = y₁.P.g := KeyGalDesc.g_eq H₂
  have := y₁.P.isAb.comm
  let M' : Matrix (Fin y₁.P.g) (Fin y₁.P.g) S' := Matrix.reindex (finCongr e) (finCongr e) M
  have uM' : IsUnit M'.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := LieComb.lieComb_algebra S' y₁.P.A y₁.P.g y₁.v y₁.basis.1
  choose v₁ hv₁ using fun i => (ex (M' i)).exists
  obtain ⟨t₁, ht₁, -, hle⟩ := exists_sec_div y₁.P.A.hom b.inv_mul y₁.th
  refine ⟨S', _, _, j, ⟨y₁.P, y₁.g_pos, y₁.rig, y₁.rig_gen, t₁,
    fun p => (y₁.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁, (bas M' v₁ y₁.basis hv₁).2 uM'⟩, s', s₀', ψ, hS', ?_, hψ, hs₀⟩
  rw [← RingHom.id_comp s']
  refine keyPB_trans _ _ _ _ _ _ _ _ ?_ Hid
  refine KeyPBScale.keyPB_scale S' ℂ s' y₁.P y₁.g_pos y₁.rig y₁.rig_gen y₁.th y₁.th_ne y₁.v y₁.basis t₁ _ v₁ _ b M' Q e
    hg rig hr th hth v hv t ht v' hv' ht₁ hv₁ (hb ▸ hat) (fun i => ?_) H₂
  convert hN i using 2 with l
  exact hM i l

end GlobalTheory.KeyFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent : ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  first | exact @GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | exact GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | (intros; apply GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarisationOfFaithfullyFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.PolFlatDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem isCommMonObj_of_pull [Flat f] [Surjective f] (h : IsGrpPullback A' A f φ) [IsCommMonObj A'] :
    IsCommMonObj A := by
  refine ⟨GrpFlatDesc.hom_ext_of_points f fun T t => ?_⟩
  obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
  obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
  obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
    CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
  rw [lift_braiding_hom_assoc]
  exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
    ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))

theorem isAbelianScheme_of_pull [Flat f] [Surjective f] [QuasiCompact f] (h : IsGrpPullback A' A f φ)
    (hA : IsAbelianScheme A') : IsAbelianScheme A := by
  have := hA.comm
  have := hA.proper
  have := hA.geomConnected
  exact ⟨isCommMonObj_of_pull h, MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hA.smooth,
    GrpFlatDesc.isProper_of_isPullback h.1, GrpFlatDesc.geometricallyConnected_of_isPullback h.1⟩

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem exists_gen_pull_of_sym (hG : Out.GlobalFnsSt) (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A')
    {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hS : Out.Sym A' L')
    {Y : Scheme.{0}} (r : Y ⟶ A'.left) :
    ∃ t : ((LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1]).pull (r ≫ φ)).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc⟩ := exists_gen_neg_of_sym hG hA hL' hS
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![r ≫ (GrpObj.inv : A' ⟶ A').left, r] _ _ r fun k => by
    fin_cases k
    · rfl
    · exact (Category.comp_id r).symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  exact gen_chartPull (chartPullOut L _ _ (r ≫ φ) _ fun k => by
      fin_cases k
      · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (inv_left_comp h)).trans (Category.assoc _ _ _).symm)
      · exact (Category.comp_id _).symm) c₂ h₂

theorem polarisation_of_faithfullyFlat : Out.Laws → ∀ (R₀ R : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [IsPrincipalIdealRing R₀] [CommRing R] [IsNoetherianRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (P : Out.PolAV (Sp R)) (A₀ : Over (Sp R₀)) [GrpObj A₀] [Flat A₀.hom] (L₀ : LB A₀.left) (π : P.A.left ⟶ A₀.left), IsProjBy A₀.hom → L₀.IsLB → IsGrpPullback P.A A₀ (spMap (algebraMap R₀ R)) π → LBIso P.L (L₀.pull π) → IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ Out.Rigidified A₀ L₀ ∧ Out.Sym A₀ L₀ ∧ Out.RelAmple A₀ L₀ ∧ Out.KTriv A₀ L₀ := by
  intro hL R₀ R _ _ _ _ _ _ _ _ P A₀ _ _ L₀ π _ hL₀ h hw
  have : Flat (spMap (algebraMap R₀ R)) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap (algebraMap R₀ R)) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have hA : IsAbelianScheme A₀ := isAbelianScheme_of_pull h P.isAb
  have := hA.smooth
  have := hA.proper
  have := P.isAb.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A₀.hom hA.smooth hA.geomConnected
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R₀) (B := R) ⊥
  let β : R →+* q.asIdeal.ResidueField := algebraMap _ _
  have hj : Function.Injective (β.comp (algebraMap R₀ R)) := by
    rw [RingHom.injective_iff_ker_eq_bot, ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
    exact congrArg PrimeSpectrum.asIdeal hq
  have H : IsPullback (pullback.fst P.A.hom (spMap β) ≫ π) (pullback.snd P.A.hom (spMap β)) A₀.hom
      (spMap (β.comp (algebraMap R₀ R))) := by
    rw [show spMap (β.comp (algebraMap R₀ R)) = spMap β ≫ spMap (algebraMap R₀ R) from
      Spec.map_comp (CommRingCat.ofHom (algebraMap R₀ R)) (CommRingCat.ofHom β)]
    exact (IsPullback.of_hasPullback P.A.hom (spMap β)).paste_horiz h.1
  refine ⟨hA, ?_, DVR.exists_gen_of_local L₀ hL₀ _ _, ?_, ?_, AmpleDescent.kTriv_of_pull h hL₀ P.isLB hw P.ktriv⟩
  · exact CM.smoothOfRelativeDimension_of_fibre R₀ _ _ A₀ _ _ _ P.g hA H
      ((smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback
        (IsPullback.of_hasPullback P.A.hom (spMap β)) P.smoothDim)
  · have hN := DVR.linComb_isLB L₀ hL₀ (K := Fin 2) ![(GrpObj.inv : A₀ ⟶ A₀).left, 𝟙 _] ![1, -1]
    obtain ⟨ρ, hρ⟩ := DVR.exists_gen_of_local (V := R₀) _ hN (K := PUnit) (fun _ => eSec A₀) (fun _ => 1)
    obtain ⟨t, ht⟩ := exists_gen_pull_of_sym hL.globalFns h P.isAb hL₀ P.isLB hw P.sym
      (pullback.fst P.A.hom (spMap β))
    obtain ⟨c, hc⟩ := GenericTriv.exists_gen_of_fibre _ hj A₀.hom (eSec A₀) (Over.w η[A₀]) _ _ H
      (Out.TLinPf.const_pullback hL.globalFns (spMap β) P.A P.isAb) hN ρ hρ t ht
    intro s
    refine ⟨⊤, trivial, gen_chartPull (chartPullSame L₀ _ _ _ (A₀.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c hc⟩
    fin_cases k
    · rfl
    · exact (Category.comp_id _).symm
  · have : Flat (Out.specOf (algebraMap R₀ R)) := ‹Flat (spMap (algebraMap R₀ R))›
    have : Surjective (Out.specOf (algebraMap R₀ R)) := ‹Surjective (spMap (algebraMap R₀ R))›
    refine (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull _ h.1 hL₀ ?_)
    exact (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).of_lbIso (LB.isLB_pull hL₀ π) hw.symm

end GlobalTheory.PolFlatDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_polarizedPullback : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownScale.known_of_polPB | exact GlobalTheory.KnownScale.known_of_polPB | (intros; apply GlobalTheory.KnownScale.known_of_polPB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZerosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (n r : ℕ) (s : Fin r → RR x n) (W : Set x.P.A.left), 1 ≤ n → IsClosed W → W.Nonempty → {y ∈ W | ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → topologicalKrullDim W ≤ r := by
  first | exact @GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros | exact GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros | (intros; apply GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VeryAmpleByDescendsCountableSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

open ProjSpace in

theorem exists_finset_isPullback_toImage_baseChange (R : Type) [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    {N : ℕ} (e : X ⟶ PSpace R N) [IsClosedImmersion e] :
    ∃ c : Finset R, ∀ R₀ : Subring R, (c : Set R) ⊆ R₀ →
      IsPullback (e ≫ baseChange N R₀.subtype).toImage (e ≫ PSpace.str R N)
        ((e ≫ baseChange N R₀.subtype).imageι ≫ PSpace.str R₀ N) (spMap R₀.subtype) := by
  classical
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} R),
      Ideal.span (chartAlgEquiv R N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart R N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart R N i⟩).comap (chartAlgEquiv R N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv R N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv R N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun R₀ hs => ?_⟩
  have key := comap_map_baseChange N R₀.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N R₀.subtype).imageι
    (e ≫ baseChange N R₀.subtype).toImage (baseChange N R₀.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N R₀.subtype)

open ProjSpace in

theorem veryAmpleBy_descends_countable_subring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Flat f] (H : LB X) (m : ℕ) (s : Fin (m + 1) → H.Sec) (S : Set R), H.IsLB → VeryAmpleBy f H s → S.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) (H₀ : LB X₀) (s₀ : Fin (m + 1) → H₀.Sec), Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R ∧ IsPullback π f f₀ (spMap R₀.subtype) ∧ Flat f₀ ∧ H₀.IsLB ∧ VeryAmpleBy f₀ H₀ s₀ ∧ LBIso H (H₀.pull π) := by
  intro R _ _ _ _ X f hf H m s S hH hs hS
  obtain ⟨hs, he⟩ := (veryAmpleBy_iff f s).1 hs
  obtain ⟨c, hc⟩ := exists_finset_isPullback_toImage_baseChange R (toProj f s hs)
  obtain ⟨R₀, i₁, i₂, h₁, h₂, h₃, h₄⟩ := GlobalTheory.exists_countable_local_pid_subring R (S ∪ c) (hS.union c.countable_toSet)
  have hp := hc R₀ (Set.subset_union_right.trans h₂)
  rw [toProj_str] at hp
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap R₀.subtype) := by
    have h : RingHom.FaithfullyFlat (CommRingCat.ofHom R₀.subtype).hom :=
      RingHom.faithfullyFlat_algebraMap_iff.2 h₄
    rw [← flat_and_surjective_SpecMap_iff] at h
    exact ⟨⟨h.2, h.1⟩, inferInstance⟩
  have := flat_descendsAlong_fpqc
  have hL := O1_isLB R₀ m
  refine ⟨R₀, i₁, i₂, _, _, _, _, _, h₁, Set.subset_union_left.trans h₂, h₃, h₄, hp,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hp.flip hσ hf,
    LB.isLB_pull hL _, veryAmpleBy_secPull_coord _, ?_⟩
  refine LBIso.trans hH (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _)
    (lbIso_pullback_O1_toProj (f ≫ spMap R₀.subtype) s hs).symm (GenSpread.lbIso_pull_pull hL _ ?_)
  rw [Scheme.Hom.toImage_imageι, toProj_baseChange]

end GlobalTheory
end


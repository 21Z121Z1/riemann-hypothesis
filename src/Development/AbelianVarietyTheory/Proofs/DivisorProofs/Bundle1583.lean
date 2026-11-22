import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.FODef

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem sqZero : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0 := by
  rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Submodule.mem_bot]
  ext
  · simp [hr, hs]
  · simp [hr, hs]

theorem constMorV (A₀ : Over (Sp k)) [GrpObj A₀] :
    GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
      congr 1) (𝟙 A₀)

variable {k V}

def IsFilLiftV {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (TrivSqZeroExt k V))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) i)
    (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) : Prop :=
  ∃ d ∈ liftFil (divided₂ (sqZero k V)) h, ∀ c : primDR A₀,
    d ((constMorV k V A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c)

end GlobalTheory.FODef

namespace GlobalTheory.HTUniv

theorem coord {k : Type} [Field k] {d : ℕ} (c : (Fin d → k) →ₗ[k] k) (v : Fin d → k) :
    c v = ∑ j, v j * c (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Pi.single j (v j) = v j • (Pi.single j (1 : k) : Fin d → k) := by
    ext i; simp [Pi.single_apply]
  rw [e, map_smul, smul_eq_mul]

theorem comp_pi {k : Type} [Field k] {d : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (c : (Fin d → k) →ₗ[k] k) (y : Fin d → (P →ₗ[k] k)) :
    c ∘ₗ LinearMap.pi y = ∑ j, c (Pi.single j 1) • y j := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.comp_apply, coord c, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pi_apply, smul_eq_mul, mul_comm]

theorem sum_proj_single {k : Type} [Field k] {d : ℕ} (c₀ : Fin d → k) (j : Fin d) :
    (∑ i, c₀ i • LinearMap.proj (R := k) (φ := fun _ : Fin d => k) i) (Pi.single j 1) = c₀ j := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try exact mul_one _

end GlobalTheory.HTUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefectStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.SymTranslate.sym_rigTransl_of_sq | exact GlobalTheory.SymTranslate.sym_rigTransl_of_sq | (intros; apply GlobalTheory.SymTranslate.sym_rigTransl_of_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tate_free_of_card :
    ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M] (r : ℕ), (∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (r * n)) → Nonempty (Tate p M ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) ∧ (∀ (n : ℕ) (x : M), x ^ p ^ n = 1 → ∃ t : Tate p M, t.lev n = x) ∧ ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s := by
  intro p _ M _ r h
  obtain ⟨T, _, _, π, hfree, hfin, hrk, hs, h0, hsm, hon, hker, huniq⟩ :=
    GlobalTheory.exists_tateModule_of_card (Additive M) p r (fun n => by
      rw [← h n]
      exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl))
  have hkill : ∀ n x, p ^ n • π n x = 0 := fun n x => by
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [pow_succ, mul_smul, hs, ih]
  let f : T →ₗ[ℤ_[p]] Tate p M :=
    { toFun := fun x => Tate.mk (fun n => Additive.toMul (π n x)) fun n =>
        ⟨congrArg Additive.toMul (hkill n x), congrArg Additive.toMul (hs n x)⟩
      map_add' := fun x y => Tate.ext fun n => congrArg Additive.toMul (map_add (π n) x y)
      map_smul' := fun a x => Tate.ext fun n => congrArg Additive.toMul (hsm n a x) }
  have hf : ∀ x n, (f x).lev n = Additive.toMul (π n x) := fun _ _ => rfl
  have hu : ∀ t : Tate p M, ∃! x, ∀ n, π n x = Additive.ofMul (t.lev n) := fun t =>
    huniq (fun n => Additive.ofMul (t.lev n))
      (by have := t.lev_pow 0
          rw [pow_zero, pow_one] at this
          rw [this]; rfl)
      (fun n => congrArg Additive.ofMul (t.lev_succ n))
  have hsurj : Function.Surjective f := fun t => by
    obtain ⟨x, hx, -⟩ := hu t
    exact ⟨x, Tate.ext fun n => by rw [hf, hx]; rfl⟩
  have hinj : Function.Injective f := fun x y hxy =>
    (hu (f y)).unique (fun n => by rw [← hxy]; rfl) (fun n => rfl)
  refine ⟨⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hrk))⟩, fun n x hx => ?_, fun n t => ?_⟩
  · obtain ⟨y, hy⟩ := hon n (Additive.ofMul x) (congrArg Additive.ofMul hx)
    exact ⟨f y, by rw [hf, hy]; rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj t
    have key : ∀ y : T, f (p ^ n • y) = (p : ℤ_[p]) ^ n • f y := fun y => by
      rw [map_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine Iff.trans (hker n x) ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨f y, key y⟩
    · rintro ⟨s, hs'⟩
      obtain ⟨y, rfl⟩ := hsurj s
      exact ⟨y, hinj (hs'.trans (key y).symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaExtend

theorem isRegularRing_sections {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsRegularRing Γ(Y, V) := by
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  rw [isRegularRing_iff]
  intro q hq
  let y : PrimeSpectrum Γ(Y, V) := ⟨q, hq⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (hV.fromSpec y)) :=
    Y.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
  have h : IsLocalization q.primeCompl (Y.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  have := hY (hV.fromSpec y)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_stalk {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (f : X ⟶ Y) [Smooth f] (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  have hs : (f.appLE V U hUV).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have := isRegularRing_sections hY hV
  algebraize [(f.appLE V U hUV).hom]
  have : IsRegularRing Γ(X, U) := isRegularRing_of_smooth Γ(Y, V) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact ExtendRig.isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem ufd_of_regular (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE R

theorem hasTheta_of_generic {Y : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (P : PPAS Y) (Q : PPAS (Sp Y.functionField))
    (ψ : Q.A.left ⟶ P.A.left) (hQ : Q.IsPull P (Y.fromSpecStalk (genericPoint Y)) ψ)
    (hT : Q.HasTheta) : P.HasTheta := by
  obtain ⟨h, hc⟩ := hQ
  obtain ⟨L₀, hL₀, hs, hp⟩ := hT
  let j : Sp Y.functionField ⟶ Y := Y.fromSpecStalk (genericPoint Y)
  have hj₁ : IsPreimmersion j := inferInstanceAs (IsPreimmersion (Y.fromSpecStalk _))
  have hj₂ : Flat j := GenericExt.flat_fromSpecStalk Y _
  have hj₃ : IsDominant j := ⟨by
    refine Dense.mono (s₁ := {genericPoint Y}) ?_ (dense_iff_closure_eq.2 (genericPoint_spec Y))
    rintro _ rfl
    exact ⟨_, Scheme.fromSpecStalk_closedPoint⟩⟩
  have hj₄ : QuasiCompact j := inferInstance
  have hn : Geo.Tor.IsNormalScheme Y := fun y => by
    have := isRegularRing_stalk hY (𝟙 Y) y
    have := ufd_of_regular (Y.presheaf.stalk y)
    exact ⟨inferInstance, inferInstance⟩
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian P.A.hom
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have := Q.isAb.smooth
  have := Q.isAb.geomConnected
  have : GeometricallyIntegral Q.A.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral Q.A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian Q.A.hom
  have : IsPreimmersion ψ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h.1.flip hj₁
  have : Flat ψ := MorphismProperty.of_isPullback (P := @Flat) h.1.flip hj₂
  obtain ⟨L, hL, hLL⟩ := exists_lineBundle_extension_of_generalizing P.A.left Q.A.left ψ
    (Flat.generalizingMap ψ) (fun x => have := isRegularRing_stalk hY P.A.hom x; ufd_of_regular _) L₀ hL₀
  have e₀ : pull ψ (cls L hL) = cls L₀ hL₀ := (cls_eq_iff (pull_isLB hL ψ) hL₀).2 hLL
  let κ : ∀ {T : Over Y}, (T ⟶ P.A) → (pullback T.hom j ⟶ Q.A.left) := fun {T} a =>
    h.1.lift (pullback.fst _ _ ≫ a.left) (pullback.snd _ _) (by
      rw [Category.assoc, Over.w]; exact pullback.condition)
  have κ₁ : ∀ {T : Over Y} (a : T ⟶ P.A), κ a ≫ ψ = pullback.fst _ _ ≫ a.left := fun a =>
    h.1.lift_fst _ _ _
  have κ₂ : ∀ {T : Over Y} (a : T ⟶ P.A), κ a ≫ Q.A.hom = pullback.snd _ _ := fun a =>
    h.1.lift_snd _ _ _
  refine ⟨L, hL, OddDescent.sym_of_pull_inv_cls P.A hL ?_, ?_⟩
  · refine ZH.EndoExtend.pic_ext j hn P.A (eSec P.A) (Over.w η[P.A]) ?_ ?_
    · rw [← pull_comp, OddDescent.eSec_inv]
    · have e : pullback.fst P.A.hom j = κ (𝟙 _) ≫ ψ := ((κ₁ _).trans (Category.comp_id _)).symm
      rw [e, pull_comp, pull_comp, ← pull_comp ψ, ← OddDescent.inv_left_comp h, pull_comp, e₀,
        OddDescent.pull_inv_cls_of_sym Q.A hL₀ hs]
  · have := smooth_tensorObj_hom P.A P.A
    have := geometricallyIntegral_tensorObj_hom P.A P.A
    refine ZH.EndoExtend.pic_ext j hn (P.A ⊗ P.A) (η[P.A] ≫ lift (1 : P.A ⟶ P.A) (𝟙 P.A)).left
      (Over.w _) ?_ ?_
    · rw [Over.comp_left, pull_comp, pull_comp, P.isPol.1, pull_lam, lift_fst, lam_one_left]
    · let δ : pullback (P.A ⊗ P.A).hom j ⟶ (Q.A ⊗ Q.A).left :=
        pullback.lift (κ (fst _ _)) (κ (snd _ _)) ((κ₂ _).trans (κ₂ _).symm)
      have e : pullback.fst (P.A ⊗ P.A).hom j = δ ≫ sqMap h.1.w := by
        apply pullback.hom_ext
        · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, δ, pullback.lift_fst_assoc]
          exact (κ₁ (fst P.A P.A)).symm
        · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, δ, pullback.lift_snd_assoc]
          exact (κ₁ (snd P.A P.A)).symm
      rw [e, pull_comp, pull_comp, ← hc, hp, PPAS.pull_sqMap_lam h, e₀]

theorem hasTheta_of_regSurf : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsRegSurf q → ∀ P : PPAS Y, (∃ (Q : PPAS (Sp Y.functionField)) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (Y.fromSpecStalk (genericPoint Y)) ψ ∧ Q.HasTheta) → P.HasTheta := by
  rintro k _ Y _ q hq P ⟨Q, ψ, hQ, hT⟩
  have := hq.toIsArithVar.isNoetherian
  exact hasTheta_of_generic hq.regular P Q ψ hQ hT

end GlobalTheory.ThetaExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqOfReal
section
open NumberField Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_eq_of_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), IsStdChar D ψ (-1) →
    ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      (∀ w : WO V W, w.map (finPart D) = 0 → f w = f' w) → f = f' := by
  intro D ψ V W _ f f' hf hf' h
  have h0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real
    (GlobalTheory.WeilVacMove.isTheta_add hf (GlobalTheory.WeilVacMove.isTheta_smul (-1) hf')) fun w hw => by
      rw [Pi.add_apply, Pi.smul_apply, h w hw, neg_one_smul, add_neg_cancel]
  rwa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

def part (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ 1, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

def total (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : ℝ :=
  (part ρ univ).toReal - (part (fun c y => -ρ c y) univ).toReal

variable {ρ ρ' : AlgChart p σ 1 → CxPts p σ → ℝ}

theorem part_congr (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ρ' c y) :
    part ρ = part ρ' := by
  unfold part ChartGlue.glueMeas
  refine iSup_congr fun c => Measure.ext fun A hA => ?_
  rw [ChartGlue.chartMeas_apply _ _ hA, ChartGlue.chartMeas_apply _ _ hA]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _
    (c.e.open_source.measurableSet.inter hA) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1, h c y hy.1]

theorem total_congr (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ρ' c y) :
    total ρ = total ρ' := by
  rw [total, total, part_congr h,
    part_congr (ρ := fun c y => -ρ c y) (ρ' := fun c y => -ρ' c y) fun c y hy => by rw [h c y hy]]

theorem part_eq_zero (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y ≤ 0) : part ρ = 0 := by
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [ChartGlue.chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  exact ENNReal.ofReal_eq_zero.2 (h c _ (c.e.map_target hv))

theorem total_eq_of_nonneg (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 ≤ ρ c y) :
    total ρ = (part ρ univ).toReal := by
  rw [total, part_eq_zero (ρ := fun c y => -ρ c y) fun c y hy => neg_nonpos.2 (h c y hy)]
  simp

theorem IsDens.part_apply [SecondCountableTopology (CxPts p σ)] (h : IsDens ρ) (c : AlgChart p σ 1)
    {T : Set (CxPts p σ)} (hT : MeasurableSet T) (hc : T ⊆ c.e.source) :
    part ρ T = ∫⁻ v in c.e '' T, ENNReal.ofReal (ρ c (c.e.symm v)) := by
  rw [part, ChartGlue.glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [h.1 c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hT hc,
    ChartGlue.chartMeas_apply_of_subset _ _ hT hc]

theorem IsDens.add (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y + ρ' c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy', mul_add],
    fun c => (h.2 c).add (h'.2 c)⟩

theorem IsDens.sub (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y - ρ' c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy', mul_sub],
    fun c => (h.2 c).sub (h'.2 c)⟩

theorem IsDens.neg (h : IsDens ρ) : IsDens fun c y => -ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', mul_neg], fun c => (h.2 c).neg⟩

theorem IsDens.mul (h : IsDens ρ) {f : CxPts p σ → ℝ} (hf : Continuous f) :
    IsDens fun c y => f y * ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', mul_left_comm],
    fun c => (hf.comp_continuousOn c.e.continuousOn_symm).mul (h.2 c)⟩

theorem IsDens.congr (h : IsDens ρ) (e : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ' c y = ρ c y) :
    IsDens ρ' :=
  ⟨fun c c' y hy hy' => by rw [e c y hy, e c' y hy', h.1 c c' y hy hy'],
    fun c => (h.2 c).congr fun v hv => e c _ (c.e.map_target hv)⟩

theorem chernPart_eq {B : LB X} (φ : Weight p σ B) :
    φ.chernPart 1 1 = part (fun c y => c.chernDens φ y) ∧
      φ.chernPart 1 (-1) = part fun c y => -c.chernDens φ y := by
  constructor <;> simp [Weight.chernPart, part]

section BC

variable {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

theorem bcMeas_eq_part : h.bcMeas hS h₁ h₃ = part fun c y => h.bcDens hS h₁ h₃ c y := rfl

theorem isDens_bcDens (H : h.IsCInf) : IsDens fun c y => h.bcDens hS h₁ h₃ c y := by
  refine ⟨fun c c' y hy hy' => Met.bcDens_trans hS h₁ h₃ c c' H hy hy', fun c v hv => ?_⟩
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ (c.e.symm v)
  have hWo := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) a.U)
  have hK : ∀ w ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ a.U,
      MContDiffAt ∞ (fun v => h.gram a.frame (c.e.symm v)) w := fun w hw => by
    have := (H.gram a.frame hw.2).mContDiffAt c (c.e.map_target hw.1)
    rwa [c.e.right_inv hw.1] at this
  have hg := continuousOn_diagVal_extTrace hWo hK (fun w hw => h.posDef_gram_frame hS a hw.2)
    (EuclideanSpace.single 0 1)
  have hm := hWo.mem_nhds (show v ∈ _ from ⟨hv, ha⟩)
  refine ContinuousAt.continuousWithinAt
    (((continuousOn_const (c := (2 : ℝ))).mul hg).continuousAt hm |>.congr ?_)
  filter_upwards [hm] with w hw
  rw [Met.bcDens_eq hS h₁ h₃ a c H (c.e.map_target hw.1) hw.2, Met.bcForm, c.e.right_inv hw.1]
  rfl

theorem total_bcDens (H : h.IsCInf) :
    total (fun c y => h.bcDens hS h₁ h₃ c y) = (h.bcMeas hS h₁ h₃ univ).toReal :=
  total_eq_of_nonneg fun c _ hy => Met.bcDens_nonneg hS h₁ h₃ c H hy

end BC

def IsCosSq {V L L' : X.Modules} {r : ℕ} (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V)
    (v : CxPts p σ → ℝ) : Prop :=
  ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), ∀ y ∈ ptsIn p σ U,
    ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2 =
      v y * (h.form (l.app U t) (l.app U t) y).re * (h.form (l'.app U t') (l'.app U t') y).re

theorem IsCosSq.symm {V L L' : X.Modules} {r : ℕ} {h : Met p σ V r} {l : L ⟶ V} {l' : L' ⟶ V}
    {v : CxPts p σ → ℝ} (H : IsCosSq h l l' v) : IsCosSq h l' l v := fun U t' t y hy => by
  rw [← h.conj_form, Complex.norm_conj, H U t t' y hy, mul_right_comm]

def VanishesAt {F Q : X.Modules} (s : F ⟶ Q) (z : X) : Prop :=
  ∀ (U : X.Opens) (t : Γ(F, U)) (e : Γ(Q, U)) (b : Γ(X, U)), z ∈ U →
    IsFrame (fun _ : Fin 1 => e) → s.app U t = b • e → z ∉ X.basicOpen b

section Calc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

def angleForm (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) : ℂ :=
  ((‖q z‖ ^ 2 / (a z * a' z)) ^ n : ℝ) *
    (starRingEnd ℂ (q z) * (del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ) -
      q z * starRingEnd ℂ (dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ)) /
    ((a z * a' z : ℝ) : ℂ)

end Calc

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSourceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_character_positive_definite_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (mt S g)).det ^ x₃ τ) • f := by
  first | exact @GlobalTheory.VacuumCharacter.vacuum_character | exact GlobalTheory.VacuumCharacter.vacuum_character | (intros; apply GlobalTheory.VacuumCharacter.vacuum_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuePulledBackSectionEqImageFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_pulledBackSection_eq_image_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  first | exact @GlobalTheory.ValuePullback.valAt_abPull | exact GlobalTheory.ValuePullback.valAt_abPull | (intros; apply GlobalTheory.ValuePullback.valAt_abPull <;> assumption)
end


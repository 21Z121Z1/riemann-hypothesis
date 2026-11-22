import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR.FormExtJ

open GlobalTheory.CatCoh

section Inst

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (j : ℕ)

@[reducible] def opModJ : Module Bᵐᵒᵖ (Om R B j) :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModJ

theorem isCentralScalarJ : IsCentralScalar B (Om R B j) := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTowerJ : IsScalarTower R Bᵐᵒᵖ (Om R B j) := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

end Inst

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

def extMapJ {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (Om R (F.obj T) j) →ₐ[R] TrivSqZeroExt (F.obj T') (Om R (F.obj T') j) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (pOm F j φ c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [pOm_smul]
  commutes' r := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).fst = mp F φ c.fst := by
  simp [extMapJ]

theorem snd_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).snd = pOm F j φ c.snd := by
  simp [extMapJ]

def omjExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
  map φ := CommAlgCat.ofHom (extMapJ F j φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans (mp_id F T _)) ((snd_extMapJ F j _ c).trans (pOm_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).fst
      rw [fst_extMapJ, fst_extMapJ])))
    ((snd_extMapJ F j _ c).trans ((pOm_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).snd
      rw [snd_extMapJ, snd_extMapJ]))))

theorem mp_omjExt_inr {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by
  change extMapJ F j φ (TrivSqZeroExt.inr x) = _
  exact TrivSqZeroExt.ext ((fst_extMapJ F j φ _).trans (by simp)) ((snd_extMapJ F j φ _).trans (by simp))

theorem snd_mp_omjExt {T T' : C} (φ : T ⟶ T') (c : (omjExt F j).obj T) :
    (mp (omjExt F j) φ c).snd = pOm F j φ c.snd := snd_extMapJ F j φ c

theorem isUnit_mp_omjExt_iff {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMapJ F j u c)))

theorem span_inlJ_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omjExt F j).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (Om R (F.obj S) j))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.CechDR.FormExtJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic.PostVal

theorem ev_comp_ofHom {E : Spc} {I J : Cx ℤ} {n : ℤ} (α : Cochain ((chains ℤ).obj E) I n) (m : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem sglι_resAug (C : Shv ℤ) : sglι C ≫ (resAug C).f 0 = resι ℤ C := rfl

theorem resι_resMap {C G : Shv ℤ} (φ : C ⟶ G) : resι ℤ C ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  unfold resι resMap res
  rw [InjectiveResolution.ι'_f_zero, InjectiveResolution.ι'_f_zero,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
  simp [InjectiveResolution.cochainComplexXIso]

theorem post_eq_picClass (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1))
    (a : Cocycle ((chains ℤ).obj E) (sgl C) 1)
    (ha : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧
      ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) :
    HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  obtain ⟨γ, hγ, h0, h1⟩ := GlobalTheory.EtC.PicSpec.spec L
  rw [← hγ]
  change CohomologyClass.mk (zcomp (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))
    (Cocycle.ofHom (resMap ℤ qb)) (add_zero 1)) = _
  congr 1
  refine GlobalTheory.EtC.PicSpec.cocycle_ext _ _ (fun U x => ?_) (fun U x => ?_)
  · rw [h0]
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      0 1 _ U x = 0
    rw [ev_comp_ofHom, ev_comp_ofHom,
      GlobalTheory.EtC.PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)) (ev a.1 0 1 _ U x),
      GlobalTheory.EtC.PicSpec.sec_map_zero, GlobalTheory.EtC.PicSpec.sec_map_zero]
  · obtain ⟨c, hc, hv⟩ := ha U x
    rw [h1]
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      1 0 _ U x = _
    rw [ev_comp_ofHom, ev_comp_ofHom, hv, GlobalTheory.EtC.PicSpec.sec_map_comp, GlobalTheory.EtC.PicSpec.sec_map_comp, ← hc,
      GlobalTheory.EtC.PicSpec.sec_map_comp, ← Category.assoc, sglι_resAug, resι_resMap]

end GlobalTheory.EtC.KumPic.PostVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LevelCmp

variable {R : Type} [CommRing R]

theorem cpull_comp_fun {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (I : Cx R) (n : ℤ) :
    ⇑(cpull (a ≫ b) I n) = ⇑(cpull a I n) ∘ ⇑(cpull b I n) :=
  funext fun x => (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 a b I n x

theorem cpull_bij_of_heq {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  obtain ⟨hid, -, -, -, hhom⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have h1 := (hhom _ _ ⟨e.homotopyHomInvId⟩ I n).1
  have h2 := (hhom _ _ ⟨e.homotopyInvHomId⟩ I n).1
  have l1 : ∀ y, cpull e.hom I n (cpull e.inv I n y) = y := fun y => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.hom e.inv I n y, h1]; exact (hid _ _ _ _).1
  have l2 : ∀ x, cpull e.inv I n (cpull e.hom I n x) = x := fun x => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.inv e.hom I n x, h2]; exact (hid _ _ _ _).1
  exact ⟨Function.LeftInverse.injective l2, Function.RightInverse.surjective l1⟩

theorem cpull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull f I n) :=
  cpull_bij_of_heq (HomotopyEquiv.ofIso (asIso f)) I n

end GlobalTheory.EtC.LevelCmp

open GlobalTheory.EtC.LevelCmp in

theorem GlobalTheory.EtC.levelwise_eqv : GlobalTheory.EtC.A3 := by
  intro R _ E E' f F hlev
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI := hle E; haveI := hle E'; haveI := hge
  intro n
  refine GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective R (res R F) hinj ((chains R).map f) ?_ n
  intro p k
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨(-p).toNat, by omega⟩
    set φ := f.app (op (SimplexCategory.mk m))

    have hfree : Function.Bijective
        (cpull ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map φ)) (res R F) k) := by
      have hc := congrArg (fun g => ⇑(cpull g (res R F) k)) (he φ)
      simp only [cpull_comp_fun] at hc
      have hr : Function.Bijective (⇑(cpull (e _).hom (res R F) k) ∘
          ⇑(cpull ((chains R).map (disc.map φ)) (res R F) k)) :=
        (cpull_bij_of_heq (e _) _ k).comp (hlev (op (SimplexCategory.mk m)) k)
      rw [hc] at hr
      exact (Function.Bijective.of_comp_iff _ (cpull_bij_of_heq (e _) _ k)).1 hr
    have hg : ((chains R).map f).f (-(m : ℤ)) =
        (chainsXIso R E m).hom ≫ (free R).map φ ≫ (chainsXIso R E' m).inv := by
      rw [← Category.assoc, ← hnat f m]; simp
    rw [hg, Functor.map_comp, Functor.map_comp, cpull_comp_fun, cpull_comp_fun]
    exact (cpull_bij_of_iso _ _ k).comp (hfree.comp (cpull_bij_of_iso _ _ k))
  · have h1 : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    have h2 : IsZero (((chains R).obj E').X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    haveI : IsIso (((chains R).map f).f p) := ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
    exact cpull_bij_of_iso _ _ k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupportStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by
  first | exact @GlobalTheory.lift_of_reduced_of_support | exact GlobalTheory.lift_of_reduced_of_support | (intros; apply GlobalTheory.lift_of_reduced_of_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyEqualOrUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_equal_or_unit : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  first | (exact @GlobalTheory.EtC.PairDich.pair_dich) | (exact GlobalTheory.EtC.PairDich.pair_dich) | (intros; apply GlobalTheory.EtC.PairDich.pair_dich  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRingsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  first | (exact @GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (exact GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (intros; apply GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBoundsStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_count_all_bounds : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality := by
  first | exact @GlobalTheory.LowCount.lowC_all | exact GlobalTheory.LowCount.lowC_all | (intros; apply GlobalTheory.LowCount.lowC_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

noncomputable def twoSidedEquiv (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    show ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) * ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    show (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]

theorem map_twoSided_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ _ _ μ _ u a
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  have := hfd
  have := (hmat α ν).1
  let T := twoSidedEquiv F E u a

  have hdet : LinearEquiv.det T =
      (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u) ^ Fintype.card ν *
        (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a) ^
          Fintype.card α := by
    ext
    rw [LinearEquiv.coe_det, GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul F E α ν (u : Matrix α α E) (a : Matrix ν ν E)
      (T : Matrix α ν E →ₗ[F] Matrix α ν E) (fun x ↦ rfl)]
    simp
  have hT : (fun x ↦ (u : Matrix α α E) * x * (a : Matrix ν ν E)) = ⇑T := rfl
  rw [hT, GlobalTheory.T.map_linearEquiv_addHaar_localField F (Matrix α ν E) μ T, hdet, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyIStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R, ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  first | (exact @GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (exact GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (intros; apply GlobalTheory.EtC.cone_kinj_and_bijective_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeClass

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem mk_injective_sgl (X : Shv R) (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (CohomologyClass.mk : Cocycle (sgl X) I 0 → CohomologyClass (sgl X) I 0) := by
  intro a b h
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff (m := -1) (hm := by norm_num)] at h
  obtain ⟨β, hβ⟩ := h
  have hβ0 : β = 0 := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    by_cases hp : p = 0
    · subst hp
      exact (CochainComplex.isZero_of_isStrictlyGE I 0 q (by omega)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  rw [hβ0, δ_zero] at hβ
  exact sub_eq_zero.1 (Cocycle.ext hβ.symm)

theorem cpull_single_injective {X Y : Shv R} (g : X ⟶ Y) [Epi g] (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map g) I 0) := by
  intro x y h
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  have h' := mk_injective_sgl X I h
  have hg : Epi (((CochainComplex.singleFunctor (Shv R) 0).map g).f 0) := by
    change Epi (((HomologicalComplex.single _ _ 0).map g).f 0)
    rw [HomologicalComplex.single_map_f_self]
    infer_instance
  congr 1
  refine Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    have e := congrArg (fun z : Cocycle (sgl X) I 0 => z.1.v 0 0 (add_zero 0)) h'
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.ofHom_v] at e
    exact (cancel_epi _).1 e
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

theorem mk_ofHom_eq_of_homotopy {K L : Cx R} (f g : K ⟶ L) (h : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  have e := congrArg (fun φ => φ (CohomologyClass.mk (Cocycle.ofHom (𝟙 L)))) ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.2.2.2 f g ⟨h⟩ L 0).1
  simpa only [← mk_ofHom_comp, Category.comp_id] using e

end GlobalTheory.EtC.ConeClass

namespace GlobalTheory.EtC.ConeClass

theorem cone_class_eq : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∀ (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) →
    CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)) ≫ resAug S.X₃)) =
      CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
  intro R _ S hS hc e hh
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI : QuasiIso (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) :=
    mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₃).IsKInjective := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsKInjective)
  haveI : (res R S.X₃).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsStrictlyGE 0)
  haveI : Epi S.g := hS.epi_g
  have hbij := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0
  obtain ⟨c, hc'⟩ := hbij.2 (CohomologyClass.mk (Cocycle.ofHom
    (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)))
  refine (mk_ofHom_comp _ _).trans (Eq.trans ?_ hc')
  refine congrArg _ ?_
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
      mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc = resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) := by
    simp [mappingCone.map]
    rfl
  have hres : resAug S.X₂ ≫ resMap R S.g = (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    InjectiveResolution.Hom.ι'_comp_hom'
      ⟨InjectiveResolution.desc S.g (injectiveResolution _) (injectiveResolution _),
        InjectiveResolution.desc_commutes_zero _ _ _⟩
  apply cpull_single_injective S.g (res R S.X₃)
  have hA : cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
      (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃))) =
      CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) := by
    calc cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
            (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃)))
        = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃)) :=
          (mk_ofHom_comp _ _).symm
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ resMap R S.g)) := by rw [hres]
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :=
          (mk_ofHom_eq_of_homotopy _ _ (hh.compLeft (resAug S.X₂))).symm
  have hB1 : CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) =
      cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) := by
    rw [hc', mk_ofHom_comp]
  have hB2 : cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) =
      cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0 c := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1, mappingCone.inr_descShortComplex]
    rfl
  have hC : (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :
        CohomologyClass (sgl S.X₂) (res R S.X₃) 0) =
      CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
    rw [reassoc_of% hinr]
    rfl
  exact hA.trans (hC.trans (hB1.trans hB2))

end GlobalTheory.EtC.ConeClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
section
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

open NumberField

section Mod

variable {O T V : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V]

def eigSub (μ : O →+* Module.End T V) (τ : O →+* T) : Submodule T V where
  carrier := {v | ∀ c, μ c v = τ c • v}
  add_mem' {u v} hu hv c := by simp only [Set.mem_setOf_eq, map_add, hu c, hv c, smul_add]
  zero_mem' c := by simp
  smul_mem' r v hv c := by simp only [Set.mem_setOf_eq, map_smul, hv c, smul_comm r]

theorem mem_eigSub {μ : O →+* Module.End T V} {τ : O →+* T} {v : V} :
    v ∈ eigSub μ τ ↔ ∀ c, μ c v = τ c • v := Iff.rfl

def LieMod (μ : O →+* Module.End T V) (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) : Prop :=
  ∀ v, μ ω v = ρ • v → ∃ w : Fin a → V, (∀ i, w i ∈ eigSub μ (τ i)) ∧ v = ∑ i, w i

end Mod

def matAct {O B T : Type} [CommRing O] [CommRing B] [CommRing T] {n : ℕ} (M : O →+* Matrix (Fin n) (Fin n) B)
    (f : B →+* T) : O →+* Module.End T (Fin n → T) :=
  (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)).toRingEquiv.toRingHom.comp (f.mapMatrix.comp M)

theorem matAct_apply {O B T : Type} [CommRing O] [CommRing B] [CommRing T] {n : ℕ}
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) (c : O) (v : Fin n → T) :
    matAct M f c v = ((M c).map f).mulVec v := rfl

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def lieMat (b : Base D R) {B : Type} [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B)
    (c : Fin D.a → 𝓞 D.F) : Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun i => M (c i) - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t i (c i)))).prod *
    (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ)))

def lieIdeal (b : Base D R) {B : Type} [CommRing B] (βB : R →+* B) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) : Ideal B :=
  Ideal.span {x | ∃ (c : Fin D.a → 𝓞 D.F) (i j : Fin n), lieMat b βB M c i j = x}

def LieHerMat (b : Base D R) {B : Type} [CommRing B] {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B)
    {T : Type} [CommRing T] (f : B →+* T) (β : R →+* T) : Prop :=
  ∀ (T' : Type) [CommRing T'] (g : T →+* T'),
    LieMod (matAct M (g.comp f)) D.ω (g (β b.ρ)) (fun i => (g.comp β).comp (b.t i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (h : T' →+* k) (i : Fin D.a),
      Module.finrank k (eigSub (matAct M (h.comp (g.comp f))) ((h.comp (g.comp β)).comp (b.t i))) = D.m

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ), (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧ (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧ ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧ (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  first | exact @GlobalTheory.DetPowShape.detPow_shape | exact GlobalTheory.DetPowShape.detPow_shape | (intros; apply GlobalTheory.DetPowShape.detPow_shape <;> assumption)
end


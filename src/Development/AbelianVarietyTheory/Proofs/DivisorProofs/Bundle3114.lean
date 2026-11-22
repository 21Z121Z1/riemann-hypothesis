import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslate
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.IsoLin

variable {S : Scheme.{0}}

theorem transl_mul' {G : Over S} [GrpObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl (x * y) = Hecke.transl x ≫ Hecke.transl y := by
  simp only [Hecke.transl, comp_mul, Category.comp_id, Category.id_comp]
  rw [← Category.assoc _ (toUnit G) y, toUnit_unique (_ ≫ toUnit G) (toUnit G), _root_.mul_assoc]

theorem transl_comm {G : Over S} [GrpObj G] [IsCommMonObj G] (x y : 𝟙_ (Over S) ⟶ G) :
    Hecke.transl x ≫ Hecke.transl y = Hecke.transl y ≫ Hecke.transl x := by
  rw [← transl_mul', ← transl_mul', _root_.mul_comm]

theorem lift_mul_lift' {A : Over S} [GrpObj A] (a b c d : 𝟙_ (Over S) ⟶ A) :
    (lift (a * c) (b * d) : 𝟙_ (Over S) ⟶ G2 A) = lift a b * lift c d := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem surj_appTop {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (fst A A).left.appTop.hom ∧ Function.Surjective (snd A A).left.appTop.hom := by
  have h2 := (GlobalTheory.globalFns_holds S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2
  have w1 : (G2 A).hom = (fst A A).left ≫ A.hom := (Over.w (fst A A)).symm
  have w2 : (G2 A).hom = (snd A A).left ≫ A.hom := (Over.w (snd A A)).symm
  refine ⟨?_, ?_⟩
  · rw [w1, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2
  · rw [w2, Scheme.Hom.comp_appTop] at h2
    exact Function.Surjective.of_comp h2

theorem rig_lbPow {X Y : Scheme.{0}} (P : LB X) (hP : P.IsLB) (m : ℕ) (f : Y ⟶ X)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : ((Hecke.lbPow P m).pull f).Gen, t.IsGen := by
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1))).2 h
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (DVR.linComb_isLB _ hQ (fun _ : PUnit => f) (fun _ => 1))).1 ?_
  have e : GlobalTheory.CechPic.cls _ hQ = (m : ℤ) • GlobalTheory.CechPic.cls P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (fun _ : Fin m => 𝟙 X) (fun _ => 1) hQ).trans ?_
    simp [GlobalTheory.CechPic.pull_id]
  rw [GlobalTheory.CechPic.cls_pull hQ f, e, map_zsmul,
    ← GlobalTheory.CechPic.cls_pull hP f (DVR.linComb_isLB P hP (fun _ : PUnit => f) (fun _ => 1)), h0, smul_zero]

end GlobalTheory.IsoLin

namespace GlobalTheory.IsoLin

theorem exists_linearisation_isotropic : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m : ℕ) (H : Subgroup (𝟙_ (Over S) ⟶ A)), (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) → (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 A) (lift 1 h₂) 1) → ∃ u : ∀ a : H × H, LB.Gen (LB.LinComb (GlobalTheory.UPel.HT.Hecke.lbPow P m) (K := Fin 2) ![𝟙 (G2 A).left, (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u (a * c)) (LB.mulGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u a) (LB.pullGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ (u c) (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left)) := by
  intro S A _ _ hA P hP hr1 hr2 m H hH1 hH2 hW
  have hQ : (Hecke.lbPow P m).IsLB := DVR.linComb_isLB P hP _ _
  have q1 := rig_lbPow P hP m _ hr1
  have q2 := rig_lbPow P hP m _ hr2
  obtain ⟨sf, ss⟩ := surj_appTop hA
  have hm1 : ∀ a c : H, (lift ((a * c : H) : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A) = lift (a : 𝟙_ (Over S) ⟶ A) 1 * lift (c : 𝟙_ (Over S) ⟶ A) 1 := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  have hm2 : ∀ a c : H, (lift 1 ((a * c : H) : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) = lift 1 (a : 𝟙_ (Over S) ⟶ A) * lift 1 (c : 𝟙_ (Over S) ⟶ A) := by
    intro a c
    rw [← lift_mul_lift', _root_.mul_one, Subgroup.coe_mul]
  obtain ⟨v₁, hv₁, cv₁⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (fst A A).left
    (lift (𝟙 A) (1 : A ⟶ A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left]) sf
    (Hecke.lbPow P m) hQ q2 H (fun a => (Hecke.transl (lift (a : 𝟙_ (Over S) ⟶ A) 1 : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => GlobalTheory.T.birigidified_bundle_translation_invariant_first_factor S A hA _ hQ q1 q2 a (hH1 a a.2))
  obtain ⟨v₂, hv₂, cv₂⟩ := GlobalTheory.MumLin.exists_linearisation A.left (G2 A).left (snd A A).left
    (lift (1 : A ⟶ A) (𝟙 A)).left (by rw [← Over.comp_left, lift_snd, Over.id_left]) ss
    (Hecke.lbPow P m) hQ q1 H (fun a => (Hecke.transl (lift 1 (a : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun a => (Hecke.transl (a : 𝟙_ (Over S) ⟶ A)).left)
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    (fun a c => by simp only [Subgroup.coe_mul, transl_mul', Over.comp_left])
    (fun a => by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [Hecke.transl, MonObj.mul_comp, MonObj.comp_mul])
    (fun a => GlobalTheory.T.birigidified_bundle_translation_invariant_second_factor S A hA _ hQ q1 q2 a (hH2 a a.2))
  exact GlobalTheory.T.exists_linearization_prod (G2 A).left (Hecke.lbPow P m) hQ H H _ _
    (fun p => (Hecke.transl (lift (p.1 : 𝟙_ (Over S) ⟶ A) (p.2 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A)).left)
    (fun p => by
      show _ = (Hecke.transl _ ≫ Hecke.transl _).left
      rw [← transl_mul', ← lift_mul_lift', _root_.mul_one, _root_.one_mul])
    (fun a b => by rw [← Over.comp_left, ← Over.comp_left, transl_comm])
    (fun a c => by simp only [hm1, transl_mul', Over.comp_left])
    (fun a c => by simp only [hm2, transl_mul', Over.comp_left])
    v₁ v₂ hv₁ hv₂ cv₁ cv₂
    (fun a b => GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one S (G2 A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ hQ _ _ (v₁ a) (v₂ b) (hv₁ a) (hv₂ b) (hW a a.2 b b.2))

end GlobalTheory.IsoLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquivPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabMove

theorem exists_mulEquiv_points {S K K' X : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over K} [GrpObj A] {A' : Over K'}
    [GrpObj A'] {g : K ⟶ S} {g' : K' ⟶ S} {α : A.left ⟶ G.left} {α' : A'.left ⟶ G.left}
    (h : IsGrpPullback A G g α) (h' : IsGrpPullback A' G g' α') (t : X ⟶ K) (t' : X ⟶ K')
    (f : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left)
    (hf₁ : f ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (hf₂ : f ≫ (snd (Over.mk t) A).left ≫ α = (snd (Over.mk t') A').left ≫ α') :
    ∃ e : (Over.mk t' ⟶ A') ≃* (Over.mk t ⟶ A), ∀ x', (e x').left ≫ α = x'.left ≫ α' ∧
      (ptSecT A' x').left ≫ f = (ptSecT A (e x')).left := by
  have s₁ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (fst T Y).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have s₂ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (snd T Y).left = x.left := fun x => by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have w : (snd (Over.mk t) A).left ≫ A.hom = (fst (Over.mk t) A).left ≫ t :=
    (Over.w (snd (Over.mk t) A)).trans (Over.w (fst (Over.mk t) A)).symm
  have w' : (snd (Over.mk t') A').left ≫ A'.hom = (fst (Over.mk t') A').left ≫ t' :=
    (Over.w (snd (Over.mk t') A')).trans (Over.w (fst (Over.mk t') A')).symm
  have hu : t' ≫ g' = t ≫ g := by
    have e := congrArg (fun q => (ptSecT A' (1 : Over.mk t' ⟶ A')).left ≫ q ≫ G.hom) hf₂
    simp only [Category.assoc] at e
    rw [h.1.w, h'.1.w, reassoc_of% w, reassoc_of% w', reassoc_of% hf₁, reassoc_of% (s₁ (1 : Over.mk t' ⟶ A')),
      reassoc_of% (s₁ (1 : Over.mk t' ⟶ A'))] at e
    exact e.symm
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h t (t ≫ g) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h' t' (t ≫ g) hu
  have key : ∀ x', ((e'.trans e.symm) x').left ≫ α = x'.left ≫ α' := fun x' => by
    rw [← he, ← he', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e'.trans e.symm, fun x' => ⟨key x', ?_⟩⟩
  have a₁ : ((ptSecT A' x').left ≫ f) ≫ (fst (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (fst (Over.mk t) A).left := by
    rw [Category.assoc, hf₁, s₁, s₁]; rfl
  have a₂ : ((ptSecT A' x').left ≫ f) ≫ (snd (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (snd (Over.mk t) A).left := by
    refine h.1.hom_ext ?_ ?_
    · rw [s₂, key, Category.assoc, Category.assoc, hf₂, reassoc_of% (s₂ x')]
    · rw [Category.assoc, w, Category.assoc _ _ A.hom, w, ← Category.assoc, a₁, Category.assoc]
  exact pullback.hom_ext a₁ a₂

end GlobalTheory.Mum.LabMove

namespace GlobalTheory.Mum

theorem Trait.exists_lab_push : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → (∀ x : TFK (R := W) F ⟶ T.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p', lab' p' = x) → ∃ lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A), LabExt em (C.lab j) lab ∧ (∀ x : TFK (R := R) F ⟶ C.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p, lab p = x) ∧ ∀ (p : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), p'.y = T.hD.xe.symm p.y → IsPullGtF T.φ T.hD F p.g p'.g → (ptSecT T.A.A (lab' p')).left ≫ f = (ptSecT C.A.A (lab p)).left := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ _ em hF f _ hf₁ hf₂ lab' hext honto
  have := T.U.gen_hom
  have : IsMonHom T.U.gen.symm.hom := by show IsMonHom T.U.gen.inv; infer_instance
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ) (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((isGrpPullback_of_iso T.U.gen.symm).comp ((isGrpPullback_pullback T.G (jK W)).comp T.cart)).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := LabMove.exists_mulEquiv_points C.α_cart gT (jFK (R := R) F) (jFK (R := W) F) f hf₁ hf₂
  let P : QkPt D.toPre F (C.n ^ j) → QkPt T.D'.toPre F (C.n ^ j) :=
    GlobalTheory.ArcPull.pullQk T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hP : ∀ p p', p' = P p ↔ p'.y = T.hD.xe.symm p.y ∧ IsPullGtF T.φ T.hD F p.g p'.g :=
    GlobalTheory.ArcPull.eq_pullQk_iff T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hs : Function.Surjective P :=
    GlobalTheory.ArcPull.pullQk_surjective T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  refine ⟨fun p => e (lab' (P p)), fun p p₁ hp => ?_, fun x => ?_, fun p p' hy hg => ?_⟩
  · refine C.α_cart.1.hom_ext ?_ ?_
    · rw [Category.assoc]
      exact (he _).1.trans (hext p p₁ (P p₁) hp ((hP _ _).1 rfl).1 ((hP _ _).1 rfl).2)
    · rw [Category.assoc, Over.w, Over.w]
      simp only [TFK, Over.mk_hom, jFK]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
  · obtain ⟨x', rfl⟩ := e.surjective x
    rw [← map_pow, MulEquiv.map_eq_one_iff, honto, hs.exists]
    exact exists_congr fun p => e.injective.eq_iff.symm
  · obtain rfl := (hP p p').2 ⟨hy, hg⟩
    exact (he _).2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

theorem GlobalTheory.HomMum.exists_gen_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), IsNrm u → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ u hu hadd
  obtain ⟨W, hW, h₁, h₂⟩ := GlobalTheory.T.exists_glued_uniformisation_iso_one_level U₁ U₂ e
  obtain ⟨v, hv, hm⟩ := GlobalTheory.T.exists_generator_multiplicative_on_quotient_kernel U₁ U₂ e hf hg W hW h₁ h₂ u hu.1 hadd
  exact GlobalTheory.T.exists_descended_generator_thickened_abelian_part U₁ U₂ e hf hg v hv (GlobalTheory.T.generator_torus_invariant_of_multiplicative U₁ U₂ e hf hg v hv hm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedGeneratorOfFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwNorm

open GlobalTheory.TwFac

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_normalised (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a]
    (hh : ∀ y, D.c (h y) = D.c y ≫ a) (n j : ℤ) (mu β' : D.X)
    (g : ∀ y : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c y).left) (fun _ => -1)))
    (hg : ∀ y, (g y).IsGen)
    (w : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j))) (hw : w.IsGen) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) J, Good D.P.L z J →
        val u (r ≫ eSec D.P.A) z J = val (g mu) r z J ^ n * val (g (h mu)) r z J ^ j * val D.rig r z J ^ (n + j) := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (g mu) (hg mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (g (h mu)) (hg _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rig D.rig_gen (n + j)
  have i₀ : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _
  have a₁ : ∀ χ, DVR.cP D (𝟙_ _) χ = D.c χ := fun χ => by rw [DVR.cP, i₀, Category.id_comp]
  have a₂ : η[D.P.A] = 1 := by rw [Hom.one_def, i₀, Category.id_comp]
  have z₃ : η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu) = D.c mu := by
    refine (MonObj.comp_mul _ (𝟙 _) (DVR.cP D _ mu)).trans ?_
    rw [DVR.comp_cP, Category.comp_id, a₂, _root_.one_mul, a₁]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (toUnit D.P.A).left (eSec D.P.A)
    (congrArg (fun q => q.left) (toUnit_unique (η[D.P.A] ≫ toUnit _) (𝟙 _))) (fun U _ f => by
      have q₁ := prod_t D a β' n j η[D.P.A] f
      have q₂ := prod_t D a 0 n j (η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)) f
      have b₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      conv_rhs at q₁ => rw [a₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, ← hh, cPoint_zero, _root_.mul_one]
      simp only [Over.comp_left, Category.assoc] at q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      have a₃ : eSec D.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left := congrArg (fun q => q.left) a₂
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) h₃)
  have hc := corr_of_val D.P.isLB (t := LB.pullGen D.P.L _ _ u (eSec D.P.A))
    (t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃) fun y J hJ => by
      rw [val_pull hJ, Category.id_comp]; exact vu y J hJ
  refine ⟨u, hu, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc r).trans ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) (v₃ _ _ _ _))

theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (x : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau x 0) (𝟙 _) z J = 1 := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero x), mul_inv_cancel, _root_.one_mul,
    GlobalTheory.PsiInPow.val_psi_zero D hB hJ, inv_inv, mul_inv_cancel]

def germK (K : Type) [Field K] (z : Sp K) : K →+* (Sp K).presheaf.stalk z :=
  ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem gs_sec {K : Type} [Field K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) (z : Sp K) (c : K) :
    gs e z ⊤ (scal p c) = germK K z c := by
  refine (gs_pull e p z ⊤ trivial _).trans ?_
  rw [he, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_generic (z : Sp (FractionRing R)) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = germK (FractionRing R) z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Sp (FractionRing R)).presheaf.germ ⊤ z trivial).hom nat.symm

theorem const_eq {S : Type} [CommRing S] {u u₀ p t k k' G : Sˣ} {c r : S} {m : ℤ} (e₁ : u.val = c * u₀.val)
    (e₂ : u = p * t * k ^ m) (ht : t = 1) (hk : k = k') (e₃ : p.val = r * G.val) (e₄ : u₀ = G * k' ^ m) : c = r := by
  subst ht hk e₂
  refine (Units.mul_left_inj u₀).1 ?_
  rw [← e₁, e₄, _root_.mul_one, Units.val_mul, Units.val_mul, e₃, _root_.mul_assoc]

theorem exists_gen_fac : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) → (∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val) → ∀ ν : D.toPre.X, ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1))), u₀.IsGen ∧ ∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) (r ν))) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ hR D a a' h h' hE N _ r g hg hr ν
  have ha : IsMonHom a := hE.1
  have hh : ∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a := hE.2.2.2.1
  obtain ⟨w, hw⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hR D a a' h h' hE N (-1) ν 0 (shift h h' N (-1) ν) (zero_add _).symm
  obtain ⟨u₀, hu₀, v₀⟩ := exists_normalised D.toPre a h hh N (-1) ν _ g hg w hw
  refine ⟨u₀, hu₀, fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := (fac_exists_unique_const R hR D a h ha hh N (-1) ν 0 _ u₀ hu₀).2.2 u hu.1
  suffices e : c = algebraMap R (FractionRing R) (r ν) by subst e; exact hc
  obtain ⟨z⟩ : Nonempty (Sp (FractionRing R)) := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose J hJ using fun ψ : Sp (FractionRing R) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  have j₁ : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : (DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (toUnit (TK R)).left ≫ eSec D.toPre.P.A := by
    refine (congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) (FractionRing R))) (toUnit _ ≫ η[D.toPre.P.A]))).trans ?_
    show (jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left) ≫ eSec D.toPre.P.A = _
    rw [j₁, Category.id_comp]
  have e₁ := hc _ (DegPre.zF D.toPre (FractionRing R)).left z J hJ
  have e₂ := hu.2 z J hJ
  have e₃ := hr ν z J hJ
  have e₄ := v₀ _ (toUnit (TK R)).left z J hJ
  have e₅ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (toUnit (TK R)).left z J :=
    (val_pull hJ _ _ _).trans (congrArg (fun q => val D.toPre.rig q z J) (Category.id_comp _))
  rw [j₁, zpow_natCast, zpow_neg_one] at e₂
  rw [zpow_natCast, zpow_neg_one] at e₄
  have e₆ := gs_sec _ _ (congrArg (fun q => q.left) z₁) z c
  have e₇ := gs_generic z (r ν)
  exact (germK (FractionRing R) z).injective (e₆.symm.trans ((const_eq e₁ e₂ (val_tau_zero D.toPre D.tau_bimult ν hJ) e₅ e₃
    ((congrArg (fun q => val u₀ q z J) z₂).trans e₄)).trans e₇))

end GlobalTheory.TwNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOActNDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddMultiplicationPullbackThetaFamilyDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), ∃ (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (S : SecK C.P.L.L C.α (m ^ 2)), ((∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ θ₀
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd R hR D m hm F₁
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_multiplicationPullback_genericSection_cover R hR D C m hm θ₀
  exact ⟨G, S, GlobalTheory.T.multiplicationPullback_family_ne_zero_odd R hR D m hm F₁ G hG,
    fun W _ _ _ T a b ha h => GlobalTheory.T.expansion_oddMultiplicationPullback_at_trait R hR D C m hm F₁ G θ₀ S hG hS W T a b ha h⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionBigCellBaseAffineCoordsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_immersion_big_cell_base_affine_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ V : (Spec (CommRingCat.of Γ(Y₀ TF.X Z, W))).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  first | exact @GlobalTheory.LogPole.CellBir.exists_isOpenImmersion | exact GlobalTheory.LogPole.CellBir.exists_isOpenImmersion | (intros; apply GlobalTheory.LogPole.CellBir.exists_isOpenImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_order_two_point_torus_extension_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R))
  (β : D₀.toPre.P.A ≅ D.toPre.P.A) (xe : D₀.toPre.X ≃+ D.toPre.X), IsMonHom β.hom →
  (∀ χ, D₀.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) →
  ∀ wΛ : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L)
      ((abelian₂ D.toPre.P.A D.toPre.P.L).pull
        (lift (fst D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) (snd D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) :
          G2 D₀.toPre.P.A ⟶ G2 D.toPre.P.A).left),
    wΛ.IsGen →
    (∀ (a a' : D₀.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.toPre.P.A.left) → D₀.toPre.P.L.ι), Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val (D₀.toPre.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.toPre.c a) (toUnit (TK R) ≫ D₀.toPre.c a')).left z J J' *
            val (D.toPre.tau (xe a) (xe a')) (𝟙 _) z J) →
  ∀ b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A, padd D.toPre.P.A b b = η[D.toPre.P.A] →
  ∀ w : LB.Iso D₀.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₀.toPre D.toPre β.hom b) GlobalTheory.MumCmp.twε), w.IsGen →
  ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), g.b = b ∧ (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧
    GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.Point.exists_point | exact GlobalTheory.MumCmp.Point.exists_point | (intros; apply GlobalTheory.MumCmp.Point.exists_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicitiesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  first | exact @GlobalTheory.Mix.exists_secPull_props | exact GlobalTheory.Mix.exists_secPull_props | (intros; apply GlobalTheory.Mix.exists_secPull_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquareStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_closure_point_fibreSquare : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  first | exact @GlobalTheory.FlagPush.exists_closure_pair | exact GlobalTheory.FlagPush.exists_closure_pair | (intros; apply GlobalTheory.FlagPush.exists_closure_pair <;> assumption)
end


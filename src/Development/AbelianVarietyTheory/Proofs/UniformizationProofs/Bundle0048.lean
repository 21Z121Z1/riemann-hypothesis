import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TensorContentEqPolyContentScalarCoeffs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivTransport
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiTransport

variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}

theorem lift_lam {G H T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G) (t : T ⟶ H) (x : T ⟶ G)
    (k : Fin 4) : (lift t x).left ≫ lamφ i k = (![(t ≫ i) * x, t ≫ i, x, 1] k : T ⟶ G).left := by
  fin_cases k
  · exact congrArg (fun q => q.left) (show lift t x ≫ ((fst H G ≫ i) * snd H G) = (t ≫ i) * x by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd])
  · exact congrArg (fun q => q.left) (lift_fst_assoc t x i)
  · exact congrArg (fun q => q.left) (lift_snd t x)
  · exact congrArg (fun q => q.left) (show lift t x ≫ (1 : H ⊗ G ⟶ G) = 1 from MonObj.comp_one _)

theorem prod_lam {G H T : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (i : H ⟶ G) (t : T ⟶ H) (x : T ⟶ G)
    {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  simp only [lift_lam, Fin.prod_univ_four]
  show h ((t ≫ i) * x).left ^ (1 : ℤ) * h (t ≫ i).left ^ (-1 : ℤ) * h x.left ^ (-1 : ℤ) *
    h (1 : T ⟶ G).left ^ (1 : ℤ) = _
  simp only [zpow_one, zpow_neg]

theorem toBase_surj {A : Over S} {A₀ : Over S₀} {E : A₀.left ⟶ A.left} (hE : IsPullback E A₀.hom A.hom ρ)
    (hw : E ≫ A.hom = A₀.hom ≫ ρ) {T : Over S₀} (x : Over.mk (T.hom ≫ ρ) ⟶ A) : ∃ x₀ : T ⟶ A₀, toBase hw x₀ = x :=
  ⟨Over.homMk (hE.lift x.left T.hom (Over.w x)) (hE.lift_snd _ _ _), Over.OverMorphism.ext (hE.lift_fst _ _ _)⟩

theorem exists_over {Z : Over S} (r : Z.left ⟶ S₀) (h : r ≫ ρ = Z.hom) : ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := by
  obtain ⟨Z, ⟨⟨⟩⟩, f⟩ := Z
  change Z ⟶ S₀ at r
  change Z ⟶ S at f
  obtain rfl : r ≫ ρ = f := h
  exact ⟨Over.mk r, rfl⟩

section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G₀ H₀ : Over S₀} [GrpObj G₀] [IsCommMonObj G₀]
  [GrpObj H₀] {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ ρ} {E : H₀.left ⟶ H.left}
  {P : CP G} {P₀ : CP G₀} {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : H ⟶ G} {i₀ : H₀ ⟶ G₀}

omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj G₀] [IsCommMonObj G₀] [GrpObj H₀] in

theorem toBase_comp (hE : E ≫ H.hom = H₀.hom ≫ ρ) (hi : E ≫ i.left = i₀.left ≫ F) {T : Over S₀} (t : T ⟶ H₀) :
    toBase hE t ≫ i = toBase hw (t ≫ i₀) := Over.OverMorphism.ext (by
  show (t.left ≫ E) ≫ i.left = (t.left ≫ i₀.left) ≫ F
  rw [Category.assoc, hi, Category.assoc])

theorem exists_gen_val [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsPullback E H₀.hom H.hom ρ)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F)
    (σ : LB.Gen (LB.LinComb P₀.L.L (lamφ i₀) Oε)) (hσ : σ.IsGen) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      ∀ (T : Over S₀) (t : T ⟶ H₀) (x : T ⟶ G₀) (a : T.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (toBase hE.w t) (toBase hw x)).left →
        ∀ (z : T.left) (J' J), Good P₀.L.L z J' → Good P.L.L z J →
        ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ y, W y = gw w y.left z (J (y.left ≫ F)) (J' y.left)) →
          val s a z J = W ((t ≫ i₀) * x) * (W (t ≫ i₀))⁻¹ * (W x)⁻¹ * W 1 * val σ (lift t x).left z J' := by
  let Y : Over S₀ := Over.mk (pullback.snd (H ⊗ G).hom ρ)
  let j : Over.mk (Y.hom ≫ ρ) ⟶ H ⊗ G := Over.homMk (pullback.fst (H ⊗ G).hom ρ) pullback.condition
  obtain ⟨t₀, ht₀⟩ := toBase_surj hE hE.w (j ≫ fst H G)
  obtain ⟨x₀, hx₀⟩ := toBase_surj hF hw (j ≫ snd H G)
  have hj : pullback.fst (H ⊗ G).hom ρ = (lift (toBase hE.w t₀) (toBase hw x₀)).left := by
    rw [ht₀, hx₀, ← comp_lift, lift_fst_snd, Category.comp_id]; rfl
  have hφ : (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) = fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F := by
    funext k
    refine ((congrArg (· ≫ lamφ i k) hj).trans (lift_lam i _ _ k)).trans
      (Eq.trans ?_ (congrArg (· ≫ F) (lift_lam i₀ t₀ x₀ k)).symm)
    rw [toBase_comp (hw := hw) hE.w hi]
    fin_cases k
    · exact (congrArg (fun q => q.left) (hP.mul Y (t₀ ≫ i₀) x₀)).symm
    · rfl
    · rfl
    · exact (congrArg (fun q => q.left) (map_one (toBaseHom hP.mul Y))).symm
  obtain ⟨s, hs, hv⟩ := exists_up ((isGen_iff w).1 hP.gen) P.L.isLB P₀.L.isLB
    (LB.pullGen P₀.L.L (lamφ i₀) Oε σ (lift t₀ x₀).left) (DVR.pullGen_isGen _ _ _ _ hσ _)
  rw [hφ]
  refine ⟨s, hs, fun T t x a ha z J' J hJ' hJ W hW => ?_⟩
  have e₀ : a ≫ pullback.snd (H ⊗ G).hom ρ = T.hom := by
    rw [← cancel_mono ρ, Category.assoc, ← pullback.condition, ← Category.assoc, ha]
    exact Over.w _
  let a' : T ⟶ Y := Over.homMk a e₀
  have e₁ : a' ≫ t₀ = t := Over.OverMorphism.ext (hE.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) ht₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fst H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_fst (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₂ : a' ≫ x₀ = x := Over.OverMorphism.ext (hF.hom_ext (by
    have := congrArg (fun q => a ≫ q.left) hx₀
    refine ((Category.assoc _ _ _).trans this).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (snd H G).left) ha)).trans ?_
    exact congrArg (fun q => q.left) (lift_snd (toBase hE.w t) (toBase hw x))) ((Over.w _).trans (Over.w _).symm))
  have e₃ : a ≫ (lift t₀ x₀).left = (lift t x).left :=
    congrArg (fun q => q.left) (show a' ≫ lift t₀ x₀ = lift t x by rw [comp_lift, e₁, e₂])
  have v := hv _ a z _ _ (hJ.mem (fun k => ((lift t₀ x₀).left ≫ lamφ i₀ k) ≫ F) a)
    (hJ'.mem (fun k => (lift t₀ x₀).left ≫ lamφ i₀ k) a)
  refine v.trans (congrArg₂ (· * ·) ?_ ((val_pull hJ' σ _ a).trans (congrArg (fun q => val σ q z J') e₃)))
  simp only [hW]
  refine Eq.trans ?_ (prod_lam i₀ t x (fun q => gw w q z (J (q ≫ F)) (J' q)))
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← e₃]
  simp only [Category.assoc]

theorem exists_transport [Mono ρ] (hF : IsPullback F G₀.hom G.hom ρ) (hE : IsGrpPullback H₀ H ρ E)
    (hP : IsCPMap P₀ P ρ F hw w) (hi : E ≫ i.left = i₀.left ≫ F) [IsMonHom i₀] (σ : BiTriv P₀.c i₀) :
    ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (H ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧
      (∀ (Z : Over S) (t t' : Z ⟶ H) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧
      (∀ (Z : Over S) (t : Z ⟶ H) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (H ⊗ G).hom ρ),
        a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left →
        d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I →
        val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  obtain ⟨s, hs, hv⟩ := exists_gen_val hF hE.1 hP hi σ.s σ.gen
  have ov : ∀ (Z : Over S) (a : Z.left ⟶ pullback (H ⊗ G).hom ρ) (p : Z ⟶ H ⊗ G), a ≫ pullback.fst _ _ = p.left →
      ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := fun Z a p ha => exists_over (a ≫ pullback.snd _ _) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha]; exact Over.w p)
  refine ⟨s, hs, fun Z t t' x a b d ha hb hd z I hI => ?_, fun Z t x x' a b d ha hb hd z I hI => ?_⟩
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨t', rfl⟩ := toBase_surj hE.1 hE.1.w t'
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    have m : toBase hE.1.w t * toBase hE.1.w t' = toBase hE.1.w (t * t') :=
      Over.OverMorphism.ext (hE.2 T t t' _ _ rfl rfl)
    rw [m] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) (t' ≫ i₀) x
    have l := σ.law1 T t t' x z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [MonObj.mul_comp] at va
    rw [toBase_comp (hw := hw) hE.1.w hi, toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw (t' ≫ i₀)) (toBase hw x)) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw (t' ≫ i₀)) (toBase hw x)) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'
  · obtain ⟨T, rfl⟩ := ov Z a _ ha
    obtain ⟨t, rfl⟩ := toBase_surj hE.1 hE.1.w t
    obtain ⟨x, rfl⟩ := toBase_surj hF hw x
    obtain ⟨x', rfl⟩ := toBase_surj hF hw x'
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB (Z := T.left) z
    rw [← hP.mul] at ha
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ y, W y = gw w y.left z (I (y.left ≫ F)) (J' y.left) := ⟨_, fun _ => rfl⟩
    have c := (hP.vals T z J' I hJ' hI W hW).2.2 (t ≫ i₀) x x'
    have l := σ.law2 T t x x' z J' hJ'
    have va := hv T _ _ a ha z J' I hJ' hI W hW
    have vb := hv T _ _ b hb z J' I hJ' hI W hW
    have vd := hv T _ _ d hd z J' I hJ' hI W hW
    rw [← _root_.mul_assoc (t ≫ i₀)] at va
    rw [toBase_comp (hw := hw) hE.1.w hi]
    show @id (T.left.presheaf.stalk z)ˣ (val s a z I) = @id (T.left.presheaf.stalk z)ˣ
      (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀)) (toBase hw x) (toBase hw x')) *
        @id (T.left.presheaf.stalk z)ˣ (val s b z I) * @id (T.left.presheaf.stalk z)ˣ (val s d z I)
    generalize @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ ρ)) z I (toBase hw (t ≫ i₀))
      (toBase hw x) (toBase hw x')) = C at c ⊢
    refine va.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (C * ·) vb) vd).symm)
    rw [l]
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv] at c' ⊢
    linear_combination (norm := abel) -c'

end

theorem biTriv_transport : ∀ (S S₀ : Scheme.{0}) (ρ : S₀ ⟶ S) [Mono ρ] (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G ρ F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P ρ F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat ρ F i₀ i → BiTriv P₀.c i₀ → ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (splitTorus S X ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧ (∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧ (∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  intro S S₀ ρ _ X _ G _ _ G₀ _ _ F hw hF P P₀ w hP i i₀ _ _ hi σ
  exact exists_transport hF.1 (SplitTorus.isGrpPullback_bcMap ρ X) hP (torusCompat_iff.1 hi) σ

end GlobalTheory.UU.BiTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMapDomainMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

section
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem exists_addGauss (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    ∃ w : AddValuation (AddMonoidAlgebra F X) (WithTop ℚ),
      ∀ (f : AddMonoidAlgebra F X) (g : WithTop ℚ), g ≤ w f ↔ ∀ m, g ≤ v (f.coeff m) := by
  haveI : UniqueSums X :=
    (AddEquiv.uniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance
  exact ⟨AddValuation.ofValuation (GlobalTheory.gaussValAlg (G := X) (AddValuation.toValuation v)),
    fun f g => GlobalTheory.gaussValAlg_le_iff (G := X) (AddValuation.toValuation v) (f := f)⟩

theorem NullV.exists_lower {X : Type} {A : X → F} (hA : NullV v A) :
    ∃ M : ℚ, ∀ M' : ℚ, M' ≤ M → ∀ χ, (M' : WithTop ℚ) ≤ v (A χ) := by
  obtain ⟨M, hM⟩ := ((hA 0).image (fun χ => (v (A χ)).untopD 0)).bddBelow
  refine ⟨min M 0, fun M' hM' χ => ?_⟩
  by_cases hχ : v (A χ) < ((0 : ℚ) : WithTop ℚ)
  · have h1 : M ≤ (v (A χ)).untopD 0 := hM ⟨χ, hχ, rfl⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hχ.ne_top
    rw [← hr] at h1 ⊢
    rw [WithTop.untopD_coe] at h1
    exact WithTop.coe_le_coe.mpr (hM'.trans ((min_le_left _ _).trans h1))
  · exact (WithTop.coe_le_coe.mpr (hM'.trans (min_le_right _ _))).trans (not_lt.mp hχ)

theorem NullV.exists_trunc {X : Type} {A : X → F} (hA : NullV v A) (N : ℚ) :
    ∃ a : AddMonoidAlgebra F X, (∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) ∧
      (∀ χ, v (A χ) ≤ v (a.coeff χ)) ∧ ∀ χ, v (A χ) < (N : WithTop ℚ) → a.coeff χ = A χ := by
  classical
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (hA N).toFinset
    (fun χ => if v (A χ) < (N : WithTop ℚ) then A χ else 0) (fun χ hχ => ?_)), fun χ => ?_, fun χ => ?_,
    fun χ hχ => ?_⟩
  · rw [Set.Finite.mem_toFinset]
    by_contra hn
    exact hχ (if_neg hn)
  · simp only [Finsupp.onFinset_apply]
    split_ifs with hχ
    · simp
    · simpa using hχ
  · simp only [Finsupp.onFinset_apply]
    split_ifs with hχ
    · exact le_rfl
    · simp
  · simp only [Finsupp.onFinset_apply, if_pos hχ]

theorem coeff_mapDomain_mul {X : Type} [AddCommGroup X] (h : X →+ X) (a c : AddMonoidAlgebra F X)
    (T : Finset X) (hT : a.coeff.support ⊆ T) (α : X) :
    (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α = ∑ χ ∈ T, a.coeff χ * c.coeff (α - h χ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_mul]),
    Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [neg_add_eq_sub]

theorem val_mul_sub_mul {x y x' y' : F} {M N : ℚ} (hx : (N : WithTop ℚ) ≤ v (x - x'))
    (hy : (N : WithTop ℚ) ≤ v (y - y')) (hy0 : (M : WithTop ℚ) ≤ v y) (hx0 : (M : WithTop ℚ) ≤ v x') :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (x * y - x' * y') := by
  have e : x * y - x' * y' = (x - x') * y + (y - y') * x' := by ring
  rw [e, WithTop.coe_add]
  refine v.map_le_add ?_ ?_ <;> rw [v.map_mul]
  · exact add_le_add hx hy0
  · exact add_le_add hy hx0

theorem SumV.fibre {X : Type} [AddCommGroup X] (h : X →+ X) (α : X) (f : X → X → F) {s : F}
    (H : SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => f p.1.1 p.1.2) s) :
    SumV v (fun χ => f χ (α - h χ)) s := by
  classical
  let e : X ≃ {p : X × X // h p.1 + p.2 = α} :=
    { toFun := fun χ => ⟨(χ, α - h χ), by simp⟩
      invFun := fun p => p.1.1
      left_inv := fun χ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl (sub_eq_of_eq_add' p.2.symm)) }
  intro q
  obtain ⟨S, hS⟩ := H q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) (fun p hp => by
    rw [Finset.mem_map_equiv]
    exact hT (Finset.mem_map_of_mem _ hp))
  rw [Finset.sum_map] at this
  exact this

theorem val_sum_sub_coeff {X : Type} [AddCommGroup X] (h : X →+ X) {A C : X → F}
    {a c : AddMonoidAlgebra F X} {M N : ℚ}
    (hA : ∀ χ, (M : WithTop ℚ) ≤ v (A χ)) (hC : ∀ χ, (M : WithTop ℚ) ≤ v (C χ))
    (ha : ∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) (ha' : ∀ χ, v (A χ) ≤ v (a.coeff χ))
    (hc : ∀ χ, (N : WithTop ℚ) ≤ v (C χ - c.coeff χ))
    (T : Finset X) (hT : a.coeff.support ⊆ T) (α : X) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (∑ χ ∈ T, A χ * C (α - h χ) -
      (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α) := by
  rw [coeff_mapDomain_mul h a c T hT, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun χ _ => val_mul_sub_mul (ha _) (hc _) (hC _) ((hA _).trans (ha' _))

theorem val_coeff_of_sumV {X : Type} [AddCommGroup X] (h : X →+ X) {A₁ A₂ C₁ C₂ : X → F}
    {a₁ a₂ c₁ c₂ : AddMonoidAlgebra F X} {M N : ℚ}
    (hA₁ : ∀ χ, (M : WithTop ℚ) ≤ v (A₁ χ)) (hA₂ : ∀ χ, (M : WithTop ℚ) ≤ v (A₂ χ))
    (hC₁ : ∀ χ, (M : WithTop ℚ) ≤ v (C₁ χ)) (hC₂ : ∀ χ, (M : WithTop ℚ) ≤ v (C₂ χ))
    (ha₁ : ∀ χ, (N : WithTop ℚ) ≤ v (A₁ χ - a₁.coeff χ)) (ha₁' : ∀ χ, v (A₁ χ) ≤ v (a₁.coeff χ))
    (ha₂ : ∀ χ, (N : WithTop ℚ) ≤ v (A₂ χ - a₂.coeff χ)) (ha₂' : ∀ χ, v (A₂ χ) ≤ v (a₂.coeff χ))
    (hc₁ : ∀ χ, (N : WithTop ℚ) ≤ v (C₁ χ - c₁.coeff χ))
    (hc₂ : ∀ χ, (N : WithTop ℚ) ≤ v (C₂ χ - c₂.coeff χ)) (α : X)
    (H : SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v ((AddMonoidAlgebra.mapDomainRingHom F h a₁ * c₂ -
      AddMonoidAlgebra.mapDomainRingHom F h a₂ * c₁).coeff α) := by
  classical
  obtain ⟨S, hS⟩ := SumV.fibre h α (fun x y => A₁ x * C₂ y - A₂ x * C₁ y) H (N + M)
  have h0 := hS (S ∪ (a₁.coeff.support ∪ a₂.coeff.support)) Finset.subset_union_left
  have h1 := val_sum_sub_coeff h hA₁ hC₂ ha₁ ha₁' hc₂ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_left.trans Finset.subset_union_right) α
  have h2 := val_sum_sub_coeff h hA₂ hC₁ ha₂ ha₂' hc₁ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_right.trans Finset.subset_union_right) α
  have h3 := v.map_le_sub (v.map_le_sub h2 h1) h0
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring
end

theorem sumV_cancel : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X →+ X), Function.Injective h → ∀ A₁ A₂ B₁ B₂ C₁ C₂ : X → F, NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  classical
  intro F _ v X _ _ _ h hinj A₁ A₂ B₁ B₂ C₁ C₂ nA₁ nA₂ nB₁ nB₂ nC₁ nC₂ HA HB hC α q
  obtain ⟨w, hw⟩ := exists_addGauss v X
  obtain ⟨χ₀, hχ₀⟩ := Function.ne_iff.mp hC
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun e => hχ₀ (v.top_iff.mp e) : v (C₂ χ₀) ≠ ⊤)
  obtain ⟨M₁, hM₁⟩ := nA₁.exists_lower
  obtain ⟨M₂, hM₂⟩ := nA₂.exists_lower
  obtain ⟨M₃, hM₃⟩ := nB₁.exists_lower
  obtain ⟨M₄, hM₄⟩ := nB₂.exists_lower
  obtain ⟨M₅, hM₅⟩ := nC₁.exists_lower
  obtain ⟨M₆, hM₆⟩ := nC₂.exists_lower
  obtain ⟨M, l1, l2, l3, l4, l5, l6⟩ : ∃ M : ℚ, M ≤ M₁ ∧ M ≤ M₂ ∧ M ≤ M₃ ∧ M ≤ M₄ ∧ M ≤ M₅ ∧ M ≤ M₆ :=
    ⟨min M₁ (min M₂ (min M₃ (min M₄ (min M₅ M₆)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  replace hM₁ := hM₁ M l1
  replace hM₂ := hM₂ M l2
  replace hM₃ := hM₃ M l3
  replace hM₄ := hM₄ M l4
  replace hM₅ := hM₅ M l5
  replace hM₆ := hM₆ M l6
  obtain ⟨N, n1, n2, n3⟩ : ∃ N : ℚ, m < N ∧ q + m ≤ M + (N + M) ∧ q ≤ N + M := by
    refine ⟨max (m + 1) (max (q + m - M - M) (q - M)), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have := (le_max_left (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
    · have := (le_max_right (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
  obtain ⟨a₁, ha₁, ha₁', -⟩ := nA₁.exists_trunc N
  obtain ⟨a₂, ha₂, ha₂', -⟩ := nA₂.exists_trunc N
  obtain ⟨b₁, hb₁, hb₁', -⟩ := nB₁.exists_trunc N
  obtain ⟨b₂, hb₂, hb₂', -⟩ := nB₂.exists_trunc N
  obtain ⟨c₁, hc₁, -, -⟩ := nC₁.exists_trunc N
  obtain ⟨c₂, hc₂, -, hc₂'⟩ := nC₂.exists_trunc N
  have EA := (hw _ _).mpr fun β =>
    val_coeff_of_sumV h hM₁ hM₂ hM₅ hM₆ ha₁ ha₁' ha₂ ha₂' hc₁ hc₂ β (HA β)
  have EB := (hw _ _).mpr fun β =>
    val_coeff_of_sumV h hM₃ hM₄ hM₅ hM₆ hb₁ hb₁' hb₂ hb₂' hc₁ hc₂ β (HB β)
  have push : ∀ (d : AddMonoidAlgebra F X) (g : WithTop ℚ),
      g ≤ w (AddMonoidAlgebra.mapDomainRingHom F h d) ↔ ∀ χ, g ≤ v (d.coeff χ) := by
    intro d g
    rw [hw, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    refine ⟨fun H χ => ?_, fun H β => ?_⟩
    · have := H (h χ)
      rwa [Finsupp.mapDomain_apply hinj] at this
    · by_cases hβ : β ∈ Set.range h
      · obtain ⟨χ, rfl⟩ := hβ
        rw [Finsupp.mapDomain_apply hinj]
        exact H χ
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hβ, v.map_zero]
        exact le_top
  set P := AddMonoidAlgebra.mapDomainRingHom F h with hP
  have key : ((q + m : ℚ) : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) + w c₂ := by
    have e : P (b₁ * a₂ - b₂ * a₁) * c₂ =
        P a₂ * (P b₁ * c₂ - P b₂ * c₁) - P b₂ * (P a₁ * c₂ - P a₂ * c₁) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [← w.map_mul, e]
    refine (WithTop.coe_le_coe.mpr n2).trans ?_
    rw [WithTop.coe_add]
    refine w.map_le_sub ?_ ?_ <;> rw [w.map_mul]
    · exact add_le_add ((push _ _).mpr fun χ => (hM₂ χ).trans (ha₂' χ)) EB
    · exact add_le_add ((push _ _).mpr fun χ => (hM₄ χ).trans (hb₂' χ)) EA
  have hc : w c₂ ≤ (m : WithTop ℚ) := by
    have := (hw c₂ _).mp le_rfl χ₀
    rwa [hc₂' χ₀ (by rw [← hm]; exact WithTop.coe_lt_coe.mpr n1), ← hm] at this
  have key2 : (q : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) := by
    have := key.trans (add_le_add le_rfl hc)
    rw [WithTop.coe_add] at this
    exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
  have key3 := (push _ _).mp key2 α
  refine ⟨b₁.coeff.support ∪ b₂.coeff.support, fun T hT => ?_⟩
  have h1 := val_sum_sub_coeff (AddMonoidHom.id X) hM₃ hM₂ hb₁ hb₁' ha₂ T
    (Finset.subset_union_left.trans hT) α
  have h2 := val_sum_sub_coeff (AddMonoidHom.id X) hM₄ hM₁ hb₂ hb₂' ha₁ T
    (Finset.subset_union_right.trans hT) α
  rw [AddMonoidAlgebra.mapDomainRingHom_id] at h1 h2
  simp only [RingHom.id_apply, AddMonoidHom.id_apply] at h1 h2
  have h3 := v.map_le_sub (v.map_le_sub ((WithTop.coe_le_coe.mpr n3).trans h2)
    ((WithTop.coe_le_coe.mpr n3).trans h1)) key3
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConvTermFe
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem famFE_val (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu β
  rw [← hv u hu hc Z r z J hJ]
  exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hs mu β u hu hc) _ r.left z J hJ

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

theorem units_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k l : ℕ) (mu β ga : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J) *
      (uVal D F l ga (cP D _ mu) r z J * val (DegPre.famMult D F l mu ga) (r ≫ fst _ _).left z J) *
      th D z J (cP D Z (β + k • mu)) (cP D Z (ga + l • mu)) (r ≫ DegPre.prB D F) =
    th D z J (cP D Z β) (cP D Z ga) ((r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F) *
      (uVal D F (k + l) (β + ga) (cP D _ mu) r z J *
        val (DegPre.famMult D F (k + l) mu (β + ga)) (r ≫ fst _ _).left z J) := by
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  have hm : r ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D Z mu := by rw [comp_cP, comp_cP]
  have hy : (r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (r ≫ DegPre.prB D F) * cP D Z mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, hm]
  have t := tau_mul (r ≫ fst (TF (R := R) F) D.P.A) hJ hB β ga mu
  rw [tau_symm _ hJ (β + ga), tau_symm _ hJ β, tau_symm _ hJ ga] at t
  have key := GlobalTheory.translationUnit_mul _ _ _ C k l (cP D Z β) (cP D Z ga) (cP D Z mu) (r ≫ DegPre.prB D F)
  rw [hy, uVal, uVal, uVal, hm, val_famMult _ hJ, val_famMult _ hJ, val_famMult _ hJ, cPoint_add, cPoint_add, cPoint_add,
    cPoint_nsmul, cPoint_nsmul]
  simp only [val_powGen, pow_add]
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  have t' := congrArg Additive.ofMul t
  simp only [ofMul_mul, ofMul_inv] at key' t' ⊢
  linear_combination (norm := abel) key' - t'

theorem conv_term_fe : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k l : ℕ) (s : Raw D F k) (s' : Raw D F l), DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ∀ (mu α β ga β' ga' : D.X), β + ga = α → β' = β + k • mu → ga' = ga + l • mu → ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α) → ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J), Good D.P.L z J → sval (s β') r.left z J * sval (s' ga') r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β') (toUnit Z ≫ D.c ga') (r ≫ snd _ _)).val = sval (s β) (r ≫ DegPre.trF D F mu).left z J * sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) ((r ≫ DegPre.trF D F mu) ≫ snd _ _)).val * (val u r.left z J).val := by
  rintro hG R _ _ D hB F _ _ k l s s' hs hs' mu _ β ga _ _ rfl rfl rfl u hu hc Z r z J hJ
  have e := congrArg Units.val (units_mul hB k l mu β ga Z r z J hJ)
  rw [famFE_val hG k s hs mu β Z r z J hJ, famFE_val hG l s' hs' mu ga Z r z J hJ,
    (gen_fe hG (k + l) mu (β + ga)).2 u hu hc Z r z J hJ]
  rw [Units.val_mul, Units.val_mul, Units.val_mul (th D z J _ _ _)] at e
  refine Eq.trans ?_ ((congrArg (sval (s β) (r ≫ DegPre.trF D F mu).left z J *
    sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * ·) e).trans (_root_.mul_assoc _ _ _).symm)
  rw [_root_.mul_mul_mul_comm, _root_.mul_assoc]
  rfl

end GlobalTheory.ConvTermFE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sval_eq_zero_of_linearIndependent_comb : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (X Y Y' : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of R)) [Flat π] (π' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y), IsPullback p π' π (Spec.map (CommRingCat.ofHom f)) → ∀ (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (M : Type) [Fintype M] (β : M → R'), (∀ c : M → R, ∑ m, f (c m) * β m = 0 → ∀ m, c m = 0) → ∀ d : M → LB.Sec (LB.LinComb L φ ε), (∀ (y : Y') (J), Good L y J → ∑ m, constVal π' y (β m) * sval (d m) p y J = 0) → ∀ (m : M) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval (d m) r z J = 0 := by
  first | exact @GlobalTheory.sval_eq_zero_of_indep_comb | exact GlobalTheory.sval_eq_zero_of_indep_comb | (intros; apply GlobalTheory.sval_eq_zero_of_indep_comb <;> assumption)
end


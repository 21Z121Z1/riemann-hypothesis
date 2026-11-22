import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) {T : Over (Sp R)} (ρ : T ⟶ D.P.A) (β : D.X) (n j : ℤ)
    {U : Type} [CommGroup U] (hh : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, hh (ρ.left ≫ tφ D a β i) ^ tε n j i = hh ρ.left ^ (n - 1) * hh (DVR.cP D T β * ρ).left *
      (hh (DVR.cP D T β).left)⁻¹ * hh (1 : T ⟶ D.P.A).left * hh (ρ ≫ a).left ^ j := by
  have e₁ : ρ.left ≫ tφ D a β 1 = (DVR.cP D T β * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (toUnit _ ≫ D.c β)).trans (by
      rw [Category.comp_id, ← DVR.cP, DVR.comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₄ : ρ.left ≫ tφ D a β 4 = (ρ ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem iota_c (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (α mu : D.X)
    (u : LB.Gen (IotaLB D a α (h' α))) (hu : IsIota u) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J)
    (hJ : Good D.P.L z J) :
    val (D.tau (h mu) α) r z J = val (D.tau mu (h' α)) r z J * val u (r ≫ D.xK mu) z J := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, hma', hr, -, hc, hB⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T (h' α) = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  have key := gen_unique' D.P.isLB (φ := Sum.elim (D.Oφ (𝟙 _) (h' α)) (D.Oφ a α)) (ε := Sum.elim Oε Oinvε)
    (u' := LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) _ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (fun y I hI => by
      let T : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
      have C : IsCub (cubV D.cub (T := T) y I) := isCub_cubV D.cub hI
      have e := (ros_add D.cub hG D.P.isAb a a' t ht t₀ (T := T) hI 1 1 (DVR.cP D _ α)).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      have e' : val₂ t (T := T) y I 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
      have o : (1 : T ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
      have k : eSec D.P.A ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
        rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
      have n := hu.2 _ (𝟙 _) y I hI
      rw [Category.id_comp] at n
      rw [val_inv, val_pull hI, k]
      exact n.trans (inv_eq_one.2 e').symm) Z (r ≫ D.xK mu) z J hJ
  have m : D.xK mu ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = D.pt2 mu α := by
    rw [← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]; rfl
  have b := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hB t ht t₀ mu α) r)
  rw [val_pull hJ] at b
  rw [val_inv, val_pull hJ, Category.assoc, m] at key
  rw [key, ← b, mul_inv_cancel_right]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem formEq_pull (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (mu ν α β β' : D.X)
    (aK : DegPre.BF D (FractionRing R) ⟶ DegPre.BF D (FractionRing R))
    (h₁ : aK ≫ DegPre.prB D (FractionRing R) = DegPre.prB D (FractionRing R) ≫ a)
    (h₂ : aK ≫ DegPre.trF D (FractionRing R) ν ≫ DegPre.prB D (FractionRing R) =
      DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) ≫ a) :
    FormEq (Sum.elim (Sum.elim (fun i => aK.left ≫ DegPre.deltaφ D (FractionRing R) k α ν i)
        (fun i => (DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β') (D.Oφ a (α + k • ν)) i))
        (fun i => (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β) (D.Oφ a α) i))
      (Sum.elim (Sum.elim (DegPre.deltaε k) (Sum.elim Oε Oinvε)) (fun i => - Sum.elim Oε Oinvε i))
      (dφ D a mu β β') (dε 0 k) := by
  intro U _ hh
  have io : ∀ (ρ : DegPre.BF D (FractionRing R) ⟶ D.P.A) (ξ δ : D.X),
      ∏ i, hh (ρ.left ≫ Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a ξ) i) ^ Sum.elim Oε Oinvε i =
        (hh (DVR.cP D _ δ * ρ).left * (hh (DVR.cP D _ δ).left)⁻¹ * (hh ρ.left)⁻¹ *
          hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left) *
        ((hh (DVR.cP D _ ξ * (ρ ≫ a)).left)⁻¹ * hh (DVR.cP D _ ξ).left * hh (ρ ≫ a).left *
          (hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left)⁻¹) := fun ρ ξ δ => by
    refine DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ ?_ ?_
    · simp only [Sum.elim_inl, WeightPf.Oφ_comp, Category.comp_id]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ D ρ δ hh
    · simp only [Sum.elim_inr, WeightPf.Oφ_comp]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ_inv D (ρ ≫ a) ξ hh
  have p₁ := DVR.prod_fam D (FractionRing R) aK (α + k • ν) k hh
  have p₂ := DVR.prod_fam D (FractionRing R) (aK ≫ DegPre.trF D (FractionRing R) ν) α k hh
  have q₁ := prod_tφ D a (DegPre.prB D (FractionRing R)) β' 0 k hh
  have q₂ := prod_tφ D a (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) β 0 k hh
  rw [h₁] at p₁
  rw [Category.assoc, h₂, ← Category.assoc] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂ q₂
  refine (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (DVR.prod_neg _ _ p₂)) (io _ _ _))
    (DVR.prod_neg _ _ (io _ _ _))).trans
    (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).symm)
  simp only [Over.comp_left, Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  intro R _ _ _ _ D a a' h h' hE k F mu α u u' s s' hu hu' hs hs'
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, -, -, hch, -, -⟩ := id hE
  have hL := D.toPre.P.isLB
  obtain ⟨⟨uF, huF, hcF⟩, -⟩ := DVR.gen_fe (D := D.toPre) (F := FractionRing R) hG k (h mu) α
  have feF := (secRel_iff hL _ _ _ _ _ _ _ _ _ uF).1 (F.F.fe (h mu) α uF huF hcF)
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by unfold scal; rw [map_one, map_one]
  have ext : ∀ β (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (F.F.s β) r z J = sval (F.f β) (r ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J := by
    intro β Z r z J hJ
    have e := F.ext β
    rw [h1] at e
    exact (DVR.SectionScalarValuation.secScal_sval e r z hJ).symm
  let aK : DegPre.BF D.toPre (FractionRing R) ⟶ DegPre.BF D.toPre (FractionRing R) :=
    lift (fst _ _) (DegPre.prB D.toPre (FractionRing R) ≫ a)
  have aK_pr : aK ≫ DegPre.prB D.toPre (FractionRing R) = DegPre.prB D.toPre (FractionRing R) ≫ a := lift_snd _ _
  have aK_fst : aK ≫ fst _ _ = fst _ _ := lift_fst _ _
  have cPh : ∀ T, DVR.cP D.toPre T (h mu) = DVR.cP D.toPre T mu ≫ a := fun T => by
    rw [DVR.cP, hch, ← Category.assoc]; rfl
  have trpr : ∀ ν, DegPre.trF D.toPre (FractionRing R) ν ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.prB D.toPre (FractionRing R) * DVR.cP D.toPre _ ν := fun ν => by
    rw [DVR.trF_eq, DVR.tr_pr, DVR.comp_cP]
  have M1 : aK ≫ DegPre.trF D.toPre (FractionRing R) (h mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R) ≫ a := by
    haveI := hma
    rw [trpr, MonObj.comp_mul, aK_pr, DVR.comp_cP, ← Category.assoc, trpr, MonObj.mul_comp, cPh]
  haveI := hma
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.prB D.toPre (FractionRing R) = 1 := lift_snd _ _
  have M2 : DegPre.zF D.toPre (FractionRing R) ≫ aK = DegPre.zF D.toPre (FractionRing R) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, aK_fst]
    · rw [Category.assoc, aK_pr, ← Category.assoc, z₂, MonObj.one_comp]
  have M3 : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.trF D.toPre (FractionRing R) mu ≫
      DegPre.prB D.toPre (FractionRing R) = DVR.cP D.toPre _ mu := by
    rw [trpr, MonObj.comp_mul, z₂, DVR.comp_cP, _root_.one_mul]
  intro v hv Z x z J hJ
  have wv : ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      val (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ uF aK.left)
        (LB.pullGen _ _ _ u' (DegPre.prB D.toPre (FractionRing R)).left)) (LB.invGen _ _ _ (LB.pullGen _ _ _ u
          (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left))) x z J =
      val uF (x ≫ aK.left) z J * val u' (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J *
        (val u (x ≫ (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left) z J)⁻¹ :=
    fun Z x z J hJ => by rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]
  have key := (gen_unique' hL (formEq_pull D.toPre a k mu (h mu) α (h' α) (h' (α + k • h mu)) aK aK_pr M1)
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
    (congrArg (fun q => q.left) z₁) (DVR.surj_appTop D.toPre _ hG) hv.1
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huF _)
      (DVR.pullGen_isGen _ _ _ _ hu'.1 _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu.1 _)))
    (fun y I hI => by
      have e₁ := val_corr hI hcF (𝟙 _)
      rw [val_pull hI, Category.id_comp] at e₁
      have e₂ := DVR.val_famMult (D := D.toPre) (F := FractionRing R) (𝟙 _) hI k (h mu) α
      rw [Over.id_left, Category.id_comp, DVR.TWM.val_powGen, DVR.TWM.val_powGen] at e₂
      have e₃ : val u' (1 : TF (R := R) (FractionRing R) ⟶ D.toPre.P.A).left y I = 1 :=
        hu'.2 _ (TF (R := R) (FractionRing R)).hom y I hI
      have e₄ := iota_c D.toPre a a' h h' hE α mu u hu _ (jFK (R := R) (FractionRing R)) y I hI
      have e₅ : jFK (R := R) (FractionRing R) ≫ D.toPre.xK mu = (DVR.cP D.toPre (TF (R := R) (FractionRing R)) mu).left :=
        (Category.assoc _ _ _).symm
      rw [wv _ _ y I hI, hv.2 y I hI, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, M2, z₂, M3, e₁, e₂, e₃, e₄, e₅]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) Z x z J hJ).trans (wv Z x z J hJ)
  have f₁ : (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left =
      (x ≫ aK.left) ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, aK_pr]
  have f₂ : ((x ≫ aK.left) ≫ (DegPre.trF D.toPre (FractionRing R) (h mu)).left) ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left := by
    have := congrArg (fun q => x ≫ q.left) M1
    simpa only [Over.comp_left, Category.assoc] using this
  rw [hs' _ _ z J hJ, hs _ _ z J hJ, key, f₁, ← ext _ _ _ z J hJ, feF _ _ z J hJ, ext _ _ _ z J hJ, f₂, Over.comp_left,
    _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_comm (val u _ z J), inv_mul_cancel_right]

end GlobalTheory.TwFam.PullRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.GenPull

theorem pull_comp_iso {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {F : Y ⟶ X} (H : LBIso M (L.pull F)) (h : Z ⟶ Y) :
    LBIso (M.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (chartPullSame L _ _ _ h fun _ => rfl) H

theorem pull_congr_iso {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a b : Y ⟶ X} (e : a = b) :
    LBIso (L.pull a) (L.pull b) := e ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)

theorem pull_pull_iso {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  pull_comp_iso (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)) b

theorem pull_id_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

end GlobalTheory.TInj.GenPull

open GlobalTheory.TInj.GenPull in

theorem GlobalTheory.TInj.overPt_genPull : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  intro X g n B _ ζ sX c R _ _ V _ _ J J' D₀ A₀ G₀ _ _ U₀ f D hD A U hU y₀ α₀ hO κ hκ
  let G := (Over.pullback (specOf f)).obj G₀
  let p := pullback.fst G.hom (jK V)
  let q := pullback.fst G₀.hom (specOf f)
  let p₀ := pullback.fst G₀.hom (jK R)
  have hsq : jK V ≫ specOf f = κ ≫ jK R := hκ.symm
  let κG : pullback G.hom (jK V) ⟶ pullback G₀.hom (jK R) :=
    pullback.lift (p ≫ q) (pullback.snd _ _ ≫ κ) (by
      have c1 : q ≫ G₀.hom = G.hom ≫ specOf f := pullback.condition
      have c2 : p ≫ G.hom = pullback.snd G.hom (jK V) ≫ jK V := pullback.condition
      rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, hsq, Category.assoc])
  have hκf : κG ≫ p₀ = p ≫ q := pullback.lift_fst _ _ _
  have w : κG ≫ ((Over.pullback (jK R)).obj G₀).hom = ((Over.pullback (jK V)).obj G).hom ≫ κ :=
    pullback.lift_snd _ _ _
  have hκG : IsGrpPullback ((Over.pullback (jK V)).obj G) ((Over.pullback (jK R)).obj G₀) κ κG :=
    (isGrpPullback_pullback G₀ (jK R)).cancel
      (((isGrpPullback_pullback G (jK V)).comp (isGrpPullback_pullback G₀ (specOf f))).congr hsq hκf.symm) w
  have : IsMonHom U.gen.hom := U.gen_hom
  have : IsMonHom U₀.gen.hom := U₀.gen_hom
  have : IsMonHom U.gen.symm.hom := show IsMonHom U.gen.inv by infer_instance
  have hu : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G₀) A₀.A (𝟙 _) U₀.gen.hom.left := isGrpPullback_of_iso U₀.gen
  let π : A.A.left ⟶ A₀.A.left := U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left
  have hπ : IsGrpPullback A.A A₀.A κ π := (hu.comp (hκG.comp hg)).congr (by simp) rfl
  obtain ⟨hO₁, α₀₂, sα₀, hΛ₀⟩ := hO

  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hLG₀ : U₀.LG.L.IsLB := U₀.LG.isLB
  obtain ⟨wL, hwL, -⟩ := hU.lg
  have E1 : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull p) := U.ext
  have E2 : LBIso (U.LG.L.pull p) (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) := pull_comp_iso ⟨wL, hwL⟩ p
  have E4 : LBIso (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) (U₀.LG.L.pull (κG ≫ p₀)) :=
    pull_congr_iso hLG₀ (by rw [hκf, Iso.refl_hom, Over.id_left, Category.id_comp])
  have E3 : LBIso ((A₀.L.pull U₀.gen.hom.left).pull κG) (U₀.LG.L.pull (κG ≫ p₀)) := pull_comp_iso U₀.ext κG
  have E5 := pull_pull_iso A₀.isLB U₀.gen.hom.left κG
  have hA₀g := pull_isLB A₀.isLB U₀.gen.hom.left
  have X1 : LBIso (A.L.pull U.gen.hom.left) (A₀.L.pull (κG ≫ U₀.gen.hom.left)) :=
    LBIso.trans (pull_isLB A.isLB _) (pull_isLB hLG _) (pull_isLB A₀.isLB _) E1
      (LBIso.trans (pull_isLB hLG _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E2
        (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E4
          (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hA₀g _) (pull_isLB A₀.isLB _) E3.symm E5)))
  have X2 : LBIso ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) (A₀.L.pull π) := pull_comp_iso X1 _
  have X3 : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_id_iso A.isLB)
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
        (pull_congr_iso A.isLB (by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]))
        (pull_pull_iso A.isLB _ _).symm)
  have hA : LBIso A.L (A₀.L.pull π) :=
    LBIso.trans A.isLB (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A₀.isLB _) X3 X2
  have sπ := GlobalTheory.LamPull.exists_isSquare hπ.1.w
  have hΛ := GlobalTheory.LamPull.lbIso_lam_pull hπ A₀.isLB A.isLB hA sπ
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hΛA₀ : (abelian₂ A₀.A A₀.L).IsLB := DVR.linComb_isLB _ A₀.isLB _ _
  refine ⟨π ≫ α₀, ⟨hπ.comp hO₁, _ ≫ α₀₂, ⟨?_, ?_⟩,
    LBIso.trans hΛA (pull_isLB hΛA₀ _) (pull_isLB c.isLB _) hΛ (pull_comp_iso hΛ₀ _)⟩, ?_⟩
  · rw [Category.assoc, sα₀.1, ← Category.assoc, sπ.1, Category.assoc]
  · rw [Category.assoc, sα₀.2, ← Category.assoc, sπ.2, Category.assoc]
  · intro Z x x₀ hx
    have : Mono (jK R) := GlobalTheory.GenericBundleDescent.mono_jK R
    have : Mono p₀ := pullback.fst_of_mono
    have h1 : x ≫ U.gen.inv.left ≫ κG = x₀ ≫ U₀.gen.inv.left := by
      apply (cancel_mono p₀).1
      simp only [Category.assoc, hκf]
      exact hx
    show x ≫ (U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left) ≫ α₀ = x₀ ≫ α₀
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc x, h1]
    simp only [Category.assoc]
    rw [← Category.assoc U₀.gen.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.HomConst

theorem map_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (ψ : G ⟶ G) :
    ((Over.pullback (thick R I e)).map ψ).left ≫ (fstG I e G).left = (fstG I e G).left ≫ ψ.left := by
  simp [fstG, pullback.lift_fst]

end GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.PullLin GlobalTheory.Mum.Two.HomConst in

theorem GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  intro R _ _ _ hB D A G _ _ hG U D' A' U' hD ψ bc b hψ hbc hb hP
  obtain ⟨hR, -⟩ := hB
  obtain ⟨wL, -, he, -, hlev⟩ := hP.lg

  have lev : ∀ e, ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h = ((Over.pullback (thick R (maximalIdeal R) e)).map ψ).left ∧
      (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        h ≫ (U.gt e).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt e).pG) x k ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            h ≫ D.toPre.Oφ ((U.gt e).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt e).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) h _
            Oinvε _ hψ ((U.gt e).t (hD.xe x)))) := by
    intro e
    obtain ⟨h, h1, h2, h3, -⟩ := hlev e
    have : Mono (fstG (maximalIdeal R) e G).left :=
      inferInstanceAs (Mono (pullback.fst G.hom (thick R (maximalIdeal R) e)))
    refine ⟨h, (cancel_mono (fstG (maximalIdeal R) e G).left).1 ?_, h2, h3⟩
    rw [h1, hbc, map_fstG]
  refine ⟨fun e => ?_, ?_⟩
  · obtain ⟨h, rfl, h2, -⟩ := lev e
    have : Mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) := inferInstance
    refine Over.OverMorphism.ext ((cancel_mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))).1 ?_)
    rw [hb] at h2
    clear lev hlev hP wL he
    simp only [Over.comp_left, Category.assoc]
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · show (U'.gt e).q.left ≫ pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ b.left = _
      congr 1
      exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨-, -, -, hC⟩ := id hR
    obtain ⟨h₀, hT⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R (maximalIdeal R) hR D' D A' A G G U'.toUnifPre
      U.toUnifPre ψ hψ
    have key : (h₀ : D.toPre.X → D'.toPre.X) = hD.xe.symm := by
      haveI := hC
      obtain ⟨t, ht, hi⟩ := hT 0
      refine acts_unique (U'.gt 0) (U.gt 0) (acts_of_torusHomOf _ _ _ ht hi) ?_
      obtain ⟨h, rfl, -, h3⟩ := lev 0
      clear lev hlev hP wL he hT ht hi
      intro Z r z J₁ J₂ hJ₁ hJ₂ c χ
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [AddEquiv.symm_apply_apply]
      obtain ⟨hψk, M⟩ := h3 x
      have P := (maps_iff hD.w _ _ Oinvε _ _ _ _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψk ·) (fun _ => rfl)).1 M
      have e := P Z r z
        (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
        (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => hJ₂ _) (fun k => hJ₁ _)
      have h1 := GlobalTheory.ArcLieCompare.prod_Oφ_zero (D := D'.toPre) (U'.gt 0).pG r
        (r ≫ (fstG (maximalIdeal R) 0 G).left ≫ G.hom) (c.trans (by simp only [Category.assoc])) x
        (fun f => gw hD.w f z (J₂ (f ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) (J₁ f))
      rw [h1, _root_.one_mul] at e
      rw [val_of _ _ z J₂
          (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
          (fun k => by simp only [Category.assoc, hψk k]),
        val_of _ r z J₁ (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => rfl)]
      exact e
    rw [key] at hT
    exact hT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatriStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (E : EndU U.toUnifPre), (∀ u, E.aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod := by
  first | exact @GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | exact GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod | (intros; apply GlobalTheory.Poinc.Sep.EndCompat.aG_comp_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndepende
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Poinc.FrameIndep

theorem ratio_indep {X H Y Z B B' : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X}
    (w : LB.Iso (L.pull ψ) (M.pull f)) (hw : w.IsGen) {e : B ⟶ X} {e' : B' ⟶ H}
    {a : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => e) (fun _ => 1))}
    {a' : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => e') (fun _ => 1))} (ha : a.IsGen)
    (ha' : a'.IsGen) (r : Z ⟶ Y) (t : Z ⟶ B) (t' : Z ⟶ B') (p : Z ⟶ X) (p' : Z ⟶ H)
    (h : r ≫ ψ = p) (h' : r ≫ f = p') (k : t ≫ e = p) (k' : t' ≫ e' = p') (z : Z)
    {J J' I I'} (hJ : Good L z J) (hJ' : Good M z J') (hI : Good L z I) (hI' : Good M z I') :
    Geo.Tor.gw w r z (J' p') (fun _ => J p) * val a t z J * (val a' t' z J')⁻¹ =
      Geo.Tor.gw w r z (I' p') (fun _ => I p) * val a t z I * (val a' t' z I')⁻¹ := by
  subst h h'
  have e₁ : val a t z J = _ * val a t z I := gen_trans ha t z (hJ.mem _ t) (hI.mem _ t)
  have e₂ : val a' t' z J' = _ * val a' t' z I' := gen_trans ha' t' z (hJ'.mem _ t') (hI'.mem _ t')
  have e₃ : Geo.Tor.gw w r z (J' (r ≫ f)) (fun _ => J (r ≫ ψ)) =
      _ * Geo.Tor.gw w r z (I' (r ≫ f)) (fun _ => I (r ≫ ψ)) :=
    (Geo.Tor.isGen_iff w).1 hw Z r z _ _ _ _ (hJ' (r ≫ f)) (hI' (r ≫ f))
      (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))
  rw [Geo.Tor.gm_pull_g L ψ r z _ _ (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))] at e₃
  rw [Geo.Tor.trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [k] at e₁
  rw [k'] at e₂
  rw [e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem frame_ratio_indep : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  intro V _ _ I D A G _ _ U w₀ hw₀ x e he h f hf hx z JA JA' JG JG' hJA hJG hJA' hJG'
  refine ratio_indep w₀ hw₀ he hf (x.left ≫ U.gen.inv.left) (𝟙 _) (toUnit (TF (R := V) (FractionRing V))).left
    x.left (toUnit (TF (R := V) (FractionRing V)) ≫ h).left ?_ ?_ (Category.id_comp _) rfl z hJA hJG hJA' hJG'
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (x.left ≫ ·) (congrArg (·.left) U.gen.inv_hom_id)).trans (Category.comp_id _)
  · exact (Category.assoc _ _ _).trans hx

end GlobalTheory.Poinc.FrameIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_characterMap_constant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  first | exact @GlobalTheory.Mum.Two.unifPre_hom_character_const | exact GlobalTheory.Mum.Two.unifPre_hom_character_const | (intros; apply GlobalTheory.Mum.Two.unifPre_hom_character_const <;> assumption)
end


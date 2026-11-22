import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTors
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTuple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.VExist

theorem cube_corr {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (h : IsCub θ) (a a' b b' p q : G) :
    θ b q a * θ b q p * θ a p (b * q) * (θ b' q a' * θ b' q p * θ a' p (b' * q)) * θ (a * b) (a' * b') (p * q) =
      θ a a' p * θ b b' q * θ a a' q * θ b b' p *
        (θ (b * b') q (a * a') * θ (b * b') q p * θ (a * a') p (b * b' * q)) := by
  have E := fun {x y : U} (e : x = y) => congrArg Additive.ofMul e
  have k0 := E (h.compat a b (a' * b') (p * q))
  have k1 := E (h.compat b b' q (a * a'))
  have k2 := E (h.compat a a' p (b * b' * q))
  have k3 := E (h.compat a' b' a (p * q))
  have k4 := E (h.compat a' b' b (p * q))
  have k5 := E (h.coc b b' q p)
  have k6 := E (h.coc b' q p b)
  have k7 := E (h.coc a' (b' * p * q) b a)
  have k8 := E (h.coc a a' q b)
  have k9 := E (h.coc a a' q b')
  have k10 := E (h.coc a' q b' a)
  have k11 := E (h.coc a (a' * q) b' b)
  have k12 := E (h.coc a a' b' b)
  have k13 := E (h.coc a' (b' * q) b a)
  have k14 := E (h.coc a' q b' b)
  have k15 := E (h.coc b (b' * q) p a)
  have k16 := E (h.coc b q p a)
  have k17 := E (h.coc b' q p a)
  have k18 := E (h.coc b (b' * q) p a')
  have k19 := E (h.coc a (p * q) b' a')
  have k20 := E (h.coc b (p * q) b' a')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  simp only [mul_comm, mul_assoc, mul_left_comm, h.s01, h.s12] at *
  linear_combination (norm := abel) k0 - k1 - k2 + k3 + k4 - k5 - k6 + k7 - k8 - k9 - k10 - k11 + k12 - k13 - k14 - k15 + k16 - k17 - k18 + k19 + k20

end GlobalTheory.Mum.TensTor.VExist

namespace GlobalTheory.Mum.TensTor.VExist

theorem pair_mult {F : Type} [Field F] (N : NumD F) (gi gj : N.Gt) (ai aj ai' aj' : N.X) :
    gj.s (ai + ai') * gi.s (aj + aj') /
        (N.θ (N.c (aj + aj')) gj.b (N.c (ai + ai')) * N.θ (N.c (aj + aj')) gj.b gi.b *
          N.θ (N.c (ai + ai')) gi.b (N.c (aj + aj') * gj.b)) *
      (N.θ (N.c ai * N.c aj) (N.c ai' * N.c aj') (gi.b * gj.b) /
        (N.θ (N.c ai) (N.c ai') gi.b * N.θ (N.c aj) (N.c aj') gj.b)) =
    gj.s ai * gi.s aj / (N.θ (N.c aj) gj.b (N.c ai) * N.θ (N.c aj) gj.b gi.b * N.θ (N.c ai) gi.b (N.c aj * gj.b)) *
      (gj.s ai' * gi.s aj' /
        (N.θ (N.c aj') gj.b (N.c ai') * N.θ (N.c aj') gj.b gi.b * N.θ (N.c ai') gi.b (N.c aj' * gj.b))) := by
  have m₁ := congrArg Additive.ofMul (gj.mult ai ai')
  have m₂ := congrArg Additive.ofMul (gi.mult aj aj')
  have k := congrArg Additive.ofMul (cube_corr N.cub (N.c ai) (N.c ai') (N.c aj) (N.c aj') gi.b gj.b)
  rw [N.c_add, N.c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at m₁ m₂ k ⊢
  linear_combination (norm := abel) m₁ + m₂ + k

theorem gtRelV_exists : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs := by
  intro F _ N N' r W φ e wv hT vs
  obtain ⟨-, hφb, he_add, -, hc, hw0, hθ, -⟩ := hT
  set b' := Function.surjInv hφb.2 (fun j => (vs j).b) with hb'def
  have hb' : ∀ j, φ b' j = (vs j).b := fun j => congrFun (Function.surjInv_eq hφb.2 _) j
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  let R : N'.X → Fˣ := fun χ' => ∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j
  let s' : N'.X → Fˣ := fun χ' => R χ' * U (N'.c χ' * b') * U 1 / (U (N'.c χ') * U b')
  have hmult : ∀ χ χ' : N'.X, s' (χ + χ') * N'.θ (N'.c χ) (N'.c χ') b' = s' χ * s' χ' := by
    intro χ χ'
    let P : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ i) * N.c (e χ j)) (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) /
        (N.θ (N.c (e χ i)) (N.c (e χ' i)) (vs i).b * N.θ (N.c (e χ j)) (N.c (e χ' j)) (vs j).b)) ^ W i j
    have hθu : N'.θ (N'.c χ) (N'.c χ') b' * U (N'.c χ * N'.c χ' * b') * U (N'.c χ) * U (N'.c χ') * U b' =
        P * U (N'.c χ * N'.c χ') * U (N'.c χ * b') * U (N'.c χ' * b') * U 1 := by
      have h := hθ (N'.c χ) (N'.c χ') b'
      simp only [hc, hb'] at h
      exact Units.ext (by simpa [U, P] using h)
    have hR : R (χ + χ') * P = R χ * R χ' := by
      simp only [R, P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow, he_add, he_add, pair_mult]
    have a := congrArg Additive.ofMul hθu
    have b := congrArg Additive.ofMul hR
    simp only [s', N'.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a + b
  refine ⟨⟨b', s', hmult⟩, hb', fun χ' => ?_⟩
  have h1 := hw0 (N'.c χ')
  have h2 := hw0 b'
  simp only [s', U, Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
  field_simp
  simp only [R]
  ring

end GlobalTheory.Mum.TensTor.VExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem exists_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X)
    (hc : ∀ χ, D.c (h' χ) = D.c χ ≫ a') (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) :
    ∃ F, IsCoordEnd g a a' h' u F := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcT : ∀ χ, DegPre.cT D T (h' χ) = DegPre.cT D T χ ≫ a' := fun χ => by
    simp only [DegPre.cT, hc, Category.assoc]
  have key : ∀ χ : D.X, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (g.pG ≫ a) χ) DegPre.gtε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val s r z J = val (g.t (h' χ)) r z J *
          val (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left) r z J := by
    intro χ
    obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (g.pG ≫ a) χ) (ε' := DegPre.gtε)
      (by
        intro U _ f
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _
          (c := (f (padd D.P.A g.pG (DegPre.cT D T (h' χ))).left)⁻¹ * f (DegPre.cT D T (h' χ)).left *
            f g.pG.left * (f (DegPre.zeroT D T).left)⁻¹) ?_
          (prod_ros a' a (DegPre.cT D T χ) g.pG f)).trans ?_
        · rw [Fin.prod_univ_four]
          show f _ ^ (-1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (-1 : ℤ) = _
          simp only [zpow_neg, zpow_one]
          rfl
        · rw [Fin.prod_univ_four]
          show _ = f (padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a)).left ^ (-1 : ℤ) * f (DegPre.cT D T χ).left ^ (1 : ℤ) *
            f (g.pG ≫ a).left ^ (1 : ℤ) * f (DegPre.zeroT D T).left ^ (-1 : ℤ)
          have p1 : padd D.P.A g.pG (DegPre.cT D T χ ≫ a') = (DegPre.cT D T χ ≫ a') * g.pG := mul_comm _ _
          have p2 : padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a) = DegPre.cT D T χ * (g.pG ≫ a) := rfl
          rw [hcT χ, p1, p2]
          simp only [zpow_neg, zpow_one]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
      (LB.mulGen D.P.L _ _ _ _ (g.t (h' χ)) (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.t_gen _) (DVR.pullGen_isGen _ _ _ _ hu _))
    exact ⟨s, hs, fun Z r z J hJ => (hv Z r z J hJ).trans (val_mul hJ _ _ _)⟩

  choose s hs hv using key
  have vv : ∀ χ (y : T.left) J, Good D.P.L y J → val (s χ) (𝟙 _) y J =
      val (g.t (h' χ)) (𝟙 _) y J * val₂ u y J (DegPre.cT D T χ) g.pG := fun χ y J hJ => by
    rw [hv χ _ _ y J hJ, val_pull hJ, Category.id_comp]; rfl
  have hm : ∀ χ χ' (y : T.left) J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J *
      cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) =
        val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J := fun χ χ' y J hJ => by
    have e1 : val (g.t (h' χ + h' χ')) (𝟙 _) y J *
        cubV D.cub y J (DegPre.cT D T χ ≫ a') (DegPre.cT D T χ' ≫ a') g.pG =
          val (g.t (h' χ)) (𝟙 _) y J * val (g.t (h' χ')) (𝟙 _) y J := by
      have := GlobalTheory.TorusCoord.val_t_mul g (𝟙 _) (h' χ) (h' χ') y J hJ
      rw [Category.id_comp] at this
      rw [← hcT, ← hcT]
      exact this
    have e2 := (ros_add D.cub GlobalTheory.globalFns_holds D.P.isAb a' a u hu h₀ hJ (DegPre.cT D T χ) (DegPre.cT D T χ')
      g.pG).1
    have hadd : DegPre.cT D T (χ + χ') = DegPre.cT D T χ * DegPre.cT D T χ' := DVR.cPoint_add D T χ χ'
    rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, map_add, hadd, _root_.mul_assoc, e2, ← _root_.mul_assoc, e1]
    exact mul_mul_mul_comm _ _ _ _
  have hcub : ∀ χ χ' (y : T.left) J, Good D.P.L y J →
      val (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)) (𝟙 _) y J =
        cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) := fun χ χ' y J hJ => by
    exact (val_cub D.cub (𝟙 T) hJ _ _ _).trans (by simp only [Category.id_comp])
  have hmult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)))
      (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' => corr_of_val D.P.isLB fun y J hJ => by
    exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl (hcub χ χ' y J hJ)).trans
      ((hm χ χ' y J hJ).trans (val_mul hJ _ _ _).symm))
  have hzero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L) := corr_of_val D.P.isLB fun y J hJ => by
    have h := hm 0 0 y J hJ
    have c0 : DegPre.cT D T 0 = 1 := cPoint_zero T
    have c1 : cubV D.cub y J (DegPre.cT D T 0) (DegPre.cT D T 0) (g.pG ≫ a) = 1 := by
      rw [c0]
      exact (isCub_cubV D.cub hJ).face 1 _
    rw [c1, add_zero, _root_.mul_one] at h
    exact (mul_eq_left.1 h.symm).trans (val_one _).symm
  let ξ : GtPt D T := ⟨g.pG ≫ a, s, hs, hzero, hmult⟩
  obtain ⟨F, hF⟩ := (GlobalTheory.TorusCoord.toGtPt_bijective g (T := thickObj R I e G)).2 ξ
  have hP := (GlobalTheory.TorusCoord.toGtPt_eq_iff g F ξ).1 hF
  refine ⟨F, hP.1.symm, fun χ Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hP.2 χ) r).symm.trans (hv χ Z r z J hJ))

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTrait
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_pow_left {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {a : G'.left ⟶ G.left} (h : IsGrpPullback G' G f a) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ a) : ∀ n : ℕ, (x₀ ^ n).left = (x ^ n).left ≫ a := by
  intro n
  induction n with
  | zero =>
    let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ a) (by
      show ((1 : T ⟶ G').left ≫ a) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hm := h.2 T 1 1 u u rfl rfl
    rw [_root_.mul_one] at hm
    have hu : u * u = u := Over.OverMorphism.ext hm
    have hu1 : u = 1 := mul_eq_left.1 hu
    rw [pow_zero, pow_zero, ← hu1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T (x ^ n) x (x₀ ^ n) x₀ ih hx

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oneTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ →
    ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A →
      ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  intro R _ _ _ hR D A hU
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, hW, hφ, hloc, hG', ga, hga, hpb, hLa⟩ := hU
  haveI : CharZero R := hR.2
  haveI : CharZero W := charZero_of_injective_ringHom hφ
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI iW : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have tf : ∀ (K M : Type) [Field K] [Field M] [Algebra K M], Module.IsTorsionFree K M := fun _ _ _ _ _ => inferInstance
  haveI := tf (FractionRing R) (Kb W)
  haveI := tf (FractionRing R) (Kb R)
  let em : Kb R →ₐ[FractionRing R] Kb W := IsAlgClosed.lift
  have hF : ∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := fun r =>
    congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (algebraMap (FractionRing R) (Kb R)).injective
  haveI : CharZero (Kb W) := charZero_of_injective_ringHom em.toRingHom.injective
  haveI := GlobalTheory.ArcExt.epi_spMap em.toRingHom
  have hρ : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact em.commutes x
  let ρ : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap em.toRingHom) hρ
  let Φ : (TFK (R := R) (Kb R) ⟶ A.A) →* (Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A) :=
    MonoidHom.mk' (fun y => ρ ≫ y) fun x y => by rw [MonObj.comp_mul]
  have hΦ : ∀ y, (Φ y).left = spMap em.toRingHom ≫ y.left := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext
    ((cancel_epi (spMap em.toRingHom)).1 ((hΦ x).symm.trans ((congrArg (fun q => q.left) e).trans (hΦ y))))
  have desc : ∀ k : ℕ, 1 ≤ k → ∀ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z ^ k = 1 →
      ∃ y : TFK (R := R) (Kb R) ⟶ A.A, Φ y = z := by
    intro k hk z hz
    let u : {y : TFK (R := R) (Kb R) ⟶ A.A // y ^ k = 1} →
        {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      fun y => ⟨Φ y.1, by rw [← map_pow, y.2, map_one]⟩
    have hu : Function.Injective u := fun y y' e => Subtype.ext (hΦinj (congrArg Subtype.val e))
    have c := GlobalTheory.ArcExt.card_torsion hL A (jFK (R := R) (Kb R)) (n := k) (Nat.cast_ne_zero.2 (by omega))
    have c' := GlobalTheory.ArcExt.card_torsion hL A ((TFK (R := W) (Kb W)).hom ≫ spMap ga) (n := k)
      (Nat.cast_ne_zero.2 (by omega))
    haveI : Finite {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c']; positivity)
    obtain ⟨y, e⟩ := (hu.bijective_of_nat_card_le (c'.trans c.symm).le).2 ⟨z, hz⟩
    exact ⟨y.1, congrArg Subtype.val e⟩
  have toA : ∀ (k : ℕ) (x' : TFK (R := W) (Kb W) ⟶ A'.A), x' ^ k = 1 →
      ∃ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z.left = x'.left ≫ a ∧ z ^ k = 1 := by
    intro k x' hx
    let z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A := Over.homMk (x'.left ≫ a) (by
      show (x'.left ≫ a) ≫ A.A.hom = (TFK (R := W) (Kb W)).hom ≫ spMap ga
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w])
    refine ⟨z, rfl, Over.OverMorphism.ext ?_⟩
    rw [grpPullback_pow_left hpb x' z rfl k, hx]
    exact ((grpPullback_pow_left hpb x' z rfl 0).trans (by rw [pow_zero])).symm
  have key : ∀ (k : ℕ) (p : QkPt D.toPre (Kb R) k), ∃ y : TFK (R := R) (Kb R) ⟶ A.A, 1 ≤ k →
      ∀ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k) (x' : TFK (R := W) (Kb W) ⟶ A'.A),
        QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
        x'.left ≫ a = spMap em.toRingHom ≫ y.left → QkToAkU U'.toUnifPre (Kb W) k p' x' := by
    intro k p
    by_cases hk : 1 ≤ k
    swap
    · exact ⟨1, fun h => absurd h hk⟩
    by_cases hex : ∃ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k),
        QkExt em.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD (Kb W) p₁.g p'.g
    swap
    · exact ⟨1, fun _ p₁ p' _ h₁ h₂ h₃ _ => absurd ⟨p₁, p', h₁, h₂, h₃⟩ hex⟩
    obtain ⟨p₁, p', h₁, h₂, h₃⟩ := hex
    obtain ⟨f, hf, hfk⟩ := GlobalTheory.TorsionIso.torsion_clause W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
    obtain ⟨z, hz, hzk⟩ := toA k (f p') (hfk p')
    obtain ⟨y, hy⟩ := desc k hk z hzk
    refine ⟨y, fun _ q₁ q' x' e₁ e₂ e₃ e₄ => ?_⟩
    obtain rfl : q₁ = p₁ := GlobalTheory.DegActCompare.qkExt_unique e₁ h₁
    obtain rfl : q' = p' := GlobalTheory.TorusExt.qk_ext (e₂.trans h₂.symm) (GlobalTheory.ArcPull.pullGt_unique hD hF e₃ h₃)
    rw [(hf.1 q' x')]
    refine Over.OverMorphism.ext (hpb.1.hom_ext ?_ ?_)
    · rw [e₄, ← hz, ← hy]
      exact (hΦ y).symm
    · rw [Over.w x', Over.w (f q')]
  choose lab hlab using key
  exact ⟨lab, W, inferInstance, inferInstance, inferInstance, φ, G', inferInstance, inferInstance, D', A', U', hD, a, iW, em,
    hW, hφ, hloc, hG', ⟨ga, hga, hpb, hLa⟩, hF, fun k hk p p₁ p' x' h₁ h₂ h₃ h₄ => hlab k p hk p₁ p' x' h₁ h₂ h₃ h₄⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsConst

theorem exists_factor_generic {R : Type} [CommRing R] [IsDomain R] {k : Type} [Field k] (τ : Sp k ⟶ Sp R)
    (w : Sp k) (hw : τ w = (⊥ : PrimeSpectrum R)) : ∃ κ : FractionRing R →+* k, τ = spMap κ ≫ jK R := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective τ
  have hφ : Function.Injective φ.hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : PrimeSpectrum.comap φ.hom w = ⊥ := hw
    have h2 : a ∈ (PrimeSpectrum.comap φ.hom w).asIdeal := by
      show φ.hom a ∈ (w : PrimeSpectrum k).asIdeal
      rw [ha]; exact Ideal.zero_mem _
    rw [h1] at h2
    exact h2
  refine ⟨IsFractionRing.lift hφ, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem exists_section_generic {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] {n : ℕ} (hA : IsAbelianScheme A) (hn : IsUnit (n : Γ(Sp R, ⊤)))
    (h : TorsRat A n) {K : Type} [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K)
    (x : Over.mk (spMap κ ≫ jK R) ⟶ A) (hx : x ^ n = 1) :
    ∃ σ : 𝟙_ (Over (Sp R)) ⟶ A, σ ^ n = 1 ∧ toUnit _ ≫ σ = x := by
  obtain ⟨x₀, h₀⟩ := h K κ x hx
  let ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (spMap κ) rfl
  have e₀ : x = ρ ≫ x₀ := Over.OverMorphism.ext h₀
  have hfl : Flat (spMap κ) := by
    letI := κ.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsu : Surjective (spMap κ) := ⟨fun p => ⟨Classical.arbitrary _, Subsingleton.elim (α := Sp (FractionRing R)) _ _⟩⟩
  have hepi : Epi ρ.left := Flat.epi_of_flat_of_surjective (spMap κ)
  have hx₀ : x₀ ^ n = 1 := by
    have : ρ ≫ x₀ ^ n = ρ ≫ 1 := by rw [MonObj.comp_pow, ← e₀, hx, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi ρ.left).1 congr(($this).left))
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (jK R) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have j₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R (FractionRing R) (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  have hp : IsProper A.hom := hA.proper
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT (jK R) A n hn _ x₀ hx₀ (𝟙 _) (Category.id_comp _)
  let σ : 𝟙_ (Over (Sp R)) ⟶ A := Over.homMk s hs₁
  have e₁ : toUnit (Over.mk (jK R)) ≫ σ = x₀ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact hs₂.trans (Category.id_comp _)
  refine ⟨σ, ?_, ?_⟩
  · have : toUnit (Over.mk (jK R)) ≫ σ ^ n = toUnit (Over.mk (jK R)) ≫ 1 := by
      rw [MonObj.comp_pow, e₁, hx₀, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h2 := congr(($this).left)
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h2
    have : AlgebraicGeometry.IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (AlgebraicGeometry.IsReduced (Sp R))
    exact ext_of_isDominant_of_isSeparated A.hom (by rw [Over.w, Over.w]) (jK R) h2
  · rw [e₀, ← e₁, ← Category.assoc, comp_toUnit]

theorem exists_section_of_torsRat : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R _ _ _ _ A _ _ n hA hn h K _ _ t x hx
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn'
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
  obtain ⟨w⟩ : Nonempty (Sp K) := inferInstance
  have hs : (⊥ : PrimeSpectrum R) ⤳ (torsion A n).hom (y.left w) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨z, hz, ez⟩ := Flat.generalizingMap (torsion A n).hom hs
  let k := AlgebraicClosure ((torsion A n).left.residueField z)
  let u : Sp k ⟶ (torsion A n).left :=
    spMap (algebraMap ((torsion A n).left.residueField z) k) ≫ (torsion A n).left.fromSpecResidueField z
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have hu : u v = z := by
    have : u v ∈ Set.range ((torsion A n).left.fromSpecResidueField z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨κ, hκ⟩ := exists_factor_generic (u ≫ (torsion A n).hom) v
    ((Scheme.Hom.comp_apply _ _ _).trans (by rw [hu]; exact ez))
  let u' : Over.mk (spMap κ ≫ jK R) ⟶ torsion A n := Over.homMk u hκ
  obtain ⟨σ, hσ, eσ⟩ := exists_section_generic A hA hn' h κ (u' ≫ torsion.ι A n) (by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])
  obtain ⟨C, hC, hCz⟩ := TorsionCover.exists_clopen_eq_one A hA hn'
    (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) (by
      rw [mul_pow, inv_pow, ← MonObj.comp_pow, hσ, MonObj.comp_one, LatticeTorsion.torsionι_pow_eq_one, inv_one,
        _root_.mul_one])
  have key : ∀ (T : Over (Sp R)) (a : T ⟶ torsion A n),
      a ≫ (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) = 1 ↔ toUnit T ≫ σ = a ≫ torsion.ι A n := fun T a => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_eq_one, eq_comm]
  have hzC : z ∈ C := (hCz _ u').1 ((key _ _).2 eσ) ⟨v, hu⟩
  have hyC : y.left w ∈ C := hz.mem_closed hC.isClosed hzC
  refine ⟨σ, hσ, ?_⟩
  rw [← hy]
  refine (key _ _).1 ((hCz _ y).2 ?_)
  rintro _ ⟨w', rfl⟩
  rwa [Subsingleton.elim (α := Sp K) w' w]

end GlobalTheory.TorsConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_cubicalSymmetricLineBundle_twoTorsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (a : 𝟙_ (Over S) ⟶ G),
    a ^ 2 = 1 → ∀ ρ : LB.Gen (P.L.L.pull a.left), ρ.IsGen →
    ∃ P' : GlobalTheory.UU.CP G, P'.L.L = P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left ∧
      (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P'.sym x.left z J' =
          val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹) ∧
      (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P'.c z J' x y u = cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹) := by
  first | exact @GlobalTheory.TranslCP.exists_transl | exact GlobalTheory.TranslCP.exists_transl | (intros; apply GlobalTheory.TranslCP.exists_transl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveAppStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transported_generator_descend_bijective_app : ∀ {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K] {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)}, PGen w → M.IsLB → L.IsLB → ∀ (π : Y' ⟶ Y), (∀ V : Y.Opens, Function.Bijective (π.app V).hom) → ∀ {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}, (∀ k, φ' k ≫ F = π ≫ φ k) → ∀ {ε : K → ℤ} (a : LB.Gen (LB.LinComb L φ' ε)), a.IsGen → ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J → val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  first | exact @GlobalTheory.Mum.BijDescent.exists_descend_bij | exact GlobalTheory.Mum.BijDescent.exists_descend_bij | (intros; apply GlobalTheory.Mum.BijDescent.exists_descend_bij <;> assumption)
end


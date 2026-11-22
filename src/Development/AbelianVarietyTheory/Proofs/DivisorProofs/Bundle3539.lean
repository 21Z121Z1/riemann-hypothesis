import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3526
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3528
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

open Polynomial in

theorem exists_finite_ext_sq_eq_uniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  intro V _ _ _ hV hP ϖ hϖ
  let K₀ := FractionRing V
  let p : K₀[X] := X ^ 2 - C (algebraMap V K₀ ϖ)
  let L := p.SplittingField
  have hdeg : (p.map (algebraMap K₀ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]
    norm_num
  obtain ⟨s, hs⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero hdeg
  have hs2 : s ^ 2 = algebraMap K₀ L (algebraMap V K₀ ϖ) := by
    simpa [p, sub_eq_zero] using hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN, hinj, hfin, hloc, hcomp⟩ :=
    GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local V hV L
  obtain ⟨hN₁, hIC₁, _, _⟩ := hCN

  have hy2 : (σ s) ^ 2 = algebraMap V₁ (FractionRing V₁) (ρ ϖ) := by
    rw [← map_pow, hs2, hcomp]
  have hint : IsIntegral V₁ (σ s) := by
    refine ⟨X ^ 2 - C (ρ ϖ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, hy2, Algebra.algebraMap_eq_smul_one]
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have ht2 : t ^ 2 = ρ ϖ := by
    apply IsFractionRing.injective V₁ (FractionRing V₁)
    rw [map_pow, ht, hy2]

  letI : Algebra V V₁ := ρ.toAlgebra
  haveI : Module.Finite V V₁ := hfin
  haveI : Algebra.IsIntegral V V₁ := Algebra.IsIntegral.of_finite V V₁
  have hϖ0 : ρ ϖ ≠ 0 := by
    intro h; apply hϖ.ne_zero; apply hinj; simpa using h
  have hϖnu : ¬ IsUnit (ρ ϖ) := fun h => hϖ.not_isUnit ((isUnit_map_iff ρ ϖ).mp h)
  have hnf : ¬ IsField V₁ := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hϖ0
    exact hϖnu (IsUnit.of_mul_eq_one _ hb)
  have hdvr : IsDiscreteValuationRing V₁ := by
    have h03 := (IsDiscreteValuationRing.TFAE V₁ hnf).out 0 3
    refine h03.mpr ⟨hIC₁, ⟨maximalIdeal V₁, ⟨?_, inferInstance⟩, ?_⟩⟩
    · intro h
      apply hϖnu
      by_contra hu
      have : ρ ϖ ∈ maximalIdeal V₁ := hu
      rw [h] at this
      exact hϖ0 ((Submodule.mem_bot _).mp this)
    · rintro P ⟨hP0, hPp⟩
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
      have hc : P.comap (algebraMap V V₁) ≠ ⊥ :=
        Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
      haveI : (P.comap (algebraMap V V₁)).IsPrime := Ideal.IsPrime.comap _
      have hm : (P.comap (algebraMap V V₁)).IsMaximal := IsPrime.to_maximal_ideal hc
      have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hm
      exact IsLocalRing.eq_maximalIdeal hPm
  exact ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, t, ⟨hN₁, hIC₁, by assumption, by assumption⟩,
    inferInstance, hinj, hloc, hfin, ht2⟩

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorTranslationBundleMonomial
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShiftGen

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_psi_gen [IsLocalRing R] (D : DegPre R) (χ : D.X) (u : Rˣ) (a : R) (h : PsiCoord D χ (u * a)) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
          (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj, le', hψ⟩ := h
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let cu : Γ(Spec (CommRingCat.of R), ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  let c : Γ(Spec (CommRingCat.of R), ⊤)ˣ := cu * (res le (e.s j))⁻¹
  refine ⟨DVR.scaleGen c e, DVR.scaleGen_isGen c e he, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val (DVR.scaleGen c e) (r ≫ jK R) z J = _ :=
    gen_trans (DVR.scaleGen_isGen c e he) (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val =
      gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (u * a)) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]
  have e₅ : gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) ((DVR.scaleGen c e).s j) =
      gm (r ≫ jK R) z ⊤ cu := by
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res (r ≫ jK R) z le_top m₂ c)
      (gm_res (r ≫ jK R) z le trivial (e.s j)).symm).trans ?_)
    rw [← map_mul]
    exact congrArg _ (inv_mul_cancel_right _ _)
  have e₆ : (gm (r ≫ jK R) z ⊤ cu).val = gs (r ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) :=
    (gs_unit _ z ⊤ trivial cu).symm
  rw [e₁, e₂, Units.val_mul, Units.val_mul]
  erw [e₃, e₄, e₅]
  rw [e₆, map_mul, gs_mul _ z ⊤ trivial]
  ring

theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    val (D.tau mu 0) (σ.left ≫ jFK (R := R) F) z J = 1 := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  have h0 : cP D T 0 = 1 := by simpa using cPoint_nsmul D T 0 0
  have h := tau_mul σ hJ hB 0 0 mu
  rw [h0, C.face, _root_.mul_one, add_zero] at h
  rw [tau_symm σ hJ]
  exact mul_eq_left.1 h.symm

theorem exists_integral_gen [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) (y : D.X) (N : ℕ) (v : Rˣ) (a : R)
    (h : PsiCoord D y (v * a)) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ uR : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (0 + N • y))
        (fun i => (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A y).left ≫ D.famφB 0 i)) (DegPre.deltaε N)), uR.IsGen ∧
      ∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N 0 y) (DegPre.deltaε N))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F N y 0) →
        ∀ (z : (DegPre.BF D F).left) (J : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
          (val u (𝟙 _) z J).val = gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) * (val uR (DegPre.prB D F).left z J).val := by
  obtain ⟨e, he, hv⟩ := exists_psi_gen D y v a h
  have c₁ : ∀ χ, D.P.A.hom ≫ (D.c χ).left = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by simp [SectionScalarValuation.cQ]
  have c₂ : D.P.A.hom ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have h0 : SectionScalarValuation.cQ D D.P.A 0 = 1 := by simpa using SectionScalarValuation.cQ_nsmul D D.P.A 0 0
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D N 0 y
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ e N)
      (GeneratorPullback.powGen D.P.L (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig N))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ he N) (powGen_isGen _ _ _ _ D.rig_gen N)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, h0, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  refine ⟨eB, heB, fun u hu hc z J hJ => ?_⟩
  have vp : ∀ {K : Type} [Fintype K] {Y : Scheme.{0}} {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (DegPre.BF D F).left ⟶ Y),
      val (GeneratorPullback.powGen D.P.L φ ε t N) r z J = val t r z J ^ N := fun t r => map_pow _ _ _
  have w₁ : ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R = (DegPre.prB D F).left ≫ D.P.A.hom :=
    (Category.assoc _ _ _).trans ((Over.w (fst (TF (R := R) F) D.P.A)).trans (Over.w (DegPre.prB D F)).symm)
  have w₂ : (toUnit (TK R)).left = jK R := (Category.comp_id _).symm.trans (Over.w (toUnit (TK R)))
  have G := (gen_fe (F := F) GlobalTheory.SemiRigid.globalFns N y 0).2 u hu hc _ (𝟙 _) z J hJ
  have v₁ := veB _ (DegPre.prB D F) z J hJ
  have p₁ := hv _ ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J hJ
  have p₂ : val D.rigK ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J =
      val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig ((DegPre.prB D F).left ≫ D.P.A.hom) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [← w₁]
    exact congrArg (fun q => val (K := PUnit) (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) D.rig
      (((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ q) z J) w₂
  rw [w₁] at p₁
  rw [Over.id_left, Category.id_comp, val_famMult _ hJ, val_tau_zero D hB F _ hJ, vp, vp, p₂, uVal_id, comp_cP,
    _root_.one_mul] at G
  rw [val_mul hJ, vp, vp] at v₁
  have q : gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a ^ N)) =
      gs ((DegPre.prB D F).left ≫ D.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) ^ N := by
    rw [gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]
  rw [G, v₁, q]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, p₁, th, cP, SectionScalarValuation.cQ]
  ring

theorem exists_integral_gen_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∃ (Nv : Fin m → ℕ) (uR : LB.Gen (LB.LinComb P.D.toPre.P.L (Sum.elim (P.D.toPre.famφB (0 + N • y)) (fun i => (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ≫ P.D.toPre.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen ∧ ∀ (u : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.deltaφ P.D.toPre (FractionRing (ChartRing k m d)) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ u (DegPre.zF P.D.toPre (FractionRing (ChartRing k m d))).left) (DegPre.famMult P.D.toPre (FractionRing (ChartRing k m d)) N y 0) → ∀ (z : (DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left) (J : ((DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ Nv i)) * (val uR (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J).val := by
  intro E _ _ _ H k _ _ m d t P gam hM y N _
  obtain ⟨v, n, -, hc⟩ := hM y
  have hT : lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A] =
      𝟙 P.D.toPre.P.A * SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y :=
    mul_comm (SectionScalarValuation.cQ P.D.toPre P.D.toPre.P.A y) (𝟙 P.D.toPre.P.A)
  rw [hT]
  obtain ⟨uR, h₁, h₂⟩ := exists_integral_gen P.D.toPre P.D.tau_bimult y N v _ hc (FractionRing (ChartRing k m d))
  refine ⟨fun i => n i * N, uR, h₁, fun u hu hcu z J hJ => ?_⟩
  rw [h₂ u hu hcu z J hJ, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.ShiftGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGenerator
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem exists_isFrame_top_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R] (F : (Sp R).Modules) {r : ℕ}
    (h : IsVB F r) : ∃ e : Fin r → Γ(F, ⊤), IsFrame e := by
  obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint R)
  have hU : U = ⊤ := by
    refine top_le_iff.1 fun p _ => ?_
    exact (IsLocalRing.specializes_closedPoint p).mem_open U.isOpen hx
  subst hU
  exact ⟨e, he⟩

theorem spMap_jK {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hgam : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) :
    spMap gam ≫ jK R = jK W ≫ spMap φ := by
  have e : gam.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext hgam
  simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem relDim {S' : Scheme.{0}} {g : ℕ} {G : Over S'} [GrpObj G] (hGg : SmoothOfRelativeDimension g G.hom)
    {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] (hG₁ : IsSemiAbelian G₁)
    {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left}
    (hα : IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α) : SmoothOfRelativeDimension g G₁.hom := by
  have := hG₁.smooth
  have h₁ : SmoothOfRelativeDimension g ((Over.pullback (jK R)).obj G₁).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hα.1 hGg
  exact GlobalTheory.SmoothRelDim.smoothOfRelativeDimension_of_generic R G₁ (FractionRing R)
    (algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) g h₁

theorem exists_integral_hodgeGen : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  intro S' g G _ _ hG hGg R _ _ _ _ _ G₁ _ _ hG₁ y α hα
  haveI := hG; haveI := hG₁
  haveI : SmoothOfRelativeDimension g G₁.hom := relDim hGg hG₁ hα
  obtain ⟨ε, hε⟩ := exists_isFrame_top_of_isLocalRing R (omega G₁) (isVB_omega G₁ g)
  have p₁ := isGrpPullback_pullback G₁ (jK R)
  have ha : IsFrame fun i => (omegaBase p₁).app ⊤ (pullbackSections (jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (jK R) hε le_top).map_iso _
  refine ⟨gen hα ha, GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hα ha, ?_⟩
  intro W _ _ _ hW φ gam hgam χ' hχ
  haveI : IsDiscreteValuationRing W := hW.1
  obtain ⟨ρ', ψ', hρ', hψ', e₁, e₂⟩ := GlobalTheory.T.traitPullback_semiAbelianModel_identification hG hG₁ hα φ gam hgam χ' hχ
  have pW := isGrpPullback_pullback G₁ (spMap φ)
  have ha' : IsFrame fun i => (omegaBase pW).app ⊤ (pullbackSections (spMap φ) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (spMap φ) hε le_top).map_iso _
  refine ⟨gen hψ' ha', GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hψ' ha', fun z J hJ => ?_⟩
  have q := isGrpPullback_pullback ((Over.pullback (jK R)).obj G₁) (spMap gam)
  have hA := q.comp hα
  have hq₁ := q.comp p₁
  have hb : IsFrame fun i => (omegaBase hq₁).app ⊤ (pullbackSections (spMap gam ≫ jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb _ hε le_top).map_iso _
  refine (GlobalTheory.T.hodge_frame_generator_value_pullback hα ha (spMap gam) q _ _ hA rfl rfl hb (fun i => ?_) z J hJ).trans
    (GlobalTheory.T.hodge_frame_generator_value_pullback hψ' ha' (jK W) hρ' _ _ hA hχ.symm e₁ hb (fun i => ?_) z J hJ).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp p₁ q hq₁ rfl rfl le_top le_top le_top (ε i)).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp pW hρ' hq₁ (spMap_jK φ gam hgam).symm e₂ le_top le_top le_top (ε i)).symm

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralShiftOfGeneratorUpToConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntegralShift

theorem trF_prB {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) :
    (DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R)).left =
      (DegPre.prB Q (FractionRing R)).left ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left := by
  rw [← Over.comp_left]
  congr 1
  have e₁ : DegPre.trF Q (FractionRing R) y ≫ DegPre.prB Q (FractionRing R) =
      DegPre.prB Q (FractionRing R) * (toUnit _ ≫ Q.c y) := lift_snd _ _
  have e₂ : (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]) = (toUnit Q.P.A ≫ Q.c y) * 𝟙 Q.P.A := rfl
  rw [e₁, e₂, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (DegPre.prB Q (FractionRing R) ≫ toUnit _) (toUnit _), mul_comm]

theorem sval_constFn_smul {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R) (s : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (constFn p ⊤ a • s) r z J =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval s r z J := by
  have hm := hJ.mem φ r
  refine (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans ((GlobalTheory.HeatMod.gs_constFn_eq_germConstHom p r z a).trans ?_)) rfl)
  exact (gs_eq (r ≫ p) z ⊤ trivial _).symm

theorem exists_shift_of_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) (N : ℕ) (c : R) (uR : LB.Gen (LB.LinComb Q.P.L (Sum.elim (Q.famφB (0 + N • y)) (fun i => (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left ≫ Q.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen → (∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) N y 0) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * (val uR (DegPre.prB Q (FractionRing R)).left z J).val) → ∃ (w : ∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), (Q.P.A.left.presheaf.stalk z)ˣ) (Sh : Q.SecB N 0 → Q.SecB N (0 + N • y)), ∀ x : Q.SecB N 0, (∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : Q.SecB N (0 + N • y), ShiftEq Q N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval x₁ X z J = gs (X ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval (Sh x) X z J := by
  intro R _ _ Q y N c uR huR H
  have ex : ∀ x : Q.SecB N 0, ∃ s₁ : Q.SecB N (0 + N • y),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Q.P.A.left) (z : Z) (J), Good Q.P.L z J →
        sval s₁ r z J = sval x (r ≫ (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left) z J *
          (val uR r z J).val := fun x => by
    obtain ⟨s₁, h⟩ := exists_sec Q.P.isLB (φ' := Q.famφB (0 + N • y)) (ε' := DegPre.famε N) (fun U _ h => by
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
      (pullMulSec x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left uR huR)
    exact ⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩
  choose Sh hSh using ex
  refine ⟨fun z J => val uR (𝟙 _) z J, Sh, fun x => ⟨fun z J hJ => ?_, constFn Q.P.A.hom ⊤ c • Sh x, ?_,
    fun Z X z J hJ => sval_constFn_smul _ _ _ _ _ hJ⟩⟩
  · rw [hSh x _ _ z J hJ, Category.id_comp]
  · intro u hu hc z J hJ
    rw [GlobalTheory.HeatMod.gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero, sval_constFn_smul _ _ _ _ _ hJ,
      hSh x _ _ z J hJ, H u hu hc z J hJ, trF_prB]
    ring

end GlobalTheory.IntegralShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicMod
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.exists_isometry_kerIs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n N hn hNn hC Z Z' h hrk hN hon
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  have hinj := GlobalTheory.T.injective_mod_of_surjective_mod_opposite D y n hn Z Z' h hrk hon
  obtain ⟨σ, hσZ', hσid, hσy, hσN⟩ := GlobalTheory.T.exists_linear_section_opposite_congr_mod D y n N hn hNn Z Z' h hN hon
  obtain ⟨w, hw⟩ := exists_adjoint D σ
  obtain ⟨t, ht, hiso, hdvd⟩ := GlobalTheory.T.exists_isotropic_shear_of_adjoint D y n N hn hNn hC Z Z' h σ w hσZ' hσid hσy hσN hw hinj
  have ht' : ∀ z : Z, t z - z ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hze⟩ := ht z
    rw [hze, add_sub_cancel_left]
    exact (perp D Z').nsmul_mem he N
  have hker := GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul D y n hn Z Z' h hon t ht' hiso hdvd
  obtain ⟨g, hg, hgN, hgt⟩ := GlobalTheory.T.exists_isometry_extending_isotropic_shear D N hN0 Z Z' h t ht hiso
  refine ⟨equivOfIsometry D g hg, hg, hgN, fun a => ?_⟩
  simp only [equivOfIsometry_apply]
  rw [hker (g a)]
  constructor
  · rintro ⟨b, hb, e, he⟩
    set G := equivOfIsometry D g hg
    have hG : ∀ x, G x = g x := fun x => rfl
    refine ⟨G.symm b, fun z hz => ?_, G.symm e, ?_⟩
    · have := hb (t ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩
      rw [← hgt ⟨z, hz⟩, ← G.apply_symm_apply b, hG, hg] at this
      exact this
    · apply G.injective
      rw [map_add, map_nsmul, G.apply_symm_apply, G.apply_symm_apply, hG, he]
  · rintro ⟨b, hb, e, rfl⟩
    refine ⟨g b, ?_, g e, by rw [map_add, map_nsmul]⟩
    rintro _ ⟨z, rfl⟩
    rw [← hgt z, hg]
    exact hb z z.2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionDescendedSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_descended_semiAbelian : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ M : LB G.left, M.IsLB ∧ LBIso (M.pull e) tF.PP.L := by
  first | exact @GlobalTheory.DescLBExt.exists_lb_extension | exact GlobalTheory.DescLBExt.exists_lb_extension | (intros; apply GlobalTheory.DescLBExt.exists_lb_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  first | exact @GlobalTheory.LBObs.exists_lift_of_lam_iso_pull | exact GlobalTheory.LBObs.exists_lift_of_lam_iso_pull | (intros; apply GlobalTheory.LBObs.exists_lift_of_lam_iso_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_opens_R_le_O : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧
    ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  intro X₁
  obtain ⟨s, hs⟩ := X₁.S.fg
  refine ⟨⟨⋂ x ∈ s, {z | x ∈ X₁.M.O z}, isOpen_biInter_finset fun x _ => X₁.M.isOpen_setOf_mem_O x⟩,
    ⟨genericPoint X₁.M.Z, ?_⟩, ?_⟩
  · show genericPoint X₁.M.Z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z}
    refine Set.mem_iInter₂.2 fun x _ => ?_
    show x ∈ X₁.M.O (genericPoint X₁.M.Z)
    rw [RatModel.O_genericPoint]
    exact Algebra.mem_top
  · intro z hz
    have hz' : z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z} := hz
    rw [← hs]
    exact Algebra.adjoin_le fun x hx => Set.mem_iInter₂.1 hz' x hx

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSectionNonvanishingClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_section_nonvanishing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ θ : U'.LG.L.Sec, (∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ) → ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  first | exact @GlobalTheory.Mum.exists_open_secNz_closedFibre | exact GlobalTheory.Mum.exists_open_secNz_closedFibre | (intros; apply GlobalTheory.Mum.exists_open_secNz_closedFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  first | exact @GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | exact GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | (intros; apply GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB <;> assumption)
end


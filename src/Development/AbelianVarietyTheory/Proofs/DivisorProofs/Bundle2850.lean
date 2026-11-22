import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricRestrictionVanishingLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

variable (B') in

abbrev sw2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
  ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]

theorem lift_comp_squareFactorIdentity_eq_lift {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 0 = (lift a b).left := by
  show (lift a b).left ≫ (lift (fst B' B') (snd B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem lift_comp_squareFactorSwap_eq_lift_swap {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 1 = (lift b a).left := by
  show (lift a b).left ≫ (lift (snd B' B') (fst B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem formEq_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => sw2 B' k ≫ β₂) (flatε lamε ![1, -1]) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  intro U _ h
  rw [GlobalTheory.LamBiext.prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
  show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
    (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
  rw [β₂_lift, β₂_lift, GlobalTheory.LamBiext.prod_lam, GlobalTheory.LamBiext.prod_lam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_gen_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {M : LB B.left} (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M) (fun k => sw2 B' k ≫ β₂) ![1, -1]), t.IsGen ∧
      ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι), Good M z J →
        val (L := abelian₂ B M) t r z (ind B J) = 1 := by
  obtain ⟨g, hg, hv⟩ := exists_gen hM (formEq_sw hβ hsq) (LB.oneGen M) (oneGen_isGen _)
  refine ⟨GlobalTheory.LamBiext.nest M (lamφ B) lamε (fun k => sw2 B' k ≫ β₂) ![1, -1] g, nest_isGen hg,
    fun r z J hJ => ?_⟩
  refine (val_nest hg r (good_ind hJ) hJ).trans ?_
  simp only [adj_ind hM hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (hv _ r z J hJ).trans (val_one r)

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.Mum.Two

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

theorem isoVal_swap (hB' : IsAbelianScheme B') {M : LB B.left} {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB)
    {f : S' ⟶ S} {f₁ : S' ⟶ S₁} {β : B'.left ⟶ B.left} {β₁ : B'.left ⟶ B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (hβ : IsGrpPullback B' B f β) (hβ₁ : IsGrpPullback B' B₁ f₁ β₁) (hsq : IsSquare β β₂) (hsq₁ : IsSquare β₁ β₂')
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) (hw : w.IsGen) {T : Over S'} (x y : T ⟶ B')
    (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.ι) (J' : (T.left ⟶ B.left) → M.ι) (hJ : Good M₁ z J)
    (hJ' : Good M z J') :
    isoVal w (lift x y).left z J J' = isoVal w (lift y x).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have hL' : ((abelian₂ B M).pull β₂).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hM _ _) _ _
  obtain ⟨t, ht, hvt⟩ := exists_gen_sw hβ₁ hsq₁ hM₁
  obtain ⟨g, hg, hvg⟩ := exists_gen_sw hβ hsq hM
  let c := chartPullLinComb (abelian₂ B M) β₂ (sw2 B') (fun k => sw2 B' k ≫ β₂) ![1, -1] (𝟙 _)
    (fun k => (Category.id_comp _).symm)
  have ha : (cGen c g).IsGen := cGen_isGen c hg
  have good_P : ∀ {Z : Scheme.{0}} {z₀ : Z} {J₀ : (Z ⟶ B.left) → M.ι}, Good M z₀ J₀ →
      Good ((abelian₂ B M).pull β₂) z₀ (fun q _ => ind B J₀ (q ≫ β₂)) :=
    fun hJ₀ q => mem_pull.2 (good_ind hJ₀ (q ≫ β₂))
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B.left) → M.ι), Good M z₀ J₀ →
      val (cGen c g) r z₀ (fun q _ => ind B J₀ (q ≫ β₂)) = 1 := by
    intro Z r z₀ J₀ hJ₀
    rw [← hvg r z₀ J₀ hJ₀, val_of g r z₀ (ind B J₀) (fun k => ind B J₀ ((r ≫ sw2 B' k) ≫ β₂))
      (fun k => by rw [Category.assoc])]
    exact gm_res r z₀ _ ((good_P hJ₀).mem _ r) _
  have gw_iso : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (φ : (G2 B').left ⟶ (G2 B').left) (z₀ : Z)
      (J₀ : (Z ⟶ B₁.left) → M₁.ι) (J₀' : (Z ⟶ B.left) → M.ι),
      gw w (r ≫ φ) z₀ (ind B₁ J₀ (r ≫ φ ≫ β₂')) (fun _ => ind B J₀' ((r ≫ φ) ≫ β₂)) =
        isoVal w (r ≫ φ) z₀ J₀ J₀' := by
    intro Z r φ z₀ J₀ J₀'
    have e₁ : ind B₁ J₀ (r ≫ φ ≫ β₂') = fun I => J₀ ((r ≫ φ) ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left) :=
      funext fun I => congrArg J₀ (by simp only [Category.assoc])
    have e₂ : ind B J₀' ((r ≫ φ) ≫ β₂) = fun I => J₀' ((r ≫ φ) ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
      funext fun I => congrArg J₀' (by simp only [Category.assoc])
    rw [e₁, e₂]; rfl
  have Fp : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B₁.left) → M₁.ι)
      (J₀' : (Z ⟶ B.left) → M.ι),
      pw w (sw2 B') ![1, -1] r z₀ (fun k => ind B₁ J₀ (r ≫ sw2 B' k ≫ β₂'))
        (fun k => (fun (q : Z ⟶ (G2 B').left) (_ : PUnit) => ind B J₀' (q ≫ β₂)) (r ≫ sw2 B' k)) =
        isoVal w (r ≫ sw2 B' 0) z₀ J₀ J₀' * (isoVal w (r ≫ sw2 B' 1) z₀ J₀ J₀')⁻¹ := by
    intro Z r z₀ J₀ J₀'
    unfold pw
    rw [Fin.prod_univ_two]
    rw [gw_iso r (sw2 B' 0) z₀ J₀ J₀', gw_iso r (sw2 B' 1) z₀ J₀ J₀']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg]
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have E := rigid_pw w hw hL hL' (sw2 B') ![1, -1] ha ht _ _ he2
    (surj_comp (surj_snd hG hB' _) (hG _ _ hB').2) (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM₁ y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      refine ⟨ind B₁ J₁, fun q _ => ind B J₁' (q ≫ β₂), good_ind hJ₁, good_P hJ₁', ?_⟩
      rw [hvt _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, mul_inv_cancel, _root_.mul_one])
    T.left (lift x y).left z (ind B₁ J) (fun q _ => ind B J' (q ≫ β₂)) (good_ind hJ) (good_P hJ')
  rw [hvt _ z J hJ, Fp, Fa _ z J' hJ', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, _root_.mul_one] at E
  exact mul_inv_eq_one.1 E.symm

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart

theorem periodConst_symm : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁ hfin hloc hκ hpb hpb' hsq hsq'
    x hx w₁ q hgen hper hnorm a b
  have hAb : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback D.toPre.P.isAb hpb
  obtain ⟨κK, hκK⟩ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ := by
    have hi : Function.Injective ((algebraMap V₁ (FractionRing V₁)).comp f₁) :=
      (IsFractionRing.injective V₁ (FractionRing V₁)).comp hf₁
    obtain ⟨g, eg⟩ : ∃ g : FractionRing V →+* FractionRing V₁,
        g.comp (algebraMap V (FractionRing V)) = (algebraMap V₁ (FractionRing V₁)).comp f₁ :=
      ⟨IsLocalization.lift (M := nonZeroDivisors V) (g := (algebraMap V₁ (FractionRing V₁)).comp f₁) fun y =>
        IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
    refine ⟨spMap g, ?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eg]
  let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  have h₁ := hper κK hκK a b z J J' hJ hJ'
  have h₂ := hper κK hκK b a z J J' hJ hJ'
  rw [GlobalTheory.Mum.RosatiSymmetry.val_tau_symm D.toPre hJ' κK,
    val_corr hJ (corr_of_val L.T.M.isLB (L.T.τ₀_symm ((n : ℤ) • b) ((n : ℤ) • a))),
    GlobalTheory.TChart.SwapIso.isoVal_swap hAb D.toPre.P.isLB L.T.M.isLB hpb hpb' hsq hsq' w₁ hgen
      (toUnit (TK V₁) ≫ x b) (toUnit (TK V₁) ≫ x a) z J J' hJ hJ'] at h₂
  have hq := mul_right_cancel (h₁.symm.trans h₂)
  have hs : Subsingleton (TK V₁).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing V₁)))
  have eu : unitOn (q a b) = unitOn (q b a) := unit_ext fun y _ => by rw [Subsingleton.elim y z]; exact hq
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv).1 eu

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSections
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

open GlobalTheory.VB GlobalTheory.VMetric GlobalTheory.CurveDens GlobalTheory.CxPts

section TwoFlags

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {V : X.Modules}

def lineQuot (fl : Vert.Flag V 2) : V ⟶ fl.gr 1 :=
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  inv (fl.ι (Fin.succ 1)) ≫ fl.π 1

theorem ι_lineQuot (fl : Vert.Flag V 2) : fl.ι (Fin.succ 1) ≫ lineQuot fl = fl.π 1 := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact IsIso.hom_inv_id_assoc _ _

theorem line_lineQuot (fl : Vert.Flag V 2) : fl.ι 1 ≫ lineQuot fl = 0 := by
  have e : fl.step 1 ≫ fl.ι (Fin.succ 1) = fl.ι 1 := fl.step_ι 1
  rw [← e]
  exact (Category.assoc _ _ _).trans ((congrArg (fl.step 1 ≫ ·) (ι_lineQuot fl)).trans
    (Limits.cokernel.condition _))

theorem shortExact_lineQuot (fl : Vert.Flag V 2) :
    (ShortComplex.mk (fl.ι 1) (lineQuot fl) (line_lineQuot fl)).ShortExact := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl 1)
    (S₂ := ShortComplex.mk (fl.ι 1) (lineQuot fl) (line_lineQuot fl)) (Iso.refl _)
    (asIso (fl.ι (Fin.succ 1))) (Iso.refl _) ((Category.id_comp _).trans (fl.step_ι 1).symm)
    ((ι_lineQuot fl).trans (Category.comp_id _).symm)) (stepSeq_shortExact fl 1)

variable {h : VMetric p V 2} (H : h.IsCInf)

theorem isometric_grLB_zero (fl : Vert.Flag V 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (grLB fl 0 H) := by
  have hS₀ := stepSeq_shortExact fl 0
  have i₂ : IsIso (stepSeq fl 0).g := hS₀.isIso_g_iff.2 (isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) (H.restrict _ _)
    (H.grMet fl 0) (asIso (stepSeq fl 0).g) ((isIsometry_iff _).2 (VMetric.ext
      (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
        (fl.isVB (Fin.castSucc 0)) _)))

theorem isometric_grLB_one (fl : Vert.Flag V 2) :
    (VMetric.det (IsCInf.quot (S := .mk _ _ (line_lineQuot fl)) (r := 1) (s := 1) (shortExact_lineQuot fl)
      (fl.isVB 1) (fl.isVB_gr 1) H)).Isometric (grLB fl 1 H) := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact (isometric_detQuot_and_bcInt_eq_of_iso k X p (stepSeq fl 1) (.mk _ _ (line_lineQuot fl)) 1 1
    (h.stepMet fl 1) h (H.restrict _ _) H (stepSeq_shortExact fl 1) (shortExact_lineQuot fl)
    (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) (fl.isVB 1) (fl.isVB_gr 1) (Iso.refl _)
    (asIso (fl.ι (Fin.succ 1))) ((Category.id_comp _).trans (fl.step_ι 1).symm)
    fun σ U s t y hy => ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm).1.symm

theorem sameStep_of_eq_zero (fl fl' : Vert.Flag V 2) (hs : fl.ι 1 ≫ lineQuot fl' = 0) (j : Fin 3) :
    fl.SameStep fl' j := by
  by_cases he : j = 0 ∨ j = Fin.last 2
  · exact AdjFlag.sameStep_of_end he
  obtain rfl : j = 1 := by
    fin_cases j
    · exact absurd (.inl rfl) he
    · rfl
    · exact absurd (.inr rfl) he
  exact SameLine.eq_line X V _ _ _ _ _ _ _ _ _ _ (shortExact_lineQuot fl') (shortExact_lineQuot fl)
    (fl'.isVB_gr 1) (fl.isVB_gr 1) hs

theorem exists_ratSec_two_flags [IsIntegral X] (fl fl' : Vert.Flag V 2) (hs : fl.ι 1 ≫ lineQuot fl' ≠ 0)
    {S M Q : HermLB p} (eS : (grLB fl 0 H).Isometric S) (eM : (grLB fl' 0 H).Isometric M)
    (eQ : (grLB fl' 1 H).Isometric Q) :
    ∃ (r : (S.dual.tens Q).B.ι → X.functionFieldˣ) (hr : IsRatSec (S.dual.tens Q).B r),
      (∀ z ∈ ((S.dual.tens Q).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          (S.restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ, IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v ∧
        ∀ y ∈ offSupp p σ ((S.dual.tens Q).div hr), v y < 1 ∧
          logNorm ((S.dual.tens Q).φ σ) r y = Real.log (1 - v y) / 2 := by
  have hS := shortExact_lineQuot fl'
  have hL := fl'.isVB 1
  have hL' := fl.isVB 1
  have hQ := fl'.isVB_gr 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have HQ := IsCInf.quot (S := .mk _ _ (line_lineQuot fl')) (r := 1) (s := 1) hS hL hQ H
  have aS := (isometric_grLB_zero H fl).trans eS
  have aM := (isometric_grLB_zero H fl').trans eM
  have aQ := (isometric_grLB_one H fl').trans eQ
  obtain ⟨r₀, hr₀, hv, hn⟩ := LineHomSec.exists_ratSec k X p _ _ _ _ (H.restrict hl' hL') HQ _ hs
  obtain ⟨r, hr, hd, he⟩ := (aS.dual.tens aQ).exists_isRatSec hr₀
  refine ⟨r, hr, fun z hz Z i _ hi => ?_, fun σ => ?_⟩
  · rw [hd] at hz
    have e := isometric_restr_of_vanishesAt k X p V _ _ _ _ _ (line_lineQuot fl') _ hS hQ hL hL' hl hl' h H
      Z i (hi ▸ hv z hz)
    exact ((aS.pull i rfl).symm.trans e.symm).trans (aM.pull i rfl)
  · obtain ⟨v, hc, -, -⟩ := exists_isCosSq k X p σ V _ _ _ (h.met σ) _ _ (H σ) hl hl' hL hL'
    refine ⟨v, hc.symm, fun y hy => ?_⟩
    rw [hd] at hy
    obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
    obtain ⟨n₁, n₂⟩ := hn σ y hy U t' ht' hU
    have e := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hc ht ht' hU
    have := (div_pos n₁ (AdjFlag.form_frame_pos ((h.met σ).restrict hl' hL') ht' hU)).trans_eq e
    exact ⟨by linarith, (he σ hy).trans (n₂.trans (congrArg (Real.log · / 2) e))⟩

end TwoFlags

theorem isIso_of_sameStep {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (n : ℕ) (flB : Vert.Flag E n)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hF : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) (fun _ => fl))
    (hs : ∀ j, fl.SameStep (flB.pull π) j) : IsIso π := by
  have key (T : Scheme.{0}) (g₁ g₂ : T ⟶ Y) (e : g₁ ≫ π = g₂ ≫ π) : g₁ = g₂ := by
    have car (g' : T ⟶ Y) (w : g' ≫ π = g₂ ≫ π) (i : Fin (n + 1)) :
        ∃ e : (Scheme.Modules.pullback g').obj (fl.F i) ≅ (flB.pull (g₂ ≫ π)).F i,
          e.hom ≫ (flB.pull (g₂ ≫ π)).ι i = (Scheme.Modules.pullback g').map (fl.ι i) ≫
            (Scheme.Modules.pullbackComp g' π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
      obtain ⟨a, ha⟩ := hs i
      refine ⟨(Scheme.Modules.pullback g').mapIso a ≪≫
        (Scheme.Modules.pullbackComp g' π ≪≫ Scheme.Modules.pullbackCongr w).app (flB.F i), ?_⟩
      have nat := (Scheme.Modules.pullbackComp g' π ≪≫ Scheme.Modules.pullbackCongr w).hom.naturality (flB.ι i)
      rw [← ha, Functor.map_comp, Category.assoc]
      exact (Category.assoc _ _ _).trans (congrArg ((Scheme.Modules.pullback g').map a.hom ≫ ·) nat.symm)
    exact (hF T (g₂ ≫ π) fun _ => flB.pull (g₂ ≫ π)).unique ⟨e, fun _ => car g₁ e⟩ ⟨rfl, fun _ => car g₂ rfl⟩
  obtain ⟨s, ⟨hσ, -⟩, -⟩ := hF B (𝟙 B) fun _ => flB.pull (𝟙 B)
  exact ⟨s, key Y _ _ (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp]), hσ⟩

theorem exists_ratSec_fam5 : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q),
    ∃ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2 := by
  intro k _ B Y _ _ q p d hB hY _ π w E h H flB fl hF A
  have hs : fl.ι 1 ≫ lineQuot (flB.pull π) ≠ 0 := fun hs => by
    have := isIso_of_sameStep π E 2 flB fl hF (sameStep_of_eq_zero fl _ hs)
    have e := π.homeomorph.isHomeomorph.topologicalKrullDim_eq _
    rw [hB.dim_eq, hY.dim_eq] at e
    have e' : d + 1 + 1 = d + 1 := by exact_mod_cast e
    omega
  obtain ⟨r, hr, h₁, h₂⟩ := exists_ratSec_two_flags (H.pull π w) fl (flB.pull π) hs (.refl _)
    (isometric_grLB_pull k B Y q p E 2 h H flB π w 0) (isometric_grLB_pull k B Y q p E 2 h H flB π w 1)
  exact ⟨r, hr, fun z hz Z i _ _ hi => h₁ z hz Z i hi, h₂⟩

end GlobalTheory.CovTest.SwapLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSectionsStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

private theorem isIso_of_sameStep {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (n : ℕ) (flB : Vert.Flag E n)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hF : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) (fun _ => fl))
    (hs : ∀ i, fl.SameStep (flB.pull π) i) : IsIso π := by
  have key (T : Scheme.{0}) (g : T ⟶ B) (a : T ⟶ Y) (w : a ≫ π = g) (i : Fin (n + 1)) :
      ∃ e : (Scheme.Modules.pullback a).obj (fl.F i) ≅ (flB.pull g).F i,
        e.hom ≫ (flB.pull g).ι i = (Scheme.Modules.pullback a).map (fl.ι i) ≫
          (Scheme.Modules.pullbackComp a π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
    obtain ⟨e, he⟩ := hs i
    refine ⟨(Scheme.Modules.pullback a).mapIso e ≪≫ (Scheme.Modules.pullbackComp a π).app (flB.F i) ≪≫
      (Scheme.Modules.pullbackCongr w).app (flB.F i), ?_⟩
    have n₁ := (Scheme.Modules.pullbackComp a π).hom.naturality (flB.ι i)
    have n₂ := (Scheme.Modules.pullbackCongr w).hom.naturality (flB.ι i)
    rw [← he, Functor.map_comp, Category.assoc]
    refine (Category.assoc _ _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ ((congrArg (· ≫ (Scheme.Modules.pullbackCongr w).hom.app E) n₁).symm.trans (Category.assoc _ _ _))
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg _ n₂.symm
  have : Mono π := ⟨fun {T} a b hab => (hF T (b ≫ π) fun _ => flB.pull _).unique
    ⟨hab, fun _ i => key T _ a hab i⟩ ⟨rfl, fun _ i => key T _ b rfl i⟩⟩
  obtain ⟨s, ⟨hs, -⟩, -⟩ := hF B (𝟙 B) fun _ => flB.pull _
  have : IsSplitEpi π := ⟨⟨⟨s, hs⟩⟩⟩
  exact isIso_of_mono_of_isSplitEpi π

private theorem isometric_first {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules}
    {h : VMetric p E 2} (H : h.IsCInf) (fl : Vert.Flag E 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (VMetric.grLB fl 0 H) := by
  have H₀ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have hS₀ := VMetric.stepSeq_shortExact fl 0
  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS₀.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact T.det_metric_isometric_of_isometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₀
      (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
        (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
          (fl.isVB (Fin.castSucc 0)) _)))

private theorem exists_ratSec_lines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {V L Q L' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V}
    (hS : (ShortComplex.mk l m w).ShortExact) (hL : VB.IsVB L 1) (hQ : VB.IsVB Q 1) (hL' : VB.IsVB L' 1)
    (hl : VB.IsSubbundle l) (hl' : VB.IsSubbundle l') {h : VMetric p V (1 + 1)} (H : h.IsCInf) (hs : l' ≫ m ≠ 0)
    {S M N : HermLB p} (e₂ : (VMetric.det (H.restrict hl' hL')).Isometric S)
    (e₃ : (VMetric.det (H.restrict hl hL)).Isometric M)
    (e₁ : (VMetric.det (VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H)).Isometric N) :
    ∃ (r : (S.dual.tens N).B.ι → X.functionFieldˣ) (hr : IsRatSec (S.dual.tens N).B r),
      (∀ z ∈ ((S.dual.tens N).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          (S.restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq (h.met σ) l' l v ∧
        ∀ y ∈ offSupp p σ ((S.dual.tens N).div hr), v y < 1 ∧
          logNorm ((S.dual.tens N).φ σ) r y = Real.log (1 - v y) / 2 := by
  have HQ := VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H
  obtain ⟨r, hr, hv, hn⟩ := T.exists_ratSec_det_dual_tensor_support k X p L' Q (h.restrict hl' hL')
    (VMetric.quot (S := .mk l m w) h hS hL hQ) (H.restrict hl' hL') HQ (l' ≫ m) hs
  obtain ⟨r', hr', hd, hN⟩ := (e₂.dual.tens e₁).exists_isRatSec hr
  refine ⟨r', hr', ?_, fun σ => ?_⟩
  · rw [hd]
    rintro z hz Z i _ rfl
    exact ((e₂.pull i rfl).symm.trans
      (T.det_metric_restriction_vanishing_locus k X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z i (hv _ hz)).symm).trans (e₃.pull i rfl)
  · obtain ⟨v, hc, -, -⟩ := T.exists_continuous_cosSq_angle_function k X p σ V L L' _ (h.met σ) l l' (H σ) hl hl' hL hL'
    refine ⟨v, hc.symm, ?_⟩
    rw [hd]
    intro y hy
    obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
    obtain ⟨n₁, n₂⟩ := hn σ y hy U t' ht' hU
    have e := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hc ht ht' hU
    have := div_pos n₁ (AdjFlag.form_frame_pos ((h.met σ).restrict hl' hL') ht' hU)
    have h₁ : 0 < 1 - v y := this.trans_eq e
    exact ⟨by linarith, (hN σ hy).trans (n₂.trans (congrArg (Real.log · / 2) e))⟩

private theorem isometric_second {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules}
    {h : VMetric p E (1 + 1)} (H : h.IsCInf) (fl : Vert.Flag E 2) {Q : X.Modules} {m : E ⟶ Q} {w : fl.ι 1 ≫ m = 0}
    (hS : (ShortComplex.mk (fl.ι 1) m w).ShortExact) (hL : VB.IsVB (fl.F 1) 1) (hQ : VB.IsVB Q 1) :
    (VMetric.det (VMetric.IsCInf.quot (S := .mk (fl.ι 1) m w) hS hL hQ H)).Isometric (VMetric.grLB fl 1 H) := by
  have i₁ : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  have H₁ : (h.stepMet fl 1).IsCInf := H.restrict _ _
  have hI : (h.stepMet fl 1).IsIsometry h (asIso (fl.ι (Fin.succ 1))) := fun σ V s t y hy =>
    ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  have he : (Iso.refl (fl.F 1)).hom ≫ fl.ι 1 = (VMetric.stepSeq fl 1).f ≫ (asIso (fl.ι (Fin.succ 1))).hom :=
    (Category.id_comp _).trans (fl.step_ι 1).symm
  have e := T.det_metric_shortExact_iso_isometric k X p (VMetric.stepSeq fl 1) (.mk (fl.ι 1) m w) 1 1 (h.stepMet fl 1) h H₁ H
      (VMetric.stepSeq_shortExact fl 1) hS (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) hL hQ
      (Iso.refl (fl.F 1)) (asIso (fl.ι (Fin.succ 1))) he hI
  exact e.1.symm

private theorem exists_ratSec_flags {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {V : X.Modules} {h : VMetric p V 2} (H : h.IsCInf) (fl fl' : Vert.Flag V 2) (hne : ¬ fl.SameStep fl' 1)
    {M Q : HermLB p} (hM : (VMetric.grLB fl' 0 H).Isometric M) (hQ : (VMetric.grLB fl' 1 H).Isometric Q) :
    ∃ (r : ((VMetric.grLB fl 0 H).dual.tens Q).B.ι → X.functionFieldˣ)
      (hr : IsRatSec ((VMetric.grLB fl 0 H).dual.tens Q).B r),
      (∀ z ∈ (((VMetric.grLB fl 0 H).dual.tens Q).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          ((VMetric.grLB fl 0 H).restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v ∧
        ∀ y ∈ offSupp p σ (((VMetric.grLB fl 0 H).dual.tens Q).div hr), v y < 1 ∧
          logNorm (((VMetric.grLB fl 0 H).dual.tens Q).φ σ) r y = Real.log (1 - v y) / 2 := by
  have hL : VB.IsVB (fl'.F 1) 1 := fl'.isVB 1
  have hL' : VB.IsVB (fl.F 1) 1 := fl.isVB 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have hC : VB.IsVB (Limits.cokernel (fl'.ι 1)) 1 := fl'.isVB_cokernel 1
  have hC' : VB.IsVB (Limits.cokernel (fl.ι 1)) 1 := fl.isVB_cokernel 1
  have hS : (ShortComplex.mk (fl'.ι 1) _ (Limits.cokernel.condition (fl'.ι 1))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hS' : (ShortComplex.mk (fl.ι 1) _ (Limits.cokernel.condition (fl.ι 1))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hs : fl.ι 1 ≫ Limits.cokernel.π (fl'.ι 1) ≠ 0 := fun hs =>
    hne (T.iso_of_equal_sublines_shortExact X V _ _ _ _ _ _ _ _ _ _ hS hS' hC hC' hs)
  exact exists_ratSec_lines hS hL hC hL' hl hl' (h := h) H hs (isometric_first H fl)
    ((isometric_first H fl').trans hM) ((isometric_second H fl' hS hL hC).trans hQ)

theorem _root_.GlobalTheory.T.rank_two_flag_rational_sections : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q),
    ∃ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2 := by
  intro k _ B Y _ _ q p d hB hY _ π w E h H flB fl hF A
  have hne : ¬ fl.SameStep (flB.pull π) 1 := fun h₁ => by
    have : IsIso π := isIso_of_sameStep π E 2 flB fl hF fun i => by
      fin_cases i
      exacts [AdjFlag.sameStep_of_end (Or.inl rfl), h₁, AdjFlag.sameStep_of_end (Or.inr rfl)]
    have e := IsHomeomorph.topologicalKrullDim_eq _ π.homeomorph.isHomeomorph
    rw [hB.dim_eq, hY.dim_eq] at e
    have e' : d + 1 + 1 = d + 1 := by exact_mod_cast e
    omega
  obtain ⟨r, hr, h₁, h₂⟩ := exists_ratSec_flags (H.pull π w) fl (flB.pull π) hne
    (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 0) (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 1)
  exact ⟨r, hr, fun z hz Z i _ _ hi => h₁ z hz Z i hi, h₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumericalStatement
section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_point_of_weight_numerical : WtPt → NumPt → SumPt := by
  first | exact @GlobalTheory.RefSum.sumPt_of_sizes | exact GlobalTheory.RefSum.sumPt_of_sizes | (intros; apply GlobalTheory.RefSum.sumPt_of_sizes <;> assumption)
end


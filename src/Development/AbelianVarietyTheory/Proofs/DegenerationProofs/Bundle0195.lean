import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSmulTopOfForallMem

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

theorem hyps (h : Laws) (h₂ : Laws2) :
    LL ∧ TwistBCSpanStatement ∧ TWM.VRatioGtStatement ∧ TWStatement ∧ UUStatement := by
  obtain ⟨h₃, h₄, h₅, -⟩ := GlobalTheory.furtherLaws_of_laws h GlobalTheory.twistBaseChange
  have t := twistBCSpan_of GlobalTheory.twistBaseChange
  have r : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  exact ⟨⟨h, h₂, h₃, h₄, h₅⟩, t, r, TWM.tw_of h.globalFns t r, GlobalTheory.UnitBallFree.main h.globalFns GlobalTheory.twistBaseChange⟩

theorem exists_rat_log (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ r : ℚ, Real.log ‖x‖ = r * Real.log p := by
  have hi : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have e : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨1 / (minpoly ℚ_[p] x).natDegree * (-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ), ?_⟩
  rw [e, Real.log_rpow (norm_pos_iff.2 h0), Padic.norm_eq_zpow_neg_valuation h0, Real.log_zpow]
  push_cast
  ring

theorem exists_addVal (p : ℕ) [Fact p.Prime] {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ (x : PadicAlgCl p) (r : ℚ),
      v x = (r : WithTop ℚ) ↔ ‖x‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  classical
  have hl : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have key : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ r : ℚ, Real.log ‖x‖ = Real.log ‖π‖ * r := fun x hx => by
    obtain ⟨a, ha⟩ := exists_rat_log p hx
    obtain ⟨b, hb⟩ := exists_rat_log p (norm_pos_iff.1 h0)
    have b0 : (b : ℝ) ≠ 0 := fun h => hl.ne (by rw [hb, h, zero_mul])
    refine ⟨a / b, ?_⟩
    rw [ha, hb]; push_cast; field_simp
  choose! f hf using key
  have inj : ∀ a b : ℚ, Real.log ‖π‖ * a = Real.log ‖π‖ * b → a = b := fun a b h => by
    exact_mod_cast mul_left_cancel₀ hl.ne h
  have mono : ∀ x y, x ≠ 0 → y ≠ 0 → ‖x‖ ≤ ‖y‖ → f y ≤ f x := fun x y hx hy h => by
    have := Real.log_le_log (norm_pos_iff.2 hx) h
    rw [hf x hx, hf y hy] at this
    exact_mod_cast (mul_le_mul_left_of_neg hl).1 this
  refine ⟨AddValuation.of (fun x => if x = 0 then ⊤ else (f x : WithTop ℚ)) (if_pos rfl) ?_ ?_ ?_, fun x r => ?_⟩
  · rw [if_neg one_ne_zero, inj (f 1) 0 (by rw [← hf 1 one_ne_zero]; simp)]; rfl
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hs : x + y = 0
    · simp [hs]
    simp only [if_neg hx, if_neg hy, if_neg hs, min_le_iff, WithTop.coe_le_coe]
    exact (le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y)).imp (mono _ _ hs hx) (mono _ _ hs hy)
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hs := mul_ne_zero hx hy
    simp only [if_neg hx, if_neg hy, if_neg hs, ← WithTop.coe_add]
    refine congrArg _ (inj _ _ ?_)
    rw [← hf _ hs, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), hf x hx, hf y hy]
    push_cast; ring
  · rw [AddValuation.of_apply, neg_mul, neg_neg]
    by_cases hx : x = 0
    · simp [hx, (Real.exp_pos _).ne]
    rw [if_neg hx, WithTop.coe_eq_coe]
    refine ⟨fun h => by rw [← h, ← hf x hx, Real.exp_log (norm_pos_iff.2 hx)], fun h => inj _ _ ?_⟩
    rw [← hf x hx, h, Real.log_exp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem charZero : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

theorem isUnit_level (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) : IsUnit ((S.r * S.N : ℕ) : u.V) := by
  obtain ⟨b, hb⟩ := S.unit.exists_right_inv
  obtain ⟨c, hc⟩ := (u.norm_le (u.yK (algebraMap o S.R b))).1 (by
    rw [← RingHom.comp_apply, u.fac]; exact h b)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  have := congrArg (fun a => u.yK (algebraMap o S.R a)) hb
  simp only [map_mul, map_natCast, map_one] at this ⊢
  rw [hc]; simpa using this

theorem exists_val : ∃ (ϖ : u.V) (_ : Irreducible ϖ) (Q : u.D.toPre.X → ℤ) (_ : QForm.IsQ u.D.toPre ϖ Q)
    (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (_ : ValOver ϖ (PadicAlgCl p) v) (lam : ℝ), 0 < lam ∧
    (∀ (x : PadicAlgCl p) (r : ℚ), v x = (r : WithTop ℚ) ↔ ‖x‖ = Real.exp (-(lam * r))) ∧
    (∀ (x : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v x ↔ ‖x‖ ≤ Real.exp (-(lam * r))) ∧
    ∀ (l : u.Lab) χ, l.q χ = lam * Q χ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  have hl := neg_pos.2 (Real.log_neg h0 h1)
  obtain ⟨v, hv⟩ := exists_addVal p h0 h1
  refine ⟨ϖ, hϖ, Q, hQ, v, fun c n hc => (hv _ _).2 ?_, _, hl, hv, fun x r => ?_, fun l χ => ?_⟩
  · rw [PsiForm.norm_of_hasVal u.norm_le hϖ hc]; simp
  · by_cases hx : x = 0
    · simp [hx, (Real.exp_pos _).le]
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hx)
    rw [(hv x s).1 hs.symm, ← hs, WithTop.coe_le_coe, Real.exp_le_exp, neg_le_neg_iff, mul_le_mul_iff_right₀ hl,
      Rat.cast_le]
  · obtain ⟨j, hj⟩ := exists_chart u.D.toPre.P.isLB ((u.D.toPre.c χ).left (IsLocalRing.closedPoint u.V))
    have hj' : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U j :=
      ((IsLocalRing.closedPoint_mem_iff _).1 hj).ge
    have a := l.q_eq χ (fun _ => j) hj'
    have b := PsiForm.norm_of_hasVal u.norm_le hϖ
      (PsiForm.hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => j) hj')
    exact neg_injective (Real.exp_injective (a.symm.trans b))

section
open GlobalTheory.ThetaCompare CommPairing

theorem exists_root_stalk {B : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV B) {T : Over B} {m : ℕ} (hm : Odd m) {k : ℤ}
    (hk : k = (m : ℤ) ^ 2) {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ}
    (hτ : IsTorsFrame P rig m (x ^ m) τ) {th : LB.Sec (LPow P.A P.L 1 T)} {s₁ t : LB.Sec (LPow P.A P.L k T)}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![k, -1])}
    {θ : ThetaGrp P.A P.L k T} (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L rig T (k - 1)))
    (h₁ : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) k 1 α th s₁)
    (hθ : SymLift P.A P.L k (m ^ 2) x θ) (h₂ : IsActOf P.A P.L k θ s₁ t) {y : T.left} {J} (hJ : Good P.L y J)
    {c c' : T.left.presheaf.stalk y}
    (hc : sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => k) t (ptSecT P.A 1).left y J =
      c * (val (rigT P.A P.L rig T k) (𝟙 _) y J).val)
    (hc' : sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => 1) th (ptSecT P.A (x ^ m)).left y J =
      c' * (val (powFrame P.A P.L (x ^ m) τ 1) (𝟙 _) y J).val) :
    c ^ (m ^ 2) = c' ^ (m ^ 2) := by
  subst hk
  have hx : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hτ.1]
  have a₁ := frame_pow hG P hm hα hx hθ hJ
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := val_corr hJ hn (𝟙 _)
  rw [val_pull hJ, val_rigT _ _ hJ, Category.id_comp] at a₃
  have b₂ := sval_twist h₂ (ptSecT P.A 1).left hJ
  have b₃ := sval_twist h₁ (ptSecT P.A x).left hJ
  have p₂ : val (powFrame P.A P.L (x ^ m) τ 1) (𝟙 _) y J = val τ (𝟙 _) y J :=
    (map_zpow _ _ _).trans (zpow_one _)
  rw [pt_translT, _root_.mul_one, congrArg (ptSecT P.A) hθ.pt_eq, b₃, hc, pt_mulT, hc', p₂, val_rigT _ _ hJ] at b₂
  have e : (tval θ (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val τ (𝟙 _) y J *
      (val rig T.hom y J ^ ((m : ℤ) ^ 2))⁻¹) ^ (m ^ 2) = 1 := by
    apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + a₂ + (m ^ 2) • a₃
  have e' : c = (tval θ (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val τ (𝟙 _) y J *
      (val rig T.hom y J ^ ((m : ℤ) ^ 2))⁻¹).val * c' := by
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₂]
    simp only [Units.val_mul, tval]
    ring
  rw [e', mul_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, _root_.one_mul]

theorem pow_eq_of_thC (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V]
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {F : Type} [Field F] [Algebra (FractionRing V) F]
    {rig : LB.Gen (A.L.pull (eSec A.A))} {m : ℕ} (hm : Odd m) {th : SecA A F 1} {x : TFK (R := V) F ⟶ A.A} {t} {c c' : F}
    (H : ThC A rig m th x t c) {e} (he : IsTorsFrame A rig m (x ^ m) e)
    (hc : (∀ z J, Good A.L z J → sA th (ptSecT A.A (x ^ m)).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c') * (val (powFrame A.A A.L (x ^ m) e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val)) :
    c ^ (m ^ 2) = c' ^ (m ^ 2) := by
  obtain ⟨α, s₁, θ, hα, hn, h₁, hθ, h₂, hv⟩ := H
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
  have := exists_root_stalk hG A hm (Nat.cast_pow m 2) he hα hn h₁ hθ h₂ hJ (hv z J hJ) (hc z J hJ)
  apply CoefBasic.cstH_inj (R := V) z
  rw [map_pow, map_pow, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]
  exact this

end

theorem val_eq_of_pow_eq {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {n : ℕ} (hn : n ≠ 0) {c c' : F}
    (h : c ^ n = c' ^ n) : v c = v c' := by
  by_cases h0 : c' = 0
  · subst h0
    rw [zero_pow hn] at h
    rw [pow_eq_zero_iff hn |>.1 h]
  have hc : c ≠ 0 := fun e => h0 (pow_eq_zero_iff hn |>.1 (by rw [← h, e, zero_pow hn]))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 h0)
  have := congrArg v h
  rw [v.map_pow, v.map_pow, ← hr, ← hr', ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, WithTop.coe_eq_coe] at this
  rw [← hr, ← hr', nsmul_right_injective hn this]

open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in

theorem val_theta : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement →
    AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ rig, NormW U.toUnifPre w₀ rig →
      ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ →
      ∀ (m : ℕ), Odd m → IsUnit (m : V) → ∀ (p : QkPt D.toPre F m) x, QkToAkU U.toUnifPre F m p x →
        (∀ e (c : F), IsTorsFrame A rig m x e → (∀ z J, Good A.L z J → sA th (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val) →
          (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧
            (v c = 0 → ∃ z, p.y = m • z)) ∧
        ∀ n, 2 ≤ n → n ∣ m → p.y = 0 → ∃ (p' : QkPt D.toPre F m) (x' : _), p'.y = 0 ∧
          QkToAkU U.toUnifPre F m p' x' ∧ (x' * x⁻¹) ^ n = 1 ∧
          ∀ e (c : F), IsTorsFrame A rig m x' e → (∀ z J, Good A.L z J → sA th (ptSecT A.A x').left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x' e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val) → v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ rig hN th ϑ hE hP m hm hu p x hx
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  have m2 : m ^ 2 ≠ 0 := (pow_pos hm.pos 2).ne'
  obtain ⟨ua₁, ua₂⟩ := ThetaConstVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hN th ϑ hE hP m hm hu
  have up := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F m m (m ^ 2) hm.pos hm.pos (sq m)
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 m hm.pos p.g
  have hg' := (isNsmul_iff_eq _ _ _).1 hg
  let q : QkPt D.toPre F (m ^ 2) := qkMk hB p.y g (by rw [sq, mul_smul, ← hg', qk_nsmul hB])
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
  obtain ⟨f', f₁', -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F m hm.pos
  have hq : QkToAkU U.toUnifPre F (m ^ 2) q (f q) := (f₁ _ _).2 rfl
  obtain rfl : x = f q ^ m := ((f₁' _ _).1 hx).trans ((f₁' _ _).1 ((up p q _).2 rfl hg hq)).symm
  refine ⟨fun e c he hval => ?_, fun n hn hnm hy => ?_⟩
  · obtain ⟨⟨t, c₀⟩, hT, -⟩ := GlobalTheory.existsUnique_thetaConst hL V A F rig hN.2.1 m hm th (f q) (hq w₀ hN.1).1
    rw [← val_eq_of_pow_eq v m2 (pow_eq_of_thC hL.1.globalFns hm hT he hval)]
    exact ua₁ q _ t c₀ hq hT
  · obtain ⟨q', x', t, c₀, hy', hq', hpow, hT, h0⟩ := ua₂ n hn hnm q _ hy hq
    let p' : QkPt D.toPre F m := qkMk hB q'.y (m • q'.g) (by rw [← mul_smul, ← sq, qk_nsmul hB])
    refine ⟨p', x' ^ m, hy', (up p' q' x').2 rfl ((isNsmul_iff_eq _ _ _).2 rfl) hq', hpow, fun e c he hval => ?_⟩
    rw [← val_eq_of_pow_eq v m2 (pow_eq_of_thC hL.1.globalFns hm hT he hval), h0]

end GlobalTheory.ZH.TestVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverLocalRing
open GlobalTheory.CechPic GlobalTheory.StabFlat GlobalTheory.PrimitiveOverValuationRing

theorem exists_ideal_complex (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a) :
    ∃ (I : Ideal A) (C : CochainComplex (ModuleCat.{0} A) ℕ), (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧
      Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] A ⧸ I) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p ∧
        ∀ i, (¬ I ≤ p ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧
      ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
        (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
          I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := GlobalTheory.T.exists_perfect_free_finite_complex A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ =>
    (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  let K := AlgebraicClosure p.ResidueField
  let φ : A →+* K := (algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)
  have hk : RingHom.ker φ = p := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · exact Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)
  · exact Or.inl hi

theorem exists_section_translate : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : PolAV (Spec (CommRingCat.of A))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL _ V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  let y' : Spec (CommRingCat.of K) ⟶ H.left := y.left
  have hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)
  obtain ⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩ :=
    FibreAcyclic.exists_localRing P.A.hom P.g P.smoothDim (y' ≫ j.left) (by
      have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)
      rwa [Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)
  have := P.isAb.comm
  obtain ⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩ := exists_ideal_complex hL.globalFns P.A P.isAb proj P.smoothDim P.isLB hO
    ⟨c.t, c.isGen⟩ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩
  have hI₀ : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI₀
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := (hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := by
    rw [← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]
    rfl
  have hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hloc : IsLocalHom (algebraMap V R) := ((IsLocalRing.local_hom_TFAE (algebraMap V R)).out 2 0).1 hN
  have hsurj : Function.Surjective (algebraMap V (R ⧸ I)) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsPreimmersion (w ≫ j.left) := hw ▸ inferInstance
    have : IsPreimmersion w := IsPreimmersion.of_comp w j.left
    have h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) := hwV ▸ inferInstance
    have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap V (R ⧸ I)) := RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)
    exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2
  have hinj : Function.Injective (algebraMap V (R ⧸ I)) := by
    have hfree := fun i => (c₁ i).1
    have hfin := fun i => (c₁ i).2
    refine FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj
    refine FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) P.g (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂
      fun p hp hNp => ?_
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]
    · obtain ⟨K', _, ψ, hψ, hex⟩ := c₃ p hp
      refine ⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
      refine (IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk I s)
      have h₁ : algebraMap V R a - s ∈ I := Ideal.Quotient.eq.1 ha
      have h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R := by
        simpa using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs
      have h₃ : a ∈ IsLocalRing.maximalIdeal V := fun h => h₂ (h.map _)
      simpa using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)
  have : IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H :=
    Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by
      rw [Category.assoc, hwV]
      exact IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverLocalRing
end
end


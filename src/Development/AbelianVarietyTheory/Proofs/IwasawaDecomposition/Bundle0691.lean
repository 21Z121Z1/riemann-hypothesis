import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveBalancedFormEqOfSameRay
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem balForms_zsmul_cancel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {g : ℤ} (hg : g ≠ 0) {a b : balForms bar X} (h : g • a = g • b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext₂ fun y z => ?_
  have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val h) y z
  simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ hg h2

theorem isPrim_ray_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  intro O _ bar X _ _ β β' p r hβ hβ' hp hr h
  set g := Nat.gcd p r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hp
  obtain ⟨p₁, hp₁⟩ : g ∣ p := Nat.gcd_dvd_left p r
  obtain ⟨r₁, hr₁⟩ : g ∣ r := Nat.gcd_dvd_right p r
  have hcop : Nat.Coprime p₁ r₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := r) hg
    rw [← hgdef] at this
    have e1 : p / g = p₁ := by rw [hp₁, Nat.mul_div_cancel_left _ hg]
    have e2 : r / g = r₁ := by rw [hr₁, Nat.mul_div_cancel_left _ hg]
    rwa [e1, e2] at this

  have h1 : (p₁ : ℤ) • β = (r₁ : ℤ) • β' := by
    apply balForms_zsmul_cancel (g := (g : ℤ)) (by exact_mod_cast hg.ne')
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, ← hp₁, ← hr₁, natCast_zsmul, natCast_zsmul]
    exact h

  have hbez : (p₁ : ℤ) * Nat.gcdA p₁ r₁ + (r₁ : ℤ) * Nat.gcdB p₁ r₁ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  set u := Nat.gcdA p₁ r₁
  set v := Nat.gcdB p₁ r₁
  have hr1 : r₁ = 1 := by
    apply hβ r₁ (u • β' + v • β)
    calc β = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β := by rw [hbez, one_smul]
      _ = u • ((p₁ : ℤ) • β) + (r₁ : ℤ) • (v • β) := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (p₁ : ℤ) u]
      _ = r₁ • (u • β' + v • β) := by
          rw [h1, smul_smul, mul_comm u, ← smul_smul, ← smul_add, natCast_zsmul]
  have hp1 : p₁ = 1 := by
    apply hβ' p₁ (u • β' + v • β)
    calc β' = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β' := by rw [hbez, one_smul]
      _ = (p₁ : ℤ) • (u • β') + v • ((r₁ : ℤ) • β') := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (r₁ : ℤ) v]
      _ = p₁ • (u • β' + v • β) := by
          rw [← h1, smul_smul v, mul_comm v, ← smul_smul, ← smul_add, natCast_zsmul]
  rw [hr1, hp1] at h1
  simpa using h1

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SiegFibrePol

theorem polAV_of_lam_univ : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  intro o _ ζ g n F K _ y B _ α α₂ hpb hsq L hL hrig hsym hΛ
  open GlobalTheory.CechPic GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw in
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.comm
  have laws : Out.Laws := GlobalTheory.allSixLaws.1
  haveI : IsProper F.univ.A.hom := F.univ.ab.proper
  have hP' : (F.univ.P.pull α₂).IsLB := pull_isLB F.univ.isLB α₂
  have hrefl : LBIso (F.univ.P.pull α₂) (F.univ.P.pull α₂) := (GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl
  have hn := GlobalTheory.SiegelPull.nondeg_pull hpb hsq F.univ.isLB hP' hrefl F.princ.2
  have hM0 : (F.univ.diag.pull α).IsLB := pull_isLB (pull_isLB F.univ.isLB _) α
  have hamp0 : Out.RelAmple B (F.univ.diag.pull α) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback (pull_isLB F.univ.isLB _) F.princ.1 hpb.1
  have hd : ((F.univ.P.pull α₂).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB hP' _
  have hdiag := GlobalTheory.SiegelPull.diag_iso hsq hrefl
  have eM0 : GlobalTheory.CechPic.cls _ hM0 = GlobalTheory.CechPic.cls _ hd := ((GlobalTheory.CechPic.cls_eq_iff hd hM0).2 hdiag).symm
  have hp : IsProjBy B.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B _ hB hM0 hamp0 K (𝟙 _) _ (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy laws K B hB hp L hL
  have s₁ := GlobalTheory.SameLam.pull_inv_cls hL hsym
  have e₀ : GlobalTheory.CechPic.cls _ hP' = GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (fst B B) (snd B B) :=
    ((GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hP').2 hΛ).symm.trans
      (GlobalTheory.CechPic.cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  have hη : GlobalTheory.CechPic.pull (η[B] : 𝟙_ _ ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [← GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)]
    exact (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).2 hrig
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp, hη, map_zero]
  have e₃ : GlobalTheory.CechPic.cls _ hd = 2 • GlobalTheory.CechPic.cls L hL := by
    refine (GlobalTheory.CechPic.cls_pull hP' _ _).trans ?_
    rw [e₀, GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd, GlobalTheory.SymRoot.lam_diag hL hΘ s₁, GlobalTheory.SymRoot.rigCls, h1, sub_zero]
  have f : IsFinite (𝟙 B : B ⟶ B).left := by rw [Over.id_left]; infer_instance
  have iso : LBIso (F.univ.diag.pull α) (lbPow L 2) :=
    (GlobalTheory.CechPic.cls_eq_iff hM0 (isLB_lbPow hL 2)).1 (eM0.trans (e₃.trans (cls_lbPow hL 2 _).symm))
  have hamp : Out.RelAmple B L :=
    (GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) L 2 two_pos hB hB hL f).2.1.1
      ((GlobalTheory.relAmple_finite_pow_iso _ B B (𝟙 _) _ 2 two_pos hB hB hM0 f).2.2.2 _ (isLB_lbPow hL 2) iso hamp0)
  exact ⟨hB, hamp, GlobalTheory.ThetaExtend.kTriv_of_lam hL hP' e₀ hn⟩

end GlobalTheory.SiegFibrePol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiTauCoordRel

open GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

def kst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem kst_algebraMap (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    kst ξ (algebraMap R (FractionRing R) r) = cst ξ r := rfl

theorem kst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (kst (R := R) ξ) :=
  RingHom.injective _

theorem gm_genVal (ξ : Spec (CommRingCat.of (FractionRing R))) {M : LB (TK R).left} (t : LB.Gen M) (j : M.ι)
    (h : ⊤ ≤ M.U j) :
    (gm (𝟙 _) ξ (M.U j) (t.s j)).val = kst ξ (genVal t j h).val := by
  rw [gm_val _ ξ _ (h trivial)]
  simp only [kst, genVal, RingHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm

theorem gm_mulGen {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (y : Y) (j : K ⊕ K' → L.ι) (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j) =
      gm (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)) *
        gm (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))

theorem gm_invGen {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι) :
    gm (𝟙 Y) y (LB.wchart L φ j) ((LB.invGen L φ ε t).s j) = (gm (𝟙 Y) y (LB.wchart L φ j) (t.s j))⁻¹ :=
  map_inv _ _

theorem mem_inl {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ (j ∘ Sum.inl) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

theorem mem_inr {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ' (j ∘ Sum.inr) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

variable [IsLocalRing R]

theorem val_psi_chart (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) :
    ∃ u : Rˣ, val (D.psi χ) (𝟙 _) ξ J = Units.map (cst ξ).toMonoidHom u *
      gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j =
        (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, t.trans ?_⟩
  rw [h2, map_inv]
  congr 2
  exact Units.ext hu

theorem val_int {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (ξ : Spec (CommRingCat.of (FractionRing R)))
    {J : ((Spec (CommRingCat.of (FractionRing R))) ⟶ A.left) → L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (p : Spec (CommRingCat.of R) ⟶ Y) (hp : ∀ k, (p ≫ φ k) ≫ A.hom = 𝟙 _) :
    ∃ w : Rˣ, val t (jK R ≫ p) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := unit_gm' ξ p (LB.wchart L φ (fun k => J ((jK R ≫ p) ≫ φ k)))
    (Set.mem_iInter.2 fun k => by
      have := hJc (p ≫ φ k) (hp k)
      rw [← Category.assoc] at this
      exact this) (t.s _)
  exact ⟨w, Units.ext hw⟩

theorem toUnit_left : (toUnit (TK R)).left = jK R := by
  simpa using Over.w (toUnit (TK R))

theorem gm_rigK (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D η[D.P.A] (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) :
    ∃ w : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) (D.rigK.s j) =
      Units.map (cst ξ).toMonoidHom w := by
  have e1 := gm_res (𝟙 _) ξ (show LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j ≤
      (toUnit (TK R)).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j from
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) hm
    (pullU (toUnit (TK R)).left _ (D.rig.s j))
  have e2 := gm_pull (𝟙 _) (toUnit (TK R)).left ξ (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) (D.rig.s j)
  have e3 : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [e3] at e2
  obtain ⟨w, hw⟩ := unit_gm' ξ (𝟙 _) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun _ => hj trivial) (D.rig.s j)
  exact ⟨w, (e1.trans e2).trans (Units.ext hw)⟩

theorem alg {G : Type} [CommGroup G] (T G1 G2 G3 c1 c2 c3 c4 c5 c6 c7 Vab Va Vb Vr Vu Kr : G)
    (h1 : T = G1 * G2⁻¹ * G3⁻¹ * c4⁻¹) (h2 : Vab = c1 * G1) (h3 : Va = c2 * G2) (h4 : Vb = c3 * G3)
    (h7 : Vr = c5) (h8 : Vu = c6)
    (h5 : Vab * Va⁻¹ * Vb⁻¹ * Vr⁻¹ * Vu = Va * Vr) (h6 : Va = c7 * Kr) :
    Kr = c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹ * T := by
  subst h1 h2 h4 h3 h7 h8
  have hK : Kr = c7⁻¹ * (c2 * G2) := by rw [h6]; group
  subst hK
  apply Additive.ofMul.injective
  have h5' := congrArg Additive.ofMul h5
  simp only [ofMul_mul, ofMul_inv] at h5' ⊢
  rw [← sub_eq_zero] at h5' ⊢
  refine Eq.trans ?_ (congrArg Neg.neg h5' |>.trans neg_zero)
  abel

theorem final (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) (h0 : r ≠ 0) (X : (FractionRing R)ˣ) (c : Rˣ)
    (key : Units.map (kst ξ).toMonoidHom (toUnitK r h0) =
      Units.map (cst ξ).toMonoidHom c * Units.map (kst ξ).toMonoidHom X) :
    algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (c : R) * (X : FractionRing R) := by
  have k3 : toUnitK r h0 = Units.map (algebraMap R (FractionRing R)).toMonoidHom c * X := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [key, map_mul]
    rfl
  exact congrArg Units.val k3

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D.X] (oa : D.OAct O) (w0 : O), TraceFormTwistIso D oa w0 → ∀ (y : D.X) (r : R) (x : (FractionRing R)ˣ),
    PsiCoord D y r → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D y (w0 • y) x →
    ∃ u : Rˣ, algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u : R) * (x : FractionRing R) := by
  intro R _ _ _ D O _ _ _ oa w0 hW y r x hr hx
  obtain ⟨u, -, -, hrel⟩ := hW
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom

  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hrel y) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [val_pull hJ] at e
  have e' := (congrArg (· * val u (𝟙 _ ≫ D.xK y) ξ J) (PeriodBalance.val_tau D ξ hJ y (w0 • y))).symm.trans e
  obtain ⟨c6, h6⟩ : ∃ w : Rˣ, val u (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
    rw [this]
    refine val_int ξ hJc u (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left,
        (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 _) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau y (w0 • y)) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (y + w0 • y) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc y _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc (w0 • y) _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)

  have h0 := PsiCoordLocal.ne_zero_of_coord hr
  obtain ⟨jp, hp, ip, ep⟩ := GlobalTheory.PeriodFormCompare.isPsiCoord_toUnitK hr h0
  obtain ⟨c7, g7⟩ := val_psi_chart D ξ hJ hJc y jp ip (hp trivial)
  have eP := gm_genVal ξ (D.psi y) jp hp
  rw [← ep] at eP
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) =
      kU (genVal (D.tau y (w0 • y)) j h) := Units.ext eT
  have eP' : gm (𝟙 _) ξ (LB.wchart D.P.L _ jp) ((D.psi y).s jp) = kU (toUnitK r h0) := Units.ext eP
  have key := alg (h1 := eT'.symm.trans (dT.trans (by rw [g4]))) (h2 := g1) (h3 := g2) (h4 := g3) (h7 := h5)
    (h8 := h6) (h5 := e') (h6 := g7.trans (congrArg (cU c7 * ·) eP'))
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹, final ξ r h0 _ _ (key.trans ?_)⟩
  simp only [cU, kU, map_mul, map_inv]

end GlobalTheory.PsiTauCoordRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcLimit
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TraitGen

theorem exists_polGen_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ n : ℕ, (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n}) →
  ∃ e : LB.Gen ((polOf Z m BD).pull (x₀ ≫ Z.j)), e.IsGen ∧
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → ∃ e' : LB.Gen ((polOf Z m BD).pull χ), e'.IsGen ∧
      ∀ z J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good (polOf Z m BD) z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => x₀ ≫ Z.j) (ε := fun _ => 1) e (spMap gam) z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := polOf Z m BD) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (Out.jK V) z J := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj huniv φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hB hC x₀ hx₀ n hn
  obtain ⟨e₁, he₁, hx₁⟩ := GlobalTheory.T.pullback_model_arc_polarization E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj huniv O' b' ϖ a χ₀ hB hC x₀ hx₀
  obtain ⟨e₂, he₂, hx₂⟩ := GlobalTheory.T.generator_extends_power _ _ _ _ e₁ m he₁ hx₁
  obtain ⟨e₃, he₃, hx₃⟩ := GlobalTheory.T.ideal_along_dvr_arcs Z.X BD (PowerSeries O') PowerSeries.X PowerSeries.X_ne_zero (x₀ ≫ Z.j) n hn
  obtain ⟨e, he, hx⟩ := GlobalTheory.T.generator_extends_tensor _ _ _ _ _ e₂ e₃ he₂ he₃ hx₂ hx₃
  exact ⟨e, he, hx⟩

end GlobalTheory.TraitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeInterCellOpenSubset
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Overlap

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_fieldPoint {A : Type} [CommRing A] (y : Sp A) :
    ∃ (k : Type) (_ : Field k) (ψ : A →+* k), ∀ q : Sp k, spMap ψ q = y := by
  refine ⟨(show PrimeSpectrum A from y).asIdeal.ResidueField, inferInstance, algebraMap _ _, fun q => ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap _ (show PrimeSpectrum _ from q).asIdeal = _
  rw [show (show PrimeSpectrum _ from q).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
  exact Ideal.ker_algebraMap_residueField _

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {ι : Type} {c c' : Let m → ι → S}
    (h : InBlock c c') (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_lform {ι : Type} {M k : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q : Fin (plN M k + 1)) :
    φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

theorem range_inter_cellOpen_subset : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∀ b' w', Set.range (h b' w') ∩ (W : Set P) ⊆ Set.range (h b w) := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hc hp b w W hW b' w'
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  obtain ⟨k, _, ψ', hψ'⟩ := exists_fieldPoint y
  have hz : ∀ q : Sp k, (spMap ψ' ≫ h b' w') q = h b' w' y := fun q => by
    rw [Scheme.Hom.comp_apply, hψ']
  obtain ⟨φ, hφ, hne⟩ := (hW k (spMap ψ' ≫ h b' w')).1 (by
    rintro _ ⟨q, rfl⟩
    rw [hz]; exact hy)
  rw [Category.assoc, hp.base] at hφ
  have hφ' : spMap φ ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← hφ, cbase, ← Category.assoc, spMap_spMap]
  have hu : InBlock (fun z => φ ∘ c b z) (fun z => ψ' ∘ uvec (c b') w' z) := by
    have := inBlock_cellVec (hc.compat k b b' φ _ hφ') w' (ψ' ∘ MvPolynomial.X)
    convert this using 2 with z
    exact map_cellVec ψ' _ w' _ z
  obtain ⟨x, d, hd, ht⟩ := GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors T m k M _ _ _ w ((hc.inv b).map φ) hu (fun τ j hj => by
    obtain ⟨hv, e⟩ := hp.plk b' w' (stdEn τ j hj)
    have := hne τ j hj _ _ _ (by rw [Category.assoc, e, spMap_pt])
    rw [map_plk] at this
    simpa only [map_lform] using this)
  have hψ : ∀ z, (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) ∘ uvec (c b) w z =
      cellVec (fun z => φ ∘ c b z) w x z := fun z => by
    refine (map_cellVec _ _ w _ z).trans ?_
    congr 1
    · funext z r; simp
    · funext r; simp
  have key := GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hc hp k b b' w w' (MvPolynomial.eval₂Hom φ x) ψ' d
    (by rw [hφ, cbase, ← Category.assoc, spMap_spMap, MvPolynomial.eval₂Hom_comp_C]) hd
    (by simpa only [hψ] using ht)
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨spMap (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) q, by
    rw [← hz q, ← key, Scheme.Hom.comp_apply]⟩

end GlobalTheory.FlagEmb.Overlap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_linearIndependent_coords_of_real_independent : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  first | exact @GlobalTheory.rowsInd_rat_of_real | exact GlobalTheory.rowsInd_rat_of_real | (intros; apply GlobalTheory.rowsInd_rat_of_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relations_period_matrix_hermitian : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  first | exact @GlobalTheory.riemann_relations_period_matrix | exact GlobalTheory.riemann_relations_period_matrix | (intros; apply GlobalTheory.riemann_relations_period_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigSymBaseChange

theorem rigidified_and_sym_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  intro S S' f G _ B _ β gp L σ hσ
  refine ⟨PolBaseChange.rigidified_pull gp ⟨L.rig, L.rigGen⟩, fun _ => ⟨⊤, trivial, ?_⟩⟩
  refine gen_chartPull (chartPullLinComb L.L β (K := Fin 2) _
    ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1] ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) fun k => ?_) σ hσ
  fin_cases k
  · show ((B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ (GrpObj.inv : G ⟶ G).left
    rw [Category.assoc, PolBaseChange.inv_comm gp, Category.assoc]
  · show (B.hom ⁻¹ᵁ ⊤).ι ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ 𝟙 G.left
    rw [Category.comp_id]

end GlobalTheory.RigSymBaseChange
end
end


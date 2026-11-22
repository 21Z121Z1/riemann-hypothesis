import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal

section Alg

variable {r : ℕ} {U : Type} [CommGroup U]

theorem prod_theta (a b c : Vec r) (F : Vec r → U) :
    ∏ v ∈ (theta a b c).support, F v ^ theta a b c v =
      F (a + b + c) * (F (a + b))⁻¹ * (F (a + c))⁻¹ * (F (b + c))⁻¹ * F a * F b * F c * (F 0)⁻¹ := by
  have h0 : ∀ v, F v ^ (0 : ℤ) = 1 := fun v => zpow_zero _
  have hadd : ∀ v (m n : ℤ), F v ^ (m + n) = F v ^ m * F v ^ n := fun v m n => zpow_add _ _ _
  change (theta a b c).prod (fun v n => F v ^ n) = _
  simp only [theta, sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.prod_add_index' h0 hadd]
  simp only [Finsupp.prod_single_index (h := fun v (n : ℤ) => F v ^ n) (h0 _), zpow_one, zpow_neg]

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp only [vecLat, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

theorem comp_vecHom (T : Tens D D' W) {Z : Over (Spec (CommRingCat.of R))} (p q : Z ⟶ D'.P.A) (v : Vec r) :
    lift p q ≫ vecHom T v = (∏ k, (p ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ T.pr k) ^ v (Sum.inr k) := by
  have e := (preHom (G := D.P.A) (lift p q)).map_mul (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k))
    (∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k))
  simp only [map_prod, map_zpow] at e
  rw [vecHom]
  simpa only [preHom, MonoidHom.mk'_apply, lift_fst_assoc, lift_snd_assoc] using e

theorem zero_vecHom (T : Tens D D' W) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom T v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    haveI := T.pr_hom k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

def cPHom (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : Multiplicative D.X →* (T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => DVR.cP D T x.toAdd) fun a b => DVR.cPoint_add D T a.toAdd b.toAdd

theorem pt_vecHom (T : Tens D D' W) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom T v = DVR.cP D (TK R) (vecLat T v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ T.pr k = cPHom D (TK R) (Multiplicative.ofAdd (T.xe x k)) := fun x k => by
    simp only [DVR.cP, Category.assoc, T.c_pr]; rfl
  rw [comp_vecHom, show DVR.cP D (TK R) (vecLat T v y y') = cPHom D (TK R) (Multiplicative.ofAdd (vecLat T v y y')) from rfl]
  simp only [hp, vecLat, ofAdd_add, ofAdd_sum, ofAdd_zsmul, map_mul, map_prod, map_zpow]

theorem cubV_psi (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (p q s : D.X) :
    cubV D.cub (T := TK R) z J (DVR.cP D _ p) (DVR.cP D _ q) (DVR.cP D _ s) =
      (val (D.psi (p + q + s)) (𝟙 _) z J)⁻¹ * val (D.psi (p + q)) (𝟙 _) z J * val (D.psi (p + s)) (𝟙 _) z J *
        val (D.psi (q + s)) (𝟙 _) z J * (val (D.psi p) (𝟙 _) z J)⁻¹ * (val (D.psi q) (𝟙 _) z J)⁻¹ *
        (val (D.psi s) (𝟙 _) z J)⁻¹ * val (D.psi 0) (𝟙 _) z J := by
  have t := DVR.tauK_mul hJ hB p q s
  have t0 := GlobalTheory.TauBalElem.tau_zero_left hB hJ 0
  rw [GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ] at t
  rw [GlobalTheory.TauBalBox.tau_val D hJ, add_zero] at t0
  apply Additive.ofMul.injective
  have t' := congrArg Additive.ofMul t
  have t0' := congrArg Additive.ofMul t0
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at t' t0' ⊢
  linear_combination (norm := abel) t' + t0'

theorem triv_theta : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  intro R _ _ D D' r W T hB a b c
  have hF : FormEq (fun I => (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left ≫ thφ D.P.A (x3 D.P.A) I) thε
      (fun v : (theta a b c).support => (vecHom T v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom T a) (vecHom T b) (vecHom T c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom T v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen D.P.isLB hF
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left)
    (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom, zero_vecHom, zero_vecHom]
    exact (isCub_cubV D.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom, pt_vecHom, pt_vecHom, cubV_psi hB hJ]
    simp only [zpow_neg, ← inv_zpow]
    rw [prod_theta (F := fun v => (val (D.psi (vecLat T v y y')) (𝟙 _) z J)⁻¹)]
    rw [vecLat_add T (a + b) c, vecLat_add T a b, vecLat_add T a c, vecLat_add T b c, vecLat_zero]
    simp only [inv_inv]

end GlobalTheory.TensBal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricOfGaloisPullbackUniformisationBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SymDesc

open GlobalTheory.CechPic

theorem exists_gen_of_invariant {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y)
    {Γ₀ : Type} (act : Γ₀ → (Y' ⟶ Y')) (hact : ∀ σ, act σ ≫ π = π)
    (H : ∀ V : Y.Opens, Function.Injective (π.app V).hom ∧ ∀ u : Γ(Y', π ⁻¹ᵁ V),
      (∀ σ (h : π ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (π.app V).hom)
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ σ (z : Y') (J), Good L z J → val u (act σ) z J = val u (𝟙 Y') z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have inv : ∀ (j : K → L.ι) σ (h₁ : π ⁻¹ᵁ LB.wchart L φ j ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ LB.wchart L φ j)),
      ((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val = (res (le j) (u.s j)).val := by
    intro j σ h₁
    refine fn_ext fun z hz => ?_
    have hz' : act σ z ∈ π ⁻¹ᵁ LB.wchart L φ j := h₁ hz
    have e₀ : gs (𝟙 Y') z _ (((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val) =
        gs (act σ) z _ (res (le j) (u.s j)).val := by
      have := (gs_res (𝟙 Y') z h₁ hz (((act σ).app _).hom (res (le j) (u.s j)).val)).trans
        (gs_pull (𝟙 Y') (act σ) z _ hz' _)
      rw [Category.id_comp] at this
      exact this
    rw [e₀, gs_unit (act σ) z _ hz', gs_unit (𝟙 Y') _ _ hz]
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu (act σ) z (le j hz') (Good.mem hI _ (act σ))
    have c₂ := gen_trans hu (𝟙 Y') z (le j hz) (Good.mem hI _ (𝟙 Y'))
    have c₃ : trF (fun k => π ≫ φ k) ε (act σ) z j (fun k => I (act σ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε (𝟙 Y') z j (fun k => I (𝟙 Y' ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : act σ ≫ π ≫ φ k = 𝟙 Y' ≫ π ≫ φ k := by rw [reassoc_of% hact σ, Category.id_comp]
      show gm (act σ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (act σ ≫ π ≫ φ k))) (L.g (j k) (I (act σ ≫ π ≫ φ k))) ^ _ =
        gm (𝟙 Y' ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (𝟙 Y' ≫ π ≫ φ k))) (L.g (j k) (I (𝟙 Y' ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res (act σ) z (le j) hz' _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h σ z I hI)).trans c₂.symm)).trans
        (gm_res (𝟙 Y') z (le j) hz _).symm))
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j)ˣ, pullU π _ a = res (le j) (u.s j) := by
    intro j
    obtain ⟨a, ha⟩ := (H _).2 _ (inv j)
    obtain ⟨b, hb⟩ := (H _).2 (res (le j) (u.s j))⁻¹.val (fun σ h₁ => by
      refine (Units.mul_left_inj (res (le j) (u.s j))).1 ?_
      rw [Units.inv_mul]
      conv_lhs => rw [← inv j σ h₁]
      rw [← map_mul, Units.inv_mul, map_one])
    have ab : a * b = 1 := (H _).1 (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
    exact ⟨⟨a, b, ab, (mul_comm b a).trans ab⟩, Units.ext ha⟩
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (a j) = gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) (ha j)).trans (gm_res r y (le j) hy _))
  refine ⟨⟨a⟩, fun j j' => Units.ext ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  simp only [trF, Category.id_comp]

theorem isSymmetric_of_exists_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (ht : t.IsGen) :
    L.IsSymmetric := by
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have z := (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two] at z
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, ← sub_eq_add_neg,
    sub_eq_zero] at z
  have he : eSec G ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := e₂.trans (Category.id_comp _).symm
  exact ⟨he, Unif.RigidifyIso.exists_rigidified_iso S S (𝟙 S) G G _ he L L
    ((cls_eq_iff L.isLB (pull_isLB L.isLB _)).1 z.symm)⟩

theorem exists_sym_pull {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f β) {L : LB G.left} (hL : L.IsLB)
    {L' : LB G'.left} (hL' : L'.IsLB) (hiso : LBIso L' (L.pull β))
    (s : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s (eSec G')) (LB.oneGen L')) :
    ∃ u : LB.Gen (LB.LinComb L (fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (I), Good L z I → val u (r ≫ eSec G') z I = 1 := by
  obtain ⟨w, hw⟩ := hiso
  have hp := (isGen_iff w).1 hw
  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have e₁ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have hc : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hp hL hL' s hs
  obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ (![1, -1] : Fin 2 → ℤ) k) (hc k)) t₁ ht₁
  refine ⟨u, hu, fun Z r z I hI => ?_⟩
  choose J hJ using fun χ : Z ⟶ G'.left => exists_chart hL' (χ z)
  rw [vu Z _ z I hI, val_of t₁ _ z I (fun k => I (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (fun k => congrArg I (Category.assoc _ _ _).symm)]
  refine (v₁ Z (r ≫ eSec G') z _ _ (Set.mem_iInter.2 fun k => hI (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (Good.mem hJ _ _)).trans ?_
  have h1 : val s (r ≫ eSec G') z J = 1 :=
    (val_pull hJ s (eSec G') r).symm.trans ((val_corr hJ hr r).trans (val_one _))
  refine (congrArg₂ (· * ·) ?_ h1).trans (_root_.mul_one 1)
  have k : ∀ (V : Type) [CommGroup V] (q : (Z ⟶ G'.left) → V),
      ∏ k : Fin 2, q ((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro V _ q
    simp [Fin.prod_univ_two, e₁]
  exact k _ (fun q => gw w q z (I (q ≫ β)) (J q))

end GlobalTheory.Mum.SymDesc

namespace GlobalTheory.Mum

open SymDesc

theorem isSymmetric_of_pull_iso_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), RigLB.IsSymmetric (⟨L, rig, hL, hr⟩ : RigLB G) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hg D D' hD A' G' _ _ _ U' a G _ _ β hG gp hβ L hL hiso rig hr
  obtain ⟨u, hu, h1⟩ := exists_sym_pull gp hL U'.LG.isLB hiso U'.symG U'.symG_gen U'.symG_rig
  have := U'.smooth
  have := hG.smooth
  have hsurj : Function.Surjective (pullback.snd G'.hom (jK R')).appTop.hom := by
    have hw : U'.gen.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK R') := Over.w U'.gen.hom
    have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
    have : IsIso U'.gen.hom.left.appTop := inferInstanceAs (IsIso (U'.gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso U'.gen.hom.left.appTop).2
      (GlobalTheory.SemiRigid.globalFns _ _ A'.isAb).2
  have he : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨t, ht⟩ := exists_gen_of_invariant hL β a.act hβ
    (GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hρ hg _ _ G.hom G'.hom β inferInstance gp.1 a.act hβ fun σ => (a.cart σ).1.w)
    _ _ u hu fun σ z J hJ => by
      have key := GlobalTheory.ValueForm.gen_unique_of_injective hL (φ := fun k : Fin 2 => a.act σ ≫ β ≫ ![(ι[G]).left, 𝟙 G.left] k)
        (fun V _ q => Finset.prod_congr rfl fun k _ => by
          dsimp only
          rw [reassoc_of% hβ σ])
        (pullback.fst G'.hom (jK R')) (GlobalTheory.ValueForm.app_generic_injective _) (pullback.snd _ _)
        (pullback.lift (jK R' ≫ eSec G') (𝟙 _) (by
          rw [Category.id_comp]
          exact (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) he).trans (Category.comp_id _))))
        (pullback.lift_snd _ _ _) hsurj (DVR.pullGen_isGen _ _ _ _ hu (a.act σ)) hu (fun y I hI => by
          rw [pullback.lift_fst]
          refine (val_pull hI _ _ _).trans (Eq.trans ?_ (h1 _ (jK R') y I hI).symm)
          have e : (jK R' ≫ eSec G') ≫ a.act σ = (jK R' ≫ (cubeMapOf (a.cart σ)).e) ≫ eSec G' :=
            (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) (cubeMapOf (a.cart σ)).e_comm).trans
              (Category.assoc _ _ _).symm)
          exact (congrArg (fun q => val u q y I) e).trans (h1 _ _ y I hI)) _ (𝟙 _) z J hJ
      have k₂ := (val_pull hJ u (a.act σ) (𝟙 _)).symm.trans key
      rwa [Category.id_comp] at k₂
  exact isSymmetric_of_exists_gen _ t ht

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupSchemeStatement
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
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranslateOfTangentVector_fibre_to_groupScheme : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] (x0 : Sp K ⟶ X) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) {R : Type} [CommRing R] (ψ : R →+* K) (v : Sp (DualNumber R) ⟶ t.G.left) (u : epsR K ⟶ A) (hu : u.left ≫ m = spMap (dualMap ψ) ≫ v) {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x u w), LogKS.IsTranslate t (φ.comp ψ) (x ≫ m) v (w ≫ m) := by
  first | exact @GlobalTheory.CechKS.IsTransl.isTranslate_comp | exact GlobalTheory.CechKS.IsTransl.isTranslate_comp | (intros; apply GlobalTheory.CechKS.IsTransl.isTranslate_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValuePullbackBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem ptSecT_comp_whisker {B : Scheme.{0}} {A : Over B} [GrpObj A] {T T' : Over B} (c : T' ⟶ T) (y : T ⟶ A) :
    (ptSecT A (c ≫ y)).left ≫ (c ▷ A).left = c.left ≫ (ptSecT A y).left := by
  rw [← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_whiskerRight, comp_lift, Category.id_comp,
    Category.comp_id]

theorem isTwVal_pull {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T) :
    IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  rintro ⟨α, U, hα, hU, H⟩
  obtain ⟨α', hα', vα⟩ := GlobalTheory.VVRank.exists_gen_pullTo
    (φ' := ![(snd T' P.A).left, (snd T' P.A ^ m).left]) α hα (c ▷ P.A).left (fun k => by
      fin_cases k
      · exact GlobalTheory.VVRank.whisker_snd_left P.A c
      · change (c ▷ P.A).left ≫ (snd T P.A ^ m).left = (snd T' P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, whiskerRight_snd])
  obtain ⟨U', hU', vU⟩ := GlobalTheory.SymLiftGlobal.exists_symLift_pull_val P.isLB c hU
  refine ⟨α', U', hα', hU', fun Z r z J hJ => ?_⟩
  have eq₁ : (c ≫ x) * (c ≫ h) = c ≫ (x * h) := (MonObj.comp_mul _ _ _).symm
  have q := H Z (r ≫ c.left) z J hJ
  have g : gs r z ⊤ (c.left.appTop.hom v) = gs (r ≫ c.left) z ⊤ v := gs_pull r c.left z ⊤ trivial v
  have w : ∀ (y : T ⟶ P.A) {W : Scheme.{0}} (k : (T ⊗ P.A).left ⟶ W),
      (ptSecT P.A (c ≫ y)).left ≫ (c ▷ P.A).left ≫ k = c.left ≫ (ptSecT P.A y).left ≫ k := fun y W k => by
    rw [← Category.assoc, ptSecT_comp_whisker, Category.assoc]
  have eq₃ : (c ≫ (x * h)) ^ m = c ≫ (x * h) ^ m := (MonObj.comp_pow _ _ _).symm
  rw [g, vα _ _ z J hJ, vα _ _ z J hJ, vU _ _ z J hJ, eq₁, eq₃]
  simp only [Category.assoc, ptSecT_comp_whisker, comp_whiskerRight, Over.comp_left, w]
  simpa only [Category.assoc] using q

end GlobalTheory.UPoinc.USum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueTranslateOrthogonalTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum

open GlobalTheory.ThetaCompare GlobalTheory.CommPairing in

theorem isTwVal_transl : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  intro B P N m T₀ T θ z₀ τ β x h v k hk hw H
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, U, hα, hU, H⟩ := H
  refine ⟨α, U, hα, hU, fun Z r z J hJ => ?_⟩
  have e₀ : (translT P.A k).left ≫ (snd T P.A).left = (translPt P.A k).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT P.A k).left ≫ (snd T P.A ^ m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, SymLiftOdd.comp_pow', translT, lift_snd,
      show translPt P.A k = (fst T P.A ≫ k) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hk,
      MonObj.comp_one, _root_.one_mul]
  obtain ⟨d, hd, hv⟩ := exists_gen P.isLB (K' := Fin 2) (φ' := ![(snd T P.A).left, (translPt P.A k).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun V _ g => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₀, e₁, neg_neg, zpow_neg, zpow_one, _root_.mul_assoc]
      rw [inv_inv, mul_left_comm (g (snd T P.A ^ m).left)⁻¹, inv_mul_cancel, _root_.mul_one])
    (LB.mulGen P.L _ _ _ _ α (LB.invGen P.L _ _ (LB.pullGen P.L _ _ α (translT P.A k).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  let D : ThetaGrp P.A P.L N T := ⟨k, d, hd⟩
  have hD : ∀ s : Z ⟶ (T ⊗ P.A).left,
      tval D s z J = val α s z J * (val α (s ≫ (translT P.A k).left) z J)⁻¹ := fun s =>
    (hv Z s z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (val α s z J * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have hx : U.pt = x := hU.pt_eq
  have hc : CommIsOf P.A P.L N U D 1 :=
    (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB U D 1).1 (hx ▸ hw)
  have q := val_corr hJ hc (r ≫ (ptSecT P.A h).left)
  have q₁ : val (constGen P.A P.L (1 : Γ(T.left, ⊤)ˣ)) (r ≫ (ptSecT P.A h).left) z J = 1 := by
    refine ((gm_res _ z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans
      (gm_pull _ (fst T P.A).left z ⊤ trivial 1)).trans (map_one _)
  have q₂ : tval U (r ≫ (ptSecT P.A h).left) z J * tval D ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A U.pt).left) z J =
      tval D (r ≫ (ptSecT P.A h).left) z J * tval U ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A k).left) z J * 1 :=
    ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))).symm.trans (q.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))) q₁)))
  simp only [hD, Category.assoc, pt_translT, hx, _root_.mul_one] at q₂
  have p₁ : (x * (h * k)) ^ m = (x * h) ^ m := by
    rw [← _root_.mul_assoc, mul_pow, hk, _root_.mul_one]
  have p₂ : k * (x * h) = x * (h * k) := by rw [mul_comm k, _root_.mul_assoc]
  rw [p₂, mul_comm k h] at q₂
  rw [p₁]
  have H' := H Z r z J hJ
  set a₁ := val α (r ≫ (ptSecT P.A h).left) z J
  set a₂ := val α (r ≫ (ptSecT P.A (h * k)).left) z J
  set a₃ := val α (r ≫ (ptSecT P.A (x * h)).left) z J
  set a₄ := val α (r ≫ (ptSecT P.A (x * (h * k))).left) z J
  set u₁ := tval U (r ≫ (ptSecT P.A h).left) z J
  set u₂ := tval U (r ≫ (ptSecT P.A (h * k)).left) z J
  set t := val τ (r ≫ β.left) z J
  have f₁ : a₂ * t = (a₂ * a₁⁻¹) * (a₁ * t) := by
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  have f₂ : u₂ * a₄ = (a₂ * a₁⁻¹) * (u₁ * a₃) := by
    apply Additive.ofMul.injective
    replace q₂ := congrArg Additive.ofMul q₂
    simp only [ofMul_mul, ofMul_inv] at q₂ ⊢
    linear_combination (norm := module) -q₂
  rw [f₁, f₂, Units.val_mul _ (a₁ * t), Units.val_mul _ (u₁ * a₃), mul_left_comm, H', _root_.mul_assoc]

end GlobalTheory.UPoinc.USum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum

theorem isTwVal_unique {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)) (hN : Odd N) (H : IsTwVal P N m θ τ β x h v)
    (H' : IsTwVal P N m θ τ β x h v') : v = v' := by
  obtain ⟨α, U, hα, hU, e⟩ := H
  obtain ⟨α', U', hα', hU', e'⟩ := H'
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hc := GlobalTheory.SymLiftOdd.symLift_unique hG P.isAb P.isLB hN U U' hU hU'
  obtain ⟨c, hcv⟩ := GlobalTheory.SymLiftOdd.exists_const P.isLB (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (GlobalTheory.SymLiftOdd.surj_fst hG P.isAb T)
    (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen P.L _ _ _ _ α (LB.invGen P.L _ _ α') hα (DVR.invGen_isGen _ _ _ _ hα'))
  refine fn_ext fun y _ => ?_
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  have r : ∀ w : T ⟶ P.A, val α (𝟙 _ ≫ (ptSecT P.A w).left) y J =
      val α' (𝟙 _ ≫ (ptSecT P.A w).left) y J * gm (𝟙 T.left) y ⊤ c := fun w => by
    have k := hcv _ (𝟙 _ ≫ (ptSecT P.A w).left) y J hJ'
    have k₂ : (𝟙 _ ≫ (ptSecT P.A w).left) ≫ (fst T P.A).left = 𝟙 T.left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_fst]; rfl
    rw [k₂, val_mul hJ', val_inv] at k
    rw [← k, mul_comm, inv_mul_cancel_right]
  have t : GlobalTheory.CommPairing.tval U (𝟙 _ ≫ (ptSecT P.A h).left) y J =
      GlobalTheory.CommPairing.tval U' (𝟙 _ ≫ (ptSecT P.A h).left) y J := val_corr hJ' hc _
  have e₁ := e _ (𝟙 _) y J hJ'
  have e₂ := e' _ (𝟙 _) y J hJ'
  rw [r, r, t] at e₁
  refine (Units.mul_left_inj (val α' (𝟙 _ ≫ (ptSecT P.A h).left) y J * gm (𝟙 T.left) y ⊤ c *
    val τ (𝟙 _ ≫ β.left) y J)).1 (e₁.trans ?_)
  simp only [Units.val_mul] at e₂ ⊢
  linear_combination (-(gm (𝟙 T.left) y ⊤ c).val) * e₂

end GlobalTheory.UPoinc.USum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isomorphism_mon_hom_descends_finite_extension : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.IsoFinExt.exists_finite_iso | exact GlobalTheory.IsoFinExt.exists_finite_iso | (intros; apply GlobalTheory.IsoFinExt.exists_finite_iso <;> assumption)
end


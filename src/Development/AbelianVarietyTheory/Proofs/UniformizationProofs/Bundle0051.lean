import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open GlobalTheory.ThetaPtMove

theorem gs_zero' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  rw [gs_eq r z U h, map_zero, map_zero]

theorem isUnit_top_of_ne_zero {K : Type} [Field K] {v : Γ(Spec (CommRingCat.of K), ⊤)} (hv : v ≠ 0) : IsUnit v := by
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 v
  have hc : c ≠ 0 := fun h => hv (by rw [h, map_zero])
  exact (IsUnit.mk0 c hc).map _

theorem exists_good_point (hG : GoodPtSt) (hB : PolBaseChangeSt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) {n : ℕ} (hn : 2 ≤ n) (hK : (n : K) ≠ 0)
    (th₀ : LB.Sec (LPow P.A P.L 1 (Over.mk t))) (h₀ : SecM.ofSec P.A th₀ ≠ 0) (a : Over.mk t ⟶ P.A) :
    ∃ x : Over.mk t ⟶ P.A, x ^ n = 1 ∧ ∀ z J, Good P.L z J →
      IsUnit (VVRank.sv P.A th₀ (ptSecT P.A (a * x)).left z J) := by
  obtain ⟨Q, g, hg, -, hm, t', ht'⟩ := hB S _ t P
  have hp : IsGrpPullback Q.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hm]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t', ht'⟩ : LBIso _ _)
  let τ : (baseOver (Spec (CommRingCat.of K))).left ⟶ (Over.mk t).left := 𝟙 _
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Spec (CommRingCat.of K))))
  have hτ : τ ≫ (Over.mk t).hom = (baseOver (Spec (CommRingCat.of K))).hom ≫ t := rfl
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw P.isLB Q.isLB th₀
  have hne : SecM.ofSec Q.A th ≠ 0 := fun e => h₀ (ThetaAct.sv_ext P.isLB fun y J hJ => by
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' Q.isLB y
    have q := hth _ χ y J J' hJ hJ'
    have q₀ : VVRank.sv Q.A th χ y J' = 0 :=
      (congrArg (fun u => ThetaAct.sv u χ y J') e).trans
        (gs_zero' χ y _ (hJ'.mem (fun _ : Fin 1 => (snd _ Q.A).left) χ))
    rw [h₂', q₀, MulZeroClass.mul_zero] at q
    exact q.trans (gs_zero' _ y _ (hJ.mem (fun _ : Fin 1 => (snd _ P.A).left) (𝟙 _))).symm)
  let a' : baseOver (Spec (CommRingCat.of K)) ⟶ Q.A :=
    Over.homMk (hg.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp t).symm)) (hg.lift_snd _ _ _)
  have ha : τ ≫ a.left = a'.left ≫ g := (Category.id_comp _).trans (hg.lift_fst _ _ _).symm
  obtain ⟨x', hx', ρ, v, -, hv, hv₀⟩ := hG K Q n hn hK th hne a'
  let x : Over.mk t ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    rw [Category.assoc, hg.w, ← Category.assoc, Over.w x']; exact Category.id_comp _)
  have hx : τ ≫ x.left = x'.left ≫ g := Category.id_comp _
  refine ⟨x, ?_, fun z J hJ => ?_⟩
  · have e₁ := over_pow hp τ hτ hx n
    rw [hx', ← over_one hp τ hτ] at e₁
    exact Over.OverMorphism.ext ((cancel_epi τ).1 e₁)
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' Q.isLB z
    have q := hth _ (𝟙 _ ≫ (ptSecT Q.A (a' * x')).left) z J J' hJ hJ'
    rw [sv_of_isValueAt hv (𝟙 _) z hJ', Category.assoc, psi_ptSec hp τ hτ (over_mul hp τ hτ ha hx)] at q
    have e : 𝟙 _ ≫ τ ≫ (ptSecT P.A (a * x)).left = (ptSecT P.A (a * x)).left :=
      (Category.id_comp _).trans (Category.id_comp _)
    rw [e] at q
    rw [q, gs_eq _ z ⊤ trivial]
    exact (Units.isUnit _).mul ((((isUnit_top_of_ne_zero hv₀).map _).map _).mul (Units.isUnit _))

theorem exists_generator_ne_zero (hS : SecBaseChangeSt) {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) :
    ∃ β : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)),
      (∀ s : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)), ∃ c : R,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
          sval s r z J = Geo.Tor.cst (r ≫ P.A.hom) z c * sval β r z J) ∧
      ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
        ∃ th : LB.Sec (LPow P.A P.L 1 (Over.mk t)), SecM.ofSec P.A th ≠ 0 ∧
          ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
            VVRank.sv P.A th r z J = sval β (r ≫ (snd (Over.mk t) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P 1 le_rfl (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left :=
    (Spec (CommRingCat.of R)).topIso.inv
  have hi : i₀ ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom ≫ i₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤ :=
    Over.homMk (P.A.hom ≫ i₀) (by rw [Category.assoc, hi, Category.comp_id])
  have uniq : ∀ {T : Over (Spec (CommRingCat.of R))} (p q : T ⟶ overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤),
      p = q := fun p q => Over.OverMorphism.ext (by
    rw [← Category.comp_id p.left, ← Category.comp_id q.left, ← hi', ← Category.assoc, ← Category.assoc, Over.w p,
      Over.w q])
  let β : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)) :=
    VVRank.pullTo (φ := fun _ : Fin 1 => (snd (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤) P.A).left)
      (ε := fun _ => 1) (b hq.default) (lift u (𝟙 P.A)).left
      (fun _ => congrArg (fun q => q.left) (lift_snd u (𝟙 P.A)))
  have key : ∀ (R' : Type) [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      ∃ th : LB.Sec (LPow P.A P.L 1 (Over.mk t)),
        (∀ r : Γ((Over.mk t).left, ⊤), r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk t)) = 0 → r = 0) ∧
        (∀ s : SecM P.A P.L 1 (Over.mk t), ∃ r : Γ((Over.mk t).left, ⊤), r • SecM.ofSec P.A th = s) ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
          VVRank.sv P.A th r z J = sval β (r ≫ (snd (Over.mk t) P.A).left) z J := by
    intro R' _ t
    obtain ⟨t', rfl⟩ : ∃ t' : Spec (CommRingCat.of R') ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left,
        t' ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = t :=
      ⟨t ≫ i₀, by rw [Category.assoc, hi, Category.comp_id]⟩
    obtain ⟨hli, hsp⟩ := hb R' t' (fun i => VVRank.pullS P.A _ (homAt t') (b i)) fun i =>
      VVRank.isPullSec_pullS _ _ _ _
    refine ⟨VVRank.pullS P.A _ (homAt t') (b hq.default), fun r hr => ?_, fun s => ?_, fun Z r z J hJ => ?_⟩
    · exact Fintype.linearIndependent_iff.1 hli (fun _ => r) (by rw [Fintype.sum_unique]; exact hr) hq.default
    · rw [Set.range_unique] at hsp
      exact Submodule.mem_span_singleton.1 (hsp.ge Submodule.mem_top)
    · have e : homAt t' ▷ P.A = snd (baseAt t') P.A ≫ lift u (𝟙 P.A) :=
        CartesianMonoidalCategory.hom_ext _ _ (uniq _ _) (by
          rw [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id])
      refine (VVRank.sv_pullS P.A _ (homAt t') _ r z hJ).trans (Eq.trans ?_ (VVRank.sval_pullTo _ _ _ _ z hJ).symm)
      rw [e, Over.comp_left, Category.assoc]
  refine ⟨β, fun s => ?_, fun K _ t => ?_⟩
  · obtain ⟨th, -, hsp, hv⟩ := key R (𝟙 _)
    obtain ⟨c, hc⟩ := hsp (SecM.ofSec P.A (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (Over.mk (𝟙 _)) P.A).left) s
      (snd (Over.mk (𝟙 _)) P.A).left fun _ => Category.comp_id _))
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 c
    refine ⟨c, fun Z r z J hJ => ?_⟩
    let u' : P.A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) := Over.homMk P.A.hom (Category.comp_id _)
    have e₁ : (r ≫ (lift u' (𝟙 P.A)).left) ≫ (snd (Over.mk (𝟙 _)) P.A).left = r := by
      rw [Category.assoc, ← Over.comp_left, lift_snd]; exact Category.comp_id _
    have e₂ : (r ≫ (lift u' (𝟙 P.A)).left) ≫ (fst (Over.mk (𝟙 _)) P.A).left = r ≫ P.A.hom := by
      rw [Category.assoc, ← Over.comp_left, lift_fst]; rfl
    have q := (congrArg (fun w => ThetaAct.sv w (r ≫ (lift u' (𝟙 P.A)).left) z J) hc).symm.trans
      (ThetaAct.sv_smul _ _ _ z hJ)
    have q₁ := (VVRank.sval_pullTo s _ (fun _ => Category.comp_id _) _ z hJ).symm.trans
      (q.trans (congrArg₂ (· * ·) rfl (hv Z _ z J hJ)))
    rw [e₁, e₂] at q₁
    exact q₁
  · obtain ⟨th, hli, -, hv⟩ := key K t
    refine ⟨th, fun e => ?_, hv⟩
    have h1 := hli 1 (by rw [e, smul_zero])
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h1
    exact one_ne_zero ((map_one _).symm.trans (h2.trans (map_zero _)))

theorem exists_secB_good (hL : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegPre R) (χ : D.X) : ∃ b : D.SecB 1 χ,
      (∀ σ : D.SecB 1 χ, ∃ c : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
          sval σ r z J = Geo.Tor.cst (r ≫ D.P.A.hom) z c * sval b r z J) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (n : ℕ), 2 ≤ n →
        (n : K) ≠ 0 → ∀ a : Over.mk t ⟶ D.P.A, ∃ x : Over.mk t ⟶ D.P.A, x ^ n = 1 ∧
          ∀ z J, Good D.P.L z J → IsUnit (sval b (a * x).left z J) := by
  have hM := D.P.isLB
  obtain ⟨β, hβ, hβ'⟩ := exists_generator_ne_zero hL.secBaseChange D.P
  obtain ⟨ξ₀, hξ₀⟩ := exists_gen_of_local D.P.L hM (K := Fin 2)
    ![(D.c χ).left, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left] ![-1, 1]
  obtain ⟨ξ, hξ, vξ⟩ := VVRank.exists_gen_pullTo (φ' := ![(SectionScalarValuation.cQ D D.P.A χ).left, (1 : D.P.A ⟶ D.P.A).left]) ξ₀ hξ₀
    D.P.A.hom (fun i => by
      fin_cases i
      · rfl
      · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toUnit D.P.A)))
  let τ : D.P.A ⟶ D.P.A := 𝟙 _ * SectionScalarValuation.cQ D D.P.A χ
  let τ' : D.P.A ⟶ D.P.A := 𝟙 _ * (SectionScalarValuation.cQ D D.P.A χ)⁻¹
  have hτ : ∀ {T : Over (Spec (CommRingCat.of R))} (y : T ⟶ D.P.A), y ≫ τ = y * SectionScalarValuation.cQ D T χ := fun y => by
    rw [MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
  have hττ : τ ≫ τ' = 𝟙 _ := by
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, SectionScalarValuation.comp_cQ, mul_inv_cancel_right]
  obtain ⟨b, hb⟩ := exists_sec hM (φ' := D.famφB χ) (ε' := DegPre.famε 1) (fun U _ h => by
    have p := SectionScalarValuation.prod_famB D (𝟙 D.P.A) χ 1 h
    simp only [Over.id_left, Category.id_comp] at p
    rw [p, Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
    simp [τ, _root_.mul_assoc]) (pullMulSec β τ.left ξ hξ)
  have vb : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval b r z J = sval β (r ≫ τ.left) z J * (val ξ r z J).val := fun Z r z J hJ =>
    (hb Z r z J hJ).trans (sval_pullMulSec _ _ _ hξ r z hJ)
  refine ⟨b, fun σ => ?_, fun K _ _ t n hn hK a => ?_⟩
  · obtain ⟨s, hs⟩ := exists_sec hM (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => 1) (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D τ' χ 1 h
      have e : τ' * SectionScalarValuation.cQ D D.P.A χ = 𝟙 _ := inv_mul_cancel_right _ _
      rw [e] at p
      rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
      refine (congrArg₂ (· * ·) p rfl).trans ?_
      simp [_root_.mul_assoc, mul_left_comm]) (pullMulSec σ τ'.left _ (invGen_isGen _ _ _ _ hξ))
    obtain ⟨c, hc⟩ := hβ s
    refine ⟨c, fun Z r z J hJ => ?_⟩
    have q := (hc Z (r ≫ τ.left) z J hJ).symm.trans ((hs Z _ z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ))
    rw [val_inv, vξ _ _ z J hJ, Category.assoc, Category.assoc, ← Over.comp_left, hττ, Over.w τ, Over.id_left,
      Category.comp_id, ← vξ _ _ z J hJ] at q
    rw [vb Z r z J hJ, ← _root_.mul_assoc, q, Units.inv_mul_cancel_right]
  · obtain ⟨th, h₀, hth⟩ := hβ' K t
    obtain ⟨x, hx, hu⟩ := exists_good_point hL.goodPt hL.polBaseChange D.P t hn hK th h₀ (a * SectionScalarValuation.cQ D _ χ)
    refine ⟨x, hx, fun z J hJ => ?_⟩
    have q := hu z J hJ
    rw [hth _ _ z J hJ, ptSecT_snd, mul_right_comm, ← hτ, Over.comp_left] at q
    rw [vb _ _ z J hJ]
    exact q.mul (Units.isUnit _)

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine (Z.mem_basicOpen ((r.app U).hom a) z h).symm.trans ?_
  exact Iff.of_eq (congrArg (z ∈ ·) (Scheme.preimage_basicOpen r a).symm)

theorem exists_gen_of_isUnit {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {O : Type} [CommRing O] [IsLocalRing O]
    (m : Spec (CommRingCat.of O) ⟶ Y)
    (h : ∀ z J, Good L z J → IsUnit (sval s (Spec.map (CommRingCat.ofHom (residue O)) ≫ m) z J)) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of O)) (z : Z) (J), Good L z J →
        (val t r z J).val = sval s (r ≫ m) z J := by
  let s' := pullSec L φ ε s m
  let z₀ : Spec (CommRingCat.of (ResidueField O)) := closedPoint (ResidueField O)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' hL z₀
  have h₀ := h z₀ J₀ hJ₀
  rw [← SectionScalarValuation.sval_pullSec φ ε s m _ z₀ hJ₀] at h₀
  have h₁ := (isUnit_gs_iff _ z₀ _ (hJ₀.mem (fun k => m ≫ φ k) _) _).1 h₀
  have e : Spec.map (CommRingCat.ofHom (residue O)) z₀ = closedPoint O := IsLocalRing.comap_closedPoint (residue O)
  rw [e] at h₁
  have h₂ := eq_top_of_closedPoint_mem _ h₁
  have hu : ∀ j, IsUnit (s'.f j) := fun j => (Spec (CommRingCat.of O)).toRingedSpace.isUnit_of_isUnit_germ _ _
    fun y hy => by
      have hy₀ := h₂.ge (Set.mem_univ y)
      have hy₁ := Scheme.basicOpen_le _ _ hy₀
      have q := sec_trans s' (𝟙 _) y hy hy₁
      exact (congrArg IsUnit ((gs_eq (𝟙 _) y (LB.wchart L (fun k => m ≫ φ k) j) hy _).symm.trans q)).mpr
        ((Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) y _ hy₁ _).2 hy₀))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun Z r z J hJ => ?_⟩
  exact (gs_unit r z _ (hJ.mem (fun k => m ≫ φ k) r) _).symm.trans (SectionScalarValuation.sval_pullSec φ ε s m r z hJ)

end GlobalTheory.UT.ExactTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.AdicValSum

theorem nullV_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) : NullV v x := by
  classical
  intro q
  obtain ⟨S, hS⟩ := h q
  refine S.finite_toSet.subset fun i hi => ?_
  by_contra hiS
  have h1 := hS S subset_rfl
  have h2 := hS (insert i S) (Finset.subset_insert i S)
  have hx : x i = (s - ∑ j ∈ S, x j) - (s - ∑ j ∈ insert i S, x j) := by
    rw [Finset.sum_insert hiS]
    ring
  have h3 : (q : WithTop ℚ) ≤ v (x i) := by
    rw [hx]
    exact le_trans (le_min h1 h2) (AddValuation.map_sub v _ _)
  exact absurd hi (not_lt.mpr h3)

theorem exists_le_on_finset {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (t : Finset F) :
    ∃ c : ℚ, ∀ y ∈ t, (c : WithTop ℚ) ≤ v y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d : ℚ, (d : WithTop ℚ) ≤ v a := by
      by_cases htop : v a = ⊤
      · exact ⟨0, htop ▸ le_top⟩
      · exact ⟨(v a).untop htop, by rw [WithTop.coe_untop]⟩
    refine ⟨min c d, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_right c d)) hd
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_left c d)) (hc y hy)

theorem sumV_of_sumI {V : Type} [CommRing V] (I : Ideal V) {F : Type} [Field F] [Module V F] (φ : V → F)
    (hφ : ∀ (a : V) (y : F), a • y = φ a * y) (v : AddValuation F (WithTop ℚ))
    (hv : ∀ (n : ℕ) (a : V), a ∈ I ^ n → ((n : ℚ) : WithTop ℚ) ≤ v (φ a))
    {Ix : Type} {x : Ix → F} {s : F} (h : SumI I x s) : SumV v x s := by
  obtain ⟨N, hNfg, -, -, hconv⟩ := h
  obtain ⟨G, rfl⟩ := hNfg
  obtain ⟨c, hc⟩ := exists_le_on_finset v G
  have h0 : ∀ a : V, (0 : WithTop ℚ) ≤ v (φ a) := by
    intro a
    have := hv 0 a (by simp)
    simpa using this
  have hN : ∀ y ∈ Submodule.span V (G : Set F), (c : WithTop ℚ) ≤ v y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simp
    | add y z _ _ hy hz => exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
    | smul a y _ hy =>
      rw [hφ, AddValuation.map_mul]
      simpa using add_le_add (h0 a) hy
  have hIN : ∀ n : ℕ, ∀ z ∈ I ^ n • Submodule.span V (G : Set F), (((n : ℚ) + c : ℚ) : WithTop ℚ) ≤ v z := by
    intro n z hz
    refine Submodule.smul_induction_on hz (fun r hr y hy => ?_) (fun y z hy hz => ?_)
    · rw [hφ, AddValuation.map_mul, WithTop.coe_add]
      exact add_le_add (hv n r hr) (hN y hy)
    · exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
  intro q
  obtain ⟨S, hS⟩ := hconv ⌈q - c⌉₊
  refine ⟨S, fun T hT => le_trans ?_ (hIN _ _ (hS T hT))⟩
  have : q ≤ (⌈q - c⌉₊ : ℚ) + c := by linarith [Nat.le_ceil (q - c)]
  exact WithTop.coe_le_coe.mpr this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (x : Ix → F) (s : F), SumF (maximalIdeal V) F x s → SumV v x s ∧ NullV v x := by
  intro V _ _ _ ϖ hϖ F _ _ v hval Ix x s hsum
  letI : Module V F := Module.compHom F (algebraMap V (FractionRing V))
  have hI : SumI (maximalIdeal V) x s := hsum
  have hV : SumV v x s := by
    refine sumV_of_sumI (maximalIdeal V) (fun a => algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))
      (fun a y => Algebra.smul_def _ _) v ?_ hI
    intro n a ha
    by_cases ha0 : a = 0
    · subst ha0
      simp
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : ϖ ^ n ∣ ϖ ^ k := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      exact (Units.dvd_mul_left).mp ha
    have hnk : n ≤ k := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
    have hhv : HasVal ϖ (algebraMap V (FractionRing V) (↑u * ϖ ^ k)) (k : ℤ) :=
      ⟨u, by rw [map_mul, map_pow, zpow_natCast, mul_comm]⟩
    rw [hval _ _ hhv, WithTop.coe_le_coe]
    exact_mod_cast hnk
  exact ⟨hV, nullV_of_sumV hV⟩

end GlobalTheory.UT.AdicValSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PrimGen

open GlobalTheory.FieldBaseChange

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_lower (v : AddValuation F (WithTop ℚ)) {n : ℕ} (c : Fin n → F) :
    ∃ r : ℚ, ∀ i, (r : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (v (c i)).untopD 0).bddBelow
  refine ⟨m, fun i => ?_⟩
  have h := hm ⟨i, rfl⟩
  cases e : v (c i) with
  | top => exact le_top
  | coe y =>
    simp only [e, WithTop.untopD_coe] at h
    exact WithTop.coe_le_coe.2 h

theorem exists_vge (U : UnifPre (maximalIdeal V) D A G) (v : AddValuation F (WithTop ℚ)) {k : ℕ}
    {σ : U.SecGF F k} {s : Fam D.toPre F k} (h : U.ExpandsG F k σ s) (α : D.toPre.X) :
    ∃ r : ℚ, VGe D F v k α (s.s α) r := by
  obtain ⟨n, c, x, -, -, hs⟩ := (expandsG_iff U F k σ s).1 h
  obtain ⟨r, hr⟩ := exists_lower v c
  refine ⟨r, n, c, fun i => (x i).2 α,
    fun i => termPull D.toPre (FractionRing V) F k α (genericTerm D k α ((x i).2 α)), fun i => ?_, hr, fun j => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ =>
      ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval ((x i).2 α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing V) F))))))).symm
  · exact (congrArg (chartLin (famBase D.toPre F) _ j) (hs α)).trans (map_sum (chartLin (famBase D.toPre F) _ j) _ _)

theorem exists_prim_span (hU : UUStatement) {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) [IsAlgClosed F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) :
    ∃ ϑ : Fam D.toPre F 1, Prim D Q v ϑ ∧
      ∀ s : Fam D.toPre F 1, (∃ r : ℚ, VGe D F v 1 0 (s.s 0) r) → ∃ c : F, s = c • ϑ := by
  classical
  obtain ⟨b, hli, hb, hsp⟩ := hU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) 1 le_rfl
  have : Subsingleton (Fin (1 ^ (D.toPre.rank + D.toPre.P.g))) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ (D.toPre.rank + D.toPre.P.g)) := ⟨0, by rw [one_pow]; exact one_pos⟩
  have hsp' : ∀ s, NuGe D Q F v 1 s 0 → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ s = c • b i₀ := fun s hs => by
    obtain ⟨c, hc, e⟩ := (hsp s).1 hs
    exact ⟨c i₀, hc i₀, e.trans (Fintype.sum_subsingleton _ i₀)⟩
  refine ⟨b i₀, ⟨hb i₀, fun r hr h => ?_⟩, ?_⟩
  · obtain ⟨ζ, s', hζ, hs', e⟩ := (n1c V ϖ hϖ D Q hQ F v hv 1 le_rfl (b i₀) (hb i₀)).1 ⟨r, hr, h⟩
    obtain ⟨c, hc, rfl⟩ := hsp' s' hs'
    rw [isSmul_iff, smul_smul] at e
    have e1 : ζ * c = 1 := smul_left_injective F (hli.ne_zero i₀) (e.symm.trans (one_smul F _).symm)
    have h0 : (0 : WithTop ℚ) < v (ζ * c) := by
      rw [AddValuation.map_mul]
      exact lt_add_of_lt_of_nonneg hζ hc
    rw [e1, AddValuation.map_one] at h0
    exact lt_irrefl _ h0
  · rintro s ⟨r, hr⟩
    have h1 : NuGe D Q F v 1 s (-(|r| + 1)) := by
      rw [n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) s]
      intro α hα
      obtain rfl := Finset.mem_singleton.1 hα
      refine hr.mono ?_
      rw [QForm.Q_zero hϖ D hQ]
      have := neg_abs_le r
      simp only [Int.cast_zero, zero_div, add_zero]
      linarith
    obtain ⟨ζ, hζ0, hζ⟩ := exists_val_eq hv (r := |r| + 1) (by positivity)
    have h2 := NuGe.smul Q hζ.ge ((isSmul_iff ζ s _).2 rfl) h1
    rw [neg_add_cancel] at h2
    obtain ⟨c, -, e⟩ := hsp' _ h2
    exact ⟨ζ⁻¹ * c, by rw [mul_smul, ← e, inv_smul_smul₀ hζ0]⟩

end GlobalTheory.UT.PrimGen

namespace GlobalTheory.UT

open GlobalTheory.FieldBaseChange

theorem exists_prim_generator : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ : W0 U.toUnifPre, w₀.IsGen → ∃ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ IsGenSec A.A A.L 1 th := by
  intro hL _ _ _ hU V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ hw
  obtain ⟨ϑ, hp, hsp⟩ := PrimGen.exists_prim_span hU hϖ hQ hv
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 1) le_rfl w₀ hw
  refine ⟨e.symm ϑ, ϑ, (he _ _).2 (e.apply_symm_apply ϑ), hp, fun t => ?_⟩
  obtain ⟨σ, -, hσ⟩ := (he t _).2 rfl
  obtain ⟨c, hc⟩ := hsp _ (PrimGen.exists_vge U.toUnifPre v hσ 0)
  have ht : t = (c • e.symm ϑ : SecOver (abelianBase A F) _) :=
    e.injective (hc.trans (by rw [map_smul, e.apply_symm_apply]))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c, fun j => ?_⟩
  rw [ht]
  rfl

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LbIsoPwPullPowLocalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  first | exact @GlobalTheory.UU.lbIso_pw_pull_pow_local | exact GlobalTheory.UU.lbIso_pw_pull_pow_local | (intros; apply GlobalTheory.UU.lbIso_pw_pull_pow_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem GlobalTheory.UU.torus_coord_add : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) (χ : D.X) (z : T.left) (J), Good D.P.L z J → val (g.t χ) (x * y).left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toUnit _ ≫ D.c χ) ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)) = val (g.t χ) x.left z J * val (g.t χ) y.left z J) :=
  fun hG _ _ _ _ _ _ _ _ _ g _ x y χ z J hJ => GlobalTheory.TorusCoord.val_t_mul_points g hG χ x y z J hJ
end


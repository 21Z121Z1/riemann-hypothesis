import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3177
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalProductIdentityOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.CubInt

theorem cubProd_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b cχ : 𝟙_ (Over (Sp V)) ⟶ D.P.A),
    b ^ N = 1 → ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit (TF (R := V) (FractionRing V)) ≫ cχ)
        (toUnit (TF (R := V) (FractionRing V)) ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) =
      val χt (toUnit (TF (R := V) (FractionRing V))).left z J ^ N) →
    ∀ (T : Over (Sp V)) (z : T.left) J, Good D.P.L z J →
      ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit T ≫ cχ) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χt T.hom z J ^ N := by
  intro V _ _ D N b cχ hbN χt ht hgen T z J hJ
  have G := (grep_cubProd cχ b N).mul ((SymFrame.grep_gen χt ht (𝟙 _)).pow N).inv
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => Eq.trans (by
      have hK : ∏ k : Fin 4, h (𝟙 _ ≫ ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] k) ^ DegPre.gtε k =
          (h (cχ * b).left)⁻¹ * h cχ.left * h b.left *
            (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ := by
        rw [Fin.prod_univ_four, ← SymFrame.eta_eq]
        simp [DegPre.gtε, zpow_neg, zpow_one]
      have hP : ∀ i, h (cχ * b ^ i * b).left * (h (cχ * b ^ i).left)⁻¹ * (h (cχ * b).left)⁻¹ *
          (h (b ^ i * b).left)⁻¹ * h cχ.left * h (b ^ i).left * h b.left *
          (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ =
          (h (cχ * b ^ (i + 1)).left / h (b ^ (i + 1)).left) / (h (cχ * b ^ i).left / h (b ^ i).left) *
            ((h (cχ * b).left)⁻¹ * h cχ.left * h b.left *
              (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹) := by
        intro i
        rw [_root_.mul_assoc cχ, ← pow_succ]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_div]
        abel
      rw [Finset.prod_congr rfl (fun i _ => hP i), Finset.prod_mul_distrib,
        Finset.prod_range_div (fun i => h (cχ * b ^ i).left / h (b ^ i).left), Finset.prod_const, Finset.card_range, hK,
        hbN, pow_zero]
      simp) (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  have hρ1 : ρ = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' D.P.isLB z₀
    have a := vs _ (toUnit (TF (R := V) (FractionRing V))) z₀ J₀ hJ₀
    rw [hρ _ _ z₀ J₀ hJ₀, val_one, _root_.mul_one] at a
    simp only [Category.comp_id] at a
    have a1 : gm (toUnit (TF (R := V) (FractionRing V))).left z₀ ⊤ ρ = 1 := by
      rw [a]
      exact mul_inv_eq_one.mpr (hgen z₀ J₀ hJ₀)
    have c := gm_top_eq ρ z₀
    rw [a1, Units.val_one, cst_eq, ← map_one (cstH z₀)] at c
    have d := cstH_inj z₀ c
    rw [← map_one (algebraMap V (FractionRing V))] at d
    have e := IsFractionRing.injective V (FractionRing V) d
    apply Units.ext
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
    apply hinj
    rw [Units.val_one, map_one]
    exact e.symm
  have a := vs T (toUnit T) z J hJ
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, hρ1, map_one] at a
  simp only [Category.comp_id] at a
  exact mul_inv_eq_one.mp a.symm

end GlobalTheory.Poinc.Sep.CubInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

section Power

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] {r : ℕ}

theorem isMonHom_prod_zpow {K : Type} [Fintype K] (a : K → (G ⟶ G₀)) (ha : ∀ i, IsMonHom (a i)) (n : K → ℤ) :
    IsMonHom (∏ i, a i ^ n i) :=
  isMonHom_of_mul _ fun T x z => by
    rw [comp_prod_zpow, comp_prod_zpow, comp_prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := ha i
    rw [MonObj.mul_comp, mul_zpow]

theorem comp_zpow' {T T' : Over S} (p : T' ⟶ T) (y : T ⟶ G) (n : ℤ) : p ≫ y ^ n = (p ≫ y) ^ n := by
  simpa using comp_prod_zpow (K := Unit) p (fun _ => y) (fun _ => n)

theorem prod_zpow_same {M K : Type} [CommGroup M] [Fintype K] (a : M) (f : K → ℤ) : ∏ i, a ^ f i = a ^ ∑ i, f i := by
  have h := map_prod (zpowersHom M a) (fun i => Multiplicative.ofAdd (f i)) Finset.univ
  rw [← ofAdd_sum] at h
  exact h.symm

theorem exists_vec (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u) (v : Fin r → ℤ) :
    ∃ i : G₀ ⟶ G, IsMonHom i ∧ ∀ b, i ≫ q b = 𝟙 G₀ ^ v b := by
  obtain ⟨i, hi, -⟩ := huniv G₀ fun b => 𝟙 G₀ ^ v b
  refine ⟨i, isMonHom_of_mul _ fun T x z => (huniv T fun b => (x * z) ^ v b).unique (fun b => ?_) (fun b => ?_), hi⟩
  · rw [Category.assoc, hi, comp_zpow', Category.comp_id]
  · have := hq b
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, comp_zpow', comp_zpow', Category.comp_id, Category.comp_id,
      mul_zpow]

theorem lam_of_tens {L₀ : LB G₀.left} (hL : L₀.IsLB) (hΘ : ∃ t : LB.Gen (Theta G₀ L₀), t.IsGen) (q : Fin r → (G ⟶ G₀))
    (hq : ∀ u, IsMonHom (q u)) (W : Matrix (Fin r) (Fin r) ℤ) {c : Pic G.left}
    (hc : c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (q a) (q b)) {T : Over S} (x y : T ⟶ G) :
    lam c x y = ∑ a, ∑ b, (W + W.transpose) a b • lam (cls L₀ hL) (x ≫ q a) (y ≫ q b) := by
  have hp : ∀ h : T ⟶ G, pull h.left c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (h ≫ q a) (h ≫ q b) := fun h => by
    rw [hc]
    simp only [map_sum, map_zsmul, pull_lam]
  have hm : ∀ i, (x * y) ≫ q i = x ≫ q i * y ≫ q i := fun i => by
    have := hq i
    exact MonObj.mul_comp _ _ _
  have ho : ∀ i, (1 : T ⟶ G) ≫ q i = 1 := fun i => by
    have := hq i
    exact MonObj.one_comp _
  have e : ∑ i, ∑ j, W i j • lam (cls L₀ hL) (y ≫ q i) (x ≫ q j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls L₀ hL) (x ≫ q i) (y ≫ q j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (y ≫ _)]
  conv_lhs => rw [lam]
  simp only [hp, hm, ho, lam_one_left, lam_mul_left hL hΘ, RosatiTens.lam_mul_right hL hΘ, smul_add,
    Finset.sum_add_distrib, Matrix.add_apply, add_smul, smul_zero, Finset.sum_const_zero]
  rw [e]
  abel

end Power

theorem exists_tens (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D D₀ : DegData R (maximalIdeal R))
    (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀]
    (hG : IsSemiAbelian G) (hG₀ : IsSemiAbelian G₀) (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀)
    {r : ℕ} (W N : Matrix (Fin r) (Fin r) ℤ) (hN : (W + W.transpose) * N = 1) (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u)
    (hc : cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b))
    (h : Fin r → (D₀.toPre.X →+ D.toPre.X)) (hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (h u))
    (xe : D.toPre.X ≃+ (Fin r → D₀.toPre.X))
    (hxe : ∀ mu, xe.symm mu = ∑ u, h u (∑ v, (W + W.transpose) u v • mu v)) :
    ∃ T : Tens D₀.toPre D.toPre W, T.xe = xe := by
  have hA := hR.1
  set Sm := W + W.transpose with hSm
  have hSs : ∀ a b, Sm a b = Sm b a := fun a b => by simp [hSm, add_comm]
  have hN' : N * Sm = 1 := mul_eq_one_comm.1 hN
  have SN : ∀ a c, ∑ b, Sm a b * N b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN, Matrix.one_apply]
  have NS : ∀ a c, ∑ b, N a b * Sm b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN', Matrix.one_apply]
  have hΘ₀ : ∃ t : LB.Gen (Theta G₀ U₀.LG.L), t.IsGen := ⟨U₀.cubG.t, U₀.cubG.isGen⟩
  have hΘ : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have P := fun {T : Over (Sp R)} (x y : T ⟶ G) => lam_of_tens U₀.LG.isLB hΘ₀ q hq W hc x y
  rw [← hSm] at P
  have zr : ∀ {T : Over (Sp R)} (x z : T ⟶ G₀) (n : ℤ), lam (cls U₀.LG.L U₀.LG.isLB) x (z ^ n) =
      n • lam (cls U₀.LG.L U₀.LG.isLB) x z := fun x z n => by
    simpa using RosatiTens.lam_prod_right (κ := Unit) U₀.LG.isLB hΘ₀ x (fun _ => z) (fun _ => n)
  choose j hj jq using fun a => exists_vec q hq huniv fun b => N b a
  choose inc hinc iq using fun a => exists_vec q hq huniv fun b => if a = b then 1 else 0
  let rr' : Fin r → (G ⟶ G₀) := fun a => ∏ b, q b ^ Sm a b
  have hrr : ∀ a, IsMonHom (rr' a) := fun a => isMonHom_prod_zpow q hq _
  have iq₁ : ∀ a, inc a ≫ q a = 𝟙 _ := fun a => by rw [iq, if_pos rfl, zpow_one]
  have jr : ∀ a, j a ≫ rr' a = 𝟙 _ := fun a => by
    simp only [rr', comp_prod_zpow, jq, ← zpow_mul, prod_zpow_same, mul_comm (N _ _), SN]
    simp
  have adjq : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (q a) (j a) := fun a T x z => by
    simp only [P, Category.assoc, jq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, SN]
    simp
  have adjr : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (rr' a) (inc a) := fun a T x z => by
    simp only [P, Category.assoc, iq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, rr', comp_prod_zpow,
      RosatiTens.lam_prod_left U₀.LG.isLB hΘ₀]
    simp [hSs a]
  have hNs : ∀ a b, N a b = N b a := fun a b => by
    have e₁ : Sm.transpose = Sm := Matrix.ext fun a b => hSs b a
    have e₂ : N.transpose * Sm = 1 := by rw [← e₁, ← Matrix.transpose_mul, hN, Matrix.transpose_one]
    have e₃ : N.transpose = N := by rw [← Matrix.mul_one N.transpose, ← hN, ← Matrix.mul_assoc, e₂, Matrix.one_mul]
    exact congrFun (congrFun e₃ b) a
  let f : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.2 ≫ j ab.1) ^ W ab.1 ab.2
  let f' : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.1 ≫ j ab.2) ^ W ab.1 ab.2
  have hf : IsMonHom f := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have hf' : IsMonHom f' := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have ff : f * f' = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [f, f', MonObj.mul_comp, prod_zpow_comp, Category.assoc, jq, comp_zpow', Category.comp_id, ← zpow_mul]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Finset.prod_comm, ← Finset.prod_mul_distrib]
    simp only [prod_zpow_same, ← zpow_add, ← Finset.sum_add_distrib, ← mul_add]
    have : ∀ b, ∑ a, N c a * (W a b + W b a) = if c = b then 1 else 0 := fun b => NS c b
    simp [this]) (fun c => Category.id_comp _)
  have adjf : AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' := fun T x z => by
    simp only [f, f', comp_prod_zpow, RosatiTens.lam_prod_left U.LG.isLB hΘ, RosatiTens.lam_prod_right U.LG.isLB hΘ]
    refine Finset.sum_congr rfl fun ab _ => congrArg _ ?_
    rw [← Category.assoc, ← Category.assoc, adjq, lam_comm _ _ z, adjq, lam_comm]
  have primf : cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f := by
    simp only [f, RosatiTens.lam_prod_right U.LG.isLB hΘ, adjq _ _, Category.id_comp, Fintype.sum_prod_type]
    exact hc
  have idq : ∏ a, (q a ≫ inc a) ^ (1 : ℤ) = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [prod_zpow_comp, Category.assoc, iq, comp_zpow', Category.comp_id]
    simp) (fun c => Category.id_comp _)
  choose qB hqB oq using fun a => exists_abelian_hom R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre (q a) (hq a)
  choose jB hjB oj using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  choose iB hiB oi using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (inc a) (hinc a)
  choose k tk using fun a => unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  have un := over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have un₀ := over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have oz : ∀ m : ℤ, Over₀ U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (𝟙 _ ^ m) := fun m => by
    simpa using GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.over_id
  have tz : ∀ m : ℤ, OnTorus U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (fun χ => m • χ) := fun m => by
    simpa using GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.onTorus_id
  have iqB : ∀ a b, iB a ≫ qB b = 𝟙 _ ^ (if a = b then 1 else 0 : ℤ) := fun a b =>
    (un₀ _).1 _ _ (iq a b ▸ FactorPol.over_comp (oi a) (oq b)) (oz _)
  have jqB : ∀ a b, jB a ≫ qB b = 𝟙 _ ^ N b a := fun a b =>
    (un₀ _).1 _ _ (jq a b ▸ FactorPol.over_comp (oj a) (oq b)) (oz _)
  have idB : ∏ a, (qB a ≫ iB a) ^ (1 : ℤ) = 𝟙 _ := (un _).1 _ _
    (idq ▸ GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D D A A G G U.toUnifPre U.toUnifPre _ (fun _ => 1) _ _ fun a => FactorPol.over_comp (oq a) (oi a))
    FactorPol.over_id
  have kh : ∀ a b χ, k a (h b χ) = N b a • χ := fun a b =>
    congrFun ((un₀ _).2 _ _ (jq a b ▸ FactorPol.onTorus_comp (tk a) (hh b)) (tz _))
  have xk : ∀ y a, xe y a = k a y := fun y a => by
    obtain ⟨mu, rfl⟩ := xe.symm.surjective y
    rw [AddEquiv.apply_symm_apply, hxe]
    simp only [map_sum, kh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hNs _ a, NS]
    simp
  have extB : ∀ {T : Over (Sp R)} (x x' : T ⟶ D.toPre.P.A), (∀ a, x ≫ qB a = x' ≫ qB a) → x = x' := fun x x' e => by
    rw [← Category.comp_id x, ← Category.comp_id x', ← idB, comp_prod_zpow, comp_prod_zpow]
    simp only [← Category.assoc, e]
  have per := fun a => GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (inc a) (j a) (hinc a) (hj a) (iq₁ a) (adjq a) (qB a) (h a)
    (k a) ⟨hq a, hqB a, oq a, hh a⟩ (tk a)
  have adjB := fun a => GlobalTheory.T.adjoint_abelianParts_of_uniformised_retract R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (rr' a) (inc a) (j a) (hq a) (hrr a) (hinc a) (hj a) (iq₁ a)
    (jr a) (adjq a) (adjr a) (qB a) (jB a) (hqB a) (hjB a) (oq a) (oj a)
  have cz : ∀ (m : ℤ) χ, D₀.toPre.c (m • χ) = D₀.toPre.c χ ^ m := fun m χ => by
    let φ : Multiplicative D₀.toPre.X →* (𝟙_ (Over (Sp R)) ⟶ D₀.toPre.P.A) :=
      MonoidHom.mk' (fun y => D₀.toPre.c y.toAdd) fun a b => D₀.toPre.c_add _ _
    exact map_zpow φ (Multiplicative.ofAdd χ) m
  have ch : ∀ a χ, D.toPre.c (h a χ) = D₀.toPre.c χ ≫ jB a := fun a χ => extB _ _ fun b => by
    rw [← (per b).1, kh, cz, Category.assoc, jqB, comp_zpow', Category.comp_id, hNs]
  obtain ⟨w, hw, hψ⟩ := GlobalTheory.T.powerData_tensorBundleIso_with_psi_values R D.toPre D₀.toPre r W qB jB (fun a => h a) (fun a => k a) ch (fun a => (per a).1)
    (fun a => (per a).2) (fun a => GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint R _ _ _ _ (hqB a) (hjB a) (adjB a)) (GlobalTheory.T.isBiextensionExpansionGenerator_of_tauBimult R _ D.tau_bimult _ _ _ _ _)
    (GlobalTheory.T.thetaMultiplier_eq_of_primitive_adjoint_bundle R hR D A G hG U f f' hf hf' ff adjf primf _ _
      (GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.over_comp (oq ab.2) (oj ab.1))
      (GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.onTorus_comp (hh ab.1) (tk ab.2)))
  have lf : ∀ {T : Over (Sp R)} (y : Fin r → (T ⟶ D₀.toPre.P.A)) b, (∏ a, (y a ≫ iB a) ^ (1 : ℤ)) ≫ qB b = y b := fun y b => by
    simp only [prod_zpow_comp, Category.assoc, iqB, comp_zpow', Category.comp_id]
    simp
  exact ⟨{ pr := qB, pr_hom := hqB, xe := xe, w := w, w_gen := hw
           lim := Fan.IsLimit.mk _ (fun s => (∏ a, (s.proj a ≫ iB a) ^ (1 : ℤ) : s.pt ⟶ D.toPre.P.A)) (fun s b => lf _ b)
             (fun s m hm => extB _ _ fun b => (hm b).trans (lf _ b).symm)
           c_pr := fun z a => by rw [xk, (per a).1]
           psi := fun y z J J' hJ hJ' => (hψ y z J J' hJ hJ').trans (congrArg _ (Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => by rw [xk, xk])) }, rfl⟩

end GlobalTheory.Mum.PowData

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
  ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Eq8 in

theorem GlobalTheory.Mum.PowData.sharpRef_of_characters : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN _ _ D₀ e₀ hRef G₀ _ _ A₀ U₀ y α α₂ hG₀ hα hsq hlb P c φc φ₂ hφ hφsq hφlb _ pr _ _
    hPL G _ _ hG D U q hq huniv hcomp ch hch e he
  have hR : Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  have hc := GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum g n o ζ F W V₁ hR D D₀ P A₀ G G₀ hG U U₀ y α α₂ hα hsq hlb c φc φ₂ hφ hφsq hφlb pr hPL q hq hcomp
  have hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (ch u) := fun u => by
    obtain ⟨h, th⟩ := unifPre_hom_character_const V₁ _ hR.1 D D₀ P A₀ G G₀ U.toUnifPre U₀.toUnifPre (q u) (hq u)
    rwa [torMatch_unique V₁ hR G₀ hG₀ D₀ A₀ U₀ V₁ hR G hG D P U _ _ Function.injective_id _ _ (hch u)
      (GlobalTheory.T.toricTorsionMatch_of_characterMap_on_torus V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ (q u) (hq u) h th)]
  obtain ⟨T, hT⟩ := GlobalTheory.Mum.PowData.exists_tens V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ W (W + W.transpose)⁻¹
    (Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)) q hq huniv hc ch hh
    (e.symm.trans (AddEquiv.piCongrRight fun _ => e₀.symm)) (fun mu => by
      show e (fun a => e₀ (mu a)) = _
      simp [he])
  refine GlobalTheory.T.sharpRef_of_refines_tensor W V Q V₁ ρ D₀.toPre D.toPre e₀ hRef T e fun mu a => ?_
  simp [hT]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.MulDeg

variable {R : Type} [CommRing R] [IsDomain R]

def tau3 (D : DegPre R) (s a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi s) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)

theorem corr_even_degenerationData_negPoint (D : DegPre R) (h : D.PsiEven) (a m : D.X) (hm : m = -a) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi m) (LB.pullGen D.P.L _ _ D.sym (D.xK a))) (D.psi a) := by
  subst hm
  exact h a

theorem corr_bimultiplicative_degenerationData_sums (D : DegPre R) (h : D.TauBimult) (a a' b s t u v : D.X) (hs : s = a + a') (ht : t = a + a' + b)
    (hu : u = a + b) (hv : v = a' + b) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D t s b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)))
      (LB.mulGen D.P.L _ _ _ _ (tau3 D u a b) (tau3 D v a' b)) := by
  subst hs ht hu hv
  exact h a a' b

theorem corr_balanced_degenerationData_rosati (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (p q : D.X → D.X) (h : D.TauBal f g p q)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h1 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (y y' a a' s t : D.X) (ha : a = p y) (ha' : a' = q y') (hs : s = p y + y') (ht : t = y + q y') :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D s a y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (tau3 D t y a') := by
  subst ha ha' hs ht
  exact h u hu h1 y y'

variable {O : Type} [CommRing O] [StarRing O]

local instance modMul (D : DegPre R) [h : Module O D.X] (n : ℕ) : Module O (mulDeg D n).X := h

def mulAct (D : DegPre R) [Module O D.X] (oa : D.OAct O) (n : ℕ) : (mulDeg D n).OAct O where
  onB := oa.onB
  c_lin := fun a (y : D.X) => by
    show D.c (n • (a • y)) = D.c (n • y) ≫ oa.onB.act a
    rw [smul_comm n a y, oa.c_lin]
  tau_bal := fun a u hu h1 (y y' : D.X) =>
    corr_balanced_degenerationData_rosati D _ _ _ _ (oa.tau_bal a) u hu h1 (n • y) (n • y') (n • (a • y)) (n • (star a • y'))
      (n • (a • y + y')) (n • (y + star a • y')) (smul_comm n a y) (smul_comm n (star a) y')
      (by rw [nsmul_add, smul_comm n a y]) (by rw [nsmul_add, smul_comm n (star a) y'])

theorem corr_polarisationElement_degenerationData (D : DegPre R) [Module O D.X] (oa : D.OAct O) (w0 : O)
    (u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left]
      ![1, -2, -1, 2]))
    (h : ∀ y, LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau y (w0 • y)) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)) (y s b : D.X) (hb : b = w0 • y) (hs : s = y + w0 • y) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (tau3 D s y b) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK) := by
  subst hb hs
  exact h y

theorem mulDeg_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  intro R _ _ D O _ _ _ oa w0 n he hb hw hg
  refine ⟨fun (a : D.X) => corr_even_degenerationData_negPoint D he (n • a) (n • (-a)) (neg_nsmul a n),
    fun (a a' b : D.X) => corr_bimultiplicative_degenerationData_sums D hb (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
      (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _),
    fun (y : D.X) => hg (n • y), mulAct D oa n, rfl, ?_⟩
  obtain ⟨u, hu, h1, h⟩ := hw
  exact ⟨u, hu, h1, fun (y : D.X) => corr_polarisationElement_degenerationData D oa w0 u h (n • y) (n • (y + w0 • y)) (n • (w0 • y)) (smul_comm n w0 y)
    (by rw [nsmul_add, smul_comm n w0 y])⟩

end GlobalTheory.UCanon.MulDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsAbelianPartOfIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

def chartPullCompOf {X Y Y' : Scheme.{0}} (L : LB X) (g : Y ⟶ X) (h : Y' ⟶ Y) (k : Y' ⟶ X) (e : h ≫ g = k) :
    ChartPull (L.pull k) (L.pull g) h where
  idx J := J
  le J y hy := by
    subst e
    exact mem_pull.2 (by simpa using mem_pull.1 hy)
  g y J J' hj hj' := by
    subst e
    have hj₁ : h y ∈ (L.pull g).U J := mem_pull.2 (by simpa using mem_pull.1 hj)
    have hj₁' : h y ∈ (L.pull g).U J' := mem_pull.2 (by simpa using mem_pull.1 hj')
    refine (gm_pull_g L (h ≫ g) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L g h y J J' hj₁ hj₁').symm
    rw [Category.id_comp]

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem descAt_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K)
    (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  intro V V₁ _ _ _ _ ρ Q D p
  have gp := pull_grp p
  refine ⟨H1.dim_unique _ D.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback gp.1 Q.P.smoothDim)
    (eSec D.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V₁)), ?_⟩
  intro K _ ev k₀ hd
  obtain ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hab, hM, h₁, h₀, hw, hc⟩ := hd
  have hL : LBIso (Q.P.L.pull (π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (M₀.pull π₀) :=
    LBIso.trans (pull_isLB Q.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB hM _)
      (LBIso.chartPull (chartPullCompOf Q.P.L _ π₁ _ rfl) (chartPullPull D.P.L π₁)
        (LBIso.symm ⟨p.w, p.w_gen⟩)) ⟨w, hw⟩
  obtain ⟨w', hw'⟩ := hL
  refine ⟨B₀, i₁, i₂, M₀, fun a => c₀ (p.xe.symm a), B', i₃, π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)),
    π₀, w', fun a => c' (p.xe.symm a), hab, hM, ?_, h₀, hw', fun a => ⟨(hc _).1, ?_, (hc _).2.2⟩⟩
  · exact (h₁.comp gp).congr (spMap_comp_ringHom ρ ev).symm rfl
  · have e₁ := (hc (p.xe.symm a)).2.1
    have e₂ := p.c_pr (p.xe.symm a)
    rw [AddEquiv.apply_symm_apply] at e₂
    rw [← Category.assoc, e₁, Category.assoc, e₂, ← Category.assoc, spMap_comp_ringHom]

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem eq_of_pow_eq_of_eq_at_closed : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → ∀ x x' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B, x ^ n = x' ^ n → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left → x = x' := by
  intro k _ B _ hB n hn x x' hpow h0
  haveI : IsCommMonObj B := hB.comm
  haveI hloc : IsLocalRing (DualNumber k) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, isUnit_iff_ne_zero]
    by_cases ha : a.fst = 0
    · right; rw [ha, sub_zero]; exact one_ne_zero
    · left; exact ha
  have hnD : IsUnit (n : DualNumber k) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_natCast]
    exact hn.isUnit
  have hnΓ : IsUnit (n : Γ(Sp (DualNumber k), ⊤)) := by
    simpa using hnD.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
  haveI : PreconnectedSpace (Sp (DualNumber k)) := by
    have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact this
  haveI : PreconnectedSpace (𝟙_ (Over (Sp (DualNumber k)))).left := ‹PreconnectedSpace (Sp (DualNumber k))›
  let T : Over (Sp (DualNumber k)) := Over.mk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  haveI : Nonempty T.left := inferInstanceAs (Nonempty (Sp k))
  have hw : (x * x'⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one B hB hnΓ (x * x'⁻¹) hw
  have hT : toUnit T ≫ x = toUnit T ≫ x' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact h0
  have h1 : toUnit T ≫ (x * x'⁻¹) = 1 := by
    show (preHom (toUnit T)) (x * x'⁻¹) = 1
    rw [map_mul, map_inv]
    show (toUnit T ≫ x) * (toUnit T ≫ x')⁻¹ = 1
    rw [hT, mul_inv_cancel]
  have hsub := (hz T (toUnit T)).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 _ ≫ (x * x'⁻¹) = 1 := (hz _ (𝟙 _)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

end GlobalTheory.UCanon
end


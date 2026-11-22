import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPower
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdTw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A)
  (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)

theorem prod_tw {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (x.left ≫ twφ D₀ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have hu : x ≫ toUnit D₀.P.A = toUnit T := toUnit_unique _ _
  rw [Fin.prod_univ_three]
  show h (x ≫ (β * (toUnit D₀.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₀.P.A ≫ b).left ^ (-1 : ℤ) *
    h (x ≫ toUnit D₀.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
  rfl

theorem lift_β {T : Over (Sp R)} (p q : T ⟶ D₀.P.A) :
    (lift p q).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left =
      (lift (p ≫ β) (q ≫ β)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

variable {D₀ D β b} [IsMonHom β]

theorem wv_mul {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    {T : Over (Sp R)} (x y : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w (x * y).left z J J' * wv w (1 : T ⟶ D₀.P.A).left z J J' *
        lamVal wΛ (lift (1 : T ⟶ D₀.P.A) (1 : T ⟶ D₀.P.A)).left z J J' =
      wv w x.left z J J' * wv w y.left z J J' * lamVal wΛ (lift x y).left z J J' *
        cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⊗ B₀ ⟶ B₀ := fst B₀ B₀
  let s : B₀ ⊗ B₀ ⟶ B₀ := snd B₀ B₀
  have H := (((((reg_wv hw (f * s).left).mul (reg_wv hw f.left).inv).mul (reg_wv hw s.left).inv).mul
    (reg_wv hw (1 : B₀ ⊗ B₀ ⟶ B₀).left)).mul (reg_lam hΛ (lift f s).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left).inv
  have ev : ∀ x y : T ⟶ B₀,
      wv w ((lift x y).left ≫ (f * s).left) z J J' * (wv w ((lift x y).left ≫ f.left) z J J')⁻¹ *
        (wv w ((lift x y).left ≫ s.left) z J J')⁻¹ * wv w ((lift x y).left ≫ (1 : B₀ ⊗ B₀ ⟶ B₀).left) z J J' *
        (lamVal wΛ ((lift x y).left ≫ (lift f s).left) z J J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          ((lift x y).left ≫ (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left) z J)⁻¹ =
      wv w (x * y).left z J J' * (wv w x.left z J J')⁻¹ * (wv w y.left z J J')⁻¹ *
        wv w (1 : T ⟶ B₀).left z J J' * (lamVal wΛ (lift x y).left z J J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b))⁻¹ := fun x y => by
    have hu : lift x y ≫ toUnit (B₀ ⊗ B₀) = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [MonObj.comp_mul, MonObj.comp_one, comp_lift, comp_lift, comp_lift, ← Category.assoc (lift x y) (toUnit _), hu,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, prod_tw, prod_tw, lift_β, prod_lam, prod_lam]
      erw [prod_cub (G := D.P.A) (f ≫ β) (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b) h]
      rw [MonObj.mul_comp, MonObj.one_comp,
        _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    ((snd B₀ B₀).left ≫ B₀.hom) (surj_comp (surj_snd hG D₀.P.isAb _) (hG _ _ D₀.P.isAb).2)
    (lift x y).left (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left (by
      rw [Over.w, Over.w, Over.w]) z hJ hJ'
  have E' := (ev x y).symm.trans (E.trans (ev 1 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, _root_.mul_one (1 : T ⟶ B₀)] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

theorem wv_inv (hb : padd D.P.A b b = η[D.P.A]) {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) =
      wv w (x⁻¹).left z J J' * val D₀.sym x.left z J' * cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⟶ B₀ := 𝟙 B₀
  have hbb : (toUnit B₀ ≫ b) * (toUnit B₀ ≫ b) = 1 := by
    rw [← MonObj.comp_mul]; exact congrArg (toUnit B₀ ≫ ·) hb
  have H := (((((reg_wv hw f.left).mul (reg_val (L' := D₀.P.L) D.sym_gen (f ≫ β).left)).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left)).mul (reg_wv hw (f⁻¹).left).inv).mul
      (reg_val' (L := D.P.L) D₀.sym_gen f.left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left).inv
  have ev : ∀ x : T ⟶ B₀,
      wv w (x.left ≫ f.left) z J J' * val D.sym (x.left ≫ (f ≫ β).left) z J *
        val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left) z J *
        (wv w (x.left ≫ (f⁻¹).left) z J J')⁻¹ * (val D₀.sym (x.left ≫ f.left) z J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left) z J)⁻¹ =
      wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) *
        (wv w (x⁻¹).left z J J')⁻¹ * (val D₀.sym x.left z J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b))⁻¹ := fun x => by
    have hu : x ≫ toUnit B₀ = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [comp_lift, comp_lift, comp_lift, comp_lift, ← Category.assoc x (toUnit _), hu, GrpObj.comp_inv, GrpObj.comp_inv,
      ← Category.assoc x f, Category.comp_id]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, GlobalTheory.GaugeValues.prod_sym, GlobalTheory.GaugeValues.prod_sym]
      erw [prod_cub (G := D.P.A) (f ≫ β) (toUnit B₀ ≫ b) (toUnit B₀ ≫ b) h,
        prod_cub (G := D.P.A) (f ≫ β) (f ≫ β)⁻¹ (toUnit B₀ ≫ b) h]
      rw [GrpObj.inv_comp,
        _root_.mul_assoc (f ≫ β), hbb, _root_.mul_one (f ≫ β), mul_inv_cancel (f ≫ β), _root_.one_mul (toUnit B₀ ≫ b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    B₀.hom (hG _ _ D₀.P.isAb).2 x.left (1 : T ⟶ B₀).left (by rw [Over.w, Over.w]) z hJ hJ'
  have E' := (ev x).symm.trans (E.trans (ev 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, (isCub_cubV D.cub hJ).face, inv_one,
    GlobalTheory.GaugeValues.val_sym_one D hJ, GlobalTheory.GaugeValues.val_sym_one D₀ hJ'] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

end GlobalTheory.MumCmp.Point
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProdAdj

theorem adj_first_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := GlobalTheory.isMonHom_section_of_prod_trivial _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := GlobalTheory.MumProd.PsumMap.psum_comp_hom _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.MumProd.exists_cubeIso _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => GlobalTheory.MumProd.c_inc_fst _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.MumProd.tau_sum_fst R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProdAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwPsi

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point

variable {R : Type} [CommRing R] [IsDomain R]

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem cancel {A : Type} [CommRing A] [IsDomain A] {S S₂ : A} {ψ rig G N W Wc W1 ψ₂ rig₂ : Aˣ} (hs : S₂ ≠ 0)
    (e : S * (ψ * rig).val * (G * N).val = (W * Wc⁻¹ * W1).val * (S₂ * (ψ₂ * rig₂).val))
    (e4 : S * N.val = W.val * S₂) : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂) := by
  refine Units.ext (mul_left_cancel₀ (mul_ne_zero W.ne_zero hs) ?_)
  simp only [Units.val_mul] at e ⊢
  linear_combination e - ((ψ : A) * G * rig) * e4

theorem core {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ))
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β g.b) twε))
    (f : ∀ α : D.X, D.SecB 1 α) (f₂ : ∀ α : D₂.X, D₂.SecB 1 α)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]))
    (h : LevelOneEq D f) (h₂ : LevelOneEq D₂ f₂)
    (hf : ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
      (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' →
      sval (f (xe χ)) (r ≫ twφ D₂ D β g.b 0) z J *
        (val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * sval (f₂ χ) r z J')
    [IsIntegral (DegPre.BF D₂ (FractionRing R)).left]
    (χ : D₂.X) (z : (DegPre.BF D₂ (FractionRing R)).left) (J : _ → D.P.L.ι) (J' : _ → D₂.P.L.ι)
    (hJ : Good D.P.L z J) (hJ' : Good D₂.P.L z J')
    (ne : sval (f₂ 0) (DegPre.prB D₂ (FractionRing R)).left z J' ≠ 0) :
    val (D.psi (xe χ)) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J *
        val (g.s (xe χ)) (toUnit (DegPre.BF D₂ (FractionRing R))).left z J *
        val D.rig (DegPre.BF D₂ (FractionRing R)).hom z J =
      (wv w (cP D₂ (DegPre.BF D₂ (FractionRing R)) χ).left z J J')⁻¹ *
        wv w (1 : DegPre.BF D₂ (FractionRing R) ⟶ D₂.P.A).left z J J' *
        (val (D₂.psi χ) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J' *
          val D₂.rig (DegPre.BF D₂ (FractionRing R)).hom z J') := by
  let T := DegPre.BF D₂ (FractionRing R)
  let κ : T ⟶ TF (R := R) (FractionRing R) := fst _ _
  let Φ : D₂.P.A ⟶ D.P.A := padd D.P.A β (toUnit D₂.P.A ≫ g.b)
  have hΦ : ∀ u : T ⟶ D₂.P.A, u ≫ Φ = (u ≫ β) * (toUnit T ≫ g.b) := fun u => by
    show u ≫ (β * (toUnit D₂.P.A ≫ g.b)) = _
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  have hU : ∀ u : T ⟶ D₂.P.A, u.left ≫ (toUnit D₂.P.A).left = (toUnit T).left := fun u => by
    rw [← Over.comp_left, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ D₂.P.A, y * cP D₂ T χ = DegPre.prB D₂ (FractionRing R) :=
    ⟨_, inv_mul_cancel_right _ _⟩
  have hyΦ : (y ≫ Φ) * cP D T (xe χ) = DegPre.prB D₂ (FractionRing R) ≫ Φ := by
    rw [hΦ, hΦ, ← hy, MonObj.mul_comp, cP_comp β (hc χ), mul_right_comm]
  have e₁ := h (xe χ) 0 rfl T κ (y ≫ Φ) z J hJ
  have e₂ := h₂ χ 0 rfl T κ y z J' hJ'
  have e₃ := hf χ _ y.left z J J' hJ hJ'
  have e₄ := hf 0 _ (DegPre.prB D₂ (FractionRing R)).left z J J' hJ hJ'
  have p₃ := prod_famB D₂ y χ (fun q => wv w q z J J')
  have p₄ := prod_famB D₂ (DegPre.prB D₂ (FractionRing R)) 0 (fun q => wv w q z J J')
  rw [hy] at p₃ e₂
  rw [cPoint_zero, _root_.mul_one, inv_mul_cancel_right] at p₄
  rw [hyΦ] at e₁
  change _ = (∏ κ, wv w (y.left ≫ D₂.famφB χ κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₃
  change _ = (∏ κ, wv w ((DegPre.prB D₂ (FractionRing R)).left ≫ D₂.famφB 0 κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₄
  rw [p₃, hU, show y.left ≫ twφ D₂ D β g.b 0 = (y ≫ Φ).left from rfl, e₁, e₂] at e₃
  rw [p₄, hU, map_zero xe, val_corr hJ g.s_zero, val_one, _root_.one_mul,
    show (DegPre.prB D₂ (FractionRing R)).left ≫ twφ D₂ D β g.b 0 = (DegPre.prB D₂ (FractionRing R) ≫ Φ).left from rfl] at e₄
  exact cancel ne e₃ e₄

theorem grp {U : Type} [CommGroup U] {ψ0 ψ₂0 rig rig₂ W1 ψ G Wc ψ₂ : U} (h0 : ψ0 = W1⁻¹ * ψ₂0)
    (c0 : ψ0 * rig = ψ₂0 * rig₂) (c : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂)) : ψ * G = Wc⁻¹ * ψ₂ := by
  subst h0
  apply Additive.ofMul.injective
  have e0 := congrArg Additive.ofMul c0
  have e := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at e0 e ⊢
  linear_combination (norm := abel) e - e0

theorem formEq {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ)) (χ : D₂.X) :
    FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (xe χ)))
        (fun k => (toUnit (TK R)).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) k))
      (Sum.elim (fun _ => -1) DegPre.gtε) (fun i => D₂.xK χ ≫ twφ D₂ D β g.b i) (fun i => -1 * twε i) := by
  let u := toUnit (TK R)
  have k : ∀ a : TK R ⟶ 𝟙_ (Over (Sp R)), a = u := fun a => toUnit_unique _ _
  have m0 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 0 = D₂.xK χ ≫ twφ D₂ D β g.b 0 := by
    show u.left ≫ ((toUnit _ ≫ D.c (xe χ)) * g.b).left = (u ≫ D₂.c χ).left ≫ (β * (toUnit _ ≫ g.b)).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [MonObj.comp_mul, ← Category.assoc]
    rw [k (u ≫ toUnit _), k ((u ≫ D₂.c χ) ≫ toUnit _), Category.assoc, hc]
  have m1 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 1 = ptK (D.c (xe χ)) := by
    show u.left ≫ (toUnit _ ≫ D.c (xe χ)).left = (u ≫ D.c (xe χ)).left
    rw [← Over.comp_left, ← Category.assoc, k (u ≫ toUnit _)]
  have m2 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 2 = D₂.xK χ ≫ twφ D₂ D β g.b 1 := by
    show u.left ≫ g.b.left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ g.b).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, k ((u ≫ D₂.c χ) ≫ toUnit _)]
  have m3 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 3 = D₂.xK χ ≫ twφ D₂ D β g.b 2 := by
    show u.left ≫ (toUnit _ ≫ η[D.P.A]).left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, ← Category.assoc, k (u ≫ toUnit _),
      k ((u ≫ D₂.c χ) ≫ toUnit _)]
  intro U _ h
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Fintype.prod_unique, Sum.elim_inl,
    Sum.elim_inr]
  rw [m0, m1, m2, m3]
  simp only [DegPre.gtε, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_succ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

end GlobalTheory.MumCmp.TwPsi

namespace GlobalTheory.MumCmp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point GlobalTheory.MumCmp.TwPsi in

theorem psi_maps_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ _ D D₂ g β hβ xe hc w hw ⟨t₀, m₀, c₀⟩ f f₂ ν _ h h₂ hne hf χ
  have hL := D.toPre.P.isLB
  have hL' := D₂.toPre.P.isLB
  have := D₂.toPre.P.isAb.smooth
  have := D₂.toPre.P.isAb.geomConnected
  have : IsIntegral (DegPre.BF D₂.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D₂.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D₂.toPre.P.A.hom).flip
  let T := DegPre.BF D₂.toPre (FractionRing R)
  let π : T.left ⟶ (TK R).left :=
    (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
  have hπ : π ≫ jK R = T.hom := by
    rw [Category.assoc]; exact Over.w (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A)
  have hT0 : π ≫ D₂.toPre.xK 0 = (1 : T ⟶ D₂.toPre.P.A).left := by
    rw [Uniq.xK_zero, ← Category.assoc, hπ]; rfl
  have hTχ : π ≫ D₂.toPre.xK χ = (cP D₂.toPre T χ).left := by
    let k : T ⟶ TK R := Over.homMk π hπ
    exact congrArg (fun q => q.left) (comp_cP D₂.toPre k χ)
  have hTU : π ≫ (toUnit (TK R)).left = (toUnit T).left := by
    rw [toUnit_left_eq, toUnit_left_eq]; exact hπ
  have key : ∀ (z : T.left) J J', Good D.toPre.P.L z J → Good D₂.toPre.P.L z J' →
      val (D.toPre.psi (xe χ)) π z J * val (g.s (xe χ)) (π ≫ (toUnit (TK R)).left) z J =
        (wv w (π ≫ D₂.toPre.xK χ) z J J')⁻¹ * val (D₂.toPre.psi χ) π z J' := by
    intro z J J' hJ hJ'
    have ne : sval (f₂ 0) (DegPre.prB D₂.toPre (FractionRing R)).left z J' ≠ 0 := fun e => hne (h₂.eq_zero z hJ' e)
    have cχ := core g β.hom xe hc w f f₂ ν h h₂ hf χ z J J' hJ hJ' ne
    have c0 := core g β.hom xe hc w f f₂ ν h h₂ hf 0 z J J' hJ hJ' ne
    rw [map_zero xe, val_corr hJ g.s_zero, val_one, _root_.mul_one, cPoint_zero, inv_mul_cancel, _root_.one_mul] at c0
    have h0 : val (D.toPre.psi 0) π z J = (wv w (π ≫ D₂.toPre.xK 0) z J J')⁻¹ * val (D₂.toPre.psi 0) π z J' := by
      have e := Uniq.gm_mapsAtExp m₀ π z (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
        (J' (π ≫ D₂.toPre.xK 0)) (Set.mem_iInter.2 fun k => hJ _) (hJ' _)
      rw [← val_of t₀ π z J (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
          (fun k => congrArg J (Category.assoc π _ _).symm), val_corr hJ c₀, val_mul hJ, val_pull hJ,
        val_corr hJ g.s_zero, val_one, _root_.mul_one] at e
      rw [e, zpow_neg_one]; rfl
    rw [hT0] at h0
    rw [hTχ, hTU]
    exact grp h0 c0 cχ
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_gen hL (formEq g β.hom xe hc χ)
    (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))
    (mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (pullGen_isGen _ _ _ _ (g.isGen _) _))
  have R₁ := reg_val (L' := D₂.toPre.P.L) ht₁ π
  have R₂ := reg_wv (L := D.toPre.P.L) (L' := D₂.toPre.P.L) hw (π ≫ D₂.toPre.xK χ)
  have R₃ := (reg_val' (L := D.toPre.P.L) (D₂.toPre.psi_gen χ) π).inv
  obtain ⟨a, ha⟩ := ((R₁.mul R₂).mul R₃).glue hL hL' (fun U _ h h' => by
    simp only [Category.assoc, Fintype.prod_unique, zpow_neg_one, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_prod, ofMul_one]
    simp only [neg_mul, _root_.one_mul, neg_zsmul, Finset.sum_neg_distrib]
    abel)
  have ha1 : a = 1 := unit_ext fun x _ => by
    obtain ⟨J, hJ⟩ := good_exists hL x
    obtain ⟨J', hJ'⟩ := good_exists hL' x
    rw [← ha _ (𝟙 _) x J J' hJ hJ', map_one]
    show val t₁ (𝟙 _ ≫ π) x J * wv w (𝟙 _ ≫ π ≫ D₂.toPre.xK χ) x J J' * (val (D₂.toPre.psi χ) (𝟙 _ ≫ π) x J')⁻¹ = 1
    rw [Category.id_comp, Category.id_comp, hv₁ _ _ x J hJ, val_mul hJ, val_pull hJ, key x J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have H : ∀ (y : (TK R).left) J J', Good D.toPre.P.L y J → Good D₂.toPre.P.L y J' →
      val t₁ (𝟙 _) y J = wv w (D₂.toPre.xK χ) y J J' ^ (-1 : ℤ) * val (D₂.toPre.psi χ) (𝟙 _) y J' := by
    intro y J J' hJ hJ'
    have e := ha _ (DegPre.zF D₂.toPre (FractionRing R)).left y J J' hJ hJ'
    rw [ha1, map_one] at e
    have hz : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π = 𝟙 _ := PsiCompare.zF_fst D₂.toPre
    change val t₁ ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J *
      wv w ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ) y J J' *
      (val (D₂.toPre.psi χ) ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J')⁻¹ = 1 at e
    have hz' : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ = D₂.toPre.xK χ := by
      rw [← Category.assoc (DegPre.zF D₂.toPre (FractionRing R)).left π, hz, Category.id_comp]
    rw [hz', hz] at e
    rw [zpow_neg_one, ← mul_inv_eq_one, mul_inv, inv_inv, ← _root_.mul_assoc]
    exact e
  exact ⟨t₁, mapsAtExp_of_val hL hL' hw (D₂.toPre.psi_gen χ) ht₁ H, corr_of_val hL fun y J hJ => hv₁ _ _ y J hJ⟩

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAevalSym
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem pull_aeval_sym : ∀ (n n' : ℕ) (L : V n' →L[ℂ] V n) (P : MvPolynomial (Fin n × Fin n) ℂ), pull L ((aeval sym P : Ev n) : Alt n) = ((aeval sym (aeval (fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)) P) : Ev n') : Alt n') := by
  intro n n' L P
  rw [MvPolynomial.comp_aeval_apply]
  have key : (pull L).comp ((Subalgebra.center ℂ (Alt n)).val.comp (aeval sym)) = (Subalgebra.center ℂ (Alt n')).val.comp
      (aeval fun x : Fin n × Fin n => aeval sym (∑ c, ∑ d,
        C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ))) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, Subalgebra.coe_val, sym, (pull_dz L _).1,
      (pull_dz L _).2, Finset.sum_mul_sum, AlgHom.commutes, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Algebra.smul_def, map_mul]
  exact congrArg (fun f => f P) key

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_O1_section_coordinates_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (I : Type) [Finite I] (th : I → Ω) (δ : LB M.Z) (t : I → δ.Sec) (N D : ℕ) (e : Fin (N + 1) → Ω) (h : M.Z ⟶ PSpace o N), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → SecCoord δ t M.pt th → PCrd (M.pt ≫ h) e → SameScale M th e D → LBIso ((GlobalTheory.ProjSpace.O1 o N).pull h) (lbPow δ D) := by
  first | exact @GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | exact GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | (intros; apply GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackComplexFormsLinearMap_comp : ∀ (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k), pull (L'.comp L) γ = pull L (pull L' γ) := by
  first | exact @GlobalTheory.CxForm.pull_comp | exact GlobalTheory.CxForm.pull_comp | (intros; apply GlobalTheory.CxForm.pull_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasisStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y → ∀ f : Form (B.hom ≫ 𝟙 (Sp R)), (∀ i, tanVal (y i) f = 0) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (B' : Over (Sp R')) [GrpObj B'] [IsCommMonObj B'] (φ : B'.left ⟶ B.left), IsGrpPullback B' B (spMap σ) φ → ∀ (m : IsMor (dp0 R) (B.hom ≫ 𝟙 (Sp R)) (dp0 R') (B'.hom ≫ 𝟙 (Sp R')) σ φ) (v : epsR R' ⟶ B'), IsTangent v → tanVal v (m.pullForm f) = 0 := by
  first | exact @GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | exact GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | (intros; apply GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFields
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem algHom_aeval_ev {m m' : ℕ} {ι : Type} (φ : Alt m →ₐ[ℂ] Alt m') (u : ι → Ev m) (u' : ι → Ev m')
    (h : ∀ i, φ (u i : Alt m) = (u' i : Alt m')) (P : MvPolynomial ι ℝ) :
    φ ((aeval u (P.map (algebraMap ℝ ℂ)) : Ev m) : Alt m) = ((aeval u' (P.map (algebraMap ℝ ℂ)) : Ev m') : Alt m') := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact φ.commutes _
  | add p q hp hq =>
    simp only [map_add, Subalgebra.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, Subalgebra.coe_mul, hp, h]

theorem pullback_evalF : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  intro M M' _ _ n n' A A' g ι w w' hw P
  funext x
  exact algHom_aeval_ev _ _ _ (fun i => congrFun (hw i) x) P

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGenericStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_divisor_pullback_generic : ∀ (G Y : Scheme.{0}) [IsIntegral G] [IsIntegral Y] [IsLocallyNoetherian G] [IsLocallyNoetherian Y] (j : G ⟶ Y), j (genericPoint G) = genericPoint Y → (∀ x : G, IsIso (j.stalkMap x)) → ∀ (M : LB Y) (hM : M.IsLB) (r : M.ι → Y.functionFieldˣ) (hr : IsRatSec M r), ∃ (r' : (M.pull j).ι → G.functionFieldˣ) (hr' : IsRatSec (M.pull j) r'), ∀ x : G, (divOfRatSec (LB.isLB_pull hM j) hr').mult x = (divOfRatSec hM hr).mult (j x) := by
  first | exact @GlobalTheory.MultPull.exists_isRatSec_pull_mult | exact GlobalTheory.MultPull.exists_isRatSec_pull_mult | (intros; apply GlobalTheory.MultPull.exists_isRatSec_pull_mult <;> assumption)
end


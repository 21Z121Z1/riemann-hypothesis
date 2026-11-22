import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
noncomputable section
namespace GlobalTheory.TorsFrame

open CommPairing GlobalLift ThetaCoord

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_pow_two (hL : L.IsLB) {Y : Scheme.{0}} {f g : Y ⟶ A.left} {k : ℤ} (m : ℕ)
    {u : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![k, -k])} (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![m * k, -(m * k)]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val u' r z J = val u r z J ^ m := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![f, g]) (ε' := ![m * k, -(m * k)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg])
    (GeneratorPullback.powGen L _ _ u m) (DVR.powGen_isGen _ _ _ _ hu _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_powGen _ _ _ _ _)⟩

theorem exists_symLift_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k q x θ) (m : ℕ) :
    ∃ θ' : ThetaGrp A L (m * k) T, SymLift A L (m * k) q x θ' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ' r z J = tval θ r z J ^ m := by
  obtain ⟨ν, hν, -⟩ := H.sym
  obtain ⟨u, hu, vu⟩ := exists_pow_two hL m (u := θ.φ) θ.isGen
  obtain ⟨ν', hν', vν⟩ := exists_pow_two hL m (u := ν) hν
  have vu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨θ.pt, u, hu⟩ : ThetaGrp A L (m * k) T) r z J = tval θ r z J ^ m := vu
  have vν' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      nval (k := m * k) ν' r z J = nval ν r z J ^ m := vν
  refine ⟨⟨θ.pt, u, hu⟩, symLift_of_tval hL H.pt_eq (ν := ν') hν' (fun T' π z J hJ p => ?_)
    (fun T' π z J hJ p => ?_), vu'⟩
  · rw [Finset.prod_congr rfl fun j _ => vu' _ _ z J hJ, Finset.prod_pow, prod_tval H π hJ p, one_pow]
  · rw [vu' _ _ z J hJ, vu' _ _ z J hJ, vν' _ _ z J hJ, vν' _ _ z J hJ, ← inv_pow, ← mul_pow, ← mul_pow, ← mul_pow,
      sym_tval hG hA hL H hν π hJ p, one_pow]

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [eSec, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, e, one_pow]

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem exists_norm (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) {n : ℕ}
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good L z J → val α (r ≫ eSec A) z J =
        val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J ^ (n ^ 2) *
          (val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J)⁻¹ := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig (n ^ 2))
        (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig))
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (eSec A)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hr _) (DVR.invGen_isGen _ _ _ _ hr))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))) _))
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have e : (r ≫ eSec A) ≫ A.hom = r := by rw [Category.assoc, eSec_hom, Category.comp_id]
  rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, e, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
    mul_comm, inv_mul_cancel_right]

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J := by
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A)
    (fun _ => J (r ≫ T.hom ≫ eSec A)) from Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

theorem tval_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {ν : LB.Gen (negLB A L 1 T)}
    (hν : ν.IsGen) {n : ℕ} (hn : Odd n)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (hα : α.IsGen)
    {y : T ⟶ A} (hy : y ^ (n ^ 2) = 1) {θ : ThetaGrp A L (n ^ 2 : ℕ) T} (H : SymLift A L (n ^ 2 : ℕ) (n ^ 2) y θ)
    {z : T.left} {J} (hJ : Good L z J) :
    tval θ (lift (𝟙 T) (1 : T ⟶ A)).left z J ^ (n ^ 2) =
      val α (1 : T ⟶ A).left z J ^ (n ^ 2) * val α (1 : T ⟶ A).left z J *
        (val α y.left z J ^ (n ^ 2) * val α (y ^ n).left z J)⁻¹ := by
  have e₁ : ∀ p : T ⊗ A ⟶ A, p.left ≫ (mulA A n).left = (p ^ n).left := fun p => by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨β, hβ, vβ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) * (n ^ 2 : ℕ), -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id, ← pow_mul, ← sq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L _ _ (LB.pullGen L _ _ α (snd T A).left) (n ^ 2))
      (LB.pullGen L _ _ α (snd T A ^ n).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) _)
      (DVR.pullGen_isGen _ _ _ _ hα _))
  have vβ' : ∀ p : T ⟶ A, bval (b := 1) β (lift (𝟙 T) p).left z J =
      val α p.left z J ^ (n ^ 2) * val α (p ^ n).left z J := fun p => by
    refine (vβ _ _ z J hJ).trans ?_
    rw [val_mul hJ, val_powGen, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, lift_snd]
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν 1
  obtain ⟨θ₁, H₁, v₁⟩ := exists_symLift_mulPull hA hL (one_dvd (n ^ 2)) (b := 1) hβ hy (hy.symm ▸ ho)
  obtain ⟨θ₂, H₂, v₂⟩ := exists_symLift_pow hG hA hL H (n ^ 2)
  have e : tval θ₂ (lift (𝟙 T) (1 : T ⟶ A)).left z J = tval θ₁ (lift (𝟙 T) (1 : T ⟶ A)).left z J :=
    val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn.pow θ₂ θ₁ H₂ H₁) _
  rw [v₂ _ _ z J hJ, v₁ _ _ z J hJ, vo _ _ z J hJ, vβ', vβ', one_pow, _root_.mul_one, _root_.mul_one,
    Category.id_comp] at e
  exact e

end GlobalTheory.TorsFrame

namespace GlobalTheory

open TorsFrame CommPairing in

theorem exists_isTorsFrame_of_symLift : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  intro hLaw S _ P rig hr n hn T y x hy hx θ H
  subst hx
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P n
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A n).left = (y ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, H.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ n).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (n ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  refine ⟨τ, by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ n) τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (n ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hn hα hy H hJ
    have c : val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
        (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    rw [one_left, vα _ _ z J hJ] at b
    rw [a, vτ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_mul hJ, c, val_powGen, val_pull hJ, val_pull hJ,
      val_pull hJ, val_rigT rig _ z hJ, Category.id_comp, Category.id_comp, Category.id_comp, mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LabelMap

theorem exists_lift_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {Γ : Type} [AddCommGroup Γ]
    (pt : Γ → (baseOver S ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) :
    ∃ xx : Multiplicative Γ →* (T ⟶ G'),
      (∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = xx (Multiplicative.ofAdd a)) ∧
      ∀ (k : ℕ), (∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ k = 1 → ∃ a, (T.hom ≫ f) ≫ (pt a).left = z.left) →
        ∀ x : T ⟶ G', x ^ k = 1 → ∃ a, xx (Multiplicative.ofAdd a) = x := by
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hΦ : ∀ x, (Φ x).left = x.left ≫ φ := fun _ => rfl
  have inj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext (h.1.hom_ext
    ((hΦ x).symm.trans ((congrArg (fun z => z.left) e).trans (hΦ y))) ((Over.w x).trans (Over.w y).symm))
  have surj : Function.Surjective Φ := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  let e := MulEquiv.ofBijective Φ ⟨inj, surj⟩
  let U : Over.mk (T.hom ≫ f) ⟶ baseOver S := Over.homMk (T.hom ≫ f) (Category.comp_id _)
  let q : Multiplicative Γ →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun a => U ≫ pt a.toAdd) fun a b =>
      (congrArg (U ≫ ·) (hadd a.toAdd b.toAdd)).trans (MonObj.comp_mul U _ _)
  have key : ∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = e.symm (q (Multiplicative.ofAdd a)) := fun a x =>
    ⟨fun H => e.eq_symm_apply.2 (Over.OverMorphism.ext H),
      fun H => congrArg (fun z => z.left) (e.eq_symm_apply.1 H)⟩
  refine ⟨e.symm.toMonoidHom.comp q, key, fun k hk x hx => ?_⟩
  obtain ⟨a, ha⟩ := hk (Φ x) (by rw [← map_pow, hx, map_one])
  exact ⟨a, ((key a x).1 ha.symm).symm⟩

attribute [local instance] TorusExt.gtGroup in

theorem pow_eq_one_of_qkAdd {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (heq : ∀ q q', QkPt.Equiv D F q q' → f q = f q') (hadd : ∀ q q' q'', QkAdd q q' q'' → f q'' = f q * f q')
    (q : QkPt D F k) : f q ^ k = 1 := by
  have fz : f (TorusExt.qkZero hB F k) = 1 := by
    have e := hadd _ _ _ (TorusExt.qkAdd_qkAdd hB (TorusExt.qkZero hB F k) (TorusExt.qkZero hB F k))
    rw [show TorusExt.qkAdd hB (TorusExt.qkZero hB F k) (TorusExt.qkZero hB F k) = TorusExt.qkZero hB F k from
      TorusExt.qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  let m : ℕ → QkPt D F k := fun n => TorusExt.qkMk hB (n • q.y) (n • q.g) (by
    rw [smul_comm, TorusExt.qk_nsmul hB, map_nsmul])
  have hm : ∀ n, f (m n) = f q ^ n := fun n => by
    induction n with
    | zero => exact (congrArg f (TorusExt.qk_ext (zero_nsmul _) (zero_nsmul _))).trans (fz.trans (pow_zero _).symm)
    | succ n ih =>
      rw [pow_succ, ← ih, ← hadd _ _ _ (TorusExt.qkAdd_qkAdd hB _ _)]
      exact congrArg f (TorusExt.qk_ext (succ_nsmul _ _) (succ_nsmul _ _))
  rw [← hm, ← fz]
  exact (heq _ _ ((TorusExt.equiv_iff hB _ _).2
    ⟨q.y, (zero_add _).symm, (TorusExt.qk_nsmul hB q).trans (zero_add _).symm⟩)).symm

theorem exists_labelMap : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  intro L _ hU o Ω _ _ _ _ S ρ p _ y₀ u
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  obtain ⟨f, hrel, honto, heq, hadd, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨xx, hxx, hsurj⟩ := exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    exact (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap _ _))).symm.trans
      (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have htors : ∀ a : S.Gam, xx (Multiplicative.ofAdd a) ^ (S.r * S.N) = 1 := fun a => by
    have : (S.r * S.N) • a = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [← map_pow, ← ofAdd_nsmul, this, ofAdd_zero, map_one]
  choose P hP using fun a => honto _ (htors a)
  have hB := u.D.tau_bimult
  have wd : ∀ q q' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), f q = f q' →
      (QuotientAddGroup.mk q.y : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk q'.y := fun q q' e => by
    obtain ⟨z, hz, -⟩ := (heq q q').1 e
    exact QuotientAddGroup.eq.2 ⟨z, by rw [hz, neg_add_cancel_left]; rfl⟩
  have ftors : ∀ q, f q ^ (S.r * S.N) = 1 := pow_eq_one_of_qkAdd hB f (fun q q' e => (heq q q').2 e) hadd
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (P a).y) fun a b => ?_, fun c => ?_, fun a pk x hx hφ => ?_⟩
  · exact wd _ (TorusExt.qkAdd hB (P a) (P b)) (by
      rw [hadd _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), hP, hP, hP, ofAdd_add, map_mul])
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨q, rfl⟩ := TorusExt.exists_qkPt (F := PadicAlgCl p) L.mulN (Or.inr L.polBaseChange) hB (Nat.pos_iff_ne_zero.1 hk) y
    obtain ⟨a, ha⟩ := hsurj' _ (ftors q)
    exact ⟨a, wd _ _ ((hP a).trans ha)⟩
  · exact wd _ _ ((hP a).trans (((hxx a x).1 (hφ.trans (by rw [hy]))).symm.trans ((hrel pk x).1 hx)))

end GlobalTheory.ZH.LabelMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelOfPowEqOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem pow_eq_one_iff_of_isGrpPullback {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a' : X ⟶ S'} {a : X ⟶ S} (e : a = a' ≫ f)
    (x' : Over.mk a' ⟶ G') (x : Over.mk a ⟶ G) (hx : x.left = x'.left ≫ φ) (m : ℕ) :
    x' ^ m = 1 ↔ x ^ m = 1 := by
  subst e
  have hx' : x = pushHom h (Over.mk a') x' := Over.OverMorphism.ext hx
  have inj : Function.Injective (pushHom h (Over.mk a')) := fun y y' hy => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hy
    · rw [Over.w y, Over.w y']
  have : x ^ m = pushHom h (Over.mk a') (x' ^ m) := by rw [map_pow]; exact congrArg (· ^ m) hx'
  rw [this]
  exact (map_eq_one_iff _ inj).symm

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_label_of_pow_eq_one : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N →
    ∀ h : baseOver (Sp u.V) ⟶ u.G, h ^ m = 1 → ∃ b : S.Gam, m • b = 0 ∧ GlobalTheory.UnitTheta.Extends u b h := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm h hh
  have := u.U.gen_hom
  have hw : h.left ≫ u.G.hom = 𝟙 _ := Over.w h
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (jK u.V ≫ h.left) (𝟙 _) (by rw [Category.assoc, hw]; simp)
  have hx₁ : x ≫ pullback.fst _ _ = jK u.V ≫ h.left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  let i : Sp (PadicAlgCl p) ⟶ Sp (FractionRing u.V) := spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))
  have : Epi i := epi_spMap_of_field _
  have hy : spMap y₀ = i ≫ spMap u.yK :=
    (congrArg spMap u.fac).symm.trans (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom _))
  have hψ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  let x' : Over.mk i ⟶ (Over.pullback (jK u.V)).obj u.G :=
    Over.homMk (i ≫ x) (by
      show (i ≫ x) ≫ pullback.snd _ _ = i
      rw [Category.assoc, hx₂, Category.comp_id])
  let t : Over.mk (i ≫ jK u.V) ⟶ baseOver (Sp u.V) := Over.homMk (i ≫ jK u.V) (by simp)
  have h₀ : (t ≫ h) ^ m = 1 := by
    have := (map_pow (preHom (G := u.G) t) h m).symm.trans ((congrArg _ hh).trans (map_one _))
    exact this
  have h₁ : x' ^ m = 1 :=
    (pow_eq_one_iff_of_isGrpPullback (isGrpPullback_pullback u.G (jK u.V)) rfl x' (t ≫ h) (by
      show (i ≫ jK u.V) ≫ h.left = (i ≫ x) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, hx₁]) m).2 h₀
  let z : Over.mk (spMap y₀) ⟶ ρ.P.A := Over.homMk (x'.left ≫ u.U.gen.hom.left ≫ u.φ) (by
    show (x'.left ≫ u.U.gen.hom.left ≫ u.φ) ≫ ρ.P.A.hom = spMap y₀
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w x', hy]; rfl)
  have h₂ : z ^ m = 1 := (pow_eq_one_iff_of_isGrpPullback hψ hy x' z rfl m).1 h₁
  have h₃ : z ^ (S.r * S.N) = 1 := by
    obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, h₂, one_pow]
  obtain ⟨b, hb, -⟩ := ρ.pt_bij (PadicAlgCl p) (spMap y₀) z h₃
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  refine ⟨b, ?_, x, hx₁, hx₂, ?_⟩
  · refine (ρ.pt_bij (PadicAlgCl p) (spMap y₀) 1 (one_pow _)).unique ?_ ?_
    · rw [hp, ← h₂, ← hb]
      exact map_pow (preHom (G := ρ.P.A) _) _ m
    · rw [h0]
      exact map_one (preHom (G := ρ.P.A) _)
  · have e : spMap y₀ ≫ (ρ.pt b).left = (i ≫ x) ≫ u.U.gen.hom.left ≫ u.φ := congrArg (fun w => w.left) hb
    rw [← cancel_epi i, ← Category.assoc i (spMap u.yK), ← hy, e, Category.assoc]

end GlobalTheory.UnitTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.ThetaReal.NormMul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  have v : ∀ (y : T.left) (i : Fin 1 → L.ι), y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k :=
    fun y i hi => (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res (𝟙 T.left) y (rigT_le A L i) hi _).trans
      (gm_pull (𝟙 T.left) T.hom y _ (rigT_le A L i hi) (ρ.s fun _ => i 0))))
  refine SymLiftOdd.isGen_of_gm fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hi) (rigT_le A L (T := T) j hj)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  rw [v y i hi, v y j hj, trF, Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd]; rfl

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left)
        (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b)) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + -b + (a + b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left))
      (LB.mulGen L _ _ _ _ (rigT A L ρ T a) (rigT A L ρ T b))) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigT_isGen hρ a) (rigT_isGen hρ b))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end GlobalTheory.ThetaReal.NormMul

namespace GlobalTheory.ThetaReal

theorem exists_normalised_mulPull : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  intro hLaw S _ P rig hrig m N hN T
  subst hN
  have H := hLaw.mulPull _ P m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α₁, hα₁, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left]) α₀ hα₀ (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  exact NormMul.exists_normalised P.isLB hrig m _ _ α₁ hα₁

end GlobalTheory.ThetaReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def HasWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gs ((τ ≫ i) * g).left z U f = (gm τ.left z ⊤ (charUnit S X α)).val * gs g.left z U f

def GenWt {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ⟶ G)
    {Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (α : X) : Prop :=
  ∀ (Z : Over S) (τ : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J : (Z.left ⟶ Y) → L.ι), Good L z J →
    val t ((τ ≫ i) * g).left z J = gm τ.left z ⊤ (charUnit S X α) * val t g.left z J

def Red {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) {K K' : Type} [Fintype K] [Fintype K'] {ψ : K → (Φ.E.B.left ⟶ Y)} {ε : K → ℤ}
    {φt : K' → (Φ.G.left ⟶ Y)} {εt : K' → ℤ} (t : LB.Gen (LB.LinComb L φt εt)) (b : LB.Sec (LB.LinComb L ψ ε))
    (φ : (Φ.H 1).Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
    r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
    gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval b (r ≫ Φ.D.q.left) z J * (val t r z J).val

end GlobalTheory.ZH.UFib
end
end


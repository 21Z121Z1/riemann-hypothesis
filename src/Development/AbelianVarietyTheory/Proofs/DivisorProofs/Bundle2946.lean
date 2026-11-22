import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMulIsoUniformisationGenericFibreOneCon
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GenericMove

theorem move_one_const : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (N : ℕ) (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![𝟙 A.A.left, (mulA A.A N).left] ![(N : ℤ) ^ 2, -1])), α.IsGen → ∀ (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (mulA G N).left] ![(N : ℤ) ^ 2, -1])), β.IsGen → ∃ c : FractionRing V, c ≠ 0 ∧ ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ ((Over.pullback (jK V)).obj G).left), r ≫ ((Over.pullback (jK V)).obj G).hom = 𝟙 _ → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (val β (r ≫ pullback.fst G.hom (jK V)) z JG).val = GlobalTheory.UT.cst (FractionRing V) z c * (GlobalTheory.TorsFrameInt.wv w₀ r z JG JA ^ ((N : ℤ) ^ 2) * (GlobalTheory.TorsFrameInt.wv w₀ (r ≫ (mulA ((Over.pullback (jK V)).obj G) N).left) z JG JA)⁻¹ * val α (r ≫ U.gen.hom.left) z JA).val := by
  intro V _ _ I D A G _ _ U w₀ hw₀ N α hα β hβ
  haveI := U.gen_hom
  have h₁ : ∀ k : Fin 2, (![𝟙 ((Over.pullback (jK V)).obj G).left,
      (mulA ((Over.pullback (jK V)).obj G) N).left] : Fin 2 → _) k ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ (![𝟙 G.left, (mulA G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact GlobalTheory.TorsFrameInt.mulA_comm (isGrpPullback_pullback G (jK V)) N
  have hmA : mulA ((Over.pullback (jK V)).obj G) N ≫ U.gen.hom = U.gen.hom ≫ mulA A.A N := by
    rw [mulA, mulA, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have h₂ : ∀ k : Fin 2, (![𝟙 ((Over.pullback (jK V)).obj G).left,
      (mulA ((Over.pullback (jK V)).obj G) N).left] : Fin 2 → _) k ≫ U.gen.hom.left =
      U.gen.hom.left ≫ (![𝟙 A.A.left, (mulA A.A N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact congrArg (fun q => q.left) hmA
  obtain ⟨a, ha, hav⟩ := GlobalTheory.TorsFrameInt.exists_move U.LG.isLB A.isLB w₀ hw₀ _ _ _ ![(N : ℤ) ^ 2, -1] h₁ h₂ β hβ
  obtain ⟨ρ, hρ⟩ := exists_ratio A.isLB rfl a (LB.pullGen A.L _ _ α U.gen.hom.left) ha
    (pullGen_isGen _ _ _ _ hα _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.BoxExpansion.unit_const GlobalTheory.abelianSchemeLaws_all.1.globalFns A U.gen ρ
  refine ⟨c, hc0, fun r hr z JA JG hJA hJG => ?_⟩
  have hg : (gm r z ⊤ ρ).val = GlobalTheory.UT.cst (FractionRing V) z c := by
    rw [← gs_unit r z ⊤ trivial ρ, hc]
    exact (gs_pull r ((Over.pullback (jK V)).obj G).hom z ⊤ trivial _).trans (by rw [hr]; rfl)
  have e := hav _ r z JG JA hJG hJA
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at e
  rw [e, hρ _ r z JA hJA, val_pull hJA, zpow_neg_one, mul_left_comm, Units.val_mul, hg]

end GlobalTheory.GenericMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedTwistedFactorValueAtLatticePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFacVal

section General

variable {X Y Z : Scheme.{0}}

def pt (q : Y ⟶ X) : Multiplicative (FreeAbelianGroup (Y ⟶ X)) := Multiplicative.ofAdd (FreeAbelianGroup.of q)

def ratSub {L : LB X} (e₀ e₁ : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Subgroup (Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (Z.presheaf.stalk z)ˣ) where
  carrier := {g | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ ∏ k, pt (φ k) ^ ε k = g.1 ∧ val t e₁ z J = g.2 * val t e₀ z J}
  one_mem' := ⟨PEmpty, inferInstance, _, _, LB.oneGen L, (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm), Fintype.prod_empty _, by
      rw [val_one, val_one]; exact (_root_.mul_one _).symm⟩
  mul_mem' := by
    rintro g g' ⟨K, _, φ, ε, t, ht, f, v⟩ ⟨K', _, φ', ε', t', ht', f', v'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
      DVR.prod_sum₂ _ f f', ?_⟩
    rw [val_mul hJ, val_mul hJ, v, v']
    exact mul_mul_mul_comm _ _ _ _
  inv_mem' := by
    rintro g ⟨K, _, φ, ε, t, ht, f, v⟩
    refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, DVR.prod_neg _ _ f, ?_⟩
    rw [val_inv, val_inv, v]
    exact mul_inv _ _

theorem ratSub_eq_one {L : LB X} (hL : L.IsLB) (p : Y ⟶ Z) (e₀ e₁ : Z ⟶ Y) (h₀ : e₀ ≫ p = 𝟙 _) (h₁ : e₁ ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    {g : Multiplicative (FreeAbelianGroup (Y ⟶ X)) × (Z.presheaf.stalk z)ˣ} (hg : g ∈ ratSub e₀ e₁ hJ) (h : g.1 = 1) :
    g.2 = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, f, v⟩ := hg
  have triv : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (φ i) ^ ε i = 1 := fun U _ k => by
    let F : Multiplicative (FreeAbelianGroup (Y ⟶ X)) →* U :=
      AddMonoidHom.toMultiplicativeLeft (FreeAbelianGroup.lift fun q => Additive.ofMul (k q))
    have hF : ∀ q, F (pt q) = k q := fun q => by simp [F, pt]
    have := congrArg F (f.trans h)
    simpa only [map_prod, map_zpow, hF, map_one] using this
  have key := gen_unique' hL (φ := φ) (ε := ε) (φ' := fun k => (p ≫ e₀) ≫ φ k) (ε' := ε)
    (fun U _ k => (triv U fun q => k ((p ≫ e₀) ≫ q)).trans (triv U k).symm) p e₀ h₀ hp ht
    (DVR.pullGen_isGen _ _ _ _ ht (p ≫ e₀)) (fun y I hI => by
      rw [val_pull hI, ← Category.assoc, h₀, Category.id_comp]) _ e₁ z J hJ
  rw [val_pull hJ, ← Category.assoc, h₁, Category.id_comp, v] at key
  exact mul_eq_right.1 key

end General

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T B : Over (Spec (CommRingCat.of R))}

theorem prod_tφ (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) (ρ : B ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : (B.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ tφ D a β i) ^ tε n j i =
      h ρ.left ^ (n - 1) * h (ρ * DVR.cP D B β).left * (h (DVR.cP D B β).left)⁻¹ * h (1 : B ⟶ D.P.A).left *
        h (ρ ≫ a).left ^ j := by
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ tφ D a β 1 = (ρ * DVR.cP D B β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D B β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : B ⟶ D.P.A).left :=
    congrArg (fun q : B ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

variable (ρ₀ ρ₁ : T ⟶ B) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)

theorem mem_const (κ : B ⟶ TK R) (hκ : ρ₁ ≫ κ = ρ₀ ≫ κ) (χ : D.X) :
    (pt (DVR.cP D B χ).left, 1) ∈ ratSub ρ₀.left ρ₁.left hJ := by
  refine (Subgroup.inv_mem_iff _).1 ⟨PUnit, inferInstance, _, _, LB.pullGen D.P.L _ _ (D.psi χ) κ.left,
    DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _, ?_, ?_⟩
  · rw [Fintype.prod_unique, zpow_neg_one, ← DVR.comp_cP D κ χ]; rfl
  · rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, hκ]
    simp

theorem mem_cub (x x' y : B ⟶ D.P.A) :
    (pt (x * x' * y).left * (pt (x * x').left)⁻¹ * (pt (x * y).left)⁻¹ * (pt (x' * y).left)⁻¹ * pt x.left * pt x'.left *
        pt y.left * (pt (1 : B ⟶ D.P.A).left)⁻¹,
      cubV D.cub z J (ρ₁ ≫ x) (ρ₁ ≫ x') (ρ₁ ≫ y) * (cubV D.cub z J (ρ₀ ≫ x) (ρ₀ ≫ x') (ρ₀ ≫ y))⁻¹) ∈
      ratSub ρ₀.left ρ₁.left hJ :=
  ⟨thK, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left,
    DVR.pullGen_isGen _ _ _ _ D.cub.isGen _, prod_cub x x' y pt,
    (val_cub D.cub ρ₁ hJ x x' y).trans ((inv_mul_cancel_right _ _).symm.trans
      (congrArg (_ * ·) (val_cub D.cub ρ₀ hJ x x' y).symm))⟩

theorem mem_ros (f g : D.P.A ⟶ D.P.A) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (x y : B ⟶ D.P.A) :
    (pt ((x ≫ f) * y).left * (pt (x ≫ f).left)⁻¹ * (pt y.left)⁻¹ * (pt (x * (y ≫ g)).left)⁻¹ * pt x.left * pt (y ≫ g).left,
      val₂ u z J (ρ₁ ≫ x) (ρ₁ ≫ y) * (val₂ u z J (ρ₀ ≫ x) (ρ₀ ≫ y))⁻¹) ∈ ratSub ρ₀.left ρ₁.left hJ := by
  refine ⟨Fin 6, inferInstance, _, _, LB.pullGen D.P.L _ _ u (lift x y).left,
    DVR.pullGen_isGen _ _ _ _ hu _, prod_ros f g x y pt, ?_⟩
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift]
  exact (inv_mul_cancel_right _ _).symm

end Points

theorem mem_of_add {X G : Type} [AddCommGroup X] [CommGroup G] (H : Subgroup G) (l : X → G)
    (hl : ∀ a b, l (a + b) * (l a)⁻¹ * (l b)⁻¹ ∈ H) (n j : ℤ) (β ν δ : X) :
    l (β + (n • ν + j • δ)) * (l β * l ν ^ n * l δ ^ j)⁻¹ ∈ H := by
  let f : X →+ Additive (G ⧸ H) := AddMonoidHom.mk' (fun a => Additive.ofMul (QuotientGroup.mk' H (l a))) (fun a b => by
    have := (QuotientGroup.eq_one_iff _).2 (hl a b)
    rw [← QuotientGroup.mk'_apply, map_mul, map_mul, map_inv, map_inv, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at this
    rw [this, ofMul_mul])
  have e : f (β + (n • ν + j • δ)) = f β + (n • f ν + j • f δ) := by simp only [map_add, map_zsmul]
  refine (QuotientGroup.eq_one_iff _).1 ?_
  rw [← QuotientGroup.mk'_apply, map_mul, map_inv, map_mul, map_mul, map_zpow, map_zpow, mul_inv_eq_one, _root_.mul_assoc]
  exact congrArg Additive.toMul e

theorem val_fac {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (a a' : D.P.A ⟶ D.P.A)
    (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (n j : ℤ) (ν mu β₀ β₁ : D.X) (hβ : β₁ = β₀ + shift h h' n j ν)
    (u₁ : LB.Gen (LB.LinComb D.P.L (dφ D a ν β₀ β₁) (dε n j))) (hu₁ : IsFac D a h n j ν β₀ β₁ u₁)
    (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    val u₁ ((DegPre.zF D (FractionRing R)).left ≫ (DegPre.trF D (FractionRing R) mu).left) z J =
      (val (D.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n *
        val (D.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) *
      (val (D.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ := by
  obtain ⟨ha, ha', hr, hc, hc', hbal⟩ := hE
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  let T : Over (Spec (CommRingCat.of R)) := TF (R := R) (FractionRing R)
  let B : Over (Spec (CommRingCat.of R)) := DegPre.BF D (FractionRing R)
  let ρ₀ : T ⟶ B := DegPre.zF D (FractionRing R)
  let ρ₁ : T ⟶ B := DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu
  let x : B ⟶ D.P.A := DegPre.prB D (FractionRing R)
  let p : B ⟶ T := fst _ _
  let κ : T ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have tx : ∀ χ, DegPre.trF D (FractionRing R) χ ≫ x = x * DVR.cP D B χ := fun χ => lift_snd _ _
  have p₀ : ρ₀ ≫ p = 𝟙 _ := lift_fst _ _
  have p₁ : ρ₁ ≫ p = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (ρ₀ ≫ ·) (lift_fst _ _)).trans p₀)
  have x₀ : ρ₀ ≫ x = 1 := lift_snd _ _
  have x₁ : ρ₁ ≫ x = DVR.cP D T mu := by
    refine (Category.assoc _ _ _).trans ((congrArg (ρ₀ ≫ ·) (tx mu)).trans ((MonObj.comp_mul _ _ _).trans ?_))
    rw [x₀, DVR.comp_cP, _root_.one_mul]
  have ca : ∀ S χ, DVR.cP D S χ ≫ a = DVR.cP D S (h χ) := fun S χ => by rw [DVR.cP, DVR.cP, hc, Category.assoc]
  have ca' : ∀ S χ, DVR.cP D S χ ≫ a' = DVR.cP D S (h' χ) := fun S χ => by rw [DVR.cP, DVR.cP, hc', Category.assoc]
  have c0 : DVR.cP D B 0 = 1 := by simpa using DVR.cPoint_nsmul D B 0 0
  have s : (𝟙 T : T ⟶ T).left ≫ jFK (R := R) (FractionRing R) = jFK (R := R) (FractionRing R) := Category.id_comp _

  let τ : D.X → D.X → (T.left.presheaf.stalk z)ˣ := fun χ χ' => val (D.tau χ χ') (jFK (R := R) (FractionRing R)) z J
  have tm : ∀ χ χ' b, τ (χ + χ') b * cubV D.cub z J (DVR.cP D T χ) (DVR.cP D T χ') (DVR.cP D T b) = τ χ b * τ χ' b :=
    fun χ χ' b => by have := DVR.tau_mul (𝟙 T) hJ hB χ χ' b; rw [s] at this; exact this
  have ts : ∀ χ χ', τ χ χ' = τ χ' χ := fun χ χ' => by have := DVR.tau_symm (𝟙 T) hJ χ χ'; rw [s] at this; exact this
  let ψ : D.X → (T.left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (jFK (R := R) (FractionRing R)) z J
  let rg : (T.left.presheaf.stalk z)ˣ := val D.rigK (jFK (R := R) (FractionRing R)) z J
  have pa : ∀ χ χ', ψ (χ + χ') = τ χ χ' * ψ χ * ψ χ' * rg := fun χ χ' => by
    have := DVR.UUA.psi_add (𝟙 T) hJ χ χ'; rw [s] at this; exact this
  have tb : τ (h mu) (h ν) * val₂ u (T := T) z J (DVR.cP D T mu) (DVR.cP D T (h ν)) = τ mu (h' (h ν)) := by
    have := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ mu (h ν)) κ.left)
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    rw [val_pull hJ, val₂, ← DVR.comp_cP D κ, ← DVR.comp_cP D κ, ← comp_lift]
    rfl
  have r₀ : val₂ u (T := T) z J 1 (DVR.cP D T (h ν)) = 1 := by
    have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ (h ν))).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm

  have mc : ∀ χ, (pt (DVR.cP D B χ).left, 1) ∈ ratSub ρ₀.left ρ₁.left hJ :=
    mem_const ρ₀ ρ₁ hJ (p ≫ κ) (by rw [← Category.assoc, ← Category.assoc, p₀, p₁])
  have ml := mem_of_add (ratSub ρ₀.left ρ₁.left hJ) (fun χ => (pt (DVR.cP D B χ * x).left * (pt x.left)⁻¹ *
      (pt (DVR.cP D B χ).left)⁻¹ * pt (1 : B ⟶ D.P.A).left, (τ χ mu)⁻¹)) (fun χ χ' => by
    have m := mem_cub ρ₀ ρ₁ hJ (DVR.cP D B χ) (DVR.cP D B χ') x
    simp only [DVR.comp_cP, x₀, x₁, C.face₃] at m
    convert m using 1
    have t := congrArg Additive.ofMul (tm χ χ' mu)
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, DVR.cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · simp only [Prod.snd_mul, Prod.snd_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at t ⊢
      linear_combination (norm := abel) -t) n j β₀ ν (h' (h ν))
  rw [show β₀ + (n • ν + j • h' (h ν)) = β₁ from hβ.symm] at ml
  have mr := mem_ros ρ₀ ρ₁ hJ a a' u hu x (DVR.cP D B (h ν))
  simp only [DVR.comp_cP, x₀, x₁, r₀, ca'] at mr
  have mk := mem_cub ρ₀ ρ₁ hJ (DVR.cP D B ν) x (DVR.cP D B β₀)
  simp only [DVR.comp_cP, x₀, x₁, C.face₂] at mk
  have f₁ := prod_tφ a n j β₁ x pt
  have f₀ := prod_tφ a n j β₀ (DegPre.trF D (FractionRing R) ν ≫ x) pt
  have mu₁ : (_, val u₁ ρ₁.left z J * (val u₁ ρ₀.left z J)⁻¹) ∈ ratSub ρ₀.left ρ₁.left hJ :=
    ⟨Fin 5 ⊕ Fin 5, inferInstance, _, _, u₁, hu₁.1, DVR.prod_sum₂ _ f₁ (DVR.prod_neg _ _
      ((Finset.prod_congr rfl fun i _ => by rw [Over.comp_left, Category.assoc]; rfl).trans f₀)),
      (inv_mul_cancel_right _ _).symm⟩
  rw [tx, MonObj.mul_comp, ca] at mu₁
  have key := ratSub_eq_one D.P.isLB p.left ρ₀.left ρ₁.left (congrArg (fun q => q.left) p₀) (congrArg (fun q => q.left) p₁)
    (DVR.surj_appTop D (FractionRing R) hG) hJ
    (mul_mem (mul_mem (mul_mem (mul_mem mu₁ (inv_mem ml)) (zpow_mem mr j)) mk)
      (mul_mem (mul_mem (mul_mem (mul_mem (mc (ν + β₀)) (zpow_mem (mc ν) (n - 1))) (inv_mem (mc β₀)))
        (zpow_mem (mc 0) (1 - n - j))) (zpow_mem (mc (h ν)) j))) (by
      simp only [Prod.fst_mul, Prod.fst_inv, Prod.pow_fst, DVR.cPoint_add, c0, _root_.mul_comm (DVR.cP D B _) x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have v₀ := hu₁.2 z J hJ
  simp only [Prod.snd_mul, Prod.snd_inv, Prod.pow_snd] at key
  show val u₁ ρ₁.left z J = ψ (ν + mu) ^ n * ψ (h (ν + mu)) ^ j * τ (ν + mu) β₀ * rg ^ (n + j) *
    (ψ mu ^ n * ψ (h mu) ^ j * τ mu β₁ * rg ^ (n + j))⁻¹
  change val u₁ ρ₀.left z J = ψ ν ^ n * ψ (h ν) ^ j * τ ν β₀ * rg ^ (n + j) at v₀
  rw [map_add, pa, pa]
  rw [v₀, ts β₁, ts β₀, ts (h' (h ν)), ← tb, ts (h mu)] at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  have t := congrArg Additive.ofMul (tm ν mu β₀)
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, smul_add, smul_neg] at k t ⊢
  linear_combination (norm := module) k - t

theorem val_fac_at_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ : D.toPre.X), β₁ = β₀ + shift h h' n j ν → ∀ (u₁ : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a ν β₀ β₁) (dε n j))), IsFac D.toPre a h n j ν β₀ β₁ u₁ → ∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val u₁ ((DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J = (val (D.toPre.psi (ν + mu)) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h (ν + mu))) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau (ν + mu) β₀) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)) * (val (D.toPre.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.toPre.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j * val (D.toPre.tau mu β₁) (jFK (R := R) (FractionRing R)) z J * val D.toPre.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j))⁻¹ :=
  fun _ _ _ _ _ D a a' h h' hE n j ν mu β₀ β₁ hβ u₁ hu₁ z J hJ =>
    val_fac D.toPre D.tau_bimult a a' h h' hE n j ν mu β₀ β₁ hβ u₁ hu₁ z J hJ

end GlobalTheory.TwFacVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericProductInequality
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowerCx

theorem numeric_product_inequality (Dc ψe ψx lam n' bu be : ℂ) (hlam : lam ≠ 0) (hψe : ψe ≠ 0) (hbe : be ≠ 0)
    (hX : lam * ψx = n' * bu) (hE : lam * ψe = n' * be) : Dc / ψe * ψx = Dc * (bu / be) := by
  have key : ψx * be = ψe * bu :=
    mul_left_cancel₀ hlam (by linear_combination be * hX - bu * hE)
  field_simp
  linear_combination Dc * key

theorem baseChange_inK {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {H : Type} [AddCommGroup H]
    [Module R H] (B : LinearMap.BilinForm R H) (u v : H) :
    B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) K H u) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) K H v) = algebraMap R K (B u v) := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

theorem polForm_bc' {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply Limits.pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem formRel : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p) (c₀ c₁ : 𝔠.elt),
    (c₁ : FR E) ≠ 0 → ∀ (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)) (ψ : LinearMap.BilinForm ℂ (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ψ₀ → IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag c₁) ψ →
    ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y →
      ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by
  intro hADR E _ _ _ 𝔠 R X₀ X p hpull m c₀ c₁ hc₁ ψ₀ ψ hψ₀ hψ
  obtain ⟨ψ₀', hψ₀', hcorr⟩ := polForm_bc' (algebraMap R ℂ) hpull m c₀ hψ₀
  obtain ⟨n', t, hn', ht⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hADR (FR E) 𝔠 ℂ X c₀ c₁ hc₁ ψ₀' ψ hψ₀' hψ
  exact ⟨n', t, hn', fun x₀ y₀ x y hx hy ↦ by rw [← ht, hcorr x₀ x y₀ y hx hy]⟩

set_option maxHeartbeats 1000000 in

theorem lower_cx : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (y : (Af E)ˣ) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X)
    (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
    ∀ (D : R), D ≠ 0 →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
    ∀ (N : I → Module.End (FractionRing R) (FractionRing R ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (e' i) (f' i) (N i)) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A), (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
    ∀ i, ψ (ev i) (yv i) ≠ 0 ∧ ∀ x₀ x, m.Corr x₀ x →
      m.Corr (eH.symm.conjRingEquiv (M i) x₀) ((((D : ℂ) / ψ (ev i) (yv i)) • (ψ.flip (yv i)).smulRight (yv i)) x) := by
  intro hPC hADR hADC E _ _ _ I _ φ c y 𝔠 R _ X₀ X U p cm hpull hcm hα j hj φK hφK n eH c₀ ψ₀ hc₀ hψ₀ hlat hcmt D hD
    e' f' hgens N M hlow hscal m hbc ψ hψ yv ev hyv hev i
  classical
  set ρ := eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm) with hρ
  set B := (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) with hB
  have hc : c ≠ ⊥ := GlobalTheory.Div.ConjugateOrderConductor.main E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hgens (hlow i)
  have hcard : 2 * Fintype.card I = Module.finrank ℚ E := by
    rw [← Fintype.card_congr U.e, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ (FR E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have hint := GlobalTheory.EigLineSumCM.eigK_isInternal_of_cmType E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat hcmt hcard
  have horth := GlobalTheory.Div.PairingEigenspaceOrthogonal.pairing_eig_orth E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat
  obtain ⟨hBef, hN⟩ := GlobalTheory.Div.LowerPairFormula.lower_pair_formula E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hint horth hgens (hlow i)
  have hU : ((U.c : FR E)) ≠ 0 := by
    intro h0
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace (FR E)))
    have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
    have := U.pos (NumberField.InfinitePlace.embedding_of_isReal hw)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨n', t, hn', hrel⟩ : ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y →
      ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by
    obtain ⟨n₁, t, hn₁, h⟩ := formRel hADR E 𝔠 R X₀ X p hpull m c₀ U.c hU _ ψ hψ₀ hψ
    refine ⟨n₁ * 2, t, mul_ne_zero hn₁ two_ne_zero, fun x₀ y₀ x y hx hy ↦ ?_⟩
    rw [h x₀ y₀ x y hx hy, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_ofNat]
    push_cast
    ring
  set a : orderC c := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t
  have hact : ∀ y₀ y', m.Corr y₀ y' →
      m.Corr (act (dp0 R) (𝟙 _) X₀.rm t y₀) (act (dp0 ℂ) (𝟙 _) X.rm t y') := by
    intro y₀ y' h
    haveI := X₀.rm.hom t
    haveI := X.rm.hom t
    exact GrpMor.Corr.push m (X₀.rm.act t) (X.rm.act t) (hpull.act t).symm h
  have hcmt' : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm a := by
    haveI := X₀.rm.hom t
    haveI := cm.hom a
    rw [act_apply, act_apply]
    exact push_congr _ _ (hcm t).symm
  have hρa : ∀ v, eH.symm (ρ a v) = act (dp0 R) (𝟙 _) cm a (eH.symm v) := by
    intro v
    simp [hρ, LinearEquiv.conjRingEquiv]
  have hfmem : f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := FractionRing R) ρ
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := by
    rw [(hgens i).2]; exact Submodule.mem_span_singleton_self _
  have hinKa : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (ρ a (f' i)) =
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E) •
        GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (f' i) := by
    rw [GlobalTheory.EigenLattice.inK_apply_map]
    exact GlobalTheory.LowerOps.act_of_mem_eigK hfmem a
  set lam := j ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E))
  have hty : act (dp0 ℂ) (𝟙 _) X.rm t (yv i) = lam • yv i := by
    refine GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (ρ a (f' i)) (f' i) _ hinKa _ _ ?_ (hyv i)
    rw [hρa, ← hcmt']
    exact hact _ _ (hyv i)
  have hrel' : ∀ x₀ x, m.Corr x₀ x → lam * ψ x (yv i) = n' * algebraMap R ℂ (ψ₀ x₀ (eH.symm (f' i))) := by
    intro x₀ x hx
    rw [← hrel x₀ _ x (yv i) hx (hyv i), hty, map_smul, smul_eq_mul]
  have hE := hrel' _ _ (hev i)
  have hσB : ∀ u, algebraMap R ℂ (ψ₀ (eH.symm u) (eH.symm (f' i))) = j (algebraMap R (FractionRing R) (B u (f' i))) :=
    fun u ↦ (hj _).symm
  have hBne : j (algebraMap R (FractionRing R) (B (e' i) (f' i))) ≠ 0 := by
    rw [hj]
    intro h0
    exact hBef (Subtype.ext (by simpa using h0))
  have hne : (n' : ℂ) * algebraMap R ℂ (ψ₀ (eH.symm (e' i)) (eH.symm (f' i))) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn') (by rw [hσB]; exact hBne)
  rw [← hE] at hne
  have hlam : lam ≠ 0 := left_ne_zero_of_mul hne
  have hψne : ψ (ev i) (yv i) ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨hψne, fun x₀ x hx ↦ ?_⟩
  have hx₀ : x₀ = eH.symm (eH x₀) := (eH.symm_apply_apply x₀).symm
  have hX := hrel' x₀ x hx
  rw [hx₀, hσB] at hX
  rw [hσB] at hE
  have hMK : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (M i (eH x₀)) =
      (algebraMap R (FractionRing R) D * (algebraMap R (FractionRing R) (B (eH x₀) (f' i)) /
        algebraMap R (FractionRing R) (B (e' i) (f' i)))) •
        GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (f' i) := by
    rw [hscal i (eH x₀), hN, smul_smul]
    rw [baseChange_inK]
  obtain ⟨Z, hZ⟩ := hbc.exists (eH.symm (M i (eH x₀)))
  have hZ' := GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (M i (eH x₀)) (f' i) _ hMK Z (yv i) hZ (hyv i)
  have hL : eH.symm.conjRingEquiv (M i) x₀ = eH.symm (M i (eH x₀)) := by
    simp [LinearEquiv.conjRingEquiv]
  rw [hL]
  convert hZ using 1
  rw [hZ', LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.BilinForm.flip_apply, smul_smul, map_mul, map_div₀, hj D]
  congr 1
  exact numeric_product_inequality _ _ _ _ _ _ _ hlam hψne hBne hX hE

end GlobalTheory.LowerCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_eq_zero_of_pullbacks_eq_zero_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  first | exact @GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero | exact GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero <;> assumption)
end


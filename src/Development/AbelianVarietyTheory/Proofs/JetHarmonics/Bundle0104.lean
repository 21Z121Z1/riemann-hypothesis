import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Formalism.LocalToGlobal.ProjectiveLattices.TensPtsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPull

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem trPt_aF (oa : D.toPre.OAct O) (a : O) (b b' : TF (R := V) F ⟶ D.toPre.P.A)
    (hb : b' = b ≫ oa.onB.act a) :
    DegPre.trPt D.toPre F b ≫ aF D F oa a = aF D F oa a ≫ DegPre.trPt D.toPre F b' := by
  have := oa.onB.hom a
  have ap : aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := by
    simp [aF, DegPre.prB]
  have af : aF D F oa a ≫ fst (TF (R := V) F) D.toPre.P.A = fst _ _ := lift_fst _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, af, tr_fst, Category.assoc, tr_fst, af]
  · show (DegPre.trPt D.toPre F b ≫ aF D F oa a) ≫ DegPre.prB D.toPre F =
      (aF D F oa a ≫ DegPre.trPt D.toPre F b') ≫ DegPre.prB D.toPre F
    rw [Category.assoc, ap, ← Category.assoc, tr_pr, MonObj.mul_comp, Category.assoc, ← hb,
      Category.assoc, tr_pr, MonObj.comp_mul, ap, ← Category.assoc, af]

theorem gen_eq_of_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hy : p₁.y = star a • p'.y) (hb : p'.g.b = p₁.g.b ≫ oa.onB.act a)
    (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ + p'.y)) (pullε k N))) (huχz : uχz.IsGen)
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k))) (hΨ : Ψ.IsGen)
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hΦ : Φ.IsGen)
    (horig : ∀ y J, Good D.toPre.P.L y J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
          (DegPre.zF D.toPre F).left y J =
        val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
          (DegPre.zF D.toPre F).left y J)
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z' : Z) (J) (hJ : Good D.toPre.P.L z' J) :
    val uχ (ρ ≫ (DegPre.trPt D.toPre F p₁.g.b).left) z' J * val Φ ρ z' J =
      val uχz ρ z' J * val Ψ (ρ ≫ (aF D F oa a).left) z' J := by
  have e1 : ∀ i, (DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left, trPt_aF oa a p₁.g.b p'.g.b hb]
  have e2 : ∀ i, (aF D F oa a).left ≫ (DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left]
  have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
  have hF : FormEq (Sum.elim (pullφ D F oa a (χ + p'.y))
      (fun i => (aF D F oa a).left ≫ DegPre.phiφ D.toPre F p'.y χ p'.g.b i)) (Sum.elim (pullε k N) (DegPre.deltaε k))
      (Sum.elim (fun i => (DegPre.trPt D.toPre F p₁.g.b).left ≫ pullφ D F oa a χ i)
        (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b)) (Sum.elim (pullε k N) (DegPre.deltaε (k * N))) :=
    fun U _ h => by
      simp only [pullφ, pullε, DegPre.phiφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, e1, e2, e3]
      simp only [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  have key := gen_unique' D.toPre.P.isLB hF (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (GC.zF_fst (D := D) (F := F)) (surj_appTop D.toPre F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ huχ _) hΦ)
    (mulGen_isGen _ _ _ _ _ _ _ huχz (pullGen_isGen _ _ _ _ hΨ _)) horig Z ρ z' J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ] at key
  exact key

theorem exists_normalisation (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (b b' : TF (R := V) F ⟶ D.toPre.P.A) (hb : b' = b ≫ oa.onB.act a)
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b') (DegPre.lineε k))) (hw' : w'.IsGen)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen) :
    ∃ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b) (DegPre.lineε (k * N))), w.IsGen ∧
      ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left y J)⁻¹ := by
  have := oa.onB.hom a
  have h1 : (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b :=
    CanonicalLiftTraces.zF_tr_pr b
  have h2 : ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = b' := by
    rw [Category.assoc, show aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a by
      simp [aF, DegPre.prB], ← Category.assoc, h1, hb]
  have e2 : ∀ i, (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left ≫ (aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i = ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i := fun i => by rw [← Category.assoc, ← Over.comp_left]
  have c0 : cP D.toPre (TF (R := V) F) 0 = 1 := cPoint_zero _
  have p0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
  have p1 : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  have hN' : ((k * (N - 1) : ℕ) : ℤ) = ((k * N : ℕ) : ℤ) - k := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]; push_cast; ring
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F b) (ε' := DegPre.lineε (k * N))
    (fun U _ h => by
      simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, e2, p1]
      simp only [CanonicalLiftTraces.comp_famφ, h1, h2, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val,
        DegPre.famε, smul_zero, c0, _root_.mul_one, DegPre.lineφ, DegPre.lineε, p0, hN']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) w')
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _) hw')
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu0 _)))
  refine ⟨w, hw, fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ u0, Category.id_comp]

theorem gen_eq_at_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hgt : GtAct oa a p₁.g p'.g)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))))
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p₁.g.b).left y J)⁻¹)
    (χ ξ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a ξ) (pullε k N)))
    (hcz : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχz (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k)))
    (hcΨ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Ψ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p'.g.s χ) w'))
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hcΦ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Φ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p₁.g.s (star a • χ)) w))
    (y : (TF (R := V) F).left) (J) (hJ : Good D.toPre.P.L y J) :
    val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
        (DegPre.zF D.toPre F).left y J =
      val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
        (DegPre.zF D.toPre F).left y J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hros := oa.onB.rosati (star a)
  rw [star_star] at hros
  obtain ⟨r, hr, hr0⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hros
  have hl : ((DegPre.zF D.toPre F).left ≫ (DegPre.trPt D.toPre F p₁.g.b).left) ≫
      (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left = (lift (DegPre.cF D.toPre F χ) p₁.g.b).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_cP, CanonicalLiftTraces.zF_tr_pr]
    rfl
  have e1 := val_corr hJ hcz (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e1
  have e2 := val_corr hJ hcΨ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e2
  have e3 := val_corr hJ hcΦ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e3
  have e5 := hwv y J hJ
  rw [Over.comp_left] at e5
  have e6 := val_corr hJ (hgt.2 r hr hr0 χ) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, Category.id_comp] at e6
  have e7 : val Ψ ((DegPre.zF D.toPre F).left ≫ (aF D F oa a).left) y J = val Ψ (DegPre.zF D.toPre F).left y J := by
    rw [← Over.comp_left, CanonicalLiftTraces.zF_aF]
  rw [val_mul hJ, val_pull hJ, val_mul hJ, val_pull hJ, e3,
    CanonicalLiftValuation.pull_val_chi hG oa a k N χ uχ huχ hc u0 hu0 hc0 r hr hr0 _ _ y J hJ, val_pull hJ, hl,
    e5, e7, e1, e2, ← e6]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiRel_pullAl : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (p' : QkPt D.toPre F k) (p₁ : QkPt D.toPre F (k * N)), GtAct oa a p₁.g p'.g → p₁.y = star a • p'.y → ∀ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen → ∃ w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))), w₁.IsGen ∧ ∀ (s t : Fam D.toPre F k) (s' t' : Fam D.toPre F (k * N)), PhiRel D.toPre F k p' w' s t → PullAl D F oa a k N s s' → PullAl D F oa a k N t t' → PhiRel D.toPre F (k * N) p₁ w₁ s' t' := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw0 a N k hN _ haa p' p₁ hgt hy w' hw'
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := hw0
  obtain ⟨u0, hu0, hc0⟩ := exists_pullGen D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k 0
  obtain ⟨w, hw, hwv⟩ := exists_normalisation oa a k N hN p₁.g.b p'.g.b hgt.1 w' hw' u0 hu0
  refine ⟨w, hw, fun s t s' t' hst hs' ht' => ?_⟩
  rw [phiRel_iff hG p₁ w hw s' t']
  intro a' β hβ T ρ z' J hJ
  by_cases ha : ∃ χ, a' = star a • χ
  · obtain ⟨χ, rfl⟩ := ha
    subst hβ
    have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
    rw [e3]
    obtain ⟨uχz, huχz, hcz, hsz⟩ := ht'.1 (χ + p'.y)
    obtain ⟨uχ, huχ, hc, hs⟩ := hs'.1 χ
    obtain ⟨⟨Ψ, hΨ, hcΨ⟩, -⟩ := gen_phi hG p' w' hw' χ
    obtain ⟨⟨Φ, hΦ, hcΦ⟩, hΦv⟩ := gen_phi hG p₁ w hw (star a • χ)
    have s1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχz).1 hsz _ ρ.left z' J hJ
    have s2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ Ψ).1 (hst χ Ψ hΨ hcΨ) _
      (ρ.left ≫ (aF D F oa a).left) z' J hJ
    have s3 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχ).1 hs _ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J hJ
    have pt : (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left =
        (ρ.left ≫ (aF D F oa a).left) ≫ (DegPre.trPt D.toPre F p'.g.b).left := by
      rw [← Over.comp_left, Category.assoc, trPt_aF oa a p₁.g.b p'.g.b hgt.1, ← Category.assoc, Over.comp_left,
        Over.comp_left]
    have eig := gen_eq_of_origin hG oa a k N p' p₁ hy hgt.1 χ uχ huχ uχz huχz Ψ hΨ Φ hΦ
      (fun y J hJ => gen_eq_at_origin hG oa a k N p' p₁ hgt u0 hu0 hc0 w' w hwv χ _ uχ huχ hc uχz hcz Ψ hcΨ
        Φ hcΦ y J hJ) _ ρ.left z' J hJ
    have hΦρ := hΦv Φ hΦ hcΦ T ρ z' J hJ
    have eig' : (val Ψ (ρ.left ≫ (aF D F oa a).left) z' J).val * (val uχz ρ.left z' J).val =
        (val uχ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J).val * (val Φ ρ.left z' J).val := by
      rw [← Units.val_mul, ← Units.val_mul, _root_.mul_comm]
      exact congrArg Units.val eig.symm
    rw [s1, s2, s3, pt, ← hΦρ, _root_.mul_assoc, _root_.mul_assoc, eig']
  · have hβn : ∀ χ, β ≠ star a • χ := by
      intro χ h
      apply ha
      refine ⟨χ - p'.y, ?_⟩
      rw [smul_sub, ← h, ← hβ, hy]
      abel
    rw [CanonicalLiftFrobenius.sval_zero _ (ht'.2 β hβn), CanonicalLiftFrobenius.sval_zero _ (hs'.2 a' (fun χ h => ha ⟨χ, h⟩)),
      MulZeroClass.zero_mul]

end GlobalTheory.ThetaPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

def lamE (σ : D.host.E →+* ℂ) : D.host.E →+* ℂ_[p] := lam.comp (σ.codRestrict Qbar (emb_mem D σ))

theorem lamC_emb (σ : D.host.E →+* ℂ) (x : D.host.E) : lamC lam (σ x) = lamE D lam σ x := dif_pos (emb_mem D σ x)

def homP : D.host.K →+* ℂ_[p] := (lamE D lam D.host.φ₀).comp (algebraMap D.host.K D.host.E)

def homPbar : D.host.K →+* ℂ_[p] := (homP D lam).comp (conjK D)

theorem atP₂ (c : D.host.K) : atP D lam c = homP D lam c := lamC_emb D lam _ _

theorem atPbar_eq (c : D.host.K) : atPbar D lam c = homPbar D lam c := lamC_emb D lam _ _

theorem conjK_conjK (c : D.host.K) : conjK D (conjK D c) = c := Subtype.ext (conj_conj D _)

theorem homP_conjK (c : D.host.K) : homP D lam (conjK D c) = homPbar D lam c := rfl

theorem homPbar_conjK (c : D.host.K) : homPbar D lam (conjK D c) = homP D lam c := by
  show homP D lam (conjK D (conjK D c)) = _
  rw [conjK_conjK]

theorem norm_int_le (ψ : D.host.K →+* ℂ_[p]) (a : 𝓞 D.host.K) : ‖ψ (a : D.host.K)‖ ≤ 1 := by
  obtain ⟨f, hf, h0'⟩ := RingOfIntegers.isIntegral_coe a
  have h0 : f.eval₂ (Int.castRingHom ℂ_[p]) (ψ (a : D.host.K)) = 0 := by
    have := congrArg ψ h0'
    rw [Polynomial.hom_eval₂, map_zero] at this
    rwa [Subsingleton.elim (Int.castRingHom ℂ_[p]) (ψ.comp (algebraMap ℤ D.host.K))]
  by_contra hlt
  rw [not_le] at hlt
  set x := ψ (a : D.host.K)
  rw [hf.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, add_eq_zero_iff_eq_neg] at h0
  have h1 : ‖x ^ f.natDegree‖ ≤ ‖x‖ ^ f.natDegree / ‖x‖ := by
    rw [h0, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow, le_div_iff₀ (by linarith)]
    have h2 : ‖(Int.castRingHom ℂ_[p]) (f.coeff i)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
    calc _ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by gcongr
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ _ := pow_le_pow_right₀ hlt.le (Finset.mem_range.1 hi)
  rw [norm_pow, le_div_iff₀ (by linarith)] at h1
  have : 0 < ‖x‖ ^ f.natDegree := by positivity
  nlinarith

def conjO (a : 𝓞 D.host.K) : 𝓞 D.host.K :=
  ⟨conjK D (a : D.host.K), (RingOfIntegers.isIntegral_coe a).map (conjK D).toIntAlgHom⟩

theorem coe_conjO (a : 𝓞 D.host.K) : ((conjO D a : 𝓞 D.host.K) : D.host.K) = conjK D (a : D.host.K) := rfl

theorem exists_trace_norm (c : D.host.K) :
    ∃ t n : ℚ, c + conjK D c = (t : D.host.K) ∧ c * conjK D c = (n : D.host.K) := by
  obtain ⟨-, σ, θ, hσ, hθ, hσθ, hx, -⟩ := quadratic_subfield D
  have e : conjK D c = σ c := Subtype.ext (hσ c).symm
  obtain ⟨a, b, rfl⟩ := hx c
  rw [e]
  refine ⟨2 * a, a ^ 2 + D.host.d * b ^ 2, ?_, ?_⟩
  · simp [hσθ]; ring
  · simp [hσθ]; linear_combination (-(b : D.host.K) ^ 2) * hθ

theorem isIdem_iff (m : ℕ) (ε : 𝓞 D.host.K) : IsIdem D lam m ε ↔
    ‖homP D lam (ε : D.host.K) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) ∧ ‖homPbar D lam (ε : D.host.K)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  rw [← atP₂, ← atPbar_eq]; rfl

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

theorem vecOf_add (A A' : Matrix (Fin N') (Fin N) D.host.E) :
    vecOf D cc δ (A + A') = vecOf D cc δ A + vecOf D cc δ A' := by
  funext τ i j
  simp [vecOf, embV, tor0, mul_add]

theorem vecOf_smul (c : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    vecOf D cc δ ((c : D.host.E) • A) = D.host.φ₀ (c : D.host.E) • vecOf D cc δ A := by
  funext τ i j
  have h := GlobalTheory.InducedType.restrict_K D
  simp only [vecOf, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h τ c]
  ring

theorem int_smul_mem_La (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (a : 𝓞 D.host.K) {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    D.host.φ₀ ((a : D.host.K) : D.host.E) • x ∈ La D (tor0 D cc δ) L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((a : D.host.K) : D.host.E) * w, ?_, A, hA, by rw [smul_smul]⟩
    change w ∈ lamOf D cc δ at hw
    change _ ∈ lamOf D cc δ
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
      push_cast
      rw [map_mul]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.PlaceComponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero => intro j _ w _; simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hk0 : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => by rw [pow_mul]; positivity
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ := fun v =>
      ((hκ.pow_const _).mul (hf v)).ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            have := mul_le_mul_of_nonneg_left (hx w) (hk0 x)
            simp only [Finset.mul_sum] at this
            calc κ x ^ (2 * (q + 1)) * f w x = κ x ^ (2 * q) * (κ x ^ 2 * f w x) := by ring
              _ ≤ _ := this
          refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finset_sum' _ (fun c _ => Finset.aemeasurable_fun_sum _ fun e _ => hm _)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [lintegral_finset_sum' _ (fun e _ => hm _)]
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ =>
            ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (∑ c, ∑ e, B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => by positivity)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (hs j w (by omega) hw) (pow_nonneg hB (2 * q))
          simp only [Finset.mul_sum] at this
          calc _ ≤ _ := this
            _ = _ := by ring

theorem ratio_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q hjq a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmass := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν).1
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS
  have hDS := hFam ν hν
  obtain ⟨hBe, hdg, -⟩ := hSF ν hν
  obtain ⟨hae, -, hlen, hl⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν).1
  obtain ⟨⟨hbv, -⟩, hsh⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hShape := (hsh ν hν).2.1
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (v : (R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (fun c e v => E ν c e v)
    (Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)))
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (by positivity) ((hlen _).div (hlen _))
    (fun v => (((hl (l ν) hBe.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _)
    (fun v x => by positivity) ?_
    (fun i v hv c e => GlobalTheory.lev_E_add_two _ _ _ _ _ i v hMod.1 hMod.2.1 hv c e)
    (fun i v hi hv => ?_) (fun v => hmass v v.2) q j hjq w hw
  · filter_upwards [hae] with x hx v
    have h1 := mul_le_mul_of_nonneg_left
      (GlobalTheory.T.bessel_cayley_side_bound hK k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDS hG hBe.1 hQ (hE ν hν).1
        _ hx a v) hdg.le
    simp only [Finset.mul_sum] at h1
    calc _ = _ := by ring
      _ ≤ _ := h1
  · have h1 := GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le _ _ _ _ _ k i bv b v hMod hShape hbv hi hv
    calc _ ≤ _ := h1
      _ = _ := by ring

end GlobalTheory.RatioMoment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RankMulFinrank
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankSum

theorem sum_lieMult {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {g : ℕ} (hG : SmoothOfRelativeDimension g G.hom) (act : OAct (𝓞 E) G) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (h : ∀ σ, LieMult act t σ (rk σ)) :
    ∑ σ : E →+* k, rk (σ.comp (algebraMap (𝓞 E) E)) = g := by
  classical
  have hk := isGrpPullback_pullback G t
  have hd : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hk.1 hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hd
  let actk := OAct.pullback t G act
  have hak : ∀ a, (actk.act a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv actk
  have hinj : Function.Injective fun σ : E →+* k => σ.comp (algebraMap (𝓞 E) E) := fun σ σ' e =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => RingHom.congr_fun e x
  have hσ : EigenSplit.IsSplitting fun σ : E →+* k => (RingHom.id k).comp (σ.comp (algebraMap (𝓞 E) E)) :=
    EigenSplit.isSplitting_of_isDomain hinj (NumberField.Embeddings.card E k) _
      (EigenSplit.isUnit_discr_of_charZero k)
  have hint := EigenSplit.isInternal_eigenSub hσ ρ
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun] at e
  rw [← e]
  exact Finset.sum_congr rfl fun σ _ => (LieEigen.finrank_of_lieMult hk hv hak hρ (h _)).symm

theorem rank_mul_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (act : OAct (𝓞 E) G) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (r : ℕ), (∀ σ : 𝓞 E →+* k, LieMult act t σ (rk σ) ∧ rk σ + rk (σ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) = r) → r * Module.finrank ℚ E = 2 * g := by
  intro E _ _ _ S G _ _ g hG act k _ _ _ t rk r h
  have h₁ := sum_lieMult hG act t rk fun σ => (h σ).1
  let c : (E →+* k) ≃ (E →+* k) :=
    ⟨fun σ => σ.comp (IsCMField.complexConj E : E →+* E), fun σ => σ.comp (IsCMField.complexConj E : E →+* E),
      fun σ => RingHom.ext fun a => by simp, fun σ => RingHom.ext fun a => by simp⟩
  have h₂ := (Equiv.sum_comp c fun σ => rk (σ.comp (algebraMap (𝓞 E) E))).trans h₁
  have h₃ : ∑ σ : E →+* k, (rk (σ.comp (algebraMap (𝓞 E) E)) + rk ((c σ).comp (algebraMap (𝓞 E) E))) =
      ∑ _σ : E →+* k, r := Finset.sum_congr rfl fun σ _ => (h _).2
  rw [Finset.sum_add_distrib, h₁, h₂, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    smul_eq_mul] at h₃
  rw [mul_comm, ← h₃, two_mul]

end GlobalTheory.LieRankSum
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem trF_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (mu : D.X) :
    (DegPre.trF D F mu).left ≫ (TF (R := R) F ◁ p).left =
      (TF (R := R) F ◁ p).left ≫ (DegPre.trF D₁ F (q mu)).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.trF D F mu ≫ (TF (R := R) F ◁ p) =
    (TF (R := R) F ◁ p) ≫ DegPre.trF D₁ F (q mu))
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerLeft_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd_assoc]
    have b : DegPre.prB D F ≫ p = (TF (R := R) F ◁ p) ≫ DegPre.prB D₁ F := (whiskerLeft_snd _ _).symm
    have e : (DegPre.prB D F * cP D _ mu) ≫ p = (TF (R := R) F ◁ p) ≫ (DegPre.prB D₁ F * cP D₁ _ (q mu)) := by
      rw [MonObj.mul_comp, MonObj.comp_mul, b, GlobalTheory.ProdUnif.cPoint_pr hc, comp_cP]
    exact e

theorem zF_pr {D D₁ : DegPre R} (p : D.P.A ⟶ D₁.P.A) [IsMonHom p] :
    (DegPre.zF D F).left ≫ (TF (R := R) F ◁ p).left = (DegPre.zF D₁ F).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.zF D F ≫ (TF (R := R) F ◁ p) = DegPre.zF D₁ F)
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem deltaφ_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (k : ℕ) (α mu : D.X) (a : Fin 4 ⊕ Fin 4) :
    DegPre.deltaφ D F k α mu a ≫ p.left = (TF (R := R) F ◁ p).left ≫ DegPre.deltaφ D₁ F k (q α) (q mu) a := by
  rcases a with a | a
  · refine (GlobalTheory.ProdUnif.famφ_pr hc F (α + k • mu) a).trans ?_
    rw [map_add, map_nsmul]; rfl
  · show ((DegPre.trF D F mu).left ≫ DegPre.famφ D F α a) ≫ _ =
      _ ≫ (DegPre.trF D₁ F (q mu)).left ≫ DegPre.famφ D₁ F (q α) a
    rw [Category.assoc, GlobalTheory.ProdUnif.famφ_pr hc, ← Category.assoc, trF_pr F hc, Category.assoc]

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

section Values

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X)
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem famMult_box₂ (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)))
    (k : ℕ) (α mu : D.X) (y : (TF (R := R) F).left) {J₁ J₂ J}
    (hJ₁ : Good D₁.P.L y J₁) (hJ₂ : Good D₂.P.L y J₂) (hJ : Good D.P.L y J) :
    (∏ a, om w y J₁ J₂ J ((DegPre.zF D F).left ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) *
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ *
        val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
  have a₁ : ∀ χ, (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
      (1 : TF (R := R) F ⟶ D.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := fun χ => hpsi χ _ (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := hrig _ ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  simp only [Fintype.prod_unique, Category.comp_id] at b₁ b₂
  have r₀ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      val D.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J := val_pull hJ _ _ _
  have r₁ : val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ =
      val D₁.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ := val_pull hJ₁ _ _ _
  have r₂ : val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂ =
      val D₂.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₂ := val_pull hJ₂ _ _ _
  have c₁ : ∀ χ, val (D.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      om w y J₁ J₂ J (cP D (TF (R := R) F) χ).left *
        (val (D₁.psi (q₁ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val (D₂.psi (q₂ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := fun χ => by
    have h := b₁ χ
    rw [zpow_neg_one, show (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ ptK (D.c χ) =
      (cP D (TF (R := R) F) χ).left from a₁ χ] at h
    exact inv_mul_eq_iff_eq_mul.1 h
  have c₂ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      (om w y J₁ J₂ J (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := by
    rw [r₀, r₁, r₂]
    rw [zpow_one, Category.assoc, a₂] at b₂
    exact eq_inv_mul_of_mul_eq b₂
  have c₃ := c₁ (mu + α)
  rw [map_add, map_add] at c₃
  rw [GlobalTheory.BoxFamily.prod_delta_zero F D k α mu (om w y J₁ J₂ J), GlobalTheory.BoxFamily.famMult_val F hJ,
    GlobalTheory.BoxFamily.famMult_val F hJ₁, GlobalTheory.BoxFamily.famMult_val F hJ₂, c₃, c₁ mu, c₁ α, c₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  module

end Values

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem fe_along {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) {k : ℕ} (E₁ : Fam D₁ F k) (mu α : D.X)
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q α) (q mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q mu) (q α)))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J₁} (hJ₁ : Good D₁.P.L z J₁) :
    sval (E₁.s (q (α + k • mu))) (r ≫ (TF (R := R) F ◁ p).left) z J₁ =
      sval (E₁.s (q α)) ((r ≫ (DegPre.trF D F mu).left) ≫ (TF (R := R) F ◁ p).left) z J₁ *
        (val u₁ (r ≫ (TF (R := R) F ◁ p).left) z J₁).val := by
  have h := (secRel_iff D₁.P.isLB _ _ _ _ _ _ _ _ _ u₁).1 (E₁.fe _ _ u₁ hu₁ hc₁) _
    (r ≫ (TF (R := R) F ◁ p).left) z J₁ hJ₁
  rw [map_add, map_nsmul, h, Category.assoc, Category.assoc, trF_pr F hc]

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} {q₁ : D.X →+ D₁.X} {q₂ : D.X →+ D₂.X}
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem gen_box₂ (hS : IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂) (hw : w.IsGen)
    (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) (hG : GlobalFnsSt)
    (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α))
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q₁ α) (q₁ mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)))
    (u₂ : LB.Gen (LB.LinComb D₂.P.L (DegPre.deltaφ D₂ F k (q₂ α) (q₂ mu)) (DegPre.deltaε k))) (hu₂ : u₂.IsGen)
    (hc₂ : LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ u₂ (DegPre.zF D₂ F).left)
      (DegPre.famMult D₂ F k (q₂ mu) (q₂ α))) :
    IsBoxGen w (TF (R := R) F ◁ p₁).left (TF (R := R) F ◁ p₂).left u u₁ u₂ := by
  haveI := hS.hom₁
  haveI := hS.hom₂
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (deltaφ_pr F hS.c_pr₁ k α mu)
    (deltaφ_pr F hS.c_pr₂ k α mu) hu hu₁ hu₂ (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D F hG) ?_
  intro y J₁ J₂ J hJ₁ hJ₂ hJ
  have e := famMult_box₂ F q₁ q₂ hrig hpsi k α mu y hJ₁ hJ₂ hJ
  have v : val u (DegPre.zF D F).left y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J := by
    have h := val_corr hJ hc (𝟙 _)
    rwa [val_pull hJ, Category.id_comp] at h
  have v₁ : val u₁ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₁).left) y J₁ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ := by
    have h := val_corr hJ₁ hc₁ (𝟙 _)
    rw [val_pull hJ₁, Category.id_comp] at h
    rw [zF_pr]; exact h
  have v₂ : val u₂ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₂).left) y J₂ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
    have h := val_corr hJ₂ hc₂ (𝟙 _)
    rw [val_pull hJ₂, Category.id_comp] at h
    rw [zF_pr]; exact h
  rw [v, v₁, v₂]
  exact e

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

theorem exists_isBoxFam₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), w.IsGen → IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig → (∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k), ∃ E : Fam D F k, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k E E₁ E₂ := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hw hrig hpsi F _ _ k E₁ E₂
  haveI := hS.hom₁
  haveI := hS.hom₂
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  choose s hs using fun α : D.X => exists_boxSec w hw D₁.P.isLB D₂.P.isLB D.P.isLB
    (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₁ F α) (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₂ F α) (E₁.s (q₁ α)) (E₂.s (q₂ α))
  refine ⟨⟨s, ?_⟩, hs⟩
  intro mu α u hu hc
  obtain ⟨u₁, hu₁, hc₁⟩ := (gen_fe (D := D₁) (F := F) hG k (q₁ mu) (q₁ α)).1
  obtain ⟨u₂, hu₂, hc₂⟩ := (gen_fe (D := D₂) (F := F) hG k (q₂ mu) (q₂ α)).1
  have hb := gen_box₂ F hS hw hrig hpsi hG k α mu u hu hc u₁ hu₁ hc₁ u₂ hu₂ hc₂
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have e₁ := hs (α + k • mu) _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₂ := hs α _ (𝟙 _ ≫ (DegPre.trF D F mu).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₃ := hb _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have f₁ := fe_along F hS.c_pr₁ E₁ mu α u₁ hu₁ hc₁ (𝟙 _) y hJ₁
  have f₂ := fe_along F hS.c_pr₂ E₂ mu α u₂ hu₂ hc₂ (𝟙 _) y hJ₂
  have e₅ : (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, om w y J₁ J₂ J ((𝟙 _ ≫ (DegPre.trF D F mu).left) ≫ DegPre.famφ D F α a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  refine (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a).mul_right_inj.1 ?_
  refine e₁.trans ?_
  rw [f₁, f₂]
  refine Eq.trans ?_ ((congrArg₂ (· * ·) e₂ (congrArg Units.val e₃)).symm.trans ?_)
  · rw [Units.val_mul]; ring
  · rw [e₅]; exact GlobalTheory.BoxFamily.unit_shuffle _ _ _ _

end GlobalTheory.BoxFamSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centred_pure_finite_extension_deeper_model : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.exists_centred_ext_tower | exact GlobalTheory.Poinc.Sep.exists_centred_ext_tower | (intros; apply GlobalTheory.Poinc.Sep.exists_centred_ext_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurface
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveClosure

theorem exists_closure_arith_surface_rat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  intro k _ X p D hX Z hZ
  have := hX.isIntegral
  have := hX.finite
  let S : Closeds X := ⟨closure (ratFibre.fst p '' (Z : Set (ratFibre p))), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set X) :=
    (hZ.isIrreducible.image _ (ratFibre.fst p).continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  haveI : IsPreimmersion (ratFibre.fst p) :=
    MorphismProperty.of_isPullback (ratFibre.isPullback p).flip inferInstance
  have hpb0 := (IsPullback.of_hasPullback w (ratFibre.fst p)).paste_vert (ratFibre.isPullback p)
  rw [← Category.assoc] at hpb0
  have hpb1 : IsPullback (pullback.fst w (ratFibre.fst p)) (pullback.snd w (ratFibre.fst p) ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := hpb0
  haveI : IsReduced (pullback ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isReduced_pullback_localization ℤ ℚ (nonZeroDivisors ℤ) _ _
  haveI : IsReduced (pullback w (ratFibre.fst p)) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w (ratFibre.fst p)) = (Z : Set (ratFibre p)) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change ratFibre.fst p ⁻¹' closure (ratFibre.fst p '' (Z : Set (ratFibre p))) = _
    rw [← (ratFibre.fst p).isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w (ratFibre.fst p)) Z hrange
  have hzw : (e.hom ≫ pullback.fst w (ratFibre.fst p)) ≫ w = redι Z ≫ ratFibre.fst p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w (ratFibre.fst p)) (redι Z ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : ℚ →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ ratFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w (ratFibre.fst p)).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  haveI : IsProper (w ≫ p) := by
    obtain ⟨N, i, _, hi⟩ := hproj
    have := isProper_str k N
    exact hi ▸ inferInstance
  haveI : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  haveI : Flat ((w ≫ p) ≫ spMap (Int.castRingHom k)) := (flat_int_iff_charZero _).2 hcW
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal S).subscheme = (1 + 1 : ℕ) :=
    IntModel.topologicalKrullDim_eq_succ (O := ℤ) (K := ℚ) Int.not_isField hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w (ratFibre.fst p), inferInstance, hX.of_isClosedImmersion w hcW hdim,
    hzw, hpb⟩

end GlobalTheory.CurveClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  first | exact @GlobalTheory.HessKer.exists_common_kernel | exact GlobalTheory.HessKer.exists_common_kernel | (intros; apply GlobalTheory.HessKer.exists_common_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_tuple_tensor_torsion_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  first | exact @GlobalTheory.Mum.TensTor.exists_components_of_unimodular | exact GlobalTheory.Mum.TensTor.exists_components_of_unimodular | (intros; apply GlobalTheory.Mum.TensTor.exists_components_of_unimodular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevels
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem aeval_surjective_of_dUnit_span {K A : Type} [Field K] [CommRing A] [Bialgebra K A]
    [Module.Finite K A] (hconn : ∀ a ∈ augIdeal K A, IsNilpotent a) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, Coalgebra.counit (R := K) (x i) = 0)
    (hspan : ∀ c : Cot K A, ∃ l : Fin d → K, c = ∑ i, l i • dUnit K (x i)) :
    Function.Surjective (MvPolynomial.aeval (R := K) x) := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower K inferInstance
  have hxm : ∀ i, x i ∈ RingHom.ker (counitAlgHom K A) := fun i => by
    rw [RingHom.mem_ker]; exact hx i
  have hnil : IsNilpotent (RingHom.ker (counitAlgHom K A)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.2 (hconn a ha)
  refine GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent (counitAlgHom K A) hnil x hxm ?_
  intro y hy
  obtain ⟨l, hl⟩ := hspan (dUnit K y)
  refine ⟨l, ?_⟩
  have hmem : y - ∑ i, l i • x i ∈ RingHom.ker (counitAlgHom K A) :=
    sub_mem hy (Ideal.sum_mem _ fun i _ => by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hxm i))
  have h0 : dUnit K (y - ∑ i, l i • x i) = 0 := by
    have e : dUnit K (y - ∑ i, l i • x i) = dUnit K y - ∑ i, l i • dUnit K (x i) := by
      simp only [dUnit, map_sub, map_sum, map_smul]
    rw [e, ← hl, sub_self]
  rwa [dUnit, AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h0

theorem exists_coords_generate (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) :
    ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n,
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧
        ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  haveI : Module.Finite K G.omega :=
    Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm
  set d := Module.finrank K G.omega with hd
  let b := Module.finBasis K G.omega
  have h1 : ∀ i, ∃ a : G.A 1, Coalgebra.counit (R := K) a = 0 ∧ dUnit K a = (b i).1 1 := by
    intro i
    obtain ⟨a, ha⟩ := AugCot.d_surjective (counitAlgHom K (G.A 1)) ((b i).1 1)
    refine ⟨a - algebraMap K _ (Coalgebra.counit (R := K) a), ?_, ?_⟩
    · have e : Coalgebra.counit (R := K) (algebraMap K (G.A 1) (Coalgebra.counit (R := K) a)) =
          Coalgebra.counit (R := K) a := by
        have := (counitAlgHom K (G.A 1)).commutes (Coalgebra.counit (R := K) a)
        simpa using this
      rw [map_sub, e, sub_self]
    · rw [dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact ha
  choose x1 hx1c hx1d using h1
  let z : (n : ℕ) → Fin d → G.A (n + 1) := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A (n + 1)) x1
      (fun n zn i => Function.surjInv (G.res_surjective (n + 1)) (zn i)) n
  let x : ∀ n, Fin d → G.A n := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A n) (fun i => G.res 0 (x1 i)) (fun n _ => z n) n
  have hres : ∀ n i, G.res n (x (n + 1) i) = x n i := by
    intro n i
    cases n with
    | zero => rfl
    | succ n => exact Function.surjInv_eq (G.res_surjective (n + 1)) (z n i)
  have hcou1 : ∀ n i, Coalgebra.counit (R := K) (x (n + 1) i) = 0 := by
    intro n
    induction n with
    | zero => exact hx1c
    | succ n ih =>
      intro i
      rw [← ih i, ← hres (n + 1) i, CoalgHomClass.counit_comp_apply]
  have hcou : ∀ n i, Coalgebra.counit (R := K) (x n i) = 0 := by
    intro n i
    cases n with
    | zero => rw [← hres 0 i, CoalgHomClass.counit_comp_apply]; exact hcou1 0 i
    | succ n => exact hcou1 n i
  have hdu : ∀ n i, dUnit K (x (n + 1) i) = (b i).1 (n + 1) := by
    intro n
    induction n with
    | zero => exact hx1d
    | succ n ih =>
      intro i
      obtain ⟨u, hu⟩ := G.omegaLevel_surjective (n + 2) (dUnit K (x (n + 2) i))
      rw [omegaLevel_apply] at hu
      have hn : (u - b i).1 (n + 1) = 0 := by
        change u.1 (n + 1) - (b i).1 (n + 1) = 0
        rw [← ih i, ← cotMap_res_omega, hu, cotMap_d, hres, sub_self]
      have h1' : G.omegaLevel 1 (u - b i) = 0 :=
        G.omega_val_eq_zero_of_le (by omega) hn
      have hub : u = b i := sub_eq_zero.1
        ((G.omegaLevel_one_bijective h).1 (h1'.trans (map_zero _).symm))
      rw [← hu, hub]
  have hspan : ∀ n (c : Cot K (G.A n)), ∃ l : Fin d → K, c = ∑ i, l i • dUnit K (x n i) := by
    intro n c
    cases n with
    | zero => exact ⟨0, by rw [G.cot_zero_eq_zero c]; simp⟩
    | succ n =>
      obtain ⟨w, rfl⟩ := G.omegaLevel_surjective (n + 1) c
      refine ⟨b.repr w, ?_⟩
      conv_lhs => rw [← b.sum_repr w]
      simp only [map_sum, map_smul, omegaLevel_apply, hdu]
      rfl
  exact ⟨x, hres, hcou, fun n =>
    aeval_surjective_of_dUnit_span (hG n) (x n) (hcou n) (hspan n)⟩

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JA))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB) (incM D.host.F JA)
                           (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JB) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) dd χS (GlobalTheory.WeilM.diagCols (Fin T.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target | exact GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target | (intros; apply GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target <;> assumption)
end


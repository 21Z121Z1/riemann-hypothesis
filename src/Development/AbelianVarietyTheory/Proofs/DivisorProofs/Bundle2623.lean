import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpGen
open GlobalTheory.PowE8

theorem exists_gen {S T : Scheme.{0}} (f : T ⟶ S) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] {B C : Over T}
    [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a)
    (u : (Over.pullback f).obj G₀ ≅ C) [IsMonHom u.hom] :
    ∃ gen : (Over.pullback f).obj (powObj G₀ 8) ≅ B, IsMonHom gen.hom ∧
      ∀ a, gen.hom ≫ pr a = (Over.pullback f).map (powPr G₀ a) ≫ u.hom := by
  let hl := isLimitOfPreserves (Over.pullback f) (powIsLimit G₀ 8)
  let ρ : Fin 8 → ((Over.pullback f).obj (powObj G₀ 8) ⟶ (Over.pullback f).obj G₀) :=
    fun a => (Over.pullback f).map (powPr G₀ a)
  choose x hx hxu using fun (T' : Over T) (y : Fin 8 → (T' ⟶ C)) => huniq T' y
  let inv : B ⟶ (Over.pullback f).obj (powObj G₀ 8) :=
    hl.lift ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩
  have hinv : ∀ a, inv ≫ ρ a = pr a ≫ u.inv := fun a => hl.fac ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩ ⟨a⟩
  let hom := x _ (fun a => ρ a ≫ u.hom)
  have hhom : ∀ a, hom ≫ pr a = ρ a ≫ u.hom := hx _ _
  refine ⟨⟨hom, inv, ?_, ?_⟩, ?_, hhom⟩
  · refine hl.hom_ext fun ⟨a⟩ => ?_
    show (hom ≫ inv) ≫ ρ a = 𝟙 _ ≫ ρ a
    rw [Category.assoc, hinv, ← Category.assoc, hhom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · have h1 := hxu B (fun a => pr a) (inv ≫ hom) (fun a => by
      rw [Category.assoc, hhom, ← Category.assoc, hinv, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have h2 := hxu B (fun a => pr a) (𝟙 B) (fun a => Category.id_comp _)
    exact h1.trans h2.symm
  · have hm : ∀ a, IsMonHom (hom ≫ pr a) := fun a => by rw [hhom]; infer_instance
    constructor
    · have h1 := hxu _ (fun a => η[C]) (η ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.one_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => η[C]) η (fun a => by haveI := hpr a; exact IsMonHom.one_hom (pr a))
      exact h1.trans h2.symm
    · have h1 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) (μ ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.mul_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) ((hom ⊗ₘ hom) ≫ μ) (fun a => by
        haveI := hpr a; rw [Category.assoc, IsMonHom.mul_hom (pr a), ← Category.assoc, tensorHom_comp_tensorHom])
      exact h1.trans h2.symm

theorem lift_lamφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (x y : T ⟶ B)
    (I : ULift.{0} (Finset (Fin 2))) :
    (lift x y).left ≫ GlobalTheory.PrimCocycle.lamφ B I = (psum B ![x, y] I.down).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
    (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))

theorem psum_comp_hom {S : Scheme.{0}} {B C T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
    (u : B ⟶ C) [IsMonHom u] (x y : T ⟶ B) (I : Finset (Fin 2)) :
    psum C ![x ≫ u, y ≫ u] I = psum B ![x, y] I ≫ u :=
  ((congrArg (fun q => psum C q I) (funext fun i => by fin_cases i <;> rfl)).trans
    (psum_hom (MonoidHom.mk' (fun z : T ⟶ B => z ≫ u) fun a b => MonObj.mul_comp a b u) ![x, y] I).symm)

theorem zpow_lam {U : Type} [CommGroup U] (a b c d : U) (w : ℤ) :
    (a * b⁻¹ * c⁻¹ * d) ^ w = a ^ (-(w * negε 0)) * b ^ (-(w * negε 1)) * c ^ (-(w * negε 2)) * d ^ (-(w * negε 3)) := by
  simp only [negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_zpow, inv_zpow', mul_neg, mul_one, neg_neg]
  norm_num

theorem gen_eighthPower : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro g n o _ ζ F W V₁ _ _ _ D₀ G₀ _ _ A₀ U₀ y α α₂ hcart hsq hlb P hP
  obtain ⟨c, ⟨φ, φ₂, hφ, hφsq, hφlb, -⟩, pr, prh, prl, hPL⟩ := hP
  obtain ⟨e, he, heα⟩ := grpPullback_iso hcart hφ
  haveI := he
  haveI := U₀.gen_hom
  haveI : IsMonHom (U₀.gen ≪≫ e).hom := by rw [Iso.trans_hom]; infer_instance
  obtain ⟨gen, hgen, hcoord⟩ := exists_gen (jK V₁) G₀ pr prh prl (U₀.gen ≪≫ e)
  refine ⟨gen, hgen, ?_⟩
  have hA0 := A₀.isLB
  have hc := c.isLB
  have hLG := U₀.LG.isLB
  have hPl := P.isLB
  have hU := F.univ.isLB
  let ρ : Fin 8 → ((Over.pullback (jK V₁)).obj (powObj G₀ 8) ⟶ (Over.pullback (jK V₁)).obj G₀) :=
    fun a => (Over.pullback (jK V₁)).map (powPr G₀ a)
  let e₂ : (G2 A₀.A).left ⟶ (G2 c.A).left := (lift (fst _ _ ≫ e.hom) (snd _ _ ≫ e.hom)).left
  let mAB : Fin 8 × Fin 8 → (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ (G2 A₀.A).left) :=
    fun ab => (lift (ρ ab.1 ≫ U₀.gen.hom) (ρ ab.2 ≫ U₀.gen.hom)).left
  have hm : ∀ ab : Fin 8 × Fin 8, mAB ab ≫ e₂ = gen.hom.left ≫ (lift (pr ab.1) (pr ab.2)).left := fun ab => by
    simp only [mAB, e₂, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hcoord, Iso.trans_hom,
      Category.assoc]
    rfl
  have he₂ : e₂ ≫ φ₂ = α₂ := by
    apply pullback.hom_ext
    · have h1 : (fst F.univ.A F.univ.A).left = pullback.fst _ _ := rfl
      rw [← h1, Category.assoc, hφsq.1, hsq.1, ← heα]
      simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_fst]
    · have h1 : (snd F.univ.A F.univ.A).left = pullback.snd _ _ := rfl
      rw [← h1, Category.assoc, hφsq.2, hsq.2, ← heα]
      simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_snd]
  have Q1 : LBIso (c.P.pull e₂) (abelian₂ A₀.A A₀.L) := by
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hφlb (fun _ : PUnit => e₂) (fun _ => 1)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PrimNorm.lbIso_nested hU (fun _ : PUnit => φ₂) (fun _ => 1) (fun _ : PUnit => e₂) (fun _ => 1)
        (fun _ : PUnit => α₂) (fun _ => 1) (by simp [he₂])) ?_
    exact hlb.symm
  let q := pullback.fst (powObj G₀ 8).hom (jK V₁)
  let q0 := pullback.fst G₀.hom (jK V₁)
  let n : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) →
      (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ ((Over.pullback (jK V₁)).obj G₀).left) :=
    fun p => (psum _ ![ρ p.1.1, ρ p.1.2] p.2.down).left
  let κ : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => GlobalTheory.PrimCocycle.lamε p.2 * W p.1.1 p.1.2
  have hn : ∀ ab I, mAB ab ≫ GlobalTheory.PrimCocycle.lamφ A₀.A I = n (ab, I) ≫ U₀.gen.hom.left := fun ab I => by
    rw [lift_lamφ, psum_comp_hom]; rfl
  let Uq : Over.mk (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).hom ≫ jK V₁) ⟶ powObj G₀ 8 :=
    Over.homMk q pullback.condition
  have hq : ∀ ab I, n (ab, I) ≫ q0 = q ≫ (lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I :=
    fun ab I => by
      rw [lift_lamφ]
      refine psum_push (isGrpPullback_pullback G₀ (jK V₁)) _ _ Uq (fun i => ?_) I.down
      apply Over.OverMorphism.ext
      fin_cases i
      · exact pullback.lift_fst _ _ _
      · exact pullback.lift_fst _ _ _
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hPL (fun _ : PUnit => gen.hom.left) (fun _ => 1)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hc _ _ (fun _ : PUnit => gen.hom.left) (fun _ => 1) (fun ab => mAB ab ≫ e₂)
      (fun ab => W ab.1 ab.2) (by simp [hm])) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hc (fun _ : PUnit => e₂) (fun _ => 1) mAB (fun ab => W ab.1 ab.2)
      (fun ab => mAB ab ≫ e₂) (fun ab => W ab.1 ab.2) (by simp)).symm ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb Q1 mAB (fun ab => W ab.1 ab.2)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hA0 (GlobalTheory.PrimCocycle.lamφ A₀.A) GlobalTheory.PrimCocycle.lamε mAB (fun ab => W ab.1 ab.2)
      (fun p => n p ≫ U₀.gen.hom.left) κ ?_) ?_
  · refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    refine Fintype.prod_congr _ _ fun ab => ?_
    rw [← Finset.prod_zpow]
    refine Fintype.prod_congr _ _ fun I => ?_
    rw [← zpow_mul, hn]
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hA0 (fun _ : PUnit => U₀.gen.hom.left) (fun _ => 1) n κ
      (fun p => n p ≫ U₀.gen.hom.left) κ (by simp)).symm ?_
  obtain ⟨w, hw⟩ := U₀.ext
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (GlobalTheory.PowPrimitive.lbIso_linComb ⟨w, hw⟩ n κ) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hLG (fun _ : PUnit => q0) (fun _ => 1) n κ (fun p => n p ≫ q0) κ (by simp)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    ((GlobalTheory.PrimNorm.lbIso_iff hLG (fun p => n p ≫ q0) κ
      (fun k : (Fin 8 × Fin 8) × Fin 4 => q ≫ lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).2 ?_) ?_
  · refine ((Fintype.prod_prod_type _).trans ?_).trans (Fintype.prod_prod_type _).symm
    refine Fintype.prod_congr _ _ fun ab => ?_
    have e1 : ∏ I, GlobalTheory.PrimNorm.cls U₀.LG.L (n (ab, I) ≫ q0) ^ κ (ab, I) =
        (∏ I, (fun m => GlobalTheory.PrimNorm.cls U₀.LG.L (q ≫ m))
          ((lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I) ^ GlobalTheory.PrimCocycle.lamε I) ^
          W ab.1 ab.2 := by
      rw [← Finset.prod_zpow]
      refine Fintype.prod_congr _ _ fun I => ?_
      rw [← zpow_mul, hq]
    rw [e1]
    refine (congrArg (· ^ W ab.1 ab.2) (GlobalTheory.PrimCocycle.prod_lam (powPr G₀ ab.1) (powPr G₀ ab.2)
      (fun m => GlobalTheory.PrimNorm.cls U₀.LG.L (q ≫ m)))).trans ?_
    rw [Fin.prod_univ_four]
    exact zpow_lam _ _ _ _ _
  exact (GlobalTheory.PrimNorm.lbIso_nested hLG
    (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)) (fun _ : PUnit => q) (fun _ => 1) _ _ (by simp)).symm

end GlobalTheory.SharpGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  first | exact @GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd | exact GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd | (intros; apply GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstantsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  first | exact @GlobalTheory.GermConst.germ_constFn_origin | exact GlobalTheory.GermConst.germ_constFn_origin | (intros; apply GlobalTheory.GermConst.germ_constFn_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictionsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  first | exact @GlobalTheory.CoverForms.eq_zero_of_cover | exact GlobalTheory.CoverForms.eq_zero_of_cover | (intros; apply GlobalTheory.CoverForms.eq_zero_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GlueNear

theorem isSeparated_of_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f :=
    pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have e : j ≫ pullback.diagonal f = pullback.diagonal (j ≫ f) ≫ m := by
    apply pullback.hom_ext <;> simp [m, pullback.map, pullback.lift_fst, pullback.lift_snd]
  have : UniversallyClosed (j ≫ pullback.diagonal f) := by rw [e]; infer_instance
  have : UniversallyClosed (pullback.diagonal f) := UniversallyClosed.of_comp_surjective j _
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range⟩

theorem isPullback_iSup {Y X S S' : Scheme.{0}} (π : Y ⟶ X) (q : X ⟶ S) (t : Y ⟶ S') (f : S' ⟶ S)
    {I : Type} (V : I → X.Opens)
    (h : ∀ i, IsPullback (π ∣_ V i) ((π ⁻¹ᵁ V i).ι ≫ t) ((V i).ι ≫ q) f) :
    IsPullback (π ∣_ (⨆ i, V i)) ((π ⁻¹ᵁ (⨆ i, V i)).ι ≫ t) ((⨆ i, V i).ι ≫ q) f := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  have e : V i ≤ ⨆ i, V i := le_iSup V i
  have sq : IsPullback (Y.homOfLE (π.preimage_mono e)) (π ∣_ V i) (π ∣_ (⨆ i, V i)) (X.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ (⨆ i, V i)).ι) (h₂₂ := (⨆ i, V i).ι) (v₁₃ := π) ?_ ?_
      (isPullback_morphismRestrict π _).flip
    · simpa using (isPullback_morphismRestrict π (V i)).flip
    · rw [← cancel_mono (⨆ i, V i).ι]; simp
  refine (h i).of_iso sq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans sq.isoPullback_hom_snd.symm
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    erw [sq.isoPullback_hom_fst]
    simp
  · change _ = 𝟙 _ ≫ X.homOfLE e ≫ _
    simp
  · simp

theorem smooth_iSup {X S : Scheme.{0}} (q : X ⟶ S) {I : Type} (V : I → X.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  change Smooth (X.homOfLE (le_iSup V i) ≫ _)
  simpa using h i

theorem exists_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (f : S ⟶ Sp R) [IsFinite f] [Surjective f]
    (G : Over S) [IsSeparated G.hom] (H : G.left.Opens)
    (hcl : ∀ g : G.left, f (G.hom g) = closedPoint R → g ∈ H) (hc : IsCompact (H : Set G.left))
    (X : Over (Sp R)) (π : H.toScheme ⟶ X.left)
    (hloc : ∀ x : H.toScheme, f (G.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧
      Smooth (V.ι ≫ X.hom) ∧ IsPullback (π ∣_ V) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G.hom) (V.ι ≫ X.hom) f) :
    ∃ N : Near f G, ∀ (α : G.left ⟶ G.left) (β : S ⟶ S) (hα : H ≤ α ⁻¹ᵁ H), α ≫ G.hom = G.hom ≫ β →
      α.resLE H H hα ≫ π = π →
      ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left), N.Pt s u x → N.Pt (s ≫ β) u (x ≫ α) := by
  classical
  have : CompactSpace H.toScheme := isCompact_iff_compactSpace.mp hc
  let Z : Set H.toScheme := {x | f (G.hom (H.ι x)) = closedPoint R}
  have hZ : IsCompact Z := by
    refine IsClosed.isCompact ?_
    exact (isClosed_singleton_closedPoint R).preimage
      (f.continuous.comp (G.hom.continuous.comp H.ι.continuous))
  choose V hV hVa hVs hVp using fun x : Z => hloc x.1 x.2
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun x : Z => ((π ⁻¹ᵁ V x : H.toScheme.Opens) : Set H.toScheme))
    (fun x => (π ⁻¹ᵁ V x).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hV ⟨x, hx⟩⟩)
  let W : t → X.left.Opens := fun i => V i.1
  have P := isPullback_iSup π X.hom (H.ι ≫ G.hom) f W fun i => hVp i.1
  have hS := smooth_iSup X.hom W fun i => hVs i.1
  have hC : IsCompact ((⨆ i, W i : X.left.Opens) : Set X.left) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => (hVa i.1).isCompact
  have hA : ∀ x ∈ Z, π x ∈ ⨆ i, W i := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hx⟩
  generalize (⨆ i, W i) = U at P hS hC hA
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hC
  have hq : QuasiCompact (U.ι ≫ X.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hsep : IsSeparated (U.ι ≫ X.hom) := by
    have h₁ : IsFinite (π ∣_ U) := MorphismProperty.of_isPullback (P := @IsFinite) P.flip inferInstance
    have h₂ : Surjective (π ∣_ U) := MorphismProperty.of_isPullback (P := @Surjective) P.flip inferInstance
    have h₃ : IsSeparated (π ∣_ U ≫ U.ι ≫ X.hom) := by rw [P.w]; infer_instance
    exact isSeparated_of_surjective (π ∣_ U) _
  let N : Near f G :=
    { U := Over.mk (U.ι ≫ X.hom)
      smooth := hS
      separated := hsep
      quasiCompact := hq
      u := P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι
      isOpen := inferInstanceAs (IsOpenImmersion (P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι))
      u_over := (Category.assoc _ _ _).trans
        ((congrArg (P.isoPullback.inv ≫ ·) (Category.assoc _ _ _)).trans P.isoPullback_inv_snd)
      all := by
        intro g hg
        refine ⟨P.isoPullback.hom ⟨⟨g, hcl g hg⟩, hA ⟨g, hcl g hg⟩ hg⟩, ?_⟩
        change (P.isoPullback.hom ≫ P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι) _ = g
        rw [Iso.hom_inv_id_assoc]
        rfl }
  have pt : ∀ {T : Scheme.{0}} (s : T ⟶ S) (u : T ⟶ U.toScheme) (x : T ⟶ G.left), N.Pt s u x ↔
      ∃ y : T ⟶ (π ⁻¹ᵁ U).toScheme, y ≫ π ∣_ U = u ∧ y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι ≫ G.hom = s ∧
        y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = x := by
    intro T s u x
    constructor
    · rintro ⟨x₀, h₁, h₂, h₃⟩
      refine ⟨x₀ ≫ P.isoPullback.inv, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans h₃
    · rintro ⟨y, h₁, h₂, h₃⟩
      refine ⟨y ≫ P.isoPullback.hom, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (P.isoPullback.hom_inv_id_assoc _)).trans h₃)
  refine ⟨N, fun α β hα hαβ hπ T s u x hx => ?_⟩
  obtain ⟨y, rfl, rfl, rfl⟩ := (pt s u x).1 hx
  have Q := isPullback_morphismRestrict π U
  let δ : (π ⁻¹ᵁ U).toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
    Q.lift (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ α.resLE H H hα) (by rw [Category.assoc, hπ, Q.w])
  have hδ : δ ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = (π ⁻¹ᵁ U).ι ≫ H.ι ≫ α := by
    rw [Q.lift_snd_assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]
  refine (pt _ _ _).2 ⟨y ≫ δ, ?_, ?_, ?_⟩
  · rw [Category.assoc, Q.lift_fst]
  · simp only [Category.assoc]
    rw [reassoc_of% hδ, hαβ]
  · simp only [Category.assoc]
    rw [hδ]

theorem glue_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ _ D D' hD A' G' _ _ hG U' a H hH hcl hc X π hX _ _ hπ _ _ hloc
  have := hG.separated
  have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hρ.2.2
  have : Surjective (spMap ρ) := ⟨RingHom.IsIntegral.comap_surjective hρ.2.2.to_isIntegral hρ.2.1⟩
  obtain ⟨N, hN⟩ := exists_near (spMap ρ) G' H hcl hc X π fun x hx => by
    obtain ⟨V, h₁, h₂, h₃, h₄⟩ := hloc x hx
    refine ⟨V, h₁, h₂, h₃, ?_⟩
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (@asIso _ _ _ _ _ h₄) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [Scheme.Hom.resLE_comp_ι_assoc, hX]
    simp only [Category.assoc]
  exact ⟨N, fun σ => hN (a.act σ) _ (hH σ).ge (a.cart σ).1.w (hπ σ)⟩

end GlobalTheory.Mum.GlueNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def IsFrameOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) : Prop :=
  ∀ k k', res (inf_le_left : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k) (T k) =
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ L.U k ⊓ L.U k') (L.g k k') *
    res (inf_le_right : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k') (T k')

def FrameCarried {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gm f z (W ⊓ L.U j) (T j) = gw w (𝟙 X) z j k * gm (𝟙 X) z (W ⊓ L.U k) (T k)

theorem gm_eq_map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a.val) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem FrameCarried.ratio_fixed {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {W W' O : X.Opens}
    {T : ∀ k, Γ(X, W ⊓ L.U k)ˣ} {T' : ∀ k, Γ(X, W' ⊓ L.U k)ˣ} {f : X ⟶ X} {w : LB.Iso L (L.pull f)}
    (hT : FrameCarried L W T f w) (hT' : FrameCarried L W' T' f w) (hOW : O ≤ W) (hOW' : O ≤ W') (r : Γ(X, O)ˣ)
    (hr : ∀ (z : X) (k : L.ι), z ∈ O → z ∈ L.U k →
      gm (𝟙 X) z O r = gm (𝟙 X) z _ (T' k) * (gm (𝟙 X) z _ (T k))⁻¹)
    (h : O ≤ f ⁻¹ᵁ O) : (f.appLE O O h).hom r.val = r.val := by
  apply TopCat.Presheaf.section_ext X.sheaf O
  intro x hx
  obtain ⟨k, hk⟩ := exists_chart hL x
  have hfx : f x ∈ O := h hx
  obtain ⟨j, hj⟩ := exists_chart hL (f x)
  have key : gm f x O r = gm (𝟙 X) x O r := by
    rw [gm_eq_map_gm f x O hfx, hr (f x) j hfx hj, map_mul, map_inv,
      ← gm_eq_map_gm f x (W' ⊓ L.U j) (show f x ∈ W' ⊓ L.U j from ⟨hOW' hfx, hj⟩),
      ← gm_eq_map_gm f x (W ⊓ L.U j) (show f x ∈ W ⊓ L.U j from ⟨hOW hfx, hj⟩),
      hT' x j k (hOW' hx) (hOW' hfx) hk hj, hT x j k (hOW hx) (hOW hfx) hk hj, hr x k hx hk, _root_.mul_inv,
      _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have e1 := congrArg Units.val key
  rw [gm_val f x O hfx, gm_val (𝟙 X) x O hx] at e1
  refine Eq.trans ?_ (e1.trans ?_)
  · simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx _
  · rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstantsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R), evO G (constO G r) = r := by
  first | exact @GlobalTheory.FormalOrigin.evO_constO | exact GlobalTheory.FormalOrigin.evO_constO | (intros; apply GlobalTheory.FormalOrigin.evO_constO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosureStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h0_lower_bound_of_isAmple_cartierDiv : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  first | exact @GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | exact GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed | (intros; apply GlobalTheory.ClosureRR.h0_ge_of_lt_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  first | (exact @GlobalTheory.HTTransport.lieHer_geomAt_iff) | (exact GlobalTheory.HTTransport.lieHer_geomAt_iff) | (intros; apply GlobalTheory.HTTransport.lieHer_geomAt_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZetaStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  first | exact @GlobalTheory.HilbertEis.eisExp | exact GlobalTheory.HilbertEis.eisExp | (intros; apply GlobalTheory.HilbertEis.eisExp <;> assumption)
end


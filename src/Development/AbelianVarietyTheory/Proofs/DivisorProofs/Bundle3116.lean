import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinGlue
open GlobalTheory.SiegelDescent GlobalTheory.SiegDesc GlobalTheory.CechPic

theorem lem_ab : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := GlobalTheory.T.abelianScheme_glue_artinian_local_fibreProduct

theorem lem_lb : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := GlobalTheory.T.exists_lineBundle_glue_milnorPatching_artinLocal

theorem lem_triv : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := GlobalTheory.T.pic_eq_zero_of_pullbacks_eq_zero_artinFibreProduct

theorem lem_pt : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := GlobalTheory.T.fibreProduct_spec_fieldPoint_factors

theorem lem_princ : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := GlobalTheory.T.siegel_principal_artinian_of_principal_pullback

theorem geom_transfer {S S' : Scheme.{0}} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B} {h M : ℕ}
    (c : SiegPre h M ζ s') (A₀ : Over S) [GrpObj A₀] [IsCommMonObj A₀] (f : S' ⟶ S) (φ : c.A.left ⟶ A₀.left)
    (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A₀)) (hs : s' = f ≫ s)
    (hp : IsGrpPullback c.A A₀ f φ) (hP₀ : P₀.IsLB)
    (diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ))
    (hlev : ∀ a, (c.lev a).left ≫ φ = f ≫ (lev₀ a).left) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (y : Sp k ⟶ S') (hy : y ≫ f = x) (β : B →+* k) (z : kˣ) (hx : x ≫ s = spMap β)
    (hz : (z : k) = β ζ) :
    (∀ a, (toUnit (Over.mk x) ≫ lev₀ a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A₀, g ^ M = 1 → ∃ a, toUnit _ ≫ lev₀ a = g) ∧
    ∀ a b, Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) M (toUnit (Over.mk x) ≫ lev₀ a) (toUnit _ ≫ lev₀ b)
      (unitOn (z ^ (2 * omegaStd a b))) := by
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ f := hp.1.w
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ c.A f φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

theorem spec_isPushout (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (hP : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P) (s₁ : Function.Surjective g₁)
    (s₂ : Function.Surjective g₂) : IsPushout (Spec.map g₁) (Spec.map g₂) (Spec.map f₁) (Spec.map f₂) := by
  have w : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hP.w]
  exact GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hl ha s₁ s₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
    (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂) (show Flat (𝟙 (Spec P)) from inferInstance) (IsPullback.id_vert _)
    (IsPullback.id_vert _) (IsPullback.id_vert _) w (by simp)

theorem nontrivial_of_pt (R : CommRingCat.{0}) (k : Type) [Field k] (y : Spec (CommRingCat.of k) ⟶ Spec R) :
    Nontrivial R := by
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y.base pt⟩

theorem exists_principal_glue : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ β c₁ c₂ hp₁ hp₂ hc₀
  obtain ⟨c₀, ⟨ψ₁, ψ₁₂, hψ₁, sψ₁, iψ₁, lψ₁⟩, ⟨ψ₂, ψ₂₂, hψ₂, sψ₂, iψ₂, lψ₂⟩⟩ := hc₀
  obtain ⟨A, instA, φ₁, φ₂, hA, hφ₁, hφ₂, hcomm⟩ :=
    lem_ab P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ c₁.A c₂.A c₀.A ψ₁ ψ₂ c₁.ab c₂.ab hψ₁ hψ₂
  haveI := hA.comm
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨φ₁₂, sφ₁⟩ := exists_isSquare hφ₁.1.w
  obtain ⟨φ₂₂, sφ₂⟩ := exists_isSquare hφ₂.1.w
  obtain ⟨χ₂, sχ⟩ := exists_isSquare (f := Spec.map g₁ ≫ Spec.map f₁) (φ := ψ₁ ≫ φ₁)
    (by rw [Category.assoc, hφ₁.1.w]; exact (reassoc_of% hψ₁.1.w) _)
  have e₁₂ : ψ₁₂ ≫ φ₁₂ = χ₂ := isSquare_comp rfl sψ₁ sφ₁ sχ
  have e₂₂ : ψ₂₂ ≫ φ₂₂ = χ₂ := isSquare_comp hcomm.symm sψ₂ sφ₂ sχ
  have flat : Flat (G2 A).hom := by
    haveI := hAA.smooth
    infer_instance
  have hiso₀ : LBIso (c₁.P.pull ψ₁₂) (c₂.P.pull ψ₂₂) :=
    LBIso.trans (pull_isLB c₁.isLB _) c₀.isLB (pull_isLB c₂.isLB _) iψ₁.symm iψ₂
  obtain ⟨L, hL, w₁, w₂⟩ := lem_lb P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (G2 A) (G2 c₁.A) (G2 c₂.A)
    (G2 c₀.A) φ₁₂ φ₂₂ ψ₁₂ ψ₂₂ flat (isPullback_of_isSquare hφ₁.1 sφ₁) (isPullback_of_isSquare hφ₂.1 sφ₂)
    (isPullback_of_isSquare hψ₁.1 sψ₁) (e₁₂.trans e₂₂.symm) (isSquare_w hψ₂.1.w sψ₂) c₁.P c₂.P c₁.isLB c₂.isLB
    hiso₀
  have clsP₁ : cls c₁.P c₁.isLB = pull φ₁₂ (cls L hL) := by
    rw [← cls_pull hL φ₁₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₁
  have clsP₂ : cls c₂.P c₂.isLB = pull φ₂₂ (cls L hL) := by
    rw [← cls_pull hL φ₂₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₂
  have rig : ∀ (a₁ : c₁.A ⟶ c₁.A ⊗ c₁.A) (a₂ : c₂.A ⟶ c₂.A ⊗ c₂.A) (a : A ⟶ A ⊗ A),
      a₁.left ≫ φ₁₂ = φ₁ ≫ a.left → a₂.left ≫ φ₂₂ = φ₂ ≫ a.left →
      (∃ t : (c₁.P.pull a₁.left).Gen, t.IsGen) → (∃ t : (c₂.P.pull a₂.left).Gen, t.IsGen) →
      ∃ t : (L.pull a.left).Gen, t.IsGen := by
    intro a₁ a₂ a e₁ e₂ t₁ t₂
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL _ (pull_isLB hL _)]
    refine lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A c₁.A c₂.A φ₁ φ₂ hA hφ₁.1 hφ₂.1 _ ?_ ?_
    · rw [← pull_comp, ← e₁, pull_comp, ← clsP₁, ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _)]
      exact (cls_eq_zero_iff _).2 t₁
    · rw [← pull_comp, ← e₂, pull_comp, ← clsP₂, ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _)]
      exact (cls_eq_zero_iff _).2 t₂
  have one₁ := one_comp hφ₁ c₁.A A φ₁ hφ₁.1.w
  have one₂ := one_comp hφ₂ c₂.A A φ₂ hφ₂.1.w
  have idφ₁ : (𝟙 c₁.A : c₁.A ⟶ c₁.A).left ≫ φ₁ = φ₁ ≫ (𝟙 A : A ⟶ A).left := by simp
  have idφ₂ : (𝟙 c₂.A : c₂.A ⟶ c₂.A).left ≫ φ₂ = φ₂ ≫ (𝟙 A : A ⟶ A).left := by simp
  have symm : LBIso L (L.pull (lift (snd A A) (fst A A)).left) := by
    have sw₁ := lift_square sφ₁ sφ₁.2.symm sφ₁.1.symm
    have sw₂ := lift_square sφ₂ sφ₂.2.symm sφ₂.1.symm
    refine (cls_eq_iff hL (pull_isLB hL _)).1 (sub_eq_zero.1 (lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
      (G2 A) (G2 c₁.A) (G2 c₂.A) φ₁₂ φ₂₂ hAA (isPullback_of_isSquare hφ₁.1 sφ₁)
      (isPullback_of_isSquare hφ₂.1 sφ₂) _ ?_ ?_))
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₁, pull_comp, ← clsP₁,
        ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₁.symm
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₂, pull_comp, ← clsP₂,
        ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₂.symm

  have hpo := spec_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
  have levc : ∀ a, Spec.map g₁ ≫ (c₁.lev a).left ≫ φ₁ = Spec.map g₂ ≫ (c₂.lev a).left ≫ φ₂ := fun a => by
    simp only [← Category.assoc]
    rw [← lψ₁ a, ← lψ₂ a, Category.assoc, Category.assoc, hcomm]
  have sec : ∀ {X : Scheme.{0}} {Bv : Over X} (u : 𝟙_ (Over X) ⟶ Bv), u.left ≫ Bv.hom = 𝟙 X := fun u => by
    simpa using Over.w u
  have hlev : ∀ a, ∃ l : 𝟙_ (Over (Spec P)) ⟶ A, Spec.map f₁ ≫ l.left = (c₁.lev a).left ≫ φ₁ ∧
      Spec.map f₂ ≫ l.left = (c₂.lev a).left ≫ φ₂ := fun a =>
    ⟨Over.homMk (hpo.desc _ _ (levc a)) (by
      refine hpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hpo.inl_desc, Category.assoc, hφ₁.1.w, ← Category.assoc, sec]
        simp
      · rw [← Category.assoc, hpo.inr_desc, Category.assoc, hφ₂.1.w, ← Category.assoc, sec]
        simp), hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  choose lev hl₁ hl₂ using hlev
  obtain ⟨ρ₁, hρ₁⟩ := exists_liftHom hφ₁ (𝟙_ _) (𝟙_ _) (Spec.map f₁)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ρ₂, hρ₂⟩ := exists_liftHom hφ₂ (𝟙_ _) (𝟙_ _) (Spec.map f₂)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρl₁ : ∀ a, ρ₁ (lev a) = c₁.lev a := fun a => (hρ₁ _ _).2 (hl₁ a).symm
  have ρl₂ : ∀ a, ρ₂ (lev a) = c₂.lev a := fun a => (hρ₂ _ _).2 (hl₂ a).symm
  have inj : ∀ x y : 𝟙_ (Over (Spec P)) ⟶ A, ρ₁ x = ρ₁ y → ρ₂ x = ρ₂ y → x = y := fun x y e₁ e₂ =>
    Over.OverMorphism.ext (hpo.hom_ext
      (by rw [← (hρ₁ x _).1 rfl, ← (hρ₁ y _).1 rfl, e₁])
      (by rw [← (hρ₂ x _).1 rfl, ← (hρ₂ y _).1 rfl, e₂]))
  have diag₁ : LBIso (c₁.P.pull (lift (𝟙 c₁.A) (𝟙 c₁.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₁) :=
    lbIso_square c₁.isLB hL w₁ (lift_square sφ₁ idφ₁ idφ₁)
  have diag₂ : LBIso (c₂.P.pull (lift (𝟙 c₂.A) (𝟙 c₂.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₂) :=
    lbIso_square c₂.isLB hL w₂ (lift_square sφ₂ idφ₂ idφ₂)
  let c : SiegPre g n (zetaAway n) (Spec.map β) :=
    { A := A, ab := hA, P := L, isLB := hL
      rig₁ := rig _ _ _ (lift_square sφ₁ one₁ idφ₁) (lift_square sφ₂ one₂ idφ₂) c₁.rig₁ c₂.rig₁
      rig₂ := rig _ _ _ (lift_square sφ₁ idφ₁ one₁) (lift_square sφ₂ idφ₂ one₂) c₁.rig₂ c₂.rig₂
      symm := symm, lev := lev
      lev_add := fun a b => inj _ _ (by rw [map_mul, ρl₁, ρl₁, ρl₁, c₁.lev_add])
        (by rw [map_mul, ρl₂, ρl₂, ρl₂, c₂.lev_add])
      lev_tors := fun a => inj _ _ (by rw [map_pow, ρl₁, c₁.lev_tors, map_one])
        (by rw [map_pow, ρl₂, c₂.lev_tors, map_one])
      geom := by
        intro k _ _ x β' z hx hz
        rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ k x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact geom_transfer c₁ A (Spec.map f₁) φ₁ L lev rfl hφ₁ hL diag₁ (fun a => (hl₁ a).symm) k x y hy β' z hx hz
        · exact geom_transfer c₂ A (Spec.map f₂) φ₂ L lev rfl hφ₂ hL diag₂ (fun a => (hl₂ a).symm) k x y hy β' z hx hz }
  have pb₁ : SiegPB c₁ c (Spec.map f₁) := ⟨φ₁, φ₁₂, hφ₁, sφ₁, w₁, fun a => (hl₁ a).symm⟩
  have pb₂ : SiegPB c₂ c (Spec.map f₂) := ⟨φ₂, φ₂₂, hφ₂, sφ₂, w₂, fun a => (hl₂ a).symm⟩
  refine ⟨c, ?_, pb₁, pb₂⟩
  rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ (IsLocalRing.ResidueField P)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue P))) with ⟨y, -⟩ | ⟨y, -⟩
  · haveI := nontrivial_of_pt R₁ _ y
    exact lem_princ g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ inferInstance β c c₁ pb₁ hp₁
  · haveI := nontrivial_of_pt R₂ _ y
    exact lem_princ g n hn hodd P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hs₂ hs₁ inferInstance β c c₂ pb₂ hp₂

end GlobalTheory.ArtinGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacter
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), (n : R) = 0 → HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb D x)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionDifference_one_cochain R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyByFiniteSubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quotient_finite :
    ∀ (K : Type) [Field K] (A : AbVar K) (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A.X), IsMonHom i → Mono i →
      IsFinite H.hom → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧
        ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 ↔ ∃ y, y ≫ i = x := by
  intro K _ A H _ i hi hmono hfin
  have hflat : Flat H.hom := inferInstance
  obtain ⟨B', inst, q, -, hB, hq, hqfin, -, hqsurj, -, hsq⟩ :=
    AbQuotientAny.exists_quotient_abelianScheme K A.X H i A.ab hi hmono hfin hflat
  obtain ⟨g, hg⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K B' hB
  let B : AbVar K := ⟨B', hB, g, hg⟩
  refine ⟨B, Hom.mk (B := B) q, ⟨hqfin, hqsurj⟩, fun T x => ⟨fun hx => ?_, ?_⟩⟩
  · have e : x ≫ q = (1 : T ⟶ A.X) ≫ q := by
      rw [MonObj.one_comp]; exact hx
    have h1 := hsq.lift_fst x 1 e
    have h2 := hsq.lift_snd x 1 e
    rw [MonObj.comp_mul, h2, _root_.mul_one, ← Category.assoc] at h1
    exact ⟨_, h1⟩
  · rintro ⟨y, rfl⟩
    have hw := congrArg (fun f => lift y (1 : T ⟶ A.X) ≫ f) hsq.w
    rw [← Category.assoc, ← Category.assoc, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst,
      _root_.mul_one] at hw
    rw [MonObj.one_comp] at hw
    exact hw

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinementTautologicalChartFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.taut_refine : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  intro o _ ζ g n φ hn C hCN
  obtain ⟨hmono, -, hcone, hdef, ht0⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ hn C
  have hsymm : ∀ i y z, ((n : ℤ) • C.δ i) y z = ((n : ℤ) • C.δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, mem_balForms_int.1 (hcone.mem i) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • C.δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hcone.nonneg i y)
  have hdef' : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • C.δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    refine ⟨i, ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hn) hi
  obtain ⟨R', _, _, _, ρ, -, D, e, hCN', hinj, hfin, hloc, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun i => (n : ℤ) • C.δ i) hCN hmono C.bd ht0 hsymm hnn hdef'
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, D, e, hCN', hinj, hfin, hloc, href⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  first | exact @GlobalTheory.Mix.exists_sec_bc | exact GlobalTheory.Mix.exists_sec_bc | (intros; apply GlobalTheory.Mix.exists_sec_bc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfExtendsOverCompleteDvrsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_extends_over_complete_dvrs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt G L (spMap (algebraMap R (FractionRing R)) ≫ χ)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ σ : SecAt G L (spMap φ ≫ χ), SecM.ofSec G (SecAt.pull G L σ (algebraMap V (FractionRing V))) = SecM.ofSec G (h ▸ SecAt.pull G L θ φK)) → ∃ σ : SecAt G L χ, SecM.ofSec G (SecAt.pull G L σ (algebraMap R (FractionRing R))) = SecM.ofSec G θ := by
  first | exact @GlobalTheory.UMin.SecExtend.exists_sec_of_extends | exact GlobalTheory.UMin.SecExtend.exists_sec_of_extends | (intros; apply GlobalTheory.UMin.SecExtend.exists_sec_of_extends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFnStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := by
  first | exact @GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | exact GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | (intros; apply GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShiftStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_section_add_multiple_ample_after_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (N : HermLB p) (s : X.functionField), IsAmpleLB P.A.B → s ∈ P.H 0 1 → s ≠ 0 → ∃ c₁ : ℕ, ∀ c, c₁ ≤ c → 0 < c → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Le (((shiftA P u).A.pow c).dual) N := by
  first | exact @GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift | exact GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift | (intros; apply GlobalTheory.HSNef.TwistSmall.le_dual_pow_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGeneratedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_semipositive_weight_of_generated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X), B.IsLB → (∃ (n : ℕ) (u : Fin n → B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → ∃ (φ : Weight p σ B), φ.IsCInf ∧ ∀ D : ℕ, φ.SemiPosReg D := by
  first | exact @GlobalTheory.weight_cInf_semiPos_of_generated | exact GlobalTheory.weight_cInf_semiPos_of_generated | (intros; apply GlobalTheory.weight_cInf_semiPos_of_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothWeightIntegralCombinationStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothWeight_integral_combination : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  first | exact @GlobalTheory.ChernCalc.exists_comb_smoothWeight | exact GlobalTheory.ChernCalc.exists_comb_smoothWeight | (intros; apply GlobalTheory.ChernCalc.exists_comb_smoothWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareDecompositionFiniteExtensionAmpleBunStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  first | exact @GlobalTheory.SqDecFinite.sqDec_of_finite_extension | exact GlobalTheory.SqDecFinite.sqDec_of_finite_extension | (intros; apply GlobalTheory.SqDecFinite.sqDec_of_finite_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrBoxOfIsSumDeg
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

variable {R : Type} [CommRing R] [IsDomain R] {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A)
  [IsMonHom p₁] [IsMonHom p₂] (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left))

theorem isBoxGen_cub (hw : w.IsGen) :
    IsBoxGen w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D.P.isAb _) (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
  have he : e.left ≫ (snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (ε := thε)
    (fun a => (CubeMap.ofHom p₁).psum_comm a.down) (fun a => (CubeMap.ofHom p₂).psum_comm a.down)
    D.cub.isGen D₁.cub.isGen D₂.cub.isGen _ e.left he sj fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have C : IsCub (cubV D.cub s I) := isCub_cubV D.cub hI
  have C₁ : IsCub (cubV D₁.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₁) := isCub_cubV D₁.cub hI₁
  have C₂ : IsCub (cubV D₂.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₂) := isCub_cubV D₂.cub hI₂
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1 1 (om w s I₁ I₂ I)
  rw [_root_.mul_one, _root_.mul_one] at p
  have o₁ : e.left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₁.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₁ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have o₂ : e.left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₂.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₂ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have v₁ := (congrArg (fun m => val D₁.cub.t m s I₁) o₁).trans (C₁.face 1 1)
  have v₂ := (congrArg (fun m => val D₂.cub.t m s I₂) o₂).trans (C₂.face 1 1)
  exact (congrArg₂ (· * ·) p (C.face 1 1)).trans (Eq.trans (by simp) (congrArg₂ (· * ·) v₁ v₂).symm)

theorem isBoxGen_sym (hw : w.IsGen) : IsBoxGen w p₁.left p₂.left D.sym D₁.sym D₂.sym := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (inv_comp p₁) (inv_comp p₂)
    D.sym_gen D₁.sym_gen D₂.sym_gen D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have q := prod_sym (eSec D.P.A) (om w s I₁ I₂ I)
  have o : eSec D.P.A ≫ (ι[D.P.A]).left = eSec D.P.A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[D.P.A] ≫ ι[D.P.A] = η[D.P.A])
  rw [o, mul_inv_cancel] at q
  rw [eSec_comp, eSec_comp, val_sym_zero D₁ hI₁, val_sym_zero D₂ hI₂]
  exact congrArg₂ (· * ·) q (val_sym_zero D hI)

theorem exists_strBox_of_isSumDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), StrBox p₁ p₂ w D.rig D₁.rig D₂.rig D.cub.t D₁.cub.t D₂.cub.t D.sym D₁.sym D₂.sym ∧ ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ h
  have := h.hom₁
  have := h.hom₂
  obtain ⟨w, hw, hr, hψ⟩ := h.w
  exact ⟨w, ⟨hw, isBoxGen_of_mapsAt w _ _ hr, isBoxGen_cub p₁ p₂ w hw, isBoxGen_sym p₁ p₂ w hw⟩,
    fun x => isBoxGen_of_mapsAt w _ _ (hψ x)⟩

end GlobalTheory.ProdUnif
end
end


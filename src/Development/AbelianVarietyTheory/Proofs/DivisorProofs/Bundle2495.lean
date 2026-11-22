import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLabelCommonGenericFibrePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

open MonObj

namespace GlobalTheory.Poinc.DeepLab

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

section Push
variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun _ _ e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

end Push

theorem exists_lab {Γ₁ Γ₂ H : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Group H] (L : ℕ)
    (f : Multiplicative Γ₂ →* H) (s : Multiplicative Γ₁ →* H)
    (uniq : ∀ z : H, z ^ L = 1 → ∃! b : Γ₂, f (Multiplicative.ofAdd b) = z)
    (hsL : ∀ a : Γ₁, s (Multiplicative.ofAdd a) ^ L = 1) :
    ∃ lab : Γ₁ →+ Γ₂, ∀ a, f (Multiplicative.ofAdd (lab a)) = s (Multiplicative.ofAdd a) := by
  choose l hl hu using fun a => uniq _ (hsL a)
  refine ⟨AddMonoidHom.mk' l fun a b => (hu (a + b) _ ?_).symm, hl⟩
  simp only [ofAdd_add, map_mul, hl]

theorem nsmul_self_eq_zero {κ : Type} (L : ℕ) (a : κ → ZMod L) : L • a = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem map_pow_self {κ H : Type} [Group H] (L : ℕ) (p : Multiplicative (κ → ZMod L) →* H) (a : κ → ZMod L) :
    p (Multiplicative.ofAdd a) ^ L = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_self_eq_zero, ofAdd_zero, map_one]

end GlobalTheory.Poinc.DeepLab

namespace GlobalTheory.Poinc.DeepLab

theorem exists_lab_same : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (φ : Ω₁ →+* Ω₂) (h : S₁.R →+* S₂.R) (ψ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), (∀ a, ((h a : S₂.R) : Ω₂) = φ a) → IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap h) ψ → LBIso ρ₂.P.L (ρ₁.P.L.pull ψ) → (∀ E, (ε₂ E).left ≫ ψ = ψ ≫ (ε₁ E).left) → S₁.r * S₁.N ∣ S₂.r * S₂.N → ∃ lab : S₁.Gam →+ S₂.Gam, Same ρ₁ ε₁ ρ₂ ε₂ lab φ ∧ ∀ x : S₂.Gam, ∃ a, lab a = (S₂.r * S₂.N / (S₁.r * S₁.N)) • x := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ ε₁ ε₂ φ h ψ hh hpb hL hε hd
  have hcomp : S₂.R.val.toRingHom.comp h = φ.comp S₁.R.val.toRingHom := RingHom.ext fun a => hh a
  have hsp : spMap (φ.comp S₁.R.val.toRingHom) = spMap S₂.R.val.toRingHom ≫ spMap h := by
    rw [← hcomp, spMap_comp]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap h) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ ψ = spMap h ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have uniq : ∀ z : Over.mk x₀ ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, (preHom V₂).comp p₂ (Multiplicative.ofAdd b) = z := fun z hz =>
    ρ₂.pt_bij K x₀ z hz
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    obtain ⟨c, hc⟩ := hd
    rw [hc, pow_mul, map_pow_self, one_pow]
  have hsL : ∀ a : S₁.Gam, (preHom V₂).comp σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [MonoidHom.comp_apply, ← map_pow, hσL, map_one]
  obtain ⟨lab, hlab⟩ := exists_lab _ _ _ uniq hsL
  have hlabl : ∀ a : S₁.Gam, x₀ ≫ (ρ₂.pt (lab a)).left = x₀ ≫ (σ (Multiplicative.ofAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hlab a)
  haveI := epi_spMap_field (algebraMap Ω₂ K)
  refine ⟨lab, ?_, ?_⟩
  · let P₀ := GlobalTheory.StrictPull.polPull ρ₂.P (spMap S₂.R.val.toRingHom)
    refine ⟨P₀, pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ ψ,
      pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom),
      fun E => (Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E), ?_, isGrpPullback_pullback _ _, ?_,
      GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, ?_, ?_⟩
    · rw [hsp]; exact IsGrpPullback.comp (isGrpPullback_pullback _ _) hpb
    · exact GlobalTheory.PolDeg.lbIso_pull_comp hL _ rfl
    · intro E
      have e₁ : ((Over.pullback (spMap S₂.R.val.toRingHom)).map (ε₂ E)).left ≫
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) =
          pullback.fst ρ₂.P.A.hom (spMap S₂.R.val.toRingHom) ≫ (ε₂ E).left := pullback.lift_fst _ _ _
      refine ⟨?_, e₁⟩
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) e₁).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (hε E)).trans (Category.assoc _ _ _).symm)))
    · intro x
      refine ⟨pullback.lift (spMap S₂.R.val.toRingHom ≫ (ρ₂.pt (lab x)).left) (𝟙 _) ?_, ?_,
        pullback.lift_fst _ _ _⟩
      · rw [Category.assoc, Over.w]; simp
      · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (pullback.lift_fst _ _ _)).trans ?_)
        rw [hsp, ← cancel_epi (spMap (algebraMap Ω₂ K))]
        have e₂ := congrArg (· ≫ ψ) (hlabl x)
        simp only [x₀, Category.assoc] at e₂ ⊢
        rw [e₂, hσl]
        rfl
  · intro x
    set y := (S₂.r * S₂.N / (S₁.r * S₁.N)) • x with hy
    have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
      rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, Nat.mul_div_cancel' hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
    let T₀ : Over (Sp S₂.R) := Over.mk x₀
    let V₁ : Over.mk (x₀ ≫ spMap h) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap h) (by simp)
    let z₁ : Over.mk (x₀ ≫ spMap h) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
    have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
      have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
        have h3 := congrArg (preHom V₂) hyL
        rwa [map_pow, map_one] at h3
      show (pushHom hpb T₀) _ ^ _ = 1
      rw [← map_pow, h0, map_one]
    obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap h) z₁ hz₁
    refine ⟨a, ?_⟩
    have hpush : pushHom hpb T₀ (V₂ ≫ σ (Multiplicative.ofAdd a)) = V₁ ≫ ρ₁.pt a := by
      apply Over.OverMorphism.ext
      show (V₂ ≫ σ _).left ≫ ψ = (V₁ ≫ ρ₁.pt a).left
      simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
      rw [hσl]
      rfl
    have h1 : V₂ ≫ σ (Multiplicative.ofAdd a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
    have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
      rwa [map_pow, map_one] at h3
    exact (uniq _ h2).unique ((hlab a).trans h1) rfl

end GlobalTheory.Poinc.DeepLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedThetaCoefficientSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN GlobalTheory.PsiRing GlobalTheory.PsiCoef

namespace GlobalTheory.PsiCoefMk

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_twist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (th : SecBT D (𝟙_ _) 1 0) :
    ∃ g : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g (lift (toUnit T) y).left z J =
        sval th (lift (toUnit T) (y * cT D T χ)).left z J * (val u (toUnit T).left z J * rigV D z J).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1)))
      (famφT D (𝟙_ _) χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [comp_cT, cT_zero]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB hF (pullMulSec th τ.left
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _))
  refine ⟨g, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, comp_cT, lift_snd]
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_pull hJ, e₃, val_mul hJ]
  congr 4

theorem exists_sec_coef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ b : R, ∃ g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ, GlobalTheory.PsiRing.Coef D χ u th g b := by
  intro R _ _ _ D th χ u hu b
  obtain ⟨g, hg⟩ := exists_twist D χ u hu th
  refine ⟨GlobalTheory.IndivisibleSection.smulSec (scal (𝟙_ _ ⊗ D.P.A).hom b) g, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
  have h := GlobalTheory.IndivisibleSection.sval_of_secIsMul (p := (𝟙_ _ ⊗ D.P.A).hom) (a := b)
    (s := GlobalTheory.IndivisibleSection.smulSec (scal (𝟙_ _ ⊗ D.P.A).hom b) g) (t := g) (fun _ => rfl)
    (lift (toUnit T) y).left z hJ
  rw [e₁, hg T y z J hJ] at h
  exact h.trans (by ring)

end GlobalTheory.PsiCoefMk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslateSurj

theorem surjective_of_factor {X Y Z : Scheme.{0}} (p : X ⟶ Y) (O : X.Opens) (g : Z ⟶ X) (q : Z ⟶ Y)
    (hg : g ≫ p = q) (hq : Surjective q) (hO : ∀ z, g z ∈ O) : Surjective (O.ι ≫ p) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hq.surj y
  refine ⟨⟨g z, hO z⟩, ?_⟩
  rw [← hg]
  rfl

end GlobalTheory.TranslateSurj

namespace GlobalTheory.TranslateSurj

theorem exists_translates_surjective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  intro S A _ hA V B j hjV hBs hBg
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI := hBs
  haveI := hBg
  haveI : GeometricallyConnected B.hom := GlobalTheory.geometricallyConnected_of_geometricallyIntegral _
  haveI : Smooth (fst (A ⊗ A) B ≫ fst A A).left := by
    show Smooth (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom); infer_instance
  haveI : GeometricallyConnected (fst (A ⊗ A) B ≫ fst A A).left := by
    show GeometricallyConnected (pullback.fst (A ⊗ A).hom B.hom ≫ pullback.fst A.hom A.hom)
    exact GeometricallyConnected.comp _ _
  haveI : GeometricallyIntegral (fst (A ⊗ A) B ≫ fst A A).left := GlobalTheory.geometricallyIntegral_of_smooth _
  have hq : Surjective (fst A B).left := by
    show Surjective (pullback.fst A.hom B.hom); infer_instance
  have key : ∀ (a₀ : A ⊗ B ⟶ A) (w : (A ⊗ A) ⊗ B ⟶ A),
      lift (lift (fst A B) a₀) (snd A B) ≫ w = snd A B ≫ j →
      Surjective ((w.left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
    intro a₀ w hw
    refine surjective_of_factor _ _ (lift (lift (fst A B) a₀) (snd A B)).left (fst A B).left ?_ hq ?_
    · rw [← Over.comp_left]; congr 1; simp
    · intro z
      show w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) ∈ V
      have e : w.left ((lift (lift (fst A B) a₀) (snd A B)).left z) = j.left ((snd A B).left z) := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw, Over.comp_left, Scheme.Hom.comp_apply]
      rw [e]; exact hjV _
  refine GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ (GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ (GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral _ _ _ _ _ ?_ ?_) ?_) ?_
  · refine key ((fst A B)⁻¹ * (snd A B ≫ j)) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key ((snd A B ≫ j)⁻¹ * fst A B) _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]
  · refine key 1 _ ?_
    simp [MonObj.comp_mul, GrpObj.comp_inv]

end GlobalTheory.TranslateSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistSquareZeroSmoothLiftSystemByDerivatio
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Twist

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

def twistHom {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B']
    [Algebra R B'] (hI : I ^ 2 = 0) (p : B →+* B₀) (hp : SemiHom π p) (α : B →ₐ[R] B') (θ : Ω[B₀⁄R₀] →+ B')
    (hsm : ∀ b w, θ (p b • w) = α b * θ w) (hmem : ∀ w, θ w ∈ I.map (algebraMap R B')) : B →ₐ[R] B' where
  toFun b := α b + θ (D R₀ B₀ (p b))
  map_one' := by simp
  map_mul' b c := by
    have h := mul_eq_zero_of_mem_map hI (hmem (D R₀ B₀ (p b))) (hmem (D R₀ B₀ (p c)))
    simp only [map_mul, Derivation.leibniz, map_add, hsm]
    linear_combination -h
  map_zero' := by simp
  map_add' b c := by simp only [map_add]; abel
  commutes' r := by
    simp only [SemiHom.map_algebraMap hp, Derivation.map_algebraMap, map_zero, add_zero, AlgHom.commutes]

variable {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) (hI : I ^ 2 = 0)
  (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V)
  (hsm : ∀ (U V : AffOp X₀) (a : U ⟶ V) b w, θ U V a (S.p U b • w) = mp S.F a b * θ U V a w)
  (hmem : ∀ (U V : AffOp X₀) (a : U ⟶ V) w, θ U V a w ∈ I.map (algebraMap R (S.F.obj V)))
  (hid : ∀ U, θ U U (𝟙 U) = 0)
  (hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
    θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))))

def twistF : AffOp X₀ ⥤ CommAlgCat.{0} R where
  obj := S.F.obj
  map {U V} a := CommAlgCat.ofHom (twistHom hI (S.p U) (S.semi U) (mp S.F a) (θ U V a) (hsm U V a) (hmem U V a))
  map_id U := CommAlgCat.hom_ext (AlgHom.ext fun b ↦ by
    change mp S.F (𝟙 U) b + θ U U (𝟙 U) (D R₀ _ (S.p U b)) = b
    rw [hid, AddMonoidHom.zero_apply, add_zero, mp_id])
  map_comp {U V W} a b := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ by
    change mp S.F (a ≫ b) c + θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
      mp S.F b (mp S.F a c + θ U V a (D R₀ _ (S.p U c))) +
        θ V W b (D R₀ _ (S.p V (mp S.F a c + θ U V a (D R₀ _ (S.p U c)))))
    have h0 : S.p V (θ U V a (D R₀ _ (S.p U c))) = 0 := (S.ker V _).2 (hmem U V a _)
    rw [map_add (S.p V), h0, add_zero, hcomp, mp_comp, map_add]
    abel)

def twistSys : Sys I π s₀ where
  F := twistF S hI θ hsm hmem hid hcomp
  p := S.p
  semi := S.semi
  nat {U V} a b := by
    change S.p V (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) = _
    rw [map_add, (S.ker V _).2 (hmem U V a _), add_zero]
    exact S.nat a b
  surj := S.surj
  ker := S.ker
  smooth := S.smooth

def ev {S' : Sys I π s₀} (v : GlobForm s₀ →+ Z1 S'.F) {U V : AffOp X₀}
    (a : U ⟶ V) : GlobForm s₀ →+ S'.F.obj V where
  toFun w := (v w).1 U V a
  map_zero' := by simp
  map_add' w w' := by simp

end GlobalTheory.LiftSys.Twist

namespace GlobalTheory.LiftSys

open Twist

theorem exists_twist : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S : Sys I π s₀) (v : GlobForm s₀ →+ Z1 S.F), (∀ w, S.IsIdealValuedLiftSystemCocycle (v w)) → (∀ (r : R) w, v (π r • w) = r • v w) → ∃ (S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ ∧ ∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = Φ.φ V ((v w).1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S v hv hs
  have hex : ∀ (U V : AffOp X₀) (a : U ⟶ V), ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj V,
      (∀ b w, θ (S.p U b • w) = mp S.F a b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R (S.F.obj V))) ∧
        ∀ w : GlobForm s₀, θ (w.1 U) = (v w).1 U V a := fun U V a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U _ _ (S.p U) (S.semi U) (S.surj U) (S.ker U) (mp S.F a)
      (ev v a) (fun r w ↦ by show (v (π r • w)).1 U V a = r • (v w).1 U V a; rw [hs]; rfl) (fun w ↦ hv w U V a)
  choose θ hθ huniq using hex
  have hsm := fun U V a ↦ (hθ U V a).1
  have hmem := fun U V a ↦ (hθ U V a).2.1
  have hglob := fun U V a ↦ (hθ U V a).2.2
  have hid : ∀ U, θ U U (𝟙 U) = 0 := fun U ↦ (huniq U U (𝟙 U) 0
    ⟨fun b w ↦ by simp, fun w ↦ by simp, fun w ↦ by rw [AddMonoidHom.zero_apply, Z1.id]⟩).symm
  have hcomp' : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]),
      θ U W (a ≫ b) x = mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x) := by
    intro U V W a b
    let ψ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S.F.obj W :=
      AddMonoidHom.mk' (fun x ↦ mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x)) (fun x y ↦ by
        simp only [map_add]; abel)
    have e : ψ = θ U W (a ≫ b) := by
      refine huniq U W (a ≫ b) ψ ⟨fun c x ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩
      · show mp S.F b (θ U V a (S.p U c • x)) + θ V W b (p1 (OAff s₀) a (S.p U c • x)) =
          mp S.F (a ≫ b) c * (mp S.F b (θ U V a x) + θ V W b (p1 (OAff s₀) a x))
        rw [hsm, oneFormsMapOfFunctorMorphism_smul, ← S.nat, hsm, map_mul, mp_comp, mul_add]
      · exact Ideal.add_mem _ (algHom_mem_map I (mp S.F b) (hmem U V a x)) (hmem V W b _)
      · show mp S.F b (θ U V a (w.1 U)) + θ V W b (p1 (OAff s₀) a (w.1 U)) = (v w).1 U W (a ≫ b)
        rw [← w.2 a, hglob, hglob, Z1.comp]
    intro x
    rw [← e]
    rfl
  have hcomp : ∀ (U V W : AffOp X₀) (a : U ⟶ V) (b : V ⟶ W) (c : S.F.obj U),
      θ U W (a ≫ b) (D R₀ _ (S.p U c)) =
        mp S.F b (θ U V a (D R₀ _ (S.p U c))) + θ V W b (D R₀ _ (S.p V (mp S.F a c))) := by
    intro U V W a b c
    rw [hcomp', p1_D, S.nat]
  let S' := twistSys S hI θ hsm hmem hid hcomp
  let Φ : S.LocIso S' := ⟨fun _ ↦ AlgEquiv.refl, fun _ _ ↦ rfl⟩
  refine ⟨S', Φ, θ, fun U V a ↦ ⟨fun b w ↦ ?_, fun b ↦ ?_, hmem U V a⟩, fun w U V a ↦ hglob U V a w⟩
  · show θ U V a (S.p U b • w) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) * θ U V a w
    rw [hsm, add_mul, mul_eq_zero_of_mem_map hI (hmem U V a _) (hmem U V a _), add_zero]
  · show θ U V a (D R₀ _ (S.p U b)) = (mp S.F a b + θ U V a (D R₀ _ (S.p U b))) - mp S.F a b
    rw [add_sub_cancel_left]

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularFrameInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_frame_inertPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.InertFrameUnimod.exists_frame_unimod | exact GlobalTheory.InertFrameUnimod.exists_frame_unimod | (intros; apply GlobalTheory.InertFrameUnimod.exists_frame_unimod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueBaseChangeVolumeFormStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_base_change_volume_form : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R' N] (e : R' ⊗[R] M ≃ₗ[R'] N)
    (n : ℕ) (δ : M [⋀^Fin n]→ₗ[R] R), Submodule.span R {δ} = ⊤ →
    ∃! δ' : N [⋀^Fin n]→ₗ[R'] R', Submodule.span R' {δ'} = ⊤ ∧
      ∀ v : Fin n → M, δ' (fun i ↦ e (1 ⊗ₜ v i)) = algebraMap R R' (δ v) := by
  first | exact @GlobalTheory.AltBaseChange.exists_unique_baseChange_generator | exact GlobalTheory.AltBaseChange.exists_unique_baseChange_generator | (intros; apply GlobalTheory.AltBaseChange.exists_unique_baseChange_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitBasicOpenOfCoboundaryIdentityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_basicOpen_of_coboundary_identity : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (V V₀ : Y.Opens)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
    (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ)
    (r : Γ(Y, V₀)) (m s : Γ(X, f ⁻¹ᵁ V₀)) (n : ℕ),
    ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m →
    m * s = (f.app V₀).hom r ^ n →
    ∃ u : Γ(X, f ⁻¹ᵁ Y.basicOpen r)ˣ, ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ Y.basicOpen r →
      gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  first | exact @GlobalTheory.LBDescent.coboundary_unit_basicOpen | exact GlobalTheory.LBDescent.coboundary_unit_basicOpen | (intros; apply GlobalTheory.LBDescent.coboundary_unit_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLiftClosedSubschemeNearFibreStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_lift_closed_subscheme_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  first | exact @GlobalTheory.Pinch.unit_lift_near_fibre | exact GlobalTheory.Pinch.unit_lift_near_fibre | (intros; apply GlobalTheory.Pinch.unit_lift_near_fibre <;> assumption)
end


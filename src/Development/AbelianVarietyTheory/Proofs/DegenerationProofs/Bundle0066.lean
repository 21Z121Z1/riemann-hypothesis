import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftGlobal

open CommPairing GlobalLift

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem exists_symLift_pull_val (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) :
    ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', ⟨e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, v⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q

omit [GrpObj A] in

theorem exists_lift_res {T : Over S} (V : T.left.Opens) {Z : Scheme.{0}} (ρ : Z ⟶ (T ⊗ A).left)
    (hρ : ∀ z, (fst T A).left (ρ z) ∈ V) :
    ∃ n : Z ⟶ (overRes V ⊗ A).left, n ≫ (overResι V ▷ A).left = ρ := by
  obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = ρ ≫ (fst T A).left :=
    ⟨IsOpenImmersion.lift V.ι (ρ ≫ (fst T A).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hρ y), IsOpenImmersion.lift_fac _ _ _⟩
  let ρ' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ T ⊗ A := Over.homMk ρ rfl
  let v' : Over.mk (ρ ≫ (T ⊗ A).hom) ⟶ overRes V := Over.homMk v (by
    show v ≫ V.ι ≫ T.hom = ρ ≫ (T ⊗ A).hom
    rw [← Category.assoc, hv, Category.assoc, Over.w (fst T A)])
  have e : v' ≫ overResι V = ρ' ≫ fst T A := Over.OverMorphism.ext hv
  have e' : lift v' (ρ' ≫ snd T A) ≫ overResι V ▷ A = ρ' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, e]
    · rw [Category.assoc, whiskerRight_snd, lift_snd]
  exact ⟨(lift v' (ρ' ≫ snd T A)).left, congrArg (fun q => q.left) e'⟩

omit [GrpObj A] in
theorem mono_res {T : Over S} (V : T.left.Opens) : Mono (overResι V ▷ A).left := by
  have : Mono (overResι V).left := inferInstanceAs (Mono V.ι)
  have : Mono (overResι V) := Over.mono_of_mono_left _
  have : Mono (overResι V ▷ A) := ⟨fun a b e => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← cancel_mono (overResι V), Category.assoc, Category.assoc, ← whiskerRight_fst, ← Category.assoc, e,
        Category.assoc]
    · rw [← whiskerRight_snd (overResι V), ← Category.assoc, e, Category.assoc]⟩
  infer_instance

theorem tval_agree (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n) {T : Over S}
    {x : T ⟶ A} {V V' : T.left.Opens} {θ : ThetaGrp A L k (overRes V)} {θ' : ThetaGrp A L k (overRes V')}
    (H : SymLift A L k n (overResι V ≫ x) θ) (H' : SymLift A L k n (overResι V' ≫ x) θ')
    {Z : Scheme.{0}} (r : Z ⟶ (overRes V ⊗ A).left) (r' : Z ⟶ (overRes V' ⊗ A).left)
    (hr : r ≫ (overResι V ▷ A).left = r' ≫ (overResι V' ▷ A).left) (z : Z) (J) (hJ : Good L z J) :
    tval θ r z J = tval θ' r' z J := by
  have mem : ∀ (W : T.left.Opens) (s : Z ⟶ (overRes W ⊗ A).left) (y : Z),
      (fst T A).left ((s ≫ (overResι W ▷ A).left) y) ∈ W := fun W s y => by
    have e : (overResι W ▷ A).left ≫ (fst T A).left = (fst (overRes W) A).left ≫ W.ι := by
      rw [← Over.comp_left, whiskerRight_fst]; rfl
    exact (congrArg (fun q => q (s y) ∈ W) e).mpr ((fst (overRes W) A).left (s y)).2
  obtain ⟨m, hm⟩ := exists_lift_res (V ⊓ V') (r ≫ (overResι V ▷ A).left)
    (fun y => ⟨mem V r y, hr ▸ mem V' r' y⟩)
  have inc : ∀ (W : T.left.Opens), V ⊓ V' ≤ W → ∃ i : overRes (V ⊓ V') ⟶ overRes W,
      i ≫ overResι W = overResι (V ⊓ V') := fun W hW =>
    ⟨Over.homMk (T.left.homOfLE hW) (by
      show T.left.homOfLE hW ≫ W.ι ≫ T.hom = (V ⊓ V').ι ≫ T.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]), Over.OverMorphism.ext (T.left.homOfLE_ι hW)⟩
  obtain ⟨i, hi⟩ := inc V inf_le_left
  obtain ⟨i', hi'⟩ := inc V' inf_le_right
  obtain ⟨ξ, Hξ, vξ⟩ := exists_symLift_pull_val hL i H
  obtain ⟨ξ', Hξ', vξ'⟩ := exists_symLift_pull_val hL i' H'
  rw [← Category.assoc, hi] at Hξ
  rw [← Category.assoc, hi'] at Hξ'
  have := mono_res (A := A) V
  have := mono_res (A := A) V'
  have e : m ≫ (i ▷ A).left = r := by
    rw [← cancel_mono (overResι V ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi, hm]
  have e' : m ≫ (i' ▷ A).left = r' := by
    rw [← cancel_mono (overResι V' ▷ A).left, Category.assoc, ← Over.comp_left, ← comp_whiskerRight, hi', hm, hr]
  rw [← e, ← e', ← vξ _ _ z J hJ, ← vξ' _ _ z J hJ]
  exact val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn ξ ξ' Hξ Hξ') m

theorem exists_lift_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {T : Over S} {x : T ⟶ A}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L k (overRes V), SymLift A L k n (overResι V ≫ x) θ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  choose V hV θ hθ using h
  choose m hm using fun p => exists_lift_res (A := A) (V p) ((fst T A).left ⁻¹ᵁ V p).ι (fun z => z.2)
  have loc : ∀ p, ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
      (fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) ![k, -k]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ ((fst T A).left ⁻¹ᵁ V p).toScheme) (z : Z) (J), Good L z J →
        val t r z J = tval (θ p) (r ≫ m p) z J := fun p => by
    have e₀ : m p ≫ (snd (overRes (V p)) A).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (snd T A).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have e₁ : m p ≫ (translPt A (θ p).pt).left = ((fst T A).left ⁻¹ᵁ V p).ι ≫ (translPt A x).left := by
      rw [← hm p, Category.assoc, ← Over.comp_left, whisker_translPt, (hθ p).pt_eq]
    obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := Fin 2)
      (φ' := fun b => ((fst T A).left ⁻¹ᵁ V p).ι ≫ ![(snd T A).left, (translPt A x).left] b) (ε' := ![k, -k])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ k) e₀
        · exact congrArg (fun q => f q ^ (-k)) e₁)
      (LB.pullGen L ![(snd (overRes (V p)) A).left, (translPt A (θ p).pt).left] ![k, -k] (θ p).φ (m p))
      (DVR.pullGen_isGen _ _ _ _ (θ p).isGen _)
    exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩
  choose t ht hv using loc
  obtain ⟨u, hu, -⟩ := glue_gen hL (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]
    (fun p => (fst T A).left ⁻¹ᵁ V p) (fun y => ⟨(fst T A).left y, hV _⟩) t ht
    (fun p q Z r r' z J hJ e => by
      rw [hv p Z r z J hJ, hv q Z r' z J hJ]
      exact tval_agree hG hA hL hn (hθ p) (hθ q) _ _ (by rw [Category.assoc, Category.assoc, hm, hm, e]) z J hJ)
  exact ⟨⟨x, u, hu⟩, rfl⟩

end GlobalTheory.SymLiftGlobal

namespace GlobalTheory

theorem exists_symLift_global : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k →
    IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  intro hLaw S _ P k hk hu T x hx
  obtain ⟨θ, hθ⟩ := SymLiftGlobal.exists_lift_of_local hLaw.globalFns P.isAb P.isLB hk
    (hLaw.symLift S P k hk hu T x hx).1
  obtain ⟨nu, hnu⟩ := exists_gen_negLB hLaw.globalFns S P k T
  exact SymLiftOdd.exists_symLift hLaw.globalFns P.isAb P.isLB hk hx θ hθ hnu

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistedSectionThetaTranslateCoef
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiCoef

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem comp_cT {T T' : Over (Spec (CommRingCat.of R))} (r : T ⟶ T') (α : D.X) : r ≫ cT D T' α = cT D T α := by
  rw [← Category.assoc, comp_toUnit]

theorem exists_untwist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (g : SecBT D (𝟙_ _) 1 χ) :
    ∃ g₀ : SecBT D (𝟙_ _) 1 0, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g₀ (lift (toUnit T) (y * cT D T χ)).left z J =
        sval g (lift (toUnit T) y).left z J * ((val u (toUnit T).left z J * rigV D z J)⁻¹).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * (cT D Y χ)⁻¹)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) χ k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (fun k => -(Sum.elim (fun _ => -1) (fun _ => 1) k)))
      (famφT D (𝟙_ _) 0) (DegPre.famε 1) := by
    intro U _ h
    have e₀ : famφT D (𝟙_ _) 0 0 = famφT D (𝟙_ _) 0 1 := by
      change (snd _ _ : Y ⟶ D.P.A).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one]
    have e₀' : famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) 0 3 := by
      change (cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero]
    have e₁ : τ.left ≫ famφT D (𝟙_ _) χ 1 = famφT D (𝟙_ _) 0 1 := by
      change (τ ≫ (snd _ _ * cT D Y χ)).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one, MonObj.comp_mul, comp_cT, lift_snd, inv_mul_cancel_right]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) χ 2 = famφT D (𝟙_ _) χ 2 := by
      change (τ ≫ cT D Y χ).left = (cT D Y χ).left
      rw [comp_cT]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) χ 3 = famφT D (𝟙_ _) 0 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) 0 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₀, e₀', e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g₀, hg₀⟩ := exists_sec D.P.isLB hF (pullMulSec g τ.left
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _)))
  refine ⟨g₀, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) (y * cT D T χ)).left ≫ τ.left = (lift (toUnit T) y).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, GrpObj.comp_inv, comp_cT, lift_snd, mul_inv_cancel_right]
  have e₃ : (lift (toUnit T) (y * cT D T χ)).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg₀ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_inv, val_pull hJ, e₃, val_mul hJ]
  congr 5

theorem exists_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  intro R _ _ D th hth χ u hu g
  obtain ⟨g₀, hg₀⟩ := exists_untwist D χ u hu g
  obtain ⟨b, hb⟩ := hth g₀
  refine ⟨b, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) (y * cT D T χ)).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
  have h := hb _ (lift (toUnit T) (y * cT D T χ)).left z J hJ
  rw [e₁, hg₀ T y z J hJ, Units.mul_inv_eq_iff_eq_mul] at h
  rw [h]
  ring

end GlobalTheory.PsiCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UniformisedModel

theorem exists_finite_factor {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {p : ℕ} [Fact p.Prime]
    (y₀ : R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (y : R →+* K),
      (∀ a, (y a : PadicAlgCl p) = y₀ a) ∧ ∀ x ∈ Fs, x ∈ K := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  let t : Finset (PadicAlgCl p) := s.image y₀ ∪ Fs
  let K := IntermediateField.adjoin ℚ_[p] (t : Set (PadicAlgCl p))
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hy : ∀ a, y₀ a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _
        (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem K n
    | add a b _ _ ha hb => rw [map_add]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  exact ⟨K, hK, y₀.codRestrict K hy, fun _ => rfl, fun x hx =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_union_right _ hx))⟩

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_polBaseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
  rfl

theorem exists_isGrpPullback_jK {V K R : Type} [CommRing V] [IsDomain V] [CommRing K] [CommRing R] (a : V →+* K)
    (b : K →+* FractionRing V) (e : b.comp a = algebraMap V (FractionRing V)) (u : R →+* K)
    (G : Over (Sp V)) [GrpObj G] (A : Over (Sp R)) [GrpObj A] {φ : pullback G.hom (spMap a) ⟶ A.left}
    (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ, IsGrpPullback ((Over.pullback (jK V)).obj G) A (spMap (b.comp u)) ψ := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V))
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_spMap, e]) rfl)
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_spMap]) rfl⟩

end GlobalTheory.UniformisedModel

namespace GlobalTheory

open UniformisedModel in

theorem exists_uniformised_model : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hN hU hB o Ω _ _ _ _ S ρ p _ y₀ Fs
  haveI := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType S.R).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  obtain ⟨K, _, y, hy, hFs⟩ := exists_finite_factor y₀ Fs
  obtain ⟨P, φ₀, hφ₀, -⟩ := exists_polBaseChange hB (spMap y) ρ.P
  obtain ⟨K', h, _, _, G, _, hG, hE, φ, hφ⟩ := exists_semiAbelian_model_split_specialFibre hN p K P
  let V := integralClosure ℤ_[p] K'
  let e : FractionRing V ≃ₐ[V] K' := FractionRing.algEquiv V K'
  let y' : S.R →+* K' := (IntermediateField.inclusion h).toRingHom.comp y
  let b : K' →+* FractionRing V := e.symm.toRingEquiv.toRingHom
  have hb : b.comp (algebraMap V K') = algebraMap V (FractionRing V) := RingHom.ext fun x => e.symm.commutes x
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_jK (algebraMap V K') b hb y' G ρ.P.A
    ((hφ.comp hφ₀).congr (spMap_spMap _ _) rfl)
  obtain ⟨A, χ, hχ, hL⟩ := exists_polBaseChange hB (spMap (b.comp y')) ρ.P
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso hψ hχ
  haveI : CharZero V := charZero_integralClosure_padicInt
  haveI := hG.comm
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V :=
    CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] V
  obtain ⟨D, U, -⟩ := hU V hc A G hG hE
    (SymBaseChange.hypS_baseChange _ _ ρ.P.A A.A _ χ ρ.P.L A.L ρ.P.isLB A.isLB hχ hL ρ.hypS) gen hgen
  let c : FractionRing V →+* PadicAlgCl p := (algebraMap K' (PadicAlgCl p)).comp e.toRingEquiv.toRingHom
  have hcb : ∀ x : K', c (b x) = x := fun x => congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨{ V := V, complete := hc, alg := c.toAlgebra, norm_le := fun x => ?_, yK := b.comp y'
            fac := RingHom.ext fun a => (hcb (y' a)).trans (hy a), A := A, φ := χ, cart := hχ, lb := hL, G := G
            semi := hG, D := D, U := U }, fun x hx => ⟨b ⟨x, h (hFs x hx)⟩, hcb _⟩⟩
  refine (mem_integralClosure_padicInt_iff K' (e x)).symm.trans ⟨fun hx => ⟨⟨e x, hx⟩, ?_⟩, ?_⟩
  · exact e.injective (e.commutes _)
  · rintro ⟨v, rfl⟩
    rw [e.commutes]
    exact v.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueOfBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

open CommPairing GlobalLift VVRank ThetaCoord

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_symLift_one (hL : L.IsLB) {k : ℤ} {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k 1 1 θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ r z J = 1 := by
  have h1 : (LB.oneGen L (Y := (T ⊗ A).left)).IsGen := SymLiftOdd.isGen_of_gm fun y j j' _ _ => by
    rw [trF, Fintype.prod_empty, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      rw [Fintype.prod_empty, Fin.prod_univ_two, ThetaAct.translPt_one]
      simp) (LB.oneGen L) h1
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, t, ht⟩ : ThetaGrp A L k T) r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨1, t, ht⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · exact Finset.prod_eq_one fun _ _ => hv' _ _ _ _ hJ
  · rw [hv' _ _ _ _ hJ, hv' _ _ _ _ hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
      mul_inv_cancel]

theorem isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {ν : LB.Gen (negLB A L 1 T)} (hν : ν.IsGen) {a : ℤ} {m q : ℕ} (hq : Odd q)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -1])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L 1 T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a 1 α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by
  have := hA.comm
  obtain ⟨θ₁, h₁, v₁⟩ := exists_symLift_one hL hν
  obtain ⟨θ', h', v'⟩ := exists_symLift_mulPull hA hL (one_dvd q) hα hy (hm.symm ▸ h₁)
  have hc := SymLiftOdd.symLift_unique hG hA hL hq θ θ' H h'
  refine isTwistPull_of_sv A hL θ.isGen fun z J hJ => ?_
  have e : tval θ (𝟙 _) z J = tval θ' (𝟙 _) z J := val_corr hJ hc _
  have e₁ := sv_mulPull hs (fst T A) hJ (snd T A)
  have e₂ := sv_mulPull hs (fst T A) hJ ((fst T A ≫ y) * snd T A)
  have e₃ := v' _ (fst T A) z J hJ (snd T A)
  rw [v₁ _ _ _ _ hJ, _root_.mul_one] at e₃
  rw [mul_pow, ← MonObj.comp_pow, hm, MonObj.comp_one, _root_.one_mul] at e₂
  change _ = (tval θ (𝟙 _) z J).val * _
  rw [e, SymLiftOdd.id_eq_lift, ThetaCoord.lift_translT, H.pt_eq, e₃, e₁, e₂, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem act_act (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c)
    {s s' s'' t : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θy s s') (h₂ : IsActOf A L k θx s' s'')
    (h₃ : IsActOf A L k θ s t) :
    (SecM.ofSec A s'' : SecM A L k T) = ((c ^ ((q + 1) / 2) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A t := by
  refine ThetaAct.sv_ext hL fun z J hJ => ?_
  have e₁ := sv_act Hx.pt_eq h₂ (fst T A) hJ (snd T A)
  have e₂ := sv_act Hy.pt_eq h₁ (fst T A) hJ ((fst T A ≫ x) * snd T A)
  have e₃ := sv_act H.pt_eq h₃ (fst T A) hJ (snd T A)
  have e₄ := tval_mul hG hA hL hq hy Hx Hy H hc (fst T A) hJ (snd T A)
  rw [← _root_.mul_assoc, ← MonObj.comp_mul] at e₂
  rw [ThetaAct.sv_smul _ _ _ _ hJ, Category.id_comp, gs_unit _ _ ⊤ trivial, map_pow, SymLiftOdd.id_eq_lift]
  refine e₁.trans ?_
  rw [e₂, ← _root_.mul_assoc, ← Units.val_mul, e₄, Units.val_mul, _root_.mul_assoc, ← e₃]
  rfl

theorem sum_iff {k : ℤ} {κ : Type} [Fintype κ] (σ : LB.Sec (LPow A L k T)) (s : κ → SecM A L k T)
    (c : κ → Γ(T.left, ⊤)) :
    (∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j) ↔ SecM.ofSec A σ = ∑ i, c i • s i := by
  have e : ∀ j, (∑ i, c i • s i : SecM A L k T).1 j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

theorem existsUnique_of_basis {k : ℤ} {κ : Type} [Fintype κ] (s : Module.Basis κ Γ(T.left, ⊤) (SecM A L k T))
    (σ : LB.Sec (LPow A L k T)) :
    ∃! c : κ → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := by
  simp only [sum_iff]
  exact ⟨s.equivFun (SecM.ofSec A σ), (s.sum_equivFun _).symm, fun c hc => by
    rw [hc, ← s.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem UnivBasis.exists_basis {P : PolAV S} [IsAffine T.left] {n : ℤ} {κ : Type} {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T), ∀ i, c i = b i := by
  obtain ⟨c, hc⟩ := h T (𝟙 T)
  exact ⟨c, fun i => (hc i).trans (pullM_id P.A P.isLB n _)⟩

theorem UnivBasis.unique {P : PolAV S} {n : ℤ} {κ : Type} [Unique κ] {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : UnivBasis P n (fun _ : Fin 1 => b default) := fun T' _ u => by
  obtain ⟨c, hc⟩ := h T' u
  refine ⟨c.reindex (Equiv.ofUnique κ (Fin 1)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hc, Subsingleton.elim ((Equiv.ofUnique κ (Fin 1)).symm i) default]

end GlobalTheory.ThetaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  first | exact @GlobalTheory.SymBaseChange.hypS_baseChange | exact GlobalTheory.SymBaseChange.hypS_baseChange | (intros; apply GlobalTheory.SymBaseChange.hypS_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormDividingWeightSumEqOfModelPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.norm_dividing_weightSum_eq_of_model_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) := by
  first | exact @GlobalTheory.norm_val_FF_eq_of_div | exact GlobalTheory.norm_val_FF_eq_of_div | (intros; apply GlobalTheory.norm_val_FF_eq_of_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCharts_torus_extension_over_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  first | exact @GlobalTheory.SplitChartsField.main | exact GlobalTheory.SplitChartsField.main | (intros; apply GlobalTheory.SplitChartsField.main <;> assumption)
end


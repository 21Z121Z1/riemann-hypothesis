import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitKoszulInvariantOfFiniteClosedFibreZeros
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SymRoot

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def rigCls (c : Pic A.left) : Pic A.left := c - pull (1 : A ⟶ A).left c

theorem pull_rigCls (c : Pic A.left) (x : T ⟶ A) :
    pull x.left (rigCls c) = pull x.left c - pull (1 : T ⟶ A).left c := by
  rw [rigCls, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_one]

theorem lam_rigCls (c : Pic A.left) (x y : T ⟶ A) : lam (rigCls c) x y = lam c x y := by
  simp only [lam, pull_rigCls]
  abel

theorem lam_diag [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hs : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) :
    lam (cls L hL) (𝟙 A) (𝟙 A) = 2 • rigCls (cls L hL) := by
  have h := lam_mul_left hL hΘ (𝟙 A) (𝟙 A)⁻¹ (𝟙 A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls L hL) (𝟙 A)⁻¹ (𝟙 A) = -(2 • rigCls (cls L hL)) := by
    rw [lam, inv_mul_cancel, Hom.inv_def, Category.id_comp, hs, Over.id_left, pull_id, rigCls]
    abel
  rw [e] at h
  exact add_neg_eq_zero.1 h.symm

theorem exists_polAV_sqOf : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  intro laws h k o _ ζ R _ _ β c L ⟨ha, hk⟩ hdim hL hΛ hs
  have hA := c.ab
  have hd : c.diag.IsLB := pull_isLB c.isLB _
  have hp : IsProjBy c.A.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ c.A c.diag hA hd ha R (𝟙 _) _ (𝟙 _) c.A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ : ∃ t : LB.Gen (Theta c.A L), t.IsGen := CubeAffine.triv_theta_of_isProjBy laws R c.A hA hp L hL
  have s₁ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls L hL) = cls L hL :=
    ((cls_eq_iff hL (pull_isLB hL _)).2 hs).symm
  have e₀ : cls c.P c.isLB = lam (cls L hL) (fst c.A c.A) (snd c.A c.A) :=
    ((cls_eq_iff (LB.isLB_linComb hL _ _) c.isLB).2 hΛ).symm.trans (cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  obtain ⟨M, hM, e⟩ := cls_surj (rigCls (cls L hL))
  have e₁ : cls c.P c.isLB = lam (cls M hM) (fst c.A c.A) (snd c.A c.A) := by rw [e, lam_rigCls, e₀]
  have e₂ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls M hM) = cls M hM := by
    rw [e, pull_rigCls, s₁, rigCls]
  have e₃ : cls c.diag hd = 2 • cls M hM := by
    refine (cls_pull c.isLB _ _).trans ?_
    rw [e₀, pull_lam, lift_fst, lift_snd, lam_diag hL hΘ s₁, e]
  have hr : Out.Rigidified c.A M := by
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ((cls_pull hM _ _).trans ?_)
    have e₄ : (η[c.A] : 𝟙_ _ ⟶ c.A) = 1 := by rw [Hom.one_def]; simp
    have := pull_rigCls (cls L hL) η[c.A]
    rw [← e₄, sub_self, ← e] at this
    exact this
  have hsym : Out.Sym c.A M := fun s => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, e₂, one_smul, neg_smul, add_neg_cancel]⟩
  have hamp : Out.RelAmple c.A M := by
    have f : IsFinite (𝟙 c.A : c.A ⟶ c.A).left := by rw [Over.id_left]; infer_instance
    refine (relAmple_finite_pow_iso _ c.A c.A (𝟙 _) M 2 two_pos hA hA hM f).2.1.1
      ((relAmple_finite_pow_iso _ c.A c.A (𝟙 _) _ 2 two_pos hA hA hd f).2.2.2 _ (isLB_lbPow hM 2) ?_ ha)
    exact (cls_eq_iff hd (isLB_lbPow hM 2)).1 (e₃.trans (cls_lbPow hM 2 _).symm)
  have hid : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  refine ⟨{ A := c.A, isAb := hA, g := h, smoothDim := hdim, L := M, isLB := hM, rigid := hr, sym := hsym,
            ample := hamp, ktriv := ThetaExtend.kTriv_of_lam hM c.isLB e₁ hk }, 𝟙 _,
    (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl, rfl, 𝟙 _, ⟨by simp, by simp⟩, ?_⟩
  refine (cls_eq_iff (LB.isLB_linComb hM _ _) (pull_isLB c.isLB _)).1 ?_
  exact (cls_cube_two hM _ _ (LB.isLB_linComb hM _ _)).trans (e₁.symm.trans (pull_id _).symm)

end GlobalTheory.SymRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitKoszulInvariantOfFiniteClosedFibreZerosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_koszulInvariant_of_finite_closedFibre_zeros : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℚ O] (F : Type) [Field F] (f : O →+* F) (x : KeyIn O) (xF : KeyIn F) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : xF.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sF : Fin xF.P.g → RR xF n) (κ : Fˣ) (a : O) (e : ℤ), Function.Injective f → admitted x.P.g n l l' al → KeyVia xF x f φ w → (∀ i, SecVia xF x φ w (sF i) (s (i.cast hg))) → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → KaVal xF n l l' al sF κ → (κ : F) ^ e = f a → e ≠ 0 → IsUnit a := by
  first | exact @GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros | exact GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros | (intros; apply GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyComplexPointEqOfSamePeriodMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegelPointUnique
open GlobalTheory.SiegelPullComp

def TriplePB {J : Type} {S S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lev' : J → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lev : J → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧ IsSquare φ φ₂ ∧ LBIso P' (P.pull φ₂) ∧
      ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left

variable {J : Type} {S S' S'' : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (A ⊗ A).left}
  {lev : J → (𝟙_ (Over S) ⟶ A)} {A' : Over S'} [GrpObj A'] {P' : LB (A' ⊗ A').left}
  {lev' : J → (𝟙_ (Over S') ⟶ A')} {A'' : Over S''} [GrpObj A''] {P'' : LB (A'' ⊗ A'').left}
  {lev'' : J → (𝟙_ (Over S'') ⟶ A'')} {f : S' ⟶ S} {f' : S'' ⟶ S'}

theorem TriplePB.comp (hP : P.IsLB) (hP' : P'.IsLB) (hP'' : P''.IsLB) (m : TriplePB A' P' lev' A P lev f)
    (m' : TriplePB A'' P'' lev'' A' P' lev' f') : TriplePB A'' P'' lev'' A P lev (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, ⟨?_, ?_⟩, ?_, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans hP'' (pull_isLB hP' _) (pull_isLB (pull_isLB hP _) _) (iso_pull ψ₂ hw)).trans
      hP'' (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (iso_pull_pull hP φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem TriplePB.cancel (hP : P.IsLB) (hP' : P'.IsLB) (hP'' : P''.IsLB) (m : TriplePB A' P' lev' A P lev f)
    (n : TriplePB A'' P'' lev'' A P lev (f' ≫ f)) : TriplePB A'' P'' lev'' A' P' lev' f' := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨χ, χ₂, hχ, hs', hw', hl'⟩ := n
  have hp := hφ.1
  let F : A''.left ⟶ A'.left := hp.lift χ (A''.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ A'.hom = A''.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((A'' ⊗ A'').hom ≫ f') ⟶ A' ⊗ A' :=
    lift (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A''))
  let F₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left := U.left
  have h₁ : F₂ ≫ (fst A' A').left = (fst A'' A'').left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A'')))
  have h₂ : F₂ ≫ (snd A' A').left = (snd A'' A'').left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A'')))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans hP'' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (iso_pull_pull hP φ₂ F₂).symm).trans hP'' (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (lev'' a).left ≫ A''.hom = 𝟙 S'' := Over.w (lev'' a)
      have a₂ : (lev' a).left ≫ A'.hom = 𝟙 S' := Over.w (lev' a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem eq_of_ptAt : Out.Laws → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ → p = q := by
  intro hL hU h k K _ ζ σ F _ _ _ _ τ p q hp hq ⟨P, lev, φ, hper, ⟨hφ, _, φ₂, hs, hw⟩, hl⟩
    ⟨P', lev', φ', hper', ⟨hφ', _, φ₂', hs', hw'⟩, hl'⟩
  obtain ⟨c, hc⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h k K K ζ ζ (RingHom.id K) _ _ F.s (p ≫ F.s) p rfl
    (by rw [show spMap (RingHom.id K) = 𝟙 (Sp K) from Spec.map_id _, Category.comp_id])).1 F.univ
  obtain ⟨e, he, ⟨e₂, hes, hew⟩, hel⟩ := GlobalTheory.T.exists_iso_of_same_periodMatrix_level hL hU h k τ P' P lev' lev hper' hper
  have l : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have l' : (abelian₂ P'.A P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have m : TriplePB P.A (abelian₂ P.A P.L) lev F.univ.A F.univ.P F.univ.lev p := ⟨φ, φ₂, hφ, hs, hw, hl⟩
  have m' : TriplePB P'.A (abelian₂ P'.A P'.L) lev' F.univ.A F.univ.P F.univ.lev q := ⟨φ', φ₂', hφ', hs', hw', hl'⟩
  have n : TriplePB c.A c.P c.lev F.univ.A F.univ.P F.univ.lev (𝟙 _ ≫ p) := by
    rw [Category.id_comp]; exact hc
  have i : TriplePB P.A (abelian₂ P.A P.L) lev P'.A (abelian₂ P'.A P'.L) lev' (𝟙 _) :=
    ⟨e.hom.left, e₂, Geo.Tor.isGrpPullback_of_iso e, hes, hew, fun a =>
      (congrArg (fun t => t.left) (hel a)).trans (Category.id_comp _).symm⟩
  have r := m'.comp F.univ.isLB l' c.isLB (i.comp l' l c.isLB (m.cancel F.univ.isLB l c.isLB n))
  rw [Category.id_comp, Category.id_comp] at r
  exact F.inj ℂ p q _ c (hp.trans hq.symm) hc r

end GlobalTheory.SiegelPointUnique
end
end


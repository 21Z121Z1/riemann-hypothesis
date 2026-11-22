import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0020
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0028
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelative
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.AmpleUpstairs

open GlobalTheory.Cartier.CartierDiv in

theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) : (-D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.neg.mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_inv_eq_inv_val]
  exact hu.inv

open GlobalTheory.Cartier.CartierDiv in

theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) (m : ℕ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [(hg.nsmul m).mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_pow_eq_pow_val]
  have key : ∀ j : ℕ, UnitAt x ((g : X.functionField) ^ j) := by
    intro j
    induction j with
    | zero => simpa using unitAt_one x
    | succ j ih => rw [pow_succ]; exact ih.mul hu
  exact key m

end GlobalTheory.AmpleUpstairs

namespace GlobalTheory

open GlobalTheory.AmpleUpstairs in

theorem exists_ample_pull_sub_eff : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hq ht I hiso hI A hA
  obtain ⟨-, L₁, hL₁⟩ := isProper_and_exists_isAmpleLB_of_isProjOver ht
  haveI : CompactSpace Y₁ := hL₁.compactSpace
  haveI : CompactSpace Y₀ := hA.compactSpace
  haveI : IsNoetherian Y₀ := {}
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y₁ := GlobalTheory.ModifSections.isNormalScheme_of_smooth (t ≫ q)
  obtain ⟨H, hH⟩ := toPic_surjective (cls L₁ hL₁.isLB)
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.divisor_agreement_on_isomorphism k Y₀ Y₁ q n t ht I.support.compl hiso H
  obtain ⟨E₀, hE₀, hsE₀, hgen⟩ := GlobalTheory.T.blowup_ample_minus_exceptional Y₀ Y₁ t I hI A hA
  have hD : (H - pullCart t H₀).supp ≤ E₀.supp := by
    intro y hy
    rw [hsE₀, Scheme.IdealSheafData.support_comap]
    by_contra h
    exact hH₀ y h hy
  obtain ⟨e, he⟩ := GlobalTheory.T.effective_multiple_dominates Y₁ (H - pullCart t H₀) E₀ hE₀ hD
  obtain ⟨c₁, hc₁, hc₁'⟩ :=
    ((hA.eventually_isGenerated_tens_lbPow (isLB_toLB (-H₀))).and (eventually_ge_atTop 1)).exists
  obtain ⟨c₂, hc₂⟩ := hgen.exists
  obtain ⟨P, hP, hPc⟩ := cls_surj (c₂ • CechPic.pull t (cls A hA.isLB) - toPic E₀)
  have gP := hc₂ P hP hPc
  have g₁ := hc₁.pull t
  have gM := AmpleModelPos.isGenerated_tens g₁ (gP.pow e)
  have hA₁L := isLB_tens hL₁.isLB gM.isLB
  have hA₁ : IsAmpleLB (tens L₁ (tens ((tens (toLB (-H₀)) (lbPow A c₁)).pull t) (lbPow P e))) := by
    refine hL₁.tensor_isGenerated gM hA₁L ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB, cls_div hA₁L hL₁.isLB, cls_tens hL₁.isLB gM.isLB]
    abel
  refine ⟨c₁ + e * c₂, e • E₀ - (H - pullCart t H₀), _, hA₁, by omega, he, ?_, ?_⟩
  · rw [sub_eq_add_neg]
    refine (GlobalTheory.Cartier.CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hsE₀.le) ?_)
    exact (supp_neg_le _).trans (hD.trans hsE₀.le)
  · rw [cls_tens hL₁.isLB gM.isLB, cls_tens g₁.isLB (gP.pow e).isLB,
      cls_lbPow hP e, hPc, cls_pull (isLB_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁)) t,
      cls_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁), cls_lbPow hA.isLB c₁, ← toPic_apply,
      map_sub, map_nsmul, map_sub, toPic_pullCart, hH, map_add, map_neg, map_nsmul, add_smul, mul_smul]
    simp only [map_neg, smul_sub]
    abel

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreadingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.kawamata_viehweg_spreading : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  first | exact @_root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | exact _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | (intros; apply _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierOpen
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory.Discrepancy

theorem isOpen_setOf_forall_specializes_of_finite {X Y : Type} [TopologicalSpace X] (s : Y → X)
    (P : Y → Prop) (hP : {w | ¬ P w}.Finite) :
    IsOpen {x : X | ∀ w : Y, s w ⤳ x → P w} := by
  have h : {x : X | ∀ w : Y, s w ⤳ x → P w} = (⋃ w ∈ {w | ¬ P w}, closure {s w})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists,
      ← specializes_iff_mem_closure]
    exact ⟨fun h w hw hx => hw (h w hx), fun h w hx => by_contra fun hw => h w hw hx⟩
  rw [h]
  exact (hP.isClosed_biUnion fun w _ => isClosed_closure).isOpen_compl

theorem isOpen_kltAt_and_lcAt_of_isLogRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro k _ _ X _ _ _ p n hproj hn Δ η m G Y _ _ s _ K B hlm hres
  obtain ⟨N, i, hi, hpi⟩ := hres.proj
  haveI : QuasiCompact (s ≫ p) := hpi ▸ inferInstance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  have hfin := (pullCart s G - m • K).finite_support_mult
  have hm : (0 : ℤ) < m := by exact_mod_cast hlm.pos
  have hiff := kltAt_lcAt_iff_of_isLogRes k X p n hproj hn Δ η m G Y s K B hlm hres
  constructor
  · have : {x : X | KltAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m} := by
      ext x
      exact (hiff x).1
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_lt] at hw
    simp only [Function.mem_support]
    omega
  · have : {x : X | LcAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m} := by
      ext x
      exact (hiff x).2
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hw
    simp only [Function.mem_support]
    omega

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependentStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_independent : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  first | exact @_root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt | exact _root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt | (intros; apply _root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt <;> assumption)
end


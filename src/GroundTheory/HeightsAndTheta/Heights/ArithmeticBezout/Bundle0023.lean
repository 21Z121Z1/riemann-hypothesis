import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ComplexFibreIdealBot
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def complexFibreIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℂ) :=
  (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (MvPolynomial.map (Int.castRingHom ℂ))

def ComplexFibreCycle.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsArithVar P (e + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ f →
      (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, IsProjPrime W) ∧
      IsChowFormCycle (fundCycle (complexFibreIdeal P)) (e + 1) f ∧
      ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.specFirst u f ≠ 0 ↔
        ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)

def blk (n : ℕ) : Fin n → (Σ _ : Unit, PBlk n ()) := fun i => ⟨(), i⟩

def genericIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℚ) :=
  (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (MvPolynomial.map (Int.castRingHom ℚ))

variable {n : ℕ}

theorem rename_linForm (u : Fin n → ℤ) :
    rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u := by
  simp [linForm, IndefiniteRowSideFullHecke.ArithBezout.linForm, map_sum, blk, Xc]

theorem linForm_mem_finIdeal (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) :
    linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P := by
  rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, ← rename_linForm]
  rfl

theorem specFirst_eq {R : Type*} [CommRing R] {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R)
    (u : Fin n → R) : specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f := by
  rw [specFirst, IndefiniteRowSideFullHecke.ArithBezout.specFirst, aeval_eq_bind₁]
  rfl

theorem map_specFirst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {e : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R) :
    map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f) := by
  have h : (fun ij => map φ (specFirstVar u ij)) =
      (specFirstVar (φ ∘ u) : Fin (e + 1) × Fin n → MvPolynomial (Fin e × Fin n) S) := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [specFirstVar]
  rw [← specFirst_eq, ← specFirst_eq, specFirst, specFirst, map_bind₁, h]

theorem weight_groupWeight {k : ℕ} (m : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (groupWeight k n) m = fun i => ∑ j, m (i, j) := by
  funext i
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; exact zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp [groupWeight, Pi.single_apply]

theorem isMultiHomog_iff {R : Type*} [CommSemiring R] {e δ : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) : IsMultiHomog δ f ↔ IsMultihomog f δ := by
  simp only [IsMultiHomog, IsWeightedHomogeneous, IsMultihomog, mem_support_iff, weight_groupWeight,
    funext_iff]

theorem isMultihomog_map_iff {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {e δ : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R) :
    IsMultihomog (map φ f) δ ↔ IsMultihomog f δ := by
  simp only [IsMultihomog, support_map_of_injective _ hφ]

theorem isMultiHomog_of_isChowForm {e δ : ℕ} {P : Ideal (MRing (PBlk n))}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) : IsMultiHomog δ f :=
  (isMultiHomog_iff f).mpr ((isMultihomog_map_iff (Rat.castHom ℂ).injective f).mp hf.1)

theorem isRelevant_finIdeal_iff (W : Ideal (MRing (PBlk n))) :
    IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
  simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap,
    rename_X]
  exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩

theorem isChowFormCycle_iff {F : Type*} [Field F] {k : ℕ} (Z : ProjCycle F n)
    (f : MvPolynomial (Fin k × Fin n) F) :
    IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧ ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
      (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g :=
  Iff.rfl

theorem isChowForm_C_mul {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := (isUnit_iff_ne_zero.mpr hc).map C
  refine ⟨mul_ne_zero (hu.ne_zero) hf.1, fun g => (hf.2 g).trans ?_⟩
  exact (hu.mul_left_dvd).symm

theorem chowDegree_eq {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k δ : ℕ}
    (hk : 0 < k) {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f)
    (hδ : IsMultiHomog δ f) : chowDegree I k = δ := by
  have key : ∀ δ', (∃ g, IsChowForm I k g ∧ IsMultiHomog δ' g) → δ' = δ := by
    rintro δ' ⟨g, hg, hδ'⟩
    obtain ⟨a, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
    obtain ⟨b, hb⟩ : f * a ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
    have hab : a * b = 1 := by
      apply mul_left_cancel₀ hf.1
      rw [mul_one, ← mul_assoc, ← hb]
    obtain ⟨r, hr, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf.1
    have h1 := hδ hd
    have h2 := hδ' (show coeff d (f * C r) ≠ 0 by rw [mul_comm, coeff_C_mul]; exact mul_ne_zero hr.ne_zero hd)
    exact congrFun (h2.symm.trans h1) ⟨0, hk⟩
  exact le_antisymm (Nat.sInf_le ⟨f, hf, hδ⟩) (le_csInf ⟨δ, f, hf, hδ⟩ fun δ' h => (key δ' h).ge)

theorem equiv :
    (∀ (n : ℕ) (u : Fin n → ℤ), rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u) ∧
    (∀ (n : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
      linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P) ∧
    (∀ (R : Type) [CommRing R] (n e : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R)
      (u : Fin n → R), specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) ∧
    (∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n e : ℕ)
      (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R),
      map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f)) ∧
    (∀ (R : Type) [CommSemiring R] (n e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R),
      IsMultiHomog δ f ↔ IsMultihomog f δ) ∧
    (∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f) → IsMultiHomog δ f) ∧
    (∀ (n : ℕ) (W : Ideal (MRing (PBlk n))),
      IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
      IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧
        ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
          (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F) (c : F),
      IsChowForm I k f → c ≠ 0 → IsChowForm I k (C c * f)) ∧
    (∀ (F : Type) [Field F] (n k δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F),
      0 < k → IsChowForm I k f → IsMultiHomog δ f → chowDegree I k = δ) :=
  ⟨fun _ => rename_linForm, fun _ => linForm_mem_finIdeal, fun _ _ _ _ => specFirst_eq,
    fun _ _ _ _ φ _ _ => map_specFirst φ, fun _ _ _ _ _ => isMultiHomog_iff,
    fun _ _ _ _ _ => isMultiHomog_of_isChowForm, fun _ => isRelevant_finIdeal_iff,
    fun _ _ _ _ => isChowFormCycle_iff, fun _ _ _ _ _ _ _ hf hc => isChowForm_C_mul hf hc,
    fun _ _ _ _ _ _ _ hk hf hδ => chowDegree_eq hk hf hδ⟩

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemConePointsSpanX0
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)

open Classical in

def ChowHeightRecQ.Holds (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : Prop :=
  (∀ (δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (0 + 1) × Fin n) ℚ) (u : Fin n → ℤ),
    IsArithVar P (0 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) 0 δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
        IndefiniteRowSideFullHecke.ArithBezout.vertPart P 0 (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
          arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
            (fun _ : Fin 0 => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
  (∀ (e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ)
      (u : Fin n → ℤ) (g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ)
      (d : Ideal (MRing (PBlk n)) → ℕ),
    IsArithVar P (e + 1 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
    (∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W))) →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
        (∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
            (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
              (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W)
                else (geoNum (e + 1) W (fun _ _ => 1) : ℝ) * Real.log (charOf W))) -
          arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
            (fun _ : Fin (e + 1) => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS))

def ChowHeightRecQ.Statement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S), ChowHeightRecQ.Holds n S hS

def ChowFormExistsRat.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P (e + 1) →
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f)

def ChowHeightRecursionRat.Statement : Prop :=
  ∀ (n e δ : ℕ) (H : ArchData ℚ n) (I : Ideal (MvPolynomial (Fin n) ℚ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ) (u : Fin n → 𝓞 ℚ),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
    linForm (fun j => (u j : ℚ)) ∉ I →
      chowHt H (e + 1) δ f =
        chowHt H e δ (specFirst f fun j => (u j : ℚ)) +
          (1 / Module.finrank ℚ ℚ : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : ℚ →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))

def RecQOfRecursion.Statement : Prop :=
  ChowHeightRecursionRat.Statement →
    ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ChowHeightRecQ.Holds n S hS

def RecursionOfRecQ.Statement : Prop :=
  (∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ChowHeightRecQ.Holds n S hS) →
    ChowHeightRecursionRat.Statement

namespace ChowHeightRecQ

end ChowHeightRecQ

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereMeanLinear.full : SphereMeanLinear.Statement := sphereMeanLinear

theorem ChowFormSwap.full : ChowFormSwap.Statement := chowFormSwap

theorem GaussLemma.full : GaussLemma.Statement := gaussLemma

theorem MahlerMul.full : MahlerMul.Statement := mahlerMul

theorem ChowHeightMul.full : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul

theorem ChowHeightConst.full : ChowHeightConst.Statement := chowHeightConst

theorem ConeLogBound.of_leaves (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ConeLogBound.Statement :=
  ConeLogBound.proof hMass hFin hInt hNull

theorem BaseChangeLogBound.of_leaves (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) (hMass : ConeIntegralMass.Statement)
    (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : BaseChangeLogBound.Statement :=
  BaseChangeLogBound.proof hB hAv (ConeLogBound.proof hMass hFin hInt hNull)

theorem ChowHeightRecursion.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) : ChowHeightRecursion.Statement :=
  ChowHeightRecursion.proof hV hA hB hAv

theorem ChowHeightLowerBound.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ChowHeightLowerBound.Statement :=
  chowHeightLowerBound_of (ChowHeightRecursion.proof hV hA hB hAv) hS
    (BaseChangeLogBound.of_leaves hB hAv hMass hFin hInt hNull) ChowHeightMul.full

theorem ChowHeightCharacterised.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hPt : ProjPrimeHasPoint.Statement) : ChowHeightCharacterised.Statement :=
  ChowHeightCharacterised.proof (ChowHeightRecursion.proof hV hA hB hAv) hS ChowHeightMul.full hPt

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInjSet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

theorem AreaFormulaInjSet.proof (h : AreaFormulaLocal.Statement) : AreaFormulaInjSet.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f hU hf hAU hA hinj
  set J : E → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) with hJdef
  change μH[(k : ℝ)] (f '' A) = ∫⁻ x in A, J x ∂(μH[(k : ℝ)])
  have hdiff : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt

  set C : Set E := A ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Function.Injective L}ᶜ with hCdef
  have hCm : MeasurableSet C :=
    hA.inter (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet.compl)
  have hJC : EqOn J (fun _ => 0) C := by
    intro x hx
    have hni : ¬ Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] F) := hx.2
    have h0 : (fderiv ℝ f x : E →ₗ[ℝ] F).normDet = 0 :=
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 fun hk0 => hni (LinearMap.ker_eq_bot.1 hk0)
    simp [hJdef, SheetImageAreaSet.areaJacobian_eq_normDet, h0]
  have hCnull : μH[(k : ℝ)] (f '' C) = 0 := by
    let e : (Fin k → ℝ) ≃L[ℝ] E := (finBasisOfFinrankEq ℝ E hk).equivFun.symm.toContinuousLinearEquiv
    have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
      rw [image_comp, image_preimage_eq _ e.surjective]
    have key := IndefiniteRowSideFullHecke.ComplexSets.hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e)
      (s := e ⁻¹' C) (f' := fun x => (fderiv ℝ f (e x)).comp (e : (Fin k → ℝ) →L[ℝ] E)) ?_ ?_
    · rw [himg]
      simpa using key
    · intro x hx
      exact ((hdiff (e x) (hAU hx.1)).comp x e.hasFDerivAt).hasFDerivWithinAt
    · intro x hx hinj'
      apply hx.2
      intro a c hac
      have h2 := @hinj' (e.symm a) (e.symm c) (by simpa using hac)
      simpa using congrArg e h2

  set R : Set E := A \ C with hRdef
  have hRm : MeasurableSet R := hA.diff hCm
  set G : Set (Set E) := {V | IsOpen V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
    μH[(k : ℝ)] (f '' B) = ∫⁻ x in B, J x ∂(μH[(k : ℝ)])} with hGdef
  have hRG : R ⊆ ⋃₀ G := by
    intro x hx
    have hxinj : Function.Injective (fderiv ℝ f x) := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    obtain ⟨V, hVo, hxV, hVU, hV⟩ := h E F k hk U f x hU hf (hAU hx.1) hxinj
    exact ⟨V, ⟨hVo, hVU, hV⟩, hxV⟩
  obtain ⟨T, hTc, hTG, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable G fun V hV => hV.1
  have hG0 : (∅ : Set E) ∈ G := ⟨isOpen_empty, empty_subset _, fun B hB _ => by
    rw [subset_empty_iff.1 hB]
    simp⟩
  obtain ⟨V, hVeq⟩ := (hTc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hVG : ∀ n, V n ∈ G := by
    intro n
    have hn : V n ∈ insert ∅ T := by
      rw [hVeq]
      exact mem_range_self n
    rcases hn with h0 | hT
    · rw [h0]
      exact hG0
    · exact hTG hT
  have hRV : R ⊆ ⋃ n, V n := by
    intro x hx
    have hx' : x ∈ ⋃₀ T := by
      rw [hTU]
      exact hRG hx
    obtain ⟨W, hWT, hxW⟩ := hx'
    have hW : W ∈ range V := by
      rw [← hVeq]
      exact mem_insert_of_mem _ hWT
    obtain ⟨n, rfl⟩ := hW
    exact mem_iUnion.2 ⟨n, hxW⟩

  set B : ℕ → Set E := fun n => R ∩ disjointed V n with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    hRm.inter (MeasurableSet.disjointed (fun m => (hVG m).1.measurableSet) n)
  have hBd : Pairwise (Function.onFun Disjoint B) := fun m n hmn =>
    ((disjoint_disjointed V) hmn).mono inter_subset_right inter_subset_right
  have hBU : ⋃ n, B n = R := by
    rw [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.2 hRV
  have hBV : ∀ n, B n ⊆ V n := fun n => inter_subset_right.trans (disjointed_subset V n)
  have hBA : ∀ n, B n ⊆ A := fun n => inter_subset_left.trans sdiff_subset
  have hR : μH[(k : ℝ)] (f '' R) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    rw [← hBU, image_iUnion, measure_iUnion, lintegral_iUnion hBm hBd]
    · exact tsum_congr fun n => (hVG n).2.2 (B n) (hBV n) (hBm n)
    · intro m n hmn
      refine disjoint_left.2 ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
      obtain rfl := hinj (hBA n hc) (hBA m ha) hca
      exact disjoint_left.1 (hBd hmn) ha hc
    · intro n
      exact (hBm n).image_of_continuousOn_injOn
        (hf.continuousOn.mono ((hBV n).trans (hVG n).2.1)) (hinj.mono (hBA n))

  have hAC : A = R ∪ C := (sdiff_union_of_subset inter_subset_left).symm
  have himgA : μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R) := by
    apply le_antisymm
    · calc μH[(k : ℝ)] (f '' A) = μH[(k : ℝ)] (f '' R ∪ f '' C) := by
            rw [← image_union, ← hAC]
        _ ≤ μH[(k : ℝ)] (f '' R) + μH[(k : ℝ)] (f '' C) := measure_union_le _ _
        _ = μH[(k : ℝ)] (f '' R) := by rw [hCnull, add_zero]
    · exact measure_mono (image_mono sdiff_subset)
  have hintA : ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
    calc ∫⁻ x in A, J x ∂(μH[(k : ℝ)]) = ∫⁻ x in R ∪ C, J x ∂(μH[(k : ℝ)]) := by rw [← hAC]
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) + ∫⁻ x in C, J x ∂(μH[(k : ℝ)]) :=
          lintegral_union hCm disjoint_sdiff_left
      _ = ∫⁻ x in R, J x ∂(μH[(k : ℝ)]) := by
          rw [setLIntegral_congr_fun hCm hJC, lintegral_zero, add_zero]
  rw [himgA, hR, hintA]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartLengthAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartLengthAlgClosed.proof (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegreeAlgClosed.Statement) :
    ChartLengthAlgClosed.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

end

end GroundTheory.Heights₂.Heights
end


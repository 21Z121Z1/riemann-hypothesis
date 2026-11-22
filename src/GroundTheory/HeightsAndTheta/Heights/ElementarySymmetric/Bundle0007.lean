import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0006
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def DivisionDimOne.Statement : Prop :=
  ∀ (T : ℕ) (X : EmbDatum 1) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L 1), 1 ≤ T →
    ∀ F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) T, IsFil X.A Z.s F (T - 1) →
      ∃ h ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) 1, F = Z.s 0 ^ (T - 1) * h

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionSkodaStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def skodaNormSq {D : ℕ} {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U)
    (s : Fin D → Fin A.n → U → ℂ) (ψ : Fin A.n → U → ℝ) (t : ℝ) (F : Fin A.n → U → ℂ) : ℝ≥0∞ :=
  chartIntegral A fun j x =>
    ENNReal.ofReal (2 ^ D * ‖F j x‖ ^ 2 * (∑ i, ‖s i j x‖ ^ 2) ^ (-t) * Real.exp (-ψ j x))

def DivisionSkodaStep.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D) (j : ℕ) (t : ℝ),
    2 ≤ D → (D : ℝ) - 1 < t → t ≤ j →
    ∀ F ∈ topSections X.A X.L₂ X.L (D + (j + 1)),
      skodaNormSq X.A Z.s (fun a x => φA.φ a x + ((j : ℝ) - t) * fsWeight X.e a x) (t + 1) F < ⊤ →
      ∃ h : Fin D → Fin X.A.n → X.U → ℂ,
        (∀ i, h i ∈ topSections X.A X.L₂ X.L (D + j) ∧
          skodaNormSq X.A Z.s (fun a x => φA.φ a x + ((j : ℝ) - t) * fsWeight X.e a x) t (h i) < ⊤) ∧
        F = ∑ i, Z.s i * h i

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial KaehlerDifferential TensorProduct IsLocalRing

theorem ConormalGenerationGeneric.D_eq_sum_pderiv {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    D ℂ (MvPolynomial (Fin n) ℂ) g = ∑ l, pderiv l g • D ℂ (MvPolynomial (Fin n) ℂ) (X l) := by
  conv_lhs => rw [← (mvPolynomialBasis ℂ (Fin n)).sum_repr (D ℂ _ g)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mvPolynomialBasis_repr_apply]
  congr 1
  rw [← (mvPolynomialBasis ℂ (Fin n)).repr_symm_single_one, mvPolynomialBasis_repr_symm_single, one_smul]

theorem ConormalGenerationGeneric.proof : ConormalGenerationGeneric.Statement :=
  _root_.UpperTheory.Reformulated.B.Qf34.proof

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVanishingCechMultInvariants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem VanishingCechMultInvariants.proof (hPB : PullbackMulMem.Statement)
    (hTA : TorsAvgDescends.Statement) : VanishingCechMultInvariants.Statement := by
  intro P a _ r x hx m hm n q hvan φ hφ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmw : ∀ w : Fin P.g → ℂ, (m : ℂ) • ((m : ℂ)⁻¹ • w) = w := fun w => by
    rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]

  have hprod : ∀ (J : Finset (Fin (r + 1))) u v w,
      ∏ i ∈ J, x i (w + P.latVec u v) = P.autL (a * J.card) u v w * ∏ i ∈ J, x i w := by
    intro J u v w
    rw [Finset.prod_congr rfl (fun i _ => P.thetaSec_add_latVec (P.S_le a _ (hx.1 i)) u v w),
      Finset.prod_mul_distrib, Finset.prod_const, P.autL_mul]
  have hprod0 : ∀ (J : Finset (Fin (r + 1))) w, w ∈ P.chartSet x J → ∏ i ∈ J, x i w ≠ 0 :=
    fun J w hw => Finset.prod_ne_zero_iff.mpr hw
  have hchart : ∀ (J : Finset (Fin (r + 1))) u v w, w ∈ P.chartSet x J →
      w + P.latVec u v ∈ P.chartSet x J := by
    intro J u v w hw i hi
    rw [P.thetaSec_add_latVec (P.S_le a _ (hx.1 i))]
    exact mul_ne_zero (P.autL_ne_zero _ _ _ _) (hw i hi)

  have hφt : ∀ J : Finset (Fin (r + 1)), J.card = q + 2 → ∀ w ∈ P.chartSet x J, ∀ u v,
      φ J (w + P.latVec u v) = P.autL n u v w * φ J w := by
    intro J hJ w hw u v
    obtain ⟨k, f, hf, hfe⟩ := hφ.1 J hJ
    rw [hfe _ (hchart J u v w hw), hfe _ hw, hprod, P.thetaSec_add_latVec (P.S_le _ _ hf),
      P.autL_add, P.autL_mul (a * J.card) k]
    have h1 := P.autL_ne_zero (a * J.card) u v w
    have h2 := hprod0 J w hw
    field_simp
    ring

  have hφ' : P.IsCocycle (a * m ^ 2) (n * m ^ 2) (q + 1) (fun j z => x j ((m : ℂ) • z))
      (fun J z => φ J ((m : ℂ) • z)) := by
    refine ⟨fun J hJ => ?_, fun J hJ z hz => hφ.2 J hJ _ hz⟩
    obtain ⟨k, f, hf, hfe⟩ := hφ.1 J hJ
    refine ⟨k, fun z => f ((m : ℂ) • z), ?_, fun z hz => hfe _ hz⟩
    rw [show n * m ^ 2 + a * m ^ 2 * J.card * k = (n + a * J.card * k) * m ^ 2 by ring]
    exact hPB P m _ f hf
  obtain ⟨ψ', hψ'c, hψ'd⟩ := hvan _ hφ'
  have hpt : ∀ (J : Finset (Fin (r + 1))) (w : Fin P.g → ℂ), w ∈ P.chartSet x J →
      ∀ u v : Fin P.g → Fin m, (m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v) ∈
        P.chartSet (fun j z => x j ((m : ℂ) • z)) J := by
    intro J w hw u v
    show ∀ i ∈ J, x i ((m : ℂ) • ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) ≠ 0
    rw [← smul_add, hmw]
    exact hchart J _ _ w hw

  refine ⟨fun J w => P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w), fun J hJ => ?_, fun J hJ w hw => ?_⟩
  · obtain ⟨k, F, hF, hFe⟩ := hψ'c J hJ
    have hF' : F ∈ P.S ((n + a * J.card * k) * m ^ 2) := by
      rw [show (n + a * J.card * k) * m ^ 2 = n * m ^ 2 + a * m ^ 2 * J.card * k by ring]; exact hF
    obtain ⟨f, hf, hfe⟩ := hTA P m hm _ F hF'
    refine ⟨k, f, hf, fun w hw => ?_⟩
    have hY : ∀ u v : Fin P.g → Fin m,
        (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
          P.autL (a * J.card) (torsIdx u) (torsIdx v) ((m : ℂ) • ((m : ℂ)⁻¹ • w)) *
            (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) := by
      intro u v
      simp only [← smul_add, hmw]
      exact hprod J _ _ w
    have hY0 : (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) ≠ 0 := by
      simp only [hmw]; exact hprod0 J w hw
    have hG : ∀ u v : Fin P.g → Fin m,
        ψ' J ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
          F ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) /
            (fun z => ∏ i ∈ J, x i ((m : ℂ) • z))
              ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) ^ k := by
      intro u v
      exact hFe _ (hpt J w hw u v)
    have key := P.torsAvg_div (n := n) (d := a * J.card) (k := k) (m := m) (F := F) (G := ψ' J)
      (Y := fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) (z := (m : ℂ)⁻¹ • w) hY hY0 hG
    show P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w) = f w / (∏ i ∈ J, x i w) ^ k
    rw [key, hfe]
    simp only [hmw]
  · have h1 : cechD (fun J w => P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w)) J w =
        cechD (fun I => P.torsAvg n m (ψ' I)) J ((m : ℂ)⁻¹ • w) := by
      simp only [cechD]
    have h2 : P.torsAvg n m (cechD ψ' J) ((m : ℂ)⁻¹ • w) =
        P.torsAvg n m (fun z => φ J ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) :=
      P.torsAvg_congr (fun u v => hψ'd J hJ _ (hpt J w hw u v))
    rw [h1, P.torsAvg_cechD, h2]
    exact P.torsAvg_pullback hm (fun u v => hφt J hJ w hw _ _)

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumAdditive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumAdditive.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (i : Fin n)
      (L' L'' : LineBundle k x), IsSubvar x pp n →
      interNum pp (Function.update (fun j => (L j).toSubSystem) i (L'.twist L''.toSubSystem)) =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i L'.toSubSystem) +
          interNum pp (Function.update (fun j => (L j).toSubSystem) i L''.toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumEventual
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumEventual.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x), IsSubvar x pp n →
      ∃ m : ℤ, ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c = m

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumPointDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterNumPointDeg.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar x pp 0 →
      interNum pp (![] : Fin 0 → SubSystem k x Ω) =
        (FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterSumTopVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def InterSumTopVanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x), IsSubvar x pp n →
      ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

open Classical in

def MixedTwistShift.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (qq : Ideal (Poly k N)), qq.IsPrime → (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ringKrullDim (Poly k N ⧸ qq) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → LineBundle k x) (M : LineBundle k x) (d : ℤ), ∀ᶠ c : ℕ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
          restrLen qq (((tensorSub (fun i => (L i).toSubSystem) T).twist M.toSubSystem).twist
            (twistSys k x ((c : ℤ) + d))) =
        if IsSubvar x qq n then interNum qq (fun i => (L i).toSubSystem) else 0

theorem mixedTwistShift_hyps (k : Type u) [Field k] :
    (primeOf (S := k) (genericPt k 1)).IsPrime ∧
      (∀ f ∈ primeOf (S := k) (genericPt k 1), ∀ d : ℕ,
        homogeneousComponent d f ∈ primeOf (S := k) (genericPt k 1)) ∧
      primeOf (S := k) (genericPt k 1) ≤ primeOf (S := k) (genericPt k 1) ∧
      ringKrullDim (Poly k 1 ⧸ primeOf (S := k) (genericPt k 1)) ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      Nonempty (Fin 1 → LineBundle k (genericPt k 1)) :=
  ⟨(isSubvar_genericPt k 1).isPrime, (isSubvar_genericPt k 1).homog, le_rfl,
    (isSubvar_genericPt k 1).dim.le, ⟨![twistBundle k (genericPt k 1) 1]⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end


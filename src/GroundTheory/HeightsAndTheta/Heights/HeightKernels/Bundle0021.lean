import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.RestAssembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem RestTermSharp.ofRestTerms (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₃ : RestTerms.RestTermWellDefined.Statement) (h₄ : RestTerms.SameFactorBound.Statement)
    (h₅ : RestTerms.RestBound.Statement) : RestTermSharp.Statement := by
  have hIdealSum : RestCutIdealSum.Statement := RestCutIdealSum.proof
  have hPsum : RestCutTransportPsum.Statement := RestCutTransportPsum.proof
  have hFlagKills : RestCutFlagKillsIdeal.Statement := RestCutFlagKillsIdeal.proof h₂ hIdealSum
  have hIKills : RestCutIKillsIdeal.Statement := RestCutIKillsIdeal.proof hIdealSum hPsum
  have hStairNonzero : RestCutStairNonzero.Statement := RestCutStairNonzero.proof h₁ hFlagKills
  have hCompare : RestCutCompare.Statement :=
    RestCutCompare.proof h₁ RestCutStairHom.proof hFlagKills hIKills
  have hCaseCompare : RestCutCaseCompare.Statement :=
    RestCutCaseCompare.proof h₄ RestCutRestHom.proof hStairNonzero hCompare RestCutCompareReal.proof
  have hPsiFlag : RestCutPsiFlag.Statement := RestCutPsiFlag.proof
  have hSyzygy : RestCutRealSyzygy.Statement := RestCutRealSyzygy.proof h₃ hPsiFlag
  have hTermEq : RestCutTermEq.Statement := RestCutTermEq.proof hSyzygy hPsiFlag hPsum
  have hCaseDecomp : RestCutCaseDecomp.Statement :=
    RestCutCaseDecomp.proof RestCutRestHom.proof RestCutHomDecomp.proof hPsum
  have hCaseSharp : RestCutCaseSharp.Statement :=
    RestCutCaseSharp.proof h₅ hCaseCompare hCaseDecomp hTermEq RestCutPrimeEq.proof
  exact RestTermSharp.proof hCaseSharp RestCutTransportLast.proof RestCutTransportFirst.proof
    RestCutLieLast.proof RestCutLieFirst.proof

theorem RestTerm.ofRestTerms (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₃ : RestTerms.RestTermWellDefined.Statement) (h₄ : RestTerms.SameFactorBound.Statement)
    (h₅ : RestTerms.RestBound.Statement) : RestTerm.Statement :=
  RestTerm.proof (RestTermSharp.ofRestTerms h₁ h₂ h₃ h₄ h₅)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def GrassGeomDegChart.Statement : Prop :=
  ∀ n : ℕ, ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
    geomDeg (grassIdeal 1 1 n) (fsMulti (plBlocks 1 1 n)) n = chartMass (Bᴴ * B)

example : Ideal (MRing (plBlocks 1 1 2)) × HermLine (plBlocks 1 1 2) :=
  ⟨grassIdeal 1 1 2, fsMulti (plBlocks 1 1 2)⟩

example (n : ℕ) : Fintype.card (PlIdx 1 n) = n + 1 := by
  simp [PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

theorem rootCoord_mem {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    rootCoord ζ ∈ mcPts (rootPointIdeal ζ) := by
  refine ⟨fun k => ⟨plAnchor j m, ?_⟩, fun g hg => ?_⟩
  · simp [rootCoord, anchor_minor]
  · have h : mConeMap (rootCoord ζ) g = 0 := hg
    have h2 := congrArg (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))) h
    have key : (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))).comp
        (mConeMap (rootCoord ζ) : MRing (plBlocks f j m) →+* MvPolynomial (Fin f) ℂ) =
        (eval (rootCoord ζ)).comp (map (Int.castRingHom ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp [mConeMap]
    have := congrArg (fun φ => φ g) key
    simp only [RingHom.comp_apply, RingHom.coe_coe, h, map_zero] at this
    exact this.symm

example : IsMultiHomogIdeal (⊥ : Ideal (MRing (fun _ : Unit => Unit))) :=
  ⟨∅, by simp, by simp⟩

theorem finite_mcClasses_bot_unit : Finite (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
  haveI : Subsingleton (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
    constructor
    intro x y
    induction x using Quot.ind with | mk z => ?_
    induction y using Quot.ind with | mk z' => ?_
    apply Quot.sound
    obtain ⟨⟨⟩, hz⟩ := z.2.1 ()
    obtain ⟨⟨⟩, hz'⟩ := z'.2.1 ()
    refine ⟨fun _ => z'.1 ⟨(), ()⟩ / z.1 ⟨(), ()⟩, fun _ => div_ne_zero hz' hz, ?_⟩
    funext p
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    field_simp
  exact Finite.of_subsingleton

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassLinesProj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GrassLinesProj.Statement : Prop :=
  ∀ (m : ℕ) (II : IntersectionSystem), IsIntersectionSystem II →
    II (Fin 1) (plBlocks 1 1 m) (grassIdeal 1 1 m) (1 * 1 * m + 1) (fun _ => fsMulti (plBlocks 1 1 m)) =
      II Unit (PBlk (m + 1)) ⊥ (m + 1) (fun _ => fsMulti (PBlk (m + 1)))

example (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, Nat.choose_one_right, add_comm]

example : (Ideal (MRing (plBlocks 1 1 1)) × HermLine (plBlocks 1 1 1)) ×
    (Ideal (MRing (PBlk 2)) × HermLine (PBlk 2)) :=
  ⟨⟨grassIdeal 1 1 1, fsMulti (plBlocks 1 1 1)⟩, ⟨⊥, fsMulti (PBlk 2)⟩⟩

end

end GroundTheory.Heights₂.Heights
end


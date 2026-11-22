import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalRingCardinality.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPinT
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapHarmonicOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdaptedVectorSystemECoZCo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramesStd

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames GlobalTheory.NormalFramesLevels

variable {D : D7}

def eCo (E : ∀ j, ℕ → (D.sp.Y j).V) (j i : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (E j i))

def zCo (z : ∀ j, (D.sp.Y j).V) (j : ℕ) : Fin (D.sp.Y j).rank → D.host.E := ⇑((D.sp.Y j).frame.repr (z j))

theorem normalFr_repr' (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V) {j : ℕ} (hj : j < D.R.m) {i : ℕ}
    (hi : i < D.R.m - 1 - j) (r : Fin (D.sp.Y j).rank) :
    (D.sp.Y j).frame.repr (normalFr D j (E j) (Ev j) (z j) i) r =
      nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r := by
  have hpar := even_iff_odd_c hj
  have hb : 0 < bI D j := by unfold bI; omega
  rw [nfScal_kap j hb i]
  unfold normalFr adaptedVector nAux
  by_cases h1 : i < (D.R.m - 1 - j) / 2
  · have hb' : ¬ bI D j ≤ i := by unfold bI; omega
    simp only [if_pos h1, if_neg hb', one_mul]
    rfl
  · by_cases h2 : Even j ∧ i = (D.R.m - 1 - j) / 2
    · have hc : (D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2 := ⟨hpar.1 h2.1, h2.2⟩
      have hb' : ¬ bI D j ≤ i := by unfold bI; omega
      simp only [if_neg h1, if_pos h2, if_pos hc, if_neg hb', one_mul]
      rfl
    · have h3 : ¬ ((D.R.m - 1 - j) % 2 = 1 ∧ i = (D.R.m - 1 - j) / 2) := fun h => h2 ⟨hpar.2 h.1, h.2⟩
      have hb' : bI D j ≤ i := by
        unfold bI
        by_cases hc : (D.R.m - 1 - j) % 2 = 1
        · have : i ≠ (D.R.m - 1 - j) / 2 := fun h => h3 ⟨hc, h⟩
          omega
        · omega
      simp only [if_neg h1, if_neg h2, if_neg h3, if_pos hb', map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl

theorem normalFr_zero_repr' (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    (hE0 : ∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩) (hz0 : z 0 = D.sp.zm)
    {i : ℕ} (hi : i < D.R.m - 1) :
    ⇑((D.sp.Y 0).frame.repr (normalFr D 0 (E 0) (Ev 0) (z 0) i)) = frame0 (D := D) i := by
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hρ : nAux D 0 / 2 = D.R.rS := by unfold nAux Ranks.rS; omega
  unfold normalFr frame0
  rw [hρ]
  by_cases h1 : i < D.R.rS
  · rw [if_pos h1, dif_pos h1, (hE0 i h1).1]
  · rw [if_neg h1, dif_neg h1]
    by_cases h3 : i = D.R.rS
    · rw [if_pos ⟨(Nat.even_iff.2 rfl : Even 0), h3⟩, if_pos h3, hz0]
    · rw [if_neg (fun h => h3 h.2), if_neg h3, if_pos (Nat.even_iff.2 rfl : Even 0)]
      have h5 : 2 * D.R.rS - i < D.R.rS := by unfold Ranks.rS at *; omega
      have h6 : nAux D 0 - 1 - i = 2 * D.R.rS - i := by unfold nAux Ranks.rS at *; omega
      rw [dif_pos h5, h6, (hE0 _ h5).2]

theorem isAdaptedVectorSystem_eCo_zCo (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    (hAux : ∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)) : IsAdaptedVectorSystem (eCo E) (eCo Ev) (zCo z) := by
  intro j hj
  obtain ⟨hA, hB, hC⟩ := hAux j hj
  have hpar := even_iff_odd_c hj
  simp only [nAux] at hA hB hC
  simp only [eCo, zCo, Formalism.IndefR.Seed.Frm.vecY_repr]
  refine ⟨fun i hi l hl => ⟨?_, ?_, ?_⟩, fun hc => ?_, fun x i' hi' => ?_⟩
  · refine hT_swap _ _ (hA i hi l hl).2.2 ?_
    split_ifs <;> simp
  · exact (hA l hl i hi).1
  · exact (hA l hl i hi).2.1
  · obtain ⟨h1, -, h3⟩ := hC (hpar.2 hc)
    exact ⟨h1, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2⟩⟩
  · unfold adaptedVector
    split_ifs with h1 h2
    · simp only [eCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      exact (hB _ h1 x).1
    · simp only [zCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      exact (hC (hpar.2 h2.1)).2.1 x
    · simp only [eCo, Formalism.IndefR.Seed.Frm.vecY_repr]
      refine (hB _ ?_ x).2
      by_cases hc : (D.R.m - 1 - j) % 2 = 1
      · have : i' ≠ (D.R.m - 1 - j) / 2 := fun h => h2 ⟨hc, h⟩
        omega
      · omega

end GlobalTheory.NormalFramesStd

namespace GlobalTheory.NormalFramesStd

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.StdFrames GlobalTheory.NormalFramesLevels

variable {D : D7}

theorem colsAt' (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Ef D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V)
    {j : ℕ} (hj : j < D.R.m) (β : GL (Fin (D.sp.Y j).rank) (EAf D)) (P : Formalism.L2.Host.PiBar D.host)
    {l : Fin 2} {PP : Pl D.host.E} (hl : P.Div l PP)
    (hA : AgreeAt PP β.val (chainMat D j (γ j) (E j) (Ev j) (z j) (D.host.g l)))
    {ei : AE D} (hei : Formalism.L2.NTheta.IsIdemAt ei PP) :
    (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i → ∀ r,
      toEAf D ei * β.val r col = toEAf D ei * eToEAf D (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) *
        (nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r))) ∧
    ∀ (col : Fin (D.sp.Y j).rank) (l' : Fin (D.sp.X j).rank), IsXCol (D := D) j col l' → ∀ r,
      toEAf D ei * β.val r col = toEAf D ei * (xMat (D := D) j).mulVec (fun i => (γ j).val i l') r := by
  refine ⟨fun i hi col hcol r => ?_, fun col l' hcl r => ?_⟩
  · rw [agree_all hA hei r col]
    simp only [chainMat]
    rw [if_neg (by omega), if_pos (by unfold nAux; omega), absNorm_of_div P hl,
      show (col : ℕ) - D.R.k = i by omega, normalFr_repr' E Ev z hj hi r]
  · rw [agree_all hA hei r col]
    simp only [chainMat]
    rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hl' : l' = ⟨col, (idx_lt hj col).1 h1⟩ := Fin.ext h2
      subst hl'
      rw [if_pos h1, colX_eq j _ col ((idx_lt hj col).1 h1)]
    · have h3 : ¬ (col : ℕ) < D.R.k := by omega
      have h4 : ¬ (col : ℕ) < D.R.k + nAux D j := by unfold nAux; omega
      have hl' : l' = ⟨(col : ℕ) - nAux D j, (idx_lt hj col).2 h4⟩ := Fin.ext (by simp only [nAux]; omega)
      subst hl'
      rw [if_neg h3, if_neg h4, colX_eq j _ _ ((idx_lt hj col).2 h4)]

theorem normalFrames_of_stdShape : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) → ∀ (γ : ∀ j, GL (Fin (D.sp.X j).rank) (Formalism.IndefR.Lev.EAf D)) (E Ev : ∀ j, ℕ → (D.sp.Y j).V) (z : ∀ j, (D.sp.Y j).V), (∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0)) → (∀ j, j < D.R.m → GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)) → (∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩) → z 0 = D.sp.zm → GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.StdShape L γ E Ev z → (∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z' : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E) (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E), NormalFrames (betaYOf L.βY) e ev z' κ s L.Pg L.Pg ∧ NormalFrame0 (betaYOf L.βY 0) L.Pg L.Pg) ∧ XBasesG L.Pg L.βY := by
  intro D T L hPg γ E Ev z hγ hAux hE0 hz0 hSh
  have hshape : ∀ j < D.R.m, ShapeY L j (γ j) (E j) (Ev j) (z j) (betaYOf L.βY j) := fun j hj =>
    shape_betaYOf L γ E Ev z L.βY j hj.le (hSh.1 j hj (hAux _ (lt_of_le_of_lt (min_le_left _ _) hj)))
  have hcols : ∀ j (hj : j < D.R.m), ∀ PP ∈ L.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      (∀ i < D.R.m - 1 - j, ∀ col : Fin (D.sp.Y j).rank, col.val = D.R.k + i → ∀ r,
        toEAf D ei * (betaYOf L.βY j).val r col =
          toEAf D ei * eToEAf D (((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) *
            (nfScal (kap D) (fun _ => 1) j i * adaptedVector (eCo E) (eCo Ev) (zCo z) j i r))) ∧
      ∀ (col : Fin (D.sp.Y j).rank) (l' : Fin (D.sp.X j).rank), IsXCol (D := D) j col l' → ∀ r,
        toEAf D ei * (betaYOf L.βY j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => (γ j).val i l') r := by
    intro j hj PP hPP ei hei
    obtain ⟨l, hl⟩ := (hPg PP).1 hPP
    exact colsAt' γ E Ev z hj _ L.C.P hl ((hshape j hj).1 l PP hl) hei
  have hxspan : ∀ j (hj : j < D.R.m), ∀ PP ∈ L.Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ col : Fin (D.sp.Y j).rank, (col.val < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ col.val) →
        XSpanAt j (betaYOf L.βY j).val ei col := by
    intro j hj PP hPP ei hei col hcol
    have hc := (hcols j hj PP hPP ei hei).2
    rcases hcol with h | h
    · exact ⟨_, hc col ⟨col, (idx_lt hj col).1 h⟩ (Or.inl ⟨h, rfl⟩)⟩
    · exact ⟨_, hc col ⟨(col : ℕ) - (D.R.m - 1 - j), (idx_lt hj col).2 (by unfold nAux; omega)⟩ (Or.inr ⟨h, rfl⟩)⟩
  have h0m : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  refine ⟨⟨eCo E, eCo Ev, zCo z, kap D, fun _ => 1,
    ⟨isAdaptedVectorSystem_eCo_zCo E Ev z hAux, kap_ne, fun _ => one_ne_zero, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro PP hPP j _ i hi
    obtain ⟨l, hl⟩ := (hPg PP).1 hPP
    have hb : 0 < bI D j := by unfold bI; omega
    rw [nfScal_kap j hb i]
    split_ifs
    · unfold sgT
      split_ifs
      · rw [Valuation.map_neg, valuation_splitTraceElement_eq_one L.C.P hl]
      · exact valuation_splitTraceElement_eq_one L.C.P hl
    · exact map_one _
  · intro PP hPP ei hei j hj
    refine ⟨fun i hi col hcol r => ?_, hxspan j hj PP hPP ei hei⟩
    rw [if_pos hPP]
    exact (hcols j hj PP hPP ei hei).1 i hi col hcol r
  · intro PP hPP ei hei
    have hc := (hcols 0 h0m PP hPP ei hei).1
    refine ⟨fun i hi col hcol r => ?_, fun col hcol => hxspan 0 h0m PP hPP ei hei col
      (Or.inl (by rw [← Formalism.IndefR.Seed.FrmC.N_zero D]; exact hcol))⟩
    have hi' : i < D.R.m - 1 - 0 := by omega
    rw [if_pos hPP, hc i hi' col (by rw [hcol, Formalism.IndefR.Seed.FrmC.N_zero]) r, ← normalFr_repr' E Ev z h0m hi' r,
      normalFr_zero_repr' E Ev z hE0 hz0 hi]
  · intro j hj
    refine ⟨γ j, by rw [← crdLat_eq_l0X]; exact hγ j hj, fun PP hPP ei hei col l' hcl r => ?_⟩
    exact (hcols j hj PP hPP ei hei).2 col l' hcl r

end GlobalTheory.NormalFramesStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc GlobalTheory.Unf.FB GlobalTheory.Unf.FB.ThLaws

noncomputable section

namespace GlobalTheory.Unf.FB.ThLawsL

variable {D : D7}

theorem zEll_rat {σ : ℕ} (B : BesL D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zEll B.L (σ + 1) B.ζ = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → Continuous (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖(fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (γ * n) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ c, ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zEll B.L (σ + 1) B.ζ))) * (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (n * J.d.levi u) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zEll B.L (σ + 1) B.ζ) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n) =
      star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) * y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) = fun n =>
        star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) * y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · show ‖star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)‖ ≤ M
    rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zEll_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (γ * n) y 0) * star (psiFlag ψ J.d (γ * n)) =
      star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nC c * n) y 0) * star (psiFlag ψ J.d (J.d.nC c * n)) =
      _ * (star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n))
    rw [(hmul _ hc n hn).2.2, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (n * J.d.levi u) y 0) * star (psiFlag ψ J.d (n * J.d.levi u)) =
      star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n) * _
    rw [hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b) = zEll B.L (σ + 1) B.ζ ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zEll B.L (σ + 1) B.ζ) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b * J.d.levi u) y 0) * star (psiFlag ψ J.d (J.d.nB b * J.d.levi u)) = _
    rw [hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLawsL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFourthStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_adoption_fourth : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S) (_ : RealPins B.Q) (_ : RealRec B.Q), NChTie D ex.nch → DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → GlobalTheory.ExportPin.ClassSumPinT B.Q → NMjT B.Q B.Q.cG B.Q.Sx B.Q.nexp ex.nch := by
  first | exact @GlobalTheory.BigTop.PtAt.nmjT_at_tied | exact GlobalTheory.BigTop.PtAt.nmjT_at_tied | (intros; apply GlobalTheory.BigTop.PtAt.nmjT_at_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.LevelInLatStab

theorem mulVec_mem_of_integral {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B)
    (β : GL (Fin n) B) {P : AddSubgroup (Fin n → A)}
    (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S) (m : Matrix (Fin n) (Fin n) A)
    (T : Matrix (Fin n) (Fin n) S) (hm : m.map e = β.val * T.map S.subtype * (β⁻¹).val) :
    ∀ z ∈ P, m *ᵥ z ∈ P := by
  intro z hz
  rw [hP] at hz ⊢
  intro i
  rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (T i j).2 (hz j)

theorem lev_le_latLev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  intro D V β Λ L hβ x hx
  have hp := Formalism.L2.DIV.lev_le_parLev hx
  have hUA := Formalism.L2.DIV.parLev_UA hp
  have hSt := Formalism.L2.DIV.parLev_St hp
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
  obtain ⟨t, ht⟩ := hSt
  let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
  let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
  have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
    simp only [g, MulEquiv.apply_symm_apply, u]
  have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
    have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
    rw [← hg]
    exact h1.symm
  refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
  refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
  constructor
  · intro hy
    exact mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
      (by rw [hmat, ← ht]; rfl) y hy
  · intro hy
    let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
    have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
      ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
    have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
      apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
      have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
        (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
      have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
      refine (e.trans ?_).trans e1.symm
      change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
      rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
      (by rw [hm', ← ht']; rfl) _ hy
    rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LevelInLatStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviFactorScalarsAutomorphicCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviFactor_scalars_automorphicCharacters : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∃ (μa : GL (Fin r) (AE D) →* Circle) (ξ : GA D V' →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharGL r μa ∧ GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharU V' ξ ∧ ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) = ((μa a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * (ξ g' : ℂ)) • ω' (g', 1) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  first | exact @GlobalTheory.LeviChar.levi_scalars_autChar | exact GlobalTheory.LeviChar.levi_scalars_autChar | (intros; apply GlobalTheory.LeviChar.levi_scalars_autChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebrasAtPlace_act_fockVectors_by_fockOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ aS aT : ℚ, HasInfExp D χS τ aS → HasInfExp D χT τ aT → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → LieAt ψ θ τ ω εS frS εT frT aS aT (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) := by
  first | exact @GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt | exact GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt | (intros; apply GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKTypeFockMap_exists_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoEx D := by
  first | exact @GlobalTheory.ArchRec.IoMap.ioEx_of_discreteSeriesCover | exact GlobalTheory.ArchRec.IoMap.ioEx_of_discreteSeriesCover | (intros; apply GlobalTheory.ArchRec.IoMap.ioEx_of_discreteSeriesCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapHarmonicOfDiscreteSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKTypeFockMap_harmonic_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoHarm D := by
  first | exact @GlobalTheory.ArchRec.IoHarmPf.ioHarm | exact GlobalTheory.ArchRec.IoHarmPf.ioHarm | (intros; apply GlobalTheory.ArchRec.IoHarmPf.ioHarm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherInstanceCharacter_eq_conjInstancePsiValue_integral : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  first | exact @GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | exact GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | (intros; apply GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelIndicatorThetaFockLatticeVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  first | exact @GlobalTheory.IndVac.indL_theta_fock_latVac | exact GlobalTheory.IndVac.indL_theta_fock_latVac | (intros; apply GlobalTheory.IndVac.indL_theta_fock_latVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighestStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  first | exact @GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | exact GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | (intros; apply GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest <;> assumption)
end


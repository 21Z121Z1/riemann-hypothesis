import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0883
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProduct
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

variable {E : Type} [Field E] [NumberField E]

theorem one_lt_v_zpow {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E} (h : IsUnifV E v ϖ) {a : ℤ}
    (ha : a < 0) : 1 < Valued.v (ϖ ^ a) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -((n + 1 : ℕ) : ℤ) := ⟨(-a - 1).toNat, by omega⟩
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at h
  have h1 : Valued.v ϖ < 1 := by
    rw [h]; exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1)
  rw [zpow_neg, zpow_natCast, map_inv₀, map_pow]
  have hp : Valued.v ϖ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' h1 (Nat.succ_ne_zero n)
  have hp0 : Valued.v ϖ ^ (n + 1) ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 h0)
  exact (one_lt_inv₀ (zero_lt_iff.2 hp0)).2 hp

end GlobalTheory.CellLastRow

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

theorem indN_lastRow_tl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) S), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
    ((∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) =
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))) ∧
    ((∃ w, l.1 w (Fin.last m) < 0) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0) := by
  intro E _ _ _ m S ϖ hϖ N hlat hloc l g hg
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hk' : ∀ v ∉ S, compV E (m + 1) v k ∈ GlobalTheory.LFun.KGL v (m + 1) := by
    simpa only [US, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  set c : (Af E)ˣ := adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) with hc
  have hev : ∀ (x : Af E) v, x v = pLoc E v x := fun _ _ => rfl
  have hcv : ∀ v, pLoc E v (c : Af E) = ((ϖ v ^ l.1 v (Fin.last m) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    intro v
    change ((ϖ v ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) v :
      (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply]
  have hrow : ∀ i, lastRow (u * k) i = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i := by
    intro i
    have := congrFun (GlobalTheory.RSLocalPart.single_vecMul_unip (ℓ := Fin.last m) (fun j => Fin.le_last j) hu k) i
    simpa [lastRow, Units.val_mul, Matrix.single_one_vecMul] using this
  have hrow' : ∀ i, GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) =
      (c : Af E) * GlobalTheory.RSJ.pFin E (lastRow (u * k) i) := by
    intro i
    simp only [lastRow, tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, map_mul]
    congr 1
    change GlobalTheory.RSJ.pFin E (1 - sFin E 1 + sFin E (c : Af E)) = _
    rw [map_add, map_sub, map_one]
    change 1 - 1 + (c : Af E) = _
    ring
  have hcomp : ∀ v i, pLoc E v (GlobalTheory.RSJ.pFin E (lastRow (u * k) i)) = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i; rw [hrow]; rfl
  have hint : ∀ v ∉ S, ∀ i j, (compV E (m + 1) v k).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0]
    exact (k0.val i j).2
  have hinv : ∀ v ∉ S, ∀ i j, ((compV E (m + 1) v k)⁻¹).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0, ← map_inv]
    exact ((k0⁻¹).val i j).2
  have hδ : ∀ v (i : Fin (m + 1)), pLoc E v (if (i : ℕ) + 1 = m + 1 then (1 : Af E) else 0) ∈ v.adicCompletionIntegers E := by
    intro v i
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  refine ⟨fun hpos => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have key : ∀ i : Fin (m + 1),
        (GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
          GlobalTheory.RSJ.natLat E N ↔
        GlobalTheory.RSJ.pFin E (lastRow (u * k) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) := by
      intro i
      refine (hloc _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)).symm
      · rw [hev, hev, map_sub, map_sub, hrow', map_mul, hcv, l.2 v hv]
        simp
      · rw [hev, map_sub, hcomp]
        exact sub_mem (hint v hv _ _) (hδ v i)
      · rw [hev, map_sub, hrow', map_mul, hcomp, hcv]
        refine sub_mem (mul_mem ?_ (hint v hv _ _)) (hδ v i)
        rw [Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg (hpos v), zpow_natCast]
        exact pow_mem (GlobalTheory.LFun.mem_Ov_of_isUnifV (hϖ v)) _
    unfold GlobalTheory.RSJ.indN
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun i => (key i).1 (h1 i)) h2
    · exact absurd (fun i => (key i).2 (h2 i)) h1
    · rfl
  · have hwS : w ∉ S := fun h => by
      have h0 := l.2 w h
      rw [h0] at hw
      exact lt_irrefl _ hw
    have hex : ∃ j, ¬ Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) < 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : ((compV E (m + 1) w k).val * ((compV E (m + 1) w k)⁻¹).val) (Fin.last m) (Fin.last m) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at h1
      have h2 : Valued.v (∑ j, (compV E (m + 1) w k).val (Fin.last m) j * ((compV E (m + 1) w k)⁻¹).val j (Fin.last m)) < 1 := by
        refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hcon j) (hinv w hwS j (Fin.last m))
      rw [h1, map_one] at h2
      exact lt_irrefl _ h2
    obtain ⟨j, hj⟩ := hex
    have hj1 : Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) = 1 :=
      le_antisymm (hint w hwS _ _) (not_lt.1 hj)
    unfold GlobalTheory.RSJ.indN
    rw [if_neg]
    intro hall
    have hz := hlat _ (hall j) w
    dsimp only at hz
    rw [hev, map_sub, hrow', map_mul, hcomp, hcv] at hz
    have ha := add_mem hz (hδ w j)
    rw [sub_add_cancel, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hj1, mul_one,
      Units.val_zpow_eq_zpow_val] at ha
    exact not_le.2 (one_lt_v_zpow (hϖ w) hw) ha

end GlobalTheory.CellLastRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIffStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  first | exact @GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff | exact GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff | (intros; apply GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponentStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  first | exact @GlobalTheory.CellDec.lastRow_sub_notMem_latt | exact GlobalTheory.CellDec.lastRow_sub_notMem_latt | (intros; apply GlobalTheory.CellDec.lastRow_sub_notMem_latt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRow
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

open Matrix

theorem decomp_lastRow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), ∃ p ∈ GlobalTheory.JSW.mirS E S m, ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
      g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ := by
  intro E _ _ _ m S J hJ N hN Φ hs g hg hΦ hind
  have hrow : ∀ h : GA E (m + 1), Pi.single (Fin.last m) 1 ᵥ* h.val = fun j => GlobalTheory.ZEul.lastRow h j := fun h => by
    rw [Matrix.single_one_vecMul]; rfl
  have hℓ : ∀ i : Fin (m + 1), i ≤ Fin.last m := Fin.le_last
  have hi : (fun i => pInf E ((Pi.single (Fin.last m) 1 ᵥ* g.val) i)) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs (subset_tsupport _ hΦ)
  have hind' : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
      GlobalTheory.RSJ.natLat E N := by
    by_contra hc
    exact hind (by rw [GlobalTheory.RSJ.indN, if_neg hc])
  have hf : ∀ v ∈ S, ∀ j, Valued.v ((pFin E ((Pi.single (Fin.last m) 1 ᵥ* g.val) j) -
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow]
    have e : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [Pi.single_apply]
      congr 1
      simp [Fin.ext_iff]
    rw [e]
    exact hN _ (hind' j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp hℓ hJ hg hi hf
  refine ⟨u, (GlobalTheory.SmGL.mem_unipB _).1 hu, p, ⟨hp.2, hp.1⟩, κ, hκ, ?_⟩
  rw [← e, hrow]
  congr 1
  rw [hrow] at hi
  have hu' := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hi
  rw [← map_inv]
  congr 1
  have hm : GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      GlobalTheory.RSTheta.rowMat (Fin.last m) (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    congr 1
    simp [Fin.ext_iff]
  have hd : IsUnit (GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i))).det := by
    rw [hm, GlobalTheory.RSTheta.det_rowMat]; exact hu'
  rw [GlobalTheory.RSJ.secInv, dif_pos hd]
  congr 1
  exact Units.ext (hm.trans (GlobalTheory.RSTheta.val_rowGL hu').symm)

end GlobalTheory.ZEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittakerStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  first | exact @GlobalTheory.ZUnf.zint_unfold | exact GlobalTheory.ZUnf.zint_unfold | (intros; apply GlobalTheory.ZUnf.zint_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEulLocal

theorem wtS_eq_sum (n : ℕ) (a : Fin n → ℤ) :
    GlobalTheory.CellDec.wtS n a = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * a i := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i < j then a i - a j else 0) =
      (∑ j : Fin n, if i < j then a i else 0) - ∑ j : Fin n, if i < j then a j else 0 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [GlobalTheory.CellDec.wtS, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
    Finset.sum_comm (f := fun i j => if i < j then a j else 0)]
  simp only [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Finset.sum_const,
    Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

open GlobalTheory.JSW in

theorem localTerm_eq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  intro q hq n α β x v h0 hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (fun i => (v i).toNat) := fun i j hij => Int.toNat_le_toNat (hv hij)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
    simp
  set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ) := by
    rw [hcR]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcast i, Complex.ofReal_intCast]
  set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'
  have hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ) := by
    rw [hA', Complex.ofReal_cpow hqR.le]
    push_cast
    rfl
  have hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR := by
    rw [GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]
    push_cast
    rfl
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1 := by
    rw [hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]
    rw [show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul,
    Complex.conj_ofReal]
  calc _ = (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) : ℝ) : ℂ) *
        (schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
          ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)) := by push_cast; ring
    _ = _ := by rw [key]; simp

end GlobalTheory.ZEulLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSq
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RSCell

theorem wtS_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  first
  | exact @_root_.GlobalTheory.WeightSumSplit.wtS_eq
  | exact _root_.GlobalTheory.WeightSumSplit.wtS_eq
  | (apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSumSplit.wtS_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSumSplit.wtS_eq ..)

theorem locFac_eq_wtS_sphZ : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  intro q hq n α x ν hlast
  by_cases hA : Antitone ν
  · have hnn : ∀ i, 0 ≤ ν i := fun i => le_trans hlast (hA (Fin.le_last i))
    have hAn : Antitone (fun i => (ν i).toNat) := fun i j h => Int.toNat_le_toNat (hA h)
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hA, hnn⟩, GlobalTheory.RSCell.sphZ, if_pos hA, GlobalTheory.JSW.sphW, if_pos hAn]
    set s := GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α
    set w : ℤ := GlobalTheory.CellDec.wtS (n + 1) ν with hw
    have hc : (∑ i : Fin (n + 1), ((((n + 1 : ℕ)) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) * (((ν i).toNat : ℕ) : ℂ)) = ((w : ℤ) : ℂ) := by
      rw [hw, wtS_eq_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (((ν i).toNat : ℕ) : ℂ) = ((ν i : ℤ) : ℂ) by exact_mod_cast Int.toNat_of_nonneg (hnn i)]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum : (((∑ i, (ν i).toNat : ℕ)) : ℝ) = ∑ i, (ν i : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact_mod_cast Int.toNat_of_nonneg (hnn i)
    rw [hc, hsum]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (zpow_nonneg hq'.le _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq]
    have hre : (-((w : ℂ)) / 2).re = -(w : ℝ) / 2 := by simp
    rw [hre, mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-(w : ℝ) / 2)), ← Real.rpow_mul hq'.le,
      ← Real.rpow_intCast]
    have h1 : (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 := by
      rw [← Real.rpow_add hq']
      norm_num
    calc (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x)) *
          ((q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) * ‖s‖ ^ 2)
        = ((q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ))) * (‖s‖ ^ 2 * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [GlobalTheory.RSCell.locFac, if_neg (fun h => hA h.1), GlobalTheory.RSCell.sphZ, if_neg hA]
    simp

end GlobalTheory.RSCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProductStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∀ F : GA E a → ℂ, Continuous F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → (∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) → Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
  first | exact @GlobalTheory.RSThetaRes.residue_geometric | exact GlobalTheory.RSThetaRes.residue_geometric | (intros; apply GlobalTheory.RSThetaRes.residue_geometric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodModulus

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem goodMod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, GoodMod R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_local_preimage_of_supportedAtPlace D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := GlobalTheory.T.weilDatumCharacters_unramified_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, hφ, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  have hmod := GlobalTheory.T.sphericalKernel_normSq_mul_latticeIndex_eq_one D (Wc D i) (Vc D i).rank _ v φ hφ (fun w h => (hunr w h).1) a
  have h1 := hc a (R.vP i t) (R.vP i t) hvac hvac
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  have hne' : GlobalTheory.AdelicScalar.l2 μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 := by
    intro h; apply hne; rw [thetaInner_eq_star_l2, h, star_zero]
  have e : coef R i t μ 𝓕 (GlobalTheory.FinZeta.embV (Wc D i) v a) = star (φ a) := by
    unfold coef
    rw [thetaInner_eq_star_l2, thetaInner_eq_star_l2, h1, star_mul', mul_div_assoc, div_self (star_ne_zero.2 hne'), mul_one]
  rw [e, norm_star]
  exact hmod

end GlobalTheory.RawLift.GoodModulus

end
end


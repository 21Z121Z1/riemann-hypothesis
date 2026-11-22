import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.InertiaEigenvalues.theoremT_all_records :
    GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal →
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  intro hBS hFon hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine (GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices hBS) hFon C hC D HW F (GlobalTheory.T.localLifting_admittedHypotheses_all hBK hTD hEC D HW F Cm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseAStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineUniversalPart_caseA : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D → UnusedSlot80.UniversalComponentCaseA D HW F Cm := by
  first | exact @GlobalTheory.universalPart_caseA | exact GlobalTheory.universalPart_caseA | (intros; apply GlobalTheory.universalPart_caseA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBoundStatement
section
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GlobalTheory.Published.CuspFormsBoundedGL → ∀ (π : CuspSub E a), π.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR π, ∃ φ : Sm E a, φ.1 = F ∧ (∀ l : List (Lie E a), (GlobalTheory.GLFin.word l φ).1 ∈ GlobalTheory.JSW.mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  first | exact @GlobalTheory.JSW.mspanR_smooth | exact GlobalTheory.JSW.mspanR_smooth | (intros; apply GlobalTheory.JSW.mspanR_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamExtension_potentiallySemistable : ExtStep := by
  first | exact @GlobalTheory.PMon.extStep_holds | exact GlobalTheory.PMon.extStep_holds | (intros; apply GlobalTheory.PMon.extStep_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WhitTorus

theorem eq_zero_of_not_antitone_int (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ψ : AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w)
    (W : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hWN : ∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g)
    (hWK : ∀ g, ∀ k ∈ KGL w n, W (g * k) = W g)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin n → ℤ) (hl : ¬ Antitone l)
    (D : GL (Fin n) (w.adicCompletion E))
    (hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ ^ l a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W D = 0 := by
  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)
  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := (l j - l i).toNat with hm
  have hlj : l j = l i + (m : ℤ) := by omega
  have hm1 : 1 ≤ m := by omega
  have hdj : ((ϖ ^ l j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((ϖ ^ l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (ϖ : w.adicCompletion E) ^ m := by
    rw [hlj, _root_.zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy
  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have hu : T x ∈ unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : T c ∈ KGL w n := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hdj]
      ring_nf
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

theorem val_emb₂_tD_one (K : Type) [Field K] {m j n : ℕ} (hn : m + (j + 1) = n) (ϖ : Kˣ) (a : Fin m → ℤ) :
    ((emb₂ K (stdSum hn) (GlobalTheory.IwaCell.tD ϖ a, 1) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun k : Fin n => ((ϖ ^ (if h : (k : ℕ) < m then a ⟨k, h⟩ else 0) : Kˣ) : K) := by
  rw [val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := (stdSum hn).surjective p
  obtain ⟨q, rfl⟩ := (stdSum hn).surjective q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [GlobalTheory.IwaCell.val_tD, Matrix.diagonal_apply, Matrix.one_apply]
  rw [show ((GlobalTheory.IwaCell.tD ϖ a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = _ from GlobalTheory.SmGL.val_diagT K _]
  simp [Matrix.diagonal_apply]

theorem whittaker_value_emb₂_tD : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (m j n : ℕ)
    (hn : m + (j + 1) = n) (ψ : AddChar (w.adicCompletion E) ℂ),
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ),
    (∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g) →
    (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) →
    (∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w n)
      (Tj ℂ n (Ov E w) ϖ i) W = satEig (qV E w) n (Finset.univ.val.map α) i • W) →
    ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) → ∀ a : Fin m → ℤ,
      W (emb₂ (w.adicCompletion E) (stdSum hn) (GlobalTheory.IwaCell.tD ϖ a, 1)) =
        if Antitone a ∧ ∀ i, 0 ≤ a i then
          GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) (GlobalTheory.JSW.padTo (Nat.le.intro hn) fun i => (a i).toNat) * W 1
        else 0 := by
  intro E _ _ w m j n hn ψ hψ W α hN hK hH ϖ hϖ a
  have hv := val_emb₂_tD_one (w.adicCompletion E) hn ϖ a
  split_ifs with ha
  · have hpow : ∀ i, ((ϖ ^ a i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (ϖ : w.adicCompletion E) ^ (a i).toNat := by
      intro i
      conv_lhs => rw [← Int.toNat_of_nonneg (ha.2 i)]
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    have heq : emb₂ (w.adicCompletion E) (stdSum hn) (GlobalTheory.IwaCell.tD ϖ a, 1) =
        Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (GlobalTheory.JSW.padTo (Nat.le.intro hn) fun i => (a i).toNat) i) := by
      apply Units.ext
      rw [hv]
      ext p q
      by_cases hpq : p = q
      · subst hpq
        by_cases hp : (p : ℕ) < m
        · simp [Matrix.diagonal_apply, GlobalTheory.JSW.padTo, hp, hpow]
        · simp [Matrix.diagonal_apply, GlobalTheory.JSW.padTo, hp]
      · simp [Matrix.diagonal_apply, hpq]
    rw [heq]
    exact GlobalTheory.JSW.shintani_formula E w n ψ hψ W α hN hK hH ϖ hϖ _
  · refine eq_zero_of_not_antitone_int E w n ψ hψ W hN hK ϖ hϖ _ ?_ _ hv
    intro hanti
    apply ha
    refine ⟨fun p q hpq => ?_, fun i => ?_⟩
    · have := hanti (show (⟨p, by omega⟩ : Fin n) ≤ ⟨q, by omega⟩ from Fin.le_def.2 (Fin.le_def.1 hpq))
      simpa [p.2, q.2] using this
    · have := hanti (show (⟨i, by omega⟩ : Fin n) ≤ ⟨m, by omega⟩ from Fin.le_def.2 (show (i : ℕ) ≤ m by omega))
      simpa [i.2] using this

end GlobalTheory.WhitTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

namespace GlobalTheory.QkRationalExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkNumberField

theorem exists_ringHom_extend {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed F] (M : IntermediateField K L) (f : M →+* F) : ∃ σ : L →+* F, σ.comp M.val.toRingHom = f := by
  letI : Algebra M F := f.toAlgebra
  have : Algebra.IsAlgebraic M L := Algebra.IsAlgebraic.tower_top (K := K) M
  have : Module.IsTorsionFree M F := DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree M L := DivisionSemiring.to_moduleIsTorsionFree
  let σ : L →ₐ[M] F := IsAlgClosed.lift
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.commutes x⟩

section Ext

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem qkExt_g (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).g = gtExt D f hf z.g := by
  unfold qkExt qkMk
  rfl

theorem qkExt_y (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).y = z.y := ((qkExt_iff hB f hf z _).2 rfl).1

theorem qkExt_qkExt (hB : D.TauBimult) {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (f' : F' →+* F'')
    (hf' : f'.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'') (f'' : F →+* F'')
    (hf'' : f''.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F'') (e : f'.comp f = f'')
    {k : ℕ} (z : QkPt D F k) : qkExt hB f' hf' (qkExt hB f hf z) = qkExt hB f'' hf'' z := by
  refine qk_ext ?_ ?_
  · rw [qkExt_y, qkExt_y, qkExt_y]
  · rw [qkExt_g, qkExt_g, qkExt_g]
    exact gtExt_gtExt f hf f' hf' f'' hf'' e z.g

theorem qkExt_pullQk (hD : IsPullDeg φ D D') (hG : GlobalFnsSt) (hB : D.TauBimult) (hB' : D'.TauBimult)
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] [Field F']
    [Algebra (FractionRing R) F'] [Algebra (FractionRing R') F'] (hF : Compat φ F) (hF' : Compat φ F') (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hf' : f.comp (algebraMap (FractionRing R') F) = algebraMap (FractionRing R') F') {k : ℕ} (z : QkPt D F k) :
    QkExt f (pullQk hD hG hF hB hB' z) (pullQk hD hG hF' hB hB' (qkExt hB f hf z)) := by
  have h₁ : QkExt f z (qkExt hB f hf z) := (qkExt_iff hB f hf _ _).2 rfl
  have h₂ : QkExt f (pullQk hD hG hF hB hB' z) (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)) :=
    (qkExt_iff hB' f hf' _ _).2 rfl
  have h₃ : IsPullGtF φ hD F z.g (pullQk hD hG hF hB hB' z).g := ((eq_pullQk_iff hD hG hF hB hB' z _).1 rfl).2
  have h₄ := isPullGtF_ext hD hF' f hf' h₃ h₁ h₂
  have h₅ : (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)).y = hD.xe.symm (qkExt hB f hf z).y := by
    rw [h₂.1, h₁.1, pullQk_y]
  rw [← (eq_pullQk_iff hD hG hF' hB hB' _ _).2 ⟨h₅, h₄⟩]
  exact h₂

end Ext

theorem exists_rational_of_finite (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    (hB : D.TauBimult) (hB' : D'.TauBimult) {L : Type} [Field L] [Algebra (FractionRing R) L]
    [Algebra.IsAlgebraic (FractionRing R) L] [IsAlgClosed L] [CharZero L]
    (M : IntermediateField (FractionRing R) L) (j : M →+* FractionRing R')
    (hj : ∀ r : R, j (algebraMap (FractionRing R) M (algebraMap R _ r)) = algebraMap R' _ (φ r))
    {k : ℕ} (hk : k ≠ 0)
    (H : ∀ q : QkPt D L k, ∃ z : QkPt D M k, qkExt hB M.val.toRingHom (val_comp M) z = q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R') F] (q : QkPt D' F k) :
    ∃ p : QkPt D' (FractionRing R') k, QkExt (algebraMap (FractionRing R') F) p q := by
  have hG := hL.globalFns
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp (fracMap hφ)).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hF : Compat φ F := fun r => congrArg (algebraMap (FractionRing R') F) (fracMap_algebraMap hφ r)
  obtain ⟨q₀, rfl⟩ := pullQk_surjective hD hG hF hB hB' q
  have hjf : j.comp (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) (FractionRing R') :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (hj r).trans (fracMap_algebraMap hφ r).symm)
  obtain ⟨σ, e⟩ := exists_ringHom_extend M ((algebraMap (FractionRing R') F).comp j)
  have hh : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := rfl
  have hc : ((algebraMap (FractionRing R') F).comp j).comp
      (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) F := by
    rw [RingHom.comp_assoc, hjf, hh]
  have hσ : σ.comp (algebraMap (FractionRing R) L) = algebraMap (FractionRing R) F := by
    rw [← val_comp M, ← RingHom.comp_assoc, e, hc]
  obtain ⟨x, rfl⟩ := GlobalTheory.ArcExt.exists_qkExt σ hσ hB hL (Nat.cast_ne_zero.2 hk) q₀
  obtain ⟨z, rfl⟩ := H x
  refine ⟨pullQk hD hG hK hB hB' (qkExt hB j hjf z), ?_⟩
  rw [qkExt_qkExt hB _ (val_comp M) σ hσ _ hc e z, ← qkExt_qkExt hB j hjf _ hh _ hc rfl z]
  exact qkExt_pullQk hD hG hB hB' hK hF _ hh (RingHom.comp_id _) _

theorem exists_cdvr_ext_rational : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V), D.TauBimult → ∀ N : ℕ, 0 < N → ∀ ϖ : T.V, Irreducible ϖ → ∃ (T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ' ∧ N ∣ e ∧ Associated (g ϖ) (ϖ' ^ e) ∧ ∀ (D' : DegPre T'.V) (_ : IsPullDeg g D D'), D'.TauBimult → ∀ k : ℕ, k ∣ N → ∀ q : QkPt D' (AlgebraicClosure (FractionRing T'.V)) k, ∃ p : QkPt D' (FractionRing T'.V) k, QkExt (algebraMap (FractionRing T'.V) (AlgebraicClosure (FractionRing T'.V))) p q := by
  intro T D hB N hN ϖ hϖ
  have hL : Laws := GlobalTheory.allSixLaws.1
  have : CharZero (FractionRing T.V) := charZero_of_injective_algebraMap (IsFractionRing.injective T.V _)
  obtain ⟨M, hM, H⟩ := exists_finite_qk (D := D) (L := AlgebraicClosure (FractionRing T.V)) hL hB
    (Nat.cast_ne_zero.2 hN.ne')
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))
    (algebraMap T.V _ ϖ)) hN
  have h₁ : FiniteDimensional (FractionRing T.V) (IntermediateField.adjoin (FractionRing T.V) {π}) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let M₂ := M ⊔ IntermediateField.adjoin (FractionRing T.V) {π}
  have h₂ : FiniteDimensional (FractionRing T.V) M₂ := inferInstance
  let π₂ : M₂ := ⟨π, (le_sup_right : _ ≤ M₂) (IntermediateField.mem_adjoin_simple_self _ π)⟩
  have hπ₂ : π₂ ^ N = algebraMap (FractionRing T.V) M₂ (algebraMap T.V _ ϖ) := Subtype.ext hπ
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, -, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V (FractionRing T.V) M₂
  have : CharZero W := charZero_of_injective_algebraMap hinj
  obtain ⟨w, hw⟩ := hint π₂ ⟨Polynomial.X ^ N - Polynomial.C ϖ, Polynomial.monic_X_pow_sub_C _ hN.ne', by
    simp [hπ₂]⟩
  have hwN : w ^ N = algebraMap T.V W ϖ := IsFractionRing.injective W M₂ (by
    rw [map_pow, hw, hπ₂]; exact (RingHom.congr_fun hc ϖ).symm)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hwN
    exact hϖ.ne_zero (hinj (hwN.symm.trans (map_zero _).symm))
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ'
  let ε := FractionRing.algEquiv W M₂
  let j : M →+* FractionRing W := ε.symm.toRingEquiv.toRingHom.comp
    (IntermediateField.inclusion (le_sup_left : M ≤ M₂)).toRingHom
  have hj : ∀ r : T.V, j (algebraMap (FractionRing T.V) M (algebraMap T.V _ r)) =
      algebraMap W _ (algebraMap T.V W r) := fun r => ε.injective (by
    refine (ε.apply_symm_apply _).trans (Eq.trans ?_ (ε.commutes _).symm)
    exact (RingHom.congr_fun hc r).symm)
  refine ⟨Formalism.L2.Pj.CDVR.mk W, algebraMap T.V W, ϖ', m * N, hinj, RingHom.finite_algebraMap.2 hfin, hϖ',
    Dvd.intro_left m rfl, ?_, ?_⟩
  · rw [← hwN, pow_mul]
    exact hm.pow_pow
  · intro D' hD hB' k hk q
    have hk0 : k ≠ 0 := by rintro rfl; exact hN.ne' (Nat.eq_zero_of_zero_dvd hk)
    exact exists_rational_of_finite hL hinj hD hB hB' M j hj hk0 (H k hk) q

end GlobalTheory.QkRationalExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstantIntegralArcFramesStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_integral_arc_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  first | exact @GlobalTheory.ArcFrame.exists_arcFrame | exact GlobalTheory.ArcFrame.exists_arcFrame | (intros; apply GlobalTheory.ArcFrame.exists_arcFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigenStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.InertHeckeTransfer.exists_lift_eigen | exact GlobalTheory.InertHeckeTransfer.exists_lift_eigen | (intros; apply GlobalTheory.InertHeckeTransfer.exists_lift_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SplitTypeCompl

theorem exists_padic_equiv : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D →
    ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous i := by
  intro D s hs
  obtain ⟨w, hw, k, hk⟩ := hs
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by simpa [placesOver] using hk
  have hv : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
    rw [← hw, Ideal.mem_comap, map_natCast]; exact hwk
  have hsw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have := hv
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ hsw
  haveI : CharZero (s.w.adicCompletion D.host.E) :=
    charZero_of_injective_ringHom (algebraMap D.host.E _).injective
  obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic (s.w.adicCompletion D.host.E) (D.host.g k)
    ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1) (GlobalTheory.TypeIdent.irreducible_natCast_compl _ hsw h2)
  exact ⟨D.host.g k, inferInstance, φ, h⟩

end GlobalTheory.SplitTypeCompl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M → (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D → SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  first | exact @GlobalTheory.PendClose.main | exact GlobalTheory.PendClose.main | (intros; apply GlobalTheory.PendClose.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubquotientJacquetModuleOfSupercuspidalSupStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subquotient_jacquetModule_of_supercuspidalSupport : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s : Multiset (IrrGL k)), HasSupport x.rep s → ∃ (r : ℕ) (u : Fin r → IrrGL k) (e : (Σ a, Fin (u a).1) ≃ Fin x.1), (∀ a, u a ∈ s) ∧ IsSubquotient (piTensor fun a => (u a).rep) (jac e x.rep) := by
  first | exact @GlobalTheory.CuspQuot.exists_isSubquotient_jac_of_hasSupport | exact GlobalTheory.CuspQuot.exists_isSubquotient_jac_of_hasSupport | (intros; apply GlobalTheory.CuspQuot.exists_isSubquotient_jac_of_hasSupport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_factor_rec_compatible : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ x : IrrGL (w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  first | exact @GlobalTheory.LocLanglands.isSpherical_iff_unr_of_lawsLit | exact GlobalTheory.LocLanglands.isSpherical_iff_unr_of_lawsLit | (intros; apply GlobalTheory.LocLanglands.isSpherical_iff_unr_of_lawsLit <;> assumption)
end


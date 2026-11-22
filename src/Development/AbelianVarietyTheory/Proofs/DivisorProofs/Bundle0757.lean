import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockLoweringPartEqSubFockOperators
section
noncomputable section
namespace GlobalTheory.FockLowDiff
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

def ixSign {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal ixSign := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, ixSign, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem omAct_kron_diagonal {p q r s : ℕ} (Z : Mat p q) (t : Ix r s → ℂ) (P : Pol p q r s) :
    omAct p q r s (Matrix.kroneckerMap (· * ·) Z (Matrix.diagonal t)) P =
      ∑ a, ∑ b, ∑ c, (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [omAct_apply, Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro d _ hd
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hd)]
  · simp

theorem lowering_eq_diff : ∀ (p q r s : ℕ) (Z : Mat p q), IsPC Z → ∀ P : Pol p q r s, omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)) P - omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q * Z) (Jm r s)) P = (2 : ℂ) • minusPart (fockAct1 p q r s Z) P := by
  intro p q r s Z hZ P
  rw [((GlobalTheory.FockParts.explicit_parts p q r s).1 Z hZ P).2, Jm_eq_diagonal, Jm_eq_diagonal,
    ← Matrix.diagonal_one, omAct_kron_diagonal, omAct_kron_diagonal, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.diagonal_mul, ← sub_smul]
  by_cases hab : sameBlock a b
  · simp [hZ a b hab]
  · rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [sameBlock] at hab <;>
      simp [ixSign, linePos, omE, raiB, lowB, two_smul, add_smul, add_comm]

end GlobalTheory.FockLowDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeLower
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.SchurIrreducible (IrrGK)
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts (delta wtK wtExt wtH IsLowestType IsKIntw)
open GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors (Place eulerProd dPart quadSign SatakeBound)
open scoped TensorProduct

namespace GlobalTheory.BlockSizes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def coverMap {p q : ℕ} (T : GrpData p q) (x : T.G) : UpqT p q := (⟨T.cov x, T.cov_mem x⟩ : Formalism.UG.Upq p q)

def IsStdHaar {p q : ℕ} (T : GrpData p q) : Prop :=
  Formalism.IndefR.Lev.IsMinf (Measure.map (coverMap T) T.haar)

def degOf {p q : ℕ} (ap : Fin p → ℕ) (am : Fin q → ℕ) : ℕ := ∑ i, ap i + ∑ i, am i

def IsRealFactor {p q n : ℕ} (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (z : ℝ) : Prop :=
  ∃ (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2)
    (D : DSRep T1) (W : Submodule ℂ D.HK.V) (M : GKMod n 0) (e0 : W) (v0 : M.V)
    (io : W ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0),
    IsStdHaar T1 ∧ IsLowestType D.HK (wtK n ap am) W ∧ (e0 : D.HK.V) ∈ wtSub D.HK.act (wtExt n ap am) ∧
    IrrGK M ∧ IsHW M.act (wtH n ap am) v0 ∧ IsKIntw F D.HK W M io ∧ io (e0 ⊗ₜ v0) = delta hn ap am ∧
    z = ‖F.ι (delta hn ap am)‖ ^ 2 * Module.finrank ℂ M.V * Module.finrank ℂ W / D.fdeg

def FormalDegreeUpper : Prop :=
  ∀ (p q n : ℕ), 1 ≤ p + q → p + q < n → ∀ (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → ∀ (T : GrpData p q) (D : DSRep T) (W : Submodule ℂ D.HK.V),
    IsStdHaar T → IsLowestType D.HK (wtK n ap am) W →
    Real.log D.fdeg ≤ 2 + ((p + q : ℕ) : ℝ) ^ 2 *
      Real.log (2 * Real.sqrt 2 * ((p + q : ℕ) : ℝ) ^ 2 * n * ((degOf ap am : ℝ) + 2))

def FormalDegreeLower : Prop :=
  ∀ (p q n : ℕ), 1 ≤ p + q → p + q < n → ∀ (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → ∀ (T : GrpData p q) (D : DSRep T) (W : Submodule ℂ D.HK.V),
    IsStdHaar T → IsLowestType D.HK (wtK n ap am) W →
    -Real.log D.fdeg ≤ 3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)

def rowsP (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) : ℕ := ⌊DV.aPlusQ D j τ i⌋₊

def rowsM (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) : ℕ :=
  ⌊DV.aMinusQ D j τ ((D.R.sigW j).2 - 1 - i)⌋₊

theorem sig_add (R : Ranks) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : (R.sigW j).1 + (R.sigW j).2 = R.r := by
  have := R.m_add_three_le_k
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem sig_lt (R : Ranks) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : (R.sigW j).1 + (R.sigW j).2 < R.nV := by
  have := R.rank_add_five_le
  rw [sig_add R h1 h2]
  simp only [Ranks.nV]
  omega

def ConjStable {K : Type} [Field K] [NumberField K] {r : ℕ} (T : Set (Place K)) (x : Place K → Fin r → ℂ) : Prop :=
  ∃ e : Equiv.Perm {w : Place K // w ∉ T}, ∀ w, ∃ s : Equiv.Perm (Fin r),
    ∀ i, x (e w).1 (s i) = starRingEnd ℂ (x w.1 i)

variable {D : D7} (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

def TieL : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, ∃ (T : Set (Place D.host.E)) (x : Place D.host.E → Fin D.R.r → ℂ),
    SatakeBound T D.R.r ((1 + (D.R.t : ℝ)) / 2) x ∧ ConjStable T x ∧ X.LsS μ j π = eulerProd T Finset.univ x

def TieD : Prop := X.dFin D.R.r = dPart (F := D.host.F) ∅ (quadSign D.host.E) D.R.r D.R.t

def TieReal : Prop :=
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ z : D.what₂.Tau → ℝ,
    (∀ τ, IsRealFactor (sig_lt D.R h1 h2) (rowsP D j τ) (rowsM D j τ) (z τ)) ∧ X.ZSbR j = ∏ τ, z τ

def TieMass : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → X.cSb j = 1 ∧ X.massSb j = Formalism.HermitianLatticesTheory.mass (D.sp.V j).hT (D.sp.V j).L0

def Ties : Prop := TieL X ∧ TieD X ∧ TieReal X ∧ TieMass X

def WindowsLe (L : SizeData₂ D) : Prop := L.etaSz ≤ L.sc.b ∧ L.Sc ≤ L.sc.b

end GlobalTheory.BlockSizes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMul
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem cob1_defect_and_defect_mul_of_isLaw : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ),
    cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧
    defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  intro O E _ _ _ d μ hμ f m n
  obtain ⟨hL, hmap⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E (algebraMap O E)
  have hup : ∀ k, up E (nmul μ k) = nmul (up E μ) k := fun k =>
    funext fun i => (hmap k i).2
  have hc : ∀ i, constantCoeff (up E μ i) = 0 := hL.const
  have hk : ∀ k, HasSubst (up E (nmul μ k)) := fun k =>
    hasSubst_of_constantCoeff_zero fun i => by
      rw [hup k]; exact ((GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL 0 k).1 i)
  have hsub : ∀ a b : MvPowerSeries (Fin d) E, cob1 (up E μ) (a - b) = cob1 (up E μ) a - cob1 (up E μ) b :=
    fun a b => by rw [eq_sub_iff_add_eq, ← formalCoboundary_add hc, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · unfold defect
    rw [hsub, formalCoboundary_smul hc, hup n]
    rw [GlobalTheory.T.coboundary_subst_eq_pullback_of_is_hom E d (up E μ) (up E μ) (nmul (up E μ) n) hc hc (GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple E d (up E μ) hL n) f]
  · have hcomp : subst (up E (nmul μ n)) (subst (up E (nmul μ m)) f) = subst (up E (nmul μ (m * n))) f := by
      rw [subst_comp_subst_apply (hk m) (hk n)]
      congr 1
      funext i
      rw [hup, hup, hup, (GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws E d (up E μ) hL m n).2.2.1 i]
    unfold defect
    rw [subst_sub (hk n), subst_smul (hk n), hcomp, smul_sub, Nat.cast_mul, mul_smul]
    abel

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleMod
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace CobSymCoc

open GlobalTheory.Katz.CobCob

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (elim_has hu hv)]
  congr 1
  funext k
  cases k <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map φ (op μ u v i) = op (fun j => map φ (μ j)) (fun j => map φ (u j)) (fun j => map φ (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem map_threeGroupsFirstVariables (φ : R →+* S) : (fun j => map φ (x1 (R := R) (d := d) j)) = x1 := by
  funext j; exact map_X φ _
theorem map_threeGroupsSecondVariables (φ : R →+* S) : (fun j => map φ (x2 (R := R) (d := d) j)) = x2 := by
  funext j; exact map_X φ _
theorem map_threeGroupsThirdVariables (φ : R →+* S) : (fun j => map φ (x3 (R := R) (d := d) j)) = x3 := by
  funext j; exact map_X φ _

theorem map_assocL (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ x1 (op μ x2 x3) i)) =
      op (fun j => map φ (μ j)) x1 (op (fun j => map φ (μ j)) x2 x3) := by
  funext i
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables (op_const h constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables), map_threeGroupsFirstVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem map_assocR (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ (op μ x1 x2) x3 i)) =
      op (fun j => map φ (μ j)) (op (fun j => map φ (μ j)) x1 x2) x3 := by
  funext i
  rw [map_op φ μ (op_const h constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables, map_threeGroupsThirdVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables]

end CobSymCoc

open CobSymCoc CobCob in

theorem cob_symCoc_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL N f hf
  have hM : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, constantCoeff_map, hL.const i, map_zero]
  obtain ⟨A, Bs, -⟩ := formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hM f
  refine ⟨?_, ?_⟩
  · rw [A]
    have eL : op (up Q μ) x1 (op (up Q μ) x2 x3) = up Q (op μ x1 (op μ x2 x3)) :=
      (map_assocL (algebraMap B Q) μ hL.const).symm
    have eR : op (up Q μ) (op (up Q μ) x1 x2) x3 = up Q (op μ (op μ x1 x2) x3) :=
      (map_assocR (algebraMap B Q) μ hL.const).symm
    rw [eL, eR]
    refine GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p B O Q θ hF (RingHom.ker θ) ?_ (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) N f _ _ hf
      (op_const hL.const constantCoeff_threeGroupsFirstVariables (op_const hL.const constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables))
      (op_const hL.const (op_const hL.const constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables) ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
      exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
    · intro i α
      rw [RingHom.mem_ker, ← coeff_map, map_sub]
      have h1 := congrFun (map_assocL θ μ hL.const) i
      have h2 := congrFun (map_assocR θ μ hL.const) i
      rw [h1, h2, hL.law.assoc, sub_self, map_zero]
  · have hs : (fun i => swap (up Q μ i)) = up Q μ := by
      funext i
      have e : map (algebraMap B Q) (swap (μ i)) = swap (map (algebraMap B Q) (μ i)) := by
        unfold swap
        rw [mvPowerSeriesMap_evalTwoGroups (algebraMap B Q) (μ i) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
        simp only [map_X]
      show swap (map (algebraMap B Q) (μ i)) = map (algebraMap B Q) (μ i)
      rw [← e, hL.comm i]
    rw [hs, sub_self] at Bs
    exact sub_eq_zero.1 Bs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightSingularWeightSmoothLeviNonneg
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s hs δ hlevi U z β hz hβ hU
  have hJ := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hz
  have hW := GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph n Y ι La A E U β (jdet A z) hz.isOpen hβ hJ
  have hP : ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source →
      ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i x) :=
    fun x hx i hi => GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet n Y ι La A L s hs x (hU x hx) i hi
  have hS := (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A U z hz).2
  refine ⟨hS (GlobalTheory.OTY.TwEst.wt A E β z)
      (fun x hx => ⟨A.pick x, A.mem_pick x, (hW x hx _ (A.mem_pick x)).1⟩),
    hS (psi A L s) (fun x hx => ⟨A.pick x, A.mem_pick x, hP x hx _ (A.mem_pick x)⟩), ?_⟩
  intro α hα
  refine GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A U z hz (fun y => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y)
    (fun x hx => ⟨A.pick x, A.mem_pick x, ?_, fun ξ => ?_⟩)
  · exact (hW x hx _ (A.mem_pick x)).1.add (contDiffAt_const.mul (hP x hx _ (A.mem_pick x)))
  · have hc : ContDiffAt ℝ ∞ ((fun y => α * psi A L s y) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      contDiffAt_const.mul (hP x hx _ (A.mem_pick x))
    exact le_of_le_of_eq (hlevi α hα (A.pick x) x (A.mem_pick x) (hU x hx) ξ)
      ((hW x hx _ (A.mem_pick x)).2 _ hc ξ).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegralStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_formalLog_sub_smul_integral : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) → (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 → In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) - (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  first | exact @GlobalTheory.QLog.in_frob_formalLog_sub_smul | exact GlobalTheory.QLog.in_frob_formalLog_sub_smul | (intros; apply GlobalTheory.QLog.in_frob_formalLog_sub_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructureStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glBlock_finiteDim_module_structure : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → (∀ U : Submodule ℂ V, U ≤ W → KStable act U → ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W) ∧ (W ≠ ⊥ → ∃ μ v, v ∈ W ∧ IsHW act μ v) ∧ (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ∧ (∀ μ v, v ∈ W → IsHW act μ v → (∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) ∧ OfType act μ v ∧ ∀ U : Submodule ℂ V, KStable act U → U ≤ sInf {N | v ∈ N ∧ KStable act N} → U = ⊥ ∨ v ∈ U) := by
  first | exact @GlobalTheory.BlockReps.finite_module_structure | exact GlobalTheory.BlockReps.finite_module_structure | (intros; apply GlobalTheory.BlockReps.finite_module_structure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharsGoodFamilyOfProductIrreducible
section
noncomputable section

namespace GlobalTheory.GoodFamily

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.BI GlobalTheory.GoodCharsCompare Formalism.MainNotions.PrimeDegreeVariant
open scoped MonoidAlgebra

section Characters

theorem irreducible_of_surjective {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [Nontrivial V]
    (ρ : Representation k G V) (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun w _ => ?_))
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
    obtain ⟨a, ha⟩ := h (LinearMap.smulRight φ w)
    have hw : ρ.asAlgebraHom a v = w := by rw [ha]; simp [hφ]
    rw [← hw]
    clear hw ha
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact S.toSubmodule.add_mem hx hy
    | single t c =>
      rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
      exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule t hv)

theorem irreducible_extend (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] {G : Type} [Group G]
    [Finite G] {n : ℕ} (ρ : Representation K G (Fin n → K))
    (h : Module.finrank K (Representation.IntertwiningMap ρ ρ) = 1) : (extendScalarsRep K L ρ).IsIrreducible := by
  have h1 := pair_character_eq_finrank K L G _ _ ρ ρ
  have h2 := pair_character_eq_finrank L L G _ _ (extendScalarsRep K L ρ) (extendScalarsRep K L ρ)
  simp only [character_extendScalarsRep, Algebra.algebraMap_self, RingHom.id_apply] at h2
  rw [h1, h] at h2
  obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one L G _ (extendScalarsRep K L ρ)
    (by exact_mod_cast h2.symm)
  exact irreducible_of_surjective _ h4

theorem norm_one_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] {χ : ∀ i, G i → ℂ}
    (h : ∀ i, IsChar ℂ ℂ (χ i) ∧ pair (χ i) (χ i) = 1) :
    IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i, χ i (t i)) ∧
      pair (fun t : ∀ i, G i => ∏ i, χ i (t i)) (fun t => ∏ i, χ i (t i)) = 1 := by
  classical
  constructor
  · have : ∀ s : Finset ι, IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i ∈ s, χ i (t i)) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using isChar_one ℂ ℂ (∀ i, G i)
      | insert a s ha ih =>
        obtain ⟨n, ρ, hρ⟩ := (h a).1
        have h1 : IsChar ℂ ℂ (fun t : ∀ i, G i => χ a (t a)) := ⟨n, ρ.comp (Pi.evalMonoidHom G a), fun t => hρ (t a)⟩
        have := isChar_mul_complex h1 ih
        convert this using 1
        funext t
        rw [Finset.prod_insert ha]; rfl
    exact this _
  · letI : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
    have h2 : ∏ i, pair (χ i) (χ i) = 1 := Finset.prod_eq_one fun i _ => (h i).2
    rw [← h2]
    simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib, Pi.inv_apply]

end Characters

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime] {r : ℕ}

end Local

section Global

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

end Global

end GlobalTheory.GoodFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTowerStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_scheme_divided_power_lift_tower : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  first | exact @GlobalTheory.SqLift.isAdmissible_reduce | exact GlobalTheory.SqLift.isAdmissible_reduce | (intros; apply GlobalTheory.SqLift.isAdmissible_reduce <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationCompIsoLiftIffStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeFiltration_comp_iso_lift_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (σ : A₀ ⟶ B₀) [IsMonHom σ] [IsIso σ] (X : Over (Sp R)) (j : B₀.left ⟶ X.left)
    (wj : j ≫ X.hom = B₀.hom ≫ spMap π) (w : (σ.left ≫ j) ≫ X.hom = A₀.hom ≫ spMap π) (d : Crys κ (spMap π) A₀),
    d ∈ schemeFil κ A₀ X (σ.left ≫ j) w ↔ push κ (spMap π) σ d ∈ schemeFil κ B₀ X j wj := by
  first | exact @GlobalTheory.SqLift.schemeFil_comp_iso | exact GlobalTheory.SqLift.schemeFil_comp_iso | (intros; apply GlobalTheory.SqLift.schemeFil_comp_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTopStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  first | exact @GlobalTheory.FilRed.filtration_reduction | exact GlobalTheory.FilRed.filtration_reduction | (intros; apply GlobalTheory.FilRed.filtration_reduction <;> assumption)
end


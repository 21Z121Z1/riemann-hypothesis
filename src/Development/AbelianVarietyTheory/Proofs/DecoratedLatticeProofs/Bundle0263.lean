import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainXOfStepXLastX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DoubleInd

variable {D : D7} {c : Comm D}

def W (t : Tup c) (k : ℕ) : ℂ :=
  ∏ l ∈ Finset.range k, t.cV (2 * l) * t.cK (2 * l) * t.cK (2 * l + 1)

theorem up_succ (t : Tup c) (k : ℕ) (ψ : t.Col 0) :
    t.up (k + 1) ψ = t.K (2 * k + 1) (t.K (2 * k) (t.S (2 * k) (t.up k ψ))) := rfl

theorem up_mem (t : Tup c) (ht : t.Is) (ψ : t.Col 0) (hψ : ψ ∈ t.Ram 0) :
    ∀ k, 2 * k ≤ D.R.m → t.up k ψ ∈ t.Ram (2 * k) := by
  intro k
  induction k with
  | zero => intro _; exact hψ
  | succ k ih =>
    intro hk
    rw [up_succ]
    have h0 := ih (by omega)
    have h1 := ht.stabS (2 * k) (by omega) _ h0
    have h2 := ht.stabK (2 * k) (by omega) _ h1
    exact ht.stabK (2 * k + 1) (by omega) _ h2

theorem up_ind {𝒯 : Type} (t : 𝒯 → Tup c) (ht : ∀ s, (t s).Is) (hS : StepX t) :
    ∀ k ρ (h : 2 * k + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (β : I → ℂ) (ψ : ∀ i, (t (s i)).Col 0)
      (G : ∀ i, (t (s i)).CC (2 * k)), (∀ i, ψ i ∈ (t (s i)).Ram 0) →
      (∀ y v, ∑ i, β i * W (t (s i)) k * (t (s i)).per (2 * k) ρ h ((t (s i)).up k (ψ i)) (G i) y v = 0) →
      ∀ ρ₀ (h₀ : 0 + 2 * ρ₀ + 2 = D.R.m) y v,
        ∑ i, β i * (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) *
          (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) (G i)) y v = 0 := by
  intro k
  induction k with
  | zero =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have hρ : ρ₀ = ρ := by omega
    subst hρ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
    rw [show (∏ j ∈ Finset.range (2 * 0), (t (s i)).cI j) = (1 : ℂ) by simp,
      show W (t (s i)) 0 = 1 by simp [W]]
    rfl
  | succ k ih =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have h' : 2 * k + 2 * (ρ + 1) + 2 = D.R.m := by omega
    have hmem : ∀ i, (t (s i)).up k (ψ i) ∈ (t (s i)).Ram (2 * k) :=
      fun i => up_mem _ (ht _) _ (hψ i) k (by omega)
    have hst := hS (2 * k) ρ h' I s (fun i => β i * W (t (s i)) k) (fun i => (t (s i)).up k (ψ i)) G hmem (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
      have hp : (t (s i)).per (2 * k + 1 + 1) ρ (idx_step h')
          ((t (s i)).K (2 * k + 1) ((t (s i)).K (2 * k) ((t (s i)).S (2 * k) ((t (s i)).up k (ψ i))))) (G i) y v =
          (t (s i)).per (2 * (k + 1)) ρ h ((t (s i)).up (k + 1) (ψ i)) (G i) y v := rfl
      rw [hp]
      simp only [W, Finset.prod_range_succ]
      ring)
    have hi := ih (ρ + 1) h' I s (fun i => β i * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1))) ψ
      (fun i => (t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i))) hψ (by
        intro y v
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hst y v)
        ring) ρ₀ h₀ y v
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hi
    have hp : ∏ j ∈ Finset.range (2 * (k + 1)), (t (s i)).cI j =
        (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
      ring
    have hd : (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * (k + 1)) (G i)) y v =
        (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) ((t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i)))) y v := rfl
    rw [hp, hd]
    ring

end GlobalTheory.SeeSaw.DoubleInd

namespace GlobalTheory.SeeSaw

open GlobalTheory.SeeSaw.DoubleInd in

theorem mainX_of_stepX_lastX : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), (∀ s, (t s).Is) → StepX t → LastX t → MainX t := by
  intro D c 𝒯 t ht hS hL
  intro n h h₀ I _ s α ψ F hψ hyp y v
  have hmem : ∀ i, (t (s i)).up n (ψ i) ∈ (t (s i)).Ram (2 * n) :=
    fun i => up_mem _ (ht _) _ (hψ i) n (by omega)
  have hL' := hL (2 * n) h I s (fun i => α i * W (t (s i)) n) (fun i => (t (s i)).up n (ψ i)) F hmem (by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hyp
    have hp : (t (s i)).tail (2 * n + 1 + 1) h
        ((t (s i)).K (2 * n + 1) ((t (s i)).K (2 * n) ((t (s i)).S (2 * n) ((t (s i)).up n (ψ i))))) (F i) =
        (t (s i)).tail (2 * (n + 1)) h ((t (s i)).up (n + 1) (ψ i)) (F i) := rfl
    rw [hp]
    simp only [Tup.cTop, W, Finset.prod_range_succ]
    ring)
  have hu := up_ind t ht hS n 0 h I s (fun i => α i * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1))) ψ
    (fun i => (t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i))) hψ (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hL' y v)
      ring) n h₀ y v
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hu
  have hc : (t (s i)).cBot =
      (∏ j ∈ Finset.range (2 * n), (t (s i)).cI j) * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1)) := by
    unfold Tup.cBot
    rw [show D.R.m = 2 * n + 1 + 1 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  have hd : (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n + 1) ((t (s i)).ioT (2 * n) h (F i))) y v =
      (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n) ((t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i)))) y v := rfl
  rw [hc, hd]
  ring

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeasurableSetTwistPlaceChainStepDatumMatrixSuppoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  first | exact @GlobalTheory.NrmVol.measurableSet_suppQ | exact GlobalTheory.NrmVol.measurableSet_suppQ | (intros; apply GlobalTheory.NrmVol.measurableSet_suppQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulStkRowsZeroDiag
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix

variable {D : D7}

theorem Tm_mul_stackRows_gram (A : HSp D) (μ : D.host.E) :
    Tm A μ * stackRows A.gram 0 = stackRows 1 1 := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [Tm, stackRows, submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (stackRows A.gram⁻¹ A.gram⁻¹ * A.gram).submatrix id id = stackRows 1 1
  rw [submatrix_id_id]
  show stkRows A.gram⁻¹ A.gram⁻¹ * A.gram = stkRows 1 1
  rw [stkRows_mul, nonsing_inv_mul _ hG]

theorem mul_stkRows_zero_diag {n : ℕ} (F : Mx D (n + n) (n + n))
    (hF : ∀ i j : Fin n, F (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
      F (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)))
    (X : Mx D n n) :
    ∃ β : Mx D n n, F ⬝ (stkRows X 0 : Mx D (n + n) n) = stkRows β β := by
  refine ⟨(F ⬝ (stkRows X 0 : Mx D (n + n) n)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id, ?_⟩
  ext a j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
  simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]
  rcases s with s | s
  · simp only [Matrix.fromRows_apply_inl, Matrix.submatrix_apply, id]
  · simp only [Matrix.fromRows_apply_inr, Matrix.submatrix_apply, id, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp]
    simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hF]

theorem exists_siegel_mul_Tm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ Fr : GL (Fin (A.rank + A.rank)) (AE D), adj Fr.1 * gA (dblSp A) * Fr.1 = incA D μ • rat (Jst D A.rank) → (∀ i j : Fin A.rank, Fr.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) = Fr.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) → ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1 := by
  intro D A μ hμ Fr hFr hdiag
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTT : Tm A μ * (Tm A μ)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hTT' : (Tm A μ)⁻¹ * Tm A μ = 1 := nonsing_inv_mul _ hdet
  have hU : adj (Fr.1 * rat (Tm A μ)⁻¹) * (gA (dblSp A) * (Fr.1 * rat (Tm A μ)⁻¹)) = gA (dblSp A) := by
    have h1 : rat ((Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹) = rat (dblSp A).gram := by
      congr 1
      rw [show (Tm A μ)⁻¹ᴴ * ((Tm A μ)ᴴ * (dblSp A).gram * Tm A μ) * (Tm A μ)⁻¹ =
          (Tm A μ * (Tm A μ)⁻¹)ᴴ * (dblSp A).gram * (Tm A μ * (Tm A μ)⁻¹) by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], hTT, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [hgram, rat_mul, rat_mul, rat_smul, ← hFr, rat_conjTranspose,
      show rat (dblSp A).gram = gA (dblSp A) from rfl] at h1
    rw [adj_mul]
    simp only [Matrix.mul_assoc] at h1 ⊢
    exact h1
  have hS : (Fr.1 * rat (Tm A μ)⁻¹ : Mx D (A.rank + A.rank) (A.rank + A.rank)) ⬝
      (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = Fr.1 ⬝ (stkRows (gA A) 0 : Mx D (A.rank + A.rank) A.rank) := by
    rw [show (stkRows 1 1 : Mx D (A.rank + A.rank) A.rank) = rat (stackRows 1 1) by rw [rat_stackRows, rat_one],
      ← Tm_mul_stackRows_gram A μ, rat_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rat (Tm A μ)⁻¹), ← rat_mul, hTT',
      rat_one, Matrix.one_mul, rat_stackRows, rat_zero]
    rfl
  obtain ⟨β, hβ⟩ := mul_stkRows_zero_diag Fr.1 hdiag (gA A)
  refine ⟨⟨ofMat (dblSp A) _ hU, mem_siegelOf.2 (keepsDiag_of_mul_stkRows_one (β := β) (hS.trans hβ))⟩, ?_⟩
  show (Fr.1 * rat (Tm A μ)⁻¹) * rat (Tm A μ) = Fr.1
  rw [Matrix.mul_assoc, ← rat_mul, hTT', rat_one, Matrix.mul_one]

end GlobalTheory.StdUnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

open IsDedekindDomain NumberField

namespace GlobalTheory.LocMod.LevelPlaces

open IsDedekindDomain NumberField GlobalTheory.IdemSupport

theorem splitPt_v_eq_under {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.L2.NTheta.IsIdemAt q.e P) : q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  obtain ⟨ε, hε, hsum⟩ := q.above
  have hc0 : Φ (cA D q.e) P = 0 := by
    have := ev_mul (Φ := Φ) q.e (cA D q.e) P
    rw [q.split.2.1, ev_zero, hd.2.1, one_mul] at this
    exact this.symm
  have h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0 := by
    rw [← hsum, ev_add, hd.2.1, hc0, add_zero]; exact one_ne_zero
  by_contra hne
  exact h1 ((place_comp hΦ hε).2.2 P (Ne.symm hne))

end GlobalTheory.LocMod.LevelPlaces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeZeroOfIsIdemAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LevelPlaces

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem splitAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {ε : AF D.host.F} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (h : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨he.1, he.2.1, h⟩

theorem eq_under {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hv : SplitAt D v e) : v = P.under (𝓞 D.host.F) := by
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e hv
  have hPQ : Q = P := GlobalTheory.PlaceVec.isIdemAt_inj hQ hP
  subst hPQ
  exact HeightOneSpectrum.ext hQv.symm

theorem ne_zero_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact ((hP.2 x hx0).1 hx) (by rw [zero_mul, map_zero]; exact zero_mem _)

theorem places : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D), c.Is → ∀ (f : c.Pg → GlobalTheory.FinPl.Pl D) (e : c.Pg → AE D),
    (∀ PP, Formalism.L2.NTheta.IsIdemAt (e PP) PP.1) →
    (∀ PP, ∃ ε, IsPlaceIdem D (f PP) ε ∧ e PP + cA D (e PP) = algebraMap (AF D.host.F) (AE D) ε) →
    Function.Injective f ∧ ∀ v, v ∈ c.S ↔ v ∈ Set.range f := by
  intro D c hc f e he hf
  have key : ∀ PP, f PP = PP.1.under (𝓞 D.host.F) := by
    intro PP
    obtain ⟨ε, hε, hsum⟩ := hf PP
    exact eq_under (he PP) (splitAt_of (he PP).1 hε hsum)
  refine ⟨fun PP PP' hPP => ?_, fun v => ?_⟩
  · rw [key, key] at hPP
    obtain ⟨E', ⟨es, hes, hsum⟩, h0⟩ := hc.split
    have h0' := h0
    rw [hsum, map_sum, Finset.sum_mul_sum, ← Finset.sum_product'] at h0'
    have hz : ∀ x ∈ c.Pg ×ˢ c.Pg, es x.1 * cA D (es x.2) = 0 :=
      GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) GlobalTheory.PlaceVec.natCast_mul_eq_zero
      (fun x : Formalism.L2.DIV.Pl D.host.E × Formalism.L2.DIV.Pl D.host.E => es x.1 * cA D (es x.2)) (c.Pg ×ˢ c.Pg) (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hi
        rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]) h0'
    have ha := hes PP.1 PP.2
    have hb := hes PP'.1 PP'.2
    have hab : es PP.1 * cA D (es PP'.1) = 0 := hz (PP.1, PP'.1) (Finset.mem_product.2 ⟨PP.2, PP'.2⟩)
    obtain ⟨va, hva⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff _).1 ha.1
    obtain ⟨vb, hvb⟩ := (GlobalTheory.IdemModTwo.isSplitIdem_iff _).1 hb.1
    have e1 := eq_under ha hva
    have e2 := eq_under hb hvb
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero ha.1 hb.1 with h | h
    · exact Subtype.ext (GlobalTheory.PlaceVec.isIdemAt_inj ha (h ▸ hb))
    · exfalso
      refine ne_zero_of_isIdemAt ha ?_
      have hv : va = vb := by rw [e1, e2, hPP]
      subst hv
      have q1 : es PP.1 * (es PP.1 + cA D (es PP.1)) = es PP.1 := by rw [mul_add, hva.1, hva.2.1, add_zero]
      rw [hva.2.2, ← hvb.2.2, mul_add, h, hab, add_zero] at q1
      exact q1.symm
  · classical
    simp only [GlobalTheory.ChainOnto.Com.S, Finset.mem_image, Set.mem_range]
    constructor
    · rintro ⟨PP, hPP, rfl⟩
      exact ⟨⟨PP, hPP⟩, key _⟩
    · rintro ⟨PP, rfl⟩
      exact ⟨PP.1, PP.2, (key PP).symm⟩

end GlobalTheory.LevelPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthRealHeisenbergTranslatesVacuumOfOrthFockStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FockRealOrth.orth_real_translate | exact GlobalTheory.FockRealOrth.orth_real_translate | (intros; apply GlobalTheory.FockRealOrth.orth_real_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHoldsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_sum_holds : ∀ D : D7, PerSum D := by
  first | exact @GlobalTheory.SeeSaw.perSum_all | exact GlobalTheory.SeeSaw.perSum_all | (intros; apply GlobalTheory.SeeSaw.perSum_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdemMemIdAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceIdemFacts

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem algebraMap_pairA (α : Af D.host.F) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem placeIdem_mem_idAt {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {P : Pl D → Prop} (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  rw [algebraMap_pairA]
  exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => h0 w fun h => hw (h ▸ hP)) 1

theorem infPart_placeIdem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := hε
  exact TensorProduct.zero_tmul _ _

theorem placeIdem_mul {v v' : Pl D} {ε ε' : AF D.host.F} (hε : IsPlaceIdem D v ε) (hε' : IsPlaceIdem D v' ε')
    (h : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨α', rfl, -, h0'⟩ := hε'
  have hαα : α * α' = 0 := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α') = evalV D.host.F w 0
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw
      rw [h0' w h, mul_zero]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α') = 0
  rw [Prod.mk_mul_mk, mul_zero, hαα]
  rfl

theorem idem_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k), cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (∀ (P : Pl D → Prop), P q.v → ∀ (m n : ℕ) (w : Mx D m n), IsHalf (q.e + cA D q.e) w →
        MxAt P w ∧ w.map (infPart D) = 0) ∧
      ∀ (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q' : SplitPt D k'),
        q.v ≠ q'.v → (q.e + cA D q.e) * (q'.e + cA D q'.e) = 0 := by
  intro D k _ _ _ _ q
  obtain ⟨ε, hε, heq⟩ := q.above
  refine ⟨by rw [map_add, cA_cA, add_comm], fun P hP m n w hw => ⟨fun i j => ?_, ?_⟩,
    fun k' _ _ _ _ q' hv => ?_⟩
  · rw [← hw i j, heq]
    exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt hε hP)
  · ext i j
    rw [Matrix.map_apply, Matrix.zero_apply, ← hw i j, map_mul, heq, infPart_placeIdem hε, zero_mul]
  · obtain ⟨ε', hε', heq'⟩ := q'.above
    rw [heq, heq', ← map_mul, placeIdem_mul hε hε' hv, map_zero]

end GlobalTheory.PlaceIdemFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  first | exact @GlobalTheory.FockScal.pureTensorO_scal | exact GlobalTheory.FockScal.pureTensorO_scal | (intros; apply GlobalTheory.FockScal.pureTensorO_scal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlicesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realCentre_acts_by_character_on_isotypic_slices : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → ∃ χ₃ : GA D S → ℂ, ∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v := by
  first | exact @GlobalTheory.CentreTarget.centre_target_char | exact GlobalTheory.CentreTarget.centre_target_char | (intros; apply GlobalTheory.CentreTarget.centre_target_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineColumnTranslationHeisenbergStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_lineColumn_translation_heisenberg : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ y₀ : n → k, ∃ x : WO S B'.L, p.up F₀ FS (fromCols 0 (Matrix.of fun r _ => y₀ r)) = (B.o.resS S).symm (0, l.κ S x) ∧ IsHalf (cA D p.e) ((B'.o.resT S).symm (0, x)) ∧ ∀ t : Matrix (n'' ⊕ Unit) n k, ψ (symplO S B'.V₀ (p.up FS F₀' t) ((B'.o.resT S).symm (0, x))) = ((ψk (-(t (Sum.inr ()) ⬝ᵥ y₀)) : Circle) : ℂ) := by
  first | exact @GlobalTheory.ContrFrameCol.frame_col | exact GlobalTheory.ContrFrameCol.frame_col | (intros; apply GlobalTheory.ContrFrameCol.frame_col <;> assumption)
end


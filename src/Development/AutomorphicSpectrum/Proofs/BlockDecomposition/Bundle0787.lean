import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0784
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0785
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralEisensteinResidue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarGLImageScaling
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.NuFin

variable {R : Type} [CommRing R] {n : ℕ}

theorem image_eq (A Ai A' B Dm K3 K4 C : Matrix (Fin n) (Fin n) R) (O : AddSubgroup (Fin n → R))
    (hAiA : Ai * A = 1) (hC : A * C = B * A') (hD3 : Dm * K3 = -1) (hD4 : Dm * K4 = -C)
    (hset : {x | ∃ y ∈ O, ∃ y' ∈ O, x = K3 *ᵥ y + K4 *ᵥ y'} = (O : Set (Fin n → R))) :
    {x | ∃ y ∈ O.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ O.map (Matrix.mulVecLin A').toAddMonoidHom,
        x = y + B *ᵥ y'} =
      (fun x => (A * Dm * Ai) *ᵥ x) '' (O.map (Matrix.mulVecLin A).toAddMonoidHom : Set (Fin n → R)) := by
  have hgA : (A * Dm * Ai) * A = A * Dm := by rw [mul_assoc, hAiA, mul_one]
  have hid : ∀ u u', (A * Dm * Ai) *ᵥ (A *ᵥ (-(K3 *ᵥ u + K4 *ᵥ u'))) = A *ᵥ u + B *ᵥ (A' *ᵥ u') := by
    intro u u'
    have e3 : (A * Dm) * K3 = -A := by rw [mul_assoc, hD3, mul_neg, mul_one]
    have e4 : (A * Dm) * K4 = -(B * A') := by rw [mul_assoc, hD4, mul_neg, hC]
    rw [Matrix.mulVec_mulVec, hgA, Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, e3, e4, Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.neg_mulVec]
    simp only [neg_add, neg_neg]
  have hK : ∀ u ∈ O, ∀ u' ∈ O, -(K3 *ᵥ u + K4 *ᵥ u') ∈ O := by
    intro u hu u' hu'
    have h1 : K3 *ᵥ u + K4 *ᵥ u' ∈ (O : Set (Fin n → R)) := by
      rw [← hset]
      exact ⟨u, hu, u', hu', rfl⟩
    exact neg_mem h1
  ext x
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hy
    obtain ⟨u', hu', rfl⟩ := AddSubgroup.mem_map.1 hy'
    exact ⟨A *ᵥ (-(K3 *ᵥ u + K4 *ᵥ u')), AddSubgroup.mem_map.2 ⟨_, hK u hu u' hu', rfl⟩, hid u u'⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hy
    have h1 : -w ∈ (O : Set (Fin n → R)) := neg_mem hw
    rw [← hset] at h1
    obtain ⟨u, hu, u', hu', e⟩ := h1
    have hw' : w = -(K3 *ᵥ u + K4 *ᵥ u') := by rw [← e, neg_neg]
    refine ⟨A *ᵥ u, AddSubgroup.mem_map.2 ⟨u, hu, rfl⟩, A' *ᵥ u', AddSubgroup.mem_map.2 ⟨u', hu', rfl⟩, ?_⟩
    change (A * Dm * Ai) *ᵥ (A *ᵥ w) = _
    rw [hw']
    exact hid u u'

theorem map_neg_matrix {S T : Type} [Ring S] [Ring T] (f : S →+* T) (M : Matrix (Fin n) (Fin n) S) :
    (-M).map f = -(M.map f) := by
  ext i j
  simp

set_option maxHeartbeats 1600000 in

theorem local_haar_GL_image_eq_absValue_det : ∀ (D : D7) (n : ℕ) (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → (∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S) → PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt a.1 v) → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) → PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) = (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := by
  intro D n a d b k₃ k₄ v lam hlam hscale hCO hk3 hk4 hset
  have matV_neg : ∀ M : Matrix (Fin n) (Fin n) (AE D), PositivityTheory.SiegelWeilFormula.Gen.matV v (-M) = -PositivityTheory.SiegelWeilFormula.Gen.matV v M := fun M =>
    map_neg_matrix (Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F))
      (AlgHom.id D.host.F D.host.E)).toRingHom M
  let gv : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    Matrix.GeneralLinearGroup.map (compFin D.host.F D.host.E v) (a * d * a⁻¹)
  have hgv : gv.1 = PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1 := by
    have key : ∀ x y z : Matrix (Fin n) (Fin n) (AE D), PositivityTheory.SiegelWeilFormula.Gen.matV v (x * y * z) = PositivityTheory.SiegelWeilFormula.Gen.matV v x * PositivityTheory.SiegelWeilFormula.Gen.matV v y * PositivityTheory.SiegelWeilFormula.Gen.matV v z := by
      intro x y z
      rw [LatCO.matV_mul, LatCO.matV_mul]
    exact key a.1 d.1 (a⁻¹).1
  have hinv : a.1 * (a⁻¹).1 = 1 := by simp
  have hinv' : (a⁻¹).1 * a.1 = 1 := by simp
  have hAiA : PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1 * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 = 1 := by
    rw [← LatCO.matV_mul, hinv', LatCO.matV_one]
  have hC : PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1 = PositivityTheory.SiegelWeilFormula.Gen.matV v b.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (adj (a⁻¹).1) := by
    have e : a.1 * (pull a b).1 = b.1 * adj (a⁻¹).1 := by
      change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) = _
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    rw [← LatCO.matV_mul, ← LatCO.matV_mul, e]
  have hD3 : PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v k₃ = -1 := by
    rw [← LatCO.matV_mul, hk3, matV_neg, LatCO.matV_one]
  have hD4 : PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v k₄ = -PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1 := by
    rw [← LatCO.matV_mul, hk4, matV_neg]
  have hS := image_eq (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) (PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1) (PositivityTheory.SiegelWeilFormula.Gen.matV v (adj (a⁻¹).1)) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) (PositivityTheory.SiegelWeilFormula.Gen.matV v d.1)
    (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄) (PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1) (latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup
    hAiA hC hD3 hD4 hset
  rw [← hgv] at hS
  have hdet : Matrix.GeneralLinearGroup.det gv = unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d) := by
    have h1 : Matrix.GeneralLinearGroup.det (a * d * a⁻¹) = Matrix.GeneralLinearGroup.det d := by
      rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det a), mul_inv_cancel_right]
    rw [← h1]
    exact Matrix.GeneralLinearGroup.map_det _ _
  have hm0 : lam (latAt a.1 v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) ≠ 0 :=
    (hCO.1.measure_pos lam ⟨0, zero_mem _⟩).ne'
  have hmT : lam (latAt a.1 v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) ≠ ⊤ :=
    hCO.2.measure_lt_top.ne
  have hval : lam {x | ∃ y ∈ latAt a.1 v, ∃ y' ∈ latAt (adj (a⁻¹).1) v, x = y + (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1).mulVec y'} =
      (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det gv) : ℝ≥0∞) * lam (latAt a.1 v : Set _) := by
    rw [← hscale gv]
    exact congrArg lam hS
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hval, hdet, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hm0 hmT, mul_one, ENNReal.coe_toReal]

end GlobalTheory.CompanionTheory.MM.NuFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoReducibleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_length_two_reducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible := by
  first | exact @GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible | exact GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible | (intros; apply GlobalTheory.CompanionTheory.BZReducible.cusp_times_nu_reducible <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSumStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ), StronglyMeasurable Φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖)) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.dsum ψ b₀ Φ v.2 v.1) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable | exact GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable | (intros; apply GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Plane

open Matrix GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse

theorem det_eq_of_sig {A D : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (hA : Formalism.UG.HasSignature A p q)
    (hD : Formalism.UG.HasSignature D p q) : ∃ r : ℝ, 0 < r ∧ D.det = r * A.det := by
  obtain ⟨Q, hQ, e⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hA hD
  refine ⟨Complex.normSq Q.det, Complex.normSq_pos.2 hQ, ?_⟩
  have h1 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, Complex.normSq_eq_conj_mul_self]
  ring

theorem sign_det {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature A p q) {δ : ℝ}
    (hdet : A.det = δ) (s : Fin 2 → ℝ)
    (hs : Formalism.UG.HasSignature (Matrix.diagonal fun i => (s i : ℂ)) p q) (hpos : 0 < s 0 * s 1) : 0 < δ := by
  obtain ⟨r, hr, e⟩ := det_eq_of_sig h hs
  rw [Matrix.det_diagonal, Fin.prod_univ_two, hdet] at e
  have e' : s 0 * s 1 = r * δ := by exact_mod_cast e
  rw [e'] at hpos
  exact (pos_iff_pos_of_mul_pos hpos).1 hr

theorem neg_det {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature A p q) {δ : ℝ}
    (hdet : A.det = δ) (s : Fin 2 → ℝ)
    (hs : Formalism.UG.HasSignature (Matrix.diagonal fun i => (s i : ℂ)) p q) (hneg : s 0 * s 1 < 0) : δ < 0 := by
  obtain ⟨r, hr, e⟩ := det_eq_of_sig h hs
  rw [Matrix.det_diagonal, Fin.prod_univ_two, hdet] at e
  have e' : s 0 * s 1 = r * δ := by exact_mod_cast e
  rw [e'] at hneg
  by_contra hc
  exact absurd hneg (not_lt.2 (mul_nonneg hr.le (not_lt.1 hc)))

theorem plane_sig {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature A p q) {c δ : ℝ}
    (hdet : A.det = δ) (hc : c ≠ 0) (h1 : p = 2 → 0 < c) (h2 : q = 2 → c < 0) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i => ((![c, c * δ] i : ℝ) : ℂ)) p q := by
  have hpq : p + q = 2 := by simpa using (Formalism.UG.P.sig_data _ _ _ h).1.symm
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (p = 2 ∧ q = 0) ∨ (p = 1 ∧ q = 1) ∨ (p = 0 ∧ q = 2) := by omega
  · have hd : 0 < δ := sign_det h hdet ![1, 1]
      (hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)) (by simp)
    have hc' := h1 rfl
    exact hasSignature_diagonal _ rfl (fun i => by
      fin_cases i
      · simpa using hc'
      · simpa using mul_pos hc' hd)
  · have hd : δ < 0 := neg_det h hdet ![1, -1]
      (hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)) (by simp)
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have := hasSignature_diagonal (P := 1) (N := 1) ![-c, -(c * δ)] rfl (fun i => by
        fin_cases i
        · simpa using hneg
        · simpa using mul_pos_of_neg_of_neg hneg hd)
      have := hasSig_neg this
      convert this using 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · exact hasSignature_diagonal _ rfl (fun i => by
        fin_cases i
        · simpa using hpos
        · simpa using mul_neg_of_pos_of_neg hpos hd)
  · have hd : 0 < δ := sign_det h hdet ![-1, -1]
      (hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)) (by simp)
    have hc' := h2 rfl
    exact hasSignature_diagonal _ rfl (fun i => by
      fin_cases i
      · simpa using hc'
      · simpa using mul_neg_of_neg_of_pos hc' hd)

theorem quad_nonneg {A : Matrix (Fin 2) (Fin 2) ℂ} (h : Formalism.UG.HasSignature A 2 0) (w : Fin 2 → ℂ) :
    0 ≤ (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hD : Formalism.UG.HasSignature (Matrix.diagonal fun _ : Fin 2 => ((1 : ℝ) : ℂ)) 2 0 :=
    hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)
  obtain ⟨Q, -, e⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hD h
  have hone : (Matrix.diagonal fun _ : Fin 2 => ((1 : ℝ) : ℂ)) = 1 := by
    simp
  rw [hone, Matrix.mul_one] at e
  have key : star w ⬝ᵥ (A *ᵥ w) = star ((Q.map (starRingEnd ℂ)) *ᵥ w) ⬝ᵥ ((Q.map (starRingEnd ℂ)) *ᵥ w) := by
    rw [e, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
    congr 2
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [key, dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have hc : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [Pi.star_apply]
  rw [hc, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end GlobalTheory.CompanionTheory.SW.Plane

namespace GlobalTheory.CompanionTheory.SW.Plane

open Matrix GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem real_of_fixed {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : E →+* ℂ) {x : E} (hx : σ x = x) :
    τ x = (((τ x).re : ℝ) : ℂ) := by
  have h := hCM.2.2.2 τ x
  rw [hx] at h
  exact (Complex.conj_eq_iff_real.1 h.symm).choose_spec ▸ by simp

theorem det_fixed {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) :
    σ J.det = J.det := by
  have h1 : (J.map (σ : E →+* E)) = Jᵀ := by
    ext i j
    exact hJ.1 j i
  have h2 : (σ : E →+* E) J.det = (J.map (σ : E →+* E)).det := RingHom.map_det _ _
  rw [h1, Matrix.det_transpose] at h2
  exact h2

theorem exists_place {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (J : Matrix (Fin 2) (Fin 2) E)
    (hJ : IsHermND σ J) (t : F) (ht : t ≠ 0) (hne : ∀ x : Fin 2 → E, hE σ J x x ≠ algebraMap F E t) :
    ∃ (τ : E →+* ℂ) (c : ℝ), c ≠ 0 ∧ τ (algebraMap F E t) = c ∧
      ∀ w : Fin 2 → ℂ, c * (star w ⬝ᵥ (J.map τ *ᵥ w)).re ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = σ x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (hCM.2.2.2 τ x).symm)
  set a : E := algebraMap F E t with ha
  set D : E := J.det with hD
  have hσa : σ a = a := σ.commutes t
  have hσD : σ D = D := det_fixed hJ
  have ha0 : a ≠ 0 := (map_ne_zero _).2 ht
  have hD0 : D ≠ 0 := hJ.2
  let G' : Matrix (Fin 2) (Fin 2) E := Matrix.diagonal ![a, a * D]
  have hG'd : G'.det = a * (a * D) := by
    simp [G', Matrix.det_diagonal, Fin.prod_univ_two]
  have hG'c : ∀ i j, ReciprocityTheory.ChartRestriction.G.FD.cc (G' i j) = G' j i := fun i j => by
    rw [hcc]
    fin_cases i <;> fin_cases j <;> simp [G', hσa, hσD]
  have hsig : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * J.map τ * Q.map (starRingEnd ℂ) := fun τ => by
    have hc := real_of_fixed hCM τ hσa
    have hδ := real_of_fixed hCM τ hσD
    set c : ℝ := (τ a).re with hcdef
    set δ : ℝ := (τ D).re with hδdef
    have hc0 : c ≠ 0 := fun h => by
      rw [h] at hc
      exact ha0 (τ.injective (by simpa using hc))
    have hH : Formalism.UG.IsHerm (starRingEnd ℂ) (J.map τ) := by
      unfold Formalism.UG.IsHerm
      rw [Formalism.UG.P.cT_conj_eq]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
      rw [← hJ.1 i j, hCM.2.2.2 τ]
    obtain ⟨p, q, hs⟩ := Formalism.UG.P.signature_exists _ (J.map τ) hH (map_isUnit_det J hJ.2 τ)
    have hdet : (J.map τ).det = δ := by
      rw [← hδ]
      exact (RingHom.map_det τ J).symm
    have hpq : p + q = 2 := by simpa using (Formalism.UG.P.sig_data _ _ _ hs).1.symm
    have h1 : p = 2 → 0 < c := fun hp => by
      have hq : q = 0 := by omega
      subst hp hq
      by_contra hneg
      have hneg' : c < 0 := lt_of_le_of_ne (not_lt.1 hneg) hc0
      obtain ⟨w, hw⟩ := hcon τ c hc0 hc
      exact absurd hw (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hneg'.le (quad_nonneg hs w)))
    have h2 : q = 2 → c < 0 := fun hq => by
      have hp : p = 0 := by omega
      subst hp hq
      by_contra hpos
      have hpos' : 0 < c := lt_of_le_of_ne (not_lt.1 hpos) hc0.symm
      obtain ⟨w, hw⟩ := hcon τ c hc0 hc
      have h3 := quad_nonneg (hasSig_neg hs) w
      have h4 : ((star w ⬝ᵥ ((-(J.map τ)) *ᵥ w))).re = -(star w ⬝ᵥ (J.map τ *ᵥ w)).re := by
        simp only [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
      rw [h4] at h3
      nlinarith
    obtain ⟨Q, hQ, e⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hs (plane_sig hs hdet hc0 h1 h2)
    refine ⟨Q, hQ, ?_⟩
    rw [← e]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G', Matrix.diagonal_apply, ← hc, ← hδ]
  obtain ⟨P, -, hP⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 E 2 J G'
    (fun i j => by rw [hcc]; exact hJ.1 j i) hG'c hJ.2
    (by rw [hG'd]; exact mul_ne_zero ha0 (mul_ne_zero ha0 hD0)) hsig
    ⟨a⁻¹, by
      rw [hcc, hG'd, map_inv₀, hσa]
      field_simp
      rfl⟩
  refine hne (fun i => σ (P i 0)) ?_
  have e := congrFun (congrFun hP 0) 0
  have hσσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2]; simp)
  simp only [G', Matrix.diagonal_apply_eq, Matrix.cons_val_zero] at e
  rw [e]
  simp only [hE, hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hcc, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [hσσ]

theorem exists_hom {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : E →+* ℂ) :
    ∃ Φ : Ainf F ⊗[F] E →+* ℂ, (∀ e, Φ (inclR (Ainf F) e) = τ e) ∧
      ∀ y, Φ (sigR (Ainf F) σ y) = star (Φ y) := by
  haveI : IsTotallyReal F := hCM.1
  let φ : F →+* ℂ := τ.comp (algebraMap F E)
  let v : InfinitePlace F := InfinitePlace.mk φ
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hφ : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 hv
  let ψ : Ainf F →+* ℝ := (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)
  have hψ : ∀ x : F, ((ψ (algebraMap F (Ainf F) x) : ℝ) : ℂ) = φ x := fun x => by
    have h1 : ψ (algebraMap F (Ainf F) x) = InfinitePlace.embedding_of_isReal hv x :=
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x)
    rw [h1, InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  letI : Algebra F ℂ := φ.toAlgebra
  let f : Ainf F →ₐ[F] ℂ := { Complex.ofRealHom.comp ψ with commutes' := hψ }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun e => ?_, fun y => ?_⟩
  · simp [inclR, f, g]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      simp [sigR, f, g, hCM.2.2.2 τ]
    | add x y hx hy => simp only [map_add, star_add, hx, hy]

end GlobalTheory.CompanionTheory.SW.Plane

namespace GlobalTheory.CompanionTheory.SW

end GlobalTheory.CompanionTheory.SW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralEisensteinResidueStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_eisenstein_residue : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₁ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisCoeffAt V Φ s₀ (-1) E₁ → CoeffAt (GlobalTheory.Eis.zeta V μ m Φ f₁ f₂) s₀ (-1) (GlobalTheory.Eis.dblInt V μ m E₁ f₁ f₂) := by
  first | exact @GlobalTheory.CompanionTheory.Eis.coeffAt_neg_one_zeta | exact GlobalTheory.CompanionTheory.Eis.coeffAt_neg_one_zeta | (intros; apply GlobalTheory.CompanionTheory.Eis.coeffAt_neg_one_zeta <;> assumption)
end


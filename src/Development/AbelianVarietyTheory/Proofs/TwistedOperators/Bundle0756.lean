import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0747
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0748
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0750
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexWeilOrbitValue
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0313
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0723
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0751
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilators
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : idLat 1 Λ = Λ := by
  apply le_antisymm
  · rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem idLat_mulVec {n : ℕ} (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ := by
  intro x hx
  have hle : idLat I Λ ≤ (idLat I Λ).comap ((Matrix.mulVecLin M).restrictScalars (𝓞 D.host.E)) := by
    rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    change M *ᵥ (s • y) ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨s, hs, M *ᵥ y, hM y hy, rfl⟩
  exact hle hx

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

section Witt

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pX_jX)
theorem qX_e' : d.qX * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_jY)
theorem qX_i₀ : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
theorem qY_e : d.qY * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_jX)
theorem qY_e' : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
theorem qY_i₀ : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)

end Witt

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem mul_col {m n r c : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E)
    (Bm : Matrix (Fin n) (Fin r) D.host.E) (q : Fin c) (p : Fin r) (κ : D.host.E) (h : ∀ l, a l q = κ * Bm l p)
    (k : Fin m) : (M * a) k q = κ * (M * Bm) k p := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ)

theorem auxiliary_vector_multiple_of_witt_basis_vector (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (q : Fin c) :
    (q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e l p) ∧
    (¬ q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e' l p) := by
  obtain ⟨h2, he, s, he'⟩ := hd
  have hq2 := q.2
  refine ⟨fun hq => ⟨⟨q.1, hq⟩, ((-D.host.xi0) ^ (q.1 + 1))⁻¹, fun l => ?_⟩, fun hq => ?_⟩
  · rw [he]
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))]
    rfl
  · have hp : c - 1 - q.1 < ρ := by omega
    have hs : s ⟨c - 1 - q.1, hp⟩ ≠ 0 := by
      intro h0
      have := congrFun (congrFun (qY_e' d) ⟨c - 1 - q.1, hp⟩) ⟨c - 1 - q.1, hp⟩
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp [he', colsOf, h0] at this
    refine ⟨⟨c - 1 - q.1, hp⟩, (s ⟨c - 1 - q.1, hp⟩)⁻¹, fun l => ?_⟩
    rw [he']
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ hs]
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_castLE]
    omega

theorem wittHyperbolic_projX_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e * d.qX * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qX_e, Matrix.mul_one, if_pos hq, mul_one, h]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qX_e', hq]

theorem wittHyperbolic_projY_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e' * d.qY * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qY_e, hq]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qY_e', Matrix.mul_one, if_neg hq, mul_one, h]

theorem proj_lat (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (hi : d.i₀ = frameMat B A a.ι)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    ∀ x ∈ a.lat Λ 𝔟, (d.e * d.qX) *ᵥ x ∈ a.lat Λ 𝔟 ∧ (d.e' * d.qY) *ᵥ x ∈ a.lat Λ 𝔟 := by
  rintro x ⟨y, hy, u, hu, rfl⟩
  have k1 : d.e * d.qX * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qX_i₀, Matrix.mul_zero]
  have k2 : d.e' * d.qY * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qY_i₀, Matrix.mul_zero]
  refine ⟨⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) *ᵥ u, fun p => ?_, ?_⟩,
    ⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) *ᵥ u, fun p => ?_, ?_⟩⟩
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [one_mul]; exact hu p
    · rw [zero_mul]; exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k1, wittHyperbolic_projX_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [zero_mul]; exact (𝔟 p).zero_mem
    · rw [one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k2, wittHyperbolic_projY_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

end SlopeTestRemainingChoices

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.BigProj in

theorem pcBF_big_core : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)),
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) →
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) ∈ latBig G (2 * ρ + 1) ∧
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) ∈ latBig G (2 * ρ + 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h w hw
  have sdS : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdT : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdB := ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have big : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := by
    have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (S := G.V (.grid (2 * ρ + 2) 0)) (B := G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0)) 1 (G.Λ (.grid (2 * ρ + 1) 0)) sdS (by rw [idLat_one]; exact sdT)
      (by rw [one_mul]; exact sdB) _ (by rw [idLat_one]; exact latO_negSp_le _ _ _ _ _ hw.1)
      ⟨e, he, by rw [idLat_one]; exact hw.2 e he⟩
    rw [one_mul] at key
    exact key
  have h1 : 1 ≤ 2 * ρ + 1 := by omega
  have h2 : 2 * ρ + 1 ≤ D.R.m := by omega
  have hlat : ∀ x ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).e * (F.dJ ρ h).qX) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) ∧
      ((F.dJ ρ h).e' * (F.dJ ρ h).qY) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
    have e1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) h1 h2).lat (G.sp.P (2 * ρ + 1)).lat
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) h1 h2
    rw [e1]
    exact proj_lat _ _ (hF.hJ ρ h) (by omega) (hF.aJ ρ h) _ _
  have sdS' : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) := sdS
  have hx := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual sdS' sdS' sdB 1 ((F.dJ ρ h).e * (F.dJ ρ h).qX)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).1) _ big
  have hy := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual sdS' sdS' sdB 1 ((F.dJ ρ h).e' * (F.dJ ρ h).qY)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).2) _ big
  have hr1 : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, x ⬝ rat 1 = x := fun x => by
    rw [rat_one]; exact Matrix.mul_one x
  have ex : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) =
      (rat ((F.dJ ρ h).e * (F.dJ ρ h).qX) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc]
    rfl
  have ey : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) =
      (rat ((F.dJ ρ h).e' * (F.dJ ρ h).qY) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc]
    rfl
  exact ⟨ex ▸ hx, ey ▸ hy⟩

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_standard_parabolic : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  first | exact @GlobalTheory.AscFin.finLat_pcBF_A₁ | exact GlobalTheory.AscFin.finLat_pcBF_A₁ | (intros; apply GlobalTheory.AscFin.finLat_pcBF_A₁ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnTypeTwistDatumEqGivenFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_column_type_twist_datum_eq_given_function : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  first | exact @GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | exact GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn | (intros; apply GlobalTheory.FlipTop.prodHalf_topFn_eq_givenFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexWeilOrbitValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_vertex_weil_orbit_value : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  first | exact @GlobalTheory.FirstRowScalar.scalar | exact GlobalTheory.FirstRowScalar.scalar | (intros; apply GlobalTheory.FirstRowScalar.scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthLatticeLineComponentsMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineFB

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  obtain ⟨-, hfr, hline⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hx := AddSubgroup.mem_comap.1 hu
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply] at hx
  have hSc : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (G.isV (X := .core (2 * (σ + 1) + 1)) (by simp [Node.InRange]; omega) (fun j e => Node.noConfusion e)).sd
  have hSg : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hTg : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hℓ := (hfr σ h').2.2.1
  have hℓ' := hline (σ + 1)
  have h0 := (hfr σ h').1
  have hj : ∀ y ∈ G.Λ (.core (2 * (σ + 1) + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * (σ + 1) + 1) 0) :=
    GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hSg) fun v => ((hfr (σ + 1) h).2.1 v).2
  have hq : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0), ((F.oB σ h').qB * (F.dB σ h').q0) *ᵥ t ∈
      idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hℓ) (hfr σ h').2.2.2 _
      (GlobalTheory.T.q0_mulVec_mem_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions h0) (fun v => ((hfr σ h').2.1 v).1) t ht)
  have key : ((F.oB σ h').resT _ u).2 =
      rat ((F.oB σ h').qB * (F.dB σ h').q0) * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * rat (F.dJ (σ + 1) h).i₀ := by
    rw [OrthDec.resT_apply, rat_mul]
    change _ = (F.oB σ h').pB * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (F.dB σ h').p0, HypDec.p0_j0, Matrix.one_mul, HypDec.p0_j0, Matrix.mul_one]
  rw [key]
  have hz := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual hSg hSc hℓ _ _ hj hq _ (latO_negSp_le' _ _ _ _ _ hx.1)
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hd := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom G.modul _ ((F.oB σ h').qB * (F.dB σ h').q0) hj hq _ (hx.2 e he)
  refine GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hD μ0 hL G _ _ _ hSc hℓ hℓ' _ hz ⟨e, he, ?_⟩
  rwa [Matrix.mul_smul, Matrix.smul_mul] at hd

end GlobalTheory.LineFB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvAAMultipleDepthLatticeMapsCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAAUnit

variable {D : D7}

theorem idem_smul_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (v : GlobalTheory.FinPl.Pl D)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.FinPlLoc.ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ w) (hαi w)
    · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold GlobalTheory.FinPlLoc.idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem smul_mulVec_mem_latV : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hOff T L μ0 hL sc G W Mv hM F hF ρ h M hMr v y hy s hs
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hO : M ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 2) 0) : Set _)
      (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) :=
    GlobalTheory.RowLoc.mem_latO_negSp.1 hMr.1
  have hyT : y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) := GlobalTheory.FinPl.PsiUnit.latV_mono trivial hy
  have hA : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hV hO hyT
  have hy' : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPlLoc.latV_idAt hy i)
  have hAv : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
    rw [← hy', Matrix.mulVec_smul]
    exact idem_smul_latA v hA
  exact (((GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v).2.2.2.2.2.2 _ _ _).1 hAv).2 s hs

end GlobalTheory.AscFin.RowAAUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiDepthLatticeKeepsIsotropicHomPartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_depth_lattice_keeps_isotropic_hom_part : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.AscFin.SplitX.latRow_extX | exact GlobalTheory.AscFin.SplitX.latRow_extX | (intros; apply GlobalTheory.AscFin.SplitX.latRow_extX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiStepCoreComponentMemCoreDepthLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  first | exact @GlobalTheory.CoreComp.core_mem_latCore | exact GlobalTheory.CoreComp.core_mem_latCore | (intros; apply GlobalTheory.CoreComp.core_mem_latCore <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCorePieceNonzeroVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.PcFBVac.pcFB_vac | exact GlobalTheory.AscFin.PcFBVac.pcFB_vac | (intros; apply GlobalTheory.AscFin.PcFBVac.pcFB_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧ ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  first | exact @GlobalTheory.AscFin.pcFB_fin | exact GlobalTheory.AscFin.pcFB_fin | (intros; apply GlobalTheory.AscFin.pcFB_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcFB W F σ h h').B₁ ↔ ∀ η ∈ (pcFB W F σ h h').B₂, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) ∧ (∀ η, MxAt (fun _ => True) η → (η ∈ (pcFB W F σ h h').B₂ ↔ ∀ ξ ∈ (pcFB W F σ h h').B₁, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) := by
  first | exact @GlobalTheory.AscFin.DualParts.pcFB_dual | exact GlobalTheory.AscFin.DualParts.pcFB_dual | (intros; apply GlobalTheory.AscFin.DualParts.pcFB_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_row_column_product_data_have_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  first | exact @GlobalTheory.VecsLast.vecs_last | exact GlobalTheory.VecsLast.vecs_last | (intros; apply GlobalTheory.VecsLast.vecs_last <;> assumption)
end


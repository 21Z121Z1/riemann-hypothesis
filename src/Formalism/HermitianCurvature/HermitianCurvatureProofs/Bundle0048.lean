import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.StatementQ
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormLevel.Imports
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LastLevelSliceOfScalar
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

lemma castW_mul (a b : B.Mat k 0) : castW (a * b) = castW a * castW b := by
  unfold castW
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]

lemma castW_ct (a : B.Mat k 0) : (castW a)ᴴ = castW aᴴ := by
  unfold castW
  simp

lemma hb_eq : Hb k = castW (Hpk k 0) := by
  ext i j
  simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply, Hb, Matrix.diagonal_apply, Hpk]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i = Fin.last k
    · subst hl
      simp [Fin.last]
    · have hv : (i : ℕ) ≠ k := fun h => hl (Fin.ext (by simpa [Fin.last] using h))
      have hlt : (i : ℕ) < k + 1 := i.isLt
      simp [hl, hv]
      omega
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [hij, Fin.ext_iff, hv]

lemma castW_mem {μ : B.Mat k 0} (hμ : μ ∈ GV k 0) : (castW μ)ᴴ * Hb k * castW μ = Hb k := by
  have h : μᴴ * Hpk k 0 * μ = Hpk k 0 := hμ
  rw [hb_eq, castW_ct, ← castW_mul, ← castW_mul, h]

def NNSlice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m → ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        B.gN ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN)

def Slice1 : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)

def SliceRegularityClauses : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) →
      B.InCC (k := k) (r := 0) ((A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))) m (sliceR D F c)) ∧
    ∀ (d : ℕ) (O : Set (Fin d → ℝ)) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0),
      IsOpen O → ContDiffOn ℝ ∞ cx O → ContDiffOn ℝ ∞ μx O → (∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) O

theorem last_level_slice_of_parts : Slice1 → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := by
  intro h1 h23 k r Wp Wq _ _ _ _ _ _ D A m F hThr hF
  exact ⟨h1 k r Wp Wq D A m F hThr hF, (h23 k r Wp Wq D A m F hThr hF).1, (h23 k r Wp Wq D A m F hThr hF).2⟩

theorem slice1_of_nnSlice : NNSlice → Slice1 := by
  intro hS k r Wp Wq _ _ _ _ _ _ D A m F hThr hF c hc μ hμ
  obtain ⟨ν, hν⟩ := hF
  have hx : bigCell k r c (castW μ) ∈ GV k r := big_cell_mem_holds k r c (castW μ) hc (castW_mem hμ)
  have := B5.haar_sigmaFinite D.haarN
  have hae : ∀ᵐ nn ∂(D.μN.prod D.μN), (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae (B5.haar_ae D.haarN)).and
      (Measure.quasiMeasurePreserving_snd.ae (B5.haar_ae D.haarN))
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} := B6.isClosed_Nset k r
  have hTc : IsClosed {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    (c2.preimage continuous_fst).inter (c2.preimage continuous_snd)
  have h1c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r) := continuous_fst
  have h2c : Continuous fun nn : Mt k r × Mt k r => (Matrix.of nn.2 : Mat k r) := continuous_snd
  have hy : ContinuousOn (fun nn : Mt k r × Mt k r => (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)
      {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} :=
    B6.continuousOn_matrix_mul (B6.continuousOn_matrix_mul
      ((B6.inv_continuousOn k r).comp h1c.continuousOn (fun nn h => B6.Nset_sub _ _ h.1)) continuousOn_const)
      h2c.continuousOn
  have hyG : ∀ nn ∈ {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r},
      (Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2 ∈ GV k r := fun nn h =>
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B6.Nset_sub _ _ h.1)) hx) (B6.Nset_sub _ _ h.2)
  have hcomp := (B6.continuousOn_of_contDiffOn_group hν.1).comp hy hyG
  have hmeas : AEStronglyMeasurable
      (fun nn : Mt k r × Mt k r => F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2))
      (D.μN.prod D.μN) := by
    have := hcomp.aestronglyMeasurable (μ := D.μN.prod D.μN) hTc.measurableSet
    have hr : (D.μN.prod D.μN).restrict
        {nn : Mt k r × Mt k r | (Matrix.of nn.1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r ∧ (Matrix.of nn.2 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r} =
        D.μN.prod D.μN := Measure.restrict_eq_self_of_ae_mem hae
    rwa [hr] at this
  refine Integrable.mono' ((hS k r Wp Wq D A m hThr c hc μ hμ).const_mul ν) hmeas ?_
  filter_upwards [hae] with nn hnn
  have hyg := hyG nn hnn
  have hpos : 0 < gN ((Matrix.of nn.1 : Mat k r)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) := B6.gN_pos hyg
  have hb := hν.2 [] [] (by simp) (by simp) (by simp) _ hyg
  change gN _ ^ A * ‖F _‖ ≤ ν at hb
  rw [Real.rpow_neg hpos.le]
  rw [mul_comm, ← le_div_iff₀ (Real.rpow_pos_of_pos hpos A)] at hb
  calc _ ≤ _ := hb
    _ = _ := by rw [div_eq_mul_inv]

theorem _root_.Formalism.FourierDecayAlt.P.last_level_slice_of_scalar : NNSlice → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := fun h h23 =>
  last_level_slice_of_parts (slice1_of_nnSlice h) h23

end Formalism.FourierDecayAlt.P.JFxDs5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x6

open C2x5

variable {k r : ℕ}

lemma herm_ff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by
  rw [ggBlockA k r z hz a b, hzz_real]
  simp only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha hb; simp
  · simp [ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]
  · simp [ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]
  · by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [ha, hab]

lemma E_cast {n : ℕ} (x : Fin n → ℂ) : star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

lemma E_unit {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((H *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  rw [← E_cast (H *ᵥ v), ← E_cast v, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hH, hH2, Matrix.one_mulVec]

lemma euclid_cs {n : ℕ} (a b : Fin n → ℂ) :
    Complex.normSq (star b ⬝ᵥ a) ≤ (∑ i, Complex.normSq (a i)) * (∑ i, Complex.normSq (b i)) := by
  have h1 : ‖star b ⬝ᵥ a‖ ≤ ∑ i, ‖b i‖ * ‖a i‖ := by
    rw [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b i‖) (fun i => ‖a i‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖star b ⬝ᵥ a‖ ^ 2 ≤ (∑ i, ‖b i‖ * ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖a i‖ ^ 2) := h2
    _ = (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := mul_comm _ _

lemma Hpk_mul_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
  rw [Matrix.mul_apply]
  simp [GBasic.Hpk_eq]

lemma mul_Hpk_apply (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (M * Hpk k r) i j = M i (GBasic.sig k r j) * GBasic.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r j)]
  · rw [GBasic.Hpk_eq, if_pos (GBasic.sig_sig k r j).symm, GBasic.sgn_sig]
  · intro l _ hl
    rw [GBasic.Hpk_eq, if_neg, mul_zero]
    intro h
    exact hl (by rw [h, GBasic.sig_sig])
  · simp

lemma normSq_sgn (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by
  unfold GBasic.sgn
  split_ifs <;> simp

end C2x6

open C2x5 C2x6

theorem gram_block_form : C2.GramBlocks := by
  intro k r z z' hz hz' g hg
  have hH := GBasic.Hpk_herm k r

  have hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    simp only [herm]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    exact herm_ff hz.1 a b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [ggHerm_swap _ hH]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [hpres]
    exact herm_ff hz'.1 a b

theorem majorant_estimate : C2.Majorant := by
  intro k r
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  refine ⟨?_, hsq, fun v => ⟨?_, ?_⟩⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hH, hsq, Matrix.one_mul]
  · simp only [herm]
    rw [E_cast, E_unit _ hH hsq]
  · have hcs := euclid_cs (Hpk k r *ᵥ v) v
    rw [E_unit _ hH hsq] at hcs
    set S := ∑ i, Complex.normSq (v i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have h1 : ‖herm (Hpk k r) v v‖ ^ 2 ≤ S ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, sq]
      exact hcs
    have h2 : ‖herm (Hpk k r) v v‖ ≤ S := (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).mp h1
    exact (Complex.re_le_norm _).trans h2

theorem norm_of_inverse : C2.NormInv := by
  intro k r g hg
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg

  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hleft
  have hright : g * g⁻¹ = 1 := by
    rw [hinv]
    first
    | exact Matrix.mul_eq_one_comm.mp hleft
    | exact mul_eq_one_comm.mp hleft
  have hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j) := by
    have he : ∀ i j, Complex.normSq (g⁻¹ i j) =
        Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i)) := by
      intro i j
      rw [hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul,
        Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]
      ring
    simp only [he]
    let σ : Equiv.Perm (Fin (2 * r + k + 1)) :=
      Function.Involutive.toPerm _ (GBasic.sig_sig k r)
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv σ _ _ fun j => ?_
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  refine ⟨by simp only [B.gN, hsum], ?_⟩

  set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hcs := euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))
  have h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1 := by
    have := congrFun (congrFun hright i0) i0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [dotProduct] using this
  rw [h1, Complex.normSq_one] at hcs
  have hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j) := fun h =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2 := by
    rw [hgN, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j))
      (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2 := by
    rw [hgN]
    simp only [Complex.star_def, Complex.normSq_conj]
    exact Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hN0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hEq : B.gN g⁻¹ = B.gN g := by simp only [B.gN, hsum]
  rw [hEq] at hA
  have h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2 :=
    hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
      (sq_nonneg _))
  by_contra hlt
  push_neg at hlt
  have : B.gN g ^ 2 * B.gN g ^ 2 < 1 := by
    have h5 : B.gN g ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (B.gN g)]
  linarith

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem one_parameter_differentiable : Formalism.FourierDecayAlt.Qr.OneParamDiff := by
  intro W _ _ _ φ h0 hadd hc
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := fun s t => hadd s t
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖φ s - 1‖ < 1 / 2 := by
    obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have := H s (by rwa [Real.dist_eq, sub_zero])
    rwa [dist_eq_norm, h0] at this
  set h : ℝ := δ / 2 with hh
  have hpos : 0 < h := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  set M : W →L[ℂ] W := ∫ s in (0 : ℝ)..h, φ s with hM
  have hbound : ‖M - h • (1 : W →L[ℂ] W)‖ ≤ 1 / 2 * |h - 0| := by
    have e : M - h • (1 : W →L[ℂ] W) = ∫ s in (0 : ℝ)..h, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 h) intervalIntegrable_const, intervalIntegral.integral_const,
        sub_zero]
    rw [e]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hpos.le] at hs
    refine (hball s ?_).le
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  set tt : W →L[ℂ] W := 1 - h⁻¹ • M with htt
  have hnorm : ‖tt‖ < 1 := by
    have e : tt = h⁻¹ • (h • (1 : W →L[ℂ] W) - M) := by
      rw [htt, smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc h⁻¹ * ‖M - h • (1 : W →L[ℂ] W)‖ ≤ h⁻¹ * (1 / 2 * |h - 0|) := by gcongr
      _ = 1 / 2 := by
        rw [sub_zero, abs_of_pos hpos, ← mul_assoc, mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      _ < 1 := by norm_num
  let u0 := Units.oneSub tt hnorm
  have hu0 : (u0 : W →L[ℂ] W) = h⁻¹ • M := by
    show 1 - tt = h⁻¹ • M
    rw [htt, sub_sub_cancel]
  set G : ℝ → W →L[ℂ] W := fun t => (∫ s in (0 : ℝ)..t + h, φ s) - ∫ s in (0 : ℝ)..t, φ s with hG
  have hφM : ∀ t, φ t * M = G t := by
    intro t
    have e1 := (ContinuousLinearMap.mul ℂ (W →L[ℂ] W) (φ t)).intervalIntegral_comp_comm (hint 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at e1
    rw [hM, ← e1]
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + h)) (hint 0 t)]
    rw [show (fun s => φ t * φ s) = fun s => φ (t + s) from funext fun s => (hmul t s).symm,
      intervalIntegral.integral_comp_add_left φ t, add_zero]
  have hφ : φ = fun t => (h⁻¹ • G t) * (↑u0⁻¹ : W →L[ℂ] W) := by
    funext t
    rw [← hφM t, ← mul_smul_comm, ← hu0, Units.mul_inv_cancel_right]
  have hF : ∀ x, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, φ s) (φ x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine ⟨(h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W), fun t => ?_⟩
  have hGd : HasDerivAt G (φ (t + h) - φ t) t := ((hF (t + h)).comp_add_const t h).sub (hF t)
  let R : (W →L[ℂ] W) →L[ℝ] (W →L[ℂ] W) :=
    (((ContinuousLinearMap.mul ℂ (W →L[ℂ] W)).flip (↑u0⁻¹ : W →L[ℂ] W)).restrictScalars ℝ)
  have hd := R.hasFDerivAt.comp_hasDerivAt t (hGd.const_smul h⁻¹)
  have e : ∀ x, φ x = (⇑R ∘ (h⁻¹ • G)) x := by
    intro x
    rw [hφ]
    rfl
  have e2 : φ t ∘SL ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = R (h⁻¹ • (φ (t + h) - φ t)) := by
    show φ t * ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = (h⁻¹ • (φ (t + h) - φ t)) * (↑u0⁻¹ : W →L[ℂ] W)
    rw [hmul t h, show φ t * φ h - φ t = φ t * (φ h - 1) by rw [mul_sub, mul_one], ← mul_smul_comm, mul_assoc]
  rw [e2]
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall e)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QxPIRttLevel
section
theorem Formalism.FourierDecayAlt.P.rtt_level_from_upper : Formalism.FourierDecayAlt.Q.RTTLevelFromUpper := by
  intro hU hLT hGI hFF _ k r i
  induction i using Fin.cases with
  | succ l => exact hU k r l
  | zero =>
    intro Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
    obtain ⟨π₁, π₁', D₁, f, hw, hw', hD₁, hf, hfJ⟩ := hFF Wp Wq k r z z' π π' D hz hz' hD J hJ
    have key : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2),
        Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z') ⟨1, by omega⟩
                  Y p q (Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z')
                    ⟨1, by omega⟩ Y' p' q' f) (Formalism.QuantumDeterminants.ιLev k 1 r g) =
          Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y p q (Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y' p' q' J) g := by
      intro Y Y' p q p' q'
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hg.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y p q).loc _ _ ?_ g hg
      intro x hx
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y' p' q').loc _ _ ?_ x hx
      intro y hy
      exact (hfJ y hy.1.1).2
    have hιg : Formalism.QuantumDeterminants.ιLev k 1 r g ∈ Formalism.FourierDecayAlt.Q.Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁ := by
      refine ⟨?_, (hfJ g hg.1.1).1.mpr hg.2⟩
      rw [hGI k 1 r]
      exact ⟨g, hg.1.1, rfl⟩
    have h1 : Formalism.FourierDecayAlt.Q.RTTAt k (1 + r) ⟨1, by omega⟩ := hU k (1 + r) ⟨0, by omega⟩
    have h := h1 Wp Wq _ _ π₁ π₁' D₁ hw hw' hD₁ f hf _ hιg u v a b c d
    simp only [key] at h
    exact h
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorIdentity
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x2 CardInsertEmbedding

theorem upper_minor_identity : C2.MinorU := by
  intro m w d hd a b hab
  refine ⟨1, Or.inl rfl, fun l hl u' hu => ?_⟩
  have ham : a.val + 1 ≤ m := a.isLt
  have hRc : (C2.wSet w (a.val + 1)).card = a.val + 1 := c2x3_wSet_card w ham
  have hIc : (C2.iSet m (a.val + 1)).card = a.val + 1 := c2x3_iSet_card ham
  have hCc : (insert b (C2.iSet m a.val)).card = a.val + 1 := card_ins b hab (by omega)
  unfold C2.minorS
  rw [dif_pos (hRc.trans hIc.symm), dif_pos (hRc.trans hCc.symm)]
  set eR := (C2.wSet w (a.val + 1)).orderEmbOfFin rfl with heR
  set eI := (C2.iSet m (a.val + 1)).orderEmbOfFin (hRc.trans hIc.symm).symm with heI
  set eC := (insert b (C2.iSet m a.val)).orderEmbOfFin (hRc.trans hCc.symm).symm with heC
  have hI : ∀ t, (eI t).val = t.val := fun t => iemb ham _ t
  have hC : ∀ t, eC t = if ht : t.val < a.val then ⟨t.val, by omega⟩ else b := fun t => cemb b hab _ t
  have hR : ∀ t, ∃ j0 : Fin m, j0.val < a.val + 1 ∧ w j0 = eR t := by
    intro t
    have := Finset.orderEmbOfFin_mem (C2.wSet w (a.val + 1)) rfl t
    obtain ⟨j0, hj0, hw⟩ := Finset.mem_image.mp this
    exact ⟨j0, by simpa [C2.iSet] using hj0, hw⟩
  have hPu := isUnit_det_monomialMatrix w d hd
  set P := C2.monoP w d with hP
  have hPl : l * P = P * (P⁻¹ * l * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
  have hlt := hl.2
  rw [hPl, Matrix.mul_assoc,
    submatrix_monomialMatrix_mul hRc (by omega) w d _ eR eI eC hI hR,
    L_mul_sub (by omega) _ _ (fun i j h => hlt.1 i j h) eI eC hI,
    Matrix.det_mul, Matrix.det_mul, det_lt_sub _ hlt eI hI]
  have hdu : (u'.submatrix eI eC).det = u' a b := by
    rw [Matrix.det_of_upperTriangular]
    · have ht0 : a.val < (C2.wSet w (a.val + 1)).card := by omega
      rw [Finset.prod_eq_single ⟨a.val, ht0⟩]
      · simp only [Matrix.submatrix_apply]
        rw [hC, dif_neg (lt_irrefl _)]
        congr 1
        exact Fin.ext (hI _)
      · intro t _ ht
        have htv : t.val < a.val := by
          have := t.isLt; have : t.val ≠ a.val := fun e => ht (Fin.ext e); omega
        simp only [Matrix.submatrix_apply]
        rw [hC, dif_pos htv]
        have : eI t = ⟨t.val, by omega⟩ := Fin.ext (hI t)
        rw [this]; exact hu.2 _
      · simp
    · intro t s hst
      simp only [id] at hst
      simp only [Matrix.submatrix_apply]
      have hsv : s.val < a.val := by have := t.isLt; rw [Fin.lt_def] at hst; omega
      rw [hC, dif_pos hsv]
      apply hu.1
      rw [Fin.lt_def, hI]; simp only; rw [Fin.lt_def] at hst; exact hst
  rw [hdu]
  ring

end Formalism.FourierDecayAlt.P
end


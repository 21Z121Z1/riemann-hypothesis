import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut.RealInt

open GlobalTheory.RealWeil

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def expM (H s g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((g - 1)ᴴ * (H * s) * (g - 1) - H * g + (H * g)ᴴ)

theorem expM_herm {H s g : Matrix ι ι ℂ} (hQ : (H * s).PosDef) (hd : (g - 1).det ≠ 0) :
    (expM H s g + (expM H s g)ᴴ).PosDef := by
  have e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
    have h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    unfold expM
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  rw [e]
  exact hQ.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))

theorem expM_mul {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) :
    expM H s g * (g * ((1 / 2 : ℂ) • ((1 + s) * g') + (1 / 2 : ℂ) • (1 - s))) = -H * (g - 1) := by
  have hi' : g' * g = 1 := mul_eq_one_comm.1 hi
  have h1 : gᴴ * H = H * g' := by
    calc gᴴ * H = gᴴ * H * g * g' := by rw [Matrix.mul_assoc _ g, hi, Matrix.mul_one]
      _ = _ := by rw [hg]
  have hc' : g' * s = s * g' := by
    calc g' * s = g' * (s * g) * g' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = _ := by rw [hc, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  have a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x) := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x) := fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  have a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x) := fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]
  have a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x := fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x := fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]
  unfold expM
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]
  module

theorem dot_expM {H s g : Matrix ι ι ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef) (z : ι → ℂ) :
    star z ⬝ᵥ expM H s g *ᵥ z = Complex.I * ((-(star z ⬝ᵥ H *ᵥ (g *ᵥ z)).im : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((-(star (Complex.I • s *ᵥ (g *ᵥ z - z)) ⬝ᵥ H *ᵥ (g *ᵥ z - z)).im : ℝ) : ℂ) := by
  have e1 : (g - 1) *ᵥ z = g *ᵥ z - z := by rw [sub_mulVec, one_mulVec]
  have e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) := by
    rw [← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z)) := by
    rw [mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]
  have e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w) := fun w => by
    rw [star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]
    simp
  have e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0 :=
    (Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm
  unfold expM
  rw [smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]
  generalize star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5
  generalize star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w
  apply Complex.ext <;> simp [e5] <;> ring

theorem gauss_det {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    (expM H s g).det⁻¹ * (g - 1).det = ((H * s).det.re⁻¹ : ℝ) * (-s).det * (g.det * dP s g') := by
  have h0 := (GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1
  have h1 := congrArg det (expM_mul hH hs hg hc hi)
  rw [det_mul, det_mul, det_mul] at h1
  have h2 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h3 := hQ.det_pos
  have h4 : ((H * s).det.re : ℂ) = (H * s).det := Complex.ext rfl (Complex.pos_iff.1 h3).2
  rw [Complex.ofReal_inv, h4]
  have h5 := h3.ne'
  unfold dP
  field_simp
  rw [← h2]
  linear_combination (-(-s).det) * h1

end Mat

section Coord

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvE (O : Type) (m n : ℕ) : ((Fin m × Fin n) × O → ℂ) ≃L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse unvecL vecL vecL_unv unv_vecL

omit [DecidableEq O] in

theorem integral_unv (f : (O → Fin m → Fin n → ℂ) → ℂ) (hf : Integrable fun z : (Fin m × Fin n) × O → ℂ => f (unvecL z)) :
    Integrable f ∧ ∃ c : ℝ, 0 < c ∧ ∫ v, f v = c * ∫ z : (Fin m × Fin n) × O → ℂ, f (unvecL z) := by
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := unvE O m n
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)
  have hp := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ))
    (Measure.map e volume)
  generalize Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp
  refine ⟨?_, c, hp, ?_⟩
  · rw [hm]
    exact (he.integrable_map_iff.2 hf).smul_measure_nnreal
  · conv_lhs => rw [hm]
    rw [integral_smul_nnreal_measure, he.integral_map]
    rfl

theorem det_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ).det := det_blockDiagonal _

theorem det_blk_sub_one (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a - 1).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det := by
  unfold RealWeil.blk
  rw [← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]
  rfl

theorem inv_unitary {G a a' : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hi : a * a' = 1) (ha : aᴴ * G * a = G) :
    a * (G⁻¹ * aᴴ) = G⁻¹ := by
  have h1 : a'ᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have h2 : G * a = a'ᴴ * G := by
    conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine (inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]

end Coord

open Classical in
theorem gaussR_unv {D : D7} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hQ : (HM S T * blk sT sS).PosDef)
    (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Ix S T → ℂ) : gaussR S T sS sT a b (unvecL z) =
      Complex.exp (-(Real.pi : ℂ) * (star z ⬝ᵥ expM (HM S T) (blk sT sS) (blk b a) *ᵥ z)) := by
  have e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z) := funext fun τ => (cpt_blk b a z τ).symm
  have e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w) := fun w => funext fun τ => by
    show Complex.I • (sT τ * cpt w τ * sS τ) = _
    rw [← cpt_blk]
    rfl
  unfold gaussR
  rw [dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]
  congr 1
  ring

open Classical in

theorem integral_gaussR : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  intro D S T sS sT hS hT
  refine ⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩
  obtain ⟨hs, hQ⟩ := HM_cartan hS hT
  have hd : (blk b a - 1).det ≠ 0 := by
    rw [det_blk_sub_one]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2
  have hi : blk b a * blk b' a' = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · exact (h τ).2.1
    · exact mul_eq_one_comm.1 (h τ).1
  have hc : blk sT sS * blk b a = blk b a * blk sT sS := by
    rw [blk_mul, blk_mul]
    congr 1 <;> funext τ
    · exact (h τ).2.2.2.2.2.1
    · exact (h τ).2.2.2.2.1.symm
  have hg : (blk b a)ᴴ * HM S T * blk b a = HM S T := by
    unfold HM
    rw [blk_conjTranspose, blk_mul, blk_mul]
    congr 1 <;> funext τ
    · rw [Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]
    · exact inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)
  simp only [← gaussR_unv hQ] at h1 h2
  obtain ⟨h3, c, hc0, h4⟩ := integral_unv _ h1
  refine ⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩
  rw [h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk,
    ← detPlus_blockDiagonal, Complex.ofReal_mul]
  ring

end GlobalTheory.RatAut.RealInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDua
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

section Perm

variable {p q n : ℕ} {ε : Fin n → Bool}

def permFrame (e : Fin p ⊕ Fin q ≃ Fin n) : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
  (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix id e.symm

theorem mul_permFrame (e : Fin p ⊕ Fin q ≃ Fin n) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    X * permFrame e = X.submatrix id e.symm := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply]

theorem permFrame_conjTranspose_mul (e : Fin p ⊕ Fin q ≃ Fin n) (Y : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) :
    (permFrame e)ᴴ * Y = Y.submatrix e.symm id := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem permFrame_herm {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e) :
    (permFrame e)ᴴ * Formalism.UG.Jpq p q * permFrame e = Formalism.REAL.Jm ε := by
  rw [Matrix.mul_assoc, mul_permFrame, permFrame_conjTranspose_mul, ← h.reindex_Jpq, Matrix.reindex_apply,
    Matrix.submatrix_submatrix]
  rfl

theorem frameInv_permFrame {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e)
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    frameInv ε (permFrame e) * X * permFrame e = Matrix.reindex e e X := by
  have : frameInv ε (permFrame e) * X * permFrame e =
      Formalism.REAL.Jm ε * ((permFrame e)ᴴ * (Formalism.UG.Jpq p q * X * permFrame e)) := by
    simp only [frameInv, Matrix.mul_assoc]
  rw [this, mul_permFrame, permFrame_conjTranspose_mul, Matrix.submatrix_submatrix,
    show (e.symm ∘ id : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    show (id ∘ e.symm : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    ← Matrix.submatrix_mul_equiv (Formalism.UG.Jpq p q) X e.symm e.symm e.symm,
    ← Matrix.reindex_apply, h.reindex_Jpq, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul,
    Matrix.reindex_apply]

end Perm

theorem map_frameEquiv_cd (cd : CDHaar) {p q n : ℕ} {ε : Fin n → Bool} (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) :
    (cd.cd p q).map (frameEquiv B hB hn) = (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
  classical
  let e₀ : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let ε₀ : Fin n → Bool := fun i => (e₀.symm i).isLeft
  have h₀ : Sorts ε₀ e₀ := ⟨fun i => by simp [ε₀], fun j => by simp [ε₀]⟩
  have hC : (B.submatrix e₀.symm id)ᴴ * Formalism.REAL.Jm ε₀ * B.submatrix e₀.symm id = Formalism.REAL.Jm ε := by
    rw [← h₀.reindex_Jpq, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hB]
    rfl
  have hcount : Nat.card {a // ε a = true} = p := (GlobalTheory.SignCount.card_true_eq _ hC).symm.trans h₀.card_true
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  have hP : P = p := he.card_true.symm.trans hcount
  have hQ : Q = q := by have := Sorts.add_eq e; omega
  subst hP hQ
  have hBp := permFrame_herm he
  have hfun : (frameEquiv (permFrame e) hBp hn : UpqT P Q → Formalism.REAL.UJ ε) = he.equiv := funext fun b =>
    umat_injective (by rw [umat_frameEquiv, frameInv_permFrame he, he.umat_equiv])
  have hmap0 : (cd.cd P Q).map (frameEquiv (permFrame e) hBp hn) =
      (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
    rw [hfun]
    ext A hA
    rw [Measure.map_apply he.measurable_equiv hA, ← he.set_eq]
    exact (cdScaleIs_trueScale cd n ε P Q e he.1 he.2 A hA).symm
  exact map_frameEquiv hBp hB hn (cd.cd P Q) _ hmap0

end GlobalTheory.LowRow.CompactDualCoef

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

theorem inv_integral_coef_sq : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  intro hHC cd D W S M Fr hFr hsig ρ hanti hhalf w hw
  classical
  haveI : BorelSpace (Upq W ρ) := ⟨rfl⟩
  have hn := hsig ρ
  have hmap := map_frameEquiv_cd cd _ (frame_herm M hFr ρ) hn
  have hme : MeasurableEmbedding (frameEquiv _ (frame_herm M hFr ρ) hn) :=
    (frameEquiv _ (frame_herm M hFr ρ) hn).toHomeomorph.measurableEmbedding
  have hk : (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) =
      (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘ frameEquiv _ (frame_herm M hFr ρ) hn :=
    funext fun b => by simp only [Function.comp_apply, rep_realMat M hFr ρ hn b]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpr := hHC cd (trueScale cd) (cdScaleIs_trueScale cd) W.rank (M.ε ρ) (M.lam ρ) ⟨hanti, hhalf⟩ (M.H ρ)
    (M.σ ρ) w (M.ds ρ) hw0
  rw [hw, one_pow, one_div] at hpr
  have hpos : 0 < (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) /
      ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
      (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    · exact abs_pos.2 (sub_ne_zero.2 (hanti.injective.ne (ne_of_lt (Finset.mem_filter.1 hb).2)))
    · have := (Finset.mem_filter.1 hb).2
      exact sub_pos.2 (by exact_mod_cast this)
  have hint : Integrable (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2)
      ((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) := by
    by_contra hni
    rw [integral_undef hni, _root_.inv_zero] at hpr
    exact hpos.ne hpr
  rw [← hmap] at hint
  rw [hk]
  refine ⟨hme.integrable_map_iff.1 hint, ?_⟩
  rw [show (∫ b, ((fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘
      frameEquiv _ (frame_herm M hFr ρ) hn) b ∂(cd.cd _ _)) =
      ∫ g, ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2 ∂((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) by
    rw [← hmap, hme.integral_map]; rfl]
  exact hpr

end GlobalTheory.LowRow.CompactDualCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_apply_of_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    {σ : ι} (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i k
  simp only [shear, Matrix.add_apply, Matrix.of_apply]
  rw [if_neg, add_zero]
  rintro ⟨h1, -⟩
  exact h (congrArg Sigma.fst h1)

theorem shear_self_mul_apply {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    (A : Matrix (Fin (m τ)) (Fin (m τ)) K) (i c : Fin (m τ)) :
    (shear τ a b t τ * A) i c = A i c + if i = a then t * A b c else 0 := by
  have e : ∀ k, shear τ a b t τ i k = (1 : Matrix (Fin (m τ)) (Fin (m τ)) K) i k + if i = a ∧ k = b then t else 0 := by
    intro k
    simp only [shear, Matrix.add_apply, Matrix.of_apply]
    congr 1
    by_cases h1 : i = a <;> by_cases h2 : k = b <;> simp [h1, h2]
  rw [Matrix.mul_apply]
  simp only [e, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h1 : i = a <;> simp [h1]

theorem almostLow_of_shear : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L,
      Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  intro ι m τ a b hab L K _ _ j t ht C hP
  have hmap : ∀ σ i c, (C.map j) σ i c = j (C σ i c) := fun _ _ _ => rfl
  have hL : ∀ σ, shear τ a b t σ * (C.map j) σ = (shear τ a b t * C.map j) σ := fun _ => rfl
  have hz : ∀ σ (i c : Fin (m σ)), i < c → (shear τ a b t σ * (C.map j) σ) i c = 0 := fun σ i c h => by
    rw [hL]; exact (hP σ).2.2.2 i c i.isLt h
  have hd : ∀ σ, (shear τ a b t σ * (C.map j) σ).det ≠ 0 := fun σ => by rw [hL]; exact (hP σ).2.1
  have hdiag : ∀ σ (i : Fin (m σ)), (shear τ a b t σ * (C.map j) σ) i i ≠ 0 := fun σ i => by
    have hbt : (shear τ a b t σ * (C.map j) σ).BlockTriangular OrderDual.toDual := fun p q hpq =>
      hz σ p q (OrderDual.toDual_lt_toDual.1 hpq)
    have := hd σ
    rw [Matrix.det_of_lowerTriangular _ hbt] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have hba : b ≠ a := ne_of_gt hab'
  refine ⟨fun σ hσ => hd σ ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Mat.det_map, hσ, map_zero, mul_zero]
  · intro h0
    have h1 := hz τ a b hab'
    have h2 := hdiag τ b
    rw [shear_self_mul_apply] at h1 h2
    rw [if_pos rfl, hmap, h0, map_zero, zero_add] at h1
    rw [if_neg hba, add_zero] at h2
    exact h2 ((mul_eq_zero.1 h1).resolve_left ht)
  · intro σ i c hic hn
    refine (map_eq_zero j).1 ?_
    rw [← hmap]
    by_cases hσ : σ = τ
    · subst hσ
      have hn' : ¬ (i = a ∧ c = b) := fun h => hn ⟨by rw [h.1], by rw [h.2]⟩
      have h1 := hz σ i c hic
      rw [shear_self_mul_apply] at h1
      by_cases hi : i = a
      · subst hi
        have hcb : c ≠ b := fun h => hn' ⟨rfl, h⟩
        have hbc : b < c := by
          rw [Fin.lt_def] at hic ⊢
          have : (c : ℕ) ≠ b := fun h => hcb (Fin.ext h)
          omega
        have h2 := hz σ b c hbc
        rw [shear_self_mul_apply, if_neg hba, add_zero] at h2
        rw [if_pos rfl, h2, mul_zero, add_zero] at h1
        exact h1
      · rw [if_neg hi, add_zero] at h1
        exact h1
    · have h1 := hz σ i c hic
      rw [shear_apply_of_ne τ a b t hσ, one_mul] at h1
      exact h1

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_res | exact GlobalTheory.LogPair.isEtCoord_res | (intros; apply GlobalTheory.LogPair.isEtCoord_res <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianNondegenerateNegTraceZeroSmulInvSkewHStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHermitianNondegenerate_neg_traceZero_smul_inv_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = -J i j) → IsUnit J.det → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
    IsHermND σ (-ξ₀ • J⁻¹) := by
  first | exact @GlobalTheory.skew_dual_isHermND | exact GlobalTheory.skew_dual_isHermND | (intros; apply GlobalTheory.skew_dual_isHermND <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
section
noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.KSplit

namespace GlobalTheory.JacLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk3 (a b : ℕ) : Fin 1 ⊕ Fin (a + b) ⊕ Fin 1 ≃ Fin (a + (b + 2)) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by omega))

def IsJacMap (a b : ℕ) (α β : kˣ →* ℂˣ) (χ₁ χ₂ : kˣ → ℂ) (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) : Prop :=
  (∀ (u : GL (Fin (a + (b + 2))) k) (X : Matrix (Fin 1) (Fin (a + b) ⊕ Fin 1) k) (Y : Matrix (Fin (a + b)) (Fin 1) k),
      u.val.submatrix (blk3 a b) (blk3 a b) = fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * u)) →
        φ f₁ = φ f) ∧
  ∀ (m : GL (Fin (a + (b + 2))) k) (x y : kˣ) (g : GL (Fin (a + b)) k),
      m.val.submatrix (blk3 a b) (blk3 a b) =
        fromBlocks (of fun _ _ => (x : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : k))) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * m)) →
        ∀ h, (φ f₁ : GL (Fin (a + b)) k → ℂ) h = χ₁ x * χ₂ y * (φ f : GL (Fin (a + b)) k → ℂ) (h * g)

end GlobalTheory.JacLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrixStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 → L.IsLattice E →
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  first | exact @GlobalTheory.isLattice_comap_mulVecLin_of_leftInverse | exact GlobalTheory.isLattice_comap_mulVecLin_of_leftInverse | (intros; apply GlobalTheory.isLattice_comap_mulVecLin_of_leftInverse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFinStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyBlockUnitary_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  first | exact @GlobalTheory.HoweR.locU_pi_fin | exact GlobalTheory.HoweR.locU_pi_fin | (intros; apply GlobalTheory.HoweR.locU_pi_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpaceStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  first | exact @GlobalTheory.isUnit_det_of_isHerm | exact GlobalTheory.isUnit_det_of_isHerm | (intros; apply GlobalTheory.isUnit_det_of_isHerm <;> assumption)
end


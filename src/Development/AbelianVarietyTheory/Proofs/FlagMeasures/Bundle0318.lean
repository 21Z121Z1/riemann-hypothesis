import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0213
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HalfTruncatedLeastLatticeSizeLeUnipotentNeighbou
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.OmegaLeast

open scoped Matrix.Norms.L2Operator in

theorem opNorm_le_sqrt_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ≤ Real.sqrt (Formalism.REAL.hs A) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hhs : 0 ≤ Formalism.REAL.hs A := by unfold Formalism.REAL.hs; positivity
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul hhs]
  apply Real.sqrt_le_sqrt
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
  refine le_trans ?_ h2
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

open scoped Matrix.Norms.L2Operator in

theorem opNorm_exp_le {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := GlobalTheory.LeastVar.opN_one hn
  haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := ⟨h1⟩
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A
  have h' := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ‖A‖
  rw [Real.exp_eq_exp_ℝ]
  refine h.norm_le_of_bounded h' fun k => ?_
  rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, norm_smul, smul_eq_mul]
  gcongr
  · simp
  · exact norm_pow_le _ _

open scoped Matrix.Norms.L2Operator in
theorem dOp_exp_mul_exp_le {n : ℕ} (hn : 1 ≤ n) (A Z : Matrix (Fin n) (Fin n) ℂ) :
    dOp (NormedSpace.exp A * NormedSpace.exp Z) ≤
      Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z) := by
  have h : ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤
      Real.exp (Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z)) := by
    rw [Real.exp_add]
    refine (norm_mul_le _ _).trans ?_
    gcongr
    · exact (opNorm_exp_le hn A).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs A))
    · exact (opNorm_exp_le hn Z).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs Z))
  change Real.log ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤ _
  rcases (norm_nonneg (NormedSpace.exp A * NormedSpace.exp Z)).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; positivity
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem half_truncatedLeastLatticeSize_le_unipotentNeighbourhood : ∀ (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ), 1 ≤ I.n → ρ ≤ Real.log 2 → ∀ y ∈ omega I x W ρ, tau1 I x / 2 ≤ tau1 I y := by
  intro I x W ρ hn hρ y hy
  obtain ⟨h2, A, Z, -, hAZ, hy1, -⟩ := hy
  obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hk : (x⁻¹ * y).2 ∈ I.Kset := by
    have : (x⁻¹ * y).2 = 1 := by simp [h2]
    rw [this, ← hK]; exact K.one_mem
  have hv := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x (x⁻¹ * y) hk
  rw [mul_inv_cancel_left] at hv
  have hcard := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.1
  have hfpos : (0 : ℝ) < I.f := by
    rw [← hcard]; exact_mod_cast Fintype.card_pos
  have hhs : ∀ B : Matrix (Fin I.n) (Fin I.n) ℂ, 0 ≤ Formalism.REAL.hs B := fun B => by
    unfold Formalism.REAL.hs; positivity
  have hd : ∀ v, dOp (uMat ((x⁻¹ * y).1 v)) ≤ Real.log 2 := by
    intro v
    have e : uMat ((x⁻¹ * y).1 v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
      have e1 : uMat ((x⁻¹ * y).1 v) = uMat ((x.1 v)⁻¹) * uMat (y.1 v) := by simp [uMat]
      have e2 : uMat ((x.1 v)⁻¹) * uMat (x.1 v) = 1 := by simp [uMat]
      rw [e1, hy1 v, Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    rw [e]
    refine (dOp_exp_mul_exp_le hn _ _).trans (le_trans ?_ (hAZ.trans hρ))
    gcongr
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (A v)) (fun v _ => hhs _) (Finset.mem_univ v)
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (Z v)) (fun v _ => hhs _) (Finset.mem_univ v)
  have hs : (∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f ≤ Real.log 2 := by
    rw [div_le_iff₀ hfpos]
    refine (Finset.sum_le_sum fun v _ => hd v).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_comm]
  have he : (1 / 2 : ℝ) ≤ Real.exp (-((∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f)) := by
    have : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [this]
    exact Real.exp_le_exp.2 (neg_le_neg hs)
  have ht : 0 ≤ tau1 I x := by
    obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
    haveI := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).1
    have hx := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.2.2
    have hne : lamX I x ≠ ⊥ := by
      intro h
      haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      rw [h] at hspan
      simp at hspan
    have h3 := (sizeMu I.E _ _ (bas I) (frm I x) (fun w => (hx w).1) (lamX I x) hfg hne).2.2.2.1
    unfold tau1 least
    rw [h3]
    exact le_min (by norm_num) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left he ht
  linarith

end GlobalTheory.OmegaLeast
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImageRationalOrthComplementUnitaryEqRationalStab
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold.RatPts

open GlobalTheory.RatDiscrete

theorem eq_map_of_resolution {E R : Type} [CommRing E] [CommRing R] (ι : E →+* R) {n m : ℕ}
    {x u : Fin n → E} {A : Matrix (Fin n) (Fin m) E} {A' : Matrix (Fin m) (Fin n) E}
    (h : vecMulVec x u + A * A' = 1) (M : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) E)
    (hx : M *ᵥ (fun i => ι (x i)) = fun i => ι (x i)) (hA : M * A.map ι = A.map ι * g.map ι) :
    M = (vecMulVec x u + A * g * A').map ι := by
  have h1 : (vecMulVec x u + A * A').map ι = 1 := by
    rw [h]; exact Matrix.map_one ι (map_zero ι) (map_one ι)
  have hvm : ∀ y w : Fin n → E, (vecMulVec y w).map ι = vecMulVec (fun i => ι (y i)) (fun i => ι (w i)) := by
    intro y w; ext i j; simp [vecMulVec_apply]
  have key : M * vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) =
      vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) := by
    ext i j
    have hi := congrFun hx i
    simp only [mulVec, dotProduct] at hi
    simp only [mul_apply, vecMulVec_apply]
    rw [← hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
  calc M = M * (vecMulVec x u + A * A').map ι := by rw [h1, Matrix.mul_one]
    _ = (vecMulVec x u + A * g * A').map ι := by
      rw [Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hvm,
        Matrix.mul_add, key, ← Matrix.mul_assoc, hA]

theorem exists_isImage (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA, IsImage I γ a := by
  have hU : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have hG : ∀ v, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
    intro v
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map (I.φ v)) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    exact (I.cm.cmUnram.2.1 (I.φ v) _).symm
  have hR : ∀ v, Formalism.REAL.inUJ (I.ε v)
      ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) := by
    intro v
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hdH : IsUnit (I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
    unfold Formalism.REAL.inUJ
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)ᴴ)⁻¹ (I.P v)ᴴ, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG v]
  have hC : ∀ v (X Y : Matrix (Fin I.n) (Fin I.n) ℂ),
      ((I.P v)⁻¹ * X * I.P v) * ((I.P v)⁻¹ * Y * I.P v) = (I.P v)⁻¹ * (X * Y) * I.P v := by
    intro v X Y
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hE : ∀ v (X : Matrix (Fin I.n) (Fin I.n) I.E) (Y : Matrix (Fin I.n) (Fin I.n) I.E), X * Y = 1 →
      ((I.P v)⁻¹ * X.map (I.φ v) * I.P v) * ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v) = 1 := by
    intro v X Y hXY
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    rw [hC, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hd]
  let ι := Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)
  have hF : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι) *
      I.J.map ι * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι = I.J.map ι := by
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map ι) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [ι, Formalism.UG.cT, Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  let af : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := Units.map (RingHom.mapMatrix ι).toMonoidHom γ
  have haf : af ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    exact hF
  refine ⟨(fun v => ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      hE v _ _ (Units.mul_inv γ), hE v _ _ (Units.inv_mul γ)⟩, hR v⟩, ⟨af, haf⟩), fun v => rfl, rfl⟩

theorem isImage_embA {I : AutInst} (D : Sib I) {x u : Fin I.n → I.E} {A : Matrix (Fin I.n) (Fin D.n) I.E}
    {A' : Matrix (Fin D.n) (Fin I.n) I.E} (h : vecMulVec x u + A * A' = 1)
    {jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)} {jf : D.inst.Gf →* I.Gf}
    (hv : IsInfEmb D x A jv) (hf : IsFinEmb D x A jf) {γ : Matrix (Fin D.n) (Fin D.n) I.E} {g : D.inst.GA}
    (hg : IsImage D.inst γ g) : IsImage I (vecMulVec x u + A * γ * A') (embA D jv jf g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun v => ?_, ?_⟩
  · have hPu := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hDu := (Matrix.isUnit_iff_isUnit_det _).mp (D.P_unit v)
    obtain ⟨h1, h2⟩ := hv v (g.1 v)
    have hxv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (x i)) =
        fun i => I.φ v (x i) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change I.P v *ᵥ (uMat (jv v (g.1 v)) *ᵥ infVec I v x) = _
      rw [h1, infVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have key : I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v =
        A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
      calc I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v
          = I.P v * (uMat (jv v (g.1 v)) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v)) := by
            simp only [Matrix.mul_assoc]
        _ = I.P v * (((I.P v)⁻¹ * A.map (I.φ v) * D.P v) *
            ((D.P v)⁻¹ * γ.map (I.φ v) * D.P v)) :=
            congrArg (I.P v * ·) (h2.trans (congrArg (infMat D v A * ·) (hg1 v)))
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (D.P v) (D.P v)⁻¹, Matrix.mul_nonsing_inv _ hDu, Matrix.one_mul,
              ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    have hAv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) =
        A.map (I.φ v) * γ.map (I.φ v) := by
      calc (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v)
          = (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) * D.P v * (D.P v)⁻¹ := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v * (D.P v)⁻¹ := by rw [key]
        _ = A.map (I.φ v) * γ.map (I.φ v) := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
    have hM := eq_map_of_resolution (I.φ v) h (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) γ hxv hAv
    change uMat (jv v (g.1 v)) = _
    rw [← hM]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul]
  · change I.fmat (jf g.2) = _
    exact eq_map_of_resolution (Formalism.UG.inclE (F := I.F) (Af I.F)) h (I.fmat (jf g.2)) γ (hf g.2).1
      ((hf g.2).2.trans (congrArg (afMat I A * ·) hg2))

theorem inclE_injective (I : AutInst) :
    Function.Injective (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) := by
  have hnf : ¬ IsField (𝓞 I.F) := by
    exact NumberField.RingOfIntegers.not_isField I.F
  obtain ⟨p, hp0, hpp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) := ⟨p, hpp, hp0⟩
  have : Nontrivial (Af I.F) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg (fun a : Af I.F => (a.1 v : v.adicCompletion I.F)) h)⟩⟩
  intro a b hab
  exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (A := I.E) (B := Af I.F)
    (RingHom.injective _) hab

end GlobalTheory.StabUnfold.RatPts

namespace GlobalTheory.StabUnfold

open GlobalTheory.RatDiscrete RatPts

theorem image_rational_eq_stab : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  intro I D s x A xf hP jv jf hv hf
  obtain ⟨hn, hβ, hxA, hAJ, -, -⟩ := hP
  have hJ : I.Jᴴ = I.J := by
    have hh := I.J_herm
    unfold Formalism.UG.IsHerm at hh
    ext i j
    have hij := congrFun (congrFun hh i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
    rw [Matrix.conjTranspose_apply]
    exact hij
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]; cases s <;> simp [GlobalTheory.GaussMean.sgn]
  obtain ⟨u, A', hA'A, hA'x, huA, hux, hres, hAJx⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ
  obtain ⟨j, hjv, hjr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer I.E (starRingEnd I.E) I.n D.n I.J D.J x u A A'
    (isUnit_iff_ne_zero.mpr hβ0) hxA hAJx hAJ hA'A hA'x huA hux hres
  ext y
  constructor
  · rintro ⟨g, ⟨γ, hγ, hg1, hg2⟩, rfl⟩
    have hIm := isImage_embA D hres hv hf (γ := (γ : Matrix (Fin D.n) (Fin D.n) I.E)) (g := g) ⟨hg1, hg2⟩
    have hj := hjv ⟨γ, hγ⟩
    refine ⟨⟨(j ⟨γ, hγ⟩ : GL (Fin I.n) I.E), (j ⟨γ, hγ⟩).2, ?_⟩, (hf g.2).1⟩
    change IsImage I _ _
    rw [hj]
    exact hIm
  · rintro ⟨⟨δ, hδ, hy1, hy2⟩, hyx⟩
    have h3 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) i)) =
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := by
      rw [← GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.map_mulVec_incl, ← hy2]
      exact hyx
    have hδx : (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = x := by
      funext i
      exact inclE_injective I (congrFun h3 i)
    obtain ⟨γ₀, hγ₀⟩ := hjr ⟨δ, hδ⟩ hδx
    obtain ⟨g, hg⟩ := exists_isImage D.inst (γ₀ : GL (Fin D.n) I.E) γ₀.2
    refine ⟨g, ⟨(γ₀ : GL (Fin D.n) I.E), γ₀.2, hg.1, hg.2⟩, ?_⟩
    have hIm := isImage_embA D hres hv hf hg
    have hM : vecMulVec x u + A * ((γ₀ : GL (Fin D.n) I.E) : Matrix (Fin D.n) (Fin D.n) I.E) * A' =
        (δ : Matrix (Fin I.n) (Fin I.n) I.E) := by
      rw [← hjv γ₀, hγ₀]
    rw [hM] at hIm
    exact subsingleton_isImage I _ hIm ⟨hy1, hy2⟩

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfinitesimalCharacterExtension
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.InfCharExt

variable {n : ℕ}

theorem kset_sub_ujset (ε : Fin n → Bool) : ∀ g ∈ Kset ε, g ∈ UJset ε := by
  intro g hg
  obtain ⟨hu, hc⟩ := hg
  show gᴴ * Jm ε * g = Jm ε
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc]
  rw [show gᴴ = star g from rfl, h1, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem ext_eq_on_su {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) : ∀ g ∈ SUset ε, π g = π' g := by
  intro g hg
  have := hE 1 (by simp) g hg
  simpa using this

theorem kfin_to_kfinS {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) {v : H} (hv : IsKFin ε π v) : IsKFinS ε π' v := by
  obtain ⟨S, hS, hvS, hst⟩ := hv
  refine ⟨S, hS, hvS, ?_⟩
  intro g hg x hx
  have hgS : g ∈ SUset ε := ⟨kset_sub_ujset ε g hg.1, hg.2⟩
  rw [← ext_eq_on_su hE g hgS]
  exact hst g hg.1 x hx

theorem coeff_shift {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hE : Ext ε m π' π) (v w : H) :
    ∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, (fun g => ⟪w, π g v⟫_ℂ) (z • g) = z ^ m * (fun g => ⟪w, π' g v⟫_ℂ) g := by
  intro z hz g hg
  simp only
  rw [hE z hz g hg, ContinuousLinearMap.smul_apply, inner_smul_right]

end GlobalTheory.InfCharExt

theorem GlobalTheory.infChar_of_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π →
    ∀ χ : Fin n → ℂ, HasInfCharS ε χ π' → HasInfChar ε (fun a => χ a + (m : ℂ) / n) π := by
  intro n hn ε H _ _ m π' π hE χ hχ v w hv hw
  have hv' := GlobalTheory.InfCharExt.kfin_to_kfinS hE hv
  have hw' := GlobalTheory.InfCharExt.kfin_to_kfinS hE hw
  obtain ⟨hsm, heig⟩ := hχ v w hv' hw'
  obtain ⟨hG1, hG2⟩ := GlobalTheory.T.gelfand_operator_extension n hn ε m (fun g => ⟪w, π g v⟫_ℂ) (fun g => ⟪w, π' g v⟫_ℂ)
    (GlobalTheory.InfCharExt.coeff_shift hE v w) hsm
  refine ⟨hG1, ?_⟩
  intro k g hg
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
  obtain ⟨hval, hval0, -⟩ := GlobalTheory.T.gelfand_values_shift n χ
  rw [hG2 k z hz g₀ hg₀, GlobalTheory.InfCharExt.coeff_shift hE v w z hz g₀ hg₀, hval]
  conv_rhs => rw [Finset.sum_range_succ', hval0]
  have hS : ∀ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) *
      gelfS ε j (fun g => ⟪w, π' g v⟫_ℂ) g₀ =
      ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k + 1 - (j + 1)) * gelfVal χ (j + 1) *
        ⟪w, π' g₀ v⟫_ℂ := by
    intro j _
    rw [heig j g₀ hg₀, Nat.add_sub_add_right]
    ring
  rw [Finset.sum_congr rfl hS, ← Finset.sum_mul]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnfoldKernel
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.AdelicUnfold

theorem unfold_smul {Γ X : Type} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
    [MeasurableConstSMul Γ X] (μ : Measure X) [SMulInvariantMeasure Γ X μ] {s : Set X}
    (hs : IsFundamentalDomain Γ s μ) (f : X → ℂ) (hf : Integrable f μ) :
    IntegrableOn (fun z => ∑' γ : Γ, f (γ • z)) s μ ∧
      ∫ z, f z ∂μ = ∫ z in s, ∑' γ : Γ, f (γ • z) ∂μ := by
  classical
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun z => f (γ • z)) μ := fun γ =>
    hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul γ μ)
  have hfin : ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ ≠ ⊤ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have hae : ∀ᵐ z ∂μ.restrict s, ∑' γ : Γ, ‖f (γ • z)‖ₑ < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).restrict.enorm)
    rw [lintegral_tsum fun γ => (hmeas γ).restrict.enorm]
    exact hfin
  have hsm : ∀ᵐ z ∂μ.restrict s, Summable fun γ : Γ => f (γ • z) := by
    filter_upwards [hae] with z hz
    exact Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.1 hz.ne)
  have hasm : AEStronglyMeasurable (fun z => ∑' γ : Γ, f (γ • z)) (μ.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset Γ)))
      (f := fun t z => ∑ γ ∈ t, f (γ • z)) (fun t => ?_) ?_
    · convert Finset.aestronglyMeasurable_sum t (fun γ _ => (hmeas γ).restrict) using 1
      ext z
      simp [Finset.sum_apply]
    · filter_upwards [hsm] with z hz using hz.hasSum
  refine ⟨⟨hasm, ?_⟩, ?_⟩
  · calc ∫⁻ z in s, ‖∑' γ : Γ, f (γ • z)‖ₑ ∂μ ≤ ∫⁻ z in s, ∑' γ : Γ, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_tsum fun γ => (hmeas γ).restrict.enorm
      _ < ⊤ := hfin.lt_top
  · rw [integral_tsum (fun γ => (hmeas γ).restrict) hfin]
    exact hs.integral_eq_tsum'' f hf

theorem measurePreserving_left (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (g : I.GA) : MeasurePreserving (fun z => g * z) (I.muA μf) (I.muA μf) := by
  unfold AutInst.muA
  have h0 : ∀ v, (muG (I.ε v)).IsMulLeftInvariant := fun v => inferInstance
  have h1 : (Measure.pi fun v => muG (I.ε v)).IsMulLeftInvariant := inferInstance
  have h2 : ((Measure.pi fun v => muG (I.ε v)).prod μf).IsMulLeftInvariant := inferInstance
  exact measurePreserving_mul_left _ g

theorem integral_unfold_kernel : ∀ (B : RowsAut) (φ F : B.I.GA → ℂ) (x : B.I.GA), (∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, F (γ * z) = F z) → Integrable (fun g => φ g * F (x * g)) (B.I.muA B.μf) → IntegrableOn (fun z => kern B.I φ x z * F z) B.fund (B.I.muA B.μf) ∧ ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z in B.fund, kern B.I φ x z * F z ∂(B.I.muA B.μf) := by
  intro B φ F x hF hint
  have := B.haar
  have := B.sf
  have hcount : Countable (GlobalTheory.RatDiscrete.ratSub B.I) := by
    have := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    exact this
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA :=
    ⟨fun γ => (measurePreserving_left B.I B.μf γ.1).measurable⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun γ A hA => (measurePreserving_left B.I B.μf γ.1).measure_preimage hA.nullMeasurableSet⟩
  have hfd : IsFundamentalDomain (GlobalTheory.RatDiscrete.ratSub B.I) B.fund (B.I.muA B.μf) :=
    GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec

  have hh : Integrable (fun z => φ (x⁻¹ * z) * F z) (B.I.muA B.μf) := by
    have := ((measurePreserving_left B.I B.μf x⁻¹).integrable_comp hint.aestronglyMeasurable).2 hint
    convert this using 1
    ext z
    simp [Function.comp, mul_inv_cancel_left]
  have hB : ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z, φ (x⁻¹ * z) * F z ∂(B.I.muA B.μf) := by
    have hmp := measurePreserving_left B.I B.μf x
    have e := integral_map hmp.measurable.aemeasurable
      (f := fun z => φ (x⁻¹ * z) * F z) (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    rw [hmp.map_eq] at e
    rw [e]
    congr 1
    ext g
    simp [inv_mul_cancel_left]

  have hD : (fun z => ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I, φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z))
      =ᵐ[(B.I.muA B.μf).restrict B.fund] fun z => kern B.I φ x z * F z := by
    filter_upwards [ae_restrict_of_ae (s := B.fund) hF] with z hz
    unfold kern
    have hγ : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z) = φ (x⁻¹ * γ.1 * z) * F z := fun γ => by
      rw [hz γ.1 γ.2, mul_assoc]
    rw [tsum_congr hγ, tsum_mul_right]
    rfl
  obtain ⟨hI, hE⟩ := unfold_smul (B.I.muA B.μf) hfd (fun z => φ (x⁻¹ * z) * F z) hh
  refine ⟨hI.congr hD, ?_⟩
  rw [hB, hE]
  exact integral_congr_ae hD

end GlobalTheory.AdelicUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModuleStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_transports_discriminantModule : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  first | exact @GlobalTheory.Mass.Transp.discModule_transport | exact GlobalTheory.Mass.Transp.discModule_transport | (intros; apply GlobalTheory.Mass.Transp.discModule_transport <;> assumption)
end


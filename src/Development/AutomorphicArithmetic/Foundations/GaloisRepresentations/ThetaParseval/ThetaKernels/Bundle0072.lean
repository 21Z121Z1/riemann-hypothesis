import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FrameArchimedeanPairing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0068
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0053
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0061
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0007
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0052
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0069
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0060
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GenDictXOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0054
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0048
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0065
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpPsiPf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Psi
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem psi_tt_arch_k (M : Mx F E d.n d.n) (hM : finOne F • M = 0) :
    d.B.ψ (d.tt M) = Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ w, 2 * ((d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hf : finOne F • M.trace = 0 := by rw [← Matrix.trace_smul, hM, Matrix.trace_zero]
  have hf' : finOne F * d.tt M = 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt
    rw [← smul_eq_mul, ← LinearMap.map_smul, hf, map_zero]
  rw [d.std.2.2 _ (Place.at_of_finOne hf'), Dense.trace_evI d.cm.1]
  congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt
  rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm]
  have : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
  rw [this, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring
theorem cw_realAd_k (w : InfinitePlace F) {p q : Type} (t : ℝ) (Y : Matrix p q (AE F E)) :
    d.cw w (realAd F t • Y) = (t : ℂ) • d.cw w Y := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, GlobalTheory.RealScalar.piInf_realAd_smul]
theorem tw_spec_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) :
    finOne F • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W = 0 ∧ ∀ w, d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W :=
  (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_tw_k R W).choose_spec
theorem sg_sq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
theorem cw_gram_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) (w : InfinitePlace F) :
    d.cw w (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X) =
      (-(t : ℂ)) • ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_realAd_k, (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.tw_spec_k R W).2, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w W, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w X]
  have h3 : ((R.fr w).1 * (Matrix.of (R.loc w X)).map star).map star = (R.fr w).1.map star * Matrix.of (R.loc w X) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h3]
  have hz := _root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R
  have e := _root_.PositivityTheory.SiegelWeilFormula.KW.frJ_k R w
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.transpose_mul]
  calc _ = ((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • (((Matrix.of (R.loc w W)).map star)ᵀ *
        ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of (R.loc w X)) := by
        rw [smul_smul]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
        have h4 : ((Matrix.of (R.loc w W)).map star)ᵀ = (Matrix.of (R.loc w W))ᴴ := rfl
        rw [h4]
        congr 1
        field_simp
        linear_combination (-(t : ℂ)) * _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.sg_sq_k R w
theorem re_trace_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (W X : Mx F E d.m d.n) :
    (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)).trace).re =
      ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]
theorem inner_arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W X : Mx F E d.m d.n) :
    ⟪_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X⟫_ℝ =
      ∑ w, ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, PiLp.inner_apply, EuclideanSpace.equiv, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp
  ring
theorem fin_gram_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    finOne F • d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X = 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, smul_comm, (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.tw_spec_k R W).1]
  simp
theorem spf_eq_k (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d x y = Algebra.trace (AF F) (AE F E)
      (-(xᵀ * incM F d.A.J * y.map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k symp
  rw [hTens_trace, neg_one_mul]
theorem trace_evI_trace_k (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (d.B.emb w) z).re := by
  rw [Dense.trace_evI d.cm.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring
theorem psi_neg_half_trace_k (z : AE F E) (hz : finOne F • z = 0) :
    d.B.ψ (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) z)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((-(∑ w, (piInf (d.B.emb w) z).re) : ℝ) : ℂ)) := by
  have hf : finOne F * Algebra.trace (AF F) (AE F E) z = 0 := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, hz, map_zero]
  have hf' : finOne F * -(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) z) = 0 := by
    rw [mul_neg, mul_left_comm, hf, mul_zero, neg_zero]
  rw [d.std.2.2 _ (Place.at_of_finOne hf')]
  congr 3
  have e : evI F (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) z)) =
      -(algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) * evI F (Algebra.trace (AF F) (AE F E) z)) := by
    rw [← evI_half, ← Dense.evI_mul]
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
  rw [e, map_neg, ← Algebra.smul_def, LinearMap.map_smul, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.trace_evI_trace_k, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [invOf_eq_inv]
  ring
theorem frame_hermForm_real_sign (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 *
      ((d.b.1.toCols₁).map (d.B.emb w).1).map star = (((R.ε : ℤ) : ℂ)) • 1 := by
  have h := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have cst : (d.b.1.map σ).map (d.B.emb w).1 = (d.b.1.map (d.B.emb w).1).map star := by
    ext i j; exact d.cm.2.2.2 (d.B.emb w).1 (d.b.1 i j)
  rw [cst] at h
  ext i j
  have := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  simpa [Matrix.mul_apply, Matrix.toCols₁, Matrix.toCols₂, Matrix.one_apply, Matrix.smul_apply, apply_ite] using this
theorem eps_zeta_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ((R.ε : ℤ) : ℂ) * star R.ζ * R.ζ⁻¹ = -1 := by
  rcases R.hζ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
theorem piInf_trace_k (w : InfinitePlace F) {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by
  simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
theorem piInf_hT_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (s t : ℝ) (w : InfinitePlace F) :
    piInf (d.B.emb w) ((((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) =
      ((s * t : ℝ) : ℂ) * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.piInf_trace_k]
  have hcw : d.cw w (((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ) =
      (((s : ℂ) • d.cw w W) * ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ)ᵀ * d.A.J.map (d.B.emb w).1 *
        ((((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • d.cw w W) * ((d.b.1.toCols₁).map (d.B.emb w).1)ᵀ).map star *
        ((dbl d.Y.J).map (d.B.emb w).1)ᵀ := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul, Matrix.transpose_map]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.dbl_incM_k]
    have c1 := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_realAd_k (d := d) w s W
    have c2 := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_realAd_k (d := d) w t (_root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W)
    have c3 := (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.tw_spec_k R W).2 w
    have c4 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w d.A.J
    have c5 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w d.b.1.toCols₁
    have c6 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w d.b.1.toCols₂
    have c7 := _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d w (dbl d.Y.J)
    have c8 := _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d w ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul, Matrix.transpose_map] at c1 c2 c3 c4 c5 c6 c7 c8
    rw [c8, c1, c2, c3, c4, c5, c6, c7, smul_smul]
  rw [hcw, trace_line, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.frame_hermForm_real_sign, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, ← _root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, R.cw_gram w W, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  have hz := _root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R
  have e := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.eps_zeta_k R
  have sq := _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.sg_sq_k R w
  push_cast
  simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal, map_intCast]
  rw [Complex.star_def] at e
  linear_combination (-(s : ℂ) * t * (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) *
    ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * e + ((s : ℂ) * t * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) * sq
end Psi
open Psi
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem psi_tw'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (t : ℝ) (X : Mx F E d.m d.n) :
    d.B.ψ (d.tt (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X)) =
      Complex.exp (4 * Real.pi * Complex.I * t * ⟪_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X⟫_ℝ) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.psi_tt_arch_k _ (_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.fin_gram_tw_k R W t X), _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.inner_arc_k]
  congr 1
  have e : ∀ w, ((d.cw w (d.gram (realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) X)).trace).re =
      -t * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.cw_gram_tw_k, Matrix.trace_smul, smul_eq_mul, ← _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.re_trace_loc_k]
    simp [Complex.mul_re]
  simp only [e]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring_nf
theorem psi_sp'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (s t : ℝ) :
    d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * s * t * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) := by
  have hx : finOne F • ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ) = 0 := by
    rw [← Matrix.smul_mul, smul_comm, hW, smul_zero, Matrix.zero_mul]
  have hz : finOne F • (-(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) = 0 := by
    rw [smul_neg, ← Matrix.trace_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul,
      ← Matrix.transpose_smul, hx]
    simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.spf_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.psi_neg_half_trace_k _ hz]
  congr 1
  have e : ∀ w, (piInf (d.B.emb w) (-(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
      ((realAd F t • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace)).re =
      -(s * t) * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w W i j).re + (R.loc w W i j).im * (R.loc w W i j).im) := by
    intro w
    rw [map_neg, _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.piInf_hT_k, ← _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.re_trace_loc_k, Complex.neg_re, Complex.re_ofReal_mul]
    ring
  simp only [e]
  rw [← Finset.mul_sum, ← _root_.PositivityTheory.SiegelWeilFormula.KFP.Psi.inner_arc_k, real_inner_self_eq_norm_sq]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRotVac
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open Matrix
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem om_place_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    ∃ (p q : ℕ) (e : ℤ), ∀ y : GR d.n, InK (mR y) → ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g →
      d.om (R.ι w y) Ω = F0 p q e y • Ω := by
  obtain ⟨L, hL⟩ := hLO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, -, hLk⟩ := hLI F E σ d R w L hL
  refine ⟨p, q, e, fun y hy g hg Ω hΩ hTΩ => ?_⟩
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g (fun k => (d.crd X k).2)
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have hvt : d.T Ω = R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    rw [hTΩ]
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k, Ψ]
    rw [← Finset.mul_prod_erase Finset.univ (fun w' => fP (1 : PX d.m d.n) (R.loc w' X)) (Finset.mem_univ w), mul_assoc]
    rfl
  have h1 := (hL y (fP (1 : PX d.m d.n)) (KFock.isSw_fP 1)).2 Ψ (_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ) Ω hΩ hvt
  rw [hLk y 1 hy, hLD.kvac y hy] at h1
  have hfP : fP (F0 p q e y • (1 : PX d.m d.n)) = F0 p q e y • fP (1 : PX d.m d.n) := by
    funext u
    simp only [fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  have htens : R.tens w (F0 p q e y • fP (1 : PX d.m d.n)) Ψ = F0 p q e y • R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfP, htens, ← hvt, ← _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k] at h1
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  exact _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hT.1 d (hS.pres _ Ω hΩ) (d.sch.smul_mem _ hΩ) h1
theorem om_rot_vac'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) :
    ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → d.om (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t) Ω = χ • Ω := by
  have key : ∀ l : List (InfinitePlace F), ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g →
      d.om ((l.map fun w => R.ι w (yrot d.n (R.sg w) t)).prod) Ω = χ • Ω := by
    intro l
    induction l with
    | nil => exact ⟨1, one_ne_zero, fun g _ Ω _ _ => by simp⟩
    | cons w l ih =>
      obtain ⟨χ, hχ, h⟩ := ih
      obtain ⟨p, q, e, hw⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.om_place_k hT hLO hLI R w
      refine ⟨F0 p q e (yrot d.n (R.sg w) t) * χ, mul_ne_zero (weight_factor_rotation_ne_zero p q e d.n (R.sg w) t) hχ,
        fun g hg Ω hΩ hTΩ => ?_⟩
      have hK : InK (mR (yrot d.n (R.sg w) t)) := by rw [mR_yrot]; exact inK_yrotM' _ _ _
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, h g hg Ω hΩ hTΩ, map_smul,
        hw _ hK g hg Ω hΩ hTΩ, smul_smul, mul_comm]
  exact key _
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAssemble
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_of_conj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {y y' : GR d.n} {x₁ x₂ : d.G} {A₁ A₂ A' : d.LF → d.LF} {B₁ B₂ : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w (R.ι w y') A' id)
    (hy : R.ι w y = x₁ * R.ι w y' * x₂) (h1 : x₁ * x₂ = 1) : R.OkY w y := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  intro f hf
  by_cases hf0 : ∀ u, f u = 0
  · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
    have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hf0])
    subst this
    rw [map_zero, d.T_zero]
    funext X
    simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
  · push Not at hf0
    obtain ⟨u₀, hu₀⟩ := hf0
    by_cases hex : ∃ κ : ℂ, κ ≠ 0 ∧ A₁ (A₂ f) = κ • f
    · obtain ⟨κ, hκ, hA⟩ := hex
      refine ⟨κ⁻¹ • A₁ (A' (A₂ f)), ?_, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      · obtain ⟨φ, hφ⟩ := hc.1 f hf
        refine ⟨κ⁻¹ • φ, ?_⟩
        funext u
        have := congrFun hφ u
        simp only [Function.comp_apply] at this
        simp [this]
      · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have hB : ∀ X, B₁ (B₂ Ψ) X = κ⁻¹ * Ψ X := by
          intro X
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
          have h2 := congrFun e0 (X + Z)
          have h3 := hΨ X Z hZ1 hZ2
          have h4 := hBaway X Z hZ1 hZ2
          simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, hZ3, hA, Pi.smul_apply, smul_eq_mul] at h2 h4
          rw [h3, h4] at h2
          rw [eq_inv_mul_iff_mul_eq₀ hκ]
          apply mul_left_cancel₀ hu₀
          linear_combination -h2
        rw [hy, e]
        funext X
        simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hB]
        ring
    · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      have hΨ0 : ∀ X, Ψ X = 0 := by
        by_contra hne
        push Not at hne
        obtain ⟨X₀, hX₀⟩ := hne
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have key : ∀ u, f u * Ψ X₀ = A₁ (A₂ f) u * B₁ (B₂ Ψ) X₀ := by
          intro u
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
          have h2 := congrFun e0 (X₀ + Z)
          have h3 := hΨ X₀ Z hZ1 hZ2
          have h4 := hBaway X₀ Z hZ1 hZ2
          simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, hZ3] at h2 h4
          rw [h3, h4] at h2
          exact h2
        have hB0 : B₁ (B₂ Ψ) X₀ ≠ 0 := by
          intro h0'
          have := key u₀
          rw [h0', mul_zero] at this
          exact mul_ne_zero hu₀ hX₀ this
        apply hex
        refine ⟨Ψ X₀ / B₁ (B₂ Ψ) X₀, div_ne_zero hX₀ hB0, ?_⟩
        funext u
        have := key u
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hB0]
        linear_combination -this
      have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨ0])
      subst this
      rw [map_zero, d.T_zero]
      funext X
      simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨ0]
end RD
theorem locOpEx_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := by
  intro F E _ _ _ _ _ σ d R w
  refine ⟨_, R.isLocOp_of_ok w fun y => ?_⟩
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, s, B, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have okN : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → R.OkY w y :=
    fun y b hb hy => R.ok_of_step w (R.stepN w hT y b hb hy)
  have okM : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = Glob.mM a → R.OkY w y := by
    intro y a ha hy
    obtain ⟨c, -, hc⟩ := R.stepM w hT y a ha hy
    exact R.ok_of_step w hc
  have okB : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = Glob.nbar c → R.OkY w y := by
    intro y c hc hy
    obtain ⟨y', x, hx, hy', hrel⟩ := R.nbar_conj' w hw₀ y c hc hy
    have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
    exact R.ok_of_conj w hT hW3 hW (R.stepN w hT y' x hx hy') hrel (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)
  obtain ⟨y1, y2, y3, y4, hy, ⟨t, ht⟩, ⟨c, hc, hc2⟩, ⟨a, ha, ha2⟩, ⟨b, hb, hb2⟩⟩ := PositivityTheory.Rg.Sw.Glob.decomp d.n y
  rw [hy]
  exact R.ok_mul w hsch (R.ok_mul w hsch (R.ok_mul w hsch (okN y1 _ (herm_smul_one' t) ht) (okB y2 c hc hc2))
    (okM y3 a ha ha2)) (okN y4 b hb hb2)
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitTop
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem genDictX_of_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.dictAsmX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.cellFormula_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.relEx_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.heightDict_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.measDict_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.thetaDict_k
theorem whitK_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : Gen.WhitGenLt)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitK_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.kFinK_k hT hA hR hF hK hS hU hW hTC hLB hPK
theorem whitEq_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (hW : Gen.WhitGenEq) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitEq_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.kFinK_k hT hA hR hF hK hS hU hEW hW hTC hLB hPK
theorem whitLow_of_k (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (hW : Gen.WhitGenLow)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitLow_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.vacSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k hVK hT hA hF hS hU hEW hW hTC hLB hPK
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end


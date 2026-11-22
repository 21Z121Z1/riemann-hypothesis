import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Strong
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.ExistsAtPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpArcPf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem cwA_add_k (w : InfinitePlace F) (X Y : Mx F E d.m d.n) : d.cw w (X + Y) = d.cw w X + d.cw w Y := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem cwA_realAd_k (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    d.cw w (realAd F t • X) = (t : ℂ) • d.cw w X := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, GlobalTheory.RealScalar.piInf_realAd_smul]
theorem locA_add_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KFP.cwA_add_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
theorem locA_realAd_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    R.loc w (realAd F t • X) = (t : ℂ) • R.loc w X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KFP.cwA_realAd_k, Matrix.mul_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rfl
def arcAF_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
theorem arcA_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X) := rfl
theorem arc_add'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Y : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R Y := by
  have : _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R Y := by
    funext i
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.locA_add_k, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, this, map_add]
theorem arc_realAd'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X := by
  have : _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X := by
    funext i
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.locA_realAd_k, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, this, map_smul]
theorem crdA_add_k (X Y : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Y) k = d.crd X k + d.crd Y k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
theorem sndA_crd_of_k (Z : Mx F E d.m d.n) (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have h1 : finOne F • Z k.1 k.2.1 = 0 := by
    have := congrFun (congrFun hZ k.1) k.2.1
    simpa using this
  have h2 : finOne F * (Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2 = 0 := by
    have := congrArg (fun z => (Algebra.TensorProduct.basis (AF F) d.bs).repr z k.2.2) h1
    simpa only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] using this
  have h3 : (1 : FiniteAdeleRing (𝓞 F) F) * ((Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2).2 = 0 :=
    congrArg Prod.snd h2
  rw [one_mul] at h3
  exact h3
theorem fin_add_of'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X := by
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.crdA_add_k]
  show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.sndA_crd_of_k Z hZ k, add_zero]
theorem fin_realAd_smul'_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  rw [smul_comm, hZ, smul_zero]
theorem gau_eq'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X = (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) := by
  have hn : ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.equiv, if_true, if_false]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k, fP, evX, map_one, one_mul, gs]
  rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem memLp_schM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : MemLp f 2 ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).symm
  have h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    exact memLpSchA _ BorelSpace.measurable_eq _ inferInstance hf'
  have h2 := (e.memLp_map_measure_iff).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def TL_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d
  map_smul' a Φ := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k d a Φ
theorem rho_smul_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring
theorem B_rel'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  have hpow : ∀ i : ℕ, d.om (k ^ i) Ω = χ ^ i • Ω := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hact : ∀ i : ℕ, actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v := by
    intro i
    have e1 : k ^ i * k⁻¹ ^ i = 1 := by rw [inv_pow, mul_inv_cancel]
    simp only [actB]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]
    simp
  set Ψ := d.dd.rho d.B.ψ v Ω with hΨdef
  have hΨ : Ψ ∈ d.sch := hrho v Ω hΩ
  have hterm : ∀ i : ℕ, (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) =
      _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν (d.om (k ^ i) Φ) Ψ := by
    intro i
    have h1 := hU F E σ d ν hν (k ^ i) Φ hΦ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)
    have h2 : d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ := by
      rw [hS.impl _ _ Ω hΩ, hact, hpow, _root_.PositivityTheory.SiegelWeilFormula.KFP.rho_smul_k]
    rw [h2, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k] at h1
    unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k
    rw [← h1]
    have e3 : ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) =
        star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) := by
      intro X
      rw [Pi.smul_apply, smul_eq_mul, star_mul', star_pow]
      ring
    simp_rw [e3]
    rw [integral_const_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), one_pow, one_mul]
  have hint : ∀ i : ℕ, Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν := by
    intro i
    have hA := _root_.PositivityTheory.SiegelWeilFormula.KFP.memLp_schM_k d ν hν ((hT.1 F E σ d).1 (d.om (k ^ i) Φ) (hS.pres (k ^ i) Φ hΦ))
    have hB := (_root_.PositivityTheory.SiegelWeilFormula.KFP.memLp_schM_k d ν hν ((hT.1 F E σ d).1 Ψ hΨ)).star
    exact hA.integrable_mul hB
  calc ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν (d.om (k ^ i) Φ) Ψ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hterm]
    _ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by
        unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k
        rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ = ∫ X, _root_.PositivityTheory.SiegelWeilFormula.KFP.TL_k d (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by
        congr 1
        funext X
        rw [map_sum, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rfl
    _ = 0 := by
        rw [hq, map_zero]
        simp
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadStrong
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont
namespace PositivityTheory.SiegelWeilFormula.Khead
theorem eisStrong_of_k : _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.EisStrong_k := by
  intro hBL F E _ _ _ _ _ σ d hS s₁ f hf s₀
  obtain ⟨r', s', hY⟩ := hS
  obtain ⟨Ê, ⟨t, hsum, hdiff⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt s₁ f hf
  have hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → d.G → ℂ), An.Reg (fun x : d.G => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x := by
    intro s₀
    obtain ⟨k, U, H, hU, he, hd⟩ := hw s₀
    refine ⟨k, fun s => (H s).1, reg_of_weak hU hd, ?_⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with s hs hne
    exact he s hs hne
  have hr : ∀ s : ℂ, t < s.re → An.Reg (fun x : d.G => (ht2 x : ℝ)) Ê s := fun s hs => by
    obtain ⟨k, H, a, e⟩ := hp s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) hdiff
  obtain ⟨U, p, G, hUo, hUr, hs₀, hp0, hreg, heq⟩ := strip one_le_height_GL2 hp hr s₀
  obtain ⟨hGd, hGc⟩ := diff_cont_of_reg hreg
  obtain ⟨t2, hmaj⟩ := _root_.PositivityTheory.SiegelWeilFormula.Khead.majorant_k d ⟨r', s', hY⟩ hf
  have hinv := _root_.GlobalTheory.T.eisenstein_series_moderate_growth F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt d.χ s₁ f hf
    d.ok.hecke t Ê hsum
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y) = flat d.a f s₁ z := fun z => funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
    rw [Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → ∀ g, d.eis f s₁ z g = Ê z g := fun z hz g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz g).tsum_eq
  refine ⟨U, p, G, max t t2, hUo, hUr, hs₀, hp0, hGd, hGc, ?_, fun z hz =>
    ⟨hmaj z (lt_of_le_of_lt (le_max_right _ _) hz), fun g => ?_⟩⟩
  · intro z hz γ hγ g
    obtain ⟨τ, hτ⟩ := hUr.1
    have han : ∀ x, AnalyticOnNhd ℂ (G · x) U := fun x => (hGd x).analyticOnNhd hUo
    have hz₀ : (((max τ t + 1 : ℝ)) : ℂ) ∈ rightOf (max τ t) := by simp
    refine (han (γ * g)).eqOn_of_preconnected_of_eventuallyEq (han g) hUr.isPreconnected
      (hτ (rightOf_subset (le_max_left _ _) hz₀)) ?_ hz
    filter_upwards [(isOpen_rightOf _).mem_nhds hz₀] with w hw
    have hw' : t < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    rw [heq w hw', heq w hw', hinv w hw' γ hγ g]
  · have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    rw [heq z hz1, Heisenberg₂ z hz1]
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVarB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_at_place_k (w : InfinitePlace F) (V : Matrix (Fin d.m) (Fin d.n) ℂ) :
    ∃ V' : Mx F E d.m d.n, At (evI F) V' ∧ ∀ w', d.cw w' V' = if w' = w then V else 0 := by
  have h := d.ok.good.cm
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h d.B.emb fun w' =>
    if w' = w then V i j else 0
  refine ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w' => ?_⟩
  ext i j
  show piInf (d.B.emb w') (x i j) = _
  rw [hz i j w']
  split_ifs <;> rfl
theorem mZ_place_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (tA : Matrix (Fin d.n) (Fin d.n) (AE F E)) (htA : _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * tA)
    {V' : Mx F E d.m d.n} {V : Matrix (Fin d.m) (Fin d.n) ℂ} (hV : ∀ w', d.cw w' V' = if w' = w then V else 0)
    (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (V' * tAᵀ) X = -(2 * ((((R.ε : ℤ) : ℂ)) * trace ((d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * V.map star)).re) := by
  have e1 : V' * tAᵀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ = V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k, Finset.sum_eq_single w]
  · congr 3
    have hX : (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = V * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w
      rw [if_pos rfl] at this
      rw [show V'.map (piInf (d.B.emb w)) = d.cw w V' from rfl, this]
      rfl
    rw [hX, hVb]
    exact trace_form_sign_eq (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (d.cw w X) V
  · intro w' _ hw'
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w')) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w'
      rw [if_neg hw'] at this
      rw [show V'.map (piInf (d.B.emb w')) = d.cw w' V' from rfl, this, Matrix.zero_mul]
    rw [hVb]
    simp
  · intro h; exact absurd (Finset.mem_univ w) h
theorem var_span'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) :
    ∃ (Z₁ Z₂ : Mx F E d.m d.n) (c₁ c₂ : ℂ), At (evI F) Z₁ ∧ At (evI F) Z₂ ∧
      ∀ X, evX (MvPolynomial.X k) (R.loc w X) = c₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₁ X : ℂ) + c₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₂ X : ℂ) := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set τ := d.B.emb w
  set fr := (R.fr w).1
  set fi := ((R.fr w)⁻¹).1
  set A := d.A.J.map τ.1
  set e : ℂ := ((R.ε : ℤ) : ℂ)
  have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hes : star e = e := by simp [e]
  have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Complex.ext_iff]
  have hfi : fr * fi = 1 := by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hif : fi * fr = 1 := by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)
  have hAP : A * P = 1 := by
    have hA := A_eq hfi hz (R.hfr w)
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl] at hA
    rw [hA]
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif]
      rw [show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 by ext i j; simp [one_apply, apply_ite]]
      rw [Matrix.one_mul, ← transpose_mul, hfi, transpose_one]
    rw [t1]
    have hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1 := by
      calc _ = (((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * (star R.ζ * R.ζ) := by ring
        _ = 1 := by rw [hz, mul_one]; rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
    rw [hs2, one_smul]
  have key : ∀ M : Matrix (Fin d.m) (Fin d.n) ℂ, ∃ Z : Mx F E d.m d.n, At (evI F) Z ∧
      ∀ X, (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ) = -(2 * e) * ((trace ((d.cw w X)ᵀ * M)).re : ℂ) := by
    intro M
    obtain ⟨V', hV'a, hV'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.exists_at_place_k (d := d) w ((P * M).map star)
    refine ⟨V' * tAᵀ, at_mul hV'a _, fun X => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_place_k R w tA htA hV' X]
    have : (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M := by
      rw [show ((P * M).map star).map star = P * M by ext i j; simp only [Matrix.map_apply, star_star], ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP,
        Matrix.mul_one]
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl, this]
    have hre : (e * trace ((d.cw w X)ᵀ * M)).re = e.re * (trace ((d.cw w X)ᵀ * M)).re := by
      rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
    rw [hre]
    rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h] <;> ring
  have hM : ∀ (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ),
      trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1 := fun c x => by
    simp only [trace, diag, mul_apply, transpose_apply, of_apply, mul_ite, mul_zero]
    rw [Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [if_true]; ring
  obtain ⟨Z₁, h1, e1⟩ := key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)
  obtain ⟨Z₂, h2, e2⟩ := key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)
  have hl : ∀ X, evX (MvPolynomial.X k) (R.loc w X) =
      if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1) := fun X => by
    simp only [evX, MvPolynomial.eval_X, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply]
    split_ifs <;> (try simp only [star_star]) <;> rfl
  have hsplit : ∀ z : ℂ, z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  have hsplit' : ∀ z : ℂ, star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  refine ⟨Z₁, Z₂, -(e / 2) * (if k.2.2 then 1 else 1), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2,
    fun X => ?_⟩
  rw [hl X, e1 X, e2 X, hM, hM, one_mul]
  have hinv : -(e / 2) * (-(2 * e)) = 1 := by linear_combination he
  split_ifs
  · conv_lhs => rw [hsplit ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) - Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
  · rw [hsplit' ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) + Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.om_sch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch := fun x Φ hΦ =>
  d.ok.dbl.weil.2.1.pres x Φ hΦ
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_zero : d.T 0 = 0 := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (0 : d.Fn) = 0 := fun p => by
    funext x
    simp [schr]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, h, map_zero, Pi.zero_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_inj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0 := fun Φ hΦ h => (hT.1 F E σ d).2.2 Φ hΦ h
end SD
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc_surj (w : InfinitePlace F) : ∀ (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ), ∃ Z : Mx F E d.m d.n,
    (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0 ∧ R.loc w (X + Z) = u := by
  intro X u
  obtain ⟨ins, h1, h2, h3⟩ := d.exists_insW w
  set M : Matrix (Fin d.m) (Fin d.n) ℂ := (R.fr w).1 * (Matrix.of u).map star - d.cw w X with hM
  refine ⟨M.map ins, fun w' hw' => ?_, ?_, ?_⟩
  · ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h2 w' hw']
  · ext i j
    simp [h3]
  · have hc : d.cw w (X + M.map ins) = (R.fr w).1 * (Matrix.of u).map star := by
      have : d.cw w (M.map ins) = M := by
        ext i j
        simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h1]
      rw [show d.cw w (X + M.map ins) = d.cw w X + d.cw w (M.map ins) from by
        ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw], this, hM]
      abel
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, hc, ← Matrix.mul_assoc]
    rw [show ((R.fr w)⁻¹).1 * (R.fr w).1 = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], Matrix.one_mul]
    ext i j
    simp
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwaX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem kFinK_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => _root_.PositivityTheory.SiegelWeilFormula.KWhit.kfin_om_k d hΦ hk
theorem iwaRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.par_decomp_k d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.int_n_k d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    simp only [flat]
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc], _root_.PositivityTheory.SiegelWeilFormula.KWhit.a_mul_K_k d _ k hk,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.constantTerm_mul_right]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.orb_n_k hT d T (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d _ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end


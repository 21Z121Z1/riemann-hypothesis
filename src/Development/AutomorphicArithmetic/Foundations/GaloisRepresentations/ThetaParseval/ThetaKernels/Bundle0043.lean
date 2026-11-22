import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsLth
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0022
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0024
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.PiInfInclR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.PureProdOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0027

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoMean
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Cpt σ d.A.J := by
  have h := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl hA) d.ok.aniso
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr hA) d.ok.aniso
theorem exists_lth_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ l ∈ (adeleClass F).adm d.κ, ∀ Φ ∈ d.sch, l Φ = thetaSum F Φ :=
  GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F d.κ
theorem cont_S_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : Continuous fun g : UA σ d.A.J => thetaSum F (d.S g Ψ) := by
  obtain ⟨l, hl, hlθ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_lth_k d
  exact (d.ok.dbl.lin.cont l hl Ψ hΨ).congr fun g => hlθ _ (d.ok.dbl.lin.pres g Ψ hΨ)
theorem inv_S_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∀ γ ∈ ratU σ d.A.J, ∀ g, thetaSum F (d.S (γ * g) Ψ) = thetaSum F (d.S g Ψ) := fun γ hγ g => by
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_S_rat_k hP hT d hγ (d.ok.dbl.lin.pres g Ψ hΨ)]
theorem bdd_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∃ C : ℝ, ∀ g, ‖thetaSum F (d.S g Ψ)‖ ≤ C :=
  (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).bdd (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.inv_S_k hP hT d hΨ)
theorem intOn_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    IntegrableOn (fun g => thetaSum F (d.S g Ψ)) d.D d.μ := by
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.bdd_S_k hS hP hT d hΨ
  exact Measure.integrableOn_of_bounded (M := C) ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom).ne
    (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ).aestronglyMeasurable (Eventually.of_forall hC)
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoOrth
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.kfour PositivityTheory.SiegelWeilFormula.Place
theorem frame_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, FrameEq σ d.Y d.b ε ∧
    ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  refine ⟨ε, hε, ?_⟩
  have key : ∀ e : E, e * e = 1 → (∀ i j, σ (d.Y.J j i) = e * d.Y.J i j) → ((ε : ℤ) : E) = e := by
    intro e he hY
    have hY' : ∀ i j, d.Y.J j i = e * σ (d.Y.J i j) := fun i j => by
      rw [hY j i, ← mul_assoc, he, one_mul]
    have hD : (dbl d.Y.J)ᵀ = e • (dbl d.Y.J).map σ := by
      ext (i | i) (j | j)
      · simp [dbl, hY' i j]
      · simp [dbl]
      · simp [dbl]
      · simp [dbl, hY' i j]
    have hM : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ)ᵀ = e • (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ := by
      have e1 : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ = (d.b.1.map σ)ᵀ * (dbl d.Y.J).map σ * d.b.1 := by
        have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q E) (Q : Matrix q r E), (P * Q).map σ = P.map σ * Q.map σ :=
          fun P Q => Matrix.map_mul (f := σ.toRingHom)
        have h2 : (d.b.1.map σ).map σ = d.b.1 := by
          rw [Matrix.map_map]
          exact Matrix.ext fun i j => hσ _
        rw [h1, h1, h2, Matrix.transpose_map]
      rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc]
    rw [hε] at hM
    have hn : 0 < d.n := d.ok.hn
    have := congrFun (congrFun hM (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
    simpa [Matrix.fromBlocks] using this
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have e := key (-1) (by ring) fun i j => by rw [hY i j]; ring
    intro i j
    rw [e, neg_neg, one_mul]
    exact (hA.herm j i).symm
  · have e := key 1 (by ring) fun i j => by rw [hY i j, one_mul]
    intro i j
    rw [e, hA.skew j i]
    ring
theorem gram_cond_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (hε : ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j))
    (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : d.gram X X ∈ nCond σ d.n ε := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hJ : (incM F d.A.J)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F d.A.J).map (cA σ)) := by
    ext i j
    simp only [Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      cA_inclR']
    rw [hε i j, map_mul, map_neg, inclR_int, neg_mul]
  show (Xᵀ * incM F d.A.J * X.map (cA σ))ᵀ = -((((ε : ℤ) : AE F E)) • (Xᵀ * incM F d.A.J * X.map (cA σ)).map (cA σ))
  have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q (AE F E)) (Q : Matrix q r (AE F E)),
      (P * Q).map (cA σ) = P.map (cA σ) * Q.map (cA σ) := fun P Q => Matrix.map_mul (f := (cA σ).toRingHom)
  have h2 : (X.map (cA σ)).map (cA σ) = X := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => cA_cA' σ hσ _
  rw [h1, h1, h2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJ,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
theorem gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [incM_mul'', incM_mul'', incM_map]
  rfl
theorem gram_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) (T : nF σ d.Y d.b) :
    ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 ∈ nA σ d.Y d.b ∧
      ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 = incM F S₀ := by
  obtain ⟨ε, hb, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.frame_sign_k d
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨T₀, hT₀⟩ := (mem_nF_iff T.1).1 T.2
  refine ⟨(mem_nA_iff hσ hb _).2 (add_mem (smul_cond ε _ (_root_.PositivityTheory.SiegelWeilFormula.Tauto.gram_cond_k d ε hε _)) ((mem_nA_iff hσ hb _).1 T.1.2)),
    (2⁻¹ : E) • (Xᵀ * d.A.J * X.map σ) + T₀, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Tauto.gram_incM_k, hT₀]
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add, map_mul]
  rw [Algebra.smul_def, ← half_eq]
theorem exists_twist_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (S₀ : Matrix (Fin d.n) (Fin d.n) E) (hS : incM F S₀ ∈ nCond σ d.n ε)
    (h0 : S₀ ≠ 0) : ∃ β₀ ∈ nCond σ d.n ε, d.B.ψ (-(d.tt (incM F S₀ * β₀))) ≠ 1 := by
  have hcm := d.cm
  have hS' : (incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F S₀).map (cA σ)) := hS
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, S₀ i j ≠ 0 := by
    by_contra h
    exact h0 (Matrix.ext fun i j => by_contra fun hne => h ⟨i, j, hne⟩)
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ := d.B.emb
  set Sw : Matrix (Fin d.n) (Fin d.n) ℂ := (incM F S₀).map (piInf (τ w)) with hSw
  have hSwT : ∀ i j, Sw j i = -(((ε : ℤ) : ℂ)) * star (Sw i j) := fun i j => by
    have := congrArg (fun M => (M.map (piInf (τ w))) i j) hS'
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg,
      map_mul, map_intCast, piInf_cA hcm] at this
    simpa [hSw] using this
  set q : ℂ := piInf (τ w) ((incM F S₀ * incM F S₀).trace) with hq
  have hqe : q = -(((ε : ℤ) : ℂ)) * ∑ i, ∑ j, ((Complex.normSq (Sw i j) : ℝ) : ℂ) := by
    rw [hq, Matrix.trace, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    change Sw i j * Sw j i = _
    rw [hSwT i j, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hN : 0 < ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Sw i j))
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i₀))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => Complex.normSq (Sw i₀ j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j₀))
    refine Complex.normSq_pos.2 ?_
    simp only [hSw, Matrix.map_apply, incM, piInf_inclR']
    exact (map_ne_zero _).2 hij
  have hε1 : (((ε : ℤ) : ℝ)) ≠ 0 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hqre : q.re = -(((ε : ℤ) : ℝ)) * ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    rw [hqe]
    simp [Complex.mul_re, ← Complex.ofReal_sum]
  have hqre0 : q.re ≠ 0 := by
    rw [hqre]
    exact mul_ne_zero (neg_ne_zero.2 hε1) hN.ne'
  set r : ℝ := -1 / (4 * q.re) with hr
  obtain ⟨s, -, hs1, hs2, -, hs4⟩ := exists_sec hcm τ
  set x : InfinitePlace F → ℂ := fun u => if u = w then (r : ℂ) else 0 with hx
  set c : AE F E := s x with hc
  have hcc : cA σ c = c := by
    refine ad_ext hcm τ (fun u => ?_) ?_
    · rw [piInf_cA hcm, hc, hs1]
      by_cases hu : u = w <;> simp [hx, hu]
    · rw [← map_smul, hc, hs2, map_zero]
  refine ⟨c • incM F S₀, ?_, ?_⟩
  · show (c • incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (c • incM F S₀).map (cA σ))
    have e : (c • incM F S₀).map (cA σ) = c • (incM F S₀).map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcc]
    rw [Matrix.transpose_smul, hS', e, smul_neg, smul_comm]
  · set z : AE F E := -(c * (incM F S₀ * incM F S₀).trace) with hz
    have e1 : -(d.tt (incM F S₀ * (c • incM F S₀))) = Algebra.trace (AF F) (AE F E) z := by
      rw [hz, map_neg, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hf : finOne F • z = 0 := by
      rw [hz, smul_neg, ← smul_mul_assoc, hc, hs2, zero_mul, neg_zero]
    have hw : ∀ u, u ≠ w → piInf (τ u) z = 0 := fun u hu => by
      rw [hz, map_neg, map_mul, hc, hs1]
      simp [hx, hu]
    rw [e1, psi_trace_at d.std hcm τ w z hf hw]
    have hzw : (piInf (τ w) z).re = 1 / 4 := by
      rw [hz, map_neg, map_mul, hc, hs1, ← hq]
      simp only [hx, if_pos rfl, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hr]
      field_simp
    rw [hzw]
    intro h
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (1 / 4 : ℝ)) : ℝ) : ℂ)) = -1 := by
      rw [show (2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num]
      rw [show -(2 * Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [h2] at h
    norm_num at h
theorem orth_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (S : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hS : S ∈ nA σ d.Y d.b) (hr : ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, S = incM F S₀) :
    ∫ β in 𝓖, d.B.ψ (-(d.tt (S * β.1))) ∂lam = if S = 0 then 1 else 0 := by
  classical
  obtain ⟨ε, hb, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.frame_sign_k d
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨-, hH, hfd, h1⟩ := hc
  haveI := hH
  haveI : BorelSpace (nA σ d.Y d.b) := (nA_top hσ d.ok.frame).2.2.2
  obtain ⟨S₀, rfl⟩ := hr
  split_ifs with h0
  · have hone : ∀ β : nA σ d.Y d.b, d.B.ψ (-(d.tt (incM F S₀ * β.1))) = 1 := fun β => by
      rw [h0, Matrix.zero_mul, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_zero, map_zero, neg_zero, AddChar.map_zero_eq_one]
    simp_rw [hone]
    rw [setIntegral_const]
    simp [Measure.real, h1]
  · have hS0 : S₀ ≠ 0 := fun h => h0 (by rw [h]; ext i j; simp [incM])
    obtain ⟨β₀, hβ₀, hne⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_twist_k d ε S₀ ((mem_nA_iff hσ hb _).1 hS) hS0
    let h : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (incM F S₀ * β.1)))
    have hadd : ∀ β β' : nA σ d.Y d.b, h (β + β') = h β * h β' := fun β β' => by
      simp only [h, AddSubgroup.coe_add, Matrix.mul_add, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add, neg_add,
        AddChar.map_add_eq_mul]
    have hper : ∀ g ∈ nF σ d.Y d.b, ∀ y, h (g + y) = h y := fun g hg y => by
      obtain ⟨T₀, hT₀⟩ := (mem_nF_iff g).1 hg
      rw [hadd]
      have hg1 : h g = 1 := by
        simp only [h, hT₀, ← incM_mul'', _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, trace_incM, trace_inclR, ← map_neg]
        exact d.std.2.1 _
      rw [hg1, one_mul]
    exact GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist lam (nF σ d.Y d.b) hfd hper
      (c := ⟨β₀, (mem_nA_iff hσ hb _).2 hβ₀⟩) (fun y => hadd _ y) hne
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoRat
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in
theorem thetaSum_rational_invariant (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil
  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1
  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat
  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPure
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem pure_prod_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf)
    (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (l : InfinitePlace F → ℝ) (hl : ∀ w, |l w| = 1) :
    ∃ (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin (fun Y => d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ))
        (Gen.phiInf θ l fr g P) Φf := by
  obtain ⟨hloc, hcof, hT⟩ := hP
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ :=
    fun v Y => gf v (crdV d.bs v (toMxV v Y * Av u v))
  refine ⟨fun X => ∏ᶠ v, Φv v (HeckeCharacterZeroLocus.SiegelWeilU.projV v X), Φv,
    ⟨fun v => isSB_comp d.bs u v (gf v) (hloc v), ?_, fun X => rfl⟩, ?_⟩
  · filter_upwards [hcof, int_iff (m := d.m) d.bs u] with v hv hint
    funext Y
    show gf v _ = _
    rw [hv]
    by_cases h : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV d.bs v
    · rw [Set.indicator_of_mem h]
      refine (Set.indicator_of_mem ?_ _).trans rfl
      exact (hint Y).2 h
    · rw [Set.indicator_of_notMem h]
      refine Set.indicator_of_notMem ?_ _
      intro h'
      exact h ((hint Y).1 h')
  · intro X
    dsimp only
    rw [hT]
    dsimp only
    congr 1
    · unfold Gen.phiInf
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB.crd_eq_k R u η θ th fr frc g gc w X, hl w, mul_one]
      rfl
    · refine finprod_congr fun v => ?_
      congr 1
      funext k
      have hZ : (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map (mapV v) =
          toMxV v (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) * Av u v := by
        rw [map_mul_alg]
        congr 1
        ext a j
        simp only [Matrix.map_apply, toMx, toMxV, Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin,
          mapV_eq]
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k).2 =
          phiV v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k) := rfl
      rw [h1, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, ← basis_repr_map']
      simp only [crdV]
      rw [← hZ]
      rfl
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitHeis
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem tHeis_k : _root_.PositivityTheory.SiegelWeilFormula.THeis_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ Z X
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, hf, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  constructor
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [rho_rho, map_smul, smul_eq_mul, symp_cols, frame_yy_A d.ok.frame, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero, neg_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul, ← Matrix.add_mul]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [hBx, Matrix.transpose_mul, ← Matrix.mul_assoc, rho_rho, map_smul, smul_eq_mul, add_comm,
      l_shift h hψ _ _ hΦ, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    rw [darboux_anti d.dd, Matrix.mul_assoc Z, ← Matrix.transpose_mul, symp_cols, hf, Matrix.mul_one, trace_gram,
      map_neg]
    linear_combination (Algebra.trace (AF F) (AE F E) (Matrix.trace (Z * (X.map (cA σ))ᵀ * (incM F d.A.J)ᵀ))) *
      (invOf_two_add_invOf_two : (⅟(2 : AF F) + ⅟2 = 1))
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaPreservingEndomorphismScalar
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_preserving_endomorphism_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  first | exact @_root_.GlobalTheory.ThetaSchurF.schur_k | exact _root_.GlobalTheory.ThetaSchurF.schur_k | (intros; apply _root_.GlobalTheory.ThetaSchurF.schur_k <;> assumption)
end
end


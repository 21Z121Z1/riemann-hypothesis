import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0063
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCountData
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono fun x hx => hx.1).trans_lt (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finset_sum _ fun q _ => hi q, ?_⟩
  rw [integral_finset_sum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (s : Q) :
    (a * b).coeff s = ∑ q, a.coeff q * b.coeff (q⁻¹ * s) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

theorem conv_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a b : MonoidAlgebra ℂ Q) :
    I.convF μf (ρ.lift μf a) (ρ.lift μf b) = ρ.lift μf (a * b) := by
  letI := Fintype.ofFinite Q
  funext x
  unfold AutInst.convF
  by_cases hx : x ∈ I.Kset
  · have e : (fun y => ρ.lift μf a y * ρ.lift μf b (y⁻¹ * x)) = fun y => if y ∈ I.Kset then
        (fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ) *
          (b.coeff (q⁻¹ * ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ))) (ρ.toFun y) else 0 := by
      funext y
      by_cases hy : y ∈ I.Kset
      · have hy' : y⁻¹ ∈ I.Kset := (Ksub I).inv_mem hy
        rw [if_pos hy, ρ.lift_of_mem μf a hy, ρ.lift_of_mem μf b ((Ksub I).mul_mem hy' hx), ρ.map_mul _ hy' _ hx,
          ρ.map_inv hy]
      · rw [if_neg hy, ρ.lift_of_notMem μf a hy, zero_mul]
    rw [e, (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ) *
      (b.coeff (q⁻¹ * ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ))).2, ρ.lift_of_mem μf _ hx, coeff_mul_eq_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : ((μf (I.Kg g)).toReal : ℂ) = 0
    · simp [h]
    · field_simp
  · rw [ρ.lift_of_notMem μf _ hx]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ I.Kset
    · have : y⁻¹ * x ∉ I.Kset := fun h => hx (((Ksub I).mul_mem_cancel_left ((Ksub I).inv_mem hy)).1 h)
      simp only [ρ.lift_of_notMem μf b this, mul_zero, Pi.zero_apply]
    · simp only [ρ.lift_of_notMem μf a hy, zero_mul, Pi.zero_apply]

theorem isPosType_lift [Finite Q] (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (h1 : a * a = a) (h2 : IsSA a) :
    I.IsPosType (ρ.lift μf a) := by
  letI := Fintype.ofFinite Q
  intro m x c
  let q : Fin m → I.Gf ⧸ Ksub I := fun i => (x i : I.Gf ⧸ Ksub I)
  have hk : ∀ i, ((q i).out)⁻¹ * x i ∈ I.Kset := fun i => by
    show _ ∈ Ksub I
    rw [← QuotientGroup.eq]
    exact Quotient.out_eq _
  let b : Q → Fin m → ℂ := fun u i => c i * a.coeff (u⁻¹ * ρ.toFun (((q i).out)⁻¹ * x i))
  have key : ∀ i j, star (c i) * c j * ρ.lift μf a ((x i)⁻¹ * x j) =
      ∑ u, (if q i = q j then star (b u i) * b u j else 0) * (1 / ((μf (I.Kg g)).toReal : ℂ)) := by
    intro i j
    by_cases hij : q i = q j
    · have e1 : (x i)⁻¹ * x j = (((q i).out)⁻¹ * x i)⁻¹ * (((q j).out)⁻¹ * x j) := by
        rw [← hij]; group
      have hi' : (((q i).out)⁻¹ * x i)⁻¹ ∈ I.Kset := (Ksub I).inv_mem (hk i)
      rw [e1, ρ.lift_of_mem μf a ((Ksub I).mul_mem hi' (hk j)), ρ.map_mul _ hi' _ (hk j), ρ.map_inv (hk i)]
      simp only [if_pos hij, b]
      generalize ρ.toFun (((q i).out)⁻¹ * x i) = s
      generalize ρ.toFun (((q j).out)⁻¹ * x j) = t
      have e2 : a.coeff (s⁻¹ * t) = ∑ u, star (a.coeff (u⁻¹ * s)) * a.coeff (u⁻¹ * t) := by
        conv_lhs => rw [← h1, coeff_mul_eq_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun u => ?_
        rw [← h2]
        simp [mul_assoc]
      rw [e2, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [star_mul']
      ring
    · have : (x i)⁻¹ * x j ∉ I.Kset := fun h => hij (QuotientGroup.eq.2 h)
      simp only [if_neg hij, ρ.lift_of_notMem μf a this, mul_zero, zero_mul, Finset.sum_const_zero]
  have e3 : ∑ i, ∑ j, star (c i) * c j * ρ.lift μf a ((x i)⁻¹ * x j) =
      ∑ u, (∑ i, ∑ j, if q i = q j then star (b u i) * b u j else 0) * (1 / ((μf (I.Kg g)).toReal : ℂ)) := by
    simp only [key, Finset.sum_mul]
    rw [Finset.sum_comm (γ := Q)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [e3]
  refine Finset.sum_nonneg fun u _ => mul_nonneg (GlobalTheory.CharIdem.sum_fiber_nonneg q (b u)) ?_
  have : (1 / ((μf (I.Kg g)).toReal : ℂ)) = ((1 / (μf (I.Kg g)).toReal : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact Complex.zero_le_real.2 (by positivity)

theorem isAdmIdem_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (g₀ : ℕ)
    (a : MonoidAlgebra ℂ Q) (h1 : a * a = a) (h2 : IsSA a)
    (h3 : ∀ x ∈ I.Kset, a.coeff (ρ.toFun x) ≠ 0 → I.UnipMod g₀ x) : I.IsAdmIdem μf g g₀ (ρ.lift μf a) := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hone : (1 : I.Gf) ∈ I.Kg g := (KgSub I g).one_mem
  have hs : ∀ x, ρ.lift μf a x ≠ 0 → x ∈ I.Kset := fun x hx => by
    by_contra h
    exact hx (ρ.lift_of_notMem μf a h)
  refine ⟨?_, by rw [conv_lift ρ μf hg, h1], ρ.lift_inv μf a h2, isPosType_lift ρ μf a h1 h2, hs,
    fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk', fun x hx => h3 x (hs x hx) fun h => hx ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' I.Kg g, hU.preimage (by fun_prop), by simpa using hone, fun y hy => ?_⟩
    have e1 : y = 1 * x * (x⁻¹ * y) := by group
    rw [e1, lift_biinv ρ μf a x 1 hone _ hy]
  · rw [ρ.lift_of_mem μf a (hs x hx), h, zero_div]

end Infl

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem tensAlg_mul (a b : ∀ i, MonoidAlgebra ℂ (G i)) : tensAlg a * tensAlg b = tensAlg fun i => a i * b i := by
  letI := fun i => Fintype.ofFinite (G i)
  ext h
  rw [coeff_mul_eq_sum]
  simp only [tensAlg_coeff, coeff_mul_eq_sum, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

theorem isSA_tensAlg (a : ∀ i, MonoidAlgebra ℂ (G i)) (h : ∀ i, IsSA (a i)) : IsSA (tensAlg a) := by
  intro q
  rw [tensAlg_coeff, tensAlg_coeff, star_prod]
  exact Finset.prod_congr rfl fun i _ => h i _

end Tens

theorem isDS_low_unitary {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsDS ε lam σ) :
    (∃ w, IsLowUnit ε lam σ w) ∧
      ∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  constructor
  · obtain ⟨v, hv, h0, -⟩ := hS.2.2.2.1
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, Submodule.smul_mem _ _ ((le_sSup hS : S ≤ _) hv)⟩
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  · intro x a b
    exact (LinearIsometry.mk (σ (uMat x) : H →ₗ[ℂ] H) (hU.2.1 (uMat x) x.2)).inner_map_map a b

theorem exists_count_data (I : AutInst) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (e : I.Gf → ℂ)
    (hσ : ∀ v (x : Formalism.REAL.UJ (I.ε v)) a b, ⟪σ v (uMat x) a, σ v (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ)
    (he : Integrable e μf) :
    ∃ (fund : Set I.GA) (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (_ : CompleteSpace Hs)
      (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
      (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsFundDom (I.muA μf) fund ∧ I.IsHilbTensor σ σs tens ∧
      I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re := by
  obtain ⟨fund, hfund⟩ := GlobalTheory.FundExists.exists_isFundDom I μf
  obtain ⟨R, hR, -⟩ := GlobalTheory.RightRegExists.exists_rightReg I μf fund hfund
  obtain ⟨Hs, i1, i2, i3, σs, tens, htens⟩ := GlobalTheory.HilbTensorExists.exists_isHilbTensor I H σ hσ
  obtain ⟨Re, hRe⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv I μf fund hfund R hR).1 e he
  exact ⟨fund, Hs, i1, i2, i3, σs, tens, R, Re, hfund, htens, hR, hRe⟩

end GlobalTheory.Mem.RowsBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalLog
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.LocalLog

theorem exists_local_log (n : ℕ) : ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    (∀ᶠ g in 𝓝 (1 : Mx n), NormedSpace.exp (L g) = g) ∧
    ∀ᶠ X in 𝓝 (0 : Mx n), L (NormedSpace.exp X) = X := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Mx n → Mx n)
      ((ContinuousLinearEquiv.refl ℂ (Mx n) : Mx n ≃L[ℂ] Mx n) : Mx n →L[ℂ] Mx n) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  have h0 : NormedSpace.exp (0 : Mx n) = 1 := NormedSpace.exp_zero
  refine ⟨h.localInverse _ _ _, ?_, ?_, ?_, h.eventually_left_inverse⟩
  · have := h.localInverse_continuousAt
    rwa [h0] at this
  · have := h.localInverse_apply_image
    rwa [h0] at this
  · have := h.eventually_right_inverse
    rwa [h0] at this

theorem local_log_UJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    ∀ᶠ g in 𝓝 (1 : Mx n), g ∈ UJset ε → L g ∈ lieSet ε ∧ NormedSpace.exp (L g) = g := by
  intro n ε
  obtain ⟨L, hc, h1, hr, hl⟩ := exists_local_log n
  refine ⟨L, hc, h1, ?_⟩
  have hJ := Jm_mul_self ε
  have ht : Tendsto (fun g => Jm ε * (-(L g)ᴴ) * Jm ε) (𝓝 1) (𝓝 0) := by
    have hcont : Continuous fun X : Mx n => Jm ε * (-Xᴴ) * Jm ε := by fun_prop
    have := (hcont.tendsto 0).comp (h1 ▸ hc.tendsto)
    simpa [Function.comp_def] using this
  filter_upwards [hr, ht.eventually hl] with g hg hg' hU
  refine ⟨?_, hg⟩
  have hU' : gᴴ * Jm ε * g = Jm ε := hU
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have he : NormedSpace.exp (Jm ε * (-(L g)ᴴ) * Jm ε) = g := by
    have h2 := Matrix.exp_conj (Jm ε) (-(L g)ᴴ) (isUnit_Jm ε)
    rw [hinv, Matrix.exp_neg, Matrix.exp_conjTranspose, hg] at h2
    rw [h2]
    have h3 : (gᴴ)⁻¹ = Jm ε * g * Jm ε := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', hJ]
    rw [h3]
    calc Jm ε * (Jm ε * g * Jm ε) * Jm ε = (Jm ε * Jm ε) * g * (Jm ε * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hJ]; simp
  rw [he] at hg'
  show (L g)ᴴ * Jm ε + Jm ε * L g = 0
  nth_rewrite 2 [hg']
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  simp

end GlobalTheory.LocalLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitaryExchangeUnimodularLatticesIner
section
noncomputable section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.InertExchange

theorem exchange : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)),
  conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
  ∀ (X Z : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E X → Submodule.IsLattice E Z →
    IsUnimodular (hStd E n) X → IsUnimodular (hStd E n) Z →
    (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z) →
    ∃ σ : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n), σ X = Z ∧ σ Z = X ∧
      (∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) →
        Submodule.IsLattice E (σ Y) ∧ IsUnimodular (hStd E n) (σ Y) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (σ Y)) ∧
      (∀ Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        ∃ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
          (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) ∧ σ Y = Y') ∧
      (∀ Y Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') → σ Y = σ Y' → Y = Y') ∧
      ∀ (s : List ℕ) (Y Y' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        (IsInertNbr P.asIdeal s (σ Y) (σ Y') ↔ IsInertNbr P.asIdeal s Y Y') := by
  intro E _ _ _ n P hP hin X Z hXl hZl hXu hZu hXZ
  obtain ⟨g, hg, hgX, hgZ⟩ := GlobalTheory.T.cartan_exchange_unimodular_inert_prime n P hP hin X Z hXl hZl hXu hZu hXZ
  have hcc : ∀ Q : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ Q) = Q := fun Q => by
    apply HeightOneSpectrum.ext
    ext r
    change cO E (cO E r) ∈ Q.asIdeal ↔ r ∈ Q.asIdeal
    rw [cO_cO]
  have locg : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E)) (M N : Submodule (𝓞 E) (Sp E n)),
      localization₂ Q.asIdeal M = localization₂ Q.asIdeal N → localization₂ Q.asIdeal (gmap h M) = localization₂ Q.asIdeal (gmap h N) := by
    intro h Q M N e
    ext x
    rw [mem_localization_gmap, mem_localization_gmap, e]
  have locg_inv : ∀ (h : Sp E n ≃ₗ[E] Sp E n) (Q : HeightOneSpectrum (𝓞 E)) (M N : Submodule (𝓞 E) (Sp E n)),
      localization₂ Q.asIdeal (gmap h M) = localization₂ Q.asIdeal (gmap h N) → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N := by
    intro h Q M N e
    ext x
    have h1 := (mem_localization_gmap Q h M (h x)).symm
    have h2 := (mem_localization_gmap Q h N (h x)).symm
    simp only [LinearEquiv.symm_apply_apply] at h1 h2
    rw [h1, h2, e]
  have ginv : ∀ M : Submodule (𝓞 E) (Sp E n), gmap g⁻¹ (gmap g M) = M := by
    intro M
    ext x
    rw [mem_gmap, mem_gmap]
    have e : g⁻¹ = g.symm := rfl
    rw [e, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  have hginv : g⁻¹ ∈ UF E n := inv_mem hg
  have unimodG : ∀ (h : Sp E n ≃ₗ[E] Sp E n), h ∈ UF E n → ∀ M : Submodule (𝓞 E) (Sp E n),
      IsUnimodular (hStd E n) M → IsUnimodular (hStd E n) (gmap h M) := by
    intro h hh M hM
    have hM' : dual (hStd E n) M = M := hM
    show dual (hStd E n) (gmap h M) = gmap h M
    rw [dual_gmap h hh, hM']
  have unimod : ∀ A B C : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E A → Submodule.IsLattice E B →
      Submodule.IsLattice E C → IsUnimodular (hStd E n) B → IsUnimodular (hStd E n) C →
      localization₂ P.asIdeal A = localization₂ P.asIdeal B → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal C) →
      IsUnimodular (hStd E n) A := by
    intro A B C hA hB hC hBu hCu hAP hAQ
    have hBu' : dual (hStd E n) B = B := hBu
    have hCu' : dual (hStd E n) C = C := hCu
    show dual (hStd E n) A = A
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    by_cases hQ : Q = P
    · rw [hQ]
      have h1 : localization₂ (conjPrime₂ P).asIdeal A = localization₂ (conjPrime₂ P).asIdeal B := by rw [hP]; exact hAP
      rw [GlobalTheory.T.localization_hermitianDual_eq P A B hA hB h1, hBu', hAP]
    · have hQ' : conjPrime₂ Q ≠ P := fun h => hQ (by rw [← hcc Q, h, hP])
      rw [GlobalTheory.T.localization_hermitianDual_eq Q A C hA hC (hAQ _ hQ'), hCu', hAQ Q hQ]
  have locσ : ∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → ∀ Q : HeightOneSpectrum (𝓞 E),
      localization₂ Q.asIdeal (patchAt P (gmap g Y) Y) = localization₂ Q.asIdeal (if Q = P then gmap g Y else Y) :=
    fun Y hY => (GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap g Y) Y (gmap_lattice g Y hY) hY).2
  have latσ : ∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y →
      Submodule.IsLattice E (patchAt P (gmap g Y) Y) :=
    fun Y hY => (GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap g Y) Y (gmap_lattice g Y hY) hY).1
  refine ⟨fun Y => patchAt P (gmap g Y) Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show patchAt P (gmap g X) X = Z
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    rw [locσ X hXl Q]
    split_ifs with hQ
    · rw [hQ]; exact hgX.localization_eq.symm
    · exact (hXZ Q hQ).localization_eq.symm
  · show patchAt P (gmap g Z) Z = X
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    rw [locσ Z hZl Q]
    split_ifs with hQ
    · rw [hQ]; exact hgZ.localization_eq.symm
    · exact (hXZ Q hQ).localization_eq
  · intro Y hYl hYu hYS
    show Submodule.IsLattice E (patchAt P (gmap g Y) Y) ∧ IsUnimodular (hStd E n) (patchAt P (gmap g Y) Y) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (patchAt P (gmap g Y) Y)
    refine ⟨latσ Y hYl, ?_, ?_⟩
    · refine unimod _ (gmap g Y) X (latσ Y hYl) (gmap_lattice g Y hYl) hXl (unimodG g hg Y hYu) hXu ?_ ?_
      · rw [locσ Y hYl P, if_pos rfl]
      · intro Q hQ
        rw [locσ Y hYl Q, if_neg hQ]
        exact (hYS Q hQ).localization_eq
    · intro Q hQ
      apply GlobalTheory.T.sameAt_of_localization_eq Q X _ hXl (latσ Y hYl)
      rw [locσ Y hYl Q, if_neg hQ]
      exact (hYS Q hQ).localization_eq.symm
  · intro Y' hl' hu' hS'
    obtain ⟨hYl, hYloc⟩ := GlobalTheory.T.submodulePatchAtPrime_isLattice_locP P (gmap g⁻¹ Y') Y' (gmap_lattice _ _ hl') hl'
    refine ⟨patchAt P (gmap g⁻¹ Y') Y', hYl, ?_, ?_, ?_⟩
    · refine unimod _ (gmap g⁻¹ Y') Y' hYl (gmap_lattice _ _ hl') hl' (unimodG _ hginv Y' hu') hu' ?_ ?_
      · rw [hYloc P, if_pos rfl]
      · intro Q hQ
        rw [hYloc Q, if_neg hQ]
    · intro Q hQ
      apply GlobalTheory.T.sameAt_of_localization_eq Q X _ hXl hYl
      rw [hYloc Q, if_neg hQ]
      exact (hS' Q hQ).localization_eq.symm
    · show patchAt P (gmap g (patchAt P (gmap g⁻¹ Y') Y')) (patchAt P (gmap g⁻¹ Y') Y') = Y'
      apply Formalism.L2.DIV.eq_of_forall_localized_eq
      intro Q
      rw [locσ _ hYl Q]
      split_ifs with hQ
      · rw [hQ]
        ext x
        rw [mem_localization_gmap, hYloc P, if_pos rfl, mem_localization_gmap]
        have e : g⁻¹ = g.symm := rfl
        rw [e, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
      · rw [hYloc Q, if_neg hQ]
  · intro Y Y' hYl hYu hYS hY'l hY'u hY'S he
    have he' : patchAt P (gmap g Y) Y = patchAt P (gmap g Y') Y' := he
    apply Formalism.L2.DIV.eq_of_forall_localized_eq
    intro Q
    by_cases hQ : Q = P
    · rw [hQ]
      apply locg_inv g P
      have h1 := congrArg (localization₂ P.asIdeal) he'
      rw [locσ Y hYl P, locσ Y' hY'l P, if_pos rfl, if_pos rfl] at h1
      exact h1
    · rw [(hYS Q hQ).localization_eq, (hY'S Q hQ).localization_eq]
  · intro s Y Y' hYl hYu hYS hY'l hY'u hY'S
    show IsInertNbr P.asIdeal s (patchAt P (gmap g Y) Y) (patchAt P (gmap g Y') Y') ↔ IsInertNbr P.asIdeal s Y Y'
    have hAl := gmap_lattice g Y hYl
    have hBl := gmap_lattice g Y' hY'l
    have hAA' := GlobalTheory.T.sameAt_of_localization_eq P (gmap g Y) _ hAl (latσ Y hYl) (by rw [locσ Y hYl P, if_pos rfl])
    have hBB' := GlobalTheory.T.sameAt_of_localization_eq P (gmap g Y') _ hBl (latσ Y' hY'l) (by rw [locσ Y' hY'l P, if_pos rfl])
    have hAB : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal (gmap g Y) = localization₂ Q.asIdeal (gmap g Y') :=
      fun Q hQ => locg g Q Y Y' ((hYS Q hQ).localization_eq.trans (hY'S Q hQ).localization_eq.symm)
    have hA'B' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P →
        localization₂ Q.asIdeal (patchAt P (gmap g Y) Y) = localization₂ Q.asIdeal (patchAt P (gmap g Y') Y') := by
      intro Q hQ
      rw [locσ Y hYl Q, locσ Y' hY'l Q, if_neg hQ, if_neg hQ, (hYS Q hQ).localization_eq, (hY'S Q hQ).localization_eq]
    obtain ⟨k1, hk1, hk1'⟩ := GlobalTheory.T.exists_prime_pow_smul_le_of_localizations_eq_away P _ _ hAl hBl hAB
    obtain ⟨k2, hk2, hk2'⟩ := GlobalTheory.T.exists_prime_pow_smul_le_of_localizations_eq_away P _ _ (latσ Y hYl) (latσ Y' hY'l) hA'B'
    obtain ⟨a, ha, a', ha', h1, h2⟩ := hAA'
    obtain ⟨b, hb, b', hb', h3, h4⟩ := hBB'
    have hα0 : a * a' * b * b' ∉ P.asIdeal :=
      Formalism.L2.DIV.lc_mul_notMem P (Formalism.L2.DIV.lc_mul_notMem P (Formalism.L2.DIV.lc_mul_notMem P ha ha') hb) hb'
    obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hα0
    have hgeom := geom_sum_mul p (k1 + k2)
    have hgd : t * (∑ i ∈ Finset.range (k1 + k2), p ^ i) * (a * a' * b * b') + p ^ (k1 + k2) = 1 := by
      linear_combination (∑ i ∈ Finset.range (k1 + k2), p ^ i) * e - hgeom
    have hδ : p ^ (k1 + k2) ∈ P.asIdeal ^ (k1 + k2) := Ideal.pow_mem_pow hp _
    set S := ∑ i ∈ Finset.range (k1 + k2), p ^ i
    have rAA' : HiRel (t * S * (a * a' * b * b')) (gmap g Y) (patchAt P (gmap g Y) Y) := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * b * b') • (a' • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h2 x hx)
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a' * b * b') • (a • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h1 x hx)
    have rBB' : HiRel (t * S * (a * a' * b * b')) (gmap g Y') (patchAt P (gmap g Y') Y') := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * a' * b) • (b' • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h4 x hx)
      · have : (t * S * (a * a' * b * b')) • x = (t * S * a * a' * b') • (b • x) := by rw [smul_smul]; congr 1; ring
        rw [this]; exact Submodule.smul_mem _ _ (h3 x hx)
    have le1 : P.asIdeal ^ (k1 + k2) ≤ P.asIdeal ^ k1 := Ideal.pow_le_pow_right (by omega)
    have le2 : P.asIdeal ^ (k1 + k2) ≤ P.asIdeal ^ k2 := Ideal.pow_le_pow_right (by omega)
    have rAB : HiRel (p ^ (k1 + k2)) (gmap g Y) (gmap g Y') :=
      HiRel.of_ideal ((Submodule.smul_mono_left le1).trans hk1) ((Submodule.smul_mono_left le1).trans hk1') hδ
    have rA'B' : HiRel (p ^ (k1 + k2)) (patchAt P (gmap g Y) Y) (patchAt P (gmap g Y') Y') :=
      HiRel.of_ideal ((Submodule.smul_mono_left le2).trans hk2) ((Submodule.smul_mono_left le2).trans hk2') hδ
    constructor
    · intro h
      have h5 := isInertNbr_par hgd rAA'.symm rBB'.symm rA'B' rAB h
      have h6 := h5.gmap g⁻¹
      rwa [ginv, ginv] at h6
    · intro h
      exact isInertNbr_par hgd rAA' rBB' rAB rA'B' (h.gmap g)

end GlobalTheory.InertExchange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), admitted V W χ χ' → V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  first | exact @GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO | exact GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO | (intros; apply GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwinerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_of_compactGroup_intertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank) (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank), IsInfFam θ → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → (∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) → I ≠ 0 → (∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) → (∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)), Function.Injective pt → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) → IsItW θ M M' ω pt It := by
  first | exact @GlobalTheory.CompactIntertwiner.exists_isItW | exact GlobalTheory.CompactIntertwiner.exists_isItW | (intros; apply GlobalTheory.CompactIntertwiner.exists_isItW <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleGoodFormValuesBoundedByClassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrame
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewFrameInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem mul_mem_range_of_trace {t : 𝓞 E} (ht : t ∈ differentIdeal ℤ (𝓞 E)) {z : E}
    (hz : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * z))) : (t : E) * z ∈ (algebraMap (𝓞 E) E).range := by
  have hz' : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0)]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact IsIntegrallyClosed.isIntegral_iff.mp (hz o)
  have ht' : (t : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨t, ht, rfl⟩
  rw [coeIdeal_differentIdeal ℤ ℚ] at ht'
  have hm := FractionalIdeal.mul_mem_mul ht' hz'
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0))] at hm
  exact (FractionalIdeal.mem_one_iff _).1 hm

theorem exists_mem_different {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) : ∃ t ∈ differentIdeal ℤ (𝓞 E), t ∉ w.asIdeal := by
  by_contra hcon
  push_neg at hcon
  have hle : differentIdeal ℤ (𝓞 E) ≤ w.asIdeal := fun t ht => hcon t ht
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hle
  rcases (Ideal.IsPrime.mul_le w.isPrime).1 hle with h1 | h2
  · have := hB.unram
    have hu : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := inferInstance
    exact (not_dvd_differentIdeal_iff.2 hu) (Ideal.dvd_iff_le.2 h1)
  · rw [Ideal.map_le_iff_le_comap] at h2
    have hc : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
      rw [← h]; rfl
    rw [hc] at h2
    exact GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std v (hB.inert v w hw).2.2 h2

theorem latLoc_le (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n : ℕ}
    {L L' : Submodule (𝓞 E) (Fin n → E)} {t : 𝓞 E} (ht : t ∉ w.asIdeal) (hL : ∀ y ∈ L, t • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  have key : GlobalTheory.LFun.latAt w L ≤ GlobalTheory.LFun.latAt w L' := by
    unfold GlobalTheory.LFun.latAt
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have htx := hL x hx
    have hv : Valued.v (algebraMap E (w.adicCompletion E) (t : E)) = 1 := by
      have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (t : E)
      refine e1.trans ?_
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w).2 ht
    have hne : algebraMap E (w.adicCompletion E) (t : E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have hu : (algebraMap E (w.adicCompletion E) (t : E))⁻¹ ∈ w.adicCompletionIntegers E := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
    have heq : (fun i => algebraMap E (w.adicCompletion E) (x i)) = (⟨_, hu⟩ : Formalism.UG.Ov E w) •
        (fun i => algebraMap E (w.adicCompletion E) ((t • x) i)) := by
      funext i
      have hc : ((t • x) i : E) = (t : E) * x i := rfl
      show _ = (algebraMap E (w.adicCompletion E) (t : E))⁻¹ * algebraMap E (w.adicCompletion E) ((t • x) i)
      rw [hc, map_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [SetLike.mem_coe]
    show (fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ _
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t • x, htx, rfl⟩)
  intro y hy
  rw [GlobalTheory.LFun.InertChart.mem_latLoc_iff (L := L) hw h] at hy
  rw [GlobalTheory.LFun.InertChart.mem_latLoc_iff (L := L') hw h]
  exact key hy

omit [NumberField F] [NumberField E] in
theorem hE_smul_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    hE σ (c • Jᵀ) x y = c * form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_ne_zero {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 := GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ r s (hX.sig w0)
  intro hJ
  apply h0
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

private theorem form_smul_left_divisor (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E)
    (y x : Fin n → E) : form σ J (c • y) x = (c : E) * form σ J y x := by
  show ((c : E) • y) ⬝ᵥ _ = _
  rw [smul_dotProduct, smul_eq_mul]
  rfl

theorem isSelfDualAt {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {n r s : ℕ} {X : Spc F E n}
    (hX : X.IsSkew σ B r s) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {d : 𝓞 E} (hd : d ∉ w.asIdeal) :
    ((d : E)⁻¹ • X.Jᵀ).det ≠ 0 ∧ IsSelfDualAt σ ((d : E)⁻¹ • X.Jᵀ) X.L v := by
  have hd0 : (d : E) ≠ 0 := by
    intro h0
    apply hd
    have hd' : d = 0 := by exact_mod_cast h0
    rw [hd']
    exact w.asIdeal.zero_mem
  have hdet : ((d : E)⁻¹ • X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hd0)) (det_ne_zero hX)
  refine ⟨hdet, ?_⟩
  unfold GlobalTheory.AdelicU.IsSelfDualAt
  rw [← SelfDual.latLoc_dualGlob hdet hX.lat v]
  obtain ⟨t, ht, htw⟩ := exists_mem_different hB hw h
  apply le_antisymm
  · refine latLoc_le hw h (t := d * t) ?_ ?_
    · intro hm
      rcases w.isPrime.mem_or_mem hm with h1 | h1
      · exact hd h1
      · exact htw h1
    · intro y hy
      rw [SelfDual.mem_dualGlob]
      intro x hx
      rw [hE_smul_transpose, form_smul_left_divisor]
      have hf : (t : E) * form σ X.J y x ∈ (algebraMap (𝓞 E) E).range :=
        mul_mem_range_of_trace ht (fun o => (hX.dual y).1 hy x hx o)
      have he : (d : E)⁻¹ * (((d * t : 𝓞 E) : E) * form σ X.J y x) = (t : E) * form σ X.J y x := by
        push_cast
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      rw [he]
      exact hf
  · refine latLoc_le hw h (t := 1) ?_ ?_
    · intro h1
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · intro y hy
      rw [one_smul]
      rw [SelfDual.mem_dualGlob] at hy
      refine (hX.dual y).2 fun x hx o => ?_
      have h1 := hy x hx
      rw [hE_smul_transpose] at h1
      obtain ⟨e, he⟩ := h1
      have hf : form σ X.J y x = (d : E) * algebraMap (𝓞 E) E e := by
        rw [he, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
      rw [hf]
      have hi : IsIntegral ℤ ((o : E) * ((d : E) * algebraMap (𝓞 E) E e)) :=
        (RingOfIntegers.isIntegral_coe o).mul ((RingOfIntegers.isIntegral_coe d).mul (RingOfIntegers.isIntegral_coe e))
      exact Algebra.isIntegral_trace hi

theorem exists_frame_skew {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {n r s : ℕ} {X : Spc F E n}
    (hX : X.IsSkew σ B r s) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) :
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin n) (w.adicCompletion E)), Valued.v δ = 1 ∧ c δ = -δ ∧
      IsFrameAt w X.L Bm ∧
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map c = δ • 1 := by
  have hcm := hB.cm
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.InertChart.exists_conj_sub_unit hcm hw
  have hxi : IsIntegral ℤ (σ (x : E) - (x : E)) :=
    (map_isIntegral_int (σ : E →+* E) (RingOfIntegers.isIntegral_coe x)).sub (RingOfIntegers.isIntegral_coe x)
  let d : 𝓞 E := ⟨σ (x : E) - (x : E), hxi⟩
  have hdE : (d : E) = σ (x : E) - (x : E) := rfl
  have hd : d ∉ w.asIdeal := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w).1 hx
  obtain ⟨hdet, hs⟩ := isSelfDualAt hB hX hw h hd
  have hσd : σ (d : E) = -(d : E) := by
    rw [hdE, map_sub, GlobalTheory.LFun.InertChart.conj_conj hcm]
    ring
  have hd0 : (d : E) ≠ 0 := by
    intro h0
    apply hd
    have hd' : d = 0 := by exact_mod_cast h0
    rw [hd']
    exact w.asIdeal.zero_mem
  have hherm : IsHermND σ ((d : E)⁻¹ • X.Jᵀ) := by
    refine ⟨fun i j => ?_, hdet⟩
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_inv₀, hσd, hX.skew j i]
    rw [inv_neg]
    ring
  obtain ⟨a, ha, haJ⟩ := GlobalTheory.LFun.InertChart.exists_frame_antiJ hcm hherm hX.lat.fg hX.lat.span_eq_top hw hc hs
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hcm hw hc
  obtain ⟨k, hk, hk1⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (B := 1) (one_mem _) (by
    unfold Formalism.UG.cT
    simp)
  set δ := algebraMap E (w.adicCompletion E) (d : E) with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact (map_ne_zero _).2 hd0
  set Jw := X.J.map (algebraMap E (w.adicCompletion E)) with hJw
  have e1 : (a.1.map c)ᵀ * Jwᵀ * a.1 = δ • ((k.1.map c)ᵀ * k.1) := by
    have h2 := haJ.trans hk1.symm
    unfold Formalism.UG.cT at h2
    have hKm : ((d : E)⁻¹ • X.Jᵀ).map (algebraMap E (w.adicCompletion E)) = δ⁻¹ • Jwᵀ := by
      ext i j
      simp [hδ, hJw, map_inv₀]
    rw [hKm, Matrix.mul_smul, Matrix.smul_mul] at h2
    have h2' : δ⁻¹ • ((a.1.map c)ᵀ * Jwᵀ * a.1) = (k.1.map c)ᵀ * k.1 := by simpa using h2
    rw [← h2', smul_smul, mul_inv_cancel₀ hδ0, one_smul]
  have e2 : a.1ᵀ * Jw * a.1.map c = δ • (k.1ᵀ * k.1.map c) := by
    have h3 := congrArg Matrix.transpose e1
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_assoc] using h3
  have hkk : k.1 * (k⁻¹).1 = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  refine ⟨δ, a * k⁻¹, ?_, ?_, (GlobalTheory.LFun.InertChart.isFrameAt_mul ha (inv_mem hk)).1, ?_⟩
  · exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (d : E)).trans hx
  · rw [hδ, GlobalTheory.LFun.InertChart.conj_algebraMap hc, hσd, map_neg]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.map_mul]
    calc (k⁻¹).1ᵀ * a.1ᵀ * Jw * (a.1.map c * (k⁻¹).1.map c)
        = (k⁻¹).1ᵀ * (a.1ᵀ * Jw * a.1.map c) * (k⁻¹).1.map c := by
          simp only [Matrix.mul_assoc]
      _ = δ • ((k.1 * (k⁻¹).1)ᵀ * (k.1 * (k⁻¹).1).map c) := by
          rw [e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
      _ = δ • 1 := by
          rw [hkk]
          simp

theorem exists_inertPlace_seesawW_scalar_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin (a + a')) (w.adicCompletion E)), Valued.v δ = 1 ∧ σL δ = -δ ∧
      IsFrameAt w G.W.L Bm ∧
      (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E))ᵀ * G.W.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)).map σL = δ • 1 := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hw h σL hc
  exact exists_frame_skew hB hG.hW hw h hc

end GlobalTheory.SkewFrameInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (AE F E)) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  first | exact @GlobalTheory.InertVacLagP.exists_lagr_inv_vac | exact GlobalTheory.InertVacLagP.exists_lagr_inv_vac | (intros; apply GlobalTheory.InertVacLagP.exists_lagr_inv_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumberStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  first | exact @GlobalTheory.ColumnRenumber.phiA_renumber | exact GlobalTheory.ColumnRenumber.phiA_renumber | (intros; apply GlobalTheory.ColumnRenumber.phiA_renumber <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelicStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_standardThetaLine_read_adelic : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := by
  first | exact @GlobalTheory.VacRead.exists_vac_reads | exact GlobalTheory.VacRead.exists_vac_reads | (intros; apply GlobalTheory.VacRead.exists_vac_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.InertTransv.exists_unip_corner_isUnit | exact GlobalTheory.InertTransv.exists_unip_corner_isUnit | (intros; apply GlobalTheory.InertTransv.exists_unip_corner_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpInt
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

theorem symm_mem_latR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyComplex E] {k : ℕ} {g : GlobalTheory.CuspRep.GA E k} (hg : g ∈ GlobalTheory.UnitaryBC.latticeGL E k) :
    (glTens F E k).symm g ∈ latR F E k := by
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
  rw [map_mul, map_zpow]
  refine mul_mem (Subgroup.mem_sup_left ⟨γ, ?_⟩) (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) n)
  apply (glTens F E k).injective
  rw [glTens_bc, ContinuousMulEquiv.apply_symm_apply]

def latEquiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyComplex E] (k : ℕ) : GlobalTheory.UnitaryBC.latticeGL E k ≃ latR F E k where
  toFun g := ⟨(glTens F E k).symm g, symm_mem_latR g.2⟩
  invFun x := ⟨glTens F E k x, latR_le k x.2⟩
  left_inv g := Subtype.ext ((glTens F E k).apply_symm_apply _)
  right_inv x := Subtype.ext ((glTens F E k).symm_apply_apply _)

theorem finvol_tens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))]
    [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E)))
    (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (latR F E k) D ν → ν D ≠ ⊤ := by
  intro F E _ _ _ _ _ _ k _ _ ν D hν hD
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let f := (glTens F E k).toHomeomorph.toMeasurableEquiv
  let μ : Measure (GlobalTheory.CuspRep.GA E k) := ν.map f
  haveI : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (glTens F E k)
  have hq : Measure.QuasiMeasurePreserving f.symm μ ν :=
    (MeasurePreserving.mk f.symm.measurable (f.map_symm_map)).quasiMeasurePreserving
  have hD' : IsFundamentalDomain (GlobalTheory.UnitaryBC.latticeGL E k) (f '' D) μ :=
    hD.image_of_equiv f.toEquiv hq (latEquiv F E k) fun g x => by
      change glTens F E k ((glTens F E k).symm g * x) = g * glTens F E k x
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have h1 : ν D = μ (f '' D) := by
    rw [f.map_apply, f.preimage_image]
  rw [h1, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hD']
  haveI := (GlobalTheory.CovolGL.finvol E k μ).1
  exact measure_ne_top _ _

end GlobalTheory.GLOneVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormVal

theorem bigC_and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  first
  | exact @_root_.GlobalTheory.BigConstantConjunction.bigC_and
  | exact _root_.GlobalTheory.BigConstantConjunction.bigC_and
  | (apply _root_.GlobalTheory.BigConstantConjunction.bigC_and <;> assumption)
  | (intros; apply _root_.GlobalTheory.BigConstantConjunction.bigC_and <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BigConstantConjunction.bigC_and <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BigConstantConjunction.bigC_and ..)

theorem bigC_mono {Q Q' : ChQ} (h : BigC Q) (hQ : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (F : Face D A) (ch : Choice R) (C b : ℝ), Q F ch C b → Q' F ch C b) : BigC Q' := by
  obtain ⟨a, h⟩ := h
  refine ⟨a, fun CF hCF => ?_⟩
  obtain ⟨c, h⟩ := h CF hCF
  refine ⟨c, fun ε C hC => ?_⟩
  obtain ⟨x, h⟩ := h ε C hC
  exact ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j k => hQ F ch C large₂.sc.b (h D large₂ e hx Γ Pl0 T A Ks R F s ch i j k)⟩

set_option maxHeartbeats 1600000 in
theorem form_fin_inf_of (h1 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (t : _) (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w 0 (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y))) (h2 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (σ : D.what₂.LL →+* ℂ) (x : Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL),
  0 ≤ (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re ∧ ∀ y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    ((Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re)) (h3 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch C b => 0 ≤ bOne ch.G C b ∧
  (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)) : FinFormK ∧ InfFormK := by
  refine ⟨bigC_mono (bigC_and h1 h3) ?_, bigC_mono (bigC_and h2 h3) ?_⟩
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, hb, -⟩
    refine ⟨fun _ => 0, ⟨fun _ => le_rfl, by simp, fun s => by simpa using hb⟩, fun t w x hx y => ?_⟩
    exact hv t w x hx y
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, -, hK⟩ σ x y
    obtain ⟨hq, hy⟩ := hv σ x
    obtain ⟨u, e, hu⟩ := hy y
    exact ⟨u, e, hu.trans (mul_le_mul_of_nonneg_right hK hq)⟩

theorem form_fin_inf : GlobalTheory.FunPr.Hypotheses₂ → FinFormK ∧ InfFormK := fun _ =>
  form_fin_inf_of GlobalTheory.T.integralGoodForm_values_mem_scaledDualWeylLattice GlobalTheory.T.baseTupleGoodForm_values_bounded_by_classSum GlobalTheory.T.kernelLossBound_nonneg_and_level_card_le_exp

end GlobalTheory.FormVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelicStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteUnitaryPart_isInvertibleUnitaryAdelic : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  first | exact @GlobalTheory.FinUA.isUA_finHom | exact GlobalTheory.FinUA.isUA_finHom | (intros; apply GlobalTheory.FinUA.isUA_finHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSelfDualLatticeFixedFunctionsLineStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  first | exact @GlobalTheory.LatVacLine.vacuum_line | exact GlobalTheory.LatVacLine.vacuum_line | (intros; apply GlobalTheory.LatVacLine.vacuum_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanishStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_tensor_local_vanish : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl F} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  first | exact @GlobalTheory.DblTrace.trace_pairing_dbl | exact GlobalTheory.DblTrace.trace_pairing_dbl | (intros; apply GlobalTheory.DblTrace.trace_pairing_dbl <;> assumption)
end


import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

private theorem haar {n : ℕ} {U : Type} [Group U] [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (e : archCompact K n ≃ₜ* (ι → U)) (ν : Measure U) [IsProbabilityMeasure ν] (hl : ∀ k, MeasurePreserving (k * ·) ν ν)
    (hr : ∀ k, MeasurePreserving (· * k) ν ν) : IsHaarK (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := by
  have hm : Measurable e.symm := e.symm.continuous.measurable
  have hE : MeasurePreserving e.symm (Measure.pi fun _ : ι => ν) (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := ⟨hm, rfl⟩
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, fun k => ?_, fun k => ?_⟩
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hl (e k i)) (fun x => ?_) (continuous_mul_left k).measurable
    change e.symm (e k * x) = _
    rw [map_mul, e.symm_apply_apply]
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hr (e k i)) (fun x => ?_) (continuous_mul_right k).measurable
    change e.symm (x * e k) = _
    rw [map_mul, e.symm_apply_apply]

private theorem coe_arc {n : ℕ} (k : archCompact K n) :
    ((arc1 k : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (k : archGroup K n) := by
  rw [arc1, ← retract_infEmb]
  exact congrArg Subtype.val (retractOne_coe (⟨_, maxCompact_le_normOneGL k.2⟩ : normOneGL K n))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem inf_fst {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n x a b).1 =
      (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from (x.1 : ArchMatrix K n)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_infEmb]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

private theorem inf_snd {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    (infEmb K n x a b).2 = (1 : Matrix (Fin n) (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_snd, prodEquiv_infEmb]
  rfl

omit [Fintype ι] in
private theorem ent (C : Co K ι) {n : ℕ} (x : ι → unitaryGroup (Fin n) ℂ) (i : ι) (a b : Fin n) :
    C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n ((C.Φ n).symm x : archCompact K n) a b).1) i =
      (x i : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [inf_fst, ← C.Ψ_val, ← C.Φ_val, ContinuousMulEquiv.apply_symm_apply]

omit [Fintype ι] in
private theorem blkA (C : Co K ι) (a b : ι → U2) :
    lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i)) := by
  apply Subtype.ext
  rw [(blkLaws (K := K)).1, neg_zero, zt0, mul_one, mul_one, coe_arc, coe_arc, coe_arc]
  ext r s
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective r
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective s
  refine Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace K).injective (C.c.injective (funext fun i => ?_))) ?_
  · rw [ent, u4.1]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact ent C a i r s
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · exact ent C b i r s
  · rw [inf_snd, ← Matrix.submatrix_apply (1 : Matrix _ _ _) finSumFinEquiv finSumFinEquiv, Matrix.submatrix_one_equiv,
      ← Matrix.fromBlocks_one]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact inf_snd _ r s
    · rfl
    · rfl
    · exact inf_snd _ r s

private theorem cmm {n : ℕ} (g : archGroup K n) (h : FA K n) : Commute (archP K n g) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h g).symm

private theorem dec (n : ℕ) (k : G1 K n) (hk : k ∈ KG K n) :
    ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  have hk' : (k : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact := hk
  have e := infEmb_infPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n)
  have hf : finEmb K n (finPart K n k) ∈ Reduction.maxCompact := by
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have : infAt w (finEmb K n (finPart K n k)) = 1 := by
        refine Units.ext (Matrix.ext fun a b => ?_)
        change (finEmb K n (finPart K n k) a b).1 w = _
        rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_finEmb]
        by_cases h : a = b
        · subst h; simp; rfl
        · simp [h]; rfl
      rw [this]; exact one_mem _
    · have : finAt v (finEmb K n (finPart K n k)) = finAt v (k : AdelicGLn.AdelicGL K n) := by
        exact Units.ext (Matrix.ext fun a b => rfl)
      rw [this]; exact hk'.2 v
  refine ⟨⟨infPart K n k, ?_⟩, finPart K n k, (AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, Subtype.ext ?_⟩
  · change infEmb K n (infPart K n k) ∈ Reduction.maxCompact
    rw [eq_mul_inv_of_mul_eq e]
    exact mul_mem hk' (inv_mem hf)
  · have : (AdelicGLn.finiteRestrictedEquiv K n (finPart K n k) v : GL (Fin n) (v.adicCompletion K)) =
        finAt v (k : AdelicGLn.AdelicGL K n) := by
      exact Units.ext (Matrix.ext fun a b => rfl)
    rw [this]; exact hk'.2 v
  · rw [Subgroup.coe_mul, coe_arc, fin1, MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL hf)]
    exact e.symm

private noncomputable def GG (C : Co K ι) : (ι → GL (Fin 2) ℂ) →* G1 K 2 := (archP K 2).comp (C.Ψ 2).symm.toMonoidHom

omit [Fintype ι] in
private theorem gl_eq (C : Co K ι) (i : ι) (a : GL (Fin 2) ℂ) : C.gl i a = GG C (Pi.mulSingle i a) := rfl

omit [Fintype ι] in
private theorem GG_eq (C : Co K ι) (g : archGroup K 2) : archP K 2 g = GG C (C.Ψ 2 g) :=
  congrArg (archP K 2) ((C.Ψ 2).symm_apply_apply g).symm

omit [Fintype ι] in
private theorem GG_cmm (C : Co K ι) (x : ι → GL (Fin 2) ℂ) (h : FA K 2) : Commute (GG C x) (fin1 h) := cmm _ h

omit [Fintype ι] in
private theorem ms_cont (i : ι) : Continuous fun m : GL (Fin 2) ℂ => (Pi.mulSingle i m : ι → GL (Fin 2) ℂ) :=
  continuous_pi fun j => by
    by_cases h : j = i
    · subst h; simpa using continuous_id'
    · simpa [h] using continuous_const

omit [Fintype ι] in
private theorem spl (C : Co K ι) (i : ι) (g : G1 K 2) : ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b) := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj g
  obtain ⟨x, hx⟩ : ∃ x, archProj K 2 A = GG C x := ⟨_, GG_eq C ⟨A, Subgroup.mem_top _⟩⟩
  refine ⟨x i, GG C (Function.update x i 1) * fin1 u, ?_, fun b => Commute.mul_left ?_ ?_⟩
  · have : Pi.mulSingle i (x i) * Function.update x i 1 = x := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [gl_eq, ← mul_assoc, ← map_mul, this, hx]
  · rw [gl_eq]
    refine Commute.map ?_ (GG C)
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [gl_eq]
    exact (GG_cmm C _ u).symm

omit [Fintype ι] in
private theorem lst (C : Co K ι) (g : archGroup K 2) :
    ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod := by
  refine ⟨C.Ψ 2 g, fun l hl hm => ?_⟩
  rw [GG_eq C]
  generalize C.Ψ 2 g = x
  have : (l.map fun i => (Pi.mulSingle i (x i) : ι → GL (Fin 2) ℂ)).prod = x := by
    funext j
    rw [Pi.list_prod_apply, List.map_map, List.prod_map_eq_pow_single j, List.count_eq_one_of_mem hl (hm j)]
    · simp
    · intro i hi _
      simp [hi.symm]
  conv_lhs => rw [← this, map_list_prod, List.map_map]
  rfl

omit [Fintype ι] in
private theorem un_eq (C : Co K ι) (i : ι) (m : U2) : C.un i m = C.gl i (kC m) := by
  refine congrArg (archP K 2) ((C.Ψ 2).injective (funext fun j => Units.ext ?_))
  rw [← C.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι), IsHaarK C.κ₂ ∧ (∀ μ, Haar4 μ → IsHaarK (C.κ₄ μ)) ∧ (∀ i m, C.un i m = C.gl i (kC m)) ∧ (∀ i, Continuous (C.gl i)) ∧
      (∀ i a b, C.gl i (a * b) = C.gl i a * C.gl i b) ∧ (∀ i j, i ≠ j → ∀ a b, Commute (C.gl i a) (C.gl j b)) ∧
      (∀ i a (h : FA K 2), Commute (C.gl i a) (fin1 h)) ∧ (∀ i (g : G1 K 2), ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b)) ∧
      (∀ g : archGroup K 2, ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod) ∧
      (∀ a b : ι → U2, lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i))) ∧
      (∀ n (k : archCompact K n) (h : FA K n), Commute (arc1 k) (fin1 h)) ∧
      ∀ n, ∀ k ∈ KG K n, ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  intro K _ _ _ ι _ C
  refine ⟨haar _ _ (measurePreserving_mul_left μK) (measurePreserving_mul_right μK), fun μ hμ => ?_, un_eq C, fun i => ?_,
    fun i a b => ?_, fun i j hij a b => ?_, fun i a h => cmm _ h, spl C, lst C, blkA C, fun n k h => cmm _ h, dec⟩
  · haveI := hμ.prob
    exact haar _ μ hμ.left hμ.right
  · exact continuous_archP.comp ((C.Ψ 2).symm.continuous.comp (ms_cont i))
  · rw [gl_eq, gl_eq, gl_eq, Pi.mulSingle_mul, map_mul]
  · rw [gl_eq, gl_eq]
    exact (Pi.mulSingle_commute (f := fun _ => GL (Fin 2) ℂ) hij a b).map (GG C)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefIdem
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem chi_mul_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi ν θ * chi ν (-θ) = 1 := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  simp

private theorem chi_mul_conj (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi ν θ * conj (chi ν θ) = 1 := by
  have h : conj (chi ν θ) = chi ν (-θ) := by
    unfold chi
    rw [← Complex.exp_conj, map_mul, map_sum, Complex.conj_I]
    congr 1
    simp only [map_mul, map_intCast, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
  rw [h, chi_mul_neg]

private theorem int_zero {μ : Measure U4} (hH : Haar4 μ) {ν ν' : Fin (2 + 2) → ℤ} (hne : ν ≠ ν') (F : U4 → ℂ)
    (hF : ∀ θ h, chi ν' θ * F (dg θ * h) = chi ν θ * F h) : ∫ h, F h ∂μ = 0 := by
  obtain ⟨θ, hθ⟩ : ∃ θ, chi ν θ ≠ chi ν' θ := by
    by_contra hc
    push_neg at hc
    exact hne (u4.2.2.2.2.2.2.2.2.2.2.1 ν ν' hc)
  have hT : ∫ h, F (dg θ * h) ∂μ = ∫ h, F h ∂μ :=
    (hH.left (dg θ)).integral_comp (Homeomorph.mulLeft (dg θ)).measurableEmbedding F
  have h1 : chi ν' θ * ∫ h, F h ∂μ = chi ν θ * ∫ h, F h ∂μ :=
    calc chi ν' θ * ∫ h, F h ∂μ = chi ν' θ * ∫ h, F (dg θ * h) ∂μ := by rw [hT]
      _ = ∫ h, chi ν' θ * F (dg θ * h) ∂μ := (integral_const_mul _ _).symm
      _ = ∫ h, chi ν θ * F h ∂μ := integral_congr_ae (Eventually.of_forall fun h => hF θ h)
      _ = chi ν θ * ∫ h, F h ∂μ := integral_const_mul _ _
  have h2 : (chi ν θ - chi ν' θ) * ∫ h, F h ∂μ = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hθ)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefIdem :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → Continuous ψ ∧ ψ 1 = 1 ∧ Idem μ (eOf μ ψ) ∧ RFix μ (eOf μ ψ) ψ := by
  intro μ ψ n q n' q' hH hO hC
  haveI : CompactSpace U4 := u4.2.2.2.2.2.2.2.2.2.2.2.1
  haveI : IsProbabilityMeasure μ := hH.prob
  obtain ⟨J, _, j₀, a, b, ν, hcont, hexp, ha0, hb0, hν0, hw, -, hne⟩ := hC.exp
  have hψc : Continuous ψ := ha0 ▸ (hcont j₀).1
  have hψ1 : ψ 1 = 1 := by
    have h := hC.res 1 1
    rw [u4.2.2.1, KT.psi_one, KT.psi_one, mul_one] at h
    exact h
  have hint : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinv : Continuous fun h : U4 => h⁻¹ := continuous_inv
  have hψdg : ∀ θ h, ψ (dg θ * h) = chi (wt n q n' q') θ * ψ h := fun θ h => by
    have := (hw j₀ θ h).2.1
    rwa [ha0] at this
  set c : ℝ := ∫ h, ‖ψ h‖ ^ 2 ∂μ with hc
  have hcpos : 0 < c := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : U4)) (by fun_prop)
      (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) ?_
    simp [hψ1]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hmc : ∀ h, ψ h * conj (ψ h) = ((‖ψ h‖ ^ 2 : ℝ) : ℂ) := fun h => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcC : ∫ h, ψ h * conj (ψ h) ∂μ = (c : ℂ) := by
    simp_rw [hmc]
    exact integral_complex_ofReal
  have key1 : ∀ k, ∫ h, ψ h * ψ (h⁻¹ * k) ∂μ = c * ψ k := fun k => by
    have e1 : ∀ h, ψ h * ψ (h⁻¹ * k) = ∑ j, (ψ h * a j h⁻¹) * b j k := fun h => by
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
    simp_rw [e1]
    rw [integral_finset_sum (μ := μ) Finset.univ (f := fun j h => ψ h * a j h⁻¹ * b j k) fun j _ =>
      hint _ ((hψc.mul ((hcont j).1.comp hinv)).mul continuous_const)]
    simp_rw [integral_mul_const]
    rw [Finset.sum_eq_single j₀]
    · rw [ha0, hb0]
      congr 1
      rw [← hcC]
      exact integral_congr_ae (Eventually.of_forall fun h => by
        show ψ h * ψ h⁻¹ = ψ h * conj (ψ h)
        rw [hC.star])
    · intro j _ hj
      rw [int_zero hH (ν := wt n q n' q') (ν' := ν j) (Ne.symm (hν0 ▸ hne j hj)) _ ?_, zero_mul]
      intro θ h
      rw [_root_.mul_inv_rev, u4.2.2.2.2.2.2.2.2.2.1, hψdg, (hw j (-θ) h⁻¹).1]
      have := chi_mul_neg (ν j) θ
      linear_combination (chi (wt n q n' q') θ * ψ h * a j h⁻¹) * this
    · intro h
      exact absurd (Finset.mem_univ _) h
  have key2 : ∀ g, ∫ k, conj (ψ k) * ψ (g * k) ∂μ = c * ψ g := fun g => by
    have e1 : ∀ k, conj (ψ k) * ψ (g * k) = ∑ j, a j g * (conj (ψ k) * b j k) := fun k => by
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e1]
    rw [integral_finset_sum (μ := μ) Finset.univ (f := fun j k => a j g * (conj (ψ k) * b j k)) fun j _ =>
      hint _ (continuous_const.mul ((Complex.continuous_conj.comp hψc).mul (hcont j).2))]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single j₀]
    · rw [ha0, hb0, mul_comm]
      congr 1
      rw [← hcC]
      exact integral_congr_ae (Eventually.of_forall fun h => mul_comm _ _)
    · intro j _ hj
      rw [int_zero hH (ν := ν j) (ν' := wt n q n' q') (hν0 ▸ hne j hj) _ ?_, mul_zero]
      intro θ k
      rw [hψdg, (hw j θ k).2.2, map_mul]
      have := chi_mul_conj (wt n q n' q') θ
      linear_combination (conj (ψ k) * chi (ν j) θ * b j k) * this
    · intro h
      exact absurd (Finset.mem_univ _) h
  have heOf : ∀ k, eOf μ ψ k = (c : ℂ)⁻¹ * conj (ψ k) := fun k => rfl
  refine ⟨hψc, hψ1, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact continuous_const.mul (Complex.continuous_conj.comp hψc)
  · intro k
    rw [heOf, heOf, hC.star, map_mul, map_inv₀, Complex.conj_ofReal]
  · intro k
    have e1 : ∀ h, eOf μ ψ h * eOf μ ψ (h⁻¹ * k) = ((c : ℂ)⁻¹ * (c : ℂ)⁻¹) * conj (ψ h * ψ (h⁻¹ * k)) := fun h => by
      rw [heOf, heOf, map_mul]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_conj, key1, heOf, map_mul, Complex.conj_ofReal]
    field_simp
  · intro g
    have e1 : ∀ k, eOf μ ψ k * ψ (g * k) = (c : ℂ)⁻¹ * (conj (ψ k) * ψ (g * k)) := fun k => by
      rw [heOf, mul_assoc]
    simp_rw [e1]
    rw [integral_const_mul, key2]
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.ExpBasic
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem sum_fin_four_expand {M : Type} [AddCommMonoid M] (f : Fin (2 + 2) → M) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

private theorem eb_dg (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i) :=
  u4.2.2.2.2.2.2.2.1 θ

private theorem eb_chi_single (j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) :
    chi (Pi.single j 1) θ = Complex.exp (Complex.I * θ j) := by
  unfold chi
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem eb_chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

private theorem eb_chi_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (-ν) θ = conj (chi ν θ) := by
  unfold chi
  rw [← Complex.exp_conj]
  congr 1
  simp [map_sum]

private theorem eb_right (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (h * dg θ) = chi (Pi.single j 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, mul_diagonal, mul_comm]

private theorem eb_left (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (dg θ * h) = chi (Pi.single i 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, diagonal_mul]

private theorem eb_mul (π : Equiv.Perm (Fin (2 + 2))) (i j : Fin (2 + 2)) (h k : U4) :
    en i j (h * k) = ∑ s, en i (π s) h * en (π s) j k := by
  unfold en
  rw [Submonoid.coe_mul, Matrix.mul_apply]
  exact (Equiv.sum_comp π fun s => (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) i s * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) s j).symm

private theorem eb_cont (i j : Fin (2 + 2)) : Continuous (en i j) :=
  (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_elem i j

private theorem eb_pair (j : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) : ∑ i, (Pi.single j 1 : Fin (2 + 2) → ℤ) i * f i = f j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem eb_pairπ (π : Equiv.Perm (Fin (2 + 2))) (s : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) :
    ∑ i, (Pi.single (π s) 1 : Fin (2 + 2) → ℤ) (π i) * f i = f s := by
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (π.injective.ne hb)]
  · simp

private theorem eb_top (z : Fin (2 + 2) → ℤ) (hz : Antitone z) (s t : Fin (2 + 2)) (hst : s ≠ t) : z s + z t ≤ z 0 + z 1 := by
  have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
  have h1 : ∀ u : Fin (2 + 2), u ≠ 0 → (1 : Fin (2 + 2)) ≤ u := by decide
  by_cases hs : s = 0
  · have ht : t ≠ 0 := fun h => hst (hs.trans h.symm)
    have := hz (h0 s)
    have := hz (h1 t ht)
    omega
  · have := hz (h0 t)
    have := hz (h1 s hs)
    omega

private theorem eb_one (π : Equiv.Perm (Fin (2 + 2))) : OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 0, fun s => en (π 0) (π s), fun s => en (π s) (π 0), fun s => Pi.single (π s) 1,
    fun s => ⟨eb_cont _ _, eb_cont _ _⟩, fun h k => eb_mul π _ _ h k, rfl, rfl, rfl,
    fun s θ h => ⟨eb_right _ _ _ _, eb_left _ _ _ _, eb_left _ _ _ _⟩, fun s w y hy => ?_, fun s hs => ?_⟩
  · rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · beta_reduce
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ)]
    revert s
    decide

private theorem eb_three (π : Equiv.Perm (Fin (2 + 2))) : OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 3, fun s k => conj (en (π 3) (π s) k), fun s k => conj (en (π s) (π 3) k),
    fun s => -Pi.single (π s) 1,
    fun s => ⟨Complex.continuous_conj.comp (eb_cont _ _), Complex.continuous_conj.comp (eb_cont _ _)⟩, fun h k => ?_, rfl, rfl, rfl,
    fun s θ h => ?_, fun s w y hy => ?_, fun s hs => ?_⟩
  · simp only [eb_mul π, map_sum, map_mul]
  · simp only [eb_right, eb_left, eb_chi_neg, map_mul, and_self]
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), u ≤ (3 : Fin (2 + 2)) := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 3 fun i => -(i : ℤ)]
    revert s
    decide

private def ebS : Fin 6 → Fin (2 + 2) := ![0, 0, 0, 1, 1, 2]

private def ebT : Fin 6 → Fin (2 + 2) := ![1, 2, 3, 2, 3, 3]

private theorem eb_two (π : Equiv.Perm (Fin (2 + 2))) :
    OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k)
      (Pi.single (π 0) 1 + Pi.single (π 1) 1) := by
  refine ⟨Fin 6, inferInstance, 0,
    fun p k => en (π 0) (π (ebS p)) k * en (π 1) (π (ebT p)) k - en (π 0) (π (ebT p)) k * en (π 1) (π (ebS p)) k,
    fun p k => en (π (ebS p)) (π 0) k * en (π (ebT p)) (π 1) k - en (π (ebS p)) (π 1) k * en (π (ebT p)) (π 0) k,
    fun p => Pi.single (π (ebS p)) 1 + Pi.single (π (ebT p)) 1,
    fun p => ⟨((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _)),
      ((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _))⟩, fun h k => ?_, rfl, rfl, rfl,
    fun p θ h => ?_, fun p w y hy => ?_, fun p hp => ?_⟩
  · simp only [eb_mul π, sum_fin_four_expand, Fin.sum_univ_six, ebS, ebT, Matrix.cons_val]
    ring
  · simp only [eb_right, eb_left, eb_chi_add]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pair (π (ebS p)) fun i => y (w i), eb_pair (π (ebT p)) fun i => y (w i), eb_pair, eb_pair]
    have hne : ∀ p, ebS p ≠ ebT p := by decide
    simpa using eb_top _ hy (π.symm (w (π (ebS p)))) (π.symm (w (π (ebT p))))
      (π.symm.injective.ne (w.injective.ne (π.injective.ne (hne p))))
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pairπ π (ebS p) fun i => -(i : ℤ), eb_pairπ π (ebT p) fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ),
      eb_pairπ π 1 fun i => -(i : ℤ)]
    revert p
    decide

private theorem eb_det_dg (δ : ℤ) (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ = chi (fun _ => δ) θ := by
  unfold chi
  rw [eb_dg, det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  ring

private theorem eb_four (π : Equiv.Perm (Fin (2 + 2))) (δ : ℤ) :
    OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  have hc : Continuous fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ :=
    (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_det.zpow₀ δ fun k =>
      Or.inl (Matrix.UnitaryGroup.det_isUnit k).ne_zero
  have hm : ∀ h k : U4, ((h * k : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ =
      (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ := fun h k => by
    rw [Submonoid.coe_mul, det_mul, mul_zpow]
  refine ⟨Unit, inferInstance, (), fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ,
    fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ, fun _ _ => δ, fun _ => ⟨hc, hc⟩, fun h k => ?_, rfl, rfl, rfl,
    fun _ θ h => ?_, fun _ w y _ => ?_, fun _ hs => absurd rfl hs⟩
  · simp only [hm, Finset.univ_unique, Finset.sum_singleton]
  · simp only [hm, eb_det_dg, and_self, and_true]
    exact mul_comm _ _
  · exact (Equiv.sum_comp w fun i => δ * y i).le

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expBasic :
    ∀ π : Equiv.Perm (Fin (2 + 2)), OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) ∧
      OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k) (Pi.single (π 0) 1 + Pi.single (π 1) 1) ∧
      OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) ∧ ∀ δ : ℤ, OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  intro π
  exact ⟨eb_one π, eb_two π, eb_three π, eb_four π⟩
end


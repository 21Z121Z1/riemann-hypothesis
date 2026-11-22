import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0158
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerIntegralEqVolumeMulIntegralPer
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.WhitCollapse

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_normF (A : Et F E) : Continuous (fun t : A.K => Algebra.norm F t) := by
  classical
  let b := Module.finBasis F A.K
  have h : (fun t : A.K => Algebra.norm F t) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : A.K => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight F (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight F (b j)))

theorem norm_eta (x : F) : ‖eta x‖ = 1 := by
  unfold eta; split_ifs <;> simp

theorem measurable_etaK [Unram F E] (A : Et F E) : Measurable A.etaK := by
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  obtain ⟨-, -, -, hlc⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hc : ContinuousOn (eta : F → ℂ) {0}ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    exact hlc.continuous
  have hm : Measurable (eta : F → ℂ) := measurable_of_continuousOn_compl_singleton 0 hc
  exact hm.comp (continuous_normF A).measurable

theorem collapse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ (a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK) * A.psiK ψ (-(a * z)) ∂μK = (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * ∫ t, (∫ b, φ' (b, t) * Set.indicator {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ U A ψ hψ μK hμ φ' hφ a c hc
  have := U.charZero; have := U.ultraF; have := U.lcF
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOKo, hOKc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hψc := GlobalTheory.FourKFub.psiK_continuous A ψ hψ
  have hηm := measurable_etaK A
  have hφc : Continuous φ' := hφ.1.continuous
  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)
  have hMset : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z
    show c • z ∈ (R : Set A.K) ↔ c • z ∈ A.OK
    rw [hR]
  have hMo : IsOpen (M : Set A.K) := by rw [hMset]; exact hOKo.preimage (continuous_const_smul c)
  have hMc : IsCompact (M : Set A.K) := by
    rw [hMset]
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z; constructor
      · intro h; exact ⟨c • z, h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        simpa [smul_smul, mul_inv_cancel₀ hc] using hw
    rw [this]; exact hOKc.image (continuous_const_smul _)
  have hMm : MeasurableSet (M : Set A.K) := hMo.measurableSet
  have hMcl : IsClosed (M : Set A.K) := hMc.isClosed
  set χ : A.K → ℂ := (M : Set A.K).indicator (fun _ => 1) with hχdef
  have hχc : Continuous χ := IsClopen.continuous_indicator ⟨hMcl, hMo⟩ continuous_const
  let K0 : A.K × (A.K × A.K) → ℂ := fun q =>
    χ q.1 * φ' (q.2.2, q.2.1) * A.psiK ψ (q.2.1 * q.1 * q.2.2) * A.psiK ψ (-(a * q.1))
  have hK0c : Continuous K0 := by fun_prop
  have hK0s : HasCompactSupport K0 := by
    refine HasCompactSupport.intro (hMc.prod (hφ.2.isCompact.image continuous_swap)) ?_
    rintro ⟨z, t, b⟩ hq
    simp only [Set.mem_prod, not_and_or] at hq
    rcases hq with hz | hp
    · simp [K0, χ, hz]
    · have : φ' (b, t) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(b, t), h, rfl⟩)
      simp [K0, this]
  have hK0i : Integrable K0 (μK.prod (μK.prod μK)) := hK0c.integrable_of_hasCompactSupport hK0s
  let H : A.K × (A.K × A.K) → ℂ := fun q => K0 q * A.etaK q.2.1
  have hH : Integrable H (μK.prod (μK.prod μK)) :=
    hK0i.mul_bdd (c := 1) (hηm.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall fun q => (norm_eta _).le)

  have hsymm : (Algebra.traceForm F A.K).IsSymm := ⟨fun x y => by simp [mul_comm]⟩
  have hI := fun y => ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) hsymm hnd μK hμ).1 M hMo hMc).2 y
  set N : Set A.K := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hNdef
  have hN : {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} = N := by
    ext y
    simp only [Set.mem_setOf_eq, N, Algebra.traceForm_apply]
    constructor
    · intro h x hx; exact h x (by rw [← SetLike.mem_coe, hMset]; exact hx)
    · intro h x hx; exact h x (by rw [← SetLike.mem_coe, hMset] at hx; exact hx)
  set vol : ℂ := (((μK (M : Set A.K)).toReal : ℝ) : ℂ) with hvol
  let Q : A.K × A.K → ℂ := fun p => vol * (φ' (p.2, p.1) * N.indicator (fun _ => (1 : ℂ)) (p.1 * p.2 - a) * A.etaK p.1)
  have h3 : ∀ p : A.K × A.K, ∫ z, H (z, p) ∂μK = Q p := by
    rintro ⟨t, b⟩
    have e1 : ∀ z, H (z, (t, b)) = (φ' (b, t) * A.etaK t) *
        (M : Set A.K).indicator (fun z => ψ (Algebra.traceForm F A.K z (t * b - a))) z := by
      intro z
      by_cases hz : z ∈ (M : Set A.K)
      · rw [Set.indicator_of_mem hz]
        simp only [H, K0, χ, Set.indicator_of_mem hz, Algebra.traceForm_apply]
        have : A.psiK ψ (t * z * b) * A.psiK ψ (-(a * z)) = ψ (Algebra.trace F A.K (z * (t * b - a))) := by
          rw [← GlobalTheory.FourKFub.psiK_add]; simp only [Et.psiK]; congr 2; ring
        linear_combination (φ' (b, t) * A.etaK t) * this
      · simp [H, K0, χ, hz]
    simp_rw [e1]
    rw [integral_const_mul, integral_indicator hMm, hI, hN]
    simp only [Q]
    by_cases hy : t * b - a ∈ N
    · simp [Set.indicator_of_mem hy, vol]; ring
    · simp [Set.indicator_of_notMem hy]
  have hQi : Integrable Q (μK.prod μK) :=
    (hH.integral_prod_right (f := H)).congr (Eventually.of_forall h3)
  rw [← hMset, ← integral_indicator hMm]
  trans ∫ z, ∫ p, H (z, p) ∂(μK.prod μK) ∂μK
  · refine integral_congr_ae ?_
    filter_upwards [hH.prod_right_ae] with z hz
    rw [integral_prod _ hz]
    by_cases hzM : z ∈ (M : Set A.K)
    · rw [Set.indicator_of_mem hzM, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [H, K0, χ, Set.indicator_of_mem hzM]
      rw [← integral_mul_const, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      simp only
      ring
    · simp [Set.indicator_of_notMem hzM, H, K0, χ]
  rw [integral_integral_swap (f := fun z p => H (z, p)) hH]
  simp_rw [h3]
  rw [integral_prod Q hQi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Q, vol]
  rw [← integral_mul_const, ← integral_const_mul]

end GlobalTheory.WhitCollapse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step

section Blocks
variable {r : ℕ} {E : Type} [Field E]

theorem embHom_castSucc_castSucc (M : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.castSucc b) = M a b := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_castSucc_last (M : Matrix (Fin r) (Fin r) E) (a : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.last r) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_castSucc (M : Matrix (Fin r) (Fin r) E) (b : Fin r) :
    embHom r E M (Fin.last r) (Fin.castSucc b) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_last (M : Matrix (Fin r) (Fin r) E) :
    embHom r E M (Fin.last r) (Fin.last r) = 1 := by
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, hb]

theorem eq_embHom_of_last (h : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : ∀ i, h i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hr : ∀ j, h (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    h = embHom r E (h.submatrix Fin.castSucc Fin.castSucc) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [embHom_last_last, hr]; simp
    | cast b => rw [embHom_last_castSucc, hr]; simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [embHom_castSucc_last, hc]; simp [Fin.castSucc_ne_last]
    | cast b => rw [embHom_castSucc_castSucc]; rfl

end Blocks

end GlobalTheory.JR.Step

namespace GlobalTheory.JR.Step

section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem actU_liftH_support {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1)
    (g : Matrix.unitaryGroup (Fin (r + 1)) E)
    (hg : unitU (r + 1) F E (actU g (liftH X ν l)) ≠ 0) :
    ∃ k ∈ uO (r + 1) E, ∃ s, g = k * uEmb r E s := by
  have hmem := Set.mem_of_indicator_ne_zero hg
  have hv : ∀ i, ‖(g.1 *ᵥ (ν • eL r E)) i‖ ≤ 1 := hmem.2.1
  set v : Fin (r + 1) → E := fun i => g.1 i (Fin.last r) with hvdef
  have hgv : g.1 *ᵥ eL r E = v := by
    funext i; simp [eL, Matrix.mulVec_single_one, v]
  have hint : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have := hv i
    rw [Matrix.mulVec_smul, hgv, Pi.smul_apply, smul_eq_mul, norm_mul, hν, one_mul] at this
    exact this
  have hunit : star v ⬝ᵥ v = 1 := by
    have h1 : (star g.1 * g.1) (Fin.last r) (Fin.last r) = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.mp g.2]; simp
    rw [← h1]
    simp [dotProduct, Matrix.mul_apply, v, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  obtain ⟨k, hk, hke⟩ := GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors F E r v hint hunit
  set h := k⁻¹ * g with hh
  have he : h.1 *ᵥ eL r E = eL r E := by
    have hgk : g.1 *ᵥ eL r E = k.1 *ᵥ eL r E := by rw [hgv]; exact hke.symm
    have hk1 : (k⁻¹).1 = star k.1 := rfl
    calc h.1 *ᵥ eL r E = star k.1 *ᵥ (g.1 *ᵥ eL r E) := by
          rw [Matrix.mulVec_mulVec, ← hk1]; rfl
      _ = star k.1 *ᵥ (k.1 *ᵥ eL r E) := by rw [hgk]
      _ = eL r E := by rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp k.2, Matrix.one_mulVec]
  have hse : star h.1 *ᵥ eL r E = eL r E := by
    conv_lhs => rw [← he]
    rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp h.2, Matrix.one_mulVec]
  have hc : ∀ i, h.1 i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
    intro i
    have := congrFun he i
    simpa [eL, Matrix.mulVec_single_one, Pi.single_apply] using this
  have hr : ∀ j, h.1 (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j
    have h0 := congrArg star (congrFun hse j)
    simp only [eL, Matrix.mulVec_single_one, Pi.single_apply, Matrix.star_eq_conjTranspose] at h0
    have h3 : star ((h.1)ᴴ.col (Fin.last r) j) = h.1 (Fin.last r) j := by
      simp [Matrix.col, Matrix.conjTranspose_apply]
    rw [← h3, h0]
    split_ifs <;> simp
  set S := h.1.submatrix Fin.castSucc Fin.castSucc with hSdef
  have hS : h.1 = embHom r E S := eq_embHom_of_last h.1 hc hr
  have hstar : star (embHom r E S) = embHom r E (star S) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  have h1 : embHom r E (S * star S) = 1 := by
    rw [map_mul, ← hstar, ← hS]; exact Matrix.mem_unitaryGroup_iff.mp h.2
  have hSu : S ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    have h2 := congrFun (congrFun h1 (Fin.castSucc a)) (Fin.castSucc b)
    rw [embHom_castSucc_castSucc] at h2
    rw [h2]
    simp [Matrix.one_apply, Fin.castSucc_inj]
  refine ⟨k, hk, ⟨S, hSu⟩, ?_⟩
  have hu : uEmb r E ⟨S, hSu⟩ = h := Subtype.ext hS.symm
  rw [hu, hh, mul_inv_cancel_left]

end Main

end GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s :=
  fun X ν l hν g hg => GlobalTheory.JR.Step.actU_liftH_support X ν l hν g hg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsEqOfPowPredEqOfValOne
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory

theorem eq_of_pow_pred_eq_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊤) (l : ℕ) (hl : 0 < l) (hlI : (l : R) ∈ I) (a b : R)
    (hab : a ^ (l - 1) = b ^ (l - 1)) (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) : a = b := by
  by_contra hne
  have h := geom_sum₂_mul a b (l - 1)
  rw [hab, sub_self] at h
  have hs := (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have ha' : Ideal.Quotient.mk I a = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact ha
  have hb' : Ideal.Quotient.mk I b = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hb
  have hl' : (l : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hlI
  have h2 := congrArg (Ideal.Quotient.mk I) hs
  simp only [map_sum, map_mul, map_pow, ha', hb', one_pow, mul_one, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, map_zero] at h2
  rw [Nat.cast_sub hl, hl', Nat.cast_one, zero_sub, neg_eq_zero] at h2
  apply hI
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact h2

def posValIdeal {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) : Ideal ↥(OL LL) where
  carrier := {x | 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact (P.v LL).map_lt_add ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at *
    have hc : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 c) := (P.v_O LL _).2 c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

theorem oneUnit_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (a b : ↥(OL LL)) (hab : a ^ (l - 1) = b ^ (l - 1))
    (ha : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 a - 1))
    (hb : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 b - 1)) : a = b := by
  refine eq_of_pow_pred_eq_of_sub_one_mem (posValIdeal P LL) ?_ l (Fact.out : l.Prime).pos ?_ a b
    hab ?_ ?_
  · rw [Ne, Ideal.eq_top_iff_one]
    change ¬ 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 1)
    simp
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)))
    rw [map_natCast, P.v_l]
    exact zero_lt_one
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (a - 1))
    rwa [map_sub, map_one]
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (b - 1))
    rwa [map_sub, map_one]

theorem units_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (u w : (↥(OL LL))ˣ) (h : u ^ (l - 1) = w ^ (l - 1))
    (hu : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (u : ↥(OL LL)) - 1))
    (hw : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1)) : u = w := by
  apply Units.ext
  refine oneUnit_eq_of_pow_pred_eq_of_pos P LL _ _ ?_ hu hw
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]

theorem units_eq_of_pow_pred_eq_of_val_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (LL : FinExt l) (u w : (↥(OL LL))ˣ), u ^ (l - 1) = w ^ (l - 1) →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((u : ↥(OL LL)) - 1)) = 1 →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1) = 1 → u = w := by
  intro l _ P LL u w h hu hw
  rw [map_sub, map_one] at hu
  refine units_eq_of_pow_pred_eq_of_pos P LL u w h ?_ ?_
  · rw [hu]; exact zero_lt_one
  · rw [hw]; exact zero_lt_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValResultantEqDegreeMulUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B₁ B₂ : InvAlg K) (ψ₁ : K'.E →+* B₁.A) (ψ₂ : K'.E →+* B₂.A) (h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e) (h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e)) (h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e) (h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e)), (∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → (B₁.P * B₂.P).Separable → ∀ s : K'.O, (∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B₁ ψ₁ h₁ h₁').P * (overExt φ B₂ ψ₂ h₂ h₂').P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree) → val K.O (resultant B₁.P B₂.P) = d * val K'.O (resultant (overExt φ B₁ ψ₁ h₁ h₁').P (overExt φ B₂ ψ₂ h₂ h₂').P) := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr | exact GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr | (intros; apply GlobalTheory.UnitLemma.Unr.ResVal.val_resultant_unr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VolumeScaledIntegersMulVolumeDualEqOne
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.LatVol

theorem stdChar_continuous {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ y in 𝓝 x, ψ y = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)
    calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
      _ = ψ x * ψ (y - x) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ x := by rw [h1, mul_one]
  exact (continuousAt_const).congr (h.mono fun y hy => hy.symm)

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd c hc
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hψc := stdChar_continuous ψ hψ

  have hcl : IsClosed {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    have : {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} =
        ⋂ x : A.K, ⋂ (_ : c • x ∈ A.OK), {y : A.K | ψ (Algebra.trace F A.K (x * y)) = 1} := by
      ext y; simp [Et.psiK]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψc.comp (htr.comp (continuous_const.mul continuous_id))
  refine ⟨hcl.measurableSet, ?_⟩

  let M : AddSubgroup A.K := R.toAddSubgroup.comap (DistribMulAction.toAddMonoidHom A.K c)
  have hM : (M : Set A.K) = {z : A.K | c • z ∈ A.OK} := by
    ext z; simp [M, ← hR]
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMo : IsOpen (M : Set A.K) := by rw [hM]; exact hOpen.preimage hsm
  have hMc : IsCompact (M : Set A.K) := by
    have : (M : Set A.K) = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      rw [hM]; ext z; constructor
      · intro hz; exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_inv_smul₀ hc] using hw
    rw [this]; exact hCpt.image (continuous_const_smul _)
  have hk : (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) = A.kerK ψ := by
    funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
  have hsd' : SelfDual μK (fun x y : A.K => ψ (Algebra.traceForm F A.K x y)) := by rw [hk]; exact hsd
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd μK hsd.1).1
    M hMo hMc).1.1 hsd'
  have hN : {y : A.K | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} =
      {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} := by
    ext y; simp [M, ← hR, Et.psiK, Algebra.traceForm_apply]
  rw [hN, show ((M : Set A.K)) = {z : A.K | c • z ∈ A.OK} from hM] at key
  have h1 : (μK {z : A.K | c • z ∈ A.OK}).toReal * (μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal = 1 := by
    rw [← ENNReal.toReal_mul, key, ENNReal.toReal_one]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one]

end GlobalTheory.LatVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOneStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilConstantStandardHermitian_eq_one : GammaOne := by
  first | exact @GlobalTheory.JR.gammaOne_holds | exact GlobalTheory.JR.gammaOne_holds | (intros; apply GlobalTheory.JR.gammaOne_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImage
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_wdRep_pull_finite_twist :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type)
      [Group G] [Finite G] (π : Weil h →* G),
      IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ)
      (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ →
      ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  intro E Ω _ _ _ _ _ A w h G _ _ π hπ n R μ hμ
  have hsm : IsSmooth (R.comp π) :=
    IsSmooth.of_le (f := π) hπ fun σ hσ => by simp [hσ]
  have hss : ∀ σ, Module.End.IsSemisimple ((R.comp π) σ) := by
    intro σ
    have hu : IsUnit ((R.comp π) σ) := ((R.comp π).toHomUnits σ).isUnit
    refine FrobSemisimple.isSemisimple_of_pow hu (m := Nat.card G) Nat.card_pos ?_
    rw [← map_pow, MonoidHom.comp_apply, map_pow, pow_card_eq_one', map_one]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X - Polynomial.C 1)
      (Polynomial.irreducible_X_sub_C 1).squarefree (by simp)
  let b0 : WDRep h (Fin n → ℂ) :=
    { ρ := R.comp π
      N := 0
      smooth := hsm
      semisimple := hss
      nilpotent := IsNilpotent.zero
      comm := fun σ => by simp }
  exact ⟨b0.twist μ hμ, fun σ => rfl⟩

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCellStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_bound_big_cell : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  first | exact @GlobalTheory.JR.LamBound.main | exact GlobalTheory.JR.LamBound.main | (intros; apply GlobalTheory.JR.LamBound.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.lam_flip_eq_zero | exact GlobalTheory.JR.lam_flip_eq_zero | (intros; apply GlobalTheory.JR.lam_flip_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerSwapStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_integral_psiK_swap : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
  first | exact @GlobalTheory.JR.Et.whittaker_swap | exact GlobalTheory.JR.Et.whittaker_swap | (intros; apply GlobalTheory.JR.Et.whittaker_swap <;> assumption)
end


import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
section
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.TorusSymbol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma isOpen_omegaSet (n : ℕ) : IsOpen (OmegaSet n) := by
  have h : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [h]
  refine isOpen_iInter_of_finite fun i => ?_
  have hc : Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z := by
    have hi : (i : ℕ) + 1 ≤ n := i.2
    simp only [lead, dif_pos hi]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  exact isOpen_ne_fun hc continuous_const

lemma differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : DifferentiableAt ℂ F z :=
  (hF.1.contDiffAt ((isOpen_omegaSet n).mem_nhds hz)).differentiableAt (by simp)

lemma lop_add (Y : Matrix (Fin n) (Fin n) ℂ) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) (hG : G ∈ OmF n) : lop Y (F + G) = lop Y F + lop Y G := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.add_apply, if_pos hz]
    have h : fderiv ℂ (F + G) z = fderiv ℂ F z + fderiv ℂ G z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.add (differentiableAt_of_mem hG hz).hasFDerivAt).fderiv
    rw [h]
    simp only [ContinuousLinearMap.add_apply]
    ring
  · simp [lop, if_neg hz]

lemma lop_smul (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : F ∈ OmF n) : lop Y (s • F) = s • lop Y F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, Pi.smul_apply, if_pos hz]
    have h : fderiv ℂ (s • F) z = s • fderiv ℂ F z :=
      ((differentiableAt_of_mem hF hz).hasFDerivAt.const_smul s).fderiv
    rw [h]
    simp
  · simp [lop, if_neg hz]

lemma lop_sum (Y : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hf : ∀ i, f i ∈ OmF n) :
    lop Y (∑ i ∈ s, f i) = ∑ i ∈ s, lop Y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp [lop, if_pos hz]
    · simp [lop, if_neg hz]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, lop_add Y (hf i) (Submodule.sum_mem _ fun j _ => hf j), ih]

def wtL (c : Fin n) (w : List (Fin n × Fin n)) : ℝ :=
  (w.map fun p => (if p.1 = c then (1 : ℝ) else 0) - (if p.2 = c then 1 else 0)).sum

lemma lw_mem (H : HolFacts) (μ : Fin n → ℤ) (w : List (Fin n × Fin n)) : lw w (PhiO μ) ∈ OmF n := by
  induction w with
  | nil => exact (H n μ).2.2.1
  | cons p w ih => exact (H n μ).1 _ _ ih

lemma lop_lw (H : HolFacts) (μ : Fin n → ℤ) (c : Fin n) (w : List (Fin n × Fin n)) :
    lop (Matrix.single c c 1) (lw w (PhiO μ)) =
      ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lw w (PhiO μ) := by
  induction w with
  | nil =>
    have h := (H n μ).2.2.2.1 c
    simpa [wtL, lw] using h
  | cons p w ih =>
    obtain ⟨a, b⟩ := p
    have hF := lw_mem H μ w
    have rel := (H n μ).2.1 (lw w (PhiO μ)) c c a b hF
    have hlw : lw ((a, b) :: w) (PhiO μ) = lop (Matrix.single a b 1) (lw w (PhiO μ)) := rfl
    have hwt : wtL c ((a, b) :: w) =
        ((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0)) + wtL c w := by
      simp [wtL]
    rw [ih, lop_smul _ _ hF] at rel
    have rel' : lop (Matrix.single c c 1) (lop (Matrix.single a b 1) (lw w (PhiO μ))) =
        ((((μ c : ℤ) : ℝ) + wtL c w : ℝ) : ℂ) • lop (Matrix.single a b 1) (lw w (PhiO μ)) +
        ((((if a = c then (1 : ℝ) else 0) - (if b = c then 1 else 0) : ℝ)) : ℂ) •
          lop (Matrix.single a b 1) (lw w (PhiO μ)) := by
      rw [sub_eq_iff_eq_add] at rel
      rw [rel, add_comm]
      congr 1
      by_cases h1 : a = c <;> by_cases h2 : b = c
      · subst h1; subst h2; simp
      · subst h1; simp [h2]
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    rw [hlw, rel', hwt, ← add_smul]
    congr 1
    push_cast
    ring

lemma exists_tor (ε : Fin n → Bool) (θ : Fin n → ℝ) : ∃ k : KG ε, toMK k = tor θ := by
  have hH : (tor θ)ᴴ = tor (-θ) := by
    unfold tor
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply, Pi.neg_apply, RCLike.star_def, ← Complex.exp_conj]
    simp
  have hm : ∀ θ : Fin n → ℝ, tor θ * tor (-θ) = 1 := by
    intro θ
    unfold tor
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← Complex.exp_add]
    simp
  have h1 : tor θ * (tor θ)ᴴ = 1 := by rw [hH, hm]
  have h2 : (tor θ)ᴴ * tor θ = 1 := by
    have := hm (-θ)
    rwa [neg_neg, ← hH] at this
  have hJ : tor θ * Jm ε = Jm ε * tor θ := by
    unfold tor Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _
  have hUJ : inUJ ε (tor θ) := by
    unfold inUJ
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hK : tor θ ∈ Kset ε := by
    refine ⟨?_, hJ⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact h1
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨tor θ, (tor θ)ᴴ, h1, h2⟩
  let g : UJ ε := ⟨u, hUJ⟩
  exact ⟨⟨g, hK⟩, rfl⟩

lemma inner_op_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (u v : T.V) :
    inner ℂ (T.op k u) (T.op k v) = inner ℂ u v := by
  have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have : star (T.op k) (T.op k v) = v := by
    have h : (star (T.op k) * T.op k) v = v := by rw [hu]; rfl
    exact h
  rw [this]

lemma wt_eq (hR : RhoTorus) (hT : TorW) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {m : ℕ}
    {η : Fin n → ℝ} {a : AS T m}
    (ha : ∀ (θ : Fin n → ℝ) (k : KG ε), toMK k = tor θ →
      rhoA T m k a = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a)
    (x : Wd n m) (hx : inner ℂ T.w (a x) ≠ 0) (c : Fin n) : wtL c (ofW x) = η c - Λ c := by
  by_contra hne
  set v : ℝ := η c - Λ c - wtL c (ofW x) with hv
  have hv0 : v ≠ 0 := fun h => hne (by rw [hv] at h; linarith)
  set t : ℝ := Real.pi / v with ht
  have htv : t * v = Real.pi := by rw [ht]; field_simp
  set θ : Fin n → ℝ := Pi.single c t with hθ
  obtain ⟨k, hk⟩ := exists_tor ε θ
  have h1 : rhoA T m k a x = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a x := by
    rw [ha θ k hk]; rfl
  have h2 := hR n ε Λ T m θ k hk a x
  have h3 := hT n ε Λ T θ k hk
  have hS : (∑ i, (θ (x.2 i).1 - θ (x.2 i).2) : ℝ) = t * wtL c (ofW x) := by
    unfold wtL ofW
    rw [List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hθ, Pi.single_apply, Function.comp_apply]
    split_ifs <;> simp
  have hE : (∑ a, η a * θ a : ℝ) = t * η c := by
    simp [hθ, Pi.single_apply, mul_comm]
  have hL : (∑ a, Λ a * θ a : ℝ) = t * Λ c := by
    simp [hθ, Pi.single_apply, mul_comm]
  rw [hS] at h2
  rw [hE] at h1
  rw [hL] at h3
  set E1 : ℂ := Complex.exp (((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I) with hE1
  set E2 : ℂ := Complex.exp (((t * η c : ℝ) : ℂ) * Complex.I) with hE2
  set E3 : ℂ := Complex.exp (((t * Λ c : ℝ) : ℂ) * Complex.I) with hE3
  have h4 : E1 • T.op k (a x) = E2 • a x := by rw [← h2, h1]
  have h5 : E1 * inner ℂ T.w (a x) = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
    calc E1 * inner ℂ T.w (a x) = E1 * inner ℂ (T.op k T.w) (T.op k (a x)) := by rw [inner_op_op]
      _ = inner ℂ (T.op k T.w) (E1 • T.op k (a x)) := by rw [inner_smul_right]
      _ = (starRingEnd ℂ) E3 * E2 * inner ℂ T.w (a x) := by
        rw [h4, h3, inner_smul_right, inner_smul_left]; ring
  have h6 : E1 = (starRingEnd ℂ) E3 * E2 := mul_right_cancel₀ hx h5
  have h7 : (starRingEnd ℂ) E3 * E3 = 1 := by
    rw [hE3, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have h8 : E1 * E3 = E2 := by
    rw [h6]
    calc (starRingEnd ℂ) E3 * E2 * E3 = ((starRingEnd ℂ) E3 * E3) * E2 := by ring
      _ = E2 := by rw [h7, one_mul]
  have h9 : E2 = -(E1 * E3) := by
    have : ((t * η c : ℝ) : ℂ) * Complex.I = ((t * wtL c (ofW x) : ℝ) : ℂ) * Complex.I +
        ((t * Λ c : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
      rw [← htv, hv]
      push_cast
      ring
    rw [hE2, this, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h10 : E1 * E3 ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  apply h10
  have h11 : E1 * E3 = -(E1 * E3) := by rw [← h9, h8]
  have h12 : (2 : ℂ) * (E1 * E3) = 0 := by linear_combination h11
  simpa using h12

theorem betaWeight : HolFacts → RhoTorus → TorW → BetaWeight := by
  intro H hR hT n ε Λ T μ m η a ha
  refine ⟨?_, ?_⟩
  · unfold betaF
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ofW x, rfl⟩)
  · intro c
    unfold betaF
    rw [lop_sum _ _ _ fun x => Submodule.smul_mem _ _ (lw_mem H μ (ofW x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lop_smul _ _ (lw_mem H μ (ofW x)), lop_lw H]
    by_cases hx : inner ℂ T.w (a x) = 0
    · simp [hx]
    · rw [wt_eq hR hT T ha x hx c, smul_comm]
      congr 2
      push_cast
      ring

end GlobalTheory.CompanionTheory.TorusSymbol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CKContinuous
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cont_triple {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Group B]
    [IsTopologicalGroup B] (F : A × B → ℝ) (c : B → ℝ) (hF : Continuous F) (hc : Continuous c) :
    Continuous fun z : A × (B × B) => F (z.1, z.2.1) * F (z.1, z.2.2) * c (z.2.1⁻¹ * z.2.2) ^ 2 := by
  have h1 : Continuous fun z : A × (B × B) => F (z.1, z.2.1) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun z : A × (B × B) => F (z.1, z.2.2) :=
    hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun z : A × (B × B) => c (z.2.1⁻¹ * z.2.2) :=
    hc.comp (((continuous_fst.comp continuous_snd).inv).mul (continuous_snd.comp continuous_snd))
  exact (h1.mul h2).mul (h3.pow 2)

theorem cont_slice {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A × B → ℝ)
    (hf : Continuous f) (a : A) : Continuous fun b : B => f (a, b) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous (cK T) := by
  have h : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have h2 : Continuous fun k : KG ε => ‖⟪T.w, T.op k T.w⟫_ℂ‖ := (continuous_const.inner h).norm
  exact h2

theorem hI_continuous (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Continuous fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  cont_triple (fun z : UJ ε × KG ε => phiK μ (pP (toM z.1)) z.2) (cK T) (hC n ε μ) (cK_continuous T)

theorem hI_measurable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Measurable fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  (hI_continuous hC T μ).measurable

theorem hI_nonneg (hMul : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    0 ≤ hI T μ x p := by
  have a := (hMul n ε μ 0 x hx p.1).1
  have b := (hMul n ε μ 0 x hx p.2).1
  exact mul_nonneg (mul_pos a b).le (sq_nonneg _)

theorem hI_integrable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) (g : UJ ε) :
    Integrable (fun p : KG ε × KG ε => hI T μ (pP (toM g)) p) ((dk ε).prod (dk ε)) := by
  haveI : IsProbabilityMeasure (dk ε) := (dk_props ε).1
  have hc : Continuous fun p : KG ε × KG ε => hI T μ (pP (toM g)) p :=
    cont_slice (fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2)
      (hI_continuous hC T μ) g
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem hsInt : HsPs → HsPol → PhiMul → PhiCont → HsInt := by
  intro hPs hPol hMul hC n ε Λ T μ
  refine ⟨hI_measurable hC T μ, fun g => ?_⟩
  obtain ⟨⟨X, hX, hE⟩, hN⟩ := hPol n ε (toM g) g.2
  have hpd : (pP (toM g)).PosDef := by
    rw [hE]
    exact exp_noncompactPart_posDef hX
  rw [hN Λ T μ, hPs n ε Λ T μ _ hpd, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (hI_integrable hC T μ g)
      (Filter.Eventually.of_forall (hI_nonneg hMul T μ hpd))]

end GlobalTheory.CompanionTheory.RgFd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
section
noncomputable section

open Finset MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.WordFam

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem eword_smooth (hP : IsPsiFor ε lam T Ψ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), IsSmoothL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v))
  | [] => datumFunction_isSmoothL2 hP T.w v
  | p :: w => (eword_smooth hP v w).Eab p.1 p.2

def cD (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : smD ε (rreg ε) :=
  ⟨toL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v)), toL2_mem_smD_of_isSmoothL2 (eword_smooth hP v w)⟩

theorem cD_cons (hP : IsPsiFor ε lam T Ψ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (v : T.V) :
    cD hP (p :: w) v = smE ε (rreg ε) p.1 p.2 (cD hP w v) :=
  Subtype.ext (rightDerivative_toL2 (eword_smooth hP v w) p.1 p.2).symm

theorem cD_add (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (u + v) = cD hP w u + cD hP w v
  | [] => Subtype.ext (datumEmbedding_add hP T.w u v)
  | p :: w => by rw [cD_cons, cD_cons, cD_cons, cD_add hP u v w, map_add]

theorem cD_smul (hP : IsPsiFor ε lam T Ψ) (c : ℂ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (c • v) = c • cD hP w v
  | [] => Subtype.ext (datumEmbedding_smul hP T.w c v)
  | p :: w => by rw [cD_cons, cD_cons, cD_smul hP c v w, map_smul]

theorem cD_zero (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) : cD hP w (0 : T.V) = 0 := by
  simpa using cD_smul hP (0 : ℂ) (0 : T.V) w

theorem actL_eq (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) :
    actL T Ψ a = ∑ x, (cD hP (ofW x) (a x) : L2 ε) := by
  have h := toL2_finset_sum_of_memLp (ε := ε) univ
    (fun x : Wd n m => Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)))
    (fun x => (eword_smooth hP (a x) (ofW x)).2 [])
  have e : actF T Ψ a = fun g => ∑ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)) g := by
    funext g
    exact Finset.sum_apply _ _ _
  unfold actL
  rw [e]
  exact h

theorem ofW_inj {m : ℕ} {x y : Wd n m} (h : ofW x = ofW y) : x = y := by
  obtain ⟨⟨l, hl⟩, w⟩ := x
  obtain ⟨⟨l', hl'⟩, w'⟩ := y
  have hlen : l = l' := by simpa [ofW] using congrArg List.length h
  subst hlen
  have : w = w' := List.ofFn_injective h
  subst this
  rfl

open Classical in

def sgl (m : ℕ) (w : List (Fin n × Fin n)) (v : T.V) : AS T m := fun y => if ofW y = w then v else 0

theorem actL_sgl (hP : IsPsiFor ε lam T Ψ) {m : ℕ} {w : List (Fin n × Fin n)} (h : w.length ≤ m) (v : T.V) :
    actL T Ψ (sgl m w v) = (cD hP w v : L2 ε) := by
  have hx0 : ofW (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m) = w := List.ofFn_get w
  rw [actL_eq hP, Finset.sum_eq_single (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m)]
  · simp only [sgl, hx0, if_true]
  · intro y _ hy
    have hne : ofW y ≠ w := fun e => hy (ofW_inj (e.trans hx0.symm))
    simp only [sgl, if_neg hne, cD_zero]
    rfl
  · intro hn
    exact absurd (Finset.mem_univ _) hn

def actLin (hP : IsPsiFor ε lam T Ψ) (m : ℕ) : AS T m →ₗ[ℂ] L2 ε where
  toFun := actL T Ψ
  map_add' a b := by
    simp only [actL_eq hP, Pi.add_apply, cD_add, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [actL_eq hP, Pi.smul_apply, cD_smul, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

theorem actLin_apply (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) : actLin hP m a = actL T Ψ a := rfl

theorem pad (hP : IsPsiFor ε lam T Ψ) {m m' : ℕ} (h : m ≤ m') (a : AS T m) :
    ∃ a' : AS T m', actL T Ψ a' = actL T Ψ a := by
  refine ⟨∑ x : Wd n m, sgl m' (ofW x) (a x), ?_⟩
  rw [← actLin_apply hP, map_sum, actL_eq hP a]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [actLin_apply, actL_sgl hP]
  have : (ofW x).length = x.1 := by simp [ofW]
  have h2 := x.1.2
  omega

def exS (hP : IsPsiFor ε lam T Ψ) : Submodule ℂ (smD ε (rreg ε)) where
  carrier := {x | ∃ (m : ℕ) (a : AS T m), (x : L2 ε) = actL T Ψ a}
  add_mem' := by
    rintro x y ⟨m, a, ha⟩ ⟨m', b, hb⟩
    obtain ⟨a', ea⟩ := pad hP (le_max_left m m') a
    obtain ⟨b', eb⟩ := pad hP (le_max_right m m') b
    refine ⟨_, a' + b', ?_⟩
    rw [Submodule.coe_add, ha, hb, ← ea, ← eb]
    exact ((actLin hP _).map_add a' b').symm
  zero_mem' := ⟨0, 0, ((actLin hP 0).map_zero).symm⟩
  smul_mem' := by
    rintro c x ⟨m, a, ha⟩
    refine ⟨m, c • a, ?_⟩
    rw [Submodule.coe_smul, ha]
    exact ((actLin hP m).map_smul c a).symm

theorem cD_mem_exS (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : cD hP w v ∈ exS hP :=
  ⟨w.length, sgl _ w v, (actL_sgl hP le_rfl v).symm⟩

theorem eq_sum (hP : IsPsiFor ε lam T Ψ) {x : smD ε (rreg ε)} {m : ℕ} {a : AS T m}
    (h : (x : L2 ε) = actL T Ψ a) : x = ∑ y, cD hP (ofW y) (a y) :=
  Subtype.ext (by rw [h, actL_eq hP, Submodule.coe_sum])

theorem genSub_le_exS (hP : IsPsiFor ε lam T Ψ) :
    genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ≤ exS hP := by
  refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 hx
    have : x = cD hP [] v := Subtype.ext hv
    rw [this]
    exact cD_mem_exS hP [] v
  · obtain ⟨m, f, hf⟩ := hx
    rw [eq_sum hP hf, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    have := cD_cons hP (a, b) (ofW y) (f y)
    simp only at this
    rw [← this]
    exact cD_mem_exS hP _ _

theorem cD_mem_genSub (hP : IsPsiFor ε lam T Ψ) (v : T.V) (w : List (Fin n × Fin n)) :
    cD hP w v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) := by
  refine (Submodule.mem_sInf).2 fun N hN => ?_
  induction w with
  | nil => exact hN.1 ((mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩)
  | cons p w ih =>
    rw [cD_cons]
    exact hN.2 _ _ _ ih

theorem exhaust : Exhaust := by
  intro n ε lam T Ψ hP
  refine ⟨fun x hx => genSub_le_exS hP hx, fun m m' h a => pad hP h a, fun m a => ?_⟩
  refine ⟨∑ x, cD hP (ofW x) (a x),
    Submodule.sum_mem _ fun x _ => cD_mem_genSub hP _ _, ?_⟩
  rw [actL_eq hP]
  simp only [Submodule.subtype_apply, Submodule.coe_sum]

end GlobalTheory.CompanionTheory.WordFam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLiftStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cone_lift : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK | exact GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK | (intros; apply GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltrationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_lift_adic_filtration : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal | exact GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal | (intros; apply GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal <;> assumption)
end


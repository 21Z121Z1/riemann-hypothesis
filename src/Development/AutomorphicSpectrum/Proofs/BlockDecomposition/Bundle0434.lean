import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0213
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0216
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0088
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeSqrtMulSum
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Calculus

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Ld_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Ld X f) (GLs n) :=
  GlobalTheory.CompanionTheory.RCalc.contDiffOn_fderiv_field GlobalTheory.CompanionTheory.RCalc.isOpen_GLs hf (GlobalTheory.CompanionTheory.RCalc.mulL X)

theorem Lw_contDiffOn (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Lw w f) (GLs n) := by
  induction w with
  | nil => simpa using hf
  | cons p w ih => rw [Lw_cons]; exact Ld_contDiffOn _ ih

theorem Ld_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Ld X f) (Ld X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) e
  simp [Ld, this.fderiv_eq]

theorem Lw_congr (w : List (Bool × Fin n × Fin n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Lw w f) (Lw w h) (GLs n) := by
  induction w with
  | nil => simpa using e
  | cons p w ih => rw [Lw_cons, Lw_cons]; exact Ld_congr _ ih

theorem Ld_cpt (X : Mat n) {f : Mat n → V} (hf : Cpt f) : Cpt (Ld X f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun y hy hl => ?_⟩
  have hc : ContinuousAt (lg : Mat n → ℝ) y :=
    GlobalTheory.CompanionTheory.KerUniq.continuousOn_lg.continuousAt (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hy)
  have h1 : ∀ᶠ g in nhds y, g ∈ GLs n ∧ R < lg g :=
    (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.eventually_mem hy).and (hc.eventually (lt_mem_nhds hl))
  have h2 : f =ᶠ[nhds y] 0 := h1.mono fun g hg => hR g hg.1 hg.2
  simp [Ld, h2.fderiv_eq]

theorem Lw_cpt (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Cpt f) : Cpt (Lw w f) := by
  induction w with
  | nil => simpa using hf
  | cons p w ih => rw [Lw_cons]; exact Ld_cpt _ ih

theorem Lw_append (w w' : List (Bool × Fin n × Fin n)) (f : Mat n → V) : Lw (w ++ w') f = Lw w (Lw w' f) := by
  simp [Lw, List.foldr_append]

end Calculus

def co (p : Bool × Fin n × Fin n) : Mat n →L[ℝ] ℝ :=
  (if p.1 then Complex.reCLM else Complex.imCLM).comp
    (LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℂ p.2.1 p.2.2 : Mat n →ₗ[ℝ] ℂ)))

theorem sum_co_bs (Y : Mat n) : ∑ p, co p Y • bs p = Y := by
  ext a b
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.sum_prod_type]
  simp [co, bs, Matrix.single_apply, Finset.sum_add_distrib]
  have e : ∀ F : Fin n → Fin n → ℂ, (∑ x, ∑ x_1, if x = a ∧ x_1 = b then F x x_1 else 0) = F a b := by
    intro F
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  rw [e (fun x y => ((Y x y).re : ℂ)), e (fun x y => ((Y x y).im : ℂ) * Complex.I)]
  exact Complex.re_add_im _

section Conv

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def cvl (φ : Mat n → ℂ) (y : Lp V 2 μ) : Mat n → V :=
  fun x => ∫ z : G n, φ (x * (z⁻¹ : G n).val) • (y : G n → V) z ∂μ

def CB (φ : Mat n → ℂ) (y : Lp V 2 μ) : Lp V 2 μ := ∫ z : G n, φ z.val • LT μ z y ∂μ

end Conv

section Classes

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] {μ : Measure (G n)}

theorem isRep_congr {b b' : Mat n → V} {y : Lp V 2 μ} (e : Set.EqOn b b' (GLs n)) (h : IsRep μ b y) : IsRep μ b' y := by
  unfold IsRep at *
  filter_upwards [h] with g hg
  rw [hg]
  exact e (GlobalTheory.CompanionTheory.KerUniq.val_mem g)

theorem isRep_memLp {b : Mat n → V} {y : Lp V 2 μ} (h : IsRep μ b y) : MemLp (fun g : G n => b g.val) 2 μ :=
  (memLp_congr_ae h).1 (Lp.memLp y)

theorem isRep_toL {b : Mat n → V} {y : Lp V 2 μ} (h : IsRep μ b y) : toL μ b = y :=
  Lp.ext ((toL_coe (isRep_memLp h)).trans h.symm)

theorem isRep_limit {Y : ℕ → Lp V 2 μ} {Y' : Lp V 2 μ} {h : ℕ → Mat n → V} {h' : Mat n → V}
    (hY : Filter.Tendsto Y Filter.atTop (nhds Y')) (hr : ∀ j, IsRep μ (h j) (Y j))
    (hp : ∀ x ∈ GLs n, Filter.Tendsto (fun j => h j x) Filter.atTop (nhds (h' x))) : IsRep μ h' Y' := by
  have hm : TendstoInMeasure μ (fun j => (Y j : G n → V)) Filter.atTop (Y' : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hY
  obtain ⟨ns, hmono, hns⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ j, (Y j : G n → V) g = h j g.val := ae_all_iff.2 hr
  unfold IsRep
  filter_upwards [hns, hall] with g h1 h2
  have h3 := (hp g.val (GlobalTheory.CompanionTheory.KerUniq.val_mem g)).comp hmono.tendsto_atTop
  refine tendsto_nhds_unique h1 (h3.congr fun j => (h2 (ns j)).symm)

end Classes

theorem le_sqrt_mul_sum {ι : Type} {S : Finset ι} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {t C : ℝ} (ht : 0 ≤ t)
    (h : t ^ 2 ≤ C * ∑ i ∈ S, a i ^ 2) : t ≤ Real.sqrt (max C 0) * ∑ i ∈ S, a i := by
  have h0 : 0 ≤ ∑ i ∈ S, a i := Finset.sum_nonneg fun i _ => ha i
  have h1 : ∑ i ∈ S, a i ^ 2 ≤ (∑ i ∈ S, a i) ^ 2 := by
    rw [sq (∑ i ∈ S, a i), Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => ha j) hi) (ha i)
  have h2 : t ^ 2 ≤ max C 0 * (∑ i ∈ S, a i) ^ 2 := by
    have h3 : 0 ≤ ∑ i ∈ S, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc t ^ 2 ≤ C * ∑ i ∈ S, a i ^ 2 := h
      _ ≤ max C 0 * ∑ i ∈ S, a i ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C 0 * (∑ i ∈ S, a i) ^ 2 := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  have h4 : (Real.sqrt (max C 0) * ∑ i ∈ S, a i) ^ 2 = max C 0 * (∑ i ∈ S, a i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
  exact abs_le_of_sq_le_sq' (h4 ▸ h2) (mul_nonneg (Real.sqrt_nonneg _) h0) |>.2

end GlobalTheory.CompanionTheory.WaveCp.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowSpanInfIdealLeSquareSpan
section
set_option maxSynthPendingDepth 1

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.LowMeet

variable {n : ℕ}

theorem not_hasUpper {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ¬ HasUpper m := by
  rintro ⟨a, ha, hne⟩
  exact not_lower_of_upper ha (hm a (Finsupp.mem_support_iff.2 hne))

theorem lowPart_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : lowPart m = m := by
  ext a
  simp only [lowPart, Finsupp.filter_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hm a (Finsupp.mem_support_iff.2 (Ne.symm hne)))

theorem diagExp_eq {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : diagExp m = 0 := by
  ext i
  rw [diagExp_apply]
  by_contra hne
  exact not_lower_of_diag (a := (i, i)) rfl (hm (i, i) (Finsupp.mem_support_iff.2 hne))

theorem recover (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n) :
    Finsupp.linearCombination ℂ (canon (n := n)) (vermaCoord lam x) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [vermaCoord_canon_of_not lam (not_hasUpper hm), lowPart_eq hm, diagExp_eq hm]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hx]

theorem eq_zero_of_mem (lam : Fin n → ℂ) {x : U n} (hx : x ∈ lowSpan n)
    (hJ : x ∈ vermaIdeal lam) : x = 0 := by
  rw [← recover lam hx, vermaCoord_vermaIdeal lam hJ, map_zero]

theorem canonSpan_lower_le (lo hi : ℕ) : canonSpan (IsLower (n := n)) lo hi ≤ lowSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact ⟨m, hm, rfl⟩

theorem word_mem_lowSpan {w : List (Fin n × Fin n)} (hw : ∀ a ∈ w, IsLower a) :
    word w ∈ lowSpan n :=
  canonSpan_lower_le _ _ (word_mem_canonSpan closed_lower w hw)

theorem isLower_simple {i j : Fin n} (hij : (j : ℕ) = i + 1) : IsLower (j, i) := by
  simp only [IsLower]; rw [Fin.lt_def, hij]; omega

theorem mul_sq_mem_lowSpan {a : Fin n × Fin n} (ha : IsLower a) {x : U n} (hx : x ∈ lowSpan n) :
    x * e a ^ 2 ∈ lowSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    have h : canon m * e a ^ 2 = word (expand m ++ [a, a]) := by
      rw [word_append, word_cons, word_singleton, pow_two]; rfl
    rw [h]
    refine word_mem_lowSpan fun b hb => ?_
    rcases List.mem_append.1 hb with hb | hb
    · exact hm b (mem_support_of_mem_expand hb)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
      rw [hb]; exact ha
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

def lowSq (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (v : U n) (i j : Fin n), v ∈ lowSpan n ∧ (j : ℕ) = i + 1 ∧
    v * e (j, i) ^ 2 = x}

theorem lowSq_le_lowSpan : lowSq n ≤ lowSpan n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, i, j, hv, hij, rfl⟩
  exact mul_sq_mem_lowSpan (isLower_simple hij) hv

theorem lowSq_le_sqSpan : lowSq n ≤ sqSpan n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨v, i, j, -, hij, rfl⟩
  exact ⟨v, i, j, hij, rfl⟩

theorem canon_mul_sq_mem (m : Fin n × Fin n →₀ ℕ) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    canon m * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  by_cases h : HasUpper m
  · refine Submodule.mem_sup_right ?_
    exact mul_pow_mem_vermaIdeal hij (rhoVec n) 1 (by rw [rhoVec_sub hij]; simp)
      (canon_mem_nPlusU h)
  · have hup : ∀ a ∈ upL n, m a = 0 := fun a ha => by
      by_contra hne; exact h ⟨a, mem_upL.1 ha, hne⟩
    set low := word (blockW (lowL n) m) with hlow
    have hlowS : low ∈ lowSpan n :=
      word_mem_lowSpan fun a ha => mem_lowL.1 (mem_of_mem_blockW ha).1
    set p := MvPolynomial.monomial (diagExp m) (1 : ℂ)
    set q := translate (fun k => ((2 : ℕ) : ℂ) * rootAt (j, i) k) p
    have hc : canon m * e (j, i) ^ 2 = low * e (j, i) ^ 2 * hcEmb q := by
      rw [canon_eq_triangular, blockW_eq_nil hup, word_nil, mul_one, mul_assoc,
        hcEmb_mul_e_pow, mul_assoc]
    have hs : canon m * e (j, i) ^ 2 =
        MvPolynomial.eval (rhoVec n) q • (low * e (j, i) ^ 2) +
          low * e (j, i) ^ 2 * (hcEmb q - algebraMap ℂ (U n) (MvPolynomial.eval (rhoVec n) q)) := by
      rw [hc, mul_sub, ← Algebra.commutes, ← Algebra.smul_def]
      abel
    rw [hs]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
      (Submodule.mem_sup_right
        (mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal (rhoVec n) q)))
    exact Submodule.subset_span ⟨low, i, j, hlowS, hij, rfl⟩

theorem mul_sq_mem (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    rw [span_canon_eq_top]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact canon_mul_sq_mem m hij
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem Jp_le : Jp n ≤ lowSq n ⊔ vermaIdeal (rhoVec n) := by
  refine sup_le le_sup_right (Submodule.span_le.2 ?_)
  rintro _ ⟨u, i, j, hij, rfl⟩
  exact mul_sq_mem u hij

theorem mem_sqSpan_of_mem_lowSpan_of_mem_Jp : ∀ {n : ℕ} (x : U n), x ∈ lowSpan n → x ∈ Jp n →
    x ∈ sqSpan n := by
  intro n x hx hJ
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 (Jp_le hJ)
  have ht0 : t = 0 := by
    refine eq_zero_of_mem (rhoVec n) ?_ ht
    have := Submodule.sub_mem _ hx (lowSq_le_lowSpan hs)
    rwa [add_sub_cancel_left] at this
  rw [ht0, add_zero]
  exact lowSq_le_sqSpan hs

end GlobalTheory.CompanionTheory.PresRho.LowMeet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicBetaCompactInduction
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix ValuativeRel GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZBeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_gl {X : Type*} [TopologicalSpace X] {m : ℕ} (f : X → GL (Fin m) k)
    (hf : Continuous fun x => ((f x : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have h : (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) =
      fun x => (Matrix.det (f x : Matrix (Fin m) (Fin m) k))⁻¹ •
        Matrix.adjugate (f x : Matrix (Fin m) (Fin m) k) := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
  rw [h]
  have hd : ∀ x, Matrix.det (f x : Matrix (Fin m) (Fin m) k) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (f x).isUnit).ne_zero
  exact (Continuous.inv₀ hf.matrix_det hd).smul hf.matrix_adjugate

theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have hv : Continuous fun g : GL (Fin n) k => ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val
  have h : Continuous fun g : GL (Fin n) k => glEmb k n g := by
    refine continuous_gl _ ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun g : GL (Fin n) k => glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast j => simpa [glEmbMat] using continuous_const
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast j =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  exact h.subtype_mk (fun g => glEmb_mem_Mir k n g)

def unipMir (m : ℕ) (x : Fin m → k) : Mir k m :=
  ⟨unip k m (Multiplicative.ofAdd x), MirU_le_Mir k m ⟨_, rfl⟩⟩

def secMat (n : ℕ) (j : Fin (n + 1)) (a : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n)
    (a ∘ Equiv.swap j (Fin.last n))).submatrix id (Equiv.swap j (Fin.last n))

end GlobalTheory.CompanionTheory.BZBeta

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat (n : ℕ) :
    Continuous (fun v : Multiplicative (Fin n → k) => colMat k n v.toAdd) := by
  refine continuous_matrix fun i j => ?_
  simp only [colMat]
  split_ifs
  · induction i using Fin.lastCases with
    | last => simpa using continuous_const
    | cast i => simpa [Function.comp_def] using (continuous_apply i).comp (continuous_toAdd (X := Fin n → k))
  · exact continuous_const

theorem continuous_unipIn (n : ℕ) : Continuous (unipIn k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat n)
  · exact continuous_const.sub (continuous_colMat n)

theorem smooth_comp {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (hτ : IsSmooth τ) : IsSmooth (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) :=
  fun v => (hτ v).preimage (continuous_unipIn n)

theorem twKer_le_top (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) :
    twKer τ (MirUin k n) (thetaA k ψ a) ≤
      twKer (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) ⊤ (resChr ψ a ⊤) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, w₀, rfl⟩
  set x : Multiplicative (Fin n → k) :=
    (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) with hx
  have hu : unipIn k n x = (u : Mir k n) := by
    have h := (unipEquiv k n).apply_symm_apply ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)
    have h2 := congrArg (Subtype.val : MirU k n → GL (Fin (n + 1)) k) h
    apply Subtype.ext
    exact h2
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w₀, ?_⟩
  show τ (u : Mir k n) w₀ - _ = τ (unipIn k n x) w₀ - _
  rw [hu]
  rfl

theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (t : kˣ) :
    IsOpen (ann ψ n t : Set (Multiplicative (Fin n → k))) := by
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  refine Subgroup.isOpen_mono (H₁ := polyBall n (t⁻¹ * c)) ?_ (isOpen_polyBall n _)
  intro x hx a ha
  refine hc _ ?_
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (a.toAdd i * x.toAdd i) ≤ valuation k (c : k)
  have h1 : (t : k) * ((t⁻¹ * c : kˣ) : k) = c := by simp
  rw [map_mul, ← h1, map_mul (valuation k) (t : k)]
  exact mul_le_mul' (ha i) (hx i)

end GlobalTheory.CompanionTheory.MirFourier

open GlobalTheory.CompanionTheory.MirFourier in

theorem GlobalTheory.CompanionTheory.MirFourier.fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Fourier k := by
  intro k _ _ _ _ ψ hψ h1 n V _ _ τ hτ v hv
  have hρ := smooth_comp τ hτ
  set ρ : Representation ℂ (Multiplicative (Fin n → k)) V := τ.comp (unipIn k n) with hρdef
  have hv1 : ∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) :=
    fun a => exists_mem_twKer_polyBall ψ ρ a v (twKer_le_top ψ τ a (hv a))
  have hS : {x | ρ x v = v} ∈ 𝓝 (1 : Multiplicative (Fin n → k)) :=
    (hρ v).mem_nhds (by simp)
  obtain ⟨t, ht⟩ := ann_subset_of_mem_nhds ψ h1 n hS
  obtain ⟨s, hs⟩ := exists_polyBall_twKer_uniform ψ hψ ρ v t hv1
  obtain ⟨R, hRne, hRt, hRsum⟩ := exists_reps_sum_eq_zero ψ hψ n t s
  refine GlobalTheory.CompanionTheory.FiniteFourier.eq_zero_of_twKer ρ hρ (polyBall n s) (isCompact_polyBall n s) ((ann ψ n t).subgroupOf _) ?_ v ?_ R hRne
    (fun a => resChr ψ a (polyBall n s)) ?_ (fun a ha => hs a (hRt a ha)) (fun x hx => hRsum x hx)
  · exact (isOpen_ann ψ hψ n t).preimage continuous_subtype_val
  · intro x hx
    exact ht hx
  · intro a ha x hx
    have h2 := hx (Multiplicative.ofAdd a) (hRt a ha)
    show Circle.toUnits (ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)) = 1
    have h3 : ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 := h2
    rw [h3, map_one]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPsiMinus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  intro k _ _ _ _ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  refine GlobalTheory.T.twisted_jacquet_exact_smooth τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k n) 1 ?_ (GlobalTheory.T.mirabolic_filtration_exhaustive k n) f g hf hg hfg
  have hker : ((1 : MirUin k n →* ℂˣ).ker : Set (MirUin k n)) = Set.univ := by
    ext x
    simp
  rw [hker]
  exact isOpen_univ

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocksStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiProd_equiv_standard_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  first | exact @GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | exact GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks | (intros; apply GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupportStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_to_twisted_eigenfunction_support : ∀ {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W) (L : Subgroup G), IsCompact (L : Set G) → ∀ θ : L →* ℂˣ, IsOpen (θ.ker : Set L) → ∀ f : smoothPart (ind P τ), ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧ (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧ ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  first | exact @GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | exact GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | (intros; apply GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd <;> assumption)
end


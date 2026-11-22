import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0084
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorExpansionOfScaledProduct
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem pos_cover (b : Fin (p + q)) : (∃ a, b = omEmb p q a) ∨ ∃ a, b = wEmb p q a := by
  rcases h : (blockEquiv p q).symm b with a | a
  · exact Or.inl ⟨a, (blockEquiv p q).symm.injective (h.trans (BlockEmbeddings.blockEquiv_symm_omEmb a).symm)⟩
  · exact Or.inr ⟨a, (blockEquiv p q).symm.injective (h.trans (BlockEmbeddings.blockEquiv_symm_wEmb a).symm)⟩

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ) (j : Fin (n s))
    (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hi := (BlockEmbeddings.posOf_strictMono (p := p) (q := q) s).injective
  simp only [aExt]
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun e => hb (hi e)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_off (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ) (j : Fin (n s))
    (b : Fin (p + q)) (hb : ¬ ∃ l, posOf p q s l = b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg fun e => hb ⟨l, e⟩

theorem tMat_posOf (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (s : Ψ ⊕ Ψ)
    (hs : s = .inl τ ∨ s = .inr τ) (l l' : Fin (rk Ψ p q s)) :
    tMat Ts τ (posOf p q s l) (posOf p q s l') = Ts s l l' := by
  rcases hs with rfl | rfl
  · exact BlockEmbeddings.blocks_wEmb _ _ l l'
  · exact BlockEmbeddings.blocks_omEmb _ _ l l'

theorem blocks_wEmb_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R)
    (a : Fin p) (b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (omEmb p q b) =
      0 := by
  rw [Matrix.submatrix_apply, BlockEmbeddings.blockEquiv_symm_wEmb, BlockEmbeddings.blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₂₁]
  rfl

theorem blocks_omEmb_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R)
    (a : Fin q) (b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (wEmb p q b) =
      0 := by
  rw [Matrix.submatrix_apply, BlockEmbeddings.blockEquiv_symm_wEmb, BlockEmbeddings.blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₂]
  rfl

theorem tMat_off (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (s : Ψ ⊕ Ψ)
    (hs : s = .inl τ ∨ s = .inr τ) (l : Fin (rk Ψ p q s)) (b : Fin (p + q))
    (hb : ¬ ∃ l', posOf p q s l' = b) : tMat Ts τ (posOf p q s l) b = 0 := by
  rcases hs with rfl | rfl
  · rcases pos_cover b with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact blocks_wEmb_omEmb _ _ l a
    · exact absurd ⟨a, rfl⟩ hb
  · rcases pos_cover b with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact absurd ⟨a, rfl⟩ hb
    · exact blocks_omEmb_wEmb _ _ l a

theorem aExt_mul_tMat (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ) :
    aExt A s * tMat Ts τ = (x ^ m s) • aExt C s := by
  ext j b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := BlockEmbeddings.sum_aExt_mul A (RingHom.id Ω) s j (fun a => tMat Ts τ a b)
  simp only [RingHom.id_apply] at h1
  rw [h1]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    have h2 := congrFun (congrFun (hAT s) j) l'
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h2
    rw [aExt_posOf, ← h2]
    exact Finset.sum_congr rfl fun l _ => by rw [tMat_posOf Ts τ s hs]
  · rw [aExt_off C s j b hb, mul_zero]
    exact Finset.sum_eq_zero fun l _ => by rw [tMat_off Ts τ s hs l b hb, mul_zero]

theorem sum_cMin_minorIJ (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (G : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1) :
    ∑ I, cMin C t J I * minorIJ G I S =
      ((aExt C t.1).submatrix J id * G.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [BlockEmbeddings.det_mul_cols _ _ S hS]
  rfl

theorem sum_cMin_tMat_mul (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1) :
    ∑ I, cMin A t J I * minorIJ (tMat Ts τ * h) I S =
      x ^ (m t.1 * ((t.2 : ℕ) + 1)) * ∑ I, cMin C t J I * minorIJ h I S := by
  rw [sum_cMin_minorIJ A t J _ S hS, sum_cMin_minorIJ C t J _ S hS]
  have hm : (aExt A t.1).submatrix J id * (tMat Ts τ * h).submatrix id (S.orderEmbOfFin hS) =
      (x ^ m t.1) • ((aExt C t.1).submatrix J id * h.submatrix id (S.orderEmbOfFin hS)) := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.mul_assoc, aExt_mul_tMat A C Ts x m hAT τ t.1 hs, Matrix.smul_mul]
    rfl
  rw [hm, Matrix.det_smul, Fintype.card_fin, pow_mul]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfMatrixIdentity
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

private theorem det_mul_eq_sum_prod_det_submatrix {Ω : Type} [Field Ω] {n r : ℕ}
    (B : Matrix (Fin r) (Fin n) Ω) (C : Matrix (Fin n) (Fin r) Ω) :
    (B * C).det = ∑ p : Fin r → Fin n, (∏ i, B i (p i)) * (C.submatrix p id).det := by
  have hsub : ∀ p : Fin r → Fin n, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : Ω) * ∏ i, C (p i) (σ i) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.det_apply']
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, hsub]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

private theorem det_submatrix_mul_det_eq_pow_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (A C : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C)
    (J : Fin r → Fin n) :
    (A.submatrix J id).det * T.det = a ^ r * (C.submatrix J id).det := by
  have h1 : A.submatrix J id * T = a • C.submatrix J id := by
    ext i j
    have h := congrFun (congrFun hAT (J i)) j
    simpa [Matrix.mul_apply] using h
  rw [← Matrix.det_mul, h1, Matrix.det_smul, Fintype.card_fin]

theorem minor_isUnit_of_leftInverse : ∀ {Ω : Type} [Field Ω] {n r : ℕ} (R : Subring Ω) (A C : Matrix (Fin n) (Fin r) Ω)
    (B : Matrix (Fin r) (Fin n) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C) (ha : a ≠ 0)
    (hT : T.det ≠ 0) (hBC : B * C = 1) (hC : ∀ j l, C j l ∈ R) (hB : ∀ l j, B l j ∈ R) (J₀ : Fin r → Fin n)
    (hz : (A.submatrix J₀ id).det ≠ 0)
    (hr : ∀ J : Fin r → Fin n, (A.submatrix J id).det / (A.submatrix J₀ id).det ∈ R),
    (C.submatrix J₀ id).det ≠ 0 ∧ (C.submatrix J₀ id).det ∈ R ∧ (C.submatrix J₀ id).det⁻¹ ∈ R ∧
      (A.submatrix J₀ id).det * T.det = a ^ r * (C.submatrix J₀ id).det := by
  intro Ω _ n r R A C B T a hAT ha hT hBC hC hB J₀ hz hr
  have hrel : ∀ J : Fin r → Fin n,
      (A.submatrix J id).det * T.det = a ^ r * (C.submatrix J id).det :=
    det_submatrix_mul_det_eq_pow_mul A C T a hAT
  have har : a ^ r ≠ 0 := pow_ne_zero r ha
  have hC0 : (C.submatrix J₀ id).det ≠ 0 := by
    intro h0
    have h := hrel J₀
    rw [h0, mul_zero] at h
    exact mul_ne_zero hz hT h
  have hCR : (C.submatrix J₀ id).det ∈ R := by
    let M : Matrix (Fin r) (Fin r) R := Matrix.of fun i j => ⟨C (J₀ i) j, hC _ _⟩
    have hM : R.subtype.mapMatrix M = C.submatrix J₀ id := by
      ext i j
      rfl
    rw [← hM, ← RingHom.map_det]
    exact SetLike.coe_mem M.det
  have hratio : ∀ J : Fin r → Fin n, (C.submatrix J id).det =
      (C.submatrix J₀ id).det * ((A.submatrix J id).det / (A.submatrix J₀ id).det) := by
    intro J
    apply mul_left_cancel₀ har
    rw [← hrel J, show a ^ r * ((C.submatrix J₀ id).det *
        ((A.submatrix J id).det / (A.submatrix J₀ id).det)) =
        (a ^ r * (C.submatrix J₀ id).det) * ((A.submatrix J id).det / (A.submatrix J₀ id).det) by ring,
      ← hrel J₀]
    field_simp
  have hs := det_mul_eq_sum_prod_det_submatrix B C
  rw [hBC, Matrix.det_one] at hs
  have hs2 : (C.submatrix J₀ id).det * ∑ p : Fin r → Fin n,
      (∏ i, B i (p i)) * ((A.submatrix p id).det / (A.submatrix J₀ id).det) = 1 := by
    refine Eq.trans ?_ hs.symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hratio p]
    ring
  refine ⟨hC0, hCR, ?_, hrel J₀⟩
  rw [inv_eq_of_mul_eq_one_right hs2]
  exact sum_mem fun p _ => mul_mem (prod_mem fun i _ => hB _ _) (hr p)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralRegularizedConvergence
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem tendsto_logPow_div_exp_add (CE : ℝ) (e : ℕ) :
    Tendsto (fun n : ℕ => CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n)) atTop (𝓝 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := e + 1)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℕ => Real.exp 1 + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h3 := (h.comp h2).const_mul CE
  simpa [mul_div_assoc] using h3

theorem tendstoUniformlyOn_cutoff_comp {β X : Type*} (σ : β → X) (c : X → ℝ)
    (hc : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (F : ℝ → X → ℝ) (f : X → ℝ) (l : Filter ℝ) (K : Set X)
    (E : Set β) (hE : ∀ y ∈ E, σ y ∈ K) (h : TendstoUniformlyOn F f l K) :
    TendstoUniformlyOn (fun t y => c (σ y) * F t (σ y)) (fun y => c (σ y) * f (σ y)) l E := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with t ht y hy
  have h1 := ht (σ y) (hE y hy)
  rw [Real.dist_eq] at h1 ⊢
  calc |c (σ y) * f (σ y) - c (σ y) * F t (σ y)|
      = c (σ y) * |f (σ y) - F t (σ y)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (hc _).1]
    _ ≤ 1 * |f (σ y) - F t (σ y)| := mul_le_mul_of_nonneg_right (hc _).2 (abs_nonneg _)
    _ < ε := by simpa using h1

theorem integrableOn_compl_of_ae_eq_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : Set α) (hE : MeasurableSet E) (f T : α → ℝ) (b : ℝ) (hT : Integrable T μ)
    (hT0 : ∀ᵐ y ∂μ, 0 ≤ T y) (hb : ∫ y, T y ∂μ ≤ b) (heq : ∀ᵐ y ∂μ, y ∉ E → f y = T y) :
    IntegrableOn f Eᶜ μ ∧ ∫ y in Eᶜ, f y ∂μ ≤ b := by
  have h : f =ᵐ[μ.restrict Eᶜ] T := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hE.compl]
    filter_upwards [heq] with y hy hyE using hy hyE
  refine ⟨(hT.integrableOn (s := Eᶜ)).congr h.symm, ?_⟩
  rw [integral_congr_ae h]
  exact (setIntegral_le_integral hT hT0).trans hb

theorem conv_chart_integral : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C CE : ℝ), IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn R.Yo (ph i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧ (∀ i, IsPsh A (th i + LocPot.ofFun (phT i t) + Θ)) ∧ GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => th i + LocPot.ofFun (phT i t) + Θ) CE) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)) (c : X → ℝ), S ⊆ (A.chart j).target → IsCompact S → @Measurable X ℝ (borel X) _ c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) → (∀ y ∈ (A.chart j).target, y ∉ S → c ((A.chart j).symm y) = 0) → IntegrableOn (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y) (A.chart j).target ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (A.chart j).target) ∧ Tendsto (fun t => ∫ y in (A.chart j).target, c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (𝓝[>] 0) (𝓝 (∫ y in (A.chart j).target, c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y)) := by
  intro e X _ _ _ A R Θ th ph phT G GT C CE hΘ hth hph hev hconv hGev hGconv j S c hST hS hcm hc01 hc0
  obtain ⟨hYo, hnull, -, hKc⟩ := GlobalTheory.T.regular_chart_data_properties e X A R
  have hsymmS : ContinuousOn (A.chart j).symm S := (A.chart j).continuousOn_symm.mono hST
  have hSm : MeasurableSet S := hS.measurableSet
  have hTm : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Set (Fin e → ℂ), ∀ n, E n = S ∩ (A.chart j).symm ⁻¹'
      {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n} := ⟨_, fun _ => rfl⟩
  have hEmem : ∀ n y, y ∈ E n ↔ y ∈ S ∧ (A.chart j).symm y ∈ R.Yo ∧
      R.r ((A.chart j).symm y) ≤ Real.exp 1 + n := by
    intro n y; rw [hEdef]; rfl
  have hEc : ∀ n, IsCompact (E n) := by
    intro n; rw [hEdef]
    exact hS.of_isClosed_subset
      (hsymmS.preimage_isClosed_of_isClosed hS.isClosed (hKc _).isClosed) Set.inter_subset_left
  have hEsub : ∀ n, E n ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := fun n y hy => by
    have := (hEmem n y).1 hy
    exact ⟨hST this.1, this.2.1⟩
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (hEc n).measurableSet
  have hEmono : Monotone E := by
    intro m n hmn y hy
    obtain ⟨h1, h2, h3⟩ := (hEmem m y).1 hy
    refine (hEmem n y).2 ⟨h1, h2, h3.trans ?_⟩
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hEfin : ∀ n, (volume.restrict S) (E n) < ⊤ := fun n => by
    rw [Measure.restrict_apply (hEm n)]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) (hEc n).measure_lt_top
  have hae : ∀ᵐ y ∂(volume.restrict S), y ∈ S ∧ (A.chart j).symm y ∈ R.Yo := by
    rw [ae_restrict_iff' hSm]
    filter_upwards [compl_mem_ae_iff.2 (hnull j)] with y hy hyS
    refine ⟨hyS, ?_⟩
    by_contra h
    exact hy ⟨hST hyS, h⟩
  have hex : ∀ᵐ y ∂(volume.restrict S), ∃ n, y ∈ E n := by
    filter_upwards [hae] with y hy
    obtain ⟨n, hn⟩ := exists_nat_ge (R.r ((A.chart j).symm y))
    refine ⟨n, (hEmem n y).2 ⟨hy.1, hy.2, ?_⟩⟩
    have := Real.exp_pos 1
    linarith
  have hlog : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  have hL : ∀ᵐ y ∂(volume.restrict S), 0 ≤ Real.log (R.r ((A.chart j).symm y)) := by
    filter_upwards [hae] with y hy using hlog _ hy.2
  have hGbd : ∀ n : ℕ, ∃ M : ℝ, ∀ x, x ∈ R.Yo → R.r x ≤ Real.exp 1 + n → |G x| ≤ M := by
    intro n
    have hu := hGconv _ (fun x hx => hx.1) (hKc (Real.exp 1 + n))
    have h1 := Metric.tendstoUniformlyOn_iff.1 hu 1 one_pos
    obtain ⟨t, ht1, ht2⟩ := (h1.and hGev).exists
    refine ⟨1 + (|C| + |C| * Real.log (Real.exp 1 + n)), fun x hx hxr => ?_⟩
    have a1 := ht1 x ⟨hx, hxr⟩
    have a2 := ht2.2 x hx
    have a3 : Real.log (R.r x) ≤ Real.log (Real.exp 1 + n) :=
      Real.log_le_log (by linarith [R.one_le_r x hx]) hxr
    have a4 := hlog x hx
    rw [Real.dist_eq] at a1
    have a5 := abs_sub_abs_le_abs_sub (G x) (GT t x)
    have a6 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) a4
    have a7 : |C| * Real.log (R.r x) ≤ |C| * Real.log (Real.exp 1 + n) :=
      mul_le_mul_of_nonneg_left a3 (abs_nonneg C)
    have a8 := le_abs_self C
    linarith
  have hρ : ∀ n, TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (𝓝[>] 0) (E n) := fun n =>
    GlobalTheory.CompanionTheory.Ar.Giv.conv_dens_of_open A Θ R.Yo th ph phT hYo hΘ hth hph
      (hev.mono fun t h => h.1) hconv j (E n) (hEsub n) (hEc n)
  have hΓ : ∀ n, TendstoUniformlyOn
      (fun t y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y))
      (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y)) (𝓝[>] 0) (E n) := fun n =>
    tendstoUniformlyOn_cutoff_comp (A.chart j).symm c hc01 GT G _ {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n} (E n)
      (fun y hy => ⟨((hEmem n y).1 hy).2.1, ((hEmem n y).1 hy).2.2⟩)
      (hGconv _ (fun x hx => hx.1) (hKc (Real.exp 1 + n)))
  have hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n,
      |locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y| ≤ M ∧
      |c ((A.chart j).symm y) * G ((A.chart j).symm y)| ≤ M := by
    intro n
    obtain ⟨M1, h1⟩ := (hEc n).exists_bound_of_continuousOn
      ((GlobalTheory.CompanionTheory.Ar.Giv.locDens_add_ofFun_continuousOn A R.Yo th ph Θ hYo hth hΘ hph j).mono (hEsub n))
    obtain ⟨M2, h2⟩ := hGbd n
    refine ⟨max M1 M2, fun y hy => ⟨(h1 y hy).trans (le_max_left _ _), ?_⟩⟩
    obtain ⟨-, b2, b3⟩ := (hEmem n y).1 hy
    rw [abs_mul, abs_of_nonneg (hc01 _).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hc01 _).2).trans ((h2 _ b2 b3).trans (le_max_right _ _))
  have hEv : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j) (volume.restrict S) ∧
      AEStronglyMeasurable (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y)) (volume.restrict S) ∧
      (∀ᵐ y ∂(volume.restrict S), 0 ≤ locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) ∧
      (∀ᵐ y ∂(volume.restrict S), y ∉ E 0 →
        |c ((A.chart j).symm y) * GT t ((A.chart j).symm y)| ≤ 2 * |C| * Real.log (R.r ((A.chart j).symm y))) ∧
      ∀ n, IntegrableOn (fun y => Real.log (R.r ((A.chart j).symm y)) *
          locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (E n)ᶜ (volume.restrict S) ∧
        ∫ y in (E n)ᶜ, Real.log (R.r ((A.chart j).symm y)) *
          locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y ∂(volume.restrict S) ≤
          CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n) := by
    filter_upwards [hev, hGev] with t ⟨hs, hp, ht⟩ ⟨hm, hb⟩
    have hpot : ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := fun i =>
      isPotentialAdd A _ _ (isPotentialAdd A _ _ (hth i) (isPotential_ofFun A _ (hs i))) hΘ
    have hnn : ∀ y ∈ (A.chart j).target,
        0 ≤ locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y :=
      fun y hy => locDens_nonneg_of_psh A _ hpot hp j hy
    have htail := fun n : ℕ => GlobalTheory.T.tail_log_bound_local_integrable A R.Yo R.r _ CE hpot R.one_le_r
      (fun j' y hy _ => locDens_nonneg_of_psh A _ hpot hp j' hy) ht j S hST hS
      (Real.exp 1 + n) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                           linarith)
    refine ⟨((locDensCont A _ hpot j).mono hST).aestronglyMeasurable hSm, ?_, ?_, ?_, ?_⟩
    · letI : MeasurableSpace X := borel X
      haveI : BorelSpace X := ⟨rfl⟩
      have h1 : AEMeasurable (A.chart j).symm (volume.restrict S) := hsymmS.aemeasurable hSm
      have h2 : AEMeasurable (fun y => c ((A.chart j).symm y) *
          R.Yo.indicator (GT t) ((A.chart j).symm y)) (volume.restrict S) :=
        (hcm.comp_aemeasurable h1).mul (hm.comp_aemeasurable h1)
      refine h2.aestronglyMeasurable.congr ?_
      filter_upwards [hae] with y hy
      rw [Set.indicator_of_mem hy.2]
    · filter_upwards [hae] with y hy using hnn y (hST hy.1)
    · filter_upwards [hae] with y hy hyE
      have hr : Real.exp 1 < R.r ((A.chart j).symm y) := by
        by_contra h
        exact hyE ((hEmem 0 y).2 ⟨hy.1, hy.2, by simpa using not_lt.1 h⟩)
      have hl : 1 ≤ Real.log (R.r ((A.chart j).symm y)) := by
        rw [Real.le_log_iff_exp_le (lt_trans (Real.exp_pos 1) hr)]
        exact hr.le
      have b1 := hb _ hy.2
      have b2 : C * Real.log (R.r ((A.chart j).symm y)) ≤
          |C| * Real.log (R.r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      have b3 : |C| * 1 ≤ |C| * Real.log (R.r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_left hl (abs_nonneg C)
      have b4 := le_abs_self C
      rw [abs_mul, abs_of_nonneg (hc01 _).1]
      have b5 := mul_le_of_le_one_left (abs_nonneg (GT t ((A.chart j).symm y))) (hc01 ((A.chart j).symm y)).2
      linarith
    · intro n
      refine integrableOn_compl_of_ae_eq_nonneg _ (E n) (hEm n) _ _ _ (htail n).1 ?_ (htail n).2 ?_
      · filter_upwards [hae] with y hy
        exact mul_nonneg (Set.indicator_nonneg (fun x hx => hlog x hx.1) _) (hnn y (hST hy.1))
      · filter_upwards [hae] with y hy hyE
        have hmem : (A.chart j).symm y ∈
            GroundTheory.Heights₂.Heights.AnalyticLimit.tail R.Yo R.r (Real.exp 1 + n) := by
          refine ⟨hy.2, ?_⟩
          by_contra h
          exact hyE ((hEmem n y).2 ⟨hy.1, hy.2, (not_le.1 h).le⟩)
        rw [Set.indicator_of_mem hmem]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.dominated_convergence_exhaustion (volume.restrict S) (𝓝[>] (0 : ℝ)) E
    (fun y => Real.log (R.r ((A.chart j).symm y)))
    (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
    (fun t y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y))
    (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j)
    (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y))
    (2 * |C|) (fun n => CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n))
    hEm hEmono hEfin hex hL (by positivity) (tendsto_logPow_div_exp_add CE e) hρ hΓ hM hEv
  have e1 : ∀ (g : X → ℝ) (d : (Fin e → ℂ) → ℝ),
      ∫ y in (A.chart j).target, c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y =
      ∫ y in S, c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y := fun g d =>
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hTm hST
      (fun y hy => by simp [hc0 y hy.1 hy.2])
  have e2 : ∀ (g : X → ℝ) (d : (Fin e → ℂ) → ℝ),
      Integrable (fun y => c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y) (volume.restrict S) →
      IntegrableOn (fun y => c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y) (A.chart j).target :=
    fun g d h => IntegrableOn.of_forall_diff_eq_zero h hTm
      (fun y hy => by simp [hc0 y hy.1 hy.2])
  refine ⟨e2 _ _ i1, i2.mono fun t h => e2 _ _ h, ?_⟩
  rw [e1 G]
  exact Tendsto.congr (fun t => (e1 (GT t) _).symm) i3

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelMonomialWeightProduct
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial

theorem step_monomial : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  classical
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h Φ _ y hy τ i
  obtain ⟨hbase, hstep⟩ := GlobalTheory.T.model_dy_weights Ψ p q Ω n A K₀ J₀ x₀ m h τ i
  have hsplit : ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) =
      (∏ k, y (.inl k)) ^ (rkW i * m (.inl τ) + rkO i * m (.inr τ)) *
        ∏ t, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) := by
    rw [Fintype.prod_sum_type, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hbase k, neg_neg, zpow_natCast]
  have hval : ∀ t : StepIx Ψ p q, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) =
      if (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then (y (.inr t))⁻¹
      else 1 := by
    intro t
    split_ifs with hc
    · rw [(hstep t).1 hc, _root_.zpow_neg, zpow_one]
    · rw [(hstep t).2 hc, neg_zero, zpow_zero]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inl τ, ⟨i, h1⟩⟩ := by
      unfold stepOf
      exact dif_pos h1
    have hW : rkW i = (i : ℕ) + 1 := by unfold rkW; omega
    have hO : rkO i = 0 := by unfold rkO; omega
    rw [hsplit, hW, hO, zero_mul, add_zero, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval,
      if_pos (Or.inl rfl), hso, div_eq_mul_inv]
    intro t ht
    rw [hval, if_neg]
    rintro (h' | ⟨-, -, hp⟩)
    · exact ht h'
    · omega
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩ := by
      unfold stepOf
      exact dif_neg (not_lt.2 h1)
    have hW : rkW i = p := by unfold rkW; omega
    have hO : rkO i = (i : ℕ) - p + 1 := by unfold rkO; omega
    rw [hsplit, hW, hO]
    by_cases hp0 : 0 < p
    · rw [dif_pos hp0]
      have hne : stepOf Ψ p q (τ, i) ≠ ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩ := by
        rw [hso]
        intro he
        exact Sum.inr_ne_inl (congrArg Sigma.fst he)
      rw [Fintype.prod_eq_mul _ _ hne, hval, hval, if_pos (Or.inl rfl),
        if_pos (Or.inr ⟨rfl, show p - 1 + 1 = p by omega, h1⟩), hso]
      · rw [div_eq_mul_inv, mul_inv]
        ring
      · rintro x ⟨hx1, hx2⟩
        rw [hval, if_neg]
        rintro (h' | ⟨hs, hj, -⟩)
        · exact hx1 h'
        · apply hx2
          obtain ⟨s, j⟩ := x
          dsimp only at hs hj
          subst hs
          exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp; omega)))
    · rw [dif_neg hp0, one_mul, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval, if_pos (Or.inl rfl), hso,
        div_eq_mul_inv]
      intro t ht
      rw [hval, if_neg]
      rintro (h' | ⟨-, hj, -⟩)
      · exact ht h'
      · omega

end GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_coordinates_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec.mem_mcPts_of_specialise <;> assumption)
end


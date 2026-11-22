import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0070
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0028
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0012
import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0006
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def pairV {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) : (Σ k, Sum.elim ι ι' k) → R
  | ⟨.inl k, i⟩ => a ⟨k, i⟩
  | ⟨.inr k, i⟩ => b ⟨k, i⟩

theorem pairV_inl {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι k) :
    pairV a b (inlV p) = a p := rfl

theorem pairV_inr {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι' k) :
    pairV a b (inrV p) = b p := rfl

def stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) : Ψ × Fin N :=
  Classical.choose (not_forall_not.1 (by simpa using h) : ∃ p, M.blk p = some k)

theorem blk_stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) :
    M.blk (stepOf M k h) = some k := by
  unfold stepOf
  exact Classical.choose_spec (p := fun p => M.blk p = some k) _

def transPt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) : (Σ k, ι k) → Φ' := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then algebraMap M'.Ω Φ' (Cv.φ (M.x ⟨⟨q.1, h⟩, q.2⟩))
  else ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef q I)) *
    minorIJ (M'.g (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem transPt_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (q : Σ k, baseIdx ι M.blk k) :
    transPt Cv ⟨q.1.1, q.2⟩ = algebraMap M'.Ω Φ' (Cv.φ (M.x q)) :=
  dif_pos q.1.2

theorem transPt_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    transPt Cv ⟨k, m⟩ = ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef ⟨k, m⟩ I)) * minorIJ (M'.g p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun H => H p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  rw [transPt, dif_neg h, e]

def trMat {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) : Matrix (Fin N) (Fin N) M'.Ω :=
  ((F.T τ).map Cv.φ)⁻¹ * F'.T τ

def coE {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (q : Σ k, ι k) (r : Σ k, ι' k) : M'.Ω :=
  ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
    Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThirdStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficients
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem tower_seq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  intro Ψ _ _ N T II B u g c s q m hII hT1 hW hB hs hs0 hq hm
  obtain ⟨h1, -, h3, h4, h5⟩ := hT1 u g hW B hB c
  have hs' : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall fun n => hs n⟩
  have hδ : ((T.M B c).δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (T.M B c).δ_pos.ne'
  have hqn : ∀ n, (q n : ℝ) ≠ 0 := fun n => Nat.cast_ne_zero.2 (hq n).ne'
  have hgeo : ∀ n, geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) =
      (T.M B c).δ * (q n : ℝ) ^ dimFl Ψ N * T.mDeg B c u (s n) := by
    intro n
    have := geoFun_comb_mixed II hII Ψ N (T.M B c) (scale (s n)) (fun _ => T.lamS u (s n)) (fun _ => s n) (q n)
      (fun _ => m n) (fun _ j => hm n j)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have har : ∀ n, II (T.M B c).K (T.M B c).ι (T.M B c).P (dimFl Ψ N + 1)
      (fun _ => combLine ((T.M B c).line (scale (s n))) (m n)) =
      (T.M B c).δ * (q n : ℝ) ^ (dimFl Ψ N + 1) * T.mbarTop II B c u (s n) := fun n =>
    top_comb_eq_arFun II hII Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)
  refine ⟨?_, ?_, ?_, h4⟩
  · filter_upwards [hs'.eventually h1] with n hn
    have a := (nefFib_integral_multiple Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)).2 hn.1
    have b := RootFieldNumerics.root_model_line_semipositive Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n) hn.2
    exact ⟨⟨_, le_rfl, b.1⟩, b.2, a⟩
  · refine ((h3.comp hs').const_mul ((T.M B c).δ : ℝ)).congr fun n => ?_
    rw [hgeo n]
    have := hqn n
    simp only [Function.comp]
    field_simp
  · refine (h5.comp hs').congr fun n => ?_
    unfold normHt
    rw [hgeo n, har n]
    have := hqn n
    simp only [Function.comp]
    by_cases h0 : T.mDeg B c u (s n) = 0
    · simp [h0]
    · have h2 : ((dimFl Ψ N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMat
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings

theorem det_mul_cols {R : Type} [CommRing R] {N d : ℕ} (M : Matrix (Fin d) (Fin N) R)
    (B : Matrix (Fin N) (Fin N) R) (C : Finset (Fin N)) (hC : C.card = d) :
    (M * B.submatrix id (C.orderEmbOfFin hC)).det =
      ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C := by
  rw [GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have h1 : ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin N) => I.card = d),
        (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) * minorIJ B I C := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
    have hc : s.card ≠ d := fun hc => hs (by simp [hc])
    rw [dif_neg hc, zero_mul]
  rw [h1, Finset.sum_subtype (Finset.univ.filter fun I : Finset (Fin N) => I.card = d)
    (p := fun s : Finset (Fin N) => s.card = d) (fun s => by simp)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dif_pos s.2, MinorCalc.minorIJ_eq_det B s.1 C d s.2 hC]
  rfl

variable {Ψ : Type} {p q : ℕ}

theorem blockEquiv_symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, omEmb]

theorem blockEquiv_symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = Sum.inr a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, wEmb]
  omega

theorem blocks_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (wEmb p q b) =
      Y a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_wEmb, blockEquiv_symm_wEmb, Matrix.fromBlocks_apply₂₂]

theorem blocks_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (omEmb p q b) =
      X a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_omEmb, blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₁]

theorem gMat_posOf (Ω : Type) [Field Ω] (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ)
    (l l' : Fin (rk Ψ p q s)) :
    gMat p q Ω τ (posOf p q s l) (posOf p q s l') = genU Ω (rk Ψ p q) s l l' := by
  rcases hs with rfl | rfl
  · exact blocks_wEmb _ _ l l'
  · exact blocks_omEmb _ _ l l'

theorem posOf_strictMono (s : Ψ ⊕ Ψ) : StrictMono (posOf p q s) := by
  rcases s with τ | τ
  · exact wEmb_strictMono p q
  · exact omEmb_strictMono p q

theorem sum_aExt_mul {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {L : Type} [Field L] (f : Ω →+* L) (s : Ψ ⊕ Ψ) (j : Fin (n s)) (G : Fin (p + q) → L) :
    ∑ a, f (aExt A s j a) * G a = ∑ l, f (A s j l) * G (posOf p q s l) := by
  simp only [aExt, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (posOf p q s l)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem stepOf_fst (r : Ψ × Fin (p + q)) :
    (stepOf Ψ p q r).1 = .inl r.1 ∨ (stepOf Ψ p q r).1 = .inr r.1 := by
  unfold stepOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mem_stepCols_iff (r : Ψ × Fin (p + q)) (a : Fin (p + q)) :
    a ∈ stepCols (p + q) p r.2 ↔
      ∃ y : Fin (((stepOf Ψ p q r).2 : ℕ) + 1),
        posOf p q (stepOf Ψ p q r).1 (Fin.castLE (stepOf Ψ p q r).2.2 y) = a := by
  have hr := r.2.2
  by_cases h : (r.2 : ℕ) < p
  · have e : stepOf Ψ p q r = ⟨.inl r.1, ⟨r.2, h⟩⟩ := dif_pos h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨a - q, ?_⟩, Fin.ext ?_⟩
      · show (a : ℕ) - q < (r.2 : ℕ) + 1
        omega
      · show q + ((a : ℕ) - q) = a
        omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) + 1 := y.2
      show p + q - p ≤ q + (y : ℕ) ∧ q + (y : ℕ) < p + q - p + ((r.2 : ℕ) + 1)
      omega
  · have e : stepOf Ψ p q r = ⟨.inr r.1, ⟨r.2 - p, by show _ < q; omega⟩⟩ := dif_neg h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg (by omega)]
    constructor
    · intro h1
      refine ⟨⟨a, ?_⟩, Fin.ext rfl⟩
      show (a : ℕ) < (r.2 : ℕ) - p + 1
      omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) - p + 1 := y.2
      show (y : ℕ) < (r.2 : ℕ) + 1 - p
      omega

theorem det_fMat_eq {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {K₀ : Type} {J₀ : K₀ → Type} (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (C : Finset (Fin (p + q)))
    (hC : ∀ a, a ∈ C ↔ ∃ y : Fin ((t.2 : ℕ) + 1), posOf p q t.1 (Fin.castLE t.2.2 y) = a)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) :
    ((fMat A t.1).submatrix J (Fin.castLE t.2.2)).det =
      ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q))
        (coefF (K₀ := K₀) (J₀ := J₀) A ⟨.inr t, J⟩ I) * minorIJ (gMat p q Ω τ) I C := by
  have hf : StrictMono fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) :=
    (posOf_strictMono t.1).comp (Fin.strictMono_castLE _)
  have hCe : C = Finset.univ.image fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) := by
    ext a
    simp [hC]
  have hcard : C.card = (t.2 : ℕ) + 1 := by
    rw [hCe, Finset.card_image_of_injective _ hf.injective]
    simp
  have henum : ∀ y, C.orderEmbOfFin hcard y = posOf p q t.1 (Fin.castLE t.2.2 y) := fun y =>
    congrFun (Finset.orderEmbOfFin_unique hcard (fun x => (hC _).2 ⟨x, rfl⟩) hf).symm y
  have hmat : (fMat A t.1).submatrix J (Fin.castLE t.2.2) =
      ((aExt A t.1).map (algebraMap Ω (GenField Ω (rk Ψ p q)))).submatrix J id *
        (gMat p q Ω τ).submatrix id (C.orderEmbOfFin hcard) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id, fMat]
    rw [sum_aExt_mul A _ t.1 (J x) fun a => gMat p q Ω τ a (C.orderEmbOfFin hcard y)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [henum, gMat_posOf Ω τ t.1 hs]
  rw [hmat, det_mul_cols _ _ C hcard]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  by_cases e : I.card = (t.2 : ℕ) + 1
  · rw [dif_pos e]
    simp only [coefF]
    rw [dif_pos e, RingHom.map_det]
    rfl
  · rw [dif_neg e]
    simp [coefF, e]

theorem yv_step : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r k, blkF Ψ p q K₀ r = some k → ∀ i : idx J₀ n k, yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) * minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk with hp
  obtain rfl := Option.some.inj hk
  exact det_fMat_eq A r.1 (stepOf Ψ p q r) (stepOf_fst r) _ (mem_stepCols_iff r) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings
end
end


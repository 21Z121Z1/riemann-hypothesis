import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def CuspBounded : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ →
      (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
        (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
          ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) →
      (∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
          ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N) →
      IsCuspFun V φ →
      ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ C : ℝ, ∀ g, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) g‖ ≤ C

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

open GlobalTheory.SmoothForms

theorem mul_norm_deriv_le {f f₁ f₂ : ℝ → ℂ} (h₁ : ∀ t, HasDerivAt f (f₁ t) t) (h₂ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    {h B : ℝ} (hh : 0 ≤ h) (hB : ∀ t ∈ Set.Icc 0 h, ‖f₂ t‖ ≤ B) :
    h * ‖f₁ 0‖ ≤ ‖f h‖ + ‖f 0‖ + B * h * h := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hh⟩)
  have a1 : ∀ t ∈ Set.Icc 0 h, ‖f₁ t - f₁ 0‖ ≤ B * h := fun t ht => by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f₁) (f' := f₂) (a := 0) (b := h) (C := B)
      (fun s _ => (h₂ s).hasDerivWithinAt) (fun s hs => hB s ⟨hs.1, hs.2.le⟩) t ht
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0)
  have a2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => f t - t • f₁ 0)
    (f' := fun t => f₁ t - f₁ 0) (a := 0) (b := h) (C := B * h)
    (fun s _ => by
      have := ((h₁ s).sub ((hasDerivAt_id s).smul_const (f₁ 0))).hasDerivWithinAt (s := Set.Icc 0 h)
      rwa [one_smul] at this)
    (fun s hs => a1 s ⟨hs.1, hs.2.le⟩) h ⟨hh, le_rfl⟩
  have e : h • f₁ 0 = f h - f 0 - (f h - h • f₁ 0 - (f 0 - (0 : ℝ) • f₁ 0)) := by rw [zero_smul]; ring
  have a3 : ‖h • f₁ 0‖ ≤ ‖f h‖ + ‖f 0‖ + B * h * (h - 0) := by
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) a2)
  rwa [norm_smul, Real.norm_of_nonneg hh, sub_zero] at a3

theorem decay_of_decay_of_growth {G : Type} [Group G] {q : G → ℝ} (hq : ∀ g, 1 ≤ q g) {a : ℝ → G} (a0 : a 0 = 1)
    (ha : ∀ s t, a (s + t) = a s * a t) {c : ℝ} (hc : ∀ g, ∀ t ∈ Set.Icc (-1 : ℝ) 1, q (g * a t) ≤ c * q g)
    {ψ ψ₁ ψ₂ : G → ℂ} (h₁ : ∀ g, HasDerivAt (fun t => ψ (g * a t)) (ψ₁ g) 0)
    (h₂ : ∀ g, HasDerivAt (fun t => ψ₁ (g * a t)) (ψ₂ g) 0)
    (hψ : ∀ M : ℕ, ∃ C : ℝ, ∀ g, ‖ψ g‖ * q g ^ M ≤ C) {N : ℕ} {B : ℝ} (hB : ∀ g, ‖ψ₂ g‖ ≤ B * q g ^ N) (M : ℕ) :
    ∃ C : ℝ, ∀ g, ‖ψ₁ g‖ * q g ^ M ≤ C := by
  have shift : ∀ {χ χ₁ : G → ℂ}, (∀ g, HasDerivAt (fun t => χ (g * a t)) (χ₁ g) 0) →
      ∀ g s, HasDerivAt (fun t => χ (g * a t)) (χ₁ (g * a s)) s := fun {χ χ₁} h g s => by
    have h1 : HasDerivAt (fun t => χ (g * a s * a t)) (χ₁ (g * a s)) (s - s) := by rw [sub_self]; exact h _
    have h2 := h1.comp_sub_const s s
    simpa only [mul_assoc, ← ha, add_sub_cancel] using h2
  obtain ⟨C, hC⟩ := hψ (N + M + M)
  refine ⟨|c| ^ (N + M + M) * C + C + |B| * |c| ^ N, fun g => ?_⟩
  have q0 : 0 < q g := zero_lt_one.trans_le (hq g)
  have p1 : 1 ≤ q g ^ (N + M) := one_le_pow₀ (hq g)
  set h := (q g ^ (N + M))⁻¹ with hh
  have h0 : 0 < h := by positivity
  have h1 : h ≤ 1 := inv_le_one_of_one_le₀ p1
  have key := mul_norm_deriv_le (shift h₁ g) (shift h₂ g) h0.le (B := |B| * (|c| * q g) ^ N) fun t ht =>
    (hB _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (zero_le_one.trans (hq _))
      ((hc g t ⟨by linarith [ht.1], ht.2.trans h1⟩).trans (mul_le_mul_of_nonneg_right (le_abs_self _) q0.le)) N)
      (pow_nonneg (zero_le_one.trans (hq _)) N) (abs_nonneg _))
  simp only [a0, mul_one] at key
  have b1 : q g ≤ |c| * q (g * a h) := by
    have := hc (g * a h) (-h) ⟨by linarith, by linarith⟩
    rw [mul_assoc, ← ha, add_neg_cancel, a0, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans (hq _)))
  have b2 : ‖ψ (g * a h)‖ * q g ^ (N + M + M) ≤ |c| ^ (N + M + M) * C :=
    calc ‖ψ (g * a h)‖ * q g ^ (N + M + M) ≤ ‖ψ (g * a h)‖ * (|c| * q (g * a h)) ^ (N + M + M) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ q0.le b1 _) (norm_nonneg _)
      _ = |c| ^ (N + M + M) * (‖ψ (g * a h)‖ * q (g * a h) ^ (N + M + M)) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  calc ‖ψ₁ g‖ * q g ^ M = h * ‖ψ₁ g‖ * q g ^ (N + M + M) := by rw [hh]; field_simp; ring
    _ ≤ (‖ψ (g * a h)‖ + ‖ψ g‖ + |B| * (|c| * q g) ^ N * h * h) * q g ^ (N + M + M) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = ‖ψ (g * a h)‖ * q g ^ (N + M + M) + ‖ψ g‖ * q g ^ (N + M + M) + |B| * |c| ^ N := by
        rw [hh]; field_simp; ring
    _ ≤ _ := add_le_add (add_le_add b2 (hC g)) le_rfl

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_add_smul (R : RealPoints θ V) (X : LieInf V) (s t : ℝ) :
    expInf θ V ((s + t) • X : LieInf V) = expInf θ V (s • X : LieInf V) * expInf θ V (t • X : LieInf V) := by
  have he := isExpFam_expInf R
  refine R.2.2.1 _ (he _).1 _ (mul_mem (he _).1 (he _).1) fun τ => ?_
  rw [R.2.2.2.1, (he _).2, (he _).2, (he _).2]
  change NormedSpace.exp ((s + t) • (X τ).1) = NormedSpace.exp (s • (X τ).1) * NormedSpace.exp (t • (X τ).1)
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)]

theorem expInf_zero_smul (R : RealPoints θ V) (X : LieInf V) : expInf θ V ((0 : ℝ) • X : LieInf V) = 1 := by
  have := expInf_add_smul R X 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem continuous_infNorm_expInf (R : RealPoints θ V) (X : LieInf V) (τ : D.what₂.Tau) :
    Continuous fun t : ℝ => infNorm θ V τ (expInf θ V (t • X : LieInf V)) := by
  have h1 : Continuous fun t : ℝ => NormedSpace.exp (t • (X τ).1) := by
    have : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ _
    letI : NormedAlgebra ℚ (AlgInf V) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h0 : Continuous fun t : ℝ => (NormedSpace.exp (t • jInf V X) : AlgInf V) :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have h3 : Continuous fun u : AlgInf V => u τ := continuous_apply τ
    exact (h3.comp h0).congr fun t => exp_algInf V _ τ
  have h2 : Continuous (Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ)) :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
  refine (h2.comp h1).nnnorm.congr fun t => ?_
  rw [infNorm, (isExpFam_expInf R _).2]
  rfl

theorem exists_quotHeight_mul_expInf_le (R : RealPoints θ V) (X : LieInf V) : ∃ c : ℝ, ∀ g, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
    (quotHeight θ V (g * expInf θ V (t • X : LieInf V)) : ℝ) ≤ c * quotHeight θ V g := by
  have hinv : ∀ t : ℝ, (expInf θ V (t • X : LieInf V))⁻¹ = expInf θ V ((-t) • X : LieInf V) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← expInf_add_smul R, add_neg_cancel, expInf_zero_smul R])
  have hcont : Continuous fun t : ℝ => ((∏ τ, infHt θ V τ (expInf θ V (t • X : LieInf V)) : NNReal) : ℝ) := by
    refine NNReal.continuous_coe.comp (continuous_finset_prod _ fun τ _ => ?_)
    simp only [infHt, hinv]
    exact continuous_const.max ((continuous_infNorm_expInf R X τ).max
      ((continuous_infNorm_expInf R X τ).comp continuous_neg))
  obtain ⟨c, hc⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hcont.continuousOn
  refine ⟨2 * c, fun g t ht => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 := (quotHeight_le (θ := θ) (g * expInf θ V (t • X : LieInf V)) hγ).trans
    ((congrArg _ (mul_assoc _ _ _).symm).trans_le
      (HeightCoset.height_mul_le θ V (γ * g) _ (isExpFam_expInf R (t • X)).1))
  have h2 := NNReal.coe_le_coe.2 (h1.trans (mul_le_mul_left hle _))
  rw [NNReal.coe_mul, NNReal.coe_mul] at h2
  refine h2.trans ((mul_le_mul_of_nonneg_left (hc ⟨t, ht, rfl⟩) (by positivity)).trans_eq ?_)
  push_cast
  ring

theorem IsRapidDecay.wordDer (R : RealPoints θ V) {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hl : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (hs : IsSmoothInf V (expInf θ V) φ)
    (hg : IsUnifModerate θ V (expInf θ V) φ) (l : List (LieInf V)) :
    IsRapidDecay θ V (wordDer V (expInf θ V) l φ) := by
  have sm : ∀ l : List (LieInf V), Sm (expInf θ V) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.wordDer V (expInf θ V) l φ) := fun l => by
    rw [show φ = (⟨φ, hs⟩ : SmF θ V).1 from rfl, wordDer_eq R]
    exact Subtype.prop _
  induction l with
  | nil => exact h
  | cons X l ih =>
    obtain ⟨N, hN⟩ := hg
    obtain ⟨B, hB⟩ := hN (X :: X :: l)
    obtain ⟨c, hc⟩ := exists_quotHeight_mul_expInf_le R X
    refine decay_of_decay_of_growth (q := fun g => (quotHeight θ V g : ℝ))
      (fun g => by exact_mod_cast one_le_quotHeight g) (a := fun t => expInf θ V (t • X : LieInf V))
      (expInf_zero_smul R X) (expInf_add_smul R X) hc
      (ψ₂ := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.wordDer V (expInf θ V) (X :: X :: l) φ)
      (fun g => ((sm l).differentiableAt g X).hasDerivAt) (fun g => ((sm (X :: l)).differentiableAt g X).hasDerivAt)
      ih (N := N) (B := |B| * 2 ^ N) fun g => ?_
    obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
    have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
    rw [← wordDer_left (expInf θ V) (hl γ hγ) _ g, mul_assoc, ← mul_pow]
    exact (hB _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))

theorem isRapidDecay_foldr_Rder (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N)
    (hc : IsCuspFun V φ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) : IsRapidDecay θ V (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  have R := (RealPts.realPoints D).2 θ hθ V
  have hs' := (smooth_iff R φ).1 hs
  have hg' := (growth_iff hθ R ha hs').1 hg
  obtain ⟨l', rfl⟩ := exists_sigma_list l hl
  rw [foldr_Rder_eq R]
  exact (hP D θ hθ V _ (isExpFam_expInf R) φ ha hs' hg' hc).wordDer R ha.left hs' hg' _

theorem cuspBounded_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) : GlobalTheory.Published.CuspBounded :=
  fun _ _ hθ _ _ ha hs hg hc l hl => (isRapidDecay_foldr_Rder hP hθ ha hs hg hc l hl).bounded

theorem memLp_of_bounded {φ : GA D V → ℂ} (hφ : Continuous φ) (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (p : ENNReal) :
    MemLp φ p (μ.restrict 𝓕) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  obtain ⟨C, hC⟩ := hb
  exact MemLp.of_bound hφ.measurable.aestronglyMeasurable C (.of_forall hC)

theorem memLp_two_of_cuspBounded (hP : GlobalTheory.Published.CuspBounded) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hg : ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N)
    (hc : IsCuspFun V φ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : MemLp φ 2 (μ.restrict 𝓕) :=
  memLp_of_bounded ha.cont (hP D θ hθ V φ ha hs hg hc [] fun _ h => absurd h List.not_mem_nil) μ 𝓕 hμ h𝓕 2

end GlobalTheory.CuspDecay

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar)
open scoped InnerProductSpace Topology

namespace GlobalTheory.Published

namespace Langlands

def IsRightDeriv {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (X : Matrix (Fin n) (Fin n) ℂ) (f f' : UJ ε → V) : Prop :=
  ∀ g, HasDerivAt (fun t : ℝ => f (g * expG ε X t)) (f' g) 0

def Induced : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε),
    IsAdmRep ε I.ρ ∧ HasFiniteLength ε I.ρ ∧ IsGKSub ε I.ρ (kFinVec ε I.ρ) ∧
    (∀ w, IsKFin ε I.ρ w ↔ ∃ f : I.fns, IsKFinFun f.1 ∧ I.ι f = w) ∧
    (∀ f : I.fns, IsKFinFun f.1 → ∀ X ∈ lieSet ε,
      ∃ f' : I.fns, IsRightDeriv X f.1 f'.1 ∧ dRep I.ρ X (I.ι f) = I.ι f') ∧
    ∀ f ∈ I.fns, ∀ f' ∈ I.dualFns, ∀ y : UJ ε,
      ∫ k : KG ε, ⟪f' (k * y), f (k * y)⟫_ℂ ∂muK ε = ∫ k : KG ε, ⟪f' k, f k⟫_ℂ ∂muK ε

def Quotient : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν →
    (∀ f ∈ I.fns, IsKFinFun f → ∃ h ∈ I.oppFns, IsKFinFun h ∧ I.IsIntegral ν f h) ∧
    (∀ f ∈ I.fns, IsKFinFun f → ∀ X ∈ lieSet ε, ∀ f' h h', IsRightDeriv X f f' → I.IsIntegral ν f h →
      I.IsIntegral ν f' h' → IsRightDeriv X h h') ∧
    ∃ Z : Submodule ℂ I.H, (Z : Set I.H) = I.intKer ν ∧ IsGKSub ε I.ρ Z ∧ Z ≠ kFinVec ε I.ρ ∧
      (∀ Y, IsGKSub ε I.ρ Y → Y = kFinVec ε I.ρ ∨ Y ≤ Z) ∧
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π ∧ IsFactor ε I.ρ Z (kFinVec ε I.ρ) π

def Classification : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π →
      (∃ I : IndModule ε, I.IsStandard W₀ ∧ ∃ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π ∧
        ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) ∧
      ∀ I I' : IndModule ε, I.IsStandard W₀ → I'.IsStandard W₀ → ∀ Z Z', IsFactor ε I.ρ Z (kFinVec ε I.ρ) π →
        IsFactor ε I'.ρ Z' (kFinVec ε I'.ρ) π → I.Equiv I'.toDatum

def Limit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), D.Positive → ∀ ν' : Measure (UJ ε), IsHaarSub D.Nbar ν' →
    ∃ c : ℝ, 0 < c ∧
      (∀ φ ∈ indFun ⊤ D.j D.W (fun _ => (1 : ℂ →L[ℂ] ℂ)) (rho n D.j),
        Integrable φ ν' ∧ ∫ k : KG ε, φ k ∂muK ε = c * ∫ u, φ u ∂ν') ∧
      ∀ f ∈ D.fns, IsKFinFun f → ∀ f' ∈ D.dualFns, IsKFinFun f' → ∀ x, InChamber x →
        ∀ t : ℝ → UJ ε, (∀ r, IsSplit ε D.W (r • x) (t r)) →
          Integrable (fun u => ⟪f' 1, f u⟫_ℂ) ν' ∧
          Tendsto (fun r : ℝ => Complex.exp (r * pairing D.j (rho n D.j - D.s) x) *
              ∫ k : KG ε, ⟪f' k, f (k * t r)⟫_ℂ ∂muK ε) atTop (𝓝 (c * ∫ u, ⟪f' 1, f u⟫_ℂ ∂ν'))

def StandardSpan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hπ : IsIrrAdm ε π),
      ∃ (N : ℕ) (I : Fin N → IndModule ε) (c : Fin N → ℤ),
        (∀ i, (I i).IsStandard W₀) ∧ (∀ i l, (I i).Equiv (I l).toDatum → i = l) ∧ (∀ i, c i ≠ 0) ∧
        (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
          (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsIrrAdm ε π' →
          ((mult ε π π').toNat : ℤ) = ∑ i, c i * (mult ε (I i).ρ π').toNat) ∧
        (∀ i χ, HasInfChar ε χ (I i).ρ ↔ HasInfChar ε χ π) ∧
        ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure], ∀ f ∈ GlobalTheory.Orb.CcMat (GlobalTheory.Orb.ujMat ε),
          (∀ i, IsTraceClass (repOp (I i).rep μ f)) ∧
          HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) (∑ i, c i * trace (repOp (I i).rep μ f))

def StandardIndependent : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ (N : ℕ) (I : Fin N → IndModule ε) (c : Fin N → ℤ),
      (∀ i, (I i).IsStandard W₀) → (∀ i l, (I i).Equiv (I l).toDatum → i = l) →
      (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (π' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsIrrAdm ε π' →
        ∑ i, c i * (mult ε (I i).ρ π').toNat = 0) → c = 0

def TemperedLevi : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (b : ℕ) (W' : Flag n b), IsIsoFlag ε (fun _ => 1) W' →
    (∀ i, D.W i ∈ Set.range W') → W' (Fin.last b) = D.W (Fin.last D.a) →
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : CompleteSpace U)
      (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (y : Fin b → ℝ), IsIrrTempered (leviOne ε W') τ ∧
      ∀ μ : Measure ↥(KG ε ⊓ D.M), μ.IsHaarMeasure → IsProbabilityMeasure μ →
        ∃ ι : indFun D.M (fun _ => 1) W' τ (fun l => Complex.I * y l) →ₗ[ℂ] D.V,
          IsIndModel D.M (KG ε ⊓ D.M) μ _ D.σ ι

end Langlands

open Langlands in

def LanglandsClassification : Prop :=
  Induced ∧ Quotient ∧ Classification ∧ Limit ∧ StandardSpan ∧ StandardIndependent ∧ TemperedLevi

theorem Langlands.exists_isHaarSub_nbar {n : ℕ} {ε : Fin n → Bool} (D : Datum ε) :
    ∃ ν : Measure (UJ ε), IsHaarSub D.Nbar ν := by
  obtain ⟨⟨N, hN⟩, hc, -⟩ := UnipRad.flagN_subgroup_closed_keeps n ε _ _ _ (isIsoFlag_opp D.flag)
  rw [Datum.Nbar, ← hN]
  rw [← hN] at hc
  have : LocallyCompactSpace N := hc.locallyCompactSpace
  refine ⟨(Measure.haar : Measure N).map Subtype.val,
    fun h => NeZero.ne _ ((Measure.map_eq_zero_iff measurable_subtype_coe.aemeasurable).1 h), ⟨fun T hT => ?_⟩, ?_,
    fun s hs => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hT.measurableSet]
    exact (hc.isClosedEmbedding_subtypeVal.isCompact_preimage hT).measure_lt_top
  · rw [Measure.map_apply measurable_subtype_coe hc.measurableSet.compl]
    convert measure_empty (μ := (Measure.haar : Measure N))
    ext x
    simp
  · conv_rhs => rw [← map_mul_left_eq_self Measure.haar (⟨s, hs⟩ : N)]
    rw [Measure.map_map (measurable_const_mul s) measurable_subtype_coe,
      Measure.map_map measurable_subtype_coe (measurable_const_mul _)]
    rfl

theorem Langlands.equiv_of_zero {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (h : I.a = 0) :
    I.M = ⊤ ∧ ∃ U : I.H ≃ₗᵢ[ℂ] I.V, ∀ g ∈ UJset ε, ∀ v, U (I.ρ g v) = I.σ g (U v) := by
  obtain ⟨⟨a, j, W, hW, hj, V, σ, hσ, s⟩, H, ρ, ι, hm⟩ := I
  obtain rfl : a = 0 := h
  have hU : IsURepOn (UJset ε) σ := by
    have := hσ.2.2.1
    rwa [leviOne_zero hW, mats_top] at this
  obtain ⟨U, -, hU⟩ := hm.unique (isIndModel_zero hW hU s) fun _ hf _ hy => indFun_mul_right hf hy
  exact ⟨leviOne_zero hW, U, mats_top (ε := ε) ▸ hU⟩

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
section
open MeasureTheory GlobalTheory.Orb GlobalTheory.AdelicU Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.Published

def PseudoCoefficientUpq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : GlobalTheory.Dec.IsSqIntIrr ε σ)
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f

theorem PseudoCoefficientUpq.of_isDS (hP : PseudoCoefficientUpq) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    (h : IsDS ε lam σ) (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure] :
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f :=
  hP n ε X σ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩ μ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult NumberField in

theorem PseudoCoefficientUpq.exists_isTestArchG (hP : PseudoCoefficientUpq) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    [∀ w, (μa w).IsHaarMeasure] : ∃ fa, IsTestArchG M μa fa :=
  GlobalTheory.Orb.exists_isTestArchG M (fun ρ =>
    have ⟨f, hf⟩ := hP.of_isDS (M.ds ρ) (Formalism.REAL.muG _)
    ⟨Formalism.REAL.muG _, inferInstance, f, hf.2⟩) μa

theorem pseudoCoefficientUpq_trivial (n : ℕ) (μ : Measure (Formalism.REAL.UJ (allPos n))) [μ.IsHaarMeasure] :
    ∃ h : GlobalTheory.Dec.IsSqIntIrr (allPos n) (fun _ => ContinuousLinearMap.id ℂ ℂ),
      ∃ f : Formalism.REAL.UJ (allPos n) → ℂ, IsBiFinite (Formalism.REAL.KG (allPos n)) f ∧
        IsPseudoCoeff (ujMat (allPos n)) μ (ujRep h.2.2.1) f := by
  have hJ : Formalism.REAL.Jm (allPos n) = 1 := by simp [Formalism.REAL.Jm, allPos]
  have hK : Formalism.REAL.KG (allPos n) = ⊤ := by
    refine eq_top_iff.2 fun g _ => ⟨?_, by simp [hJ]⟩
    have := g.2
    change _ * _ * _ = _ at this
    rw [hJ, mul_one] at this
    exact Matrix.mem_unitaryGroup_iff'.2 this
  have : CompactSpace (Formalism.REAL.UJ (allPos n)) := by
    have : CompactSpace (Formalism.REAL.KG (allPos n)) := inferInstance
    rw [hK] at this
    exact (Homeomorph.Set.univ _).compactSpace
  refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ => continuousOn_const⟩,
    fun S _ _ => eq_bot_or_eq_top S, fun v w => memLp_const _⟩, fun _ => (μ.real Set.univ : ℂ)⁻¹, ?_, ?_⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ fun _ => (μ.real Set.univ : ℂ)⁻¹) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, -, k', -, rfl⟩
    exact Submodule.mem_span_singleton_self _
  · have := isPseudoCoeff_char (ι := ujMat (allPos n)) (μ := μ) (χ := 1) (isEmbedding_ujMat _).continuous
      ⟨(isClosed_tsupport _).isCompact, fun _ => 1, contDiff_const, fun _ => by simp⟩
    convert this using 1
    · ext g; simp [ujRep, repVia, GlobalTheory.OpTrace.charRep]
    · ext g; simp

end GlobalTheory.Published
end
end


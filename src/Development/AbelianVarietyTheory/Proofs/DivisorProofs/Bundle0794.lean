import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMemSUAdelic
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem idem_mul (e : R) (he : e * e = e) (A B : Matrix n n R) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 + e • (A * B - 1) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem idem_cT (c : R →+* R) (e : R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, hc, eq_comm]

theorem idem_unitary (c : R →+* R) (e : R) (he : e * e = e) (hc : c e = e) (J A : Matrix n n R)
    (hA : Formalism.UG.cT c A * J * A = J) :
    Formalism.UG.cT c (1 + e • (A - 1)) * J * (1 + e • (A - 1)) = J := by
  rw [idem_cT c e hc]
  have : (1 + e • (Formalism.UG.cT c A - 1)) * J * (1 + e • (A - 1)) =
      J + e • (Formalism.UG.cT c A * J * A - J) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add, Matrix.mul_assoc]
    abel
  rw [this, hA, sub_self, smul_zero, add_zero]

theorem idem_det (e : R) (he : e * e = e) (A : Matrix n n R) (hA : A.det = 1) :
    (1 + e • (A - 1)).det = 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Matrix.det_isEmpty
  have hpow : ∀ f : R, f * f = f → ∀ k : ℕ, f ^ (k + 1) = f := by
    intro f hf k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hf]
  have hk : Fintype.card n = (Fintype.card n - 1) + 1 := by
    have := Fintype.card_pos (α := n); omega
  have h1 : e • (1 + e • (A - 1)) = e • A := by
    rw [smul_add, smul_smul, he, smul_sub]; abel
  have h2 : (1 - e) • (1 + e • (A - 1)) = (1 - e) • (1 : Matrix n n R) := by
    rw [smul_add, smul_smul, show (1 - e) * e = 0 by rw [sub_mul, one_mul, he, sub_self], zero_smul, add_zero]
  have he' : (1 - e) * (1 - e) = 1 - e := by ring_nf; rw [sq, he]; ring
  have d1 := congrArg Matrix.det h1
  have d2 := congrArg Matrix.det h2
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow e he, hA] at d1
  rw [Matrix.det_smul, Matrix.det_smul, hk, hpow _ he', Matrix.det_one] at d2
  linear_combination d1 + d2

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qr (x : Fin M → E) (u : E) : Matrix (Fin M) (Fin M) E :=
  1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) J)

theorem sigR_inclR (e : E) : sigR (AF F) σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

def rmat (g : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  RingHom.mapMatrix (inclR (AF F)) (g : Matrix (Fin M) (Fin M) E)

theorem cT_rmat (g : GL (Fin M) E) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) =
      RingHom.mapMatrix (inclR (AF F)) (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)) := by
  ext i j
  simp [rmat, Formalism.UG.cT, sigR_inclR]

theorem rmat_unitary {g : GL (Fin M) E} (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.cT (sigR (AF F) σ) (rmat (F := F) g) * JR (AF F) J * rmat (F := F) g = JR (AF F) J := by
  have h : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  rw [cT_rmat, show JR (AF F) J = RingHom.mapMatrix (inclR (AF F)) J from rfl, rmat, ← map_mul, ← map_mul, h]

def tm (η : AF F) (A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  1 + algebraMap (AF F) (AF F ⊗[F] E) η • (A - 1)

theorem tm_mul (η : AF F) (hη : η * η = η) (A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    tm η A * tm η B = tm η (A * B) :=
  idem_mul _ (by rw [← map_mul, hη]) A B

def trunc (η : AF F) (hη : η * η = η) : Formalism.UG.UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨⟨tm η (rmat g.1), tm η (rmat g.1⁻¹),
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero],
      by rw [tm_mul η hη, rmat, rmat, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, tm,
        sub_self, smul_zero, add_zero]⟩,
    idem_unitary _ _ (by rw [← map_mul, hη]) (StrongApprox.sigR_algebraMap σ η) _ _ (rmat_unitary σ J g.2)⟩ : HR (AF F) σ J)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (1 : GL (Fin M) E)) = 1
    rw [rmat, Units.val_one, map_one, tm, sub_self, smul_zero, add_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    change tm η (rmat (g.1 * h.1)) = tm η (rmat g.1) * tm η (rmat h.1)
    rw [tm_mul η hη, rmat, rmat, rmat, ← map_mul, Units.val_mul]

theorem mv_trunc (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) :
    ((HA.mat (AF F) σ J (trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g.1 - 1) := rfl

theorem trunc_mem_SUAdelic (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J)
    (hg : (g.1 : Matrix (Fin M) (Fin M) E).det = 1) : trunc σ J η hη g ∈ SUAdelic σ J := by
  rw [StrongApprox.mem_SUAdelic, mv_trunc]
  refine idem_det _ (by rw [← map_mul, hη]) _ ?_
  rw [rmat, ← RingHom.map_det, hg, map_one]

theorem idem_mul_of_sub {S₁ S₁' : Finset (InfinitePlace F)} {S₂ S₂' : Finset (HeightOneSpectrum (𝓞 F))}
    {ε ε' : AF F} (h : IsPlacesIdem S₁ S₂ ε) (h' : IsPlacesIdem S₁' S₂' ε') (hS₁ : S₁' ⊆ S₁) (hS₂ : S₂' ⊆ S₂) :
    ε * ε' = ε' := by
  obtain ⟨a1, -, b1, -⟩ := h
  obtain ⟨-, a0', -, b0'⟩ := h'
  apply Prod.ext
  · funext w
    change fstA F ε w * fstA F ε' w = fstA F ε' w
    by_cases hw : w ∈ S₁'
    · rw [a1 w (hS₁ hw), one_mul]
    · rw [a0' w hw, mul_zero]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε') = evalV F v (sndA F ε')
    by_cases hv : v ∈ S₂'
    · rw [b1 v (hS₂ hv), one_mul]
    · rw [b0' v hv, mul_zero]

theorem idem_sq {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε :=
  idem_mul_of_sub h h subset_rfl subset_rfl

theorem SUSupp_mono {ε ε' : AF F} (hε : ε * ε' = ε') {g : HA (AF F) σ J} (hg : g ∈ SUSupp σ J ε') :
    g ∈ SUSupp σ J ε := by
  refine ⟨hg.1, fun i j => ?_⟩
  rw [← hg.2 i j, ← mul_assoc, ← map_mul, hε]

end GlobalTheory.SUAssemble
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinLogGrowthWeight
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LogGrowth

noncomputable section

theorem db_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n) (c : ℂ) :
    db n z k (fun _ => c) = fun _ => 0 := by
  funext x
  unfold db
  split_ifs <;> simp [wdb, Function.comp_def]

theorem d_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (c : ℂ) (x : M) :
    d n z j (fun _ => c) x = 0 := by
  unfold d
  split_ifs <;> simp [wd, Function.comp_def]

theorem levi_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (x : M)
    (ξ : Fin n → ℂ) : Levi n z (fun _ => c) x ξ = 0 := by
  simp only [Levi, db_const_fun, d_const_fun, zero_mul, Finset.sum_const_zero]

theorem ckR_two_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ)
    (h : SmoothR n z f) : CkR n z 2 f := fun e he => (h e he).of_le (by exact_mod_cast lse_two_le_infty)

theorem smoothR_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) :
    SmoothR n z (fun _ => c) := fun e _ => by
  simpa [Function.comp_def] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : V n => (c : ℂ)) e.target)

theorem levi_add_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) (c : ℝ)
    (hf : SmoothR n z f) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => f y + c) x ξ = Levi n z f x ξ := by
  have := levi_add n z f (fun _ => c) (ckR_two_of_smoothR n z f hf)
    (ckR_two_of_smoothR n z _ (smoothR_const n z c)) x ξ
  rw [this, levi_const_fun, add_zero]

theorem logShift_lse {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (X : EtaleStein n M) (k : ℕ) :
    SmoothR n X.z (fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1))) ∧
      LeviNonneg n X.z (fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1))) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsub : SmoothR n X.z (fun y => X.e y + (-Real.log ((k : ℝ) + 1))) := by
    rw [lse_smoothR_iff_real]
    intro e he
    exact ((lse_smoothR_iff_real n X.z X.e).1 X.smooth_e e he).add contDiffOn_const
  have h := lse n M X.z X.isLocalHomeomorph 2 0
    ![fun _ => 0, fun y => X.e y + (-Real.log ((k : ℝ) + 1))] (fun j => j.elim0) ?_ ?_
    (fun j => j.elim0) ?_
  · have hfun : (fun x => Real.log (∑ i, Real.exp ((![fun _ => (0 : ℝ), fun y => X.e y + (-Real.log ((k : ℝ) + 1))] : Fin 2 → M → ℝ) i x) +
        ∑ j : Fin 0, ‖(j.elim0 : M → ℂ) x‖ ^ 2)) =
        fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1)) := by
      funext x
      simp [Fin.sum_univ_two, Real.exp_add, Real.exp_neg, Real.exp_log hk, div_eq_mul_inv]
    rw [hfun] at h
    exact h
  · intro i
    fin_cases i
    · exact smoothR_const n X.z 0
    · exact hsub
  · intro i
    fin_cases i
    · intro x ξ
      simp [levi_const_fun]
    · intro x ξ
      show 0 ≤ (Levi n X.z (fun y => X.e y + (-Real.log ((k : ℝ) + 1))) x ξ).re
      rw [levi_add_const n X.z X.e _ X.smooth_e]
      exact X.levi_e x ξ
  · intro x
    simp
    positivity

end

end GlobalTheory.LogGrowth

namespace GlobalTheory.LogGrowth

noncomputable section

theorem twisted_extension_logGrowth : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → (∃ (N : ℕ) (C : ℝ), ∀ x, -ψ x ≤ N * X.e x + C) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) φ < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGhol hΩψ hgrow hfin
  obtain ⟨N, C, hNC⟩ := hgrow
  set B : ℝ≥0∞ := 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
    ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z with hB
  by_cases hBtop : B = ⊤
  · refine ⟨fun _ => 0, fun e _ => differentiableOn_const 0, ?_⟩
    rw [hBtop]
    exact le_top
  have hBlt : B < ⊤ := lt_top_iff_ne_top.2 hBtop
  set Lk : ℕ → M → ℝ := fun k x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1)) with hLk
  have hL : ∀ k, SmoothR n X.z (Lk k) ∧ LeviNonneg n X.z (Lk k) := fun k => logShift_lse X k
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : ∀ k x, 0 ≤ Lk k x := by
    intro k x
    apply Real.log_nonneg
    have : 0 ≤ Real.exp (X.e x) / ((k : ℝ) + 1) := by positivity
    linarith
  have hLlow : ∀ (k : ℕ) (x : M), X.e x - Real.log ((k : ℝ) + 1) ≤ Lk k x := by
    intro k x
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have ha : 0 < Real.exp (X.e x) / ((k : ℝ) + 1) := by positivity
    calc X.e x - Real.log ((k : ℝ) + 1) = Real.log (Real.exp (X.e x) / ((k : ℝ) + 1)) := by
          rw [Real.log_div (Real.exp_pos _).ne' hk.ne', Real.log_exp]
      _ ≤ Lk k x := Real.log_le_log ha (by linarith)
  have hφR := (lse_smoothR_iff_real n X.z φ).1 hφ
  have hψR := (lse_smoothR_iff_real n X.z ψ).1 hψ
  have hsmk : ∀ k, SmoothR n X.z (fun x => φ x + N * Lk k x) := by
    intro k
    rw [lse_smoothR_iff_real]
    intro e he
    exact (hφR e he).add (contDiffOn_const.mul ((lse_smoothR_iff_real n X.z _).1 (hL k).1 e he))
  have hpk : ∀ k, SmoothR n X.z (fun x => (φ x + N * Lk k x) + ψ x) := by
    intro k
    rw [lse_smoothR_iff_real]
    intro e he
    exact ((lse_smoothR_iff_real n X.z _).1 (hsmk k) e he).add (hψR e he)
  have hstep : ∀ k : ℕ, ∃ F : M → ℂ, Holo n X.z F ∧
      ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) * Real.exp (-((φ x + N * Lk k x) + ψ x)))) ∂vol n X.z ≤ B := by
    intro k
    have hlev : ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ),
        LeviNonneg n X.z (fun x => (φ x + N * Lk k x) + α * ψ x) := by
      intro α hα x ξ
      have hfun : (fun x => (φ x + N * Lk k x) + α * ψ x) =
          fun y => (fun x => φ x + α * ψ x) y + (fun x => (N : ℝ) * Lk k x) y := by
        funext y; ring
      have hc1 : SmoothR n X.z (fun x => φ x + α * ψ x) := by
        rw [lse_smoothR_iff_real]
        intro e he
        exact (hφR e he).add (contDiffOn_const.mul (hψR e he))
      rw [hfun, levi_add n X.z (fun x => φ x + α * ψ x) (fun x => (N : ℝ) * Lk k x)
        (ckR_two_of_smoothR n X.z _ hc1)
        (ckR_two_of_smoothR n X.z _ (by
          rw [lse_smoothR_iff_real]
          intro e he
          exact contDiffOn_const.mul ((lse_smoothR_iff_real n X.z _).1 (hL k).1 e he))),
        levi_const_mul n X.z (N : ℝ) (Lk k) (ckR_two_of_smoothR n X.z _ (hL k).1)]
      rw [Complex.add_re, Complex.re_ofReal_mul]
      exact add_nonneg (hlevi α hα x ξ) (mul_nonneg hN0 ((hL k).2 x ξ))
    have hfin' : wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x)
        (fun x => (φ x + N * Lk k x) + ψ x) < ⊤ := by
      unfold wint at hfin ⊢
      have hK : ∀ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
          Real.exp (-((φ x + N * Lk k x) + ψ x))) ≤
          ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) := by
        intro x
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have h2 : (N : ℝ) * X.e x - N * Real.log ((k : ℝ) + 1) ≤ N * Lk k x := by
          have := mul_le_mul_of_nonneg_left (hLlow k x) hN0
          linarith [mul_sub (N : ℝ) (X.e x) (Real.log ((k : ℝ) + 1))]
        have h3 : Real.exp (-((φ x + N * Lk k x) + ψ x)) ≤
            Real.exp (C + N * Real.log ((k : ℝ) + 1)) * Real.exp (-φ x) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          linarith [hNC x]
        calc ‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-((φ x + N * Lk k x) + ψ x))
            ≤ ‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
              (Real.exp (C + N * Real.log ((k : ℝ) + 1)) * Real.exp (-φ x)) :=
              mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
          _ = _ := by ring
      calc _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) ∂vol n X.z :=
            lintegral_mono hK
        _ = ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) ∂vol n X.z :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    obtain ⟨F, hF, hFle⟩ := GlobalTheory.T.twistedExtension_etaleStein_sqIntegrable n M X (fun x => φ x + N * Lk k x) ψ G Ω δ T θ (hsmk k)
      hψ hψ0 hδ hT hθ hlev hΩ hG hGhol hΩψ hfin'
    refine ⟨F, hF, hFle.trans ?_⟩
    rw [hB]
    refine mul_le_mul_of_nonneg_left (lintegral_mono fun x => ?_) (zero_le)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.2
    have := mul_nonneg hN0 (hL0 k x)
    linarith
  choose F hFholo hFle using hstep
  have hz := X.isLocalHomeomorph
  have hψc : Continuous ψ := by
    have h := Smooth.continuous n X.z hz _ hψ
    simpa [Function.comp_def] using Complex.continuous_re.comp h
  have hF0 := (GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθ.1 hθ.2.2.1 hΩ hGhol hΩψ).1
  have hF0c := Smooth.continuous n X.z hz _ hF0
  have hden : ∀ x, 0 < 1 + min ((δ * ψ x) ^ 2) ((T + 1) ^ 2) := fun x =>
    add_pos_of_pos_of_nonneg one_pos (le_min (sq_nonneg _) (sq_nonneg _))
  have homc : Continuous (fun x => wT T (δ * ψ x)) := by
    unfold wT
    exact Continuous.div continuous_const (continuous_const.add
      (((continuous_const.mul hψc).pow 2).min continuous_const)) fun x => (hden x).ne'
  have hc : (0 : ℝ) < 1 / (1 + (T + 1) ^ 2) := by positivity
  have hbd : ∀ x, 1 / (1 + (T + 1) ^ 2) ≤ wT T (δ * ψ x) ∧ wT T (δ * ψ x) ≤ 1 := by
    intro x
    unfold wT
    constructor
    · exact one_div_le_one_div_of_le (hden x) (by linarith [min_le_right ((δ * ψ x) ^ 2) ((T + 1) ^ 2)])
    · rw [div_le_one (hden x)]
      linarith [le_min (sq_nonneg (δ * ψ x)) (sq_nonneg (T + 1))]
  have hanti : ∀ x, Antitone (fun k => (φ x + N * Lk k x) + ψ x) := by
    intro x k k' hkk
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkk' : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkk 1
    have h1 : Lk k' x ≤ Lk k x := by
      apply Real.log_le_log (by have : 0 ≤ Real.exp (X.e x) / ((k' : ℝ) + 1) := by positivity
                                linarith)
      have := div_le_div_of_nonneg_left (Real.exp_pos (X.e x)).le hk hkk'
      linarith
    have := mul_le_mul_of_nonneg_left h1 hN0
    show (φ x + N * Lk k' x) + ψ x ≤ (φ x + N * Lk k x) + ψ x
    linarith
  have htend : ∀ x, Tendsto (fun k => (φ x + N * Lk k x) + ψ x) atTop (𝓝 (φ x + ψ x)) := by
    intro x
    have h1 : Tendsto (fun k : ℕ => Real.exp (X.e x) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      have h2 := (tendsto_const_div_atTop_nhds_zero_nat (Real.exp (X.e x))).comp
        (tendsto_add_atTop_nat 1)
      refine h2.congr fun k => ?_
      simp [Function.comp]
    have h3 : Tendsto (fun k : ℕ => Lk k x) atTop (𝓝 (Real.log (1 + 0))) :=
      ((Real.continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add h1)
    rw [add_zero, Real.log_one] at h3
    have h4 := ((tendsto_const_nhds (x := φ x)).add (h3.const_mul (N : ℝ))).add_const (ψ x)
    simpa using h4
  obtain ⟨Gf, hGf, hGle⟩ := GlobalTheory.T.exists_holo_l2_bound_of_increasing_weights n M X (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => wT T (δ * ψ x)) (1 / (1 + (T + 1) ^ 2)) (fun k x => (φ x + N * Lk k x) + ψ x)
    (fun x => φ x + ψ x) F B hF0c homc hc hbd hpk hanti htend hFholo hBlt hFle
  exact ⟨Gf, hGf, hGle⟩

end

end GlobalTheory.LogGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCube
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

private lemma twelfth_power_clear_denom_three_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hp0 : (p:ℂ) ≠ 0) (hD0 : D ≠ 0)
    (hQ0 : Q ≠ 0) (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+1)) :
    (A*D^n/(Q*p))^12 * (p:ℂ)^3 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+3) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+3) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (-(A^12 * (p:ℂ)^3)) * h3

private lemma twelfth_power_clear_denom_seven_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+3)) :
    (A*Q/D^(n+1))^12 * (p:ℂ)^9 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+9) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+9) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (A^12 * D^3 * s) * h3 + (A^12 * D^(12*n+12)) * hs2

private lemma twelfth_cancel (V : ValuationSubring ℂ) (D A u P s : ℂ) (e : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hv : V.valuation A ^ 3 = V.valuation D)
    (h : u^12 * P^e * D^3 * s = A^12) :
    V.valuation u ^ 12 * V.valuation P ^ e = V.valuation D := by
  have hs : V.valuation s = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs2.trans (one_pow 2).symm) with h1 | h1 <;>
      simp [h1]
  have h' := congrArg V.valuation h
  simp only [map_mul, map_pow, hs, mul_one] at h'
  have hD' : V.valuation D ^ 3 ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hD0)
  apply mul_right_cancel₀ hD'
  rw [h', show 12 = 3 * 4 from rfl, pow_mul, hv, ← pow_succ']

theorem valuation_twelfth_power_of_cube :
    ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 →
      D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D →
      Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) →
      ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9)
        = V.valuation D := by
  intro p V F D A Q hp hD hA hQ hD0 hA0 hv hrel
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [show p - 1 = 2 * (2 * k + 1) by omega, pow_mul'] at hrel
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hrel
    exact pow_ne_zero _ (pow_ne_zero _ hD0) hrel.symm
  have hsq : (Q^4 * (p:ℂ)^3)^2 = (D^(2*k+1))^2 := by rw [← hrel]; ring
  obtain ⟨s, hs2, hε⟩ : ∃ s : ℂ, s^2 = 1 ∧ Q^4 * (p:ℂ)^3 = s * D^(2*k+1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨1, by norm_num, by rw [h, one_mul]⟩
    · exact ⟨-1, by norm_num, by rw [h, neg_one_mul]⟩
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at hε
    refine ⟨A * D^n / (Q * p), div_mem (mul_mem hA (pow_mem hD n)) (mul_mem hQ (natCast_mem F p)),
      div_ne_zero (mul_ne_zero hA0 (pow_ne_zero _ hD0)) (mul_ne_zero hQ0 hp0), ?_⟩
    rw [if_pos (by omega)]
    exact twelfth_cancel V D A _ _ s 3 hD0 hs2 hv (twelfth_power_clear_denom_three_mod_eight p D A Q s n hp0 hD0 hQ0 hs2 hε)
  · rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring] at hε
    refine ⟨A * Q / D^(n+1), div_mem (mul_mem hA hQ) (pow_mem hD _),
      div_ne_zero (mul_ne_zero hA0 hQ0) (pow_ne_zero _ hD0), ?_⟩
    rw [if_neg (by omega)]
    exact twelfth_cancel V D A _ _ s 9 hD0 hs2 hv (twelfth_power_clear_denom_seven_mod_eight p D A Q s n hD0 hs2 hε)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelliStatement
section
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zalg_eq_adjoin_finite_capelli : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ), ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧ Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  first | exact @GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | exact GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | (intros; apply GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps <;> assumption)
end


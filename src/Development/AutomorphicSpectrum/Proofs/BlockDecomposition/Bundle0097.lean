import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0083
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0006
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0026
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumDiagonalFactor
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.GaussProd

theorem sum_pi_prod {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q] (g : ι → Q → ℂ) :
    (∑ y : ι → Q, ∏ i, g i (y i)) = ∏ i, ∑ w, g i w := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem chi_sum {ι Q : Type} [AddCommMonoid Q] (χ : AddChar Q ℂ) (s : Finset ι) (g : ι → Q) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem trace_diag {Q : Type} [CommRing Q] (τ : Q →+* Q) (m n : ℕ) (d : Fin n → Q) (e : Fin m → Q)
    (y : Matrix (Fin m) (Fin n) Q) :
    Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)) =
      ∑ i, ∑ l, e l * d i * (τ (y l i) * y l i) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  ring

theorem red_diagonal {R : Type} [CommRing R] (ϖ : R) (k n : ℕ) (D : Fin n → R) :
    red ϖ k (Matrix.diagonal D) =
      Matrix.diagonal fun i => Ideal.Quotient.mk (lev ϖ k) (D i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [red]
  · simp [red, Matrix.diagonal_apply_ne _ h]

theorem sum_fun_prod {Q : Type} [Fintype Q] (m n : ℕ) (f : Fin n → Fin m → Q → ℂ) :
    (∑ y : Fin m → Fin n → Q, ∏ l, ∏ i, f i l (y l i)) = ∏ i, ∏ l, ∑ w, f i l w := by
  have h1 : ∀ l, ∑ v : Fin n → Q, ∏ i, f i l (v i) = ∏ i, ∑ w, f i l w := fun l =>
    sum_pi_prod (fun i => f i l)
  have h2 := sum_pi_prod (ι := Fin m) (Q := Fin n → Q) (fun l v => ∏ i, f i l (v i))
  simp only [h1] at h2
  rw [Finset.prod_comm]
  exact h2

theorem gauss_gen {Q : Type} [CommRing Q] [Fintype Q] (τ : Q →+* Q) (χ : AddChar Q ℂ) (m n : ℕ)
    (d : Fin n → Q) (e : Fin m → Q) :
    (∑ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)))) =
      ∏ i : Fin n, ∏ l : Fin m, ∑ w : Q, χ (e l * d i * (τ w * w)) := by
  let f : Fin n → Fin m → Q → ℂ := fun i l w => χ (e l * d i * (τ w * w))
  have hterm : ∀ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y))) =
        ∏ l, ∏ i, f i l (y l i) := by
    intro y
    rw [trace_diag, chi_sum, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [chi_sum]
  exact (Fintype.sum_equiv Matrix.of.symm _ _ fun y => hterm y).trans (sum_fun_prod m n f)

theorem gauss_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  intro R _ σ ϖ hf k _ χ m n D E
  have h := gauss_gen (barσ σ ϖ hf k) χ m n (fun i => Ideal.Quotient.mk (lev ϖ k) (D i))
    (fun l => Ideal.Quotient.mk (lev ϖ k) (E l))
  simp only [red_diagonal, map_mul]
  exact h

end GlobalTheory.CompanionTheory.GaussProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPowSmulTopIff
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Completion

theorem mem_pow_smul_top_iff {T : Type} [CommRing T] (t y : T) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule T T) ↔ y ∈ Ideal.span {t ^ n} := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem aic_of_isCompl : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := by
  intro B _ T _ π g hc hπ hA hV P hP hd
  have step := GlobalTheory.T.hensel_polynomial_refinement B T π g hc hπ hA hV P hP hd
  set d := P.natDegree with hdd
  set t := g π with ht

  let S : ℕ → Type := fun M => {a : B // P.eval (g a) ∈ Ideal.span {t ^ (d * M)}}
  have s0 : P.eval (g 0) ∈ Ideal.span {t ^ (d * 0)} := by simp
  let seq : (M : ℕ) → S M := fun M =>
    Nat.rec (motive := S) ⟨0, s0⟩ (fun M a => ⟨(step M a.1 a.2).choose, (step M a.1 a.2).choose_spec.2⟩) M
  have hstep : ∀ M, (seq (M + 1)).1 - (seq M).1 ∈ Ideal.span {π ^ M} := fun M =>
    (step M (seq M).1 (seq M).2).choose_spec.1
  let a : ℕ → T := fun M => g (seq M).1
  have hg : ∀ M, a (M + 1) - a M ∈ Ideal.span {t ^ M} := by
    intro M
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (hstep M)
    refine Ideal.mem_span_singleton'.2 ⟨g c, ?_⟩
    simp only [a, ht, ← map_pow, ← map_mul, hc', map_sub]
  have hpow : ∀ {m n : ℕ}, m ≤ n → Ideal.span {t ^ n} ≤ Ideal.span {t ^ m} := by
    intro m n hmn
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow t hmn
  have hcau : ∀ {m n : ℕ}, m ≤ n → a n - a m ∈ Ideal.span {t ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := Ideal.add_mem _ ih (hpow hmn (hg n))
      simpa using this
  have hpre := hc.compl.toIsPrecomplete
  obtain ⟨x, hx⟩ := hpre.prec' a (fun {m n} hmn => by
    rw [SModEq.sub_mem, mem_pow_smul_top_iff]
    have := Ideal.neg_mem_iff _ |>.2 (hcau hmn)
    simpa using this)
  refine ⟨x, ?_⟩
  have hz : ∀ n, P.eval x ∈ Ideal.span {t ^ n} := by
    intro n
    have h1 : a n - x ∈ Ideal.span {t ^ n} := by
      have := hx n
      rwa [SModEq.sub_mem, mem_pow_smul_top_iff] at this
    have h2 : P.eval (a n) ∈ Ideal.span {t ^ n} :=
      hpow (Nat.le_mul_of_pos_left n hd) (seq n).2
    have h3 : a n - x ∣ P.eval (a n) - P.eval x := Polynomial.sub_dvd_eval_sub _ _ _
    have h4 : P.eval (a n) - P.eval x ∈ Ideal.span {t ^ n} := Ideal.mem_of_dvd _ h3 h1
    have := Ideal.sub_mem _ h2 h4
    simpa using this
  have := hc.compl.toIsHausdorff.haus' (P.eval x) (fun n => by
    rw [SModEq.zero, mem_pow_smul_top_iff]
    exact hz n)
  exact this

end GlobalTheory.CompanionTheory.Completion
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProd
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag

private theorem card_range_vecMul_mul_mul_eq_of_mul_eq_one {Q : Type} [CommRing Q] {n : ℕ}
    (H P P' G G' : Matrix (Fin n) (Fin n) Q) (hP : P' * P = 1) (hG : G * G' = 1) :
    Nat.card (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      Nat.card (Set.range fun x : Fin n → Q => Matrix.vecMul x H) := by
  have hinj : Function.Injective fun y : Fin n → Q => Matrix.vecMul y G := by
    intro y₁ y₂ hy
    have h := congrArg (fun v => Matrix.vecMul v G') hy
    simpa only [Matrix.vecMul_vecMul, hG, Matrix.vecMul_one] using h
  have hrange : (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      (fun y => Matrix.vecMul y G) '' Set.range fun x : Fin n → Q => Matrix.vecMul x H := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Matrix.vecMul (Matrix.vecMul z P) H, ⟨Matrix.vecMul z P, rfl⟩,
        by simp only [Matrix.vecMul_vecMul]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Matrix.vecMul x P', by
        simp only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hP, Matrix.one_mul]⟩
  rw [hrange, Nat.card_image_of_injective hinj]

theorem cT_mul' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} :
    cT σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem red_mul' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    red ϖ k (a * b) = red ϖ k a * red ϖ k b := by
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_mul]

theorem red_one' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} :
    red ϖ k (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.red]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem card_range_vecMul_diagonal {A : Type} [CommRing A] {n : ℕ} (e : Fin n → A) :
    Nat.card (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      ∏ i : Fin n, Nat.card (Set.range fun w : A => w * e i) := by
  have hset : (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      Set.pi Set.univ (fun i => Set.range fun w : A => w * e i) := by
    ext v
    simp only [Set.mem_range, Set.mem_univ_pi]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, by rw [Matrix.vecMul_diagonal]⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext fun i => by rw [Matrix.vecMul_diagonal, hz i]⟩
  rw [hset, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]

theorem nuAt_eq_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  intro R _ σ ϖ _ _ k _ n h g g' d hgg' hg'g hdiag
  have hP : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g') *
      PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_mul', hgg',
      GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_one', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hG : PositivityTheory.PfSWUS.Loc.red ϖ k g * PositivityTheory.PfSWUS.Loc.red ϖ k g' = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hgg', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hD : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) * PositivityTheory.PfSWUS.Loc.red ϖ k h *
      PositivityTheory.PfSWUS.Loc.red ϖ k g =
        Matrix.diagonal fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i) := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hdiag]
    simp only [PositivityTheory.PfSWUS.Loc.red]
    exact Matrix.diagonal_map (map_zero _)
  unfold PositivityTheory.PfSWUS.Loc.nuAt
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
    (fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i)))
  rw [← hD]
  exact (card_range_vecMul_mul_mul_eq_of_mul_eq_one _ _ _ _ _ hP hG).symm

end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormInvGammaLeReflect
section
open Complex Set
open scoped Real

namespace GlobalTheory.CompanionTheory.InvGammaStrip

theorem norm_inv_Gamma_le_reflect {z : ℂ} (hre : z.re < 1) (him : z.im ≠ 0) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (1 - z.re) * Real.exp (π * |z.im|) / π := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : Complex.sin (π * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have h := congrArg Complex.im hk
    simp [Real.pi_ne_zero] at h
    exact him h
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero fun m h => him (by rw [h]; simp)
  have hinv : (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
    have h6 : Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (π * z) = π := by
      rw [Complex.Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hsin]
    refine eq_div_of_mul_eq hpi ?_
    rw [inv_mul_eq_iff_eq_mul₀ hG]
    linear_combination -h6
  have h1 : ‖Complex.Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have := PI.EF.norm_Gamma_le (w := 1 - z) (by simp; linarith)
    simpa using this
  have h2 : ‖Complex.sin (π * z)‖ ≤ Real.exp (π * |z.im|) := by
    refine (GlobalTheory.CompanionTheory.DigammaStrip.norm_sin_le_exp _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr

theorem exists_bound_left (a : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 / 2 → z.im ≠ 0 →
      ‖(Complex.Gamma z)⁻¹‖ ≤ K * Real.exp (π * |z.im|) := by
  have hc : ContinuousOn Real.Gamma (Icc (1 / 2) (max (1 / 2) (1 - a))) := fun x hx =>
    (Real.differentiableAt_Gamma fun m h => by
      have h0 := hx.1
      have h1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [h] at h0
      linarith).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|M| / π, by positivity, fun z h1 h2 h3 => ?_⟩
  refine (norm_inv_Gamma_le_reflect (by linarith) h3).trans ?_
  have hb : Real.Gamma (1 - z.re) ≤ |M| := by
    have := hM (1 - z.re) ⟨by linarith, le_max_of_le_right (by linarith)⟩
    exact (le_abs_self _).trans (this.trans (le_abs_self _))
  rw [div_mul_eq_mul_div]
  gcongr

theorem exists_bound_far (a b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ K * Real.exp (π * |z.im|) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_left (min a (-1 / 2))
  refine ⟨K, hK0, ?_⟩
  have key : ∀ n : ℕ, ∀ z : ℂ, min a (-1 / 2) ≤ z.re → z.re ≤ 1 / 2 + n → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ K * Real.exp (π * |z.im|) := by
    intro n
    induction n with
    | zero =>
      intro z h1 h2 h3
      refine hK z h1 (by simpa using h2) ?_
      intro h
      rw [h, abs_zero] at h3
      linarith
    | succ n ih =>
      intro z h1 h2 h3
      by_cases hz : z.re ≤ 1 / 2 + n
      · exact ih z h1 hz h3
      push_neg at hz
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hlow : min a (-1 / 2) ≤ (z - 1).re := by
        have : min a (-1 / 2) ≤ -1 / 2 := min_le_right _ _
        simp only [sub_re, one_re]
        linarith
      have hup : (z - 1).re ≤ 1 / 2 + n := by
        push_cast at h2
        simp only [sub_re, one_re]
        linarith
      have him : (z - 1).im = z.im := by simp
      have h := ih (z - 1) hlow hup (by rwa [him])
      rw [him] at h
      have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z - 1)
      rw [sub_add_cancel] at hrec
      have hnorm : 1 ≤ ‖z - 1‖ := h3.trans (by
        rw [← him]
        exact Complex.abs_im_le_norm _)
      have hle : ‖(Complex.Gamma z)⁻¹‖ ≤ ‖(Complex.Gamma (z - 1))⁻¹‖ := by
        rw [hrec, norm_mul]
        exact le_mul_of_one_le_left (norm_nonneg _) hnorm
      exact hle.trans h
  intro z h1 h2 h3
  obtain ⟨n, hn⟩ := exists_nat_ge b
  exact key n z ((min_le_left _ _).trans h1) (by linarith) h3

theorem exists_norm_inv_Gamma_le (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (π * |z.im|) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_far a b
  have hcomp : IsCompact (Icc a b ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨D, hD⟩ := hcomp.exists_bound_of_continuousOn
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  refine ⟨max K |D|, le_max_of_le_left hK0, fun z h1 h2 => ?_⟩
  have hexp : 1 ≤ Real.exp (π * |z.im|) := Real.one_le_exp (by positivity)
  by_cases hz : 1 ≤ |z.im|
  · exact (hK z h1 h2 hz).trans (by gcongr; exact le_max_left _ _)
  · push_neg at hz
    have hmem : z ∈ Icc a b ×ℂ Icc (-1 : ℝ) 1 :=
      Complex.mem_reProdIm.2 ⟨⟨h1, h2⟩, (abs_le.1 hz.le)⟩
    have h := hD z hmem
    calc ‖(Complex.Gamma z)⁻¹‖ ≤ |D| := h.trans (le_abs_self _)
      _ ≤ max K |D| := le_max_right _ _
      _ ≤ max K |D| * Real.exp (π * |z.im|) :=
        le_mul_of_one_le_right (le_max_of_le_left hK0) hexp

end GlobalTheory.CompanionTheory.InvGammaStrip
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
section
noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.MassCount

variable {F : Type} [Field F] [NumberField F]

def emb [IsTotallyReal F] (w : InfinitePlace F) : F →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)

theorem count_box [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB

theorem norm_theta_mul [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (ε : ℝ) (x : F) (w : InfinitePlace F) :
    ‖(θ ε * algebraMap F (InfiniteAdeleRing F) x) w‖ = |ε| * w x := by
  have hw := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ev : InfiniteAdeleRing F →+* w.Completion := Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w
  have h0 : ((e : w.Completion →+* ℝ).comp (ev.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h1 : e (ev (θ ε)) = ε := DFunLike.congr_fun h0 ε
  have hn : ∀ a : w.Completion, ‖a‖ = |e a| := by
    intro a
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a).symm
  have h2 : (θ ε * algebraMap F (InfiniteAdeleRing F) x) w = ev (θ ε) * (algebraMap F (InfiniteAdeleRing F) x) w := rfl
  rw [h2, norm_mul, hn (ev (θ ε)), h1, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
  rfl

theorem countBd : PositivityTheory.Rg.Mass.CountBd := by
  intro F _ _ hF θ _ K hK N hN
  haveI := hF
  have hb : ∀ w : InfinitePlace F, ∃ c : ℝ, ∀ a ∈ K, ‖(a : InfiniteAdeleRing F) w‖ ≤ c := fun w =>
    hK.exists_bound_of_continuousOn (f := fun a : InfiniteAdeleRing F => a w)
      (continuous_apply w).continuousOn
  choose c hc using hb
  set R : ℝ := ∑ w, |c w| with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcR : ∀ w, c w ≤ R := fun w =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w => |c w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))
  refine ⟨(4 * R * N) ^ Module.finrank ℚ F, fun ε hε I hI => ?_⟩
  have hsub : {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (InfiniteAdeleRing F) x ∈ K} ⊆
      {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ R / ε} := by
    rintro x ⟨hx, hy, hxK⟩
    refine ⟨hx, hy, fun w => ?_⟩
    have h := hc w _ hxK
    rw [norm_theta_mul, abs_of_pos hε] at h
    rw [le_div_iff₀ hε, mul_comm]
    exact h.trans (hcR w)
  obtain ⟨hfin, hcount⟩ := count_box N hN I hI (R / ε) (div_nonneg hR0 hε.le)
  refine ⟨hfin.subset hsub, ?_⟩
  have hI0 : (0 : ℝ) < Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hle := Set.ncard_le_ncard hsub hfin
  rw [le_div_iff₀ hI0]
  have hle' := (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hle) hI0.le).trans hcount
  calc _ ≤ ε ^ Module.finrank ℚ F * (4 * (R / ε) * N) ^ Module.finrank ℚ F := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hle' (by positivity)
    _ = (4 * R * N) ^ Module.finrank ℚ F := by
        rw [← mul_pow]
        congr 1
        field_simp

end GlobalTheory.CompanionTheory.MassCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionOffDiagonalIdentityStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_off_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k → 1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | exact GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfOrth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentityStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_square_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfDer | exact GlobalTheory.CompanionTheory.RgHeFrame.pfDer | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfDer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhatStatement
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_integral_mem_schwartzBruhat : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [IsFiniteMeasureOnCompacts μ] (w : B → ℂ), Continuous w → ∀ F : SB (A × B), (fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) ∈ SB A := by
  first | exact @GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | exact GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB | (intros; apply GlobalTheory.CompanionTheory.TestFunctionFibreIntegral.integral_mem_SB <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjMemFixedPiN
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem proj_mem_fixed_piN (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : fixed π D.J) : D.proj π (v : V) ∈ fixed (D.piN π) D.JT := by
  intro t
  have ht : ((t : D.T) : G) ∈ D.J := Subgroup.mem_comap.mp t.2
  have hv : π ((t : D.T) : G) (v : V) = (v : V) := by
    have h := v.2 ⟨((t : D.T) : G), ht⟩
    simpa using h
  have hq : (D.piN π) (t : D.T) (D.proj π (v : V)) = D.proj π (π ((t : D.T) : G) (v : V)) := rfl
  rw [hq, hv, MonoidHom.one_apply, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensorsStatement
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_prod_span_tensors : ∀ (A B : Type) [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B] [TotallyDisconnectedSpace B] (f : SB (A × B)), (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B, (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧ F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by
  first | exact @GlobalTheory.CompanionTheory.FrobProd.span_box | exact GlobalTheory.CompanionTheory.FrobProd.span_box | (intros; apply GlobalTheory.CompanionTheory.FrobProd.span_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzQuadraticPhaseMultiplicationStatement
section
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_quadratic_phase_multiplication : ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  first | exact @GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | exact GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul | (intros; apply GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightAntisymmetricEqStatement
section
open Zc.Comb
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_weight_antisymmetric_eq : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L → AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) → InSh s (L : Multiset (ASeg T)) (wt s M) → (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | exact GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | (intros; apply GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm <;> assumption)
end


import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedMetricLogFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem log_refNorm_blocks {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (d : κ → ℤ)
    {z : (Σ k, ρ k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm d z) = ∑ k, (d k : ℝ) / 2 * Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i))
  unfold refNorm
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hpos k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_rpow (hpos k) _

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem xiDeg_self (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} (hk : M.blk (τ, a) = some k₀) :
    xiDeg M τ a k₀ = -2 := by
  have hd : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := fun p => by
    have hn : ¬ ∀ p', M.blk p' ≠ some k₀ := fun h => h _ hk
    unfold FlagModel.dy
    rw [dif_neg hn]
    by_cases hp : p = (τ, a)
    · rw [if_pos (hp ▸ hk), if_pos hp]
    · rw [if_neg fun e => hp (M.blk_inj _ _ k₀ e hk), if_neg hp]
  unfold xiDeg
  simp only [hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [xiCoef]

theorem log_potA : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ hk zz hz
  have hf : ∀ k, ∃ i, fstPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => hz (some k)
  have hs : ∀ k, ∃ i, sndPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      obtain ⟨i, hi⟩ := hz none
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_self] using hi
    · obtain ⟨i, hi⟩ := hz (some k)
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_ne (p := ⟨k, i⟩) e] using hi
  set A : K → ℝ := fun k => Real.log (∑ i, ‖fstPt k₀ zz ⟨k, i⟩‖ ^ 2) with hA
  set B : K → ℝ := fun k => Real.log (∑ i, ‖sndPt k₀ zz ⟨k, i⟩‖ ^ 2) with hB
  set Ln : ℝ := Real.log (∑ i : ι k₀, ‖zz ⟨none, i⟩‖ ^ 2) with hLn
  have hB₀ : B k₀ = Ln := by
    simp only [hB, hLn, sndPt, Function.comp_apply, v₁_self]
  have hBne : ∀ k, k ≠ k₀ → B k = A k := fun k e => by
    simp only [hA, hB, fstPt, sndPt, Function.comp_apply, v₀]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [v₁_ne (p := ⟨k, i⟩) e]
  have hlhs : Real.log ((potA M τ a k₀).h zz) = 1 / 2 * Ln + ∑ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k := by
    show Real.log (refNorm (aDeg M τ a k₀) zz) = _
    rw [log_refNorm_blocks _ hz, Fintype.sum_option]
    simp only [aDeg, hLn, hA]
    norm_num
    rfl
  have hrhs : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) +
      Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) = ∑ k, (xiDeg M τ a k : ℝ) / 2 * (A k + B k) := by
    have hp : ∀ p, Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz)) =
        ∑ k, (M.dy p k : ℝ) / 2 * (A k + B k) := fun p => by
      rw [fsHerm_h, fsHerm_h, log_refNorm_blocks _ hf, log_refNorm_blocks _ hs, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hA, hB]; ring
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [xiDeg]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hlhs, hrhs]
  have hterm : ∀ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k + 1 / 2 * ((xiDeg M τ a k : ℝ) / 2 * (A k + B k)) =
      if k = k₀ then -(1 / 2) * Ln else 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      rw [if_pos rfl, hB₀, xiDeg_self M hk]
      simp only [aDeg, if_true]
      push_cast
      ring
    · rw [if_neg e, hBne k e]
      simp only [aDeg, if_neg e]
      push_cast
      ring
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset K) = _) fun k _ => hterm k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ k₀, if_pos (Finset.mem_univ _)] at hsum
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib

theorem shear_mul {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s t : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca t) =
      1 + Matrix.single cb ca (s + t) := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hne,
    Matrix.single_add]
  abel

theorem logNorm_add_weights_eq_logSin : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hstep hca hcb k₀ hk₀ RW q h0 h1 f hf Un Gn ΦYn ΦWn l H bp hUn hD z hz hne
  have hPos := GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hstep hca hcb RW.X q Un Gn ΦYn ΦWn l H bp hUn hD _ hz
  obtain ⟨-, -, -, hbase, hG, hex, hq⟩ := hD
  have hπ := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨hq0, hq1⟩ := hq z hz
  generalize hw : Fin.tail (Fin.tail z) = w at hz hPos hq0 ⊢
  obtain ⟨hbO, hH⟩ := hbase w hz
  have hcab : ca ≠ cb := fun e => by
    have : (ca : ℕ) = cb := congrArg Fin.val e
    omega
  have shear := fun s : ℂ => GlobalTheory.T.elementary_factor_properties N j a b ca cb s M.j_le hb hstep hca hcb
  have hflag : ∀ (s : ℂ) (τ' : Ψ), IsBlockDiag j (flagAt H τ ca cb s w τ') ∧ (flagAt H τ ca cb s w τ').det ≠ 0 := by
    intro s τ'
    unfold flagAt
    split_ifs with e
    · refine ⟨(hH τ).1.mul (shear s).1, ?_⟩
      rw [Matrix.det_mul, (shear s).2.1, mul_one]
      exact (hH τ).2
    · exact hH τ'
  obtain ⟨x₀, hx₀⟩ := hπ.2 (q 0 (ΦWn z))
  obtain ⟨x₁, hx₁⟩ := hπ.2 (q 1 (ΦWn z))
  have t0 : Fin.tail (Fin.cons (z 0) w : Fin (d + 1) → ℂ) = w := Fin.tail_cons _ _
  obtain ⟨z₀, o0, b0, ex0⟩ := hex (Fin.cons (z 0) w) (by rw [t0]; exact hz) x₀ (hx₀.trans hq0)
  obtain ⟨z₁, o1, b1, ex1⟩ := hex (Fin.tail z) (by rw [hw]; exact hz) x₁ (hx₁.trans hq1)
  rw [t0] at b0 ex0
  rw [hw] at b1 ex1
  have c0 : (Fin.cons (z 0) w : Fin (d + 1) → ℂ) 0 = z 0 := rfl
  have c1 : (Fin.tail z : Fin (d + 1) → ℂ) 0 = z 1 := rfl
  rw [c0] at ex0
  rw [c1] at ex1

  have L0 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (q 0 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 0) w p.1) := fun p => by
    rw [← hx₀]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ z₀ (bp w) p _ hbO o0 b0 (ex0 p.1 p.2) (hflag _ _).1 (hflag _ _).2
  have L1 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₁) + FA.S.ph (some p) (q 1 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 1) w p.1) := fun p => by
    rw [← hx₁]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₁ z₁ (bp w) p _ hbO o1 b1 (ex1 p.1 p.2) (hflag _ _).1 (hflag _ _).2

  have S : ∀ s : ℂ, ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp w) (flagAt H τ ca cb s w p.1) =
      xiPot (Gn w) s - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := fun s =>
    GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp w)) (fun τ' => H τ' w)
      (fun p => upsLogAt BM l p (bp w)) s (Gn w) M.j_le hb hstep hca hcb (BM.G_pos l τ _ hbO).1
      (BM.G_pos l τ _ hbO).2 (hH τ).1 (hH τ).2 (hG w hz)

  have ht : z 1 - z 0 ≠ 0 := sub_ne_zero.2 fun e => hne e.symm
  have hz0 : ∀ i, M.ExactAt (BM.F l) (τ, i) z₀ (H τ w * (1 + Matrix.single cb ca (z 0))) := fun i => by
    have := ex0 τ i
    rwa [flagAt, if_pos rfl] at this
  have hz1 : ∀ i, M.ExactAt (BM.F l) (τ, i) z₁ (H τ w * (1 + Matrix.single cb ca (z 0)) *
      (1 + Matrix.single cb ca (z 1 - z 0))) := fun i => by
    have := ex1 τ i
    rwa [flagAt, if_pos rfl, show z 1 = z 0 + (z 1 - z 0) by ring, ← shear_mul hcab, ← Matrix.mul_assoc] at this
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₀)) := by
    rw [CovMap.mCoordIdeal_eq_of_sameOrbit b0]
    exact BM.good l _ hbO.1
  have hfx := hf (ΦWn z) z₀ z₁ (BM.F l) (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) (BM.isFrame l) hgood
    (orbit_trans (orbit_symm o0) (h0 _ x₀ hx₀)) (orbit_trans (orbit_symm o1) (h1 _ x₁ hx₁))
    ((hH τ).1.mul (shear _).1) (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2) ht hz0 hz1

  have hval : ∀ i, ¬ IsProperStep N j i → valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀) = upsVal BM l (τ, i) (bp w) := by
    intro i _
    exact (GlobalTheory.T.value_constant_on_orbit _ _ M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _)) (orbit_symm b0)).symm
  have hfac : ∀ i, facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i = facOf N j a (H τ w) i :=
    (shear (z 0)).2.2.1 (H τ w)
  have hlog := GlobalTheory.T.log_norm_product_formula N (IsProperStep N j) (z 1 - z 0)
    (fun i => valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀))
    (fun i => facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i) (fun i => xiCoef τ a (τ, i)) ht
    (fun i hi => by
      refine ⟨?_, GlobalTheory.T.step_factor_ne_zero N j a i _ ((hH τ).1.mul (shear _).1)
        (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2)⟩
      rw [hval i hi]
      exact GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) (bp w) hbO.1 ((M.blk_none _).2 hi))
  have hC : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    by_cases hp : IsProperStep N j i
    · have hn : M.blk (τ, i) ≠ none := fun e => (M.blk_none _).1 e hp
      simp [hp, upsLogAt, hn]
    · have hn : M.blk (τ, i) = none := (M.blk_none _).2 hp
      simp only [hp, if_false, upsLogAt, hn, if_true, hval i hp, hfac i]
      ring
  have hsin := GlobalTheory.T.log_sine_formula (Gn w) (z 0) (z 1) hPos hne
  have hL : normRhs M τ a (BM.F l) z₀ z₁ (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) -
      (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      Real.log ‖z 1 - z 0‖ + ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) := by
    unfold normRhs
    rw [add_sub_cancel_right]
    exact hlog
  have T : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) +
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      (xiPot (Gn w) (z 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) +
      (xiPot (Gn w) (z 1) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) := by
    rw [← S (z 0), ← S (z 1), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e0 : (FA.S.comap some).ph p (q 0 (ΦWn z)) = FA.S.ph (some p) (q 0 (ΦWn z)) := rfl
    have e1 : (FA.S.comap some).ph p (q 1 (ΦWn z)) = FA.S.ph (some p) (q 1 (ΦWn z)) := rfl
    rw [e0, e1, ← L0 p, ← L1 p]
    ring
  rw [hfx, hsin]
  rw [hC] at hL
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib
end
end


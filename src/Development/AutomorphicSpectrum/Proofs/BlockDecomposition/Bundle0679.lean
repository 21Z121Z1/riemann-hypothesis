import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0541
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLFunctionAnalytic
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorExtension
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Nondeg

theorem box_subset_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    (box m s : Set (Fin m → k)) ⊆ box m t := fun x hx j =>
  le_trans (show valuation k (x j) ≤ valuation k (s : k) from hx j) h

theorem exists_unit_bound {k : Type} [Field k] [ValuativeRel k] {W : Type} {S : Set W} (hS : S.Finite)
    (τ : W → kˣ) (t : kˣ) :
    ∃ u : kˣ, valuation k (t : k) ≤ valuation k (u : k) ∧
      ∀ w ∈ S, valuation k (τ w : k) ≤ valuation k (u : k) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨t, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨u, h1, h2⟩ := ih
    rcases le_total (valuation k (u : k)) (valuation k (τ a : k)) with h | h
    · refine ⟨τ a, h1.trans h, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact le_rfl
      · exact (h2 w hw).trans h
    · refine ⟨u, h1, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact h
      · exact h2 w hw

theorem exists_large_unit {k : Type} [Field k] [ValuativeRel k] (c r t₀ : kˣ) :
    ∃ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) ∧
      valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
  · refine ⟨c * r⁻¹, h, ?_⟩
    have e : c * (c * r⁻¹)⁻¹ = r := by simp
    rw [e]
  · refine ⟨t₀, le_rfl, ?_⟩
    have e : ((c * t₀⁻¹ : kˣ) : k) = ((c * r⁻¹ : kˣ) : k) * ((t₀⁻¹ : kˣ) : k) * (r : k) := by
      push_cast
      field_simp
    have e1 : valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul]
      simp
    rw [e, map_mul, map_mul]
    calc valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k)
        ≤ valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k) := by gcongr
      _ = valuation k (r : k) := by rw [e1, one_mul]

theorem continuous_wt_mul_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) {n : ℕ} {V V' : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T) (v : V) (v' : V') :
    Continuous fun x => wt ψ n x * coef T B v v' x := by
  refine Continuous.mul ?_ (continuous_coef T B hT v v')
  have h : Continuous fun x : Fin (n + 1) → k => ψ (-x (Fin.last n)) :=
    hψ.comp (continuous_apply _).neg
  exact continuous_subtype_val.comp h

end GlobalTheory.CompanionTheory.MirPair.Nondeg

namespace GlobalTheory.CompanionTheory.MirPair

open GlobalTheory.CompanionTheory.MirPair.Nondeg in

theorem exists_evVal_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hinv hnd v hv
  obtain ⟨r₁, hr₁, hfix⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₂, hr₂, hlat⟩ := GlobalTheory.T.shear_preserves_box_membership (k := k) (n := n) 1
  obtain ⟨r, hr, hrr₁, hrr₂⟩ : ∃ r : kˣ, valuation k (r : k) < 1 ∧
      valuation k (r : k) ≤ valuation k (r₁ : k) ∧ valuation k (r : k) ≤ valuation k (r₂ : k) := by
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h | h
    · exact ⟨r₁, hr₁, le_rfl, h⟩
    · exact ⟨r₂, hr₂, h, le_rfl⟩
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.mirabolic_twisted_kernel_nonvanishing ν ψ T B hψ hT hnd v hv
  obtain ⟨t, htt₀, htc⟩ := exists_large_unit c r t₀
  obtain ⟨v', hv'⟩ := ht₀ t htt₀
  by_contra hno
  push_neg at hno
  have hev : ∀ w : V', ∃ τ : kˣ, ∀ u : kˣ, valuation k (τ : k) ≤ valuation k (u : k) →
      JJ ν ψ T B (box (n + 1) u : Set (Fin (n + 1) → k)) v w = 0 := by
    intro w
    obtain ⟨A, hA⟩ := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv v w
    have h0 : A = 0 := hno w A hA
    obtain ⟨τ, hτ⟩ := hA
    exact ⟨τ, fun u hu => (hτ u hu).trans h0⟩
  choose τ hτ using hev
  obtain ⟨u, htu, hu⟩ := exists_unit_bound (GlobalTheory.T.shear_orbit_box_finite_of_isSmooth T' hT' v' r hr) τ t
  have hz : ∀ b ∈ box (n + 1) (c * t⁻¹), ∫ x in (box (n + 1) u : Set (Fin (n + 1) → k)),
      ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = 0 := by
    intro b hb
    have hbr : b ∈ (box (n + 1) r : Set (Fin (n + 1) → k)) := box_subset_of_valuation_le htc hb
    have hlast : valuation k (b (Fin.last n)) < 1 :=
      lt_of_le_of_lt (show valuation k (b (Fin.last n)) ≤ valuation k (r : k) from hbr _) hr
    rw [GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hinv b _ v v' hlast
      (hfix b (box_subset_of_valuation_le hrr₁ hbr)) ?_]
    · exact hτ _ u (hu _ ⟨b, hbr, rfl⟩)
    · intro x
      have h := hlat b (box_subset_of_valuation_le hrr₂ hbr) u x
      simpa using h
  have hm : MeasurableSet (box (n + 1) u : Set (Fin (n + 1) → k)) := by
    rw [coe_box]
    exact MeasurableSet.univ_pi fun _ => (isOpen_cball u).measurableSet
  have hfin := setIntegral_inter_box_of_twists ν ψ c hψ hc (n + 1) t
    (box (n + 1) u : Set (Fin (n + 1) → k)) (fun x => wt ψ n x * coef T B v v' x) 0
    (isCompact_box _ _) hm (continuous_wt_mul_coef ψ hψ T B hT v v') hz
  rw [Set.inter_eq_right.2 (box_subset_of_valuation_le htu)] at hfin
  exact hv' hfin

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonsplitPlacePairEquivStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonsplit_place_pair_equiv : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := by
  first | exact @GlobalTheory.CompanionTheory.LocHypInert.inert_iso | exact GlobalTheory.CompanionTheory.LocHypInert.inert_iso | (intros; apply GlobalTheory.CompanionTheory.LocHypInert.inert_iso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfEllipticStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_charpoly_separable_of_elliptic : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
  (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  first | exact @GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | exact GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl | (intros; apply GlobalTheory.CompanionTheory.SepLocEl.separable_charpoly_nrmL_locEl <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLeNormCatRight
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval

lemma norm_le_norm_cat_left (A : Ad3.LR.M22) (y : Fin 2 → ℝ) : ‖A‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
  have h1 : ‖(cat A y) r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  refine le_trans ?_ h1
  fin_cases c
  · exact norm_le_pi_norm (cat A y r) 0
  · exact norm_le_pi_norm (cat A y r) 1

lemma norm_le_norm_cat_right (A : Ad3.LR.M22) (y : Fin 2 → ℝ) : ‖y‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : ‖(cat A y) r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  exact le_trans (norm_le_pi_norm (cat A y r) 2) h1

theorem fz_decay_in_A : ∀ (Φ : Ad3.LR.Sw) (N : ℕ), ∃ C : ℝ, ∀ (A : Ad3.LR.M22) (ξ : Fin 2 → ℝ),
    (1 + ‖A‖) ^ N * ‖GlobalTheory.CompanionTheory.Parseval.fz Φ A ξ‖ ≤ C := by
  intro Φ N
  set C' : ℝ := 2 ^ (N + 3) *
    ((Finset.Iic ((N + 3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ with hC'
  have hdec : ∀ X : Ad3.LR.M23, (1 + ‖X‖) ^ (N + 3) * ‖Φ X‖ ≤ C' := by
    intro X
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 3, 0))
      (k := N + 3) (n := 0) le_rfl le_rfl Φ X
    simpa [norm_iteratedFDeriv_zero] using this
  have hC'0 : 0 ≤ C' := by
    have h0 := hdec 0
    refine le_trans ?_ h0
    positivity
  have hint : Integrable (fun y : Fin 2 → ℝ => (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  set I : ℝ := ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(3 : ℝ)) with hI
  refine ⟨C' * I, fun A ξ => ?_⟩
  have hA : 0 < (1 + ‖A‖) ^ N := by positivity
  have hpt : ∀ y : Fin 2 → ℝ,
      ‖(Φ (cat A y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))‖
        ≤ (C' / (1 + ‖A‖) ^ N) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hph : ‖Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))‖ = 1 := by
      have : (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ)) =
          ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hph, mul_one]
    have hy : 0 < 1 + ‖y‖ := by positivity
    have hy3 : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hy.le]
      norm_cast
    rw [hy3, div_mul_eq_mul_div, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
    have h1 : (1 + ‖A‖) ^ N ≤ (1 + ‖cat A y‖) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_cat_left A y]) N
    have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_cat_right A y]) 3
    have h3 : (1 + ‖A‖) ^ N * (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ (N + 3) := by
      rw [pow_add]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc ‖Φ (cat A y)‖ * ((1 + ‖y‖) ^ 3 * (1 + ‖A‖) ^ N)
        ≤ ‖Φ (cat A y)‖ * (1 + ‖cat A y‖) ^ (N + 3) :=
          mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact h3) (norm_nonneg _)
      _ ≤ C' := by rw [mul_comm]; exact hdec _
  have hbound : ‖fz Φ A ξ‖ ≤ (C' / (1 + ‖A‖) ^ N) * I := by
    unfold fz
    have := norm_integral_le_of_norm_le (hint.const_mul (C' / (1 + ‖A‖) ^ N))
      (Filter.Eventually.of_forall hpt)
    rwa [integral_const_mul] at this
  calc (1 + ‖A‖) ^ N * ‖fz Φ A ξ‖
      ≤ (1 + ‖A‖) ^ N * ((C' / (1 + ‖A‖) ^ N) * I) :=
        mul_le_mul_of_nonneg_left hbound hA.le
    _ = C' * I := by field_simp

end GlobalTheory.CompanionTheory.Parseval
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfMulBlk
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval

open Ad3 Ad3.LR Ad3.LR.C

lemma of_mul_blk (h : M22) (z : Fin 2 → ℝ) :
    Matrix.of.symm (Matrix.of h * blk z) = cat h (fun r => h r 0 * z 0 + h r 1 * z 1) := by
  funext r c
  fin_cases c <;> simp [cat, blk, Matrix.mul_apply, Fin.sum_univ_succ]

lemma dualF_pair (h : M22) (ζ : ℝ) (z : Fin 2 → ℝ) (hd : (Matrix.of h).det ≠ 0) :
    ζ * z 0 + z 1 = dualF h ζ 0 * (h 0 0 * z 0 + h 0 1 * z 1) +
      dualF h ζ 1 * (h 1 0 * z 0 + h 1 1 * z 1) := by
  have hD : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    simp [Matrix.det_fin_two]
  simp only [dualF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  rw [hD]
  ring

theorem gz_eq_fz : ∀ (Φ : Ad3.LR.Sw) (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    GlobalTheory.CompanionTheory.Parseval.gz Φ h ζ = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) *
      GlobalTheory.CompanionTheory.Parseval.fz Φ h (GlobalTheory.CompanionTheory.Parseval.dualF h ζ) := by
  intro Φ h ζ hd
  let L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (Matrix.of h)
  have hLdet : LinearMap.det L = (Matrix.of h).det := LinearMap.det_toLin' _
  have hLz : ∀ z, L z = fun r => h r 0 * z 0 + h r 1 * z 1 := by
    intro z
    funext r
    simp [L, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  let G : (Fin 2 → ℝ) → ℂ := fun y => Φ (cat h y) *
    Complex.exp (2 * Real.pi * Complex.I * ((dualF h ζ 0 * y 0 + dualF h ζ 1 * y 1 : ℝ) : ℂ))
  have hcat : Continuous (fun y : Fin 2 → ℝ => cat h y) := by
    refine continuous_pi fun r => continuous_pi fun c => ?_
    fin_cases c
    · simpa [cat] using continuous_const
    · simpa [cat] using continuous_const
    · simpa [cat] using continuous_apply r
  have hG : Continuous G := by
    refine (Φ.continuous.comp hcat).mul (Complex.continuous_exp.comp ?_)
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    fun_prop
  have hmap : Measure.map L (volume : Measure (Fin 2 → ℝ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hLdet]; exact hd)
  have hint : ∫ z, G (L z) = ∫ y, G y ∂(Measure.map L volume) :=
    (integral_map L.continuous_of_finiteDimensional.aemeasurable hG.aestronglyMeasurable).symm
  have hgz : gz Φ h ζ = ∫ z, G (L z) := by
    unfold gz
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [G]
    rw [of_mul_blk, hLz, dualF_pair h ζ z hd]
  rw [hgz, hint, hmap, integral_smul_measure, hLdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  simp [fz, G, Complex.real_smul]

end GlobalTheory.CompanionTheory.Parseval
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenSupp

theorem isLocallyConstant_ind {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ) :
    IsLocallyConstant (fun g => f.1.1 g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hT := f.2
  refine Filter.mem_of_superset
    ((IsOpen.preimage (f := fun y => g⁻¹ * y) (continuous_const.mul continuous_id) hT).mem_nhds ?_) ?_
  · show _ = _
    simp
  · intro y hy
    have h1 := congrFun (congrArg Subtype.val hy) g
    have h2 : f.1.1 (g * (g⁻¹ * y)) = f.1.1 g := h1
    simpa using h2

theorem support_stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (p : GL (Fin N) k) (hp : p ∈ parab k (stdBlocks d hd)) (g : GL (Fin N) k) (hg : f.1.1 g ≠ 0) :
    f.1.1 (p * g) ≠ 0 := by
  intro h0
  apply hg
  have := parInd_law (stdBlocks d hd) ρ f (⟨p, hp⟩⁻¹) (p * g)
  rw [h0, map_zero, smul_zero] at this
  simpa using this

theorem cell_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : GL (Fin N) k)
    (hg : g ∈ cell k d hd (wOpen d hd)) :
    ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ unipU k d hd, g = p * pm k (wOpen d hd) * u := by
  obtain ⟨p, hp, n, hn, rfl⟩ := hg
  obtain ⟨a, ha, u, hu, rfl⟩ := (GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd).1 n hn
  obtain ⟨m, hm⟩ : (MulAut.conj (pm k (wOpen d hd))).toMonoidHom a ∈ (leviEmb k (stdBlocks d hd)).range := ha.2
  have hc : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m := by
    rw [hm]; rfl
  refine ⟨p * leviEmb k (stdBlocks d hd) m, mul_mem hp (leviEmb_mem_parab k _ m), u, hu, ?_⟩
  rw [← hc]; group

theorem exists_open_of_le {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (U L L₀ : Subgroup G)
    (hL : L ≤ U) (h0 : L₀ ≤ L) (O₀ : Set G) (hO : IsOpen O₀) (hOU : O₀ ∩ (U : Set G) = L₀) :
    ∃ O : Set G, IsOpen O ∧ O ∩ (U : Set G) = L := by
  refine ⟨⋃ l ∈ (L : Set G), (fun x => l⁻¹ * x) ⁻¹' O₀, isOpen_biUnion fun l _ =>
    hO.preimage (continuous_const.mul continuous_id), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨⟨l, hl, hx⟩, hxU⟩
    have : l⁻¹ * x ∈ (L₀ : Set G) := by
      rw [← hOU]
      exact ⟨hx, mul_mem (inv_mem (hL hl)) hxU⟩
    have h2 := mul_mem hl (h0 this)
    simpa using h2
  · intro hx
    have h1 : (1 : G) ∈ (L₀ : Set G) := one_mem L₀
    rw [← hOU] at h1
    exact ⟨⟨x, hx, by simpa using h1.1⟩, hL hx⟩

end GlobalTheory.CompanionTheory.Rodier.OpenSupp

open GlobalTheory.CompanionTheory.Rodier.OpenSupp in

theorem GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  intro k _ _ _ _ h N d hd W _ _ ρ hρ f hf
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  set w := pm k (wOpen d hd) with hw
  set U := unipU k d hd with hU
  set P := parab k (stdBlocks d hd) with hP
  have hUB : U ≤ unipB k (Fin N) := inf_le_left
  have hUc : IsClosed (U : Set (GL (Fin N) k)) := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.2
  obtain ⟨Lj, hmono, hcpt, hle, hexh⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N U hUB hUc
  have hlc := isLocallyConstant_ind d hd ρ f
  let S : Set (GL (Fin N) k) := {g | f.1.1 g ≠ 0}
  have hSo : IsOpen S := hlc ({0}ᶜ)
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff]
    have : Sᶜ = (fun g => f.1.1 g) ⁻¹' {0} := by
      ext g; simp [S]
    rw [this]; exact hlc {0}
  have hcov : ∀ g ∈ S, ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n := by
    intro g hg
    obtain ⟨p, hp, u, hu, rfl⟩ := cell_eq d hd g (hf g hg)
    obtain ⟨j, hj⟩ := hexh u hu
    exact ⟨p, hp, j, u, hj, rfl⟩
  have hSeq : S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ Lj j, g = p * w * n} = S :=
    Set.inter_eq_left.2 hcov
  obtain ⟨j, hj⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset P (GlobalTheory.WhitHered.CellLoc.isClosed_parab _) (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k))
    GlobalTheory.SplitFlip.isCompact_KO (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩) Lj hmono hcpt w S hSo
    (fun p hp g hg => support_stable d hd ρ f p hp g hg) (by rw [hSeq]; exact hSc)
  obtain ⟨L₀, hL₀U, hL₀c, ⟨O₀, hO₀, hO₀U⟩, -⟩ :=
    GlobalTheory.T.exists_bump_section_on_compact_unipotent k (1 : AddChar k Circle) (by simpa using (continuous_one : Continuous (1 : k → Circle))) h N d hd ρ hρ 0
  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact
    ((L₀ : Set (GL (Fin N) k)) ∪ (Lj j : Set (GL (Fin N) k))) (hL₀c.union (hcpt j)) (by
      rintro x (hx | hx)
      · exact hUB (hL₀U hx)
      · exact hUB (hle j hx))
  refine ⟨U₀ ⊓ U, inf_le_right, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hU₀c.inter_right hUc
  · exact exists_open_of_le U (U₀ ⊓ U) L₀ inf_le_right
      (fun x hx => ⟨hU₀ (Or.inl hx), hL₀U hx⟩) O₀ hO₀ hO₀U
  · intro g hg
    obtain ⟨p, hp, n, hn, e⟩ := hj g hg (hcov g hg)
    exact ⟨p, hp, n, ⟨hU₀ (Or.inr hn), hle j hn⟩, e⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadricStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_concentrated_on_quadric : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariantStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_translation_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t), (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariantStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_unitary_group_invariant : QK → Law → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (h : GA D B), (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | exact GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuousStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_involution_continuous : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
  Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧ ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | exact GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLFunctionAnalyticStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_l_function_analytic : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A9 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A10 → Ad3.R.A11 → Ad3.R.H1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.X0 → Ad3.R.RealPlaceGammaFactors → Ad3.R.HalfPlaneAnalyticIdentities → Ad3.R.X1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergLFunctionAnalytic.x1 | exact GlobalTheory.CompanionTheory.RankinSelbergLFunctionAnalytic.x1 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergLFunctionAnalytic.x1 <;> assumption)
end


import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerPolyBallLeOfValuationLe
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_le_of_valuation_le {n : ℕ} {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) : polyBall n s₁ ≤ polyBall n s₂ := by
  intro x hx i
  exact le_trans (show valuation k (Multiplicative.toAdd x i) ≤ valuation k (s₁ : k) from hx i) h

theorem twKer_polyBall_le_of_valuation_le (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  apply Submodule.span_mono
  rintro w ⟨m, u, rfl⟩
  exact ⟨⟨m.1, polyBall_le_of_valuation_le h m.2⟩, u, rfl⟩

theorem resChr_polyBall_eq (ψ : AddChar k Circle) {n : ℕ} {c s : kˣ}
    (hc : ∀ y ∈ cball c, ψ y = 1) {a b : Fin n → k}
    (hab : ∀ i, (a - b) i ∈ cball (c * s⁻¹)) :
    resChr ψ a (polyBall n s) = resChr ψ b (polyBall n s) := by
  ext x
  have hx : ∀ i, valuation k ((Multiplicative.toAdd x.1) i) ≤ valuation k (s : k) := x.2
  have hd : (a - b) ⬝ᵥ Multiplicative.toAdd x.1 ∈ cball c := by
    show valuation k _ ≤ valuation k (c : k)
    unfold dotProduct
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [Valuation.map_mul]
    calc valuation k ((a - b) i) * valuation k ((Multiplicative.toAdd x.1) i)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul' (hab i) (hx i)
      _ = valuation k (c : k) := by rw [← Valuation.map_mul, ← Units.val_mul, inv_mul_cancel_right]
  have key : a ⬝ᵥ Multiplicative.toAdd x.1 = b ⬝ᵥ Multiplicative.toAdd x.1 + (a - b) ⬝ᵥ Multiplicative.toAdd x.1 := by
    rw [sub_dotProduct]
    abel
  show ((Circle.toUnits (ψ (a ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ) =
    ((Circle.toUnits (ψ (b ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ)
  rw [key, AddChar.map_add_eq_mul, hc _ hd, mul_one]

theorem exists_unit_valuation_ge {ι : Type} (S : ι → kˣ) (T : Finset ι) :
    ∃ s : kˣ, ∀ a ∈ T, valuation k (S a : k) ≤ valuation k (s : k) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨1, by simp [hT]⟩
  · obtain ⟨a₀, -, ha₀⟩ := T.exists_max_image (fun a => valuation k (S a : k)) hT
    exact ⟨S a₀, ha₀⟩

end

private theorem isHecke_div_and_resEtaPow_div {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hψ : Continuous ψ) : ∃ c : kˣ, ∀ y ∈ GlobalTheory.SplitWeil.cball c, ψ y = 1 := by
  have hU : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  have hW : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact hU.mem_nhds (by simp)
  have hW' : {f : Fin 1 → k | f 0 ∈ ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re}} ∈ 𝓝 (0 : Fin 1 → k) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds hW
  obtain ⟨c, hcW⟩ := GlobalTheory.SplitWeil.FourierPi.exists_box_subset hW'
  refine ⟨c, fun y hy => ?_⟩
  have hmem : ∀ m : ℕ, m • y ∈ GlobalTheory.SplitWeil.cball c := by
    intro m
    induction m with
    | zero => simp only [zero_smul, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'
    | succ m ih =>
      rw [succ_nsmul]
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at ih hy ⊢
      exact Valuation.map_add_le _ ih hy
  have hpos : ∀ m : ℕ, 0 < (((ψ y) ^ m : Circle) : ℂ).re := by
    intro m
    have := hcW (show (fun _ : Fin 1 => m • y) ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin 1) c from fun i _ => hmem m)
    rw [← AddChar.map_nsmul_eq_pow]
    exact this
  have hn : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := by
    intro w
    rw [← Complex.normSq_apply]
    exact Circle.normSq_coe w
  have hsq : ∀ w : Circle, ((w ^ 2 : Circle) : ℂ).re = 2 * (w : ℂ).re ^ 2 - 1 := by
    intro w
    have h2 : ((w ^ 2 : Circle) : ℂ) = (w : ℂ) * (w : ℂ) := by rw [pow_two]; rfl
    rw [h2, Complex.mul_re]
    nlinarith [hn w]
  have hle1 : ∀ w : Circle, (w : ℂ).re ≤ 1 := fun w => by nlinarith [hn w]
  have hstep : ∀ j : ℕ, (ψ y) ^ (2 ^ (j + 1)) = ((ψ y) ^ (2 ^ j)) ^ 2 := fun j => by rw [pow_succ, pow_mul]
  have hgrow : ∀ j : ℕ, (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) ≤ 1 - ((((ψ y) ^ (2 ^ j) : Circle)) : ℂ).re := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hstep j, hsq]
      have h0 := hpos (2 ^ j)
      have h1 := hle1 ((ψ y) ^ (2 ^ j))
      rw [pow_succ]
      nlinarith
  have hx0 : 1 ≤ ((ψ y : Circle) : ℂ).re := by
    by_contra hlt
    push_neg at hlt
    have hd : 0 < 1 - ((ψ y : Circle) : ℂ).re := by linarith
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - ((ψ y : Circle) : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have h1 := hgrow j
    have h2 := hpos (2 ^ j)
    have h3 : 1 < (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) := by
      rw [div_lt_iff₀ hd] at hj
      linarith
    linarith
  have hre : ((ψ y : Circle) : ℂ).re = 1 := le_antisymm (hle1 _) hx0
  have him : ((ψ y : Circle) : ℂ).im = 0 := by nlinarith [hn (ψ y)]
  apply Circle.ext
  apply Complex.ext
  · simp [hre]
  · simp [him]

theorem exists_polyBall_twKer_uniform : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (t : kˣ),
    (∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s))) →
    ∃ s : kˣ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall n t →
      v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ v t hv
  obtain ⟨c, hc⟩ := isHecke_div_and_resEtaPow_div ψ hψ
  choose S hS using hv
  obtain ⟨T, hT⟩ := (GlobalTheory.SplitWeil.FourierPi.isCompact_box (n := Fin n) t).elim_finite_subcover
    (fun a : Fin n → k => (fun b => b - a) ⁻¹' GlobalTheory.SplitWeil.FourierPi.box (Fin n) (c * (S a)⁻¹))
    (fun a => (GlobalTheory.SplitWeil.FourierPi.isOpen_box _).preimage (continuous_id.sub continuous_const))
    (fun b _ => Set.mem_iUnion.2 ⟨b, fun i _ => by simp only [sub_self, Pi.zero_apply, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'⟩)
  obtain ⟨s, hs⟩ := exists_unit_valuation_ge S T
  refine ⟨s, fun a ha => ?_⟩
  have haK : a ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin n) t := fun i _ => ha i
  obtain ⟨b, hbT, hab⟩ := Set.mem_iUnion₂.1 (hT haK)
  have heq : resChr ψ a (polyBall n (S b)) = resChr ψ b (polyBall n (S b)) :=
    resChr_polyBall_eq ψ hc (fun i => hab i (Set.mem_univ i))
  have h1 := hS b
  rw [← heq] at h1
  exact twKer_polyBall_le_of_valuation_le ψ ρ a (hs b hbT) h1

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSiegelSet
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.TailU

open GlobalTheory.CompanionTheory.SlabGlue An

theorem isCompact_box {K : Type} [Field K] [NumberField K] {n : ℕ} {ω : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (x : Fin n → ℝ) :
    IsCompact {g : AdelicGLn.AdelicGL K n | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧
      ∃ k ∈ maxCompact (K := K) (n := n), g = b * tor K (x + y) * k} := by
  have hY : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-(n : ℝ)) n) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hc : Continuous fun p : AdelicGLn.AdelicGL K n × (Fin n → ℝ) × AdelicGLn.AdelicGL K n =>
      p.1 * tor K (x + p.2.1) * p.2.2 :=
    (continuous_fst.mul (JSqIntGlue.continuous_tor.comp
      (continuous_const.add (continuous_fst.comp continuous_snd)))).mul
      (continuous_snd.comp continuous_snd)
  convert (hω.prod (hY.prod (isCompact_maxCompact (K := K) (n := n)))).image hc using 1
  ext g
  constructor
  · rintro ⟨b, hb, y, hy, k, hk, rfl⟩
    exact ⟨(b, y, k), ⟨hb, fun i _ => abs_le.1 (hy i), hk⟩, rfl⟩
  · rintro ⟨⟨b, y, k⟩, ⟨hb, hy, hk⟩, rfl⟩
    exact ⟨b, hb, y, fun i => abs_le.2 (hy i trivial), k, hk, rfl⟩

theorem tail_lib (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (AdelicGLn.AdelicGL K n))
    [μ.IsHaarMeasure] (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hB : UBnd f κ) (hκ : ∀ r, 0 < r → r < n → κ r < An.rho K n r)
    (ω : Set (AdelicGLn.AdelicGL K n)) (hω : IsCompact ω)
    (hωB : ω ⊆ (adelicBorel (K := K) (n := n) : Set _)) (t₀ : ℝ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  obtain ⟨Cv, hCv⟩ := boxvol_holds K n μ ω hω hωB
  obtain ⟨C, hC⟩ := hB ω hω hωB (|t₀| + 2 * n) (maxCompact (K := K) (n := n) : Set _)
    isCompact_maxCompact
  let box : (Fin n → ℝ) → Set (AdelicGLn.AdelicGL K n) := fun x =>
    {g | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧ ∃ k ∈ maxCompact (K := K) (n := n),
      g = b * tor K (x + y) * k}
  let X : (Fin (n - 1) → ℕ) → Fin n → ℝ := fun s => part n fun j => -t₀ + s j
  let a : Fin (n - 1) → ℝ := fun j => 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))
  let E : ℝ := ∑ r ∈ Finset.range n, |κ r| * (2 * n)
  let D : ℝ := (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j)
  have ha : ∀ j, a j < 0 := by
    intro j
    have hj := j.2
    have := hκ ((j : ℕ) + 1) (by omega) (by omega)
    show 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)) < 0
    linarith
  have hXs : ∀ s (j : Fin (n - 1)), sr (X s) ((j : ℕ) + 1) = -t₀ + s j := fun s j => sr_part _ j

  have hcover : slab ω t₀ ⊆ ⋃ s, box (X s) := by
    rintro g ⟨b, hb, x, hx, hlast, k, hk, rfl⟩
    let s : Fin (n - 1) → ℕ := fun j => ⌊sr x ((j : ℕ) + 1) + t₀⌋₊
    refine Set.mem_iUnion.2 ⟨s, b, hb, x - X s, ?_, k, hk, ?_⟩
    · refine abs_y_le _ ?_ ?_
      · intro i hi
        have : X s i = 0 := part_last _ i hi
        simpa [this] using hlast i hi
      · intro j
        have e : sr x ((j : ℕ) + 1) = sr (X s) ((j : ℕ) + 1) + sr (x - X s) ((j : ℕ) + 1) := by
          rw [← sr_add, add_sub_cancel]
        rw [hXs] at e
        have h0 : 0 ≤ sr x ((j : ℕ) + 1) + t₀ := by
          have := hx ((j : ℕ) + 1)
          linarith
        have h1 : ((s j : ℕ) : ℝ) ≤ sr x ((j : ℕ) + 1) + t₀ := Nat.floor_le h0
        have h2 : sr x ((j : ℕ) + 1) + t₀ < (s j : ℕ) + 1 := Nat.lt_floor_add_one _
        constructor <;> linarith
    · rw [add_sub_cancel]

  have hbox : ∀ i s, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) := by
    intro i s
    let S : ℝ := ∑ r ∈ Finset.range n, κ r * sr (X s) r
    let W : ℝ := max C 0 * Real.exp E * Real.exp S
    have hW0 : 0 ≤ W := by positivity
    have hnorm : ∀ g ∈ box (X s), ‖f i g‖ₑ ^ 2 ≤ ENNReal.ofReal (W ^ 2) := by
      rintro g ⟨b, hb, y, hy, k, hk, rfl⟩
      have hsr : ∀ r, -(|t₀| + 2 * n) ≤ sr (X s + y) r := by
        intro r
        by_cases hr : 0 < r ∧ r < n
        · rw [sr_add]
          have h1 : sr (X s) r = -t₀ + s ⟨r - 1, by omega⟩ := by
            have := hXs s ⟨r - 1, by omega⟩
            simp only at this
            rwa [Nat.sub_add_cancel hr.1] at this
          have h2 := abs_le.1 (abs_sr_le y hy r)
          have h3 : (0 : ℝ) ≤ (s ⟨r - 1, by omega⟩ : ℕ) := Nat.cast_nonneg _
          have h4 := le_abs_self t₀
          rw [h1]
          linarith [h2.1]
        · have : sr (X s + y) r = 0 := by simp [sr, hr]
          rw [this]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          have := abs_nonneg t₀
          linarith
      have h1 := hC i b hb (X s + y) hsr k hk
      have h2 : ∑ r ∈ Finset.range n, κ r * sr (X s + y) r ≤ S + E := by
        show _ ≤ ∑ r ∈ Finset.range n, κ r * sr (X s) r + ∑ r ∈ Finset.range n, |κ r| * (2 * n)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [sr_add, mul_add]
        have h3 : κ r * sr y r ≤ |κ r| * (2 * n) := by
          calc κ r * sr y r ≤ |κ r * sr y r| := le_abs_self _
            _ = |κ r| * |sr y r| := abs_mul _ _
            _ ≤ |κ r| * (2 * n) := mul_le_mul_of_nonneg_left (abs_sr_le y hy r) (abs_nonneg _)
        linarith
      have h3 : ‖f i (b * tor K (X s + y) * k)‖ ≤ W := by
        calc _ ≤ C * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) := h1
          _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max C 0 * Real.exp (S + E) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (le_max_right _ _)
          _ = W := by
              show _ = max C 0 * Real.exp E * Real.exp S
              rw [Real.exp_add]; ring
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h3 2)
    have hmeas : Measurable fun g => ‖f i g‖ₑ ^ 2 := ((hf i).measurable.enorm).pow_const 2
    have hexp : W ^ 2 * (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r))
        = D * ∏ j, Real.exp (a j * s j) := by
      have e1 : ∑ r ∈ Finset.range n, κ r * sr (X s) r
          = ∑ j : Fin (n - 1), κ ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e2 : ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = ∑ j : Fin (n - 1), 2 * rho K n ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr (fun r => 2 * rho K n r)]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e3 : 2 * S - ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = -t₀ * ∑ j, a j + ∑ j, a j * s j := by
        show 2 * ∑ r ∈ Finset.range n, κ r * sr (X s) r - _ = _
        rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        show _ = -t₀ * (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)))
          + (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))) * s j
        ring
      have e4 : Real.exp S ^ 2 * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)
          = Real.exp (-t₀ * ∑ j, a j) * ∏ j, Real.exp (a j * s j) := by
        rw [← Real.exp_sum, ← Real.exp_add, ← e3, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
      show (max C 0 * Real.exp E * Real.exp S) ^ 2 * _ = (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j) * _
      calc _ = (max C 0 * Real.exp E) ^ 2 * Cv * (Real.exp S ^ 2 *
              Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by ring
        _ = _ := by rw [e4]; ring
    calc ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (W ^ 2) * μ (box (X s)) :=
          setLIntegral_le_of_bound μ hmeas _ _ hnorm
      _ ≤ ENNReal.ofReal (W ^ 2) * ENNReal.ofReal
            (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by
          gcongr
          exact hCv (X s)
      _ = ENNReal.ofReal (D * ∏ j, Real.exp (a j * s j)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hexp]
      _ = _ := by
          rw [ENNReal.ofReal_mul' (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
            ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  have hsum : ∑' s : Fin (n - 1) → ℕ, ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤ :=
    tsum_pi_prod_ne_top (n - 1) (fun j k => ENNReal.ofReal (Real.exp (a j * k)))
      fun j => tsum_exp_ne_top (ha j)
  let G : (Fin (n - 1) → ℕ) → ℝ≥0∞ := fun s =>
    ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j))
  have hG : ∑' s, G s ≠ ⊤ := by
    show ∑' s : Fin (n - 1) → ℕ, ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero hG)).2 η hη).exists
  refine ⟨⋃ s ∈ F, box (X s), F.isCompact_biUnion fun s _ => isCompact_box hω (X s), fun i => ?_⟩
  have hsub : slab ω t₀ \ ⋃ s ∈ F, box (X s) ⊆ ⋃ s : {s // s ∉ F}, box (X s) := by
    rintro g ⟨hg, hgF⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 (hcover hg)
    refine Set.mem_iUnion.2 ⟨⟨s, fun hsF => hgF ?_⟩, hs⟩
    exact Set.mem_biUnion hsF hs
  calc ∫⁻ g in slab ω t₀ \ ⋃ s ∈ F, box (X s), ‖f i g‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in ⋃ s : {s // s ∉ F}, box (X s), ‖f i g‖ₑ ^ 2 ∂μ := lintegral_mono_set hsub
    _ ≤ ∑' s : {s // s ∉ F}, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' s : {s // s ∉ F}, G s := ENNReal.tsum_le_tsum fun s => hbox i s
    _ ≤ η := hF.le

theorem tail_unif : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (AdelicGLn.AdelicGL K n)] [BorelSpace (AdelicGLn.AdelicGL K n)] (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (ι : Type)
  (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), (∀ i, Continuous (f i)) → UBnd f κ → (∀ r, 0 < r → r < n → κ r < An.rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ (t₀ : ℝ) (η : ℝ≥0∞), 0 < η →
  ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  intro K _ _ n m hb μ _ ι f κ hf hB hκ ω hω hωB t₀ η hη
  have e : m = measurableSpace_adelicGL := hb.measurable_eq
  subst e
  exact tail_lib K n μ ι f κ hf hB hκ ω hω hωB t₀ η hη

end GlobalTheory.CompanionTheory.Conc.TailU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSmoothingStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ), Ker ν β → (∀ i, Continuous (f i)) →
  UBnd f m → UBnd (fun i => sm ν β (f i)) m := by
  first | exact @GlobalTheory.CompanionTheory.Conc.uBnd_sm | exact GlobalTheory.CompanionTheory.Conc.uBnd_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.uBnd_sm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFamilySmoothingStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_family_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.uFam_sm | exact GlobalTheory.CompanionTheory.Conc.uFam_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.uFam_sm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformTwistedInvarianceOnBallStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_twisted_invariance_on_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (M : ℤ), (∀ a : Fin n → k, ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (chiOn k ψ a (box k n j'))) → ∃ J : ℤ, ∀ J' ≤ J, ∀ a : Fin n → k, (∀ i, a i ∈ valBall k M) → v ∈ twKer ρ (box k n J') (chiOn k ψ a (box k n J')) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHold
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu

namespace GlobalTheory.CompanionTheory.SegLayers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun a b h =>
  Fin.ext ((IrrGL.nu_natCast_inj (x := Δ.first) Δ.d_pos).1 h)

theorem ms_nodup (Δ : Segment k) : Δ.ms.Nodup :=
  Multiset.Nodup.map (term_injective Δ) Finset.univ.nodup

theorem ncard_carrier (Δ : Segment k) : Δ.carrier.ncard = Δ.len := by
  rw [Segment.carrier, ← Set.image_univ, Set.ncard_image_of_injective _ (term_injective Δ)]
  simp

theorem ms_le {Δ : Segment k} {s : Multiset (IrrGL k)} (h : ∀ x ∈ Δ.carrier, x ∈ s) : Δ.ms ≤ s :=
  (Multiset.le_iff_subset (ms_nodup Δ)).2 fun _ hx => h _ (Segment.mem_ms.1 hx)

theorem exists_longest {s : Multiset (IrrGL k)} {y : IrrGL k} (hy : y ∈ s) (hc : y.IsCusp) :
    ∃ Γ : Segment k, (∀ x ∈ Γ.carrier, x ∈ s) ∧
      ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len := by
  classical
  let P : ℕ → Prop := fun l => ∃ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) ∧ D.len = l
  have hb : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Multiset.card s := fun D hD => by
    rw [← Segment.card_ms]
    exact Multiset.card_le_card (ms_le hD)
  have h1 : P 1 := ⟨Segment.single y hc, fun x hx => by
    rw [Segment.carrier_single] at hx
    exact hx ▸ hy, rfl⟩
  have h1' : 1 ≤ Multiset.card s := by
    obtain ⟨D, hD, e⟩ := h1
    exact e ▸ hb D hD
  obtain ⟨Γ, hΓ, e⟩ := Nat.findGreatest_spec h1' h1
  exact ⟨Γ, hΓ, fun D hD => e ▸ Nat.le_findGreatest (hb D hD) ⟨D, hD, rfl⟩⟩

theorem not_linked_of_longest {s : Multiset (IrrGL k)} {Γ D : Segment k} (hΓ : ∀ x ∈ Γ.carrier, x ∈ s)
    (hm : ∀ D : Segment k, (∀ x ∈ D.carrier, x ∈ s) → D.len ≤ Γ.len) (hD : ∀ x ∈ D.carrier, x ∈ s) :
    ¬ Γ.Linked D := by
  rintro ⟨⟨U, hU⟩, -, h2⟩
  have h3 : U.len ≤ Γ.len := hm U fun x hx => by
    rw [hU] at hx
    exact hx.elim (hΓ x) (hD x)
  have h4 : Γ.carrier ⊂ U.carrier := by
    rw [hU]
    exact ⟨Set.subset_union_left, fun h => h2 (Set.subset_union_right.trans h)⟩
  have h5 := Set.ncard_lt_ncard h4 (Set.finite_range U.term)
  rw [ncard_carrier, ncard_carrier] at h5
  omega

theorem exists_unlinked (n : ℕ) : ∀ s : Multiset (IrrGL k), Multiset.card s = n → (∀ y ∈ s, y.IsCusp) →
    ∃ m : Multiset (Segment k), (∀ D ∈ m, ∀ D' ∈ m, ¬ D.Linked D') ∧ m.bind Segment.ms = s := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs
    rcases Multiset.empty_or_exists_mem s with rfl | ⟨y, hy⟩
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨Γ, hΓ, hm⟩ := exists_longest hy (hs y hy)
    have hle := ms_le hΓ
    have hsub : ∀ x ∈ s - Γ.ms, x ∈ s := fun x hx => Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    have hcard : Multiset.card (s - Γ.ms) < n := by
      have h1 := Multiset.card_sub hle
      have h2 := Multiset.card_le_card hle
      have h3 := Γ.len_pos
      rw [Segment.card_ms] at h1 h2
      omega
    obtain ⟨m, hu, hb⟩ := ih _ hcard _ rfl fun x hx => hs x (hsub x hx)
    have hin : ∀ D ∈ m, ∀ x ∈ D.carrier, x ∈ s := fun D hD x hx =>
      hsub x (hb ▸ Multiset.mem_bind.2 ⟨D, hD, Segment.mem_ms.2 hx⟩)
    have hΓD : ∀ D ∈ m, ¬ Γ.Linked D := fun D hD => not_linked_of_longest hΓ hm (hin D hD)
    refine ⟨Γ ::ₘ m, fun D hD D' hD' => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hD with e | e₁ <;> rcases Multiset.mem_cons.1 hD' with e' | e₂
      · rw [e, e']
        exact Segment.not_linked_self _
      · rw [e]
        exact hΓD _ e₂
      · rw [e']
        exact fun h => hΓD _ e₁ h.symm
      · exact hu _ e₁ _ e₂
    · rw [Multiset.cons_bind, hb]
      exact add_tsub_cancel_of_le hle

theorem unlinkedLayers (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UnlinkedLayers k := by
  intro s hs
  obtain ⟨m, hu, hb⟩ := exists_unlinked _ s rfl hs
  have hmem : ∀ i : Fin m.toList.length, m.toList.get i ∈ m := fun i =>
    Multiset.mem_toList.1 (List.get_mem _ _)
  refine ⟨m.toList.length, m.toList.get, fun i j _ => hu _ (hmem i) _ (hmem j), ?_⟩
  have h1 : (Finset.univ.val.map m.toList.get : Multiset (Segment k)) = m := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  conv_rhs => rw [← hb, ← h1]
  simp [Multiset.bind, Multiset.map_map, Function.comp_def]

end GlobalTheory.CompanionTheory.SegLayers

end
end


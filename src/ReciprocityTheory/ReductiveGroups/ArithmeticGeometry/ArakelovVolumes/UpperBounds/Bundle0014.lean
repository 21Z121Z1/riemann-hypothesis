import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsm
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def onDom {r : ℕ} (X : Data E r) (f : Frame X.Ψ r → ℂ) : Frame X.Ψ r → ℂ :=
  fun x => if x ∈ X.dom then f x else 0

def spanDom {r : ℕ} (X : Data E r) (S : Set (Frame X.Ψ r → ℂ)) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  Submodule.span ℂ (onDom X '' S)

def ZcM {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  spanDom X {g | ∃ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∃ θ ∈ X.SS (Xa.Fp + nd X • Xa.L),
    g = fun x => monoM X Fl.s α x * θ x}

def CountRhoPMStatement : Prop :=
  CuspSectionsUpperCount (E := E) → CuspSectionsLowerCount (E := E) →
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    ((Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) : ℝ) -
        Module.finrank ℂ (spanDom X (X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1))) ≤
      (nd X : ℝ) * (nd X + 6) * Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) / Xa.T

def CountRhoMStatement : Prop :=
  CuspSectionsUpperCount (E := E) → CuspLeadingIndependent (E := E) →
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    (Module.finrank ℂ (ZcM X Xa Fl) : ℝ) ≤
      22 * (nd X : ℝ) ^ 2 * Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) / Xa.T

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountJet
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def JetInjAt {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Prop :=
  ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L), VanS X Fl.xs Fl.s (Xa.T + nd X + 7) f → ∀ x ∈ X.dom, f x = 0

def CuspFormsJetInjectiveCount : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), JetInjAt X Xa Fl →
    ∀ (rr : ℕ) (f : Fin rr → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin rr → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      rr ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X)

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_zero' (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by
  ext a b
  by_cases h : b < a
  · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
    simp [mat, nmat, h, hab, Matrix.one_apply]
    rfl
  · by_cases hab : a = b
    · subst hab; simp [mat, nmat]
    · simp [mat, nmat, h, hab, Matrix.one_apply]

theorem cpt_zero' (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show mat x0 τ * mat (nmat X (0 : V (nd X))) τ = x0 τ
  rw [nmat_zero', mul_one]
  rfl

theorem nmat_zero_mem : nmat X (0 : V (nd X)) ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · rw [nmat_zero']; simp
  · simp [nmat, hca]
    rfl

theorem lact_one' (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp only [lact, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]
  rfl

theorem s_xs_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 := by
  have he : Fl.xs j = lact (1 : GL (Fin r) E) (rmul (Fl.xs j) (nmat X 0)) := by
    rw [lact_one']
    exact (cpt_zero' X (Fl.xs j)).symm
  exact (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).mpr ⟨j, 1, X.Γ.one_mem, nmat X 0, nmat_zero_mem X, he⟩ k

theorem anal_loc {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : AnalyticAt ℂ (fun z => P (cpt X x z)) 0 := by
  have hc := OntoB.cd_cpt X x
  have hU : IsOpen {z : V (nd X) | cpt X x z ∈ X.dom} :=
    (FourierCoefficientDomain.isOpen_dom X).preimage hc.continuous
  refine DivLA.analyticAt_of_diffOn hU ?_ (by simpa [cpt_zero'] using hx)
  exact hP.comp (hc.differentiable (by simp)).differentiableOn (fun z hz => hz)

theorem leadM_succ {n δ : ℕ} (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T d : ℕ) (cc cc' cnew : (Fin n → ℕ) → Fin δ → ℂ)
    (h1 : ∀ α ∈ Finset.Nat.antidiagonalTuple n d, cc' α = cnew α)
    (h2 : ∀ α, α ∉ Finset.Nat.antidiagonalTuple n d → cc' α = cc α) (y : Frame X.Ψ r) :
    leadM X s w0 t T (d + 1) cc' y =
      leadM X s w0 t T d cc y + ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, cnew α k * monoM X s α y * w0 y ^ (T - d) * t k y := by
  have hU : ReciprocityTheory.ChartRestriction.G.AR.multiLt n (d + 1) =
      ReciprocityTheory.ChartRestriction.G.AR.multiLt n d ∪ Finset.Nat.antidiagonalTuple n d := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.multiLt
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  have hD : Disjoint (ReciprocityTheory.ChartRestriction.G.AR.multiLt n d) (Finset.Nat.antidiagonalTuple n d) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    simp only [ReciprocityTheory.ChartRestriction.G.AR.multiLt, Finset.mem_biUnion, Finset.mem_range,
      Finset.Nat.mem_antidiagonalTuple] at h1 h2
    obtain ⟨e, he, he'⟩ := h1
    omega
  unfold leadM
  rw [hU, Finset.sum_union hD]
  congr 1
  · apply Finset.sum_congr rfl
    intro α hα
    rw [h2 α (Finset.disjoint_left.mp hD hα)]
  · apply Finset.sum_congr rfl
    intro α hα
    rw [h1 α hα, Finset.Nat.mem_antidiagonalTuple.mp hα]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem comp_O (L : V n ≃L[ℂ] V n) (k : Fin n) :
    (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := by
  have h1 : (fun z : V n => L z) =O[𝓝 0] fun z => z := (L : V n →L[ℂ] V n).isBigO_id _
  have h2 : (fun z : V n => (L z) k) =O[𝓝 0] fun z => L z := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => ?_)
    rw [one_mul]
    first
      | exact norm_le_pi_norm (L z) k
      | exact PiLp.norm_apply_le (L z) k
      | simpa using norm_le_pi_norm (L z) k
  exact (h2.trans h1).trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem sub_val_O {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g 0 - g z) =O[𝓝 0] fun z => ‖z‖ ^ 1 := by
  have h := hg.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [sub_zero] at h
  have h2 := h.neg_left
  simp only [neg_sub] at h2
  simp only [pow_one]
  exact h2.trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem local_step {δ T d : ℕ} (hd : d ≤ T) (W : V n → ℂ) (S : Fin n → V n → ℂ)
    (Tt : Fin δ → V n → ℂ) (L : V n ≃L[ℂ] V n)
    (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0) (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hT : ∀ k, AnalyticAt ℂ (Tt k) 0)
    (hL : ∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z)
    (G : V n → ℂ) (hG : AnalyticAt ℂ G 0) (hGO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ c : (Fin n → ℕ) → Fin δ → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ k, c α k * Tt k 0 * W 0 ^ T = a α) →
      (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
  obtain ⟨q, hq⟩ := taylor_step hG hGO
  obtain ⟨a, ha⟩ := multilinear_expand q L
  refine ⟨a, fun c hc => ?_⟩
  have hWev : ∀ᶠ z in 𝓝 (0 : V n), W z ≠ 0 := hW.continuousAt.eventually_ne hW0
  have hφan : ∀ i, AnalyticAt ℂ (fun y => S i y / W y) 0 := fun i => (hS i).div hW hW0
  have hφℓ : ∀ i, (fun z => S i z / W z - (L z) i) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
    intro i
    exact (taylor2 (hφan i)).congr' (Filter.Eventually.of_forall fun z => by
      simp only [hS0 i, zero_div, sub_zero, ← hL i z]) Filter.EventuallyEq.rfl
  have hℓO : ∀ i, (fun z => (L z) i) =O[𝓝 0] fun z => ‖z‖ := fun i => comp_O L i
  have hφO : ∀ i, (fun z => S i z / W z) =O[𝓝 0] fun z => ‖z‖ := by
    intro i
    have h2 : (fun z => S i z / W z - (L z) i) =O[𝓝 0] fun z => ‖z‖ :=
      ((hφℓ i).trans (isBigO_norm_pow_of_le (F := V n) (by norm_num : 1 ≤ 2))).congr'
        Filter.EventuallyEq.rfl (Filter.Eventually.of_forall fun z => pow_one _)
    exact (h2.add (hℓO i)).congr' (Filter.Eventually.of_forall fun z => sub_add_cancel _ _)
      Filter.EventuallyEq.rfl
  have hprodO : ∀ u : Fin n → V n → ℂ, (∀ i, u i =O[𝓝 0] fun z => ‖z‖) →
      ∀ (e : Fin n → ℕ) (s : Finset (Fin n)),
        (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
    intro u hu e s
    induction s using Finset.induction_on with
    | empty =>
      exact (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 (0 : V n))).congr'
        (Filter.Eventually.of_forall fun z => by simp) (Filter.Eventually.of_forall fun z => by simp)
    | insert a s ha ih =>
      refine (((hu a).pow (e a)).mul ih).congr' (Filter.Eventually.of_forall fun z => ?_)
        (Filter.Eventually.of_forall fun z => ?_)
      · simp only [Finset.prod_insert ha]
      · simp only [Finset.sum_insert ha, pow_add]
  have hsplit : (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =
      fun z => (G z - q (fun _ => z)) + ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        (a α * ∏ k, (L z) k ^ α k - ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) := by
    funext z
    rw [Finset.sum_sub_distrib, ← ha z]
    ring
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple n d,
      (fun z => a α * ∏ k, (L z) k ^ α k -
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
    intro α hα
    have hsumα : ∑ i, α i = d := Finset.Nat.mem_antidiagonalTuple.mp hα
    have hsumAn : AnalyticAt ℂ (fun z => ∑ k, c α k * Tt k z) 0 := by
      have hfun : (fun z => ∑ k, c α k * Tt k z) = ∑ k, fun z => c α k * Tt k z := by
        funext z
        simp [Finset.sum_apply]
      rw [hfun]
      exact Finset.analyticAt_sum Finset.univ fun k _ => analyticAt_const.mul (hT k)
    have hH : AnalyticAt ℂ (fun z => W z ^ T * ∑ k, c α k * Tt k z) 0 := by
      exact (hW.pow T).mul hsumAn
    have hH0 : W 0 ^ T * ∑ k, c α k * Tt k 0 = a α := by
      rw [← hc α hα, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hdiffH := sub_val_O hH
    have hP := prod_pow_sub Finset.univ (fun i z => (L z) i) (fun i z => S i z / W z) α hℓO hφO
      (fun i => (hφℓ i).neg_left.congr' (Filter.Eventually.of_forall fun z => by
        first
        | ring
        | (simp only []; ring)) Filter.EventuallyEq.rfl)
    have hφα := hprodO (fun i z => S i z / W z) hφO α Finset.univ
    have hmain : (fun z => a α * (∏ i, (L z) i ^ α i - ∏ i, (S i z / W z) ^ α i) +
        (∏ i, (S i z / W z) ^ α i) *
          (W 0 ^ T * ∑ k, c α k * Tt k 0 - W z ^ T * ∑ k, c α k * Tt k z)) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
      refine IsBigO.add ?_ ?_
      · exact (hP.const_mul_left (a α)).congr' (Filter.Eventually.of_forall fun z => rfl)
          (Filter.Eventually.of_forall fun z => by simp only [hsumα])
      · exact (hφα.mul hdiffH).congr' (Filter.Eventually.of_forall fun z => rfl)
          (Filter.Eventually.of_forall fun z => by
            simp only [pow_one]
            rw [← pow_succ, hsumα])
    refine hmain.congr' (hWev.mono fun z hz => ?_) Filter.EventuallyEq.rfl
    have hSz : ∏ i, S i z ^ α i = (∏ i, (S i z / W z) ^ α i) * W z ^ d := by
      rw [← hsumα, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_pow, div_mul_cancel₀ _ hz]
    have hWT : W z ^ T = W z ^ d * W z ^ (T - d) := by
      rw [← pow_add, Nat.add_sub_cancel' hd]
    have hsumk : ∑ k, c α k * ((∏ i, (S i z / W z) ^ α i) * W z ^ d) * W z ^ (T - d) * Tt k z =
        (∏ i, (S i z / W z) ^ α i) * (W z ^ T * ∑ k, c α k * Tt k z) := by
      rw [hWT, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    beta_reduce
    rw [hH0, hSz, hsumk]
    ring
  rw [hsplit]
  exact hq.add ((IsBigO.sum hsum).congr'
    (Filter.Eventually.of_forall fun z => by simp only [Finset.sum_apply]) Filter.EventuallyEq.rfl)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
open scoped ContDiff ENNReal

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

def BasePotentialExistence {r : ℕ} (X : FD.Data E r) (de : Wt X.Ψ r) (rr a1 : ℝ) : Prop :=
  ∃ ps0 : Frame X.Ψ r → ℝ, IsInvFn X ps0 ∧
    (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ) ∧
    cfwM X ps0 a1

def InterpolationModelInequalities {r : ℕ} (X : FD.Data E r) {N : ℕ} (L eW : Wt X.Ψ r) (w : Fin N → Frame X.Ψ r → ℂ)
    (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ) : Prop :=
  (∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2) ∧
  ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm eW et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))

def InstArchStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (het : d.et c ∈ R.Rg) (hta1 : d.ta1 c ∈ R.Rg)
    (hta2 : d.ta2 c ∈ R.Rg) (k0 : Fin d.np) (hthp : d.thp k0 c ∈ R.Rg)
    (ph : Frame X.Ψ r → ℝ) (c1 a1 rr : ℝ)
    (hF : d.wF ∈ R.WE) (hde : (2 : ℕ) • d.wde ∈ R.WE),
    d.AxW 𝒜 → Even d.g0 →
    2 ≤ nd X → 11 * nd X ^ 2 ≤ d.T → 1 ≤ d.i → 1 ≤ d.g0 → 0 < d.cc → (d.T : ℝ) * d.cc * d.g0 ≤ 1 →
    0 < c1 → 0 < a1 → 0 ≤ rr → rr * (1 + c1 / a1) ≤ 2 * d.T →
    (∀ j, R.rd ⟨d.w j c, R.w_mem j⟩ ∈ X.SSgt (R.wt ⟨d.wL, R.wL_mem⟩) 0) →
    (∀ x ∈ X.dom, ∃ j, R.rd ⟨d.w j c, R.w_mem j⟩ x ≠ 0) →
    X.IsSec ((d.i * (d.g0 / 2)) • R.wt ⟨(2 : ℕ) • d.wde, hde⟩) (R.rd ⟨d.et c, het⟩) →
    (∃ x ∈ X.dom, R.rd ⟨d.et c, het⟩ x ≠ 0) →
    R.rd ⟨d.ta1 c, hta1⟩ ∈ X.SSgt ((2 : ℕ) • R.wt ⟨d.wL, R.wL_mem⟩ - R.wt ⟨(2 : ℕ) • d.wde, hde⟩) 0 →
    (∃ x ∈ X.dom, R.rd ⟨d.ta1 c, hta1⟩ x ≠ 0) →
    R.rd ⟨d.ta2 c, hta2⟩ ∈ X.SSgt ((nd X + 4 : ℕ) • R.wt ⟨d.wL, R.wL_mem⟩ - R.wt ⟨d.wF, hF⟩) 0 →
    (∃ x ∈ X.dom, R.rd ⟨d.ta2 c, hta2⟩ x ≠ 0) →
    R.rd ⟨d.thp k0 c, hthp⟩ ∈ X.SSgt (R.wt ⟨d.wF, hF⟩) 0 →
    (∃ x ∈ X.dom, R.rd ⟨d.thp k0 c, hthp⟩ x ≠ 0) →
    IsInvFn X ph → (∀ x ∈ X.dom, 0 ≤ ph x) →
    (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x) →
    (∀ x ∈ X.dom, (d.T : ℝ) * d.cc * ph x ≤ c1 / X.la1 x ^ 2) →
    InterpolationModelInequalities X (R.wt ⟨d.wL, R.wL_mem⟩) ((d.i * (d.g0 / 2)) • R.wt ⟨(2 : ℕ) • d.wde, hde⟩) (fun j x => R.rd ⟨d.w j c, R.w_mem j⟩ x)
      (R.rd ⟨d.et c, het⟩) d.cc d.i ph →
    BasePotentialExistence X (R.wt ⟨(2 : ℕ) • d.wde, hde⟩) rr a1 →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (R.wt ⟨d.wL, R.wL_mem⟩)) x0 z ξ) →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X ((2 : ℕ) • R.wt ⟨d.wL, R.wL_mem⟩ - R.wt ⟨(2 : ℕ) • d.wde, hde⟩)) x0 z ξ) →
    (∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * d.T →
      ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviM X (phla X (R.wt ⟨d.wL, R.wL_mem⟩)) x0 z ξ ≤
          leviM X (phla X (R.wt ⟨d.wF, hF⟩ - kapW X - nd X • R.wt ⟨d.wL, R.wL_mem⟩)) x0 z ξ -
            t * (rr / 2) * leviM X (phla X (R.wt ⟨(2 : ℕ) • d.wde, hde⟩)) x0 z ξ) →
    ∃ (Xa : ArchInM X) (e : Fin Xa.N ≃ Fin (d.N + 1)),
      Xa.L = R.wt ⟨d.wL, R.wL_mem⟩ ∧ Xa.de = R.wt ⟨(2 : ℕ) • d.wde, hde⟩ ∧ Xa.Fp = R.wt ⟨d.wF, hF⟩ ∧ Xa.T = d.T ∧
      Xa.i = d.i ∧ Xa.g0 = d.g0 ∧ Xa.c = d.cc ∧ Xa.c1 = c1 ∧ Xa.a1 = a1 ∧ Xa.rr = rr ∧ Xa.ph = ph ∧
      (∀ j, Xa.w j = R.rd ⟨d.w (e j) c, R.w_mem _⟩) ∧
      Xa.et = R.rd ⟨d.et c, het⟩ ∧ Xa.th1 = R.rd ⟨d.ta1 c, hta1⟩ ∧
      Xa.th2 = R.rd ⟨d.ta2 c, hta2⟩ ∧ Xa.thp = R.rd ⟨d.thp k0 c, hthp⟩

def IsDominantR {r : ℕ} (X : FD.Data E r) (v : X.Ψ → Fin r → ℝ) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → v τ i ≤ v τ j)

def CurvNumStatement : Prop :=
  ∀ (r : ℕ) (X : FD.Data E r) (L de Fp : Wt X.Ψ r) (T rr η : ℝ), 0 < η → 0 < rr → 0 ≤ T →
    IsStrictDom X L → IsStrictDom X (2 • L - de) →
    (∀ t ∈ ({0, 2 * T / rr} : Set ℝ), IsDominantR X fun τ a =>
      ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X L) x0 z ξ) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (2 • L - de)) x0 z ξ) ∧
    ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T → ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ

def de2W {r : ℕ} (X : FD.Data E r) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1

def TorusHyp {r : ℕ} (X : FD.Data E r) : Prop :=
  (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
    Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - FD.cc (w0 : E)) • v)) -
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) ∧
  (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧
  (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧
  16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧
  ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (X.p0 ≤ m ∨ r - X.p0 ≤ m)

def BasePotentialExistenceInstance : Prop :=
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    BasePotentialExistence X.toData (de2W X.toData) (r : ℝ)
      (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)))

def TTset (T : ReciprocityTheory.ChartRestriction.G.I2.PT E) : Set (Fin T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) :=
  {a | (∀ j, a j ∈ ZSpan.fundamentalDomain T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ T.L) ∧
    ∀ x ∈ T.L, ∃ c : Fin T.r → 𝓞 E, ∃ y ∈ T.L,
      x = ∑ j, ReciprocityTheory.ChartRestriction.G.I2.act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}

def psiT {r : ℕ} {X : FD.Data E r} {x : Frame X.Ψ r} (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt X x) : ℝ :=
  Real.log (∑ᶠ (a : Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) (_ : a ∈ TTset A.T),
    ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)

def psi0 {r : ℕ} (X : FD.Data E r) (x : Frame X.Ψ r) : ℝ :=
  open Classical in if h : Nonempty (ReciprocityTheory.ChartRestriction.G.I2.TorusAt X x) then psiT (Classical.choice h) else 0

def BasePotentialPositivity : Prop :=
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    ∀ x ∈ X.toData.dom, ∀ A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt X.toData x,
      0 < ∑ᶠ (a : Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) (_ : a ∈ TTset A.T),
        ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s

def BasePotentialInvariance : Prop :=
  BasePotentialPositivity (E := E) →
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    IsInvFn X.toData (psi0 X.toData) ∧
    ∀ x0 ∈ X.toData.dom, ContDiffOn ℝ ∞ (fun z => psi0 X.toData (cpt X.toData x0 z))
      {z | cpt X.toData x0 z ∈ X.toData.dom}

def BasePotentialSmoothness : Prop :=
  BasePotentialPositivity (E := E) →
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    ∀ x0 ∈ X.toData.dom, ContDiffOn ℝ ∞ (fun z => psi0 X.toData (cpt X.toData x0 z))
      {z | cpt X.toData x0 z ∈ X.toData.dom}

def BasePotentialLeviForm : Prop :=
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    ∀ x0 ∈ X.toData.dom, ∀ z, cpt X.toData x0 z ∈ X.toData.dom → ∀ ξ : Fin (nd X.toData) → ℂ,
      -((r : ℝ) / 2 * leviM X.toData (phla X.toData (de2W X.toData)) x0 z ξ) ≤
        leviM X.toData (psi0 X.toData) x0 z ξ

def BasePotentialComparison : Prop :=
  BasePotentialPositivity (E := E) →
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    cfwM X.toData (psi0 X.toData)
      (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end


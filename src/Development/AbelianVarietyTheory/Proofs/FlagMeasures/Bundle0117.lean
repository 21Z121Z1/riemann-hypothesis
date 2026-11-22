import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
section
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff

open scoped Nat Topology

noncomputable section

namespace GlobalTheory.RightDerivSmooth

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in

theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  have hp : ∀ m : ℕ, Y ^ m * H = H * Z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) (NormedSpace.exp Y * H) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mul_right H
  have h2 : HasSum (fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m)) (H * NormedSpace.exp Z) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z).mul_left H
  have e : (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) = fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m) := by
    funext m
    rw [Matrix.smul_mul, hp, Matrix.mul_smul]
  rw [e] at h1
  exact h1.unique h2

set_option backward.isDefEq.respectTransparency false in

theorem inUH_exp {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := by
  have hY : ((t : ℂ) • X)ᴴ * H + H * ((t : ℂ) • X) = 0 := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hX, smul_zero]
  generalize (t : ℂ) • X = Y at hY
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

set_option backward.isDefEq.respectTransparency false in

theorem hasDerivAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  open scoped Matrix.Norms.Operator in
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  open scoped Matrix.Norms.Operator in
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_entry X k j).const_mul _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_local {H X g : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (hg : inUH H g)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (e : ∀ h ∈ U, inUH H h → f h = F h) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hc := hasDerivAt_mul_exp g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd : HasFDerivAt F (fderiv ℝ F g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hc
  refine h1.congr_of_eventuallyEq ?_
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hc.continuousAt.eventually (hU.mem_nhds (by simpa only [h0] using hgU))
  filter_upwards [h2] with t ht
  exact e _ ht (inUH_mul hg (inUH_exp hX t))

end GlobalTheory.RightDerivSmooth

section
open GlobalTheory.RightDerivSmooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option backward.isDefEq.respectTransparency false in

theorem GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  intro n H X E _ _ f hX hf
  have hder : ∀ g, inUH H g → ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), ∃ F : Matrix (Fin n) (Fin n) ℂ → E,
      IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ (∀ h ∈ U, inUH H h → f h = F h) ∧
      ∀ h ∈ U, inUH H h → rdM X f h = fderiv ℝ F h (h * X) ∧
        HasDerivAt (fun t : ℝ => f (h * NormedSpace.exp ((t : ℂ) • X))) (rdM X f h) 0 := by
    intro g hg
    obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
    refine ⟨U, F, hU, hgU, hF, e, fun h hhU hh => ?_⟩
    have hd := hasDerivAt_local hX hh hU hhU hF e
    have hr : rdM X f h = fderiv ℝ F h (h * X) := hd.deriv
    exact ⟨hr, hr ▸ hd⟩
  refine ⟨?_, ?_, fun g hg => ?_⟩
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, e, -⟩ := hder g hg
    have hFc : ContinuousWithinAt F {g | inUH H g} g :=
      ((hF.continuousOn).continuousAt (hU.mem_nhds hgU)).continuousWithinAt
    refine hFc.congr_of_eventuallyEq ?_ (e g hgU hg)
    filter_upwards [inter_mem_nhdsWithin {g | inUH H g} (hU.mem_nhds hgU)] with h hh
    exact e h hh.2 hh.1
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    refine ⟨U, fun h => fderiv ℝ F h (h * X), hU, hgU, ?_, fun h hhU hh => (hr h hhU hh).1⟩
    have h1 : ContDiffOn ℝ ∞ (fun h => fderiv ℝ F h) U := hF.fderiv_of_isOpen hU (le_of_eq rfl)
    have h2 : ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => h * X) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
    exact h1.clm_apply h2.contDiffOn
  · obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    exact (hr g hgU hg).2

end

example : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_eq rfl

theorem GlobalTheory.rdM_smoothOnH : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 :=
  fun n H X E _ _ f hX hf => GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group n H X E f hX hf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumNormSqEqTrace
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA.FrobNorm

variable {k r : ℕ}

theorem sum_normSq_eq_trace (g : B.Mat k r) :
    (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem gN_unitary_mul {κ : B.Mat k r} (g : B.Mat k r) (hκ : κᴴ * κ = 1) : B.gN (κ * g) = B.gN g := by
  have hsq : (κ * g)ᴴ * (κ * g) = gᴴ * g := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ κ g, hκ, Matrix.one_mul]
  simp only [B.gN]
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace, hsq]

theorem gN_conjTranspose (g : B.Mat k r) : B.gN gᴴ = B.gN g := by
  simp only [B.gN, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  rw [Finset.sum_comm]

theorem gN_mul_unitary {κ : B.Mat k r} (g : B.Mat k r) (hκ : κ * κᴴ = 1) : B.gN (g * κ) = B.gN g := by
  have hκ' : κᴴᴴ * κᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hκ
  rw [← gN_conjTranspose (g * κ), Matrix.conjTranspose_mul, gN_unitary_mul gᴴ hκ', gN_conjTranspose]

open scoped Matrix.Norms.Frobenius in
theorem gN_eq_norm (g : B.Mat k r) : B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

open scoped Matrix.Norms.Frobenius in
theorem gN_mul_le (x y : B.Mat k r) : B.gN (x * y) ≤ B.gN x * B.gN y := by
  simpa only [gN_eq_norm] using Matrix.frobenius_norm_mul x y

theorem left_inv {g : B.Mat k r} (hg : g ∈ B.GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, GBasic.Hpk_sq]

theorem inv_eq {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have h := left_inv hg
  exact Matrix.inv_eq_left_inv h

theorem gN_inv {g : B.Mat k r} (hg : g ∈ B.GV k r) : B.gN g⁻¹ = B.gN g := by
  have h1 : (Hpk k r)ᴴ * Hpk k r = 1 := by rw [GBasic.Hpk_herm, GBasic.Hpk_sq]
  have h2 : Hpk k r * (Hpk k r)ᴴ = 1 := by rw [GBasic.Hpk_herm, GBasic.Hpk_sq]
  rw [inv_eq hg, gN_mul_unitary _ h2, gN_unitary_mul _ h1, gN_conjTranspose]

end GlobalTheory.ThA.FrobNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriSubOnePow
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev.LevelIdem

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

theorem unitri_sub_one_pow {k : Type} [Field k] {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h1 : ∀ a, M a a = 1) (h2 : ∀ a b, b < a → M a b = 0) : (M - 1) ^ N = 0 := by
  have ht : (M - 1).BlockTriangular id := by
    intro a b hab
    have hab' : b < a := hab
    rw [Matrix.sub_apply, h2 a b hab', Matrix.one_apply_ne hab'.ne', sub_zero]
  have h := Matrix.aeval_self_charpoly (M - 1)
  rw [Matrix.charpoly_of_isUpperTriangular _ ht] at h
  simpa [h1] using h

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem spec_of_eps (L : Lev g N) (χ : GG g N → ℂ) (hp : IsProj (eps L.Mem χ)) (a : MonoidAlgebra ℂ (GG g N))
    (ha : ∀ x, a.coeff x = eps L.Mem χ x) :
    a * a = a ∧ IsSA a ∧ ∀ q, a.coeff q ≠ 0 → ((q : Matrix (Fin N) (Fin N) (ZMod g)) - 1) ^ N = 0 := by
  have e : a = alg (eps L.Mem χ) := by
    ext x
    rw [coeff_alg, ha]
  refine ⟨by rw [e, ← alg_conv, hp.1], fun q => ?_, fun q hq => ?_⟩
  · rw [ha, ha, hp.2]
    rfl
  · rw [ha] at hq
    have hm : L.Mem q := by
      by_contra hc
      exact hq (if_neg hc)
    exact unitri_sub_one_pow _ hm.1.1 hm.1.2

theorem spec_eDat (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (b : Bool) (s k : ℕ) (h : s + k < N)
    (H : ∀ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) x,
      (eDat g N P φ ψ).coeff x = (levOfChar ψ hψ N b s k h).e x) (ψ : AddChar (ZMod g) ℂ) :
    eDat g N P φ ψ * eDat g N P φ ψ = eDat g N P φ ψ ∧ IsSA (eDat g N P φ ψ) ∧
      ∀ q, (eDat g N P φ ψ).coeff q ≠ 0 → ((q : Matrix (Fin N) (Fin N) (ZMod g)) - 1) ^ N = 0 := by
  by_cases hψ : ψ = 1
  swap
  · exact spec_of_eps _ _ (isProj_e _) _ (H ψ hψ)
  subst hψ
  have h0 : (ZMod.stdAddChar (N := g)) ≠ 1 := (levStandard g N b s k h).hψ
  set L := levOfChar ZMod.stdAddChar h0 N b s k h with hL
  haveI : Nonempty {u // L.Mem u} := ⟨⟨1, mem_one L⟩⟩
  have hc : (Nat.card {u // L.Mem u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (fun u : GG g N => P u.val) = L.Mem := by
    funext x
    have hx := H _ h0 x
    rw [coeff_eDat, Lev.e] at hx
    unfold eps at hx
    refine propext ⟨fun h1 => ?_, fun h1 => ?_⟩
    · by_contra h2
      haveI : Nonempty {u : GG g N // P u.val} := ⟨⟨x, h1⟩⟩
      have hc' : (Nat.card {u : GG g N // P u.val} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
      rw [if_pos h1, if_neg h2] at hx
      refine div_ne_zero (inv_ne_zero fun h3 => ?_) hc' hx
      have := AddChar.norm_apply (ZMod.stdAddChar (N := g)) (φ x.val)
      beta_reduce at h3
      rw [h3] at this
      simp at this
    · by_contra h2
      rw [if_neg h2, if_pos h1] at hx
      exact div_ne_zero (inv_ne_zero (chi_ne L x)) hc hx.symm
  refine spec_of_eps L (fun _ => 1) (GlobalTheory.BadShare.EpsProj.isProj_eps (mem_one L) (fun _ _ => mem_mul L) rfl (fun _ _ _ _ => by simp)) _
    fun x => ?_
  rw [coeff_eDat, hP]
  rfl

theorem eUk_eJk_spec : ∀ (D : D7) (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))), a = eUk D k ψ₀ ∨ a = eJk D k ψ₀ → a * a = a ∧ IsSA a ∧ ∀ q, a.coeff q ≠ 0 → ((q : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) - 1) ^ D.R.r = 0 := by
  intro D k ψ a ha
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hN : D.R.r = D.R.k + 2 * (D.R.m / 2 - 1) + 1 := by
    have := dimS_eq D.R
    unfold Ranks.rS at this
    omega
  have h : (D.R.m / 2 - 1) + D.R.k < D.R.r := by omega
  rcases ha with rfl | rfl
  · exact spec_eDat _ _ false _ _ h (fun ψ hψ x => coeff_eU ψ hψ _ _ h x) ψ
  · exact spec_eDat _ _ true _ _ h (fun ψ hψ x => coeff_eJ ψ hψ _ _ hN h x) ψ

end GlobalTheory.RowLev.LevelIdem
end


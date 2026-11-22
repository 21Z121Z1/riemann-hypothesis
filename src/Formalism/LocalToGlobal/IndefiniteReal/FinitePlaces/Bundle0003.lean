import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.PHeisThA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem hO_add_left (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO
  rw [hO_add_left, mul_add, map_add]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add]

theorem symplO_zero_left (y : WO S T) : symplO S T 0 y = 0 := by
  have h := symplO_add_left S T 0 0 y
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  have h := symplO_add_right S T x 0 0
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_add_left S T x (-x) y
  have h0 : x + -x = 0 := by simp
  rw [h0, symplO_zero_left] at h
  linear_combination -1 * h

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  have h0 : y + -y = 0 := by simp
  rw [h0, symplO_zero_right] at h
  linear_combination -1 * h

abbrev MO : Type := Matrix (Fin T.rank) (Fin S.rank) (AE D)

def hOM (x y : MO S T) : Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
  HMul.hMul (HMul.hMul (HMul.hMul (Brg.GI S) (y.map (cA D))ᵀ) (Brg.GG T)) x

theorem hO_eq_trace (x y : MO S T) : hO S T x y = (hOM S T x y).trace := by
  unfold hO hOM
  simp only [Brg.GI, Brg.GG, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext d; rw [Finset.sum_comm]

theorem cA_trace {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) : cA D M.trace = ((M.map (cA D))ᵀ).trace := by
  rw [Matrix.trace_transpose]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem hO_swap (x y : MO S T) : hO S T y x = cA D (hO S T x y) := by
  have e0 : (y.map (cA D)).map (cA D) = y := by ext i j; simp [cA_cA]
  have e2 : ((hOM S T x y).map (cA D))ᵀ =
      HMul.hMul (HMul.hMul (HMul.hMul (x.map (cA D))ᵀ (Brg.GG T)) y) (Brg.GI S) := by
    unfold hOM
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Brg.GI_herm, Brg.GG_herm, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, cA_trace, e2, Matrix.trace_mul_comm]
  unfold hOM
  simp only [Matrix.mul_assoc]

theorem symplO_swap (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [hO_swap S T x y]
  have e : incA D D.host.xi0 * cA D (hO S T x y) = cA D (cA D (incA D D.host.xi0) * hO S T x y) := by
    rw [map_mul, cA_cA]
  rw [e, Brg.trace_cA, Brg.cA_inc, Brg.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_add_left (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH
  rw [symplO_add_left, mul_add]

theorem symplOH_add_right (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH
  rw [symplO_add_right, mul_add]

theorem symplOH_swap (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_swap, mul_neg]

theorem symplOH_two (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add]
  norm_num

theorem ratW_add (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S (a + b) = ratW T S a + ratW T S b := by
  exact Matrix.map_add _ (map_add (incA D)) a b

theorem ratW_neg (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ratW T S (-a) = -ratW T S a := by
  exact Matrix.map_neg _ (map_neg (incA D)) a

theorem ratW_zero : ratW T S (0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E) = 0 := by
  exact Matrix.map_zero _ (map_zero (incA D))

theorem mem_ratL_iff (x : WO S T) : x ∈ ratL T S ↔ ∃ a, ratW T S a = x := by
  unfold ratL
  simp only [AddMonoidHom.mem_range]
  exact Iff.rfl

theorem incA_eq_tmul (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem trace_incA (e : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  rw [incA_eq_tmul]
  exact Formalism.IndefR.PHeisTh.trace_tmul _

theorem hO_rat (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ e : D.host.E, hO S T (ratW T S a) (ratW T S b) = incA D e := by
  refine ⟨∑ i, ∑ j, ∑ k, ∑ l, (HSpace.gram S)⁻¹ i j * D.sp.cm.sig (b k j) * HSpace.gram T k l * a l i, ?_⟩
  unfold hO ratW
  simp only [Matrix.map_apply, Formalism.IndefR.PHeisTh.cA_incA, map_sum, map_mul]

theorem symplO_rat (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ q : D.host.F, symplO S T (ratW T S a) (ratW T S b) = algebraMap D.host.F (AF D.host.F) q := by
  obtain ⟨e, he⟩ := hO_rat S T a b
  refine ⟨Algebra.trace D.host.F D.host.E (D.host.xi0 * e), ?_⟩
  unfold symplO
  rw [he, ← map_mul, trace_incA]

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CircleEqOneOfRePos
section
noncomputable section

open Filter Topology

namespace Formalism.IndefR.Fin.U1

theorem circle_eq_one_of_re_pos (z : Circle) (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  set θ := Complex.arg (z : ℂ) with hθ
  have hz : (z : ℂ) = Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
    exact this.symm
  have hre : ∀ n : ℕ, ((z ^ n : Circle) : ℂ).re = Real.cos (n * θ) := by
    intro n
    rw [Circle.coe_pow, hz, ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  by_cases h0 : θ = 0
  · apply Circle.ext
    rw [hz, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Circle.coe_one]
  · exfalso
    set t := |θ| with ht
    have ht0 : 0 < t := abs_pos.mpr h0
    have htpi : t ≤ Real.pi := Complex.abs_arg_le_pi _
    set n := ⌈Real.pi / (2 * t)⌉₊ with hn
    have h1 : Real.pi / 2 ≤ n * t := by
      have := Nat.le_ceil (Real.pi / (2 * t))
      rw [← hn] at this
      have e : Real.pi / 2 = Real.pi / (2 * t) * t := by field_simp
      rw [e]; exact mul_le_mul_of_nonneg_right this ht0.le
    have h2 : (n : ℝ) * t < Real.pi / 2 + t := by
      have := Nat.ceil_lt_add_one (div_nonneg Real.pi_pos.le (by positivity : (0 : ℝ) ≤ 2 * t))
      rw [← hn] at this
      have e : Real.pi / 2 + t = (Real.pi / (2 * t) + 1) * t := by field_simp
      rw [e]; exact mul_lt_mul_of_pos_right this ht0
    have hc : Real.cos (n * θ) = Real.cos (n * t) := by
      rw [← Real.cos_abs (n * θ), abs_mul, Nat.abs_cast]
    have := h n
    rw [hre, hc] at this
    have := Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
    linarith

section Defs

variable {K : Type*} [Field K]

def nrm (Δ p r : K) : K := p * p - Δ * (r * r)

def cAq (Δ a b p r : K) : K := (a * (p * p + Δ * (r * r)) - Δ * b * (2 * p * r)) / nrm Δ p r

def cBq (Δ a b p r : K) : K := (b * (p * p + Δ * (r * r)) - a * (2 * p * r)) / nrm Δ p r

end Defs

section Loc

variable {K : Type*} [NormedField K]

theorem loc_of (Δ a b p0 r0 : K) (hN : nrm Δ p0 r0 ≠ 0) (hA : cAq Δ a b p0 r0 = 1) (hB : cBq Δ a b p0 r0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ p r : K, ‖p - p0‖ < η → ‖r - r0‖ < η →
      nrm Δ p r ≠ 0 ∧ ‖cAq Δ a b p r - 1‖ < ε ∧ ‖cBq Δ a b p r‖ < ε := by
  have hcN : Continuous fun y : K × K => nrm Δ y.1 y.2 := by unfold nrm; fun_prop
  have hn1 : Continuous fun y : K × K => a * (y.1 * y.1 + Δ * (y.2 * y.2)) - Δ * b * (2 * y.1 * y.2) := by
    fun_prop
  have hn2 : Continuous fun y : K × K => b * (y.1 * y.1 + Δ * (y.2 * y.2)) - a * (2 * y.1 * y.2) := by
    fun_prop
  have hA' : ContinuousAt (fun y : K × K => cAq Δ a b y.1 y.2) (p0, r0) := by
    unfold cAq; exact hn1.continuousAt.div hcN.continuousAt hN
  have hB' : ContinuousAt (fun y : K × K => cBq Δ a b y.1 y.2) (p0, r0) := by
    unfold cBq; exact hn2.continuousAt.div hcN.continuousAt hN
  have e1 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), nrm Δ y.1 y.2 ≠ 0 := hcN.continuousAt.eventually_ne hN
  have e2 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), ‖cAq Δ a b y.1 y.2 - 1‖ < ε := by
    have t := hA'.tendsto
    simp only [hA] at t
    exact (Metric.tendsto_nhds.1 t ε hε).mono fun y hy => by rwa [dist_eq_norm] at hy
  have e3 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), ‖cBq Δ a b y.1 y.2‖ < ε := by
    have t := hB'.tendsto
    simp only [hB] at t
    exact (Metric.tendsto_nhds.1 t ε hε).mono fun y hy => by rwa [dist_zero_right] at hy
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and e3))
  refine ⟨η, hη, fun p r hp hr => ?_⟩
  have hd : dist ((p, r) : K × K) (p0, r0) < η := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hp, hr⟩
  obtain ⟨h1, h2, h3⟩ := hball hd
  exact ⟨h1, h2, h3⟩

theorem loc_near (Δ a b : K) (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (hab : a * a - Δ * (b * b) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p0 r0 : K, ∃ η > 0, ∀ p r : K, ‖p - p0‖ < η → ‖r - r0‖ < η →
      nrm Δ p r ≠ 0 ∧ ‖cAq Δ a b p r - 1‖ < ε ∧ ‖cBq Δ a b p r‖ < ε := by
  by_cases ha : 1 + a = 0
  · have hb : b = 0 := by
      have hbb : Δ * (b * b) = 0 := by
        have : a = -1 := by linear_combination ha
        subst this; linear_combination -hab
      exact mul_self_eq_zero.mp ((mul_eq_zero.mp hbb).resolve_left hΔ)
    have hN : nrm Δ 0 1 = -Δ := by unfold nrm; ring
    have hN0 : nrm Δ 0 1 ≠ 0 := by rw [hN]; exact neg_ne_zero.mpr hΔ
    refine ⟨0, 1, loc_of Δ a b 0 1 hN0 ?_ ?_ ε hε⟩
    · unfold cAq; rw [div_eq_one_iff_eq hN0, hN, hb]; linear_combination Δ * ha
    · unfold cBq; rw [hb]; simp
  · have hN : nrm Δ (1 + a) b = 2 * (1 + a) := by unfold nrm; linear_combination hab
    have hN0 : nrm Δ (1 + a) b ≠ 0 := by rw [hN]; exact mul_ne_zero h2 ha
    refine ⟨1 + a, b, loc_of Δ a b (1 + a) b hN0 ?_ ?_ ε hε⟩
    · unfold cAq; rw [div_eq_one_iff_eq hN0, hN]; linear_combination (a + 2) * hab
    · unfold cBq; rw [div_eq_zero_iff]; left; linear_combination (-b) * hab

end Loc

end Formalism.IndefR.Fin.U1

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.DetLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction Formalism.IndefR.Fin.U1
  MeasureTheory IsDedekindDomain NumberField Topology

namespace Formalism.IndefR.Fin.DL

set_option synthInstance.maxHeartbeats 80000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cUD (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (cA D).toMonoidHom

@[simp] theorem cUD_val (x : (AE D)ˣ) : ((cUD D x : (AE D)ˣ) : AE D) = cA D (x : AE D) := rfl

def hq (D : D7) : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / cUD D

theorem hq_apply (x : (AE D)ˣ) : hq D x = x / cUD D x := rfl

section Inv

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0)

include hδ hδ0 in
theorem cA_cA (y : AE D) : cA D (cA D y) = y := by
  rw [← pt_co δ hδ hδ0 y, cA_pt δ hδ, cA_pt δ hδ, neg_neg]

end Inv

theorem cA_cA' (y : AE D) : cA D (cA D y) = y := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_delta_D D
  exact cA_cA δ hδ hδ0 y

theorem cUD_cUD' (x : (AE D)ˣ) : cUD D (cUD D x) = x := Units.ext (cA_cA' _)

theorem hq_mem (x : (AE D)ˣ) : hq D x ∈ FirstPropositionFrame D := by
  have h : hq D x * cUD D (hq D x) = 1 := by
    rw [hq_apply, map_div, cUD_cUD', div_mul_div_cancel, div_self']
  show ((hq D x : (AE D)ˣ) : AE D) * cA D ((hq D x : (AE D)ˣ) : AE D) = 1
  have := congrArg (fun z : (AE D)ˣ => (z : AE D)) h
  simpa using this

def phiU (D : D7) : (AE D)ˣ →* FirstPropositionFrame D := (hq D).codRestrict (FirstPropositionFrame D) hq_mem

section Coord

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

end Coord

theorem detU_mem (V : HSp D) (g : GA D V) : Matrix.GeneralLinearGroup.det (matHom V g) ∈ FirstPropositionFrame D := by
  show ((Matrix.GeneralLinearGroup.det (matHom V g) : (AE D)ˣ) : AE D) *
    cA D ((Matrix.GeneralLinearGroup.det (matHom V g) : (AE D)ˣ) : AE D) = 1
  rw [Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact det_conj_mul V g

def detU (V : HSp D) : GA D V →* FirstPropositionFrame D :=
  (Matrix.GeneralLinearGroup.det.comp (matHom V)).codRestrict (FirstPropositionFrame D) (detU_mem V)

end Formalism.IndefR.Fin.DL

namespace Formalism.IndefR.Fin

open Formalism.IndefR.Fin.DL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev latAll (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T ΛS ΛT fun _ => True

def PlaceLatDual (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ e' : AE D, IsSplitIdem D e' → ∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e' * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT) ∧
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT)) ∧
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT)) ∧
      (∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceModelAt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
      (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm ∧
          (∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm' →
            ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → Tm' Φ = Tm Φ) ∧
          (∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ)) ∧
          ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) →
            heisO ψ S T u f₀ = f₀ → heisO ψ S T u (Tm Φ) = Tm Φ

def SplitLin (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
    ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm →
    ∀ e₁ : AE D, IsSplitIdem D e₁ → e₁ * e = e₁ →
    ∀ (g : GA D S) (h : GA D T), SuppAt e₁ S g → SuppAt e₁ T h →
    ∀ x y : (AE D)ˣ, IsDetAt e₁ S g x → IsDetAt e₁ T h y →
      ∃ r : ℝ, 0 < r ∧
        (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
          om (g, h) (Tm Φ) = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • Tm (fun t => Φ (actO S T g⁻¹ h⁻¹ t))) ∧
        ((∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) →
          (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) → r = 1)

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

def TwoSplits (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), (2 : 𝓞 D.host.E) ∈ P.asIdeal → ¬ Lev.IsConjPl (D := D) P P

def TwoSplitIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal →
    ∃ (e : AE D) (ε : AF D.host.F), IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def LatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      IsCompact ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True :
          AddSubgroup (WO S T)) : Set (WO S T)) ∧
      IsOpen {w : WO S T | ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
          (fun _ => True), (w - u).map (finPart D) = 0} ∧
      (∀ a : AE D, finPart D a ∈ intAE D →
        ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ x : WO S T, x.map (infPart D) = 0 →
        (x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
          ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
            ψ (symplO S T x u) = 1)

open Classical in

def IdemExists (D : D7) : Prop :=
  (∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ Lev.IsConjPl (D := D) P P → ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e P ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal →
      ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e e' : AE D), Formalism.L2.NTheta.IsIdemAt e P → Formalism.L2.NTheta.IsIdemAt e' P →
    e = e') ∧
  ∀ (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 D.host.E) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)),
    Lev.IsTypePlaces (D := D) gp pb Pg → Lev.IsTwistPlaces (D := D) gp Q → ∃ e : AE D, IsIdemSum e (Pg ∪ Q)

def LiftsExistB (D : D7) : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 D.host.E),
    Lev.IsBaseFrame V β Λ N → Lev.IsTypePlaces (D := D) gp pb L.Pg → Lev.IsTwistPlaces (D := D) gp L.Q →
      Lev.LiftsExist V β L

def HeisStable (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ),
    IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w₀ f)

def DRhoStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)

def PtStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ)
      (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)

end Formalism.IndefR.Fin

end
end


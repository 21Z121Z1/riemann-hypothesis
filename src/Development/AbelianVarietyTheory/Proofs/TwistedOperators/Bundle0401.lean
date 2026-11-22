import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProdu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenMetric

variable {D : D7}

theorem finDim : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, FinDim D := by
  intro hP D c hc j _ s hs
  obtain ⟨U, hU, hUJ⟩ := hs.isOpen
  have : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) 1) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf ⟨U, hU, fun k hk hf => ⟨hUJ k hk hf, rfl⟩⟩
  exact Module.Finite.map _ _

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.ChainOnto.exists_ipD_smT D s.V s.par s.M
  set J : Set (GA D s.V) := (s.J : Set (GA D s.V))
  set χ : GA D s.V → ℂ := 1
  have hS : SchurMult c.θ s.M J χ s.ν s.fd := GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  obtain ⟨hI1, hI2⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M J χ s.ν s.fd hc.inf hs.haar hs.fund hS
    (GlobalTheory.GardingVec.sm_ne_bot D s.V s.par s.M)
  let T : s.CC c → MMap s.M := fun x => PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
  have hT : ∀ x : s.CC c, T x ∈ Mult c.θ s.M J χ := fun x => (mem_multT c.θ s.M J χ _).1 x.2
  have hTadd : ∀ x y : s.CC c, T (x + y) = T x + T y := fun x y => by
    simp only [T, Submodule.coe_add, map_add]
  have hTsmul : ∀ (a : ℂ) (x : s.CC c), T (a • x) = a • T x := fun a x => by
    simp only [T, Submodule.coe_smul, map_smul]
  have hlin : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T y + a • T y') = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => (hI1 _ (hT x) _ (hT y) _ (hT y') a).1
  have hsym : ∀ x y : s.CC c, ipM s.M s.ν s.fd (T y) (T x) = star (ipM s.M s.ν s.fd (T x) (T y)) :=
    fun x y => (hI1 _ (hT x) _ (hT y) _ (hT y) 0).2
  have hzero : ∀ x : s.CC c, ipM s.M s.ν s.fd (T x) (T 0) = 0 := fun x => by
    have h := hlin x 0 0 1
    rw [one_smul, one_mul, show T 0 + T 0 = T 0 by simp [T]] at h
    linear_combination -h
  have hlin' : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T (y + a • y')) = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => by rw [hTadd, hTsmul]; exact hlin x y y' a
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => ipM s.M s.ν s.fd (T y) (T x))
      (fun x x' y => by simpa using hlin' y x x' 1)
      (fun a x y => by
        have h := hlin' y 0 x a
        rw [zero_add, hzero, zero_add] at h
        simpa using h)
      (fun x y y' => by
        rw [hsym x (y + y'), hsym x y, hsym x y']
        have h := hlin' x y y' 1
        rw [one_mul, one_smul] at h
        rw [h, star_add])
      (fun a x y => by
        rw [hsym x (a • y), hsym x y]
        have h := hlin' x 0 y a
        rw [zero_add, hzero, zero_add] at h
        rw [h, star_mul', smul_eq_mul, starRingEnd_apply])
  have hip : ∀ x y, ip x y = ipM s.M s.ν s.fd (T y) (T x) := fun _ _ => rfl
  have hpair : ∀ x y : s.CC c, ∀ w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν ∧
      ∫ g in s.fd, PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g) ∂s.ν = ip x y * ipD w w' := by
    intro x y
    refine GlobalTheory.ChainMetric.integ_pair (μ := s.ν) (A := s.fd) (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
      (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ipD (ip x y) ?_
    intro v v'
    obtain ⟨hi, he⟩ := ipM_spec s.M s.ν s.fd (T y) (T x) (hS hc.inf hs.haar hs.fund _ (hT y) _ (hT x)) v' v
    have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
        conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) = fun g => star (T y v' g) * T x v g := by
      funext g
      rw [GlobalTheory.ChainMetric.val_tprod, GlobalTheory.ChainMetric.val_tprod, starRingEnd_apply, mul_comm]
    rw [e, hip, hpure]
    exact ⟨hi, he⟩
  refine ⟨ipD, ip, hpure, hhermD, hposD, fun x y => ?_, fun x hx => ?_, fun x y w w' => (hpair x y w w').1,
    fun x y w w' => (hpair x y w w').2⟩
  · rw [hip, hip, hsym, starRingEnd_apply]
  · rw [hip]
    refine hI2 _ (hT x) fun h0 => hx ?_
    exact Submodule.coe_eq_zero.1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

theorem finDim_and_metEx : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D :=
  fun h h' D => ⟨finDim h D, metEx h' D⟩

end GlobalTheory.EvenMetric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ChainVal

variable {D : D7}

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_same (χ : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    GlobalTheory.ChainOnto.stepPar χ χ t B = B + GlobalTheory.LFun.segFam (vf χ) t := by
  funext w; simp [GlobalTheory.ChainOnto.stepPar, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = B + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i)) c.t := by
  induction k with
  | zero => simp [chainPar]
  | succ k ih => rw [chainPar_succ, ih, stepPar_same, Finset.sum_range_succ, add_assoc]

theorem chainPar_twist (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹ =
      GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i * (c.χ k)⁻¹)) c.t := by
  rw [chainPar_closed, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam]
  congr 1
  funext w; simp [vf, mul_comm]

theorem locL_finsetSum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (d : ι → GlobalTheory.LFun.Fam K)
    (w : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    GlobalTheory.LFun.locL (∑ i ∈ s, d i) w x = ∏ i ∈ s, GlobalTheory.LFun.locL (d i) w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [GlobalTheory.LFun.locL]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, GlobalTheory.LFun.locL_add, ih]

theorem bounded_single {K : Type} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) : GlobalTheory.LFun.Bounded T (fun w => {z w}) 1 0 :=
  fun w _ => ⟨by simp, fun b hb => by rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, hz]⟩

theorem eulerProd_add_segFam {K : Type} [Field K] [NumberField K] {ι : Type} (T : Set (HeightOneSpectrum (𝓞 K)))
    (A : GlobalTheory.LFun.Fam K) (s : Finset ι) (z : ι → HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (x : ℂ)
    (hA : GlobalTheory.LFun.Converges T A x)
    (hz : ∀ i ∈ s, ∀ l < t, GlobalTheory.LFun.Converges T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :
    GlobalTheory.LFun.eulerProd T (A + ∑ i ∈ s, GlobalTheory.LFun.segFam (z i) t) x = GlobalTheory.LFun.eulerProd T A x *
      ∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l) := by
  have h1 : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ s, ∏ l ∈ Finset.range t,
      GlobalTheory.LFun.locL (fun u => {z i u}) w (x + ((t : ℂ) - 1) / 2 - l))
      (∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :=
    hasProd_prod fun i hi => hasProd_prod fun l hl => (hz i hi l (Finset.mem_range.1 hl)).hasProd
  have h2 := hA.hasProd.mul h1
  show ∏' w : {w // w ∉ T}, _ = _
  refine HasProd.tprod_eq ?_
  convert h2 using 1
  funext w
  rw [GlobalTheory.LFun.locL_add, locL_finsetSum]
  simp only [GlobalTheory.LFun.locL_segFam']

end GlobalTheory.EvenOnto.ChainVal

open GlobalTheory.EvenOnto.ChainVal in

theorem GlobalTheory.EvenOnto.chainL_and_inj : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  intro D
  refine ⟨?_, ?_⟩
  · intro c hc B hB k hk
    set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
    have hnt : c.n + 2 ≤ c.t := hc.step
    have hnt' : (c.n : ℝ) + 2 ≤ c.t := by exact_mod_cast hnt
    have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.range k → Differentiable ℂ Λ ∧
        (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
          (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ k)⁻¹) w}) z) ∧
        ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
      intro i
      by_cases hi : i ∈ Finset.range k
      · obtain ⟨Λ, h⟩ := GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers D c hc i k (Finset.mem_range.1 hi) hk
        exact ⟨Λ, fun _ => h⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose Λ hΛ using hΛ
    set A := GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ with hA
    have hAb : GlobalTheory.LFun.Bounded T A c.n (((c.n : ℝ) - 1) / 2) :=
      hB.twist fun w _ => by simp [vf, GlobalTheory.LFun.norm_val]
    let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => vf (c.χ i * (c.χ k)⁻¹)
    have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
      (bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
    let H : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
      ∏ i ∈ Finset.range k, ∏ l ∈ Finset.range c.t, Λ i (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l)
    have hEq : ∀ x : ℂ, ((c.n : ℝ) + c.t + 2) < x.re →
        H x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.χ k) (x + 1 / 2) := by
      intro x hx
      have hre : ∀ l : ℕ, l < c.t → 1 < (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l).re := by
        intro l hl
        have : (l : ℝ) + 1 ≤ c.t := by exact_mod_cast hl
        have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _
        simp
        linarith
      show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
        (GlobalTheory.LFun.val (F := D.host.F) (c.χ k))⁻¹) (x + 1 / 2)
      change _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹) (x + 1 / 2)
      rw [chainPar_twist, ← hA, eulerProd_add_segFam T A (Finset.range k) z c.t (x + 1 / 2)
        (hAb.converges (by have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _; simp; linarith))
        (fun i _ l hl => hzc i _ (hre l hl))]
      refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi =>
        Finset.prod_congr rfl fun l hl => ?_)
      exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
    have hU : IsOpen (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
    have hD : DifferentiableOn ℂ H (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := by
      refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
      · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
        simp only [GlobalTheory.Cont.mem_rightOf] at hx
        simp
        linarith
      · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
          (hΛ i hi).1.comp (by fun_prop)
    have hAn := hD.analyticOnNhd hU
    have hmem : ((c.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2) := by
      simp only [GlobalTheory.Cont.mem_rightOf]
      simp
      linarith
    refine ⟨H ((c.t : ℂ) / 2), ?_, H, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (c.n : ℝ) + c.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, rfl⟩
    refine mul_ne_zero ((hAb.converges ?_).ne_zero) ?_
    · simp
      linarith
    · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun l hl => ?_
      have hl' := Finset.mem_range.1 hl
      have e : (c.t : ℂ) / 2 + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l = ((c.t - l : ℕ) : ℂ) := by
        rw [Nat.cast_sub hl'.le]
        ring
      rw [e]
      exact (hΛ i hi).2.2 _ (by omega)
  · intro c k B B' w h
    induction k with
    | zero => simpa [chainPar] using h
    | succ k ih =>
      apply ih
      rw [chainPar_succ, chainPar_succ] at h
      simp only [GlobalTheory.ChainOnto.stepPar] at h
      have h2 := add_right_cancel h
      exact Multiset.map_injective (mul_right_injective _) h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoeffici
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.MeasPet

variable {D : D7}

open GlobalTheory.ChainOnto.HaarInf in

theorem meas_petco : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  let K : Subgroup (GA D V) := s.J
  let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
  let A : Subgroup (GA D V) := Lf.comap (GlobalTheory.AutMult.toFin V)
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg => Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hAset : (A : Set (GA D V)) = s.big := by
    ext g
    refine ⟨fun hg => ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩, ?_⟩
    rintro ⟨b, κ, hκ, rfl⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
    have e : GlobalTheory.AutMult.toFin V (κ : GA D V) = ⟨κ, hs.fin hκ⟩ := GlobalTheory.AutMult.toFin_coe (⟨κ, hs.fin hκ⟩ : GfC V)
    rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf, one_mul, e]
    exact hκ
  have hLf : IsOpen (Lf : Set (GfC V)) := by
    obtain ⟨U, hU, hUK⟩ := hs.isOpen
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
    exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hk) k.2)
  have hAopen : IsOpen (A : Set (GA D V)) := hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact hs.stab _ (hfinK g hg) v
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    constructor
    · rintro ⟨hgA, hgf⟩
      have := hfinK g hgA
      rwa [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hgf⟩ : GfC V))] at this
    · intro hg
      refine ⟨?_, hs.fin hg⟩
      refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
      rw [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hs.fin hg⟩ : GfC V))]
      exact hg
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.ChainOnto.isCompact_of_integral_open D V s.Λ hs.selfDual K hs.fin hs.stab hs.isOpen
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    rw [← SetLike.mem_coe, hAset]
    exact ⟨b, 1, one_mem _, by simp⟩
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨⟨hIopen.measurableSet, hAset ▸ hAopen.measurableSet, hAset ▸ hAint, _, hHaar, fun f F hf hF => ?_⟩, ?_⟩
  · have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
      (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
    have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
      conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
      exact hF _ _ (hfinK g hg)
    have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
      (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
    rw [← hAset]
    refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
    rw [setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]
  · intro ipD ip hM u v b κ hκ
    have hmem := (mem_multT c.θ s.M (s.J : Set (GA D V)) 1 (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ))).1 u.2
    have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (s.J : Set (GA D V)) 1 hc.inf v b
    have hUw := hU _ hmem
    have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ)) x := by
      intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
      funext g
      rw [ev, ev, hUw]
      simp only [rTr]
      rw [← mul_assoc]
      simpa using hmap.lev v κ hκ (g * (b : GA D s.V))
    have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
    rw [key, hsch, hM.pure w v]
    simp only [hw]

end GlobalTheory.EvenOnto.MeasPet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.FockOff

theorem latO_le {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {p q : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

end GlobalTheory.EvenOnto.FockOff

open GlobalTheory.EvenOnto.FockOff in

theorem GlobalTheory.EvenOnto.fock_sph_vac : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D c hc k hk s s' hs hs' p hp φ
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hv := hp.pre.vac
  have hF : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) :=
    GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ
  have hpt : ∀ φ', IsThetaFunO c.ψ s.V s'.V (p.pt φ') := fun φ' =>
    (GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ').1
  have hle : latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S) ≤ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      fun _ => True := latO_le _ _ _ _ fun _ _ => trivial
  have fix : ∀ u ∈ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S), heisO c.ψ s.V s'.V u p.f = p.f → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hθ _ _ _ _ p.f hpt u
      (GlobalTheory.VacGood.infPart_latO (hle hu)) h0 φ
  have hsph := hp.pre.sph
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) :=
    ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hsph.1 u hu),
      fun e he u hu hh => fix u hu (hsph.2 e he u hu hh)⟩
  refine ⟨hF.1, hF, hS, fun v hv => ⟨hF.1, ?_, ?_⟩⟩
  · intro u hu
    exact hS.1 u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu)
  · intro e he u hu hh
    exact hS.2 e he u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu) hh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_one_param_line_transposeGramUnitary : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau),
    ∀ Y ∈ lieAt X τ, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Z,
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.TransportedLine.exists_line_toUX_oneP | exact GlobalTheory.TransportedLine.exists_line_toUX_oneP | (intros; apply GlobalTheory.TransportedLine.exists_line_toUX_oneP <;> assumption)
end


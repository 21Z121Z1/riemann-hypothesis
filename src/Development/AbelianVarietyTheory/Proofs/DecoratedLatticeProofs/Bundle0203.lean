import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourier
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.CQLast

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem eq_zero_of_hat_eq_zero (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) {n : Type} [Fintype n] [DecidableEq n] {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (h0 : ∀ η, GlobalTheory.StepData.hat ψ ν (-1) f η = 0) (a : n → k) : f a = 0 := by
  classical
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hψ hne
  set μ : Measure (n → k) := Measure.pi fun _ => ν with hμ
  have hF : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have h1 := h0 (-y)
    simp only [GlobalTheory.StepData.hat] at h1
    rw [← h1]
    congr 1
    funext x
    rw [neg_dotProduct, neg_one_mul, neg_neg, dotProduct_comm]
  set g : (n → k) → ℂ := fun x => f (x + a) with hgdef
  have hg : g ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_add_const a), hf.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have hpsi : ∀ u v : k, (ψ (u + v) : ℂ) = ψ u * ψ v := fun u v => by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  have hpsi' : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := fun u => by
    rw [← hpsi, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  have hG : ∀ y, ∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have e : ∀ x, g x * (ψ (x ⬝ᵥ y) : ℂ) = (ψ (-(a ⬝ᵥ y)) : ℂ) * (f (x + a) * ψ ((x + a) ⬝ᵥ y)) := by
      intro x
      rw [add_dotProduct, hpsi, hgdef]
      linear_combination (f (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) * (hpsi' (a ⬝ᵥ y)).symm
    simp_rw [e]
    rw [integral_const_mul, integral_add_right_eq_self (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) a, hF, mul_zero]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μ hc hg
  simp only [hG, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (FourierPi.box n r) := by
    intro r
    refine ENNReal.toReal_pos ((FourierPi.isOpen_box r).measure_pos μ ⟨0, ?_⟩).ne'
      (FourierPi.isCompact_box r).measure_lt_top.ne
    simp [FourierPi.box, cball]
  have h2 : g 0 = 0 := by
    rcases mul_eq_zero.1 hs.symm with h | h
    · exfalso
      have := mul_pos (hpos s) (hpos (c * s⁻¹))
      exact this.ne' (by exact_mod_cast h)
    · exact h
  simpa [hgdef] using h2

def withLast {n n' : Type} (x₀ : Matrix n n' k) (y : n → k) : Matrix n (n' ⊕ Unit) k :=
  fromCols x₀ (Matrix.of fun r (_ : Unit) => y r)

theorem withLast_toCols {n n' : Type} (x : Matrix n (n' ⊕ Unit) k) :
    withLast x.toCols₁ (fun r => x r (Sum.inr ())) = x := by
  ext r (j | u)
  · rfl
  · cases u; rfl

theorem continuous_withLast {n n' : Type} (x₀ : Matrix n n' k) : Continuous (withLast x₀) := by
  refine continuous_matrix fun i j => ?_
  rcases j with a | u
  · simp only [withLast, Matrix.fromCols_apply_inl]; exact continuous_const
  · simp only [withLast, Matrix.fromCols_apply_inr, Matrix.of_apply]; exact continuous_apply i

theorem slice_mem_SB {n n' : Type} [Fintype n] [Fintype n'] {Ψ : Matrix n (n' ⊕ Unit) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) (x₀ : Matrix n n' k) :
    (fun y : n → k => Ψ (withLast x₀ y)) ∈ SB (n → k) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have hcl : Topology.IsClosedEmbedding (withLast x₀) :=
    Function.LeftInverse.isClosedEmbedding (f := fun x : Matrix n (n' ⊕ Unit) k => fun r => x r (Sum.inr ()))
      (fun y => rfl) (by fun_prop) (continuous_withLast x₀)
  exact ⟨hΨ.1.comp_continuous (continuous_withLast x₀), hΨ.2.comp_isClosedEmbedding hcl⟩

def partialHat (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × (n → k) → ℂ) where
  toFun Ψ p := GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ.1 (withLast p.1 y)) p.2
  map_add' Ψ Ψ' := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ.2 p.1) p.2)
      (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ'.2 p.1) p.2)
  map_smul' a Ψ := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul a _

theorem partialHat_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (partialHat ν ψ hψ n n') := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Ψ h
  ext x
  have h1 := eq_zero_of_hat_eq_zero ν ψ hψ hne (slice_mem_SB Ψ.2 x.toCols₁)
    (fun η => congrFun h (x.toCols₁, η)) (fun r => x r (Sum.inr ()))
  simpa [withLast_toCols] using h1

def coupleBil (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' Z : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × Matrix (Z ⊕ Unit) n k → ℂ) :=
  LinearMap.mk₂ ℂ (fun g Ψ q => g.1 q.2.toRows₁ * partialHat ν ψ hψ n n' Ψ (q.1, q.2 (Sum.inr ())))
    (fun g g' Ψ => by funext q; simp [add_mul])
    (fun a g Ψ => by funext q; simp [mul_assoc])
    (fun g Ψ Ψ' => by funext q; simp [mul_add])
    (fun a g Ψ => by funext q; simp; ring)

theorem coupleBil_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (TensorProduct.lift (coupleBil ν ψ hψ n n' Z)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB (Matrix Z n k))
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i m => b i ⊗ₜ m := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ (x₀ : Matrix n n' k) (η : n → k) (x : Matrix Z n k),
      ∑ i ∈ c.support, (b i).1 x * partialHat ν ψ hψ n n' (c i) (x₀, η) = 0 := by
    intro x₀ η x
    have hrow : (fromRows x (Matrix.of fun (_ : Unit) r => η r)) (Sum.inr ()) = η := by
      funext r; simp
    have := congrFun ht (x₀, fromRows x (Matrix.of fun (_ : Unit) r => η r))
    simp only [ht', Finsupp.sum, map_sum, TensorProduct.lift.tmul] at this
    simpa [coupleBil, Finset.sum_apply, hrow] using this
  have hzero : c = 0 := by
    ext i : 1
    by_cases hi : i ∈ c.support
    · have hP : partialHat ν ψ hψ n n' (c i) = partialHat ν ψ hψ n n' 0 := by
        rw [map_zero]
        funext p
        have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support
          (fun j => partialHat ν ψ hψ n n' (c j) p)
          (by
            ext x
            simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
              ZeroMemClass.coe_zero, Pi.zero_apply]
            rw [← hm p.1 p.2 x]
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
        simpa using hli
      simpa using partialHat_injective ν ψ hψ hne n n' hP
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

theorem exists_pair_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z] (M : Type) [AddCommGroup M] [Module ℂ M] (Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M), ∃ Λ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] M, (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) → Λ Ξ = Bl Ψ₂ Ψ₁) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (a : SB (Matrix Z n k)) (c : SB (Matrix n Unit k)) (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * (a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (q.2 (Sum.inr ())))) → Λ Ξ = Bl a Ψ₁ := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _ M _ _ Bl
  classical
  set T := TensorProduct.lift (coupleBil ν ψk hψ n n' Z) with hT
  have hinj := coupleBil_injective ν ψk hψ hne n n' Z
  let eT := LinearEquiv.ofInjective T hinj
  let W : Submodule ℂ (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)) :=
    (LinearMap.range T).comap (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype
  let res : W →ₗ[ℂ] LinearMap.range T :=
    (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype.restrict (fun x hx => hx)
  let Λ₀ : W →ₗ[ℂ] M := (TensorProduct.lift Bl).comp (eT.symm.toLinearMap.comp res)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have key : ∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k))
      (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), Ξ.1 = T (Ψ₂ ⊗ₜ Ψ₁) → Λ Ξ = Bl Ψ₂ Ψ₁ := by
    intro Ψ₁ Ψ₂ Ξ hΞ
    have hmem : Ξ ∈ W := ⟨Ψ₂ ⊗ₜ Ψ₁, hΞ.symm⟩
    have h1 := LinearMap.congr_fun hΛ ⟨Ξ, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    have h2 : res ⟨Ξ, hmem⟩ = eT (Ψ₂ ⊗ₜ Ψ₁) := Subtype.ext (by
      rw [LinearEquiv.ofInjective_apply]
      exact hΞ)
    simp only [Λ₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2, LinearEquiv.symm_apply_apply,
      TensorProduct.lift.tmul]
  refine ⟨Λ, fun Ψ₁ Ψ₂ Ξ h => key Ψ₁ Ψ₂ Ξ (funext fun q => ?_),
    fun Ξ₁ a c Ψ₁ Ξ h1 h2 => key Ψ₁ a Ξ (funext fun q => ?_)⟩
  · rw [h q, hT, TensorProduct.lift.tmul]
    rfl
  · rw [h2 q, hT, TensorProduct.lift.tmul]
    have e : (fun y => Ψ₁.1 (withLast q.1 y)) = fun y => Ξ₁.1 q.1 * c.1 (Matrix.of fun r (_ : Unit) => y r) := by
      funext y
      rw [h1]
      rfl
    change _ = a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (withLast q.1 y)) (q.2 (Sum.inr ()))
    rw [e]
    simp only [GlobalTheory.StepData.hat, mul_assoc]
    rw [integral_const_mul]
    ring

end GlobalTheory.LocFlat.CQLast
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTrans
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Unf.MajLoc

theorem exists_compact_sub {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (K Q : Set G)
    (hK : IsCompact K) (hQ : IsCompact Q) : ∃ K' : Set G, IsCompact K' ∧ ∀ k ∈ K, ∀ x ∈ Q, k - x ∈ K' :=
  ⟨_, (hK.prod hQ).image continuous_sub, fun k hk x hx => ⟨(k, x), ⟨hk, hx⟩, rfl⟩⟩

theorem summable_of_tsum_ne_top {α β : Type*} (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) (h : (∑' y, ENNReal.ofReal (f y)) ≠ ⊤)
    (e : α → β) (he : Function.Injective e) : Summable fun a => f (e a) :=
  ((ENNReal.summable_toReal h).congr fun y => ENNReal.toReal_ofReal (hf y)).comp_injective he

theorem inv_pow_le {a c R : ℝ} (N : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 ≤ R) (h : c ≤ a + R) :
    ((1 + a) ^ N)⁻¹ ≤ (1 + R) ^ N * ((1 + c) ^ N)⁻¹ := by
  have hle : 1 + c ≤ (1 + R) * (1 + a) := by nlinarith [mul_nonneg ha hR]
  have hA : 0 < (1 + a) ^ N := by positivity
  have hB : 0 < (1 + c) ^ N := by positivity
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle N

theorem realSize_neg {D : D7} (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : realSize θ (-x) = realSize θ x := by
  unfold realSize
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (-x) i j = -compAt θ τ x i j := by
    show θ τ (infPart D (-x i j)) = -θ τ (infPart D (x i j))
    rw [RingHom.map_neg (infPart D), RingHom.map_neg (θ τ)]
  rw [this, norm_neg]

theorem maj_add_le {D : D7} (θ : InfFam D) {m n : ℕ} (K K' : Set (Mx D m n)) (N : ℕ) (x y : Mx D m n) (R : ℝ)
    (hR : 0 ≤ R) (hx : realSize θ x ≤ R) (hK : ∀ k ∈ K, k - x ∈ K') :
    maj θ K N (x + y) ≤ (1 + R) ^ N * maj θ K' N y := by
  by_cases hb : InBox K (x + y)
  · have hb' : InBox K' y := by
      obtain ⟨k, hk, hkx⟩ := hb
      refine ⟨k - x, hK k hk, ?_⟩
      have : y - (k - x) = x + y - k := by abel
      rw [this]; exact hkx
    unfold maj
    rw [if_pos hb, if_pos hb']
    have hadd := GlobalTheory.MajSum.realSize_add_le θ (x + y) (-x)
    have e2 : x + y + -x = y := by abel
    rw [e2, realSize_neg] at hadd
    exact inv_pow_le N (realSize_nonneg θ _) (realSize_nonneg θ _) hR (by linarith)
  · have e0 : maj θ K N (x + y) = 0 := by
      unfold maj
      rw [if_neg hb]
    rw [e0]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N _)

theorem summable_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n),
    IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  intro D θ hθ m n
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ m n
  refine ⟨N, fun K Q hK hQ => ?_⟩
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) := GlobalTheory.Unf.MajMeas.continuous_realSize hθ
  obtain ⟨K', hK', hKK⟩ := @exists_compact_sub (Mx D m n) _ _ (lattice_Mx D m n).1 K Q hK hQ
  obtain ⟨R, hR⟩ := (hQ.image hcont).bddAbove
  have hs : Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => maj θ K' N (rat ξ) :=
    summable_of_tsum_ne_top (fun y : ratMx D m n => maj θ K' N y) (fun y => maj_nonneg θ K' N y) (hN K' hK')
      (fun ξ => ⟨rat ξ, rat_mem ξ⟩) fun a b h => rat_injective (congrArg Subtype.val h)
  exact ⟨fun ξ => (1 + max R 0) ^ N * maj θ K' N (rat ξ), hs.mul_left _, fun x hx ξ =>
    maj_add_le θ K K' N x (rat ξ) (max R 0) (le_max_right _ _) ((hR ⟨x, hx, rfl⟩).trans (le_max_left _ _))
      fun k hk => hKK k hk x hx⟩

end GlobalTheory.Unf.MajLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopologicalIsoParahoricChartSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartSplitIso

variable {D : D7}

def projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem splitProj_projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (x : Fv D.host.F v ⊗[D.host.F] D.host.E) : GlobalTheory.AdelicU.splitProj (projEmb φ) x = φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    have e : (a ⊗ₜ[D.host.F] x : Fv D.host.F v ⊗[D.host.F] D.host.E) = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [GlobalTheory.AdelicU.splitProj_tmul, e, map_smul, smul_eq_mul]
    rfl

def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) : GL κ K ≃ₜ* GL ι K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε.symm).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem reindexGL_val {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) (x : GL κ K) : (reindexGL K ε x).1 = x.1.submatrix ε ε := rfl

theorem grpCo_eq {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (V : HSp D)
    (hJ : IsHermND D.sp.cm.sig V.gram) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    grpCo φ V B g = GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) B
      (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g) := by
  refine Units.ext ?_
  rw [GlobalTheory.AdelicU.splitEquivIn_apply]
  simp only [grpCo, Units.val_mul]
  congr 2
  exact Matrix.ext fun i j => (splitProj_projEmb φ _).symm

end GlobalTheory.ChartSplitIso

namespace GlobalTheory.ChartSplitIso

theorem exists_equiv_emb : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ →
    IsChart s k φ ι → ∃ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v,
      ∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y) := by
  intro D s k v φ ι _ _ hι
  obtain ⟨ε, -, hε⟩ := hι
  have hJ : IsHermND D.sp.cm.sig s.V.gram := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 s.V
  let Ψ := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) (frCo φ s.β)
  refine ⟨(reindexGL (Fv D.host.F v) ε).symm.trans Ψ.symm, fun y => (hε y).1.symm.trans ?_⟩
  change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = _
  congr 1
  apply Ψ.injective
  apply (reindexGL (Fv D.host.F v) ε).injective
  refine Units.ext ?_
  rw [reindexGL_val, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply,
    ContinuousMulEquiv.apply_symm_apply, ← (hε y).2, grpCo_eq φ s.V hJ]

end GlobalTheory.ChartSplitIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramified
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.SphSec

section Gen

variable {G : Type} [Group G] (P K : Subgroup G) (f : P →* ℂ)

theorem gen_wd (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p p' : P) (k k' : G) (hk : k ∈ K) (hk' : k' ∈ K)
    (e : (p : G) * k = p' * k') : f p = f p' := by
  have h1 : ((p'⁻¹ * p : P) : G) = k' * k⁻¹ := by
    have : (p : G) = p' * (k' * k⁻¹) := by rw [← mul_assoc, ← e, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, inv_mul_cancel_left]
  have h2 := hK _ (h1 ▸ mul_mem hk' (inv_mem hk))
  calc f p = f (p' * (p'⁻¹ * p)) := by rw [mul_inv_cancel_left]
    _ = f p' := by rw [map_mul, h2, mul_one]

variable (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k)

noncomputable def genFun (g : G) : ℂ := f (hI g).choose

variable {P K f hI}

theorem genFun_mul (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) {k : G} (hk : k ∈ K) :
    genFun P K f hI (p * k) = f p := by
  obtain ⟨k', hk', e⟩ := (hI (p * k)).choose_spec
  exact gen_wd P K f hK _ _ _ _ hk' hk e.symm

theorem genFun_right (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (g : G) {k : G} (hk : k ∈ K) :
    genFun P K f hI (g * k) = genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, mul_assoc]
  exact genFun_mul hK _ (mul_mem hk₀ hk)

theorem genFun_left (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) (g : G) :
    genFun P K f hI (p * g) = f p * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, ← mul_assoc]
  rw [← Subgroup.coe_mul, genFun_mul hK _ hk₀, map_mul]
  rfl

theorem genFun_one (hK : ∀ p : P, (p : G) ∈ K → f p = 1) : genFun P K f hI 1 = 1 := by
  have := genFun_mul (hI := hI) hK 1 (one_mem K)
  rwa [Subgroup.coe_one, mul_one, map_one] at this

theorem genFun_unique (Ψ : G → ℂ) (hΨ : ∀ (p : P) g, Ψ (p * g) = f p * Ψ g) (hΨK : ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g)
    (g : G) : Ψ g = Ψ 1 * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  have := hΨ (hI g).choose 1
  rw [mul_one] at this
  rw [genFun, mul_comm]
  conv_lhs => rw [e]
  rw [hΨK _ hk₀, this]

theorem continuous_genFun [TopologicalSpace G] [IsTopologicalGroup G] (hK : ∀ p : P, (p : G) ∈ K → f p = 1)
    (ho : IsOpen (K : Set G)) : Continuous (genFun P K f hI) := by
  refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := genFun P K f hI g)).congr ?_
  filter_upwards [(ho.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])] with h hh
  have := genFun_right (hI := hI) hK g (k := g⁻¹ * h) hh
  rwa [mul_inv_cancel_left, eq_comm] at this

theorem gen_exists [TopologicalSpace G] [IsTopologicalGroup G] (P K : Subgroup G) (f : P →* ℂ)
    (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (ho : IsOpen (K : Set G)) :
    ∃ φ : G → ℂ, (∀ (p : P) g, φ (p * g) = f p * φ g) ∧ Continuous φ ∧ (∀ g, ∀ k ∈ K, φ (g * k) = φ g) ∧ φ 1 = 1 ∧
      ∀ Ψ : G → ℂ, (∀ (p : P) g, Ψ (p * g) = f p * Ψ g) → (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g :=
  ⟨genFun P K f hI, genFun_left hK, continuous_genFun hK ho, fun g _ hk => genFun_right hK g hk, genFun_one hK,
    fun Ψ hΨ hΨK g => genFun_unique Ψ hΨ hΨK g⟩

end Gen

set_option maxHeartbeats 1000000 in

theorem exists_isSphSecAt_unique : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  intro D A L hL μ hμ v hunr s
  haveI : Submodule.IsLattice D.host.E L := hL.1
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place D A L hL v hs
    · exact GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place D A L hL v hs
  let N : ℝ≥0 →* ℂ := ⟨⟨fun r => npow r (s + (A.rank : ℂ) / 2), one_npow _⟩, fun r r' => GlobalTheory.Doubling.npow_mul r r' _⟩
  let f : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram →* ℂ :=
    (Circle.coeHom.comp ((charAt μ v).comp (aH _ D.sp.cm.sig (dblSp A).gram))) *
      (N.comp ((absEv D.host.F D.host.E v).comp (aH _ D.sp.cm.sig (dblSp A).gram)))
  have hf : ∀ p, f p = (charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) : ℂ) *
      npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) := fun p => rfl
  have hK : ∀ p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram,
      (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → f p = 1 := by
    intro p hp
    have h1 := GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p hp
    have h2 : (((aH _ D.sp.cm.sig (dblSp A).gram p)⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) :
        Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
      rw [← map_inv]
      exact GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p⁻¹ (inv_mem hp)
    rw [hf, GlobalTheory.T.ideleCharacter_eq_one_integral_units_unramified_adelic D μ v _ h1 h2 hunr,
      abs_aH_eq_one (continuous_absEv v) (isCompact_KFin v) p hp, one_npow, Circle.coe_one, one_mul]
  clear_value f
  obtain ⟨φ, hl, hc, hr, h1, hu⟩ := gen_exists (G := Gv (dblSp A) v) _ _ f hI hK (isOpen_KFin v)
  refine ⟨φ, ⟨mem_degPSH.2 ⟨fun p g => by rw [hl, hf], hc, IsKFinite.of_invariant fun g k hk => hr g k hk⟩,
    fun k hk g => hr g k hk, h1⟩, fun Ψ hΨ hΨK g => hu Ψ (fun p g => by rw [hΨ, hf]) hΨK g⟩

end GlobalTheory.Core.Rk.SphSec

end
end


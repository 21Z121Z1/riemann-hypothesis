import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal

theorem sum_notMem_of_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ hle hR l a b w hw hc
  let g : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨(a i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (a i)),
      sub_mem (tmul_mem (hR _ (a i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩
  let bb : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨1 ⊗ₜ b i, tmul_mem (one_mem (placeAlg E)) _⟩
  let u : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i), tmul_mem (one_mem (placeAlg E)) _⟩
  let v : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i)⁻¹, tmul_mem (one_mem (placeAlg E)) _⟩
  have hg : ∀ i, g i ∈ graphIdeal E R π ρ := fun i => Ideal.subset_span (Or.inr ⟨a i, rfl⟩)
  have hsum : w - u = ∑ i, g i * bb i := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, hw, AddSubmonoidClass.coe_finset_sum]
    simp only [g, bb, u, Subalgebra.coe_mul, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Finset.sum_sub_distrib, TensorProduct.tmul_sum]
  have huv : u * v = 1 := by
    apply Subtype.ext
    simp only [u, v, Subalgebra.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hc, Subalgebra.coe_one, Algebra.TensorProduct.one_def]
  have hu : u ∉ 𝔭 := fun h => one_notMem 𝔭 (huv ▸ 𝔭.mul_mem_right v h)
  intro hwp
  have hd : w - u ∈ 𝔭 :=
    hle (hsum ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hg i))
  exact hu (by simpa using 𝔭.sub_mem hwp hd)

end GlobalTheory.GraphLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummablePartialFourierAdelicSchwartzRationalPairStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_partialFourier_adelicSchwartz_rationalPairs : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t)) (fun i => algebraMap F (AF F) (uv.2 i))‖ := by
  first | exact @GlobalTheory.PartialFourierSum.summable_partial_fourier | exact GlobalTheory.PartialFourierSum.summable_partial_fourier | (intros; apply GlobalTheory.PartialFourierSum.summable_partial_fourier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.SelfInterGrowth

open MvPolynomial

theorem expand (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Φ ((X 0 + C t * X 1) ^ (D + 1)) = ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  intro hC k _ Y _ p D hX L A a ha
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).1
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  refine ⟨fun n => Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)), fun n => ?_, ?_⟩
  · exact (hiso n).isSelfInter hX (hΦ.1 _)
  have h0 : Φ (X 0 ^ (D + 1)) = a :=
    HermLB.IsSelfInter.unique hX ((((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1 0)) ha
  set f : ℝ → ℝ := fun t => Φ ((X 0 + C t * X 1) ^ (D + 1)) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Φ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = a := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)) / (n : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hlin, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.SelfInterGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCompactActionDerivative
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigSep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def evAt (π : CuspSub E a) (g : GA E a) : π.V →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp ((Sm E a).subtype.comp π.V.subtype)

def ell (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) :
    Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map (evAt π g) (LinearMap.proj i))

theorem ell_tmul (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) (φ : π.V) (v : Fin Ξ.d → ℂ) :
    ell π Ξ g i (φ ⊗ₜ v) = φ.1.1 g * v i := by
  simp [ell, evAt]

theorem piScalarRight_eval (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) (i : Fin Ξ.d) :
    ((TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d) m) i).1.1 g = ell π Ξ g i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul φ v =>
    rw [ell_tmul]
    simp [TensorProduct.piScalarRight_apply, mul_comm]

theorem ell_sep (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ))
    (h : ∀ g i, ell π Ξ g i m = 0) : m = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d))).1 ?_
  funext i
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [piScalarRight_eval, h]
  rfl

theorem ell_deriv (π : CuspSub E a) (Ξ : AlgRep E a) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t).1) (toL Z) 0) (g : GA E a) (i : Fin Ξ.d)
    (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => ell π Ξ g i (tensorK π Ξ (c t) m)) (ell π Ξ g i (tensorLie π Ξ (toL Z) m)) 0 := by
  have h0' : Unitary.toUnits (c 0) = 1 := by rw [h0, map_one]
  have hc' : HasDerivAt (fun t => toL (Unitary.toUnits (c t)).val) (toL Z) 0 := hc
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simp only [map_add]; exact hx.add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc'
    have h2 : HasDerivAt (fun t => (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i) ((Ξ.dmat (toL Z) *ᵥ v) i) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc' i j).mul_const (v j)
    have e1 : ∀ t, ell π Ξ g i (tensorK π Ξ (c t) (φ ⊗ₜ v)) =
        φ.1.1 (g * infGL E a (Unitary.toUnits (c t))) * (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i := fun t => by
      rw [tensorK, TensorProduct.map_tmul, ell_tmul]
      rfl
    have e2 : ell π Ξ g i (tensorLie π Ξ (toL Z) (φ ⊗ₜ v)) =
        lieD (toL Z) φ.1.1 g * (Ξ.mat (Unitary.toUnits (c 0)) *ᵥ v) i +
          φ.1.1 (g * infGL E a (Unitary.toUnits (c 0))) * (Ξ.dmat (toL Z) *ᵥ v) i := by
      rw [h0', map_one, map_one, mul_one, Matrix.one_mulVec, tensorLie_tmul, map_add, ell_tmul, ell_tmul]
      rfl
    rw [funext e1, e2]
    exact h1.mul h2

end GlobalTheory.WigSep

namespace GlobalTheory.WigSep

theorem exists_separating_functionals : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), ∃ S : Set (Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), (∀ m, (∀ l ∈ S, l m = 0) → m = 0) ∧ ∀ (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → ∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (tensorK π Ξ (c t) m)) (l (tensorLie π Ξ (toL Z) m)) 0 := by
  intro E _ _ _ a π Ξ
  refine ⟨Set.range fun p : GA E a × Fin Ξ.d => ell π Ξ p.1 p.2, fun m h => ell_sep π Ξ m fun g i => h _ ⟨(g, i), rfl⟩, ?_⟩
  rintro c Z h0 hc _ ⟨⟨g, i⟩, rfl⟩ m
  exact ell_deriv π Ξ c Z h0 hc g i m

end GlobalTheory.WigSep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariantStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_heisenberg_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  first | exact @GlobalTheory.HeisThetaF.isThetaFunOF_heisOF | exact GlobalTheory.HeisThetaF.isThetaFunOF_heisOF | (intros; apply GlobalTheory.HeisThetaF.isThetaFunOF_heisOF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodic
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    exact continuous_finset_sum _ fun l _ => continuous_const.mul (continuous_apply l)
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralAdd
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem glue_mono {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y} (hS : MeasurableSet S) {ρ ρ' : κ → Y → ℝ≥0∞}
    (h : ∀ i y, ρ i y ≤ ρ' i y) : glueMeas e ρ S ≤ glueMeas e ρ' S := by
  have key : glueMeas e ρ ≤ glueMeas e ρ' := by
    refine iSup_mono fun i => Measure.le_iff.2 fun B hB => ?_
    rw [chartMeas_apply _ _ hB, chartMeas_apply _ _ hB]
    exact lintegral_mono fun v => h i _
  exact Measure.le_iff.1 key S hS

private theorem ofReal_balance (a b : ℝ) :
    ENNReal.ofReal (1 * (a + b)) + (ENNReal.ofReal (-1 * a) + ENNReal.ofReal (-1 * b)) =
      ENNReal.ofReal (-1 * (a + b)) + (ENNReal.ofReal (1 * a) + ENNReal.ofReal (1 * b)) := by
  have hm : ∀ v : ℝ, ENNReal.ofReal v = ENNReal.ofReal (max v 0) := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have conv : ∀ x y z : ℝ, ENNReal.ofReal x + (ENNReal.ofReal y + ENNReal.ofReal z) =
      ENNReal.ofReal (max x 0 + (max y 0 + max z 0)) := fun x y z => by
    rw [ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) (le_max_right _ _)),
      ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), ← hm, ← hm, ← hm]
  have hs : ∀ v : ℝ, max (1 * v) 0 - max (-1 * v) 0 = v := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [conv, conv]
  congr 1
  linarith [hs a, hs b, hs (a + b)]

theorem hasInt_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d d' s t hf hf' hi hi'
  have hsum : IsTopForm e (fun i y => d i y + d' i y) S :=
    ⟨fun i j y hy h1 h2 => by rw [hf.trans i j y hy h1 h2, hf'.trans i j y hy h1 h2, mul_add],
      fun i => (hf.meas i).add (hf'.meas i)⟩
  have comp : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i j y, y ∈ S → y ∈ (e i).source →
      y ∈ (e j).source → ENNReal.ofReal (c * f i y) =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (c * f j y) := by
    intro f h c i j y hy h1 h2
    rw [h.trans i j y hy h1 h2, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  have meas : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i,
      AEMeasurable (fun v => ENNReal.ofReal (c * f i ((e i).symm v)))
        (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)) := fun h c i =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((h.meas i).const_mul c)
  have h2 : ∀ c : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * d i y) + ENNReal.ofReal (c * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * d i y)) S +
        glueMeas e (fun i y => ENNReal.ofReal (c * d' i y)) S := fun c =>
    glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hf c) (comp hf' c) (meas hf c)
  have h3 : ∀ c c' : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y)) +
      (ENNReal.ofReal (c' * d i y) + ENNReal.ofReal (c' * d' i y))) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y))) S +
        (glueMeas e (fun i y => ENNReal.ofReal (c' * d i y)) S +
          glueMeas e (fun i y => ENNReal.ofReal (c' * d' i y)) S) := fun c c' => by
    rw [← h2]
    refine glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hsum c) ?_ (meas hsum c)
    intro i j y hy h1 h2
    rw [comp hf c' i j y hy h1 h2, comp hf' c' i j y hy h1 h2, mul_add]
  have hfin : ∀ ε : ℤˣ,
      glueMeas e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (d i y + d' i y))) S ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hi.1 ε, hi'.1 ε⟩) ?_
    rw [← h2]
    refine glue_mono e hS fun i y => ?_
    rw [mul_add]
    exact ENNReal.ofReal_add_le
  refine ⟨hfin, ?_⟩
  have hbal := h3 1 (-1)
  simp only [ofReal_balance] at hbal
  rw [h3] at hbal
  have a1 := hfin 1
  have a2 := hfin (-1)
  have b1 := hi.1 1
  have b2 := hi.1 (-1)
  have c1 := hi'.1 1
  have c2 := hi'.1 (-1)
  have e1 := hi.2
  have e2 := hi'.2
  simp only [measureReal_def, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at a1 a2 b1 b2 c1 c2 e1 e2 ⊢
  have hr := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add a2 (ENNReal.add_ne_top.2 ⟨b1, c1⟩), ENNReal.toReal_add b1 c1,
    ENNReal.toReal_add a1 (ENNReal.add_ne_top.2 ⟨b2, c2⟩), ENNReal.toReal_add b2 c2] at hr
  linarith

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChart
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem hasInt_of_chart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d e' W g hW hWe hd' hT h0 hg hint
  have hSW : MeasurableSet (S ∩ W) := hS.inter hW.measurableSet
  have hsub : S ∩ W ⊆ e'.source := Set.inter_subset_right.trans hWe
  have key : ∀ ε : ℝ, glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) S =
      ∫⁻ v in e' '' (S ∩ W), ENNReal.ofReal (ε * g v) := by
    intro ε
    have hD : MeasurableSet (S \ W) := hS.diff hW.measurableSet
    have hz := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := fun i y => ENNReal.ofReal (ε * d i y))
      (ρ' := fun i y => ENNReal.ofReal (ε * d i y)) (c := 0) ENNReal.zero_ne_top hD
      (fun i y hi hy => by rw [h0 i y hy.1 hy.2 hi]; simp)
    have hz' : glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) (S \ W) = 0 := by
      have := congrArg (fun μ : Measure Y => μ (S \ W)) hz
      simpa only [Measure.restrict_apply_self, zero_smul, Measure.coe_zero, Pi.zero_apply] using this
    rw [← measure_inter_add_diff S hW.measurableSet, hz', add_zero,
      glueMeas_eq_chartMeas_of_compat_on e hd hcov hSW e' (fun y => ENNReal.ofReal (ε * g (e' y))) hsub hd'
        (fun i j y hy hi hj => by
          rw [hT.trans i j y hy.1 hi hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm])
        (fun j y hy hj => by
          rw [hg j y hy.1 hy.2 hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]),
      chartMeas_apply_of_subset _ _ hSW hsub]
    refine setLIntegral_congr_fun (measurableSet_image e' hSW hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [e'.left_inv (hsub hy)]
  refine ⟨fun ε => ?_, ?_⟩
  · rw [key]
    exact (Integrable.const_mul hint _).lintegral_lt_top.ne
  · rw [measureReal_def, measureReal_def, key, key,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
    simp

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureLeOfSpecializes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_le_of_specializes :
    ∀ (X : Scheme.{0}) (z w : X) (j : ℕ), z ⤳ w → w ≠ z →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      topologicalKrullDim (closure ({w} : Set X)) ≤ j := by
  first
  | exact @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | (apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes ..)

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeOfIsClosedNeUnivIntegral
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem topologicalKrullDim_le_of_isClosed_ne_univ :
    ∀ (X : Scheme.{0}) [IsIntegral X] (d : ℕ), topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → topologicalKrullDim Z ≤ (d : ℕ) := by
  intro X _ d h Z hZ hne
  have h₁ := GlobalTheory.topologicalKrullDim_add_one_le hZ isClosed_univ fun x _ =>
    ⟨genericPoint X, Set.mem_univ _, fun hg => hne (Set.eq_univ_of_forall fun z =>
      (genericPoint_specializes z).mem_closed hZ hg), genericPoint_specializes x⟩
  rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] at h₁
  exact ENat.WithBot.add_le_add_one_right_iff.1 (h₁.trans (h.trans_eq (Nat.cast_succ d)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibresStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.torsion_sections_exhaust_geometric_fibres : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  first | exact @GlobalTheory.Poinc.Tors.torsion_exhaust_geometric | exact GlobalTheory.Poinc.Tors.torsion_exhaust_geometric | (intros; apply GlobalTheory.Poinc.Tors.torsion_exhaust_geometric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusLattice_standard_points_scaled_embedding : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b), x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) → ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧ x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  first | exact @GlobalTheory.LaStdEntries.La_std_rep | exact GlobalTheory.LaStdEntries.La_std_rep | (intros; apply GlobalTheory.LaStdEntries.La_std_rep <;> assumption)
end


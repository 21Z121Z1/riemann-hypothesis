import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem adelic_schwartz_slice_l2_word_bound : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  intro F _ _ _ κ _ ψ hψ i j
  obtain ⟨ℓ, hnd, hℓ⟩ := hψ
  obtain ⟨n, ⟨b⟩⟩ : ∃ n, Nonempty (Module.Basis (Fin n) ℝ (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, ⟨Module.finBasis ℝ _⟩⟩
  obtain ⟨K4, hK4, hb4⟩ := GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values (κ → mixedEmbedding.mixedSpace F) _ b j
  obtain ⟨K5, hK5, hb5⟩ := GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow (κ → mixedEmbedding.mixedSpace F) _ b i
  choose u hu using fun c => GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm F κ ℓ hnd (b.coord c)
  let ia : Option (Fin n) → ℕ := fun a => a.elim 0 (fun _ => i)
  let ua : Option (Fin n) → (κ → mixedEmbedding.mixedSpace F) := fun a => a.elim 0 u
  let wd : Option (Fin n) × (Fin j → Fin n) →
      List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    fun p => List.replicate (ia p.1) (0, ua p.1) ++ (List.ofFn fun r => b (p.2 r)).map fun v => (v, 0)
  refine ⟨Finset.univ.toList.map wd, (K5 * K4) ^ 2 * (Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ),
    fun Φ hΦ y => ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hΦ y
  have hsf : (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = s := funext fun x => (hs x).symm
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := hsf ▸ s.smooth ⊤
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have key : ∀ p x, GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * ua p.1 k) : ℂ)) ^ (ia p.1) *
        iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r)) := by
    intro p x
    rw [GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv F κ ψ ℓ hℓ Φ y hsm, GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv _ _ hsm]
  have hcont : ∀ p, Continuous fun x => GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
    intro p
    simp_rw [key]
    have h1 : Continuous fun x : κ → mixedEmbedding.mixedSpace F => ∑ k, x k * ua p.1 k := by fun_prop
    have h2 : Continuous fun x => iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x :=
      hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (hℓc.comp h1))).pow _).mul
      ((ContinuousMultilinearMap.apply ℝ _ ℂ (fun r => b (p.2 r))).continuous.comp h2)
  rw [List.map_map, Finset.sum_map_toList]
  refine GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise _ MeasureTheory.volume _ _ _ _ hcont fun x => ?_
  have hterm : ∀ p : Option (Fin n) × (Fin j → Fin n),
      p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ ≤
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    intro p
    rw [key, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases p with ⟨_ | c, cs⟩
    · simp [ia]
    · simp only [Option.elim, ia, ua, hu, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, mul_one]
      rw [mul_pow]
      refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
  have h1 : ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤
      K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    calc _ ≤ (K5 * (1 + ∑ c, |b.coord c x| ^ i)) *
          (K4 * ∑ cs : Fin j → Fin n, ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x
            (fun r => b (cs r))‖) :=
          mul_le_mul (hb5 x) (hb4 _) (norm_nonneg _) (by positivity)
      _ = K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n), p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ := by
          rw [Fintype.sum_prod_type, Fintype.sum_option]
          simp only [Option.elim, one_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
          gcongr with p
          exact hterm p
  have h0 : 0 ≤ ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ := by positivity
  calc _ ≤ (K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (K5 * K4) ^ 2 * (∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := by ring
    _ ≤ (K5 * K4) ^ 2 * ((Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ) * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ ^ 2) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq
    _ = _ := by ring

end GlobalTheory.WeilL2Words
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFiniteParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
namespace GlobalTheory.WeilL2Words
open NumberField IsDedekindDomain

theorem adeleOfMixedSpaceComponent_add (F : Type) [Field F] [NumberField F] (z w : mixedEmbedding.mixedSpace F) :
    arch1 F (z + w) = arch1 F z + arch1 F w :=
  Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z w) (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem mul_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    a * arch1 F z = arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * z) := by
  refine Prod.ext ?_ ?_
  · change a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

theorem adeleOfMixedSpaceComponent_zero (F : Type) [Field F] [NumberField F] : arch1 F 0 = 0 :=
  Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl

theorem add_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (a + arch1 F z).1 = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 + z ∧
    (a + arch1 F z).2 = a.2 := by
  constructor
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = _
    rw [map_add, RingEquiv.apply_symm_apply]
  · exact add_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

def arch1Hom (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F where
  toFun := arch1 F
  map_zero' := adeleOfMixedSpaceComponent_zero F
  map_add' := adeleOfMixedSpaceComponent_add F

theorem adeleOfMixedSpaceComponent_finsetSum (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (z : ι → mixedEmbedding.mixedSpace F) :
    arch1 F (∑ i ∈ s, z i) = ∑ i ∈ s, arch1 F (z i) :=
  map_sum (arch1Hom F) z s

theorem dotProduct_arch (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : κ → AdeleRing (𝓞 F) F)
    (y : κ → mixedEmbedding.mixedSpace F) :
    a ⬝ᵥ arch F y = arch1 F (∑ k, InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 * y k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  exact Finset.sum_congr rfl fun k _ => mul_arch1' F (a k) (y k)

theorem fst_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (arch1 F z).1 = z :=
  RingEquiv.apply_symm_apply _ z

theorem dS_sum_pureA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro F _ _ _ κ _ ψ hψ m g f h
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Complex.ofRealCLM.toLinearMap.comp (ℓ.comp M))
  have hL : ∀ X, L X = ((ℓ (∑ k, X k * h.2 k) : ℝ) : ℂ) := by
    intro X
    simp [L, M]
  have hg : (fun X => (2 * Real.pi * Complex.I) * L X).HasTemperateGrowth :=
    ((2 * Real.pi * Complex.I) • L).hasTemperateGrowth
  refine ⟨fun i => SchwartzMap.smulLeftCLM ℂ (fun X => (2 * Real.pi * Complex.I) * L X) (f i) +
    LineDeriv.lineDerivOp h.1 (f i), ?_⟩
  funext a
  set X : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 with hX
  set Y : κ → FiniteAdeleRing (𝓞 F) F := fun k => (a k).2 with hY
  set c : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 with hc
  set A : ℝ := ℓ (∑ k, X k * h.2 k) with hA
  set B : ℝ := ℓ (c * ∑ k, h.1 k * h.2 k) with hB
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) *
        ∑ i, f i (X + t • h.1) * g i Y := by
    funext t
    unfold GlobalTheory.WeilM.schr
    congr 1
    · have e0 : (archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2 =
          arch1 F (∑ k, (t • h.1) k * (t • h.2) k) := by
        rw [archPair, dotProduct_arch]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· * (t • h).2 k) (fst_arch1 F ((t • h).1 k))
      have e1 : a ⬝ᵥ (archPair F (t • h)).2 + ⅟(2 : AdeleRing (𝓞 F) F) * ((archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2)
          = arch1 F (t • (∑ k, X k * h.2 k) + t ^ 2 • (c * ∑ k, h.1 k * h.2 k)) := by
        rw [e0, mul_arch1', archPair, dotProduct_arch, ← adeleOfMixedSpaceComponent_add]
        congr 1
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum,
          Finset.mul_sum, smul_smul, pow_two]
        rfl
      rw [e1, hℓ, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((a + (archPair F (t • h)).1) k).1) = X + t • h.1 :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).1
      have hy : (fun k => ((a + (archPair F (t • h)).1) k).2) = Y :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).2
      unfold GlobalTheory.WeilM.pureA
      rw [hx, hy]

  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((f i).hasFDerivAt (X + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add X)).mul_const (g i Y))
  have hT := hφ.cexp.fun_mul hS
  unfold dS
  rw [key]
  refine (HasDerivAt.deriv hT).trans ?_
  simp only [Finset.sum_apply, GlobalTheory.WeilM.pureA, SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  simp only [hL, ← hA]
  simp only [← hX, ← hY, ← hA, id, zero_smul, add_zero, one_smul, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [show ((0:ℝ) ^ (2 - 1)) = 0 by norm_num, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  ring
end GlobalTheory.WeilL2Words
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivatiStatement
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMaximalCompact_intertwines_fockDerivativeOps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  first | exact @GlobalTheory.KInfComm.main | exact GlobalTheory.KInfComm.main | (intros; apply GlobalTheory.KInfComm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzDatumStableHeisenbergDerivatiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSchwartzDatum_stable_heisenbergDerivative : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ (f : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f₁ : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
    ∃ a', IsDatumA W e Γ (tensT W a' τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) := by
  first | exact @GlobalTheory.BigNZ.DatRealStable.datum_stable | exact GlobalTheory.BigNZ.DatRealStable.datum_stable | (intros; apply GlobalTheory.BigNZ.DatRealStable.datum_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotClassSumSmall

open scoped ComplexOrder

open GlobalTheory.DefiniteClassAvg in

theorem openCompact {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (hstd : X.rA'.IsStd) :
    IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) ∧
    IsCompact (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
  have hJo : IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅] with κ h1
    exact h1.2.1
  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hstd.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hLc : IsCompact ((Lev.levA A' (Formalism.L2.DIV.St X.rA'.β) : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hJo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2
  refine ⟨hJo, (hLc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hJo) ?_⟩
  intro k hk
  exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩

set_option maxHeartbeats 4000000 in

theorem classSum_small : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  intro hPr hK hM hI hB
  obtain ⟨c1, h1⟩ := GlobalTheory.T.bottom_triangle_level_fixes_vector hPr hK hM hI hB
  obtain ⟨c2, h2⟩ := GlobalTheory.T.bottom_pair_modular_twist_identity hPr hK hM hI hB
  refine ⟨max c1 c2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have h1 := h1 C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have h2 := h2 C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX
  obtain ⟨hJo, hJc⟩ := openCompact X hX.std'
  haveI : X.m'.IsHaarMeasure := hX.is.meas'.1
  have hJtop : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ 0 :=
    (hJo.measure_pos X.m' ⟨1, Subgroup.one_mem _⟩).ne'
  refine ⟨((X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))).toReal : ℂ),
    by exact_mod_cast (ENNReal.toReal_pos hJ0 hJtop).ne', fun s Q P P' hP ea ed h g hg gx hgx T' => ?_⟩
  obtain ⟨hu, hcard⟩ := GlobalTheory.T.standardLattice_doubleCosetClasses_stabilisers A' X.rA' hX.is.rigA' hX.std' ea gx hgx
  haveI : Finite (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := (GlobalTheory.NormSum.cls_finite_card_le D P'.a).1
  letI : Fintype (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := Fintype.ofFinite _
  have hfin : ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧
      (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))}.Finite := fun x => by
    have h1 := GlobalTheory.InnerClassSum.finite_stab_of_measure X.m' (GQ A') _ hX.is.meas'.2 hJ0 hJtop (gx x)
    have him : {γ : GA D A' | γ ∈ GQ A' ∧
        (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} =
        Subtype.val '' {γ : GQ A' | (gx x)⁻¹ * (γ : GA D A') * gx x ∈
          ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact h1.image _
  have hl := GlobalTheory.SqTower.Normal.ker'_left hX.is s (GlobalTheory.BotFormula.minorF ea ed T') g
  have hr : ∀ k ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')), ∀ x,
      X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (x * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g x := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    refine GlobalTheory.DefiniteClassSum.invariant_sup ?_ ?_
    · intro k hk x
      obtain ⟨hk1, -⟩ := Lev.mem_levA.1 hk
      have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' s) := hX.is.weil' s
      have hf' : IsThetaFunO W.ψ A' WW (X.f' s) :=
        GlobalTheory.GalLift.Vec.theta_of_thetaAt hX.is.isVac.1 hX.is.isVac.2.inf (hX.is.snd s) hX.is.isVac'.2.theta
      show X.ω' s (x * k, g) _ 0 = X.ω' s (x, g) _ 0
      have e : ((x * k, g) : GA D A' × GA D WW) = (x, g) * (k, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hX.is.isVac'.2.inf k hk1 1
        (GfC WW).one_mem _ _ _ _ _ _ hf', h1 W hψ i j A A' WW X hX s k hk]
    · intro k hk x
      exact h2 W hψ i j A A' WW X δ t0 hX s Q P P' hP ea ed T' g k hk x
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (GA D A') X.m' (GQ A') _ X.fd' hX.is.meas'.2 hJo hJtop
    _ gx hu hfin _ hl hr
  rw [Tri.I', heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]

end GlobalTheory.BotClassSumSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEvalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_theta_eval : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (Pf : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (n : ℕ) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n)
        (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ y, X.ker W.ψ W.θ t Pf g (y * k) = X.ker W.ψ W.θ t Pf g y := by
  first | exact @GlobalTheory.BotBigLevel.ker_mul_level | exact GlobalTheory.BotBigLevel.ker_mul_level | (intros; apply GlobalTheory.BotBigLevel.ker_mul_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentationStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateModulus_standardTheta_presentation : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hb : IsCoprime (D.host.conj • 𝔪) D.host.𝔟) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ Q : ℕ, Ideal.absNorm 𝔪 = Q → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D (D.host.conj • 𝔪) (r⁻¹ * k)) → Pres D ⊤ δ Q e0 (∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0)) := by
  first | exact @GlobalTheory.BotPairSmall.pres_conj_std | exact GlobalTheory.BotPairSmall.pres_conj_std | (intros; apply GlobalTheory.BotPairSmall.pres_conj_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumPhiASplitPlaceTransportEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumPhiA_splitPlace_transport_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  first | exact @GlobalTheory.PureMatch.phiA_transport_split_place | exact GlobalTheory.PureMatch.phiA_transport_split_place | (intros; apply GlobalTheory.PureMatch.phiA_transport_split_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteBottomTriple_transferred_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @GlobalTheory.BotFrames.frames_transfer | exact GlobalTheory.BotFrames.frames_transfer | (intros; apply GlobalTheory.BotFrames.frames_transfer <;> assumption)
end


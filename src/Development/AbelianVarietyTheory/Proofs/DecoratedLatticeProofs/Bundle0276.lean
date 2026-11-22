import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0136
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.LastTwoSteps
open GlobalTheory.StepData GlobalTheory.SymChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intInd_mem_SB (a b : Type) [Fintype a] [Fintype b] :
    Set.indicator {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈ SB (Matrix a b k) := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix a b k) := inferInstanceAs (T2Space (a → b → k))
  have e : {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} =
      Set.pi Set.univ fun _ : a => Set.pi Set.univ fun _ : b => (𝒪[k] : Set k) := by
    ext x; exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩
  have hK : IsCompact {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have ho : IsOpen {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have := GlobalTheory.FinPl.Comm.ite_mem_SB hK ho
  convert this using 1
  funext x
  by_cases h : ∀ r q, x r q ∈ 𝒪[k] <;> simp [Set.indicator_apply, h]

variable [MeasurableSpace k] [BorelSpace k]

theorem hat_const_mul {n : Type} [Fintype n] (ψ : AddChar k Circle) (ν : Measure k) (ε : k) (c : ℂ)
    (f : (n → k) → ℂ) (η : n → k) : hat ψ ν ε (fun y => c * f y) η = c * hat ψ ν ε f η := by
  simp only [hat, mul_assoc]
  rw [integral_const_mul]

open Classical in

theorem hat_int {n : Type} [Fintype n] [DecidableEq n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k}
    (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (η : n → k) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0)) η = if ∀ i, η i ∈ 𝒪[k] then 1 else 0 := by
  classical
  have := hν.1
  have := secondCountable k
  split_ifs with hη
  · have hε' : ε ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, hε]
    rw [GlobalTheory.StepData.Model.hat_coset hψ hν hε' 0 hη]
    simp
  · have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) (x + z) =
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) x := fun z hz x => by
      have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
        (Submodule.Quotient.eq _).2 (by simpa using hz)
      simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
    refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
      (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
    · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

section Entries
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

theorem psi_mem_SB (T : Chain k s X Z) (hT : T.Regular) (y : X (s + 1) → k) :
    (fun x₀ => T.Psi 1 x₀ y) ∈ SB (Matrix (X (s + 1)) (X s) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := X (s + 1)) (n' := X s)
  refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (T.mu (s + 1)) 1 1 (hT.1 s 0 rfl))
    (p := fun x₀ => withCol x₀ y) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
  · unfold withCol; fun_prop
  · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))

variable [MeasurableSpace k] [BorelSpace k]

theorem xiTop_mem_SB (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) (1 : kˣ)) :
    T.xiTop (box _ (1 : kˣ)) ψ ν ε yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν ε hψ hν hε (X (s + 1)) 1 1 _ (cosetInd_mem_SB 1 yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

end Entries

section Ones
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [Fintype c]

open Classical in

theorem cosetInd_zero (y : a → k) :
    cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y = if ∀ i, y i ∈ 𝒪[k] then 1 else 0 := by
  have hy : (Submodule.Quotient.mk y : (a → k) ⧸ box a (1 : kˣ)) = Submodule.Quotient.mk 0 ↔ ∀ i, y i ∈ 𝒪[k] := by
    simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
  unfold cosetInd
  by_cases h : ∀ i, y i ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (hy.2 h), if_pos h]
  · rw [Set.indicator_of_notMem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (mt hy.1 h), if_neg h]

open Classical in

theorem intInd_fromCols (q : Matrix a b k) (y : a → k) :
    Set.indicator {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ))
        (fromCols q (Matrix.of fun r _ => y r)) =
      Set.indicator {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q *
        cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
  have hf : (∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]) ↔
      (∀ r c, q r c ∈ 𝒪[k]) ∧ ∀ i, y i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => by simpa using h r (Sum.inl c), fun r => by simpa using h r (Sum.inr ())⟩
    · rintro ⟨hq, hy⟩ r (c | c)
      · simpa using hq r c
      · simpa using hy r
  rw [cosetInd_zero]
  by_cases h : ∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h,
      Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) (hf.1 h).1, if_pos (hf.1 h).2,
      mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h]
    by_cases hq : ∀ r c, q r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq,
        if_neg fun h2 => h (hf.2 ⟨hq, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq, zero_mul]

open Classical in

theorem intInd_rows (q : Matrix (c ⊕ Unit) a k) :
    Set.indicator {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q =
      Set.indicator {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q.toRows₁ *
        if ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] then 1 else 0 := by
  have hr : (∀ r c, q r c ∈ 𝒪[k]) ↔ (∀ r c, q.toRows₁ r c ∈ 𝒪[k]) ∧ ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => h (Sum.inl r) c, fun i => h (Sum.inr ()) i⟩
    · rintro ⟨hr, hη⟩ (r | r) c
      · exact hr r c
      · exact hη c
  by_cases h : ∀ r c, q r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h,
      Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) (hr.1 h).1,
      if_pos (hr.1 h).2, mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h]
    by_cases h1 : ∀ r c, q.toRows₁ r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1,
        if_neg fun h2 => h (hr.2 ⟨h1, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1, zero_mul]

end Ones

theorem gLast : ∀ (D : D7), LastLoc D → GlobalTheory.SymChain.AtMostOne → GLast D := by
  classical
  intro D hLL hAMO k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    FA F₀ FS FT FX hcore hFX c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have := hν.1
  obtain ⟨-, -, h1, h2, -⟩ := hAMO k ν hν s κ S t
  obtain ⟨Λ, hΛ, hK⟩ := hLL k p ν hν.1 ψ hstd S.ψ hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz _ _ _ FA F₀ FS FT FX
    hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hreg : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have hv1 : valuation k (-1 : k) = 1 := by simp
  let Ξ₁ : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, psi_mem_SB _ hreg (S.y0 t)⟩
  let Ξ₂ : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) :=
    ⟨_, xiTop_mem_SB _ hreg S.cond hν hv1 (Submodule.Quotient.mk (S.y0 t))⟩
  let O₁' : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) := ⟨_, intInd_mem_SB _ _⟩
  have hcp : ∀ x₀ y, (S.T t).Psi 1 x₀ y =
      (S.T t).Psi 1 x₀ (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := fun x₀ y => by
    by_cases hy : y - S.y0 t ∈ box _ (1 : kˣ)
    · rw [h2 x₀ y hy, cosetInd, Set.indicator_of_mem, mul_one]
      exact (Submodule.Quotient.eq _).2 hy
    · rw [cosetInd, Set.indicator_of_notMem, mul_zero]
      · exact not_not.1 (mt (h1 x₀ y) hy)
      · exact fun h => hy ((Submodule.Quotient.eq _).1 h)
  have hprod : ∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2 := fun q => by
    rw [hΞ q, hΦ₂]
    have e : (fun y => Φ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        (S.T t).Psi 1 q.1 (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := by
      funext y
      rw [hΦ₁, ← hcp]
      rfl
    rw [e, hat_const_mul]
    show _ = (S.T t).Psi 1 q.1 (S.y0 t) * ((S.T t).PhiTop (fromCols q.2.toRows₁ 0) * _)
    ring
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact intInd_fromCols q.1 y
    rw [e, hat_const_mul, hat_int S.cond hν hv1]
    simp only [O₁', O₂']
    rw [intInd_rows q.2]
    ring
  have key := (GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension D k p ψ _ _ _).1 B.A W X FA FS FX Λ c₁ c₂ Ξ₁ O₁' Ξ₂ O₂' Ξ Ξ' hΛ hc₁ hc₂ rfl rfl hprod hone
  have e1 := funext hΞK
  have e2 := funext hΞ'K
  rw [e1, e2]
  exact key

end GlobalTheory.LastTwoSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsAtTauChart
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RegSch.ChartDer

open GlobalTheory.StdUnn

variable {D : D7}

theorem isUnit_det_map {n : ℕ} {R : Type} [CommRing R] (f : D.host.E →+* R) {T : Matrix (Fin n) (Fin n) D.host.E}
    (hT : IsUnit T.det) : IsUnit (T.map f).det := by
  have := hT.map f
  rwa [RingHom.map_det] at this

theorem isAtTau_iff (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) :
    IsAtTau θ V τ x h ↔ compAt θ τ (mt V h) = x ∧ (∀ τ', τ' ≠ τ → compAt θ τ' (mt V h) = 1) ∧
      (mt V h).map (finPart D) = 1 := by
  have : h ∈ GinfC V ↔ (mt V h).map (finPart D) = 1 := by
    rw [GinfC, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [IsAtTau, this]
  exact ⟨fun ⟨a, b, c⟩ => ⟨b, c, a⟩, fun ⟨b, c, a⟩ => ⟨a, b, c⟩⟩

end GlobalTheory.RegSch.ChartDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactGinfCOfOntoUni
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem isCompact_ginfC_of_ontoUni (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hθ : IsInfFam θ) (hr : OntoUni (fun k : GinfC V => inB θ V B k.1)) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hB : ∀ τ, IsUnit (B τ).det := by
    intro τ
    by_contra hn
    have h0 := hr.uni 1 τ
    have e : inB (Formalism.IndefR.Eqv.thetaC D) V B (1 : GinfC V).1 τ = 0 := by
      simp only [inB, Matrix.nonsing_inv_apply_not_isUnit _ hn, Matrix.zero_mul]
    rw [e] at h0
    have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 0 := by
      have := Matrix.mem_unitaryGroup_iff.mp h0
      simpa using this.symm
    have hB1 : B τ = 1 := by
      calc B τ = B τ * 1 := (Matrix.mul_one _).symm
        _ = 0 := by rw [h1, Matrix.mul_zero]
        _ = 1 := h1.symm
    exact hn (by rw [hB1, Matrix.det_one]; exact isUnit_one)
  have hconj : ∀ τ (M : Matrix (Fin V.rank) (Fin V.rank) ℂ), B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = M := by
    intro τ M
    calc B τ * ((B τ)⁻¹ * M * B τ) * (B τ)⁻¹ = (B τ * (B τ)⁻¹) * M * (B τ * (B τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = M := by rw [Matrix.mul_nonsing_inv _ (hB τ), Matrix.one_mul, Matrix.mul_one]
  have hU : ∀ u : D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ,
      Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) := by
    intro u
    obtain ⟨k, hk⟩ := hr.onto (fun τ => (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)) (fun τ => (u τ).2)
    have e : (fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) =
        fun τ => infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) (k : GA D V) := by
      funext τ
      have := congrFun hk τ
      rw [← this]
      exact hconj τ _
    rw [e]
    exact Formalism.IndefR.Eqv.infMat_unitary' D V _
  have : CompactSpace (unitaryGroup (Fin V.rank) ℂ) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.isCompact_unitaryGroup _ _)
  let Ψ : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) → GA D V := fun u => Formalism.IndefR.Eqv.famH D V _ (hU u)
  have hg : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
      fun τ => B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹ :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_subtype_val.comp (continuous_apply τ))).matrix_mul
      continuous_const
  have hΨ : Continuous Ψ := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact GlobalTheory.HaarReal.continuous_famM.comp hg
    · have hi : Continuous fun u : (D.what₂.Tau → unitaryGroup (Fin V.rank) ℂ) =>
          fun τ => Formalism.IndefR.Eqv.ginv D V τ (B τ * (u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (B τ)⁻¹) :=
        continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
          continuous_const
      exact GlobalTheory.HaarReal.continuous_famM.comp hi
  have hsub : (GinfC V : Set (GA D V)) ⊆ Set.range Ψ := by
    intro g hg
    refine ⟨fun τ => ⟨inB (Formalism.IndefR.Eqv.thetaC D) V B g τ, hr.uni ⟨g, hg⟩ τ⟩, ?_⟩
    refine (Formalism.IndefR.Eqv.famH_unique D V _ (hU _) g hg fun τ => ?_).symm
    exact (hconj τ _).symm
  exact (isCompact_range hΨ).of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) hsub

end GlobalTheory.SeeSaw

namespace GlobalTheory.SeeSaw

theorem integral_eq_classSum : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → OntoUni (fun k : GinfC V => inB θ V B k.1) → BorelSpace (GinfC V) ∧ CompactSpace (GinfC V) ∧ (∀ g ∈ GfC V, ∀ k ∈ GinfC V, g * k = k * g) ∧ ∃ ν : Measure (GinfC V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (v : Vol V) (U : Subgroup (GA D V)) (cl : Type) [Fintype cl] (h : cl → GA D V), IsReps V U h → 0 < volLev v U ∧ (∀ a, 0 < stabOrd U (h a)) ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ κ ∈ U, ∀ g, Φ (g * κ) = Φ g) → ∫ g in v.𝓕, Φ g ∂v.μ = (volLev v U : ℂ) * ∑ a, ((stabOrd U (h a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h a * k.1) ∂ν := by
  intro D θ V B hθ hr
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  have hK : IsCompact (GinfC V : Set (GA D V)) := isCompact_ginfC_of_ontoUni D θ V B hθ hr
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.mp hK
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hcf : ∀ {a b : GA D V}, a ∈ GinfC V → b ∈ GfC V → a * b = b * a := fun ha hb =>
    Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb
  refine ⟨inferInstance, inferInstance, fun g hg k hk => (hcf hk hg).symm, ?_⟩
  let ν : Measure (GinfC V) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν :=
    ⟨by simpa using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))))⟩
  refine ⟨ν, inferInstance, inferInstance, ?_⟩
  intro v U cl _ h hU
  haveI := v.haar
  haveI : v.μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V v.μ v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hmemK : ∀ g, g ∈ K ↔ ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ := fun g => by
    rw [← SetLike.mem_coe, hKset]; rfl
  have hvol : volLev v U = (v.μ K).toReal := by
    simp only [volLev]
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hU.cpt
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      hU.opn.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho
    rw [hmemK]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  have huniq : ∀ x : GA D V, ∃! i, ∃ γ ∈ GQ V, ∃ k ∈ K, x = γ * h i * k := by
    intro x
    obtain ⟨γ, hγ, c, k, hk, κ, hκ, e⟩ := hU.dec x
    refine ⟨c, ⟨γ, hγ, k * κ, (hmemK _).2 ⟨k, hk, κ, hκ, rfl⟩, by rw [e]; group⟩, ?_⟩
    rintro c' ⟨γ', hγ', k', hk', e'⟩
    obtain ⟨k₁, hk₁, κ₁, hκ₁, rfl⟩ := (hmemK _).1 hk'
    refine (hU.uniq c c' (γ'⁻¹ * γ) (mul_mem (inv_mem hγ') hγ) (k * k₁⁻¹) (mul_mem hk (inv_mem hk₁)) (κ * κ₁⁻¹)
      (mul_mem hκ (inv_mem hκ₁)) ?_).symm
    have hc1 : k₁⁻¹ * (κ * κ₁⁻¹) = (κ * κ₁⁻¹) * k₁⁻¹ := hcf (inv_mem hk₁) (hU.le (mul_mem hκ (inv_mem hκ₁)))
    have e2 : h c' = γ'⁻¹ * x * (k₁ * κ₁)⁻¹ := by rw [e']; group
    rw [e2, e, _root_.mul_inv_rev]
    calc γ'⁻¹ * (γ * (h c * k) * κ) * (κ₁⁻¹ * k₁⁻¹) = γ'⁻¹ * γ * (h c * k) * ((κ * κ₁⁻¹) * k₁⁻¹) := by group
      _ = γ'⁻¹ * γ * (h c * k) * (k₁⁻¹ * (κ * κ₁⁻¹)) := by rw [hc1]
      _ = γ'⁻¹ * γ * (h c * (k * k₁⁻¹)) * (κ * κ₁⁻¹) := by group
  have hfin : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite := by
    intro i
    have hC : IsCompact ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V))) :=
      hKc.image ((continuous_const.mul continuous_id).mul continuous_const)
    have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have hTc : IsCompact (((↑) : GQ V → GA D V) ⁻¹' ((fun y => h i * y * (h i)⁻¹) '' (K : Set (GA D V)))) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
    refine (hTc.finite_of_discrete.image Subtype.val).subset ?_
    rintro γ ⟨hγ, hk⟩
    exact ⟨⟨γ, hγ⟩, ⟨_, hk, by group⟩, rfl⟩
  have hst : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard = stabOrd U (h i) := by
    intro i
    have hs : {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ K} =
        Subtype.val '' {γ : GQ V | ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h i = h i * k * κ} := by
      ext γ
      constructor
      · rintro ⟨hγ, hk⟩
        obtain ⟨k, hk, κ, hκ, e⟩ := (hmemK _).1 hk
        refine ⟨⟨γ, hγ⟩, ⟨k, hk, κ, hκ, ?_⟩, rfl⟩
        calc γ * h i = h i * ((h i)⁻¹ * γ * h i) := by group
          _ = h i * k * κ := by rw [e, mul_assoc]
      · rintro ⟨γ, ⟨k, hk, κ, hκ, e⟩, rfl⟩
        refine ⟨γ.2, (hmemK _).2 ⟨k, hk, κ, hκ, ?_⟩⟩
        calc (h i)⁻¹ * γ.1 * h i = (h i)⁻¹ * (γ.1 * h i) := by group
          _ = k * κ := by rw [e]; group
    rw [hs, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    rfl
  refine ⟨by rw [hvol]; exact ENNReal.toReal_pos hKpos.ne' hKfin, fun a => ?_, ?_⟩
  · rw [← hst]
    exact (Set.ncard_pos (hfin a)).mpr ⟨1, (GQ V).one_mem, by simpa using K.one_mem⟩
  intro Φ hΦc hΦl hΦr
  obtain ⟨-, he⟩ := GlobalTheory.integral_fundamentalDomain_eq_sum_doubleCoset_avg (GA D V) v.μ (GQ V) K U v.𝓕 v.fund hKo hKfin
    (GinfC V) ν (GinfC V).subtype continuous_subtype_val
    (fun k hk => by
      obtain ⟨a, ha, κ, hκ, rfl⟩ := (hmemK _).1 hk
      exact ⟨κ, hκ, ⟨a, ha⟩, hcf ha (hU.le hκ)⟩)
    (fun k hk w => (hcf w.2 (hU.le hk)).symm) cl h huniq hfin Φ hΦc hΦl hΦr
  rw [he, hvol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hst i]
  rfl

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitDatumCompletedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SBHalfAt

theorem isSBHalf_extFun_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT Ψ hΨ
  exact GlobalTheory.FinPl.CombProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ

end GlobalTheory.FinPl.SBHalfAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem isThetaFunO_sliceT :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L),
      IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.SliceModelT.isThetaFunO_sliceT_left o hf y

end GlobalTheory.FinPl.ExtZero
end


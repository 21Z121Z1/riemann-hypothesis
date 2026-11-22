import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Formalism.LocalToGlobal.Columns.ChainOneOk
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.FormalDegreeBessel.StatementIO
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterOneNe
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

def ordTop (R : Ranks) (s : ℕ) (hm : R.m = s + 2) :
    Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m) :=
  (((ordZ R s hm).sumCongr (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv).trans
    (finCongr (by have := N_m_succ R; omega))

def joinRow {E : Type} [Field E] (R : Ranks) {n : ℕ} (x' : (Fin n → E) →ₗ[E] (Fin (R.N R.m - 1 + 0) → E))
    (η : (Fin n → E) →ₗ[E] E) : (Fin n → E) →ₗ[E] (Fin (R.N R.m) → E) :=
  LinearMap.pi fun i => if h : i.1 < R.N R.m - 1 + 0 then LinearMap.proj (⟨i.1, h⟩ : Fin (R.N R.m - 1 + 0)) ∘ₗ x' else η

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_nat (n : ℕ) : IntAt P (n : E) := by simpa using IntAt.coe P (n : 𝓞 E)

theorem reduction_natCast (n : ℕ) : redP P (n : E) = (n : 𝓞 E ⧸ P.asIdeal) := by
  simpa using reduction_coe P (n : 𝓞 E)

theorem reduction_natCast_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : redP P (q : E) = 0 := by
  rw [reduction_natCast]
  simpa using Ideal.Quotient.eq_zero_iff_mem.2 hq

theorem pow_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (n : ℕ) :
    IntAt P ((q : E) ^ (n + 1)) ∧ redP P ((q : E) ^ (n + 1)) = 0 := by
  induction n with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_nat q, reduction_natCast_eq_zero hq⟩
  | succ n ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_nat q), by rw [reduction_mul ih.1 (intAt_nat q), ih.2, zero_mul]⟩

theorem valuation_one₂ (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) : LocE.vP P q (1 : E) = 0 := by
  have hI : IntAt P (1 : E) := by simpa using intAt_nat (P := P) 1
  have hU : IsUnit (redP P (1 : E)) := by
    have := reduction_natCast (P := P) 1
    rw [Nat.cast_one, Nat.cast_one] at this
    rw [this]; exact isUnit_one
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (q : E) ^ z)) := ⟨0, by rwa [zpow_zero, div_one]⟩
  have hspec : IsUnit (redP P ((1 : E) / (q : E) ^ LocE.vP P q (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨n, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P q (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (q : E) ^ (k' + 1))
    · have e : (1 : E) = (q : E) ^ (k' + 1) * ((1 : E) / (q : E) ^ (k' + 1)) := by field_simp
      have h0 : redP P (1 : E) = 0 := by
        rw [e, reduction_mul (pow_red hq k').1 hI', (pow_red hq k').2, zero_mul]
      rw [h0] at hU
      exact not_isUnit_zero hU
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, reduction_mul hI (pow_red hq k').1, (pow_red hq k').2,
      mul_zero] at hspec
    exact not_isUnit_zero hspec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

def TailTrivial (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  ∀ i, R.m ≤ i → ∀ a : X.Eˣ, IsUnit (redP P (a : X.E)) → S.μ (i + 1) (Units.map ι.toMonoidHom a) = 1

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def trunc : SymData k s κ :=
  { S with
    μ := fun j => if j ≤ s + 2 then S.μ j else 1
    tame := fun j => by
      split_ifs
      · exact S.tame j
      · exact fun _ _ => rfl }

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

def extChars : Chars (extFields X K') (onePrimes X K' π) R.m where
  psi0 := fun w => (φ : X.K →* K').compAddChar (psi0P Ch w.1)
  chi := fun j w => (Units.map (φ : X.K →* K')).comp (chiP Ch w.1 j)
  muVal := 1
  etaVal := 1

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

def extCst (π : 𝓞 X.E) : LocCst (extFields X K') (rowSG (onePrimes X K' π) sel (mu0 X.F X.E K' S₀)) where
  psi := fun _ a => φ (cst.psi P a)
  D := fun _ => 1
  sq := fun _ => z
  muq := fun j _ => φ (cst.muq j P)
  A := cst.A
  B := cst.B
  M := 1
  sharp := true

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_localElement_eq_simpleEntrySum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → psiBes ψ B.d 1 (vecB B.o B.ζ) g = (ψk (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  first | exact @GlobalTheory.LocBesChar.psiBes_isLoc | exact GlobalTheory.LocBesChar.psiBes_isLoc | (intros; apply GlobalTheory.LocBesChar.psiBes_isLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDoubleStep_linear_in_secondDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  first | exact @GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | exact GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | (intros; apply GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLinkStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDoubleStepUnfolding_of_unfoldings_and_link : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  first | exact @GlobalTheory.Unf.doubleStep_of_laws | exact GlobalTheory.Unf.doubleStep_of_laws | (intros; apply GlobalTheory.Unf.doubleStep_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  first | exact @GlobalTheory.LocMod.normalFrames_exist | exact GlobalTheory.LocMod.normalFrames_exist | (intros; apply GlobalTheory.LocMod.normalFrames_exist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HandFam

theorem star_psi_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem handBF_isQuasiFam : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ)
    (s : StepBF ψ B J) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ')
    (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ), IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  obtain ⟨hτ, -⟩ := GlobalTheory.T.besselLineLink_gram_similitude_bijective D ρ B L' ζ' hz l
  obtain ⟨hadd, hcont, hrat, heq, hsym, -⟩ :=
    GlobalTheory.T.hermitianLinkMap_additive_rational_equivariant D B.L L' J.W₀ l.τ 1 hτ (l.κ J.W₀) (fun _ => rfl)
  have hF : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (s.om₀ p Ξ) := fun p => s.weil₀.om_pres p Ξ hΞ
  have hsub := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
  refine ⟨?_, ?_, ?_⟩
  · intro h γ w
    have hr : (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)) ∈ ratMx D J.W₀.rank B.V₀.rank := by
      rw [B.o.resS_symm_apply, Matrix.zero_mul, zero_add]
      exact ratMx_mul (hrat _ (rat_mem γ)) (rat_mem _)
    obtain ⟨δ, hδ⟩ := hr
    have hs : symplOH B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)))
        ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = -(symplOH J.W₀ L' (ratW L' J.W₀ γ) w) := by
      rw [B.o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
      rw [symplOH, symplOH, hsym]
      push_cast
      ring
    have key : ∀ h₀, s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ + w))) =
        ψ (symplOH J.W₀ L' (ratW L' J.W₀ γ) w) * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      intro h₀
      have e : ((0 : WO B.A J.W₀), l.κ J.W₀ (ratW L' J.W₀ γ + w)) =
          ((0 : WO B.A J.W₀), l.κ J.W₀ (ratW L' J.W₀ γ)) + (0, l.κ J.W₀ w) := by
        rw [hadd, Prod.mk_add_mk, add_zero]
      have hq := (hF (B.o.emb (h₀, 1), h)).quasi δ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
      have hδ' : rat δ = (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)) := hδ
      rw [ratW_eq, hδ', hs, neg_neg] at hq
      rw [e, map_add, hq]
    simp only [handBF, key]
    simp_rw [mul_left_comm (φ _) (ψ _)]
    rw [integral_const_mul, star_mul', star_psi_eq s.weil₀.std]
  · have jc := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
    have hmap : Continuous fun q : GA D B.A × (GA D J.W₀ × WO J.W₀ L') =>
        ((B.o.emb (q.1, 1), q.2.1), (B.o.resS J.W₀).symm (0, l.κ J.W₀ q.2.2)) :=
      ((B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)).prodMk
        (continuous_fst.comp continuous_snd)).prodMk
        ((B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hcont.comp (continuous_snd.comp continuous_snd))))
    have hK := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D B.A B.cpt B.vA (GA D J.W₀ × WO J.W₀ L')
      (fun h₀ p => φ h₀ * s.om₀ (B.o.emb (h₀, 1), p.1) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.2)))
      ((hφ.2.comp continuous_fst).mul (jc.comp hmap)) (by
        intro γ hγ h₀ p
        have e : B.o.emb (γ * h₀, 1) = B.o.emb (γ, 1) * B.o.emb (h₀, 1) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        have hq := hsub (B.o.emb (γ, 1)) (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (B.o.emb (h₀, 1)) p.1
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.2))
        rw [one_mul] at hq
        rw [hφ.1 γ hγ h₀, e, hq, inv_one, mt_one, Matrix.one_mul]
        simp only [B.o.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, B.o.pB_emb, mt_one,
          Matrix.one_mul])
    exact continuous_star.comp hK.2.1
  · intro γ hγ h w
    have hκ := heq γ⁻¹ w
    rw [inv_inv] at hκ
    have key : ∀ h₀, s.om₀ (B.o.emb (h₀, 1), γ * h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) =
        s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (w ⬝ mt J.W₀ γ))) := by
      intro h₀
      have hq := hsub 1 (one_mem _) γ hγ (B.o.emb (h₀, 1)) h ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
      rw [one_mul] at hq
      rw [hq, mt_one, Matrix.mul_one, hκ]
      simp only [B.o.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
    simp only [handBF, key]

end GlobalTheory.HandFam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSphericalStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalUnique.eq_mul_zonalInt | exact GlobalTheory.ZonalUnique.eq_mul_zonalInt | (intros; apply GlobalTheory.ZonalUnique.eq_mul_zonalInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfTrivialAtPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  first | exact @GlobalTheory.fixes_latV_of_mem_grpOff | exact GlobalTheory.fixes_latV_of_mem_grpOff | (intros; apply GlobalTheory.fixes_latV_of_mem_grpOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelBoundAtEmbeddingAnyLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m → ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu)) (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' → ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j) (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) L fr L' fr' Ξ) (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z))) (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1))  := by
  first | exact @GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp | exact GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp | (intros; apply GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjSplitLocalModelBySupportedPair
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def conjH (gk : GL Y' k) (hk : GL Y k) : Matrix Y Y' k ≃ₜ Matrix Y Y' k where
  toFun x := (hk⁻¹).val * x * gk.val
  invFun x := hk.val * x * (gk⁻¹).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def twist (c : ℂ) (gk : GL Y' k) (hk : GL Y k) : SB (Matrix Y Y' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => c * Φ.1 ((hk⁻¹).val * x * gk.val),
    (SB _).smul_mem c (show Φ.1 ∘ conjH gk hk ∈ SB _ from ⟨Φ.2.1.comp_continuous (conjH gk hk).continuous,
      Φ.2.2.comp_homeomorph (conjH gk hk)⟩)⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' a Φ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem twist_apply (c : ℂ) (gk : GL Y' k) (hk : GL Y k) (Φ : SB (Matrix Y Y' k)) (x) :
    (twist c gk hk Φ).1 x = c * Φ.1 ((hk⁻¹).val * x * gk.val) := rfl

variable {D : D7} (p : Place D k)

theorem mt_inv_mul' {S : HSp D} (g : GA D S) : mt S g⁻¹ * mt S g = 1 := by
  rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
  simp [Formalism.L2.Theta.mt]

theorem actO_up {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {g : GA D S} {gk : GL Y' k}
    {h : GA D T} {hk : GL Y k} (hg : p.IsLoc FS g gk) (hh : p.IsLoc FT h hk) (x : Matrix Y Y' k) :
    actO S T g h (p.up FS FT x) = p.up FS FT (hk.val * x * (gk⁻¹).val) := by
  have h1 : IsHalf p.e (actO S T g h (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO g h (Witness.up_half p FS FT x)
  rw [← Witness.up_down p FS FT h1]
  congr 1
  set M := (mt S g⁻¹).map p.π with hMdef
  have hM : M * (FS.β * gk.val * FS.γ) = 1 := by
    rw [← hg.2, hMdef, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : FS.γ * (M * FS.β) * gk.val = 1 := by
    have : FS.γ * (M * (FS.β * gk.val * FS.γ)) * FS.β = 1 := by rw [hM, Matrix.mul_one, FS.γβ]
    rw [← this]
    simp only [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hN : FS.γ * (M * FS.β) = (gk⁻¹).val := by
    calc FS.γ * (M * FS.β) = FS.γ * (M * FS.β) * gk.val * (gk⁻¹).val := by
          rw [Matrix.mul_assoc (FS.γ * (M * FS.β)), Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e1, Matrix.one_mul]
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hh.2, hu, ← hMdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, hN]

end GlobalTheory.LocTwist

namespace GlobalTheory.LocTwist

theorem conj_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → ∃ T₂ : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ), p.IsModel ψ FS FT T₂ ∧ ∀ Φ Φ' : SB (Matrix Y Y' k), Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 → T₂ Φ = ω (g⁻¹, h⁻¹) (Tm Φ') := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT Y Y' _ _ _ _ FS FT Tm hm g gk h hk hg hh
  set c : ℂ := (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) *
    ((μS⁻¹ (Matrix.GeneralLinearGroup.det gk) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det hk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-(Fintype.card Y' : ℝ) / 2) : ℝ) : ℂ)) with hc
  let L := LocTwist.twist c gk hk
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (g⁻¹, h⁻¹)
  have hA := LocTwist.actO_up p FS FT hg hh
  have hback : ∀ z, actO S T g⁻¹ h⁻¹ (p.up FS FT (hk.val * z * (gk⁻¹).val)) = p.up FS FT z := fun z => by
    rw [← hA, GlobalTheory.SplitHecke.actO_inv_actO]
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun x Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + hk.val * x * (gk⁻¹).val) := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      congr 2
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc ((hk⁻¹).val) hk.val, Units.inv_mul, Matrix.one_mul]
    have h2 := hm.trans _ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hback]
  · set y' := actO S T g h y
    have hy' : IsHalf (cA D p.e) y' := GlobalTheory.SplitHecke.isHalf_actO g h hy
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y') * (L Φ).1 t := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      have hu : p.up FS FT ((hk⁻¹).val * t * gk.val) = actO S T g⁻¹ h⁻¹ (p.up FS FT t) := by
        rw [← hback ((hk⁻¹).val * t * gk.val)]
        congr 2
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hs : symplO S T (p.up FS FT ((hk⁻¹).val * t * gk.val)) y = symplO S T (p.up FS FT t) y' := by
        rw [hu, ← GlobalTheory.SplitHecke.symplO_actO S T g⁻¹ h⁻¹ (p.up FS FT t) y', GlobalTheory.SplitHecke.actO_inv_actO]
      rw [hs]; ring
    have h2 := hm.modul y' hy' (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), GlobalTheory.SplitHecke.actO_inv_actO]
  · have : Φ' = L Φ := by
      apply Subtype.ext; funext t
      rw [e]
      simp only [L, LocTwist.twist_apply, Pi.smul_apply, smul_eq_mul, om, hc]
      ring
    rw [this]; rfl

end GlobalTheory.LocTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverFactoringRepresentationUnitaryGroupDictionaStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverFactoringRepresentation_unitaryGroup_dictionary : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (U : URep T) (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)), BlockOrd e ε → Factors U e σ → IsURepOn (UJset ε) σ ∧ (IrrU U → IsIrredOn (UJset ε) σ) ∧ (∀ x, KFin T U.π x ↔ IsKFin ε σ x) ∧ (∀ Y, Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y)) ∧ (∀ Y ∈ upq p q, ∀ t : ℝ, U.π (T.expt (t • Y)) = σ (NormedSpace.exp (t • Matrix.reindex e e Y))) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∃ x ∈ T.Kset, U.π x = σ k := by
  first | exact @GlobalTheory.RealPar.CoverFactor.dictionary | exact GlobalTheory.RealPar.CoverFactor.dictionary | (intros; apply GlobalTheory.RealPar.CoverFactor.dictionary <;> assumption)
end


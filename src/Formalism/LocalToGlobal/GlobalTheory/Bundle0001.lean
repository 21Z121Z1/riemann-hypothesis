import Formalism.SharpRestriction.GlobalSchurBounds.JointsL
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.HermitianColumns.Bundle0003
import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionCompatibleMeanSquare
import Formalism.SizeWindowBrackets.Bundle0003
import Formalism.SizeWindowBrackets.ChainSlopeWindows.Bundle0003
import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied
import Formalism.SizeWindowBrackets.ChainSlopeWindows.Bundle0002
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBridge
import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfFlags
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.FrobeniusOrbits NumberField

theorem sigma_fix_K {R : Ranks} (H : Host R) (g : R.Psi) {x : H.E} (hx : x ∈ H.K) :
    H.sigmaOf (g : R.GG) x = x := by
  have hg : H.galE (H.sigmaOf (g : R.GG)) = g :=
    (H.gal).apply_symm_apply _
  have hb : H.sigmaOf (g : R.GG) (H.sqd) = H.sqd :=
    (H.toHostAx.galE_mem_Psi_iff _).1 (by rw [hg]; exact g.2)
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hb
  | algebraMap r => exact AlgEquiv.commutes _ r
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | inv y _ hy => rw [map_inv₀, hy]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

theorem tauLL_of_K (D : D7) (τ : D.what₂.Tau) {x : D.host.E} (hx : x ∈ D.host.K) : tauLL D τ x = D.embE x := by
  unfold tauLL
  rw [sigma_fix_K D.host (D.eTau τ) hx]

def AdmBRest (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m →
    ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
      (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
      (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
      ∀ c : (D.mem u).C.cls i, ∃ Ln : SDLat D.host.E (D.R.N i),
        (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
          y = a + D.host.conj (π : D.host.E) • b) ∧
        (QuotientGroup.mk (D.detCls u i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln

theorem base_lattice_convention_of_flags {D : D7} (X : ErrX D) (hs : SeenDef D X) (u : D.what₂.Word)
    (h : AdmBRest D u (X.piT u)) : product_first_zeroth_parts.admB D u := by
  refine ⟨X.piT u, X.piT_K u, X.piT_norm u, fun w hw => ?_, h⟩
  rw [hs u w hw]
  constructor
  · intro h1
    have := h1 (D.eTau.symm 1)
    rwa [tauLL_of_K D _ (X.piT_K u)] at this
  · intro h1 τ
    rwa [tauLL_of_K D _ (X.piT_K u)]

end Formalism.L2.GlobalTheoryTheory

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.ConclusionsOfPrimeNumberTheoremAP
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2c

open Formalism.LFunctionChainParameters Formalism.HermitianLattices Formalism.L2.GlobalTheoryTheory.MergeGL2 Formalism.L2.GlobalTheoryTheory.MergeGL2b

def AnalyticEndUncond : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x)

def AnalyticEndUncondTied : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d

def Chain6AtUncond : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

section Part2

open Formalism Formalism.D5 Formalism.HN Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7

def CoreAt7 (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    Inputs6d (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def CoreAt7' (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    (∀ u0, Fam6.GainIn (Fc u0).toFam (inertPs (hostData e q d) N) (Lp u0).cl (TT.card : ℝ) (aTx x ε)) ∧
    Inputs6d' (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def Chain6At7Uncond : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt7 (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def Chain6At7'Uncond : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt7' (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def PublishedFormSixPair : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          CoreAt (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

def RHConclusionsOfPrimePairCore : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          CoreAt7 (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

def RHConclusionsOfPrimePairCore' : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          CoreAt7' (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

end Part2

section Proofs

open Formalism Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain7 Formalism.LFunctionChainParameters.LTop7 Formalism.LFunctionChainParameters.LBr2

end Proofs

section Part5

example : PrimeNumberTheoremConsequences.PNTAPRelW := Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak

end Part5

end Formalism.L2.GlobalTheoryTheory.MergeGL2c
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem hermitian_form_H1_eq (Λ : AddSubgroup ℂ) (z w : ℂ) : GL3Theta.hf1 Λ z w = H1 Λ z w := rfl

theorem lattice_character_eq (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : GL3Theta.al1 d Λ x = al1 d Λ x := rfl

theorem taylorLogMetric_U1_eq_U1 (Λ : AddSubgroup ℂ) (x : ℂ) (G : ℂ → ℂ) : TaylorLogMetric.U1 Λ x G = U1 Λ x G := by
  funext z
  simp only [TaylorLogMetric.U1, U1, H1]
  congr 2
  ring

theorem is_theta_zero_iff (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.IsTheta0 d Λ G ↔ IsTheta0 d Λ G := by
  unfold GL3Theta.IsTheta0 IsTheta0
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    have hx' := h2 x hx z
    rwa [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z] at hx'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    rw [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z]
    exact h2 x hx z

theorem normSq_lattice_function_eq (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.normSq1 Λ G = normSq1 Λ G := rfl

theorem theta_power_of_first_layer {D : D7} {δ : ℂ} {e : TaylorLogMetric.FamE D} (h : GL3Theta.thPow D D.host.ccK δ e) : ThPow D δ e := by
  intro M _ hD N N' L L' hA hC ρ G hG
  have h2 := (h.2 M hD ρ).2 G ((is_theta_zero_iff _ _ _).2 hG) N N' L L' hA hC
  exact h2

end Formalism.L2.GlobalTheoryTheory

end
end


import Formalism.SizeWindowBrackets.ErrorFormsEventualPowerBound
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.SizeWindowBrackets.PowerBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable

-- bundled from Formalism.SizeWindowBrackets.FixedEpsilonConcreteGrowthBound
section
open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LTop7

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LErr7
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6

def cTop7 (eD eL : ℝ) : ℝ := max (eD + 1) (max (eL + 2) 3)

def CTop7Values : Prop :=
  cTop7 2 0 = 3 ∧
  (∀ eD eL : ℝ, eD ≤ 2 → eL ≤ 1 → cTop7 eD eL = 3) ∧
  (∀ eD eL : ℝ, 3 ≤ cTop7 eD eL) ∧
  (∀ eD eL eD' eL' : ℝ, eD ≤ eD' → eL ≤ eL' → cTop7 eD eL ≤ cTop7 eD' eL') ∧
  (∀ C : Consts, CErr7 C = cTop7 C.eDiv C.eLoss) ∧
  (∀ eD eL : ℝ, 0 ≤ eD → 0 ≤ eL → cTop7 eD eL ≤ eD + eL + 3)

def CoreTopEachSized7 : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    Ident Dd D N ell TT a w eT eP → SizeData₂ Dd C Xpp → ErrWindows Dd C Xpp eK K → BNBounds Dd T2 →
    LargeX Dd.x Dd.ε K C.cHH eK →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤ Dd.Main u0
      + Dd.x ^ (CErr7 C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a

def PropTL7 : Prop :=
  ∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)),
    Ident Dd D N ell TT a w eT eP → SizeData₂ Dd C Xpp → ErrWindows Dd C Xpp eK K → BNBounds Dd T2 →
    LargeX Dd.x Dd.ε K C.cHH eK → C.eDiv ≤ 2 → C.eLoss ≤ 1 →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤ Dd.Main u0
      + Dd.x ^ (3 * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a

section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

def TopOfInputs2Sized7 : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ), Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL → LargeX G.x G.ε K C.cHH eK →
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j))
      ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Main u0
        + G.x ^ (CErr7 C * G.ε)
          * errorBracketSizeWindows G.x G.ε (Fintype.card H) TT.card T2.card m (bTx G.x G.ε) G.k (aTx G.x G.ε)

end DataT

def ChainTop7 : Prop :=
  ∀ Cd eD eL ε x : ℝ, ChainInputs Cd eD eL ε x → ReducedGrowthInequalityDataExists Cd (cTop7 eD eL) ε x

def ChainAt7 : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧
    ∀ eD eL ε x : ℝ, ChainInputs Cd eD eL ε x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)

def ExponentSevenBoundLeEarlierBound : Prop :=
  ∀ eD eL ε x : ℝ, 0 ≤ eD → 0 ≤ eL → 0 ≤ ε → 1 ≤ x →
    x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε) ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)

def ChainCoreMono : Prop :=
  ∀ eD eL eD' eL' K cHH eK CL ε x : ℝ, eD ≤ eD' → eL ≤ eL' →
    ChainCore eD eL K cHH eK CL ε x → ChainCore eD' eL' K cHH eK CL ε x

def FixedEpsilonGrowthBound : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)

def ChainEpsHalfPlane7 : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∀ s : ℂ, (1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε < s.re → riemannZeta s ≠ 0

def Core6ToCore : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ eD eL CL x : ℝ, x₁ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
      ChainCore eD eL K cHH eK CL ε x

def Core6'ToCore : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ eD eL CL x : ℝ, x₁ ≤ x → Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x →
      ChainCore eD eL K cHH eK CL ε x

def Chain6AtTop7 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)

def Chain6At'Top7 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)

def GrowthBoundAndRiemannHypothesis : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + 6 * ε)) ∧
  (∀ s : ℂ, (1 : ℝ) / 2 < s.re → riemannZeta s ≠ 0) ∧
  RiemannHypothesis

def RiemannHypothesisOfEventualGrowthBound : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + 6 * ε)) → GrowthBoundAndRiemannHypothesis

def GrowthBoundSmallExponents : Prop :=
  ∀ eD eL ε : ℝ, eD ≤ 2 → eL ≤ 1 →
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + 6 * ε)

def RiemannHypothesisOfChainCore : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
    ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCore 2 0 K cHH eK CL ε x) → GrowthBoundAndRiemannHypothesis

def FixedEpsilonConcreteGrowthBound : Prop :=
  ∀ eD eL ε : ℝ,
    (∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2Core eD eL K cHH eK CL ε x) →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Gz x ≤ x ^ ((1 : ℝ) / 2 + (cTop7 eD eL + 3) * ε)

def RiemannHypothesisOfConcreteChain : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
    ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain2Core 2 0 K cHH eK CL ε x) → GrowthBoundAndRiemannHypothesis

def RiemannHypothesisOfComposedChain : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core A Cord 2 0 K cHH eK CL eW KW ε x) → GrowthBoundAndRiemannHypothesis)

def RiemannHypothesisOfComposedChain' : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core' A Cord 2 0 K cHH eK CL eW KW ε x) → GrowthBoundAndRiemannHypothesis)

def ChainSizesModelEv7 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ChainCoreNoAnalytic 2 0 1 1 2 ε x

end Formalism.LFunctionChainParameters.LTop7
end
end

-- bundled from Formalism.SizeWindowBrackets.Losses5OfLossHypD
section
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain7

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6

section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}

abbrev PlAllD (Fm : ∀ u0, Fam (W u0) m) : Type := Σ u0 : H, slopeLatticeData.FinPl (Fm u0).K

def plEmbD (Fm : ∀ u0, Fam (W u0) m) (u0 : H) : slopeLatticeData.FinPl (Fm u0).K ↪ PlAllD Fm :=
  Function.Embedding.sigmaMk (β := fun u0 => slopeLatticeData.FinPl (Fm u0).K) u0

def ldOfD (D : ArithData H) (N : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m) (u0 : H) :
    PrimeWindowSizeBounds.LD (PlAllD Fm) (Fin m) H where
  W := (Fm u0).S.map (plEmbD Fm u0)
  below := fun z => prBelow z.2
  l := fun z => lE z.2
  cl := (Lp u0).cl
  TTp := (Lp u0).TTp
  Iex := fun _ _ p => (Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p))
  at_ := a
  wz := fun j t p i => w u0 j (partner t (i • D.frob p))
  Id := fun _ _ => Finset.Icc 1 N
  wd := fun j t i => w u0 j (partner t (gD D i))
  gainW := fun j z => (Fm z.1).gain j z.2
  tauW := fun z => (Fm z.1).tauR z.2
  gain := (Lp u0).gainP
  tau := (Lp u0).tauP
  lo := (Lp u0).lo
  fl := (Lp u0).fl
  L₁ := (Lp u0).L₁

def LdIdentD : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (N : ℕ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m) (u0 : H),
    (ldOfD D N a w Fm Lp u0).ASK D.d (inertPs D N) Finset.univ TT
      = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j) ∧
    (ldOfD D N a w Fm Lp u0).Ga Finset.univ = (Fm u0).Ga

def LossHypD (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ) : Prop :=
  P.x = G.x ∧ P.ε = G.ε ∧ P.k = G.k ∧ P.d = D.d ∧ P.Cord = Cord ∧
  SmallOrderPrimeLosses.WindowsD P eW KW ∧
  SmallOrderPrimeLosses.PrimeClassLossHypotheses P (inertPs D N) cand PR (Finset.univ : Finset (Fin m)) TT BAD Sig
    (fun u0 p => (Fm u0).iop p) (ldOfD D N a w Fm Lp) ∧
  (∀ u0, (∀ p ∈ (Fm u0).Pr, p ∉ cand → (Fm u0).iop p = 0) ∧ ∀ p ∈ cand, 0 ≤ (Fm u0).iop p) ∧
  3 * P.C + 13 ≤ C.cLoss ∧ 0 ≤ C.eLoss

variable [∀ u0, Fintype (W u0)]

def LossesOfD : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ),
    LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW → 1 ≤ G.x →
    SmallOrderPrimeLosses.ExcessAndPrimeLogSumUnitBounds P (inertPs D N) cand (Finset.univ : Finset (Fin m)) TT (fun u0 p => (Fm u0).iop p)
      (ldOfD D N a w Fm Lp) →
    LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C

end Loss

def Losses5OfLossHypD : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
      (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (G : Glob) (C : Consts) (N : ℕ)
      (TT T2 : Finset H) (a : H → ℝ)
      (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
      (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ),
      G.ε = ε → x₁ ≤ G.x → LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW →
      LossBounds (mkData G C.cHH D ell N TT T2 a w Fm) C

def Chain6Core7 (A Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    Inputs6d (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def Core7ToCore2 : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ c' : ℝ, 0 < c' → HostAn c' → ∀ ε A K cHH eK eW KW : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ eD eL CL x : ℝ, x₁ ≤ x →
      Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x → Chain2Core eD eL K cHH eK CL ε x

def Chain6_7 : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis

def Chain6At7 : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)

def Chain6_7Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis

def Chain6At7Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)

section Comp
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}

def LossHypDOfEmpty : Prop :=
  ∀ (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → Unit → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (BAD : ℕ → H → Prop) (Sig : ℕ → Unit → ℝ) (Cord eW KW : ℝ), 0 ≤ G.x →
    LossHyp (W := fun _ => W) D G C N TT (fun _ : Unit => a) (fun _ => w) (fun _ => Fm) Lp P (fun _ => 1) ∅ ∅ BAD Sig
      Cord eW KW →
    LossHypD D G C N TT a w Fm (fun u0 => Lp u0 ()) P ∅ ∅ BAD (fun p => Sig p ()) Cord eW KW

end Comp

def LossCompletionD : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (_ : InfinitePlace K)
    (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H), HostFacts D →
    ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (m : ℕ) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (G : Glob) (C : Consts) (cT : ℝ) (T : H → ℕ)
    (P : PrimeWindowSizeBounds.Par) (Cord eW KW : ℝ),
    CompletionSigns G C cT m → LChain2.LevelWindow G C w T → TopAtLevel D ell G C N TT T2 a w T →
    LossSide D G C N TT a w P Cord eW KW →
    ∃ (Mw : ℕ) (Fm : H → Fam (Fin Mw) m) (Lp : H → LossP H m),
      0 < Mw ∧ (Mw : ℝ) < G.x ^ C.cHH + 1 ∧ (∀ u0 u, (Fm u0).T u = T u0) ∧
      InputsL D ell G C cT N TT T2 a w Fm ∧
      LossHypD (W := fun _ => Fin Mw) D G C N TT a w Fm Lp P ∅ ∅ (fun _ _ => False) (fun _ => 0) Cord eW KW

section Clr
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} {m : ℕ}

def LossHypDClr : Prop :=
  ∀ (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW β s₀ : ℝ),
    LossHypD D G C N TT a w Fm Lp P cand PR BAD Sig Cord eW KW ↔
      LossHypD D G C N TT a w Fm Lp { P with β := β, s₀ := s₀ } cand PR BAD Sig Cord eW KW

end Clr

def Chain6Core7' (A Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    (∀ u0, Fam6.GainIn (Fc u0).toFam (inertPs (hostData e q d) N) (Lp u0).cl (TT.card : ℝ) (aTx x ε)) ∧
    Inputs6d' (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def Core7'ToCore7 : Prop :=
  ∀ ε eW KW : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₁ : ℝ, ∀ A Cord eD eL K cHH eK CL x : ℝ, x₁ ≤ x →
    Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x → Chain6Core7 A Cord eD eL K cHH eK CL eW KW ε x

def Chain6_7' : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis

def Chain6At7' : Prop :=
  Chi8NoRealZero → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)

def Chain6_7'Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ A K cHH eK CL eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis

def Chain6At7'Closed : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK CL eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → Chain6Core7' A Cord eD eL K cHH eK CL eW KW ε x →
      Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)

def Chain6Core7OfTop : Prop :=
  ∀ (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts), 2 ≤ C0S → TopIn6 A Cord K eK CL eW KW ε x C0S C →
    Chain6Core7 A Cord C.eDiv C.eLoss K C.cHH eK CL eW KW ε x

def Chain6Core7'OfTop : Prop :=
  ∀ (A Cord K eK CL eW KW ε x C0S : ℝ) (C : Consts), 3 ≤ C0S → TopIn6 A Cord K eK CL eW KW ε x C0S C →
    Chain6Core7' A Cord C.eDiv C.eLoss K C.cHH eK CL eW KW ε x

end Formalism.LFunctionChainParameters.LChain7
end
end


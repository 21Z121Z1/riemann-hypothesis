import Formalism.PieriBlockIdeals.Bundle0001
import Formalism.PieriBlockIdeals.Bundle0002
import Formalism.RankGapBounds.Bundle0003
import Formalism.RankGapBounds.Bundle0001

-- bundled from Formalism.PieriBlockIdeals.JointCW5
section
noncomputable section

namespace Formalism.CohomologicalDescent

open Formalism.RankGapBounds.ChebyshevFactorialBounds

def JointCW5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (τ : ι) (l : ℕ), l.Prime → τ ∈ D.T2 → D.Params → D.h < l ^ 2 →
    ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * (((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)) + (D.ecl τ l : ℝ) +
        labelLHS l D.k D.t (D.depth τ l : ℝ) (D.xlo τ) (D.xhi τ) (D.maxB τ) ≤
      Cor.coefficientBoundTau D τ l

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.JointTheoremALoc
section
noncomputable section

open TensorProduct

namespace Formalism.CohomologicalDescent

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization

def exactExp {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) : ℕ := sInf {e : ℕ | LatIncl l B e}

def JointTheoremA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k),
    (∀ i, ∃ e, LatIncl l (B i) e) →
    (∀ f ∈ AMFK k Γ K ρK, l ^ (∑ i, exactExp l (B i)) • f ∈ formsIn Γ K ρK (tensSub B)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK k Γ K ρK, l ^ J • f ∈ formsIn Γ K ρK (tensSub B)} ≤
      ∑ i, exactExp l (B i)

def JointTheoremALoc : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k)
    (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ρK)]
    [IsScalarTower k T (AMFK k Γ K ρK)] (S : Submonoid T),
    (∀ i, ∃ e, LatIncl l (B i) e) →
    (∀ y : LocalizedModule S (AMFK k Γ K ρK),
        (algebraMap k T l) ^ (∑ i, exactExp l (B i)) • y ∈
          locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK k Γ K ρK),
        (algebraMap k T l) ^ J • y ∈
          locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}} ≤
      ∑ i, exactExp l (B i)

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.LemmaWAssembled
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

structure WData (ι : Type) (t n : ℕ) (F : Type) [Field F] where
  a : F
  Θ : ι → Matrix (Fin n) (Fin n) F
  Φ : ι → Matrix (Fin n) (Fin n) (PowerSeries F)
  b : Fin n → ℕ
  pos : Fin t → Fin n

def WProps {ι : Type} [Fintype ι] {t n : ℕ} {F : Type} [Field F] (W : WData ι t n F)
    (σ : Equiv.Perm ι) (l : ℕ) (U' : ι → Fin n → ℤ) (bot : ι → ℤ) (kap : ι → Fin t → ℤ)
    (c : ι → ℕ) : Prop :=
  W.a ≠ 0 ∧ Function.Injective W.pos ∧ (∀ s j, W.b j = W.b (W.pos s) → j = W.pos s) ∧
  (∀ i, (W.Θ i).BlockTriangular W.b) ∧
  (∀ i, (W.Θ i).charpoly = ∏ u, (Polynomial.X - Polynomial.C (-W.a * ((U' i u : ℤ) : F)))) ∧
  (∀ i s, W.Θ i (W.pos s) (W.pos s) = -W.a * ((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ) : F)) ∧
  (∀ i, (W.Φ i).BlockTriangular W.b) ∧
  (∀ i s, ∃ u : (PowerSeries F)ˣ, W.Φ i (W.pos s) (W.pos s) =
    (u : PowerSeries F) *
      PowerSeries.X ^ ((l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s).toNat) ∧
  (∀ i, (PowerSeries.X : PowerSeries F) ^ c i ∣ ((W.Φ i).submatrix W.pos W.pos).det)

def LemmaWAssembled : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t n F) (U' : ι → Fin n → ℤ) (bot : ι → ℤ) (kap : ι → Fin t → ℤ) (c : ι → ℕ),
    l.Prime → WProps W σ l U' bot kap c →
    (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    (∀ i s, ((l : ℤ) - 1) * |kap i s| ≤ (h : ℤ)) ∧
    (∀ i, Multiset.map (fun s : Fin t => ((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ) : ZMod l))
        Finset.univ.val ≤ Multiset.map (fun u => ((U' i u : ℤ) : ZMod l)) Finset.univ.val) ∧
    (∀ i, (c i : ℤ) ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s))

def WEFull : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t (k + j + t + q) F) (U U' : ι → Fin (k + j + t + q) → ℤ) (bot cst : ι → ℤ)
    (kap : ι → Fin t → ℤ) (c : ι → ℕ) (τ : ι),
    l.Prime → t + 2 * (h / (l - 1)) < l →
    WProps W σ l U' bot kap c →
    (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (bot i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    (∀ i, StrictAnti (U i)) → (∀ i, StrictAnti (U' i)) →
    (∀ i (s : Fin t), ∃ a, U i a = bot i + ((s : ℕ) : ℤ)) →
    (∀ i, (∏ a, (Polynomial.X + Polynomial.C (((U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' i a + cst i : ℤ)) : F))) →
    (∀ a, 0 ≤ U τ a) → (∀ a, 0 ≤ U' τ a ∧ U' τ a ≤ (h : ℤ)) → ∑ a, U τ a = ∑ a, U' τ a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U τ a = bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (c τ : ℤ) = ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      U' τ a →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l (bot (σ τ)) t (h / (l - 1)) (Finset.univ.image (U (σ τ))) : ℤ) +
          (mwCount l (bot τ) t (h / (l - 1)) (Finset.univ.image (U τ)) : ℤ)) *
          ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.StatementJ
section
open Finset

namespace Formalism.CohomologicalDescent.Joint

open Formalism.RankGapBounds.ChebyshevFactorialBounds Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.Cor

noncomputable section

structure Weights {ι : Type} (D : Data ι) where

  U : ι → Fin D.Nr → ℤ

  anti : ∀ τ, StrictAnti (U τ)

  inRange : ∀ τ a, 0 ≤ U τ a ∧ U τ a ≤ (D.h : ℤ)

  k_le : D.k ≤ D.Nr

  cloudIn : ∀ τ ∈ D.T2, ∀ a : Fin D.Nr, (a : ℕ) < D.k → D.xlo τ ≤ U τ a ∧ U τ a ≤ D.xhi τ

  cloudWidth : ∀ τ ∈ D.T2, D.xhi τ - D.xlo τ ≤ (D.S : ℤ)

  restLo : ι → ℤ

  restIn : ∀ τ ∈ D.T2, ∀ a : Fin D.Nr, D.k ≤ (a : ℕ) →
    restLo τ ≤ U τ a ∧ U τ a ≤ restLo τ + (D.eta' : ℤ)

  Wd : ℕ

  thinLo : ι → ℤ

  thinIn : ∀ τ, τ ∉ D.T2 → ∀ a : Fin D.Nr, thinLo τ ≤ U τ a ∧ U τ a ≤ thinLo τ + (Wd : ℤ)

  thinWidth : Wd + D.Nr ≤ D.Wthin

def Weights.cloud {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Fin D.k → ℤ :=
  fun a => W.U τ (Fin.castLE W.k_le a)

def Weights.rest {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Fin (D.Nr - D.k) → ℤ :=
  fun a => W.U τ ⟨D.k + (a : ℕ), by have := a.isLt; have := W.k_le; omega⟩

def Weights.set {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Finset ℤ :=
  Finset.univ.image (W.U τ)

def LemmaAInputs {ι : Type} {D : Data ι} (W : Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    (∀ τ, D.ex τ l ≤ eExp (W.U τ) l) ∧
    (∀ τ ∈ D.T2, D.ecl τ l ≤ eExp (W.cloud τ) l ∧ D.erest τ l ≤ eExp (W.rest τ) l)

structure Windows {ι : Type} (D : Data ι) (W : Weights D) where
  minB : ι → ℤ

  maxB_eq : ∀ τ, D.maxB τ = minB τ + (D.t : ℤ) - 1
  UF : ι → ℕ → Fin D.Nr → ℤ
  minBF : ι → ℕ → ℤ
  mw_eq : ∀ τ l, D.mw τ l = Formalism.CohomologicalDescent.mwCount l (minB τ) D.t (D.kap l) (W.set τ)
  mwF_eq : ∀ τ l, D.mwF τ l =
    Formalism.CohomologicalDescent.mwCount l (minBF τ l) D.t (D.kap l) (Finset.univ.image (UF τ l))

def SepFrom (l : ℕ) (b : ℤ) (t κ : ℕ) (u : ℤ) : Prop :=
  ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
    (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)

def Separation {ι : Type} {D : Data ι} {W : Weights D} (B : Windows D W) : Prop :=
  ∀ l : ℕ, l.Prime → D.lJ < (l : ℝ) → l ∉ D.Bad → l ∉ D.Exc → ∀ τ : ι,
    (∀ a : Fin D.Nr, W.U τ a ∉ Finset.Icc (B.minB τ) (B.minB τ + D.t - 1) →
      SepFrom l (B.minB τ) D.t (D.kap l) (W.U τ a)) ∧
    (∀ a : Fin D.Nr, B.UF τ l a ∉ Finset.Icc (B.minBF τ l) (B.minBF τ l + D.t - 1) →
      SepFrom l (B.minBF τ l) D.t (D.kap l) (B.UF τ l a))

def JointExactExpTotal : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → D.ExactExpTotal

def JointExactExpStop5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → ExactExpStop5 D

def JointExactExpStopH : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W →
    ∀ (τ : ι) (l : ℕ), l.Prime → l ∉ D.Exc → D.h < l → D.ex τ l = 0

def JointThinStop5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → ThinStop5 D

def JointCloudBound : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → D.CloudBound

def JointRestBound : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → D.RestBound

def JointNoWindow : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D) (B : Windows D W), Separation B → D.NoWindowResidue

def JointInputs5 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (W : Weights D) (B : Windows D W),
    LemmaAInputs W → Separation B → D.ExcCost → D.SumExactBound → D.CloudRestCut →
      BlockIdealBound5 D → Inputs5 D

def Corollary5J : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (W : Weights D) (B : Windows D W),
      LemmaAInputs W → Separation B → D.ExcCost → D.SumExactBound → D.CloudRestCut →
        BlockIdealBound5 D → D.Params →
        ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ rhs5 D C

def ESplit : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D) (τ : ι) (l : ℕ),
    eExp (W.U τ) l = eExp (W.cloud τ) l + eExp (W.rest τ) l
      + ∑ a : Fin D.k, ∑ b : Fin (D.Nr - D.k),
          Formalism.RankGapBounds.JumpSetsAlt.maxVal l (W.cloud τ a - W.rest τ b - 1).toNat

def LemmaAFull {ι : Type} {D : Data ι} (W : Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ, D.ex τ l ≤ eExp (W.U τ) l

def FormulaParts {ι : Type} {D : Data ι} (W : Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ ∈ D.T2,
    D.ecl τ l = eExp (W.cloud τ) l ∧ D.erest τ l = eExp (W.rest τ) l

def JointCloudRestCutE : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAFull W → FormulaParts W → D.CloudRestCut

def Corollary5E : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (W : Weights D) (B : Windows D W),
      LemmaAFull W → FormulaParts W → Separation B → D.ExcCost → D.SumExactBound →
        BlockIdealBound5 D → D.Params →
        ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ rhs5 D C

end

end Formalism.CohomologicalDescent.Joint
end


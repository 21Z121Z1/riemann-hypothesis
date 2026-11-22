import Formalism.GradedWeylDivisibility.StatementA
import Formalism.RankGapBounds.Bundle0001
import Formalism.RankGapBounds.Bundle0003
import Formalism.PieriBlockIdeals.Bundle0001
import Formalism.PieriBlockIdeals.Bundle0003

-- bundled from Formalism.PieriBlockIdeals.StatementLA
section
open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LA

open Formalism.GradedWeylDivisibility

def lamU (r n : ℕ) (ν : Fin n → ℕ) : Fin r → ℤ :=
  fun a => (rowNu (r := r) ν a : ℤ) + ((r : ℤ) - 1 - (a.val : ℤ))

def InclZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) : Prop :=
  ∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((m * l ^ e : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν

def LemmaAZ : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def LemmaAR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ l : ℕ, l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    ∀ x ∈ dualWeyl R r n ν, (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l • x ∈ weyl R r n hn ν

def LemmaAROfZ : Prop := LemmaAZ → LemmaAR

def LemmaAZOfR : Prop := LemmaAR → LemmaAZ

def InclZIffR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l : ℕ), l.Prime →
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    (∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ),
      InclZ r n hn ν l e ↔ ∀ x ∈ dualWeyl R r n ν, (l : R) ^ e • x ∈ weyl R r n hn ν

def exZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l : ℕ) : ℕ := sInf {e : ℕ | InclZ r n hn ν l e}

def MaxValEq : Prop := ∀ l n : ℕ, Formalism.CohomologicalDescent.maxVal l n = Formalism.RankGapBounds.JumpSetsAlt.maxVal l n

def LamUStrictAnti : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ), Antitone ν → StrictAnti (lamU r n ν)

def InclZMono : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e e' : ℕ), e ≤ e' →
    InclZ r n hn ν l e → InclZ r n hn ν l e'

def ExZSpec : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (exZ r n hn ν l)

def ExactExponentRankTwo : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ) (l : ℕ),
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 n ν) l =
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l (rowNu (r := 2) ν 0 - rowNu (r := 2) ν 1)

def binForm (R : Type) [CommRing R] (d : ℕ) :
    (Fin (d + 1) → R) →ₗ[R] MvPolynomial (Fin 2 × Fin 1) R :=
  ∑ i : Fin (d + 1), (LinearMap.proj i : (Fin (d + 1) → R) →ₗ[R] R).smulRight
    ((X ((0 : Fin 2), (0 : Fin 1)) : MvPolynomial (Fin 2 × Fin 1) R) ^ (d - i.val) *
      X ((1 : Fin 2), (0 : Fin 1)) ^ i.val)

def BinFormInj : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ), Function.Injective (binForm R d)

def DualWeylBinaryForms : Prop :=
  ∀ (R : Type) [CommRing R] (ν : Fin 1 → ℕ),
    dualWeyl R 2 1 ν = LinearMap.range (binForm R (ν 0))

def WeylRankTwoOneColumnImage : Prop :=
  ∀ (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ),
    weyl R 2 1 hn ν =
      (LinearMap.range (Formalism.CohomologicalDescent.diagBinom R (ν 0))).map (binForm R (ν 0))

def LatticeInclusionTrivialWeight : Prop :=
  ∀ (r : ℕ) (hn : 0 ≤ r) (ν : Fin 0 → ℕ) (l : ℕ), l.Prime →
    InclZ r 0 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r 0 ν) l)

def LatticeInclusionRankOne : Prop :=
  ∀ (n : ℕ) (hn : n ≤ 1) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 1 n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 1 n ν) l)

def LemmaAZ_r2n1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    InclZ 2 1 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l)

def LemmaAZ_r2n2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 2 2 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l)

def LatticeInclusionRankLeTwo : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r), r ≤ 2 → ∀ ν : Fin n → ℕ, Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def LemmaAR_r2n1 : Prop :=
  ∀ (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    ∀ x ∈ dualWeyl R 2 1 ν, (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l • x ∈ weyl R 2 1 hn ν

def SharpInclusionRankTwoOneColumn : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l e : ℕ), l.Prime →
    (InclZ 2 1 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e)

def ExZR2N1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    exZ 2 1 hn ν l = Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l

def SharpInclusionRankTwoTwoColumns : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l e : ℕ, l.Prime →
    (InclZ 2 2 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e)

def ExZR2N2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    exZ 2 2 hn ν l = Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l

def JointExZ : Prop :=
  LemmaAZ → ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    exZ r n hn ν l ≤ Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l

def nuOf {r : ℕ} (U : Fin r → ℤ) : Fin r → ℕ :=
  fun a => (U a - ((r : ℤ) - 1 - (a.val : ℤ))).toNat

def NuOfSpec : Prop :=
  ∀ (r : ℕ) (U : Fin r → ℤ), StrictAnti U → (∀ a, 0 ≤ U a) →
    Antitone (nuOf U) ∧ lamU r r (nuOf U) = U

def ExLeExact {ι : Type} {D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι} (W : Formalism.CohomologicalDescent.Joint.Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ, D.ex τ l ≤ exZ D.Nr D.Nr le_rfl (nuOf (W.U τ)) l

def JointLemmaAFull : Prop :=
  ∀ (ι : Type) (D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι) (W : Formalism.CohomologicalDescent.Joint.Weights D),
    LemmaAZ → ExLeExact W → Formalism.CohomologicalDescent.Joint.LemmaAFull W

def ExLeExactParts {ι : Type} {D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι} (W : Formalism.CohomologicalDescent.Joint.Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ ∈ D.T2,
    D.ecl τ l ≤ exZ D.k D.k le_rfl (nuOf (W.cloud τ)) l ∧
    D.erest τ l ≤ exZ (D.Nr - D.k) (D.Nr - D.k) le_rfl (nuOf (W.rest τ)) l

def JointLemmaAInputs : Prop :=
  ∀ (ι : Type) (D : Formalism.RankGapBounds.ChebyshevFactorialBounds.Data ι) (W : Formalism.CohomologicalDescent.Joint.Weights D),
    LemmaAZ → ExLeExact W → ExLeExactParts W → Formalism.CohomologicalDescent.Joint.LemmaAInputs W

def JointLatIncl : Prop :=
  LemmaAR → ∀ (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
    Antitone ν → ∀ l : ℕ, l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    Formalism.RankGapBounds.FormsTensorLocalization.LatIncl (l : R) ((weyl R r n hn ν).comap (dualWeyl R r n ν).subtype)
      (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

end Formalism.CohomologicalDescent.LA
end
end

-- bundled from Formalism.PieriBlockIdeals.StatementLD
section
open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def boxesOfContent {q : ℕ} (lam2 tau : Fin q → ℕ) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).card

def colLen {q : ℕ} (lam2 tau : Fin q → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => lam2 a ≤ j ∧ j < tau a).card

def shapes (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0

def mu (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) (c : ℤ) : ℕ :=
  (shapes p w i lam2).sup fun tau => boxesOfContent lam2 tau c

def Dn (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ :=
  ∏ k ∈ Finset.range (q + w + i), ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ))

noncomputable def nablaWt (r : ℕ) (ν μ : Fin r → ℕ) : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
  dualWeyl ℤ r r ν ⊓ weightedHomogeneousSubmodule ℤ (rowW r r) μ

def KilledAt (l r : ℕ) (ν μ : Fin r → ℕ) (c : ℤ) : Prop :=
  ∀ x ∈ nablaWt r ν μ, ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * c) • x ∈ weyl ℤ r r le_rfl ν

def ExpLe (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) : Prop := KilledAt l r ν μ ((l : ℤ) ^ e)

def blockWt (p q w : ℕ) (κ : Fin q → ℕ) : Fin (p + q) → ℕ := Fin.append (fun _ : Fin p => w) κ

def blockWtLast (p q w : ℕ) (κ : Fin q → ℕ) : Fin (q + p) → ℕ := Fin.append κ (fun _ : Fin p => w)

def IsDepth (p q w : ℕ) (μ : Fin (p + q) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.castAdd q a) + i = p * w

def IsDepthLast (p q w : ℕ) (μ : Fin (q + p) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.natAdd q a) = p * w + i

def depth2 {r : ℕ} (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) : ℤ := ∑ a, ξ a * ((lam a : ℤ) - (μ a : ℤ))

def LemmaDAt (l p q w : ℕ) (lam2 : Fin q → ℕ) : Prop :=
  ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))

def LemmaDGradedAt (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWt p q w lam2) (blockWt p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i → depth2 ξ (blockWt p q w lam2) μ ≤ i' →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))

def BranchingBoundOneRow : Prop :=
  ∀ (l q w : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) → LemmaDAt l 1 q w lam2

def LemmaD : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) → LemmaDAt l p q w lam2

def LemmaDGraded : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) →
    Antitone ξ → LemmaDGradedAt l p q w lam2 ξ

def LemmaDLast : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i →
        ExpLe l (q + p) (blockWtLast p q w lam2) μ
          (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))

def DnNeZero : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), Dn p w i lam2 ≠ 0

def MuSupport : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    -(q : ℤ) ≤ c ∧ c < (w : ℤ) + (i : ℤ)

def ExpLeIffKilled : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (D : ℤ), l.Prime → D ≠ 0 →
    (ExpLe l r ν μ (e + padicValInt l D) ↔ KilledAt l r ν μ ((l : ℤ) ^ e * D))

def ExpLeMono : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e e' : ℕ), e ≤ e' → ExpLe l r ν μ e → ExpLe l r ν μ e'

def ExpBounded : Prop :=
  ∀ (l r : ℕ) (ν : Fin r → ℕ), l.Prime → Antitone ν → ∃ e : ℕ, ∀ μ : Fin r → ℕ, ExpLe l r ν μ e

def GradedImpliesPlain : Prop := LemmaDGraded → LemmaD

def OneRowOfBound : Prop := LemmaD → BranchingBoundOneRow

def wt2 (w y : ℕ) : Fin 2 → ℕ := ![w, y]

noncomputable def vec2 (w y i : ℕ) : MvPolynomial (Fin 2 × Fin 2) ℤ :=
  X (0, 0) ^ (w - y - i) * X (1, 0) ^ i * (X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)) ^ y

def Dn2 : Prop :=
  ∀ (p w y i : ℕ), 1 ≤ p → y + i ≤ w →
    Dn p w i (fun _ : Fin 1 => y) = ((i.factorial * (w - y).choose i : ℕ) : ℤ)

def Rank2Exact : Prop :=
  ∀ (w y i : ℕ), y + i ≤ w →
    nablaWt 2 (wt2 w y) (wt2 (w - i) (y + i)) = Submodule.span ℤ {vec2 w y i} ∧ vec2 w y i ≠ 0 ∧
      ∀ c : ℤ, c • vec2 w y i ∈ weyl ℤ 2 2 le_rfl (wt2 w y) ↔ (((w - y).choose i : ℕ) : ℤ) ∣ c

def Rank2Other : Prop :=
  ∀ (w y : ℕ) (μ : Fin 2 → ℕ), y ≤ w → (∀ i : ℕ, y + i ≤ w → μ ≠ wt2 (w - i) (y + i)) →
    nablaWt 2 (wt2 w y) μ = ⊥

def LemmaD_rank2 : Prop :=
  ∀ (l w y : ℕ), l.Prime → y ≤ w → LemmaDAt l 1 1 w (fun _ : Fin 1 => y)

def LemmaDGraded_rank2 : Prop :=
  ∀ (l w y : ℕ) (ξ : Fin (1 + 1) → ℤ), l.Prime → y ≤ w → Antitone ξ →
    LemmaDGradedAt l 1 1 w (fun _ : Fin 1 => y) ξ

def MuLe : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), mu p w i lam2 c ≤ p

def MuRange : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    (m : ℤ) - (q : ℤ) < c ∧ c < (w : ℤ)

def DnPos : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), (∀ b, lam2 b ≤ w) → 0 < Dn p w i lam2

def DnDvd : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    Dn p w i lam2 ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ)

def DnVal : Prop :=
  ∀ (l p w i q m : ℕ) (lam2 : Fin q → ℕ), l.Prime → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    (l - 1) * padicValInt l (Dn p w i lam2) ≤ p * (w + q - m - 1)

def PeelBound : Prop :=
  BranchingBoundOneRow → ∀ (l q w m : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ μ : Fin (1 + q) → ℕ, ExpLe l (1 + q) (blockWt 1 q w lam2) μ (eL + (w + q - m - 1) / (l - 1))

def LemmaD_sym : Prop :=
  ∀ (l q w : ℕ), l.Prime → LemmaDAt l 1 q w (fun _ : Fin q => 0)

end Formalism.CohomologicalDescent.LD
end


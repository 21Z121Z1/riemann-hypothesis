import Formalism.FormalGroupWitt.Statement

-- bundled from Formalism.FormalGroupWitt.ShiftSOneLetter
section
noncomputable section

open PowerSeries

universe u v

namespace Formalism.FG

open Formalism.G Formalism.LT

def shiftLogS (K : Type u) [Field K] (l : ℕ) (ε : ℤ) (m : ℕ) (j : ZMod m) :
    MvPowerSeries (ZMod m) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then (((ε : K) * l) ^ e)⁻¹ else 0

def ltLogS (K : Type u) [Field K] (l : ℕ) (ε : ℤ) {ι : Type v} [DecidableEq ι] (r : ι) :
    MvPowerSeries ι K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single r ((l ^ 2) ^ e) then (((ε : K) * l) ^ e)⁻¹ else 0

def ShiftSOne : Prop :=
  ∀ (K : Type u) [Field K] (l m : ℕ), shiftLogS K l 1 m = shiftLog K l m

def ShiftSOneLetter : Prop :=
  ∀ (K : Type u) [Field K] (l : ℕ) (ε : ℤ), shiftLogS K l ε 1 0 = ltLogS K l ε (0 : ZMod 1)

def ShiftSFunEq : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (l : ℕ) (hl : l.Prime) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ (m : ℕ) [NeZero m] (σ : K →+* K),
    IsIdMod2 (shiftLogS K l ε m) ∧
    ∀ j, shiftLogS K l ε m j - (l : K)⁻¹ • ∑ k, ((ε : K) * shiftMat K m j k) •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLogS K l ε m k)) = MvPowerSeries.X j

def ShiftSGroup : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m],
    ∃ F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l], IsFGL F ∧ IsCommV F ∧
      IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m)

def ShiftSHeight : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m) →
    ∃ e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l], IsHomV F F e ∧
      (∀ j, MvPowerSeries.subst (fun k => MvPowerSeries.map PadicInt.Coe.ringHom (e k))
          (shiftLogS ℚ_[l] l ε m j) = (l : ℚ_[l]) • shiftLogS ℚ_[l] l ε m j) ∧
      (∀ j n, (l : ℤ_[l]) ∣ MvPowerSeries.coeff n
        (e j - MvPowerSeries.C (ε : ℤ_[l]) * MvPowerSeries.X (j - 1) ^ (l ^ 2))) ∧
      (∀ j n, (l : ℤ_[l]) ∣ MvPowerSeries.coeff n
        (iterV e m j - MvPowerSeries.C ((ε : ℤ_[l]) ^ m) * MvPowerSeries.X j ^ (l ^ (2 * m))))

def ShiftSTeich : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m) →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [CharZero R] (φ : ℤ_[l] →+* R) (w : R),
      w ^ ((l ^ 2) ^ m) = w →
      IsHomV (fun i => MvPowerSeries.map φ (F i)) (fun i => MvPowerSeries.map φ (F i))
        (fun j => MvPowerSeries.C (w ^ ((l ^ 2) ^ j.val)) * MvPowerSeries.X j)

def ShiftSTeichWitt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLogS ℚ_[l] l ε m) →
    ∃ ζ : WittVector l (AlgebraicClosure (ZMod l)), IsPrimitiveRoot ζ (l ^ (2 * m) - 1) ∧
      IsHomV (fun i => MvPowerSeries.map (zlToW l) (F i))
        (fun i => MvPowerSeries.map (zlToW l) (F i))
        (fun j => MvPowerSeries.C (ζ ^ ((l ^ 2) ^ j.val)) * MvPowerSeries.X j)

def GaussLogShiftS : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m] (c : ℝ), 0 < c →
      c ^ (l ^ 2 - 1) ≤ ‖(l : K)‖ →
      ∀ j, HasGauss c (shiftLogS K l ε m j) ∧ gauss c (shiftLogS K l ε m j) = c

def GaussExpShiftS : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m] (c : ℝ), 0 < c →
      c ^ (l ^ 2 - 1) ≤ ‖(l : K)‖ →
      ∀ g : ZMod m → MvPowerSeries (ZMod m) K, (∀ j, MvPowerSeries.constantCoeff (g j) = 0) →
        (∀ j, MvPowerSeries.subst g (shiftLogS K l ε m j) = MvPowerSeries.X j) →
        ∀ j, HasGauss c (g j) ∧ gauss c (g j) = c

def BridgeLT : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (τ : K →+* K),
    FunctionalEquationSetting K l (l ^ 2) τ → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZMod m → ι → K),
    (∀ j r, ‖M j r‖ ≤ 1) → (∀ j r, τ (M j r) = M (j + 1) r) →
      ∃ h : ZMod m → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (h j) = 0) ∧
        (∀ j, IntegralMv (h j)) ∧
        (∀ j r, MvPowerSeries.coeff (Finsupp.single r 1) (h j) = M j r) ∧
        ∀ j, MvPowerSeries.subst h (shiftLogS K l ε m j) =
          ∑ r, MvPowerSeries.C (M j r) * ltLogS K l ε r

def BridgeLTIso : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (τ : K →+* K),
    FunctionalEquationSetting K l (l ^ 2) τ → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ (m : ℕ) [NeZero m]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ZMod m → ι → K) (N : ι → ZMod m → K),
    (∀ j r, ‖M j r‖ ≤ 1) → (∀ r j, ‖N r j‖ ≤ 1) → (∀ j r, τ (M j r) = M (j + 1) r) →
    (∀ j k, ∑ r, M j r * N r k = if j = k then 1 else 0) →
    (∀ r s, ∑ j, N r j * M j s = if r = s then 1 else 0) →
    ∀ h : ZMod m → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (h j) = 0) →
      (∀ j, MvPowerSeries.subst h (shiftLogS K l ε m j) =
        ∑ r, MvPowerSeries.C (M j r) * ltLogS K l ε r) →
      ∃ h' : ι → MvPowerSeries (ZMod m) K, (∀ r, MvPowerSeries.constantCoeff (h' r) = 0) ∧
        (∀ r, IntegralMv (h' r)) ∧
        (∀ r, MvPowerSeries.subst h' (ltLogS K l ε r) =
          ∑ j, MvPowerSeries.C (N r j) * shiftLogS K l ε m j) ∧
        (∀ j, MvPowerSeries.subst h' (h j) = MvPowerSeries.X j) ∧
        (∀ r, MvPowerSeries.subst h (h' r) = MvPowerSeries.X r)

end Formalism.FG
end
end

-- bundled from Formalism.FormalGroupWitt.SubstInjectiveV
section
noncomputable section

open PowerSeries

universe u v w

namespace Formalism.FG

open Formalism.G Formalism.LT

def SolveExistsV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (G : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ j, MvPowerSeries.constantCoeff (G j) = 0) →
      ∃ h : ι → MvPowerSeries τ R, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) ∧
        ∀ j, MvPowerSeries.subst h (f j) = G j

def SubstInjectiveV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, MvPowerSeries.constantCoeff (b i) = 0) →
    (∀ j, MvPowerSeries.subst a (f j) = MvPowerSeries.subst b (f j)) → a = b

def CoeffBoundV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K), IntegralMat M →
    ∀ (τ : Type w) (f : ι → MvPowerSeries τ K), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      IsFunEqTypeV p q hq σ M f →
      ∀ j (n : τ →₀ ℕ), ∃ k : ℕ, (∀ i, q ^ k ∣ n i) ∧
        ‖MvPowerSeries.coeff n (f j)‖ * ‖(p : K)‖ ^ k ≤ 1

def IntegralSubstV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Finite ι] (τ : Type w)
    (g : MvPowerSeries ι K) (a : ι → MvPowerSeries τ K),
    IntegralMv g → (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, IntegralMv (a i)) →
      IntegralMv (MvPowerSeries.subst a g)

def FunEqSubstV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      IsFunEqTypeV p q hq σ M f →
    ∀ (τ : Type w) (α : ι → MvPowerSeries τ K), (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      (∀ i, IntegralMv (α i)) →
      IsFunEqTypeV p q hq σ M (fun j => MvPowerSeries.subst α (f j))

def LowCoeffV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K),
    2 ≤ q → ∀ (ι : Type v) [Fintype ι] (M : ι → ι → K) (τ : Type w)
    (D : ι → MvPowerSeries τ K), IsFunEqTypeV p q hq σ M D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1

def InvIntegralV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K),
    IsIdMod2 f →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv (P i)) → C (fun j => MvPowerSeries.subst P (f j))) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1) →
    ∀ h : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) →
      C (fun j => MvPowerSeries.subst h (f j)) → ∀ i, IntegralMv (h i)

def FrobLiftPadicSq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], FunctionalEquationSetting ℚ_[l] l (l ^ 2) (RingHom.id ℚ_[l])

end Formalism.FG
end
end


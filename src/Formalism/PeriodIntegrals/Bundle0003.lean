import Mathlib

-- bundled from Formalism.PeriodIntegrals.ExpIntW
section
noncomputable section

namespace PI

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))

def ExpIntW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → Simeq f 0 → SimeqW f 0

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.ExpTri
section
open Matrix

noncomputable section

namespace PI

def ExpTri : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ), Xᴴ = X → Yᴴ = Y → Zᴴ = Z →
    U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2)

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.ExplicitFormula
section
noncomputable section

namespace PI

open Classical in

def psi0 {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
    (if χ = 1 then (u : ℂ) else 0)

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ExplicitFormulaWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖)

def ExplicitFormula : Prop := ∃ C : ℝ, 0 < C ∧ ExplicitFormulaWith C

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FglChordFactor
section
noncomputable section

open Classical

namespace PI.FglChordFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → ‖W.Δ‖ = 1 →
    IsWq W wq → PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq)⁻¹ =
        add (flog W wq) ex (Xv 0) (Xv 1) * sub (flog W wq) ex (Xv 0) (Xv 1) * n

end PI.FglChordFactor
end
end

-- bundled from Formalism.PeriodIntegrals.FglGram
section
noncomputable section

open Classical

namespace PI.FglGram

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def DualIso {p : ℕ} [Fact p.Prime] {κ ι : Type*} [Fintype κ] (b b' : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e e', hP (b e) (b e') = 0) ∧ (∀ e e', hP (b' e) (b' e') = 0) ∧
    ∀ e e', hP (b e) (b' e') = if e = e' then 1 else 0

section

variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  pt ex (MvPowerSeries.C c * lg l a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  pt ex (∑ j, MvPowerSeries.C (c j) * lg l (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end

def PhOn {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) (fun e => Xv e))

def beSum {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (ι : Type*) [Fintype ι] :
    MvPowerSeries (ι ⊕ ι) ℂ_[p] :=
  ∑ e : ι, be l ex ph (Xv (Sum.inl e)) (Xv (Sum.inr e))

def GramRhs {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {κ : Type*} [Fintype κ] {k : ℕ}
    (A : Fin k → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (Fin k) ℂ_[p] :=
  ∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * phAt ph (Xv j) +
    ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (mulBy l ex (hP (A j) (A j')).1 (Xv j)) (Xv j')

def Data {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧ PowerSeries.constantCoeff ph = 0

def CubeRelationOfParallelogram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1)) →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt ph (sub l ex (Xv 0) (Xv 1)) +
        phAt ph (sub l ex (Xv 1) (Xv 2)) + phAt ph (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2))) →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
        phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def PhGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Data l ex ph →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    (∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))) →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)

def GramUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      GramRhs l ex ph de = ∑ j, phAt ph (Xv j)

def GramIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (b : Fin r → κ → ℂ_[p] × ℂ_[p]), (∀ e e', hP (b e) (b e') = 0) →
      GramRhs l ex ph b = 0

def PhDualGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Data l ex ph →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)) →
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e k, b e k ∈ S) →
      (∀ e k, b' e k ∈ S) → DualIso b b' →
      Simeq (PhOn l ex ph (Sum.elim b b')) (beSum l ex ph ι)

end PI.FglGram
end
end

-- bundled from Formalism.PeriodIntegrals.FglPhSplit
section
noncomputable section

namespace PI.FglPhSplit

open Classical

def expMv {K : Type*} [Field K] {σ : Type*} (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : K)

def SimeqW {K : Type*} [Field K] (W : Subring K) {σ : Type*} (f g : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ ∀ n, MvPowerSeries.coeff n (expMv (f - g)) ∈ W

def hP {K : Type*} [Field K] {ι : Type*} [Fintype ι] (x y : ι → K × K) : K × K :=
  ∑ k, x k * (y k).swap

structure Dat (K : Type*) [Field K] where
  l : PowerSeries K
  ex : PowerSeries K
  ph : PowerSeries K

namespace Dat

variable {K : Type*} [Field K] (g : Dat K) {σ : Type*}

def lg (a : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ K) : MvPowerSeries σ K := g.pt (g.lg a + g.lg b)

def mulBy (c : K) (a : MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.pt (MvPowerSeries.C c * g.lg a)

def lin {ι : Type*} [Fintype ι] (c : ι → K) (a : ι → MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

def phAt (a : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst a g.ph

def be (a b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.phAt (g.add a b) - g.phAt a - g.phAt b

def PhV {κ ι : Type*} [Fintype κ] [Fintype ι] (b : ι → κ → K × K) (w : ι → MvPowerSeries σ K) :
    MvPowerSeries σ K :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) w)

def PhOn {κ ι : Type*} [Fintype κ] [Fintype ι] (b : ι → κ → K × K) : MvPowerSeries ι K :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) (fun e => MvPowerSeries.X e))

def beSum (ι : Type*) [Fintype ι] : MvPowerSeries (ι ⊕ ι) K :=
  ∑ e : ι, g.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))

def sdL {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → K × K) (a' : ι' → κ → K × K) : MvPowerSeries (ι ⊕ ι') K :=
  g.PhOn (Sum.elim a a') - g.PhV a (fun e => MvPowerSeries.X (Sum.inl e)) -
    g.PhV a' (fun e => MvPowerSeries.X (Sum.inr e))

def sdR {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → K × K) (a' : ι' → κ → K × K) : MvPowerSeries (ι ⊕ ι') K :=
  ∑ f, ∑ f', g.be (g.mulBy (hP (a f) (a' f')).1 (MvPowerSeries.X (Sum.inl f))) (MvPowerSeries.X (Sum.inr f'))

end Dat

def DualIso {K : Type*} [Field K] {κ ι : Type*} [Fintype κ] (b b' : ι → κ → K × K) : Prop :=
  (∀ e e', hP (b e) (b e') = 0) ∧ (∀ e e', hP (b' e) (b' e') = 0) ∧
    ∀ e e', hP (b e) (b' e') = if e = e' then 1 else 0

def Target : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (g : Dat K) (S : Set (K × K)),
    PowerSeries.constantCoeff g.ex = 0 → PowerSeries.subst g.ex g.l = PowerSeries.X →
    PowerSeries.constantCoeff g.ph = 0 →
    (∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → K × K)
        (a' : ι' → κ → K × K), (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
        SimeqW W (g.sdL a a') (g.sdR a a')) →
    (∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → K × K), (∀ e k, b e k ∈ S) →
        (∀ e k, b' e k ∈ S) → DualIso b b' → SimeqW W (g.PhOn (Sum.elim b b')) (g.beSum ι)) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (b b' : ι → κ → K × K)
      (b'' : ι' → κ → K × K), (∀ e k, b e k ∈ S) → (∀ e k, b' e k ∈ S) → (∀ e k, b'' e k ∈ S) →
      DualIso b b' → (∀ e f, hP (b e) (b'' f) = 0) → (∀ e f, hP (b' e) (b'' f) = 0) →
      SimeqW W (g.PhOn (Sum.elim (Sum.elim b b') b''))
        (∑ e : ι, g.be (MvPowerSeries.X (Sum.inl (Sum.inl e))) (MvPowerSeries.X (Sum.inl (Sum.inr e))) +
          g.PhV b'' (fun f => MvPowerSeries.X (Sum.inr f)))

end PI.FglPhSplit

end
end

-- bundled from Formalism.PeriodIntegrals.FglPtW
section
noncomputable section

namespace PI.FglPtW

def SerOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ S

def PtOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (a : MvPowerSeries σ K) : Prop :=
  SerOver S a ∧ MvPowerSeries.constantCoeff a = 0

def AddGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (σ : Type) (a b : MvPowerSeries σ K), PtOver S a → PtOver S b →
      PtOver S (PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex)

def MulGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    ∀ c : K, SerOver S (PowerSeries.subst
      (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) →
    ∀ (σ : Type) (a : MvPowerSeries σ K), PtOver S a →
      PtOver S (PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex)

def LinGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (ι : Type) [Fintype ι] (c : ι → K),
    (∀ j, SerOver S (PowerSeries.subst
      (MvPowerSeries.C (c j) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex)) →
    ∀ (σ : Type) (a : ι → MvPowerSeries σ K), (∀ j, PtOver S (a j)) →
      PtOver S (PowerSeries.subst (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex)

end PI.FglPtW

end
end

-- bundled from Formalism.PeriodIntegrals.FglTriFactor
section
noncomputable section

open Classical

namespace PI.FglTriFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

def T {p : ℕ} [Fact p.Prime] (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  (Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 2 - Xv 1) +
    (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 0 - Xv 2) +
    (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 1 - Xv 0)

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → ‖W.Δ‖ = 1 →
    IsWq W wq → PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T wq = add (flog W wq) ex (add (flog W wq) ex (Xv 0) (Xv 1)) (Xv 2) *
        sub (flog W wq) ex (Xv 0) (Xv 1) * sub (flog W wq) ex (Xv 1) (Xv 2) *
        sub (flog W wq) ex (Xv 2) (Xv 0) * n

end PI.FglTriFactor
end
end

-- bundled from Formalism.PeriodIntegrals.FiltLen
section
namespace PI

def FiltLen : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, W →ₗ[R] V k),
      (∀ k, ∀ x ∈ F k, φ k x = 0 → x ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M ⊓ F k).map (φ k) ≤ P k) → (∀ k < a, Q k ≤ (N ⊓ F k).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

end PI
end

-- bundled from Formalism.PeriodIntegrals.FiltLenF
section
namespace PI

def FiltLenF : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, ↥(F k) →ₗ[R] V k),
      (∀ k, ∀ x : ↥(F k), φ k x = 0 → (x : W) ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M.comap (F k).subtype).map (φ k) ≤ P k) →
        (∀ k < a, Q k ≤ (N.comap (F k).subtype).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

end PI
end


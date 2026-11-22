import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.PeriodIntegrals.Bundle0026

-- bundled from Formalism.PeriodIntegrals.AdIndexEq
section
noncomputable section

namespace PI.AdIndexEq

open Formalism.MainNotions.S

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def IndexEq : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    ((Ksub I).map (MulAut.conj x).toMonoidHom).relIndex (Ksub I) =
      ((Ksub I).map (MulAut.conj x⁻¹).toMonoidHom).relIndex (Ksub I)

end PI.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.AdUnimod
section
open MeasureTheory

noncomputable section

namespace PI

def AdUnimod : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf), μf.IsHaarMeasure → μf.IsMulRightInvariant

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.AdelClassFin
section
noncomputable section

namespace PI.AdelClassFin

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

def GFf (I : Formalism.MainNotions.S.AutInst) : Set I.Gf :=
  {x | ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    I.fmat x = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))}

def AdelClassFin : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) →
    ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ u ∈ U, x = γ * s * u

end PI.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.AdelFinVol
section
noncomputable section

namespace PI.AdelFinVol

open MeasureTheory

def AdelFinVol : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf], μf.IsHaarMeasure →
    ∀ fund : Set I.GA, I.IsFundDom (I.muA μf) fund → I.muA μf fund ≠ ⊤

end PI.AdelFinVol
end
end

-- bundled from Formalism.PeriodIntegrals.GTDefs
section
noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def lastGL (R : Type) [CommRing R] (N : ℕ) (a : Rˣ) : GL (Fin N) R :=
  diagGL R N (fun i => if i.1 + 1 = N then a else 1)

def wsum {k : ℕ} (l : DomWeight k) : ℤ := ∑ i, l.w i

def aa {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  sg.w i - lam.w ⟨i.1 + 1, by omega⟩

def bb {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  lam.w ⟨i.1, by omega⟩ - sg.w i

def D0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, (sg.w i - lam.w ⟨i.1 + 1, by omega⟩)

def D1 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg)

def degZ {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n) : ℤ := wsum lam - wsum sg

def Rset {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg))

def cBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - sg.w j + (j.1 : ℤ))

def rowsZ {n N : ℕ} (h : n + 1 = N) (i : Fin n) : Fin (i.1 + 1) → Fin N :=
  fun p => if p.1 = i.1 then ⟨N - 1, by omega⟩ else ⟨p.1, by omega⟩

def xi (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin n, (Formalism.GradedWeylDivisibility.lpMinor R (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat *
    (Formalism.GradedWeylDivisibility.initMinor R (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat

def cBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  (((2 * lam.spread : ℤ) : ℝ)) ^ ((((N : ℤ) * D1 h lam sg : ℤ) : ℝ))

def brBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  cBd h lam sg * Real.sqrt (Module.finrank ℂ (delSq ℂ N lam))

def IsIota {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
    io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) ∧
  (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
    io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s)) ∧
  io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg ∧
  (∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (io s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • io s) ∧
  (∀ s ∈ nablaSq ℂ n sg,
    (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re)

def IsBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
    br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)

def IsTranspose {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ s ∈ nablaSq ℂ n sg, ∀ f ∈ delSq ℂ N lam, normFock lam (io s) f = normFock sg s (br f)

def Branch {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧ xi ℂ h lam sg ≠ 0 ∧
  degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg ∧
  ∃ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io ∧ IsBr h lam sg br ∧ IsTranspose lam sg io br

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.LatSizeCont
section
noncomputable section

namespace PI.LatSizeCont

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

def coordV (x : I.GA) (v : InfinitePlace I.F) (u : Fin I.n → I.E) : Fin I.n → ℂ :=
  (Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (u i))

def gramV (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) : Matrix (Fin j) (Fin j) ℂ :=
  fun a c => ∑ i, star (coordV I x v (b a) i) * coordV I x v (b c) i

structure Sub (x : I.GA) where
  j : ℕ
  j_pos : 1 ≤ j
  b : Fin j → Fin I.n → I.E
  b_ind : LinearIndependent I.E b
  B : Submodule (𝓞 I.E) (Fin I.n → I.E)
  B_lat : (B : Set (Fin I.n → I.E)) ⊆ latSet I x
  b_mem : ∀ a, b a ∈ B
  B_span : (B : Set (Fin I.n → I.E)) ⊆ Submodule.span I.E (Set.range b)

def ht {x : I.GA} (s : Sub I x) : ℝ :=
  (∏ v, (gramV I x v s.b).det.re) /
    (Nat.card (s.B ⧸ (Submodule.span (𝓞 I.E) (Set.range s.b)).comap s.B.subtype) : ℝ)

def size {x : I.GA} (s : Sub I x) : ℝ := ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)))

def tau1 (x : I.GA) : ℝ := min (1 / 2) (⨅ s : Sub I x, size I s)

end Size

def LatSizeCont : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, 1 ≤ I.n →
    Continuous (Size.tau1 I) ∧ ∀ x : I.GA, 0 < Size.tau1 I x ∧ Size.tau1 I x ≤ 1 / 2

end PI.LatSizeCont
end
end

-- bundled from Formalism.PeriodIntegrals.NMeasInv
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.NMeasInv

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

def FrameRel (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) ∧
  Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0

end Inst

def FinCpt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ K : Set I.Ginf, IsCompact K → μ K < ⊤

def RightInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ n ∈ Ninf I e z, μ.map (fun x => x * n) = μ

def InvInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      μ.map (fun x => x⁻¹) = μ

def ConjInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ h ∈ Hset I (Set.range e ∪ Set.range f ∪ {z}), μ.map (fun x => h * x * h⁻¹) = μ

def Target : Prop := FinCpt ∧ RightInv ∧ InvInv ∧ ConjInv

end PI.NMeasInv
end
end

-- bundled from Formalism.PeriodIntegrals.ScMuExists
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.ScMuExists

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

abbrev muInf : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def IsQuotMeasS (μS ν : Measure I.Ginf) : Prop :=
  ∀ f : I.Ginf → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂(muInf I) = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

end Inst

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0 →
    ∃ muN muH nuQ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) muN ∧
      IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH ∧
      IsQuotMeasS I ((muN.prod muH).map (fun p => p.1 * p.2)) nuQ

end PI.ScMuExists
end
end

-- bundled from Formalism.PeriodIntegrals.ScPsiExists
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScPsiExists

def psiEinf (I : Formalism.MainNotions.S.AutInst) (x : I.E) : ℂ :=
  ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x)))

def Target : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, ∃ psiEf : I.E ⊗[I.F] Af I.F → ℂ,
    (∀ x y, psiEf (x + y) = psiEf x * psiEf y) ∧
    (∀ x ∈ IntAf I.F I.E, psiEf x = 1) ∧
    ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Af I.F) x) * psiEinf I x = 1

end PI.ScPsiExists
end
end

-- bundled from Formalism.PeriodIntegrals.ScRefExists
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open Matrix

namespace PI.ScRefExists

section Fin

variable (I : Formalism.MainNotions.S.AutInst)

abbrev VA : Type := Fin I.n → I.E ⊗[I.F] Af I.F

def incl (x : Fin I.n → I.E) : VA I := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def hA (x y : VA I) : I.E ⊗[I.F] Af I.F :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x y

abbrev sigA : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def mL (m : ℕ) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x}

def InMod (m : ℕ) (S : Set (VA I)) (x : VA I) : Prop :=
  x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I m

def ZMod' (m : ℕ) (c : I.E ⊗[I.F] Af I.F) : Prop :=
  ∃ t ∈ IntAf I.F I.E, c = (m : I.E ⊗[I.F] Af I.F) * t

def InAt (g m : ℕ) (x : VA I) : Prop :=
  ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • x ∈ mL I m

end Fin

structure RefData (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) where
  e0 : Fin r → VA I
  f0 : Fin r → VA I
  z0 : VA I
  bw : Fin k → VA I
  bwd : Fin k → VA I
  ew : I.E ⊗[I.F] Af I.F
  vectorsInLattice : (∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf
  basisApprox : ∀ a, InAt I g g (e0 a - incl I (e a)) ∧ InAt I g g (f0 a - incl I (f a))
  gramIntegral : ∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
    ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)
  formsAtZero : ZMod' I g (hA I z0 z0 + 1) ∧
    ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)
  weightVectorsIntegral : ∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
    ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
      ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))
  ew_idem : ew * ew = ew
  ew_orth : ew * sigA I ew = 0
  ew_int : ew ∈ IntAf I.F I.E
  ew_full : ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g
  bw_w : ∀ i, bw i = ew • bw i
  bwd_w : ∀ i, bwd i = sigA I ew • bwd i
  bw_dual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)
  latticeSpan : ∀ y ∈ I.Lf,
    InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)

end PI.ScRefExists
end
end


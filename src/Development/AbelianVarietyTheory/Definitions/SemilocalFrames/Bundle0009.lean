import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Sg2 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : ℝ :=
  Finset.univ.fold max 1 fun a : Fin (r + 1) => max (lA k r z x a) (lA k r z x a)⁻¹

def Dj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ :=
  ‖Dmin k r z z' γ ⟨j, by omega⟩‖

def Yj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) : ℝ :=
  gramProj (Ppos k r z z' γ x) (fun a : Fin j => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) / Dj k r hj z z' γ

def XstJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1))

def XJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1))

def IsNormal0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (β : Fin r → ℕ) (c : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ ‖c‖ = 1 ∧ g *ᵥ z' = c • z ∧ Monotone β ∧
    (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
    (∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j) ∧
    (∀ a : Fin r, j ≤ a.val → g *ᵥ bvec (eI k r a) = c • bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = c • bvec (esI k r a)) ∧
    BlockAnti (fun a : Fin j => β (Fin.castLE hj a)) ((Zr k r g).submatrix (Fin.castLE hj) (Fin.castLE hj))

abbrev PTop (k r j : ℕ) :=
  ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × ({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)

abbrev PSec (k r j : ℕ) :=
  ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ) × ({p : UT r // p.1.1.val < j} → ℂ) × ({a : Fin r // a.val < j} → ℝ)

def pTop (k r j : ℕ) (q : PTop k r j) : Mat k r :=
  pOf k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0, fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)

def pSec (k r j : ℕ) (q : PSec k r j) : Mat k r :=
  pOf k r (fun a => if h : a.val < j then q.1 ⟨a, h⟩ else 0, fun p => if h : p.1.1.val < j then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : a.val < j then q.2.2 ⟨a, h⟩ else 0)

def rEl (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r := uEmb k r (upperIn β q.1) * pTop k r j q.2

def sEl (k r j : ℕ) (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : Mat k r := pSec k r j q.1 * uEmb k r (upperOff β q.2)

def lebR0 (k r j : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure ((UTin β → ℂ) × PTop k r j)).map fun q => Matrix.of.symm (rEl k r j β q)

def IsNormalFormStabilizerMeasure (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧
    ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), IsNormal0 k r hj β c z z' g₀ ∧
      γ = n₁ * g₀ * n₂ ∧ μR = (ENNReal.ofReal s • lebR0 k r j β).map (conjM n₂⁻¹)

def Eset0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (R₀ y : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ GG k r ∧ Sg2 k r z' (Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x) ≤ R₀ ∧
    y < Yj k r hj z z' γ (Matrix.of x) ∧ Yj k r hj z z' γ (Matrix.of x) ≤ 2 * y}

def fibVol0 (k r j : ℕ) (R₀ De y : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * (R₀ ^ (2 * r) * De) ^ (8 * r ^ 2) *
    (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j))

def TailBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ la : ℝ, 0 < la →
    ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
        (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS ≤
      ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ

def sgV (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : ℝ :=
  Finset.univ.fold max 1 fun l : Fin (r + 1) => ‖Dmin k r z z' γ l.castSucc‖ / (2 * H₁) ^ (2 * r)

def degBd (k r j q : ℕ) (H₁ De D sg : ℝ) : ℝ :=
  16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ (8 * r ^ 2 + 2) *
    (8 * Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (D ^ (k - 1 - j))⁻¹ *
    sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r))

example (k : ℕ) (z : Fin (2 * 0 + k + 1) → ℂ) (x : Mat k 0) : 1 ≤ Sg2 k 0 z x := by
  unfold Sg2; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

end GlobalTheory.Amp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def pairMaj {k r : ℕ} (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (p : PairSp k r) : ℝ :=
  Formalism.FourierDecayAlt.B.gN ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1) ^ (-b)

def coefF {k r : ℕ} (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, L.σ g v'⟫_ℂ • ξ)

def CellData {k r : ℕ} (L : LocBessel k r) (μG : Measure (Mt k r))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) : Prop :=
  γ ∈ UH (Hpk k r) ∧ 0 < Gf k r L.z L.z' γ ∧ Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) ∧
    IsRelStab L γ ∧ IsHaarOn (RStab k r γ) μR ∧ IsOrbQuot L γ μR ν ∧
    PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR

def OnePlace {k r : ℕ} (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) : Prop :=
  GapAtLeast L.ε L.lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h ∧ L.c ≠ 0 ∧ PI.UpqRep.IsLowUnitH k r L.ε L.lam L.σ w0 ∧
    IsHaarOn (UH (Hpk k r)) μG ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def OnePlaceKF {k r : ℕ} (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) : Prop :=
  OnePlace L h μG w0 l l' ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v →
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v →
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def AmpKF : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.Inputs →
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

def GapCell (k r : ℕ) (h : ℝ) : Prop :=
  10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) + 2 * Formalism.FourierDecayAlt.ThreeDimData.AG k r + 4 ≤
    Formalism.FourierDecayAlt.ThreeDimData.aOf r h

def CellConv : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)),
    L.κN ≠ ⊤ → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → CellData L μG γ μR νR ν →
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) →
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ Integrable (pairMaj γ b) ν

def amp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (R : BranchingSupport.Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (w : R.H)
    (ν : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  ampJ ν 1 (fun g => l (R.σ g w)) (fun g => l' (R.σ g w)) γ

end GlobalTheory.CellAmp

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
section
namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB Finset NumberField MeasureTheory Formalism.QuantumDeterminants

noncomputable section

open Classical

def ThresholdProductsBounded {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (Θ : ℝ) : Prop :=
  (∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i : ℕ, 2 ≤ i → i ≤ G.r + 1 →
    ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i s : ℕ, 1 ≤ i → 2 ≤ s → s + i ≤ G.r + 2 →
    ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) ≤ (Θ ^ G.f)⁻¹) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ G.r →
    ∏ w, Sz.lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') ≤ (Θ ^ G.f)⁻¹)

def arData (E : Type) [Field E] [NumberField E] [IsCMField E] (g r : ℕ) (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ)
    (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) : TB.Data E Unit where
  r := r
  f := 0
  K := 5
  av := fun _ _ => 0
  wt := fun _ => 1
  cnt := fun _ => 0
  Wall := {()}
  emp := ()
  emp_mem := by simp
  cnt_emp := rfl
  wt_emp := rfl
  gram := fun _ _ _ _ _ => 0
  Kr := Kr
  K0 := hK0
  Th := fun _ _ _ _ _ => 0
  e := e
  La := fun b s => J.LaB E g r b s
  Lap := fun b s => J.LapB E g r b s
  Lad := fun b => J.LadB E g r b
  Nhat := fun _ _ _ _ _ _ => 0
  szD := fun _ _ => 0
  szL := fun _ _ _ => 0
  vol := fun _ _ => 0

def ArAx (E : Type) [Field E] [NumberField E] [IsCMField E] (g r : ℕ) (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ)
    (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) : Prop :=
  TC.KrPSD (arData E g r Kr hK0 e) ∧ (arData E g r Kr hK0 e).KernelSupport ∧ TC.EBounds (arData E g r Kr hK0 e) ∧
    TC.DomAfter (arData E g r Kr hK0 e)

def frS (rd : ℝ) (r b s : ℕ) : ℝ := rd ^ (-(S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ))

abbrev parG {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (x : ι) : M.Par :=
  ⟨G.k, G.r, T, T', (G.place x).u de, (G.place x).u de'⟩

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def vStd {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g rd : ℝ) (p : C.LPt) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  ((√(C.nLoc k r (frS rd r) (D.ptGG (Tz k r Bs.z * Tz k r Bs.z')) p) * (D.bSt (D.kapG g rd) p)⁻¹ : ℝ) : ℂ) •
    B.hsVec (D.vecV Bs ν' m₀ F (D.toStd r g 1 p))

structure PlaceOK {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (x : ι)
    (Bs : B.RealPlaceData G.k G.r Wp Wq) (ν' : Fin (2 * G.r + G.k + 1) → ℂ) (m₀ : B.Mat G.k G.r)
    (F : B.Mat G.k G.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) : Prop where
  hW : Bs.μW Set.univ = 1
  hW' : Bs.μW' Set.univ = 1
  hN : Bs.μN = D.muN G.k G.r
  frame : D.IsBaseFrame Bs ν' m₀
  place : Q.IsPlace (parG G de de' T T' x) Bs.z Bs.z' Bs.π Bs.π'
  smooth : B.CkOn ⊤ (B.GV G.k G.r) F
  decay : ∀ m : ℕ, B.InCC A₀ m F
  eigen : ∀ Y : ℝ, ∀ g ∈ B.GV G.k G.r, Q.CV G.k G.r (Y : ℂ) F g = (((G.place x).P Y : ℝ) : ℂ) • F g

end place

def ChaptersBuilt : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsLeadingFormPlace Cb Cc S p f c.χ A₀ → JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    (∀ v, B.normSq (plT S p v).base (f v) ≠ ⊤) ∧
    ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄
      (∏ v, (B.normSq (plT S p v).base (f v)).toReal /
        D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0) Vt

def SizesLe : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ) (Θ : ℝ),
    S6.Unram E → 0 < S.G.g1 → 0 < S.G.g2 → 0 ≤ S.CA → 0 < S.G.lenI → 4 < Θ →
    ThresholdProductsBounded S.G S.CA S.de S.de' S.T S.T' S.l Θ →
    (S.mkData Kr hK0 Th e).SizesBelow Θ ∧
      (S.mkData Kr hK0 Th e).LatticeSums ((C₁ * Θ ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f)

def MainBuilt : Prop :=
  ∀ Cb : ℝ, ∃ Cc Cst Cst' : ℝ, 0 ≤ Cc ∧ 0 ≤ Cst ∧ 4 < Cst' ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) (Θ : ℝ) (cr : ℕ → TB.Pt E → ℂ),
    IsLeadingFormPlace Cb Cc S p f c.χ A₀ → JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    Cst' ≤ Θ → ((S.G.r : ℝ) + 1) * (Cst / Θ) ^ S.f ≤ 1 → ThresholdProductsBounded S.G S.CA S.de S.de' S.T S.T' S.l Θ →
    ArAx E S.g S.G.r Kr hK0 e → (arData E S.g S.G.r Kr hK0 e).LeadingDomination Vt cr →
    (∀ v, B.normSq (plT S p v).base (f v) ≠ ⊤) ∧
    ∀ Rs : Finset ℕ, ∑ ρ ∈ Rs, ‖∑' q, cr ρ q • Vt q‖ ^ 2 ≤
      (1 + Cst * ((S.G.r : ℝ) + 1) * (Cst / Θ) ^ S.f) * (∏ i ∈ Icc 1 (S.G.r + 1), (1 + e i)) *
        ∏ v, (B.normSq (plT S p v).base (f v)).toReal /
          D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0

def GridsExist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    (∀ v, (S.G.place (S.pl v)).Ok) → 1 ≤ S.l → S.l + 2 ≤ S.G.k → 42 * (S.Ntop : ℝ) ^ 3 ≤ S.G.lenI →
    ∃ (gr : Fin S.f → ℕ → Finset ℝ) (gr1 : Fin S.f → Finset ℝ),
      C.GridsOK { S with grid := gr, grid1 := gr1 } ∧ GridsRich { S with grid := gr, grid1 := gr1 }

def PlExists : Prop :=
  ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (l0 : ℕ),
    1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.μW Set.univ = 1 → Bs.μW' Set.univ = 1 → Bs.μN = D.muN P.k P.r →
    D.IsBaseFrame Bs ν' m₀ → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∃ p : Pl P Wp Wq, p.l0 = l0 ∧ p.T.base = Bs ∧ p.ν' = ν' ∧ p.m₀ = m₀ ∧ InDDplus2 P l0 p.T.base Cb p.Θ

def MainFreeAt (C C' : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (G : Sz.Glob (InfinitePlace E)) (emb : InfinitePlace E → (E →+* ℂ)) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
    (Bs : ∀ x, B.RealPlaceData G.k G.r (Wp x) (Wq x)) (ν' : InfinitePlace E → Fin (2 * G.r + G.k + 1) → ℂ)
    (m₀ : InfinitePlace E → B.Mat G.k G.r) (F : ∀ x, B.Mat G.k G.r → (Wq x →L[ℂ] Wp x)) (A₀ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1) (e : ℕ → ℝ) (Θ : ℝ) (cr : ℕ → TB.Pt E → ℂ),
    (∀ x, InfinitePlace.mk (emb x) = x) → S6.Unram E → G.v = S6.rd E / 2 → 0 < G.g1 → 0 < G.g2 →
    (∀ x, (G.place x).Ok) → Sz.IsWord G.k de → Sz.IsWord G.k de' → 1 ≤ l → l + 2 ≤ G.k → de l ≠ de' l →
    C * ((G.k : ℝ) * G.N * ((G.r : ℝ) + 1) ^ 2 + G.N ^ 2 * ((G.r : ℝ) + 1) ^ 2 + G.N ^ 3) ≤ G.lenI →
    C * ((G.r : ℝ) + 1) ^ 4 * (G.N * (2 * (G.r : ℝ) + G.k + 1) ^ 2 + (2 * (G.r : ℝ) + G.k + 1) ^ 3) ≤ A₀ →
    (∀ x, PlaceOK G de de' T T' x (Bs x) (ν' x) (m₀ x) (F x) A₀) →
    (∀ p q : TB.Pt E, TB.IsPt p (G.r + 1) → TB.IsPt q (G.r + 1) → inner ℂ (Vt q) (Vt p) =
      ∏ x, inner ℂ (vStd (Bs x) (ν' x) (m₀ x) (F x) G.g (S6.rd E) (Formalism.FourierDecayAlt.C.loc (emb x) q))
        (vStd (Bs x) (ν' x) (m₀ x) (F x) G.g (S6.rd E) (Formalism.FourierDecayAlt.C.loc (emb x) p))) →
    C' ≤ Θ → ((G.r : ℝ) + 1) * (C / Θ) ^ G.f ≤ 1 → ThresholdProductsBounded G C de de' T T' l Θ →
    ArAx E (G.g1 * G.g2) G.r Kr hK0 e → (arData E (G.g1 * G.g2) G.r Kr hK0 e).LeadingDomination Vt cr →
    (∀ x, B.normSq (Bs x) (F x) ≠ ⊤) ∧
    ∀ Rs : Finset ℕ, ∑ ρ ∈ Rs, ‖∑' q, cr ρ q • Vt q‖ ^ 2 ≤
      (1 + C * ((G.r : ℝ) + 1) * (C / Θ) ^ G.f) * (∏ i ∈ Icc 1 (G.r + 1), (1 + e i)) *
        ∏ x, (B.normSq (Bs x) (F x)).toReal / D.GamLev G.k G.r (D.kapG G.g (S6.rd E)) (D.deG G.g (S6.rd E)) 0

def MainFree : Prop := ∃ C₀ C' : ℝ, 1 ≤ C₀ ∧ 4 < C' ∧ ∀ C : ℝ, C₀ ≤ C → MainFreeAt C C'

end

end GlobalTheory.ThA
end


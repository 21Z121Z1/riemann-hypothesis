import Mathlib

-- bundled from Formalism.PeriodIntegrals.RamBound
section
open Finset

noncomputable section

namespace PI.RamBound

def geV (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (x : Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Kc) ^ (-a) ∈ Oc

def gaussGe (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) {τ : Type} (y : MvPolynomial τ Kc) (g : ℝ) : Prop :=
  ∀ n, geV p Oc (MvPolynomial.coeff n y) g

def JetInt {Kc : Type} [Field Kc] (Oc : Subring Kc) {σ : Type} (f : MvPowerSeries σ Kc) : Prop :=
  ∀ n : σ →₀ ℕ, (∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f ∈ Oc

def IsPart {n' : ℕ} (r0 : ℕ) (nu : Fin n' → ℕ → ℤ) : Prop :=
  (∀ s i, 0 ≤ nu s i) ∧ (∀ s i, 1 ≤ i → nu s (i + 1) ≤ nu s i) ∧ (∀ s i, r0 < i → nu s i = 0)

def sz {n' : ℕ} (rb : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := ∑ i ∈ Icc 1 rb, nu s i

abbrev ZV (nH r0 r1 : ℕ) : Type := Σ _t : Fin nH, Fin 2 × Fin r0 × Fin r1

abbrev FrV (nH r0 : ℕ) : Type := Σ _t : Fin nH, Fin 2 × ℕ × Fin r0

abbrev Wt (nH : ℕ) : Type := Fin nH → Fin 2 → ℕ → ℤ

abbrev ColCh (nH r1 : ℕ) : Type := Fin nH → Fin 2 → ℕ → ℕ → Fin r1

def colHt {nH : ℕ} (rb : ℕ) (nu : Wt nH) (v : Fin nH) (s : Fin 2) (c : ℕ) : ℕ :=
  ((Icc 1 rb).filter fun i => (c : ℤ) < nu v s i).card

def colFac {nH r0 r1 : ℕ} (rb : ℕ) (nu : Wt nH) (I : ColCh nH r1) (v : Fin nH) (s : Fin 2) (c : ℕ) :
    MvPolynomial (ZV nH r0 r1) (MvPolynomial (FrV nH r0) ℤ) :=
  Matrix.det (Matrix.of fun (i i' : Fin (colHt rb nu v s c)) =>
    ∑ a : Fin r0,
      MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : FrV nH r0)) *
        MvPolynomial.X (⟨v, (s, a, I v s c i'.val)⟩ : ZV nH r0 r1))

def prodP {nH r0 r1 : ℕ} (rb : ℕ) (nu : Wt nH) (I : ColCh nH r1) : MvPolynomial (ZV nH r0 r1) (MvPolynomial (FrV nH r0) ℤ) :=
  ∏ v : Fin nH, ∏ s : Fin 2, ∏ c ∈ range (nu v s 1).toNat, colFac rb nu I v s c

def applyD {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    MvPolynomial τ Kc :=
  ∑ n ∈ P.support, ((∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f) •
    MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n P)

def KG {Kc : Type} [Field Kc] (Oc : Subring Kc) (nH r0 r1 rb : ℕ) (nu : Wt nH) (Th : MvPowerSeries (ZV nH r0 r1) Kc) :
    AddSubgroup (MvPolynomial (FrV nH r0) Kc) :=
  AddSubgroup.closure {y | ∃ (I : ColCh nH r1) (g : MvPolynomial (FrV nH r0) Kc), (∀ n, MvPolynomial.coeff n g ∈ Oc) ∧
    y = g * applyD (prodP (r0 := r0) rb nu I) Th}

def beD {Kc : Type} [Field Kc] (nH r0 r1 : ℕ) (u : Fin nH → Kc) : MvPowerSeries (ZV nH r0 r1) Kc :=
  ∑ t : Fin nH, MvPowerSeries.C (u t) * ∑ a : Fin r0, ∑ b : Fin r1,
    MvPowerSeries.X (⟨t, ((0 : Fin 2), a, b)⟩ : ZV nH r0 r1) *
      MvPowerSeries.X (⟨t, ((1 : Fin 2), a, b)⟩ : ZV nH r0 r1)

def expK {Kc : Type} [Field Kc] {σ : Type} (f : MvPowerSeries σ Kc) : MvPowerSeries σ Kc :=
  fun n => ∑ k ∈ range (n.degree + 1), ((k.factorial : Kc))⁻¹ * MvPowerSeries.coeff n (f ^ k)

def IntD (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (nH r0 r1 : ℕ) (Th : MvPowerSeries (ZV nH r0 r1) Kc) : Prop :=
  ∃ (S : Kc) (u : Fin nH → Kc) (F0 : MvPowerSeries (ZV nH r0 r1) Kc),
    geV p Oc S (-(1 / 2)) ∧ (∀ t, u t ∈ Oc) ∧ JetInt Oc F0 ∧
      Th = expK (-(MvPowerSeries.C S) * beD nH r0 r1 u) * F0

def ct {nH : ℕ} (rb : ℕ) (TT : Finset (Fin nH)) (nu : Fin nH → Fin 2 → ℕ → ℤ) (t : Fin nH) : ℤ :=
  sz rb (nu t) 0 - (if t ∈ TT then nu t 0 1 - nu t 0 2 else 0) + (if t ∈ TT then nu t 1 1 else 0)

end PI.RamBound

open PI.RamBound in

def PI.RamBound : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (nH r0 r1 rb : ℕ) (TT : Finset (Fin nH)) (nu : Wt nH)
    (Th : MvPowerSeries (ZV nH r0 r1) Kc),
    p.Prime → (∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) → ((p : Kc))⁻¹ ∉ Oc → (∀ t, IsPart r0 (nu t)) → r0 ≤ rb →
      IntD p Oc nH r0 r1 Th →
      ∀ y ∈ KG Oc nH r0 r1 rb nu Th, gaussGe p Oc y (-(1 / 2) * ∑ t, (ct rb TT nu t : ℝ))
end
end

-- bundled from Formalism.PeriodIntegrals.RayBoundIQ
section
open NumberField

namespace PI

def RayBoundIQ : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      1 ≤ Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) ∧
      (Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) : ℝ) ≤
        4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

end PI
end

-- bundled from Formalism.PeriodIntegrals.RegSeqQuasiReg
section
universe u

namespace PI

def RegSeqQuasiReg : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) →
    ∀ (k : ℕ) (F : MvPolynomial (Fin n) R), F.IsHomogeneous k →
      MvPolynomial.eval x F ∈ Ideal.span (Set.range x) ^ (k + 1) →
      ∀ m, F.coeff m ∈ Ideal.span (Set.range x)

end PI
end

-- bundled from Formalism.PeriodIntegrals.Residue
section
open NumberField

noncomputable section

namespace PI

def ResidueBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E], 2 ≤ Module.finrank ℚ E →
    dedekindZeta_residue E ≤
      (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.RhsWLim
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ContDiff

namespace PI.RhsWLim

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def Hb (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then -1 else 1

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def IsSection (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j : Fin (k + 1), ContDiffOn ℝ ∞ (fun ζ => μsec ζ i j) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    Matrix.conjTranspose (μsec ζ) * Hb k * μsec ζ = Hb k ∧ herm (Hb k) (μsec ζ *ᵥ wbPart k r z') (wbPart k r z) = ζ

def embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) then 1 else 0

def zWeight (k : ℕ) (T T' : ℝ) (ζ : ℂ) : ℝ :=
  if T * T' ≤ Complex.normSq ζ then (Complex.normSq ζ - T * T') ^ (k - 1) else 0

def volU (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ)

def wbConst (k : ℕ) (T T' a a' : ℝ) : ℝ :=
  2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1) * a * a')

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def rhsW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
    ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def zeta0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ := ((2 * Real.sqrt (Tz k r z * Tz k r z') : ℝ) : ℂ)

def mBase (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  embWb k r (μsec (zeta0 k r z z'))

def bBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UWb k r) ρ

def mBall (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ρ : ℝ) :
    Set (Mt k r) :=
  {x | (fun i j => ((mBase k r z z' μsec)⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def bVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal

structure WbData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarW : IsHaarOn (UWset k r z) μW
  haarW' : IsHaarOn (UWset k r z') μW'
  a_pos : 0 < a
  a'_pos : 0 < a'
  massW : μW Set.univ = ENNReal.ofReal a
  massW' : μW' Set.univ = ENNReal.ofReal a'
  sec : IsSection k r z z' μsec

def WbDataEx : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), WbData k r z z' μW μW' a a' μsec

def RhsWLim : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    Tendsto (fun ρ : ℝ => (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ)
      (𝓝[>] 0) (𝓝 (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹)

end PI.RhsWLim
end
end

-- bundled from Formalism.PeriodIntegrals.RowLetter
section
open MvPolynomial

noncomputable section

namespace PI.RL

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def TE (K : Type) [CommRing K] (k : ℕ) (vec : Bool) (d : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  if vec then X a * pderiv b f else (if a = b then (d : K) • f else 0) - X b * pderiv a f

end PI.RL

namespace PI

open PI.RL

def RowLetter : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)), ∀ P ∈ Hd K (m + 1) d,
    RE K (m + 1) a b (theta K m vec P) = theta K m vec (TE K (m + 1) vec d a b P)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.RowWtSpan
section
open MvPolynomial

noncomputable section

namespace PI.RW

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def initMinor (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin r × Fin n) R)).det

def bideterminant (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : MvPolynomial (Fin r × Fin n) R :=
  ∏ k : Fin K, initMinor R (I k) (hsz k)

def shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (t : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin K => t.val < sz k).card

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def BideterminantMem : Prop :=
  ∀ (R : Type) [CommRing R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r),
    bideterminant R sz hsz I ∈ dualWeyl R r n (shapeDeg sz)

def BideterminantSpan : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ),
    dualWeyl R k n ν ≤ Submodule.span R {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ f = bideterminant R sz hsz I}

end PI.RW

namespace PI

open PI.RW

def RowWtSpan : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∃ (J : Type) (b : J → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (μ : J → Fin (m + 1) → ℕ),
      Submodule.span K (Set.range b) = dualWeyl K (m + 1) (m + 1) ν ∧
      (∀ i a, RE K (m + 1) a a (b i) = (μ i a : K) • b i) ∧ ∀ i a, μ i a ≤ ν 0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.SDiffGram
section
noncomputable section

namespace PI.SDiffGram

open Classical

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

def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])

section FG

variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  pt ex (MvPowerSeries.C c * lg l a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  pt ex (∑ j, MvPowerSeries.C (c j) * lg l (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end FG

section SD

variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p])

def PhOn {κ ι : Type*} [Fintype κ] [Fintype ι] (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) (fun e => Xv e))

def PhV {κ ι σ : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (w : ι → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) w)

def sdL {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  PhOn l ex ph (Sum.elim a a') - PhV l ex ph a (fun e => Xv (Sum.inl e)) - PhV l ex ph a' (fun e => Xv (Sum.inr e))

def sdR {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (mulBy l ex (hP (a f) (a' f')).1 (Xv (Sum.inl f))) (Xv (Sum.inr f'))

def sdR' {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', be l ex ph (Xv (Sum.inl f)) (mulBy l ex (hP (a f) (a' f')).2 (Xv (Sum.inr f')))

end SD

def SDiffGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), PowerSeries.constantCoeff l = 0 → PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X → PowerSeries.constantCoeff ph = 0 →
    ∀ (S : Set (ℂ_[p] × ℂ_[p])),
    (0 : ℂ_[p] × ℂ_[p]) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * phAt ph (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (mulBy l ex (hP (A j) (A j')).1 (Xv j)) (Xv j'))) →
    (∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
      Simeq (sdL l ex ph a a') (sdR l ex ph a a') ∧ Simeq (sdL l ex ph a a') (sdR' l ex ph a a')

end PI.SDiffGram
end
end

-- bundled from Formalism.PeriodIntegrals.SSAscent
section
namespace PI

namespace SSAscent

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

def IsInv (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

def IsSSRep (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'

end Rep

def mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : Γ →* GL (Fin a) B :=
  (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) A →+* Matrix (Fin a) (Fin a) B).toMonoidHom).comp ρ

end SSAscent

open SSAscent

def SSAscent : Prop :=
  ∀ (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] (Γ : Type) [Group Γ] (a : ℕ)
    (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → IsSSRep (mapRep (algebraMap K L) ρ)

end PI
end


import Mathlib

-- bundled from Formalism.UnipotentAdelicQuotients.JetMomFound
section
set_option autoImplicit false

noncomputable section

open PowerSeries

namespace JetMomFound

section FG

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![mulN F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries

def IsIsoGm (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ IsUnit (coeff 1 f) ∧
    PowerSeries.subst F.toPowerSeries f =
      (FormalGroup.𝔾ₘ : FormalGroup R).toPowerSeries.subst
        ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f]

end FG

section Padic

variable {p : ℕ} [Fact p.Prime]

def CoeffFinite (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ∃ L : IntermediateField ℚ_[p] ℂ_[p], FiniteDimensional ℚ_[p] L ∧
    ∀ m : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff m F.toPowerSeries : 𝓞_ℂ_[p]) : ℂ_[p]) ∈ L

def HtOne (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ‖((coeff p (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 ∧ ∀ k < p, ‖((coeff k (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1

end Padic

def HtOneIsGm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]), CoeffFinite F → HtOne F → ∃ f : PowerSeries 𝓞_ℂ_[p], IsIsoGm F f

def RootUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) (f g : MvPowerSeries σ K) (m : ℕ), 0 < m →
    MvPowerSeries.constantCoeff f = 1 → MvPowerSeries.constantCoeff g = 1 → f ^ m = g ^ m → f = g

def BimulTriv : Prop :=
  ∀ (A M : Type) [AddCommGroup A] [CommGroup M] (q : ℕ) (ze : A → A → M),
    (∀ a a' b, ze (a + a') b = ze a b * ze a' b) → (∀ a b b', ze a (b + b') = ze a b * ze a b') →
    (∀ a : A, ∃ n : ℕ, q ^ n • a = 0) → (∀ (a : A) (n : ℕ), ∃ b : A, q ^ n • b = a) → ∀ a b, ze a b = 1

def EvenHomTriv : Prop :=
  ∀ (A M : Type) [AddCommGroup A] [CommGroup M] (c : A → M), (∀ a b, c (a + b) = c a * c b) → (∀ a, c (-a) = c a) →
    (∀ a : A, ∃ b : A, (2 : ℕ) • b = a) → ∀ a, c a = 1

def substAll {σ : Type*} {p : ℕ} [Fact p.Prime] (e : PowerSeries ℂ_[p]) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  MvPowerSeries.subst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) e) G

def SolFE {σ : Type*} {p : ℕ} [Fact p.Prime] (e : PowerSeries ℂ_[p]) (ε : MvPowerSeries σ ℂ_[p]) (m : ℕ)
    (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff G = 1 ∧ substAll e G = G ^ m * ε

def FunEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] ℂ_[p]), FiniteDimensional ℚ_[p] L →
    ∀ (r : ℕ) (e : PowerSeries ℂ_[p]) (ε : MvPowerSeries (Fin r) ℂ_[p]) (m : ℕ),
      (∀ n, coeff n e ∈ L ∧ ‖coeff n e‖ ≤ 1) → constantCoeff e = 0 → ‖coeff 1 e‖ = 1 →
      (∀ ν, MvPowerSeries.coeff ν ε ∈ L ∧ ‖MvPowerSeries.coeff ν ε‖ ≤ 1) → MvPowerSeries.constantCoeff ε = 1 → p ∣ m →
      (∃ G, SolFE e ε m G ∧ ∀ ν, MvPowerSeries.coeff ν G ∈ L ∧ ‖MvPowerSeries.coeff ν G‖ ≤ 1) ∧ ∀ G₁ G₂, SolFE e ε m G₁ → SolFE e ε m G₂ → G₁ = G₂

def wCurve (L : PeriodPair) : WeierstrassCurve ℂ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -(L.g₂ / 4), a₆ := -(L.g₃ / 4) }

def PAddThm : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z + w ∉ L.lattice →
    ∃ (h₁ : (wCurve L).toAffine.Nonsingular (L.weierstrassP z) (L.derivWeierstrassP z / 2))
      (h₂ : (wCurve L).toAffine.Nonsingular (L.weierstrassP w) (L.derivWeierstrassP w / 2))
      (h₃ : (wCurve L).toAffine.Nonsingular (L.weierstrassP (z + w)) (L.derivWeierstrassP (z + w) / 2)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ = WeierstrassCurve.Affine.Point.some _ _ h₃

def PParam : Prop :=
  ∀ L : PeriodPair, ∃ w : PowerSeries ℂ,
    PowerSeries.constantCoeff w = 0 ∧
    w = PowerSeries.X ^ 3 - PowerSeries.C (L.g₂ / 4) * PowerSeries.X * w ^ 2 - PowerSeries.C (L.g₃ / 4) * w ^ 3 ∧
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ,
      let u := -(2 * L.weierstrassP z) / L.derivWeierstrassP z
      L.weierstrassP z ≠ 0 ∧ L.derivWeierstrassP z ≠ 0 ∧ HasSum (fun n => PowerSeries.coeff n w * u ^ n) (u / L.weierstrassP z)

abbrev Qb : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

def lamOf {p : ℕ} [Fact p.Prime] (lam : Qb →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  open Classical in if h : x ∈ Qb then lam ⟨x, h⟩ else 0

def uC (L : PeriodPair) (z : ℂ) : ℂ := -(2 * L.weierstrassP z) / L.derivWeierstrassP z

def offL (L : PeriodPair) (r : ℕ) : Set (Fin r → ℂ) := {z | ∀ i, z i ∉ L.lattice}

def IsUSer (L : PeriodPair) {r : ℕ} (f : (Fin r → ℂ) → ℂ) (S : MvPowerSeries (Fin r) ℂ) : Prop :=
  ∀ᶠ z in nhdsWithin (0 : Fin r → ℂ) (offL L r),
    HasSum (fun ν : Fin r →₀ ℕ => MvPowerSeries.coeff ν S * ∏ i, uC L (z i) ^ ν i) (f z)

def IsULaw (L : PeriodPair) (F : MvPowerSeries (Fin 2) ℂ) : Prop :=
  ∀ᶠ z in nhdsWithin (0 : Fin 2 → ℂ) {z | z 0 ∉ L.lattice ∧ z 1 ∉ L.lattice ∧ z 0 + z 1 ∉ L.lattice},
    HasSum (fun k : Fin 2 →₀ ℕ => MvPowerSeries.coeff k F * (uC L (z 0) ^ k 0 * uC L (z 1) ^ k 1)) (uC L (z 0 + z 1))

def ratC (L : PeriodPair) {r : ℕ} (A B : MvPolynomial (Fin r × Fin 2) Qb) (z : Fin r → ℂ) : ℂ :=
  MvPolynomial.eval₂ (algebraMap Qb ℂ) (fun k : Fin r × Fin 2 => if k.2 = 0 then L.weierstrassP (z k.1) else L.derivWeierstrassP (z k.1) / 2) A /
    MvPolynomial.eval₂ (algebraMap Qb ℂ) (fun k : Fin r × Fin 2 => if k.2 = 0 then L.weierstrassP (z k.1) else L.derivWeierstrassP (z k.1) / 2) B

def shiftSer {p : ℕ} [Fact p.Prime] {r : ℕ} (F : MvPowerSeries (Fin 2) ℂ_[p]) (y : Fin r → ℂ_[p]) (i : Fin r) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  fun μ => open Classical in if μ = Finsupp.single i (μ i) then
    ∑' b : ℕ, MvPowerSeries.coeff (Finsupp.single 0 (μ i) + Finsupp.single 1 b) F * y i ^ b else 0

def yAt {p : ℕ} [Fact p.Prime] (lam : Qb →+* ℂ_[p]) (L : PeriodPair) {r : ℕ} (yt : Fin r → ℂ) (i : Fin r) : ℂ_[p] :=
  open Classical in if yt i ∈ L.lattice then 0 else lamOf lam (uC L (yt i))

def TransferTR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (lam : Qb →+* ℂ_[p]) (L : PeriodPair), L.g₂ ∈ Qb → L.g₃ ∈ Qb →
    ‖lamOf lam (L.g₂ / 4)‖ ≤ 1 → ‖lamOf lam (L.g₃ / 4)‖ ≤ 1 → ‖lamOf lam (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1 →
    ∀ F : MvPowerSeries (Fin 2) ℂ, IsULaw L F →
    ∀ (r : ℕ) (A B : MvPolynomial (Fin r × Fin 2) Qb) (yt : Fin r → ℂ),
      (∃ N : ℕ, 0 < N ∧ ∀ i, (N : ℂ) * yt i ∈ L.lattice) →
      (∀ i, yt i ∈ L.lattice ∨ 1 < ‖lamOf lam (L.derivWeierstrassP (yt i) / 2)‖) →
    ∀ S Sy : MvPowerSeries (Fin r) ℂ, IsUSer L (ratC L A B) S → IsUSer L (fun z => ratC L A B (z + yt)) Sy →
      (∀ k, MvPowerSeries.coeff k F ∈ Qb) ∧ (∀ ν, MvPowerSeries.coeff ν S ∈ Qb) ∧ (∀ ν, MvPowerSeries.coeff ν Sy ∈ Qb) ∧
      ((∃ C : ℝ, ∀ ν, ‖lamOf lam (MvPowerSeries.coeff ν S)‖ ≤ C) →
        ∀ μ, HasSum (fun ν : Fin r →₀ ℕ => lamOf lam (MvPowerSeries.coeff ν S) *
            MvPowerSeries.coeff μ (∏ i, shiftSer ((fun k : Fin 2 →₀ ℕ => lamOf lam (MvPowerSeries.coeff k F)) : MvPowerSeries (Fin 2) ℂ_[p]) (yAt lam L yt) i ^ ν i))
          (lamOf lam (MvPowerSeries.coeff μ Sy)))

end JetMomFound
end
end

-- bundled from Formalism.UnipotentAdelicQuotients.SiegelSetsSL2Adelic
section
open NumberField

noncomputable section

namespace Formalism.D

def adeleOfParts (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F)
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x, y)

def siegelSetsSL2Adelic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ (Ω K : Set (Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F))) (t₀ : ℝ),
      IsCompact Ω ∧ (∀ p ∈ Ω, (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0) ∧ IsCompact K ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F),
        ∃ γ ∈ (Matrix.SpecialLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F))).range,
        ∃ p ∈ Ω, ∃ t : ℝ, t₀ ≤ t ∧
        ∃ a a' : InfiniteAdeleRing F,
          (∀ w, a w * a' w = 1 ∧ InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) ∧
          ∃ k ∈ K, ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
            (p : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) *
              !![adeleOfParts F a 1, 0; 0, adeleOfParts F a' 1] *
              (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))

end Formalism.D

end
end

-- bundled from Formalism.UnipotentAdelicQuotients.SmComplete
section
open Filter Topology
open scoped ContDiff

noncomputable section

namespace SmoothVectors

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsClosedMatrixGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1

def IsIsomRep (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ g ∈ G, ∀ h ∈ G, σ (g * h) = (σ g).comp (σ h)) ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G

def lieAlg (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G}

def SmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ G → f g = F g

def smoothVecs (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | SmoothOn G (fun g => σ g v)}

def dsig (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def SmComplete : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsClosedMatrixGroup G → IsIsomRep G σ →
    ∀ v : ℕ → H, (∀ m, v m ∈ smoothVecs G σ) →
      (∀ w : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ w, X ∈ lieAlg G) →
        CauchySeq fun m => dsigW σ w (v m)) →
      ∃ v₀ ∈ smoothVecs G σ, ∀ w : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ w, X ∈ lieAlg G) →
        Tendsto (fun m => dsigW σ w (v m)) atTop (𝓝 (dsigW σ w v₀))

end SmoothVectors

end
end

-- bundled from Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
section
namespace HeckeCharacterZeroLocus

open NumberField

def StdAdditiveCharExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
    ∃ ψ : AddChar (AdeleRing (𝓞 F) F) ℂ, Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧
      (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) ∧ (∃ x, ψ x ≠ 1) ∧
      ∀ x : InfiniteAdeleRing F, ψ (x, 0) =
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)))

end HeckeCharacterZeroLocus
end

-- bundled from Formalism.UnipotentAdelicQuotients.ThmBInSatake
section
noncomputable section

open NumberField IsDedekindDomain

namespace HeckeCharacterZeroLocus.ThmBIn

variable {K : Type} [Field K] [NumberField K]

def Kmax (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Set (GL (Fin n) (w.adicCompletion K)) :=
  {g | ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K ∧
    ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈
      w.adicCompletionIntegers K}

def IsDiagAt (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ϖ : 𝓞 K) (d : List ℤ) (α : GL (Fin n) (w.adicCompletion K)) :
    Prop :=
  (α : Matrix (Fin n) (Fin n) (w.adicCompletion K)) =
    Matrix.diagonal (fun i => (algebraMap K (w.adicCompletion K) (ϖ : K)) ^ (d.getD i.1 0))

def IsCosetRep {G : Type} [Group G] (Kset : Set G) (α : G) (R : Finset G) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, γ = k₁ * α * k₂) ∧
    ∀ x : G, (∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Kset

def IsSphPD (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ϖ : 𝓞 K) (ω : GL (Fin n) (w.adicCompletion K) → ℂ) : Prop :=
  ω 1 = 1 ∧
  (∀ g, ∀ k ∈ Kmax w n, ω (g * k) = ω g ∧ ω (k * g) = ω g) ∧
  (∀ (m : ℕ) (g : Fin m → GL (Fin n) (w.adicCompletion K)) (z : Fin m → ℂ),
    (∑ i, ∑ j, star (z i) * z j * ω ((g i)⁻¹ * g j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, star (z i) * z j * ω ((g i)⁻¹ * g j)).re) ∧
  ∀ (d : List ℤ) (α : GL (Fin n) (w.adicCompletion K)), IsDiagAt w ϖ d α →
    ∀ R, IsCosetRep (Kmax w n) α R → ∀ x, ∑ γ ∈ R, ω (x * γ) = (∑ γ ∈ R, ω γ) * ω x

def splitLab (n k : ℕ) : List ℤ := List.replicate (n - k) 0 ++ List.replicate k (-1)

def satPolyL (c : List ℤ → ℂ) (q : ℕ) (r : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (r + 1), Polynomial.monomial (r - k)
    ((-1 : ℂ) ^ k * ((q : ℝ) ^ (-((k * (r - k) : ℕ) : ℝ) / 2) : ℝ) * c (splitLab r k))

def SatakeBoundLocal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K), ϖ ∈ w.asIdeal →
    ϖ ∉ w.asIdeal ^ 2 → ∀ (n : ℕ) (ω : GL (Fin n) (w.adicCompletion K) → ℂ), IsSphPD w ϖ ω →
    ∀ c : List ℤ → ℂ, (∀ k ≤ n, ∀ α R, IsDiagAt w ϖ (splitLab n k) α → IsCosetRep (Kmax w n) α R →
      c (splitLab n k) = ∑ γ ∈ R, ω γ) →
    ∀ a : ℂ, (satPolyL c (Ideal.absNorm w.asIdeal) n).IsRoot a →
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-((n : ℝ) - 1) / 2) ≤ ‖a‖ ∧
        ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((n : ℝ) - 1) / 2)

end HeckeCharacterZeroLocus.ThmBIn

end
end

-- bundled from Formalism.UnipotentAdelicQuotients.WeylLatDual
section
open MvPolynomial

noncomputable section

namespace WeylLatticeDuality

def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)

def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k

def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det

def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0

def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)

def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f

def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def nablaX {Lt : Type} [Fintype Lt] (N0 : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

def DelW (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) :
    AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :=
  AddSubgroup.closure {F | ∃ (r : ℂ_[p]) (f : T → MvPolynomial (Fin N × Fin N) ℤ), ‖r‖ ≤ 1 ∧
    (∀ τ, f τ ∈ weyl ℤ N N le_rfl (ν τ)) ∧
    F = fun y => r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))}

def Stmt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (nu : Lt → YoungDiagram) (ν : T → Fin N → ℕ),
      (∀ z (r : Fin N), (nu z).rowLen r = ν (e z) r) → (∀ z r, N ≤ r → (nu z).rowLen r = 0) →
      ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
        ((∀ J : ColChoice N nu, ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (nablaX N nu J))‖ ≤ 1) ↔
          (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => φ (DeX N nu fun s => colsOf (y (e s)))) ∈ DelW p T N ν)

end WeylLatticeDuality

end
end


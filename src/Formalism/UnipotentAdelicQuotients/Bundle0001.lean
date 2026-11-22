import Mathlib

-- bundled from Formalism.UnipotentAdelicQuotients.BruhatFunctionExistsVariant
section
universe u

namespace HeckeCharacterZeroLocus

open MeasureTheory Pointwise

def BruhatFunctionExistsVariant : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure H), μ.IsHaarMeasure →
      ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
        (∀ K : Set G, IsCompact K → IsCompact (tsupport β ∩ (K * (H : Set G)))) ∧
        ∀ x : G, ∫ h : H, β (x * (h : G)) ∂μ = 1

end HeckeCharacterZeroLocus
end

-- bundled from Formalism.UnipotentAdelicQuotients.CharRealisedOverRootsOfUnity
section
namespace Formalism.D.Classical

def CharRealisedOverRootsOfUnity : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] [CharZero K] (z : K), IsPrimitiveRoot z (Nat.card Γ) →
    ∀ χ : Γ → K,
      (∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) Γ (Fin n → AlgebraicClosure K)),
        ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)) →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K)),
        (Nontrivial (Fin m → K) ∧ Function.Surjective τ.asAlgebraHom) ∧
          ∀ g, LinearMap.trace K (Fin m → K) (τ g) = χ g

end Formalism.D.Classical
end

-- bundled from Formalism.UnipotentAdelicQuotients.ClassNumberFinite
section
namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def zeroLocusGL {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (R : Type) [CommRing R] [Algebra F R] : Set (GL (Fin n) R) :=
  {g | ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) R) ij.1 ij.2) P = 0}

def IsGroupLocus {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    1 ∈ zeroLocusGL S R ∧ (∀ g ∈ zeroLocusGL S R, ∀ h ∈ zeroLocusGL S R, g * h ∈ zeroLocusGL S R) ∧
      (∀ g ∈ zeroLocusGL S R, g⁻¹ ∈ zeroLocusGL S R)

def locusSubgroup {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (R : Type) [CommRing R] [Algebra F R] : Subgroup (GL (Fin n) R) where
  carrier := zeroLocusGL S R
  one_mem' := (hS R).1
  mul_mem' := fun {a b} ha hb => (hS R).2.1 a ha b hb
  inv_mem' := fun {a} ha => (hS R).2.2 a ha

def ClassNumberFinite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (U : Subgroup (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))),
    IsOpen (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    IsCompact (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    ∃ T : Finset (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧
        ∃ s ∈ T, ∃ u ∈ U,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
            Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ *
              (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) * ((u : locusSubgroup S hS _) : GL (Fin n) _)

end HeckeCharacterZeroLocus
end

-- bundled from Formalism.UnipotentAdelicQuotients.ClassNumberQuad
section
universe u

open NumberField Module

namespace HeckeCharacterZeroLocus.ClassNumberQuad

def ClassNumberLe : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], finrank ℚ K = 2 → IsTotallyComplex K →
    (classNumber K : ℝ) ≤ Real.sqrt (|discr K| : ℝ) * (Real.log (|discr K| : ℝ) + 2) / Real.pi

end HeckeCharacterZeroLocus.ClassNumberQuad
end

-- bundled from Formalism.UnipotentAdelicQuotients.CuspEllipticValues
section
set_option autoImplicit false

namespace CuspElliptic

def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)

def IsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  IsChar χ ∧ (∑ x, χ x * star (χ x)) = (Fintype.card G : ℂ)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def unipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

def IsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  IsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open Classical in if u ∈ (unipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0

def Statement : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) (χ χ' : GL (Fin d) F → ℂ),
    IsCuspChar χ → IsCuspChar χ' →
    (∀ x : GL (Fin d) F, Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)) → χ x = χ' x) →
    χ = χ'

end CuspElliptic
end

-- bundled from Formalism.UnipotentAdelicQuotients.CuspidalCharExists
section
open Polynomial

noncomputable section

namespace Formalism.D.Classical

def grRootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (AlgebraicClosure (ZMod g)) :=
  (f.map (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)))).roots

def grIp {G : Type} [Fintype G] (χ ψ : G → ℂ) : ℂ := ∑ x, χ x * star (ψ x)

def grIsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)

def grIsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  grIsChar χ ∧ grIp χ χ = (Fintype.card G : ℂ)

section
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def grUnipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

def grIsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  grIsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open _root_.Classical in if u ∈ (grUnipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0
end

variable {g : ℕ} [Fact g.Prime]

def grEllipticValues (teich : AlgebraicClosure (ZMod g) →* ℂ) {d : ℕ} (χ : GL (Fin d) (ZMod g) → ℂ) (k : ℕ) : Prop :=
  ∀ x : GL (Fin d) (ZMod g), Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g))) →
    χ x = (-1) ^ (d - 1) *
      ((grRootsBar (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g)))).map fun α => teich α ^ k).sum

def grIsGenSys (ζ : ℕ → AlgebraicClosure (ZMod g)) : Prop :=
  ∀ d, 0 < d → orderOf (ζ d) = g ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d

def grLab (ζ : ℕ → AlgebraicClosure (ZMod g)) (d k : ℕ) : (ZMod g)[X] := minpoly (ZMod g) (ζ d ^ k)

end Formalism.D.Classical

namespace Formalism.D.Classical

def CuspidalCharExists : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (teich : AlgebraicClosure (ZMod g) →* ℂ) (ζ : ℕ → AlgebraicClosure (ZMod g)),
    (∀ x y : AlgebraicClosure (ZMod g), x ≠ 0 → y ≠ 0 → teich x = teich y → x = y) → grIsGenSys ζ →
    ∀ d k : ℕ, 0 < d → (grLab ζ d k).natDegree = d →
      ∃ χ : GL (Fin d) (ZMod g) → ℂ, grIsCuspChar χ ∧ grEllipticValues teich χ k

end Formalism.D.Classical
end
end

-- bundled from Formalism.UnipotentAdelicQuotients.CyclicNormPrinciple
section
namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def CyclicNormPrinciple : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsGalois F E → IsCyclic (E ≃ₐ[F] E) → ∀ x : F, x ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) →
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) →
    ∃ y : E, Algebra.norm F y = x

end HeckeCharacterZeroLocus
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllReg
section
namespace ZetaZeros.D.EllReg

open scoped ContDiff

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def ev {d : ℕ} (j : Fin d) : E d := EuclideanSpace.single j (1 : ℝ)

noncomputable def dw {d : ℕ} : List (Fin d) → (E d → ℂ) → E d → ℂ
  | [], f => f
  | j :: w, f => fun x => fderiv ℝ (dw w f) x (ev j)

noncomputable def trOp {d : ℕ} (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
    (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x

structure Sys (d : ℕ) (ι : Type) where
  ord : ι → ℕ
  a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ

noncomputable def Sys.tr {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (φ : E d → ℂ) (x : E d) : ℂ :=
  trOp (P.ord i) (P.a i) φ x

noncomputable def Sys.symb {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (x ξ : E d) : ℂ :=
  ∑ w : Fin (P.ord i) → Fin d, P.a i (P.ord i) w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)

def WeakSol {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  ∀ (i : ι) (φ : E d → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, u x * P.tr i φ x = 0

def Hyp {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  IsOpen U ∧ (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) ∧
    (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) ∧ ContinuousOn u U ∧ WeakSol P U u

def Internal : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ),
    Hyp P U u → ContDiffOn ℝ ∞ u U

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.FinOrdValGen
section
noncomputable section

open NumberField IsDedekindDomain

namespace HeckeValGen

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom

open Classical in

def finiteSingle (v : HeightOneSpectrum (𝓞 L)) :
    v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v x
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing L), finiteSingle L v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle L v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle L v) x y) }

def FinOrdValGen : Prop :=
  ∀ χ : Ideles L →* ℂˣ, Continuous χ → (∀ k : Lˣ, χ (diagUnits L k) = 1) → (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) →
    ∀ ϖ : (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletion L)ˣ,
      (∀ v, Valued.v ((ϖ v : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ)) →
    ∀ S : Set (HeightOneSpectrum (𝓞 L)), S.Finite →
    ∀ (P : HeightOneSpectrum (𝓞 L)) (x : (P.adicCompletion L)ˣ),
      χ (localIdele L P x) ∈ Subgroup.closure {z : ℂˣ | ∃ v, v ∉ S ∧
        (∀ y : (v.adicCompletion L)ˣ, Valued.v (y : v.adicCompletion L) = 1 → χ (localIdele L v y) = 1) ∧
        z = χ (localIdele L v (ϖ v))}

end HeckeValGen
end
end

-- bundled from Formalism.UnipotentAdelicQuotients.GlobalNormIndexTwo
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.D.Classical

def GlobalNormIndexTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 →
    ∃! η : (AdeleRing (𝓞 F) F)ˣ →* Circle,
      Continuous η ∧
      (∀ a : Fˣ, η (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1) ∧
      (∀ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ,
        η (Units.map (Algebra.norm (AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F ⊗[F] E →* AdeleRing (𝓞 F) F) x) = 1) ∧
      η ≠ 1

end Formalism.D.Classical

end
end

-- bundled from Formalism.UnipotentAdelicQuotients.GordanCones
section
set_option autoImplicit false

namespace GordanCones

def toQ {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun i => (v i : ℚ)

def cone {n : ℕ} (s : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∃ c : (Fin n → ℤ) → ℚ, (∀ v ∈ s, 0 ≤ c v) ∧ x = ∑ v ∈ s, c v • toQ v}

def dualCone {n : ℕ} (A : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∀ a ∈ A, 0 ≤ ∑ i, (a i : ℚ) * x i}

def Lattice : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ t : Finset (Fin n → ℤ),
    {x : Fin n → ℤ | toQ x ∈ cone s} = {x | ∃ d : (Fin n → ℤ) → ℕ, x = ∑ v ∈ t, d v • v}

def GenIneq : Prop :=
  (∀ (n : ℕ) (A : Finset (Fin n → ℤ)), ∃ s : Finset (Fin n → ℤ), dualCone A = cone s) ∧
  (∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ A : Finset (Fin n → ℤ), cone s = dualCone A)

def Alternative : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j < b i) ↔
      ∃ y : Fin m → ℚ, (∀ i, 0 ≤ y i) ∧ y ≠ 0 ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i ≤ 0

end GordanCones
end

-- bundled from Formalism.UnipotentAdelicQuotients.HaarProductClosedCompact
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.D

def haarProductClosedCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ →
    μ ≠ 0 → ∀ P K : Subgroup G, IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ μP μK : Measure G, μP (P : Set G)ᶜ = 0 → (∀ p ∈ P, μP.map (fun x => p * x) = μP) →
      (∀ s : Set G, IsCompact s → μP s ≠ ⊤) → μP ≠ 0 →
      μK Set.univ = 1 → μK (K : Set G)ᶜ = 0 → (∀ k ∈ K, μK.map (fun x => k * x) = μK) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ Φ : G → ℝ≥0∞, Measurable Φ →
        ∫⁻ x, Φ x ∂μ = c * ∫⁻ p, (∫⁻ k, Φ (p * k) ∂μK) ∂μP

end Formalism.D

end
end


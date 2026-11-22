import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.FormalDegreeBessel.StatementG
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.Bundle0014
import Formalism.PeriodIntegrals.JointBlockShapes.JointShape
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.Bundle0016
import Formalism.SatakeDualWeyl.Bundle0001

-- bundled from Formalism.PeriodIntegrals.AdelicOrbitU
section
noncomputable section

namespace PI.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Vol

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

def AdelicOrbit : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F),
    IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    ∀ y : Fin 1 → Fin (M + 1) → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
      ∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y

end Vol

def AdelicOrbitQuad : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Module.finrank F E = 2 → (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) → AdelicOrbit F E σ

end PI.AdelicOrbitU
end
end

-- bundled from Formalism.PeriodIntegrals.BesselDeriv
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

section

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def thetaH (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  -(Hpk k r * Xᴴ * Hpk k r)

def dsigC (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  dsig (k := k) (r := r) σ ((1 / 2 : ℂ) • (X + thetaH k r X)) v +
    Complex.I • dsig (k := k) (r := r) σ ((-(Complex.I / 2)) • (X - thetaH k r X)) v

end

def BesselDeriv : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (B : H → Wp),
    IsDSHpk k r ε lam σ →
    (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B (v + w) = B v + B w) →
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, B (c • v) = c • B v) →
    IsCWCont (k := k) (r := r) σ B →
    ∀ (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (θ : ℝ), Y * Y * Y = 0 →
      (∀ t : ℝ, (1 + (t : ℂ) • Y + ((t : ℂ) ^ 2 / 2) • (Y * Y)) ∈ UH (Hpk k r)) →
      (∀ t : ℝ, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
        B (σ (1 + (t : ℂ) • Y + ((t : ℂ) ^ 2 / 2) • (Y * Y)) v) = Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) • B v) →
      ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ g ∈ UH (Hpk k r),
        (∀ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
          dsigC (k := k) (r := r) σ (Matrix.single i.1 i.2 1) w ∈ smoothVecs (k := k) (r := r) σ) ∧
        ((θ : ℂ) * Complex.I) • B (σ g w) =
          ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
            (g⁻¹ * Y * g) i.1 i.2 • B (σ g (dsigC (k := k) (r := r) σ (Matrix.single i.1 i.2 1) w))

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.BesselLevi
section
noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace PI.BesselLevi

def BesselLevi : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T → ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    s ∈ UH (Hpk k r) →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (s *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) i =
        (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) i) →
    s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))

end PI.BesselLevi
end
end

-- bundled from Formalism.PeriodIntegrals.FdegScale
section
noncomputable section

namespace PI

open PI.UpqRep

def FdegScale : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (s : NNReal), 0 < s → ∀ (lam : Fin n → ℝ), IsHCParam lam →
    ∃ d0 : ℝ, 0 < d0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (d : ℝ),
      IsDS ε lam σ → IsFdeg ((s : ENNReal) • muG ε) σ d → d = d0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FockDegreeTwoParts
section
noncomputable section

open Matrix FockH1Action

namespace PI.FockDegreeTwoParts

def WtDeg : Prop := ∀ p q r s : ℕ,
  (∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct1 p q r s) μ P →
    degW (cPair r s) μ ≤ d) ∧
  (∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct2 p q r s) μ P →
    degW (cPair p q) μ ≤ d)

def OneDeg : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d)

def JointMult : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s)) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s) = ⊥))

def HarmSplit : Prop := ∀ p q r s : ℕ,
  (∀ (u1 u2 : Bool), (u1 || u2) = true → ∀ d : ℕ,
    homog (Ix p q × Ix r s) (d + 2) =
      (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (lowKer p q r s u1 u2)) ⊔
      Submodule.span ℂ (raised p q r s u1 u2 d))

end PI.FockDegreeTwoParts
end
end

-- bundled from Formalism.PeriodIntegrals.FoldDCUnfold
section
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldDCUnfold

def FoldDCUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
    Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (g h : G → ℝ≥0∞), Measurable g → Measurable h →
    (∀ s ∈ S, ∀ y : G, g (s * y) = g y) → (∀ s ∈ S', ∀ y : G, h (s * y) = h y) →
    (∫⁻ x in FΓ, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, g x * h ((r : G)⁻¹ * x) ∂μ

end PI.FoldDCUnfold
end

-- bundled from Formalism.PeriodIntegrals.FoldMult
section
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldMult

def FoldMult : Prop :=
  ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G), DiscreteTopology Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
    (∀ x : G, 1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x) ∧
    (∀ x : G, Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤) ∧
    (∀ γ ∈ Γ, ∀ x : G, Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x) ∧
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω)

end PI.FoldMult
end

-- bundled from Formalism.PeriodIntegrals.FoldUnfold
section
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldUnfold

def FoldUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S : Subgroup G) [Countable Γ], S ≤ Γ →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (D : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
  ∀ (f : G → ℝ≥0∞), Measurable f → (∀ s ∈ S, ∀ y : G, f (s * y) = f y) →
    (∫⁻ x in FΓ, ∑' δ : D, f ((δ : G) * x) ∂μ) = ∫⁻ y in F, f y ∂μ

end PI.FoldUnfold
end

-- bundled from Formalism.PeriodIntegrals.GoodLatCM
section
open NumberField

namespace PI

namespace GoodLatCM

def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i

def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range

section Lat

variable {E : Type} [Field E] [NumberField E]

def gYY (MM : Submodule (𝓞 E) E) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) :
    Submodule (𝓞 E) (Matrix (Fin N') (Fin N) E) :=
  Submodule.span (𝓞 E)
    {B | ∃ a ∈ MM, ∃ A ∈ Submodule.span (𝓞 E) {A : Matrix (Fin N') (Fin N) E | ∀ x ∈ L, A.mulVec x ∈ L'}, B = a • A}

def gLa {S : Type} (emb : S → E →+* ℂ) (abelian₂ : AddSubgroup ℂ) (MM : Submodule (𝓞 E) E) {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) : AddSubgroup (S → Fin N' → Fin N → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ abelian₂, ∃ A ∈ gYY MM L L', z = w • (fun s i j => emb s (A i j))}

end Lat

end GoodLatCM

open GoodLatCM in

def GoodLatCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (K : IntermediateField ℚ E) (d : ℕ), Module.finrank ℚ K = 2 → NumberField.discr K = -(d : ℤ) → d % 4 = 3 →
  ∀ (φ₀ : E →+* ℂ) (S : Type) [Fintype S] (emb : S → E →+* ℂ), Function.Injective emb →
    (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) → Fintype.card S = Module.finrank K E →
  ∀ MM : Submodule (𝓞 E) E, MM.FG → MM ≠ ⊥ →
    (∀ x : E, x ∈ MM ↔ ∀ y ∈ MM, Algebra.trace K E (x * star y) ∈ (algebraMap (𝓞 K) K).range) →
  ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
  ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin N → E)) (L₁' L₂' : Submodule (𝓞 E) (Fin N' → E)),
    IsSDLat E N L₁ → IsSDLat E N' L₁' → IsSDLat E N L₂ → IsSDLat E N' L₂' →
    GoodLat (Real.sqrt d / 2) (area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}))
      (gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₁ L₁') ∧
    ((gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₁ L₁').addSubgroupOf
      (gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₂ L₂')).index ≠ 0

end PI
end

-- bundled from Formalism.PeriodIntegrals.LevelProdIdx
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI

open Formalism.UG in
def LevelProdIdx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ →
    (∀ x, x ∈ U ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v) →
    (∀ v, Uloc v ≤ levelVL σ J v Lb) →
    {v | Uloc v ≠ levelVL σ J v Lb}.Finite →
    (∀ v, (Uloc v).relIndex (levelVL σ J v Lb) ≠ 0) →
    U ≤ levelAfL σ J Lb ∧ U.relIndex (levelAfL σ J Lb) ≠ 0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.LocJacOrd
section
noncomputable section

namespace PI.LocJacOrd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def sdE (ι : Type) [Fintype ι] : Measure (ι → Fv F v ⊗[F] E) :=
  if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
  then h.choose else 0

end Meas

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

def locZ {r : ℕ} (z : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) (i j : Fin (r + 1)) : Fv F v ⊗[F] E :=
  sc (E := E) v (alp v r i * alp v r j) * z (i, j)

end Frames

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ZZOrd (r : ℕ) : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, locZ v z i j ∈ OEv (E := E) v}

def ZZTyp (g r : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, (locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v ∧
    ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ +
        sigR (Fv F v) σ ((locZ v z j i - TF j i) * sc (E := E) v (g : Fv F v)⁻¹) -
        (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def PPOrd (r : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  {c | sc (E := E) v (alp v r l ^ 2) * c ∈ OEv (E := E) v}

def PPTyp (g r T T' : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if (l : ℕ) < r then
    {c | sc (E := E) v (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v ∧
      sc (E := E) v (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c) ∈ OEv (E := E) v}
  else
    {c | sc (E := E) v (g : Fv F v)⁻¹ * (c + (T : Fv F v ⊗[F] E)) ∈ OEv (E := E) v ∧
      sc (E := E) v (((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c + (T : Fv F v ⊗[F] E) + (T' : Fv F v ⊗[F] E))
        ∈ OEv (E := E) v}

abbrev UIdx (r : ℕ) : Type := {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}

def UO (r : ℕ) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * x p ∈ OEv (E := E) v}

def localVolumeOrdinary (r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  UO v r ×ˢ UO v r

def deepCongruenceVolume (g r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  {p | p.1 ∈ UO v r ∧ p.2 ∈ UO v r ∧ ∀ q,
    sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2 * (g : Fv F v)⁻¹) * (p.1 q - p.2 q) ∈ OEv (E := E) v}

def volS {r : ℕ} (S : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) S).toReal

def volC (S : Set (Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v Unit ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' S)).toReal

def volU {r : ℕ} (S : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E))) : ℝ :=
  (((sdE (E := E) ψ v (UIdx r)).prod (sdE (E := E) ψ v (UIdx r))) S).toReal

def absV (x : Fv F v) : ℝ :=
  if h : Valued.v x = 0 then 0
  else ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero h))

def jacS (typed : Prop) (g r : ℕ) : ℝ :=
  ∏ l : Fin r, ((absV v ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), alp v r i ^ 2) *
    (if typed then ((g : Fv F v)⁻¹) ^ ((l : ℕ) + 1) else 1))) ^ 2) ^ 2

end Sets

section Stmt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def LocJacOrd : Prop :=
  ∀ (typed : Prop) (g r : ℕ), Module.finrank F E = 2 → ¬ typed →
    volS (E := E) ψ v (ZZOrd v r) * jacS v typed g r =
      volU (E := E) ψ v (localVolumeOrdinary v r) * ∏ l : Fin (r + 1), volC (E := E) ψ v (PPOrd v r l)

end Stmt

end PI.LocJacOrd
end
end

-- bundled from Formalism.PeriodIntegrals.LowCyc
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

def LowSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H), IsHCParam lam →
    IsDSHpk k r ε lam σ → IsLowUnitH k r ε lam σ w → w ∈ smoothVecs (k := k) (r := r) σ

def SmoothCyc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H), IsHCParam lam →
    IsDSHpk k r ε lam σ → IsLowUnitH k r ε lam σ w →
    ∀ x ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)),
    (∀ w' ∈ Ws, ∀ Y ∈ w', InLieHpk k r Y) → ∀ δ : ℝ, 0 < δ →
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ i, g i ∈ UH (Hpk k r)) ∧
      (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (x - ∑ i, c i • σ (g i) w)‖).sum < δ

end PI
end
end


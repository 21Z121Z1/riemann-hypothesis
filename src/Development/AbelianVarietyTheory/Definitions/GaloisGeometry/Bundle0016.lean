import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MZmix
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.W1
open scoped TensorProduct

namespace GlobalTheory.WH

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F) {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1))

def bI (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Finset (Fin (d + 1)) := lft (lft s) ∪ (rgt s).image p1

def bJ (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Finset (Fin (d + 1)) := rgt (lft s) ∪ (rgt s).image p2

def TZ (a : ℕ) (q : ℤ) (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Submodule ℂ (Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :=
  if (lft (lft s)).Nonempty ∧ (rgt (lft s)).Nonempty ∧ 0 < q then
    ⨅ i ∈ bI p1 s, ⨅ j ∈ bJ p2 s, kFam (YZ F K x) (XZ F K x i) (XZ F K x i ^ 0 * YZ F K x j) (MZ F K x a (bI p1 s) (bJ p2 s)) q
  else ⊥

def wZ (z : κ → K ⊗[ℂ] K) : (Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ → Module.End ℂ (Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :=
  fun t => match ofLex t with
    | Sum.inl _ => 1
    | Sum.inr l => pw (actZ K (z l))

def YZi : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.lTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x 0)⁻¹))

def topZ (c : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :
    Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K :=
  fun b => YZi F K x (c (uni b ∅) {0})

def MZmix (a : ℕ) : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  mixF fun I J => MZ F K x a I J

section Y

variable {F K} {K' : Type} [Field K'] [Algebra ℂ K'] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K']
  [IsScalarTower F K K'] [IsScalarTower ℂ F K']

def XY (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K') := (Algebra.lsmul ℂ ℂ (DR ℂ K')) (algebraMap F K' (x l))

def YY (j2 : K →ₐ[ℂ] K') (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K') :=
  (Algebra.lsmul ℂ ℂ (DR ℂ K')) (j2 (algebraMap F K (x l)))

def MY (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) : Submodule ℂ (DR ℂ K') := omB ℂ K' (RY x j2 I J) d

def TY (j2 : K →ₐ[ℂ] K') (q : ℤ) (s : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ)) : Submodule ℂ (Finset (Fin (d + 1)) → DR ℂ K') :=
  if (lft (lft s)).Nonempty ∧ (rgt (lft s)).Nonempty ∧ 0 < q then
    ⨅ i ∈ bI p1 s, ⨅ j ∈ bJ p2 s, kFam (YY x j2) (XY x i) (XY x i ^ 0 * YY x j2 j) (MY x j2 (bI p1 s) (bJ p2 s)) q
  else ⊥

def gz (j2 : K →ₐ[ℂ] K') (z : K ⊗[ℂ] K) : K' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ K K') j2 z

def wY (j2 : K →ₐ[ℂ] K') (z : κ → K ⊗[ℂ] K) : (Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ → Module.End ℂ (Finset (Fin (d + 1)) → DR ℂ K') :=
  fun t => match ofLex t with
    | Sum.inl _ => 1
    | Sum.inr l => pw ((Algebra.lsmul ℂ ℂ (DR ℂ K')) (gz j2 (z l)))

def topY (j2 : K →ₐ[ℂ] K') (c : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K') :
    Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → DR ℂ K' :=
  fun b => (Algebra.lsmul ℂ ℂ (DR ℂ K')) (j2 (algebraMap F K (x 0)))⁻¹ (c (uni b ∅) {0})

def MYmix (j2 : K →ₐ[ℂ] K') : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → Submodule ℂ (DR ℂ K') :=
  mixF fun I J => MY x j2 I J

end Y

end GlobalTheory.WH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatsushimaLattice
section
noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic MeasureTheory
open scoped Matrix ComplexOrder

namespace GlobalTheory.Mt

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

namespace CartanData

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

def IsAdm {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i j, D.lie.IsSmoothFun (F := ℂ) fun g => ξ g i j) ∧
  ∃ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef ∧ (∀ X ∈ D.p, Q * D.dξ ξ X = (D.dξ ξ X)ᴴ * Q) ∧
    ∀ X ∈ D.k, Q * D.dξ ξ X = -((D.dξ ξ X)ᴴ * Q)

def IsCCR {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) : Prop :=
  ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ∀ f : CompactlySupportedContinuousMap G ℂ, IsCompactOperator (π.integrated μ (UnitaryRep.ccToL1 μ f))

def repξ (Γ : Subgroup G) {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ Γ (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toRingEquiv.toMonoidHom.comp
    (ξ.comp Γ.subtype)

def MatsushimaAbs : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (d : ℕ) (ξ : G →* Matrix (Fin d) (Fin d) ℂ), IsCCR π → D.IsAdm ξ →
  ∀ (s : Set (Submodule ℂ H)) (hc : ∀ V : s, CompleteSpace (V : Submodule ℂ H)) (hinv : ∀ V : s, π.IsInvariant V),
    IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ H)) (fun V => (V : Submodule ℂ H).subtypeₗᵢ) →
    (∀ V : s, letI := hc V; (π.restrict V (hinv V)).IsIrreducible) →
    ∀ q, FiniteDimensional ℂ (D.HGK π ξ q) ∧
      {V : s | letI := hc V; Nontrivial (D.HGK (π.restrict V (hinv V)) ξ q)}.Finite ∧
      Module.finrank ℂ (D.HGK π ξ q) = ∑ᶠ V : s, letI := hc V; Module.finrank ℂ (D.HGK (π.restrict V (hinv V)) ξ q)

def MatsushimaLattice : Prop :=
  ∀ (Γ : Subgroup G) [DiscreteTopology Γ] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant], CompactSpace (GlobalTheory.AutomorphicL2Unitary.Quot Γ) →
  ∀ (π : UnitaryRep G (GlobalTheory.AutomorphicL2Unitary.L2 Γ μ)), (∀ g, (π.toHom g : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ →L[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) = GlobalTheory.AutomorphicL2Unitary.R Γ μ g) →
  ∀ (d : ℕ) (ξ : G →* Matrix (Fin d) (Fin d) ℂ), D.IsAdm ξ →
  ∀ q, Nonempty (groupCohomology (Rep.of (repξ Γ ξ)) q ≃ₗ[ℂ] D.HGK π ξ q)

end CartanData

end GlobalTheory.Mt
end
end


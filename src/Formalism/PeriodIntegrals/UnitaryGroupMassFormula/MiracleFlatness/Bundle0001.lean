import Mathlib
import Formalism.PeriodIntegrals.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.FromQuotTensorToQuotTensor

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.MiracleFlatOfRegSeqDepth
section
universe u

namespace PI.UnitaryGroupMassFormula.MF

open RingTheory.Sequence IsLocalRing

def RegSeqGen : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
    ∃ xs : List A, IsRegular A xs ∧ Ideal.ofList xs = maximalIdeal A ∧ (xs.length : WithBot ℕ∞) = ringKrullDim A

def AssDim : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R), IsRegular M rs → ∀ p ∈ associatedPrimes R M, (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)

def DepthDrop : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (x : R), IsRegular M rs → rs ≠ [] → x ∈ maximalIdeal R → IsSMulRegular M x →
      ∃ zs : List R, zs.length + 1 = rs.length ∧ IsRegular (QuotSMulTop x M) zs

def CMSop : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B],
    (∃ rs : List B, IsRegular B rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ (rs.length : WithBot ℕ∞) = ringKrullDim B) →
    ∀ xs : List B, (∀ x ∈ xs, x ∈ maximalIdeal B) →
      ringKrullDim B = (xs.length : WithBot ℕ∞) + ringKrullDim (B ⧸ Ideal.ofList xs) → IsRegular B xs

def CMSopOf : Prop := AssDim.{u} → DepthDrop.{u} → CMSop.{u}

def LocCrit : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] (x : A),
    IsSMulRegular A x → IsSMulRegular B (algebraMap A B x) → algebraMap A B x ∈ maximalIdeal B →
    Module.Flat (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B)) → Module.Flat A B

def FlatOfReg : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (xs : List A), IsRegular A xs → Ideal.ofList xs = maximalIdeal A →
    IsRegular B (xs.map (algebraMap A B)) → Module.Flat A B

def FlatOfRegOf : Prop := LocCrit.{u} → FlatOfReg.{u}

def Assembly : Prop := RegSeqGen.{u} → CMSop.{u} → FlatOfReg.{u} → PI.MiracleFlat.{u}

end PI.UnitaryGroupMassFormula.MF
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.MulXProjQExact
section
universe u v

open TensorProduct

namespace PI.UnitaryGroupMassFormula.MF

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

noncomputable def mulMap (𝔞 : Ideal A) : B ⊗[A] 𝔞 →ₗ[B] B :=
  (AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ AlgebraTensorModule.lTensor B B 𝔞.subtype

@[simp] lemma mulMap_tmul (𝔞 : Ideal A) (b : B) (a : 𝔞) : mulMap 𝔞 (b ⊗ₜ a) = (a : A) • b := by
  simp [mulMap]

variable (x : A)

noncomputable def mulX (𝔞 𝔟 : Ideal A) (h1 : ∀ b ∈ 𝔟, x * b ∈ 𝔞) : 𝔟 →ₗ[A] 𝔞 :=
  (LinearMap.mulLeft A x).restrict (p := 𝔟) (q := 𝔞) h1

@[simp] lemma mulX_apply (𝔞 𝔟 : Ideal A) (h1 : ∀ b ∈ 𝔟, x * b ∈ 𝔞) (b : 𝔟) :
    ((mulX x 𝔞 𝔟 h1 b : 𝔞) : A) = x * b := rfl

noncomputable def projQ (𝔞 : Ideal A) : 𝔞 →ₗ[A] (𝔞.map (Ideal.Quotient.mk (Ideal.span {x}))) where
  toFun a := ⟨Ideal.Quotient.mk _ a, Ideal.mem_map_of_mem _ a.2⟩
  map_add' a b := by ext; simp
  map_smul' c a := by
    ext
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

end PI.UnitaryGroupMassFormula.MF
end


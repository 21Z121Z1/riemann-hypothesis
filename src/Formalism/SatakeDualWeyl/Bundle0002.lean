import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.SatakeDualWeyl.Bundle0001

-- bundled from Formalism.SatakeDualWeyl.NablaRepApply
section
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG

def stdRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Representation O (GL n O) (n → O) where
  toFun := stdAct O n
  map_one' := (P.standard_action_mul_holds O n 1 1).2
  map_mul' g h := (P.standard_action_mul_holds O n g h).1

def tensRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (⨂[O]^k (n → O)) where
  toFun := tensAct O n k
  map_one' := (P.tensor_action_mul_holds O n k 1 1).2
  map_mul' g h := (P.tensor_action_mul_holds O n k g h).1

def polyRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Representation O (GL n O) (MvPolynomial n O) where
  toFun g := (polyAct O n g).toLinearMap
  map_one' := by
    rw [(P.polynomial_action_mul_holds O n 1 1).2, AlgHom.toLinearMap_id]
    rfl
  map_mul' g h := by
    rw [(P.polynomial_action_mul_holds O n g h).1, AlgHom.comp_toLinearMap]
    rfl

def nablaRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (nabla O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict (fun P hP => Formalism.UG.P.nabla_subspace_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl

def weylRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (weylSub O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict
    (fun P hP => Formalism.UG.P.weyl_module_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl

def ratEquiv {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : UJ (σ : E →+* E) J ≃* ratPts σ J R :=
  Subgroup.equivMapOfInjective (UJ (σ : E →+* E) J) (bc (inclE (F := F) R))
    (Formalism.UG.P.UG_inclusion_injective F E n R inferInstance)

theorem tensRep_apply (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
    (g : GL n O) : tensRep O n k g = tensAct O n k g := rfl

theorem polyRep_apply (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (g : GL n O) : polyRep O n g = (polyAct O n g).toLinearMap := rfl

end Formalism.UG
end
end

-- bundled from Formalism.SatakeDualWeyl.StatementG
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.UG

def IsInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal

def InertLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), σ ≠ AlgHom.id F E → (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w →
    ∃ (e : E ⊗[F] v.adicCompletion F ≃+* w.adicCompletion E) (σw : w.adicCompletion E →+* w.adicCompletion E)
      (ϖ : w.adicCompletion E),
      (∀ x, e (sigR σ (v.adicCompletion F) x) = σw (e x)) ∧ IsUnramInv ϖ σw (qV F v) ∧
      ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v) ↔ e x ∈ intL (w.adicCompletion E)

def InertAntidiag : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Odd q →
    ∃ P : GL (Fin n) L, P ∈ (bc (n := Fin n) (intL L).subtype).range ∧
      cT σ (P : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = antiJ L n

def LocInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (e : E ⊗[F] v.adicCompletion F ≃+* L) (σw : L →+* L) (P : GL (Fin n) L),
    (∀ x, e (sigR σ (v.adicCompletion F) x) = σw (e x)) →
    (∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v) ↔ e x ∈ intL L) →
    P ∈ (bc (n := Fin n) (intL L).subtype).range →
    cT σw (P : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = antiJ L n →
    ∃ f : UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ≃* GU σw n,
      (∀ x, ((f x : GU σw n) : GL (Fin n) L) = P⁻¹ * bc (e : E ⊗[F] v.adicCompletion F →+* L) x * P) ∧
      ((levelV σ (1 : Matrix (Fin n) (Fin n) E) v).subgroupOf
          (UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))).map f.toMonoidHom = KU σw n

end Formalism.UG
end
end


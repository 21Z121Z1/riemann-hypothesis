import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatDimFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatDimFormula.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

abbrev primeFibreLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal S)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap S (Localization.AtPrime P)) (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P))

def FlatNormalFibres.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S],
    IsNoetherianRing R → IsNoetherianRing S → IsLocalRing S → Module.Flat R S →
      IsDomain R → IsIntegrallyClosed R →
      (∀ (P : Ideal S) [P.IsPrime],
        IsDomain (primeFibreLocalRing R P) ∧ IsIntegrallyClosed (primeFibreLocalRing R P)) →
        IsDomain S ∧ IsIntegrallyClosed S

noncomputable def primeFibreLocalRing_complex_equiv (P : Ideal ℂ) [P.IsPrime] :
    primeFibreLocalRing ℂ P ≃+* ℂ := by
  have hP : P = ⊥ := (Ideal.eq_bot_or_top P).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  have hmap : Ideal.map (algebraMap ℂ (Localization.AtPrime P))
      (Ideal.map (algebraMap ℂ ℂ) (Ideal.comap (algebraMap ℂ ℂ) P)) = ⊥ := by
    subst hP
    simp
  refine (Ideal.quotEquivOfEq hmap).trans (RingEquiv.quotientBot _) |>.trans ?_
  exact (IsLocalization.atUnits ℂ P.primeCompl (fun x hx => by
    subst hP
    exact isUnit_iff_ne_zero.2 (by simpa using hx))).toRingEquiv.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGeneralProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix

noncomputable section

def GeneralProjection.Statement : Prop :=
  ∀ (n d m : ℕ) (L : Fin m → (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)), (∀ b, Function.Injective (L b)) →
    ∃ π : Matrix (Fin d) (Fin n) ℂ, ∀ b, Function.Injective fun v => π *ᵥ L b v

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericFibreRadical.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsRadical → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IsRadicalAway {R : Type*} [CommRing R] (K : Ideal R) (g : R) : Prop :=
  ∀ f ∈ K.radical, ∃ k : ℕ, g ^ k * f ∈ K

def fibreIdeal {σ : Type*} {n : ℕ} (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ))) (t : σ → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  K.map (MvPolynomial.map (eval t))

theorem fibreIdeal_map_C {σ : Type*} {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (t : σ → ℂ) :
    fibreIdeal (J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ))) t = J := by
  have h : (MvPolynomial.map (eval t)).comp (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ)) =
      RingHom.id (MvPolynomial (Fin n) ℂ) := by
    ext p <;> simp
  rw [fibreIdeal, Ideal.map_map, h, Ideal.map_id]

def GenericFibreRadicalAway.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (n : ℕ) (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ)))
    (g : MvPolynomial (Fin n) (MvPolynomial σ ℂ)), IsRadicalAway K g →
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      IsRadicalAway (fibreIdeal K t) (MvPolynomial.map (eval t) g)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericFibreRadicalPrime.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsPrime → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreTor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ker_fibreMap {σ ι : Type*} (t : σ → ℂ) :
    RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) =
      (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) :=
  MvPolynomial.ker_map _

def GenericFibreTor.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      L ⊓ RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤
        RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) * L

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFreeness
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

def GenericFreeness.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M],
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u

def GenericNoetherNormalisation.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (q : Ideal (MvPolynomial (Fin (n + 1)) A)),
    q.IsPrime → q ≠ ⊥ → q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥ →
    ∃ a : A, a ≠ 0 ∧ ∃ (z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q)
      (s : Finset (MvPolynomial (Fin (n + 1)) A ⧸ q)),
      ∀ d : MvPolynomial (Fin (n + 1)) A ⧸ q, ∃ (k : ℕ) (c : MvPolynomial (Fin (n + 1)) A ⧸ q → MvPolynomial (Fin n) A),
        a ^ k • d = ∑ t ∈ s, aeval z (c t) * t

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def GenericPrimitive.Statement : Prop :=
  ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (n : ℕ) (x : Fin n → L),
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      ∃ D : MvPolynomial (Fin n) k, D ≠ 0 ∧ ∀ c : Fin n → k, MvPolynomial.eval c D ≠ 0 →
        IntermediateField.adjoin K {∑ j, c j • x j} = ⊤

theorem adjoin_real_I : IntermediateField.adjoin ℝ {Complex.I} = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  rw [← Complex.re_add_im z]
  have hI := IntermediateField.mem_adjoin_simple_self ℝ Complex.I
  have hre : (z.re : ℂ) ∈ IntermediateField.adjoin ℝ {Complex.I} :=
    IntermediateField.algebraMap_mem _ z.re
  have him : (z.im : ℂ) ∈ IntermediateField.adjoin ℝ {Complex.I} :=
    IntermediateField.algebraMap_mem _ z.im
  exact add_mem hre (mul_mem him hI)

theorem GenericPrimitive.hypotheses_inhabited :
    IsScalarTower ℚ ℝ ℂ ∧ FiniteDimensional ℝ ℂ ∧ Algebra.IsSeparable ℝ ℂ ∧
      IntermediateField.adjoin ℝ (Set.range ![Complex.I]) = ⊤ := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  exact adjoin_real_I

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def graphJac {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  √(LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
    LinearMap.adjoint B ∘ₗ B))

def GraphJacContinuous.Statement : Prop :=
  ∀ (k m : ℕ) (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ε : ℝ), 0 < ε →
    ∃ r : ℝ, 0 < r ∧ ∀ B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m), ‖B - A‖ ≤ r →
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∧
        graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGridProductLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GridProductLowerBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (N : ℕ) (Z : Set (σ → ℂ)) (z₀ : σ → ℂ),
    Bornology.IsBounded Z → z₀ ∉ closure Z →
    ∃ μ : ℝ, 0 < μ ∧ ∃ U ∈ 𝓝 z₀, ∀ z ∈ U, ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) ⊆ Z → s.card ≤ N →
      ∃ u : σ → Fin (N + 1), μ ≤ ‖∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)‖

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end


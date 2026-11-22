import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreLocalUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsolatedFibreLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B, (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ B ∩ W, A x = A w → x = w) →
    ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), M ∈ 𝓝 w ∧ AnalyticAt ℂ g (A w) ∧
      (¬ ∀ᶠ y in 𝓝 (A w), g y = 0) ∧
      ∀ x ∈ X ∩ B ∩ M, g (A x) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutGlobal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutGlobal.Statement : Prop :=
  ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
    IsNilpotent P → IsPrincipalIdealRing (C ⧸ P) → y ∉ P → (P ⊔ Ideal.span {y}).IsMaximal →
      (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (M ⧸ (Ideal.span {y} • ⊤ : Submodule C M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutLocalizedModule.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B) (Q₀ : Ideal B) [Q₀.IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M],
    IsNilpotent P → y ∉ P → Q₀ = P ⊔ Ideal.span {y} → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length (Localization.AtPrime Q₀)
          (LocalizedModule Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M))) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedLocalized
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthLocalizedLocalized.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M],
    P ≤ Q →
      Module.length (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (LocalizedModule (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
            (LocalizedModule Q.primeCompl M)) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

theorem LengthLocalizedLocalized.map_isPrime (B : Type u) [CommRing B] (P Q : Ideal B) [hP : P.IsPrime]
    [Q.IsPrime] (h : P ≤ Q) : (P.map (algebraMap B (Localization.AtPrime Q))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hP
    (Set.disjoint_left.mpr fun _ hx hxP => hx (h hxP))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def LengthLocalizedQuotient.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B),
    minimalPrimes B = {P} → (∀ s ∉ P, s ∈ nonZeroDivisors B) → y ∉ P →
    ∀ (Q : Ideal (B ⧸ Ideal.span {y})) [Q.IsPrime], Q.comap (Ideal.Quotient.mk _) = P ⊔ Ideal.span {y} →
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizationAtPrimeQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

def LocalizationAtPrimeQuotient.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A) (T : Submonoid (A ⧸ I)) (P : Ideal (Localization T)) [P.IsPrime]
    (W : Ideal A) [W.IsPrime],
    P.comap ((algebraMap (A ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) = W →
      ∃ e : Localization.AtPrime P ≃+* (Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))),
        ∀ a : A,
          e (algebraMap (Localization T) (Localization.AtPrime P)
              (algebraMap (A ⧸ I) (Localization T) (Ideal.Quotient.mk I a))) =
            Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime W)))
              (algebraMap A (Localization.AtPrime W) a)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizeQuotientStages
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem isPrime_map_quotient_localization {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by
  rw [← Ideal.map_map]
  have hd : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) W ‹_› hd
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.map_mono hIW)

def LocalizeQuotientStages.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime], W ≤ m → I ≤ W →
    ∀ (P : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))) [P.IsPrime],
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) = P →
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) =
        Module.length (Localization.AtPrime W)
          (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNonIsolatedFibreCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

def NonIsolatedFibreCurve.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (p : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → p ∈ U → AccPt p (𝓟 {v | v ∈ U ∧ f v = f p}) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → Fin k → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = p ∧
          Set.MapsTo γ (ball 0 r) {v | v ∈ U ∧ f v = f p}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def zeroSetIn {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) : Set (σ → ℂ) :=
  {z | ∀ q ∈ I, eval z q = 0}

def firstCoords {n m : ℕ} (w : Fin n ⊕ Fin m → ℂ) : Fin n → ℂ :=
  fun i => w (Sum.inl i)

structure NormalModel {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) where

  m : ℕ

  ideal : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)
  isPrime : ideal.IsPrime
  isIntegrallyClosed : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ ideal)
  comap_eq : ideal.comap
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ) = J
  integral : ∀ i : Fin m, ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P.Monic ∧
    P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ ideal
  birational : ∀ i : Fin m, ∃ a b : MvPolynomial (Fin n) ℂ, b ∉ J ∧
    rename Sum.inl b * X (Sum.inr i) - rename Sum.inl a ∈ ideal

def lineDiagonalMap : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval (Sum.elim X fun _ => X 0)

theorem lineDiagonalMap_rename (q : MvPolynomial (Fin 1) ℂ) : lineDiagonalMap (rename Sum.inl q) = q := by
  rw [lineDiagonalMap, aeval_rename]
  exact aeval_X_left_apply q

theorem lineDiagonalMap_surjective : Function.Surjective lineDiagonalMap :=
  fun q => ⟨rename Sum.inl q, lineDiagonalMap_rename q⟩

def lineDiagonalIdeal : Ideal (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) :=
  RingHom.ker lineDiagonalMap.toRingHom

theorem lineDiagonalIdeal_isPrime : lineDiagonalIdeal.IsPrime :=
  RingHom.ker_isPrime _

theorem lineDiagonalIdeal_isIntegrallyClosed :
    IsIntegrallyClosed (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ ⧸ lineDiagonalIdeal) :=
  IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective
    (f := lineDiagonalMap.toRingHom) lineDiagonalMap_surjective).symm

def lineDiagonalModel : NormalModel (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) where
  m := 1
  ideal := lineDiagonalIdeal
  isPrime := lineDiagonalIdeal_isPrime
  isIntegrallyClosed := lineDiagonalIdeal_isIntegrallyClosed
  comap_eq := by
    ext q
    rw [Ideal.mem_comap, Ideal.mem_bot]
    show lineDiagonalMap (rename Sum.inl q) = 0 ↔ q = 0
    rw [lineDiagonalMap_rename]
  integral := fun i => ⟨Polynomial.X - Polynomial.C (X 0), Polynomial.monic_X_sub_C _, by
    show lineDiagonalMap _ = 0
    simp [lineDiagonalMap, Polynomial.eval₂_sub]⟩
  birational := fun i => ⟨X 0, 1, by simp, by
    show lineDiagonalMap _ = 0
    simp [lineDiagonalMap]⟩

theorem eval_const_of_lineDiagonalMap_eq_zero (c : ℂ) (q : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ)
    (hq : lineDiagonalMap q = 0) : eval (fun _ => c) q = 0 := by
  have h2 : ((aeval (fun _ : Fin 1 => c)).comp lineDiagonalMap) q = 0 := by
    rw [AlgHom.comp_apply, hq, map_zero]
  rw [lineDiagonalMap, MvPolynomial.comp_aeval] at h2
  have hpt : (fun i : Fin 1 ⊕ Fin 1 => (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ)
      (Sum.elim (X : Fin 1 → MvPolynomial (Fin 1) ℂ) (fun _ => X 0) i)) = fun _ => c := by
    funext s
    rcases s with i | i <;> simp
  rw [hpt] at h2
  rw [← coe_aeval_eq_eval]
  exact h2

theorem const_mem_zeroSetIn_lineDiagonal (c : ℂ) :
    (fun _ => c : Fin 1 ⊕ Fin 1 → ℂ) ∈ zeroSetIn lineDiagonalIdeal :=
  fun q hq => eval_const_of_lineDiagonalMap_eq_zero c q hq

theorem X_inl_not_mem_lineDiagonalIdeal :
    (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) ∉ lineDiagonalIdeal := by
  intro hX
  have h1 : lineDiagonalMap (X (Sum.inl 0)) = 0 := hX
  simp [lineDiagonalMap] at h1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametricCircleIntegralAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

noncomputable section

def ParametricCircleIntegralAnalytic.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ : (ι → ℂ) × ℂ → ℂ) (O : Set ((ι → ℂ) × ℂ)) (U : Set (ι → ℂ)) (c : ℂ) (r : ℝ),
    0 ≤ r → IsOpen O → IsOpen U → DifferentiableOn ℂ Φ O →
    (∀ x ∈ U, ∀ s ∈ sphere c r, (x, s) ∈ O) →
    AnalyticOnNhd ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) U

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyKaehlerFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolyKaehlerFree.Statement : Prop :=
  ∀ (R k : Type) [Field R] [Field k] [Algebra R k] (n : ℕ),
    Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄R]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialChartInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def PolynomialChartInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (k : ℕ) (t : MvPolynomial σ ℂ) (f : Fin k → MvPolynomial σ ℂ) (w : σ → ℂ),
    k + 1 = Fintype.card σ →
    LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
      Fin (k + 1) → σ → ℂ) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) {z | z ∈ U ∧ ∀ j, eval z (f j) = 0}

end

end GroundTheory.Heights₂.Heights
end


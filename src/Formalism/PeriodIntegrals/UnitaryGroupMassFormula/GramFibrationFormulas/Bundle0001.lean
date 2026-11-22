import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.AdelicVectorDecomposition
section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def LocalFieldInstances : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Module.finrank F E = 2 → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    (∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (Fv F v) ∧ SecondCountableTopology (Fv F v) ∧
      IsTopologicalRing (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧
      LocallyCompactSpace (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧
      BorelSpace (Fv F v ⊗[F] E)) ∧
    (IsTopologicalRing (Ainf F ⊗[F] E) ∧ T2Space (Ainf F ⊗[F] E) ∧ LocallyCompactSpace (Ainf F ⊗[F] E) ∧
      SecondCountableTopology (Ainf F ⊗[F] E) ∧ BorelSpace (Ainf F ⊗[F] E)) ∧
    (IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧ LocallyCompactSpace (AF F ⊗[F] E) ∧
      SecondCountableTopology (AF F ⊗[F] E) ∧ BorelSpace (AF F ⊗[F] E)) ∧
    (IsTopologicalGroup (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) ∧ LocallyCompactSpace (HA (AF F) σ J) ∧
      SecondCountableTopology (HA (AF F) σ J) ∧ BorelSpace (HA (AF F) σ J))

def AdelicVectorDecomposition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E),
    IsHomeomorph (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    (∀ X : Fin n → Fin M → Af F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧
    Function.Injective (fun (X : Fin n → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) => projV v X) ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      let P := {X : Fin n → Fin M → Af F ⊗[F] E |
        ∀ v, (v ∈ S → projV v X ∈ U v) ∧ (v ∉ S → projV v X ∈ latV b v)}
      ((∀ v ∈ S, IsOpen (U v)) → IsOpen P) ∧ ((∀ v ∈ S, IsCompact (U v)) → IsCompact P)

def RationalPointsLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J) ∧
    (∀ n : ℕ, DiscreteTopology (Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _)) ∧
      ∃ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K ∧
        ∀ Y, ∃ X : Fin n → Fin M → E, Y - ratTup (F := F) (AF F) X ∈ K) ∧
    (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure) ∧
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ

def GoodPlacesCofinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
      Set.Finite {v : HeightOneSpectrum (𝓞 F) | ¬ IsGoodV b σ J v (psiV F ψ v)}

def AdelicCharacterExistence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ) ∧
    (∀ ψ ψ' : AddChar (AF F) ℂ, IsCharAF F ψ → IsCharAF F ψ' →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x)) ∧
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ y : AF F,
      (∀ a : F, ψ (algebraMap F (AF F) a * y) = 1) → ∃ c : F, y = algebraMap F (AF F) c

def SelfDualMeasuresExist : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ,
    (∃ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))) ∧
    (∃ ν : Measure (HermR (Ainf F) σ n), SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S'))) ∧
    (∃ ν : Measure (Ainf F), SelfDual ν (fun s t => psiInf F ψ (s * t))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∃ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
        (IsGoodV b σ J v (psiV F ψ v) → μ (latV b v) = 1)) ∧
      (∃ ν : Measure (HermR (Fv F v) σ n), SelfDual ν (fun S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S')) ∧
        (IsGoodV b σ J v (psiV F ψ v) →
          ν {S | ∀ a c, (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ latE b v} = 1)) ∧
      (∃ ν : Measure (Fv F v), SelfDual ν (fun s t => psiV F ψ v (s * t)) ∧
        (IsGoodV b σ J v (psiV F ψ v) → ν (v.adicCompletionIntegers F) = 1))

end PI.GramFibrationFormulas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.FundamentalDomainPigeonhole
section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def LocData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) : Prop :=
  IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧
  SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
  SelfDual ν (fun S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S'))

def IsGramFib {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n))
    (fib : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | FreeT (F := F) (E := E) (Fv F v) X} ν Set.univ fib

def FreeFramesOpenConull : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (M n : ℕ), n ≤ M →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure →
      IsOpen {X : Fin n → Fin M → Fv F v ⊗[F] E | FreeT (F := F) (E := E) (Fv F v) X} ∧ μ {X | ¬ FreeT (F := F) (E := E) (Fv F v) X} = 0) ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | FreeT (F := F) (E := E) (Ainf F) X} ∧ μ {X | ¬ FreeT (F := F) (E := E) (Ainf F) X} = 0

def GramMapFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M →
    ∃ fib, IsGramFib σ J v μ ν fib ∧
      (∀ (S : HermR (Fv F v) σ n) (U : Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsOpen U →
        (U ∩ XT (Fv F v) σ J S.1).Nonempty → 0 < fib S U) ∧
      ∀ S : HermR (Fv F v) σ n, IsUnit S.1.det →
        ∀ K, IsCompact K → fib S K < ⊤

def GramFibreFamilyUnique : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M →
    ∀ fib fib', IsGramFib σ J v μ ν fib → IsGramFib σ J v μ ν fib' → fib = fib'

def HaarScalingGramMap : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M → ∀ fib, IsGramFib σ J v μ ν fib →
    (∀ (g : GL (Fin n) (Fv F v ⊗[F] E)) (c c' : ℝ≥0∞),
      (∀ A, MeasurableSet A → μ ((fun X => tupMul (Fv F v) X (g⁻¹ : GL (Fin n) _).val) ⁻¹' A) = c * μ A) →
      (∀ A : Set (HermR (Fv F v) σ n), MeasurableSet A →
        ν {S | ∃ S' ∈ A, S.1 = starT (Fv F v) σ g.val * S'.1 * g.val} = c' * ν A) →
      c' ≠ 0 → c' ≠ ⊤ →
      ∀ (S S' : HermR (Fv F v) σ n), S'.1 = starT (Fv F v) σ g.val * S.1 * g.val →
        ∀ φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞, Measurable φ →
          ∫⁻ X, φ X ∂(fib S') = c / c' * ∫⁻ X, φ (tupMul (Fv F v) X g.val) ∂(fib S)) ∧
    ∀ (h : HA (Fv F v) σ J) (S : HermR (Fv F v) σ n), (fib S).map (fun X => h • X) = fib S

def WittTransitivityFreeFrames : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X X' : Fin n → Fin M → E, LinearIndependent E X → LinearIndependent E X' →
      gramE σ J X = gramE σ J X' →
      ∃ g : GL (Fin M) E, g ∈ Formalism.UG.UJ (σ : E →+* E) J ∧ ∀ a, (g : Matrix (Fin M) (Fin M) E).mulVec (X a) = X' a) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (X X' : Fin n → Fin M → Fv F v ⊗[F] E), FreeT (F := F) (E := E) (Fv F v) X →
      FreeT (F := F) (E := E) (Fv F v) X' → gramR (Fv F v) σ J X = gramR (Fv F v) σ J X' →
      ∃ h : HA (Fv F v) σ J, h • X = X'

def GoodPlaceOrthonormalLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), IsGoodV b σ J v (psiV F ψ v) →
    (∃ e : Fin M → Fin M → Fv F v ⊗[F] E, (∀ i, e i ∈ latW b v) ∧
      (∀ i j, hR (Fv F v) σ J (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ y ∈ latW (M := M) b v, ∃ c : Fin M → Fv F v ⊗[F] E, (∀ i, c i ∈ latE b v) ∧ y = ∑ i, c i • e i) ∧
    (∀ x ∈ latW (M := M) b v, (Valued.v (qR (Fv F v) σ J x)) = 1 →
      ∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x y = 1) ∧
    ∀ β : Fv F v, (Valued.v β = 1 ∨ β = 0) →
      ∀ x ∈ latW (M := M) b v, ∀ x' ∈ latW (M := M) b v,
        (∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x y = 1) → (∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x' y = 1) →
        qR (Fv F v) σ J x = β → qR (Fv F v) σ J x' = β →
        ∃ h : HA (Fv F v) σ J, (∀ y, y ∈ latW (M := M) b v ↔ (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec y ∈ latW b v) ∧
          (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec x = x'

def FundamentalDomainPigeonhole : Prop :=
  ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (Λ : AddSubgroup G) [Countable Λ] (D : Set G), IsAddFundamentalDomain Λ D μ → μ D = 1 →
    ∀ Ω₀ : Set G, MeasurableSet Ω₀ → 1 < μ Ω₀ → ∃ l ∈ Λ, l ≠ 0 ∧ ∃ x ∈ Ω₀, ∃ y ∈ Ω₀, l = x - y

end PI.GramFibrationFormulas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.SL2AdelicReductionTheory
section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def rationalSL2 (F : Type) [Field F] [NumberField F] : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (AF F)) :=
  (Matrix.SpecialLinearGroup.map (algebraMap F (AF F))).range

def SL2AdelicReductionTheory : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∃ (ω : Set (AF F)) (C : Set (Matrix.SpecialLinearGroup (Fin 2) (AF F))) (t₀ : ℝ),
      IsCompact ω ∧ IsCompact C ∧ 0 < t₀ ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) (AF F), ∃ γ ∈ rationalSL2 F, ∃ y ∈ ω, ∃ T : ℝ, t₀ ≤ T ∧
        ∃ a a' : Ainf F, (∀ w, a w * a' w = 1 ∧ ‖a w‖ = T) ∧ ∃ c ∈ C,
          ((γ * g : Matrix.SpecialLinearGroup (Fin 2) (AF F)) : Matrix (Fin 2) (Fin 2) (AF F)) =
            !![1, y; 0, 1] * !![pairA F a 1, 0; 0, pairA F a' 1] * (c : Matrix (Fin 2) (Fin 2) (AF F))) ∧
    letI : MeasurableSpace (Matrix.SpecialLinearGroup (Fin 2) (AF F)) := borel _
    ∃ μ : Measure (Matrix.SpecialLinearGroup (Fin 2) (AF F)), μ.IsHaarMeasure ∧
      ∃ 𝓕, IsFundamentalDomain (rationalSL2 F) 𝓕 μ ∧ μ 𝓕 < ⊤

end PI.GramFibrationFormulas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.WeilRepresentationIrreducible
section
open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def B1 (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin M → Fv F v ⊗[F] E) : Fv F v :=
  Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J x y)

def rhoH {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → Fv F v ⊗[F] E) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => χ (B1 σ J v u y + B1 σ J v x y / 2) * φ (u + x)

def opU {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Fv F v) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => χ (b * qR (Fv F v) σ J u) * φ u

def modW {d M : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (a : Fv F v) : ℝ≥0∞ :=
  μ ((fun u => a • u) '' latW b v) / μ (latW b v)

def opD {d M : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (a : Fv F v) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) :
    (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => (((modW b μ a).toReal ^ (1 / 2 : ℝ) : ℝ) : ℂ) * φ (a • u)

def opF {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => ∫ s, φ s * χ (B1 σ J v s u) ∂μ

def Fstar {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) (b : Fv F v) : ℂ :=
  ∫ x, φ x * χ (b * qR (Fv F v) σ J x) ∂μ

def l2 {V : Type} [MeasurableSpace V] (μ : Measure V) (φ : V → ℂ) : ℝ := ∫ x, ‖φ x‖ ^ 2 ∂μ

def OmV {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (g : Matrix (Fin 2) (Fin 2) (Fv F v)) :
    Set (((Fin M → Fv F v ⊗[F] E) → ℂ) →ₗ[ℂ] ((Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  {T | (∀ φ, IsSB φ → IsSB (T φ) ∧ l2 μ (T φ) = l2 μ φ) ∧
    ∀ x y φ, IsSB φ → rhoH χ σ J x y (T φ) = T (rhoH χ σ J (g 0 0 • x + g 1 0 • y) (g 0 1 • x + g 1 1 • y) φ)}

def LocDataV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ SelfDual μ (fun x y => psiV F ψ v (B1 σ J v x y))

def WeilRepresentationIrreducible : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    ∀ T : ((Fin M → Fv F v ⊗[F] E) → ℂ) →ₗ[ℂ] ((Fin M → Fv F v ⊗[F] E) → ℂ),
      (∀ φ, IsSB φ → IsSB (T φ)) →
      (∀ x y φ, IsSB φ → T (rhoH (psiV F ψ v) σ J x y φ) = rhoH (psiV F ψ v) σ J x y (T φ)) →
      ∃ c : ℂ, ∀ φ, IsSB φ → T φ = c • φ

def WeilOperatorsPreserveSchwartz : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    ∀ φ : (Fin M → Fv F v ⊗[F] E) → ℂ, IsSB φ →
      (∀ c : Fv F v, IsSB (opU χ σ J c φ) ∧ l2 μ (opU χ σ J c φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opU χ σ J c φ) = opU χ σ J c (rhoH χ σ J x (y + c • x) φ)) ∧
      (∀ a : Fv F v, a ≠ 0 → IsSB (opD b μ a φ) ∧ l2 μ (opD b μ a φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opD b μ a φ) = opD b μ a (rhoH χ σ J (a • x) (a⁻¹ • y) φ)) ∧
      (IsSB (opF χ σ J μ φ) ∧ l2 μ (opF χ σ J μ φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opF χ σ J μ φ) = opF χ σ J μ (rhoH χ σ J (-y) x φ)) ∧
      ∀ h : HA (Fv F v) σ J, let hv := fun u => (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec u
        (∀ c, opU χ σ J c (φ ∘ hv) = opU χ σ J c φ ∘ hv) ∧ (∀ a, opD b μ a (φ ∘ hv) = opD b μ a φ ∘ hv) ∧
        opF χ σ J μ (φ ∘ hv) = opF χ σ J μ φ ∘ hv

def MetaplecticOperatorClasses : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    (∀ g : Matrix (Fin 2) (Fin 2) (Fv F v), g.det = 1 → (OmV χ σ J μ g).Nonempty) ∧
    (∀ g g' T T', T ∈ OmV χ σ J μ g → T' ∈ OmV χ σ J μ g' → T.comp T' ∈ OmV χ σ J μ (g * g')) ∧
    (∀ g T T', T ∈ OmV χ σ J μ g → T' ∈ OmV χ σ J μ g → g.det = 1 →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, IsSB φ → T' φ = c • T φ) ∧
    (∀ c : Fv F v, ∃ T ∈ OmV χ σ J μ !![1, c; 0, 1], ∀ φ, IsSB φ → T φ = opU χ σ J c φ) ∧
    (∀ a : Fv F v, a ≠ 0 → ∃ T ∈ OmV χ σ J μ !![a, 0; 0, a⁻¹], ∀ φ, IsSB φ → T φ = opD b μ a φ) ∧
    ∃ T ∈ OmV χ σ J μ !![0, 1; -1, 0], ∀ φ, IsSB φ → T φ = opF χ σ J μ φ

def WeilIndexFourierFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    let r := fun β : Fv F v => (modW b μ β).toReal ^ (-(1 / 2 : ℝ))
    ∃ γ : Fv F v → ℂ, (∀ β, β ≠ 0 → ‖γ β‖ = 1) ∧
      (∀ β : Fv F v, β ≠ 0 → ∀ φ, IsSB φ →
        Fstar χ σ J μ (opF χ σ J μ φ) β = γ β * (r β : ℂ) * Fstar χ σ J μ φ (-1 / β)) ∧
      (∀ φ, IsSB φ → ∃ C : ℝ, ∀ β : Fv F v, β ≠ 0 → ‖Fstar χ σ J μ φ β‖ ≤ C * min 1 (r β)) ∧
      (IsGoodV b σ J v χ →
        (∀ β ∈ v.adicCompletionIntegers F, Fstar χ σ J μ ((latW b v).indicator 1) β = 1) ∧
        (∀ β ∉ v.adicCompletionIntegers F, ‖Fstar χ σ J μ ((latW b v).indicator 1) β‖ = r β) ∧
        ∀ β : Fv F v, Valued.v β = 1 → γ β = 1)

def MaximalCompactFiniteness : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    let K := {k : Matrix (Fin 2) (Fin 2) (Fv F v) | k.det = 1 ∧ ∀ i j, k i j ∈ v.adicCompletionIntegers F}
    (∀ φ, IsSB φ → ∃ (N : ℕ) (φs : Fin N → (Fin M → Fv F v ⊗[F] E) → ℂ), (∀ j, IsSB (φs j)) ∧
      ∀ k ∈ K, ∀ T ∈ OmV χ σ J μ k, ∃ j, ∃ c : ℂ, ‖c‖ = 1 ∧ T φ = c • φs j) ∧
    (IsGoodV b σ J v χ → ∀ k ∈ K, ∀ T ∈ OmV χ σ J μ k, ∃ c : ℂ, ‖c‖ = 1 ∧
      T ((latW b v).indicator 1) = c • (latW b v).indicator 1)

end Fin

def RealGaussianWeilIndex : Prop :=
  ∀ (M : ℕ) (η : Fin (2 * M) → ℝ) (ε : ℝ), (∀ l, η l = 1 ∨ η l = -1) → (ε = 1 ∨ ε = -1) →
    let q := fun u : Fin (2 * M) → ℝ => ∑ l, η l * u l ^ 2
    let qp := fun u : Fin (2 * M) → ℝ => ∑ l, u l ^ 2
    let B := fun u u' : Fin (2 * M) → ℝ => 2 * ∑ l, η l * u l * u' l
    let φ := fun (τ : ℂ) (u : Fin (2 * M) → ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * ε * τ.re * q u - 2 * Real.pi * τ.im * qp u)
    ∀ τ : ℂ, 0 < τ.im → ∃ c : ℂ, c ≠ 0 ∧ ∀ u' : Fin (2 * M) → ℝ,
      (2 : ℂ) ^ M * ∫ u, φ τ u * Complex.exp (2 * Real.pi * Complex.I * ε * B u u') = c * φ (-1 / τ) u'

end PI.GramFibrationFormulas
end
end


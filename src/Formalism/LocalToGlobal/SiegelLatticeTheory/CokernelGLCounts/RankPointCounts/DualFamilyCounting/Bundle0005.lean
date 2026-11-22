import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitSk
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXFinVolSk

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSFinVolSk
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.FinVolSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def KfOrb : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (X0 : Fin a → Fin n → E)
    (Λ : Set (Fin n → E)),
    IsCMExt F E σ → IsHermND σ J →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0} ∧
    ∀ x : Fin a → Fin n → Af F ⊗[F] E, (∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0) ↔
      ∀ v : HeightOneSpectrum (𝓞 F),
        projV v x ∈ {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) X0}

def LocSB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (X0 : Fin a → Fin n → E)
    (Λ : Set (Fin n → E)),
    IsCMExt F E σ → IsHermND σ J → (gramE σ J X0).det ≠ 0 →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∃ (d : ℕ) (b : Module.Basis (Fin d) F E)
      (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
      (∀ v, IsSB ((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ))) ∧
      (∀ v, MeasurableSet (C v)) ∧
      (∀ v, C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))} =
        {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) X0}) ∧
      ∀ᶠ v in Filter.cofinite, C v = latV b v

def BoxVol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (a : ℕ)
    (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)),
    StdHyp σ J ψ → (gramE σ J X0).det ≠ 0 → 1 ≤ a → 2 * a < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → IsOmT F E σ n J ψ (gramE σ J X0) hT νX →
    ∀ (μinf : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)),
      SdW F E σ n J (Ainf F) (psiInf F ψ) a μinf → SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
      fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT) ≠ 0 →
      ∀ ωf : Measure (Fin a → Fin n → Af F ⊗[F] E),
        (∀ (A : (Fin a → Fin n → Ainf F ⊗[F] E) → ENNReal) (S : Set (Fin a → Fin n → Af F ⊗[F] E)),
          MeasurableSet S →
          ∫⁻ y, A (projInf y) * S.indicator 1 (projFin y) ∂νX =
            ωf S * ∫⁻ z, A z ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) →
        ωf {x | ¬ ∀ v : HeightOneSpectrum (𝓞 F),
          gramR (Fv F v) σ J (projV v x) = (gramE σ J X0).map (inclR (Fv F v))} = 0 ∧
        ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
          (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
          (∀ v, IsSB ((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ))) →
          (∀ v, MeasurableSet (C v)) → (∀ᶠ v in Filter.cofinite, C v = latV b v) →
          ωf {x | ∀ v, projV v x ∈ C v} =
            ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F),
              (omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v)))
                (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal)

theorem omFinVol_of (h1 : KfOrb) (h2 : LocSB) (h3 : BoxVol) : Formalism.L2.SG.Pf.NcS.SplitSk.OmFinVol := by
  intro F E _ _ _ _ _ σ n J ψ a X0 hT νX Λ μf hStd hdet ha hn hSWa hSWc hLat hOm _ _ _
  obtain ⟨hKYm, hKYiff⟩ := h1 F E σ n J a X0 Λ hStd.1 hStd.2.1 hLat
  refine ⟨hKYm, ?_⟩
  intro μinf νinf fibInf hμ hν hfib hne ωf hdec
  obtain ⟨hsupp, hbox⟩ := h3 F E σ n J ψ a X0 hT νX hStd hdet ha hn hSWa hSWc hOm μinf νinf fibInf hμ hν hfib
    hne ωf hdec
  obtain ⟨d, b, C, hSB, hCm, hCeq, hCa⟩ := h2 F E σ n J a X0 Λ hStd.1 hStd.2.1 hdet hLat
  have hae : ∀ᵐ x ∂ωf, ∀ v : HeightOneSpectrum (𝓞 F),
      gramR (Fv F v) σ J (projV v x) = (gramE σ J X0).map (inclR (Fv F v)) := ae_iff.2 hsupp
  have hset : ωf {x | ∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0} = ωf {x | ∀ v, projV v x ∈ C v} := by
    apply measure_congr
    filter_upwards [hae] with x hx
    apply propext
    show (∃ k ∈ Kf σ J Λ, x = k • ratTup (Af F) X0) ↔ ∀ v, projV v x ∈ C v
    constructor
    · intro h v
      have h' := (hKYiff x).1 h v
      rw [← hCeq v] at h'
      exact h'.1
    · intro h
      refine (hKYiff x).2 fun v => ?_
      rw [← hCeq v]
      exact ⟨h v, hx v⟩
  rw [hset, hbox d b C hSB hCm hCa]
  congr 1
  exact tprod_congr fun v => by rw [hCeq v]

end Formalism.L2.SG.Pf.NcS.FinVolSk
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXBoxVolSk
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.BoxVolSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def GramMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
    MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ T.map (inclR (Af F))} ∧
    (∀ y : Fin a → Fin n → AF F ⊗[F] E, gramR (AF F) σ J y = T.map (inclR (AF F)) →
      gramR (Af F) σ J (projFin y) = T.map (inclR (Af F))) ∧
    (∀ x : Fin a → Fin n → Af F ⊗[F] E, gramR (Af F) σ J x = T.map (inclR (Af F)) →
      ∀ v, gramR (Fv F v) σ J (projV v x) = T.map (inclR (Fv F v)))

def PosTest : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (t : HermR (Ainf F) σ a),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    fib t ≠ 0 →
    ∃ Φ : (Fin a → Fin n → Ainf F ⊗[F] E) → ℝ, Continuous Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ Φ x) ∧
      Integrable Φ (fib t) ∧ 0 < ∫ x, Φ x ∂(fib t)

def FinInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a d : ℕ) (b : Module.Basis (Fin d) F E) (x : Fin a → Fin n → Af F ⊗[F] E),
    ∀ᶠ v in Filter.cofinite, projV v x ∈ latV b v

def BoxMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a : ℕ) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
    (∀ v, MeasurableSet (C v)) → MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}

theorem BoxVolSk_tprod_ofReal {ι : Type} (r : ι → ℝ) (hm : Multipliable (fun i => (r i : ℂ))) :
    ∏' i, (r i : ℂ) = ((∏' i, r i : ℝ) : ℂ) := by
  obtain ⟨L, hL⟩ := hm
  have hclosed : IsClosed (Set.range ((↑) : ℝ → ℂ)) := Complex.isometry_ofReal.isClosedEmbedding.isClosed_range
  have hmem : L ∈ Set.range ((↑) : ℝ → ℂ) :=
    hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun s => ⟨∏ i ∈ s, r i, by rw [Complex.ofReal_prod]⟩)
  obtain ⟨l, rfl⟩ := hmem
  have hr : HasProd r l :=
    (Complex.isometry_ofReal.isEmbedding.isInducing.hasProd_iff (g := Complex.ofRealHom) (f := r) (a := l)).mp hL
  rw [hL.tprod_eq, hr.tprod_eq]

end Formalism.L2.SG.Pf.NcX.BoxVolSk
end
end


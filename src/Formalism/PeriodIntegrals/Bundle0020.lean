import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.FormalDegreeBessel.Bundle0001
import Mathlib
import Formalism.DoubleCosetMeasures.StatementV
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.HermitianLattices.StatementLat
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.PeriodIntegrals.Bundle0019

-- bundled from Formalism.PeriodIntegrals.AlgebraMapMemO
section
noncomputable section

open ValuativeRel MeasureTheory
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.SlopeTestRemainingChoices

open Polynomial Topology

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem mem_O_of_quad (L : LocE F E) (z : E) (t n : 𝒪[F])
    (h : z * z - algebraMap F E t * z + algebraMap F E n = 0) : z ∈ L.O := by
  rw [L.O_def]
  refine ⟨(X ^ 2 + (C (-t) * X + C n) : Polynomial 𝒪[F]), ?_, ?_⟩
  · monicity!
  · have ht : algebraMap 𝒪[F] E t = algebraMap F E t := rfl
    have hn : algebraMap 𝒪[F] E n = algebraMap F E n := rfl
    simp only [eval₂_add, eval₂_mul, eval₂_neg, eval₂_X_pow, eval₂_X, eval₂_C, map_neg, ht, hn]
    linear_combination h

theorem algebraMap_mem_O (L : LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O :=
  mem_O_of_quad L _ a 0 (by simp)

theorem mem_OF_of_mem_O [Nontrivial E] (L : LocE F E) (a : F) (h : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have hE : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  rw [L.O_def] at h
  have hF : IsIntegral 𝒪[F] a := by
    obtain ⟨p, hp, he⟩ := h
    refine ⟨p, hp, ?_⟩
    apply hE
    have hc : (algebraMap F E).comp (algebraMap 𝒪[F] F) = algebraMap 𝒪[F] E := by
      ext r
      rfl
    rw [Polynomial.hom_eval₂, map_zero, hc, he]
  exact (Valuation.integer.integers _).mem_of_integral hF

theorem cj_mem_O (L : LocE F E) (x : E) (h : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at h ⊢
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, ?_⟩
  have hc : L.cj.toRingEquiv.toRingHom.comp (algebraMap 𝒪[F] E) = algebraMap 𝒪[F] E := by
    ext r
    show L.cj (algebraMap F E (r : F)) = algebraMap F E (r : F)
    exact L.cj.commutes _
  have h2 := congrArg L.cj.toRingEquiv.toRingHom he
  rw [Polynomial.hom_eval₂, map_zero, hc] at h2
  exact h2

end Top

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem inv_mem_OF (a : F) (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  have h' := h
  rw [Valuation.mem_integer_iff] at h'
  rw [Valuation.mem_integer_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h'))

theorem exists_scale (a : F) : ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ (r : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, by simp, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
    refine ⟨⟨a⁻¹, inv_mem_OF a ha⟩, ?_, ?_⟩
    · show a⁻¹ ≠ 0
      exact inv_ne_zero ha0
    · show a⁻¹ * a ∈ 𝒪[F]
      rw [inv_mul_cancel₀ ha0]
      exact one_mem _

variable (L : LocE F E)

theorem tr_ex (x : E) : ∃ a : F, algebraMap F E a = x + L.cj x :=
  (L.cj_fix _).1 (by rw [map_add, L.cj_cj, add_comm])

theorem nm_ex (x : E) : ∃ a : F, algebraMap F E a = x * L.cj x :=
  (L.cj_fix _).1 (by rw [map_mul, L.cj_cj, mul_comm])

theorem nontrivial_E (L : LocE F E) : Nontrivial E := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h2 := L.rank
  rw [Module.finrank_zero_of_subsingleton] at h2
  omega

theorem exists_theta : ∃ θ ∈ L.O, L.cj θ = -θ ∧ ∃ D : 𝒪[F], (D : F) ≠ 0 ∧ θ * θ = algebraMap F E D := by
  have hx : ∃ x : E, L.cj x ≠ x := by
    by_contra hex
    have hall : ∀ w : E, L.cj w = w := fun w => not_not.mp (not_exists.mp hex w)
    have hle : Module.finrank F E ≤ 1 := by
      have := L.free
      have hw : ∀ w : E, ∃ c : F, c • (1 : E) = w := by
        intro w
        obtain ⟨a, ha⟩ := (L.cj_fix w).1 (hall w)
        exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
      exact finrank_le_one (1 : E) hw
    have h2 := L.rank
    omega
  obtain ⟨x, hx⟩ := hx
  have hc0 : L.cj (x - L.cj x) = -(x - L.cj x) := by
    rw [map_sub, L.cj_cj]
    ring
  have hθ0ne : x - L.cj x ≠ 0 := by
    intro h0
    apply hx
    exact (sub_eq_zero.mp h0).symm
  obtain ⟨D0, hD0⟩ := (L.cj_fix ((x - L.cj x) * (x - L.cj x))).1 (by rw [map_mul, hc0, neg_mul_neg])
  have hD0ne : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD0
    have := L.reduced
    exact hθ0ne (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact hD0.symm⟩)
  obtain ⟨r, hr0, hrD⟩ := exists_scale D0
  refine ⟨algebraMap F E r * (x - L.cj x), ?_, ?_, ⟨r * ⟨(r : F) * D0, hrD⟩, ?_, ?_⟩⟩
  · apply mem_O_of_quad L _ 0 (-(r * ⟨(r : F) * D0, hrD⟩))
    have e : ((-(r * ⟨(r : F) * D0, hrD⟩) : 𝒪[F]) : F) = -((r : F) * ((r : F) * D0)) := rfl
    have e0 : ((0 : 𝒪[F]) : F) = 0 := rfl
    rw [e, e0, map_zero, map_neg, map_mul, map_mul]
    linear_combination (-(algebraMap F E r) ^ 2) * hD0
  · rw [map_mul, L.cj.commutes, hc0, mul_neg]
  · show (r : F) * ((r : F) * D0) ≠ 0
    exact mul_ne_zero hr0 (mul_ne_zero hr0 hD0ne)
  · show _ = algebraMap F E ((r : F) * ((r : F) * D0))
    rw [map_mul, map_mul, hD0]
    ring

end Top2

section Top3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem decomp (L : LocE F E) (θ : E) (hθc : L.cj θ = -θ) (D : F) (hD : θ * θ = algebraMap F E D) (x : E) :
    ∃ t c : F, algebraMap F E t = x + L.cj x ∧ algebraMap F E c = (x - L.cj x) * θ ∧
      algebraMap F E (2 * D) * x = algebraMap F E (D * t) + algebraMap F E c * θ := by
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  obtain ⟨c, hc⟩ := (L.cj_fix ((x - L.cj x) * θ)).1 (by rw [map_mul, map_sub, L.cj_cj, hθc]; ring)
  refine ⟨t, c, ht, hc, ?_⟩
  rw [map_mul, map_mul, map_ofNat, ht, hc]
  linear_combination (-(x - L.cj x)) * hD

end Top3

end PI.LocHerm.SlopeTestRemainingChoices
end
end

-- bundled from Formalism.PeriodIntegrals.BordDefs
section
open Matrix

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

def omF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ • prW k (wbPart k r z) (Matrix.mulVec μ (wbPart k r z'))

def omF' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) • prW k (wbPart k r z') (Matrix.mulVec μ⁻¹ (wbPart k r z))

def bordDet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun (a b : Fin (r + 1)) =>
    herm (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) (if a = Fin.last r then w else fvec k r z a))

def omG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  prW k (wbPart k r z) (fun j => Hb k j j * bordDet k r z z' g (bvec (wI k r j)))

def omG' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  omG k r z' z (Hpk k r * g.conjTranspose * Hpk k r)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.DatumBlockEigen
section
noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI.DatumBlockEigen

def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)

end PI.DatumBlockEigen

namespace PI

open PI.DatumBlockEigen in

def DatumBlockEigen : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a →
    ∀ (ρ : J' →* ℂˣ), (∀ k : J', (k : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a → ρ k = 1) →
    ∀ h : GL (Fin (a + t)) F, blockCond O ϖ J' h →
      let Mi : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
        Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
          ((h⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F)
      ∃ k' : J', ((k' : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = Mi.toBlocks₁₁ ∧
        ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
          Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ (Mi * x) = ((ρ k' : ℂˣ) : ℂ) * Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.DatumConjInv
section
noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI

def DatumConjInv : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (a t : ℕ) (k : GL (Fin a) F),
    k ∈ Formalism.DoubleCosetMeasures.GLint O a → ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1
                (Matrix.fromBlocks ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
                  (1 : Matrix (Fin t) (Fin t) F) * x * (k : Matrix (Fin a) (Fin a) F)) =
        Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1 x

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.GaugeGap
section
noncomputable section

namespace PI.GaugeGap

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsQuadInv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  Module.finrank F E = 2 ∧ ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∃ G : GaugeFam F E σ, G.IsGauge

def CharAF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ

def HaarEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∃ μ : Measure (HA (AF F) σ J), IsHaarH F E σ M J μ

def Unimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ μ : Measure (HA (AF F) σ J), IsHaarH F E σ M J μ →
    ∀ g : HA (AF F) σ J, μ.map (fun h => h * g) = μ

def FrameIso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ →
    (∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
      J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) →
      ∃ e : HA (AF F) σ J ≃* HA (AF F) σ J',
        (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ Continuous e ∧ Continuous e.symm) ∧
    (∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
      (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
      IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
      J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
      ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
        (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) ∧
        Continuous e ∧ Continuous e.symm)

def XbetaEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsQuadInv σ →
    ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (β : F),
      3 ≤ M + 1 → IsHermND σ J → β ≠ 0 → (∃ x : Fin (M + 1) → E, hE σ J x x = algebraMap F E β) →
      ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
      ∃ νX : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E), IsXbetaMeasure F E σ (M + 1) J ψ β νX

end PI.GaugeGap
end
end

-- bundled from Formalism.PeriodIntegrals.HaarDefs
section
open MeasureTheory Matrix

noncomputable section

namespace PI

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (Formalism.QuantumDeterminants.lmulM s) = μ

def muS {k r : ℕ} (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) : Measure (Formalism.QuantumDeterminants.Mt k r) :=
  (μW.prod μN).map (fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def haarLie {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ENNReal) :
    Measure (Formalism.QuantumDeterminants.Mt k r) :=
  κ • Measure.map (fun x : lieE S => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) volume

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.LatIdxDet
section
open NumberField IsDedekindDomain

noncomputable section

namespace PI

def LatIdxDet : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V)
    (γ : V ≃ₗ[K] V), Submodule.IsLattice K A →
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (A.map ((γ : V →ₗ[K] V).restrictScalars (𝓞 K))) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A B = - WithZero.log (w.valuation K (LinearMap.det (γ : V →ₗ[K] V)))

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.LocDensCorank
section
open ValuativeRel Classical

noncomputable section

namespace PI.LocDensCorank

open Formalism.MainNotions.S

def LocDensCorank : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (a : ι → 𝒪[F]),
        (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ ((A.map M.L.cj).transpose * Matrix.diagonal (fun i => algebraMap F E (a i : F)) * A) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (if ∀ x : E, x ≠ 0 → IsUnit x then -1 else 1)
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card

end PI.LocDensCorank
end
end

-- bundled from Formalism.PeriodIntegrals.LocDualGen
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen

def DualAtL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (δ : A.Fp) : Prop :=
  ∀ x : A.Ep, (∀ y ∈ A.O, A.psiE (-(x * y * algebraMap A.Fp A.Ep δ⁻¹)) = 1) ↔ x ∈ A.O

def UnramL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) : Prop :=
  ∀ ϖ : 𝒪[A.Fp], Irreducible ϖ → ∀ x ∈ A.O,
    x * x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)} →
      x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)}

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    (IsReduced A.Ep → UnramL A → ∃ δ : A.Fp, δ ≠ 0 ∧ DualAtL A δ) ∧
    (∀ (δ : A.Fp) (u : 𝒪[A.Fp]), IsUnit u → DualAtL A δ → DualAtL A (δ * (u : A.Fp))) ∧
    (IsReduced A.Ep → UnramL A → Irreducible ((resChar p : ℕ) : 𝒪[A.Fp]) → DualAtL A 1)

end PI.LocDualGen
end
end

-- bundled from Formalism.PeriodIntegrals.LocHaarRR
section
noncomputable section

open scoped Classical

open IsDedekindDomain NumberField ValuativeRel MeasureTheory

namespace PI.LocHaarRR

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def ordR {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}
    (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) : Subring A.Ep :=
  let S : Subring (𝒪[A.Fp] × 𝒪[A.Fp]) :=
    RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.fst _ _))
      ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.snd _ _))
  (S.map ((𝒪[A.Fp]).subtype.prodMap (𝒪[A.Fp]).subtype)).comap sg.e.toRingEquiv.toRingHom

def RR (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) : Set A.Ep :=
  match A.split with
  | none => (A.O : Set A.Ep)
  | some sg => (ordR sg : Set A.Ep)

end

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p),
    IsReduced A.Ep → ∃ μ : Measure A.Ep, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (RR A) = 1

end PI.LocHaarRR
end
end

-- bundled from Formalism.PeriodIntegrals.LocHerm
section
noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def LocWitt : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M => IsField E →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (S₁ S₂ : Submodule E V)
    (σ : S₁ ≃ₗ[E] S₂), (∀ x y : S₁, H.h (σ x) (σ y) = H.h x y) →
    ∃ g : V ≃ₗ[E] V, (∀ x y, H.h (g x) (g y) = H.h x y) ∧ ∀ x : S₁, g x = σ x

def LocGlue : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (abelian₂ : Submodule M.L.O V),
    H.IsSelfDual abelian₂ → ∀ (U : Submodule E V) (hU : IsCompl U (H.perp U)),
    (∀ u : V, u ∈ U → ((∃ x ∈ abelian₂, (Submodule.linearProjOfIsCompl U (H.perp U) hU x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ U → H.h u y ∈ M.L.O)) ∧
    (∀ u : V, u ∈ H.perp U → ((∃ x ∈ abelian₂,
        (Submodule.linearProjOfIsCompl (H.perp U) U hU.symm x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ H.perp U → H.h u y ∈ M.L.O))

def LocOProj : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (W : Type) [AddCommGroup W] [Module E W] (P : Submodule M.L.O W), P.FG → Module.Projective M.L.O P

end PI.LocHerm
end
end

-- bundled from Formalism.PeriodIntegrals.WOnLatG
section
namespace PI

open WPhDefs

def WOnLatG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)), QIntLat s A La' →
    ∀ p : ℕ, p.Prime → ∀ x ∈ La', wPhG s A p x = alG s A x

end PI
end


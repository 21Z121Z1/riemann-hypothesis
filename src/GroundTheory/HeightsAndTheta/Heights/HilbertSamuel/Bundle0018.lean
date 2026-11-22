import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StandardLatticeVecIndep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0017

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal

noncomputable section

section OneBlock

variable {κ : Type} [Fintype κ]

def IsAnalyticSubset (D : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin D → ℂ) M]
    (A : Set M) : Prop :=
  IsClosed A ∧ ∀ q : M, ∃ U ∈ 𝓝 q, ∃ (r : ℕ) (g : Fin r → M → ℂ),
    (∀ j, MDifferentiableOn 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, ℂ) (g j) U) ∧
      A ∩ U = {q' | q' ∈ U ∧ ∀ j, g j q' = 0}

def IsConeAnalyticSubset (P : Ideal (MvPolynomial (Ix κ) ℤ)) (B : Set (Ix κ → ℂ)) : Prop :=
  B ⊆ pts P ∧ (∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → c • z ∈ B) ∧
    ∀ z ∈ pts P, ∃ U ∈ 𝓝 z, ∃ (r : ℕ) (g : Fin r → (Ix κ → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (g j) U) ∧ B ∩ U = {w | w ∈ U ∧ w ∈ pts P ∧ ∀ j, g j w = 0}

structure IsAnalyticRes (P : Ideal (MvPolynomial (Ix κ) ℤ)) (D : ℕ) {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin D → ℂ) M] [MeasurableSpace M] (f : M → Ix κ → ℂ) : Prop where
  mem : ∀ q, f q ∈ pts P
  meas : Measurable f
  holo : ∀ q, ∃ c : M → ℂ, (∀ᶠ q' in 𝓝 q, c q' ≠ 0) ∧
    MDifferentiableAt 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, Ix κ → ℂ) (fun q' ↦ c q' • f q') q
  onto : ∀ z ∈ pts P, ∃ q, ∃ c : ℂ, c ≠ 0 ∧ z = c • f q
  exc : ∃ (A : Set M) (B : Set (Ix κ → ℂ)), IsAnalyticSubset D A ∧ Dense Aᶜ ∧
    IsConeAnalyticSubset P B ∧ pts P ⊆ closure (pts P \ B) ∧ (∀ q, q ∉ A → f q ∉ B) ∧
    (∀ q q', q ∉ A → q' ∉ A → ∀ c : ℂ, f q' = c • f q → q' = q) ∧
    ∀ z ∈ pts P, z ∉ B → ∃ q, q ∉ A ∧ ∃ c : ℂ, c ≠ 0 ∧ z = c • f q

def IsSmoothVolume (D : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin D → ℂ) M]
    [MeasurableSpace M] (dV : Measure M) : Prop :=
  IsProbabilityMeasure dV ∧ ∀ e ∈ atlas (Fin D → ℂ) M, ∃ ν : (Fin D → ℂ) → ℝ,
    ContDiffOn ℝ ∞ ν e.target ∧ (∀ y ∈ e.target, 0 < ν y) ∧
    ∀ s : Set M, MeasurableSet s → s ⊆ e.source → dV s = ∫⁻ y in e '' s, ENNReal.ofReal (ν y)

def symMeasure {M : Type} [MeasurableSpace M] (f : M → Ix κ → ℂ) (dV : Measure M) :
    Measure (Ix κ → ℂ) :=
  (2 : ℝ≥0∞)⁻¹ • (dV.map f + dV.map (conjPt ∘ f))

def secRank {Ω : Type} [Field Ω] (x : Ix κ → Ω) (n : ℕ) : ℕ :=
  Module.finrank ℤ (sec ℤ x n)

def secNorm {J : Type} [Fintype J] {Ω : Type} [Field Ω] (x : J → Ω) (m : ConeMetric ℂ J)
    (μ : Measure (J → ℂ)) (n : ℕ) (s : Ω) : ℝ := by
  classical
  exact if h : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ aeval x f = s then
    l2Norm m (Int.castRingHom ℂ) μ n h.choose else 0

structure IsHSDatum (D : ℕ) {Ω : Type} [Field Ω] [CharZero Ω] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (P₀ : Ideal (MvPolynomial (Ix κ) ℤ)) : Prop where
  one_le : 1 ≤ D
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℤ x
  le : P₀ ≤ coordIdeal ℤ x
  semipos : IsSemipositiveRel (ι := GlobalTheory κ) P₀ (coordIdeal ℤ x) (HermLine.ofCone m)
  conj : IsConjInvariantH (HermLine.ofCone m)

end OneBlock

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def hpow (A : HermLine ι) (j : ℕ) : HermLine ι where
  a := (j : ℤ) • A.a
  h z := A.h z ^ j
  pos z hz := pow_pos (A.pos z hz) j
  smul c z hc := by
    rw [A.smul c z hc, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul, zpow_natCast]

def SupLE (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (a : K → ℤ) (hm : ((Σ k, ι k) → ℂ) → ℝ)
    (c : ℝ) (s : Ω) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ), IsMultiHomog g dg → IsMultiHomog h dh →
    (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * hm z

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y h ≠ 0 ∧ aeval y g = s * aeval y h

def NonzeroAtPt (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ g h, IsRep y a s g h ∧ eval z (map (Int.castRingHom ℂ) g) ≠ 0 ∧
    eval z (map (Int.castRingHom ℂ) h) ≠ 0

def NonzeroAtPrime (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (Q : Ideal (MRing ι)) : Prop :=
  ∃ g h, IsRep y a s g h ∧ g ∉ Q ∧ h ∉ Q

def IsGeneratedOnModel (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∀ Q : Ideal (MRing ι), Inter.IsClosedPt Q → mCoordIdeal y ≤ Q →
    ∃ s ∈ chartLat y a 1, NonzeroAtPrime y a s Q

def IsGeneratedGeneric (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal y), ∃ s ∈ chartLat y a 1, NonzeroAtPt y a s z

def IsSemiampleOnFibres (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ∃ j : ℕ, 1 ≤ j ∧ ∀ Q : Ideal (MRing ι), Inter.IsClosedPt Q → W ≤ Q →
      ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
        (∀ k, (dg k : ℤ) = dh k + j * a k) ∧ h ∉ W ∧ g ∉ Q ∧ h ∉ Q ∧
        ∀ Q' : Ideal (MRing ι), Inter.IsClosedPt Q' → W ≤ Q' →
          ∃ (g' h' : MRing ι) (dg' dh' : K → ℕ), IsMultiHomog g' dg' ∧ IsMultiHomog h' dh' ∧
            (∀ k, (dg' k : ℤ) = dh' k + j * a k) ∧ h' ∉ Q' ∧ g * h' - g' * h ∈ W

def IsBig (y : (Σ k, ι k) → Ω) (a : K → ℤ) (D : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ j : ℕ, 1 ≤ j ∧ ∀ᶠ n : ℕ in atTop, ∃ (r : ℕ) (s : Fin r → Ω),
    c * (n : ℝ) ^ D ≤ (r : ℝ) ∧ LinearIndependent ℤ s ∧ ∀ i, s i ∈ chartLat y a (j * n)

def IsAmpleGeneric (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d

def IsAmpleOnFibres (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 < geoNum d W (fun _ ↦ a)

def IsVeryAmpleGeneric (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  IsGeneratedGeneric y a ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s ∈ chartLat y a n, ∃ N : ℕ, 0 < N ∧
    (N : Ω) * s ∈ (Submodule.span ℤ (chartLat y a 1 : Set Ω)) ^ n

structure IsGoodDatum (y : (Σ k, ι k) → Ω) (D : ℕ) (P₀ : Ideal (MRing ι)) (A : HermLine ι) : Prop where
  gen : IsGeneratedGeneric y A.a
  big : IsBig y A.a D
  le : P₀ ≤ mCoordIdeal y
  semipos : IsSemipositiveRel P₀ (mCoordIdeal y) A
  semiample : IsSemiampleOnFibres (mCoordIdeal y) A.a

structure IsSmallGenerated (y : (Σ k, ι k) → Ω) (D : ℕ) (P₀ : Ideal (MRing ι)) (A : HermLine ι) :
    Prop where
  nonneg : ∀ k, 0 ≤ A.a k
  gens : ∃ (q : ℕ) (w : Fin q → MRing ι), (∀ j, IsMultiHomog (w j) fun k ↦ (A.a k).toNat) ∧
    (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → mCoordIdeal y ≤ Q → ∃ j, w j ∉ Q) ∧
    ∀ j, ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z
  le : P₀ ≤ mCoordIdeal y
  semipos : IsSemipositiveRel P₀ (mCoordIdeal y) A
  big : IsBig y A.a D

def hHat0 (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) : ℝ :=
  smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n

def volHat (y : (Σ k, ι k) → Ω) (A : HermLine ι) (D : ℕ) : ℝ :=
  arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

def PtDominated (y : (Σ k, ι k) → Ω) (a b : K → ℤ) (ha hb : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ)
    (s t : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ g h g' h' : MRing ι, IsRep y a s g h → IsRep y b t g' h' →
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 → eval z (map (Int.castRingHom ℂ) h') ≠ 0 →
    ‖eval z (map (Int.castRingHom ℂ) g')‖ / (‖eval z (map (Int.castRingHom ℂ) h')‖ * hb z) ≤
      c * (‖eval z (map (Int.castRingHom ℂ) g)‖ / (‖eval z (map (Int.castRingHom ℂ) h)‖ * ha z))

end Block

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.NormFibreVecPosOfLinearIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField TensorProduct

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem norm_fibreVec_pos_of_linearIndependent {E : HermitianBundle.{0} K} {ι : Type*}
    {s : ι → E.carrier} (hs : LinearIndependent (𝓞 K) s) (σ : K →+* ℂ) (i : ι) :
    0 < ‖fibreVec E.metric σ (s i)‖ :=
  norm_pos_iff.mpr ((linearIndependent_fibreVec E.metric σ hs).ne_zero i)

theorem exists_linearIndependent_one (E : HermitianBundle.{0} K) (h : 0 < bundleRank E) :
    ∃ s : Fin 1 → E.carrier, LinearIndependent (𝓞 K) s := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank (R := 𝓞 K) (M := E.carrier)
    (v := Fin.elim0) (linearIndependent_empty_type) h
  exact ⟨_, hx⟩

theorem BoundedInjection.pos {E' E : HermitianBundle.{0} K} {A : (K →+* ℂ) → ℝ}
    (α : BoundedInjection E' E A) (h : 0 < bundleRank E') (σ : K →+* ℂ) : 0 < A σ := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_one E' h
  have hs' : LinearIndependent (𝓞 K) (α.toLinearMap ∘ s) :=
    hs.map' α.toLinearMap (LinearMap.ker_eq_bot.mpr α.injective)
  have h1 := norm_fibreVec_pos_of_linearIndependent hs' σ 0
  simp only [Function.comp_apply] at h1
  have h2 := α.norm_le σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] s 0)
  rw [LinearMap.lTensor_tmul, fibreNorm_one_tmul, fibreNorm_one_tmul] at h2
  have h3 := norm_nonneg (fibreVec E'.metric σ (s 0))
  by_contra hA
  have hA' := not_lt.mp hA
  nlinarith

theorem ShortFamily.pos {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) (h : 0 < bundleRank E) (σ : K →+* ℂ) : 0 < lam σ := by
  have h1 := norm_fibreVec_pos_of_linearIndependent F.linearIndependent σ ⟨0, h⟩
  have h2 := F.norm_le σ ⟨0, h⟩
  rw [fibreNorm_one_tmul] at h2
  linarith

omit [NumberField K] in

def posOrOne (f : (K →+* ℂ) → ℝ) (σ : K →+* ℂ) : ℝ := if 0 < f σ then f σ else 1

omit [NumberField K] in
theorem le_posOrOne {f : (K →+* ℂ) → ℝ} {σ : K →+* ℂ} {y : ℝ} (h : y ≤ f σ) :
    y ≤ posOrOne f σ := by
  unfold posOrOne
  split_ifs with hf
  · exact h
  · have hf' := not_lt.mp hf; linarith

def ShortFamily.posOrOne {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) : ShortFamily E (posOrOne lam) where
  vec := F.vec
  linearIndependent := F.linearIndependent
  norm_le σ i := le_posOrOne (F.norm_le σ i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalCoordinatesA
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BirationalCoordinates

section Scale

variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx

omit [Fintype κ] in

theorem mCoordIdeal_eq : mCoordIdeal (ι := GlobalTheory κ) y = mCoordIdeal (ι := GlobalTheory κ) x := by
  let φ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω := aeval fun k => C μ * X k
  let ψ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω := aeval fun k => C μ⁻¹ * X k
  have hψφ : ∀ q, ψ (φ q) = q := by
    have h : ψ.comp φ = AlgHom.id Ω _ := by
      refine MvPolynomial.algHom_ext fun k => ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, ψ, aeval_X, map_mul, algHom_C, algebraMap_eq]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hμ, C_1, one_mul]
    intro q
    exact AlgHom.congr_fun h q
  have hcomp : (mConeMap (ι := GlobalTheory κ) x).toRingHom =
      (φ.toRingHom.comp (MvPolynomial.map j)).comp (mConeMap (ι := GlobalTheory κ) y).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      mConeMap, aeval_X, map_mul, map_C, map_X, φ, algHom_C, algebraMap_eq, hx p, ]
    ring
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  have hf : mConeMap (ι := GlobalTheory κ) x f = φ (MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f)) :=
    congrArg (fun F : MRing (GlobalTheory κ) →+* MvPolynomial Unit Ω => F f) hcomp
  rw [hf]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    have h1 : MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f) = 0 := by
      rw [← hψφ (MvPolynomial.map j _), h, map_zero]
    exact MvPolynomial.map_injective j j.injective (by rw [h1, map_zero])

omit hμ in

theorem aeval_homog {g : MRing (GlobalTheory κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    aeval x g = μ ^ d () * j (aeval y g) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = d () := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have hjx : j (aeval y g) = aeval (fun p => j (y p)) g := by
    rw [← RingHom.toIntAlgHom_apply, comp_aeval_apply]
    rfl
  rw [hjx, show x = fun p => μ * j (y p) from funext hx]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm]
  ring

omit [Fintype κ] in

theorem chartRingZ_eq (c' : Unit → κ) :
    chartRingZ (ι := GlobalTheory κ) x c' = (chartRingZ (ι := GlobalTheory κ) y c').map j.toIntAlgHom := by
  rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
  congr 2
  funext p
  simp only [Function.comp_apply, RingHom.toIntAlgHom_apply, map_div₀, hx, mul_div_mul_left _ _ hμ]

omit [Fintype κ] in

theorem mem_chartLat_iff (a : Unit → ℤ) (τ : ℕ) (s' : Ω'') :
    μ ^ ((τ : ℤ) * a ()) * j s' ∈ chartLat (ι := GlobalTheory κ) x a τ ↔ s' ∈ chartLat (ι := GlobalTheory κ) y a τ := by
  have hne : ∀ c' : Unit → κ, (∀ k, x ⟨k, c' k⟩ ≠ 0) ↔ (∀ k, y ⟨k, c' k⟩ ≠ 0) := fun c' =>
    forall_congr' fun k => by rw [hx, mul_ne_zero_iff, map_ne_zero]; exact and_iff_right hμ
  have hval : ∀ c' : Unit → κ, μ ^ ((τ : ℤ) * a ()) * j s' * ∏ k, x ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) =
      j (s' * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) := by
    intro c'
    simp only [Fintype.prod_unique, hx, map_mul, map_zpow₀, mul_zpow]
    have h1 : μ ^ ((τ : ℤ) * a ()) * μ ^ (-((τ : ℤ) * a default)) = 1 := by
      rw [← zpow_add₀ hμ]
      simp
    linear_combination (j s' * j (y ⟨default, c' default⟩) ^ (-((τ : ℤ) * a default))) * h1
  change (∀ c' : Unit → κ, _ → _) ↔ (∀ c' : Unit → κ, _ → _)
  refine forall_congr' fun c' => ?_
  rw [hne c', hval c', chartRingZ_eq j hμ hx c', Subalgebra.mem_map]
  refine imp_congr_right fun _ => ⟨fun ⟨t, ht, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  rw [RingHom.toIntAlgHom_apply] at he
  rwa [j.injective he] at ht

omit [Fintype κ] in

theorem exists_of_mem_chartLat {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (a : Unit → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ chartLat (ι := GlobalTheory κ) x a τ) : ∃ s' : Ω'', μ ^ ((τ : ℤ) * a ()) * j s' = s := by
  have h := hs (fun _ => c) (fun _ => hc)
  simp only [Fintype.prod_unique] at h
  rw [chartRingZ_eq j hμ hx, Subalgebra.mem_map] at h
  obtain ⟨t, -, ht⟩ := h
  rw [RingHom.toIntAlgHom_apply] at ht
  have hyc : y ⟨(), c⟩ ≠ 0 := fun h0 => hc (by rw [hx, h0, map_zero, mul_zero])
  refine ⟨t * y ⟨(), c⟩ ^ ((τ : ℤ) * a ()), ?_⟩
  rw [map_mul, ht, map_zpow₀]
  change μ ^ ((τ : ℤ) * a ()) * (s * x ⟨(), c⟩ ^ (-((τ : ℤ) * a ())) * j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ())) = s
  rw [hx, mul_zpow, zpow_neg]
  have h1 : μ ^ ((τ : ℤ) * a ()) ≠ 0 := zpow_ne_zero _ hμ
  have h2 : j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ()) ≠ 0 := zpow_ne_zero _ (map_ne_zero j |>.2 hyc)
  field_simp
  rw [zpow_neg, inv_mul_cancel_right₀ h2]

theorem rep_iff (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') {dg dh : Unit → ℕ} {g h : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) :
    aeval x g = μ ^ ((τ : ℤ) * A.a ()) * j s' * aeval x h ↔ aeval y g = s' * aeval y h := by
  rw [aeval_homog j hx hg, aeval_homog j hx hh, ← zpow_natCast, ← zpow_natCast, hd (), add_comm,
    zpow_add₀ hμ, mul_assoc, mul_assoc]
  have hm : μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hμ) (zpow_ne_zero _ hμ)
  rw [show μ ^ ((τ : ℤ) * A.a ()) * (j s' * (μ ^ ((dh () : ℕ) : ℤ) * j (aeval y h))) =
      μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) * j (s' * aeval y h) by rw [map_mul]; ring,
    ← mul_assoc, mul_right_inj' hm]
  exact j.injective.eq_iff

theorem isSmallH_iff (P : Ideal (MRing (GlobalTheory κ))) (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') :
    IsSmallH P x A τ (μ ^ ((τ : ℤ) * A.a ()) * j s') ↔ IsSmallH P y A τ s' := by
  constructor
  · intro H dg dh g h z hg hh hd he hz
    exact H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).2 he) hz
  · intro H dg dh g h z hg hh hd he hz
    exact H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).1 he) hz

theorem smallSectionCount_eq_of_birational {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (A : HermLine (GlobalTheory κ)) (τ : ℕ) :
    smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) y) y A) (chartLat (ι := GlobalTheory κ) y A.a) τ =
      smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x A) (chartLat (ι := GlobalTheory κ) x A.a) τ := by
  rw [mCoordIdeal_eq j hμ hx]
  set P := mCoordIdeal (ι := GlobalTheory κ) x
  unfold smallSectionCount
  congr 2
  let F : {s : chartLat (ι := GlobalTheory κ) y A.a τ // IsSmallH P y A τ (s : Ω'')} →
      {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} := fun s =>
    ⟨⟨μ ^ ((τ : ℤ) * A.a ()) * j s.1.1, (mem_chartLat_iff j hμ hx A.a τ _).2 s.1.2⟩,
      (isSmallH_iff j hμ hx P A τ _).2 s.2⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨fun s t hst => ?_, fun s => ?_⟩)
  · have h1 : μ ^ ((τ : ℤ) * A.a ()) * j s.1.1 = μ ^ ((τ : ℤ) * A.a ()) * j t.1.1 :=
      congrArg (fun u : {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} => (u.1 : Ω)) hst
    exact Subtype.ext (Subtype.ext (j.injective (mul_left_cancel₀ (zpow_ne_zero _ hμ) h1)))
  · obtain ⟨s', hs'⟩ := exists_of_mem_chartLat j hμ hx hc A.a τ s.1.2
    have hm : s' ∈ chartLat (ι := GlobalTheory κ) y A.a τ := (mem_chartLat_iff j hμ hx A.a τ s').1 (hs' ▸ s.1.2)
    have hsm : IsSmallH P y A τ s' := (isSmallH_iff j hμ hx P A τ s').1 (hs' ▸ s.2)
    exact ⟨⟨⟨s', hm⟩, hsm⟩, Subtype.ext (Subtype.ext hs')⟩

end Scale

end BirationalCoordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClopenDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ClopenDegree.proof (h₁ : ClopenComponents.Statement) (h₂ : ComponentDegree.Statement)
    (h₃ : ComponentsAdditive.Statement) (h₄ : IntNumComponents.Statement) : ClopenDegree.Statement := by
  intro K _ _ ι _ P e L A hP hL hA hcl
  obtain ⟨S, hS, hAS, hI⟩ := h₁ K ι P e A hP hA hcl
  rw [hI, hAS, h₃ K ι P e L S hP hL hS, h₄ K ι P e _ S hP hS]
  push_cast
  exact Finset.sum_congr rfl fun W hW => h₂ K ι P e L W hP hL (hS W hW)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLogDetDerivative
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem LogDetDerivative.proof : LogDetDerivative.Statement :=
  LogDetDerivative.intersectionNumber_baseChange

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentsMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComponentsMeetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y ∧
      ∃ W ∈ S, ∃ W' ∈ S, W ≠ W' ∧ z ∈ zeroLocus ℂ W ∧ z ∈ zeroLocus ℂ W'} = 0

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end


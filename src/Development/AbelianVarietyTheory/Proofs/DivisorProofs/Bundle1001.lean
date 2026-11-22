import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Formalism.FockGram.Bundle0001
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusCharacterUnitActionProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChange
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.HilbBaseChange

open Module TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] (n : ℕ) (p : MvPolynomial σ K) :
    homogeneousComponent n (MvPolynomial.map (algebraMap K L) p) =
      MvPolynomial.map (algebraMap K L) (homogeneousComponent n p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem homogeneousComponent_mem_span_map_homogeneous {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    {g : MvPolynomial σ L}
    (hg : g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))))
    (n : ℕ) :
    homogeneousComponent n g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
      ((P.restrictScalars K ⊓ homogeneousSubmodule σ K n : Submodule K (MvPolynomial σ K)) :
        Set (MvPolynomial σ K))) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, rfl⟩ := hy
    rw [homogeneousComponent_map_algebraMap]
    exact Submodule.subset_span ⟨_, ⟨hP q hq n, homogeneousComponent_mem n q⟩, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem mem_span_image_of_mem_ideal_map {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial σ K)) {g : MvPolynomial σ L}
    (hg : g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)) :
    g ∈ Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) := by
  obtain ⟨M, hM⟩ : ∃ M : Submodule L (MvPolynomial σ L),
      M = Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (P : Set (MvPolynomial σ K))) :=
    ⟨_, rfl⟩
  rw [← hM]
  have hX : ∀ (i : σ) (x : MvPolynomial σ L), x ∈ M → X i * x ∈ M := by
    intro i x hx
    rw [hM] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      refine Submodule.subset_span ⟨X i * q, P.mul_mem_left _ hq, ?_⟩
      simp
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hmul : ∀ (a x : MvPolynomial σ L), x ∈ M → a * x ∈ M := by
    intro a x hx
    induction a using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.C_mul']; exact M.smul_mem c hx
    | add p q hp hq => rw [add_mul]; exact M.add_mem hp hq
    | mul_X p i hp =>
      rw [show p * X i * x = X i * (p * x) by ring]
      exact hX i _ hp
  induction hg using Submodule.span_induction with
  | mem y hy => rw [hM]; exact Submodule.subset_span hy
  | zero => exact M.zero_mem
  | add y z _ _ hy hz => exact M.add_mem hy hz
  | smul a y _ hy => exact hmul a y hy

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem decompose_coe_eq_homogeneousComponent {σ L : Type} [Field L]
    (g : MvPolynomial σ L) (n : ℕ) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
    (((DirectSum.decompose (homogeneousSubmodule σ L)) g) n : MvPolynomial σ L) =
      homogeneousComponent n g := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := L)
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single n]
    · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem n g)
    · intro i _ hi
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) hi
    · intro h; exact absurd hn h
  · rw [homogeneousComponent_eq_zero]
    · refine Finset.sum_eq_zero fun i hi => ?_
      exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem i g) (by rintro rfl; exact hn hi)
    · simp at hn; omega

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem linearIndependent_map_algebraMap {σ K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} {v : ι → MvPolynomial σ K}
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => MvPolynomial.map (algebraMap K L) (v i)) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := L) hv
  have h2 := h.map' (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap
    (algebraTensorAlgEquiv K L).toLinearEquiv.ker
  have he : (fun i => MvPolynomial.map (algebraMap K L) (v i)) =
      (algebraTensorAlgEquiv K L).toLinearEquiv.toLinearMap ∘ fun i => (1 : L) ⊗ₜ[K] v i := by
    funext i
    simp [algebraTensorAlgEquiv_tmul]
  rw [he]
  exact h2

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem finrank_span_map_algebraMap_eq {σ K L : Type} [Field K] [Field L] [Algebra K L]
    (W : Submodule K (MvPolynomial σ K)) [FiniteDimensional K W] :
    Module.finrank L (Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K)))) =
      Module.finrank K W := by
  let b := Module.finBasis K W
  let v : Fin (Module.finrank K W) → MvPolynomial σ L :=
    fun i => MvPolynomial.map (algebraMap K L) (b i : MvPolynomial σ K)
  have hli : LinearIndependent L v :=
    linearIndependent_map_algebraMap (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
  have hspan : Submodule.span L (Set.range v) =
      Submodule.span L ((MvPolynomial.map (algebraMap K L)) '' (W : Set (MvPolynomial σ K))) := by
    apply le_antisymm
    · refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (b i).2, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw' : (⟨w, hw⟩ : W) ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
      have key : ∀ x : W, x ∈ Submodule.span K (Set.range b) →
          MvPolynomial.map (algebraMap K L) (x : MvPolynomial σ K) ∈
            (Submodule.span L (Set.range v)).restrictScalars K := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          have : MvPolynomial.map (algebraMap K L) ((c • y : W) : MvPolynomial σ K) =
              c • MvPolynomial.map (algebraMap K L) (y : MvPolynomial σ K) := by
            simp [MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
          rw [this]
          exact Submodule.smul_mem _ c hy
      exact key _ hw'
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]

open MvPolynomial Filter in
open scoped ENNReal in
open Module TensorProduct in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem _root_.GlobalTheory.HilbBaseChange.idealHilbertPoly_map : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ _root_.GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = _root_.GlobalTheory.idealHilbertPoly P := by
  intro K L _ _ _ N P hP
  have hW : ∀ n : ℕ,
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).restrictScalars L ⊓
          homogeneousSubmodule (Fin N) L n =
        Submodule.span L ((MvPolynomial.map (algebraMap K L)) ''
          ((P.restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K (MvPolynomial (Fin N) K)) :
            Set (MvPolynomial (Fin N) K))) := by
    intro n
    apply le_antisymm
    · rintro g ⟨hg1, hg2⟩
      have := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg1) n
      rwa [homogeneousComponent_of_mem hg2, if_pos rfl] at this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      exact ⟨Ideal.mem_map_of_mem _ hw1,
        (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hw2).map _)⟩
  have hA : ∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L),
      ∀ n : ℕ, homogeneousComponent n g ∈
        P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) := by
    intro g hg n
    have h := homogeneousComponent_mem_span_map_homogeneous P hP (mem_span_image_of_mem_ideal_map P hg) n
    rw [← hW n] at h
    exact h.1
  refine ⟨hA, ?_⟩
  have hhomP : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hP r hr i
  have hhomQ : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) L)
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
    intro i r hr
    rw [decompose_coe_eq_homogeneousComponent]
    exact hA r hr i
  have hdim : ∀ n : ℕ,
      Module.finrank L (_root_.GlobalTheory.quotPiece
        (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) (n : ℤ)) =
      Module.finrank K (_root_.GlobalTheory.quotPiece P (n : ℤ)) := by
    intro n
    have h1 := _root_.GlobalTheory.finrank_quotPiece_add
      (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) n
    have h2 := _root_.GlobalTheory.finrank_quotPiece_add P n
    rw [hW n, finrank_span_map_algebraMap_eq, _root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h1
    rw [_root_.GlobalTheory.ProjCut.finrank_homogeneousSubmodule] at h2
    omega
  obtain ⟨n₀, hn₀⟩ := ((_root_.GlobalTheory.eventually_finrank_quotPiece hhomQ).and
    (_root_.GlobalTheory.eventually_finrank_quotPiece hhomP)).exists_forall_of_atTop
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
  · intro a b h
    simpa using h
  · intro m
    obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (by omega)
    simp only [Set.mem_setOf_eq]
    rw [← h1, ← h2, hdim]

end GlobalTheory.HilbBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev l2 {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (φ₁ φ₂ : X → ℂ) : ℂ := Lift.pet μ 𝓕 φ₁ φ₂

abbrev Upq (W : HSp D) (ρ : D.what₂.Tau) : Type := UpqT (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2

abbrev Frames (W : HSp D) : Type :=
  ∀ ρ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D ρ)).1 ⊕ Fin (W.sig (tauE D ρ)).2) (Fin W.rank) ℂ

def IsFrames (W : HSp D) (A : Frames W) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * A ρ = gramAt D W ρ

def conjFrame {p q n : ℕ} (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q * b * A : Matrix (Fin n) (Fin n) ℂ)

def realMat (W : HSp D) (A : Frames W) (ρ : D.what₂.Tau) (b : Upq W ρ) : Matrix (Fin W.rank) (Fin W.rank) ℂ :=
  conjFrame (gramAt D W ρ) (A ρ) (UpqT.mat b)

def realElt (θ : Datum.InfFam D) (W : HSp D) (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : GA D W :=
  ((Finset.univ : Finset D.what₂.Tau).toList.map fun ρ => atTau θ W ρ (g ρ)).prod

abbrev FinCos (W : HSp D) (K : Subgroup (GA D W)) : Type := GfC W ⧸ K.subgroupOf (GfC W)

def FinCos.rep {W : HSp D} {K : Subgroup (GA D W)} (c : FinCos W K) : GA D W := (c.out : GfC W)

open Classical in

def quadSign (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ :=
  if (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 then 1 else -1

def quadTerm (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : ℕ) : ℝ :=
  quadSign D v ^ i / (Ideal.absNorm v.asIdeal : ℝ) ^ i

def dLoc (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ := ∏ i ∈ Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D v i)⁻¹

def dOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ℝ :=
  ∏' p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D p.1.1 p.2.1)⁻¹

def eulerOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ) : ℂ :=
  ∏' p : {w : HeightOneSpectrum (𝓞 D.host.E) // OffS D S w} × Fin D.R.r, (1 - x p.1.1 p.2)⁻¹

variable (D) in

def degAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ :=
  ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

abbrev levV (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    Subgroup (GL (Fin (Vc D i).rank) (Lev.EAf D)) := lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)

abbrev petW (i : Fin D.R.m) (F₁ F₂ : GA D (Wc D i) → ℂ) : ℂ := l2 (R.νW i) (R.fdW i) F₁ F₂

def upLift (i : Fin D.R.m) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (F : GA D (Wc D i) → ℂ) (h : GA D (Vc D i)) : ℂ :=
  petW R i (fun g => Datum.thetaKO ω h g φ) F

def IsLiftData (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  R.Char F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io

def ForLiftData (F : Face D A)
    (Φ : ∀ (i : Fin D.R.m) (_t : T) (σ : D.what₂.LL →+* ℂ) (_P : LevelP R.Pg D.R.r ℂ) (_m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
      (_ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
      (_BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (_f : Datum.WO (Vc D i) (Wc D i) → ℂ)
      (c : CoefA (Vc D i)) (_io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), Prop) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftData R F i t σ s P cμ cη m ω BW f₀ f c io → Φ i t σ P m ω BW f c io

def LiftIsCuspForm (F : Face D A) : Prop :=
  ForLiftData R F fun i t σ P m ω BW f c io =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ φ ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)),
      ∃ U ∈ R.Wall i σ, ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)), U (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) (ptAt R i σ BW f) io (c.ext φ) (PiTensorProduct.tprod ℂ v) g

def SourceLevelLaw (F : Face D A) : Prop :=
  ForLiftData R F fun i t σ P m ω BW f _ _ =>
    ∀ κ ∈ Lev.levA (Vc D i) (levV R i t P m), ∀ Q : PolF D (Wc D i).rank (Vc D i).rank,
      ω (κ, 1) (ptAt R i σ BW f Q) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • ptAt R i σ BW f Q

open Datum in

def InnerProductFormula (F : Face D A) : Prop :=
  ForLiftData R F fun i t σ P m ω BW f _ _ =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : ∀ ρ, Measure (Upq (Wc D i) ρ), (∀ ρ, Lev.IsMinf (mR ρ)) →
    ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ (v₁ v₂ : ∀ ρ, lowT (R.MW i σ) ρ) (Q₁ Q₂ : PolF D (Wc D i).rank (Vc D i).rank),
      let φ₁ := ptAt R i σ BW f Q₁
      let φ₂ := ptAt R i σ BW f Q₂
      let F₁ := U₁ fun ρ => v₁ ρ
      let F₂ := U₂ fun ρ => v₂ ρ
      let Z : GA D (Wc D i) → ℂ := fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
      let pt : FinCos (Wc D i) (levW R i) → (∀ ρ, Upq (Wc D i) ρ) → GA D (Wc D i) := fun x b =>
        x.rep * realElt R.θ (Wc D i) fun ρ => realMat (Wc D i) Fr ρ (b ρ)
      (∀ h, IntegrableOn (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) (R.fdW i) (R.νW i)) ∧
      IntegrableOn (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) 𝓕 ν ∧
      ∫⁻ b, ∑' x, ‖Z (pt x b)‖ₑ ∂(Measure.pi mR) < ⊤ ∧
      l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) = ((ν 𝓕).toReal : ℂ) * ∫ b, ∑' x, Z (pt x b) ∂(Measure.pi mR)

open Datum in

def FockCoefficient (F : Face D A) : Prop :=
  ForLiftData R F fun i _ σ _ _ ω BW f c io =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ x ∈ GfC (Wc D i), ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W),
      l2 μ 𝓧 (ω (1, x * realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
          (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) =
        Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) *
          (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) *
          ⟪w', w⟫_ℂ * l2 μ 𝓧 (ω (1, x) f) f

variable (D) in

def DeltaNorm : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) =
    ∏ ρ : D.what₂.Tau, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℂ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℂ))

open Datum in

def FiniteZeta (F : Face D A) : Prop :=
  ForLiftData R F fun i t σ P _ ω _ f _ _ =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ,
        (∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (eulerOff D (finS R t) x / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

open Datum in

def LevelIndexNorm (F : Face D A) : Prop :=
  ForLiftData R F fun i t _ P m _ _ f _ _ =>
    levV R i t P m ≤ GlobalTheory.Mass.Levels.latLev (Vc D i) ∧
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
      (((levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) * nrm2 μ 𝓧 f = ∏ v ∈ finS R t, (dLoc D v)⁻¹

variable (D) in

def MassLower : Prop :=
  ∀ i : Fin D.R.m, (Vc D i).IsPosDef → 1 / ((NumberField.Units.torsionOrder D.host.E : ℝ) ^ D.R.nV * (D.R.nV.factorial : ℝ)) ≤
    GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i))

def FormalDegreeUpper (F : Face D A) : Prop :=
  ForLiftData R F fun i _ σ _ _ _ _ _ _ _ =>
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ (ρ : D.what₂.Tau) (mR : Measure (Upq (Wc D i) ρ)), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ 0 < ∫ b, k b ∂mR ∧
        Real.log (∫ b, k b ∂mR)⁻¹ ≤
          2 + (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (D.R.r : ℝ) ^ 2 * D.R.nV * ((degAt D i σ ρ : ℝ) + 2))

end GlobalTheory.AdelicScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerWordNeZeroReversedWordNeZero
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.SignInnerAdjoint

theorem sgn_sq_one {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    (Formalism.REAL.sgn ε a b : ℂ) * (Formalism.REAL.sgn ε a b : ℂ) = 1 := by
  unfold Formalism.REAL.sgn; split_ifs <;> norm_num

theorem sgn_symm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.sgn ε b a = Formalism.REAL.sgn ε a b := by
  unfold Formalism.REAL.sgn; split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem inner_E_right {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (a b : Fin n) (w y : V) :
    ⟪w, E a b y⟫_ℂ = (Formalism.REAL.sgn ε a b : ℂ) * ⟪E b a w, y⟫_ℂ := by
  rw [hU b a w y, sgn_symm, ← mul_assoc, sgn_sq_one, one_mul]

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E)
    (l : List (Fin n × Fin n)) : ∃ c : ℂ, c ≠ 0 ∧ ∀ w x : V,
      ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ =
        c * ⟪((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w, x⟫_ℂ := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, fun w x => by simp⟩
  | cons p t ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨(Formalism.REAL.sgn ε p.1 p.2 : ℂ) * c, mul_ne_zero ?_ hc, fun w x => ?_⟩
    · intro h0; have := sgn_sq_one ε p.1 p.2; rw [h0] at this; simp at this
    · simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.map_nil, List.prod_append, List.prod_nil, mul_one, Module.End.mul_apply,
        Prod.fst_swap, Prod.snd_swap] at h ⊢
      rw [inner_E_right hU, h, mul_assoc]

end GlobalTheory.SignInnerAdjoint

theorem GlobalTheory.SignInnerAdjoint.main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  intro n ε V _ _ E hU l w x hne
  obtain ⟨c, hc, h⟩ := GlobalTheory.SignInnerAdjoint.word_adj hU l
  rw [h] at hne
  have h2 := right_ne_zero_of_mul hne
  intro h3; exact h2 (inner_eq_zero_symm.mp h3)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesTer
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)), IsCompact X → IsClosed (SUSupp σ J ε) → (∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_cohomology_injective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → (∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = 0 → x = 0 := by
  first | (exact @GlobalTheory.EtC.kerLaurent) | (exact GlobalTheory.EtC.kerLaurent) | (intros; apply GlobalTheory.EtC.kerLaurent  <;> assumption)
end


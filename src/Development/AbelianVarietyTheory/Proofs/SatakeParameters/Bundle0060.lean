import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import ReciprocityTheory.Hypotheses.GalCoh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixedStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.tame_vanish | exact GlobalTheory.StringRepresentationDecomposition.tame_vanish | (intros; apply GlobalTheory.StringRepresentationDecomposition.tame_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertiaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), Br.DegW nbr i w hw := by
  first | exact @GlobalTheory.bridge_degW | exact GlobalTheory.bridge_degW | (intros; apply GlobalTheory.bridge_degW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLengthStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.longOrbit_thickLetters_clusters_and_length : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j → 2 * j + 2 ≤ H.Lw → Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  first | exact @GlobalTheory.long_clusters | exact GlobalTheory.long_clusters | (intros; apply GlobalTheory.long_clusters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeAndBoundStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  first | exact @GlobalTheory.HTW.wMax_le_and_ge | exact GlobalTheory.HTW.wMax_le_and_ge | (intros; apply GlobalTheory.HTW.wMax_le_and_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersPageLargeScaleBoundsOfLargeScaleStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roomy_of_large_scale : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  first | exact @GlobalTheory.HTW.roomy_of_large | exact GlobalTheory.HTW.roomy_of_large | (intros; apply GlobalTheory.HTW.roomy_of_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
section
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

abbrev MP (R : Type) [CommRing R] (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) R

def genM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) := Matrix.of fun a s => X (a, s)

def cofAct (R : Type) [CommRing R] (n : ℕ) : MP R n →ₐ[R] MP R n :=
  aeval fun v => (genM R n).adjugate v.2.rev v.1

def nuDual {m : ℕ} (ν : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ := fun i => ν 0 - ν i.rev

def CofRel (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (f g : MP R (m + 1)) : Prop :=
  (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * g = cofAct R (m + 1) f

def stdN (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (dualWeyl O n n ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def stdD (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (weyl O n n le_rfl ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def rnd (Kf : Type) [Field Kf] {n : ℕ} (e : ℤ) (g : Matrix (Fin n) (Fin n) Kf) : MP Kf n →ₗ[Kf] MP Kf n :=
  g.det ^ (-e) • (rowAct Kf g⁻¹).toLinearMap

def twLat {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n : ℕ} (e : ℤ) (S : Submodule O (MP Kf n))
    (g : Matrix (Fin n) (Fin n) Kf) : Submodule O (MP Kf n) :=
  S.map ((rnd Kf e g).restrictScalars O)

def twOf {Kf : Type} [Field Kf] {n : ℕ} (s : ℕ) (h : Matrix (Fin n) (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf :=
  if Even s then h else (h⁻¹).transpose

def PosOk (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν ν' : Fin n → ℕ) (e e' c : ℤ)
    (tw : Matrix (Fin n) (Fin n) Kf → Matrix (Fin n) (Fin n) Kf) (Ψ : MP Kf n →ₗ[Kf] MP Kf n) : Prop :=
  (∀ f ∈ dualWeyl Kf n n ν, Ψ f = 0 → f = 0) ∧
  (dualWeyl Kf n n ν).map Ψ = dualWeyl Kf n n ν' ∧
  (∀ h : Matrix (Fin n) (Fin n) Kf, IsUnit h.det → ∀ f ∈ dualWeyl Kf n n ν,
    Ψ (rnd Kf e h f) = h.det ^ c • rnd Kf e' (tw h) (Ψ f)) ∧
  (stdN O Kf n ν).map (Ψ.restrictScalars O) = stdN O Kf n ν' ∧
  (stdD O Kf n ν).map (Ψ.restrictScalars O) = stdD O Kf n ν'

def renP {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {ι : Type} (e : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ ι) :
    Formalism.L2.DIV.Pol Kf ι (P.m + 1) →ₐ[Kf] P.Xsp :=
  rename fun y => ⟨(e.symm y.1).1, ((e.symm y.1).2, y.2)⟩

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimitiveRootNotPrimePowMapNeOneStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRoot_notPrimePow_map_ne_one' : ∀ (k : Type) [Field k] (O : Type) [CommRing O] [IsDomain O] (f : O →+* k) (ζ : O) (n : ℕ), 1 < n → IsPrimitiveRoot ζ n → (¬ IsPrimePow n) → f ζ ≠ 1 := by
  first | exact @GlobalTheory.primitiveRoot_notPrimePow_map_ne_one | exact GlobalTheory.primitiveRoot_notPrimePow_map_ne_one | (intros; apply GlobalTheory.primitiveRoot_notPrimePow_map_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointConditionStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEqualityStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sixth_character_equality : HeckeCharEqOfLAdicRealisation := by
  first | exact @GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds | exact GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds | (intros; apply GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatementStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sixth_weight_statement : PurityStringWeight := by
  first | exact @GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity | exact GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity | (intros; apply GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatumStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitEx_every_datum : ∀ D : D7, Formalism.L2.SplitEx D := by
  first | exact @GlobalTheory.SplitConjPlace.splitEx_all | exact GlobalTheory.SplitConjPlace.splitEx_all | (intros; apply GlobalTheory.SplitConjPlace.splitEx_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingletonStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton : Numerics ∧ Rest := by
  first | exact @GlobalTheory.SixthNumerics.numerics_and_rest | exact GlobalTheory.SixthNumerics.numerics_and_rest | (intros; apply GlobalTheory.SixthNumerics.numerics_and_rest <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0048
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNegStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingSign_alternate_of_sign_neg : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 → Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧ Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  first | exact @GlobalTheory.signs_alternate_inert | exact GlobalTheory.signs_alternate_inert | (intros; apply GlobalTheory.signs_alternate_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedByRepMatricesOfScalarExtensionStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L)), EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L)))) → EndSpanned τ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_endSpanned_map | exact GlobalTheory.SplitField.endSpanned_of_endSpanned_map | (intros; apply GlobalTheory.SplitField.endSpanned_of_endSpanned_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfiStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)), DirectSum.IsInternal Vs → (∀ m, IsInv (mapRep f τ) (Vs m)) → (∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) → ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧ ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  first | exact @GlobalTheory.SplitField.descend_decomp | exact GlobalTheory.SplitField.descend_decomp | (intros; apply GlobalTheory.SplitField.descend_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbeddingStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧ ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  first | exact @GlobalTheory.LocPlace.exists_place_of_emb | exact GlobalTheory.LocPlace.exists_place_of_emb | (intros; apply GlobalTheory.LocPlace.exists_place_of_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroupStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_local_field_eq_card_decomposition_group : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) [IsGalois ℚ E] (v : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) → Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range c)) = Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) := by
  first | exact @GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer | exact GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer | (intros; apply GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbeddingStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.floor_size_bounds_at_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m), Thick D.host g → L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  first | exact @GlobalTheory.HTW.SizeThick.size_thick | exact GlobalTheory.HTW.SizeThick.size_thick | (intros; apply GlobalTheory.HTW.SizeThick.size_thick <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbeddingStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.floor_size_bounds_not_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.size_not_thick | exact GlobalTheory.HTW.size_not_thick | (intros; apply GlobalTheory.HTW.size_not_thick <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  first | exact @GlobalTheory.RowTie.howeUp_of_pairLift | exact GlobalTheory.RowTie.howeUp_of_pairLift | (intros; apply GlobalTheory.RowTie.howeUp_of_pairLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_prime_ne_typePrime : ∀ (D : D7) (l : ℕ) (k : Fin 2), TwistedPlaces.InertK D l → l ≠ D.host.g k := by
  first | exact @GlobalTheory.InertNotType.main | exact GlobalTheory.InertNotType.main | (intros; apply GlobalTheory.InertNotType.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternalStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)), DirectSum.IsInternal Us → (∀ m, IsIrrSub τ (Us m)) → ∀ W, IsIrrSub τ W → ∃ m, IsoSub τ W (Us m) := by
  first | exact @GlobalTheory.SplitField.isoSub_summand_of_isInternal | exact GlobalTheory.SplitField.isoSub_summand_of_isInternal | (intros; apply GlobalTheory.SplitField.isoSub_summand_of_isInternal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfMultVNeZero
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.TwistDualLoc

def matGRep {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_dot {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) :
    IsDual1 PD (matRep M) (matRep (twistM (dualM M) (cycLL PD LL))) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose).mulVec y) =
      ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

end

end GlobalTheory.HTW.TwistDualLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondIffRhoOfGoodPoint
section
noncomputable section

namespace GlobalTheory.ParamRepCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations
open scoped Pointwise

section Inertia

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma valuation_lt_one_iff_eq_zero_or_inv_notMem' (B : ValuationSubring Ω) (y : Ω) :
    B.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ B := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← B.valuation_le_one_iff, map_inv₀]
    have h0 : 0 < B.valuation y := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hy
    simp [hy, inv_le_one₀ h0]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma smul_mem_smul_valuationSubring_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    h • y ∈ h • B ↔ y ∈ B := by
  refine ⟨fun hy => ?_, ValuationSubring.smul_mem_pointwise_smul h y B⟩
  have := ValuationSubring.smul_mem_pointwise_smul h⁻¹ _ _ hy
  simpa [smul_smul] using this

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma valuation_smul_smul_lt_one_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    (h • B).valuation (h • y) < 1 ↔ B.valuation y < 1 := by
  rw [valuation_lt_one_iff_eq_zero_or_inv_notMem', valuation_lt_one_iff_eq_zero_or_inv_notMem', ← smul_inv'',
    smul_mem_smul_valuationSubring_iff]
  simp

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in

theorem _root_.GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq {A A' : ValuationSubring Ω} {g σ : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hg : g • A = A') (hσ : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A') : g⁻¹ * σ * g ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A := by
  subst hg
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    rw [mul_smul, mul_smul, hdec, inv_smul_smul]
  · rw [← valuation_smul_smul_lt_one_iff g]
    have hx' : (g • A).valuation (g • x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact ValuationSubring.smul_mem_pointwise_smul g x A hx
    have := hval (g • x) hx'
    convert this using 2
    rw [smul_sub]
    simp [AlgEquiv.smul_def]

end Inertia

section Clauses

variable (D : D7)

end Clauses

end GlobalTheory.ParamRepCompare

end
end


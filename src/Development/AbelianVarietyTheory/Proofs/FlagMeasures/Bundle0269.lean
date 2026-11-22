import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0266
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLevelOfPreservesFirstComponentsSplit
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem mem_levelVL_of_first_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J v sp hsig hdiag L hsd κ hκ hfirst
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag

  have pair1 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).1 =
      ∑ i, ∑ j, (sp (z i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro z y
    unfold hR hform
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have pair2 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).2 =
      ∑ i, ∑ j, (sp (z i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro z y
    unfold hR hform
    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

  have hprod : ∀ y : Fin n → E ⊗[F] v.adicCompletion F, y ∈ loc v L ↔
      (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2 := by
    intro y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add, map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm

  set Kv := v.adicCompletion F with hKv
  set φ1 : E ⊗[F] Kv →+* Kv := (RingHom.fst _ _).comp sp.toRingHom with hφ1
  set φ2 : E ⊗[F] Kv →+* Kv := (RingHom.snd _ _).comp sp.toRingHom with hφ2
  have e1 : ∀ a, φ1 a = (sp a).1 := fun _ => rfl
  have e2 : ∀ a, φ2 a = (sp a).2 := fun _ => rfl
  set K1 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ1 with hK1
  set K2 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ2 with hK2
  set J2 : Matrix (Fin n) (Fin n) Kv := (J.map (inclE (F := F) Kv)).map φ2 with hJ2

  have hU : cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) * J.map (inclE (F := F) Kv) *
      (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) = J.map (inclE (F := F) Kv) := hκ
  have hc : (cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv))).map φ2 = K1ᵀ := by
    refine Matrix.ext fun i j => ?_
    show (sp (sigR cm.sig Kv ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i))).2 = (sp ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i)).1
    rw [hsig]; rfl
  have hU2 : K1ᵀ * J2 * K2 = J2 := by
    have := congrArg (fun M => M.map φ2) hU
    simp only [Matrix.map_mul] at this
    rw [hc] at this
    exact this
  have hQ : ∀ u w : Fin n → Kv, (K1 *ᵥ u) ⬝ᵥ (J2 *ᵥ (K2 *ᵥ w)) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    conv_rhs => rw [← hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : ∀ u w : Fin n → Kv, (∑ i, ∑ j, u i * J2 i j * w j) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

  have hL2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∀ u : Fin n → Kv, (∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = u b) → u ⬝ᵥ (J2 *ᵥ w) ∈ v.adicCompletionIntegers F := by
    intro w
    constructor
    · rintro ⟨y, hy, ey⟩ u ⟨z, hz, ez⟩
      have h := ((hint _).1 (((hsd y).1 hy) z hz)).2
      rw [pair2] at h
      simp only [ez, ey] at h
      rw [← hsum]; exact h
    · intro h
      refine ⟨fun b => sp.symm (0, w b), ?_, fun b => by simp⟩
      refine (hsd _).2 fun z hz => (hint _).2 ⟨?_, ?_⟩
      · rw [pair1]; simp
      · rw [pair2]
        have := h (fun b => (sp (z b)).1) ⟨z, hz, fun _ => rfl⟩
        rw [← hsum] at this
        have e : ∀ j, (sp (sp.symm (0, w j))).2 = w j := fun j => by simp
        simp only [e]
        exact this

  have hH : ∀ x : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = (K1 *ᵥ x) b := hfirst
  have hK1inv : ∀ u : Fin n → Kv, ∃ u', K1 *ᵥ u' = u := by
    intro u
    refine ⟨(((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) *ᵥ u, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have : K1 * (((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) = 1 := by
      have := (bc φ1 κ).mul_inv
      exact this
    rw [this, Matrix.one_mulVec]
  have hK2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = (K2 *ᵥ w) b := by
    intro w
    rw [hL2, hL2]
    constructor
    · intro h u hu
      obtain ⟨u', rfl⟩ := hK1inv u
      rw [hQ]
      exact h u' ((hH u').2 hu)
    · intro h u hu
      rw [← hQ]
      exact h _ ((hH u).1 hu)

  have hc1 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).1 =
      (K1 *ᵥ fun j => (sp (x j)).1) b := by
    intro x b
    simp only [mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
    rfl
  have hc2 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).2 =
      (K2 *ᵥ fun j => (sp (x j)).2) b := by
    intro x b
    simp only [mulVec, dotProduct, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]
    rfl
  show κ ∈ UJ _ _ ⊓ stabGL _
  rw [Subgroup.mem_inf]
  refine ⟨hκ, fun x => ?_⟩
  change x ∈ loc v L ↔ _ ∈ loc v L
  rw [hprod x, hprod (_ *ᵥ x)]
  simp only [hc1, hc2]
  rw [hH (fun j => (sp (x j)).1), hK2 (fun j => (sp (x j)).2)]

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimeSqLeLocalHermitianDualIndexStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_sq_le_local_hermitian_dual_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ≠ 0 → T ^ 2 ≤ (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup := by
  first | exact @GlobalTheory.St.G.IdxLower.sq_le_local_index | exact GlobalTheory.St.G.IdxLower.sq_le_local_index | (intros; apply GlobalTheory.St.G.IdxLower.sq_le_local_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalRelIndexDvdHermitianDualStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_local_relIndex_dvd_hermitian_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, (T : 𝓞 F) ∈ v.asIdeal) → ∏ v ∈ S, (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ∣ L.toAddSubgroup.relIndex (dualL cm.sig J L).toAddSubgroup := by
  first | exact @GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd | exact GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd | (intros; apply GlobalTheory.St.G.GlobIdx.prod_loc_relIndex_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModelStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_transport_block_model : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_transport | exact GlobalTheory.GaugeQuot.gauge_transport | (intros; apply GlobalTheory.GaugeQuot.gauge_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegAsm.FixedForm.main | exact GlobalTheory.DegAsm.FixedForm.main | (intros; apply GlobalTheory.DegAsm.FixedForm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlagStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_pos_on_orth_liftedFlag : ∀ (D : D7) (T' : ℕ) (F' : Fg D ((T' : ℕ) : D.host.E)), 0 < T' → ∀ x ∈ orth (hS D) (Xplus F'), x ∉ Xsp F' → 0 < Algebra.trace ℚ D.host.E ((hS D).hT x x) := by
  first | exact @GlobalTheory.LoopC.PerpPos.trace_pos_perp | exact GlobalTheory.LoopC.PerpPos.trace_pos_perp | (intros; apply GlobalTheory.LoopC.PerpPos.trace_pos_perp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIsotropicFlagMovesStepIntoPrevStatement
section
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_isotropicFlag_moves_step_into_prev : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ j : ℕ, j ≤ r → ∀ v ∈ Fr.Fj j, n v - v ∈ Fr.Fj (j - 1) ∧ n.symm v - v ∈ Fr.Fj (j - 1) := by
  first | exact @GlobalTheory.unipRadical_moves_step_into_prev | exact GlobalTheory.unipRadical_moves_step_into_prev | (intros; apply GlobalTheory.unipRadical_moves_step_into_prev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth
section
noncomputable section

open MeasureTheory Metric
open scoped Matrix

namespace GlobalTheory.UJGrowth

variable {n : ℕ} {ε : Fin n → Bool}

def ent (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (Formalism.MainNotions.S.uMat g)

theorem ent_closedEmb : Topology.IsClosedEmbedding (ent (ε := ε)) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1

theorem mem_closedBall_iff_entries {x y : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall y R ↔ ∀ i j, ‖x i j - y i j‖ ≤ R := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hR

theorem mem_closedBall_zero_iff_entries {x : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall 0 R ↔ ∀ i j, ‖x i j‖ ≤ R := by
  rw [mem_closedBall_iff_entries hR]
  simp

theorem uMat_inv_mul' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g⁻¹ * g) = Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g from rfl, inv_mul_cancel]
  rfl

theorem uMat_mul_inv' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g * g⁻¹) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

theorem uMat_inv_eq (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.MainNotions.S.uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc Formalism.MainNotions.S.uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g) * Formalism.MainNotions.S.uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv', Matrix.mul_one]

theorem norm_inv_entry (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖Formalism.MainNotions.S.uMat g⁻¹ i j‖ = ‖Formalism.MainNotions.S.uMat g j i‖ := by
  rw [uMat_inv_eq]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem small_ball {S : Subgroup (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (h : (n : ℝ) * (R * (2 * δ)) ≤ 1) (x : Fin n → Fin n → ℂ) :
    μ (ent ⁻¹' (closedBall 0 R ∩ closedBall x δ)) ≤
      μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) := by
  by_cases hex : ∃ s ∈ ent ⁻¹' (closedBall 0 R ∩ closedBall x δ), s ∈ S
  · obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hex
    have hme : MeasurableEmbedding (fun t : Formalism.REAL.UJ ε => s * t) :=
      (Homeomorph.mulLeft s).isClosedEmbedding.measurableEmbedding
    conv_lhs => rw [← hμ.2.2.2 s hs]
    rw [hme.map_apply]
    refine measure_mono fun t ht => ?_
    have ht2 : ent (s * t) ∈ closedBall x δ := ht.2
    have h1 : ent (s * t) ∈ closedBall (ent s) (2 * δ) := by
      have := dist_triangle_right (ent (s * t)) (ent s) x
      rw [mem_closedBall]
      linarith [mem_closedBall.1 ht2, mem_closedBall.1 hs2]
    rw [Set.mem_preimage, mem_closedBall_iff_entries zero_le_one]
    intro i j
    have e : Formalism.MainNotions.S.uMat t = Formalism.MainNotions.S.uMat s⁻¹ * Formalism.MainNotions.S.uMat (s * t) := by
      rw [show Formalism.MainNotions.S.uMat (s * t) = Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat t from rfl, ← Matrix.mul_assoc,
        uMat_inv_mul', Matrix.one_mul]
    have e2 : Formalism.MainNotions.S.uMat t - 1 =
        Formalism.MainNotions.S.uMat s⁻¹ * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) := by
      rw [Matrix.mul_sub, ← e, uMat_inv_mul']
    have e3 : ent t i j - ent (1 : Formalism.REAL.UJ ε) i j = (Formalism.MainNotions.S.uMat t - 1) i j := rfl
    rw [e3, e2, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ l ∈ (Finset.univ : Finset (Fin n)),
        ‖Formalism.MainNotions.S.uMat s⁻¹ i l * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) l j‖ ≤ R * (2 * δ) :=
      fun l _ => by
        rw [norm_mul]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) hR
        · rw [norm_inv_entry]
          exact (mem_closedBall_zero_iff_entries hR).1 hs1 l i
        · exact (mem_closedBall_iff_entries (by linarith)).1 h1 l j
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    simpa using h
  · rw [measure_mono_null (fun s hs (hS : s ∈ (S : Set (Formalism.REAL.UJ ε))) => hex ⟨s, hs, hS⟩) hμ.2.2.1]
    exact zero_le

end GlobalTheory.UJGrowth

namespace GlobalTheory.UJGrowth

theorem growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε),
    Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ →
    ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R →
      μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  intro n ε S _ μ hμ hfin
  haveI := hμ.1
  have hemb : Topology.IsClosedEmbedding (ent (ε := ε)) := ent_closedEmb
  let ν : Measure (Fin n → Fin n → ℂ) := μ.map ent
  have hνA : ∀ A, MeasurableSet A → ν A = μ (ent ⁻¹' A) := fun A hA =>
    Measure.map_apply hemb.continuous.measurable hA
  have hcpt : ∀ y r, μ (ent ⁻¹' closedBall y r) < ⊤ := fun y r =>
    (hemb.isCompact_preimage (isCompact_closedBall y r)).measure_lt_top
  haveI : SigmaFinite ν := hemb.measurableEmbedding.sigmaFinite_map
  set M := μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) with hM
  have hMf : M ≠ ⊤ := (hcpt _ _).ne
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set d := Module.finrank ℝ (Fin n → Fin n → ℂ)
  let lam : Measure (Fin n → Fin n → ℂ) := Measure.addHaar
  refine ⟨M.toReal * (4 * N) ^ d, 2 * d, fun R hR => ?_⟩
  set δ := (2 * N * R)⁻¹ with hδ
  have hp : 1 ≤ 2 * N * R := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hcond : (n : ℝ) * (R * (2 * δ)) ≤ 1 := by
    have e : (n : ℝ) * (R * (2 * δ)) = n / N := by
      rw [hδ]; field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hsb : ∀ x, ν (closedBall 0 R ∩ closedBall x δ) ≤ M := fun x => by
    rw [hνA _ (measurableSet_closedBall.inter measurableSet_closedBall)]
    exact small_ball hμ (by linarith) hδ0.le hcond x
  have hset : {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} = ent ⁻¹' closedBall 0 R := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff_entries (by linarith)]
    rfl
  rw [hset, ← hνA _ measurableSet_closedBall]
  let W : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) := {p | p.1 ∈ closedBall 0 R ∧ dist p.1 p.2 ≤ δ}
  have hW : MeasurableSet W :=
    ((isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le continuous_dist continuous_const)).measurableSet
  have e1 : (ν.prod lam) W = lam (closedBall 0 δ) * ν (closedBall 0 R) := by
    rw [Measure.prod_apply hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ closedBall (0 : Fin n → Fin n → ℂ) R
    · rw [Set.indicator_of_mem hs, ← Measure.addHaar_closedBall_center lam s]
      congr 1
      ext x
      exact ⟨fun h => mem_closedBall'.2 h.2, fun h => ⟨hs, mem_closedBall'.1 h⟩⟩
    · rw [Set.indicator_of_notMem hs]
      have : Prod.mk s ⁻¹' W = ∅ := by
        ext x
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, hs, false_and, Set.mem_empty_iff_false]
      rw [this, measure_empty]
  have e2 : (ν.prod lam) W ≤ M * lam (closedBall 0 (2 * R)) := by
    rw [Measure.prod_apply_symm hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Fin n → Fin n → ℂ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact hsb x
    · have : (fun s => (s, x)) ⁻¹' W = ∅ := by
        ext s
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, mem_closedBall]
        rintro ⟨h1, h2⟩
        apply hx
        have := dist_triangle_left x 0 s
        rw [mem_closedBall]; linarith
      simp [this]
  rw [e1, Measure.addHaar_closedBall lam _ hδ0.le, Measure.addHaar_closedBall lam _ (by linarith)] at e2
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam _ one_pos).ne' measure_ball_lt_top.ne
  have e3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)) e2
  simp only [ENNReal.toReal_mul] at e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at e3
  have e4 : δ ^ d * (ν (closedBall 0 R)).toReal ≤ M.toReal * (2 * R) ^ d := by
    refine le_of_mul_le_mul_right ?_ hb0
    calc _ = δ ^ d * (lam (ball 0 1)).toReal * (ν (closedBall 0 R)).toReal := by ring
      _ ≤ _ := e3
      _ = _ := by ring
  have e5 : M.toReal * (2 * R) ^ d = δ ^ d * (M.toReal * (4 * N) ^ d * R ^ (2 * d)) := by
    have : 2 * R = δ * (4 * N) * R ^ 2 := by rw [hδ]; field_simp; ring
    rw [this, mul_pow, mul_pow, pow_mul]; ring
  rw [e5] at e4
  have e6 := le_of_mul_le_mul_left e4 (by positivity)
  have hνf : ν (closedBall 0 R) ≠ ⊤ := by
    rw [hνA _ measurableSet_closedBall]; exact (hcpt _ _).ne
  rw [← ENNReal.ofReal_toReal hνf]
  exact ENNReal.ofReal_le_ofReal e6

end GlobalTheory.UJGrowth
end
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebr
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulus
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPoints
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem cM_one (k r : ℕ) (β : Bk r) : cM k r β (Matrix.of.symm 1) = 0 := by
  rcases β with p | a | p | a
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (eI k r p.1.2) = 0
    exact Matrix.one_apply_ne (fun h => p.2.ne (by simpa [eI, Fin.ext_iff] using h))
  · funext j
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (wI k r j) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, wI] at h'
    have := a.isLt
    omega
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (esI k r p.1.2) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    have := p.1.1.isLt
    have := p.1.2.isLt
    omega
  · show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (esI k r a)).im = 0
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem pos_le (k r : ℕ) (i : Fin (2 * r + k + 1)) : pos k r i ≤ 2 * r := by
  have := i.isLt
  unfold pos
  split_ifs <;> omega

theorem eq_one_of_dep {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : Dep k r (2 * r + 1) (x - 1)) : x = 1 := by
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  exact h i j (by have := pos_le k r j; omega)

theorem countable_units (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Countable (Matrix (Fin n) (Fin n) E)ˣ := by
  haveI : Countable E :=
    Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : (Matrix (Fin n) (Fin n) E)ˣ => (u : Matrix (Fin n) (Fin n) E))
    Units.val_injective

theorem ofReal_five (t u h c g : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hh : 0 ≤ h) (hc : 0 ≤ c) (hg : 0 ≤ g) :
    ENNReal.ofReal (t * (u * h * c * g)) =
      ENNReal.ofReal t * (ENNReal.ofReal u * ENNReal.ofReal h * ENNReal.ofReal c * ENNReal.ofReal g) := by
  rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu]

abbrev MM (k r : ℕ) (E : Type) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E

theorem covolume_N : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hV : IsVolData σ J Λ P f T A s := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨⟨G, hG⟩, hGu⟩ := GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup F E σ k r J Λ P f T A s hV
  obtain ⟨ha1, ha2, ha3⟩ := GlobalTheory.T.unipotentModelAction_isAction_and_faithful F E σ k r J Λ P f T A s hV
  have hmem := GlobalTheory.T.integralUnipotent_mem_modelUnipotentAtPlace F E σ k r J Λ P f T A s hV
  choose DU hDUm hDUf hDUv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_div_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 / s p.1.2) (div_pos (h9 _) (h9 _))
  choose DC hDCm hDCf hDCv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 * s p.1.2) (mul_pos (h9 _) (h9 _))
  choose DH hDHm hDHf hDHv using GlobalTheory.T.covolume_middleLattice_homLattice_ideal F E σ k r J Λ P f T A s hV
  choose DG hDGm hDGf hDGv using fun a : Fin r =>
    GlobalTheory.T.skewLattice_inverseDifferentPow_covolume F E σ h1 h2 (r - a.val) (s a ^ 2) (pow_pos (h9 _) 2)
  let LB := blkSet (InfinitePlace E) k r
    (fun p => (ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) : Set _))
    (fun a => homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a))
    (fun p => (ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) : Set _))
    (fun a => (skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) : Set _))
  let DB := blkSet (InfinitePlace E) k r DU DH DC DG
  let NN : Set (InfinitePlace E → Mt k r) := {x | ∀ w, Matrix.of (x w) ∈ Nset k r}
  let ρ : G → (InfinitePlace E → Mt k r) → (InfinitePlace E → Mt k r) :=
    fun g => actM A ((g : (MM k r E)ˣ) : MM k r E)
  let o : InfinitePlace E → Mt k r := fun _ => Matrix.of.symm 1
  let gm : G → InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    fun g => gM A ((g : (MM k r E)ˣ) : MM k r E)
  have hρo : ∀ g w, ρ g o w = Matrix.of.symm (gm g w) := fun g w => by
    show Matrix.of.symm (gm g w * 1) = Matrix.of.symm (gm g w)
    rw [mul_one]
  have hgm : ∀ g w, gm g w ∈ Nset k r := fun g => hmem _ ((hG _).1 g.2)
  have hρ1 : ∀ x, ρ 1 x = x := fun x => by
    have e : (((1 : G) : (MM k r E)ˣ) : MM k r E) = 1 := rfl
    show actM A (((1 : G) : (MM k r E)ˣ) : MM k r E) x = x
    rw [e]; exact ha1 x
  have hρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by
    have e : (((g * h : G) : (MM k r E)ˣ) : MM k r E) = ((g : (MM k r E)ˣ) : MM k r E) * ((h : (MM k r E)ˣ) : MM k r E) := rfl
    show actM A (((g * h : G) : (MM k r E)ˣ) : MM k r E) x = _
    rw [e]; exact ha2 _ _ x
  have hρN : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN := fun g x hx w =>
    PI.AmpOrbQuot.nset_mul (hgm g w) (hx w)
  have hdep : ∀ (g : G) (d : ℕ), (∀ β : Bk r, degB r β < d →
      (fun w => cM k r β (ρ g o w)) = 0) → ∀ w, Dep k r d (gm g w - 1) := fun g d hg w =>
    GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish k r _ d (hgm g w) fun β hβ => by
      have := congrFun (hg β hβ) w
      rwa [hρo] at this
  have tw := GlobalTheory.T.existsUnique_layered_strictFundamentalDomain (V := fun β : Bk r => InfinitePlace E → VM k r β) ρ NN o (degB r)
    (fun β x w => cM k r β (x w)) LB DB (fun w => by simpa [o] using PI.AmpOrbQuot.nset_one) hρ1 hρm hρN
    (by
      rintro (p | a | p | a)
      · exact (ideLat _ _).zero_mem
      · exact ⟨0, ⟨fun a => by simp [form], fun c _ => by simp⟩, fun w l => by
          have e : (fun i => w.embedding ((0 : Fin (2 * r + k + 1) → E) i)) = 0 := by ext; simp
          rw [e, Matrix.mulVec_zero]
          simp [herm]
          rfl⟩
      · exact (ideLat _ _).zero_mem
      · exact (skewLat _ _ _).zero_mem)
    (by
      rintro (p | a | p | a) v
      · exact hDUf p v
      · exact hDHf a v
      · exact hDCf p v
      · exact hDGf a v)
    (fun β => funext fun w => cM_one k r β)
    (fun d g hg x hx β hβ => funext fun w => by
      have := GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast k r (gm g w) (Matrix.of (x w)) d (hdep g d hg w) (GlobalTheory.T.flagUnipotent_block_upper_unitriangular k r _ (hx w)) β hβ
      show cM k r β (ρ g x w) = cM k r β (x w) + cM k r β (ρ g o w)
      rw [hρo]
      exact this)
    (by
      intro g β hβ
      have hgN := (hG _).1 g.2
      have e : (fun w => cM k r β (ρ g o w)) = fun w => cM k r β (Matrix.of.symm (gm g w)) :=
        funext fun w => by rw [hρo]
      show (fun w => cM k r β (ρ g o w)) ∈ LB β
      rw [e]
      rcases β with p | a | p | a
      · exact GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice F E σ k r J Λ P f T A s hV _ hgN a
      · exact GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice F E σ k r J Λ P f T A s hV _ hgN a fun w =>
          GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth k r _ a (hgm g w) (hdep g _ hβ w))
    (by
      have lift : ∀ (β : Bk r) (l : InfinitePlace E → VM k r β),
          (∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = l w) ∧
            ∀ β' : Bk r, β' ≠ β → degB r β' ≤ degB r β → ∀ w, cM k r β' (Matrix.of.symm (gM A γ w)) = 0) →
          ∃ g : G, (fun w => cM k r β (ρ g o w)) = l ∧ ∀ β', β' ≠ β → degB r β' ≤ degB r β →
            (fun w => cM k r β' (ρ g o w)) = 0 := by
        rintro β l ⟨γ, hγ, hl, h0⟩
        obtain ⟨u, rfl⟩ := hGu γ hγ
        refine ⟨⟨u, (hG u).2 hγ⟩, funext fun w => ?_, fun β' h h' => funext fun w => ?_⟩
        · rw [hρo]; exact hl w
        · rw [hρo]; exact h0 β' h h' w
      rintro (p | a | p | a) l hl
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_entry F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.lift_row_middleSpace_integralPoint F E σ k r J Λ P f T A s hV a l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_corner F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal F E σ k r J Λ P f T A s hV a l hl))
    (fun g hg => by
      have h1' : ∀ w, gm g w = 1 := fun w => eq_one_of_dep (hdep g _ (fun β _ => hg β) w)
      exact Subtype.ext (Units.ext (ha3 _ h1')))
  obtain ⟨hNm, hN0⟩ := GlobalTheory.T.pi_unipotentModel_measurable_full_measure (InfinitePlace E) k r
  obtain ⟨hDm, hDv⟩ := GlobalTheory.T.measure_unipotent_tuples_free_entry_blocks (InfinitePlace E) k r DU DH DC DG hDUm hDHm hDCm hDGm
  set Dset : Set (InfinitePlace E → Mt k r) := {x | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
    ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet (InfinitePlace E) k r DU DH DC DG β} with hDset
  have hstrict : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ Dset := fun x hx => by
    obtain ⟨g, hg, hu⟩ := tw x hx
    exact ⟨g, ⟨hρN g x hx, hg⟩, fun g' hg' => hu g' hg'.2⟩
  have conv : ∀ S : Set (InfinitePlace E → Mt k r), (∀ x ∈ NN, ∃! g : G, ρ g x ∈ S) ↔
      ∀ x ∈ NN, ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E,
        (InN (σ : E →+* E) J P γ ∧ latMap γ Λ = Λ) ∧ actM A γ x ∈ S := fun S => by
    refine forall₂_congr fun x hx => ?_
    constructor
    · rintro ⟨g, hg, hu⟩
      refine ⟨_, ⟨(hG _).1 g.2, hg⟩, fun γ hγ => ?_⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      exact congrArg (fun g : G => ((g : (MM k r E)ˣ) : MM k r E)) (hu ⟨u, (hG u).2 hγ.1⟩ hγ.2)
    · rintro ⟨γ, hγ, hu⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      refine ⟨⟨u, (hG u).2 hγ.1⟩, hγ.2, fun g hg => ?_⟩
      exact Subtype.ext (Units.ext (hu _ ⟨(hG _).1 g.2, hg⟩))
  haveI : Countable G := by
    haveI := countable_units E (2 * r + k + 1)
    infer_instance
  refine ⟨⟨Dset, hDm, (conv Dset).1 hstrict⟩, fun 𝓓 h𝓓 => ?_⟩
  have hEq := GlobalTheory.T.strictFundamentalDomain_measure_eq (G := G) _ ρ NN 𝓓 Dset hNm hN0 h𝓓.1 hDm hρ1 hρm hρN
    (fun g => GlobalTheory.T.unipotentModelProductAction_measurePreserving E k r A _ (hgm g)) ((conv 𝓓).2 h𝓓.2) hstrict
  beta_reduce
  rw [hEq, hDv]
  simp only [hDUv, hDHv, hDCv, hDGv]
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [← GlobalTheory.T.unipotentRadical_blockCovolumes_prod _ (Fintype.card (InfinitePlace E)) k r s hd h9]
  have nnU : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnC : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnH : ∀ a : Fin r, 0 ≤ ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1) := fun a => by
    have := h9 a; positivity
  have nnG : ∀ a : Fin r, 0 ≤ |(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ Fintype.card (InfinitePlace E) := fun a => by
    have := h9 a; positivity
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => nnU p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnH a,
    ← ENNReal.ofReal_prod_of_nonneg fun p _ => nnC p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnG a,
    ofReal_five _ _ _ _ _ (by positivity) (Finset.prod_nonneg fun p _ => nnU p) (Finset.prod_nonneg fun a _ => nnH a)
      (Finset.prod_nonneg fun p _ => nnC p) (Finset.prod_nonneg fun a _ => nnG a),
    ENNReal.ofReal_pow (by norm_num)]
  simp

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstant
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapConstant

set_option maxHeartbeats 2000000 in
theorem gap_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
              (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
      GlobalTheory.CellAmp.GapCell k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have h3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hNdef : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hs, h3]
  set P : ℝ := (r : ℝ) + 1 with hPdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNd
  have hP1 : 1 ≤ P := by linarith
  have hN2 : 2 * P ≤ N := by rw [hNdef]; linarith
  have hN1 : 1 ≤ N := by linarith
  have h2P : 0 < 2 * P := by linarith
  have hsq : 0 < Real.sqrt (2 * P) := Real.sqrt_pos.mpr h2P
  have hsq1 : 1 ≤ Real.sqrt (2 * P) := Real.one_le_sqrt.mpr (by linarith)
  have hrp : (2 * P) ^ ((9 : ℝ) / 2) = (2 * P) ^ 4 * Real.sqrt (2 * P) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add h2P]
    norm_num
  rw [hrp]
  set X : ℝ := 3 * P * N ^ 2 + N ^ 3 with hX
  have ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r (1000 * ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X) = 2000 * P ^ 4 * X := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [← hPdef]
    field_simp
    ring

  have hAS : Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * P * N ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    have e : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k := by push_cast; ring
    rw [e]
    have hd0 : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 := by nlinarith
    have hd : (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2 ≤ 2 * P * N := by
      rw [hNdef]; nlinarith
    have hm : 2 * (r : ℝ) + k ≤ N := by rw [hNdef]; linarith
    calc (2 * (r : ℝ) + k) * ((r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2)
        ≤ N * (2 * P * N) := mul_le_mul hm hd hd0 (by linarith)
      _ = 2 * P * N ^ 2 := by ring
  have hAS0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.dN
    apply mul_nonneg (Nat.cast_nonneg _); nlinarith
  have hAG : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * N * P := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have : (k : ℝ) + r ≤ N := by rw [hNdef]; linarith
    nlinarith
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * P ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; rw [hPdef]; nlinarith
  have hM0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r := by unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity

  have hP35 : P ^ 3 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP15 : P ≤ P ^ 5 := by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 5 by norm_num)
  have hP25 : P ^ 2 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP5 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
  have hN12 : N ≤ N ^ 2 := by nlinarith
  have hN21 : 1 ≤ N ^ 2 := by nlinarith
  have hN2_0 : 0 ≤ N ^ 2 := by positivity
  have hP50 : 0 ≤ P ^ 5 := by positivity
  have hbig : 6000 * P ^ 5 * N ^ 2 ≤ 2000 * P ^ 4 * X := by
    rw [hX]
    have : 0 ≤ P ^ 4 * N ^ 3 := by positivity
    nlinarith
  have m1 : P ^ 3 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP35 hN2_0
  have m2 : P ^ 3 * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP35 hN12 (by positivity) hP50
  have m3 : P * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP15 hN12 (by positivity) hP50
  have m4 : (1 : ℝ) ≤ P ^ 5 * N ^ 2 := one_le_mul_of_one_le_of_one_le hP5 hN21
  have m5 : P * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP15 hN2_0
  have m6 : P ^ 2 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP25 hN2_0
  have hprod : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul hM (show Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 2 * P * N ^ 2 + 4 * N * P by linarith)
      (add_nonneg hAS0 hAG0) (by nlinarith)
  have hprod2 : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsqN : 0 ≤ (2 * P) ^ 4 * Real.sqrt (2 * P) - 1 := by
    have : 1 ≤ (2 * P) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · have hX3 : N ^ 3 ≤ X := by rw [hX]; nlinarith
    have hN3 : 0 ≤ N ^ 3 := by positivity
    have : X ≤ ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X := by nlinarith
    nlinarith
  · rw [ha]
    have e : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      2 * (Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) = 4 * (P ^ 3 * N ^ 2) + 8 * (P ^ 3 * N) := by ring
    nlinarith
  · rw [ha]
    have e : (9 : ℝ) * ((r : ℝ) + 1) * N ^ 2 = 9 * (P * N ^ 2) := by rw [← hPdef]; ring
    rw [e]
    nlinarith
  · unfold GlobalTheory.CellAmp.GapCell
    rw [ha]
    have e : 10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) =
      10 * (((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r)) := by ring
    rw [e]
    have : P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) = 2 * (P ^ 3 * N ^ 2) + 4 * (P ^ 3 * N) := by ring
    nlinarith

theorem gap_constant_exists : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  refine ⟨1000, fun D ε lam hg => ⟨_, hg, ?_⟩⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact gap_thresholds D.R.k D.R.rS hk

end GlobalTheory.GapConstant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasureStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLevi_realPlaces_product_measure : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  first | exact @GlobalTheory.LeviIso.levi_product | exact GlobalTheory.LeviIso.levi_product | (intros; apply GlobalTheory.LeviIso.levi_product <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtConvolutionArchimedeanUnitaryLieAlgebrStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra : ∀ (B : RowsAut) (A : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (χ : B.I.Gf → ℂ) (ψ : B.I.GA → ℂ) (E : gInf B), ContDiff ℝ ∞ A → HasCompactSupport A → Continuous χ → HasCompactSupport χ → (∀ y, ψ y = A (fun v i j => uMat (y.1 v) i j) * χ y.2) → Continuous ψ ∧ HasCompactSupport ψ ∧ ∃ ψ' : B.I.GA → ℂ, Continuous ψ' ∧ HasCompactSupport ψ' ∧ ∀ F : B.I.L2 B.μf B.fund, HasDerivAt (fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf))) (∫ y, ψ' y • B.R y F ∂(B.I.muA B.μf)) 0 ∧ ∀ x : B.I.GA, HasDerivAt (fun t : ℝ => ∫ z, ψ ((x * ((fun v => expU (t • E v)), 1))⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) (∫ z, ψ' (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) 0 := by
  first | exact @GlobalTheory.ConvDeriv.convolution_hasDerivAt | exact GlobalTheory.ConvDeriv.convolution_hasDerivAt | (intros; apply GlobalTheory.ConvDeriv.convolution_hasDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HtDelta
section
namespace GlobalTheory.DiffModProd

theorem htDelta : Formalism.L2.SG.NGHTie.HTDelta := by
  unfold Formalism.L2.SG.NGHTie.HTDelta
  exact finprod_modK_localGen

end GlobalTheory.DiffModProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.InflBasic

open GlobalTheory.RowLev.Inhab GlobalTheory.Mem.RowsBundle

theorem finite_of_red {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (hg : 1 ≤ g) : Finite Q := by
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, -, -, s, hs⟩ := hK g hg
  refine Finite.of_surjective (fun t : s => ρ.toFun t) ?_
  intro q
  obtain ⟨x, hx, rfl⟩ := ρ.surj q
  obtain ⟨t, ht, htx⟩ := hs x hx
  have hk : t⁻¹ * x ∈ I.Kset := htx.1
  have htK : t ∈ I.Kset := by
    have hmem := (Ksub I).mul_mem ((mem_Ksub I x).2 hx) ((Ksub I).inv_mem ((mem_Ksub I _).2 hk))
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    exact (mem_Ksub I t).1 hmem
  refine ⟨⟨t, ht⟩, ?_⟩
  show ρ.toFun t = ρ.toFun x
  calc ρ.toFun t = ρ.toFun t * ρ.toFun (t⁻¹ * x) := by rw [(ρ.ker _ hk).2 htx, mul_one]
    _ = ρ.toFun (t * (t⁻¹ * x)) := (ρ.map_mul t htK _ hk).symm
    _ = ρ.toFun x := by rw [mul_inv_cancel_left]

theorem inflation_basic : ∀ (I : AutInst) (g : ℕ) (Q : Type) [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf) [μf.IsHaarMeasure], 1 ≤ g → Finite Q ∧ 0 < (μf (I.Kg g)).toReal ∧ ρ.toFun 1 = 1 ∧ (∀ x ∈ I.Kset, ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹) ∧ (∀ q : Q, μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) ∧ IsOpen {x | x ∈ I.Kset ∧ ρ.toFun x = q}) ∧ (∀ a, Integrable (ρ.lift μf a) μf ∧ IsLocallyConstant (ρ.lift μf a) ∧ ∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, ρ.lift μf a (k * x * k') = ρ.lift μf a x) ∧ (∀ a b, ρ.lift μf (a + b) = ρ.lift μf a + ρ.lift μf b) ∧ (∀ (c : ℂ) a, ρ.lift μf (c • a) = c • ρ.lift μf a) ∧ ∀ a, ρ.lift μf a 1 = a.coeff 1 / ((μf (I.Kg g)).toReal : ℂ) := by
  intro I g Q _ ρ μf _ hg
  have hQ : Finite Q := finite_of_red ρ hg
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, hopen, -, -⟩ := hK g hg
  obtain ⟨hcpt, -, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset := (mem_Ksub I 1).1 (Ksub I).one_mem
  have h1 : (1 : I.Gf) ∈ I.Kg g := (ρ.ker 1 h1K).1 ρ.map_one
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hpos : 0 < (μf (I.Kg g)).toReal :=
    ENNReal.toReal_pos (hopen.measure_pos μf ⟨1, h1⟩).ne'
      ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne
  refine ⟨hQ, hpos, ρ.map_one, fun x hx => ρ.map_inv hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨measure_preimage_mul μf t _, hopen.preimage (continuous_mul_left t)⟩
  · intro a
    refine ⟨integrable_lift ρ μf hg a, ?_, fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk'⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => x⁻¹ * y) ⁻¹' I.Kg g ∈ nhds x :=
      (hopen.preimage (continuous_mul_left x⁻¹)).mem_nhds (by
        show x⁻¹ * x ∈ I.Kg g
        rw [inv_mul_cancel]
        exact h1)
    filter_upwards [hnhds] with y hy
    have h := lift_biinv ρ μf a x 1 h1 (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  · intro a b
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.add_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx,
        MonoidAlgebra.coeff_add, Finsupp.add_apply, add_div]
    · rw [Pi.add_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx,
        add_zero]
  · intro c a
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.smul_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    · rw [Pi.smul_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, smul_zero]
  · intro a
    rw [ρ.lift_of_mem μf a h1K, ρ.map_one]

end GlobalTheory.InflBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulusStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → ∀ μ, IsGaugeSub (flagN ε W) (dimN n j) μ → ∀ m ∈ flagM ε W, μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) • μ := by
  first | exact @GlobalTheory.FlagModulus.modulus | exact GlobalTheory.FlagModulus.modulus | (intros; apply GlobalTheory.FlagModulus.modulus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNineStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localMass_le_genericMass_const_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  first | exact @GlobalTheory.localMass_le_genericMass_nine | exact GlobalTheory.localMass_le_genericMass_nine | (intros; apply GlobalTheory.localMass_le_genericMass_nine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedIwasawaIntegralSmallBallAsymptoticsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisedIwasawaIntegral_smallBall_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub (flagN ε W) dN μN → IsGaugeSub (flagM ε W) dM μM → IsGaugeSub (maxK ε) dK μK → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Filter.Tendsto (fun r : ℝ => (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  first | exact @GlobalTheory.IwConst.localised_iwasawa_asymptotics | exact GlobalTheory.IwConst.localised_iwasawa_asymptotics | (intros; apply GlobalTheory.IwConst.localised_iwasawa_asymptotics <;> assumption)
end


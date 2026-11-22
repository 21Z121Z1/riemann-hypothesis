import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.LubinTateReciprocity

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTranspose
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjLocComp

open GlobalTheory.TypeTame

theorem map_invTranspose {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (f : A →+* B) (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.map f (invTranspose n g) = invTranspose n (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  rw [invTranspose_val, ← map_inv]
  rfl

theorem exists_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (hσ : IsLocS S s σ) :
    ∃ (κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : L, κ (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧
      IsLocS S (conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  obtain ⟨i, T, hi, hiL, hTi, hTm, hTe⟩ := hσ
  obtain ⟨i₀, hi₀, hi₀', hi₀L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L s
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i₀ i hi₀ hi hi₀L hiL
  obtain ⟨i', hi', hi'', hi'L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L (conjSP s)
  let j : s.v.adicCompletion (maximalRealSubfield L) ≃+* (conjSP s).w.adicCompletion L := i'
  let κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L := i₀.symm.trans j
  have hκ : Continuous κ := hi'.comp hi₀'
  have hκ' : Continuous κ.symm := hi₀.comp hi''
  let ψ : GL (Fin n) ((conjSP s).w.adicCompletion L) →* GL (Fin n) (s.w.adicCompletion L) :=
    (invTranspose n).comp (Matrix.GeneralLinearGroup.map κ.symm.toRingHom)
  have hψc : Continuous ψ :=
    (continuous_invTranspose n).comp (Continuous.units_map _ (continuous_id.matrix_map hκ'))
  have hψκ : ∀ g, ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g) = invTranspose n g := fun g =>
    congrArg (invTranspose n) (GlobalTheory.LocCompSplit.gl_map_symm_map κ g)
  have hψs : Function.Surjective ψ := fun g =>
    ⟨Matrix.GeneralLinearGroup.map κ.toRingHom (invTranspose n g), by rw [hψκ, invTranspose_invTranspose]⟩
  have hj : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      Matrix.GeneralLinearGroup.map j.toRingHom g =
        Matrix.GeneralLinearGroup.map κ.toRingHom (Matrix.GeneralLinearGroup.map i₀.toRingHom g) := fun g => by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show j (g.val a b) = j (i₀.symm (i₀ (g.val a b)))
    rw [RingEquiv.symm_apply_apply]
  let σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L)) :=
    ⟨σ.V, σ.ρ.comp ψ, fun v => (σ.smooth v).preimage hψc,
      GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective σ.ρ ψ hψs σ.irr⟩
  refine ⟨κ, σ', LinearEquiv.refl ℂ σ.V, hκ, fun x => ?_, ⟨i', T, hi', hi'L, hTi, hTm, fun x hx a => ?_⟩, fun g a => ?_⟩
  · rw [← hi'L, conjSP_i, IsCMField.complexConj_apply_apply, ← hiL]
    show j (i₀.symm (i₀ (s.i x))) = j (s.i x)
    rw [RingEquiv.symm_apply_apply]
  · have h1 : ψ (Matrix.GeneralLinearGroup.map j.toRingHom (invTranspose n (s.loc n x))) =
        Matrix.GeneralLinearGroup.map i₀.toRingHom (s.loc n x) := by
      rw [hj, hψκ, map_invTranspose, invTranspose_invTranspose]
    have h2 := hTe x hx a
    rw [← h1, ← conjSP_loc] at h2
    exact h2
  · show σ.ρ (invTranspose n g) a = σ.ρ (ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g)) a
    rw [hψκ]

theorem exists_isLocS_conjSP : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  intro D n π s σ hσ
  obtain ⟨κ, σ', e, h1, h2, h3, h4⟩ := exists_conj π.S s σ hσ
  exact ⟨κ, σ', e, h1, fun x => by rw [h2, GlobalTheory.SplitPlaceOver.host_conj_eq'], h3, h4⟩

end GlobalTheory.ConjLocComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableHopfOrderSubgroupColength
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

open Matrix

theorem schurSquareMatrixToBlocks_mul {R : Type} [CommRing R] {m r : ℕ} (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk (M * N) = blk M * blk N := by
  simp only [blk]
  exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem schur_mul_conjLowUni : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  intro R _ m r g k hD hD'
  have hL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R, blk (lowUni Z) = fromBlocks 1 0 Z 1 :=
    fun Z => blk_unblk _
  have hLL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R,
      fromBlocks (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 (-Z) (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) * fromBlocks 1 0 Z 1 = 1 := by
    intro Z
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  set Y := Yof g with hY
  set k' := conjLowUni Y k with hk'
  have hK : blk k' = fromBlocks 1 0 Y 1 * blk k * fromBlocks 1 0 (-Y) 1 := by
    rw [hk', conjLowUni, schurSquareMatrixToBlocks_mul, schurSquareMatrixToBlocks_mul, hL, hL]
  have hkk : blk k = fromBlocks 1 0 (-Y) 1 * blk k' * fromBlocks 1 0 Y 1 := by
    rw [hK]
    calc blk k = 1 * blk k * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) * blk k * (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) := by
          rw [hLL]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hG : blk g = fromBlocks (Aof g) (Bof g) (Cof g) (Dof g) := (fromBlocks_toBlocks _).symm
  have hK' : blk k' = fromBlocks (Aof k') (Bof k') (Cof k') (Dof k') := (fromBlocks_toBlocks _).symm
  set A := Aof g
  set B := Bof g
  set C := Cof g
  set D := Dof g
  set A' := Aof k'
  set B' := Bof k'
  set C' := Cof k'
  set D' := Dof k'
  set Sc := Scof g with hSc
  have i1 : D⁻¹ * D = 1 := nonsing_inv_mul D hD
  have i2 : D * D⁻¹ = 1 := mul_nonsing_inv D hD
  have i3 : D'⁻¹ * D' = 1 := nonsing_inv_mul D' hD'
  have i4 : D' * D'⁻¹ = 1 := mul_nonsing_inv D' hD'
  have j1 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D⁻¹ * (D * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D * (D⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have j3 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D'⁻¹ * (D' * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i3, Matrix.one_mul]
  have j4 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D' * (D'⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i4, Matrix.one_mul]
  have hGL : blk g * fromBlocks 1 0 (-Y) 1 = fromBlocks Sc B 0 D := by
    rw [hG, fromBlocks_multiply]
    congr 1
    · rw [hSc, Scof, hY, Yof]; simp only [Matrix.mul_one, Matrix.mul_neg, Matrix.mul_assoc]; abel
    · simp
    · have hDY : D * Y = C := j2 C
      rw [Matrix.mul_one, Matrix.mul_neg, hDY, add_neg_cancel]
    · simp
  have hprod : blk (g * k) = fromBlocks (Sc * A' + B * C' + (Sc * B' + B * D') * Y) (Sc * B' + B * D')
      (D * C' + D * D' * Y) (D * D') := by
    rw [schurSquareMatrixToBlocks_mul, hkk, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGL, hK', fromBlocks_multiply, fromBlocks_multiply]
    simp
  have eD : Dof (g * k) = D * D' := by simp only [Dof, hprod, toBlocks_fromBlocks₂₂]
  have eC : Cof (g * k) = D * C' + D * D' * Y := by simp only [Cof, hprod, toBlocks_fromBlocks₂₁]
  have eB : Bof (g * k) = Sc * B' + B * D' := by simp only [Bof, hprod, toBlocks_fromBlocks₁₂]
  have eA : Aof (g * k) = Sc * A' + B * C' + (Sc * B' + B * D') * Y := by simp only [Aof, hprod, toBlocks_fromBlocks₁₁]
  refine ⟨?_, eD, ?_, ?_, ?_⟩
  · rw [eD, det_mul]; exact hD.mul hD'
  · rw [Yof, Yof, eD, eC, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.mul_assoc, j1, j3]
    abel
  · rw [Scof, Scof, eA, eB, eC, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, j1, j3, j4]
    abel
  · rw [Xof, Xof, Xof, eB, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, j4, i4]
    abel

end GlobalTheory.SchurExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHeckeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingCharacter_ladicGaloisCharacter_eq_hecke : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  first | exact @GlobalTheory.SeriesTie.charOf_psiAt_chrEq | exact GlobalTheory.SeriesTie.charOf_psiAt_chrEq | (intros; apply GlobalTheory.SeriesTie.charOf_psiAt_chrEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGeneratorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_mem_placesOver_generators : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ P ∈ Rl.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k) := by
  first | exact @GlobalTheory.TypePlacesOver.mem_placesOver | exact GlobalTheory.TypePlacesOver.mem_placesOver | (intros; apply GlobalTheory.TypePlacesOver.mem_placesOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolicStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_mirabolic_alt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  first | exact @GlobalTheory.MirTower.unfold_mirabolic | exact GlobalTheory.MirTower.unfold_mirabolic | (intros; apply GlobalTheory.MirTower.unfold_mirabolic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModuleLocalConclusions_usedForms : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm ∧ DeltaInvariantLattices.ConclusionE D HW F := by
  first | exact @GlobalTheory.NL.usedLocalConclusion_and_prvE | exact GlobalTheory.NL.usedLocalConclusion_and_prvE | (intros; apply GlobalTheory.NL.usedLocalConclusion_and_prvE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneAboveStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_above : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WDAbove D := by
  first | exact @GlobalTheory.WDAboveProof.main | exact GlobalTheory.WDAboveProof.main | (intros; apply GlobalTheory.WDAboveProof.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupDenseInDecompositionStatement
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_group_dense_in_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w),
    IsLocEmb A w ι → ∀ (g : Dec (F := E) A) (τ : GalLoc w), Lifts ι τ (g : G E Ω) →
    ∀ (U : Subgroup (GalLoc w)), IsOpen (U : Set (GalLoc w)) → ∀ (V : Set (Dec (F := E) A)), IsOpen V → g ∈ V →
    ∃ (σ : Weil h) (τ' : GalLoc w), Lifts ι τ' (σ : G E Ω) ∧ τ⁻¹ * τ' ∈ U ∧
      (⟨σ, Weil_le_Dec h σ.2⟩ : Dec (F := E) A) ∈ V := by
  first | exact @GlobalTheory.WeilDense.weil_dense | exact GlobalTheory.WeilDense.weil_dense | (intros; apply GlobalTheory.WeilDense.weil_dense <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Formalism.DoubleCosetMeasures.LatticeCoset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.Bundle0013
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChange
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficientStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (R : MvPolynomial (ι × ℕ) ℝ), R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n → (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicModularFormsIrreducibleDecomposition
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutReps

variable {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem comap_ne_bot_iff {f : M →ₗ[ℂ] N} (hf : Function.Injective f) (A : Submodule ℂ N) :
    A.comap f ≠ ⊥ ↔ A ⊓ LinearMap.range f ≠ ⊥ := by
  rw [inf_comm, ← Submodule.map_comap_eq, not_iff_not]
  constructor
  · intro h; rw [h, Submodule.map_bot]
  · intro h
    exact Submodule.map_injective_of_injective hf (by rw [h, Submodule.map_bot])

theorem iSupIndep_comap {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : iSupIndep A) : iSupIndep (fun i => (A i).comap f) := by
  intro i
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  have h3 : f x ∈ ⨆ j, ⨆ (_ : j ≠ i), A j := by
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).comap f) ≤ (⨆ j, ⨆ (_ : j ≠ i), A j).comap f := by
      apply iSup_le; intro j; apply iSup_le; intro hj
      exact Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
    exact hle h2
  have h4 : f x ∈ A i ⊓ ⨆ j, ⨆ (_ : j ≠ i), A j := Submodule.mem_inf.mpr ⟨h1, h3⟩
  rw [disjoint_iff.mp (hA i)] at h4
  have : f x = 0 := (Submodule.mem_bot ℂ).mp h4
  exact (Submodule.mem_bot ℂ).mpr (hf (this.trans (map_zero f).symm))

theorem iSup_comap_eq_top {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : ⨆ i, A i ⊓ LinearMap.range f = LinearMap.range f) : ⨆ i, (A i).comap f = ⊤ := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_iSup, Submodule.map_top]
  simp_rw [Submodule.map_comap_eq]
  simpa only [inf_comm] using hA

end GlobalTheory.AutReps

theorem GlobalTheory.AutReps.mtReal_decomp : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  intro D μ j Mr
  obtain ⟨_, ι, hι, S, hirr, hinj, hsurj, hne, hind, hsup⟩ :=
    GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  have hR := Mr.real_range
  refine ⟨ι, hι, S, hirr, hinj, ?_, ?_, ?_, ?_⟩
  · intro S' h1 h2
    apply hsurj S' h1
    rw [← hR]; exact (GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj _).mp h2
  · intro P
    rw [GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj, hR]; exact hne P
  · exact GlobalTheory.AutReps.iSupIndep_comap Mr.real_inj hind
  · apply GlobalTheory.AutReps.iSup_comap_eq_top Mr.real_inj
    rw [hR]; exact hsup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.HQStepBlocks

variable {F : Type} [Field F] {r c : ℕ}

theorem submatrix_eq_fromBlocks (x : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    x.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (bAA x) (bAD x) (bDA x) (bDD x) := by
  ext (i|i) (j|j) <;> simp [bAA, bAD, bDA, bDD]

theorem submatrix_mul' (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    (x * y).submatrix finSumFinEquiv finSumFinEquiv =
      x.submatrix finSumFinEquiv finSumFinEquiv * y.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [Matrix.submatrix_mul_equiv]

theorem blocks_mul (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧
    bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  have h := submatrix_mul' x y
  rw [submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, submatrix_eq_fromBlocks,
    fromBlocks_multiply, fromBlocks_inj] at h
  exact h

theorem det_eq_of_bDA_eq_zero (x : Matrix (Fin (r + c)) (Fin (r + c)) F) (hx : bDA x = 0) :
    x.det = (bAA x).det * (bDD x).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv x, submatrix_eq_fromBlocks, hx,
    Matrix.det_fromBlocks_zero₂₁]

theorem main : ∀ (F : Type) [Field F] (r c : ℕ) (p q : GL (Fin (r + c)) F), bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det = (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ∧ bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  intro F _ r c p q hp hq
  obtain ⟨h11, -, h21, h22⟩ := blocks_mul (p : Matrix (Fin (r + c)) (Fin (r + c)) F) (q : Matrix _ _ F)
  refine ⟨?_, ?_, ?_, det_eq_of_bDA_eq_zero _ hp, ?_⟩
  · rw [Units.val_mul, h21, hp, hq]; simp
  · rw [Units.val_mul, h11, hq]; simp
  · rw [Units.val_mul, h22, hp]; simp
  · obtain ⟨k11, -, k21, -⟩ := blocks_mul ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
      (p : Matrix _ _ F)
    have hone : ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) * (p : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hone, hp, Matrix.mul_zero, add_zero] at k11 k21
    have e11 : bAA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
      ext i j; simp [bAA, Matrix.one_apply]
    have e21 : bDA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
      ext i j; simp [bDA, Matrix.one_apply, Fin.ext_iff]; omega
    rw [e11] at k11
    rw [e21] at k21
    have hA : bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
      mul_eq_one_comm.mp k11.symm
    calc bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
        = bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) *
            (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) := by
          rw [hA, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, ← k21, Matrix.zero_mul]

end GlobalTheory.HQStepBlocks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProdStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_finiteField_eq_pow_mul_prod : ∀ (k : Type) [Field k] [Fintype k] (r : ℕ), (Nat.card (GL (Fin r) k) : ℝ) = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  first | exact @GlobalTheory.Mem.card_GL_eq_pow_mul_qE | exact GlobalTheory.Mem.card_GL_eq_pow_mul_qE | (intros; apply GlobalTheory.Mem.card_GL_eq_pow_mul_qE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardResidueRingCompletionChosenUniformiserStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueRing_completion_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  first | exact @GlobalTheory.ResidueCardUnif.card_kF_piP | exact GlobalTheory.ResidueCardUnif.card_kF_piP | (intros; apply GlobalTheory.ResidueCardUnif.card_kF_piP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnFaceLevelsBaseLevelSymmetricLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LevelsFace

theorem level_ext'₂ {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {L L' : LevelP Pg r ℂ}
    (h : ∀ g, g ∈ L.H ↔ g ∈ L'.H) (h' : ∀ g hg hg', L.chi ⟨g, hg⟩ = L'.chi ⟨g, hg'⟩) : L = L' := by
  obtain ⟨H, c⟩ := L
  obtain ⟨H', c'⟩ := L'
  obtain rfl : H = H' := Subgroup.ext h
  obtain rfl : c = c' := MonoidHom.ext fun g => h' g.1 g.2 g.2
  rfl

theorem chi_ofLocal_map' {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K] (σ : K →+* ℂ)
    (Hl : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (f : ∀ PP : Pg, Hl PP →* Multiplicative (kP PP.1))
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (g g' : G0 Pg r) (e : g = g') (hg : g ∈ Subgroup.pi Set.univ Hl)
    (hg' : g' ∈ Subgroup.pi Set.univ Hl) :
    Units.map σ.toMonoidHom ((LevelP.ofLocal Hl fun PP => addCharHom (ψ PP.1) (f PP)).chi ⟨g, hg⟩) =
      (LevelP.ofLocal Hl fun PP => addCharHom (σ.toMonoidHom.compAddChar (ψ PP.1)) (f PP)).chi ⟨g', hg'⟩ := by
  subst e
  refine ((congrArg (Units.map σ.toMonoidHom) (MonoidHom.finsetProd_apply _ _ _)).trans (map_prod _ _ _)).trans
    (Eq.trans ?_ (MonoidHom.finsetProd_apply _ _ _).symm)
  exact Finset.prod_congr rfl fun PP _ => Units.ext rfl

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px)

theorem levels_of_eq (hI : I.Ok) {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    (eG : Gc X.B px ≃* G0 Pg X.toD7.R.r) (hId : IsPlacewiseIdentity X (px := px) eG) :
    ∃ ψ0 : ∀ PP : Pl X.toD7.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ0 ∧
      levPOf eG X.toD7.what₂.embLL (lev0 I) (chr0 I) = P0 Pg X.toD7.R.r ψ0 ∧
      ∃ π : Equiv.Perm (Fin X.toD7.R.r), IsSymOrd X.toD7.R.rS X.toD7.R.k π ∧
        (∀ g, g ∈ (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).H ↔
          reord π g ∈ (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).H) ∧
        ∀ g hg hg', (levPOf eG X.toD7.what₂.embLL (lev1 I) (chr1 I)).chi ⟨g, hg⟩ =
          (PsharpSym Pg X.toD7.R.r X.toD7.R.rS X.toD7.R.k ψ0).chi ⟨reord π g, hg'⟩ := by
  subst hPg
  have hs : ∀ g, eG.symm g = g := fun g =>
    funext fun w => (hId (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  have hle : X.toD7.R.k + X.toD7.R.rS ≤ X.toD7.R.r := by
    have := Formalism.L2.Col.r_eq_sym X.toD7.R
    omega
  refine ⟨fun PP => X.B.embLL.toMonoidHom.compAddChar (psiC I PP), fun PP hP h => ?_, level_ext'₂ (fun g => ?_)
    fun g hg hg' => ?_, (Formalism.L2.Col.symPerm X.toD7.R.r X.toD7.R.k X.toD7.R.rS).symm, fun a => ?_, fun g => ?_, fun g hg hg' => ?_⟩
  · have h1 : psiC I PP = 1 :=
      by
        ext x
        exact X.B.embLL.injective ((DFunLike.congr_fun h x).trans (map_one _).symm)
    rw [psiC_of_mem I hP] at h1
    exact hI.ch_ok.psi_zero_nontrivial_character _ h1
  · show eG.symm g ∈ lev0 I ↔ _
    rw [hs]
    exact Iff.rfl
  · exact chi_ofLocal_map' X.B.embLL _ _ (psiC I) _ _ (hs g) hg hg'
  · rw [Formalism.L2.Col.symPerm_symm_val hle]
    unfold Formalism.L2.Col.symIdxInv
    split_ifs <;> omega
  · show eG.symm g ∈ (Formalism.L2.Col.rPsymF I.Ch).grp ↔ _
    rw [hs]
    show g ∈ Subgroup.pi Set.univ _ ↔ reord _ g ∈ Subgroup.pi Set.univ _
    simp only [Subgroup.mem_pi]
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    show g w ∈ Formalism.L2.Col.HPsymF _ _ _ _ ↔ _
    rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap]
    exact Iff.rfl
  · apply Units.ext
    have key : ∀ (w : (X.B.primes px).vGs) (M M' : GL (Fin X.toD7.R.r) (kP w.1)) (e : M' = Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS M)
        (hM : M ∈ Formalism.L2.Col.HPsymF (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS)
        (hM' : M' ∈ unipSym (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k),
        X.B.embLL ((Formalism.L2.Col.chiSymF (I.Ch.psi0 w) X.toD7.R.r X.toD7.R.k X.toD7.R.rS ⟨M, hM⟩ : X.B.LLˣ) : X.B.LL) =
          X.B.embLL (psiC I w.1 (Multiplicative.toAdd (symHom (kP w.1) X.toD7.R.r X.toD7.R.rS X.toD7.R.k ⟨M', hM'⟩))) := by
      intro w M M' e hM hM'
      subst e
      rw [Formalism.L2.Col.chiSymF_apply, Formalism.L2.Col.chiSym_eq_symHom _ _ _ _ _ hM', psiC_of_mem I w.2]
      rfl
    show X.B.embLL (((Formalism.L2.Col.rPsymF I.Ch).chr ⟨eG.symm g, hg⟩ : X.B.LLˣ) : X.B.LL) = _
    rw [Formalism.L2.Col.LevFam.chr_apply, Units.coe_prod, map_prod]
    erw [MonoidHom.finsetProd_apply, Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact key w _ _ (congrArg (fun h : G0 (X.B.primes px).vGs X.toD7.R.r =>
      Formalism.L2.Col.toSymOrd (kP w.1) X.toD7.R.r X.toD7.R.k X.toD7.R.rS (h w)) (hs g)).symm _ _

theorem levelsL_face0 : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  intro X px I hX U Xg tr L eG hI hL hId
  exact levels_of_eq X I hI hL.Pg eG hId

end GlobalTheory.Mem.R3.LevelsFace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEquivariantRealPlaceStatement
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugated_intertwiner_equivariant_real_place : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau R.θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  first | exact @GlobalTheory.ConjEquivRealSee.conjMap_update_real_see | exact GlobalTheory.ConjEquivRealSee.conjMap_update_real_see | (intros; apply GlobalTheory.ConjEquivRealSee.conjMap_update_real_see <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreAt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DatEx (X : Stages) (f : Top.Fr X.B.toPre) (T : Top.TwDat X.B) : Prop :=
  ∀ (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok), I.Ok → I.C = f → Set.range I.xi = T.set f → SelHalf I →
    GrpAt X I → VolTieG X.toD7 → ∀ Wt : Set X.B.places.Pl, Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) →
      ∃ z : Dat X I hX T Wt, z.R.toRealDat.ExAt ∧ (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.Ok3 1 ∧ GlobalTheory.RealGeo.InGeo z.geo

def CoreAt (X : Stages) (f : Top.Fr X.B.toPre) : Prop :=
  ∃ (C : Formalism.L2.Pj.CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL),
    (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧
    (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧
    (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧
    (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧
    Formalism.L2.Pj.LawsJ C ∧ Formalism.L2.Pj.LawsCore C.toCore ∧ Formalism.IndefR.FWT.AlgTie C ∧
    C.pb = (Top.Fr.at X f).P.pb ∧ Formalism.L2.Host.ValLL X.toD7 (Top.Fr.at X f) ∧
    ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Top.Fr.at X f →
      ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y)

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

section Cut

variable {G Γ : Type} [Group G] [Group Γ] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def cutSp (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (Q : Subgroup G) (ch : Q →* ℂˣ)
    {G₀ : Type} [Group G₀] (red : Q →* G₀) (P : Subgroup G₀) (ψ : P →* ℂˣ) : Submodule ℂ (G → W) :=
  Bridge.AdForms ι ρ J χ ⊓
    { carrier := {F | ∀ (κ : Q) (hκ : red κ ∈ P) (h : G), F (h * κ) = ((ch κ * ψ ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h}
      add_mem' := fun {F F'} hF hF' κ hκ h => by simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, smul_add]
      zero_mem' := fun κ hκ h => by simp
      smul_mem' := fun c F hF κ hκ h => by simp only [Pi.smul_apply, hF κ hκ h]; rw [smul_comm] }

def lvlForm {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G₀ : Type} [Group G₀] [Fintype G₀]
    (r : Representation K G₀ S.Forms) (P : Subgroup G₀) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) : S.Forms :=
  S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x)

end Cut

variable {D : D7}

variable (D) in

def km (n : ℕ) : Formalism.AUTREP.GAf D.host.E n →* GL (Fin n) (EAf D) := (ReciprocityTheory.Aut.GA D.host.E n).subtype

def stdJ {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Subgroup (Formalism.AUTREP.GAf D.host.E n) :=
  (Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comap (km D n)

def stdX {n : ℕ} (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n) : stdJ Ld →* ℂˣ :=
  (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld).comp ((km D n).subgroupComap _)

variable (D) in

def datV (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  datY n D.R.r D.R.t 1 hr Pg Q P (fun _ => chi) xi Frm.A

def UnitFr {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Prop := ∀ κ, finE V (P.ψ κ) = km D V.rank κ

def toGf {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : Formalism.AUTREP.GAf D.host.E n →* Bridge.Gf V :=
  (finHom V).rangeRestrict.comp P.ψ

def RatIso {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V) : Prop :=
  ∀ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V (e γ) = toGf P γ.1 ∧
    ∀ γ₀ : GL (Fin V.rank) D.host.E,
      (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
        (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom →
      Bridge.IsRatMat V (e γ) γ₀

def wtRep {V : HSp D} {n : ℕ} (c : CoefA V) (e : ReciprocityTheory.Aut.GQ D.host.E n ≃* Formalism.L2.Theta.GQ V) :
    Representation ℂ (ReciprocityTheory.Aut.GQ D.host.E n) c.W :=
  c.coef.ρ.comp e.toMonoidHom

end GlobalTheory.MtIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllTInclTTprod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.SchurTensor

theorem ellT_inclT_tprod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ τ, M.H τ) (v : M.Vec) :
    ellT M w (inclT M (PiTensorProduct.tprod ℂ v)) = ∏ τ, ⟪w τ, (v τ : M.H τ)⟫_ℂ := by
  simp [ellT, inclT]

theorem schur_tensor : ∀ (D : D7) (θ : InfF D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕 → IsInfFam θ → IsQuot V μ 𝓕 → ∀ x ∈ MultT θ M J χ, ∀ y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec), IsCuspForm θ V (y (PiTensorProduct.tprod ℂ w)) ∧ IntegrableOn (fun g => star (x v g) * y (PiTensorProduct.tprod ℂ w) g) 𝓕 μ ∧ ∫ g in 𝓕, star (x v g) * y (PiTensorProduct.tprod ℂ w) g ∂μ = ipT M μ 𝓕 y x * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v)) := by
  intro D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w
  have hx' := (mem_multT θ M J χ x).1 hx
  have hy' := (mem_multT θ M J χ y).1 hy
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'
  have hI := ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')
  refine ⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    obtain ⟨h1, h2⟩ := hI u w
    have e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) := by
      funext g
      rw [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rw [e]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]
    refine (congrArg (star c * ·) h2).trans ?_
    have e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ :=
      Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    rw [e2, ipT]
    ring
  | add a b ha hb =>
    have e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g := by
      funext g
      rw [map_add, Pi.add_apply, star_add, add_mul]
    rw [e]
    refine ⟨ha.1.add hb.1, ?_⟩
    rw [integral_add ha.1 hb.1, ha.2, hb.2, map_add, map_add, star_add, mul_add]

end GlobalTheory.Mem.SchurTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOneStatement
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ), letI : MeasurableSpace (P.adicCompletion L) := borel _; ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)), ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  first | exact @GlobalTheory.HaarMat.exists_haar_intMat | exact GlobalTheory.HaarMat.exists_haar_intMat | (intros; apply GlobalTheory.HaarMat.exists_haar_intMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChangeStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change : ∀ (D : D7) (T : CoreJ D) (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), VolTieG D → LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ)) → ∃ dict, LawsJ (reCore T dict T.mu T.chiW x₀ T.cE) ∧ LawsCore (reCore T dict T.mu T.chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | exact GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | (intros; apply GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth <;> assumption)
end


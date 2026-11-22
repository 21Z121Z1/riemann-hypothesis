import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0099
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0761
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegRightMulLetterShiftApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0762
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem goodStalks_structureModule {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} {d : ℕ}
    (t : Fin d → L.Sec) (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) (h : CotIndep t) :
    GoodStalks (structureModule X) t := by
  intro x i hx
  have := hreg x
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.weakly_regular_of_cotangent_indep (X.presheaf.stalk x) d (fun j => germSec (t j) hx) (hdim x)
    (h x i hx)
  have e : ((structureModule X).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    structureModuleStalkEquiv x
  refine ⟨(LinearEquiv.isWeaklyRegular_congr e _).2 h₁, ?_⟩
  set I := Ideal.span (Set.range fun j => germSec (t j) hx) with hI
  have hmap : (I • (⊤ : Submodule (X.presheaf.stalk x) ((structureModule X).presheaf.stalk x :))).map
      e.toLinearMap = I := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective,
      smul_eq_mul, Ideal.mul_top]
  rw [(Submodule.Quotient.equiv _ I e hmap).length_eq]
  exact h₂

end GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNum_eq_ncard {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K X)) {L : LB X} (hL : L.IsLB) (d : ℕ) :
    ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists K F → suppDim F ≤ (d : ℕ) →
      ∀ t : Fin d → L.Sec, GoodStalks F t →
        interNum K F (fun _ : Fin d => L) =
            ((support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)}).ncard : ℤ) ∧
          ∀ x ∈ support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)}, IsClosed ({x} : Set X) := by
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hF hd t hg
    have hlen : ∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1 := by
      intro x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
      have h := (hg x i hi).2
      have e : Ideal.span (Set.range fun j : Fin 0 => germSec (t j) hi) = ⊥ := by simp
      rw [e, Submodule.bot_smul] at h
      rwa [(Submodule.quotEquivOfEqBot _ rfl).length_eq] at h
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.euler_char_zero_dim_support hp F hd hlen
    have e : support F ∩ {x | ∀ j : Fin 0, x ∉ nonzeroLocus (t j)} = support F := by simp
    rw [e, interNum_of_isEmpty]
    exact ⟨h₁, h₂⟩
  | succ d ih =>
    intro F _ hF hd t hg
    have hg' : GoodStalks F (Fin.cons (t 0) (Fin.tail t) : Fin (d + 1) → L.Sec) := by
      rwa [Fin.cons_self_tail]
    obtain ⟨hm, hc⟩ := GlobalTheory.T.hyperplane_cut_good_stalks hL F (t 0) (Fin.tail t) hg'
    have e : (fun _ : Fin (d + 1) => L) = Fin.cons L (fun _ : Fin d => L) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hS : support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)} =
        support (cut F hL (t 0)) ∩ {x | ∀ j, x ∉ nonzeroLocus (Fin.tail t j)} := by
      rw [support_cut]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Fin.forall_fin_succ, Fin.tail]
      tauto
    rw [e, interNum_cons_eq_interNum_cut hL (t 0) (fun _ => hL) hF, hS]
    exact ih (cut F hL (t 0)) (FiniteCohTwists.cut hL _ hF) (suppDim_cut_le F hL (t 0) hd) _ hc

end GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem secVal_comb (Y : Var ℂ) (L : LB Y.X) {n : ℕ} (c : Fin n → ℂ) (b : Fin n → L.Sec) (i : L.ι)
    (y : CxPts Y.str (RingHom.id ℂ)) :
    secVal Y.str (RingHom.id ℂ) (∑ j, algebraMap ℂ Γ(Y.X, ⊤) (c j) • b j) i y =
      ∑ j, c j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
  have e : ∀ a : ℂ, algebraMap ℂ Γ(Y.X, ⊤) a = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str ⊤ a := fun a => by
    rw [← GlobalTheory.strHom_eq Y.algebraMap_Γ]
    exact (GlobalTheory.GeomConnConst.algX_top_strHom ℂ Y.X a).symm
  simp only [e, map_sum, secVal_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem koszul_count : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∀ᵐ C ∂(volume : Measure (Fin Y.dim → Fin n → ℂ)), ((({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℕ) : ℤ) = Y.inter fun _ => Δ := by
  intro Y Δ L r hL n b hb hP
  obtain ⟨Q, hQ, hC⟩ := GlobalTheory.T.generic_sections_cotangent_indep Y L hL n Y.dim b hb
  filter_upwards [GlobalTheory.T.ae_polynomial_nonvanishing _ _ Q hQ] with C hCQ
  have hct := hC C hCQ
  set t : Fin Y.dim → L.Sec := fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j with ht
  have hp : IsProjOver (strHom ℂ Y.X) := by
    rw [GlobalTheory.strHom_eq Y.algebraMap_Γ]
    exact Y.isProjOver
  have hg : GoodStalks (structureModule Y.X) t :=
    goodStalks_structureModule t (fun x => (GlobalTheory.T.variety_stalk_regular_dim Y x).1) (fun x => (GlobalTheory.T.variety_stalk_regular_dim Y x).2) hct
  obtain ⟨h₁, h₂⟩ := interNum_eq_ncard hp hL Y.dim (structureModule Y.X)
    (Y.isAmple_projective_O_one.finiteCohTwists Y.algebraMap_Γ _)
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq]) t hg
  rw [support_structureModule, Set.univ_inter] at h₁ h₂
  have hset : {y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι),
      y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0} =
      {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ {x | ∀ j, x ∉ nonzeroLocus (t j)}} := by
    ext y
    simp only [Set.mem_setOf_eq]
    have key : ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
        (∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 ↔
          y.1 (IsLocalRing.closedPoint ℂ) ∉ nonzeroLocus (t k)) := fun k i hi => by
      rw [← secVal_comb Y L (C k) b i y, ← mem_ptsIn, ← secVal_ne_zero_iff (t k) hi, not_not]
    constructor
    · intro h k
      obtain ⟨i, hi⟩ := exists_mem_ptsIn hL.cover y
      exact (key k i hi).1 (h k i hi)
    · intro h k i hi
      exact (key k i hi).2 (h k)
  rw [hset, GlobalTheory.T.closed_points_count_complex Y _ h₂, ← h₁]
  exact (Var.inter_eq_of_toPic_eq (fun _ => hL) (fun _ => hP.toPic_eq)).symm

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGL
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

section Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

def skewGram (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) : GL (Fin m) (Fv F v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (J.map τ) (by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero τ).2 hd)

theorem map_comp_conj_skew (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v) :
    J.map (τ.comp σ) = -(J.map τ)ᵀ :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, AlgHom.comp_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [hs j i, map_neg]

theorem splitPairMat_unitary_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v)
    {a b : Matrix (Fin m) (Fin m) (Fv F v)} (e : bᵀ * J.map τ * a = J.map τ) :
    Formalism.UG.cT (sigR _ σ) (splitPairMat h τ a b) * JR (Fv F v) J * splitPairMat h τ a b = JR (Fv F v) J := by
  refine splitMat_ext h τ ?_ ?_
  · rw [map_unitary, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj, e]
  · rw [map_unitary, comp_conj_conj h, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj,
      map_comp_conj_skew hs, Matrix.mul_neg, Matrix.neg_mul, neg_inj,
      ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, e]

theorem splitHom_injective_skew (h : IsCMExt F E σ) (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) :
    Function.Injective (splitHom σ J τ) := fun g g' e => by
  have c : ∀ x : GLoc σ J v, splitHom σ J (τ.comp σ) x = dualConj (skewGram hd τ) (splitHom σ J τ x) :=
    fun x => eq_dualConj_iff.2 (splitHom_unitary τ x)
  exact matHom_injective _ σ J (Units.ext (splitMat_ext h τ (congrArg Units.val e) (by
    rw [← splitHom_val, ← splitHom_val, c, c, e])))

theorem splitHom_surjective_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) : Function.Surjective (splitHom σ J τ) := fun x =>
  ⟨(⟨splitPairGL h τ x (dualConj (skewGram hd τ) x),
    splitPairMat_unitary_skew h hs τ ((eq_dualConj_iff (A := skewGram hd τ)).1 rfl)⟩ : HR (Fv F v) σ J),
    Units.ext (splitPairMat_map h τ _ _)⟩

end Skew

theorem blkGL_bijective {R : Type} [CommRing R] (n : ℕ) : Function.Bijective (blkGL (R := R) n) :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv).bijective

theorem Jst_mul_self (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  have e : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) *
      Matrix.fromBlocks 0 1 (-1) 0 = -1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have e2 := Matrix.submatrix_mul_equiv
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (finSumFinEquiv (m := n) (n := n)).symm (finSumFinEquiv (m := n) (n := n)).symm
    (finSumFinEquiv (m := n) (n := n)).symm
  rw [e] at e2
  refine e2.trans (Matrix.ext fun i j => ?_)
  simp [Matrix.one_apply]

theorem Jst_det_ne_zero (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  have : IsUnit (Jst D n).det :=
    Matrix.isUnit_det_of_left_inverse (B := -Jst D n) (by rw [Matrix.neg_mul, Jst_mul_self, neg_neg])
  exact this.ne_zero

theorem Jst_skew (D : D7) (n : ℕ) (i j : Fin (n + n)) :
    D.sp.cm.sig (Jst D n j i) = -Jst D n i j := by
  have key : ∀ a b : Fin n ⊕ Fin n,
      D.sp.cm.sig ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) b a) =
        -(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) a b := by
    rintro (a | a) (b | b) <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, map_zero, neg_zero, map_neg]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
  exact key _ _

theorem thU_bijective : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    Function.Bijective (thU D n v τ) := fun D n _ τ =>
  (blkGL_bijective n).comp
    ⟨splitHom_injective_skew (isCMExt_host D) (Jst_det_ne_zero D n) τ,
      splitHom_surjective_skew (isCMExt_host D) (Jst_skew D n) (Jst_det_ne_zero D n) τ⟩

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnitStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_continuous_unit : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | exact GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | (intros; apply GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionReal
section
noncomputable section

open Finset Formalism.REAL
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.PairMult.CenScal (UD Ds eb mi eu xl xl_apply xs_same levRel_xl leftMulLetter negRightMulLetterShift central_letters evB_intertwine
  mem_of_eb center_UD_le glHom glHom_comm glHom_single qdet_map)

namespace GlobalTheory.CompanionTheory.BlockCapelliWords

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

variable {n : ℕ}

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (X : Fin n → Fin n → A) (f : Fin t → Fin n)
    (hf : Function.Injective f) (u : ℂ) : qminor X f f u = qdet (fun i k => X (f i) (f k)) u := by
  unfold qdet qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp [Tm, hf.eq_iff]

theorem qminor_of_size_zero {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (ht : t = 0) (X : Fin n → Fin n → A)
    (f : Fin t → Fin n) (u : ℂ) : qminor X f f u = 1 := by
  subst ht
  simp [qminor]

theorem blkE_injective (lev : Fin n → ℕ) (j : ℕ) : Function.Injective (blkE lev j) :=
  ((blk lev j).orderEmbOfFin rfl).injective

theorem lev_blkE (lev : Fin n → ℕ) (j : ℕ) (i : Fin (blk lev j).card) : lev (blkE lev j i) = j := by
  have h : blkE lev j i ∈ blk lev j := (blk lev j).orderEmbOfFin_mem rfl i
  exact (Finset.mem_filter.1 h).2

theorem exists_blkE (lev : Fin n → ℕ) (a : Fin n) : ∃ i, blkE lev (lev a) i = a := by
  refine ⟨((blk lev (lev a)).orderIsoOfFin rfl).symm ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩, ?_⟩
  exact congrArg Subtype.val (((blk lev (lev a)).orderIsoOfFin rfl).apply_symm_apply
    ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩)

abbrev numLev (lev : Fin n → ℕ) : ℕ := univ.sup lev + 1

abbrev bd (lev : Fin n → ℕ) : Fin (numLev lev) → ℕ := fun i => (blk lev i).card

def blkEquiv (lev : Fin n → ℕ) : (Σ i, Fin (bd lev i)) ≃ Fin n :=
  Equiv.ofBijective (fun p => blkE lev p.1 p.2) (by
    constructor
    · rintro ⟨i, p⟩ ⟨k, q⟩ h
      have h' : blkE lev i p = blkE lev k q := h
      have hik : i = k := Fin.ext ((lev_blkE lev i p).symm.trans ((congrArg lev h').trans (lev_blkE lev k q)))
      subst hik
      rw [blkE_injective lev i h']
    · intro a
      obtain ⟨i, hi⟩ := exists_blkE lev a
      exact ⟨⟨⟨lev a, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))⟩, i⟩, hi⟩)

def kpWord : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if p.1 then FreeAlgebra.ι ℂ (true, p.2) - FreeAlgebra.ι ℂ (false, p.2)
    else FreeAlgebra.ι ℂ (true, p.2) + FreeAlgebra.ι ℂ (false, p.2)

theorem evLv_eq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (F1 F2 : Fin n → Fin n → Module.End ℂ V)
    (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    evLv lev F1 F2 b = GlobalTheory.CompanionTheory.PairMult.evB lev F1 F2 (kpWord b) := by
  have h : evLv lev F1 F2 = (GlobalTheory.CompanionTheory.PairMult.evB lev F1 F2).comp kpWord := by
    apply FreeAlgebra.hom_ext
    funext x
    obtain ⟨s, p, q⟩ := x
    by_cases hpq : lev p = lev q
    · cases s <;> simp [evLv, kpWord, GlobalTheory.CompanionTheory.PairMult.evB, hpq, pA, kA]
    · cases s <;> simp [evLv, kpWord, GlobalTheory.CompanionTheory.PairMult.evB, hpq]
  rw [h]
  rfl

theorem isLevPairA_of_lRel {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
    {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h : GlobalTheory.CompanionTheory.PairMult.LRel lev F1 F2) : IsLevPairA lev F1 F2 :=
  fun a b c d h1 h2 => ⟨h.1 a b c d h1 h2, h.2.1 a b c d h1 h2, (h.2.2 a b c d h1 h2).eq⟩

theorem lRel_of_isLevPairA {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
    {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h : IsLevPairA lev F1 F2) : GlobalTheory.CompanionTheory.PairMult.LRel lev F1 F2 :=
  ⟨fun a b c d h1 h2 => (h a b c d h1 h2).1, fun a b c d h1 h2 => (h a b c d h1 h2).2.1,
    fun a b c d h1 h2 => (h a b c d h1 h2).2.2⟩

theorem invLev_kpWord {lev : Fin n → ℕ} {b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hb : InvLv lev b) :
    GlobalTheory.CompanionTheory.PairMult.InvLev lev (kpWord b) := by
  intro W _ _ X1 X2 hL p q hpq
  have h := hb W X1 X2 (isLevPairA_of_lRel hL) p q hpq
  rw [evLv_eq] at h
  exact h

theorem exists_rho {M : ℕ} {d : Fin M → ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) {lev : Fin n → ℕ}
    (he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ)) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hL : GlobalTheory.CompanionTheory.PairMult.LRel lev X1 X2) :
    ∃ ρ : UD d →ₐ[ℂ] Module.End ℂ W, ∀ i p q, ρ (eb d i p q) = X1 (e ⟨i, p⟩) (e ⟨i, q⟩) := by
  have hl : ∀ i (p q : Fin (d i)), lev (e ⟨i, p⟩) = lev (e ⟨i, q⟩) := fun i p q => by rw [he, he]
  have hG : ∀ i, GlRel (fun p q : Fin (d i) => X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) := fun i a c f g => by
    have := hL.1 (e ⟨i, a⟩) (e ⟨i, c⟩) (e ⟨i, f⟩) (e ⟨i, g⟩) (hl _ _ _) (hl _ _ _)
    simpa only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and] using this
  have hC : ∀ i k, i ≠ k → ∀ (p q : Fin (d i)) (r v : Fin (d k)),
      Commute (X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) (X1 (e ⟨k, r⟩) (e ⟨k, v⟩)) := fun i k hik p q r v => by
    have := hL.1 (e ⟨i, p⟩) (e ⟨i, q⟩) (e ⟨k, r⟩) (e ⟨k, v⟩) (hl _ _ _) (hl _ _ _)
    have n1 : e ⟨i, q⟩ ≠ e ⟨k, r⟩ := fun h => hik (congrArg Sigma.fst (e.injective h))
    have n2 : e ⟨k, v⟩ ≠ e ⟨i, p⟩ := fun h => hik (congrArg Sigma.fst (e.injective h)).symm
    rw [if_neg n1, if_neg n2, sub_zero] at this
    exact sub_eq_zero.1 this
  refine ⟨lift ℂ (DirectSum.toLieAlgebra _
    (fun i => glHom (fun p q : Fin (d i) => X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) (hG i))
    (fun i k hik Z Z' => glHom_comm _ _ (hC i k hik) Z Z')), fun i p q => ?_⟩
  simp only [eb, eu, GlobalTheory.CompanionTheory.PairMult.CenScal.mi_ι, lift_ι_apply]
  refine (GlobalTheory.EnvCentre.toLieAlgebra_of (fun i => GlobalTheory.CompanionTheory.PairMult.CenScal.Gl (d i)) _ _ i _).trans ?_
  exact glHom_single _ (hG i) p q

def capLetter (lev : Fin n → ℕ) (p : ℕ × ℂ) : UD (bd lev) :=
  if h : p.1 < numLev lev then
    mi (bd lev) ⟨p.1, h⟩ (qdet (eu (bd lev ⟨p.1, h⟩)) (p.2 + ((bd lev ⟨p.1, h⟩ : ℂ) - 1) / 2))
  else 1

def capWord (lev : Fin n → ℕ) : FreeAlgebra ℂ (ℕ × ℂ) →ₐ[ℂ] UD (bd lev) := FreeAlgebra.lift ℂ (capLetter lev)

theorem rho_capWord {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W)
    (ρ : UD (bd lev) →ₐ[ℂ] Module.End ℂ W)
    (hρ : ∀ i p q, ρ (eb (bd lev) i p q) = F (blkE lev i p) (blkE lev i q)) (z : FreeAlgebra ℂ (ℕ × ℂ)) :
    ρ (capWord lev z) = evCap lev F z := by
  have h : ρ.comp (capWord lev) = evCap lev F := by
    apply FreeAlgebra.hom_ext
    funext x
    obtain ⟨j, u⟩ := x
    simp only [Function.comp_apply, AlgHom.comp_apply, capWord, evCap, FreeAlgebra.lift_ι_apply, capLetter]
    by_cases hj : j < numLev lev
    · rw [dif_pos hj]
      simp only [capS]
      rw [qminor_reindex _ _ (blkE_injective lev j), ← AlgHom.comp_apply, qdet_map]
      congr 1
      funext p q
      exact hρ ⟨j, hj⟩ p q
    · rw [dif_neg hj, map_one]
      have hc : (blk lev j).card = 0 := by
        refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun a _ ha => hj ?_)
        rw [← ha]
        exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
      exact (qminor_of_size_zero hc _ _ _).symm
  rw [← h]
  rfl

theorem mem_range_capWord (lev : Fin n → ℕ) {y : UD (bd lev)}
    (hy : y ∈ Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi (bd lev) i (qdet (eu (bd lev i)) u))) :
    ∃ z, capWord lev z = y := by
  have hle : Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi (bd lev) i (qdet (eu (bd lev i)) u)) ≤
      (capWord lev).range := by
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.1 hx
    refine ⟨FreeAlgebra.ι ℂ ((i : ℕ), u - ((bd lev i : ℂ) - 1) / 2), ?_⟩
    change capWord lev (FreeAlgebra.ι ℂ _) = _
    simp only [capWord, FreeAlgebra.lift_ι_apply, capLetter]
    rw [dif_pos i.2]
    simp
  obtain ⟨z, hz⟩ := hle hy
  exact ⟨z, hz⟩

theorem commutant_block_capelli_words : LeviCommutantWordReduction := by
  intro n lev _ b hb ν hν
  let e := blkEquiv lev
  have he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ) := fun i p => lev_blkE lev i p
  let τ : Fin n → ℂ := fun a => (ν a : ℂ)
  have hτ : ∀ a c, lev a = lev c → τ a = τ c := fun a c h => by simp only [τ, hν a c h]
  have hb' := invLev_kpWord hb
  have hl : ∀ i (p q : Fin (bd lev i)), lev (e ⟨i, p⟩) = lev (e ⟨i, q⟩) := fun i p q => by rw [he, he]
  set y := GlobalTheory.CompanionTheory.PairMult.evB lev (leftMulLetter (xl e)) (negRightMulLetterShift (xl e) τ) (kpWord b) 1 with hy
  have hcen : y ∈ Subalgebra.center ℂ (UD (bd lev)) := by
    rw [Subalgebra.mem_center_iff]
    intro g
    have hg : g ∈ Subalgebra.centralizer ℂ {y} := mem_of_eb (bd lev) _ (fun i r v => by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      have := central_letters (levRel_xl e he) hτ hb' _ _ (hl i r v)
      rw [xl_apply, xs_same] at this
      exact this.symm) g
    rw [Subalgebra.mem_centralizer_iff] at hg
    exact (hg _ rfl).symm
  obtain ⟨z, hz⟩ := mem_range_capWord lev (center_UD_le (bd lev) hcen)
  refine ⟨z, fun H _ _ F1 F2 hL h hh => ?_⟩
  have hL' := lRel_of_isLevPairA hL
  obtain ⟨ρ, hρ⟩ := exists_rho e he hL'
  have hρx : ∀ p q, lev p = lev q → ρ (xl e p q) = F1 p q := by
    intro p q hpq
    obtain ⟨⟨i, p⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨k, q⟩, rfl⟩ := e.surjective q
    rw [he, he] at hpq
    obtain rfl : i = k := Fin.ext hpq
    rw [xl_apply, xs_same, hρ]
  have hcomm : ∀ p q, lev p = lev q → ∀ u, Commute (ρ u) (F2 p q) := fun p q hpq u => by
    have hu : u ∈ (Subalgebra.centralizer ℂ {F2 p q}).comap ρ := mem_of_eb (bd lev) _ (fun i r v => by
      rw [Subalgebra.mem_comap, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      rw [hρ]
      exact (hL'.2.2 _ _ _ _ (hl _ _ _) hpq).eq.symm) u
    rw [Subalgebra.mem_comap, Subalgebra.mem_centralizer_iff] at hu
    exact (hu _ rfl).symm
  have e1 := evB_intertwine (x := xl e) (τ := τ) ρ F1 F2 h hρx hcomm hh (kpWord b) 1
  rw [map_one, Module.End.one_apply] at e1
  rw [evLv_eq, e1, ← hy, ← hz, rho_capWord F1 ρ hρ]

end GlobalTheory.CompanionTheory.BlockCapelliWords
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmallerStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_finite_of_smaller : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ctFin | exact GlobalTheory.CompanionTheory.CTFin.ctFin | (intros; apply GlobalTheory.CompanionTheory.CTFin.ctFin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPartialFourierMeanStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_partial_fourier_mean : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : hermA D n → ℂ), Continuous Φ → IsPer Φ → Continuous (pm hn m ψ b₀ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.continuous_pm | exact GlobalTheory.CompanionTheory.PcFc.continuous_pm | (intros; apply GlobalTheory.CompanionTheory.PcFc.continuous_pm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovarianceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_covariance : PositivityTheory.GramSchwartzFunctions.EC.Covar := by
  first | exact @GlobalTheory.CompanionTheory.EisCovar.covar | exact GlobalTheory.CompanionTheory.EisCovar.covar | (intros; apply GlobalTheory.CompanionTheory.EisCovar.covar <;> assumption)
end


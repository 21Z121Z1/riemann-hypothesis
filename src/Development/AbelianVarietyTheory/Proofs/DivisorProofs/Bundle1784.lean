import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix nonZeroDivisors

noncomputable section
namespace GlobalTheory.FinSupp

theorem exists_den_of_trace_int (F : Type) [Field F] [NumberField F] :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ t : F, (∀ a : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((a : F) * t) = m) →
      IsIntegral ℤ ((D : F) * t) := by
  classical
  obtain ⟨c, hc, hfr⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, fun t ht => ?_⟩
  · rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · have hmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        first | exact one_ne_zero | simp | exact FractionalIdeal.one_ne_zero
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨m, hm⟩ := ht b
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, hm]
      simp
    obtain ⟨y, hy⟩ := hfr t hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) * t = ((e * y : 𝓞 F) : F) := by
      have h1 : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) = ((e : F) * (c : F)) := by
        have := congrArg (fun z : 𝓞 F => (z : F)) he
        simp only [map_mul, map_natCast] at this
        rw [← this]
      rw [h1, mul_assoc]
      have h2 : (y : F) = (c : F) * t := by
        rw [show (y : F) = algebraMap (𝓞 F) F y from rfl, hy, Algebra.smul_def]
      push_cast
      first | rw [h2] | rw [← h2] | exact congrArg (_ * ·) h2.symm | simp [h2]
    rw [this]
    exact (e * y).isIntegral_coe

theorem trace_int_of_finPart {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (s : F)
    (hs : ψ (finPart F (algebraMap F (AF F) s)) = 1) : ∃ m : ℤ, Algebra.trace ℚ F s = m := by
  set x : AF F := algebraMap F (AF F) s with hx
  set z : AF F := x - finPart F x with hzdef
  have hz : At (evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := by
      apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      rw [map_zero]
      exact hu
    show u * z = 0
    refine Prod.ext ?_ ?_
    · change u.1 * (x.1 - (0 : Ainf F)) = 0
      rw [hu1, zero_mul]
    · change u.2 * (x.2 - x.2) = 0
      rw [sub_self, mul_zero]
  have hψz : ψ z = 1 := by
    have h := hψ.2.1 s
    rw [← hx, show x = z + finPart F x by rw [hzdef, sub_add_cancel], AddChar.map_add_eq_mul, hs, mul_one] at h
    exact h
  have hev : evI F z = mixedEmbedding F s := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x.1 - 0) = _
    rw [sub_zero, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rfl
  have h := hψ.2.2 z hz
  rw [hψz, hev, GlobalTheory.LatVacArith.trace_mixedEmbedding] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h.symm
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : (((Algebra.trace ℚ F s : ℚ) : ℝ) : ℂ) = -(n : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -hn
  refine ⟨-n, ?_⟩
  push_cast
  exact_mod_cast hq

end GlobalTheory.FinSupp

namespace GlobalTheory.FinSupp.DenStd

theorem exists_den : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  intro F _ _
  obtain ⟨D, hD, hint⟩ := GlobalTheory.FinSupp.exists_den_of_trace_int F
  exact ⟨D, hD, fun ψ hψ t ht => hint t fun a => GlobalTheory.FinSupp.trace_int_of_finPart hψ _ (ht a)⟩

end GlobalTheory.FinSupp.DenStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCoreUnitaryGroupEmbedding
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem adelicConjTranspose_adelicMatrixOfTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k
  simp [cT, adMat, sigR, inclR]

theorem adelicMatrixOfTensor_gram_conjTranspose_mul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := by
  rw [adelicConjTranspose_adelicMatrixOfTensor]
  simp only [adMat, Matrix.map_mul]

theorem ringHomConjTranspose_mul_rev {A : Type} [CommRing A] (s : A →+* A) {a b c : ℕ} (X : Matrix (Fin a) (Fin b) A)
    (Y : Matrix (Fin b) (Fin c) A) : cT s (X * Y) = cT s Y * cT s X := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem core_embeds : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ →* GAd σ J, Continuous e ∧ (∀ g, e g ∈ fixG σ J C ∧ e g ∈ fixG σ J D ∧ (matHom _ σ J (e g)).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1) ∧ ∀ g ∈ ratPts σ J₀, e g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hU : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * adMat F J₀ * (matHom _ σ J₀ g).1 = adMat F J₀ :=
    fun g => g.2
  have hZ' : ∀ g : GAd σ J₀, cT (sigR (AF F) σ) (adMat F Z * (matHom _ σ J₀ g).1) * adMat F J *
      (adMat F Z * (matHom _ σ J₀ g).1) = adMat F J₀ := by
    intro g
    rw [ringHomConjTranspose_mul_rev]
    have h := adelicMatrixOfTensor_gram_conjTranspose_mul (F := F) σ J Z Z
    rw [hF.zz] at h
    calc _ = cT (sigR (AF F) σ) (matHom _ σ J₀ g).1 * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J * adMat F Z) *
          (matHom _ σ J₀ g).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, hU]
  have img : ∀ g : GAd σ J₀, ∃ h : GAd σ J, (matHom _ σ J h).1 * adMat F C = adMat F C ∧
      (matHom _ σ J h).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g).1 ∧ (matHom _ σ J h).1 * adMat F D = adMat F D :=
    fun g => GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D) (adMat F Z * (matHom _ σ J₀ g).1)
      (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cc]; simp [adMat]) (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.dd]; simp [adMat])
      (by rw [adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cd]; simp [adMat])
      (by rw [← Matrix.mul_assoc, adelicMatrixOfTensor_gram_conjTranspose_mul, hF.cz]; simp [adMat])
      (by rw [← Matrix.mul_assoc, adelicMatrixOfTensor_gram_conjTranspose_mul, hF.dz]; simp [adMat]) (hZ' g)
  choose f hC hZ hD using img
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    apply GlobalTheory.SphEis.eq_of_frame_cols F E σ n J j m C D Z J₀ hF
    · rw [hC, map_mul, Units.val_mul, Matrix.mul_assoc, hC, hC]
    · rw [hZ]
      symm
      calc (matHom _ σ J (f a * f b)).1 * adMat F Z
          = (matHom _ σ J (f a)).1 * ((matHom _ σ J (f b)).1 * adMat F Z) := by
            rw [map_mul, Units.val_mul, Matrix.mul_assoc]
        _ = ((matHom _ σ J (f a)).1 * adMat F Z) * (matHom _ σ J₀ b).1 := by rw [hZ, Matrix.mul_assoc]
        _ = _ := by rw [hZ, map_mul, Units.val_mul, Matrix.mul_assoc]
    · rw [hD, map_mul, Units.val_mul, Matrix.mul_assoc, hD, hD]
  refine ⟨MonoidHom.mk' f hmul, ?_, fun g => ⟨hC g, hD g, hZ g⟩, ?_⟩
  · haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    apply GlobalTheory.T.continuous_unitaryAdelic_of_frameColumns F E σ n J j m C D Z J₀ hF (GAd σ J₀) f
    · simp only [hC]; exact continuous_const
    · simp only [hZ]
      exact continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J₀).continuous)
    · simp only [hD]; exact continuous_const
  · intro g hg
    change (matHom _ σ J₀ g) ∈ HFin (AF F) σ J₀ at hg
    rw [HFin, Subgroup.mem_map] at hg
    obtain ⟨γ, -, hγ⟩ := hg
    have hg' : (matHom _ σ J₀ g).1 = adMat F γ.1 := by
      rw [← hγ]; rfl
    apply GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF (f g) C D (Z * γ.1) (hC g)
    · rw [hZ, hg', adMat, adMat, adMat, Matrix.map_mul]
    · exact hD g

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicHaarIntegralPointsOne
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.FinAdeleHaarNorm

open scoped RestrictedProduct Topology

theorem isCompact_integral (F : Type) [Field F] [NumberField F] :
    IsCompact {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem exists_addHaar_integral_eq_one : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)],
    ∃ μf : Measure (κ → Af F), μf.IsAddHaarMeasure ∧ μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _ κ _ _ _
  set U : Set (κ → Af F) := {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F}
  have hU : U = Set.pi Set.univ (fun _ : κ =>
      {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F}) := by
    ext y; simp [U]
  have hc : IsCompact U := hU ▸ isCompact_univ_pi (fun _ => isCompact_integral F)
  have ho : IsOpen U := hU ▸ isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_integral F)
  have h0 : (0 : κ → Af F) ∈ U := fun i v => by simp
  let K₀ : TopologicalSpace.PositiveCompacts (κ → Af F) :=
    ⟨⟨U, hc⟩, ⟨0, ho.interior_eq.symm ▸ h0⟩⟩
  exact ⟨Measure.addHaarMeasure K₀, inferInstance, Measure.addHaarMeasure_self⟩

end GlobalTheory.FinAdeleHaarNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotFormula

theorem toFinE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = GlobalTheory.CuspRep.conjFin (D.host.conj : D.host.E ≃+* D.host.E) (toFinE D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x a =>
    change GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] D.host.conj x) =
      GlobalTheory.CuspRep.conjFin _ (GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul,
      GlobalTheory.DefU.ClassFin.conjFin_adMap _ (fun q => D.host.conj.commutes q), GlobalTheory.CuspRep.conjFin_algebraMap]
    rfl

def toAfE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* TensorProduct D.host.F (Af D.host.F) D.host.E :=
  (toFinE D).trans (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm

theorem toAfE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = sigR (Af D.host.F) D.sp.cm.sig (toAfE D y) := by
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x)]
  simp only [toAfE, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact toFinE_sgA D y

theorem exists_isFinPt_of_gram_one : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  intro D WW hG n h hr
  subst hr
  let x' : GL (Fin WW.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := Formalism.UG.bc (toAfE D).toRingHom h.1
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * h.1 = 1 := by
    have h2 := h.2
    change Formalism.UG.cT _ (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hx' : x' ∈ HR (Af D.host.F) D.sp.cm.sig WW.gram := by
    show Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) *
      JR (Af D.host.F) WW.gram * (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) = JR (Af D.host.F) WW.gram
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (toAfE D).toRingHom (Formalism.MainNotions.StandardLatticesGL3.sgA D) _ (toAfE_sgA D) _ hh
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue WW 1 x' (one_mem _) hx'
  refine ⟨k, k1, rfl, fun i j => ?_⟩
  rw [k2]
  exact (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

end GlobalTheory.BotFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusTranslate

open GlobalTheory.AdLat GlobalTheory.UnRep

theorem hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z ∈ Formalism.L2.Herm.hatL L ↔
      (fun i => (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  refine ⟨GlobalTheory.PrincInLevel.swap_symm_mem_hat L z, fun h => ?_⟩
  have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ h
  simpa using this

set_option maxHeartbeats 2000000 in

theorem exists_move_colLat : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    ∃ x : GA D V, x ∈ GfC V ∧ ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (Formalism.IndefR.Lev.finE V x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V fr Λ hfr hΛ
  have hU := GlobalTheory.T.selfDual_comap_orthonormalFrame_unimodular D V fr Λ hfr hΛ
  have hT : (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).TrivAt 1 :=
    ⟨0, Nat.coprime_zero_left 1 |>.2 rfl, by simp, by simp⟩
  have hgen : ∃ g : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g.1 ∧
      ∀ z, z ∈ GlobalTheory.AdLat.hat D.host.F ((Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔
      (g⁻¹).1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) := by
    obtain ⟨g, hgU, hgL, -⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank 1 _
      one_pos hU hT
    have hstd := GlobalTheory.UnRep.StdInhab.main D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank
    have hfg := hstd.2.2.1
    have hsp := hstd.2.2.2.1
    have hL := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield D.host.E) D.host.E V.rank
      (Formalism.L2.Pj.stdLat D.host.E V.rank) g hfg hsp
    obtain ⟨Λ'', hL''⟩ := hL
    have h1 := hL''.1
    have h4 := hL''.2.2.2
    have e : Λ'' = Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :=
      SetLike.coe_injective (h1.trans hgL.symm)
    refine ⟨g, by
      have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [hc]; exact hgU, fun z => ?_⟩
    rw [← e, ← SetLike.mem_coe, h4]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · intro hz
      exact ⟨_, hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  obtain ⟨g, hgU, hg'⟩ := hgen
  have hfm1 : GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 * GlobalTheory.UnRep.fm D.host.F fr.1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.inv_mul, GlobalTheory.UnRep.FullReps.fm_one]
  have hfm2 : GlobalTheory.UnRep.fm D.host.F fr.1 * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one]
  obtain ⟨U, hU1, hU2⟩ : ∃ U : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E),
      U.1 = GlobalTheory.UnRep.fm D.host.F fr.1 ∧ (U⁻¹).1 = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 :=
    ⟨⟨GlobalTheory.UnRep.fm D.host.F fr.1, GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1, hfm2, hfm1⟩, rfl, rfl⟩
  have hX := GlobalTheory.T.isUnitaryAdelicMatrix_conj_orthonormalFrame D V fr g.1 hfr hgU
  rw [← hU1, ← hU2, ← Units.val_mul, ← Units.val_mul] at hX
  obtain ⟨X, hXe⟩ : ∃ X : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), X = U * g * U⁻¹ := ⟨_, rfl⟩
  rw [← hXe] at hX
  have hlift := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.2.1 X hX
  obtain ⟨x, hx, hxX⟩ := hlift
  have key : ∀ w : Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E,
      w ∈ GlobalTheory.AdLat.hat D.host.F (colLat fr : Set (Fin V.rank → D.host.E)) ↔
        X.1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    intro w
    have ew : GlobalTheory.UnRep.fm D.host.F fr.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one, Matrix.one_mulVec]
    have h1 := GlobalTheory.T.adelicCompletion_comap_rational_matrix D.host.F D.host.E V.rank fr (colLat fr) (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)
    rw [ew, GlobalTheory.T.columnLattice_comap_eq_standardLattice] at h1
    have h2 := GlobalTheory.T.adelicCompletion_comap_rational_matrix D.host.F D.host.E V.rank fr Λ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w))
    have hgg : (g⁻¹).1 *ᵥ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)) = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hg', hgg] at h2
    rw [h1, hXe, Units.val_mul, Units.val_mul, hU1, hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨x, hx, fun v => ?_⟩
  have hfin : (fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
      (((Formalism.IndefR.Lev.finE V x).1 *ᵥ v) i)) =
      X.1 *ᵥ fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v i) := by
    have hfe : Formalism.IndefR.Lev.finE V x = Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) X := by rw [← hxX]; rfl
    rw [hfe]
    funext i
    rw [AlgEquiv.symm_apply_eq]
    have hv : ⇑(Formalism.IndefR.Lev.swapAE D) ∘ (fun j =>
        (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) = v :=
      funext fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).apply_symm_apply (v j)
    have hm := RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) X.1
      (fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) i
    rw [hv] at hm
    exact hm.symm
  rw [hatL_iff, hatL_iff, hfin]
  exact key _

end GlobalTheory.GenusTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetCosetRepsBoundedHalfPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_cosetReps_bounded_half_points : ∀ {D : D7} {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ), IsIdemSum e P → ∃ R : Finset (Mx D b a), (∀ r ∈ R, IsHalf e r ∧ IsSmall P β' β (-(n : ℤ)) r) ∧ (∀ t, IsHalf e t → IsSmall P β' β (-(n : ℤ)) t → ∃ r ∈ R, IsSmall P β' β n (t - r)) ∧ ∀ r ∈ R, ∀ r' ∈ R, IsSmall P β' β n (r - r') → r = r' := by
  first | exact @GlobalTheory.FunObj.exists_finset_cosetReps | exact GlobalTheory.FunObj.exists_finset_cosetReps | (intros; apply GlobalTheory.FunObj.exists_finset_cosetReps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalMatrixApproxTwoAdelicModuliStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)), 𝔫 ≠ ⊥ → ∀ (a d : ℕ) (M : Matrix (Fin d) (Fin a) (AE D)) (m : ℕ), 0 < m → ∃ z : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, ∃ y ∈ IhE D ⊤, (z.map (inc D) - M) i l = (m : AE D) * y) ∧ ∀ i l, (M - z.map (inc D)) i l ∈ hatId D 𝔫 := by
  first | exact @GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli | exact GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli | (intros; apply GlobalTheory.BotPairSmall.CongApprox.approx_two_moduli <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTowerStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    ∃ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν := by
  first | exact @GlobalTheory.TowerFD.exists_fd_any | exact GlobalTheory.TowerFD.exists_fd_any | (intros; apply GlobalTheory.TowerFD.exists_fd_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslateStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_matrix_approx_congruent_one_translate : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  first | exact @GlobalTheory.CongApprox.exists_closeTo_congOne | exact GlobalTheory.CongApprox.exists_closeTo_congOne | (intros; apply GlobalTheory.CongApprox.exists_closeTo_congOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCmStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_conj_eq_one_unramified_cm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  first | exact @GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood | exact GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood | (intros; apply GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisCompletionInSpanLieLatticeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_completion_in_span_lieLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib B.pol) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (n : SABMap G.t B.t (spMap ρV)), ∃ vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G), IsLieBasis vV ∧ ∀ k, ∃ (M : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A), IsLieComb M F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ ∧ (fun l => iK (M l)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) l => iK (v l)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  first | exact @GlobalTheory.LieSpan.exists_isLieBasis_span | exact GlobalTheory.LieSpan.exists_isLieBasis_span | (intros; apply GlobalTheory.LieSpan.exists_isLieBasis_span <;> assumption)
end


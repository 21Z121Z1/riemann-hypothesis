import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralGeneratorSplitPlaceCmExtension
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitGen

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_integral_gen_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (a : 𝓞 E) (b c : 𝓞 F), (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 ∧
      σ (a : E) = -algebraMap F E (b : F) - a ∧ c ∈ v.asIdeal ∧ b ∉ v.asIdeal := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨P, Q, hPQ, hPv, hQv⟩ := hv
  have hσ := hB.cm
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : IsGalois ℚ E := hB.galois
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  have hPo : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨P.isPrime, ⟨hPv.symm⟩⟩
  have hQo : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨Q.isPrime, ⟨hQv.symm⟩⟩
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F E (𝓞 E) hPo hQo
  have hgQ : ∀ x : 𝓞 E, x ∈ Q.asIdeal → galRestrict (𝓞 F) F E (𝓞 E) g x ∈ P.asIdeal := by
    intro x hx
    rw [← hg] at hx
    exact hx
  have hgE : ∀ x : 𝓞 E, ((galRestrict (𝓞 F) F E (𝓞 E) g x : 𝓞 E) : E) = g (x : E) :=
    fun x => algebraMap_galRestrict_apply (𝓞 F) g x

  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal hne
  obtain ⟨a, haP, j, hjQ, haj⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ P.asIdeal ⊔ Q.asIdeal)
  have ha1Q : a - 1 ∈ Q.asIdeal := by
    have : a - 1 = -j := by rw [← haj]; ring
    rw [this]; exact neg_mem hjQ
  have hga1 : galRestrict (𝓞 F) F E (𝓞 E) g a - 1 ∈ P.asIdeal := by
    have := hgQ _ ha1Q
    rwa [map_sub, map_one] at this
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hga : g (a : E) ≠ a := by
    intro h
    apply h1P
    have e : galRestrict (𝓞 F) F E (𝓞 E) g a = a := by
      apply RingOfIntegers.ext
      rw [hgE]; exact h
    have := P.asIdeal.sub_mem haP hga1
    rw [e] at this
    simpa using this
  have hnot : (a : E) ∉ (algebraMap F E).range := by
    rintro ⟨x, hx⟩
    apply hga
    rw [← hx, AlgEquiv.commutes]
  have hi : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hmap : minpoly F (a : E) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hi
  have hdeg : (minpoly F (a : E)).natDegree = (minpoly (𝓞 F) a).natDegree := by
    rw [hmap, (minpoly.monic hi).natDegree_map]
  have hge : 2 ≤ (minpoly (𝓞 F) a).natDegree := by
    rw [← hdeg]
    exact (minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)).2 hnot
  have hle : (minpoly F (a : E)).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le (a : E)
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hi⟩ : IsMonicOfDegree (minpoly (𝓞 F) a) 2)
  have hq0 : a ^ 2 + algebraMap _ _ b * a + algebraMap _ _ c = 0 := by
    have := minpoly.aeval (𝓞 F) a
    rw [hbc] at this
    simpa using this
  have hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 := by
    have := congrArg (algebraMap (𝓞 E) E) hq0
    simp only [map_add, map_mul, map_pow, map_zero] at this
    exact this
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro x hx
    exact hnot ⟨x, by rw [Algebra.algebraMap_eq_smul_one, hx]⟩
  let Bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hBs : ⇑Bs = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hσa : σ (a : E) ≠ a := by
    intro hfix
    obtain ⟨x, hx⟩ := GlobalTheory.InertUnitNorm.exists_ne_of_isCMExt σ hσ
    apply hx
    have : σ.toLinearMap = LinearMap.id := by
      refine Bs.ext fun i => ?_
      fin_cases i
      · simp [hBs]
      · simp [hBs, hfix]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hqσ : σ (a : E) ^ 2 + algebraMap F E (b : F) * σ a + algebraMap F E (c : F) = 0 := by
    have := congrArg σ hq
    simpa only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero] using this
  have hconj : σ (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (σ (a : E) - a) * (σ a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqσ - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hσa
    · linear_combination h
  have hqg : g (a : E) ^ 2 + algebraMap F E (b : F) * g a + algebraMap F E (c : F) = 0 := by
    have := congrArg g hq
    simpa only [map_add, map_mul, map_pow, AlgEquiv.commutes, map_zero] using this
  have hgconj : g (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (g (a : E) - a) * (g a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqg - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hga
    · linear_combination h
  have hgO : galRestrict (𝓞 F) F E (𝓞 E) g a = -algebraMap (𝓞 F) (𝓞 E) b - a := by
    apply RingOfIntegers.ext
    rw [hgE, hgconj]
    simp only [map_sub, map_neg]
    rfl
  refine ⟨a, b, c, hq, hconj, ?_, ?_⟩
  ·
    rw [← hPv, Ideal.mem_comap]
    have e : algebraMap (𝓞 F) (𝓞 E) c = a * (-algebraMap (𝓞 F) (𝓞 E) b - a) := by
      linear_combination hq0
    rw [e]
    exact P.asIdeal.mul_mem_right _ haP
  · intro hb
    rw [← hPv, Ideal.mem_comap] at hb
    apply h1P
    rw [hgO] at hga1
    have e : (1 : 𝓞 E) = -(-algebraMap (𝓞 F) (𝓞 E) b - a - 1) - algebraMap (𝓞 F) (𝓞 E) b - a := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.sub_mem (neg_mem hga1) hb) haP

end GlobalTheory.SplitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralSiegelParabolicOfConjugateIdempote
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitConjPar

section FinTwoTypeFamily
variable {R : Type} [CommRing R] {d : ℕ}

def blk2 (d : ℕ) (a b : R) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  Matrix.fromBlocks (a • 1) (b • 1) (b • 1) (a • 1)

theorem symmetricScalarBlockMatrix_mul (a b a' b' : R) : blk2 d a b * blk2 d a' b' = blk2 d (a * a' + b * b') (a * b' + b * a') := by
  simp only [blk2, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

theorem symmetricScalarBlockMatrix_one_zero : blk2 d (1 : R) 0 = 1 := by
  simp [blk2, Matrix.fromBlocks_one]

theorem symmetricScalarBlockMatrix_transpose (a b : R) : (blk2 d a b)ᵀ = blk2 d a b := by
  simp [blk2, Matrix.fromBlocks_transpose, Matrix.transpose_smul]

theorem symmetricScalarBlockMatrix_map (c : R → R) (h0 : c 0 = 0) (a b : R) : (blk2 d a b).map c = blk2 d (c a) (c b) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [blk2, Matrix.one_apply, h, h0]

theorem symmetricScalarBlockMatrix_mul_gram_mul (J : Matrix (Fin d) (Fin d) R) (a b a' b' : R) :
    blk2 d a b * Matrix.fromBlocks J 0 0 (-J) * blk2 d a' b' =
      Matrix.fromBlocks ((a * a' - b * b') • J) ((a * b' - b * a') • J) ((b * a' - a * b') • J) ((b * b' - a * a') • J) := by
  simp only [blk2, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_neg, Matrix.neg_mul, Matrix.mul_neg, smul_smul]
  congr 1 <;> module

theorem symmetricScalarBlockMatrix_mul_diagonalColumns (a b : R) :
    blk2 d a b * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) : Matrix (Fin d ⊕ Fin d) (Fin d) R) =
      (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) : Matrix (Fin d ⊕ Fin d) (Fin d) R) * ((a + b) • (1 : Matrix (Fin d) (Fin d) R)) := by
  simp only [blk2, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, add_comm b a, ← add_smul]

theorem symmetricScalarBlockMatrix_mul_antidiagonalColumns (a b : R) :
    blk2 d a b * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-(1 : Matrix (Fin d) (Fin d) R)) : Matrix (Fin d ⊕ Fin d) (Fin d) R) =
      (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-(1 : Matrix (Fin d) (Fin d) R)) : Matrix (Fin d ⊕ Fin d) (Fin d) R) * ((a - b) • (1 : Matrix (Fin d) (Fin d) R)) := by
  simp only [blk2, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> module

theorem symmetricScalarBlockMatrix_sub_one (a b : R) : blk2 d a b - 1 = blk2 d (a - 1) b := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [blk2, Matrix.one_apply, h]

theorem symmetricScalarBlockMatrix_mulVec_inl (a b : R) (z : Fin d ⊕ Fin d → R) (i : Fin d) :
    (blk2 d a b *ᵥ z) (Sum.inl i) = a * z (Sum.inl i) + b * z (Sum.inr i) := by
  simp [blk2, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec]

theorem symmetricScalarBlockMatrix_mulVec_inr (a b : R) (z : Fin d ⊕ Fin d → R) (i : Fin d) :
    (blk2 d a b *ᵥ z) (Sum.inr i) = b * z (Sum.inl i) + a * z (Sum.inr i) := by
  simp [blk2, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec]

end FinTwoTypeFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_half_mem (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟2 : AF F) ∈ v.adicCompletionIntegers F := by
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2 : v.adicCompletionIntegers F) : Fv F v) = 2 := by
      rw [map_ofNat]; rfl
    have hn := (GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff v 2).not.2 h2
    rw [GlobalTheory.InertUnitNorm.mem_maximalIdeal_iff_valued_lt_one, e] at hn
    have hle : Valued.v (2 : Fv F v) ≤ 1 := by
      rw [← e]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2).2
    exact le_antisymm hle (not_lt.1 hn)
  have hx : (2 : Fv F v) * evFin F v (⅟2 : AF F) = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have := congrArg Valued.v hx
  rw [map_mul, hv2, one_mul, map_one] at this
  exact this.le

theorem symmetricScalarBlockMatrix_mulVec_mem_doubledLattice {d : ℕ} {W : Spc F E d} {v : Pl F} {a b : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a)
    (hb : GlobalTheory.SplitConj.Mult W v b) (z : Fin d ⊕ Fin d → AE F E) (hz : z ∈ GlobalTheory.InertDbl.latAtD W v) :
    blk2 d a b *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  constructor
  · simp only [symmetricScalarBlockMatrix_mulVec_inl]
    exact add_mem (ha _ hz.1) (hb _ hz.2)
  · simp only [symmetricScalarBlockMatrix_mulVec_inr]
    exact add_mem (hb _ hz.1) (ha _ hz.2)

theorem mult_neg {d : ℕ} {W : Spc F E d} {v : Pl F} {a : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a) :
    GlobalTheory.SplitConj.Mult W v (-a) := fun z hz => by
  have : (fun i => -a * z i) = -(fun i => a * z i) := by ext i; simp
  rw [this]; exact neg_mem (ha z hz)

theorem mult_sub {d : ℕ} {W : Spc F E d} {v : Pl F} {a b : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a)
    (hb : GlobalTheory.SplitConj.Mult W v b) : GlobalTheory.SplitConj.Mult W v (a - b) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.SplitConj.mult_add ha (mult_neg hb)

theorem mult_one {d : ℕ} (W : Spc F E d) (v : Pl F) : GlobalTheory.SplitConj.Mult W v 1 := fun z hz => by
  simpa using hz

theorem exists_par : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ Eid : AE F E, Eid * Eid = Eid → Eid + cA σ Eid = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    Eid * cA σ Eid = 0 →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => Eid * z i) ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v,
      GlobalTheory.InertDbl.matD s * diagCols (Fin d) =
        diagCols (Fin d) * ((1 - (⅟2 : AF F) • Eid) • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      GlobalTheory.InertDbl.matD s * GlobalTheory.InertDbl.antiCols d =
        GlobalTheory.InertDbl.antiCols d * ((1 + cA σ Eid) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  intro F E _ _ _ _ _ σ B _ d W v h2 A hA hAe hAB hL
  set h : AE F E := algebraMap (AF F) (AE F E) (⅟2) with hh
  set e : AE F E := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he
  set A' : AE F E := cA σ A with hA'
  have h2h : 2 * h = 1 := by
    rw [hh, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one]
  have hee : e * e = e := by rw [he, ← map_mul, ← GlobalTheory.SplitConj.liftV_mul, one_mul]
  have hAe' : A * e = A := by rw [← hAe, mul_add, hA, hAB, add_zero]
  have hA'e : A' = e - A := by rw [← hAe]; ring
  have hA'A' : A' * A' = A' := by rw [hA'e]; linear_combination hee - 2 * hAe' + hA
  have ch : cA σ h = h := (cA σ).commutes _
  have ce : cA σ e = e := (cA σ).commutes _
  have cA' : cA σ A' = A := by rw [hA'e, map_sub, ce, ← hA', hA'e]; ring
  have hx : (1 - h * A) * (1 + A) = 1 := by linear_combination (-h) * hA - A * h2h
  have hy : (1 + A') * (1 - h * A') = 1 := by linear_combination (-h) * hA'A' - A' * h2h
  have cx : cA σ (1 - h * A) = 1 - h * A' := by rw [map_sub, map_one, map_mul, ch]
  have cy : cA σ (1 + A') = 1 + A := by rw [map_add, map_one, cA']
  have Mh : GlobalTheory.SplitConj.Mult W v h := GlobalTheory.SplitConj.mult_algebraMap W v _ (evFin_half_mem v h2)
  have Me : GlobalTheory.SplitConj.Mult W v e := GlobalTheory.SplitConj.mult_algebraMap W v _ (by
    rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _)
  have MA : GlobalTheory.SplitConj.Mult W v A := hL
  have MA' : GlobalTheory.SplitConj.Mult W v A' := hA'e ▸ mult_sub Me MA
  have Mx := mult_sub (mult_one W v) (GlobalTheory.SplitConj.mult_mul Mh MA)
  have Mx' := GlobalTheory.SplitConj.mult_add (mult_one W v) MA
  have My := GlobalTheory.SplitConj.mult_add (mult_one W v) MA'
  have My' := mult_sub (mult_one W v) (GlobalTheory.SplitConj.mult_mul Mh MA')
  have hu : ∀ u : AF F, evFin F v u = 0 →
      algebraMap (AF F) (AE F E) u * A = 0 ∧ algebraMap (AF F) (AE F E) u * A' = 0 := by
    intro u hu
    have h1 : algebraMap (AF F) (AE F E) u * e = 0 := by
      have := GlobalTheory.LatVac.at_liftV v 1 u hu
      rw [he, ← map_mul, ← smul_eq_mul, this, map_zero]
    have h3 : algebraMap (AF F) (AE F E) u * A = 0 := by
      rw [← hAe']; linear_combination A * h1
    exact ⟨h3, by rw [hA'e, mul_sub, h1, h3, sub_zero]⟩
  have hsm : (⅟2 : AF F) • A = h * A := Algebra.smul_def _ _
  rw [hsm]
  generalize hxe : 1 - h * A = x at *
  generalize hxe' : 1 + A = x' at *
  generalize hye : 1 + A' = y at *
  generalize hye' : 1 - h * A' = y' at *
  have i1 : h * (x + y) * (h * (x' + y')) + h * (x - y) * (h * (x' - y')) = 1 := by
    linear_combination 2 * h * h * hx + 2 * h * h * hy + (2 * h + 1) * h2h
  have i2 : h * (x + y) * (h * (x' - y')) + h * (x - y) * (h * (x' + y')) = 0 := by
    linear_combination 2 * h * h * hx - 2 * h * h * hy
  have i3 : h * (x' + y') * (h * (x + y)) + h * (x' - y') * (h * (x - y)) = 1 := by
    linear_combination i1
  have i4 : h * (x' + y') * (h * (x - y)) + h * (x' - y') * (h * (x + y)) = 0 := by
    linear_combination i2
  have ca : cA σ (h * (x + y)) = h * (x' + y') := by rw [map_mul, map_add, ch, cx, cy, add_comm]
  have cb : cA σ (h * (x - y)) = -(h * (x' - y')) := by rw [map_mul, map_sub, ch, cx, cy]; ring
  have hmem : (blk2 d (h * (x + y)) (h * (x - y)))ᵀ * dbl (incM F W.J) *
      (blk2 d (h * (x + y)) (h * (x - y))).map (cA σ) = dbl (incM F W.J) := by
    rw [symmetricScalarBlockMatrix_transpose, symmetricScalarBlockMatrix_map _ (map_zero _), ca, cb, dbl, symmetricScalarBlockMatrix_mul_gram_mul]
    have j1 : h * (x + y) * (h * (x' + y')) - h * (x - y) * -(h * (x' - y')) = 1 := by linear_combination i1
    have j2 : h * (x + y) * -(h * (x' - y')) - h * (x - y) * (h * (x' + y')) = 0 := by linear_combination -i2
    have j3 : h * (x - y) * (h * (x' + y')) - h * (x + y) * -(h * (x' - y')) = 0 := by linear_combination i2
    have j4 : h * (x - y) * -(h * (x' - y')) - h * (x + y) * (h * (x' + y')) = -1 := by linear_combination -i1
    rw [j1, j2, j3, j4, one_smul, zero_smul, neg_smul, one_smul]
  let s : GlobalTheory.InertDbl.UD σ W :=
    ⟨⟨blk2 d (h * (x + y)) (h * (x - y)), blk2 d (h * (x' + y')) (h * (x' - y')),
      by rw [symmetricScalarBlockMatrix_mul, i1, i2, symmetricScalarBlockMatrix_one_zero], by rw [symmetricScalarBlockMatrix_mul, i3, i4, symmetricScalarBlockMatrix_one_zero]⟩, hmem⟩
  have hs : GlobalTheory.InertDbl.matD s = blk2 d (h * (x + y)) (h * (x - y)) := rfl
  have hs' : GlobalTheory.InertDbl.matD s⁻¹ = blk2 d (h * (x' + y')) (h * (x' - y')) := rfl
  have hd : GlobalTheory.InertDbl.matD s * diagCols (Fin d) = diagCols (Fin d) * (x • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
    have : h * (x + y) + h * (x - y) = x := by linear_combination x * h2h
    have k := symmetricScalarBlockMatrix_mul_diagonalColumns (d := d) (h * (x + y)) (h * (x - y))
    rw [this] at k
    exact k
  refine ⟨s, ⟨⟨?_, ?_⟩, ⟨x • 1, x' • 1, ?_, ?_⟩, hd⟩, hd, ?_⟩
  · intro u hu0
    obtain ⟨u1, u2⟩ := hu u hu0
    have k1 : u • (h * (x + y) - 1) = 0 := by
      rw [Algebra.smul_def, ← hxe, ← hye]
      linear_combination (-h * h) * u1 + h * u2 + algebraMap (AF F) (AE F E) u * h2h
    have k2 : u • (h * (x - y)) = 0 := by
      rw [Algebra.smul_def, ← hxe, ← hye]
      linear_combination (-h * h) * u1 - h * u2
    rw [hs, symmetricScalarBlockMatrix_sub_one, blk2, Matrix.fromBlocks_smul, ← smul_assoc, ← smul_assoc, k1, k2, zero_smul,
      Matrix.fromBlocks_zero]
  · intro z hz
    rw [hs, hs']
    exact ⟨symmetricScalarBlockMatrix_mulVec_mem_doubledLattice (GlobalTheory.SplitConj.mult_mul Mh (GlobalTheory.SplitConj.mult_add Mx My))
        (GlobalTheory.SplitConj.mult_mul Mh (mult_sub Mx My)) z hz,
      symmetricScalarBlockMatrix_mulVec_mem_doubledLattice (GlobalTheory.SplitConj.mult_mul Mh (GlobalTheory.SplitConj.mult_add Mx' My'))
        (GlobalTheory.SplitConj.mult_mul Mh (mult_sub Mx' My')) z hz⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hx, one_smul]
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, hx, one_smul]
  · have : h * (x + y) - h * (x - y) = y := by linear_combination y * h2h
    have k := symmetricScalarBlockMatrix_mul_antidiagonalColumns (d := d) (h * (x + y)) (h * (x - y))
    rw [this] at k
    exact k

end GlobalTheory.SplitConjPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsJointEigenDecompositionCommutingSymmetricO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.JointSpectral

theorem exists_finset_joint_eigen : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F Z hfd hmap hadd hsmul hcomm b hpos hsymm hadj
  let T : ι → Module.End ℂ Z := fun i =>
    { toFun := fun x => ⟨F i x, hmap i x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd i x x.2 y y.2)
      map_smul' := fun a x => Subtype.ext (hsmul i a x x.2) }
  let core : InnerProductSpace.Core ℂ Z :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by
        show star (b (y : E) x) = b x y
        exact hsymm y y.2 x x.2
      re_inner_nonneg := fun x => by
        show 0 ≤ (b (x : E) x).re
        by_cases hx : (x : E) = 0
        · rw [hx]; simp
        · exact (hpos x x.2 hx).le
      add_left := fun x y z => by
        show b ((x : E) + y) z = b x z + b y z
        rw [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by
        show b (r • (x : E)) y = starRingEnd ℂ r * b x y
        rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      definite := fun x hx => by
        by_contra h0
        have h1 := hpos x x.2 (fun e => h0 (Subtype.ext e))
        have h2 : b (x : E) x = 0 := hx
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup Z := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := core)
  letI : InnerProductSpace ℂ Z := InnerProductSpace.ofCore core.toCore
  have hT : ∀ i, (T i).IsSymmetric := fun i x y => (hadj i x x.2 y y.2).symm
  have hC : Pairwise (Function.onFun Commute T) := fun i j _ =>
    LinearMap.ext fun x => Subtype.ext (hcomm i j x x.2)
  have key := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have htop : IsCompactElement (⊤ : Submodule ℂ Z) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 hfd)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ htop
    (fun χ : ι → ℂ => ⨅ i, Module.End.eigenspace (T i) (χ i)) key.ge
  have hle : (⊤ : Submodule ℂ Z) ≤
      (⨆ c ∈ s, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}).comap Z.subtype := by
    refine hs.trans (iSup₂_le fun c hc y hy => ?_)
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy
    refine Submodule.mem_comap.2 ((le_iSup₂ (f := fun c (_ : c ∈ s) =>
      Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}) c hc) (Submodule.subset_span ⟨y.2, fun i => ?_⟩))
    exact congrArg Subtype.val (hy i)
  exact ⟨s, fun x hx => hle (x := ⟨x, hx⟩) Submodule.mem_top⟩

end GlobalTheory.JointSpectral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruencStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  first | exact @GlobalTheory.HeckeLevel.exists_level | exact GlobalTheory.HeckeLevel.exists_level | (intros; apply GlobalTheory.HeckeLevel.exists_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalProjectionPosDefSesquilinearFiniStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  first | exact @GlobalTheory.exists_proj_sesq_posDef_finiteDim | exact GlobalTheory.exists_proj_sesq_posDef_finiteDim | (intros; apply GlobalTheory.exists_proj_sesq_posDef_finiteDim <;> assumption)
end


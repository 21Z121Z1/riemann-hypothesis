import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMinkowskiExistsShortRationalVector
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  first | exact @GlobalTheory.abs_lrd_sub_log_d_le_lrd | exact GlobalTheory.abs_lrd_sub_log_d_le_lrd | (intros; apply GlobalTheory.abs_lrd_sub_log_d_le_lrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommute
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem supS_mul_comm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS E a S →
    GeneralLinearGroup.map (pInf E) t = 1 →
    (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  intro E _ _ _ a S h t hh ht htS
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, ht, mul_one, one_mul]
  · ext i j w
    have key : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (h * t) =
        GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (t * h) := by
      rw [map_mul, map_mul]
      by_cases hw : w ∈ S
      · rw [htS w hw, mul_one, one_mul]
      · rw [hh w hw, mul_one, one_mul]
    have e : ((GeneralLinearGroup.map (pFin E) (h * t)).val i j) w =
        ((GeneralLinearGroup.map (pFin E) (t * h)).val i j) w :=
      congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.val i j) key
    rw [e]

end GlobalTheory.JSW.MirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFiniteStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  first | exact @GlobalTheory.WhitBump.psiN_split | exact GlobalTheory.WhitBump.psiN_split | (intros; apply GlobalTheory.WhitBump.psiN_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndex
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.LatLoc

variable {E : Type} [Field E] [NumberField E]

theorem natCast_coord (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (n : Af E) w = (n : w.adicCompletion E) := by
  rfl

theorem val_nat_le_one (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((n : Af E) w) ≤ 1 := by
  have h : (n : Af E) = iota ((n : ℕ) : OF E) := by rw [iota, map_natCast, map_natCast]
  rw [h]; exact val_iota_le_one w _

theorem val_nat_eq_one {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} (hw : (n : 𝓞 E) ∉ w.asIdeal) :
    Valued.v ((n : Af E) w) = 1 := by
  have h1 := (w.valuation_eq_one_iff_notMem (K := E)).mpr hw
  have h2 := w.valuedAdicCompletion_eq_valuation' (K := E) ((n : ℕ) : E)
  have h3 : (algebraMap E (w.adicCompletion E)) ((n : ℕ) : E) = ((n : ℕ) : w.adicCompletion E) := map_natCast _ _
  have h4 : (((n : ℕ) : 𝓞 E) : E) = ((n : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) _
  rw [natCast_coord, ← h3]
  exact h2.trans (h4 ▸ h1)

theorem exp_neg_nat_le_one (k : ℕ) : WithZero.exp (-(k : ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem mul_mem_hatO [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) {l : ℕ} {u : Af E}
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → u P = 1) {n : ℕ}
    (hn : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∉ w.asIdeal →
      Valued.v ((n : Af E) w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) ∧
      Valued.v ((n : Af E) w) * Valued.v (u w) ≤
        WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)))
    {z : Af E} (hz : z ∈ hatO c) : (n : Af E) * z * u ∈ hatO c := by
  obtain ⟨a, ha, hai, hza⟩ := (HatPlace.mem_hatO_iff E c hc z).1 hz
  refine (HatPlace.mem_hatO_iff E c hc _).2 ⟨(n : Af E) * a, (hatF (E := E)).mul_mem (natCast_mem _ n) ha,
    fun w => ?_, fun w => ?_⟩
  · rw [mul_coord, map_mul]; exact mul_le_one' (val_nat_le_one n w) (hai w)
  · have hzi : Valued.v (z w) ≤ 1 := by
      have h := Valuation.map_add_le Valued.v ((hza w).trans (exp_neg_nat_le_one _)) (hai w)
      rwa [sub_add_cancel] at h
    by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
    · rw [mul_coord, mul_coord, mul_coord, hu w hw, mul_one, ← mul_sub, map_mul]
      exact (mul_le_mul' (val_nat_le_one n w) (hza w)).trans_eq (one_mul _)
    · obtain ⟨h1, h2⟩ := hn w hw
      refine Valuation.map_sub_le _ ?_ ?_
      · rw [mul_coord, mul_coord, map_mul, map_mul]
        calc Valued.v ((n : Af E) w) * Valued.v (z w) * Valued.v (u w)
            ≤ Valued.v ((n : Af E) w) * 1 * Valued.v (u w) := mul_le_mul' (mul_le_mul' le_rfl hzi) le_rfl
          _ ≤ _ := by rw [mul_one]; exact h2
      · rw [mul_coord, map_mul]; exact (mul_le_mul' h1 (hai w)).trans_eq (mul_one _)

theorem lattice_near_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime →
    ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
    ∃ n : ℕ, n.Coprime l ∧ (∀ x ∈ lattice c y, (n : E) * x ∈ orderC c) ∧ ∀ x ∈ orderC c, (n : E) * x ∈ lattice c y := by
  intro E _ _ _ c hc l hl y hy
  have hy' : ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (↑y⁻¹ : Af E) P = 1 := fun P hP => by
    have h : ((y : Af E) * ↑y⁻¹) P = 1 := by rw [Units.mul_inv]; rfl
    rwa [mul_coord, hy P hP, one_mul] at h
  obtain ⟨m₁, hm₁, hi₁⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral (F := E) (y : Af E)
  obtain ⟨m₂, hm₂, hi₂⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral (F := E) (↑y⁻¹ : Af E)
  have hN : Ideal.absNorm c ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hn0 : Ideal.absNorm c * m₁ * m₂ ≠ 0 := mul_ne_zero (mul_ne_zero hN hm₁) hm₂
  obtain ⟨k, n, hln, hkn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl.one_lt.ne'

  have hint : ∀ (m : ℕ) (u : Af E), (∀ v, (m • u) v ∈ v.adicCompletionIntegers E) → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v ((m : Af E) w) * Valued.v (u w) ≤ 1 := fun m u hmu w => by
    have h := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hmu w)
    change Valued.v (m • u w) ≤ 1 at h
    rwa [nsmul_eq_mul, map_mul, ← natCast_coord] at h
  have hNw : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((Ideal.absNorm c : Af E) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := fun w => by
    have h := HatPlace.val_mul_le hc (Ideal.absNorm_mem c) (y := 1) (fun w => by
      show Valued.v ((1 : w.adicCompletion E)) ≤ 1
      rw [map_one]) w
    have e : iota ((Ideal.absNorm c : ℕ) : OF E) * 1 = (Ideal.absNorm c : Af E) := by
      rw [mul_one, iota, map_natCast, map_natCast]
    rwa [e] at h
  have hnw : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∉ w.asIdeal →
      Valued.v ((n : Af E) w) = Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) *
        Valued.v ((m₂ : Af E) w) := fun w hw => by
    have h1 : Valued.v (((Ideal.absNorm c * m₁ * m₂ : ℕ) : Af E) w) = Valued.v ((n : Af E) w) := by
      rw [hkn, Nat.cast_mul, Nat.cast_pow, mul_coord, map_mul]
      have h2 : Valued.v ((((l : ℕ) : Af E) ^ k) w) = 1 := by
        rw [← Nat.cast_pow, natCast_coord, Nat.cast_pow, map_pow, ← natCast_coord, val_nat_eq_one hw, one_pow]
      rw [h2, one_mul]
    rw [← h1, Nat.cast_mul, Nat.cast_mul, mul_coord, mul_coord, map_mul, map_mul]
  have hle : ∀ a b : WithZero (Multiplicative ℤ), a ≤ 1 → b ≤ 1 → ∀ e, ∀ t : WithZero (Multiplicative ℤ), t ≤ e →
      t * a * b ≤ e := fun a b ha hb e t ht =>
    (mul_le_mul' (mul_le_mul' ht ha) hb).trans_eq (by rw [mul_one, mul_one])
  refine ⟨n, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hln), fun x hx => ?_, fun x hx => ?_⟩
  · have h := LatLoc.mul_mem_hatO hc hy (n := n) (fun w hw => by
      rw [hnw w hw]
      refine ⟨hle _ _ (val_nat_le_one _ w) (val_nat_le_one _ w) _ _ (hNw w), ?_⟩
      have e : Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) * Valued.v ((m₂ : Af E) w) *
          Valued.v ((y : Af E) w) = Valued.v ((Ideal.absNorm c : Af E) w) * (Valued.v ((m₁ : Af E) w) *
            Valued.v ((y : Af E) w)) * Valued.v ((m₂ : Af E) w) := by ac_rfl
      rw [e]
      exact hle _ _ (hint m₁ _ hi₁ w) (val_nat_le_one _ w) _ _ (hNw w)) (mem_lattice.1 hx)
    have e : (n : Af E) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (y : Af E) = algebraMap E (Af E) ((n : E) * x) := by
      rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one, map_mul, map_natCast]
    rw [e] at h
    exact HatCap.mem_orderC_of_mem_hatO hc h
  · have h := LatLoc.mul_mem_hatO hc hy' (n := n) (fun w hw => by
      rw [hnw w hw]
      refine ⟨hle _ _ (val_nat_le_one _ w) (val_nat_le_one _ w) _ _ (hNw w), ?_⟩
      have e : Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) * Valued.v ((m₂ : Af E) w) *
          Valued.v ((↑y⁻¹ : Af E) w) = Valued.v ((Ideal.absNorm c : Af E) w) * Valued.v ((m₁ : Af E) w) *
            (Valued.v ((m₂ : Af E) w) * Valued.v ((↑y⁻¹ : Af E) w)) := by ac_rfl
      rw [e]
      exact hle _ _ (val_nat_le_one _ w) (hint m₂ _ hi₂ w) _ _ (hNw w)) (algebraMap_mem_hatO hx)
    rw [mem_lattice, map_mul, map_natCast]
    exact h

end GlobalTheory.CMVal.LatLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMinkowskiExistsShortRationalVectorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_minkowski_exists_short_rational_vector : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∃ B : Set (Fin n → AF F), IsCompact B ∧ ∀ g : Matrix (Fin n) (Fin n) (AF F), IsUnit g.det → (∃ u : (AF F)ˣ, (u : AF F) = g.det ∧ (GroundTheory.Global.IdeleGroup.ideleModule F u : ℝ) ≤ 1) → ∃ ξ : Fin n → F, ξ ≠ 0 ∧ g *ᵥ (fun i => algebraMap F (AF F) (ξ i)) ∈ B := by
  first | exact @GlobalTheory.AdelicMinkowski.exists_compact_mulVec_rat_mem | exact GlobalTheory.AdelicMinkowski.exists_compact_mulVec_rat_mem | (intros; apply GlobalTheory.AdelicMinkowski.exists_compact_mulVec_rat_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  first | exact @GlobalTheory.SchwartzDecay.decay_of_mem_schA | exact GlobalTheory.SchwartzDecay.decay_of_mem_schA | (intros; apply GlobalTheory.SchwartzDecay.decay_of_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  first | exact @GlobalTheory.ThetaTransform.symV_realLine_eq_zero | exact GlobalTheory.ThetaTransform.symV_realLine_eq_zero | (intros; apply GlobalTheory.ThetaTransform.symV_realLine_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleComplementTwoAlongFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleComplementTwo_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  first | exact @GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | exact GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | (intros; apply GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.SumDual

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem sum_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ G *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

omit [NumberField E] [StarRing E] in
theorem antiDiagonalEpsilonGram_mulVec {c : ℕ} (ε : E) (u : Fin c → E) (p : Fin c) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) p = (if p = p.rev then ε else 1) * u p.rev := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p.rev]
  · have := p.2
    simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
    rw [if_pos (by omega)]
  · intro q _ hq
    have := p.2
    simp only [antiDiagonalSignGramMatrix]
    rw [if_neg, zero_mul]
    intro h
    exact hq (Fin.ext (by rw [Fin.val_rev]; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_herm (S : HSpace E) : S.gramᴴ = S.gram := by
  ext i j
  exact S.herm.eq _ _

theorem hT_eq (S : HSpace E) (x y : S.V) :
    S.hT x y = star (S.frame.equivFun x) ⬝ᵥ S.gram *ᵥ S.frame.equivFun y := by
  rw [← sum_eq_dot]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, Module.Basis.equivFun_apply, HSpace.gram]
  ring

theorem gram_inj (S : HSpace E) (y : Fin S.rank → E) (h : S.gram *ᵥ y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := S.frame.equivFun.surjective y
  rw [S.nondeg.2 y fun x => by rw [hT_eq, h, dotProduct_zero], map_zero]

theorem gram_isom (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (h : HSpace.IsIsomEmb A B ι) :
    (LinearMap.toMatrix A.frame B.frame ι)ᴴ * B.gram * LinearMap.toMatrix A.frame B.frame ι = A.gram := by
  ext i j
  rw [HSpace.gram, ← h, hT_eq, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, LinearMap.toMatrix_apply, Pi.star_apply,
    Module.Basis.equivFun_apply]

theorem selfDual_sum {n k c : ℕ} (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (G : Matrix (Fin n) (Fin n) E) (J : Matrix (Fin k) (Fin k) E) (M : Matrix (Fin n) (Fin k) E)
    (a : Matrix (Fin n) (Fin c) E) (ε : E) (hε : ε = 1 ∨ ε = -1) (hG : Gᴴ = G) (hJ : ∀ y, J *ᵥ y = 0 → y = 0)
    (h1 : Mᴴ * G * M = J) (h2 : Mᴴ * G * a = 0) (h3 : aᴴ * G * a = antiDiagonalSignGramMatrix c ε) (hr : k + c = n)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (𝔟 : Fin c → FractionalIdeal (𝓞 E)⁰ E)
    (hΛ : Submodule.IsLattice E Λ)
    (hΛd : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * J i j * y j)
    (hb : ∀ p, 𝔟 p ≠ 0) (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹)
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ ∃ y ∈ Λ, ∃ u : Fin c → E, (∀ p, u p ∈ 𝔟 p) ∧ x = M *ᵥ y + a *ᵥ u) :
    Submodule.IsLattice E L ∧
      ∀ y, y ∈ L ↔ ∀ x ∈ L, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  classical
  have h2' : aᴴ * G * M = 0 := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have eM : ∀ y u, Mᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = J *ᵥ y := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h1, h2, zero_mulVec, add_zero]
  have ea : ∀ y u, aᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = antiDiagonalSignGramMatrix c ε *ᵥ u := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h2', h3, zero_mulVec, zero_add]
  have key : ∀ x v y u, ∑ i, ∑ j, star ((M *ᵥ x + a *ᵥ v) i) * G i j * (M *ᵥ y + a *ᵥ u) j =
      (∑ i, ∑ j, star (x i) * J i j * y j) + ∑ p, (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := by
    intro x v y u
    rw [sum_eq_dot, sum_eq_dot, star_add, add_dotProduct, star_mulVec, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, eM, ea]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [antiDiagonalEpsilonGram_mulVec, Pi.star_apply]; ring
  have hsg : ∀ p : Fin c, ∃ e : 𝓞 E, (e : E) = (if p = p.rev then ε else 1) ∧ e * e = 1 := fun p => by
    split_ifs
    · rcases hε with rfl | rfl
      · exact ⟨1, rfl, by simp⟩
      · exact ⟨-1, by simp, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  have hst : ∀ z : E, (∃ b : 𝓞 E, (b : E) = z) → ∃ b : 𝓞 E, (b : E) = star z := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨star (b : E), hs _ b.isIntegral_coe⟩, rfl⟩
  let f : ((Fin k → E) × (Fin c → E)) →ₗ[E] (Fin n → E) := M.mulVecLin.coprod a.mulVecLin
  have hf : ∀ y u, f (y, u) = M *ᵥ y + a *ᵥ u := fun _ _ => rfl
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    rintro ⟨y, u⟩ h
    rw [hf] at h
    have e1 := eM y u
    have e2 := ea y u
    rw [h, mulVec_zero, mulVec_zero] at e1 e2
    refine Prod.ext (hJ y e1.symm) (funext fun p => ?_)
    have e3 := congrFun e2 p.rev
    obtain ⟨e, he, hee⟩ := hsg p.rev
    rw [antiDiagonalEpsilonGram_mulVec, ← he, Fin.rev_rev] at e3
    have he0 : (e : E) ≠ 0 := by
      intro h0
      have : e = 0 := by exact_mod_cast h0
      rw [this] at hee; simp at hee
    exact (mul_eq_zero.1 e3.symm).resolve_left he0
  have fsur : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).1 finj
  refine ⟨⟨?_, ?_⟩, fun y' => ⟨?_, fun h => ?_⟩⟩
  · have : L = (Λ.prod (Submodule.pi Set.univ fun p => (𝔟 p : Submodule (𝓞 E) E))).map (f.restrictScalars (𝓞 E)) := by
      ext x
      rw [hL, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, u, hu, rfl⟩
        exact ⟨(y, u), ⟨hy, fun p _ => hu p⟩, rfl⟩
      · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
        exact ⟨y, hy, u, fun p => hu p trivial, rfl⟩
    rw [this]
    exact (hΛ.fg.prod (Submodule.fg_pi fun p => FractionalIdeal.fg_of_isNoetherianRing le_rfl _)).map _
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨⟨y, u⟩, rfl⟩ := fsur y
    rw [hf]
    refine Submodule.add_mem _ ?_ ?_
    · have hy : y ∈ Submodule.span E (Λ : Set (Fin k → E)) := by rw [hΛ.span_eq_top]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, by simp⟩)
      | zero => simp
      | add x z _ _ hx hz => rw [mulVec_add]; exact Submodule.add_mem _ hx hz
      | smul r x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ r hx
    · rw [← Finset.univ_sum_single u, mulVec_sum]
      refine Submodule.sum_mem _ fun p _ => ?_
      obtain ⟨t, ht0, ht⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (hb p)
      have ht0' : algebraMap (𝓞 E) E t ≠ 0 := by simpa using ht0
      have : (Pi.single p (u p) : Fin c → E) =
          (u p / algebraMap (𝓞 E) E t) • Pi.single p (algebraMap (𝓞 E) E t) := by
        rw [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ ht0']
      rw [this, mulVec_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p (algebraMap (𝓞 E) E t), fun q => ?_, by rw [mulVec_zero, zero_add]⟩))
      by_cases hq : q = p
      · subst hq; simpa using ht
      · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
  · intro hy' x' hx'
    obtain ⟨y, hy, u, hu, rfl⟩ := (hL _).1 hy'
    obtain ⟨x, hx, v, hv, rfl⟩ := (hL _).1 hx'
    obtain ⟨b, hb1⟩ := (hΛd y).1 hy x hx
    have : ∀ p : Fin c, ∃ t : 𝓞 E, (t : E) = (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := fun p => by
      obtain ⟨e, he, -⟩ := hsg p
      have := (FractionalIdeal.mem_inv_iff (hb p)).1 ((hd p _).1 (hu p.rev)) _ (hv p)
      obtain ⟨t, ht⟩ := hst _ ((FractionalIdeal.mem_one_iff _).1 this)
      refine ⟨e * t, ?_⟩
      rw [← he, RingOfIntegers.coe_eq_algebraMap, map_mul]
      congr 1
      refine ht.trans ?_
      rw [star_mul, star_star]
    choose t ht using this
    refine ⟨b + ∑ p, t p, ?_⟩
    rw [key, ← hb1, ← Finset.sum_congr rfl fun p _ => ht p]
    simp
  · obtain ⟨⟨y, u⟩, rfl⟩ := fsur y'
    rw [hf] at h ⊢
    refine (hL _).2 ⟨y, (hΛd y).2 fun x hx => ?_, u, fun q => ?_, rfl⟩
    · have := h _ ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, rfl⟩)
      rw [key] at this
      simpa using this
    · obtain ⟨p, rfl⟩ := Fin.rev_surjective q
      refine (hd p _).2 ((FractionalIdeal.mem_inv_iff (hb p)).2 fun s hs => ?_)
      have := h _ ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p s, fun q => by
        by_cases hq : q = p
        · subst hq; simpa using hs
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem, rfl⟩)
      rw [key, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp)
        (fun h => absurd (Finset.mem_univ _) h)] at this
      obtain ⟨b, hb1⟩ := this
      obtain ⟨e, he, hee⟩ := hsg p
      rw [← he] at hb1
      have hee' : (e : E) * e = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hee
      obtain ⟨t, ht⟩ := hst (star s * u p.rev) ⟨e * b, by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul]
        change (e : E) * (b : E) = _
        rw [hb1]
        simp only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, Pi.single_eq_same]
        rw [← mul_assoc, hee', one_mul]⟩
      refine (FractionalIdeal.mem_one_iff _).2 ⟨t, ht.trans ?_⟩
      rw [star_mul, star_star]

end General

theorem isSelfDualC_lat : ∀ (D : D7) (A B : HSp D) (c : ℕ) (ε : D.host.E) (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), (ε = 1 ∨ ε = -1) → IsSelfDualC A Λ → (∀ p, 𝔟 p ≠ 0) → (∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) → IsSelfDualC B (d.lat Λ 𝔟) := by
  intro D A B c ε d Λ 𝔟 hε hΛ hb hd
  exact selfDual_sum Formalism.BasicNotions.Examples₂.star_isIntegral B.gram A.gram (frameMat B A d.ι) d.a ε hε (gram_herm B) (gram_inj A)
    (gram_isom A B d.ι d.isom) d.perp d.gram d.rank Λ 𝔟 hΛ.1 hΛ.2 hb hd _ fun _ => Iff.rfl

end GlobalTheory.ChiGrid.SumDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothKernelRepresentationStatement
section
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_smooth_kernel_representation : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : GlobalTheory.CuspRep.Lie E a → ℂ), GlobalTheory.JSW.IsTestInf f → GlobalTheory.JSW.IsRapidInf (volume : Measure (GlobalTheory.CuspRep.Lie E a)) f (fun x : GlobalTheory.CuspRep.Lie E a => if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (GlobalTheory.CuspRep.Cinf E))) ∧ ∀ F : GlobalTheory.CuspRep.GA E a → ℂ, GlobalTheory.JSW.smoothInf f F = GlobalTheory.JSW.kerInf (volume : Measure (GlobalTheory.CuspRep.Lie E a)) f (fun x : GlobalTheory.CuspRep.Lie E a => if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (GlobalTheory.CuspRep.Cinf E))) F := by
  first | exact @GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf | exact GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf | (intros; apply GlobalTheory.JSW.isRapidInf_and_smoothInf_eq_kerInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzero
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroup
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem levSetInf_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ),
    (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧
    (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  intro E _ _ n r
  refine ⟨fun g hg h hh w => ?_, fun g hg w => ?_, fun u hu => ?_, ?_⟩
  · rw [map_mul]
    exact (levSet_closed_subgroup n r).1 _ (hg w) _ (hh w)
  · rw [map_inv]
    exact (levSet_closed_subgroup n r).2.1 _ (hg w)
  · obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    exact mem_levSetInf.2 fun i _ => ⟨fun j hj => h0 i j hj, h1 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) (Cinf E) =>
        (g : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
      fun i j => (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf E))).matrix_elem i j
    have hs : levSetInf E n r = {g : GL (Fin n) (Cinf E) | ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
          (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1} := Set.ext fun g => mem_levSetInf
    rw [hs]
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const
    · exact isClosed_eq (hc i i) continuous_const

end GlobalTheory.JSW.MirCinf
end


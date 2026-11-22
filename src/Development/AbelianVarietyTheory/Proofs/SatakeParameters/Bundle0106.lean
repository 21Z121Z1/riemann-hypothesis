import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Formalism.LocalToGlobal.AlgebraicTheory.Bundle0002
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
section
namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_eq_of_split_factor (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : DegOne v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hm : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hq, hq2⟩ := hv
  constructor
  · have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
      rw [← h2]
      exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
    have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) v.asIdeal
    rw [hm, hr, map_mul] at h1
    have hP : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    have hP' : Ideal.absNorm P'.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P'.isPrime.ne_top
    obtain ⟨k, hk, e⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ h1)
    interval_cases k
    · exact absurd (by simpa using e) hP
    · simpa using e
    · rw [e] at h1
      exact absurd ((Nat.mul_eq_left (pow_pos hq.pos 2).ne').1 h1) hP'
  · intro hmem
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem _
    have h3 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hI
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, hm, mul_assoc] at h3
    have h4 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * I.map (algebraMap (𝓞 F) (𝓞 E))) := by
      rw [← h3, ← sq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have h5 := (mul_dvd_mul_iff_left P.ne_bot).1 h4
    rcases P.prime.dvd_or_dvd h5 with h6 | h6
    · rw [Ideal.dvd_iff_le] at h6
      exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h6).symm)
    · rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h6
      have h7 : v.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
        rw [← Ideal.map_le_iff_le_comap, hm]
        exact (Ideal.mul_le_inf).trans inf_le_left
      rw [← v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h7] at h6
      apply hq2
      rw [← Ideal.span_singleton_le_iff_mem, hI, sq]
      exact Ideal.mul_mono_right h6

theorem absNorm_eq_of_splitAt (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hv : DegOne v) {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  obtain ⟨P, P', hne, hm⟩ := hs
  have h1 : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hQ]
  rcases Q.isPrime.mul_le.1 h1 with h | h
  · obtain rfl : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne hm
  · obtain rfl : P' = Q := HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact absNorm_eq_of_split_factor h2 hv hne.symm (hm.trans (mul_comm _ _))

omit [NumberField E] [Field E] [Algebra F E] in

theorem plc_eq_absNorm {v : HeightOneSpectrum (𝓞 F)} (hq : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have := v.isPrime
  rcases (Nat.dvd_prime hq).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · exact h7

end Split

theorem degOneUnram_of_mem_vG {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vG i) : DegOneUnram P := by
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have hn : qOf P = Pr.g i := hPr.vG_norm i P hP
  refine ⟨hn ▸ hPr.g_prime i, ?_⟩
  rw [hn]
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO (X.conjO (Pr.piG i)) (Pr.g i) hcc (hPr.g_prime i) ?_ ?_ ?_
    (hPr.vG_norm i) P hP
  · rw [hcc, mul_comm]; exact hPr.piG_norm i
  · rw [hcc]; exact (hPr.piG_cop i).symm
  · rw [hE, ← hPr.vG_card i]; rfl

theorem levelPrimes : LevelPrimes := by
  classical
  intro X Pr sel S mu hX hPr hsel P
  by_cases hP : P.1 ∈ Pr.vGs
  · refine ⟨?_, fun h => absurd hP h⟩
    rcases Finset.mem_union.1 hP with h | h
    exacts [degOneUnram_of_mem_vG hX hPr 0 h, degOneUnram_of_mem_vG hX hPr 1 h]
  · rcases Finset.mem_union.1 P.2 with h1 | h1
    · exact absurd h1 hP
    unfold QE at h1
    split_ifs at h1 with h2
    · obtain ⟨v0, hv0, e⟩ := Finset.mem_image.1 h1
      have hv1 : v0 ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv0
      have hgood : GoodPl X.E S v0 := by
        by_contra hn
        have h4 := (Subgroup.mem_inf.1 mu.2).2
        exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v0) hn)
      obtain ⟨h3, h4⟩ := absNorm_eq_of_splitAt hX.rankE hgood.1 hgood.2.1 (Q := P.1) (e ▸ hsel v0)
      have h5 : qOf P.1 = Ideal.absNorm v0.asIdeal := h3
      refine ⟨⟨h5 ▸ hgood.2.1.1, h5 ▸ h4⟩, fun _ => ?_⟩
      rw [h5, ← plc_eq_absNorm hgood.2.1.1]
      exact hgood.2.2
    · simp at h1

end GlobalTheory.ColPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeFgOfFullStatement
section
open NumberField IsDedekindDomain Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPointLattice_fg_of_full : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), (latAd x Lb).FG := by
  first | exact @GlobalTheory.LatAdFG.latAd_fg_of_full | exact GlobalTheory.LatAdFG.latAd_fg_of_full | (intros; apply GlobalTheory.LatAdFG.latAd_fg_of_full <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSubspacesKerTransposeEqCardRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem card_le_ker_transpose_eq_card_range_le :
    ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  intro k _ m n j z
  set B : LinearMap.BilinForm k (Fin m → k) := Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) k) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ y := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := by
    intro x y h
    rw [hB] at h ⊢
    rw [dotProduct_comm]; exact h
  have hnd : B.Nondegenerate := by
    rw [hBdef]
    exact Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have hinv : ∀ W : Submodule k (Fin m → k), B.orthogonal (B.orthogonal W) = W :=
    fun W => LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W
  have hdim : ∀ W : Submodule k (Fin m → k),
      Module.finrank k W + Module.finrank k (B.orthogonal W) = m := by
    intro W
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
    have h2 := Submodule.finrank_le W
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  have hker : LinearMap.ker zᵀ.mulVecLin = B.orthogonal (LinearMap.range z.mulVecLin) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff, Matrix.mulVecLin_apply]
    constructor
    · rintro h _ ⟨y, rfl⟩
      show B (z.mulVecLin y) x = 0
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, h, zero_dotProduct]
    · intro h
      ext i
      have h1 : B (z.mulVecLin (Pi.single i 1)) x = 0 := h _ ⟨_, rfl⟩
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, dotProduct_single, mul_one] at h1
      simpa using h1
  let e : Submodule k (Fin m → k) ≃ Submodule k (Fin m → k) :=
    ⟨B.orthogonal, B.orthogonal, hinv, hinv⟩
  refine Nat.card_congr (e.subtypeEquiv fun W => ?_)
  show _ ↔ Module.finrank k (B.orthogonal W) = j ∧ LinearMap.range z.mulVecLin ≤ B.orthogonal W
  have hd := hdim W
  refine and_congr ⟨fun h => by omega, fun h => by omega⟩ ?_
  rw [hker]
  constructor
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramifiedStatement
section
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_good_model_unramified : (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) → ReciprocityTheory.ChartRestriction.L1.ChebOmSt → Formalism.L2.Th1.CM.CM2 := by
  first | exact @GlobalTheory.ArtinClassCM.good_model | exact GlobalTheory.ArtinClassCM.good_model | (intros; apply GlobalTheory.ArtinClassCM.good_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  first | exact @GlobalTheory.DivDual.divAt_inv_and_mul | exact GlobalTheory.DivDual.divAt_inv_and_mul | (intros; apply GlobalTheory.DivDual.divAt_inv_and_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
section
noncomputable section

namespace GlobalTheory.SplitLift

section General

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

open Formalism.UG

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_add (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_smul (σ : A →+* A) (a : A) (M : Matrix n n A) : cT σ (a • M) = σ a • cT σ M := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_involutive (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem exists_unitary (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (m m' : Matrix n n A)
    (h : e • (m * m') = e • (1 : Matrix n n A)) :
    ∃ g ∈ UJ σ J, (e + σ e) • ((g : Matrix n n A) - 1) = (g : Matrix n n A) - 1 ∧
      e • (g : Matrix n n A) = e • m := by
  have hKJ : K * J = 1 := mul_eq_one_comm.1 hJK
  have hK : cT σ K = K := by
    have h1 : cT σ K * J = 1 := by rw [← hJ, ← cT_mul, hJK, cT_one]
    calc cT σ K = cT σ K * (J * K) := by rw [hJK, mul_one]
      _ = K := by rw [← mul_assoc, h1, one_mul]
  have hee : σ e * σ e = σ e := by rw [← map_mul, he]
  have he'' : σ e * e = 0 := by rw [mul_comm, he']

  obtain ⟨x, hx⟩ : ∃ x, x = m - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = m' - 1 := ⟨_, rfl⟩
  have hm : m = 1 + x := by rw [hx]; abel
  have hm' : m' = 1 + y := by rw [hy]; abel
  have hab : (1 + e • x) * (1 + e • y) = 1 := by
    have h2 : e • (x + y + x * y) = 0 := by
      have : x + y + x * y = m * m' - 1 := by rw [hm, hm']; noncomm_ring
      rw [this, smul_sub, h, sub_self]
    calc (1 + e • x) * (1 + e • y) = 1 + (e • x + e • y + (e • x) * (e • y)) := by
          simp only [mul_add, add_mul, one_mul, mul_one]; abel
      _ = 1 := by
        rw [smul_mul_smul_comm, he, ← smul_add, ← smul_add, h2, add_zero]
  have hba : (1 + e • y) * (1 + e • x) = 1 := mul_eq_one_comm.1 hab
  let s : Matrix n n A → Matrix n n A := fun z => K * cT σ z * J
  have hs_mul : ∀ z w, s (z * w) = s w * s z := by
    intro z w
    show K * cT σ (z * w) * J = K * cT σ w * J * (K * cT σ z * J)
    rw [cT_mul]
    calc K * (cT σ w * cT σ z) * J = K * cT σ w * (J * K) * cT σ z * J := by rw [hJK]; noncomm_ring
      _ = _ := by noncomm_ring
  have hs_one : s 1 = 1 := by
    show K * cT σ 1 * J = 1
    rw [cT_one, mul_one, hKJ]
  have hs_e : ∀ z, s (1 + e • z) = 1 + σ e • s z := by
    intro z
    show K * cT σ (1 + e • z) * J = 1 + σ e • (K * cT σ z * J)
    rw [conjTransposeBy_ringInvolution_add, cT_one, conjTransposeBy_ringInvolution_smul, mul_add, add_mul, mul_one, hKJ, Matrix.mul_smul, Matrix.smul_mul]
  have hss : ∀ z, s (s z) = z := by
    intro z
    show K * cT σ (K * cT σ z * J) * J = z
    rw [cT_mul, cT_mul, conjTransposeBy_ringInvolution_involutive σ hσ, hJ, hK]
    calc K * (J * (z * K)) * J = (K * J) * z * (K * J) := by noncomm_ring
      _ = z := by rw [hKJ, one_mul, mul_one]
  have hcomm : ∀ z w : Matrix n n A, (1 + e • z) * (1 + σ e • w) = 1 + e • z + σ e • w ∧
      (1 + σ e • w) * (1 + e • z) = 1 + e • z + σ e • w := by
    intro z w
    constructor
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm e z (σ e) w, he', zero_smul]; simp
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm (σ e) w e z, he'', zero_smul]; simp; abel
  have hu : s ((1 + e • x) * s (1 + e • y)) * ((1 + e • x) * s (1 + e • y)) = 1 := by
    have hc : s (1 + e • x) * (1 + e • x) = (1 + e • x) * s (1 + e • x) := by
      rw [hs_e, (hcomm _ _).1, (hcomm _ _).2]
    rw [hs_mul, hss]
    calc (1 + e • y) * s (1 + e • x) * ((1 + e • x) * s (1 + e • y))
        = (1 + e • y) * (s (1 + e • x) * (1 + e • x)) * s (1 + e • y) := by simp only [mul_assoc]
      _ = ((1 + e • y) * (1 + e • x)) * (s (1 + e • x) * s (1 + e • y)) := by rw [hc]; simp only [mul_assoc]
      _ = 1 := by rw [← hs_mul, hba, hs_one, one_mul]
  have hg : (1 + e • x) * s (1 + e • y) = 1 + e • x + σ e • s y := by rw [hs_e, (hcomm _ _).1]
  refine ⟨⟨_, _, mul_eq_one_comm.1 hu, hu⟩, ?_, ?_, ?_⟩
  · show cT σ ((1 + e • x) * s (1 + e • y)) * J * ((1 + e • x) * s (1 + e • y)) = J
    generalize (1 + e • x) * s (1 + e • y) = g at hu
    calc cT σ g * J * g = (J * K) * (cT σ g * J * g) := by rw [hJK, one_mul]
      _ = J * (s g * g) := by simp only [s, mul_assoc]
      _ = J := by rw [hu, mul_one]
  · show (e + σ e) • ((1 + e • x) * s (1 + e • y) - 1) = (1 + e • x) * s (1 + e • y) - 1
    have : (1 + e • x) * s (1 + e • y) - 1 = e • x + σ e • s y := by rw [hg]; abel
    rw [this, smul_add, smul_smul, smul_smul, add_mul, add_mul, he, he', he'', hee, add_zero, zero_add]
  · show e • ((1 + e • x) * s (1 + e • y)) = e • m
    rw [hg, hm, smul_add, smul_add, smul_add, smul_smul, smul_smul, he, he', zero_smul, add_zero]

theorem exists_unitary_prod {B C : Type} [CommRing B] [CommRing C] (p : A →+* B) (q : A →+* C) (φ : A ≃+* B × C)
    (hφ : ∀ z, (φ z).1 = p z ∧ (φ z).2 = q z)
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (hinf : p e = 0) (m m' : Matrix n n C)
    (h : q e • (m * m') = q e • (1 : Matrix n n C)) :
    ∃ g ∈ UJ σ J, (∀ i j, (e + σ e) * ((g : Matrix n n A) - 1) i j = ((g : Matrix n n A) - 1) i j) ∧
      q e • (g : Matrix n n A).map q = q e • m := by
  have lift : ∀ M : Matrix n n C, ∃ N : Matrix n n A, N.map q = M := by
    intro M
    refine ⟨Matrix.of fun i j => φ.symm (0, M i j), Matrix.ext fun i j => ?_⟩
    show q (φ.symm (0, M i j)) = M i j
    rw [← (hφ _).2, RingEquiv.apply_symm_apply]
  obtain ⟨N, rfl⟩ := lift m
  obtain ⟨N', rfl⟩ := lift m'
  have hN : e • (N * N') = e • (1 : Matrix n n A) := by
    refine Matrix.ext fun i j => φ.injective (Prod.ext ?_ ?_)
    · rw [(hφ _).1, (hφ _).1, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul, hinf, zero_mul, zero_mul]
    · rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero _) (map_one _)] at h
      rw [(hφ _).2, (hφ _).2, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul]
      exact congrFun (congrFun h i) j
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary σ hσ _ _ hJ hJK e he he' N N' hN
  refine ⟨g, hg, fun i j => congrFun (congrFun h1 i) j, Matrix.ext fun i j => ?_⟩
  have h3 : e * g.1 i j = e * N i j := congrFun (congrFun h2 i) j
  have h4 := congrArg q h3
  rw [map_mul, map_mul] at h4
  exact h4

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_lift : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ m m' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (m * m') = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) → ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finPart D e • finMat D.sp.cm.sig V.gram g = finPart D e • m := by
  intro D V e he m m' h
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hinf : infPart D e = 0 := by
    obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
    have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
    rw [h6, RingHom.map_mul, h5, mul_zero]
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D) GlobalTheory.DualPairCheck.cA_cA _ _
    hJ hJK e he.1 he.2.1 hinf m m' h
  exact ⟨⟨g, hg⟩, h1, h2⟩

end GlobalTheory.SplitLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLinearEquivMapEqOfFinrankEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem exists_linearEquiv_map_eq_of_finrank_eq {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (W W' : Submodule k V)
    (h : Module.finrank k W = Module.finrank k W') :
    ∃ e : V ≃ₗ[k] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank k U = Module.finrank k U' := by omega
  let a : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[k] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_residue_eq (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (W W' : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL (Fin n) O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' h
  let M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeUnit
section
open GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriod

theorem heckeUnit : GlobalTheory.ColPeriod.HeckeUnit :=
  fun _ _ _ _ _ _ _ _ hX hPr hμ _ _ _ _ hw hP x _ hk => GlobalTheory.CharVal.mu_unit hX hPr hμ x hk hP hw

end GlobalTheory.ColPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeFactsAt
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recSeam HostTie AnTie)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg LatWithBasis)

def JetOpWeyl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      (∀ τ, Submodule.IsLattice K (M τ)) → (∀ τ, Submodule.IsLattice K (MW τ)) → LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)),
          c • jetOp lam lam' J n F ∈ localization₂ w.asIdeal (delK lam' fun τ => dualFr (MW τ))

def LatticeFactsAt {X : Fields} (A : Amb X) : Prop := ∀ a b : ℕ, Even a → Even b → A.LaHyp a b ∅ ∧ A.ESmooth a b

def FamilyFacts (D : D7) (EX : ErrX D) {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → AnTie D δ χ cD → B.VecP χ ∧ B.IntP χ ∧ LatticeFactsAt (ambOf (recSeam D) B χ cD)

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndex
section
namespace GlobalTheory

theorem locNormInter : Formalism.L2.AlgTh.LocNormInter := Formalism.L2.AlgTh.local_norm_intertwiner

end GlobalTheory
end


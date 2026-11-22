import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0007
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EmbGramDetConjugate
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramMean

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def embGramDet {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (E : Matrix (Fin d) (Fin j) K)
    (φ : K →+* ℂ) : ℂ :=
  ((E.map φ)ᴴ * H.map φ * E.map φ).det

omit [NumberField K] [StarRing K] in
theorem embGramDet_conjugate {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    embGramDet H E (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (embGramDet H E φ) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) K),
      M.map (ComplexEmbedding.conjugate φ) = (M.map φ).map (starRingEnd ℂ) := by
    intro a b M
    ext i k
    simp [ComplexEmbedding.conjugate_coe_eq]
  unfold embGramDet
  rw [hm E, hm H, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul]
  congr 2

omit [NumberField K] [StarRing K] in
theorem embGramDet_re_mk {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    (embGramDet H E (InfinitePlace.mk φ).embedding).re = (embGramDet H E φ).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, embGramDet_conjugate, Complex.conj_re]

theorem gram_eq_mul {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = (((Matrix.of e)ᵀ).map v.embedding)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) *
      ((Matrix.of e)ᵀ).map v.embedding := by
  ext a c
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, majAt_eq, metMat, cv, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem map_gramR {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (e : Fin j → Fin d → K)
    (φ : K →+* ℂ) :
    φ (gramR H e) = ((((Matrix.of e)ᵀ).map (Rb.tw φ))ᴴ * H.map φ *
      ((Matrix.of e)ᵀ).map φ).det := by
  unfold gramR
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul,
    Rb.tw_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

private theorem det_gram_eq_embGramDet {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) :
    (gram X v e).det = embGramDet H ((Matrix.of e)ᵀ) v.embedding := by
  rw [gram_eq_mul, hX v]
  rfl

private theorem det_gram_re_nonneg' {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v : InfinitePlace K, IsUnit (X v).det)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  have hP : (((X v)⁻¹)ᴴ * (X v)⁻¹).PosDef := Rb.metMat_posDef X v (hX v)
  have hS := hP.posSemidef.conjTranspose_mul_mul_same (((Matrix.of e)ᵀ).map v.embedding)
  rw [← gram_eq_mul] at hS
  exact (Complex.le_def.mp hS.det_nonneg).1

theorem prod_norm_gramR_le (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hR : IsRatHerm (cmMax K) H X) (e : Fin j → Fin d → K) :
    ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ≤
      ∏ v : InfinitePlace K, (gram X v e).det.re := by
  have hU : ∀ v : InfinitePlace K, IsUnit (X v).det := fun v => (hR.2 v).1
  have hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding := fun v => (hR.2 v).2
  have hK0 : IsCMSub (cmMax K) := fun σ a ha => ha σ
  set E : Matrix (Fin d) (Fin j) K := (Matrix.of e)ᵀ with hE
  set g : InfinitePlace K → ℝ := fun v => (gram X v e).det.re with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => det_gram_re_nonneg' X hU e v
  have hloc : ∀ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ^ 2 ≤ g (Rb.plc v) * g v := by
    intro v
    have hPD : (H.map v.embedding).PosDef := by
      rw [← hX v]; exact Rb.metMat_posDef X v (hU v)
    have hcs := determinant_cauchy_schwarz d j (H.map v.embedding) hPD ((E.map (Rb.tw v.embedding))ᴴ)
      ((E.map v.embedding)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at hcs
    rw [map_gramR]
    have h1 : g (Rb.plc v) = (embGramDet H E (Rb.tw v.embedding)).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e, Rb.plc, embGramDet_re_mk]
    have h2 : g v = (embGramDet H E v.embedding).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e]
    rw [h1, h2]
    unfold embGramDet
    rw [Rb.Hmap_tw (cmMax K) hK0 H hR.1]
    exact hcs
  have hperm : ∏ v : InfinitePlace K, g (Rb.plc v) = ∏ v : InfinitePlace K, g v :=
    Equiv.prod_comp (Function.Involutive.toPerm _ (fun v => Rb.plc_plc v)) g
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, g v) ^ 2 := by
    have hsq2 : (∏ v : InfinitePlace K, g v) ^ 2 = ∏ v : InfinitePlace K, (g (Rb.plc v) * g v) := by
      rw [Finset.prod_mul_distrib, hperm, sq]
    rw [← Finset.prod_pow, hsq2]
    exact Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => hloc v)
  have ha : 0 ≤ ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ :=
    Finset.prod_nonneg fun v _ => norm_nonneg _
  have hb : 0 ≤ ∏ v : InfinitePlace K, g v := Finset.prod_nonneg fun v _ => hg0 v
  nlinarith

end GlobalTheory.GramMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (coeff mo F) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : coeff mo F = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * coeff mo F = ((coeff mo Q : 𝓞 K) : K) := by
      have h1 := congrArg (coeff mo) hQ
      rw [coeff_smul] at h1
      have h2 : coeff mo (toK K _ Q) = ((coeff mo Q : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (coeff mo Q)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOne
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.FracPrim

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Bd (X : Tower Ω ε) (x : X.K) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp x).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * (X.exp x).coeff r)

theorem bd_one (X : Tower Ω ε) : Bd X 1 := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact ⟨one_mem _, by simpa using isIntegral_one⟩
  · exact ⟨zero_mem _, by simpa using isIntegral_zero⟩

theorem bd_mul (X : Tower Ω ε) {x y : X.K} (hx : Bd X x) (hy : Bd X y) : Bd X (x * y) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hx
  obtain ⟨S', D', hD', h'⟩ := hy
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ?_⟩
  have hS : IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hS' : IntermediateField.adjoin ℚ (S' : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right)
  rw [map_mul, HahnSeries.coeff_mul]
  refine ⟨sum_mem (fun ij _ => mul_mem (hS (h ij.1).1) (hS' (h' ij.2).1)), ?_⟩
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ (fun ij _ => ?_)
  have := (h ij.1).2.mul (h' ij.2).2
  convert this using 1
  push_cast; ring

theorem bd_prod (X : Tower Ω ε) {ι : Type} (s : Finset ι) (t : ι → X.K) (h : ∀ i ∈ s, Bd X (t i)) :
    Bd X (∏ i ∈ s, t i) :=
  Finset.prod_induction t (Bd X) (fun _ _ => bd_mul X) (bd_one X) h

end GlobalTheory.FracPrim

namespace GlobalTheory

open GlobalTheory.FracPrim

theorem exists_prim_frac_level_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ f : X.K, f ≠ 0 → ∃ (a b : X.K) (κ : Ω) (S : Finset Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) b = b) ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X hj l _ A hl f hf
  classical
  obtain ⟨M, hM, hfM⟩ := X.level f
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    simp [Nat.add_mod]
  have hcM : 6 * M + 1 ≡ 1 [MOD M] :=
    ((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm
  have hfG := GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits ε X hj M (6 * M + 1) hM hc1 hc6 hcM f hfM
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := IntermediateField.mem_adjoin_iff_div.mp hfG
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hPQ)
  have hfQ : f * Q = P := by rw [hPQ, div_mul_cancel₀ _ hQ0]
  obtain ⟨M', hM', hQM'⟩ := X.level Q
  haveI : NeZero M' := ⟨hM'.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M').Normal := CongruenceSubgroup.Gamma_normal M'
  haveI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M') := Fintype.ofFinite _
  have tq : ∀ g g' : SL(2, ℤ), g⁻¹ * g' ∈ CongruenceSubgroup.Gamma M' → X.sl (ofSL g') Q = X.sl (ofSL g) Q := by
    intro g g' h
    have hc : g * (g⁻¹ * g') * g⁻¹ ∈ CongruenceSubgroup.Gamma M' :=
      (CongruenceSubgroup.Gamma_normal M').conj_mem _ h g
    have e : g' = (g * (g⁻¹ * g') * g⁻¹) * g := by group
    rw [e, map_mul, X.sl_mul, hQM' _ hc]
  set t : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M' → X.K := fun q => X.sl (ofSL q.out) Q with ht
  set b0 : X.K := ∏ q, t q with hb0def
  have hb0 : ∀ δ : SL(2, ℤ), X.sl (ofSL δ) b0 = b0 := by
    intro δ
    rw [hb0def, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M')) _ _ (fun q => ?_)
    simp only [ht, Equiv.coe_mulRight]
    rw [← X.sl_mul, ← map_mul]
    symm
    apply tq
    rw [← QuotientGroup.eq]
    simp
  have ht1 : t 1 = Q := by
    simp only [ht]
    rw [tq 1 _ (by rw [← QuotientGroup.eq]; simp), map_one, X.sl_one]
  have hbd : ∀ γ : SL(2, ℤ), Bd X (X.sl (ofSL γ) Q) := fun γ =>
    GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM Q hQ γ
  have hPbd : Bd X P := by
    have := GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM P hP 1
    rwa [map_one, X.sl_one] at this
  set R : X.K := ∏ q ∈ Finset.univ.erase 1, t q with hR
  have hbR : b0 = R * Q := by
    rw [hb0def, hR, ← ht1, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have ha0 : f * b0 = P * R := by rw [hbR, ← hfQ]; ring
  have hb0bd : Bd X b0 := bd_prod X _ _ (fun q _ => hbd _)
  have ha0bd : Bd X (f * b0) := by
    rw [ha0]; exact bd_mul X hPbd (bd_prod X _ _ (fun q _ => hbd _))
  have hb0ne : b0 ≠ 0 := by
    rw [hb0def]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (map_ne_zero _).mpr hQ0)
  have ha0ne : f * b0 ≠ 0 := mul_ne_zero hf hb0ne
  obtain ⟨κa, hκa, hPa, Sa, hSa⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl (f * b0) ha0ne ha0bd
  obtain ⟨κb, hκb, hPb, Sb, hSb⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl b0 hb0ne hb0bd
  refine ⟨algebraMap Ω X.K κa * (f * b0), algebraMap Ω X.K κb * b0, κb / κa, Sa ∪ Sb, div_ne_zero hκb hκa, ?_, hPa, hPb,
    ?_, fun r => ⟨?_, ?_⟩⟩
  · have e : algebraMap Ω X.K (κb / κa) * algebraMap Ω X.K κa = algebraMap Ω X.K κb := by
      rw [← map_mul, div_mul_cancel₀ _ hκa]
    rw [← mul_assoc (algebraMap Ω X.K (κb / κa)), e]; ring
  · intro γ
    rw [map_mul, AlgEquiv.commutes, hb0]
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left) (hSa r)
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right) (hSb r)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankLeFinrankDirectSumBelow
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem finrank_nablaSq_eq_card (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    Module.finrank K (nablaSq K N lam) = Nat.card (ssIdx N N lam.natW) := by
  obtain ⟨b, ⟨hli, hb, -⟩, -⟩ := sSBasis K N N lam.natW
  have : Finite (ssIdx N N lam.natW) := (sSIdxFinite N N _).to_subtype
  have := Fintype.ofFinite (ssIdx N N lam.natW)
  unfold nablaSq
  rw [← hb, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

theorem finrank_le_finrank_directSum_below (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    Module.finrank ℂ (nablaSq ℂ N lam) ≤ Module.finrank ℂ (⨁ mu : Below h lam, nablaSq ℂ n mu.1) := by
  obtain ⟨F, hF⟩ := GlobalTheory.Branching.exists_ssIdx_injective n N h lam
  have := Fintype.ofFinite (Below h lam)
  have : ∀ mu : Below h lam, Finite (ssIdx n n mu.1.natW) := fun mu => (sSIdxFinite n n _).to_subtype
  rw [Module.finrank_directSum, finrank_nablaSq_eq_card]
  simp only [finrank_nablaSq_eq_card]
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective F hF

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HookREqHookProd
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.LiftSizeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

theorem telescope (a k b : ℕ) (hb : b ≤ a) :
    (∏ c ∈ Finset.range b, (a - c - 1 + (k + 1) + 1)) * (a - b + k + 1) =
      (∏ c ∈ Finset.range b, (a - c - 1 + k + 1)) * (a + k + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have h1 : a - b - 1 + (k + 1) + 1 = a - b + k + 1 := by omega
    have h2 : a - (b + 1) + k + 1 = a - b - 1 + k + 1 := by omega
    rw [h1, h2, ih (by omega)]
    ring

theorem row_hook (ν : ℕ → ℕ) (r k : ℕ) (hν : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x) :
    (∏ c ∈ Finset.range (ν r),
        ((ν r - c - 1) + ((Finset.Ioo r (r + 1 + k)).filter (fun r' => c < ν r')).card + 1)) *
      ∏ l ∈ Finset.Ioo r (r + 1 + k), (ν r - ν l + (l - r)) = (ν r + k).factorial := by
  induction k with
  | zero =>
    have he : Finset.Ioo r (r + 1 + 0) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.prod_empty, mul_one, Nat.add_zero]
    simp only [Finset.filter_empty, Finset.card_empty, add_zero]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    omega
  | succ k ih =>
    have hν' : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x := fun x y hxy hy => hν x y hxy (by omega)
    have IH := ih hν'
    set m := r + 1 + k with hm
    have hIns : Finset.Ioo r (r + 1 + (k + 1)) = insert m (Finset.Ioo r m) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hmn : m ∉ Finset.Ioo r m := by simp
    have hba : ν m ≤ ν r := hν r m (by omega) (by omega)
    have hcardIoo : (Finset.Ioo r m).card = k := by rw [Nat.card_Ioo]; omega
    rw [hIns, Finset.prod_insert hmn]
    rw [← Finset.prod_range_mul_prod_Ico _ hba] at IH ⊢
    have hlow : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + (k + 1) + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem (by simp),
        Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hlow' : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + k + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hhigh : ∀ c ∈ Finset.Ico (ν m) (ν r),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 := by
      intro c hc
      rw [Finset.mem_Ico] at hc
      rw [Finset.filter_insert, if_neg (by omega)]
    rw [Finset.prod_congr rfl hlow, Finset.prod_congr rfl hhigh]
    rw [Finset.prod_congr rfl hlow'] at IH
    have hT := telescope (ν r) k (ν m) hba
    have hd : ν r - ν m + (m - r) = ν r - ν m + k + 1 := by omega
    rw [hd, show ν r + (k + 1) = (ν r + k) + 1 by ring, Nat.factorial_succ, ← IH]
    calc (∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ((ν r - ν m + k + 1) * ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)))
        = ((∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) * (ν r - ν m + k + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)) := by ring
      _ = _ := by rw [hT]; ring

theorem hookProd_mul (n : ℕ) (ν : ℕ → ℕ) (hν : ∀ x y, x ≤ y → y < n → ν y ≤ ν x) :
    hookProd n ν * ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (ν r - ν l + (l - r)) =
      ∏ r ∈ Finset.range n, (ν r + n - 1 - r).factorial := by
  unfold hookProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have e : r + 1 + (n - 1 - r) = n := by omega
  have h := row_hook ν r (n - 1 - r) (fun x y hxy hy => hν x y hxy (by omega))
  rw [e] at h
  rw [h]
  congr 1
  omega

variable (D : D7) (L : SizeData₂ D)

variable {eps : ℝ} (Fm : FamP eps)

end GlobalTheory.LiftSizeCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlaceStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_has_basis_at_every_finite_place : BasisAtEx := by
  first | exact @GlobalTheory.LatBasisAt.basisAtEx | exact GlobalTheory.LatBasisAt.basisAtEx | (intros; apply GlobalTheory.LatBasisAt.basisAtEx <;> assumption)
end


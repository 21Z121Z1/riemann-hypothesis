import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def contr (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) :
    Fin d → E := fun j => ∑ i, X i j * (J *ᵥ fun m => σ (x m)) i

theorem hTens_eq_form (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) = form σ JB (contr σ JA X x) y := by
  unfold GlobalTheory.WeilM.hTens form contr
  simp only [Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hTens_smul_vec (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (c : E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec (c • x) y) = σ c * GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) := by
  unfold GlobalTheory.WeilM.hTens
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem decomp_sum (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E)
    (p f : Fin n → Fin n → E) (h : ∀ k l, form σ J (p k) (f l) = if k = l then 1 else 0) :
    X = ∑ k, Matrix.vecMulVec (p k) (contr σ J X (f k)) := by
  set P : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => p k i with hP
  set Q : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => (J *ᵥ fun m => σ (f k m)) i with hQ
  have h1 : Pᵀ * Q = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← h k l]
    simp [P, Q, form, dotProduct]
  have h2 : Q * Pᵀ = 1 := mul_eq_one_comm.mp h1
  have h3 : P * Qᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  ext i j
  have e : X i j = ((P * Qᵀ) * X) i j := by rw [h3, Matrix.one_mul]
  rw [e, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, contr, P, Q, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem incM_smul {m k : Type} (c : F) (Z : Matrix m k E) : incM F (c • Z) = algebraMap F (AF F) c • incM F Z := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def c, Algebra.smul_def (algebraMap F (AF F) c), map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes c

theorem inv_mem_O {v : Pl F} {t : 𝓞 F} (ht : t ∉ v.asIdeal) :
    algebraMap F (Fv F v) ((t : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (t : F) = 1 := by
    have := (v.valuation_eq_one_iff_notMem (K := F)).2 ht
    simpa using this
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : F)⁻¹)
  have h3 : v.valuation F (t : F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem sigma_surj (σ : E →ₐ[F] E) (o : 𝓞 E) : ∃ o' : 𝓞 E, σ (o' : E) = o := by
  obtain ⟨e, he⟩ := (AlgHom.bijective σ).2 (o : E)
  have hi : IsIntegral ℤ e := by
    have h : IsIntegral ℤ (σ e) := he ▸ NumberField.RingOfIntegers.isIntegral_coe o
    exact (isIntegral_algHom_iff (σ.restrictScalars ℤ) σ.injective).1 h
  exact ⟨⟨e, hi⟩, he⟩

theorem lemD (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : Pl F)
    (X₀ : Matrix (Fin n) (Fin d) E)
    (hint : ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v)
      (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y))) ∈ v.adicCompletionIntegers F) :
    GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  have hloc : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      IsIntegral ℤ (algebraMap F E (t : F) * GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) := by
    intro x hx y hy
    obtain ⟨t, ht, hti⟩ := GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace F E hun v (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) (fun o => by
      obtain ⟨o', ho'⟩ := sigma_surj σ o
      have hx' : (o' : E) • x ∈ X.L := X.L.smul_mem o' hx
      have h := hint _ hx' y hy
      rw [hTens_smul_vec, ho'] at h
      rwa [mul_neg])
    refine ⟨t, ht, ?_⟩
    have h := hti.neg
    rwa [mul_neg, neg_neg] at h
  obtain ⟨f, p, hf, hp, hpf⟩ := GlobalTheory.T.exists_basis_with_dual_basis_in_hermitian_lattice_away_place F E σ B X hX v
  have hw : ∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • contr σ X.J X₀ (f k) ∈ Y.L := by
    intro k
    obtain ⟨s0, hs0, hsf⟩ := hf k
    refine GlobalTheory.T.skewSelfDual_lattice_localised_at_place F E σ B Y hY v _ fun y hy => ?_
    obtain ⟨t, ht, hti⟩ := hloc _ hsf y hy
    refine ⟨t * s0, fun h => (v.isPrime.mem_or_mem h).elim ht hs0, ?_⟩
    rw [← hTens_eq_form]
    rw [hTens_smul_vec, AlgHom.commutes] at hti
    convert hti using 1
    rw [show ((t * s0 : 𝓞 F) : F) = (t : F) * (s0 : F) from rfl, map_mul]
    ring
  choose tw htw hwY using hw
  choose tp htp hpX using hp
  have hdec := decomp_sum σ X.J X₀ p f hpf
  rw [hdec]
  have hsum : incM F (∑ k, Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) =
      ∑ k, incM F (Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) := by
    ext i j
    simp [incM, Matrix.sum_apply, map_sum]
  rw [hsum, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
  have hc0 : (tp k * tw k : 𝓞 F) ∉ v.asIdeal := fun h => (v.isPrime.mem_or_mem h).elim (htp k) (htw k)
  have hne : (tp k * tw k : 𝓞 F) ≠ 0 := fun h => hc0 (h ▸ zero_mem _)
  have hcF : ((tp k * tw k : 𝓞 F) : F) ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast h0)
  have hcE : algebraMap F E ((tp k * tw k : 𝓞 F) : F) ≠ 0 := (map_ne_zero _).2 hcF
  have hvm : Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k)) = ((tp k * tw k : 𝓞 F) : F)⁻¹ •
      Matrix.vecMulVec (algebraMap F E (tp k : F) • p k) (algebraMap F E (tw k : F) • contr σ X.J X₀ (f k)) := by
    ext i j
    rw [show ((tp k * tw k : 𝓞 F) : F) = (tp k : F) * (tw k : F) from rfl] at hcE ⊢
    rw [map_mul] at hcE
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def ((tp k : F) * (tw k : F))⁻¹, map_inv₀, map_mul]
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hcE]
    ring
  refine ⟨GlobalTheory.EmbChart.atPlace v (algebraMap F (Fv F v) ((tp k * tw k : 𝓞 F) : F)⁻¹), GlobalTheory.VacAny.at_atPlace _, ?_, _,
    hpX k, _, hwY k, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]
    exact inv_mem_O hc0
  · rw [hvm, incM_smul, smul_smul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul, AlgHom.commutes]

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin z hz
  have hB := hT.base
  have hV' := hT.geo.hV'
  have hW := hT.geo.hW
  have h1v : evFin F v (1 : AF F) ∈ v.adicCompletionIntegers F := by rw [map_one]; exact one_mem _
  constructor
  · intro hzΓ γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v z hzΓ γ hγ
    simpa using h
  · intro hc
    obtain ⟨X₀, hX₀⟩ := GlobalTheory.T.matrix_adelic_decomposition_at_finite_place F E G.V' G.W hV'.lat hW.lat v z hz
    have hc₀ : ∀ γ ∈ latAtV G.V' G.W v, B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J)
        (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1 := by
      intro γ hγ
      have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v _ hX₀ γ hγ
      have hm : inclR (F := F) (AF F) (((-1 : 𝓞 E)) : E) = -1 := by simp
      rw [hm, one_mul] at h1
      have e : GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ = z + -(z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) := by abel
      rw [e, GlobalTheory.LatVacArith.symp_add_left, GlobalTheory.LatVacArith.symp_neg_left, AddChar.map_add_eq_mul,
        AddChar.map_neg_eq_inv, hc γ hγ, h1, inv_one, one_mul]
    have hint := GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial F E σ B.ψ G.V' G.W v (hB.inert v w hin).2.2 X₀ hc₀
    have hmem := lemD σ B G.V' G.W hB.unram hV' hW v X₀ hint
    have e : z = (z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) + GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ := by abel
    rw [e]
    exact add_mem hX₀ hmem

end GlobalTheory.InertDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertPlace

open GlobalTheory.IdemSupport

theorem inertQ_iff_cP {D : D7} {q : ℕ} (hq : q.Prime) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal) : Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ cP P = P := by
  constructor
  · intro hI
    exact ((isConjPl_iff P P).1 (GlobalTheory.XiSplit.isConjPl_of_smul_eq (hI P.asIdeal P.isPrime P.ne_bot hqP))).symm
  · intro hc
    by_contra h
    exact GlobalTheory.NormSum.VacInt.conj_smul_ne D hq h P.asIdeal P.isPrime hqP
      (GlobalTheory.XiSplit.smul_eq_of_isConjPl ((isConjPl_iff P P).2 hc.symm))

theorem nonSplitAt_iff_cP {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hη : IsPlaceIdem D v η) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = v) :
    GlobalTheory.WeilParts.NonSplitAt D v η ↔ cP P = P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hη
  constructor
  · rintro ⟨-, hns⟩
    by_contra hc
    obtain ⟨e, f, h⟩ := exists_isPrimeIdem hΦ P
    obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem hΦ h
    rw [hP] at hε
    have hεη := placeIdem_unique hε hη
    subst hεη
    rcases h with ⟨h, rfl⟩ | ⟨rfl, -, -⟩
    · exact hns ⟨e, h.1, hf⟩
    · have hd' := delta_conj hΦ hd
      rw [hf, cA_algebraMap, ← hf] at hd'
      have := hd'.2.2 P (Ne.symm hc)
      rw [hd.2.1] at this
      exact one_ne_zero this
  · intro hc
    refine ⟨hη, ?_⟩
    rintro ⟨e, ⟨ee, ec, -⟩, hs⟩
    have he : e * algebraMap (AF D.host.F) (AE D) η = e := by
      rw [← hs, mul_add, ee, ec, add_zero]
    have hi : infPart D e = 0 := by
      rw [← he, RingHom.map_mul, h0, mul_zero]
    have hout : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q ≠ P → Φ e Q = 0 := by
      intro Q hQ
      have hQv : Q.under (𝓞 D.host.F) ≠ v := by
        intro hv
        rcases eq_or_eq_cP (hv.trans hP.symm) with h | h
        · exact hQ h
        · exact hQ (h.trans hc)
      rw [← he, ev_mul, h2 Q hQv, mul_zero]
    have hPP : Φ e P * Φ e P = Φ e P := by rw [← ev_mul, ee]
    have h01 : Φ e P = 0 ∨ Φ e P = 1 := by
      have : Φ e P * (Φ e P - 1) = 0 := by rw [mul_sub, hPP, mul_one, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    rcases h01 with h | h
    · have e0 : e = 0 := by
        refine hΦ.ext e hi (FiniteAdeleRing.ext _ fun Q => ?_)
        by_cases hQ : Q = P
        · subst hQ; rw [h]; rfl
        · rw [hout Q hQ]; rfl
      have := h1 P hP
      rw [← hs, e0, map_zero, add_zero, ev_zero] at this
      exact zero_ne_one this
    · have hd : IsDelta Φ P e := ⟨hi, h, hout⟩
      have hd' := delta_conj hΦ hd
      rw [hc] at hd'
      have hce := delta_unique hΦ hd' hd
      rw [hce, ee] at ec
      rw [ec, ev_zero] at h
      exact zero_ne_one h

theorem inertQ_iff_nonSplitAt : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
    (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  intro D q hq v η hη hqv
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  have hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h : (q : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by rw [hP]; exact hqv
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal at h
    rwa [map_natCast] at h
  rw [inertQ_iff_cP hq P hqP, nonSplitAt_iff_cP hη P hP]

end GlobalTheory.InertPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDdcClosedFormZero
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxFormStokes

theorem integral_ddc_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (η Z : A.Fld), A.IsForm η → A.IsForm Z → A.del Z = 0 →
    A.dbar Z = 0 → A.integral (A.ddc η * Z) = 0 := by
  intro M _ _ _ _ _ _ n A η Z hη hZ hdZ _
  have hdη := GlobalTheory.T.isForm_dbar' A η hη
  have hγ := GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ hdη hZ
  obtain ⟨hγ', hdel⟩ := GlobalTheory.T.isForm_smul_del_smul A GlobalTheory.HermFrame.kappa _ hγ
  have e1 : A.ddc η * Z = A.del (GlobalTheory.HermFrame.kappa • (A.dbar η * Z)) := by
    rw [hdel, GlobalTheory.T.del_mul_of_del_eq_zero' A _ _ hdη hZ hdZ, GlobalTheory.CxForm.HolAtlas.ddc, smul_mul_assoc]
  rw [e1]
  set γ := GlobalTheory.HermFrame.kappa • (A.dbar η * Z)
  obtain ⟨N, c, χ, hχs, hχt, hχ1⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * γ) := fun j => GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ (A.isForm_fn (hχs j)) hγ'
  have hsum : γ = ∑ j, A.fn (χ j) * γ := by
    rw [← Finset.sum_mul]
    funext x
    simp only [Finset.sum_apply, Pi.mul_apply, GlobalTheory.CxForm.HolAtlas.fn, ← map_sum]
    rw [show (∑ j, ((χ j x.pt : ℝ) : ℂ)) = 1 by exact_mod_cast hχ1 x.pt, map_one, one_mul]
  rw [hsum, GlobalTheory.T.holAtlas_del_finset_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ fun j => GlobalTheory.T.holAtlas_isForm_del A _ (hf j)]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A γ (χ j) (c j) hγ' (hχs j) (hχt j)

end GlobalTheory.CxFormStokes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameSpanCompletedEigenLattice
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL
  exact ⟨GlobalTheory.T.cm_point_integral_frame_mem_span_eigen_lattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL,
    GlobalTheory.T.completed_eigenLattice_le_span_integral_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C a y' hC hL⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqVolMulClassSum
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
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.BotClassMeas

open GlobalTheory.BotClassDict GlobalTheory.DefiniteClassAvg GlobalTheory.BotFormula

theorem isFrame_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Formalism.L2.Col.stdLat E n) := by
  letI : StarRing E := starRingOfComm
  intro z
  rw [inv_one, Units.val_one, Matrix.one_mulVec]
  exact Formalism.L2.Col.mem_latS_std z

variable {D : D7}

theorem isFinPt_finPart (A : HSp D) (hG : A.gram = 1) (k : Formalism.L2.Theta.GA D A) :
    IsFinPt A (finPart A k) (finStd A hG k) := by
  have h1 : finHom A (realPart A k) = 1 := realPart_mem A k
  have h2 : finHom A (finPart A k) = finHom A k := by
    conv_rhs => rw [← realPart_mul_finPart A k]
    rw [map_mul, h1, one_mul]
  refine ⟨finPart_mem A k, rfl, fun i j => ?_⟩
  rw [h2, ← finAdEquiv_toAfE, ← toAfE_finStd A hG]
  rfl

theorem integral_eq_vol_mul_classSum : ∀ {D : D7} (A : HSp D), A.gram = 1 → ∀ (m : Measure (Formalism.L2.Theta.GA D A)) (fd : Set (Formalism.L2.Theta.GA D A)),
    m.IsHaarMeasure → IsFundamentalDomain (GQ A) fd m →
    ∃ v : ℂ, v ≠ 0 ∧ ∀ (n : ℕ), n = A.rank → ∀ (pt : Formalism.MainNotions.StandardLatticesGL3.GA D n → Formalism.L2.Theta.GA D A),
      (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ Φ : Formalism.L2.Theta.GA D A → ℂ,
      (∀ γ ∈ GQ A, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ GinfC A, ∀ h, Φ (h * k) = Φ h) →
      (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D n) (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ h, Φ (h * k) = Φ h) →
      ∫ g in fd, Φ g ∂m = v * ∑ᶠ x : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n),
        ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out : ℂ))⁻¹ * Φ (pt x.out) := by
  intro D A hA m fd hm hfd
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hA, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (Formalism.L2.Theta.GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  let J : Subgroup (Formalism.L2.Theta.GA D A) :=
    (Formalism.L2.DIV.St (1 : GL (Fin A.rank) (Lev.EAf D))).comap (Lev.finE A)
  have hJ : ∀ g, g ∈ J ↔ finStd A hA g ∈ GlobalTheory.NormSum.intG D A.rank := mem_level_iff A hA (isFrame_one _)
  have hJo : IsOpen (J : Set (Formalism.L2.Theta.GA D A)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A 1 ∅] with κ hh
    exact hh.2.1
  have hJc : IsCompact (J : Set (Formalism.L2.Theta.GA D A)) := by
    obtain ⟨C, hCc, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A 1
    refine (hCc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hJo) ?_
    intro k hk
    refine ⟨finPart A k, hCm _ (finPart_mem A k) ?_, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
    rw [finE_finPart]
    exact hk
  have hJtop : m J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : m J ≠ 0 := (hJo.measure_pos m ⟨1, J.one_mem⟩).ne'
  refine ⟨((m J).toReal : ℂ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hJ0 hJtop).ne', ?_⟩
  intro n hn pt hpt Φ hl hinf hlev
  subst hn
  haveI : Finite (GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank)) := (GlobalTheory.NormSum.cls_finite_card_le D A.rank).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank))
  let z : GlobalTheory.NormSum.Cls D A.rank (GlobalTheory.NormSum.intG D A.rank) → Formalism.L2.Theta.GA D A := fun x => pt x.out
  obtain ⟨hu, hcard⟩ := transport (finStd A hA) (GQ A) J (GlobalTheory.NormSum.ratG D A.rank) (GlobalTheory.NormSum.intG D A.rank)
    hJ (fun γ hγ => finStd_mem_ratG A hA hγ) (fun δ hδ => exists_rat_lift A hA hδ)
    (fun γ hγ γ' hγ' h => finStd_injOn A hA hγ hγ' h) z (fun x => finStd_of_isFinPt A hA (hpt _))
  have hfin : ∀ l, {γ : Formalism.L2.Theta.GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l => by
    have him : {γ : Formalism.L2.Theta.GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
        Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : Formalism.L2.Theta.GA D A) * z l ∈ J} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact (GlobalTheory.InnerClassSum.finite_stab_of_measure m (GQ A) J hfd hJ0 hJtop (z l)).image _
  have hr : ∀ k ∈ J, ∀ h, Φ (h * k) = Φ h := fun k hk h => by
    rw [← finPart_mul_realPart A k, ← mul_assoc, hinf _ (realPart_mem A k),
      hlev _ _ ((hJ k).1 hk) (isFinPt_finPart A hA k)]
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (Formalism.L2.Theta.GA D A) m (GQ A) J fd hfd hJo
    hJtop _ z hu hfin Φ hl hr
  rw [heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]
  rfl

end GlobalTheory.BotClassMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConst_seesawTriple_transport_isometries : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  first | exact @GlobalTheory.TriMoveConst.isConst_triMove | exact GlobalTheory.TriMoveConst.isConst_triMove | (intros; apply GlobalTheory.TriMoveConst.isConst_triMove <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTeStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
  first | exact @GlobalTheory.ResidueEisenstein.reps_perm | exact GlobalTheory.ResidueEisenstein.reps_perm | (intros; apply GlobalTheory.ResidueEisenstein.reps_perm <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnit
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SkewNorm

theorem exists_norm_eq {R : Type} [CommRing R] (c : R →+* R) (a : R) (ha : c a = -a) (B B' : Ideal R)
    (hsup : B ⊔ B' = ⊤) (h1 : ∀ x ∈ B, c x ∈ B') (h2 : ∀ y ∈ B', c y ∈ B)
    (hP : ∀ P : Ideal R, P.IsPrime → a ∈ P → B ≤ P ∨ B' ≤ P) (hcc : ∀ x, c (c x) = x) :
    ∃ α η : R, α * c α = a * η ∧ IsCoprime η a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
  have hrad : x * c x ∈ (Ideal.span {a}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hp⟩
    rcases hP P hp (hle (Ideal.mem_span_singleton_self a)) with h | h
    · exact P.mul_mem_right _ (h hx)
    · exact P.mul_mem_left _ (h (h1 x hx))
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hn
  have hN : x ^ (2 * n + 1) * c x ^ (2 * n + 1) = a ^ 2 * (k ^ 2 * (x * c x)) := by
    rw [← mul_pow, pow_succ, mul_comm 2 n, pow_mul, ← hk]; ring
  refine ⟨x ^ (2 * n + 1) + a, c x ^ (2 * n + 1) - x ^ (2 * n + 1) + a * (k ^ 2 * (x * c x) - 1), ?_, ?_⟩
  · rw [map_add, map_pow, ha]; linear_combination hN
  · rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hp := hPm.isPrime
    have haP : a ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
    have hη := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    have hd : c x ^ (2 * n + 1) - x ^ (2 * n + 1) ∈ P := by
      have := P.sub_mem hη (P.mul_mem_right (k ^ 2 * (x * c x) - 1) haP)
      rwa [add_sub_cancel_right] at this
    refine hp.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rcases hP P hp haP with h | h
    · have : c x ∈ P := hp.mem_of_pow_mem (2 * n + 1)
        (by simpa using P.add_mem hd (P.pow_mem_of_mem (h hx) (2 * n + 1) (by omega)))
      rw [← map_one c, ← hxy, map_add]
      exact P.add_mem this (h (h2 y hy))
    · have : x ∈ P := hp.mem_of_pow_mem (2 * n + 1)
        (by simpa using P.sub_mem (P.pow_mem_of_mem (h (h1 x hx)) (2 * n + 1) (by omega)) hd)
      rw [← hxy]
      exact P.add_mem this (h hy)

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_natCast_mem (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : (n : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (Fv F v) (n : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (algebraMap (𝓞 F) F n) = 1 := by
    refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h' => hn ?_)
    exact (v.valuation_lt_one_iff_mem _).1 h'
  rw [map_natCast] at h1
  have h2 := v.valuedAdicCompletion_eq_valuation' (n : F)⁻¹
  exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))

omit [NumberField E] in

theorem inv_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : (n : 𝓞 F) ∉ v.asIdeal) [CharZero E] (x y : 𝓞 E)
    (h : x * y = n) : (1 : Fv F v) ⊗ₜ[F] (x : E)⁻¹ ∈ intLoc F E v := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have h' : (x : E) * y = n := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) h
  have hx : (x : E) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h'; exact hn0 (by exact_mod_cast h'.symm)
  have : (x : E)⁻¹ = (n : F)⁻¹ • (y : E) := by
    rw [Algebra.smul_def, map_inv₀, map_natCast, ← h']
    have hy : (y : E) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h'; exact hn0 (by exact_mod_cast h'.symm)
    field_simp
  rw [this, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  exact tmul_mem_intLoc (inv_natCast_mem v n hn) y

open Classical in

noncomputable def idemAt (F : Type) [Field F] [NumberField F] (q : ℕ) : AF F :=
  (0, ⟨fun v => if (q : 𝓞 F) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    dsimp only
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem⟩)

open Classical in
theorem evFin_idemAt (q : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (idemAt F q) = if (q : 𝓞 F) ∈ v.asIdeal then 1 else 0 := rfl

theorem idemAt_mul (q : ℕ) : idemAt F q * idemAt F q = idemAt F q := by
  refine Prod.ext (mul_zero _) (DFunLike.ext _ _ fun v => ?_)
  change evFin F v (idemAt F q) * evFin F v (idemAt F q) = evFin F v (idemAt F q)
  rw [evFin_idemAt]
  split_ifs <;> simp

omit [NumberField E] in
theorem glue_mul (q : ℕ) (x y x' y' : E) :
    (idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] y) * (idemAt F q ⊗ₜ[F] x' + (1 - idemAt F q) ⊗ₜ[F] y') =
      idemAt F q ⊗ₜ[F] (x * x') + (1 - idemAt F q) ⊗ₜ[F] (y * y') := by
  have h := idemAt_mul (F := F) q
  have h1 : idemAt F q * (1 - idemAt F q) = 0 := by linear_combination -h
  have h2 : (1 - idemAt F q) * idemAt F q = 0 := by linear_combination -h
  have h3 : (1 - idemAt F q) * (1 - idemAt F q) = 1 - idemAt F q := by linear_combination h
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, h, h1, h2, h3, TensorProduct.zero_tmul,
    add_zero, zero_add]

omit [NumberField E] in
theorem glue_self (q : ℕ) (x : E) :
    idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] x = (1 : AF F) ⊗ₜ[F] x := by
  rw [← TensorProduct.add_tmul, add_sub_cancel]

noncomputable def glue (q : ℕ) (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) : (AF F ⊗[F] E)ˣ where
  val := idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] y
  inv := idemAt F q ⊗ₜ[F] x⁻¹ + (1 - idemAt F q) ⊗ₜ[F] y⁻¹
  val_inv := by rw [glue_mul, mul_inv_cancel₀ hx, mul_inv_cancel₀ hy, glue_self]; rfl
  inv_val := by rw [glue_mul, inv_mul_cancel₀ hx, inv_mul_cancel₀ hy, glue_self]; rfl

omit [NumberField E] in
theorem glue_mem (q : ℕ) (x y : E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (q : 𝓞 F) ∈ v.asIdeal → (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v)
    (h2 : (q : 𝓞 F) ∉ v.asIdeal → (1 : Fv F v) ⊗ₜ[F] y ∈ intLoc F E v) :
    compFin F E v (idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] y) ∈ intLoc F E v := by
  have e : ∀ (a : AF F) (z : E), compFin F E v (a ⊗ₜ[F] z) = evFin F v a ⊗ₜ[F] z := fun _ _ => rfl
  rw [map_add, e, e, map_sub, map_one, evFin_idemAt]
  split_ifs with h
  · simpa using h1 h
  · simpa using h2 h

theorem exists_idele (σ : E →ₐ[F] E) (q : ℕ) (hq : 1 < q) (a α η : 𝓞 E) (ha : a ^ 2 = -(q : 𝓞 E))
    (hα : (α : E) * σ α = a * η) (hcop : IsCoprime η a) (hu : ¬ IsUnit a) :
    ∃ u ε : (AF F ⊗[F] E)ˣ, (ε : AF F ⊗[F] E) * u * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u = (1 : AF F) ⊗ₜ[F] (a : E) ∧
      (∀ v, compFin F E v ε ∈ intLoc F E v) ∧ ∀ v, compFin F E v (ε⁻¹ : (AF F ⊗[F] E)ˣ) ∈ intLoc F E v := by
  have hη : η ≠ 0 := by rintro rfl; exact hu (isCoprime_zero_left.1 hcop)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : (q : 𝓞 E) = 0 := by simpa using ha
    exact absurd (by exact_mod_cast this : q = 0) (by omega)
  have hηE : (η : E) ≠ 0 := by simpa using hη
  have haE : (a : E) ≠ 0 := by simpa using ha0
  have hαE : (α : E) ≠ 0 := by
    intro h; rw [h, zero_mul] at hα; exact mul_ne_zero haE hηE hα.symm
  obtain ⟨k, hk, d, hd⟩ : ∃ k : ℕ, 0 < k ∧ η ∣ (q : 𝓞 E) ^ k - 1 := by
    haveI : Finite (𝓞 E ⧸ Ideal.span {η}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hη)
    have hcq : IsCoprime η (q : 𝓞 E) := by
      have := (hcop.pow_right (n := 2)).neg_right
      rwa [ha, neg_neg] at this
    have hu' : IsUnit (Ideal.Quotient.mk (Ideal.span {η}) (q : 𝓞 E)) := by
      obtain ⟨s, t, e⟩ := hcq
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ t) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨-s, by linear_combination e⟩
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu'.unit)
    refine ⟨k, hk, ?_⟩
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  refine ⟨glue q (α : E) 1 hαE one_ne_zero, glue q (η : E)⁻¹ a (inv_ne_zero hηE) haE, ?_, fun v => ?_, fun v => ?_⟩
  · have e : ∀ (b : AF F) (z : E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (b ⊗ₜ[F] z) = b ⊗ₜ[F] σ z := fun _ _ => rfl
    simp only [glue]
    rw [map_add, e, e, glue_mul, glue_mul, map_one, mul_one, mul_one, mul_assoc, hα,
      show (η : E)⁻¹ * (a * η) = a by field_simp, glue_self]
  · refine glue_mem q _ _ v (fun h => inv_mem_intLoc v (q ^ k - 1) (fun h' => ?_) η d ?_)
      fun _ => tmul_mem_intLoc (one_mem _) a
    · rw [Nat.cast_sub h1] at h'
      push_cast at h'
      refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      simpa using v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h k hk) h'
    · rw [Nat.cast_sub h1, ← hd]; push_cast; rfl
  · refine glue_mem q _ _ v (fun _ => ?_) fun h => inv_mem_intLoc v q h a (-a) (by linear_combination -ha)
    rw [inv_inv]
    exact tmul_mem_intLoc (one_mem _) η

end Adelic

theorem different_le (D : D7) (a : 𝓞 D.host.E) (ha : a ^ 2 = -(D.host.q : 𝓞 D.host.E)) (P : Ideal (𝓞 D.host.E))
    (hp : P.IsPrime) (haP : a ∈ P) : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≤ P := by
  have hq := D.host.hyp.1
  have hqP : (D.host.q : 𝓞 D.host.E) ∈ P ^ 2 := by
    rw [← neg_mem_iff, ← ha]; exact Ideal.pow_mem_pow haP 2
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_pow (by norm_num), Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  haveI := hp.isMaximal hP0
  haveI : Fact D.host.q.Prime := ⟨hq⟩
  haveI : (Ideal.span {(D.host.q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have h2 := pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(D.host.q : ℤ)}) P 2 (by simpa using hq.ne_zero)
    (by rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_le_iff_mem]
        exact hqP)
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E), Ideal.dvd_iff_le] at h2
  norm_num at h2
  refine (hp.mul_le.1 h2).resolve_right fun h => ?_
  have hd := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.K))
  rw [absNorm_differentIdeal D.host.K, GlobalTheory.CurveLattice.discr_hostK] at hd
  have hd' := h (Ideal.mem_map_of_mem _ hd)
  rw [map_natCast, Int.natAbs_neg, Int.natAbs_natCast] at hd'
  have hne : D.host.q ≠ D.host.d := by
    have := D.host.hyp.2.2.1; have := D.host.hyp.2.2.2.1; omega
  obtain ⟨s, t, e⟩ : IsCoprime (D.host.q : 𝓞 D.host.E) (D.host.d : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hq D.host.hyp.2.1).2 hne)
  exact hp.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ add_mem (P.mul_mem_left s (Ideal.pow_le_self two_ne_zero hqP)) (P.mul_mem_left t hd')))

theorem exists_skew_norm_mul_unit : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) := by
  intro D
  have hs : ∀ x : D.host.E, star x = D.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj D.host
  have hsq := Formalism.BasicNotions.Examples₂.aE_sq D.host
  have hc := Formalism.BasicNotions.Examples₂.conj_aE D.host
  set a₀ := D.host.sqq
  have hq := D.host.hyp.1
  have hint : IsIntegral ℤ a₀ := IsIntegral.of_pow two_pos (by rw [hsq]; exact (isIntegral_natCast _).neg)
  set a : 𝓞 D.host.E := ⟨a₀, hint⟩
  have ha : a ^ 2 = -(D.host.q : 𝓞 D.host.E) := RingOfIntegers.ext (by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]; exact hsq)
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E := MulSemiringAction.toRingHom _ _ D.host.conj
  have hcv : ∀ x, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun x => (hs x).symm
  have hcc : ∀ x, c (c x) = x := fun x => RingOfIntegers.ext (by rw [hcv, hcv, star_star])
  obtain ⟨α, η, e, hcop⟩ := exists_norm_eq c a (RingOfIntegers.ext hc) D.host.𝔟 _ D.host.𝔟_spec.2
    (fun x hx => Ideal.smul_mem_pointwise_smul _ _ _ hx)
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective c (fun z => ⟨c z, hcc z⟩)).1 hy
      rwa [hcc])
    (fun P hp haP => hp.mul_le.1 (D.host.𝔟_spec.1 ▸ different_le D a ha P hp haP)) hcc
  have hu : ¬ IsUnit a := fun h => by
    have h2 : IsUnit (D.host.q : 𝓞 D.host.E) := by
      have := (h.pow 2).neg
      rwa [ha, neg_neg] at this
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 h2)
    rw [Ideal.absNorm_span_natCast] at h1
    exact Module.finrank_pos.ne' ((Nat.pow_eq_one.1 h1).resolve_left hq.one_lt.ne')
  refine ⟨a₀, ⟨fun h => hq.ne_zero ?_, (hs _).trans hc⟩, exists_idele D.sp.cm.sig _ hq.one_lt a α η ha ?_ hcop hu⟩
  · rw [h] at hsq
    exact_mod_cast (by simpa using hsq : (D.host.q : D.host.E) = 0)
  · have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at this
    exact (congrArg _ (hcv α).symm).trans this

end GlobalTheory.StdUnn.SkewNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramifiedStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_spherical_doubling_section_unramified : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  first | exact @GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique | exact GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique | (intros; apply GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIsometryIsotropicFrameLocalRing
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.WittFrame

open Matrix

variable {O : Type} [CommRing O]

theorem cT_mul_r (s : O →+* O) {a b c : Type} [Fintype b] (M : Matrix a b O) (N : Matrix b c O) :
    Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_r (s : O →+* O) {a : Type} [DecidableEq a] : Formalism.UG.cT s (1 : Matrix a a O) = 1 := by
  ext i j; by_cases h : i = j <;> simp [Formalism.UG.cT, Matrix.one_apply, h, eq_comm]

theorem cT_zero_r (s : O →+* O) {a b : Type} : Formalism.UG.cT s (0 : Matrix a b O) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub_r (s : O →+* O) {a b : Type} (M N : Matrix a b O) :
    Formalism.UG.cT s (M - N) = Formalism.UG.cT s M - Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_r {s : O →+* O} (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b O) :
    Formalism.UG.cT s (Formalism.UG.cT s M) = M := by
  ext i j; exact hs _

theorem cT_fromCols_r (s : O →+* O) {a b c : Type} (X : Matrix a b O) (Y : Matrix a c O) :
    Formalism.UG.cT s (fromCols X Y) = fromRows (Formalism.UG.cT s X) (Formalism.UG.cT s Y) := by
  ext (i | i) j <;> rfl

theorem assoc3 {a b c d : Type} [Fintype b] [Fintype c] {X : Matrix a b O} {Y : Matrix b c O}
    {Z : Matrix c d O} {V : Matrix a d O} (h : X * Y * Z = V) : X * (Y * Z) = V := by
  rw [← Matrix.mul_assoc, h]

theorem tail3 {a b c d : Type} [Fintype b] [Fintype c] [Fintype d] {X : Matrix a b O} {Y : Matrix b c O}
    {Z : Matrix c d O} {V : Matrix a d O} (h : X * Y * Z = V) {p : Type} (W : Matrix d p O) :
    X * (Y * (Z * W)) = V * W := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

theorem tail2 {a b c : Type} [Fintype b] [Fintype c] {X : Matrix a b O} {Y : Matrix b c O}
    {V : Matrix a c O} (h : X * Y = V) {p : Type} (W : Matrix c p O) : X * (Y * W) = V * W := by
  rw [← Matrix.mul_assoc, h]

theorem idem_factor [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι O) (hP : P * P = P) :
    ∃ (m : ℕ) (B : Matrix ι (Fin m) O) (B' : Matrix (Fin m) ι O), B' * B = 1 ∧ B * B' = P := by
  have hfix : ∀ y ∈ LinearMap.range (Matrix.mulVecLin P), P *ᵥ y = y := by
    rintro y ⟨w, rfl⟩
    show P *ᵥ (P *ᵥ w) = P *ᵥ w
    rw [mulVec_mulVec, hP]
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) := by
    refine Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype
      (Matrix.mulVecLin P).rangeRestrict ?_
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hfix _ x.2
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  set b := Module.finBasis O (LinearMap.range (Matrix.mulVecLin P)) with hb
  have hmul : ∀ c : Fin _ → O, (Matrix.of fun x i => (b i : ι → O) x) *ᵥ c =
      ((b.equivFun.symm c : LinearMap.range (Matrix.mulVecLin P)) : ι → O) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    funext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hres : ∀ y : LinearMap.range (Matrix.mulVecLin P), (Matrix.mulVecLin P).rangeRestrict (y : ι → O) = y :=
    fun y => Subtype.ext (hfix _ y.2)
  refine ⟨_, Matrix.of fun x i => (b i : ι → O) x,
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.mulVecLin P).rangeRestrict), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro c
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply,
      hmul, LinearMap.comp_apply, hres]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply, hmul,
      LinearMap.comp_apply]
    simp

theorem card_eq_of_inv [Nontrivial O] {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {S : Matrix b a O} {T : Matrix a b O} (h1 : S * T = 1) (h2 : T * S = 1) : Fintype.card a = Fintype.card b := by
  let e : (b → O) ≃ₗ[O] (a → O) := LinearEquiv.ofLinear (Matrix.toLin' T) (Matrix.toLin' S)
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
  have := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem exists_completion [IsLocalRing O] {s : O →+* O} (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1)
    (hnorm : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    {n r : ℕ} {Q : Matrix (Fin n) (Fin n) O} (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q)
    {C : Matrix (Fin n) (Fin r) O} {L : Matrix (Fin r) (Fin n) O} (hL : L * C = 1)
    (hC : Formalism.UG.cT s C * Q * C = 0) :
    ∃ (m : ℕ) (T : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) O) (S : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) (Fin n) O),
      S * T = 1 ∧ T * S = 1 ∧
      Formalism.UG.cT s T * Q * T = fromBlocks (fromBlocks 0 1 1 0) 0 0 1 ∧
      T * (fromRows (fromRows (1 : Matrix (Fin r) (Fin r) O) 0) (0 : Matrix (Fin m) (Fin r) O) :
        Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) (Fin r) O) = C := by
  obtain ⟨Z, h1, h2, h3⟩ := GlobalTheory.InertIwasawa.exists_dual_isotropic hs hτ hQ hu hL hC
  have key : ∀ {a b : Type} [Fintype a] [Fintype b] (X : Matrix (Fin n) a O) (X' : Matrix (Fin n) b O),
      Formalism.UG.cT s (Formalism.UG.cT s X * Q * X') = Formalism.UG.cT s X' * Q * X := fun X X' => by
    rw [cT_mul_r, cT_mul_r, cT_cT_r hs, hQ, Matrix.mul_assoc]
  obtain ⟨π, hπ⟩ : ∃ π : Matrix (Fin n) (Fin n) O,
      π = 1 - C * (Formalism.UG.cT s Z * Q) - Z * (Formalism.UG.cT s C * Q) := ⟨_, rfl⟩
  have hπC : π * C = 0 := by
    rw [hπ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, assoc3 h2, assoc3 hC, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have hπZ : π * Z = 0 := by
    rw [hπ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, assoc3 h3, assoc3 h1, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have hCπ : Formalism.UG.cT s C * Q * π = 0 := by
    rw [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, tail3 hC, tail3 h1, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, sub_self]
  have hZπ : Formalism.UG.cT s Z * Q * π = 0 := by
    rw [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, tail3 h2, tail3 h3, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, sub_self]
  have hππ : π * π = π := by
    nth_rewrite 2 [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, tail2 hπC, tail2 hπZ, Matrix.zero_mul, sub_zero]
  have hπQ : Formalism.UG.cT s π * Q = Q * π := by
    rw [hπ]
    simp only [cT_sub_r, cT_one_r, cT_mul_r, cT_cT_r hs, hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
    abel
  obtain ⟨m, B0, B0', hB0, hB0π⟩ := idem_factor π hππ
  have hBπ0 : π * B0 = B0 := by rw [← hB0π, Matrix.mul_assoc, hB0, Matrix.mul_one]
  have hG : Formalism.UG.cT s B0 * Q * B0 * (B0' * (hu.unit⁻¹).1 * Formalism.UG.cT s B0') = 1 := by
    calc Formalism.UG.cT s B0 * Q * B0 * (B0' * (hu.unit⁻¹).1 * Formalism.UG.cT s B0')
          = Formalism.UG.cT s B0 * (Q * π) * (hu.unit⁻¹).1 * Formalism.UG.cT s B0' := by
            rw [← hB0π]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s B0 * Formalism.UG.cT s π * (Q * (hu.unit⁻¹).1) * Formalism.UG.cT s B0' := by
            rw [← hπQ]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s (π * B0) * Formalism.UG.cT s B0' := by
            rw [hu.mul_val_inv, Matrix.mul_one, cT_mul_r]
      _ = 1 := by rw [hBπ0, ← cT_mul_r, hB0, cT_one_r]
  have hGu : IsUnit (Formalism.UG.cT s B0 * Q * B0) :=
    ⟨⟨_, _, hG, mul_eq_one_comm.mp hG⟩, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_orthonormal_basis_unimodular_hermitian_local_ring O s hs ⟨τ, hτ⟩ hnorm m (Formalism.UG.cT s B0 * Q * B0) (key B0 B0) hGu
  obtain ⟨B, B', hB, hBB, hBg⟩ : ∃ (B : Matrix (Fin n) (Fin m) O) (B' : Matrix (Fin m) (Fin n) O),
      B' * B = 1 ∧ B * B' = π ∧ Formalism.UG.cT s B * Q * B = 1 := by
    refine ⟨B0 * a.1, (a⁻¹).1 * B0', ?_, ?_, ?_⟩
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B0', hB0, Matrix.one_mul, Units.inv_mul]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc a.1, Units.mul_inv, Matrix.one_mul, hB0π]
    · rw [← ha, cT_mul_r]; simp only [Matrix.mul_assoc]
  have hπB : π * B = B := by rw [← hBB, Matrix.mul_assoc, hB, Matrix.mul_one]
  have hB'π : B' * π = B' := by rw [← hBB, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hCB : Formalism.UG.cT s C * Q * B = 0 := by rw [← hπB, ← Matrix.mul_assoc, hCπ, Matrix.zero_mul]
  have hZB : Formalism.UG.cT s Z * Q * B = 0 := by rw [← hπB, ← Matrix.mul_assoc, hZπ, Matrix.zero_mul]
  have hB'C : B' * C = 0 := by rw [← hB'π, Matrix.mul_assoc, hπC, Matrix.mul_zero]
  have hB'Z : B' * Z = 0 := by rw [← hB'π, Matrix.mul_assoc, hπZ, Matrix.mul_zero]
  have hBC : Formalism.UG.cT s B * Q * C = 0 := by rw [← key, hCB, cT_zero_r]
  have hBZ : Formalism.UG.cT s B * Q * Z = 0 := by rw [← key, hZB, cT_zero_r]
  refine ⟨m, fromCols (fromCols C Z) B, fromRows (fromRows (Formalism.UG.cT s Z * Q) (Formalism.UG.cT s C * Q)) B',
    ?_, ?_, ?_, ?_⟩
  · simp only [fromRows_mul_fromCols, fromRows_mul, mul_fromCols, h1, h2, h3, hC, hCB, hZB, hB'C, hB'Z, hB]
    ext (((i|i)|i)) (((j|j)|j)) <;> simp [Matrix.one_apply]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, hBB, hπ]
    abel
  · rw [cT_fromCols_r, cT_fromCols_r]
    simp only [fromRows_mul, mul_fromCols, h1, h2, h3, hC, hCB, hZB, hBC, hBZ, hBg]
    ext (((i|i)|i)) (((j|j)|j)) <;> simp
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows]
    simp

theorem exists_isometry_frame : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n r : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∀ C C' : Matrix (Fin n) (Fin r) O, (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) → (∃ L : Matrix (Fin r) (Fin n) O, L * C' = 1) → Formalism.UG.cT s C * Q * C = 0 → Formalism.UG.cT s C' * Q * C' = 0 → ∃ k : GL (Fin n) O, Formalism.UG.cT s k.1 * Q * k.1 = Q ∧ k.1 * C = C' := by
  intro O _ _ s hs hτ hnorm n r Q hQ hu C C' hL hL' hC hC'
  obtain ⟨τ, hτ⟩ := hτ
  obtain ⟨L, hL⟩ := hL
  obtain ⟨L', hL'⟩ := hL'
  obtain ⟨m, T, S, h1, h2, h3, h4⟩ := exists_completion hs hτ hnorm hQ hu hL hC
  obtain ⟨m', T', S', h1', h2', h3', h4'⟩ := exists_completion hs hτ hnorm hQ hu hL' hC'
  have hm : m = m' := by
    have e1 := card_eq_of_inv h1 h2
    have e2 := card_eq_of_inv h1' h2'
    simp only [Fintype.card_sum, Fintype.card_fin] at e1 e2
    omega
  subst hm
  have hk1 : Formalism.UG.cT s (T' * S) * Q * (T' * S) = Q := by
    calc Formalism.UG.cT s (T' * S) * Q * (T' * S) = Formalism.UG.cT s S * (Formalism.UG.cT s T' * Q * T') * S := by
          rw [cT_mul_r]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s (T * S) * Q * (T * S) := by
          rw [h3', ← h3, cT_mul_r]; simp only [Matrix.mul_assoc]
      _ = Q := by rw [h2, cT_one_r, Matrix.one_mul, Matrix.mul_one]
  have hk2 : T' * S * C = C' := by
    rw [← h4, ← h4', ← Matrix.mul_assoc (T' * S), Matrix.mul_assoc T' S T, h1, Matrix.mul_one]
  refine ⟨⟨T' * S, T * S', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, h1, Matrix.one_mul, h2']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', h1', Matrix.one_mul, h2]
  · exact hk1
  · exact hk2

end GlobalTheory.WittFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentUnfolding_besselFourierJacobi_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  first | exact @GlobalTheory.Unf.StepFour.fl_eq_flatBF | exact GlobalTheory.Unf.StepFour.fl_eq_flatBF | (intros; apply GlobalTheory.Unf.StepFour.fl_eq_flatBF <;> assumption)
end


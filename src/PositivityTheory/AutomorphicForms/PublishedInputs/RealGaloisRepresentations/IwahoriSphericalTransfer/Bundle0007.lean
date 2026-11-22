import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0037
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AlgSatPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.AttResProof

theorem algSat_pow (a q f : ℕ) (B : Multiset ℂˣ) :
    algSat a (q ^ f) (B.map (· ^ f)) = (algSat a q B).map (· ^ f) := by
  unfold algSat
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, Units.val_pow_eq_pow_val, mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (Nat.cast_nonneg q)]

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (χ : HChar (maximalRealSubfield K)) (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), IsGalRepOf P χ ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a π P hBC χ r wt HT H
  have hloc := GlobalTheory.T.local_global_compatibility_complex L
  have hsl := GlobalTheory.T.satakeParameters_local
  have hsf := GlobalTheory.T.satake_frobenius_compatibility L
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have h1 := hsf K Ω l ι a r H.cont w hw σ _ (((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw)
    fun A h rc hrc => H.away w hw A h rc hrc σ hσ
  rwa [hf, algSat_pow] at h1

end GlobalTheory.RealGal.AttResProof
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BcDualOfPolarized
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PolarBc

theorem normV_under_eq {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem bcDual_of_polarized : Cr.BcDual := by
  intro js gk F K _ _ _ _ _ _ _ h2 n hn π χ P hpol hBC
  obtain ⟨χ', hs, hv⟩ := UpperTheory.heckeChar_realTransport F K h2 χ
  refine ⟨χ', fun v v' => ?_, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse js gk K n hn P _ ?_⟩
  · obtain ⟨u, e⟩ := hs v
    obtain ⟨u', e'⟩ := hs v'
    rw [e, e', hpol.sign u u']
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
    rw [Filter.eventually_cofinite]
    refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
      fun v _ => ?_).subset fun w hw => hw
    haveI := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
    exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩
  filter_upwards [hu, hBC.unr, UpperTheory.baseChange_complexConj_invariance F K n π P hBC] with w hw h3 ⟨B₁, hB₁, hB₂⟩
  obtain ⟨B, hB, hB'⟩ := h3 (w.under (𝓞 F)) rfl _ (normV_under_eq w)
  obtain rfl := hB'.unique hB₁
  obtain ⟨e1, e2⟩ := hv w
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (e1.symm ▸ normV_under_eq (K := F) w) (e2 hw).1
  refine ⟨e3, _, _, hB', hB₂, ?_⟩
  obtain ⟨β, d, hl, -, -, hβ, -⟩ := hpol.dual
  have e5 := UpperTheory.satake_inv_mul_char_eq_of_similitude_pairing F n _ _ _ (π.isSmooth_locRep _) χ hw β hl (fun g x y => by
    have := hβ (GlobalTheory.CuspRep.locGL F n _ g) x y
    rwa [TR.CuspSub.chiDet_locGL] at this) B hB
  rw [e4, (e2 hw).2]
  conv_rhs => rw [← e5]
  simp only [Multiset.map_map]
  exact Multiset.map_congr rfl fun b _ => by simp [mul_pow]

end GlobalTheory.PolarBc
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsInfiniteQcmSplitRam
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ExSplitCM

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem prime_eq_of_mem (u : HeightOneSpectrum (𝓞 F)) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (h : ((p : ℕ) : 𝓞 F) ∈ u.asIdeal) (h' : ((p' : ℕ) : 𝓞 F) ∈ u.asIdeal) : p = p' := by
  by_contra hne
  have hc : Nat.gcd p p' = 1 := (Nat.coprime_primes hp hp').2 hne
  have hm : (((Nat.gcd p p' : ℕ) : ℤ) : 𝓞 F) ∈ u.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab p p']
    push_cast
    exact u.asIdeal.add_mem (u.asIdeal.mul_mem_right _ h) (u.asIdeal.mul_mem_right _ h')
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem finite_primes_of_finite {B : Set (HeightOneSpectrum (𝓞 F))} (hB : B.Finite) :
    {p : ℕ | p.Prime ∧ ∃ u ∈ B, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}.Finite := by
  refine (hB.biUnion (t := fun u => {p : ℕ | p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun u _ => Set.Subsingleton.finite fun p hp p' hp' => prime_eq_of_mem u hp.1 hp'.1 hp.2 hp'.2).subset ?_
  rintro p ⟨hp, u, hu, h⟩
  exact Set.mem_biUnion hu ⟨hp, h⟩

theorem exists_mem_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show ((p : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at h2
    have := hp.two_le
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hne : M ≠ ⊥ := by
    intro h
    rw [h] at hle
    have h0 := hle (Ideal.mem_span_singleton_self _)
    rw [Ideal.mem_bot] at h0
    exact hp.ne_zero (by exact_mod_cast h0)
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.mem_span_singleton_self _)⟩

theorem mem_range_res_iff (K : IntermediateField F Ω) (σ : G F Ω) :
    σ ∈ (res F Ω ↥K).range ↔ ∀ x ∈ K, σ x = x := by
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes (⟨x, hx⟩ : K)
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => h _ x.2, rfl⟩

theorem fix_adjoin {δ : Ω} (hint : IsIntegral F δ) (s : G F Ω) (h : s δ = δ) :
    ∀ x ∈ IntermediateField.adjoin F {δ}, s x = x := by
  intro x hx
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
  have := (AlgHom.eqOn_adjoin_iff (φ := (s : Ω →ₐ[F] Ω)) (ψ := AlgHom.id F Ω)).2
    (by simpa [Set.EqOn] using h) hx
  simpa using this

theorem exists_qcm [IsTotallyReal F] [IsAlgClosure F Ω] (d : F) (δ : Ω) (hδ : δ ^ 2 = algebraMap F Ω d)
    (hd : ∀ φ : F →+* ℝ, φ d < 0) : ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ} := by
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).Monic :=
      Polynomial.monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := Polynomial.natDegree_le_natDegree h1
    rwa [Polynomial.natDegree_X_pow_sub_C] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let w : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have h3 := hd ((InfinitePlace.embedding_of_isReal hw).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  exact ⟨⟨K, inferInstance, IsCMField.ofCMExtension F K, hrk⟩, rfl⟩

end GlobalTheory.ExSplitCM

open GlobalTheory.ExSplitCM in
theorem GlobalTheory.RealGal.exists_infinite_qcm_split_ram : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : HeightOneSpectrum (𝓞 F) → Prop), (∀ᶠ u in Filter.cofinite, T u) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range}.Infinite := by
  intro F Ω _ _ _ _ _ _ T hT v A hA
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q, hq, hqv⟩ := exists_prime_mem v
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  let Good : Set ℕ := {p | p.Prime ∧ IsSquare (-(p : ℚ_[q])) ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr F ∧
    ∀ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → T u}
  have hGood : Good.Infinite := by
    have hbad : ({2} ∪ {p : ℕ | p ∣ (discr F).natAbs} ∪
        {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) | ¬ T u}, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}).Finite := by
      refine ((Set.finite_singleton 2).union ?_).union (finite_primes_of_finite (Filter.eventually_cofinite.1 hT))
      exact (Nat.divisors (discr F).natAbs).finite_toSet.subset fun p hp =>
        Nat.mem_divisors.2 ⟨hp, Int.natAbs_ne_zero.2 (discr_ne_zero F)⟩
    refine ((GlobalTheory.T.infinite_primes_neg_square_padic q).diff hbad).mono ?_
    rintro p ⟨⟨hp, hs⟩, hn⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or, not_and, not_exists] at hn
    refine ⟨hp, hs, hn.1.1, fun h => hn.1.2 (Int.natCast_dvd.1 h), fun u hu => ?_⟩
    by_contra hTu
    exact hn.2 hp u hTu hu
  have hQ : ∀ p ∈ Good, ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} := by
    intro p hp
    refine exists_qcm (-(p : F)) (δ p) (by simp [hδ p]) fun φ => ?_
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.1.pos
  have hmove : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      ∀ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal →
        IsPlaceOver A' u → ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range := by
    intro p hp Q hQK u A' hu hA' hle
    obtain ⟨s, hs, hne⟩ := GlobalTheory.T.inertia_moves_square_root F Ω p hp.1 hp.2.2.1 hp.2.2.2.1 (δ p) (hδ p) u A' hu hA'
    refine hne ((mem_range_res_iff Q.K s).1 (hle hs) (δ p) ?_)
    rw [hQK]
    exact IntermediateField.mem_adjoin_simple_self F (δ p)
  have hmem : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      Q ∈ {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range} := by
    intro p hp Q hQK
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.T.decomposition_fixes_square_root F Ω v A hA q hqv (-(p : ℤ)) (δ p) (by push_cast; exact hδ p)
        (by push_cast; exact hp.2.1) s hs
    · obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
      obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
      exact ⟨u, A', hp.2.2.2.2 u hu, hA', hmove p hp Q hQK u A' hu hA'⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : QCM F Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := F) A' ≤ (res F Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds F ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  exact ⟨u, fun hall => hmove p hp Q hQK u A' hu hA' (hall A' hA'), hu⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsNormVEqPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttUniq

theorem exists_normV_eq_pow (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f := by
  haveI := w.isMaximal
  refine ⟨w.asIdeal.inertiaDeg (𝓞 F), ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 F)).asIdeal (w.under (𝓞 F)).isPrime
      (w.under (𝓞 F)).ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at h
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem main_of_isoOfFrob (hI : IsoOfFrob) : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r r' : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι K r → AttRes π ι K r' → RepIso r r' := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r r' hc hc' hs hs' h h'
  refine hI K Ω l ι a r r' hc hc' hs hs' ?_
  filter_upwards [h, h'] with w hw hw'
  obtain ⟨f, hf⟩ := exists_normV_eq_pow F K w
  obtain ⟨B, hB, hr⟩ := hw f hf
  obtain ⟨B', hB', hr'⟩ := hw' f hf
  obtain rfl := hB.unique hB'
  exact ⟨_, hr, hr'⟩

end GlobalTheory.AttUniq

theorem GlobalTheory.AttUniq.attRes_repIso : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r r' : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι K r → AttRes π ι K r' → RepIso r r' :=
  GlobalTheory.AttUniq.main_of_isoOfFrob GlobalTheory.T.isomorphism_of_frobenius_traces
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HasFixedOfHasSat
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.TwistUnr

section Loc

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

theorem isLocComp_twist {π : TR.CuspSub F a} {η : HChar F} (hT : IsoTwist π η) {u : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin a) (u.adicCompletion F))} (hσ : π.IsLocComp u σ) :
    π.IsLocComp u (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)) := by
  obtain ⟨T, hT1, -, -⟩ := hT
  obtain ⟨f, hf0, hf⟩ := hσ
  have key : ∀ g x, π.locRep u g (T.symm x) =
      ((GlobalTheory.CuspRep.CuspSub.locDet a η u g : ℂˣ) : ℂ) • T.symm (π.locRep u g x) := by
    intro g x
    have h1 := hT1 (locGL F a u g) (T.symm x)
    rw [LinearEquiv.apply_symm_apply, TR.CuspSub.chiDet_locGL] at h1
    apply T.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact h1
  refine ⟨T.symm.toLinearMap ∘ₗ f, fun h => hf0 (LinearMap.ext fun v => T.symm.injective ?_), fun g v => ?_⟩
  · have h2 := LinearMap.congr_fun h v
    rw [LinearMap.zero_apply, map_zero]
    exact h2
  · change T.symm (f (((GlobalTheory.CuspRep.CuspSub.locDet a η u g : ℂˣ) : ℂ) • σ.ρ g v)) = π.locRep u g (T.symm (f v))
    rw [key, LinearMap.map_smul, LinearEquiv.map_smul]
    congr 2
    exact hf g v

theorem hasFixed_of_hasSat (hL : LocCompR) {π : TR.CuspSub F a} {u : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ}
    (hB : π.HasSat u B) {σ : SmIrr (GL (Fin a) (u.adicCompletion F))} (hσ : π.IsLocComp u σ) :
    HasFixed σ.ρ (GlobalTheory.LFun.KGL u a) := by
  refine ((hL F a π u).2 σ hσ).hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL u a).2 ?_
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hB.1
  exact ⟨x, h0, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk⟩

end Loc

section Par

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem unr_of_hasFixed {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w n)) :
    (rc (cls (ParLaws.toRep σ))).unr := by
  refine (ParLaws.unr_iff H _).2 ?_
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  obtain ⟨v, h0, hv⟩ := hf
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩

theorem ine_trivial {x : WD h} (hx : x.unr) (hd : 1 ≤ x.lpDim) {ξ : Weil h →* ℂˣ} (hξ : IsSmooth ξ)
    (ht : (x.lpChar (WD.lpOfChar h ξ hξ)).unr) (s : Ine (F := E) A) : ξ (ineIncl h s) = 1 := by
  rw [lpChar_lpOfChar] at ht
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.unr_mk] at ht
  rw [WD.unr_mk] at hx
  rw [WD.lpDim_mk] at hd
  have h1 := ht.2 s
  change ((ξ (ineIncl h s) : ℂ) • b.ρ (ineIncl h s)) = 1 at h1
  rw [hx.2 s] at h1
  have hn : 1 ≤ n := by simpa using hd
  have h3 := congrFun (LinearMap.congr_fun h1 (fun _ => 1)) ⟨0, hn⟩
  simpa using h3

end Par

end GlobalTheory.RealGal.TwistUnr

open GlobalTheory.RealGal.TwistUnr in

theorem GlobalTheory.RealGal.unrAt_of_isoTwist : GlobalTheory.Mem.LiteralAutomorphy.LitN → AdmissibleReal → ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F), IsoTwist π η →
    ∀ (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ), π.HasSat u B → η.UnrAt u := by
  intro LN hA F _ _ _ a ha π η hT u B hB
  have hL := GlobalTheory.T.local_global_compatibility_real hA
  have L := LN.loc
  obtain ⟨σ, hσ⟩ := (hL F a π u).1
  have hσ' := isLocComp_twist hT hσ
  obtain ⟨A, hAu⟩ := exists_isPlaceOver (AlgebraicClosure F) u
  obtain ⟨rc, hrc⟩ := L.llc F (AlgebraicClosure F) A u hAu
  have H : IsRec hAu rc := GlobalTheory.LocLanglands.isRec_of_isRecLit L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz
    F (AlgebraicClosure F) A u hAu rc hrc
  have u1 := unr_of_hasFixed H σ (hasFixed_of_hasSat hL hB hσ)
  have u2 := unr_of_hasFixed H _ (hasFixed_of_hasSat hL hB hσ')
  obtain ⟨ar, har, ε, -, LL⟩ := H
  have hs := GlobalTheory.HeckeComp.smooth_loc η u
  have e : rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)))) =
      (rc (cls (ParLaws.toRep σ))).lpChar (rc (.ofChar (η.loc u) hs)) := by
    rw [← LL.twist]
    exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm
  rw [e, LL.one] at u2
  have hd : 1 ≤ (rc (cls (ParLaws.toRep σ))).lpDim := by rw [LL.dim]; exact ha
  have hi := ine_trivial u1 hd _ u2
  have hU : (WD.lpOfChar hAu ((η.loc u).comp ar) (har.smooth hs)).unr := by
    rw [WD.lpOfChar, WD.unr_mk]
    refine ⟨rfl, fun s => LinearMap.ext fun v => funext fun i => ?_⟩
    have := hi s
    simp [this]
  have hU' := (GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff har hs).1 hU
  intro x hx
  refine hU' x ?_
  have h0 : Valued.v (x : u.adicCompletion F) ≠ 0 := by simp
  rw [← GlobalTheory.SmGL.ord_eq_zero_iff, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero]
  unfold IsUnitAt at hx
  rw [hx, WithZero.log_one]
end
end


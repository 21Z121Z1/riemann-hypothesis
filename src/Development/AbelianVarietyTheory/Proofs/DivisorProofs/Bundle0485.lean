import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.DualEval

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem evalPt_of_eq {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (φ : R →+* R')
    (G' : Sp R ⟶ X) (x : Sp R' ⟶ X) (O : X.Opens) (h0 : ⊤ ≤ G' ⁻¹ᵁ O) (hx : ⊤ ≤ x ⁻¹ᵁ O)
    (e : x = spMap φ ≫ G') (f : Γ(X, O)) : evalPt x O hx f = φ (evalPt G' O h0 f) := by
  subst e
  exact evalPt_spMap_comp φ G' O h0 hx f

theorem snd_of_mul_eq {K : Type} [Field K] (u t s : DualNumber K) (ht : t.fst ≠ 0)
    (e : u * t = s) : u.snd = (s.snd - s.fst / t.fst * t.snd) / t.fst := by
  have e1 : u.fst * t.fst = s.fst := by rw [← e]; rfl
  have e2 : u.fst * t.snd + u.snd * t.fst = s.snd := by rw [← e, DualNumber.snd_mul]
  have hu : u.fst = s.fst / t.fst := by rw [eq_div_iff ht, e1]
  rw [eq_div_iff ht, ← e2, hu]
  ring

end GlobalTheory.DualEval

namespace GlobalTheory.DualEval

attribute [local instance] RingHom.ker_isPrime

section Lift

variable {S K : Type} [CommRing S] [Field K] (ψ : S →+* K)

theorem isUnit_of_lifts (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
    (y : (RingHom.ker ψ).primeCompl) : IsUnit (φ y) := by
  refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
  rw [hφ]
  exact Ne.isUnit fun h0 => y.2 (by simpa [RingHom.mem_ker] using h0)

def liftAt (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    Localization.AtPrime (RingHom.ker ψ) →+* DualNumber K :=
  IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (isUnit_of_lifts ψ φ hφ)

theorem liftAt_comp (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    (liftAt ψ φ hφ).comp (algebraMap S (Localization.AtPrime (RingHom.ker ψ))) = φ :=
  IsLocalization.lift_comp _

theorem liftAt_mk'_mul (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t) * φ t = φ s := by
  have := congrArg (liftAt ψ φ hφ)
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker ψ)) s t)
  rw [map_mul] at this
  unfold liftAt at this ⊢
  rw [IsLocalization.lift_eq, IsLocalization.lift_eq] at this
  exact this

theorem psi_ne_zero (t : (RingHom.ker ψ).primeCompl) : ψ t ≠ 0 := fun h0 =>
  t.2 (by simpa [RingHom.mem_ker] using h0)

theorem liftAt_mk'_snd (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).snd =
      ((φ s).snd - ψ s / ψ t * (φ t).snd) / ψ t := by
  have := snd_of_mul_eq _ _ _ (by rw [hφ]; exact psi_ne_zero ψ t) (liftAt_mk'_mul ψ φ hφ s t)
  rw [hφ, hφ] at this
  exact this

theorem liftAt_isLocalHom (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    IsLocalHom ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (liftAt ψ φ hφ)) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hs
  have e1 : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst *
      ψ t = ψ s := by
    rw [← hφ, ← hφ, ← liftAt_mk'_mul ψ φ hφ s t]
    rfl
  have hs0 : ψ s = 0 := by simpa [RingHom.mem_ker] using hs
  rw [hs0] at e1
  have hne : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst
      ≠ 0 := hx.ne_zero
  exact hne ((mul_eq_zero.1 e1).resolve_right (psi_ne_zero ψ t))

end Lift

theorem evalPt_snd_sum {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X)
    (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K)
    (m : ι → K) (h1 : ∀ a s, (θc a s).fst = ψ s) (h2 : ∀ s, (θ s).fst = ψ s)
    (h3 : ∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) (O : X.Opens) (f : Γ(X, O))
    (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O) :
    (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  classical
  let L := Localization.AtPrime (RingHom.ker ψ)
  let alg : S →+* L := algebraMap S L
  let fstR : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  let G' : Sp L ⟶ X := spMap alg ≫ G
  haveI := liftAt_isLocalHom ψ θ h2
  have hm : IsLocalRing.closedPoint L ∈ G' ⁻¹ᵁ O := by
    rw [← IsLocalRing.comap_closedPoint (fstR.comp (liftAt ψ θ h2))]
    have hmor : spMap (fstR.comp (liftAt ψ θ h2)) ≫ G' = spMap fstR ≫ spMap θ ≫ G := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp_ring, ← spMap_comp_ring,
        RingHom.comp_assoc, liftAt_comp]
    let pt : Sp K := IsLocalRing.closedPoint K
    have key : (spMap (fstR.comp (liftAt ψ θ h2)) ≫ G') pt ∈ O := by
      rw [hmor]
      exact h (Set.mem_univ ((spMap fstR) pt))
    exact key
  have h0 : ⊤ ≤ G' ⁻¹ᵁ O := ((IsLocalRing.closed_point_mem_iff (U := G' ⁻¹ᵁ O)).1 hm).ge
  have hval : ∀ (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
      (hx : ⊤ ≤ (spMap φ ≫ G) ⁻¹ᵁ O),
      evalPt (spMap φ ≫ G) O hx f = liftAt ψ φ hφ (evalPt G' O h0 f) := by
    intro φ hφ hx
    refine evalPt_of_eq _ G' _ O h0 hx ?_ f
    rw [← Category.assoc, ← spMap_comp_ring, liftAt_comp]
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl (evalPt G' O h0 f)
  have hA : ∀ a, (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd =
      (((θc a) s).snd - ψ s / ψ t * ((θc a) t).snd) / ψ t := fun a => by
    rw [hval (θc a) (h1 a) (h' a), ← hst, liftAt_mk'_snd]
  rw [hval θ h2 h, ← hst, liftAt_mk'_snd]
  simp_rw [hA, h3, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end GlobalTheory.DualEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

theorem exists_intLift (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (k : Type) [Field k] [Algebra V k] [IsFractionRing V k] (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by
  have hinj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  have h : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (x : E) := by
    intro x
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ.toIntAlgHom
    exact h1.tower_top
  choose s hs using h
  refine ⟨{ toFun := s, map_one' := hinj ?_, map_mul' := fun x y => hinj ?_,
            map_zero' := hinj ?_, map_add' := fun x y => hinj ?_ }, hs⟩
  · rw [hs]; simp
  · rw [map_mul, hs, hs, hs]; simp
  · rw [hs]; simp
  · rw [map_add, hs, hs, hs]; simp

theorem ord_vw_pow_mul_unit (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    ord_vw O (algebraMap O K (ϖ ^ n * u)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K (u : O)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K ϖ) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
  unfold ord_vw
  rw [map_mul, map_pow, map_mul, map_pow, h1, h2, mul_one, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem exists_pow_mul_unit {E : Type} [Field E] [NumberField E] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : 𝓞 E →+* O) (hQ0 : Ideal.comap ι (IsLocalRing.maximalIdeal O) ≠ ⊥) {ϖ : O} (e : ℕ)
    (he : Ideal.map ι (Ideal.comap ι (IsLocalRing.maximalIdeal O)) = Ideal.span {ϖ ^ e}) (z : 𝓞 E) (hz : z ≠ 0) :
    ∃ u : Oˣ, ι z = ϖ ^ (e * multiplicity (Ideal.comap ι (IsLocalRing.maximalIdeal O)) (Ideal.span {z})) * u := by
  set Q := Ideal.comap ι (IsLocalRing.maximalIdeal O) with hQdef
  have hQp : Q.IsPrime := Ideal.comap_isPrime ι _
  set k := multiplicity Q (Ideal.span {z})
  have hz0 : Ideal.span {z} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : FiniteMultiplicity Q (Ideal.span {z}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp) hz0
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd Q (Ideal.span {z})
  have hJQ : ¬ J ≤ Q := by
    intro hle
    have : Q ^ (k + 1) ∣ Ideal.span {z} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle)
    exact (hfin.pow_dvd_iff_le_multiplicity.1 this).not_gt (Nat.lt_succ_self k)
  obtain ⟨s, hsJ, hsQ⟩ := SetLike.not_le_iff_exists.1 hJQ
  have hsu : IsUnit (ι s) := by
    by_contra h
    exact hsQ (Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
  have hJt : Ideal.map ι J = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem ι hsJ) hsu
  have h1 : Ideal.span {ι z} = Ideal.span {ϖ ^ (e * k)} := by
    rw [← Set.image_singleton, ← Ideal.map_span, hJ, Ideal.map_mul, Ideal.map_pow, he, hJt, Ideal.mul_top,
      Ideal.span_singleton_pow, pow_mul]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.1 h1).symm
  exact ⟨u, hu.symm⟩

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l ((discr E).natAbs.factorization l) (ordCompl[l] (discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hspan0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  rw [multiplicity_eq_count_normalizedFactors hirr differentIdeal_ne_bot,
    multiplicity_eq_count_normalizedFactors hirr hspan0, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

open Classical in

theorem diff_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
    ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal →
        val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧
      ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) →
        ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by
  intro E _ _ _ _ l hl O _ _ _ _ K _ _ _ hlm hcard
  have hne : Nonempty (E →+* K) := by
    have : 0 < Nat.card (E →+* K) := hcard ▸ Module.finrank_pos
    exact (Nat.card_pos_iff.1 this).1
  obtain ⟨σ0⟩ := hne
  obtain ⟨ι, hι⟩ := exists_intLift E O K σ0
  set Q := Ideal.comap ι (IsLocalRing.maximalIdeal O) with hQdef
  have hlQ : (l : 𝓞 E) ∈ Q := by rw [Ideal.mem_comap, map_natCast]; exact hlm
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hlO : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h] at hlQ
    exact hl0 ((Submodule.mem_bot _).1 hlQ)
  have hQp : Q.IsPrime := Ideal.comap_isPrime ι _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmap0 : Ideal.map ι Q ≠ ⊥ := by
    intro h
    have := Ideal.mem_map_of_mem ι hlQ
    rw [h, map_natCast] at this
    exact hlO ((Submodule.mem_bot _).1 this)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hϖ
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.span_singleton_one] at he
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 (he ▸ Ideal.map_comap_le))

  set 𝔇 := differentIdeal ℤ (𝓞 E) with h𝔇def
  have h𝔇 : 𝔇 ≠ ⊥ := differentIdeal_ne_bot
  have hfin𝔇 : FiniteMultiplicity Q 𝔇 := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp) h𝔇
  set k := multiplicity Q 𝔇 with hkdef
  have hnle : ¬ 𝔇 ≤ Q ^ (k + 1) := fun h =>
    (hfin𝔇.pow_dvd_iff_le_multiplicity.1 (Ideal.dvd_iff_le.2 h)).not_gt (Nat.lt_succ_self k)
  obtain ⟨x, hx𝔇, hxQ⟩ := SetLike.not_le_iff_exists.1 hnle
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxQ (zero_mem _)
  have hxk : multiplicity Q (Ideal.span {x}) = k := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
    · exact Ideal.dvd_iff_le.2 (((Ideal.span_singleton_le_iff_mem _).2 hx𝔇).trans
        (Ideal.le_of_dvd (pow_multiplicity_dvd Q 𝔇)))
    · intro h
      exact hxQ ((Ideal.span_singleton_le_iff_mem _).1 (Ideal.le_of_dvd h))
  refine ⟨ι x, ?_, ?_⟩
  · intro P hP
    obtain ⟨u, hu⟩ := exists_pow_mul_unit ι hQ0 e he x hx0
    obtain ⟨u', hu'⟩ := exists_pow_mul_unit ι hQ0 e he (l : 𝓞 E) hl0
    have hxK : algebraMap O K (ι x) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective O K), hu]
      exact mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero
    have hlK : (l : K) = algebraMap O K (ι (l : 𝓞 E)) := by rw [map_natCast, map_natCast]
    rw [val_vp, if_neg hxK, hlK, hu, hu', ord_vw_pow_mul_unit O K hϖ, ord_vw_pow_mul_unit O K hϖ, hxk]
    congr 1
    have hr1 := mult_ratio E l hl P.asIdeal P.isPrime hP
    have hr2 := mult_ratio E l hl Q hQp hlQ
    rw [diffExp_vp, hr1, ← hr2]
    have hkl : multiplicity Q (Ideal.span {(l : 𝓞 E)}) ≠ 0 := by
      have hfl : FiniteMultiplicity Q (Ideal.span {(l : 𝓞 E)}) := FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime hQ0 hQp) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hl0)
      have := hfl.le_multiplicity_of_pow_dvd (k := 1) (by
        rw [pow_one]; exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hlQ))
      omega
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast he0)]
  · intro σ y hy
    haveI : CharZero K := charZero_of_injective_ringHom σ0.injective
    letI : Algebra E K := σ0.toAlgebra
    haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun q => by
      show algebraMap ℚ K q = σ0 (algebraMap ℚ E q)
      rw [eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
    let τ : E ≃ₐ[ℚ] E := (σ.toRatAlgHom).restrictNormal' E
    have hτ : ∀ w, σ0 (τ w) = σ w := fun w => (σ.toRatAlgHom).restrictNormal_commutes E w
    have hyd : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
      obtain ⟨n, hn⟩ := hy b
      exact ⟨n, by rw [Algebra.traceForm_apply, eq_intCast]; exact hn.symm⟩
    have hτy := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.traceDual_smul τ hyd
    have hx' := (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.mem_differentIdeal_iff x).1 hx𝔇
    rw [Submodule.mem_div_iff_forall_mul_mem] at hx'
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx' _ hτy)
    refine ⟨ι b, ?_⟩
    rw [hι, hι, ← hτ, ← map_mul]
    exact congrArg σ0 hb

end GlobalTheory.DifferentElement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersPrime
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.TorsionFreeDividedPowers

open DividedPowers

def natPosSubmonoid (R : Type) [CommRing R] : Submonoid R where
  carrier := {r | ∃ k : ℕ, k ≠ 0 ∧ (k : R) = r}
  one_mem' := ⟨1, one_ne_zero, Nat.cast_one⟩
  mul_mem' := by
    rintro a b ⟨j, hj, rfl⟩ ⟨k, hk, rfl⟩
    exact ⟨j * k, Nat.mul_ne_zero hj hk, by push_cast; ring⟩

noncomputable def ofFactorialUnits {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) : DividedPowers J where
  dpow           := OfInvertibleFactorial.dpow J
  dpow_null hx   := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx   := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx    := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt (h _) (n.lt_succ_self) hx hy
  dpow_mul hx := OfInvertibleFactorial.dpow_mul hx
  mul_dpow {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt (h _) (m + k).lt_succ_self hx
  dpow_comp hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt (h _) hk (lt_add_one _) hx

theorem ofFactorialUnits_dpow {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) {n : ℕ} {x : A} (hx : x ∈ J) :
    (ofFactorialUnits h J).dpow n x = Ring.inverse (n.factorial : A) * x ^ n :=
  OfInvertibleFactorial.dpow_eq_of_mem hx

theorem exists_factorial_mul_eq (l : ℕ) (hl : l.Prime) {O : Type} [CommRing O] [IsLocalRing O]
    (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) (hn : n ≠ 0) :
    ∃ q : O, (n.factorial : O) * q = (l : O) ^ (n - 1) := by
  haveI := Fact.mk hl
  have hN : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n.factorial l
  have hcop := Nat.coprime_ordCompl hl hN
  have hv : n.factorial.factorization l < n := by
    rw [Nat.factorization_def _ hl]
    exact padicValNat_factorial_lt_of_ne_zero l hn
  set v := n.factorial.factorization l
  set u := n.factorial / l ^ v
  have hu : IsUnit (u : O) := by
    by_contra hnu
    have hum : (u : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom O)
    simp only [eq_intCast, Int.cast_natCast] at hab
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hum)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨w, hw⟩ := hu
  refine ⟨(↑w⁻¹ : O) * (l : O) ^ (n - 1 - v), ?_⟩
  rw [← hfac]
  push_cast
  have e : (l : O) ^ v * (u : O) * ((↑w⁻¹ : O) * (l : O) ^ (n - 1 - v))
      = (l : O) ^ v * (l : O) ^ (n - 1 - v) * ((u : O) * ↑w⁻¹) := by ring
  rw [e, ← hw, Units.mul_inv, mul_one, ← pow_add, Nat.add_sub_cancel' (by omega)]

theorem exists_dividedPowers :
    ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R],
    (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) →
    ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)},
      (m.factorial : R) * γ₀.dpow m y = y ^ m := by
  intro l hl O _ _ _ _ hlm R _ _ htf
  let S := natPosSubmonoid R
  have hS : S ≤ nonZeroDivisors R := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => htf k x hk hx
  have hinj : Function.Injective (algebraMap R (Localization S)) :=
    IsLocalization.injective (Localization S) hS
  have hunit : ∀ n : ℕ, IsUnit (n.factorial : Localization S) := fun n => by
    have := IsLocalization.map_units (Localization S)
      (⟨(n.factorial : R), n.factorial, Nat.factorial_ne_zero n, rfl⟩ : S)
    simpa using this
  refine ⟨DividedPowers.ofInjective (Ideal.span {(l : R)}) (Ideal.span {(l : Localization S)})
    (algebraMap R (Localization S)) hinj (ofFactorialUnits hunit _) ?_ ?_,
    fun m y hy => DividedPowers.factorial_mul_dpow_eq_pow _ hy⟩
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
  · intro n x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have hmem : algebraMap R (Localization S) (z * l) ∈ Ideal.span {(l : Localization S)} := by
      rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    rw [ofFactorialUnits_dpow hunit _ hmem]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun h => absurd rfl h, by simp⟩
    · obtain ⟨q, hq⟩ := exists_factorial_mul_eq l hl hlm n hn.ne'
      refine ⟨algebraMap O R q * z ^ n * l,
        fun _ => Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [eq_comm, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hunit n)]
      have hq' : (n.factorial : R) * algebraMap O R q = (l : R) ^ (n - 1) := by
        have := congrArg (algebraMap O R) hq
        simpa using this
      have key : (n.factorial : R) * (algebraMap O R q * z ^ n * l) = (z * l) ^ n := by
        calc (n.factorial : R) * (algebraMap O R q * z ^ n * l)
            = ((n.factorial : R) * algebraMap O R q) * l * z ^ n := by ring
          _ = (z * l) ^ n := by
            rw [hq', ← pow_succ, Nat.sub_add_cancel hn, mul_pow, mul_comm]
      have := congrArg (algebraMap R (Localization S)) key
      simpa using this.symm

end GlobalTheory.TorsionFreeDividedPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZero
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem exists_lift_of_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps R R₀ π hπ hI X hX g₀ hg₀ κ f hf V hV hL
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_glue_spec_localizationAway_morphisms R κ f hf X.left e he3
  refine ⟨E, ?_, ?_⟩
  · refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R κ f hf (Sp R) _ _ (fun k => ?_)
    rw [← Category.assoc, hE k, he1 k, Category.comp_id]
  · have hf₀ : Ideal.span (Set.range (fun k => π (f k))) = ⊤ := by
      rw [show (fun k => π (f k)) = π ∘ f from rfl, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R₀ κ (fun k => π (f k)) hf₀ X.left _ _ (fun k => ?_)
    rw [← he2 k, ← hE k, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp _).symm

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCommonZeroOfIsHomogeneousStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k), (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n → ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous | exact GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous | (intros; apply GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneFormsCocycleRestrictSubCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict (FormExt.omExt F) G).pull1 → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) := by
  first | exact @GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary | exact GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary | (intros; apply GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankTwoBasisModNStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_two_basis_mod_N : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  first | exact @GlobalTheory.LatticeModN.exists_gen_modN | exact GlobalTheory.LatticeModN.exists_gen_modN | (intros; apply GlobalTheory.LatticeModN.exists_gen_modN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPointStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  first | exact @GlobalTheory.AffineLineExt.extend | exact GlobalTheory.AffineLineExt.extend | (intros; apply GlobalTheory.AffineLineExt.extend <;> assumption)
end


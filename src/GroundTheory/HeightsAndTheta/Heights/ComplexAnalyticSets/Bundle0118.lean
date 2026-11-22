import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0111
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0113
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0117
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ExistsMulEqZeroOfMemAssociatedPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

theorem weaklyRegular_eq_nil_of_socle {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {z : M} (hz : z ≠ 0) (hk : ∀ r ∈ maximalIdeal R, r • z = 0) {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) (hreg : IsWeaklyRegular M rs) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    exfalso
    have h := ((isWeaklyRegular_cons_iff M r rs).mp hreg).1
    exact hz (h (show r • z = r • (0 : M) by rw [hk r (hm r List.mem_cons_self), smul_zero]))

theorem algebraMap_not_mem_map_of_colon_le {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r, r * y ∈ I → r ∈ Q) :
    algebraMap B (Localization.AtPrime Q) y ∉ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro h
  obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp h
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl] at hs
  obtain ⟨c, hc⟩ := hs
  have h1 : (↑c * ↑s) * y ∈ I := by
    rw [show (↑c * ↑s) * y = ↑c * (y * ↑s) by ring, hc]
    exact I.mul_mem_left _ i.2
  have h2 := hy _ h1
  exact (Q.primeCompl.mul_mem c.2 s.2) h2

theorem mul_algebraMap_mem_map_of_le_colon {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r ∈ Q, r * y ∈ I) :
    ∀ m ∈ maximalIdeal (Localization.AtPrime Q),
      m * algebraMap B (Localization.AtPrime Q) y ∈ I.map (algebraMap B (Localization.AtPrime Q)) := by
  intro m hm
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
  have hle : Q.map (algebraMap B (Localization.AtPrime Q)) ≤
      (I.map (algebraMap B (Localization.AtPrime Q))).colon {algebraMap B (Localization.AtPrime Q) y} := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (hy r hr)
  have := hle hm
  rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this

theorem ringKrullDim_le_zero_of_socle {L : Type*} [CommRing L] [IsLocalRing L] (hS : SerreSAt L 2)
    {z : L} (hz : z ≠ 0) (hk : ∀ m ∈ maximalIdeal L, m * z = 0) : ringKrullDim L ≤ 0 := by
  obtain ⟨rs, hm, hreg, hlen⟩ := hS
  have := weaklyRegular_eq_nil_of_socle hz (fun m hm => by rw [smul_eq_mul]; exact hk m hm) hm hreg
  subst this
  simp only [List.length_nil, Nat.cast_zero] at hlen
  exact (min_le_iff.mp hlen).resolve_left (by decide)

theorem exists_mul_eq_zero_of_mem_associatedPrime {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hR : SerreR B 1) (hS : SerreS B 2) {Q : Ideal B} (hQ : IsAssociatedPrime Q B) {q : B} (hq : q ∈ Q) :
    ∃ t ∉ Q, t * q = 0 := by
  obtain ⟨hprime, y, rfl⟩ := isAssociatedPrime_iff.mp hQ
  set Q := (⊥ : Submodule B B).colon {y} with hQdef
  have hmem : ∀ r, r ∈ Q ↔ r * y = 0 := fun r => by
    rw [hQdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  let L := Localization.AtPrime Q
  have hz : algebraMap B L y ≠ 0 := by
    have := algebraMap_not_mem_map_of_colon_le Q ⊥ (y := y) (fun r hr => (hmem r).mpr (by simpa using hr))
    simpa [Ideal.map_bot] using this
  have hk : ∀ m ∈ maximalIdeal L, m * algebraMap B L y = 0 := fun m hm => by
    have := mul_algebraMap_mem_map_of_le_colon Q ⊥ (y := y) (fun r hr => by simpa using (hmem r).mp hr) m hm
    simpa [Ideal.map_bot] using this
  have hdim := ringKrullDim_le_zero_of_socle (hS Q) hz hk
  have hreg : IsRegularLocalRing L := hR Q (hdim.trans (by decide))
  have hsf := (isRegularLocalRing_iff L).mp hreg
  have h0 : (maximalIdeal L).spanFinrank = 0 := by
    have : ((maximalIdeal L).spanFinrank : WithBot ℕ∞) ≤ 0 := hsf ▸ hdim
    exact Nat.le_zero.mp (by exact_mod_cast this)
  have hbot : maximalIdeal L = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal L).fg_of_isNoetherianRing).mp h0
  have hqm : algebraMap B L q ∈ maximalIdeal L := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L Q]
    exact hq
  rw [hbot, Submodule.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hqm
  obtain ⟨⟨t, ht⟩, htq⟩ := hqm
  exact ⟨t, ht, htq⟩

theorem ringKrullDim_le_one_of_colon_span {B : Type*} [CommRing B] [IsNoetherianRing B] (hS : SerreS B 2)
    {b y : B} (hb : b ∈ nonZeroDivisors B) (Q : Ideal B) [Q.IsPrime]
    (hQ : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b}) : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hbQ : b ∈ Q := (hQ b).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b))
  have hbm : f b ∈ maximalIdeal L := (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q b).mpr hbQ
  have hbL : f b ∈ nonZeroDivisors L :=
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hb)
  have hbreg : IsSMulRegular L (f b) := fun u v huv => by
    simp only [smul_eq_mul] at huv
    have : (u - v) * f b = 0 := by rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hbL).mp this)
  have hmap : (Ideal.span {b}).map f = Ideal.span {f b} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hsm : ∀ z : L, z ∈ f b • (⊤ : Submodule L L) ↔ z ∈ Ideal.span {f b} := fun z => by
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, -, hw⟩
      exact ⟨w, by rw [← hw, smul_eq_mul, mul_comm]⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, trivial, by rw [smul_eq_mul, mul_comm, hw]⟩
  let zb : QuotSMulTop (f b) L := Submodule.Quotient.mk (f y)
  have hz : zb ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero, hsm, ← hmap] at h
    exact algebraMap_not_mem_map_of_colon_le Q _ (fun r hr => (hQ r).mpr hr) h
  have hk : ∀ m ∈ maximalIdeal L, m • zb = 0 := fun m hm => by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsm, ← hmap, smul_eq_mul]
    exact mul_algebraMap_mem_map_of_le_colon Q _ (fun r hr => (hQ r).mp hr) m hm
  obtain ⟨rs, hm, hreg, hlen⟩ := hS Q
  obtain ⟨rs', hlen', hm', hreg'⟩ := GroundTheory.Heights₂.Heights.exists_isRegular_quotSMulTop hm hreg hbreg hbm
  have hnil := weaklyRegular_eq_nil_of_socle hz hk hm' hreg'.toIsWeaklyRegular
  subst hnil
  simp only [List.length_nil] at hlen'
  have h1 : rs.length ≤ 1 := by omega
  have h2 : min (2 : WithBot ℕ∞) (ringKrullDim L) ≤ 1 := hlen.trans (by exact_mod_cast h1)
  exact (min_le_iff.mp h2).resolve_left (by decide)

theorem isReduced_of_serre {B : Type*} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1) (hS : SerreS B 2) :
    IsReduced B := by
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B x hx0
  have hprime : Q.IsPrime := hQ.isPrime
  obtain ⟨n, hn⟩ := hx
  have hxQ : x ∈ Q := hprime.mem_of_pow_mem n (by rw [hn]; exact Q.zero_mem)
  obtain ⟨t, ht, htx⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ hxQ
  exact ht (hle (by rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htx))

theorem isIntegrallyClosed_of_serre {B : Type} [CommRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsIntegrallyClosed B := by
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective (FractionRing B) le_rfl, fun {x} hx => ?_⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) x
  suffices ha : a ∈ Ideal.span {b} by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hc]⟩
  by_contra ha
  have ha0 : (Ideal.Quotient.mk (Ideal.span {b}) a) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing B _ ha0
  obtain ⟨hprime, yb, hyb⟩ := isAssociatedPrime_iff.mp hQ
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hcol : ∀ r z : B, r ∈ (⊥ : Submodule B (B ⧸ Ideal.span {b})).colon {Ideal.Quotient.mk _ z} ↔
      r * z ∈ Ideal.span {b} := fun r z => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem, map_mul,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hQy : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b} := fun r => by rw [hyb, hcol]
  have haQ : ∀ r, r * a ∈ Ideal.span {b} → r ∈ Q := fun r hr => hle ((hcol r a).mpr hr)
  set L := Localization.AtPrime Q
  set f := algebraMap B L
  have hdim := ringKrullDim_le_one_of_colon_span hS hb Q hQy
  have : IsRegularLocalRing L := hR Q hdim
  have : IsDomain L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  have hic : IsIntegrallyClosed L :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one hdim
  have hnz : ∀ s ∈ nonZeroDivisors B, f s ∈ nonZeroDivisors L := fun s hs =>
    IsLocalization.map_nonZeroDivisors_le Q.primeCompl L (Submonoid.mem_map_of_mem _ hs)
  let K := FractionRing L
  let g : B →+* K := (algebraMap L K).comp f
  have hg : ∀ s : nonZeroDivisors B, IsUnit (g s) := fun s =>
    IsLocalization.map_units K (⟨f s, hnz s s.2⟩ : nonZeroDivisors L)
  let φ : FractionRing B →+* K := IsLocalization.lift hg
  have hφ : ∀ r, φ (algebraMap B (FractionRing B) r) = g r := IsLocalization.lift_eq hg
  have hint : IsIntegral L (φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map, show (algebraMap L K).comp f = φ.comp (algebraMap B (FractionRing B)) from
      (IsLocalization.lift_comp hg).symm, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have h1 : φ (IsLocalization.mk' (FractionRing B) a ⟨b, hb⟩) * g b = g a := by
    rw [← hφ, ← hφ, ← map_mul, IsLocalization.mk'_spec]
  have h2 : c * f b = f a := IsFractionRing.injective L K (by rw [map_mul, hc]; exact h1)
  apply algebraMap_not_mem_map_of_colon_le Q (Ideal.span {b}) haQ
  rw [← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self b))

theorem isDomain_of_serre {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (hR : SerreR B 1)
    (hS : SerreS B 2) : IsDomain B := by
  have hred : IsReduced B := isReduced_of_serre hR hS
  have hic : IsIntegrallyClosed B := isIntegrallyClosed_of_serre hR hS
  refine @NoZeroDivisors.to_isDomain B _ _ ⟨fun {u v} huv => ?_⟩
  by_contra! h
  obtain ⟨hu, hv⟩ := h
  let J : Ideal B := Ideal.span {u} ⊔ (⊥ : Submodule B B).colon {u}
  have hJ : ∃ s ∈ J, s ∈ nonZeroDivisors B := by
    by_contra! hJ
    have hsub : (J : Set B) ⊆ ⋃ p ∈ associatedPrimes B B, (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
      exact fun s hs => hJ s hs
    obtain ⟨Q, hQ, hJQ⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite B B) (f := id) ⊥ ⊥
      (fun Q hQ _ _ => hQ.isPrime)).mp hsub
    obtain ⟨t, ht, htu⟩ := exists_mul_eq_zero_of_mem_associatedPrime hR hS hQ
      (hJQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u)))
    exact ht (hJQ (Ideal.mem_sup_right (by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]; exact htu)))
  obtain ⟨s, hsJ, hs⟩ := hJ
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hsJ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hwu : w * u = 0 := by
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] at hw
  have hxy : r * u * w = 0 := by rw [mul_assoc, mul_comm u w, hwu, mul_zero]
  let e := IsLocalization.mk' (FractionRing B) (r * u) (⟨r * u + w, hs⟩ : nonZeroDivisors B)
  have he : e * e = e := by
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul]
    linear_combination (-(r * u + w)) * hxy
  have hint : IsIntegral B e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num)
    · simp [Polynomial.eval₂_sub, pow_two, he]
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hic).2 hint
  have hc' : c * (r * u + w) = r * u := by
    rw [IsLocalization.eq_mk'_iff_mul_eq] at hc
    exact IsLocalization.injective (FractionRing B) le_rfl (by rw [map_mul]; exact hc)
  have h1 : c * (w * w) = 0 := by linear_combination w * hc' + (1 - c) * hxy
  have h2 : (1 - c) * ((r * u) * (r * u)) = 0 := by linear_combination (-(r * u)) * hc' + c * hxy
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hc1 | hc1
  · have hw0 : w = 0 := IsReduced.eq_zero w ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h1⟩
    subst hw0
    rw [add_zero] at hs
    apply hv
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp (by rw [mul_assoc, huv, mul_zero])
  · have hx0 : r * u = 0 := IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact (hc1.mul_right_eq_zero).mp h2⟩
    rw [hx0, zero_add] at hs
    exact hu ((mul_left_mem_nonZeroDivisors_eq_zero_iff hs).mp hwu)

theorem SerreNormalOfRegularDepth.proof : SerreNormalOfRegularDepth.Statement := by
  intro A _ hA hR hS P _
  set B := Localization.AtPrime P
  have hRB : SerreR B 1 := fun Q _ =>
    (hR (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  have hSB : SerreS B 2 := fun Q _ =>
    (hS (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  exact ⟨isDomain_of_serre hRB hSB, isIntegrallyClosed_of_serre hRB hSB⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.NormalModelFibreNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets Metric

noncomputable section

namespace NormalModelFibre

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem firstCoords_mem_zeroSet {w : Fin n ⊕ Fin M.m → ℂ} (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ zeroSet J := by
  intro f hf
  have h1 : f ∈ M.ideal.comap
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := by
    rw [M.comap_eq]
    exact hf
  have h0 := hw _ (Ideal.mem_comap.1 h1)
  rw [eval_rename] at h0
  exact h0

theorem exists_mem_fibre {q : Fin n → ℂ} (hq : q ∈ zeroSet J) :
    ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q := by
  have : M.ideal.IsPrime := M.isPrime
  have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
    intro h
    obtain ⟨f, hf, hf0⟩ := Submonoid.mem_map.1 h
    apply (Ideal.mem_primeCompl_iff).1 hf
    rw [RingHom.mem_ker]
    have h1 : rename Sum.inl f ∈ M.ideal := Ideal.Quotient.eq_zero_iff_mem.1 hf0
    have h2 : f ∈ J := by
      rw [← M.comap_eq]
      exact h1
    exact hq f h2
  have hle := le_nonZeroDivisors_of_noZeroDivisors h0
  have : Nontrivial (Localization (normalModelSubmonoid M q)) :=
    (IsLocalization.injective (M := normalModelSubmonoid M q)
      (S := Localization (normalModelSubmonoid M q)) hle).nontrivial
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (Localization (normalModelSubmonoid M q))
  obtain ⟨w, hw, hwq, -⟩ := ModelLocalizationMaximalPoint.proof n J q M P hP
  exact ⟨w, hw, hwq⟩

theorem fibre_finite (q : Fin n → ℂ) :
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}.Finite := by
  choose P hPm hP using M.integral
  have hroots : (Set.univ.pi fun i : Fin M.m => {a : ℂ | ((P i).map (eval q)).IsRoot a}).Finite :=
    Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map _).ne_zero
  refine (hroots.image fun y : Fin M.m → ℂ => Sum.elim q y).subset ?_
  rintro w ⟨hw, rfl⟩
  refine ⟨fun i => w (Sum.inr i), fun i _ => ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.isRoot_map_eval_of_mem_zeroSetIn hw i (P i) (hP i)
  · funext s
    rcases s with i | i <;> rfl

theorem isClosed_zeroSetIn : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) := by
  have h : IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal = ⋂ f ∈ M.ideal, {z | eval z f = 0} := by
    ext z
    simp [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem continuous_firstCoords : Continuous (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (n := n) (m := M.m)) :=
  continuous_pi fun _ => continuous_apply _

theorem eventually_mem_of_fibre_subset {q : Fin n → ℂ} {U : Set (Fin n ⊕ Fin M.m → ℂ)} (hU : IsOpen U)
    (hfib : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q → w ∈ U) :
    ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ∈ U := by
  set K : Set (Fin n ⊕ Fin M.m → ℂ) := {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ closedBall q 1} ∩ Uᶜ with hKdef
  have hKb : Bornology.IsBounded K :=
    (IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof n J M (closedBall q 1) isBounded_closedBall).subset
      Set.inter_subset_left
  have hKc : IsClosed K :=
    ((isClosed_zeroSetIn M).inter (isClosed_closedBall.preimage (continuous_firstCoords M))).inter
      hU.isClosed_compl
  have hK : IsCompact K := isCompact_of_isClosed_isBounded hKc hKb
  have hKi : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K) :=
    (hK.image (continuous_firstCoords M)).isClosed
  have hq : q ∉ IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K := by
    rintro ⟨w, ⟨⟨hw, -⟩, hwU⟩, hwq⟩
    exact hwU (hfib w hw hwq)
  refine ⟨closedBall q 1 ∩ (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)ᶜ,
    inter_mem (closedBall_mem_nhds q one_pos) (hKi.isOpen_compl.mem_nhds hq), ?_⟩
  intro w hw hwN
  by_contra hwU
  exact hwN.2 ⟨w, ⟨⟨hw, hwN.1⟩, hwU⟩, rfl⟩

end NormalModelFibre

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem BranchLift.proof (hR : RiemannExtensionAnalytic.Statement)
    (hB : BranchOffHypersurface.Statement) (hO : NormalModelOpenMapping.Statement)
    (hP : NormalModelProper.Statement) : BranchLift.Statement := by
  intro n k J p M γ hJ hdim
  set Δ := Metric.ball (0 : Fin k → ℂ) γ.radius with hΔ
  have hγd : DifferentiableOn ℂ γ.toFun Δ := γ.differentiableOn
  have hγZ : ∀ τ ∈ Δ, γ.toFun τ ∈ zeroSetIn J := fun τ hτ => γ.mapsTo hτ
  choose a b hbJ hab using M.birational
  have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, Differentiable ℂ (fun z : Fin n → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq =>
      simp only [eval_add]
      exact hp.add hq
    | mul_X p i hp =>
      simp only [eval_mul, eval_X]
      exact hp.mul (differentiable_apply i)
  have hcomp : ∀ q, DifferentiableOn ℂ (fun τ => eval (γ.toFun τ) q) Δ := fun q =>
    (hpoly q).comp_differentiableOn hγd
  set g : (Fin k → ℂ) → ℂ := fun τ => eval (γ.toFun τ) (∏ i, b i) with hg
  have hBJ : (∏ i, b i) ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  have hgne : ∀ V, IsOpen V → V ⊆ Δ → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := fun V hV hVΔ hne =>
    hB n k J _ V γ.toFun hJ hdim hBJ hV hne (hγd.mono hVΔ) (γ.injOn.mono hVΔ)
      fun τ hτ => hγZ τ (hVΔ hτ)
  have hbne : ∀ τ, g τ ≠ 0 → ∀ i, eval (γ.toFun τ) (b i) ≠ 0 := fun τ hτ i h =>
    hτ (by simp only [hg, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
  set f : Fin M.m → (Fin k → ℂ) → ℂ := fun i τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)
  have hgraph : ∀ τ ∈ Δ, g τ ≠ 0 → (Sum.elim (γ.toFun τ) fun i => f i τ) ∈ zeroSetIn M.ideal :=
    fun τ hτ hgτ => M.graph_mem_zeroSetIn a b hab _ (hγZ τ hτ) (hbne τ hgτ)
  have hfd : ∀ i, DifferentiableOn ℂ (f i) (Δ ∩ {t | g t ≠ 0}) := fun i τ hτ => by
    have h1 := (hcomp (a i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    have h2 := (hcomp (b i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    show DifferentiableWithinAt ℂ (fun τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)) _ τ
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv (hbne τ hτ.2 i))
  have hbdd : ∀ i, ∀ τ ∈ Δ, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f i '' (N ∩ Δ ∩ {t | g t ≠ 0})) := by
    intro i τ hτ
    obtain ⟨ε, hε, hεΔ⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball τ hτ
    have hsub : Metric.closedBall τ (ε / 2) ⊆ Δ :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεΔ
    have hK : Bornology.IsBounded (γ.toFun '' Metric.closedBall τ (ε / 2)) :=
      ((isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hγd.continuousOn.mono hsub)).isBounded
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hP n J M _ hK)
    refine ⟨Metric.closedBall τ (ε / 2), Metric.closedBall_mem_nhds τ (by linarith),
      isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩⟩
    rintro _ ⟨t, ⟨⟨ht, htΔ⟩, hgt⟩, rfl⟩
    have hw := hC _ ⟨hgraph t htΔ hgt, ⟨t, ht, rfl⟩⟩
    exact (norm_le_pi_norm (Sum.elim (γ.toFun t) fun i => f i t) (Sum.inr i)).trans hw
  choose F hFd hFeq using fun i => hR k Δ g (f i) Metric.isOpen_ball
    ((hpoly _).comp_differentiableOn hγd) hgne (hfd i) (hbdd i)
  set Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ := fun τ => Sum.elim (γ.toFun τ) fun i => F i τ with hΓ
  have hΓd : DifferentiableOn ℂ Γ Δ := by
    refine differentiableOn_pi.2 fun s => ?_
    rcases s with j | i
    · simpa [hΓ] using differentiableOn_pi.1 hγd j
    · simpa [hΓ] using hFd i
  have hdense : Δ ⊆ closure (Δ ∩ {t | g t ≠ 0}) := by
    intro τ hτ
    rw [mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ⟨hto, htΔ⟩, hgt⟩ := hgne (o ∩ Δ) (ho.inter Metric.isOpen_ball)
      Set.inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, hto, htΔ, hgt⟩
  have hΓZ : ∀ τ ∈ Δ, Γ τ ∈ zeroSetIn M.ideal := by
    intro τ hτ q hq
    have heq : Set.EqOn (fun t => eval (Γ t) q) (fun _ => (0 : ℂ)) (Δ ∩ {t | g t ≠ 0}) := by
      intro t ht
      have hΓt : Γ t = Sum.elim (γ.toFun t) fun i => f i t := by
        simp only [hΓ]
        congr 1
        funext i
        exact hFeq i ht
      simp only [hΓt]
      exact hgraph t ht.1 ht.2 q hq
    exact heq.of_subset_closure ((MvPolynomial.continuous_eval q).comp_continuousOn hΓd.continuousOn)
      continuousOn_const Set.inter_subset_left hdense hτ
  have hΓinj : Set.InjOn Γ Δ := fun s hs t ht hst =>
    γ.injOn hs ht (by
      have := congrArg firstCoords hst
      exact this)
  refine ⟨Γ, hΓd, fun τ hτ => ⟨hΓZ τ hτ, rfl⟩, fun V hV hVo => ?_⟩
  exact hO n k J M V Γ hJ hdim hVo (hΓd.mono hV) (hΓinj.mono hV) fun τ hτ => hΓZ τ (hV hτ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ImageDimLe.proof : ImageDimLe.Statement := by
  intro n m P Q hP
  set φ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp (aeval Q) with hφ
  have : P.IsPrime := hP
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨s, hs1, hs2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ)
  obtain ⟨t, ht1, ht2⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial (Fin n) ℂ ⧸ P)
  have hle : Algebra.trdeg ℂ (MvPolynomial (Fin m) ℂ ⧸ RingHom.ker φ) ≤
      Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg φ) (Ideal.kerLiftAlg_injective φ)
  rw [hs2, ht2] at hle
  have hst : s ≤ t := by exact_mod_cast hle
  rw [hs1, ht1]
  exact_mod_cast hst

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProjectionLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def NormalModelProjectionLocallyInjective.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ U ∈ 𝓝 w, Set.InjOn IndefiniteRowSideFullHecke.ComplexSets.firstCoords (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U)

end

end GroundTheory.Heights₂.Heights
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedGroupLike
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueFieldTilt
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.TiltResidue

theorem preTilt_onto_algClosed_residue : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (r : PreTilt O p →+* k), Function.Surjective r := by
  intro p _ C _ _ _ v O _ _ hpu _ hv
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := hpu.out

  have hroot : ∀ y : O, ∃ z : O, z ^ p = y := by
    intro y
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C y) (Fact.out : p.Prime).pos
    have hw1 : v w ≤ 1 := by
      have h := hv.map_le_one y
      rw [← hw, map_pow] at h
      exact (pow_le_one_iff_of_nonneg zero_le (Fact.out : p.Prime).ne_zero).1 h
    obtain ⟨z, hz⟩ := hv.exists_of_le_one hw1
    exact ⟨z, hv.hom_inj (by rw [map_pow, hz, hw])⟩
  choose s hs using hroot
  have hcoeff : Function.Surjective (PreTilt.coeff (O := O) (p := p) 0) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨show Perfection (ModP O p) p from
      ⟨fun n => Ideal.Quotient.mk _ (s^[n] y), fun n => ?_⟩, rfl⟩
    rw [← map_pow, Function.iterate_succ_apply', hs]
  let q : ModP O p →+* IsLocalRing.ResidueField O :=
    Ideal.Quotient.lift _ (IsLocalRing.residue O) (fun a ha =>
      (IsLocalRing.residue_eq_zero_iff a).2
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hpm) ha))
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hchar : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  have hac : IsAlgClosed (IsLocalRing.ResidueField O) := by
    refine IsAlgClosed.of_exists_root _ fun g hg hirr => ?_
    have hl : g ∈ Polynomial.lifts (IsLocalRing.residue O) :=
      (Polynomial.mem_lifts _).mpr
        (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)
    obtain ⟨f, rfl, hdeg, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hg
    have hd : (f.map (algebraMap O C)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective hv.hom_inj]
      intro h0
      have := Polynomial.degree_pos_of_irreducible hirr
      rw [Polynomial.degree_eq_natDegree hf.ne_zero, Nat.cast_eq_zero] at h0
      rw [Polynomial.degree_eq_natDegree (hf.map _).ne_zero] at this
      have h1 : (f.map (IsLocalRing.residue O)).natDegree = 0 := by
        rw [← hdeg]; exact h0
      rw [h1] at this; exact lt_irrefl _ this
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
    have hi : IsIntegral O a := ⟨f, hf, by rw [← Polynomial.eval_map]; exact ha⟩
    obtain ⟨b, rfl⟩ := hv.exists_of_le_one (r := a) (hv.mem_of_integral hi)
    have hb : f.eval b = 0 := hv.hom_inj (by
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]; exact ha)
    refine ⟨IsLocalRing.residue O b, ?_⟩
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hb, map_zero]
  exact ⟨IsLocalRing.ResidueField O, inferInstance, hac, hchar, q.comp (PreTilt.coeff 0),
    hq.comp hcoeff⟩

end GlobalTheory.TiltResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomain
section
open scoped TensorProduct

namespace GlobalTheory.SepPoint

theorem exists_sepBasis (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    (hB : Algebra.FiniteType k B)
    (hH : ∀ p : ℕ, p.Prime → CharP k p → ∀ s : Finset (FractionRing B),
      LinearIndepOn k _root_.id (s : Set (FractionRing B)) →
        LinearIndepOn k (· ^ p) (s : Set (FractionRing B))) :
    ∃ s : Finset (FractionRing B), IsTranscendenceBasis k ((↑) : s → FractionRing B) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set (FractionRing B)))
        (FractionRing B) := by
  haveI : Algebra.EssFiniteType k B := inferInstance
  haveI : Algebra.EssFiniteType B (FractionRing B) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType k (FractionRing B) := Algebra.EssFiniteType.comp k B _
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k _
  · haveI : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out (hH p hp.out hpk)

theorem core (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F)
    (B : Subalgebra k F) (hB : B.FG) : Nonempty (B →ₐ[k] SeparableClosure k) := by
  obtain ⟨T, rfl⟩ := hB
  haveI : IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := isIntegrallyClosed_adjoin k F s hs.1
  obtain ⟨θ, hθ, H, hH0, U, V, hUV, hT⟩ := GlobalTheory.T.exists_primitive_element_separability_certificate k F s hs hsep T
  obtain ⟨ev, hev⟩ := exists_ev k F s hs.1 H hH0
  let R := Algebra.adjoin k (s : Set F)
  let f := minpoly R θ
  let e : R →+* SeparableClosure k := (ev : R →+* SeparableClosure k)
  have hmon : f.Monic := minpoly.monic hθ
  have hsepa : (f.map e).Separable := by
    have h1 := congrArg (Polynomial.map e) hUV
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h1
    refine ⟨Polynomial.C (e H)⁻¹ * U.map e, Polynomial.C (e H)⁻¹ * V.map e, ?_⟩
    rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul,
      inv_mul_cancel₀ (show e H ≠ 0 from hev), Polynomial.C_1]
  have hdeg : (f.map e).degree ≠ 0 := by
    rw [hmon.degree_map]
    exact (minpoly.degree_pos hθ).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg hsepa
  have hr' : Polynomial.eval₂ (ev : R →+* SeparableClosure k) r f = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hr
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root k F (SeparableClosure k) R θ hθ ev r hr'
  have hHS : (H : F) ∈ Algebra.adjoin k (insert θ (R : Set F)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ H.2)
  exact GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero k F (SeparableClosure k) _ ψ ⟨H, hHS⟩
    (by rw [hψ _ H.2 hHS]; exact hev) (T : Set F) hT

theorem exists_sepPoint : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
    Algebra.FiniteType k B →
    (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B)) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB hK
  haveI : IsDomain (k ⊗[k] B) := hK k inferInstance inferInstance
  haveI : IsDomain B := (Algebra.TensorProduct.lid k B).symm.toMulEquiv.isDomain
  obtain ⟨s, hs, hsep⟩ := exists_sepBasis k B hB
    (fun p hp hpk => GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep k B p hp hpk hK)
  let g : B →ₐ[k] FractionRing B := IsScalarTower.toAlgHom k B (FractionRing B)
  have hfg : g.range.FG := by
    rw [← Algebra.map_top]
    exact hB.out.map g
  obtain ⟨ψ⟩ := core k (FractionRing B) s hs hsep g.range hfg
  exact GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' k B hB ⟨ψ.comp g.rangeRestrict⟩

end GlobalTheory.SepPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPow
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def sqZeroInterp {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B]
    [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S) (h : ∀ x, β x - α x ∈ J)
    (c : S) : B →ₐ[R] S where
  toFun x := α x + c * (β x - α x)
  map_one' := by simp
  map_mul' x y := by
    have hxy : (β x - α x) * (β y - α y) = 0 := by
      have hm := Ideal.mul_mem_mul (h x) (h y)
      rw [← pow_two, hJ] at hm
      simpa using hm
    simp only [map_mul]
    linear_combination (c - c ^ 2) * hxy
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring
  commutes' r := by simp

@[simp] theorem sqZeroInterp_apply {R B S : Type} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S)
    (h : ∀ x, β x - α x ∈ J) (c : S) (x : B) :
    sqZeroInterp J hJ α β h c x = α x + c * (β x - α x) := rfl

theorem exists_sqZero_extend_base (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S]
    [Algebra R' A] [Algebra R' S]
    [hfp : Algebra.FinitePresentation R' A] (J : Ideal S) (hJ : J ^ 2 = ⊥) (g : S)
    (φ : A →ₐ[R'] S) (ψ : A →ₐ[R'] Localization.Away g)
    (hψ : ∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈
      J.map (algebraMap S (Localization.Away g))) :
    ∃ N₀ : ℕ, ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N₀ *
          (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  obtain ⟨n, π, hπ, hker⟩ := hfp.out
  have hJg : (J.map (algebraMap S (Localization.Away g))) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hy : ∀ i : Fin n, ∃ k : ℕ, ∃ y ∈ J, algebraMap S (Localization.Away g) y =
      algebraMap S (Localization.Away g) g ^ k * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    obtain ⟨⟨⟨j, hj⟩, ⟨m, ⟨k, rfl⟩⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g)).1 (hψ (π (MvPolynomial.X i)))
    refine ⟨k, j, hj, ?_⟩
    simp only [map_pow] at e
    rw [← e]; ring
  choose k y hyJ hyeq using hy
  set M := Finset.univ.sup k with hM
  set y' : Fin n → S := fun i => g ^ (M - k i) * y i with hy'
  have hy'J : ∀ i, y' i ∈ J := fun i => J.mul_mem_left _ (hyJ i)
  have hy'eq : ∀ i, algebraMap S (Localization.Away g) (y' i) =
      algebraMap S (Localization.Away g) g ^ M * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    have hk : k i ≤ M := Finset.le_sup (Finset.mem_univ i)
    simp only [y', map_mul, map_pow, hyeq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  set α₀ : MvPolynomial (Fin n) R' →ₐ[R'] S := φ.comp π with hα₀
  set β₀ : MvPolynomial (Fin n) R' →ₐ[R'] S :=
    MvPolynomial.aeval (fun i => φ (π (MvPolynomial.X i)) + y' i) with hβ₀
  have hβα : ∀ p, β₀ p - α₀ p ∈ J := by
    intro p
    rw [← Ideal.Quotient.eq]
    have e : (Ideal.Quotient.mkₐ R' J).comp β₀ = (Ideal.Quotient.mkₐ R' J).comp α₀ := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, β₀, α₀, MvPolynomial.aeval_X]
      rw [Ideal.Quotient.eq]; simpa using hy'J i
    exact DFunLike.congr_fun e p
  have hloc : ∀ p, algebraMap S (Localization.Away g) (β₀ p) =
      algebraMap S (Localization.Away g) (α₀ p) + algebraMap S (Localization.Away g) g ^ M *
        (ψ (π p) - algebraMap S (Localization.Away g) (α₀ p)) := by
    intro p
    have e : (IsScalarTower.toAlgHom R' S (Localization.Away g)).comp β₀ =
        sqZeroInterp _ hJg ((IsScalarTower.toAlgHom R' S (Localization.Away g)).comp α₀)
          (ψ.comp π) (fun q => hψ (π q)) (algebraMap S (Localization.Away g) g ^ M) := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, sqZeroInterp_apply, IsScalarTower.coe_toAlgHom', β₀, α₀,
        MvPolynomial.aeval_X, map_add, hy'eq]
      rfl
    exact DFunLike.congr_fun e p

  obtain ⟨s, hs⟩ := hker
  have hrel : ∀ r ∈ s, ∃ K : ℕ, g ^ K * (β₀ r - α₀ r) = 0 := by
    intro r hr
    have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
    have hπr : π r = 0 := hrk
    have hz : algebraMap S (Localization.Away g) (β₀ r - α₀ r) = 0 := by
      rw [map_sub, hloc]; simp [α₀, hπr]
    obtain ⟨⟨m, ⟨K, rfl⟩⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 hz
    exact ⟨K, hm⟩
  choose! Kf hKf using hrel
  set K := s.sup Kf with hK
  set θ := sqZeroInterp J hJ α₀ β₀ hβα (g ^ K) with hθ
  have hθker : ∀ r ∈ RingHom.ker π.toRingHom, θ r = 0 := by
    intro r hr
    rw [← hs] at hr
    have hle : Ideal.span (s : Set (MvPolynomial (Fin n) R')) ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro r hr
      have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
      have hπr : π r = 0 := hrk
      have hle' : Kf r ≤ K := Finset.le_sup hr
      show θ r = 0
      rw [hθ, sqZeroInterp_apply]
      have : α₀ r = 0 := by simp [α₀, hπr]
      have h2 := hKf r hr
      rw [this, sub_zero] at h2
      rw [this, sub_zero, zero_add, ← Nat.sub_add_cancel hle', pow_add, mul_assoc, h2, mul_zero]
    exact hle hr
  let χ₀ : A →ₐ[R'] S := (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) θ hθker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hχ₀ : ∀ p, χ₀ (π p) = θ p := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ _ θ hθker ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p)) = θ p
    rw [this]
    rfl
  refine ⟨K + M, χ₀, ?_, ?_⟩
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, add_sub_cancel_left]
    exact J.mul_mem_left _ (hβα p)
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, map_add, map_mul, map_sub, hloc, map_pow, pow_add]
    ring

theorem exists_sqZero_extend_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  intro R' A S _ _ _ _ _ _ J hJ g φ ψ hψ
  obtain ⟨N₀, χ₀, h1, h2⟩ := exists_sqZero_extend_base R' A S J hJ g φ ψ hψ
  refine ⟨N₀, fun N hN => ⟨sqZeroInterp J hJ φ χ₀ h1 (g ^ (N - N₀)), ?_, ?_⟩⟩
  · intro x
    rw [sqZeroInterp_apply, add_sub_cancel_left]
    exact J.mul_mem_left _ (h1 x)
  · intro x
    rw [sqZeroInterp_apply, map_add, map_mul, map_sub, h2, map_pow, add_sub_cancel_left,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

end GlobalTheory.SecGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionCharStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorInduction_char' : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ χ : G → ℂ, IsChar ℂ ℂ χ → ∃ X : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X ∧ (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  first | (exact @GlobalTheory.Shin.TensorInd.exists_tensorInduction_char) | (exact GlobalTheory.Shin.TensorInd.exists_tensorInduction_char) | (intros; apply GlobalTheory.Shin.TensorInd.exists_tensorInduction_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjection
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem theta_map_smul_fontaine {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    (σ : Λ →+* O) (f : RL p O Λ →+* O) (hf : IsTheta σ f) (a : Ainf p O) (r : RL p O Λ) :
    f (a • r) = WittVector.fontaineTheta O p a * f r := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  have := hf a 1
  simpa [Algebra.TensorProduct.algebraMap_apply] using this

theorem proj_exists (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type)
    [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O)
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) :
    IsTheta σ f → ∃ π, IsProj C e f π := by
  intro hf
  let M : Matrix (Fin N) (Fin h) C := fun i j => algebraMap O C (f (e.symm (Pi.single j 1) i))
  refine ⟨Matrix.mulVecLin M, ?_⟩
  intro w
  have hw : w = ∑ j, e w j • e.symm (Pi.single j 1) := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  funext i
  conv_rhs => rw [hw]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Finset.sum_apply, Pi.smul_apply,
    map_sum, theta_map_smul_fontaine σ f hf, map_mul]
  show (M *ᵥ _) i = _
  simp only [Matrix.mulVec, dotProduct, M]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedGroupLikeStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_groupLike' : ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Bialgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H] (c : H ⊗[K] H), IsUnit c → c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c = (Algebra.TensorProduct.assoc K K K H H H).symm ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c) → Algebra.TensorProduct.comm K H H c = c → ∃ u : H, u ≠ 0 ∧ c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u := by
  first | exact @GlobalTheory.exists_twisted_groupLike | exact GlobalTheory.exists_twisted_groupLike | (intros; apply GlobalTheory.exists_twisted_groupLike <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMonoStatement
section
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (A : Subring K) (L : Set V), (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧ (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q → x * y ∈ forms (A : Set K) L (q + 1)) ∧ (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧ (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧ ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  first | exact @GlobalTheory.DI.forms_mul_smul_mono | exact GlobalTheory.DI.forms_mul_smul_mono | (intros; apply GlobalTheory.DI.forms_mul_smul_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerBasisLatticePrincipalStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_basis_lattice_principal : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (N : ℕ) (b : Module.Basis (Fin N) C V), Module.finrank C (⋀[C]^N V) = 1 ∧ exteriorPower.ιMulti C N b ≠ 0 ∧ Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range b) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O {exteriorPower.ιMulti C N b} := by
  first | exact @GlobalTheory.span_wedge_of_span_basis | exact GlobalTheory.span_wedge_of_span_basis | (intros; apply GlobalTheory.span_wedge_of_span_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerSpanOfLatticeStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_span_of_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range g) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
  first | exact @GlobalTheory.span_ιMulti_span_range_eq | exact GlobalTheory.span_ιMulti_span_range_eq | (intros; apply GlobalTheory.span_ιMulti_span_range_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTopFinrankOneStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPower_top_finrank_one : ∀ (C : Type) [Field C] (V : Type) [AddCommGroup V] [Module C V] (h N : ℕ) (g : Fin h → V), Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → Module.finrank C (⋀[C]^N V) = 1 ∧ ∃ s : Fin N → Fin h, exteriorPower.ιMulti C N (g ∘ s) ≠ 0 := by
  first | exact @GlobalTheory.topWedge_line_and_nonzero | exact GlobalTheory.topWedge_line_and_nonzero | (intros; apply GlobalTheory.topWedge_line_and_nonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulRepMulVecInjectiveStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithful_rep_mulVec_injective : ∀ (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ) (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R), a ≠ 0 → (ρ a).mulVec x = 0 → x = 0 := by
  first | exact @GlobalTheory.torsionFree_of_finite_domain_action' | exact GlobalTheory.torsionFree_of_finite_domain_action' | (intros; apply GlobalTheory.torsionFree_of_finite_domain_action' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqMulVecOfSchrodingerAnnihilated
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.RealWeil

theorem dRho_apply_basis {l : Type} [Fintype l] [DecidableEq l] (w : l ⊕ l → ℝ) (f : Sch l)
    (x : EuclideanSpace ℝ l) :
    dRho w f x = ∑ b, (w (.inl b) : ℂ) * fderiv ℝ f x (EuclideanSpace.single b 1) +
      2 * π * I * (∑ b, (w (.inr b) : ℂ) * (x b : ℂ)) * f x := by
  rw [dRho_apply]
  have h1 : pPart w = ∑ b, w (.inl b) • EuclideanSpace.single b (1 : ℝ) := by
    ext i
    simp [pPart, EuclideanSpace.single_apply, Pi.single_apply]
  have h2 : inner ℝ (qPart w) x = ∑ b, w (.inr b) * x b := by
    simp [qPart, PiLp.inner_apply, mul_comm]
  rw [h1, map_sum, h2]
  simp [Complex.real_smul, ofReal_sum]

theorem fderiv_eq_of_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 →
    ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) →
    ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) =
      2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  intro l _ _ s P Q hP hQ hdet f hf a x
  set u : l → ℂ := fun b => fderiv ℝ f x (EuclideanSpace.single b 1) with hu
  set xC : l → ℂ := fun i => (x i : ℂ) with hxC
  have hj : ∀ j, ∑ b, P b j * u b + 2 * π * I * (∑ b, Q b j * xC b) * f x = 0 := by
    intro j
    have e := congrArg (fun g : Sch l => g x) (hf j)
    simp only [SchwartzMap.smul_apply, smul_eq_mul, dRho_apply_basis] at e
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at e
    simp only [hP, hQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [hu, hxC]
    linear_combination e
  have hv : Pᵀ *ᵥ u = -(2 * π * I * f x) • (Qᵀ *ᵥ xC) := by
    funext j
    simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hj j
  have hunit : IsUnit Pᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  have hu' : u = (Pᵀ)⁻¹ *ᵥ (Pᵀ *ᵥ u) := by rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have key : u a = ((Pᵀ)⁻¹ *ᵥ (-(2 * π * I * f x) • (Qᵀ *ᵥ xC))) a := by rw [← hv, ← hu']
  change u a = _
  rw [key, mulVec_smul, mulVec_mulVec, ← transpose_nonsing_inv, ← transpose_mul, Matrix.transpose_neg,
    Matrix.neg_mulVec]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end GlobalTheory.RealWeil
end


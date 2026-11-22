import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPoincareSeriesThetaVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankGraphJetsLeChoose
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.JetDim

theorem mem_of_formallyEtale {K R F : Type} [Field K] [CommRing R] [Field F] [Algebra F K]
    [Algebra.IsSeparable F K] (φ : K →+* R) (B : Subring R)
    (hF : ∀ c : F, φ (algebraMap F K c) ∈ B) (N : Ideal R) (hN : IsNilpotent N)
    (σ : K →+* B) (hσ : ∀ a, φ a - σ a ∈ N) (a : K) : φ a ∈ B := by
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let iB : F →+* B := (φ.comp (algebraMap F K)).codRestrict B hF
  letI : Algebra F B := iB.toAlgebra
  letI : Algebra F R := (φ.comp (algebraMap F K)).toAlgebra
  let I : Ideal B := N.comap B.subtype
  have hI : IsNilpotent I := by
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    have h1 : I ^ n ≤ (N ^ n).comap B.subtype := Ideal.le_comap_pow _ n
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro x hx
    have := h1 hx
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact Subtype.ext this
  let g : K →ₐ[F] B ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp σ
      commutes' := fun c => by
        change Ideal.Quotient.mk I (σ (algebraMap F K c)) = Ideal.Quotient.mk I (iB c)
        rw [Ideal.Quotient.eq, Ideal.mem_comap, map_sub]
        have := N.neg_mem (hσ (algebraMap F K c))
        convert this using 1
        simp [iB] }
  let ψ : K →ₐ[F] B := Algebra.FormallySmooth.lift I hI g
  let ψR : K →ₐ[F] R :=
    { toRingHom := B.subtype.comp ψ.toRingHom
      commutes' := fun c => by
        change B.subtype (ψ (algebraMap F K c)) = φ (algebraMap F K c)
        rw [ψ.commutes]
        rfl }
  let φF : K →ₐ[F] R := { toRingHom := φ, commutes' := fun c => rfl }
  have e : ψR = φF := by
    refine Algebra.FormallyUnramified.ext N hN (fun x => ?_)
    have h1 := Algebra.FormallySmooth.mk_lift I hI g x
    change Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (σ x) at h1
    rw [Ideal.Quotient.eq, Ideal.mem_comap, map_sub] at h1
    rw [Ideal.Quotient.eq]
    have := N.sub_mem h1 (hσ x)
    convert this using 1
    change (ψ x : R) - φ x = _
    simp only [Subring.coe_subtype]
    ring
  have := DFunLike.congr_fun e a
  change (ψ a : R) = φ a at this
  rw [← this]
  exact (ψ a).2

end GlobalTheory.JetDim

namespace GlobalTheory.JetDim

theorem jets_finrank_le : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k M : ℕ) (ρ : κ →ₐ[ℂ] κ'),
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra;
  Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) ≤
    (M + k - 1).choose k ∧
  Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) := by
  intro κ κ' _ _ _ _ k M ρ hz0
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  obtain ⟨z, hz⟩ := hz0
  set J := RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) with hJ
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · haveI : Subsingleton ((κ ⊗[ℂ] κ') ⧸ J ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    exact ⟨by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _, inferInstance⟩
  let mk : κ ⊗[ℂ] κ' →+* (κ ⊗[ℂ] κ') ⧸ J ^ M := Ideal.Quotient.mk (J ^ M)
  let φ : κ →+* (κ ⊗[ℂ] κ') ⧸ J ^ M := mk.comp Algebra.TensorProduct.includeLeftRingHom
  let N : Ideal ((κ ⊗[ℂ] κ') ⧸ J ^ M) := J.map mk
  have hNM : N ^ M = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hN : IsNilpotent N := ⟨M, by rw [Ideal.zero_eq_bot]; exact hNM⟩
  have hφσ : ∀ a, φ a - algebraMap κ' _ (ρ a) ∈ N := by
    intro a
    have e : φ a - algebraMap κ' _ (ρ a) = mk (a ⊗ₜ 1 - 1 ⊗ₜ ρ a) := by rw [map_sub]; rfl
    rw [e]
    refine Ideal.mem_map_of_mem _ ?_
    simp [hJ, RingHom.mem_ker, Algebra.TensorProduct.productMap_apply_tmul]
  let t : Fin k → (κ ⊗[ℂ] κ') ⧸ J ^ M := fun i => φ (z i) - algebraMap κ' _ (ρ (z i))
  let B : Subalgebra κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M) := Algebra.adjoin κ' (Set.range t)
  have hzB : ∀ i, φ (z i) ∈ B := by
    intro i
    have : φ (z i) = t i + algebraMap κ' _ (ρ (z i)) := by simp [t]
    rw [this]
    exact B.add_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (B.algebraMap_mem _)

  let F : IntermediateField ℂ κ :=
    { carrier := {a | φ a ∈ B}
      mul_mem' := fun {a b} ha hb => by
        show φ (a * b) ∈ B
        rw [map_mul]; exact B.mul_mem ha hb
      one_mem' := by show φ 1 ∈ B; rw [map_one]; exact B.one_mem
      add_mem' := fun {a b} ha hb => by
        show φ (a + b) ∈ B
        rw [map_add]; exact B.add_mem ha hb
      zero_mem' := by show φ 0 ∈ B; rw [map_zero]; exact B.zero_mem
      algebraMap_mem' := fun r => by
        show φ (algebraMap ℂ κ r) ∈ B
        have : φ (algebraMap ℂ κ r) = algebraMap κ' _ (algebraMap ℂ κ' r) := by
          show mk (algebraMap ℂ κ r ⊗ₜ 1) = mk (1 ⊗ₜ algebraMap ℂ κ' r)
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rw [this]; exact B.algebraMap_mem _
      inv_mem' := fun a ha => by
        show φ a⁻¹ ∈ B
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero, map_zero]; exact B.zero_mem
        have ha' : φ a ∈ B := ha
        have hnil : IsNilpotent ((⟨φ a, ha'⟩ : B) - algebraMap κ' B (ρ a)) := by
          refine ⟨M, Subtype.ext ?_⟩
          have h2 := Ideal.pow_mem_pow (hφσ a) M
          rw [hNM, Ideal.mem_bot] at h2
          simpa using h2
        have hu : IsUnit (algebraMap κ' B (ρ a)) :=
          (isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 ha0)).map _
        have hx : IsUnit (⟨φ a, ha'⟩ : B) := by
          have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
          simpa using this
        obtain ⟨y, hy⟩ := hx.exists_right_inv
        have hy' : φ a * (y : (κ ⊗[ℂ] κ') ⧸ J ^ M) = 1 := congrArg Subtype.val hy
        have h2 : φ a⁻¹ * φ a = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
        have : φ a⁻¹ = y := by
          calc φ a⁻¹ = φ a⁻¹ * (φ a * y) := by rw [hy', mul_one]
          _ = y := by rw [← mul_assoc, h2, one_mul]
        rw [this]; exact y.2 }
  have hle : IntermediateField.adjoin ℂ (Set.range z) ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hzB i
  have eAlg : (algebraMap ℂ κ).toAlgebra = ‹Algebra ℂ κ› := Algebra.algebra_ext _ _ fun _ => rfl
  have hz' : IsTranscendenceBasis ℂ z := by
    unfold TrBasis at hz
    rw [eAlg] at hz
    exact hz
  haveI := hz'.isAlgebraic_field
  letI : Algebra (IntermediateField.adjoin ℂ (Set.range z)) F :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin ℂ (Set.range z)) F κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic F κ :=
    Algebra.IsAlgebraic.extendScalars (R := IntermediateField.adjoin ℂ (Set.range z))
      (IntermediateField.inclusion_injective hle)
  haveI : Algebra.IsSeparable F κ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let σ : κ →+* B.toSubring :=
    ((algebraMap κ' _).comp ρ.toRingHom).codRestrict B.toSubring (fun a => B.algebraMap_mem _)
  have key : ∀ a, φ a ∈ B := fun a =>
    mem_of_formallyEtale φ B.toSubring (fun c : F => c.2) N hN σ (fun a => hφσ a) a
  have hB : ∀ x, x ∈ B := by
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact B.zero_mem
    | tmul a b =>
      have : Ideal.Quotient.mk (J ^ M) (a ⊗ₜ b) = φ a * algebraMap κ' _ b := by
        show mk _ = mk (a ⊗ₜ 1) * mk (1 ⊗ₜ b)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]; exact B.mul_mem (key a) (B.algebraMap_mem b)
    | add x y hx hy => rw [map_add]; exact B.add_mem hx hy

  have ht : ∀ i, t i ∈ N := fun i => hφσ (z i)
  let f : Sym (Fin (k + 1)) (M - 1) → (κ ⊗[ℂ] κ') ⧸ J ^ M :=
    fun s => ∏ i : Fin k, t i ^ ((s : Multiset (Fin (k + 1))).count i.castSucc)
  have hmono : ∀ y ∈ Submonoid.closure (Set.range t), ∃ α : Fin k → ℕ, y = ∏ i, t i ^ α i := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨Pi.single i 1, by simp [Pi.single_apply, pow_ite]⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      exact ⟨α + β, by simp [pow_add, Finset.prod_mul_distrib]⟩
  have hspan : ∀ x, x ∈ Submodule.span κ' (Set.range f) := by
    intro x
    have hx : x ∈ Subalgebra.toSubmodule B := hB x
    rw [Algebra.adjoin_eq_span] at hx
    refine Submodule.span_le.2 ?_ hx
    intro y hy
    obtain ⟨α, rfl⟩ := hmono y hy
    by_cases hα : ∑ i, α i < M
    · let g : Fin (k + 1) → ℕ := Fin.snoc α (M - 1 - ∑ i, α i)
      let m : Multiset (Fin (k + 1)) := Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm g)
      have hcard : Multiset.card m = M - 1 := by
        simp only [m, Finsupp.card_toMultiset]
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        change ∑ j, g j = M - 1
        rw [Fin.sum_univ_castSucc]
        simp only [g, Fin.snoc_castSucc, Fin.snoc_last]
        omega
      refine Submodule.subset_span ⟨⟨m, hcard⟩, ?_⟩
      simp only [f]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [m, g, Finsupp.count_toMultiset]
    · have h1 : ∏ i, t i ^ α i ∈ ∏ i : Fin k, N ^ α i :=
        Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _
      rw [Finset.prod_pow_eq_pow_sum] at h1
      have h2 := Ideal.pow_le_pow_right (not_lt.1 hα) h1
      rw [hNM, Ideal.mem_bot] at h2
      rw [h2]
      exact Submodule.zero_mem _
  have htop : Submodule.span κ' (Set.range f) = ⊤ := eq_top_iff.2 fun x _ => hspan x
  refine ⟨?_, ⟨htop ▸ Submodule.fg_span (Set.finite_range f)⟩⟩
  calc Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)
      = Module.finrank κ' (⊤ : Submodule κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)) := (finrank_top _ _).symm
    _ = Module.finrank κ' (Submodule.span κ' (Set.range f)) := by rw [htop]
    _ ≤ Fintype.card (Sym (Fin (k + 1)) (M - 1)) := finrank_range_le_card f
    _ = (M + k - 1).choose k := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have e : k + 1 + (M - 1) - 1 = M + k - 1 := by omega
      rw [e]
      exact Nat.choose_symm_of_eq_add (by omega)

end GlobalTheory.JetDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlaces
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
noncomputable section

namespace GlobalTheory.LocNorm

theorem good_eventually : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (κ : Type) (bL : Module.Basis κ ℚ L) (θ : L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      Valued.v (2 : v.adicCompletion ℚ) = 1 ∧ IsIntB v bL 1 ∧
      (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) ∧
      (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) ∧
      (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      (∀ x, IsSmallB v bL x → IsSmallB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ) ∧ IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ⁻¹) := by
  intro L _ _ c κ bL θ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have ev := fun (q : ℚ) => rat_mem_adicCompletionIntegers_eventually q
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (bL t.1 * bL t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (c (bL t.1)) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hl : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Fin 3 × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (![1, θ, θ⁻¹] t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hfin := Filter.eventually_cofinite.1 (((hc.and hs).and hl).and (ev (1 / 2)))
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨⟨⟨hcv, hsv⟩, hlv⟩, h2v⟩ := hv
  have hmem : ∀ a : v.adicCompletion ℚ, a ∈ v.adicCompletionIntegers ℚ ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hint : ∀ ℓ : L, (∀ k, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr ℓ k) ∈ v.adicCompletionIntegers ℚ) →
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ℓ) := by
    intro ℓ hℓ k
    rw [repr_tmul_apply, one_mul]; exact hℓ k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hint θ (fun k => hlv (1, k)), hint θ⁻¹ (fun k => hlv (2, k))⟩
  · have hle : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by
      have h := (v.adicCompletionIntegers ℚ).add_mem 1 1 (one_mem _) (one_mem _)
      rw [one_add_one_eq_two] at h
      exact (hmem _).1 h
    have hle' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) ≤ 1 := (hmem _).1 h2v
    have hprod : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) = 1 := by
      rw [← map_mul, show (2 : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) (1 / 2) = 1 by
        rw [show (2 : v.adicCompletion ℚ) = algebraMap ℚ _ 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num, map_one]
    refine le_antisymm hle ?_
    calc (1 : _) = _ := hprod.symm
      _ ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul' le_rfl hle'
      _ = _ := mul_one _
  · rw [Algebra.TensorProduct.one_def]; exact hint 1 (fun k => hlv (0, k))
  · intro y z hy hz k
    rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · intro y z hy hz k
    rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' (mul_le_mul' ((hmem _).1 (hy i)) le_rfl) ((hmem _).1 (hcv (i, j, k))))
      (by simpa using hz j)
  · intro y hy k
    rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))
  · intro y hy k
    rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl ((hmem _).1 (hsv (i, k)))) (by simpa using hy i)

theorem unit_fixed_is_norm : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  intro L _ _ c hc hne κ bL
  obtain ⟨x, hx⟩ := hne
  set θ : L := x - c x with hθdef
  have hθ : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcθ : c θ = -θ := by simp [θ, hc]
  obtain ⟨S, hS⟩ := good_eventually L c κ bL θ
  refine ⟨S, fun v hv e hee hei hei' => ?_⟩
  obtain ⟨h2, h1, hmul, hmulS, hσI, hσS, hθI, hθI'⟩ := hS v hv
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r l => simp [σ, hc]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hσinv : ∀ g : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, σ ↑g = ↑g → σ ↑g⁻¹ = ↑g⁻¹ := by
    intro g hg
    calc σ ↑g⁻¹ = σ ↑g⁻¹ * (↑g * ↑g⁻¹) := by simp
      _ = σ (↑g⁻¹ * ↑g) * ↑g⁻¹ := by rw [map_mul, hg]; ring
      _ = ↑g⁻¹ := by simp
  let θu : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    ⟨1 ⊗ₜ θ, 1 ⊗ₜ θ⁻¹,
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hθ, Algebra.TensorProduct.one_def],
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hθ, Algebra.TensorProduct.one_def]⟩
  have hσθ : σ ↑θu = -↑θu := by simp [θu, σ, hcθ, TensorProduct.tmul_neg]
  obtain ⟨z, hzI, hzS⟩ := GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor v L c hc κ bL h2 h1 hmul hmulS hσI θu hθI hθI' hσθ e hee hei hei'
  set w := z * σ z with hwdef
  have hwσ : σ w = w := by simp only [w, map_mul, hσσ]; ring
  set u : v.adicCompletion ℚ ⊗[ℚ] L := ↑e⁻¹ * w with hudef
  have huI : IsIntB v bL u := hmul _ _ hei' (hmul _ _ hzI (hσI _ hzI))
  have huS : IsSmallB v bL (u - 1) := by
    have : u - 1 = ↑e⁻¹ * (w - ↑e) := by simp [u, mul_sub]
    rw [this]; exact hmulS _ _ hei' hzS
  obtain ⟨f, hfI, hfI', hf2, hfS, huniq⟩ := GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt v L κ bL h2 h1 hmul hmulS u huI huS
  have hσu : σ u = u := by simp only [u, map_mul, hσinv e hee, hwσ]
  have hσf : σ ↑f = ↑f := by
    refine huniq _ (hσI _ hfI) (by rw [← map_pow, hf2, hσu]) ?_
    have := hσS _ hfS
    simpa using this
  have hw : w = ↑e * ↑f ^ 2 := by rw [hf2]; simp [u]
  have hzU : IsUnit z := isUnit_of_mul_isUnit_left (x := z) (y := σ z)
    (by rw [← hwdef, hw]; exact e.isUnit.mul (f.isUnit.pow 2))
  obtain ⟨zu, hzu⟩ := hzU
  refine ⟨zu * f⁻¹, ?_⟩
  have hf' := hσinv f hσf
  simp only [Units.val_mul, map_mul, hf', hzu]
  have : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) = w * ↑f⁻¹ * ↑f⁻¹ := by
    rw [hw]; simp [pow_two, mul_assoc]
  rw [this, hwdef]; ring

end GlobalTheory.LocNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormNonneg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

theorem formOrd_dForm_nonneg : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K) (E : Place c),
  TrBasis c x → (∀ i, x i ∈ E.ring) → 0 ≤ E.formOrd (dForm c x) := by
  intro k K _ _ _ c n x E hx hmem
  let y : Fin n → E.ring := fun i => ⟨x i, hmem i⟩
  have e₁ : E.toRat n (dForm E.const y) = dForm c x := by
    exact formMap_dForm (α := E.const) (β := c) E.ring.subtype rfl y
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hx
  obtain ⟨a, ha⟩ := hω.2 (dForm E.const y)
  rw [← e₁, ← ha, map_smulₛₗ]
  by_cases h0 : (a : K) = 0
  · have hz : (E.ring.subtype a) • E.toRat n ω = 0 := by
      change (a : K) • _ = 0
      rw [h0, zero_smul]
    rw [hz, formOrd, dif_neg]
    rintro ⟨b, hb⟩
    exact hb.ne_zero rfl
  · change 0 ≤ E.formOrd ((a : K) • E.toRat n ω)
    rw [E.formOrd_smul_toRat hω h0]
    exact (E.ord_nonneg_iff h0).2 a.2

end GlobalTheory.FieldPair.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_uniformiser_cons : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (E : Place c) (t : E.ring)
  (w : Fin n → E.ring), Irreducible t →
  (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ E.const w P)) →
  (∃ x : Fin (n + 1) → K, TrBasis c x) →
  E.formOrd (dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K)) = 0 := by
  intro k K _ _ _ c n E t w ht hw hx
  obtain ⟨x, hx⟩ := hx
  have e : dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K) =
      E.toRat (n + 1) (dForm E.const (Fin.cons t w : Fin (n + 1) → E.ring)) := by
    have h := TopForm.formMap_dForm (D := n + 1) (α := E.const) (β := c) E.ring.subtype rfl
      (Fin.cons t w : Fin (n + 1) → E.ring)
    refine Eq.trans ?_ h.symm
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t', ht'⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser k ht'
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m := by
    have : n + 1 = m + 1 := by exact_mod_cast h2
    omega
  have hG := isFreeGen_dForm_uniformiser_cons k E.ring E.const n t w E.essFiniteType ht ⟨b⟩ hw
  rw [e]
  exact E.formOrd_toRat hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPoincareSeriesThetaVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_poincare_series_theta_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ a : RW T S, ∃ hf : IsThetaFunO ψ S T (serO ψ θ σ S T sS sT ΛS ΛT w a), Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) (⟨serO ψ θ σ S T sS sT ΛS ΛT w a, hf⟩ : thetaSub ψ S T) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (serO ψ θ σ S T sS sT ΛS ΛT w a) := by
  first | exact @GlobalTheory.GaussSeriesVacuum.series_theta_vacuum | exact GlobalTheory.GaussSeriesVacuum.series_theta_vacuum | (intros; apply GlobalTheory.GaussSeriesVacuum.series_theta_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.GenericMember

noncomputable def genVar (k : Type) [Field k] (N : ℕ) {X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (i : Fin N) : Γ(X', ⊤) :=
  f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv
    (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))

noncomputable def genSec (k : Type) [Field k] (N : ℕ) {X X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X)
    (b : Fin N → L.Sec) : (L.pull π).Sec :=
  ∑ i, genVar k N f' i • secPull (b i) π

end GlobalTheory.GenericMember
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPatch_chart_image_properties : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  first | exact @GlobalTheory.GoodTop.goodPatch_image | exact GlobalTheory.GoodTop.goodPatch_image | (intros; apply GlobalTheory.GoodTop.goodPatch_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasBlocksOfSystemOccursInBlockPartStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) → Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  first | exact @GlobalTheory.OccBlock.hasBlock_of_occurs | exact GlobalTheory.OccBlock.hasBlock_of_occurs | (intros; apply GlobalTheory.OccBlock.hasBlock_of_occurs <;> assumption)
end


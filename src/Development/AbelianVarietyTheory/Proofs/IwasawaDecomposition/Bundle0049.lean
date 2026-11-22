import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMul
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.NormValuation

def exponent {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (I : Ideal R) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk I).factors

section
variable {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R)

theorem exponent_mul {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    exponent w (I * J) = exponent w I + exponent w J := by
  unfold exponent
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI)
    (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]

theorem exponent_pow {I : Ideal R} (hI : I ≠ ⊥) (n : ℕ) :
    exponent w (I ^ n) = n * exponent w I := by
  unfold exponent
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 hI) w.associates_irreducible]

theorem exponent_self : exponent w w.asIdeal = 1 :=
  Associates.count_self w.associates_irreducible

theorem exponent_top : exponent w ⊤ = 0 := by
  unfold exponent
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero w.associates_irreducible]

theorem exponent_prime_of_ne (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) (h : p ≠ w.asIdeal) :
    exponent w p = 0 := by
  unfold exponent
  refine Associates.count_eq_zero_of_ne w.associates_irreducible
    (HeightOneSpectrum.associates_irreducible ⟨p, inferInstance, hp⟩) ?_
  intro h1
  exact h (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h1)).symm

theorem log_valuation_of_integer (F : Type) [Field F] [Algebra R F] [IsFractionRing R F] (x : R) (hx : x ≠ 0) :
    WithZero.log (w.valuation F (algebraMap R F x)) = -(exponent w (Ideal.span {x}) : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_if_neg hx, WithZero.log_exp, exponent]

end

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exponent_relNorm_prime (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (exponent v (Ideal.relNorm (𝓞 E) p) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w p : ℤ) := by
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  have hq : p.under (𝓞 E) ≠ ⊥ := Ideal.under_ne_bot (𝓞 E) hp
  have : (p.under (𝓞 E)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq inferInstance
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 E)), exponent_pow v hq]
  by_cases h : p.under (𝓞 E) = v.asIdeal
  · let w0 : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hp⟩
    have hw0 : w0 ∈ s := (hs w0).2 h
    rw [Finset.sum_eq_single w0]
    · rw [h, exponent_self, exponent_self]
      simp [w0]
    · intro w _ hw
      rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
      intro he
      exact hw (HeightOneSpectrum.ext he.symm)
    · intro h'; exact absurd hw0 h'
  · rw [exponent_prime_of_ne v _ hq h, mul_zero, Nat.cast_zero]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
    intro he
    apply h
    rw [← (hs w).1 hw, he]

theorem exponent_relNorm (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (I : Ideal (𝓞 K)) : I ≠ ⊥ →
    (exponent v (Ideal.relNorm (𝓞 E) I) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w I : ℤ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, exponent_top]
    simp [exponent_top]
  | h₃ a p ha hp ih =>
    intro _
    have : p.IsPrime := Ideal.isPrime_of_prime hp
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [map_mul, exponent_mul v (Ideal.relNorm_eq_bot_iff.not.2 hp0)
      (Ideal.relNorm_eq_bot_iff.not.2 ha), Nat.cast_add, exponent_relNorm_prime v s hs p hp0, ih ha,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [exponent_mul w hp0 ha, Nat.cast_add, mul_add]

end GlobalTheory.NormValuation

namespace GlobalTheory.NormValuation

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem log_valuation_norm_integer (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (x : 𝓞 K) (hx : x ≠ 0) :
    WithZero.log (v.valuation E (Algebra.norm E (algebraMap (𝓞 K) K x))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (algebraMap (𝓞 K) K x)) := by
  have h1 : algebraMap (𝓞 E) E (Algebra.intNorm (𝓞 E) (𝓞 K) x) = Algebra.norm E (algebraMap (𝓞 K) K x) :=
    Algebra.algebraMap_intNorm (A := 𝓞 E) (K := E) (L := K) (B := 𝓞 K) x
  have h2 : Algebra.intNorm (𝓞 E) (𝓞 K) x ≠ 0 := by
    intro h0
    have : Algebra.norm E (algebraMap (𝓞 K) K x) = 0 := by rw [← h1, h0, map_zero]
    rw [Algebra.norm_eq_zero_iff] at this
    exact hx ((FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).1 this)
  have hI : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [← h1, log_valuation_of_integer v E _ h2, ← Ideal.relNorm_singleton,
    exponent_relNorm v s hs _ hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [log_valuation_of_integer w K x hx, mul_neg]

theorem log_valuation_norm (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) :
    WithZero.log (v.valuation E (Algebra.norm E (a : K))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) := by
  obtain ⟨b, c, hc, h⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (a : K)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    rw [← h, map_zero, zero_div]
  have hK : ∀ y : 𝓞 K, y ≠ 0 → algebraMap (𝓞 K) K y ≠ 0 := fun y hy =>
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.2 hy
  have hN : ∀ y : 𝓞 K, y ≠ 0 → Algebra.norm E (algebraMap (𝓞 K) K y) ≠ 0 := fun y hy =>
    Algebra.norm_ne_zero_iff.2 (hK y hy)
  have hdiv : Algebra.norm E (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c) =
      Algebra.norm E (algebraMap (𝓞 K) K b) / Algebra.norm E (algebraMap (𝓞 K) K c) := by
    rw [eq_div_iff (hN c hc0), ← map_mul, div_mul_cancel₀ _ (hK c hc0)]
  rw [← h, hdiv, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hN b hb0))
    ((Valuation.ne_zero_iff _).2 (hN c hc0)), log_valuation_norm_integer v s hs b hb0,
    log_valuation_norm_integer v s hs c hc0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hK b hb0))
    ((Valuation.ne_zero_iff _).2 (hK c hc0)), mul_sub]

end GlobalTheory.NormValuation

theorem GlobalTheory.NormValuation.log_valuation_norm_eq_sum : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K))), (∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) → WithZero.log (v.valuation E (Algebra.norm E (a : K))) = ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) :=
  fun _ _ _ _ _ _ _ v a s hs => GlobalTheory.NormValuation.log_valuation_norm v a s hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem exists_ne_zero_lt_val_subset_of_mem_nhds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {s : Set K} {x : K} :
    s ∈ nhds x → ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by
  rw [Valued.mem_nhds]
  rintro ⟨γ, hγ⟩
  obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ)) γ.1
  have hc' : (Valued.v : Valuation K Γ).restrict c = γ.1 := hc
  refine ⟨c, ?_, fun y hy => hγ ?_⟩
  · rintro rfl
    rw [map_zero] at hc'
    exact γ.ne_zero hc'.symm
  · change (Valued.v : Valuation K Γ).restrict (y - x) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact hy

theorem exists_exp_of_nhds (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletion F)) (hu : u ∈ nhds 1) :
    ∃ M : ℕ, ∀ y : v.adicCompletion F, Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → y ∈ u := by
  obtain ⟨c, hc, hsub⟩ := exists_ne_zero_lt_val_subset_of_mem_nhds hu
  have h0 : Valued.v c ≠ 0 := by simpa using hc
  set k := WithZero.log (Valued.v c) with hkdef
  have hk : Valued.v c = WithZero.exp k := (WithZero.exp_log h0).symm
  refine ⟨(-k).toNat + 1, fun y hy => hsub ?_⟩
  show Valued.v (y - 1) < Valued.v c
  refine lt_of_le_of_lt hy ?_
  rw [hk, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-k)
  push_cast
  omega

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_adicIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  Valued.isOpen_valuationSubring _

theorem finiteSingle_mem_of_nhds (Vf : Set (FiniteAdeleRing (𝓞 F) F)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (y : v.adicCompletion F),
      y ∈ v.adicCompletionIntegers F → (v ∈ S → Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ))) →
      finiteSingle F v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) isOpen_adicIntegers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  have hM : ∀ i : HeightOneSpectrum (𝓞 F), ∃ M : ℕ, ∀ (y : i.adicCompletion F) (hy : y ∈ i.adicCompletionIntegers F),
      Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → (⟨y, hy⟩ : ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ t i := by
    intro i
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht i)
    obtain ⟨M, hM⟩ := exists_exp_of_nhds i u hu
    exact ⟨M, fun y hy h => hut (hM y h)⟩
  choose M hMs using hM
  refine ⟨I, hI.toFinset.sup M, hI, fun v y hy hS => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :
      (i : HeightOneSpectrum (𝓞 F)) → ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ I.pi t := by
    intro i hi
    by_cases hne : i = v
    · subst hne
      rw [Pi.mulSingle_eq_same]
      refine hMs i y hy ((hS hi).trans ?_)
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact Finset.le_sup (hI.mem_toFinset.2 hi)
    · rw [Pi.mulSingle_eq_of_ne hne]
      exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle F v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem localIdele_mem_of_isOpen (V : Subgroup (Ideles F)) (hV : IsOpen (V : Set (Ideles F))) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (x : (v.adicCompletion F)ˣ),
      Valued.v (x : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) → localIdele F v x ∈ V := by
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have hW1 : Units.embedProduct _ (1 : Ideles F) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact V.one_mem
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 F) F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hN : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨S, M, hS, hSV⟩ := finiteSingle_mem_of_nhds Vf hVf
  refine ⟨S, M, hS, fun v x hx hxS => ?_⟩
  have hin : ∀ y : (v.adicCompletion F)ˣ, Valued.v (y : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((y : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) →
      ((localIdele F v y : Ideles F) : AdeleRing (𝓞 F) F) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy hyS =>
    hVprod ⟨mem_of_mem_nhds hVi, hSV v _ (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hy.le) hyS⟩
  have hxi : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hxiS : v ∈ S → Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(M : ℤ)) := by
    intro hv
    have e : ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * -((x : v.adicCompletion F) - 1) := by
      rw [mul_neg, mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, map_mul, Valuation.map_neg, hxi, one_mul]
    exact hxS hv
  have h1 := hin x hx hxS
  have h2 := hin x⁻¹ hxi hxiS
  rw [← SetLike.mem_coe, ← hWU, Set.mem_preimage, Units.embedProduct_apply]
  refine hprod ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [map_inv] at h3
  exact h3

theorem open_subgroup_contains_congr : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)),
    IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧
      (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧
      ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  intro F _ _ V hV S₀
  classical
  obtain ⟨S₁, M₁, hS₁, key⟩ := localIdele_mem_of_isOpen V hV
  refine ⟨S₀ ∪ hS₁.toFinset, M₁ + 1, Finset.subset_union_left, fun v hv x hx => ?_, fun v _ a ha => ?_⟩
  · refine key v x hx fun hv' => absurd (Finset.mem_union_right _ (hS₁.mem_toFinset.2 hv')) hv
  · rw [locUnit_apply]
    set x := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a with hxdef
    have hxv : (x : v.adicCompletion F) = ((a : F) : v.adicCompletion F) := rfl
    have hsub : Valued.v ((x : v.adicCompletion F) - 1) = v.valuation F ((a : F) - 1) := by
      have e : (x : v.adicCompletion F) - 1 = (((a : F) - 1 : F) : v.adicCompletion F) := by
        show algebraMap F (v.adicCompletion F) (a : F) - 1 = _
        rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub]
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hle : Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
      rw [hsub]
      refine ha.trans ?_
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have hlt : Valued.v ((x : v.adicCompletion F) - 1) < 1 := by
      rw [hsub]
      refine lt_of_le_of_lt ha ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      push_cast
      omega
    have hunit : Valued.v (x : v.adicCompletion F) = 1 := by
      have := Valuation.map_one_add_of_lt _ hlt
      rwa [add_sub_cancel] at this
    exact key v x hunit fun _ => hle

end GlobalTheory.OpenIdeleCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplex
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

theorem isTotallyComplex_of_algebra (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsTotallyComplex E] : IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have h := InfinitePlace.IsReal.comap (algebraMap E K) hw
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _) h

example : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsTotallyComplex E], IsTotallyComplex K :=
  fun E K _ _ _ _ _ _ => isTotallyComplex_of_algebra E K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInduction
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

noncomputable def LowerGen.offDiagSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ M p.1 p.2 ≠ 0

theorem LowerGen.lowerTriangular_elim_step {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ)
    (hL : L.BlockTriangular OrderDual.toDual) (i j : Fin n) (hij : j < i)
    (hjj : L j j ≠ 0)
    (hmin : ∀ a b : Fin n, b < j → a ≠ b → L a b = 0) (a b : Fin n) :
    (transvection i j (-L i j / L j j) * L) a b = if a = i ∧ b = j then 0 else L a b := by
  by_cases ha : a = i
  · subst ha
    rw [transvection_mul_apply_same]
    have hrow : L j b = if b = j then L j j else 0 := by
      rcases lt_trichotomy b j with h | h | h
      · rw [if_neg h.ne]; exact hmin j b h (Ne.symm h.ne)
      · subst h; simp
      · rw [if_neg h.ne']; exact hL (by simpa using h)
    rw [hrow]
    by_cases hb : b = j
    · subst hb; simp; field_simp; ring
    · simp [hb]
  · rw [transvection_mul_apply_of_ne _ _ _ _ ha]; simp [ha]

end GlobalTheory

open GlobalTheory GlobalTheory.LowerGen in
theorem GlobalTheory.lowerTriangular_GL_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
    (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) →
    (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) →
    ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  intro n P _h1 hmul hdiag htr
  suffices H : ∀ m : ℕ, ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      (LowerGen.offDiagSupport L.val).card = m → P L by
    intro L hL; exact H _ L hL rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro L hL hm

  have hdet : L.val.det ≠ 0 := by
    have h := congrArg Matrix.det L.mul_inv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdiag0 : ∀ k, L.val k k ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ hL] at hdet
    exact fun k => (Finset.prod_ne_zero_iff.mp hdet) k (Finset.mem_univ _)
  by_cases hS : (LowerGen.offDiagSupport L.val) = ∅
  · apply hdiag
    intro a b hab
    by_contra hne
    have : (a, b) ∈ LowerGen.offDiagSupport L.val := by simp [LowerGen.offDiagSupport, hab, hne]
    rw [hS] at this; simp at this
  ·
    have hne : (LowerGen.offDiagSupport L.val).Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let cols := (LowerGen.offDiagSupport L.val).image Prod.snd
    have hcols : cols.Nonempty := hne.image _
    set j := cols.min' hcols with hjdef
    have hjmem : j ∈ cols := Finset.min'_mem _ _
    obtain ⟨⟨i, jj⟩, hp, hj'⟩ := Finset.mem_image.mp hjmem
    simp only at hj'
    subst hj'
    simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hij, hLij⟩ := hp
    have hlt : j < i := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd (hL (by simpa using h)) hLij
      · exact h
    have hmin : ∀ a b : Fin n, b < j → a ≠ b → L.val a b = 0 := by
      intro a b hb hab
      by_contra hne'
      have hbm : b ∈ cols := Finset.mem_image.mpr
        ⟨(a, b), by simp [LowerGen.offDiagSupport, hab, hne'], rfl⟩
      have := Finset.min'_le cols b hbm
      rw [← hjdef] at this
      exact absurd hb (not_lt.mpr this)
    set c : ℂ := -L.val i j / L.val j j with hc
    have hijne : i ≠ j := hij
    let U : GL (Fin n) ℂ := ⟨transvection i j c, transvection i j (-c),
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    let V : GL (Fin n) ℂ := ⟨transvection i j (-c), transvection i j c,
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    have hentry := LowerGen.lowerTriangular_elim_step L.val hL i j hlt (hdiag0 j) hmin
    have hUL : ∀ a b, (U * L).val a b = if a = i ∧ b = j then 0 else L.val a b := by
      intro a b; exact hentry a b
    have hlowUL : (U * L).val.BlockTriangular OrderDual.toDual := by
      intro a b hab
      rw [hUL]
      split_ifs with h
      · rfl
      · exact hL hab
    have hsupp : LowerGen.offDiagSupport (U * L).val = (LowerGen.offDiagSupport L.val).erase (i, j) := by
      ext ⟨a, b⟩
      simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, hUL, ne_eq, Prod.mk.injEq]
      by_cases h : a = i ∧ b = j
      · simp [h]
      · simp only [h, if_false]; tauto
    have hcard : (LowerGen.offDiagSupport (U * L).val).card < m := by
      rw [hsupp, ← hm]
      apply Finset.card_erase_lt_of_mem
      simp [LowerGen.offDiagSupport, hij, hLij]
    have hPUL : P (U * L) := ih _ hcard _ hlowUL rfl
    have hPV : P V := htr i j (-c) V hlt rfl
    have hVUL : V * (U * L) = L := by
      rw [← mul_assoc]
      have : V * U = 1 := by
        ext : 1
        show transvection i j (-c) * transvection i j c = 1
        rw [transvection_mul_transvection_same _ _ hij]; simp
      rw [this, one_mul]
    rw [← hVUL]
    exact hmul _ _ hPV hPUL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndexStatement
section
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassGroup_idelic_finiteIndex : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite → ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex := by
  first | exact @GlobalTheory.LevelChars.rayClass_finite | exact GlobalTheory.LevelChars.rayClass_finite | (intros; apply GlobalTheory.LevelChars.rayClass_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffMapOfIsPushoutStatement
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | exact GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.normCoeff_map_of_isPushout <;> assumption)
end


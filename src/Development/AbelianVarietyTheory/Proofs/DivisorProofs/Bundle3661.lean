import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3655
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.QuotientCardinalityFinrank

theorem free_baseChange_quot (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Finite (𝓞 K) L] [Module.IsTorsionFree (𝓞 K) L] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (j : ℕ) :
    Module.Free (𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)})
      ((𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ⊗[𝓞 K] L) := by
  set I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}
  let P : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  haveI : P.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hℓ)
  have hP0 : P ≠ ⊥ := by simp [P, hℓ.ne_zero]
  let T := Algebra.algebraMapSubmonoid (𝓞 K) P.primeCompl
  have hT : T ≤ nonZeroDivisors (𝓞 K) :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain (Localization T) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hT
  haveI : IsDedekindDomain (Localization T) := IsLocalization.isDedekindDomain (𝓞 K) hT _
  haveI : IsPrincipalIdealRing (Localization T) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) P hP0
  have hunit : ∀ t : T, IsUnit (Ideal.Quotient.mk I (t : 𝓞 K)) := by
    rintro ⟨_, z, hz, rfl⟩
    have hz' : ¬ (ℓ : ℤ) ∣ z := fun h => hz (Ideal.mem_span_singleton.mpr h)
    have hc : IsCoprime z ((ℓ : ℤ) ^ j) :=
      (((Nat.prime_iff_prime_int.mp hℓ).irreducible.coprime_iff_not_dvd).mpr hz').symm.pow_right
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (u : 𝓞 K)) ?_
    have hmem : (((ℓ ^ j : ℕ) : 𝓞 K)) ∈ I := Ideal.mem_span_singleton_self _
    have : (algebraMap ℤ (𝓞 K) z) * (u : 𝓞 K) = 1 - (v : 𝓞 K) * ((ℓ ^ j : ℕ) : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this ⊢
      linear_combination this
    rw [← map_mul, this, map_sub, map_one, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero,
      sub_zero]
  letI : Algebra (Localization T) (𝓞 K ⧸ I) := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower (𝓞 K) (Localization T) (𝓞 K ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.algebraMap_eq]
  haveI : Module.Flat (Localization T) (Localization T ⊗[𝓞 K] L) := Module.Flat.baseChange _ _ _
  haveI : Module.IsTorsionFree (Localization T) (Localization T ⊗[𝓞 K] L) := Module.Flat.isTorsionFree
  haveI : Module.Free (Localization T) (Localization T ⊗[𝓞 K] L) := Module.free_of_finite_type_torsion_free'
  exact Module.Free.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (Localization T) (𝓞 K ⧸ I) (𝓞 K ⧸ I) L)

end GlobalTheory.QuotientCardinalityFinrank

namespace GlobalTheory.QuotientCardinalityFinrank

theorem card_eq_pow_finrank (A M : Type) [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] : Nat.card M = Nat.card A ^ Module.finrank A M := by
  rw [Nat.card_congr (Module.finBasis A M).equivFun.toEquiv, Nat.card_fun]
  simp

theorem card_quot_int (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card (L ⧸ (Ideal.span {((n : ℕ) : ℤ)} • ⊤ : Submodule ℤ L)) = n ^ Module.finrank ℤ L := by
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {((n : ℕ) : ℤ)})).toEquiv]
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hA : Nat.card (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}) = n := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod n).toEquiv, Nat.card_zmod]
  haveI : Nontrivial (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}) := (Int.quotientSpanNatEquivZMod n).nontrivial
  rw [card_eq_pow_finrank (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}), Module.finrank_baseChange, hA]

theorem card_ringOfIntegers_quot (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Nat.card (𝓞 K ⧸ Ideal.span {((n : ℕ) : 𝓞 K)}) = n ^ Module.finrank ℚ K := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : ((n : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((n : ℕ) : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem restrictScalars_span_smul_top (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] (n : ℕ) :
    (Ideal.span {((n : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L).restrictScalars ℤ =
      (Ideal.span {((n : ℕ) : ℤ)} • ⊤ : Submodule ℤ L) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul]
  ext x
  simp only [Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and, Nat.cast_smul_eq_nsmul]

theorem quot_equiv_pi_pos (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] [Module.Finite ℤ L] [Module.IsTorsionFree (𝓞 K) L] (r : ℕ)
    (hr : Module.finrank ℤ L = r * Module.finrank ℚ K) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) (hj : 0 < j) :
    Nonempty ((Fin r → 𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ≃ₗ[𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}]
      L ⧸ (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
  set I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}
  haveI : Module.Finite (𝓞 K) L := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) L
  have hn : 2 ≤ ℓ ^ j := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ ≤ ℓ ^ j := Nat.le_self_pow hj.ne' ℓ
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hcardA := card_ringOfIntegers_quot K (ℓ ^ j)
  haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcardA]; positivity)
  haveI : Nontrivial (𝓞 K ⧸ I) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hcardA]
    exact Nat.one_lt_pow hd.ne' (by omega)
  haveI := free_baseChange_quot K L ℓ hℓ j
  let e1 : ((𝓞 K ⧸ I) ⊗[𝓞 K] L) ≃ₗ[𝓞 K ⧸ I] L ⧸ (I • ⊤ : Submodule (𝓞 K) L) :=
    (TensorProduct.quotTensorEquivQuotSMul L I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  haveI : Module.Free (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) := Module.Free.of_equiv e1
  haveI : Module.Finite (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) := Module.Finite.equiv e1
  have hM := card_eq_pow_finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L))
  have hM2 : Nat.card (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) = (ℓ ^ j) ^ (r * Module.finrank ℚ K) := by
    rw [← hr, ← card_quot_int L (ℓ ^ j) hn, ← restrictScalars_span_smul_top K L (ℓ ^ j)]
    exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ _).toEquiv.symm
  have hM' : (ℓ ^ j) ^ (r * Module.finrank ℚ K) =
      (ℓ ^ j) ^ (Module.finrank ℚ K * Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L))) := by
    rw [← hM2, hM, hcardA, pow_mul]
  have hk : Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) = r := by
    have := Nat.pow_right_injective hn hM'
    have : Module.finrank ℚ K * Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) =
      Module.finrank ℚ K * r := by rw [← this]; ring
    exact (Nat.eq_of_mul_eq_mul_left hd this)
  exact ⟨(Module.finBasisOfFinrankEq (𝓞 K ⧸ I) _ hk).equivFun.symm⟩

theorem quot_equiv_pi (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] [Module.Finite ℤ L] [Module.IsTorsionFree (𝓞 K) L] (r : ℕ)
    (hr : Module.finrank ℤ L = r * Module.finrank ℚ K) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    Nonempty ((Fin r → 𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ≃ₗ[𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}]
      L ⧸ (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hI : Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)} = ⊤ := by simp
    haveI : Subsingleton (𝓞 K ⧸ Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)}) := Ideal.Quotient.subsingleton_iff.mpr hI
    haveI : Subsingleton (L ⧸ (Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
      rw [hI, Submodule.top_smul]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · exact quot_equiv_pi_pos K L r hr ℓ hℓ j hj

theorem isTorsionFree_of_free_int (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] : Module.IsTorsionFree (𝓞 K) L := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c y h => ?_
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  have hmem := Ideal.absNorm_mem (Ideal.span {c})
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
  have hne : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  have : (Ideal.absNorm (Ideal.span {c})) • y = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc', mul_smul, h, smul_zero]
  rw [← Nat.cast_smul_eq_nsmul ℤ] at this
  exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hne)

end GlobalTheory.QuotientCardinalityFinrank

namespace GlobalTheory.QuotientCardinalityFinrank

theorem torsion_points_free : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ j : ℕ, ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ o.A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g := by
  intro p _ D R _ b N S s o k _ _ x ℓ hℓ hℓp j
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, x ≫ s = spMap β :=
    ⟨(Spec.preimage (x ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, -⟩ := o.geom k x β hβ
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  haveI := isTorsionFree_of_free_int D.F D.La
  obtain ⟨e⟩ := quot_equiv_pi D.F D.La (D.m * D.n) D.rankLa ℓ hℓ j
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have hcop : (ℓ ^ j).Coprime p :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes hℓ (Fact.out : p.Prime)).mpr hℓp)
  set Sub := (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)} • ⊤ : Submodule (𝓞 D.F) D.La) with hSub
  have hmem : ∀ y : D.La, y ∈ Sub ↔ ∃ z, y = (ℓ ^ j) • z := by
    intro y
    rw [hSub, Submodule.ideal_span_singleton_smul]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Nat.cast_smul_eq_nsmul]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  let φ : D.La →+ Additive (Over.mk x ⟶ o.A) :=
    { toFun := fun y => Additive.ofMul (I.ev (ℓ ^ j) y)
      map_zero' := by
        show Additive.ofMul (I.ev (ℓ ^ j) 0) = Additive.ofMul 1
        rw [(I.ker (ℓ ^ j) hpos hcop 0).mpr ⟨0, by simp⟩]
      map_add' := fun y y' => by
        show Additive.ofMul (I.ev (ℓ ^ j) (y + y')) = Additive.ofMul (I.ev (ℓ ^ j) y * I.ev (ℓ ^ j) y')
        rw [I.add] }
  have hle : Sub.toAddSubgroup ≤ φ.ker := by
    intro y hy
    obtain ⟨z, rfl⟩ := (hmem y).mp hy
    show Additive.ofMul (I.ev (ℓ ^ j) ((ℓ ^ j) • z)) = 0
    rw [(I.ker (ℓ ^ j) hpos hcop _).mpr ⟨z, rfl⟩]
    rfl
  let ψ : D.La ⧸ Sub →+ Additive (Over.mk x ⟶ o.A) := QuotientAddGroup.lift Sub.toAddSubgroup φ hle
  have hψ : ∀ y : D.La, ψ (Submodule.Quotient.mk y) = Additive.ofMul (I.ev (ℓ ^ j) y) := fun y => rfl
  refine ⟨fun a => Additive.toMul (ψ (e a)), ?_, ?_, ?_, ?_⟩
  · intro a a'
    simp only [map_add, toMul_add]
  · intro c a
    dsimp only
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective Sub (e a)
    rw [map_smul, ← hy, Module.Quotient.mk_smul_mk, hψ, hψ]
    exact I.lin (ℓ ^ j) (algebraMap (𝓞 D.F) D.O c) y
  · intro a a' h
    dsimp only at h
    apply e.injective
    rw [← sub_eq_zero, ← map_sub]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective Sub (e (a - a'))
    have h1 : ψ (e (a - a')) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact congrArg Additive.ofMul h
    rw [← hy, Submodule.Quotient.mk_eq_zero, hmem]
    rw [← hy, hψ] at h1
    exact (I.ker (ℓ ^ j) hpos hcop y).mp (congrArg Additive.toMul h1)
  · intro g hg
    obtain ⟨y, hy⟩ := (I.onto (ℓ ^ j) hpos hcop g).mp hg
    refine ⟨e.symm (Submodule.Quotient.mk y), ?_⟩
    dsimp only
    rw [LinearEquiv.apply_symm_apply, hψ]
    exact hy

end GlobalTheory.QuotientCardinalityFinrank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

theorem GlobalTheory.GSep.exists_stalk_zeta (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

theorem GlobalTheory.GSep.twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := GlobalTheory.T.exists_twisted_theta_sum_common_sign_member I X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X)
      (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : X → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt
  obtain ⟨e₂, he₂⟩ := hsg V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh
    rw [dif_pos hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    have key := GlobalTheory.T.twistedThetaSum_zeta_exponent_indep_of_member I X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩
    exact key zt h hzt hh wt hwt
  · beta_reduce at hh
    rw [dif_neg hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := GlobalTheory.GSep.exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_principal_objects_iso_unique : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.ZarhinFam.actPB_of_zRel) | (exact GlobalTheory.ZarhinFam.actPB_of_zRel) | (intros; apply GlobalTheory.ZarhinFam.actPB_of_zRel  <;> assumption)
end


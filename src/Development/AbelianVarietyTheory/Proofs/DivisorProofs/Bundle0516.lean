import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  have h := WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] at h

theorem intIndex : GlobalTheory.SatakeWeyl.IntIndex := by
  intro L _ _ ϖ σ q hU
  obtain ⟨-, -, -, hϖ, -, -, hcard⟩ := hU
  set v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v with hv
  set A := v.valuationSubring
  set O := (intL L).toAddSubgroup
  let e : O →+ A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : O →+ A ⧸ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toAddMonoidHom.comp e
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨⟨a.1, a.2⟩, rfl⟩
  have hϖ1 : v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hker : (O.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf O = f.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change _ ↔ Ideal.Quotient.mk _ (e x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff]
    change _ ↔ v x.1 < 1
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy1 : v y ≤ 1 := hy
      rw [← hxy, AddMonoidHom.coe_mulLeft, map_mul, hϖ1]
      calc WithZero.exp (-1 : ℤ) * v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact (lt_one_iff_le_exp_neg_one _).2 le_rfl
    · intro hx
      refine ⟨ϖ⁻¹ * x.1, ?_, ?_⟩
      · show v (ϖ⁻¹ * x.1) ≤ 1
        rw [map_mul, map_inv₀, hϖ1, ← WithZero.exp_neg, neg_neg]
        calc WithZero.exp (1 : ℤ) * v x.1 ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
              by gcongr; exact (lt_one_iff_le_exp_neg_one _).1 hx
          _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · rw [AddMonoidHom.coe_mulLeft]
        show ϖ * (ϖ⁻¹ * x.1) = x.1
        rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact hcard

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumLeftRightInvarianceNormaliser
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem cellInv_holds : CellInv := by
  classical
  intro G _ K N h g k₁ k₂ hh hk₁ hk₂ hN hN'
  unfold cellSum
  rw [← finsum_comp_equiv (MulAction.toPerm k₁ : Equiv.Perm (G ⧸ K))]
  refine finsum_congr fun x => ?_
  obtain ⟨k, hk⟩ : ∃ k : K, (k₁ • x).out = k₁ * x.out * k := by
    rw [← MulAction.Quotient.mk_smul_out]
    exact QuotientGroup.mk_out_eq_mul K _
  rw [MulAction.toPerm_apply, hk]
  have e : h (k₁ * x.out * k) = h x.out := hh ⟨k₁, hk₁⟩ k _
  rw [e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂ * u * k₂⁻¹, hN u hu, k₂ * k' * (k : G)⁻¹, K.mul_mem (K.mul_mem hk₂ hk') (K.inv_mem k.2), ?_⟩
    have : x.out = k₁⁻¹ * (k₁ * x.out * k) * (k : G)⁻¹ := by group
    rw [this, e']; group
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂⁻¹ * u * k₂, hN' u hu, k₂⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk₂) hk') k.2, ?_⟩
    rw [e']; group

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumRankOneReflectionSymmetryOfSteps
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem rankOne_of_steps : Descent → CellInv → ChainSum → RankOne := by
  intro hD hI hC G A _ _ K N N' ι c Q d h t t' hbi hfin hle hι hsplit hK hnorm hc hQ hidx hex hconj hdc
  obtain ⟨-, e1⟩ := hD G A K N N' ι h t hfin hle hι hsplit hK hnorm
  obtain ⟨f2, e2⟩ := hD G A K N N' ι h t' hfin hle hι hsplit hK hnorm
  have hcomm : ∀ a, t' * ι a = ι ((c ^ d) a) * t' := fun a => by
    rw [← hconj a]; group
  have key := hC A (K.comap ι) c Q d (fun v => cellSum K N' h (t' * ι v)) hc hQ hidx hex
    (by
      intro v hv a
      have := hI G K N' h (t' * ι a) (ι ((c ^ d) v)) 1 hbi hv K.one_mem (by simp) (by simp)
      show cellSum K N' h (t' * ι (v * a)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, ← mul_assoc, hcomm v, mul_one, mul_assoc])
    (by
      intro u hu a
      have := hI G K N' h (t' * ι a) 1 (ι u) hbi K.one_mem hu (hnorm u)
        (fun w hw => by simpa using hnorm u⁻¹ w hw)
      show cellSum K N' h (t' * ι (a * u)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, one_mul, mul_assoc])
    f2
  rw [e1, e2, ← key]
  refine finsum_congr fun y => ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, n1, n2, e⟩ := hdc y.out
  have hcc : (c ^ d) ((c ^ (-d)) y.out) = y.out := by
    rw [← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply]
  rw [hcomm, map_inv, hcc, map_inv, e, hI G K N' h _ k₁ k₂ hbi hk₁ hk₂ n1 n2]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotent
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

open Classical in

theorem finsum_partition {X Y : Type} (f : X → ℂ) (Q : X → Prop) (R : Y → X → Prop)
    (hf : (Function.support f).Finite) (hQ : ∀ x, Q x ↔ ∃ y, R y x)
    (hu : ∀ x y y', R y x → R y' x → y = y') :
    (Function.support fun y => ∑ᶠ x, if R y x then f x else 0).Finite ∧
      (∑ᶠ x, if Q x then f x else 0) = ∑ᶠ y, ∑ᶠ x, if R y x then f x else 0 := by
  have hS : ∀ (T : X → Prop) [DecidablePred T],
      (∑ᶠ x, if T x then f x else 0) = ∑ x ∈ hf.toFinset, if T x then f x else 0 := by
    intro T _
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    exact hx (by simp [h0])
  have hfin : ∀ x, (Function.support fun y => if R y x then f x else 0).Finite := by
    intro x
    refine Set.Subsingleton.finite fun y hy y' hy' => hu x y y' ?_ ?_
    · by_contra h; exact hy (by simp [h])
    · by_contra h; exact hy' (by simp [h])
  simp only [hS]
  constructor
  · refine (hf.biUnion fun x _ => hfin x).subset fun y hy => ?_
    obtain ⟨x, hx, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    exact Set.mem_biUnion (hf.mem_toFinset.1 hx) hx'
  · rw [finsum_sum_comm _ _ fun x _ => hfin x]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Q x
    · obtain ⟨y, hy⟩ := (hQ x).1 hx
      rw [finsum_eq_single _ y, if_pos hx, if_pos hy]
      intro y' hy'
      exact if_neg fun h => hy' (hu x y' y h hy)
    · rw [if_neg hx]
      symm
      exact finsum_eq_zero_of_forall_eq_zero fun y => if_neg fun h => hx ((hQ x).2 ⟨y, h⟩)

theorem descent : GlobalTheory.SatakeWeyl.Descent := by
  intro G A _ _ K N N' ι h g hf hle hN hdec hK hconj
  have key := finsum_partition (fun x : G ⧸ K => h x.out)
    (fun x => ∃ u ∈ N, ∃ k ∈ K, x.out = g * u * k)
    (fun (y : A ⧸ K.comap ι) x => ∃ u ∈ N', ∃ k ∈ K, x.out = g * ι y.out * u * k) hf ?_ ?_
  · unfold cellSum
    convert key
  · intro x
    constructor
    · rintro ⟨u, hu, k, hk, e⟩
      obtain ⟨a, u', hu', rfl⟩ := hdec u hu
      obtain ⟨⟨u₀, hu₀⟩, e₀⟩ := QuotientGroup.mk_out_eq_mul (K.comap ι) a
      refine ⟨QuotientGroup.mk a, ι u₀⁻¹ * u' * (ι u₀⁻¹)⁻¹, hconj _ _ hu', ι u₀⁻¹ * k,
        K.mul_mem (by rw [map_inv]; exact K.inv_mem hu₀) hk, ?_⟩
      rw [e, e₀]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨y, u, hu, k, hk, e⟩
      exact ⟨ι y.out * u, N.mul_mem (hN _) (hle hu), k, hk, by rw [e]; group⟩
  · rintro x y y' ⟨u₁, hu₁, k₁, hk₁, e₁⟩ ⟨u₂, hu₂, k₂, hk₂, e₂⟩
    have e : ι y.out * u₁ * k₁ = ι y'.out * u₂ * k₂ := by
      apply mul_left_cancel (a := g)
      have := e₁.symm.trans e₂
      simpa only [mul_assoc] using this
    set b := y'.out⁻¹ * y.out with hb
    have hb' : ι b ∈ K := by
      refine hK b (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) (N'.mul_mem (hconj _ _ (N'.inv_mem hu₂)) hu₁) ?_
      have : ι b * (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) = k₂ * k₁⁻¹ := by
        have e' : ι y.out * u₁ = ι y'.out * u₂ * k₂ * k₁⁻¹ := by rw [← e]; group
        calc _ = u₂⁻¹ * (ι y'.out)⁻¹ * (ι y.out * u₁) := by
              simp only [hb, map_mul, map_inv]; group
          _ = _ := by rw [e']; group
      rw [this]
      exact K.mul_mem hk₂ (K.inv_mem hk₁)
    rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
    exact (QuotientGroup.eq.2 hb').symm

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSmoothSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace GlobalTheory.EtC

theorem chains_cechAug_quasiIso_of_smooth (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X)
    [Smooth f] [Surjective f] : QuasiIso ((chains R).map (cechAug f)) :=
  GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R (yoneda.map f) (fun U y => GlobalTheory.T.smooth_surjective_etale_locally_has_sections f U y)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsShortExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEtale

theorem cpull_neg {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (-g) I n x = -cpull g I n x := by
  have h := BiprodCls.cpull_add g (-g) I n x
  rw [add_neg_cancel, BiprodCls.cpull_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_lift_neg {R : Type} [CommRing R] {K M N : _root_.GlobalTheory.EtC.Cx R} (a : K ⟶ M) (b : K ⟶ N) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (x : CohomologyClass (M ⊞ N) I n) :
    _root_.GlobalTheory.EtC.cpull (biprod.lift a (-b)) I n x =
      _root_.GlobalTheory.EtC.cpull a I n (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n x) - _root_.GlobalTheory.EtC.cpull b I n (_root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n x) := by
  rw [biprod.lift_eq, _root_.GlobalTheory.EtC.BiprodCls.cpull_add, Preadditive.neg_comp,
    _root_.GlobalTheory.EtC.MayerVietoris.cpull_neg, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull,
    _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_desc_pair {R : Type} [CommRing R] {M N L : _root_.GlobalTheory.EtC.Cx R} (c : M ⟶ L) (d : N ⟶ L) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (z : CohomologyClass L I n) :
    (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z),
      _root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z)) = (_root_.GlobalTheory.EtC.cpull c I n z, _root_.GlobalTheory.EtC.cpull d I n z) := by
  rw [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_desc,
    biprod.inr_desc]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.chains_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A)
    (h1 : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (h2 : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) :
    ∃ w, (ShortComplex.mk (biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)))) ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))) w).ShortExact := by
  have hcomp : (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  have hsq : _root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)) =
      _root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A A') := by
    unfold _root_.GlobalTheory.EtC.spMap
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have hchains := ((_root_.GlobalTheory.EtC.chains R).map_comp _ _).symm.trans
    ((congrArg (_root_.GlobalTheory.EtC.chains R).map hsq).trans
      ((_root_.GlobalTheory.EtC.chains R).map_comp _ _))
  obtain ⟨w', hw'⟩ := _root_.GlobalTheory.EtC.MVExact.mv_exact R A A' f h1 h2
  have hfree := _root_.GlobalTheory.EtC.MVFree.shortExact R A A' f ⟨h1, h2⟩ w'
  have w : biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ≫
      biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
        ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A'))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, hchains, add_neg_cancel]
  refine ⟨w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_⟩
  rcases lt_or_ge 0 i with hi | hi
  · have hX₁ := _root_.GlobalTheory.EtC.chains_isZero_pos R
      (_root_.GlobalTheory.EtC.sp (Localization.Away (algebraMap A A' f))) i hi
    have hX₃ := _root_.GlobalTheory.EtC.chains_isZero_pos R (_root_.GlobalTheory.EtC.sp A) i hi
    have hX₂ : IsZero (((_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp (Localization.Away f)) ⊞
        (_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp A')).X i) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2
        ⟨_root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi, _root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi⟩)
        (HomologicalComplex.biprodXIso _ _ i)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ hX₂
        mono_f := ⟨fun _ _ _ => hX₁.eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => hX₃.eq_of_src _ _⟩ }
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    exact _root_.GlobalTheory.EtC.mv_map_shortExact (HomologicalComplex.eval _ _ (-(p : ℤ)))
      (a := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (b := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))))
      (f := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
      (g := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))
      (W' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away ((algebraMap A A') f))))))
      (X' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away f)))))
      (Y' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A'))))
      (Z' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A))))
      (a' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))))
      (b' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))
      (f' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      (g' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p) w w' hfree

end GlobalTheory.EtC.MVEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditive
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6add_holds : GlobalTheory.EtC.DivisorAdditivity := by
  intro q _
  exact ⟨fun L M N hE hN => (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.2 L M N hE hN,
    fun u v hq => (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 u v hq⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobson
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem closed_empty_of_universallyClosed_of_le_jacobson :
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), UniversallyClosed p → ∀ Z : Set X, IsClosed Z → (∀ x ∈ Z, ¬ I ≤ (p x).asIdeal) → Z = ∅ := by
  intro R _ I hI X p hp Z hZ hmiss
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (p.base '' Z) := p.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (p x).isPrime.ne_top
  let q : Spec (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have hq : q ∈ closure {p.base x} := (PrimeSpectrum.le_iff_mem_closure _ _).mp hle
  have hq' : q ∈ p.base '' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem p.base hx)) hcl hq
  obtain ⟨y, hy, hyq⟩ := hq'
  apply hmiss y hy
  have hmy : (p y).asIdeal = m := by
    show (p.base y).asIdeal = m
    rw [hyq]
  rw [hmy]
  refine hI.trans ?_
  exact sInf_le ⟨bot_le, hm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

namespace GlobalTheory.FieldDimCoheight

theorem coheight_add_dim_closure_eq (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) [LocallyOfFiniteType p] (z : X) :
    (Order.coheight z : WithBot ℕ∞) + topologicalKrullDim (closure ({z} : Set X)) =
      topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [add_comm]
    haveI : QuasiSober (closure ({z} : Set X)) :=
      isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  let φ := Spec.preimage (hU.fromSpec ≫ p)
  have hφ : Spec.map φ = hU.fromSpec ≫ p := Spec.map_preimage _
  let _ : Algebra F Γ(X, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have : Nonempty (Spec Γ(X, U)) := ⟨P⟩
  have hA : ringKrullDim Γ(X, U) = topologicalKrullDim X := by
    rw [← OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X _ p hU.fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
  have h2 := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F P.asIdeal
  let x : Spec Γ(X, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(X, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]
  have h3 : ringKrullDim (Γ(X, U) ⧸ P.asIdeal) ≤ topologicalKrullDim (closure ({z} : Set X)) := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec P, hP]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [← hA, ← h2, hPh]
  exact add_le_add le_rfl h3

theorem eq_one_iff_of_add_eq {c : ℕ∞} {t : WithBot ℕ∞} {e : ℕ}
    (h : (c : WithBot ℕ∞) + t = (e + 1 : ℕ)) : c = 1 ↔ t = e := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h' : c + t = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have hc : c ≠ ⊤ := by rintro rfl; rw [top_add] at h'; exact ENat.natCast_ne_top _ h'.symm
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h'; exact ENat.natCast_ne_top _ h'.symm
    lift c to ℕ using hc
    lift t to ℕ using ht
    have h'' : c + t = e + 1 := by exact_mod_cast h'
    constructor
    · intro h1
      have : c = 1 := by exact_mod_cast h1
      have : t = e := by omega
      exact_mod_cast this
    · intro h1
      have : t = e := by exact_mod_cast h1
      have : c = 1 := by omega
      exact_mod_cast this

theorem coheight_eq_one_iff : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F)
    (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ z : X,
    Order.coheight z = 1 ↔ topologicalKrullDim (closure ({z} : Set X)) = e := by
  intro F _ X _ p e hp hd z
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  exact eq_one_iff_of_add_eq ((coheight_add_dim_closure_eq F X p z).trans hd)

end GlobalTheory.FieldDimCoheight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeOfLevels
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CcStep

theorem cc_step : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  intro R _ F S E p I _ _ G c h
  apply GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F I (G ⋙ bc p) ((bc p).mapCone c)
  intro k
  obtain ⟨X, r, e, he, hc⟩ := h k
  obtain ⟨φ⟩ := GlobalTheory.EtC.BcLevel.bc_level S E p k X r e he
  have hiso := (GlobalTheory.EtC.eqv_basic R F).1
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ bc (sch.map r)) ((G ⋙ bc p) ⋙ (evaluation _ PSh).obj k ⋙ disc)
    ((bc (sch.map r)).mapCone c) (((evaluation _ PSh).obj k ⋙ disc).mapCone ((bc p).mapCone c))
    (Functor.whiskerLeft G φ.hom) (φ.hom.app c.pt) ?_ ?_ ?_).1 hc
  · intro i
    exact φ.hom.naturality (c.π.app i)
  · intro i
    exact hiso _ _ _ inferInstance
  · exact hiso _ _ _ inferInstance

end GlobalTheory.EtC.CcStep
end


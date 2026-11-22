import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.InvAlg

theorem ker_evalₐ {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval J.fg_of_isNoetherianRing, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

theorem completion_invariants_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  intro R _ _ _ hR R' _ _ _ _ hinj hgal C' _ _ _ _ _ act hact O _ _ _ _ i h1 h2 h3 C hC hCft hCfin e
  classical
  haveI : IsNoetherianRing R := hR.1
  haveI := hCft
  haveI := hCfin
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  haveI : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing R O
  haveI : Finite (Gal (algebraMap R R')) := hgal.1
  let T := TensorProduct R O R'
  let JC : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let JO : Ideal O := (maximalIdeal R).map (algebraMap R O)
  let IC : Ideal C' := JC.map (algebraMap C C')
  let IT : Ideal T := JO.map (algebraMap O T)
  let gC : Gal (algebraMap R R') → (C' →ₐ[C] C') := fun σ =>
    { (act σ).toRingEquiv.toRingHom with commutes' := fun c => (hC _).1 c.2 σ }

  have hfixC : ∀ x : C', x ∈ LinearMap.range (Algebra.linearMap C C') ↔ ∀ σ, (gC σ).toLinearMap x = x := by
    intro x; constructor
    · rintro ⟨c, rfl⟩ σ; exact (gC σ).commutes c
    · intro hx; exact ⟨⟨x, (hC x).2 hx⟩, rfl⟩
  have hmC := GlobalTheory.T.adicCompletion_map_injective_and_invariants C JC C C' (Algebra.linearMap C C') _ (fun σ => (gC σ).toLinearMap) Subtype.val_injective hfixC
  obtain ⟨injC, rangeC⟩ := GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module C C' JC _ gC hmC.1 hmC.2

  obtain ⟨injOT, fixOT⟩ := GlobalTheory.T.flat_tensor_galois_injective_invariants R R' O hinj hgal
  have hfixO : ∀ t : T, t ∈ LinearMap.range (Algebra.linearMap O T) ↔
      ∀ σ, (galTensor O σ).toLinearMap t = t := by
    intro t; constructor
    · rintro ⟨x, rfl⟩ σ; exact (galTensor O σ).commutes x
    · intro ht; obtain ⟨x, hx⟩ := fixOT t ht; exact ⟨x, hx⟩
  have hmO := GlobalTheory.T.adicCompletion_map_injective_and_invariants O JO O T (Algebra.linearMap O T) _ (fun σ => (galTensor O σ).toLinearMap) injOT hfixO
  obtain ⟨injO, rangeO⟩ := GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module O T JO _ (galTensor O) hmO.1 hmO.2

  have hIT : IT = (maximalIdeal R).map (algebraMap R T) := by
    simp only [IT, JO, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hIC : IC = (maximalIdeal R).map (algebraMap R C') := by
    simp only [IC, JC, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hCσ : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC := fun σ => map_algebraMap_le (gC σ) JC
  obtain ⟨Ψ, hΨσ, hΨi⟩ := GlobalTheory.T.adicCompletion_equivariant_equiv_of_level_isos R (maximalIdeal R) R' C' act hact O i h1 h2 h3 IT IC hIT hIC
    (fun σ => map_algebraMap_le (galTensor O σ) JO) hCσ
  let κC := cmap (algebraMap C C') JC IC le_rfl
  let κO1 := cmap (algebraMap O T) JO IT le_rfl
  let κO : AdicCompletion JO O →+* AdicCompletion IC C' := (Ψ : _ →+* _).comp κO1
  have hr : ∀ y, y ∈ Set.range κO ↔ y ∈ Set.range κC := by
    intro y
    rw [rangeC y]
    have : y ∈ Set.range κO ↔ Ψ.symm y ∈ Set.range κO1 := by
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by simp [κO]⟩
      · rintro ⟨a, ha⟩; exact ⟨a, by simp [κO, ha]⟩
    rw [this, rangeO]
    refine forall_congr' fun σ => ?_
    rw [← Ψ.injective.eq_iff, hΨσ, Ψ.apply_symm_apply]
  have hrange : κO.range = κC.range := by ext y; exact hr y
  have injκO : Function.Injective κO := Ψ.injective.comp injO
  let eO : AdicCompletion JO O ≃+* κO.range := RingEquiv.ofBijective κO.rangeRestrict
    ⟨fun a b h => injκO (congrArg Subtype.val h), κO.rangeRestrict_surjective⟩
  let eC : AdicCompletion JC C ≃+* κC.range := RingEquiv.ofBijective κC.rangeRestrict
    ⟨fun a b h => injC (congrArg Subtype.val h), κC.rangeRestrict_surjective⟩
  let Θ : AdicCompletion JO O ≃+* AdicCompletion JC C := (eO.trans (RingEquiv.subringCongr hrange)).trans eC.symm
  have hΘ : ∀ a, κC (Θ a) = κO a := fun a =>
    congrArg Subtype.val (eC.apply_symm_apply ((RingEquiv.subringCongr hrange) (eO a)))

  have hΘR : ∀ r : R, Θ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    apply injC
    rw [hΘ]
    show Ψ (κO1 (algebraMap R (AdicCompletion JO O) r)) = κC (algebraMap R (AdicCompletion JC C) r)
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, cmap_of, cmap_of,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← AdicCompletion.algebraMap_apply IT r, ← AdicCompletion.algebraMap_apply IC r]
    exact Ψ.commutes r
  have hOm : ∀ k, (JO ^ k).map (algebraMap O (AdicCompletion JO O)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JO O)) := by
    intro k; simp only [JO, Ideal.map_pow, Ideal.map_map]; rfl
  have hCm : ∀ k, (JC ^ k).map (algebraMap C (AdicCompletion JC C)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JC C)) := by
    intro k; simp only [JC, Ideal.map_pow, Ideal.map_map]; rfl
  have key : ∀ a, AdicCompletion.evalₐ JC (e + 1) (Θ a) = 0 ↔ AdicCompletion.evalₐ JO (e + 1) a = 0 := by
    intro a
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, ker_evalₐ, ker_evalₐ, hOm, hCm]
    have hmap : ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JC C))) =
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JO O))).map (Θ : _ →+* _) := by
      rw [Ideal.map_map]; congr 1; exact RingHom.ext fun r => (hΘR r).symm
    rw [hmap, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
  have hJC : JC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C) := (Ideal.map_pow _ _ _).symm
  let ψ0 : O →+* C ⧸ JC ^ (e + 1) :=
    (AdicCompletion.evalₐ JC (e + 1) : AdicCompletion JC C →+* C ⧸ JC ^ (e + 1)).comp
      ((Θ : _ →+* _).comp (algebraMap O (AdicCompletion JO O)))
  have hψ0 : ∀ x, ψ0 x = AdicCompletion.evalₐ JC (e + 1) (Θ (AdicCompletion.of JO O x)) := fun x => rfl
  have hsurj : Function.Surjective ψ0 := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ JO (e + 1) (Θ.symm (AdicCompletion.of JC C c)))
    refine ⟨x, ?_⟩
    have h0 : AdicCompletion.evalₐ JO (e + 1)
        (AdicCompletion.of JO O x - Θ.symm (AdicCompletion.of JC C c)) = 0 := by
      rw [map_sub, AdicCompletion.evalₐ_of, hx, sub_self]
    have h1 := (key _).2 h0
    rw [map_sub, map_sub, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_of, sub_eq_zero] at h1
    rw [hψ0, h1]
  have hker : RingHom.ker ψ0 = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O) := by
    ext x
    rw [RingHom.mem_ker, hψ0, key, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    simp only [JO, Ideal.map_pow]
  let gR : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃+*
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).trans
      (Ideal.quotEquivOfEq hJC)
  have hgR : ∀ x, gR (Ideal.Quotient.mk _ x) = Ideal.quotEquivOfEq hJC (ψ0 x) := fun x => rfl
  let gm : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R]
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    AlgEquiv.ofRingEquiv (f := gR) (fun r => by
      change gR (Ideal.Quotient.mk _ (algebraMap R O r)) = Ideal.Quotient.mk _ (algebraMap R C r)
      rw [hgR, hψ0, ← AdicCompletion.algebraMap_apply JO r, hΘR, AdicCompletion.algebraMap_apply,
        AdicCompletion.evalₐ_of, Ideal.quotEquivOfEq_mk])
  refine ⟨gm, fun x c hxc => ?_⟩
  have h1' : ψ0 x = Ideal.Quotient.mk (JC ^ (e + 1)) c := by
    apply (Ideal.quotEquivOfEq hJC).injective
    rw [Ideal.quotEquivOfEq_mk]; exact (hgR x).symm.trans hxc
  have h2' : AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R')))) =
      Ideal.Quotient.mk (IC ^ (e + 1)) (c : C') := by
    have := congrArg (Ideal.quotientMap (IC ^ (e + 1)) (algebraMap C C')
      (pow_le_comap (algebraMap C C') (le_rfl : JC.map (algebraMap C C') ≤ IC) (e + 1))) h1'
    rw [hψ0, ← evalₐ_cmap] at this
    change AdicCompletion.evalₐ IC (e + 1) (κC (Θ _)) = _ at this
    rw [hΘ] at this
    rw [show κO (AdicCompletion.of JO O x) = Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R'))) from by
      show Ψ (κO1 _) = _
      rw [cmap_of]; rfl] at this
    rw [this, Ideal.quotientMap_mk]; rfl
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i e x)
  have h3' := hΨi e x y hy
  rw [h2', Ideal.Quotient.eq] at h3'
  rw [← hy, Ideal.Quotient.eq]
  have hpow : IC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C') := by rw [hIC, Ideal.map_pow]
  rw [← hpow]; exact h3'

end GlobalTheory.InvAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecomposition
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecC

theorem frame_power_identity : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L M : LB A.left) (g : ℕ) (uL : HolUnif A L g) (uM : HolUnif A M g)
    (HL HM : Matrix (Fin g) (Fin g) ℂ) (χL : uL.Λ → ℂ) (χM : uM.Λ → ℂ), uM.ex = uL.ex →
    GlobalTheory.TorusRM.IsFactorAH uL HL χL → GlobalTheory.TorusRM.IsFactorAH uM HM χM →
    (∀ l, χL l = 1 ∨ χL l = -1) → (∀ l, χM l = 1 ∨ χM l = -1) →
    ∀ (N : ℕ) (K : Type) [Fintype K] (F : K → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ), Even N → (∀ k, Even (ε k)) →
    (∀ k, ∀ l ∈ uL.Λ, F k l ∈ uM.Λ) →
    (∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ HL.mulVec (star w)) = ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k w)))) →
    ∀ (l : uL.Λ) (i : L.ι) (j : K → M.ι) (z : Fin g → ℂ), ⊤ ≤ (uL.ex z).left ⁻¹ᵁ L.U i →
      (∀ k, ⊤ ≤ (uM.ex (F k z)).left ⁻¹ᵁ M.U (j k)) →
      uL.fr i z ^ N * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k = uL.fr i (z + l) ^ N * ∏ k, uM.fr (j k) (F k z) ^ ε k := by
  intro A _ L M g uL uM HL HM χL χM _ hfL hfM hχL hχM N K _ F ε hN hε hF hdec l i j z hi hj
  have hL1 := hfL.2.2 l i z hi
  have hM1 : ∀ k, uM.fr (j k) (F k z) = χM ⟨F k l, hF k l l.2⟩ *
      Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) * uM.fr (j k) (F k (z + l)) := fun k => by
    rw [map_add]
    exact hfM.2.2 ⟨F k l, hF k l l.2⟩ (j k) (F k z) (hj k)
  have hcL : χL l ^ N = 1 := by
    rcases hχL l with h | h <;> rw [h]
    · exact one_pow N
    · exact hN.neg_one_pow
  have hcM : ∀ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k = 1 := fun k => by
    rcases hχM ⟨F k l, hF k l l.2⟩ with h | h <;> rw [h]
    · exact one_zpow _
    · exact (hε k).neg_one_zpow
  have hR : ∏ k, uM.fr (j k) (F k z) ^ ε k = (∏ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k) *
      (∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k) * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hM1 k, mul_zpow, mul_zpow]
  have key : Complex.exp (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) ^ N =
      ∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k := by
    rw [← Complex.exp_nat_mul, Finset.prod_congr rfl (fun k _ => (Complex.exp_int_mul _ (ε k)).symm),
      ← Complex.exp_sum]
    congr 1
    have h1 := hdec z l
    have h2 := hdec l l
    calc (N : ℂ) * (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))))
        = Real.pi * ((N : ℂ) * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) +
          Real.pi / 2 * ((N : ℂ) * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) := by ring
      _ = Real.pi * ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
          Real.pi / 2 * ∑ k, (ε k : ℂ) * (F k l ⬝ᵥ HM.mulVec (star (F k l))) := by rw [h1, h2]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
  rw [hR, hL1, mul_pow, mul_pow, hcL, Finset.prod_eq_one (fun k _ => hcM k), key]
  ring

theorem lbIso_of_sameFactor (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (X Y : LB A.left) (g : ℕ)
    (u : HolUnif A X g) (v : HolUnif A Y g) (hX : X.IsLB) (hY : Y.IsLB) (hex : v.ex = u.ex)
    (hper : ∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ X.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ Y.U j →
      u.fr i z * v.fr j (z + l) = u.fr i (z + l) * v.fr j z) : LBIso X Y := by
  haveI := hA.comm
  haveI := hA.smooth
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := HolUnifSec.exists_isFn (SameFactor.divUnif u v hex) hA hp (LB.isLB_div hY hX)
    (θ := fun _ => 1) (differentiable_const _) (by
      intro l hl p z hz
      obtain ⟨hz1, hz2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e := hper ⟨l, hl⟩ p.2 p.1 z hz2 hz1
      have hl' : u.ex (z + l) = u.ex z := by
        rw [u.ex_add, (u.ker _).2 hl, _root_.mul_one]
      have n1 := u.fr_ne p.2 z hz2
      have n2 := u.fr_ne p.2 (z + l) (by rw [hl']; exact hz2)
      change 1 * (v.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (v.fr p.1 z * (u.fr p.2 z)⁻¹)
      field_simp
      linear_combination e)
  exact SameFactor.exists_gen_of_isFn _ s _ hs fun _ => one_ne_zero

theorem sqDec_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB →
    RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L →
    LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  intro A _ hA L M hL hM haL haM hsL hsM
  haveI := hA.comm
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim ℂ A hA
  obtain ⟨L₀, ⟨u₀⟩⟩ := HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨uL, HL, χL, hexL, hfL⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ L hL
  obtain ⟨uM, HM, χM, hexM, hfM⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  have hposL := AmpleHermPos.re_form_pos_of_relAmple A hA L hL haL g uL HL χL hfL.1 hfL.2.1 hfL.2.2
  have hposM := AmpleHermPos.re_form_pos_of_relAmple A hA M hM haM g uM HM χM hfM.1 hfM.2.1 hfM.2.2
  have hAHL := TorusRM.isAH_of_isFactorAH hfL hposL
  have hAHM := TorusRM.isAH_of_isFactorAH hfM hposM
  have hex : uM.ex = uL.ex := hexM.trans hexL.symm
  have hΛ : ∀ z, z ∈ uM.Λ ↔ z ∈ uL.Λ := fun z => by rw [← uM.ker, ← uL.ker, hex]
  have hχL := ThetaUnifCompare.chi_eq_one_or_of_sym hL (sym_of_lbIso_neg hsL.symm) hAHL
  have hχM := ThetaUnifCompare.chi_eq_one_or_of_sym hM (sym_of_lbIso_neg hsM.symm) hAHM
  have hiL : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HL.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hL hAHL ⟨l, hl⟩ ⟨m, hm⟩
  have hiM : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HM.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hM hAHM ⟨l, (hΛ l).2 hl⟩ ⟨m, (hΛ m).2 hm⟩
  obtain ⟨N, a₀, r, a, F, hN, ha₀, hNe, ha₀e, hae, hF, hdec⟩ :=
    GlobalTheory.T.exists_even_multiple_hermitian_positive_combination g uL.Λ uL.discrete uL.full HL HM hAHL.1 hAHM.1 hposL hposM hiL hiM
  choose β hβ hβF using fun i => GlobalTheory.T.exists_endomorphism_of_lattice_preserving_linear A hA L g uL (F i) (hF i)
  let f : Option (Fin r) → (A ⟶ A) := fun o => o.elim (𝟙 A) β
  let FF : Option (Fin r) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun o => o.elim LinearMap.id F
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  have hfF : ∀ k z, uM.ex (FF k z) = uL.ex z ≫ f k := by
    intro k z
    cases k with
    | none => simp [FF, f, hex]
    | some i => simpa [FF, f, hex] using hβF i z
  obtain ⟨u₁, hex₁, -, hfr₁⟩ := exists_holUnif_linComb A A L M g g uL uM _ f FF ε hfF
  have hcomb : LB.LinComb M (fun k => (f k).left) ε = LB.LinComb M (fun (o : Option (Fin r)) => o.elim (𝟙 A.left) fun i => (β i).left)
      (fun (o : Option (Fin r)) => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) := by
    congr 1
    funext o
    cases o <;> rfl
  refine ⟨N, a₀, r, a, β, hN, ha₀, hβ, ?_⟩
  rw [← hcomb]
  refine lbIso_of_sameFactor A hA _ _ g (ThetaGAGA.powFrame uL N) u₁ (isLB_lbPow hL N) (LB.isLB_linComb hM _ _)
    hex₁ ?_
  intro l i j z hi hj
  refine (congrArg₂ (· * ·) rfl (hfr₁ j (z + l))).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (hfr₁ j z)).symm)
  have hi' := ThetaGAGA.top_le_of_lbPow uL N i hi
  have hj' : ∀ k, ⊤ ≤ (uM.ex (FF k z)).left ⁻¹ᵁ M.U (j k) := fun k => by
    rw [hfF k z]
    exact (CubeValues.le_preimage_wchart (uL.ex z).left M (fun k => (f k).left) j).1 hj k
  exact frame_power_identity A L M g uL uM HL HM χL χM hex hfL hfM hχL hχM N _ FF ε hNe
    (fun k => by cases k with | none => exact (Int.even_coe_nat _).2 ha₀e | some i => exact (Int.even_coe_nat _).2 (hae i))
    (fun k l hl => by cases k with | none => exact (hΛ l).2 hl | some i => exact (hΛ _).2 (hF i l hl))
    (fun z w => by rw [Fintype.sum_option, hdec z w]; simp [FF, ε]) l (i PUnit.unit) j z hi' hj'

end GlobalTheory.SqDecC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurveTangentCompat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open scoped nonZeroDivisors

namespace GlobalTheory.CMTorsion.ConjPt

theorem coords_conj : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair)
    (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (a a' : K),
    (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) →
    coords Λ₁ Ω₁ (io a') = (g : ℂ →+* ℂ) ∘ coords Λ₀ Ω₀ (io a) := by
  intro K _ _ io g t Λ₀ Λ₁ Ω₀ Ω₁ hT a a' hint
  obtain ⟨hΩ₀, hΩ₁, hfix, hL0, ⟨𝔞, h𝔞, hL1⟩, h2, h3, hval⟩ := hT
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hd : (t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := (hA _).2 hint
  have hmem𝔞 : a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ io '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ io '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : io a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← io.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : io a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← io.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  by_cases ha : io a ∈ Λ₀.lattice
  · have ha' : io a' ∈ Λ₁.lattice := by
      rw [h1, hmem𝔞]
      have := add_mem hd ((hone a).1 (h0.1 ha))
      rwa [sub_add_cancel] at this
    simp only [coords, if_pos ha, if_pos ha']
    ext i; fin_cases i <;> simp
  · have ha' : io a' ∉ Λ₁.lattice := by
      intro h
      apply ha
      rw [h0, hone]
      have := sub_mem (hmem𝔞.1 (h1.1 h)) hd
      rwa [sub_sub_cancel] at this
    obtain ⟨e2, e3⟩ := hval a a' ha hint
    simp only [coords, if_neg ha, if_neg ha']
    have e3' : g (Λ₀.derivWeierstrassP (io a) / (2 * Ω₀ ^ 3)) = Λ₁.derivWeierstrassP (io a') / (2 * Ω₁ ^ 3) := by
      rw [mul_comm, ← div_div, map_div₀, e3, map_ofNat, div_div, mul_comm]
    ext i; fin_cases i <;> simp [e2, e3']

end GlobalTheory.CMTorsion.ConjPt

namespace GlobalTheory.CMTorsion.ConjPt

theorem conj_pt : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (a a' : K), (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) → pt Λ₁ Ω₁ (io a') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (io a) := by
  intro K _ _ io g t Λ₀ Λ₁ Ω₀ Ω₁ hT h a a' hint
  have e := coords_conj K io g t Λ₀ Λ₁ Ω₀ Ω₁ hT a a' hint
  unfold pt
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, spMap, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  exact GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ (by ext; simp) e _

end GlobalTheory.CMTorsion.ConjPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationDifferentialZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjTangent

theorem isDiff_zero_of_isGrpPullback : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (n n' : ℕ) (u : HolUnif A L n)
    (u' : HolUnif A' L' n') (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
    v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff 0 v → u'.IsDiff 0 v' := by
  intro A A' _ _ p g h L L' n n' u u' v v' e hd U hU f
  haveI : IsIso (spMap (g : ℂ →+* ℂ)) :=
    (inferInstance : IsIso (Spec.map (g.toCommRingCatIso).hom))
  haveI : IsIso p := h.1.isIso_fst_of_isIso
  have e2 : v'.left = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv p).2 e
  have h2 : ⊤ ≤ v.left ⁻¹ᵁ (inv p ⁻¹ᵁ U) := by
    refine (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).2 fun q _ => ?_
    have hq := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).1 hU (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    have hs : ∀ a b : PrimeSpectrum (DualNumber ℂ), a = b := fun a b => by
      obtain ⟨a, rfl⟩ := GlobalTheory.TangentOrigin.spMap_fst_surjective a
      obtain ⟨b, rfl⟩ := GlobalTheory.TangentOrigin.spMap_fst_surjective b
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) a b]
    rw [e2] at hq
    change v.left (spMap GlobalTheory.TangentOrigin.fstC q) ∈ inv p ⁻¹ᵁ U
    rw [hs (spMap GlobalTheory.TangentOrigin.fstC q)
      (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) (spMap GlobalTheory.TangentOrigin.fstC q))]
    exact hq
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p →
      TangentOrigin.evalPt y U hy f = Chart.dualMapR (g : ℂ →+* ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) v.left _ h2 (((inv p).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv p).app U).hom f)
  rw [map_zero] at e3 ⊢
  simp only [Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact (congrArg (g : ℂ →+* ℂ) e3).trans (map_zero _)

end GlobalTheory.ConjTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMul
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem bas_repr_mul (n : ℕ) (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ T, ∑ U, (bas n).repr x T * (bas n).repr y U * (bas n).repr (bas n T * bas n U) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

theorem contDiff_coeff_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  intro n m F G
  refine ⟨fun s hF hG S => ?_, fun v hF hG S => ?_⟩
  · rw [show (fun v => (bas n).repr (F v * G v) S) = _ from funext fun v => bas_repr_mul n (F v) (G v) S]
    exact ContDiffOn.sum fun T _ => ContDiffOn.sum fun U _ => ((hF T).mul (hG U)).mul contDiffOn_const
  · rw [show (fun x => (bas n).repr (F x * G x) S) = _ from funext fun x => bas_repr_mul n (F x) (G x) S]
    exact DifferentiableAt.fun_sum fun T _ => DifferentiableAt.fun_sum fun U _ =>
      ((hF T).fun_mul (hG U)).fun_mul (differentiableAt_const _)

end GlobalTheory.CxForm
end


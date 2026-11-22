import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.Untwist

theorem res_X_isZero {R : Type} [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) :=
  (injectiveResolution F).cocomplex.isZero_extend_X ComplexShape.embeddingUpNat n (fun i hi => by
    change (i : ℤ) = n at hi; omega)

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (y : Sec F U) : y = 0 := by
  have h := congrArg (fun φ : F ⟶ F => Sec.map φ y) (hF.eq_of_src (𝟙 F) 0)
  exact h

theorem sec_res_neg {R : Type} [CommRing R] (F : Shv R) {n : ℤ} (hn : n < 0) {U : Scheme.{0}} (y z : Sec ((res R F).X n) U) :
    y = z := (sec_eq_zero (res_X_isZero F n hn) y).trans (sec_eq_zero (res_X_isZero F n hn) z).symm

theorem cocycle_ext_zero {R : Type} [CommRing R] {X : Scheme.{0}} {F : Shv R}
    (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = ev β.1 0 0 (by simp) U x) : α = β := by
  refine Cocycle.ext (CupSpec.ev_ext _ _ fun p s hs U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using hs.symm
    exact h U x
  | succ p => exact sec_res_neg F (by omega) _ _

theorem cup_rootClass {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (a b : ℤ) :
    cup q (rootClass a ζ) (rootClass b ζ) = (rootClass (a + b) ζ : Ht q (sch.obj X) (0 + 0) (a + b)) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec a ζ
  obtain ⟨β, hβ, hβ'⟩ := rootClass_spec b ζ
  obtain ⟨γ, hγ, hγ'⟩ := rootClass_spec (a + b) ζ
  rw [← hα, ← hβ, ← hγ]
  refine Pair.cup_spec (twPair q a b) (sch.obj X) rfl α β γ ?_
  intro N w hw U x
  cases N with
  | zero =>
    obtain rfl : w = 0 := by simpa using hw.symm
    rw [Fin.sum_univ_one]
    change ev γ.1 0 0 _ U x = ((0 : ℤ) * 0).negOnePow • (twPair q a b).mul U 0 0 0 rfl (ev α.1 0 0 (by simp) U x) (ev β.1 0 0 (by simp) U x)
    have e1 : ev α.1 0 0 (by simp) U x = _ := hα' U x
    have e2 : ev β.1 0 0 (by simp) U x = _ := hβ' U x
    rw [e1, e2, mul_zero, Int.negOnePow_zero, one_smul]
    refine Eq.trans (hγ' U x) ?_
    change Sec.res (show U ⟶ X from x) _ = (twPair q a b).mul U 0 0 0 rfl (Sec.res (show U ⟶ X from x) _) (Sec.res (show U ⟶ X from x) _)
    rw [ClsSpec.res_resGen, ClsSpec.res_resGen, ClsSpec.res_resGen]
    exact (twPair_spec q a b U _).symm
  | succ N => exact sec_res_neg _ (by omega) _ _

theorem rootClass_zero {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) :
    rootClass 0 ζ = one q (sch.obj X) := by
  obtain ⟨α, hα, hα'⟩ := rootClass_spec 0 ζ
  obtain ⟨β, hβ, hβ'⟩ := one_spec q (sch.obj X) hX
  rw [← hα, ← hβ]
  refine congrArg CohomologyClass.mk (cocycle_ext_zero α β fun U x => ?_)
  rw [hα', hβ' U x (ζ.map x.appTop.hom), ClsSpec.res_resGen]

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h₁ : n = n') (h₂ : i = i') (h₃ : n' = n'') (h₄ : i' = i'') :
    (x.cast h₁ h₂).cast h₃ h₄ = x.cast (h₁.trans h₃) (h₂.trans h₄) := by
  subst h₁; subst h₂; subst h₃; subst h₄; rfl

theorem cast_add {n i n' i' : ℤ} (x y : Ht q E n i) (hn : n = n') (hi : i = i') :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem eq_cast_symm {n i n' i' : ℤ} {x : Ht q E n i} {y : Ht q E n' i'} (hn : n' = n) (hi : i' = i) (h : x = y.cast hn hi) :
    y = x.cast hn.symm hi.symm := by
  subst hn; subst hi; exact h.symm

theorem cup_cast_left {n m i j n' i' : ℤ} (x : Ht q E n i) (b : Ht q E m j) (hn : n = n') (hi : i = i') :
    cup q (x.cast hn hi) b = (cup q x b).cast (congrArg (· + m) hn) (congrArg (· + j) hi) := by
  subst hn; subst hi; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (a : Ht q E n i) (y : Ht q E m j) (hm : m = m') (hj : j = j') :
    cup q a (y.cast hm hj) = (cup q a y).cast (congrArg (n + ·) hm) (congrArg (i + ·) hj) := by
  subst hm; subst hj; rfl

theorem cup_cup_of_unit [NeZero q] (hE : Inv q E) {d e n i : ℤ} (u : Ht q E 0 d) (v : Ht q E 0 e) (hde : (0 : ℤ) = e + d)
    (hvu : cup q v u = (one q E).cast (by simp) hde) (a : Ht q E n i)
    {k : ℤ} (h₁ : 0 + n = n) (h₂ : d + i = k) (h₃ : 0 + n = n) (h₄ : e + k = i) :
    (cup q v ((cup q u a).cast h₁ h₂)).cast h₃ h₄ = a := by
  have hring := GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q E
  have hassoc := eq_cast_symm _ _ (hring.2.1 v u a)
  rw [cup_cast_right, cast_cast, hassoc, cast_cast, hvu, cup_cast_left, cast_cast, hring.1 hE a, cast_cast]
  rfl

end Cast

theorem rootClass_cast {q : ℕ} {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) {k k' : ℤ} (h : k = k') (hn : (0 : ℤ) = 0 + 0) :
    (rootClass k ζ).cast hn h = (rootClass k' ζ : Ht q (sch.obj X) (0 + 0) k') := by
  subst h; rfl

noncomputable def twistEquiv {q : ℕ} [NeZero q] {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (hX : Inv q (sch.obj X)) (n i j : ℤ) :
    Ht q (sch.obj X) n i ≃+ Ht q (sch.obj X) n j := by
  have key : ∀ d e : ℤ, ∀ hde : (0 : ℤ) = e + d,
      cup q (rootClass e ζ) (rootClass d ζ) = (one q (sch.obj X)).cast (by simp) hde := by
    intro d e hde
    rw [cup_rootClass, ← rootClass_zero ζ hX, rootClass_cast ζ hde]
  exact
    { toFun := fun a => (cup q (rootClass (j - i) ζ) a).cast (zero_add n) (by ring)
      invFun := fun b => (cup q (rootClass (i - j) ζ) b).cast (zero_add n) (by ring)
      left_inv := fun a => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) a _ _ _ _
      right_inv := fun b => cup_cup_of_unit hX _ _ (by ring) (key _ _ (by ring)) b _ _ _ _
      map_add' := fun a b => by simp only [map_add, cast_add] }

end GlobalTheory.EtC.Untwist

open GlobalTheory.EtC.Untwist in

theorem GlobalTheory.EtC.untwist : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  intro q _ A _ hq ⟨z, hz⟩ n i j
  let φ : A →+* Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hX : Inv q (sp A) := fun U ⟨x⟩ => by
    have h := (hq.map φ).map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
    simpa only [map_natCast] using h
  exact ⟨twistEquiv (Prim.map φ ⟨z, hq, hz⟩) hX n i j⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
section
set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt (f g : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) =
      _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← add_smul, show (fun z ↦ f z + g z) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt, ContinuousMultilinearMap.add_apply, mul_add]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_const_fun (c : ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => ?_]
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_congr_germ (f g : (I → ℂ) → ℂ) (h : f =ᶠ[𝓝 0] g) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem map_taylor_algHom (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ) :
    ψ (taylor N t f) = taylor N (fun i ↦ ψ (t i)) f := by
  unfold taylor
  simp only [map_sum, map_smul, map_prod]

set_option autoImplicit false in
open Filter Topology in
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) in
theorem _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span (f : (I → ℂ) → ℂ) :
    _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t) := by
  unfold _root_.GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ']
  have h0 : ∑ s : Fin 0 → I, ((↑(Nat.factorial 0))⁻¹ * (iteratedFDeriv ℂ 0 f 0)
      fun a ↦ Pi.single (s a) 1) • ∏ a, t (s a) = algebraMap ℂ D (f 0) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h0, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun s _ => ?_
  rw [Algebra.smul_def, Fin.prod_univ_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s 0, rfl⟩))

end

set_option autoImplicit false in
open Filter Topology in

theorem _root_.GlobalTheory.PeriodFamily.taylor_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = _root_.GlobalTheory.PeriodFamily.taylor N t f + _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → _root_.GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • _root_.GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → _root_.GlobalTheory.PeriodFamily.taylor N t f = _root_.GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (_root_.GlobalTheory.PeriodFamily.taylor N t f) = _root_.GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, _root_.GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  intro I _ _ D _ _ N t
  refine ⟨fun f g hf hg => _root_.GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t f g hf hg,
    fun c f hf => ?_, _root_.GlobalTheory.PeriodFamily.taylor_const_fun N t,
    _root_.GlobalTheory.PeriodFamily.taylor_congr_germ N t, fun D' _ _ ψ f => ?_,
    _root_.GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t⟩
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show (fun z ↦ c * f z) = fun z ↦ c • f z from rfl,
      iteratedFDeriv_const_smul_apply' hf.contDiffAt, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, smul_smul, mul_left_comm]
  · unfold _root_.GlobalTheory.PeriodFamily.taylor
    simp [map_sum, map_prod]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
section
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory

open Filter Topology in
open Filter Topology TopologicalSpace TensorProduct in

theorem _root_.GlobalTheory.tensor_hol_ext_of_values :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  intro E _ _ W D _ _ x y h
  classical
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hzp : ∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D)
      ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp))
      (fun _ _ ↦ Commute.all _ _) z = 0 := fun p hp => by
    rw [hz, map_sub, h p hp, sub_self]
  let b := Module.Free.chooseBasis ℂ D
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := _root_.GlobalTheory.AnPer.Hol W) b
  have hc : ∀ i, e z i = 0 := by
    intro i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    have hzero : (0 : _root_.GlobalTheory.AnPer.Hol W).fn p = 0 := by
      rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_zero]
    have h0 := hzp p hp
    rw [← e.symm_apply_apply z, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
      map_sum] at h0
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
      _root_.GlobalTheory.AnPer.Hol.ev_apply, Algebra.ofId_apply] at h0
    have h1 : ∑ j ∈ (e z).support, (e z j).fn p • b j = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    by_cases hi : i ∈ (e z).support
    · rw [linearIndependent_iff'.1 b.linearIndependent (e z).support (fun j => (e z j).fn p) h1 i hi,
        hzero]
    · rw [Finsupp.notMem_support_iff.1 hi]
  exact e.injective (by rw [map_zero]; exact Finsupp.ext hc)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (exact GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (intros; apply GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
section
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom
variable {F : Type} [Field F] [NumberField F]

open Classical in

def cls (I : Ideal (𝓞 F)) : ClassGroup (𝓞 F) := if h : I ∈ (Ideal (𝓞 F))⁰ then ClassGroup.mk0 ⟨I, h⟩ else 1

open Classical in

def wideInd (C : ClassGroup (𝓞 F)) : Ideal (𝓞 F) → ℚ := fun I => if cls I = C then 1 else 0

theorem cls_of_ne_bot {I : Ideal (𝓞 F)} (h : I ≠ ⊥) :
    cls I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero h⟩ := by
  rw [cls, dif_pos]

theorem cls_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : cls (I * J) = cls I * cls J := by
  rw [cls_of_ne_bot hI, cls_of_ne_bot hJ, cls_of_ne_bot (mul_ne_zero hI hJ), ← map_mul]
  rfl

theorem cls_span {a : 𝓞 F} (ha : a ≠ 0) : cls (Ideal.span {a}) = 1 := by
  have h : Ideal.span {a} ≠ ⊥ := by simpa using ha
  rw [cls_of_ne_bot h, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨a, rfl⟩⟩

theorem cls_span_mul {a : 𝓞 F} (ha : a ≠ 0) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : cls (Ideal.span {a} * I) = cls I := by
  rw [cls_mul (by simpa using ha) hI, cls_span ha, one_mul]

theorem isRayFun_wideInd (𝔣 : Ideal (𝓞 F)) (C : ClassGroup (𝓞 F)) : IsRayFun 𝔣 (wideInd C) := by
  intro I J hI hJ e
  obtain ⟨a, b, ha, hb, -, -, -, e⟩ := e
  have : cls I = cls J := by rw [← cls_span_mul ha hI.1, e, cls_span_mul hb hJ.1]
  unfold wideInd
  rw [this]

theorem translate_wideInd {a : 𝓞 F} (ha : a ≠ 0) (C : ClassGroup (𝓞 F)) :
    GlobalTheory.RayZeta.translate (Ideal.span {a}) (wideInd C) = wideInd C := by
  funext I
  by_cases hI : I = ⊥
  · simp [GlobalTheory.RayZeta.translate, hI]
  · simp only [GlobalTheory.RayZeta.translate, wideInd]
    rw [cls_span_mul ha hI]

end GlobalTheory.ZetaDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportModularFamilyGL2ZModWeierstrass
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem transport_GL : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  classical
  intro g N N' w _ a A F F' τ₀ τ₁ ω₀ ω₁ hN' hdiv hζ hF hFF' hω₀ h4 h6 hwp α
  let e : Fin 2 → Fin 2 → ZMod N := fun i => Pi.single i 1
  let m : Fin 2 × Bool → ℕ := fun s => if s.2 then 3 else 2
  let u : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β =>
    if s.2 then wpd N (vmul (e s.1) (β * 1)) else wp N (vmul (e s.1) (β * 1))
  let u' : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β => u s (β * dg a)
  have hact : ActBij (gact N 1) := (GlobalTheory.WpFam.Act.isRAct_gact N 1).actBij
  have hu : ∀ s, IsFam (gact N 1) (m s) (u s) := by
    rintro ⟨i, _ | _⟩
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).1
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).2
  have huu' : ∀ s β, QConj g N' (u s β) (u' s β) := by
    rintro ⟨i, _ | _⟩ β
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).2.1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
  have hsep : ∀ β, (∀ s, u s β τ₀ = u s α τ₀) → F β τ₀ = F α τ₀ := by
    intro β hβ
    have : β = α := GlobalTheory.WpFam.SepGL.main N τ₀ β α fun i =>
      ⟨by simpa [u] using hβ (i, false), by simpa [u] using hβ (i, true)⟩
    rw [this]
  have hα : α * A * (dg a)⁻¹ * dg a = α * A := by group
  have hval : ∀ s, g (u s α τ₀ / ω₀ ^ m s) = u' s (α * A * (dg a)⁻¹) τ₁ / ω₁ ^ m s := by
    rintro ⟨i, _ | _⟩
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).1
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).2
  have key := GlobalTheory.QFam.transport_of_separating g (GL (Fin 2) (ZMod N)) (Fin 2 × Bool) (gact N 1) N' w
    m F (fun β => F' (β * dg a)) u u' τ₀ τ₁ ω₀ ω₁ hN' hact hF hu hFF' huu' hω₀ h4 h6 α
    (α * A * (dg a)⁻¹) hsep hval
  simpa [hα] using key

end GlobalTheory.WpFamGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMu
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WinLift

theorem lift_solves_div_frob_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V G0 hP hθ i m
  have ent : ∀ (c : Ainf p O) (i : Fin d ⊕ Fin k) (m : Fin h),
      (V * blk d k c 1 * G0.map WittVector.frobenius) i m =
        ∑ l, V i l * (Sum.elim (fun _ => c) (fun _ => (1 : Ainf p O)) l *
          WittVector.frobenius (G0 l m)) := by
    intro c i m
    rw [Matrix.mul_apply]
    simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h1 : ∀ l, ∃ w : Ainf p O,
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l *
        WittVector.frobenius (G0 l m) = WittVector.frobenius (xi ε) * w := by
    rintro (l | l)
    · exact ⟨_, rfl⟩
    · have hmem : G0 (Sum.inr l) m ∈ RingHom.ker (WittVector.fontaineTheta O p) := hθ l m
      rw [AinfXi.ker_theta hv ε (root_prim hε), Ideal.mem_span_singleton'] at hmem
      obtain ⟨w, hw⟩ := hmem
      exact ⟨WittVector.frobenius w, by rw [← hw, map_mul]; simp; ring⟩
  choose w hw using h1
  have hE : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
      WittVector.frobenius (xi ε) * G0 i m =
        WittVector.frobenius (xi ε) * ((∑ l, V i l * w l) - G0 i m) := by
    rw [ent]
    simp_rw [hw]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdiff : ∀ l : Fin d ⊕ Fin k, Sandwich.mu ε ∣
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
        Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l := by
    rintro (l | l)
    · exact mu_dvd_frob_xi_sub ε
    · simp
  have hmu : Sandwich.mu ε ∣
      (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m := by
    have hPim := hP i m
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPim
    have key : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m -
        ((V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius) i m - (p : Ainf p O) * G0 i m) =
        (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
          Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
            WittVector.frobenius (G0 l m))) -
        (WittVector.frobenius (xi ε) - p) * G0 i m := by
      rw [ent, ent]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    have hR : Sandwich.mu ε ∣ (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε))
        (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
          WittVector.frobenius (G0 l m))) - (WittVector.frobenius (xi ε) - p) * G0 i m :=
      dvd_sub (Finset.dvd_sum fun l _ => Dvd.dvd.mul_left ((hdiff l).mul_right _) _)
        ((mu_dvd_frob_xi_sub ε).mul_right _)
    rw [← key] at hR
    have := dvd_add hR hPim
    rwa [sub_add_cancel] at this
  rw [hE] at hmu ⊢
  exact mul_dvd_mul_left _ (mu_dvd_of_xi_mul F _ hmu)

end GlobalTheory.WinLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_virtualCharacter_norm_one_support : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → Kills (fun δ => X (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (exact GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (intros; apply GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAtSimpleZeroOfWeightedSqIntegrableStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_simple_zero_of_weighted_sq_integrable : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ u : V n → ℂ, ContinuousOn u O → ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ → u p = 0 := by
  first | exact @GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable | exact GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable | (intros; apply GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyFromFibresStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_property_from_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  first | exact @GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres | exact GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres | (intros; apply GlobalTheory.AbCoh.Wedge.wedgeO_of_fibres <;> assumption)
end


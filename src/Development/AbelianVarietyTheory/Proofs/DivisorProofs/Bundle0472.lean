import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmul
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.OmLoc

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem pow_smul_d_mem (B : Subalgebra k K) {f v : K} (hf : f ∈ B) (M : ℕ) (hw : v * f ^ M ∈ B) :
    (f ^ (M + M)) • ι1 (D k K v) ∈ omB k K B 1 := by
  have hD : ∀ u ∈ B, ι1 (D k K u) ∈ omB k K B 1 := by
    intro u hu
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, fun _ => u, fun _ => hu, ?_⟩
    rw [one_smul, ExteriorAlgebra.ιMulti_apply]
    simp
  have hc : ∀ c ∈ B, ∀ a ∈ omB k K B 1, c • a ∈ omB k K B 1 := fun c hc a ha =>
    ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B 1 1).2.1 a ha).2.2.2 c hc
  have key : (f ^ (M + M)) • ι1 (D k K v) =
      f ^ M • ι1 (D k K (v * f ^ M)) - (v * f ^ M) • ι1 (D k K (f ^ M)) := by
    rw [Derivation.leibniz, map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul, pow_add,
      mul_comm (f ^ M) v]
    abel
  rw [key]
  exact sub_mem (hc _ (pow_mem hf M) _ (hD _ hw)) (hc _ hw _ (hD _ (pow_mem hf M)))

end GlobalTheory.PD.OmLoc

namespace GlobalTheory

theorem omB_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K),
      y ∈ omB k K (rB k K x I) q ↔
        ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  intro k _ _ F K _ _ _ _ _ _ d x h I i hi q y
  set f := algebraMap F K (∏ j ∈ I, x j / x i) with hfdef
  obtain ⟨hmono1, -⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)
  obtain ⟨-, hloc⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi
  have hBB' : rB k K x {i} ≤ rB k K x I := hmono1 I (Finset.singleton_subset_iff.2 hi)
  have hfB : f ∈ rB k K x {i} := by
    have hz : (∏ j ∈ I, x j / x i) ∈ rA k x {i} :=
      Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
    show IsIntegral (rA k x {i}) f
    exact isIntegral_algebraMap (R := rA k x {i}) (A := K) (x := ⟨_, hz⟩)
  have hf0 : f ≠ 0 :=
    (map_ne_zero (algebraMap F K)).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.pd.ne j) (h.pd.ne i))
  have hfinv : f⁻¹ ∈ rB k K x I :=
    (hloc _).2 ⟨1, by rw [pow_one, inv_mul_cancel₀ hf0]; exact Subalgebra.one_mem _⟩
  have hsmul : ∀ (C : Subalgebra k K) (p : ℕ), ∀ c ∈ C, ∀ a ∈ omB k K C p, c • a ∈ omB k K C p :=
    fun C p c hc a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K C p p).2.1 a ha).2.2.2 c hc
  constructor
  · intro hy
    have hQc : ∀ (p : ℕ) (c : K) (z : DR k K), c ∈ rB k K x I →
        (∃ N : ℕ, f ^ N • z ∈ omB k K (rB k K x {i}) p) → ∃ N : ℕ, f ^ N • (c • z) ∈ omB k K (rB k K x {i}) p := by
      rintro p c z hc ⟨N, hN⟩
      obtain ⟨M, hM⟩ := (hloc c).1 hc
      refine ⟨M + N, ?_⟩
      have e : f ^ (M + N) • (c • z) = (c * f ^ M) • (f ^ N • z) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      rw [e]
      exact hsmul _ p _ hM _ hN
    have hQmul : ∀ (p p' : ℕ) (a b : DR k K), (∃ N : ℕ, f ^ N • a ∈ omB k K (rB k K x {i}) p) →
        (∃ N : ℕ, f ^ N • b ∈ omB k K (rB k K x {i}) p') →
        ∃ N : ℕ, f ^ N • (a * b) ∈ omB k K (rB k K x {i}) (p + p') := by
      rintro p p' a b ⟨N, hN⟩ ⟨N', hN'⟩
      refine ⟨N + N', ?_⟩
      have e : f ^ (N + N') • (a * b) = (f ^ N • a) * (f ^ N' • b) := by
        rw [pow_add, mul_smul, smul_mul_assoc, mul_smul_comm]
      rw [e]
      exact (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) p p').1 _ hN _ hN'
    have hQ1 : ∀ v ∈ rB k K x I, ∃ N : ℕ, f ^ N • ι1 (D k K v) ∈ omB k K (rB k K x {i}) 1 := by
      intro v hv
      obtain ⟨M, hM⟩ := (hloc v).1 hv
      exact ⟨M + M, GlobalTheory.PD.OmLoc.pow_smul_d_mem _ hfB M hM⟩
    have hQm : ∀ (n : ℕ) (v : Fin n → K), (∀ j, v j ∈ rB k K x I) →
        ∃ N : ℕ, f ^ N • ExteriorAlgebra.ιMulti K n (fun j => D k K (v j)) ∈ omB k K (rB k K x {i}) n := by
      intro n
      induction n with
      | zero =>
        intro v _
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul, ExteriorAlgebra.ιMulti_zero_apply]
        exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) 0 0).2.2.2 1).2 ⟨1, Subalgebra.one_mem _, (map_one _).symm⟩
      | succ n ih =>
        intro v hv
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        have := hQmul 1 n _ _ (hQ1 (v 0) (hv 0)) (ih (fun j => v j.succ) fun j => hv j.succ)
        rw [Nat.add_comm 1 n] at this
        exact this
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hz
      exact hQc q b _ hb (hQm q v hv)
    | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
    | add a c _ _ ha hc =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hc
      refine ⟨N₁ + N₂, ?_⟩
      rw [smul_add]
      apply add_mem
      · rw [pow_add, mul_comm, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₁
      · rw [pow_add, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₂
    | smul r a _ ha =>
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, by rw [smul_comm]; exact Submodule.smul_mem _ r hN⟩
  · rintro ⟨N, hN⟩
    have := hsmul _ q (f⁻¹ ^ N) (pow_mem hfinv N) _
      ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) q q).2.2.1 _ hBB' hN)
    rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_smul] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
section
namespace GlobalTheory

universe u

theorem trdeg_quotient_eq_of_mem_minimalPrimes_span (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (k : Type u) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) {ϖ : R} (hϖ0 : ϖ ≠ 0)
    (hker : RingHom.ker (algebraMap R k) = Ideal.span {ϖ})
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [FaithfulSMul R A] {q : Ideal A}
    (hq : q ∈ (Ideal.span {algebraMap R A ϖ}).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower R k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg R A := by
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType R k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) R) →ₐ[R] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) R)) :
      Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap R k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap R k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hmem (r : (MvPolynomial (Fin s) R)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap R A ϖ ≠ 0 := by
    intro h
    exact hϖ0 ((FaithfulSMul.algebraMap_injective R A) (h.trans (map_zero _).symm))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin s) R) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) R) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) R) A :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin s) R) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) R) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) R) A q
      (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) ∈ q'.under (MvPolynomial (Fin s) R) :=
        h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap R k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) R) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) R) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k),
    trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin s) R) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]

theorem ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime (A : Type) [CommRing A]
    [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A)
    [q.IsPrime] (hq : q ∈ (Ideal.span {(l : A)}).minimalPrimes) (d : ℕ)
    (hd : Algebra.trdeg ℤ A = d) : ringKrullDim (A ⧸ q) = d := by
  have hk : Function.Surjective (algebraMap ℤ (ZMod l)) := ZMod.intCast_surjective
  have hker : RingHom.ker (algebraMap ℤ (ZMod l)) = Ideal.span {(l : ℤ)} := by
    rw [algebraMap_int_eq]; exact ZMod.ker_intCastRingHom l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [algebraMap_int_eq]; exact Int.cast_injective)
  have hq' : q ∈ (Ideal.span {algebraMap ℤ A (l : ℤ)}).minimalPrimes := by simpa using hq
  have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hle : RingHom.ker (algebraMap ℤ (ZMod l)) ≤ RingHom.ker (algebraMap ℤ (A ⧸ q)) := by
    rw [hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    simpa using hlq
  let := ((algebraMap ℤ (ZMod l)).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower ℤ (ZMod l) (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : Algebra.FiniteType (ZMod l) (A ⧸ q) := .of_restrictScalars_finiteType ℤ _ _
  refine ringKrullDim_eq_of_trdeg_eq (ZMod l) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes_span ℤ (ZMod l) hk hl0 hker hq', hd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit

set_option maxHeartbeats 1000000 in

theorem res_resGen_of_pow (q : ℕ) [NeZero q] {W V : Scheme.{0}} (k : W ⟶ V) (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : k.appTop.hom ξ.1 = k.appTop.hom ζ.1 ^ (a : ZMod q).val) :
    Sec.res k (resGen 1 ξ) = (a : ZMod q).val • resGen 1 (ζ.map k.appTop.hom) := by
  have e1 : Sec.res k (resGen 1 ξ) = resGen 1 (ξ.map k.appTop.hom) := by
    unfold resGen
    rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
  rw [e1]
  have e2 := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.2.1 W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a h
  simp only [zpow_one] at e2
  unfold resGen
  rw [e2]
  exact map_nsmul ((resι (ZMod q) (tw q 1)).hom.app (op W)).hom _ _

end GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit

set_option maxHeartbeats 1000000 in

theorem relation_kernel (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (hc : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  classical
  set d : unitsP.obj (op V) →₀ ULift.{1} (ZMod q) :=
    c.sum fun x r => Finsupp.single (unitsP.mk (tripP.get x).tgt) r - Finsupp.single (unitsP.mk (tripP.get x).src) r
    with hd_def
  have hd : (d.sum fun u r => r • freeGen (ZMod q) unitsP V u) = 0 := by
    rw [← Finsupp.linearCombination_apply, hd_def, map_finsuppSum, ← hc]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
  have hloc := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) unitsP V).2 d hd
  by_cases hc0 : c = 0
  · simp [hc0]
  obtain ⟨x₀, -⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hroots : ∀ x : ↥c.support, Loc V fun _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val :=
    fun x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (tripP.get x₀).root (tripP.get x.1).root
  have hall := loc_calculus.2.2.2.2.2.1 V (↥c.support) (fun x _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val) hroots
  have hboth := loc_calculus.2.2.1 V _ _ hloc hall
  apply sec_eq_zero_of_loc
  refine loc_calculus.2.1 V _ _ hboth ?_
  rintro W k ⟨hkd, hka⟩
  rw [res_sum]
  by_cases hW : IsEmpty W
  · exact sec_eq_zero_of_loc _ _ (loc_calculus.2.2.2.2.2.2 W _)
  rw [not_isEmpty_iff] at hW
  haveI : Nontrivial Γ(W, ⊤) := @Scheme.component_nontrivial W ⊤ ⟨⟨hW.some, trivial⟩⟩
  choose a ha using hka
  let a' : (tripP q).obj (op V) → ℕ := fun x =>
    if h : x ∈ c.support then ((a ⟨x, h⟩ : (ZMod q)ˣ) : ZMod q).val else 0
  have hax : ∀ x (hx : x ∈ c.support), a' x = ((a ⟨x, hx⟩ : (ZMod q)ˣ) : ZMod q).val := fun x hx => dif_pos hx
  have hsum : (c.sum fun x r => r • Sec.res k (resGen 1 (tripP.get x).root)) =
      (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) •
        resGen 1 ((tripP.get x₀).root.map k.appTop.hom) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [res_resGen_of_pow q k (tripP.get x₀).root _ (a ⟨x, hx⟩) (ha ⟨x, hx⟩), ← hax x hx, mul_smul,
      Nat.cast_smul_eq_nsmul]
  have halg := GlobalTheory.T.primitiveRoot_free_action_finsupp_sum q Γ(W, ⊤) ((tripP.get x₀).root.map k.appTop.hom) ((tripP q).obj (op V)) c.support
    (fun x => c x) a'
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).src)
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).tgt) ?_ ?_
  · rw [hsum]
    suffices h0 : (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) = 0 by rw [h0, zero_smul]
    apply ULift.ext
    rw [Finsupp.sum]
    refine Eq.trans ?_ halg
    induction c.support using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ULift.add_down, ih]; simp
  · intro x hx
    rw [hax x hx]
    change k.appTop.hom ((tripP.get x).tgt : Γ(V, ⊤)) =
      k.appTop.hom (tripP.get x₀).root.1 ^ _ * k.appTop.hom ((tripP.get x).src : Γ(V, ⊤))
    rw [(tripP.get x).tgt_eq, map_mul, ha ⟨x, hx⟩]
  · rw [hd_def, Finsupp.sum, Finsupp.mapDomain_finsetSum] at hkd
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, unitsP.map_mk] at hkd
    exact hkd

end GlobalTheory.EtC.KummerSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqSiegelParabolicOperatorEq
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_lintegral_sq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ _ hψ1 _ χ _ hres _ _ μ _ p hp φ
  obtain ⟨h1, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  obtain ⟨-, htop, -, -, -, -, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨-, -, -, hnorm, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have h1' := mul_eq_one_comm.mp h1
  let A : GL ν E := ⟨(mat c p).toBlocks₁₁, _, h1, h1'⟩
  have hA : ((A : GL ν E) : Matrix ν ν E) = (mat c p).toBlocks₁₁ := rfl
  set D : NNReal := distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) with hD
  have hD0 : D ≠ 0 := distribHaarChar_pos.ne'
  have hsc : ‖sc F χ (Fintype.card α) (mat c p).toBlocks₁₁.det‖ₑ ^ 2 = ((D ^ Fintype.card α : NNReal) : ENNReal) := by
    have := hnorm (Matrix.GeneralLinearGroup.det A)
    have hd : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = (mat c p).toBlocks₁₁.det := rfl
    rw [hd] at this
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.eq
    push_cast
    rw [this]
    rfl
  have hpt : ∀ x, ‖parFun c ψ χ Q (mat c p) φ x‖ₑ ^ 2 =
      ((D ^ Fintype.card α : NNReal) : ENNReal) * ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 := by
    intro x
    have hψe : ∀ t, ‖ψ t‖ₑ = 1 := fun t => by
      rw [enorm_eq_nnnorm]; simp [← NNReal.coe_eq_one, coe_nnnorm, hψ1 t]
    simp only [parFun, enorm_mul, hψe, one_mul, mul_pow, hsc, hA]
  haveI := htop
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * (A : Matrix ν ν E)
      invFun := fun x => x * ((A⁻¹ : GL ν E) : Matrix ν ν E)
      left_inv := fun x => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  have hmap : μ.map (e.toMeasurableEquiv) = ((D ^ Fintype.card α)⁻¹ : NNReal) • μ := by
    have := GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ 1 A
    have hf : (fun x : Matrix α ν E => ((1 : GL α E) : Matrix α α E) * x * (A : Matrix ν ν E)) = e.toMeasurableEquiv := by
      funext x; simp [e]
    rw [hf] at this
    rw [this, ← hD]
    simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hl := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) e.toMeasurableEquiv (μ := μ)
  have hl' : ∫⁻ x, ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(μ.map e.toMeasurableEquiv) := hl.symm
  rw [hl', hmap, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hD0), ENNReal.coe_one, one_mul]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.MayerVietorisEqv

theorem a4 : GlobalTheory.EtC.A4 := by
  intro R _ U V E U' V' E' f g f' g' p u v hu hv F hc hc' hU hV hW
  obtain ⟨d, hex, hnat⟩ := GlobalTheory.T.exists_mayerVietoris_connecting_exact R F
  have hwf : pullback.map f g f' g' u v p hu hv ≫ pullback.fst f' g' = pullback.fst f g ≫ u := pullback.lift_fst _ _ _
  have hwg : pullback.map f g f' g' u v p hu hv ≫ pullback.snd f' g' = pullback.snd f g ≫ v := pullback.lift_snd _ _ _
  have cf : ∀ n x, pull R f F n (pull R p F n x) = pull R u F n (pull R f' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hu]
  have cg : ∀ n x, pull R g F n (pull R p F n x) = pull R v F n (pull R g' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hv]
  have cfst : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.fst f' g') F n x) =
      pull R (pullback.fst f g) F n (pull R u F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwf]
  have csnd : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.snd f' g') F n x) =
      pull R (pullback.snd f g) F n (pull R v F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwg]
  have hcond : ∀ n x, pull R (pullback.fst f g) F n (pull R f F n x) =
      pull R (pullback.snd f g) F n (pull R g F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, pullback.condition]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : pull R f' F (m + 1) y = 0 := by
      apply (hU (m + 1)).1
      rw [← cf, hy, map_zero, map_zero]
    have h2 : pull R g' F (m + 1) y = 0 := by
      apply (hV (m + 1)).1
      rw [← cg, hy, map_zero, map_zero]
    obtain ⟨c, rfl⟩ := ((hex f' g' hc' m).2.2 y).1 ⟨h1, h2⟩
    have hd : d f g hc m (pull R (pullback.map f g f' g' u v p hu hv) F m c) = 0 := by
      rw [← hnat f g f' g' p u v hu hv hc hc' m c]; exact hy
    obtain ⟨a, b, hab⟩ := ((hex f g hc m).2.1 _).1 hd
    obtain ⟨a', rfl⟩ := (hU m).2 a
    obtain ⟨b', rfl⟩ := (hV m).2 b
    have hc1 : c = pull R (pullback.fst f' g') F m a' - pull R (pullback.snd f' g') F m b' := by
      apply (hW m).1
      rw [hab, map_sub, cfst, csnd]
    exact ((hex f' g' hc' m).2.1 c).2 ⟨a', b', hc1⟩
  · intro z
    obtain ⟨a', ha'⟩ := (hU (m + 1)).2 (pull R f F (m + 1) z)
    obtain ⟨b', hb'⟩ := (hV (m + 1)).2 (pull R g F (m + 1) z)
    have hab : pull R (pullback.fst f' g') F (m + 1) a' = pull R (pullback.snd f' g') F (m + 1) b' := by
      apply (hW (m + 1)).1
      rw [cfst, csnd, ha', hb', hcond]
    obtain ⟨y, hy1, hy2⟩ := ((hex f' g' hc' (m + 1)).1 a' b').1 hab
    have k1 : pull R f F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cf, hy1, ha', sub_self]
    have k2 : pull R g F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cg, hy2, hb', sub_self]
    obtain ⟨c, hc0⟩ := ((hex f g hc m).2.2 _).1 ⟨k1, k2⟩
    obtain ⟨c', rfl⟩ := (hW m).2 c
    refine ⟨y + d f' g' hc' m c', ?_⟩
    rw [map_add, hnat f g f' g' p u v hu hv hc hc' m c', hc0]
    abel

end GlobalTheory.MayerVietorisEqv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalSectionsLinearExtension
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_sections_linear_extension : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), Injective G → ∀ {A B : Shv R} (f : A ⟶ B), Mono f → ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V), (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V), Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) → ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) → Sec B V →ₗ[ULift.{1} R] Sec G V, (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : Sec B V), Sec.res w (χ V x b) = χ W (P.map w.op x) (Sec.res w b)) ∧ ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : Sec A V), χ V x (Sec.map f a) = ψ V x a := by
  first | (exact @GlobalTheory.natFam_extend_of_injective) | (exact GlobalTheory.natFam_extend_of_injective) | (intros; apply GlobalTheory.natFam_extend_of_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapSurjectiveFiniteField
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_surjective_finite_field : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F', (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s δ = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (exact GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (intros; apply GlobalTheory.Shin.NormSurj.nrm_surj_adjoin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R']), (∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) → ω = 0 := by
  first | exact @GlobalTheory.CechDR.form_eq_zero_of_pair | exact GlobalTheory.CechDR.form_eq_zero_of_pair | (intros; apply GlobalTheory.CechDR.form_eq_zero_of_pair <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitFiniteSubextensionSpecArrowCone
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem isLimit_leftFunc_arrCone (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (hc : IsColimit (ringCocone K Ω)) :
    Nonempty (IsLimit (Arrow.leftFunc.mapCone (arrCone K Ω))) :=
  ⟨isLimitOfPreserves (Scheme.Spec ⋙ yoneda) hc.op⟩

end GlobalTheory.SepCech
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecSingle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem isLimit_cone_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B)
      (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    exact t.condition 0
  · intro t i
    rw [WidePullbackCone.mk_π]
    exact (Category.comp_id (t.π 0)).trans (congrArg t.π (Fin.fin_one_eq_zero i).symm)
  · intro t m _ hπ
    have := hπ 0
    rw [WidePullbackCone.mk_π] at this
    exact (Category.comp_id m).symm.trans this

end GlobalTheory.CechOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquare
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section
namespace GlobalTheory.CechOne

theorem isLimit_widePullback_tensor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B B)
  have e0 : y1 A B 0 = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := rfl
  have e1 : y1 A B 1 = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) := rfl
  refine ⟨WidePullbackCone.IsLimit.mk _ (fun t => H.lift (t.π 0) (t.π 1) ?_) ?_ ?_ ?_⟩
  · exact (t.condition 0).trans (t.condition 1).symm
  · intro t
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = _
    rw [← hy1 A B 0, ← Category.assoc, e0, H.lift_fst]
    exact t.condition 0
  · intro t i
    fin_cases i
    · exact H.lift_fst _ _ _
    · exact H.lift_snd _ _ _
  · intro t m _ hm
    apply H.hom_ext
    · rw [H.lift_fst, ← hm 0]; rfl
    · rw [H.lift_snd, ← hm 1]; rfl

end GlobalTheory.CechOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprodStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  first | (exact @GlobalTheory.EtC.flatS_biprod) | (exact GlobalTheory.EtC.flatS_biprod) | (intros; apply GlobalTheory.EtC.flatS_biprod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  first | exact @GlobalTheory.EtC.flatS_iso_and_zero | exact GlobalTheory.EtC.flatS_iso_and_zero | (intros; apply GlobalTheory.EtC.flatS_iso_and_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZeroStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRat_of_hankel_eventually_eq_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ), (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  first | exact @GlobalTheory.Nef.isRat_of_hankel_eventually_zero | exact GlobalTheory.Nef.isRat_of_hankel_eventually_zero | (intros; apply GlobalTheory.Nef.isRat_of_hankel_eventually_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRootsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  first | (exact @GlobalTheory.EtC.isField_aic_sh) | (exact GlobalTheory.EtC.isField_aic_sh) | (intros; apply GlobalTheory.EtC.isField_aic_sh  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorOfCompatIsIsoTargetStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTensor_of_compat_isIso_target : ∀ (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K') (u : K ⟶ K'), IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  first | (exact @GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (exact GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (intros; apply GlobalTheory.EtC.Pair.isTensor_of_compat_isIso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisQuotientIntegralClosure
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open Polynomial in

theorem isTranscendenceBasis_quotient_integralClosure
    (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
    [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K)
    (hB : B = (integralClosure A K).restrictScalars k) (Q : Ideal B) (hQ : Q.IsPrime) (t : A)
    (htQ : ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a))
    (m : ℕ) (y : Fin m → A)
    (hy : IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)))
    (y' : Fin m → B) (hy' : ∀ j, (y' j : K) = algebraMap F K (y j)) :
    IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y' j)) := by
  haveI := hQ
  have hBK : ∀ x : K, x ∈ B ↔ IsIntegral A x := by
    intro x; rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := fun a =>
    (hBK _).2 (isIntegral_algebraMap (R := A) (A := K) (x := a))
  let ι : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  have hι : ∀ a : A, ((ι a : B) : K) = algebraMap F K (a : F) := fun a => rfl
  let g : A →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp ι
  have hg : ∀ a : A, g a = 0 ↔ a ∈ Ideal.span {t} := by
    intro a
    rw [Ideal.mem_span_singleton, ← htQ a (ι a) (hι a)]
    exact Ideal.Quotient.eq_zero_iff_mem
  let f : A ⧸ Ideal.span {t} →+* B ⧸ Q :=
    Ideal.Quotient.lift (Ideal.span {t}) g (fun a ha => (hg a).2 ha)
  have hf : ∀ a : A, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk Q (ι a) := fun a => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hg a).1 hx)
  letI : Algebra (A ⧸ Ideal.span {t}) (B ⧸ Q) := f.toAlgebra
  haveI : IsScalarTower k (A ⧸ Ideal.span {t}) (B ⧸ Q) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change Ideal.Quotient.mk Q (algebraMap k B c) = f (Ideal.Quotient.mk _ (algebraMap k A c))
    rw [hf]
    congr 1
    apply Subtype.ext
    rw [hι]
    change algebraMap k K c = algebraMap F K (algebraMap k F c)
    exact IsScalarTower.algebraMap_apply k F K c
  haveI : FaithfulSMul (A ⧸ Ideal.span {t}) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : NoZeroDivisors (A ⧸ Ideal.span {t}) :=
    hinj.noZeroDivisors f (map_zero f) (map_mul f)
  haveI : Nontrivial (A ⧸ Ideal.span {t}) := f.domain_nontrivial
  haveI : Algebra.IsIntegral (A ⧸ Ideal.span {t}) (B ⧸ Q) := by
    constructor
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hpm, hp⟩ := (hBK _).1 b.2
    refine ⟨p.map (Ideal.Quotient.mk _), hpm.map _, ?_⟩
    have h0 : p.eval₂ ι b = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ p ι B.val.toRingHom b
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_val] at this
      rw [this]
      exact hp
    rw [RingHom.algebraMap_toAlgebra, Polynomial.eval₂_map]
    have hfg : f.comp (Ideal.Quotient.mk (Ideal.span {t})) = (Ideal.Quotient.mk Q).comp ι :=
      RingHom.ext fun a => hf a
    rw [hfg, ← Polynomial.hom_eval₂, h0, map_zero]
  have key := hy.algebraMap_comp (A := B ⧸ Q)
  convert key using 1
  funext j
  simp only [Function.comp_apply, RingHom.algebraMap_toAlgebra, hf]
  congr 1
  exact Subtype.ext ((hy' j).trans (hι (y j)).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroTensorOfDegreeZeroComplexes
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TensZero

variable {R : Type} [CommRing R]

theorem sec_eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h : 𝟙 F = 0 := hF.eq_of_src _ _
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  have h1 : Sec.map (𝟙 F) a = a := rfl
  have h2 : Sec.map (0 : F ⟶ F) a = 0 := by
    simp only [Sec.map]
    rfl
  rw [h1, h2] at this
  exact this

theorem isZero_of_sec {F : Shv R} (h : ∀ (U : Scheme.{0}) (a : Sec F U), a = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine ((GlobalTheory.EtC.mono_epi_sections R (𝟙 F)).2.2.2 0 fun U a => ?_)
  rw [h U a]
  simp

theorem tens_eq_zero {I J : Cx R} (hI : ∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) (hJ : ∀ t : ℤ, t ≠ 0 → IsZero (J.X t))
    (U : Scheme.{0}) (w : ℤ) (hw : w ≠ 0) (x : Tens I J U w) : x = 0 := by
  refine DFinsupp.ext fun p => ?_
  show x p = 0
  have hp := p.2
  by_cases h1 : p.1.1 = 0
  · have h2 : p.1.2 ≠ 0 := by omega
    induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hJ _ h2) b, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hI _ h1) a, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]

end GlobalTheory.EtC.TensZero

open GlobalTheory.EtC.TensZero in
theorem GlobalTheory.EtC.isZero_tensor_of_deg_zero : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  intro R _ I J K τ hτ hI hJ w hw
  refine isZero_of_sec fun U y => ?_
  refine (GlobalTheory.EtC.sec_ext_glue R (K.X w) U).1 y 0 ?_
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [tens_eq_zero hI hJ V w hw x, map_zero] at hx
  rw [← hx]
  exact (map_zero _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem dDR_ιMulti_D (q : ℕ) (v : Fin q → K) :
    dDR k K (ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (DR k K)), dDR_algebraMap,
      Derivation.map_one_eq_zero, map_zero]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, dDR_mul]
    have ht : Matrix.vecTail (fun j => D k K (v j)) = fun j => D k K (v j.succ) := rfl
    rw [ht, ih (fun j => v j.succ), mul_zero, zero_add,
      show dDR k K (ExteriorAlgebra.ι K (D k K (v 0))) = 0 from dDR_D (v 0), zero_mul]

variable {k K}

theorem mem_deg_of_mem_omB (B : Subalgebra k K) (q : ℕ) (a : DR k K) (ha : a ∈ omB k K B q) :
    a ∈ ⋀[K]^q Ω[K⁄k] := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, v, -, rfl⟩ := hx
    exact Submodule.smul_mem _ c (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_of_tower_mem _ r hx

theorem mul_mem_omB (B : Subalgebra k K) (p q : ℕ) (a : DR k K) (ha : a ∈ omB k K B p)
    (b : DR k K) (hb : b ∈ omB k K B q) : a * b ∈ omB k K B (p + q) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hx
      obtain ⟨c', hc', w, hw, rfl⟩ := hy
      have happ : Fin.append (fun j => D k K (v j)) (fun j => D k K (w j)) =
          fun j => D k K (Fin.append v w j) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      refine Submodule.subset_span ⟨c * c', B.mul_mem hc hc', Fin.append v w, fun j => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · rw [Fin.append_left]; exact hv i
        · rw [Fin.append_right]; exact hw i
      · rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti, happ]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem dDR_mem_omB (B : Subalgebra k K) (p : ℕ) (a : DR k K) (ha : a ∈ omB k K B p) :
    dDR k K a ∈ omB k K B (p + 1) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [dDR_smul, dDR_ιMulti_D, smul_zero, add_zero]
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.cons c v, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]; exact hc
      · rw [Fin.cons_succ]; exact hv i
    · rw [one_smul, ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Matrix.vecTail, Function.comp_def, Fin.cons_succ, Fin.cons_zero]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem smul_mem_omB (B : Subalgebra k K) (p : ℕ) (c : K) (hc : c ∈ B) (a : DR k K)
    (ha : a ∈ omB k K B p) : c • a ∈ omB k K B p := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm c r x]; exact Submodule.smul_mem _ r hx

theorem omB_mono (B B' : Subalgebra k K) (h : B ≤ B') (p : ℕ) : omB k K B p ≤ omB k K B' p := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

theorem mem_omB_zero (B : Subalgebra k K) (y : DR k K) :
    y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, -, rfl⟩ := hx
      exact ⟨b, hb, by rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩
    | zero => exact ⟨0, B.zero_mem, (map_zero _).symm⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hz
      exact ⟨c + c', B.add_mem hc hc', (map_add _ _ _).symm⟩
    | smul r x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨r • c, B.smul_mem hc r, by simp only [Algebra.algebraMap_eq_smul_one, smul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.subset_span ⟨c, hc, Fin.elim0, fun j => j.elim0, by
      rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩

theorem omB_alg : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ),
    (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧
    (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧
      a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧
    (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧
    ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  intro k K _ _ _ B p q
  refine ⟨fun a ha b hb => mul_mem_omB B p q a ha b hb, fun a ha => ?_,
    fun B' h => omB_mono B B' h p, mem_omB_zero B⟩
  have hdeg := mem_deg_of_mem_omB B p a ha
  refine ⟨dDR_mem_omB B p a ha, ?_, hdeg, fun c hc => smul_mem_omB B p c hc a ha⟩
  change sgn a = _
  rw [sgn_of_mem hdeg, Algebra.smul_def, map_pow, map_neg, map_one]

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraComapSpanEqTop
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.KSpan

theorem alt_mem_of_span {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {n : ℕ} (f : M [⋀^Fin n]→ₗ[K] N) (s : Set M) (hs : Submodule.span K s = ⊤) (T : Submodule K N)
    (hT : ∀ v : Fin n → M, (∀ i, v i ∈ s) → f v ∈ T) (v : Fin n → M) : f v ∈ T := by
  have key : ∀ j : ℕ, ∀ v : Fin n → M, (∀ i : Fin n, j ≤ i.val → v i ∈ s) → f v ∈ T := by
    intro j
    induction j with
    | zero => intro v hv; exact hT v fun i => hv i (Nat.zero_le _)
    | succ j ih =>
      intro v hv
      by_cases hj : j < n
      · have hmem : v ⟨j, hj⟩ ∈ Submodule.span K s := hs ▸ Submodule.mem_top
        have hall : ∀ x ∈ Submodule.span K s, f (Function.update v ⟨j, hj⟩ x) ∈ T := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            apply ih
            intro i hi
            by_cases h : i = ⟨j, hj⟩
            · rw [h, Function.update_self]; exact hx
            · rw [Function.update_of_ne h]
              apply hv
              have : i.val ≠ j := fun h' => h (Fin.ext h')
              omega
          | zero => rw [AlternatingMap.map_update_zero]; exact T.zero_mem
          | add a b _ _ ha hb => rw [AlternatingMap.map_update_add]; exact T.add_mem ha hb
          | smul r a _ ha => rw [AlternatingMap.map_update_smul]; exact T.smul_mem r ha
        simpa using hall _ hmem
      · exact ih v fun i hi => hv i (by have := i.isLt; omega)
  exact key n v fun i hi => absurd i.isLt (by omega)

end GlobalTheory.PD.KSpan

namespace GlobalTheory.PD

open KSpan in

theorem omB_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  intro k K _ _ _ B _ p W _ _ _ _ e he hr
  have hD : Submodule.span K (D k K '' (B : Set K)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation k K, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨b1, b2, hb2, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    have h2 : algebraMap B K b2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb2
    set q := algebraMap B K b1 / algebraMap B K b2 with hqdef
    have e1 : algebraMap B K b1 = q * algebraMap B K b2 := by rw [hqdef, div_mul_cancel₀ _ h2]
    have hq : D k K q = (algebraMap B K b2)⁻¹ • (D k K (algebraMap B K b1) - q • D k K (algebraMap B K b2)) := by
      rw [e1, Derivation.leibniz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have m1 : D k K (algebraMap B K b1) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b1 : K), b1.2, rfl⟩
    have m2 : D k K (algebraMap B K b2) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b2 : K), b2.2, rfl⟩
    rw [SetLike.mem_coe, hq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
  have hS : (omB k K B p : Set (DR k K)) ⊆ ⋀[K]^p Ω[K⁄k] := by
    intro y hy
    change y ∈ Submodule.span k _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, -, v, -, rfl⟩ := hy
      exact Submodule.smul_mem _ b (ExteriorAlgebra.ιMulti_range K p ⟨_, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [← algebraMap_smul K r a]; exact Submodule.smul_mem _ _ ha
  have hP : ⋀[K]^p Ω[K⁄k] ≤ Submodule.span K (omB k K B p : Set (DR k K)) := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine alt_mem_of_span (ExteriorAlgebra.ιMulti K p) _ hD _ ?_ v
    intro v hv
    choose b hb hbv using hv
    apply Submodule.subset_span
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, b, hb, ?_⟩
    rw [one_smul]
    simp only [hbv]
  have hSC : (omB k K B p : Set (DR k K)) ⊆ e '' ((omB k K B p).comap (e.restrictScalars k) : Set W) := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ LinearMap.range e := hr ▸ hS hy
    exact ⟨w, hy, rfl⟩
  rw [eq_top_iff, ← Submodule.map_le_map_iff_of_injective he, ← LinearMap.range_eq_map, hr, Submodule.map_span]
  exact hP.trans (Submodule.span_mono hSC)

end GlobalTheory.PD
end
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Formalism.LocalRingCardinality.DataParams₂
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixDegreeLeTwoMulOfUpperTriangular
section
set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem GlobalTheory.Nef.deg_le_two_mul_of_triangular : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ 2 * b := by
  intro k F _ _ _ _ _ hFF g hg htri b hb
  by_cases hne : IsEmpty (Place k F)
  · have h0 : deg g = 0 := by simp [deg, finsum_of_isEmpty]
    have hres : IsRes (k := k) (F := F) (E := F) id := fun p x => by simp
    have hw : (![1, 0] : Fin 2 → F) ≠ 0 := by intro h; simpa using congrFun h 0
    have h1 := hb F id hres ![1, 0] hw
    have hl : degLine (pullAd id g) (![1, 0] : Fin 2 → F) = 0 := by simp [degLine, finsum_of_isEmpty]
    rw [hl] at h1
    simp at h1
    rw [h0]; push_cast; linarith
  rw [not_isEmpty_iff] at hne
  obtain ⟨v₀⟩ := hne
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_section_of_large_adelic_degree k F hFF
  obtain ⟨π, hπ0, hπ⟩ := (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v₀).2.2.2.2.2.1
  have key : ∀ m : ℕ, ((m * (m + 1) / 2 : ℕ) : ℝ) * (deg g : ℝ) ≤ (m + 1) * (m * b + 1 + γ) := by
    intro m
    set N : ℕ := m * (m + 1) / 2 with hN
    set S : Place k F → Matrix (Fin (m + 1)) (Fin (m + 1)) F := fun v => symMat m (g v) with hS
    obtain ⟨hSadm, hSdeg⟩ := GlobalTheory.Nef.admissible_degree_symmetricPowerFamily k F m g hg htri
    rw [← hN] at hSdeg
    set D : ℤ := (N : ℤ) * deg g - (m + 1) * γ - 1 with hD
    set e : ℤ := D / (m + 1) with he
    have hm0 : (0 : ℤ) < m + 1 := by positivity
    have hdiv := Int.mul_ediv_add_emod D (m + 1)
    have hmod0 := Int.emod_nonneg D hm0.ne'
    have hmod1 := Int.emod_lt_of_pos D hm0
    rw [← he] at hdiv
    obtain ⟨hTadm, hTdeg⟩ := GlobalTheory.Nef.admissible_degree_twistFamilyAtPlaceByScalar k F (m + 1) S hSadm v₀ π hπ0 hπ e
    have hdegT : ((m + 1 : ℕ) : ℤ) * γ < deg (twistAt v₀ (π ^ (-e)) S) := by
      have hc1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hTdeg, hSdeg, hc1]; linarith
    obtain ⟨p, hp0, hpint⟩ := hγ (m + 1) _ hTadm hdegT
    have hep : e ≤ degLine S p := GlobalTheory.T.lineDegree_ge_of_twisted_section k F hFF (m + 1) S hSadm v₀ π hπ0 hπ e p hp0 hpint
    obtain ⟨E, _, _, _, c, s, t, hc, hst, hid⟩ := GlobalTheory.T.exists_binary_form_eq_mul_prod_linear F m p hp0
    letI : Algebra k E := ((algebraMap F E).comp (algebraMap k F)).toAlgebra
    haveI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).1
    have hEFF : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hFF).2 E
    have pS := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hFF ρ hρ (m + 1) S hSadm
    have pg := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hFF ρ hρ 2 g hg
    have hpull : pullAd ρ S = fun P => symMat m (pullAd ρ g P) := by
      funext P; simp only [pullAd, hS, symMat_map]
    have htriE : ∀ P, pullAd ρ g P 1 0 = 0 := by intro P; simp [pullAd, htri]
    set q : Fin (m + 1) → E := fun i => algebraMap F E (p i) with hq
    have hpt : ∀ P, ordVec P ((symMat m (pullAd ρ g P)).mulVec q) =
        ord P c + ∑ j, ordVec P ((pullAd ρ g P).mulVec ![s j, t j]) := fun P =>
      GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder k E P m _ (htriE P) (pg.1.1 P) q c s t hc hst (by
        have h3 := hid E[X] (C ((pullAd ρ g P) 0 0)) (C ((pullAd ρ g P) 0 1) + C ((pullAd ρ g P) 1 1) * X)
        rw [Polynomial.algebraMap_eq] at h3
        exact h3)
    have h6 := GlobalTheory.T.lineDegree_eq_sum_of_scalar_split k E hEFF m (m + 1) (pullAd ρ g) pg.1 (fun P => symMat m (pullAd ρ g P)) q c
      (fun j => ![s j, t j]) hc hst hpt
    have h2 := pS.2.2.1 p hp0
    rw [hpull] at h2
    have hbound : ∀ j, (degLine (pullAd ρ g) ![s j, t j] : ℝ) ≤ b * Module.finrank F E :=
      fun j => hb E ρ hρ _ (hst j)
    have hsum : ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) ≤ m * (b * Module.finrank F E) := by
      push_cast
      calc (∑ j : Fin m, (degLine (pullAd ρ g) ![s j, t j] : ℝ)) ≤ ∑ _j : Fin m, b * Module.finrank F E :=
            Finset.sum_le_sum fun j _ => hbound j
        _ = m * (b * Module.finrank F E) := by simp
    have hfr : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
    have h7 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ m * (b * Module.finrank F E) := by
      have h8 : (Module.finrank F E : ℤ) * degLine S p = ∑ j, degLine (pullAd ρ g) ![s j, t j] := by
        rw [← h6, ← h2]
      have h8' : (Module.finrank F E : ℝ) * (degLine S p : ℝ) = ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) := by
        exact_mod_cast h8
      have h9 : (e : ℝ) ≤ (degLine S p : ℝ) := by exact_mod_cast hep
      have h10 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (degLine S p : ℝ) :=
        mul_le_mul_of_nonneg_left h9 hfr.le
      linarith
    have hemb : (e : ℝ) ≤ m * b := by
      have : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (m * b) := by linarith
      exact le_of_mul_le_mul_left this hfr
    have hint : (N : ℤ) * deg g ≤ (m + 1) * (e + 1 + γ) := by linarith
    have hreal : ((N : ℤ) : ℝ) * (deg g : ℝ) ≤ ((m : ℝ) + 1) * ((e : ℝ) + 1 + γ) := by exact_mod_cast hint
    push_cast at hreal
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hpos : (0 : ℝ) < (deg g : ℝ) - 2 * b := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (1 + γ) / ((deg g : ℝ) - 2 * b))
  have hk := key m
  have hN : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m + 1) / 2 := by
    have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
    rw [Nat.cast_div h2 (by norm_num)]; push_cast; ring
  rw [hN] at hk
  rw [div_lt_iff₀ hpos] at hm
  have hm' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : (m : ℝ) * (deg g : ℝ) ≤ 2 * (m * b + 1 + γ) := by
    have h3 : ((m : ℝ) + 1) * ((m : ℝ) * (deg g : ℝ)) ≤ ((m : ℝ) + 1) * (2 * (m * b + 1 + γ)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hm'
  nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPrimitiveVectorCompactRescale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.GeomZero

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero ((F.obj.map g.op).hom)

theorem q_dvd_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q * k : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [this]
  exact zero_smul _ t

theorem eq_zero_of_geom : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ)
    (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  intro q _ R _ _ j a ha
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q j)
  obtain ⟨s, rfl⟩ := (e (Spec (CommRingCat.of R))).surjective a
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      Sec.res φ s = 0 := by
    intro K _ _ φ
    have h := ha K (Spec.preimage φ).hom
    have hφ : Spec.map (CommRingCat.ofHom (Spec.preimage φ).hom) = φ := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [spMap, hφ, he] at h
    exact (map_eq_zero_iff _ (e _).injective).1 h
  have hs : s = 0 := by
    refine (sec_ext_glue (ZMod q) (tw q j) (Spec (CommRingCat.of R))).1 s 0 ?_
    refine (loc_iff_etale_affine_points (Spec (CommRingCat.of R)) (fun _ g => Sec.res g s = Sec.res g 0)
      (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
    intro x
    have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of R)) (k : W ⟶ V),
        (Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) →
        (Sec.res (k ≫ g) s = 0 ∨ ∃ (ζ : Prim q Γ(W, ⊤)) (c : ℕ), Sec.res (k ≫ g) s = c • twGen j ζ) := by
      rintro V W g k (h | ⟨ζ, c, h⟩)
      · left; rw [res_comp, h, res_zero]
      · right; exact ⟨ζ.map k.appTop.hom, c, by rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1]⟩
    obtain ⟨V, g, hV, hg, hx, hP⟩ := (loc_iff_etale_affine_points (Spec (CommRingCat.of R))
      (fun V g => Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) stab).1
      ((GlobalTheory.T.tateTwist_sections_locally_generated q j).1 _ s) x
    refine ⟨V, g, hV, hg, hx, ?_⟩
    show Sec.res g s = Sec.res g 0
    rw [res_zero]
    rcases hP with h | ⟨ζ, c, h⟩
    · exact h
    · obtain ⟨v, -⟩ := hx
      let ψ : Spec (CommRingCat.of (AlgebraicClosure (V.residueField v))) ⟶ V :=
        Spec.map (CommRingCat.ofHom (algebraMap (V.residueField v) (AlgebraicClosure (V.residueField v)))) ≫
          V.fromSpecResidueField v
      have h0 := hgeo (AlgebraicClosure (V.residueField v)) (ψ ≫ g)
      rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1] at h0
      haveI : Nonempty (Spec (CommRingCat.of (AlgebraicClosure (V.residueField v)))) := inferInstance
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.1 _ _ _ h0
      rw [h]
      exact q_dvd_nsmul _ k
  rw [hs, map_zero]

end GlobalTheory.EtC.GeomZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
section
open IsLocalRing

namespace GlobalTheory.EtaleHensel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem algHom_eq_of_residue_eq [Algebra.Etale R A] [IsLocalRing B] {φ₁ φ₂ : A →ₐ[R] B}
    (h : ∀ a, residue B (φ₁ a) = residue B (φ₂ a)) : φ₁ = φ₂ := by

  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let ψ : TensorProduct R A A →ₐ[R] B := Algebra.TensorProduct.productMap φ₁ φ₂
  let ρ : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hρ : ∀ b, ρ b = residue B b := fun _ => rfl
  have key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]
  have hres : residue B (ψ t) = 1 := by
    have := congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key
    simpa only [AlgHom.comp_apply, ht1, map_one, hρ] using this
  have hu : IsUnit (ψ t) := by
    by_contra hn
    have h0 : residue B (ψ t) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)
    exact one_ne_zero (hres.symm.trans h0)
  ext a
  have hz := congrArg ψ (ht a)
  simp only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, one_mul, mul_one] at hz
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

theorem bijective_residue_comp : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B],
    Function.Bijective
      (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  intro R A B _ _ _ _ _ _ _
  refine ⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩
  · exact DFunLike.congr_fun he a
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B)
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective
      (fun b => (residue_eq_zero_iff b).symm) φ
    exact ⟨ψ, hψ⟩

end GlobalTheory.EtaleHensel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_cech_conerve_quasiIso : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  intro R _ T _ _ Ψ hΨ U V g hg
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.cechConerve_map_eq_cechNerve_of_preservesWidePushouts T Ψ hΨ U V g
  have h2 := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R _ _ (Ψ.map g).unop hg
  let h : ((Arrow.mk (Ψ.map g).unop).cechNerve : Spc) ⟶ disc.obj (Ψ.obj U).unop :=
    (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
  have key : lev Ψ (coAug g) = e ≫ h := hc.symm
  have h2' : QuasiIso ((chains R).map h) := h2
  rw [key, Functor.map_comp]
  haveI : IsIso ((chains R).map e) := inferInstance
  exact quasiIso_comp _ _
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisible
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 →
    ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  obtain ⟨d, hd⟩ := GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed k B q (Ne.isUnit hq) (ClassGroup.equivPic B c)
  refine ⟨(ClassGroup.equivPic B).symm d, ?_⟩
  apply (ClassGroup.equivPic B).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hd]

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassMeanLogNormDiscChowlaSelberg
section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

namespace GlobalTheory.ClassMeanDisc

theorem classMean_log_norm_disc : ∀ (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → discr K = -(D.host.d : ℤ) → 4 < D.host.d → ∀ (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair), (∀ c, ClassGroup.mk K (rep c) = c) → (∀ c, IsLatOf φK (rep c : FractionalIdeal (𝓞 K)⁰ K) (L c)) → (∑ c, Real.log (nrm (rep c : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (L c)‖)) / (classNumber K : ℝ) = 12 * Real.log (2 * Real.pi) - 6 * Real.log D.host.d + 6 * Real.eulerMascheroniConstant - 6 * Formalism.BasicNotions.dlogL D 1 := by
  intro D K _ _ φK h2 hD hd rep L hrep hL
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd3 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hχ : IsKroneckerChar (Formalism.BasicNotions.chiK D) := isKroneckerChar_quadraticChar hd3
  have key := chowla_selberg_discriminant h2 hD hd hχ φK hrep hL
  have hre := congrArg Complex.re key
  simp only [Complex.ofReal_re, Complex.sub_re] at hre
  unfold Formalism.BasicNotions.dlogL nrm latDisc
  rw [hre]
  simp [Complex.mul_re]

end GlobalTheory.ClassMeanDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpanStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K, ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | exact GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | (intros; apply GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIff
section
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.ComplStd

theorem mem_omA_iff {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}
    (hx : ∀ i, x i ≠ 0) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (f : F) :
    f ∈ omA k x I ↔ (∏ j, x i / x j) * f ∈ rA k x I := by
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]
  refine ⟨fun h => h i hi, fun h i' _ => ?_⟩
  have hg : x i' / x i ∈ rA k x I := Algebra.subset_adjoin ⟨i, hi, i', rfl⟩
  have e : (∏ j, x i' / x j) = (x i' / x i) ^ (d + 1) * ∏ j, x i / x j := by
    rw [show (x i' / x i) ^ (d + 1) = ∏ _j : Fin (d + 1), x i' / x i by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (div_mul_div_cancel₀ (hx i)).symm
  rw [e, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hg _) h

theorem trace_algebraMap_mul {F K : Type} [Field F] [Field K] [Algebra F K] (c : F) (w : K) :
    Algebra.trace F K (algebraMap F K c * w) = c * Algebra.trace F K w := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem single (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (τ : DR k K →ₗ[K] K) (hτ : IsTop k K x τ) (i : Fin (d + 1)) (z : K) :
    (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔ ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
  haveI := hc.fin
  have hx := hc.pd.ne
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd i
  set u : Fin d → F := fun j => x (i.succAbove j) / x i with hu_def
  have hu : AlgebraicIndependent k u := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : MvPolynomial.aeval u = (rA k x {i}).val.comp e.toAlgHom :=
      MvPolynomial.algHom_ext fun j => by simp [he, u]
    rw [this]
    exact Subtype.val_injective.comp e.injective
  have hA : rA k x {i} = Algebra.adjoin k (Set.range u) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro y ⟨i', hi', j, rfl⟩
      rw [Finset.mem_singleton] at hi'
      subst hi'
      by_cases hj : j = i'
      · subst hj; rw [div_self (hx _)]; exact one_mem _
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact Algebra.subset_adjoin ⟨j', rfl⟩
    · apply Algebra.adjoin_le
      rintro y ⟨j, rfl⟩
      exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, _, rfl⟩
  haveI : IsFractionRing (rA k x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {i} (Finset.singleton_nonempty _)).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_sign_iMulti_D_chart_change k F K d x hc i
  set P : F := ∏ j, x i / x j with hP
  set C : F := ∏ j, x j / x i with hC
  have hPC : algebraMap F K P * algebraMap F K C = 1 := by
    rw [← map_mul, hP, hC, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one fun j _ => by rw [div_mul_div_cancel₀ (hx j), div_self (hx i)], map_one]
  have hPne : algebraMap F K P ≠ 0 := left_ne_zero_of_mul_eq_one hPC
  let τ' : DR k K →ₗ[K] K := (((ε : ℤ) : K) * algebraMap F K P) • τ
  have hτ' : τ' (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 := by
    simp only [u]
    rw [hε]
    rw [LinearMap.smul_apply, Units.smul_def, map_zsmul, map_smul, hτ.1]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    have hε2 : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    linear_combination (algebraMap F K P * algebraMap F K C) * hε2 + hPC
  have key := GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover k F K d u hu (rA k x {i}) hA (rB k K x {i}) rfl (hc.smooth i) τ' hτ'
    (algebraMap F K P * z)
  have lhs : (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔
      ∀ b : rB k K x {i}, Algebra.trace F K (algebraMap F K P * z * b) ∈ rA k x {i} := by
    simp only [Subtype.forall, mem_omA_iff hx (Finset.mem_singleton_self i), mul_assoc, trace_algebraMap_mul]
    exact Iff.rfl
  have rhs : (∃ y ∈ omB k K (rB k K x {i}) d, τ' y = algebraMap F K P * z) ↔
      ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
    have h1 : ∀ y, τ' y = algebraMap F K P * z ↔ ((ε : ℤ) : K) * τ y = z := by
      intro y
      simp only [τ', LinearMap.smul_apply, smul_eq_mul]
      rw [show ((ε : ℤ) : K) * algebraMap F K P * τ y = algebraMap F K P * (((ε : ℤ) : K) * τ y) by ring,
        mul_right_inj' hPne]
    simp only [h1]
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp
    · constructor
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simpa using h⟩
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simp [h]⟩
  exact lhs.trans (key.trans rhs)

theorem unif (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (z : K)
    (h : ∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) :
    ∃ N : ℕ, ∀ b ∈ rB k K x {i},
      Algebra.trace F K (z * algebraMap F K (∏ j ∈ I, x j / x i) ^ N * b) ∈ omA k x {i} := by
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  set P : F := ∏ j, x i / x j with hP
  have hs1 : s ∈ rA k x {i} :=
    Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, j, rfl⟩
  have hle : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc {i} i (Finset.mem_singleton_self _)).1 I (Finset.singleton_subset_iff.2 hi)
  haveI : Module.Finite (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {i} (Finset.singleton_nonempty _)).1
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := rA k x {i}) (M := integralClosure (rA k x {i}) K)
  have hg : ∀ g : integralClosure (rA k x {i}) K, ∃ N : ℕ,
      P * Algebra.trace F K (z * g) * s ^ N ∈ rA k x {i} := by
    intro g
    have hgI : (g : K) ∈ rB k K x I := hle g.2
    exact (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi _).1 ((mem_omA_iff hx hi _).1 (h _ hgI))
  choose Nf hNf using hg
  refine ⟨∑ g ∈ S, Nf g, fun b hb => ?_⟩
  rw [mem_omA_iff hx (Finset.mem_singleton_self i)]
  have hb' : (⟨b, hb⟩ : integralClosure (rA k x {i}) K) ∈ Submodule.span (rA k x {i}) (S : Set _) := by
    rw [hS]; trivial
  have key : ∀ w : integralClosure (rA k x {i}) K, w ∈ Submodule.span (rA k x {i}) (S : Set _) →
      P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * w) ∈ rA k x {i} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg)
      have e : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * g) =
          s ^ m * (P * Algebra.trace F K (z * g) * s ^ Nf g) := by
        rw [hm, mul_comm z, ← map_pow, mul_assoc, trace_algebraMap_mul]; ring
      rw [e]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs1 _) (hNf g)
    | zero => simp
    | add a c _ _ ha hc =>
      have e : ((a + c : integralClosure (rA k x {i}) K) : K) = a + c := rfl
      rw [e, mul_add, map_add, mul_add]
      exact add_mem ha hc
    | smul r a _ ha =>
      have e : ((r • a : integralClosure (rA k x {i}) K) : K) = algebraMap F K (r : F) * a := by
        rw [SetLike.val_smul, Algebra.smul_def]; rfl
      have e2 : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a)) =
          (r : F) * (P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a)) := by
        rw [show z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a) =
          algebraMap F K (r : F) * (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a) by ring, trace_algebraMap_mul]
        ring
      rw [e, e2]
      exact Subalgebra.mul_mem _ r.2 ha
  exact key _ hb'

theorem complementary_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI z
  obtain ⟨i, hi⟩ := hI
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsne : algebraMap F K s ≠ 0 :=
    (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx j) (hx i))
  constructor
  · intro h
    obtain ⟨N, hN⟩ := unif k F K d x hc I i hi z h
    obtain ⟨y', hy', hτy'⟩ := (single k F K d x hc τ hτ i _).1 hN
    refine ⟨(algebraMap F K s ^ N)⁻¹ • y', (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d _).2 ⟨N, ?_⟩, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hsne), one_smul]; exact hy'
    · rw [map_smul, hτy', smul_eq_mul]; field_simp; exact mul_comm _ _
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨N, hN⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d y).1 hy
    have h1 := (single k F K d x hc τ hτ i _).2 ⟨_, hN, rfl⟩
    intro b hb
    obtain ⟨M, hM⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc I i hi).2 b).1 hb
    have h2 := (mem_omA_iff hx (Finset.mem_singleton_self i) _).1 (h1 _ hM)
    rw [mem_omA_iff hx hi, GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi]
    refine ⟨N + M, ?_⟩
    convert h2 using 1
    rw [map_smul, smul_eq_mul, show algebraMap F K s ^ N * τ y * (b * algebraMap F K s ^ M) =
      algebraMap F K (s ^ (N + M)) * (τ y * b) by rw [map_pow, pow_add]; ring, trace_algebraMap_mul]
    ring

end GlobalTheory.ComplStd
end


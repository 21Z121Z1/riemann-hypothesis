import Development.EtaleCohomology.EtaleSheaves.Bundle0037
import Development.EtaleCohomology.EtaleSheaves.Bundle0032
import Development.EtaleCohomology.EtaleSheaves.Bundle0038
import Development.EtaleCohomology.TateTwists.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafQuotEtPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.E.LeafQuotEtPf

abbrev J0 (d : ℕ) (C : Type) [CommRing C] : Ideal (MvPolynomial (Fin d) C) :=
  Ideal.span (Set.range fun j => MvPolynomial.X j)

theorem sub_C_mem {d : ℕ} {C : Type} [CommRing C] (p : MvPolynomial (Fin d) C) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ J0 d C := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have : p + q - MvPolynomial.C (MvPolynomial.constantCoeff (p + q)) =
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) +
        (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by simp; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p i _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem ideal_zero_le_ker_constant_coeff {d : ℕ} {C : Type} [CommRing C] :
    J0 d C ≤ RingHom.ker (MvPolynomial.constantCoeff (R := C) (σ := Fin d)) := by
  rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩; simp

theorem bij (d : ℕ) (C : Type) [CommRing C] :
    Function.Bijective ((Ideal.Quotient.mk (J0 d C)).comp MvPolynomial.C) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h := ideal_zero_le_ker_constant_coeff (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    simpa using h
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨MvPolynomial.constantCoeff p, ?_⟩
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq]
    have := (J0 d C).neg_mem (sub_C_mem p)
    simpa using this

theorem LeafQuotEt_of : LateralTheory.E.LeafRoofEtPPf.LeafQuotEt := by
  intro d C B _ _ φ hφ
  let A := MvPolynomial (Fin d) C
  let _ : Algebra A B := φ.toAlgebra
  have : Algebra.Etale A B := RingHom.etale_algebraMap.mp hφ
  have hI : (J0 d C).map (algebraMap A B) = LateralTheory.E.t_E6Cut.varIdeal φ := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  let e0 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (J0 d C)
  let e : (A ⧸ J0 d C) ⊗[A] B ≃+* B ⧸ LateralTheory.E.t_E6Cut.varIdeal φ :=
    ((Algebra.TensorProduct.comm A (A ⧸ J0 d C) B).toRingEquiv.trans e0.symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hI)
  have hg : (algebraMap (A ⧸ J0 d C) ((A ⧸ J0 d C) ⊗[A] B)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.baseChange A B (A ⧸ J0 d C))
  have h1 : (e.toRingHom.comp (algebraMap (A ⧸ J0 d C) ((A ⧸ J0 d C) ⊗[A] B))).Etale :=
    RingHom.Etale.respectsIso.1 _ e hg
  have h2 := RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (bij d C)) h1
  convert h2 using 1
  ext c
  simp only [RingHom.comp_apply]
  show _ = e (Ideal.Quotient.mk (J0 d C) (MvPolynomial.C c) ⊗ₜ[A] (1 : B))
  have : (Ideal.Quotient.mk (J0 d C) (MvPolynomial.C c) ⊗ₜ[A] (1 : B)) =
      (1 : A ⧸ J0 d C) ⊗ₜ[A] φ (MvPolynomial.C c) := by
    have h3 : Ideal.Quotient.mk (J0 d C) (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : A ⧸ J0 d C) := by
      rw [Algebra.smul_def, mul_one]; rfl
    have h4 : φ (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : B) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [h3, h4, TensorProduct.smul_tmul]
  rw [this]
  show _ = Ideal.quotEquivOfEq hI (e0.symm (φ (MvPolynomial.C c) ⊗ₜ[A] (1 : A ⧸ J0 d C)))
  have h5 : e0.symm (φ (MvPolynomial.C c) ⊗ₜ[A] (1 : A ⧸ J0 d C)) = Ideal.Quotient.mk _ (φ (MvPolynomial.C c)) := by
    rw [AlgEquiv.symm_apply_eq]
    simp [e0]
    rfl
  rw [h5]
  rfl

end LateralTheory.E.LeafQuotEtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRootLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafRootLocPf

def kpair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) : StandardEtalePair A where
  f := X ^ q - C u
  monic_f := monic_X_pow_sub_C _ (NeZero.ne q)
  g := X
  cond := ⟨C c * X, 0, q, by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    subst hk
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [show (C (((k + 1 : ℕ) : A)) * X ^ k) * (C c * X) = C (c * ((k + 1 : ℕ) : A)) * X ^ (k + 1) by
      rw [C_mul, pow_succ]; ring]
    rw [hc, C_1, one_mul]⟩

theorem kpair_root {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) :
    (kpair q c hc u).X ^ q = algebraMap A (kpair q c hc u).Ring u := by
  have h : aeval (kpair q c hc u).X (X ^ q - C u) = 0 := (kpair q c hc u).hasMap_X.1
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

theorem kpair_surj {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : Aˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (kpair q c hc (u : A)).Ring)) := by
  intro p
  let K := p.asIdeal.ResidueField
  let Ω := AlgebraicClosure K
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω u) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hu : IsUnit (algebraMap A Ω u) := u.isUnit.map _
  have hzu : IsUnit z := by
    rw [← hz] at hu; exact (isUnit_pow_iff (NeZero.ne q)).mp hu
  have hm : (kpair q c hc (u : A)).HasMap z := by
    refine ⟨?_, ?_⟩
    · simp [kpair, hz]
    · simpa [kpair] using hzu
  let ψ := (kpair q c hc (u : A)).lift z hm
  refine ⟨⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  ext1
  change Ideal.comap _ (RingHom.ker ψ.toRingHom) = p.asIdeal
  rw [RingHom.comap_ker, show ψ.toRingHom.comp (algebraMap A _) = algebraMap A Ω from ψ.comp_algebraMap]
  rw [IsScalarTower.algebraMap_eq A K Ω, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap K Ω).injective, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

theorem loc_of_cover {U Y : Scheme.{0}} (π : Y ⟶ U) [Etale π] [Surjective π]
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : ∀ (V : Scheme.{0}) (h : V ⟶ Y), P V (h ≫ π)) : Loc U P := by
  let 𝒰 : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => Y) (fun _ => π)
      (fun x => ⟨PUnit.unit, π.surjective x⟩) inferInstance
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V g hg
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact hP V h

theorem LeafRootLoc_of : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc := by
  intro q _ U hq u
  obtain ⟨c, hc⟩ := hq.exists_left_inv
  let P := kpair q c hc (u : Γ(U, ⊤))
  let B : CommRingCat.{0} := CommRingCat.of P.Ring
  let φ : Γ(U, ⊤) ⟶ B := CommRingCat.ofHom (algebraMap _ P.Ring)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨kpair_surj q c hc u⟩
  refine loc_of_cover (pullback.fst U.toSpecΓ (Spec.map φ)) _ fun V h => ?_
  have hX : IsUnit P.X := (isUnit_pow_iff (NeZero.ne q)).mp (by rw [kpair_root]; exact u.isUnit.map _)
  have e : (h ≫ pullback.snd _ _) ≫ Spec.map φ = (h ≫ pullback.fst _ _) ≫ U.toSpecΓ := by
    simp [pullback.condition]
  have hcomp : φ ≫ (Scheme.ΓSpecIso B).inv ≫ (h ≫ pullback.snd _ _).appTop = (h ≫ pullback.fst _ _).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop, e,
      Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨Units.map ((h ≫ pullback.snd _ _).appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom).toMonoidHom hX.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [← map_pow, kpair_root]
  exact congrArg (fun f => f.hom (u : Γ(U, ⊤))) hcomp

end LateralTheory.E.LeafRootLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensFactorPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTensFactorPf

theorem lift_lof {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)
      ⟨(s, t), hw⟩ (a ⊗ₜ b)) = τ.mul U s t w hw a b := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

theorem uniq_mul {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) {M : Shv R}
    (ψ ψ' : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec M U)
    (hψ : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ U y) = ψ V (Sec.res g y))
    (hψ' : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ' U y) = ψ' V (Sec.res g y))
    (h : ∀ U s t (hw : s + t = w) a b, ψ U (τ.mul U s t w hw a b) = ψ' U (τ.mul U s t w hw a b))
    (U : Scheme.{0}) (y : Sec (T.X w) U) : ψ U y = ψ' U y := by
  have hl : ∀ V (x : Tens I J V w), ψ V (τ.lift V w x) = ψ' V (τ.lift V w x) := by
    intro V x
    classical
    induction x using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add]; rw [ha, hb]
    | of p z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add]; rw [ha, hb]
      | tmul a c =>
        obtain ⟨⟨s, t⟩, hw⟩ := p
        rw [lift_lof]
        exact h V s t hw a c
  apply LateralTheory.EtaleFoundations.TensFam.sep M
  obtain ⟨S, hS, h1⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := h1 V g hg
  rw [hψ, hψ', ← hx, hl]

theorem secMap_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map f y) = Sec.map f (Sec.res g y) := by
  have := f.hom.naturality g.op
  exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) y) this).symm

theorem addHom_usmul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (n : ℤˣ) (x : A) :
    φ (n • x) = n • φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

end LateralTheory.E.LeafTensFactorPf

namespace LateralTheory.E.LeafTensFactorPf

theorem phi_exists {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ) :
    ∃ φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧
      ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b := by
  obtain ⟨φ, h1, h2⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing R R τ hτ w (K.X w)
    (fun U => (ν.lift U w).toAddMonoidHom) (fun V U g x => LateralTheory.EtaleFoundations.TensFam.lift_res ν g w x)
  refine ⟨φ, h1, fun U s t hw a b => ?_⟩
  have := h2 U (DirectSum.of _ ⟨(s, t), hw⟩ (a ⊗ₜ b))
  rw [lift_lof] at this
  rw [this]
  exact lift_lof ν U s t w hw a b

theorem phi_smul {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ)
    (φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (h2 : ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b)
    (U : Scheme.{0}) (r : ULift.{1} R) (y : Sec (T.X w) U) : φ U (r • y) = r • φ U y := by
  refine uniq_mul τ hτ w (fun U => (φ U).comp (DistribSMul.toAddMonoidHom _ r))
    (fun U => (DistribSMul.toAddMonoidHom _ r).comp (φ U)) ?_ ?_ ?_ U y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [h1]; congr 1; exact map_smul _ r y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← h1]; exact map_smul _ r _
  · intro U s t hw a b
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← LinearMap.map_smul₂, h2, h2, LinearMap.map_smul₂]

def toHom {R : Type} [CommRing R] {F G : Shv R} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (hsm : ∀ U (r : ULift.{1} R) y, φ U (r • y) = r • φ U y) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom { toFun := φ (unop U), map_add' := map_add _, map_smul' := hsm (unop U) }
      naturality := fun U V g => by
        ext y
        exact (hnat _ _ g.unop y).symm }

theorem sheafHom_ext {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = Sec.map g y) : f = g := by
  apply Sheaf.hom_ext
  ext U y
  exact h (unop U) y

theorem factor {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) :
    ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u := by
  choose φ h1 h2 using fun w => phi_exists τ hτ ν w
  have hsm : ∀ w U (r : ULift.{1} R) y, φ w U (r • y) = r • φ w U y :=
    fun w => phi_smul τ hτ ν w (φ w) (h1 w) (h2 w)
  refine ⟨{ f := fun w => toHom (φ w) (h1 w) (hsm w), comm' := ?_ }, ?_⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    apply sheafHom_ext
    intro U y
    show Sec.map (K.d i (i + 1)) (φ i U y) = φ (i + 1) U (Sec.map (T.d i (i + 1)) y)
    refine uniq_mul τ hτ i (M := K.X (i + 1))
      (fun U => ((K.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom.comp (φ i U))
      (fun U => (φ (i + 1) U).comp ((T.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom) ?_ ?_ ?_ U y
    · intro V U g y
      show Sec.res g (Sec.map (K.d i (i + 1)) (φ i U y)) = Sec.map (K.d i (i + 1)) (φ i V (Sec.res g y))
      rw [secMap_nat, h1]
    · intro V U g y
      show Sec.res g (φ (i + 1) U (Sec.map (T.d i (i + 1)) y)) = φ (i + 1) V (Sec.map (T.d i (i + 1)) (Sec.res g y))
      rw [h1, secMap_nat]
    · intro U s t hw a b
      show Sec.map (K.d i (i + 1)) (φ i U (τ.mul U s t i hw a b)) = φ (i + 1) U (Sec.map (T.d i (i + 1)) (τ.mul U s t i hw a b))
      rw [h2, ν.leibniz, τ.leibniz, map_add, addHom_usmul, h2, h2]
  · intro U s t w hw a b
    rw [LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f, LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f]
    exact h2 w U s t hw a b

end LateralTheory.E.LeafTensFactorPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := by
  intro R _ I J T K τ hτ ν
  exact LateralTheory.E.LeafTensFactorPf.factor τ hτ ν
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTrdegDimPf
section
namespace LateralTheory.E.LeafTrdegDimPf

open Algebra

theorem trdeg_le_card (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F) :
    Algebra.trdeg k F ≤ (s.card : Cardinal) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F :=
    ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.1 (h.isAlgebraic x)⟩
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (A := F) (s : Set F)
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk (s : Set F) := Cardinal.mk_le_mk_of_subset hts
    _ = (s.card : Cardinal) := by simp

theorem LeafTrdegDim_of : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := by
  intro k F Ω _ _ _ _ _ _ _ _ n s hs hF R hR
  have hFT : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨d, hd1, hd2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k R
  have h1 : Algebra.trdeg k R ≤ Algebra.trdeg k Ω :=
    trdeg_le_of_injective R.val Subtype.val_injective
  have h2 : Algebra.trdeg k Ω = Algebra.trdeg k F := GlobalTheory.trdeg_eq_of_isAlgebraic_top k F Ω
  have h3 := trdeg_le_card k F s hF
  have hdn : (d : Cardinal) ≤ (n : Cardinal) := by
    rw [← hd2]
    exact h1.trans (h2 ▸ h3.trans (by exact_mod_cast hs))
  have : d ≤ n := by exact_mod_cast hdn
  rw [hd1]
  exact_mod_cast this

end LateralTheory.E.LeafTrdegDimPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwInjPf

theorem prim_field {q : ℕ} [NeZero q] {A : Type} [CommRing A] {K : Type} [Field K] (π : A →+* K)
    (ξ : Prim q A) : IsPrimitiveRoot (π ξ.1) q := by
  have hq : (q : K) ≠ 0 := by simpa using (ξ.2.1.map π).ne_zero
  haveI : NeZero (q : K) := ⟨hq⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := Polynomial.aeval_algHom_apply π.toIntAlgHom ξ.1 (Polynomial.cyclotomic q ℤ)
  rw [ξ.2.2, map_zero] at h
  rw [Polynomial.IsRoot, ← Polynomial.map_cyclotomic q (Int.castRingHom K), Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem pow_val_eq {q : ℕ} [NeZero q] {K : Type} [Field K] {μ : K} (hμ : IsPrimitiveRoot μ q) (m n : ℕ) :
    μ ^ m = μ ^ n ↔ (m : ZMod q) = n := by
  have hf : IsOfFinOrder μ := isOfFinOrder_iff_pow_eq_one.2 ⟨q, NeZero.pos q, hμ.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← hμ.eq_orderOf, ZMod.natCast_eq_natCast_iff]

theorem key {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (c : ULift.{1} (ZMod q))
    (h : c • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = 0) :
    c = 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have hμ := prim_field π ζ
  have hex : ∀ ξ : Prim q A, ∃ u : (ZMod q)ˣ, π ξ.1 = π ζ.1 ^ (u : ZMod q).val := by
    intro ξ
    obtain ⟨j, hj, hj'⟩ := hμ.eq_pow_of_pow_eq_one (prim_field π ξ).pow_eq_one
    have cop : j.Coprime q := (hμ.pow_iff_coprime (NeZero.pos q) j).1 (hj' ▸ prim_field π ξ)
    refine ⟨ZMod.unitOfCoprime j cop, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj, hj']
  have uniq : ∀ u w : (ZMod q)ˣ, π ζ.1 ^ (u : ZMod q).val = π ζ.1 ^ (w : ZMod q).val → u = w := by
    intro u w huw
    rw [pow_val_eq hμ, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at huw
    exact Units.ext huw
  choose e he using hex
  have hmul : ∀ (ζ' ξ : Prim q A) (b : (ZMod q)ˣ), ξ.1 = ζ'.1 ^ (b : ZMod q).val → e ξ = e ζ' * b := by
    intro ζ' ξ b hb
    apply uniq
    rw [← he ξ, hb, map_pow, he ζ', ← pow_mul, pow_val_eq hμ]
    push_cast
    simp [ZMod.natCast_zmod_val]
  have h1 : e ζ = 1 := by
    apply uniq
    rw [← he ζ]
    conv_lhs => rw [← pow_one (π ζ.1)]
    rw [pow_val_eq hμ]
    simp [ZMod.natCast_zmod_val]
  let f := Finsupp.linearCombination (ULift.{1} (ZMod q))
    (fun ξ : Prim q A => (ULift.up (((e ξ) ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)))
  have hker : twRel q i A ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, f, Finsupp.linearCombination_single,
      hmul ζ' ξ b hb, mul_zpow, sub_eq_zero]
    apply ULift.ext
    simp [mul_comm]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  have h2 := hker h
  rw [LinearMap.mem_ker, map_smul] at h2
  have h3 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) = 1 := rfl
  simpa [f, Finsupp.linearCombination_single, h1, h3] using h2

theorem aux {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (x y : ULift.{1} (ZMod q))
    (h : x • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) =
      y • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) : x = y :=
  sub_eq_zero.1 (key i ζ (x - y) (by rw [sub_smul, sub_eq_zero]; exact h))

theorem LeafTwInj_of : LeafTwInj := by
  intro q _ B _ ζ k
  refine ⟨fun {X} x y h => ?_⟩
  by_cases hX : Nonempty X.unop.left
  · haveI : Nontrivial Γ(X.unop.left, ⊤) := by
      obtain ⟨p⟩ := hX
      exact RingHom.domain_nontrivial (X.unop.left.presheaf.germ ⊤ p trivial).hom
    have h0 : x • gen ζ k X.unop = y • gen ζ k X.unop := h
    have hxy : x = y := aux (A := Γ(X.unop.left, ⊤)) k _ x y h0
    subst hxy
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact GrothendieckTopology.top_mem _ _
  · haveI : IsEmpty X.unop.left := not_nonempty_iff.1 hX
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ bot_le ?_
    first
      | exact Scheme.bot_mem_grothendieckTopology _
      | exact bot_mem_grothendieckTopology _
      | exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology (P := @Etale) _

end LateralTheory.E.LeafTwInjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwResHtpyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwResHtpyPf

theorem res_isKInj (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem htpy_of_qiso {C : Type*} [Category C] [Abelian C] {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] [I.IsKInjective] (u u' : L ⟶ I) (h : f ≫ u = f ≫ u') :
    Nonempty (Homotopy u u') := by
  have hY := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hY
  have hf : (HomotopyCategory.subcategoryAcyclic C).trW
      ((HomotopyCategory.quotient C _).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    assumption
  have hb := (hY _ hf).1
  have : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u' := by
    apply hb
    simp only [← Functor.map_comp, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _ this⟩

theorem sh_ext {R : Type} [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {X : Shv R}
    (φ ψ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj P ⟶ X)
    (h : toSheafify Scheme.etaleTopology.{0} P ≫ φ.hom = toSheafify Scheme.etaleTopology.{0} P ≫ ψ.hom) : φ = ψ := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

theorem tw_hom_ext (q : ℕ) (i : ℤ) {X : Shv (ZMod q)} (φ ψ : tw q i ⟶ X)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) : φ = ψ := by
  apply sh_ext
  ext U : 2
  apply ModuleCat.hom_ext
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
  exact h U.unop ζ

end LateralTheory.E.LeafTwResHtpyPf

open LateralTheory.E.LeafTwResHtpyPf in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := by
  intro q _ k T e hT u u' hu
  obtain ⟨_, ε, hε, he⟩ := hT
  have := res_isKInj (ZMod q) (tw q k)
  refine htpy_of_qiso ε u u' ?_
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0 := by
    apply tw_hom_ext
    intro U ζ
    have := hu U ζ
    rw [← he U ζ] at this
    exact this
  have h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  have h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  exact h1.trans ((congrArg _ key).trans h2.symm)
end
end


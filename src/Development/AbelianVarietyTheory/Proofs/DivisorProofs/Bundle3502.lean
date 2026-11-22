import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRoots
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitForm

theorem exists_coords {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (τ : Forms.balForms ℤ O X B) :
    ∃ c : J → B, ∀ a b, (τ : Forms.Bil X B) a b = ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel O X)
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  refine ⟨fun k => ∑ j, ε.repr (β j) k • Forms.balTensorLift τ (e j), fun a b => ?_⟩
  have h1 (j) : e.repr (Forms.balTensorMk O a b) j =
      ∑ k, ε.repr (β j) k * (ε k : LinearMap.BilinForm ℤ X) a b := by
    have h := congrArg (fun g : PolFan.balForms (star : O → O) X =>
      (g : LinearMap.BilinForm ℤ X) a b) (ε.sum_repr (β j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  rw [← Forms.balTensorLift_mk, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
  simp only [map_zsmul]
  simp only [h1, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_comm]

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    [IsAlgClosed (ResidueField V)] {n : ℕ} (hn : IsUnit (n : V)) (u : Vˣ) :
    ∃ v : Vˣ, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue V u) (Nat.pos_of_ne_zero hn0)
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsUnit a := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0] at hz
    exact (residue_ne_zero_iff_isUnit _).2 u.isUnit hz.symm
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian (R := V) (I := maximalIdeal V)
    (Polynomial.X ^ n - Polynomial.C (u : V)) (Polynomial.monic_X_pow_sub_C _ hn0) a
    (by
      rw [← residue_eq_zero_iff]
      simp [hz])
    (by
      refine IsUnit.map _ ?_
      simpa [Polynomial.derivative_X_pow] using ⟨hn, ha.pow _⟩)
  have hy' : y ^ n = u := by
    simpa [sub_eq_zero] using hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0).1 (hy' ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext (by simpa using hy')⟩

theorem mem_of_diag {O : Type} [CommRing O] (bar : O → O) {w : O} (hw : w + bar w = 1)
    {X : Type} [AddCommGroup X] [Module O X] {G : Type} [CommGroup G] (U : Subgroup G)
    (q : X → X → G) (hs : ∀ a b, q a b = q b a) (ha : ∀ a a' b, q (a + a') b = q a b * q a' b)
    (hb : ∀ (x : O) a b, q (x • a) b = q a (bar x • b)) (hd : ∀ y, q y (w • y) ∈ U) (a b : X) :
    q a b ∈ U := by
  have hr (a b b') : q a (b + b') = q a b * q a b' := by rw [hs, ha, hs b, hs b']
  have h1 : q a (w • b) * q b (w • a) = q a b := by
    rw [hs b, hb, ← hr, ← add_smul, hw, one_smul]
  have h2 : q a b = q (a + b) (w • (a + b)) / (q a (w • a) * q b (w • b)) := by
    rw [smul_add, ha, hr, hr, ← h1, eq_div_iff_mul_eq']
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h2]
  exact U.div_mem (hd _) (U.mul_mem (hd _) (hd _))

theorem exists_unit_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  intro E _ _ _ H X _ _ _ _ V _ _ _ hV hk n hn m N ε t ht q hs ha hb hd
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  let φ : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V) : V →* FractionRing V)
  have hφ : Function.Injective φ := Units.map_injective hinj
  let τ : Fin m → (FractionRing V)ˣ := fun i =>
    Units.mk0 (algebraMap V (FractionRing V) (t i)) (fun h => ht i (hinj (by rw [h, map_zero])))
  let M : X → X → (FractionRing V)ˣ := fun a b =>
    ∏ i, τ i ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) a b)
  have Ms (a b) : M a b = M b a := Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.1 a b]
  have Ma (a a' b) : M (a + a') b = M a b * M a' b := by
    simp only [M, map_add, LinearMap.add_apply, mul_add, zpow_add, Finset.prod_mul_distrib]
  have Mb (x : 𝓞 E) (a b) : M (x • a) b = M a (H.bar x • b) :=
    Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.2 x a b]
  have hmem := mem_of_diag H.bar hw φ.range (fun a b => q a b / M a b)
    (fun a b => by rw [hs, Ms]) (fun a a' b => by rw [ha, Ma, mul_div_mul_comm])
    (fun x a b => by rw [hb, Mb]) (fun y => by
      obtain ⟨u, hu⟩ := hd y
      refine ⟨u, ?_⟩
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      rw [hu]
      simp [M, τ, φ])
  choose u hu using hmem
  have us (a b) : u a b = u b a := hφ (by rw [hu, hu, hs, Ms])
  have ua (a a' b) : u (a + a') b = u a b * u a' b :=
    hφ (by rw [map_mul, hu, hu, hu, ha, Ma, mul_div_mul_comm])
  have ub (x : 𝓞 E) (a b) : u (x • a) b = u a (H.bar x • b) := hφ (by rw [hu, hu, hb, Mb])
  have ur (a b b') : u a (b + b') = u a b * u a b' := by rw [us, ua, us b, us b']
  obtain ⟨c, hc⟩ := exists_coords (O := 𝓞 E) hw ε ⟨Forms.bilOfMul u ua ur, us, ub⟩
  choose v hv using fun k => exists_root hn (c k).toMul
  refine ⟨Sum.elim (fun i => t i * v (.inl i)) (fun j => v (.inr j)),
    fun i => ⟨(v (.inl i))⁻¹, by simp⟩, fun j => Units.isUnit _, fun a b => ?_⟩
  have h1 : u a b = ∏ k, v k ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
    have h := congrArg Additive.toMul (hc a b)
    simp only [toMul_sum, toMul_zsmul, ← hv] at h
    simp only [zpow_mul, zpow_natCast]
    exact h
  have h2 : q a b = M a b * φ (u a b) := by rw [hu, mul_div_cancel]
  rw [h2, h1]
  simp [M, τ, φ, Fintype.prod_sum_type, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.UnitForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitFiniteExtensionClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UTraitExtLab

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → ∃ (T' : UTrait Xo cf) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : ratHull S.R →+* FractionRing T'.V) (e : T'.P.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₁ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.be a b = (k : ℤ) * T.be (e a) (e b) := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ _ S u' p _ y₁ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI hTc : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p T.V hTc ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p T.V hTc ι hι hQ S.R (y₁.comp (toRat S.R))
  have hy₁ : ∀ a, y₁ a ∈ κ.range := fun a => by
    obtain ⟨n, hn, ha⟩ := mem_ratHull.1 a.2
    obtain ⟨x, hx⟩ := hy₀ ⟨_, ha⟩
    have h0 : (n : PadicAlgCl p) ≠ 0 := Int.cast_ne_zero.2 hn
    have h1 : toRat S.R ⟨_, ha⟩ = (n : ratHull S.R) * a := Subtype.ext rfl
    rw [RingHom.comp_apply, h1, map_mul, map_intCast] at hx
    refine ⟨(n : FractionRing W)⁻¹ * x, ?_⟩
    rw [map_mul, map_inv₀, map_intCast, hx, inv_mul_cancel_left₀ h0]
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf W hbase inferInstance (spMap fK ≫ T.y)
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  haveI hTc' : IsAdicComplete (maximalIdeal T'.V) T'.V := T'.cdvr.2.1
  haveI : CharZero T'.V := T'.cdvr.2.2
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := IsAlgClosed.lift
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₁ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₁ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : ratHull S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₁.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₁ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₁.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hTc'⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.UPoinc.uTraitUniqSt_holds E H Dw l Xo cf T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by
      rw [hTy, spMap_comp_ringHom, Category.assoc]
      rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp_ringHom, hyK, hy, hTy, ← hιc, spMap_comp_ringHom,
      spMap_comp_ringHom, Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [LinearEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.UTraitExtLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UTraitPt

theorem spMap_comp_eq {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem exists_embed_padicAlgCl (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (f : integralClosure ℤ_[p] K →+* W) (fK : FractionRing (integralClosure ℤ_[p] K) →+* FractionRing W)
    (hfin : f.Finite) (hfK : ∀ a, fK (algebraMap _ _ a) = algebraMap W (FractionRing W) (f a)) :
    ∃ (ι : FractionRing W →+* PadicAlgCl p) (j : W →+* OO p),
      (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧
      (∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v)) ∧ IsLocalHom j ∧
      ∀ a, (j (f a) : PadicAlgCl p) = ((a : K) : PadicAlgCl p) := by
  let V₀ := integralClosure ℤ_[p] K
  letI : Algebra V₀ W := f.toAlgebra
  haveI : Module.Finite V₀ W := hfin
  haveI : IsFractionRing V₀ K := integralClosure.isFractionRing_of_finite_extension ℚ_[p] K
  let eK : K ≃ₐ[V₀] FractionRing V₀ := IsLocalization.algEquiv (nonZeroDivisors V₀) K (FractionRing V₀)
  letI : Algebra K (FractionRing W) := (fK.comp eK.toRingHom).toAlgebra
  have e : (algebraMap W (FractionRing W)).comp (algebraMap V₀ W) =
      (algebraMap K (FractionRing W)).comp (algebraMap V₀ K) := by
    refine RingHom.ext fun a => ?_
    show algebraMap W (FractionRing W) (f a) = fK (eK (algebraMap V₀ K a))
    rw [AlgEquiv.commutes, hfK]
  obtain ⟨K', hKK', hK', τ, f', hτK, hτW⟩ :=
    GlobalTheory.SS.exists_ringHom_integralClosure p K W (FractionRing W) e
  let ι : FractionRing W →+* PadicAlgCl p := K'.val.toRingHom.comp τ
  let j : W →+* OO p := (integralClosureToPadicAlgClIntegers K').comp f'
  have hj : ∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v) := fun v => by
    show ((f' v : K') : PadicAlgCl p) = ((τ (algebraMap W (FractionRing W) v) : K') : PadicAlgCl p)
    rw [← RingHom.comp_apply τ, hτW]; rfl
  have hball : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
    intro x
    constructor
    · intro hx
      have hint : IsIntegral ℤ_[p] (τ x) := (mem_integralClosure_padicInt_iff K' (τ x)).2 hx
      let ρ : ℤ_[p] →+* W := f.comp (algebraMap ℤ_[p] V₀)
      letI : Algebra ℤ_[p] W := ρ.toAlgebra
      have hτc : ∀ r : ℤ_[p], τ (algebraMap ℤ_[p] (FractionRing W) r) = algebraMap ℤ_[p] K' r := by
        intro r
        have h1 : algebraMap ℤ_[p] (FractionRing W) r =
            (algebraMap K (FractionRing W)) (algebraMap V₀ K (algebraMap ℤ_[p] V₀ r)) := by
          rw [IsScalarTower.algebraMap_apply ℤ_[p] W (FractionRing W)]
          exact congrArg (fun φ : V₀ →+* FractionRing W => φ (algebraMap ℤ_[p] V₀ r)) e
        rw [h1, ← RingHom.comp_apply τ, hτK]
        rfl
      let τa : FractionRing W →ₐ[ℤ_[p]] K' := { τ with commutes' := hτc }
      have hx' : IsIntegral ℤ_[p] x := (isIntegral_algHom_iff τa τ.injective).1 hint
      have hxW : IsIntegral W x := hx'.tower_top
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxW
      exact ⟨w, hw⟩
    · rintro ⟨w, rfl⟩
      rw [← hj]
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (j w).2
  refine ⟨ι, j, hball, hj, ⟨fun v hv => ?_⟩, fun a => ?_⟩
  · obtain ⟨u, hu⟩ := hv.exists_right_inv
    have hu' : ι (algebraMap W (FractionRing W) v) * (u : PadicAlgCl p) = 1 := by
      rw [← hj]; exact congrArg (fun z : OO p => (z : PadicAlgCl p)) hu
    have h0 : algebraMap W (FractionRing W) v ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hu'; exact zero_ne_one hu'
    have hinv : (algebraMap W (FractionRing W) v)⁻¹ ∈ Set.range (algebraMap W (FractionRing W)) := by
      rw [← hball, map_inv₀, ← eq_inv_of_mul_eq_one_right hu']
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
    obtain ⟨w, hw⟩ := hinv
    refine IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective W (FractionRing W) ?_)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ h0]
  · rw [hj]
    have h1 : algebraMap W (FractionRing W) (f a) = algebraMap K (FractionRing W) (algebraMap V₀ K a) :=
      congrArg (fun φ : V₀ →+* FractionRing W => φ a) e
    show ((τ (algebraMap W (FractionRing W) (f a)) : K') : PadicAlgCl p) = _
    rw [h1, ← RingHom.comp_apply τ, hτK]
    rfl

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

theorem exists_lift_i {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (C : UCompact Xo c) (F : Type) [Field F]
    (g : Sp F ⟶ C.Z) (hg : Set.range g ⊆ Set.range C.i) : ∃ g' : Sp F ⟶ Xo.XF c, g' ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  let pt : Sp F := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, hx⟩ := hg ⟨pt, rfl⟩
  let φ : C.o →+* F := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hφi : Function.Injective φ := by
    have e : (spMap φ) pt = (spMap C.b) ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
      rw [hφ, Scheme.Hom.comp_apply, ← hx]
      show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
      rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
      rfl
    have e2 : RingHom.ker φ = ⊥ := by
      have := congrArg PrimeSpectrum.asIdeal e
      have h1 : ((spMap φ) pt).asIdeal = RingHom.ker φ := by
        show Ideal.comap φ ⊥ = _
        rfl
      rw [h1] at this
      rw [this]
      haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
      show Ideal.comap C.b _ = ⊥
      rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.comap_bot_of_injective _ C.inj]
    exact (RingHom.injective_iff_ker_eq_bot φ).2 e2
  let ψ : c.F →+* F := IsFractionRing.lift hφi
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsFractionRing.lift_algebraMap hφi a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact spMap_comp_eq _ _
  let g₁ : Sp F ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hw : w = pt := Subsingleton.elim _ _
    subst hw
    refine ⟨x, hinj ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hx
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

theorem exists_uTrait_of_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i → ∃ (T : UTrait Xo c) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C X₁ Y πY p _ y hy
  haveI : Algebra.FiniteType ℤ X₁.o₁ := X₁.ar.ft
  haveI := Y.lft
  haveI hSpecZ : LocallyOfFiniteType (spMap (algebraMap ℤ X₁.o₁)) := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ X₁.o₁)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨K, hK, hKall⟩ := padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI : FiniteDimensional ℚ_[p] K := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := hKall K le_rfl
  let V₀ := integralClosure ℤ_[p] K
  haveI hdvr : IsDiscreteValuationRing V₀ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K
  haveI : Module.Finite ℤ_[p] V₀ := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsAdicComplete (maximalIdeal V₀) V₀ := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] _
  haveI : CharZero V₀ := inferInstance
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

  have hj₀i : Function.Injective ((OO p).subtype.comp j₀) := by
    intro a b h
    have h' : ((a : K) : PadicAlgCl p) = ((b : K) : PadicAlgCl p) := by
      rw [← hj₀, ← hj₀]; exact h
    exact Subtype.ext (Subtype.ext h')
  obtain ⟨e₀, he₀'⟩ : ∃ e₀ : FractionRing V₀ →+* PadicAlgCl p,
      ∀ a, e₀ (algebraMap V₀ (FractionRing V₀) a) = ((OO p).subtype.comp j₀) a :=
    ⟨IsFractionRing.lift hj₀i, fun a => IsFractionRing.lift_algebraMap hj₀i a⟩
  have he₀ : e₀.comp (algebraMap V₀ (FractionRing V₀)) = (OO p).subtype.comp j₀ := RingHom.ext he₀'
  have hgy : gPt p ≫ y = spMap e₀ ≫ jK V₀ ≫ y₀ := by
    rw [← hy₀, ← Category.assoc, ← Category.assoc]
    congr 1
    show spMap (OO p).subtype ≫ spMap j₀ = spMap e₀ ≫ spMap (algebraMap V₀ (FractionRing V₀))
    rw [← spMap_comp_eq, ← spMap_comp_eq, he₀]
  let gen₀ : Sp (FractionRing V₀) ⟶ C.Z := jK V₀ ≫ y₀ ≫ πY ≫ X₁.π
  have hgen : Set.range gen₀ ⊆ Set.range C.i := by
    rintro _ ⟨w, rfl⟩
    let q : Sp (PadicAlgCl p) := ⟨⊥, Ideal.isPrime_bot⟩
    have hw : w = (spMap e₀) q := Subsingleton.elim _ _
    apply hy
    refine ⟨q, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply]
    congr 1
    rw [← Category.assoc, hgy]
    simp only [gen₀, Category.assoc]
  obtain ⟨yK, hyK⟩ := exists_lift_i C (FractionRing V₀) gen₀ hgen
  obtain ⟨T, f, fK, -, -, hfin, hfK, hTy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V₀ hB hdvr yK
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨ι, j, hball, hj, hloc, hjf⟩ := exists_embed_padicAlgCl p K T.V f fK hfin hfK
  refine ⟨T, ι, j, spMap f ≫ y₀, hball, hj, hloc, ?_, ?_⟩
  · have hjf' : j.comp f = j₀ := RingHom.ext fun a => Subtype.ext ((hjf a).trans (hj₀ a).symm)
    rw [← Category.assoc, ← spMap_comp_eq, hjf', hy₀]
  · have hc : jK T.V ≫ spMap f = spMap fK ≫ jK V₀ := by
      show spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap f = spMap fK ≫ spMap (algebraMap V₀ (FractionRing V₀))
      rw [← spMap_comp_eq, ← spMap_comp_eq]
      congr 1
      exact RingHom.ext fun a => (hfK a).symm
    rw [hTy, Category.assoc (spMap fK), hyK]
    simp only [gen₀, ← Category.assoc]
    rw [hc]

end GlobalTheory.UTraitPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMinStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_uChart_le_min_signature : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  first | exact @GlobalTheory.UChart.Fam.finrank_le_min | exact GlobalTheory.UChart.Fam.finrank_le_min | (intros; apply GlobalTheory.UChart.Fam.finrank_le_min <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGermsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrder_translation_formula_germs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  first | exact @GlobalTheory.TranslGerm.transl_germ | exact GlobalTheory.TranslGerm.transl_germ | (intros; apply GlobalTheory.TranslGerm.transl_germ <;> assumption)
end


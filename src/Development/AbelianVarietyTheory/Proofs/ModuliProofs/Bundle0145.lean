import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ.rt_coe (S A : ℕ) : ((RZ.rt H S A : RZ H S A) : ℂ) = H.rt0 := by
  have h2 : ((2 : RZ H S A) : ℂ) = 2 := map_ofNat (RZ H S A).subtype 2
  unfold RZ.rt
  push_cast
  rw [h2]
  ring

theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (KA l))
    (o : Obj D l (baseKA l) s) (β : RZ H n l.A →+* KA l) (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) :
    FullObj D (s ≫ spMap β) o.t o.etaA := by
  unfold IsInc at hβ
  have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := by
    apply Subtype.ext
    show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0
    rw [← RZ.rt_coe (H := H) n l.A]
    exact hβ (RZ.rt H n l.A)
  have hze : β (RZ.ze H n l.A) = (baseKA l).ζ := by
    apply Subtype.ext
    show ((β (RZ.ze H n l.A) : ℂ)) = zeta l.A
    exact hβ (RZ.ze H n l.A)
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩
  intro k _ _ _ x β' hx
  obtain ⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by
    refine ⟨(Spec.preimage (x ≫ s)).hom, ?_⟩
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : β' = g0.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β)) := by
      unfold spMap at hx hg0
      rw [← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hb
  obtain ⟨hdet, I, hI1, hI2, -⟩ := o.geom k x g0 hg0
  refine ⟨?_, I, ?_, hI2⟩
  · rw [RingHom.comp_apply, hρ]
    exact hdet
  · rw [RingHom.comp_apply, hze]
    exact hI1

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpFamOfDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild.Fibre

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S S' : Scheme.{0}}

theorem basis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

variable {A : Over S'} {Z : Over S} {x : S' ⟶ S} {φ : A.left ⟶ Z.left}

theorem comp_eq_pushPt (w : φ ≫ Z.hom = A.hom ≫ x) {a : Out.baseOver S' ⟶ A} {s : Out.baseOver S ⟶ Z}
    (h : a.left ≫ φ = x ≫ s.left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S) : t ≫ s = pushPt w (u ≫ a) := by
  apply Over.OverMorphism.ext
  have h1 : t.left = T.hom ≫ x := by simpa using Over.w t
  have h2 : u.left = T.hom := by simpa using Over.w u
  change t.left ≫ s.left = (u.left ≫ a.left) ≫ φ
  rw [h1, h2, Category.assoc, Category.assoc, h]

theorem basis_push [GrpObj A] [GrpObj Z] (hφ : IsGrpPullback A Z x φ) {r k : ℕ}
    {a : Fin r → (Out.baseOver S' ⟶ A)} {s : Fin r → (Out.baseOver S ⟶ Z)}
    (h : ∀ i, (a i).left ≫ φ = x ≫ (s i).left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S)
    (hb : ∀ z : T ⟶ A, z ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ a i) (fun i => (c i).val) = z)
    (z : Over.mk (T.hom ≫ x) ⟶ Z) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => t ≫ s i) (fun i => (c i).val) = z := by
  have inj : Function.Injective (pushHom hφ T) := fun y y' e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))
  obtain ⟨z, rfl⟩ := GrpDense.pushPt_surjective hφ.1 T z
  change pushHom hφ T z ^ k = 1 at hz
  rw [← map_pow, map_eq_one_iff _ inj] at hz
  have key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e =
      pushHom hφ T (Out.linComb (fun i => u ≫ a i) e) := fun e => by
    simp only [Out.linComb, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp, map_pow]
    rw [comp_eq_pushPt hφ.1.w (h i) u t]
    rfl
  simp only [key]
  change ∃! c : Fin r → ZMod k, _ = pushHom hφ T z
  simp only [inj.eq_iff]
  exact hb z hz

theorem lab_single {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · simp

theorem lab_zero {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) : t.lab 0 = 1 := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn]
  simp

theorem one_left {A : Over S} [GrpObj A] : (1 : Out.baseOver S ⟶ A).left = (η[A]).left :=
  Category.id_comp _

end GlobalTheory.ZM.NearBuild.Fibre

namespace GlobalTheory.ZM.NearBuild

open Fibre

theorem grpFam_of_dense_fibres :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (mu : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), N' ≠ 0 → DenseP (objPrimes b Mat κ β v) → Fam b Mat κ β v m M th sc → SmoothOfRelativeDimension g Z.hom → GeometricallyConnected Z.hom → AddAt b Mat κ β v m M th sc mu → (∀ i, EndAt b Mat κ β v m M th sc i (F i)) → ∃ _ : GrpObj Z, GrpFam b Mat κ β v m Z M (fun i => F (some i)) (fun i => sc (Pi.single i 1)) := by
  intro hL _ o _ g N' J b Mat κ R _ _ _ β v m Z M th sc mu F hN0 hden ⟨⟨I, p, hrep, _⟩, _, hfib⟩ hsm hgc hm hF
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (N' : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_denseP hden
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ N').left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z mu (F none) (sc 0) _ hD hs hpr hgc (by
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x s t' φ ht hφ, ?_, ?_⟩
    · have := hF none K x s t' φ ht hφ
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF (some i) K x s t' φ ht hφ, ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) (i),
      (t'.pt i ^ N') ^ N' = 1 := fun t' i => by
    have e : N' * N' = N' ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ N' = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z N' (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := hun.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, hφ⟩ := hfib K x s t' ht
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  refine ⟨inferInstance, hab, hsm, hrep.1, hamp, ⟨hhom, hQ, hB⟩, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x s t' ht
  exact ⟨φ, ⟨hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ), fun i => (hF (some i) K x s t' φ ht hφ).symm,
    h1 t' hφ.2.2.2⟩, hφ.2.2.1⟩

end GlobalTheory.ZM.NearBuild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCover
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ThetaLocal

open GlobalTheory.AbLocusPull

variable {X X' : Scheme.{0}}

theorem fn_ext_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    {a b : Γ(X, U)} (h : ∀ x, F x ∈ U → gs F x U a = gs F x U b) : a = b := by
  have := F.isIso_app U hU
  apply (ConcreteCategory.bijective_of_isIso (F.app U)).1
  refine fn_ext fun x hx => ?_
  have e₁ := gs_pull (𝟙 X') F x U hx a
  have e₂ := gs_pull (𝟙 X') F x U hx b
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h x hx).trans e₂.symm)

theorem exists_fn_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    (b : Γ(X', F ⁻¹ᵁ U)) : ∃ a : Γ(X, U), ∀ x, F x ∈ U → gs F x U a = gs (𝟙 X') x _ b := by
  have := F.isIso_app U hU
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (F.app U)).2 b
  refine ⟨a, fun x hx => ?_⟩
  have e₁ := gs_pull (𝟙 X') F x U hx a
  rw [Category.id_comp] at e₁
  exact e₁.symm

theorem exists_secOn_push {F : X' ⟶ X} [IsOpenImmersion F] {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hr : W ≤ F.opensRange) (hW : F ⁻¹ᵁ W ≤ W')
    {θ' : ∀ k, Γ(X', W' ⊓ L'.U k)} (hθ' : θ' ∈ secOn L' W') :
    ∃ θ ∈ secOn L W, ∀ x, F x ∈ W → ∀ j k, F x ∈ L.U j → x ∈ X'.basicOpen (θ' k) → F x ∈ X.basicOpen (θ j) := by
  obtain ⟨w, hw⟩ := hw
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', F x ∈ W → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) =
        (gm F x (L.U j ⊓ L.U j') (L.g j j')).val * ((gw w (𝟙 X') x j' k').val * gs (𝟙 X') x _ (θ' k')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ' (𝟙 X') x k k' (hW hx) hk hk', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul]
    congr 2
    rw [mul_right_comm, inv_mul_cancel_right]
  have ex : ∀ j, ∃ a : Γ(X, W ⊓ L.U j), ∀ x k, F x ∈ W → F x ∈ L.U j → x ∈ L'.U k →
      gs F x _ a = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
    intro j
    let O : L'.ι → X'.Opens := fun k => F ⁻¹ᵁ W ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ k, O k ≤ W' ⊓ L'.U k := fun k x hx => ⟨hW hx.1, hx.2.2⟩
    let u : ∀ k, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun k => w.s (fun _ => j, k)
    let a : ∀ k, Γ(X', O k) := fun k => resG X' inf_le_right (u k).val * resG X' (le k) (θ' k)
    have va : ∀ x k, x ∈ O k → gs (𝟙 X') x _ (a k) = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
      intro x k hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (F ⁻¹ᵁ (W ⊓ L.U j)) O (fun k x hx => ⟨hx.1, mem_pull.1 hx.2.1⟩)
      (fun x hx => (exists_chart hL' x).imp fun k hk => ⟨hx.1, mem_pull.2 hx.2, hk⟩) a (fun k k' x hk hk' => by
        rw [va x k hk, va x k' hk', rel x j j k k' hk.1 (mem_pull.1 hk.2.1) (mem_pull.1 hk.2.1) hk.2.2 hk'.2.2,
          gm_self hL F x (mem_pull.1 hk.2.1), Units.val_one, _root_.one_mul])
    obtain ⟨c, hc⟩ := exists_fn_of_isOpenImmersion F (inf_le_left.trans hr) b
    refine ⟨c, fun x k hx hj hk => ?_⟩
    have hm : x ∈ O k := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hc x ⟨hx, hj⟩).trans ((hb x k hm).trans (va x k hm))
  choose θ hθ using ex
  refine ⟨θ, fun j j' => fn_ext_of_isOpenImmersion F (inf_le_left.trans (inf_le_left.trans hr)) fun x hx => ?_,
    fun x hx j k hj hk => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' x
    rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit F x (L.U j ⊓ L.U j') ⟨hx.1.2, hx.2⟩, hθ j x k hx.1.1 hx.1.2 hk, hθ j' x k hx.1.1 hx.2 hk]
    exact rel x j j' k k hx.1.1 hx.1.2 hx.2 hk hk
  · have hm : x ∈ W' ⊓ L'.U k := X'.basicOpen_le _ hk
    refine (isUnit_gs_iff F x (W ⊓ L.U j) ⟨hx, hj⟩ _).1 ?_
    rw [hθ j x k hx hj hm.2]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X') x _ hm _).2 hk)

theorem hasTheta_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  intro E _ _ _ H Z t I Y f u m hf hc hu z
  obtain ⟨i, y, rfl⟩ := hc z
  have := hf i
  have h := (m i).cart.1
  have : IsOpenImmersion (m i).cm.F := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  obtain ⟨w, g, -⟩ := (m i).lin
  have sq : ∀ x, t.G.hom ((m i).cm.F x) = f i ((u i).G.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hy, θ', hθ', hne⟩ := hu i y
  have hr : t.G.hom ⁻¹ᵁ (f i ''ᵁ V) ≤ (m i).cm.F.opensRange := by
    rintro x ⟨y', -, e⟩
    obtain ⟨x', h₁, -⟩ := Scheme.exists_preimage_of_isPullback h x y' e.symm
    exact ⟨x', h₁⟩
  have hW : (m i).cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ (f i ''ᵁ V)) ≤ (u i).G.hom ⁻¹ᵁ V := by
    rintro x ⟨y', hy', e⟩
    have e' : y' = (u i).G.hom x := (f i).isOpenEmbedding.injective (e.trans (sq x))
    show (u i).G.hom x ∈ V
    rw [← e']; exact hy'
  obtain ⟨θ, hθ, hb⟩ := exists_secOn_push t.PP.isLB (u i).PP.isLB ⟨w, g⟩ hr hW hθ'
  refine ⟨f i ''ᵁ V, ⟨y, hy, rfl⟩, θ, hθ, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨x, k, hx, hk⟩ := hne y' hy'
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB ((m i).cm.F x)
  refine ⟨(m i).cm.F x, j, (sq x).trans (congrArg _ hx), hb x ⟨y', hy', ?_⟩ j k hj hk⟩
  exact ((sq x).trans (congrArg _ hx)).symm

end GlobalTheory.ThetaLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in

theorem lin_of_isEmpty {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} [hT : IsEmpty T'.left]
    (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T')) : Lin G L N h b c s := by
  intro z
  exact isEmptyElim ((fst T' G).left z)

theorem isEmpty_of_eq_bot {Z : Scheme.{0}} {U : Z.Opens} (h : U = ⊥) : IsEmpty U.toScheme := by
  subst h
  exact ⟨fun x => by simpa using x.2⟩

theorem subsingleton_sections_of_isEmpty {X : Scheme.{0}} [IsEmpty X] : Subsingleton Γ(X, ⊤) := by
  refine CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)
  ext x
  exact isEmptyElim x

open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in

theorem trans_of_inf_eq_bot {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) {n : ℕ} (r s : ℤ) {U V : Z.Opens}
    (hUV : U ⊓ V = ⊥) (thU : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk U.ι)))
    (thV : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk V.ι)))
    (bU : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))) (bV : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk V.ι)))
    (g : Γ(Z, U ⊓ V)) :
    ∃ (c : Γ((U ⊓ V).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((U ⊓ V).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => thU) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        (fun _ : Fin 1 => thV) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => bU k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        bV (fun k' => M.val k k') t) ∧
    (U ⊓ V).topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val := by
  have hE : IsEmpty (U ⊓ V).toScheme := isEmpty_of_eq_bot hUV
  have := subsingleton_sections_of_isEmpty (X := (U ⊓ V).toScheme)
  have sec : ∀ M : ℕ, LB.Sec (LPow G L (M : ℤ) (Over.mk (U ⊓ V).ι)) := fun M =>
    { f := fun _ => 0
      compat := fun _ _ => fn_ext fun y _ => (hE.false ((fst (Over.mk (U ⊓ V).ι) G).left y)).elim }
  refine ⟨1, 1, ⟨sec 1, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _⟩,
    fun k => ⟨sec N, lin_of_isEmpty (hT := hE) G L N _ _ _ _, lin_of_isEmpty (hT := hE) G L N _ _ _ _⟩,
    Subsingleton.elim _ _⟩

theorem hasFrames_sumLB : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  intro Z G L N A B n r s hAB hA hB
  obtain ⟨thA, bA, hAt, hAb⟩ := hA
  obtain ⟨thB, bB, hBt, hBb⟩ := hB
  refine ⟨fun | .inl i => thA i | .inr j => thB j, fun | .inl i => bA i | .inr j => bB j, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · exact hAt i j
    · exact trans_of_inf_eq_bot G L N r s (hAB i j) (thA i) (thB j) (bA i) (bB j) _
    · exact trans_of_inf_eq_bot G L N r s (by rw [inf_comm]; exact hAB j i) (thB i) (thA j) (bB i) (bA j) _
    · exact hBt i j
  · rintro (i | i) W _ _ _ hW χ hχ
    · exact hAb i W hW χ hχ
    · exact hBb i W hW χ hχ

end GlobalTheory.ModelSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirationalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_near_normal_point_of_finite_birational : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.main | exact GlobalTheory.FiniteBirationalNear.main | (intros; apply GlobalTheory.FiniteBirationalNear.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.isProjOver_comp_finite : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isProjOver_comp_of_finite | exact GlobalTheory.isProjOver_comp_of_finite | (intros; apply GlobalTheory.isProjOver_comp_of_finite <;> assumption)
end


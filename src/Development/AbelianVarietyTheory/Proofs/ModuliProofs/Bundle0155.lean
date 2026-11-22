import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0145
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0117

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjectAtMinimalPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem TObj.HasTh.unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem exists_object_at_minimalPrime :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ w w' d, Out.Laws → Out.Laws2 → 3 ≤ N' → Odd N' → Countable o → GoodClass em C Mat κ w w' d → ∀ 𝔭 ∈ (thIdeal em C).minimalPrimes, ∃ t v, C t ∧ t.HasTh (𝟙 _) v ∧ RingHom.ker (MvPolynomial.eval₂Hom em v) = 𝔭 := by
  intro o _ g N' J b em C Mat κ w w' d hL hL2 h3 _ _ hG 𝔭 h𝔭
  classical
  obtain ⟨r, B, θ, hB, hC⟩ := hG.fam
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ (by omega)⟩
  have hvg := fun i : {i : Fin r // (B i).Nonempty} =>
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em (Ix g (N' ^ 2)) d (B i) (θ i)
      (hB i).1 (hB i).2.1 i.2 (hB i).2.2.1
  choose z hz c hc hgen using hvg
  let p : {i : Fin r // (B i).Nonempty} → Ideal (MvPolynomial (Ix g (N' ^ 2)) o) := fun i =>
    RingHom.ker (MvPolynomial.eval₂Hom em (c i • θ i (z i)))
  have hobj : ∀ i, ∃ t, C t ∧ t.HasTh (𝟙 _) (c i • θ i (z i)) := by
    intro i
    obtain ⟨t, ht, hth⟩ := ((hB i).2.2.2 (z i) (hz i)).1
    exact ⟨t, ht, hth.unit_mul (c i) (hc i).isUnit⟩
  have hle : ∀ i, thIdeal em C ≤ p i := by
    intro i
    obtain ⟨t, ht⟩ := hobj i
    exact iInf_le_of_le t (iInf_le_of_le _ (iInf_le_of_le ht le_rfl))
  have hge : Finset.univ.inf p ≤ thIdeal em C := by
    refine le_iInf fun t => le_iInf fun v => le_iInf fun htv => ?_
    obtain ⟨i, z', hz', hth⟩ := hC t htv.1
    have hspan : Ideal.span (Set.range (θ i z')) = ⊤ := by
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t N' ℂ (𝟙 _) (θ i z') ⊥ (by omega)
        dvd_rfl hth Ideal.isPrime_bot 0
      rw [Ideal.mem_bot] at ha
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
    obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b _ _ t ℂ (𝟙 _) (θ i z') v hth htv.2 hspan
    have hv : v = (u : ℂ) • θ i z' := funext fun a => hu a
    intro F hF
    have hF' : F ∈ p ⟨i, z', hz'⟩ := Finset.inf_le (f := p) (Finset.mem_univ _) hF
    rw [RingHom.mem_ker, hv]
    exact hgen ⟨i, z', hz'⟩ F hF' z' hz' u u.ne_zero
  have hp : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨i, -, hi⟩ := hp.inf_le'.mp (hge.trans h𝔭.1.2)
  obtain ⟨t, ht, hth⟩ := hobj i
  refine ⟨t, _, ht, hth, le_antisymm hi ?_⟩
  exact h𝔭.2 ⟨RingHom.ker_isPrime _, hle i⟩ hi

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjOfDescendedData
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaDescent

theorem map_prod_pow {M N : Type*} [Monoid M] [Monoid N] (P : M →* N) {n : ℕ} (p : Fin n → M) (a : Fin n → ℕ) :
    P (List.ofFn fun i => p i ^ a i).prod = (List.ofFn fun i => P (p i) ^ a i).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem existsUnique_transfer {M M₀ N C : Type*} [Monoid M] [Monoid M₀] [Monoid N] (P : M →* N) (R : M₀ →* N)
    (hP : Function.Bijective P) (hR : Function.Injective R) {n : ℕ} (p : Fin n → M) (p₀ : Fin n → M₀)
    (h : ∀ i, P (p i) = R (p₀ i)) (k : ℕ) (e : C → Fin n → ℕ)
    (H : ∀ y : M, y ^ k = 1 → ∃! c : C, (List.ofFn fun i => p i ^ e c i).prod = y)
    (y₀ : M₀) (hy : y₀ ^ k = 1) : ∃! c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ := by
  obtain ⟨y, hyR⟩ := hP.2 (R y₀)
  have hyk : y ^ k = 1 := hP.1 (by rw [map_pow, hyR, ← map_pow, hy, map_one, map_one])
  have key : ∀ c : C, (List.ofFn fun i => p₀ i ^ e c i).prod = y₀ ↔ (List.ofFn fun i => p i ^ e c i).prod = y := by
    intro c
    rw [← hR.eq_iff, ← hP.1.eq_iff, hyR, map_prod_pow, map_prod_pow]
    simp only [h]
  simpa only [key] using H y hyk

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pushHom_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushHom h T x).left = x.left ≫ φ := rfl

theorem pushHom_bijective (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have e := congrArg (fun u => u.left) hxy
    simp only [pushHom_left] at e
    exact Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w x, Over.w y]))
  · refine ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    ext1
    rw [pushHom_left]
    exact h.1.lift_fst _ _ _

theorem preHom_injective {T T' : Over S} (U : T' ⟶ T) [Epi U.left] :
    Function.Injective (preHom (G := G) U) := by
  intro x y hxy
  ext1
  rw [← cancel_epi U.left, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun u => u.left) hxy

theorem weilIs_congr {Z : Scheme.{0}} {s s' : Z ⟶ S} (e : s = s') (L : LB G.left) (k : ℤ)
    (x y : Over.mk s ⟶ G) (x' y' : Over.mk s' ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(Z, ⊤)ˣ) : Out.WeilIs G L k x y c ↔ Out.WeilIs G L k x' y' c := by
  subst e
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

theorem unitS_spMap {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (n : ℤ) :
    unitS (spMap β) u ^ n = unitOn (Units.map β.toMonoidHom u ^ n) := by
  unfold unitS unitOn
  simp only [← map_zpow]
  ext1
  simp only [Units.coe_map]
  exact (congrArg (fun g => CommRingCat.Hom.hom g ((u ^ n : oˣ) : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) : Epi (spMap j) := by
  have := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K Ω j).1 (Sp K) (Sp Ω) (𝟙 _) (𝟙 _) (spMap j)
    (IsPullback.of_vert_isIso ⟨by simp⟩)
  exact this.1

end GlobalTheory.ThetaDescent

namespace GlobalTheory

open ThetaDescent

theorem exists_thetaObj_of_descended_data : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i) := by
  intro o _ g k J b K₀ K _ _ i β₀ β t A₀ _ φ L₀ pt₀ act₀ hβ hpb hL₀ hLiso hpt hact
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ t.A φ hpb t.ab
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i A₀ t.A φ L₀ t.L hab hpb hL₀ t.isLB hLiso t.ample
  have hmon := (GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).2
  refine ⟨{ A := A₀, ab := hab, dim := hdim g t.dim, L := L₀, isLB := hL₀
            rigid := hrig t.rigid, sym := hsym (TObj.sym t), ample := hamp, ktriv := hkt t.ktriv
            pt := pt₀, torsion := ?_, bij := ?_, pairing := ?_, act := act₀
            hom := fun j => (hmon A₀ A₀ t.A t.A φ φ (act₀ j) (t.act j) hpb hpb (hact j).symm).1 (t.hom j) },
    φ, hpb, hLiso, hpt, hact⟩
  ·
    intro a
    obtain ⟨U0, hU0⟩ : ∃ U0 : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀),
        U0.left = spMap i := ⟨Over.homMk (spMap i) (by simp), rfl⟩
    have hE : Epi U0.left := by rw [hU0]; exact epi_spMap i
    apply preHom_injective U0
    have e1 : preHom U0 (pt₀ a) = pushHom hpb _ (t.pt a) := by
      ext1
      show (U0 ≫ pt₀ a).left = _
      rw [Over.comp_left, hU0, pushHom_left, hpt a]
    rw [map_pow, map_one, e1, ← map_pow, t.torsion a, map_one]
  ·
    intro K' _ _ x y hy
    obtain ⟨χ, rfl⟩ : ∃ χ : K₀ →+* K', spMap χ = x := ⟨(Spec.preimage x).hom, by
      show Spec.map (CommRingCat.ofHom _) = x
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    obtain ⟨Ω, _, _, jK, jL, hcomm⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (jK : K →+* Ω) (jL : K' →+* Ω),
        jK.comp i = jL.comp χ := by
      let _ : Algebra K₀ K := i.toAlgebra
      let _ : Algebra K₀ K' := χ.toAlgebra
      have : Nontrivial (K ⊗[K₀] K') :=
        Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective χ.injective
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
      let _ := Ideal.Quotient.field m
      refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom,
        ((algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)).comp
          (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom, ?_⟩
      ext r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have h1 := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes r
      have h2 := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes r
      exact congrArg (fun z => algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))
        (Ideal.Quotient.mk m z)) (h1.trans h2.symm)
    have hw : spMap jL ≫ spMap χ = spMap jK ≫ spMap i := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
    have hE : Epi (Over.Hom.left (Over.homMk (spMap jL) hw :
        Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ))) := epi_spMap jL
    refine existsUnique_transfer (pushHom hpb (Over.mk (spMap jK)))
      (preHom (G := A₀) (Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)))
      (pushHom_bijective hpb _) (preHom_injective _)
      (fun a => (Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a)
      (fun a => (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a)
      ?_ k (fun (c : Ix g k) a => (c a).val) (fun z hz => t.bij Ω (spMap jK) z hz) y hy
    intro a
    ext1
    rw [pushHom_left]
    show ((Over.homMk (spMap jK) (by simp) : Over.mk (spMap jK) ⟶ Out.baseOver (Sp K)) ≫ t.pt a).left ≫ φ = ((Over.homMk (spMap jL) hw : Over.mk (spMap jK ≫ spMap i) ⟶ Over.mk (spMap χ)) ≫
      (Over.homMk (spMap χ) (by simp) : Over.mk (spMap χ) ⟶ Out.baseOver (Sp K₀)) ≫ pt₀ a).left
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [hpt a, ← Category.assoc, ← Category.assoc, hw]
  ·
    intro a a'
    subst hβ
    have := t.ab.comm
    have h1 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp K₀) (Sp K) A₀ t.A (spMap i) φ L₀ t.L hL₀ t.isLB hpb hLiso
      (Out.baseOver (Sp K)) (k : ℤ) (t.pt a) (t.pt a') (pushHom hpb _ (t.pt a)) (pushHom hpb _ (t.pt a')) _
      (pushHom_left hpb _ _) (pushHom_left hpb _ _)).1 (t.pairing a a')
    have e1 : unitS (spMap (i.comp β₀)) b.ζ ^ (Out.stdSymp g a a') =
        unitOn (Units.map i.toMonoidHom (Units.map β₀.toMonoidHom b.ζ ^ (Out.stdSymp g a a'))) := by
      rw [unitS_spMap, map_zpow]
      rfl
    rw [e1] at h1
    have hxa : ∀ c, (pushHom hpb (Out.baseOver (Sp K)) (t.pt c)).left =
        ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K₀)) ⟶ Over.mk (𝟙 (Sp K₀))) ≫ pt₀ c).left := by
      intro c
      rw [pushHom_left, hpt c]
      rfl
    have h2 := (weilIs_congr (s' := spMap i ≫ 𝟙 (Sp K₀)) (by simp) L₀ (k : ℤ) _ _ _ _ (hxa a) (hxa a') _).1 h1
    have h3 := (GlobalTheory.T.weilPairing_fieldExtension_iff (Sp K₀) A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a')
      (Units.map β₀.toMonoidHom b.ζ ^ Out.stdSymp g a a') hab hL₀).1 h2
    rw [unitS_spMap]
    exact h3

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_of_covering_pullbacks : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  first | exact @GlobalTheory.FullDescent.fullObj_of_cover | exact GlobalTheory.FullDescent.fullObj_of_cover | (intros; apply GlobalTheory.FullDescent.fullObj_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFullStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_pullback_exists_and_full : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  first | exact @GlobalTheory.fullObj_pull | exact GlobalTheory.fullObj_pull | (intros; apply GlobalTheory.fullObj_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.hasTheta_of_cover | exact GlobalTheory.ThetaLocal.hasTheta_of_cover | (intros; apply GlobalTheory.ThetaLocal.hasTheta_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFrames_disjointUnionCechData : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_sumLB | exact GlobalTheory.ModelSum.hasFrames_sumLB | (intros; apply GlobalTheory.ModelSum.hasFrames_sumLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoinStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ), 1 ≤ n' → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z)) → HasFrames G L N A n r s → HasFrames G L N A n' r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | exact GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | (intros; apply GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforwardStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁] [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB → AmpleFam A₁ → AmpleFam A₂ → (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  first | exact @GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | exact GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | (intros; apply GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective : ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ Sp R) (G : Over S) (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom → IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → IsProjOver B.hom := by
  first | exact @GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | exact GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | (intros; apply GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_completeDVR_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | exact GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | (intros; apply GlobalTheory.ValuativeGeneric.isProper_of_lift_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_of_isCompl_openImmersions : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ → IsCompl (Set.range f₁) (Set.range f₂) → IsQProjOver (f₁ ≫ s) → IsQProjOver (f₂ ≫ s) → IsQProjOver s := by
  first | exact @GlobalTheory.ProjSpace.isQProjOver_of_isCompl | exact GlobalTheory.ProjSpace.isQProjOver_of_isCompl | (intros; apply GlobalTheory.ProjSpace.isQProjOver_of_isCompl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfRelAmpleRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.InhabZOn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.Models.InhabZOn.exists_dim_triple {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
    [ConnectedSpace S] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H S) : ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyIntegral t.G.hom :=
    _root_.GlobalTheory.geometricallyIntegral_of_isSemiAbelian (h := t.semi) _
  let e : S ⟶ t.G.left := (η[t.G]).left
  have he : e ≫ t.G.hom = 𝟙 S := Over.w (η[t.G])
  have hes : ∀ s, t.G.hom (e s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfib : ∀ s : S, _root_.IsPreconnected (t.G.hom ⁻¹' {s}) := fun s => by
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  have hsec : _root_.IsPreconnected (Set.range e) :=
    isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  haveI : PreconnectedSpace t.G.left := by
    refine ⟨isPreconnected_of_forall (e s₀) fun x _ => ?_⟩
    refine ⟨Set.range e ∪ t.G.hom ⁻¹' {t.G.hom x}, Set.subset_univ _, Or.inl ⟨s₀, rfl⟩,
      Or.inr rfl, ?_⟩
    exact hsec.union (e (t.G.hom x)) ⟨_, rfl⟩ (hes _) (hfib _)
  exact _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected t.G.hom (e s₀)

end GlobalTheory.Models.InhabZOn

end
end


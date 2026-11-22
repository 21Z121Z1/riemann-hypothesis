import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.WeilDeligne GlobalTheory.Pst
open GlobalTheory.BKReal IsLocalRing Formalism.BasicNotions.Examples₂.LB

namespace GlobalTheory.AinfK

theorem fK_eq_resDeg {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w)
    (hj : Induces Bw) : fK Bw.Kw = resDeg l w := by
  have hN := normV_eq_pow (hj.mem_placesOver h)
  refine Nat.pow_right_injective hl.out.two_le (le_antisymm ?_ ?_)
  · obtain ⟨-, ω, hω, -⟩ := exists_gen l (fK Bw.Kw)
    have h1 := one_lt_pow_l l (fK Bw.Kw)
    have hm : ω ∈ K0 Bw.Kw := Kunr_fK Bw.Kw ▸ IntermediateField.subset_adjoin _ _ (show ω ^ l ^ fK Bw.Kw = ω by
      rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
    have h2 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_of_deg (by simp)) ⟨ω, hm.2⟩
    rw [mul_one, mul_zero, pow_zero, frobUr_pow_root _ _ (l ^ fK Bw.Kw - 1) (by omega)
      (fun hd => hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd))
      (Subtype.ext hω.pow_eq_one)] at h2
    have h3 : ω = ω ^ l ^ resDeg l w :=
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (weilToGK Bw h (frob h)).2 _ hm.1).symm.trans h2
    have h4 := one_lt_normV w
    rw [hN] at h4
    have h5 : ω ^ (l ^ resDeg l w - 1) = 1 := mul_right_cancel₀ (hω.ne_zero (by omega)) (by
      rw [← pow_succ, Nat.sub_add_cancel h4.le, one_mul, ← h3])
    have := Nat.le_of_dvd (by omega) (hω.dvd_of_pow_eq_one _ h5)
    change l ^ _ ≤ l ^ _
    omega
  · change l ^ _ ≤ l ^ _
    rw [← hN, ← card_res]
    let u : 𝓞 E →+* ↥Bw.Kw.1 :=
      (Bw.j.comp ((algebraMap E Ω).comp (algebraMap (𝓞 E) E))).codRestrict Bw.Kw.1 fun x => Bw.j_E _
    let v : 𝓞 E →+* ↥(OL Bw.Kw) := u.codRestrict (OL Bw.Kw) fun x =>
      (map_isIntegral_int u (RingOfIntegers.isIntegral x)).tower_top
    have hk : ∀ x, ((residue _).comp v) x = 0 ↔ x ∈ w.asIdeal := fun x => by
      rw [RingHom.comp_apply, residue_eq_zero_iff, mem_max, ← h x, hj.valuation_lt_one_iff]
      rfl
    have := OL_resFinite Bw.Kw
    exact Nat.card_le_card_of_injective (Ideal.Quotient.lift w.asIdeal _ fun x hx => (hk x).2 hx)
      (RingHom.lift_injective_of_ker_le_ideal _ _ fun x hx => (hk x).1 hx)

end GlobalTheory.AinfK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesOfSeparableCharPoly
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.ClFin

variable {K : UQ} (B : InvAlg K)

def sigU : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)

theorem sigU_val (u : B.Aˣ) : ((sigU B u : B.Aˣ) : B.A) = B.σ u := rfl

def fixG : Subgroup B.Aˣ where
  carrier := {x | B.σ (x : B.A) = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = 1 := by
      calc B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = B.σ ((a⁻¹ : B.Aˣ) : B.A) * B.σ (a : B.A) := by
            rw [ha]
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * ((a⁻¹ : B.Aˣ) : B.A)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((a⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, h, one_mul]

def normHom : B.Aˣ →* fixG B where
  toFun u := ⟨u * sigU B u, by
    show B.σ ((u : B.A) * B.σ u) = (u : B.A) * B.σ u
    rw [map_mul, B.σ_σ, mul_comm]⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp [sigU_val]
  map_mul' := by
    intro a b
    apply Subtype.ext; apply Units.ext
    simp only [Units.val_mul, sigU_val, map_mul, Subgroup.coe_mul]
    ring

theorem finite_quot (hsq : Finite (B.Aˣ ⧸ (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range))
    (hmu : Set.Finite {x : B.A | x ^ 2 = 1}) : Finite (fixG B ⧸ (normHom B).range) := by
  set Sq := (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range
  set φ : fixG B →* B.Aˣ ⧸ Sq := (QuotientGroup.mk' Sq).comp (fixG B).subtype
  haveI : Finite (fixG B ⧸ φ.ker) := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  set M := {x : fixG B | ((x : B.Aˣ) : B.A) ^ 2 = 1}
  haveI : Finite M := by
    have : Finite {x : B.A | x ^ 2 = 1} := hmu.to_subtype
    refine Finite.of_injective (fun x : M => (⟨((x.1 : B.Aˣ) : B.A), x.2⟩ : {x : B.A | x ^ 2 = 1})) ?_
    intro a b h
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact congrArg Subtype.val h
  let g : (fixG B ⧸ φ.ker) × M → fixG B ⧸ (normHom B).range :=
    fun p => QuotientGroup.mk (Quotient.out p.1 * p.2.1)
  refine Finite.of_surjective g ?_
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set x₀ : fixG B := Quotient.out (QuotientGroup.mk x : fixG B ⧸ φ.ker)
  have hx₀ : x₀⁻¹ * x ∈ φ.ker := by
    have : (QuotientGroup.mk x₀ : fixG B ⧸ φ.ker) = QuotientGroup.mk x := Quotient.out_eq' _
    exact QuotientGroup.eq.mp this
  rw [MonoidHom.mem_ker] at hx₀
  simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx₀
  obtain ⟨y, hy⟩ := hx₀
  rw [powMonoidHom_apply] at hy

  have hfix : B.σ ((y : B.A) ^ 2) = (y : B.A) ^ 2 := by
    have := (x₀⁻¹ * x).2
    rw [← Units.val_pow_eq_pow_val, hy]
    exact this
  set ε : B.Aˣ := y * (sigU B y)⁻¹
  have hε2 : (ε : B.A) ^ 2 = 1 := by
    have h1 : ((sigU B y : B.Aˣ) : B.A) ^ 2 = (y : B.A) ^ 2 := by rw [sigU_val, ← map_pow, hfix]
    have h1' : (sigU B y) ^ 2 = y ^ 2 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h1])
    have h2 : ((sigU B y)⁻¹ : B.Aˣ) ^ 2 = (y ^ 2)⁻¹ := by rw [inv_pow, h1']
    rw [← Units.val_pow_eq_pow_val]
    simp only [ε, mul_pow, h2, mul_inv_cancel, Units.val_one]
  have hεfix : B.σ (ε : B.A) = ε := by

    have hσ : B.σ (ε : B.A) * (ε : B.A) = 1 := by
      have hyinv : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
        have : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
          calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A)
              = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * B.σ (B.σ (y : B.A)) := by rw [B.σ_σ]
            _ = 1 := by rw [← map_mul, ← sigU_val, Units.inv_mul, map_one]
        calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A)
            = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by
              rw [Units.mul_inv, mul_one]
          _ = ((y⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, this, one_mul]
      simp only [ε, Units.val_mul, map_mul, hyinv]
      calc B.σ (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A))
          = (((sigU B y) : B.Aˣ) : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A) *
              ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by rw [sigU_val]; ring
        _ = 1 := by rw [Units.mul_inv, Units.mul_inv, one_mul]
    calc B.σ (ε : B.A) = B.σ (ε : B.A) * ((ε : B.A) * (ε : B.A)) := by rw [← sq, hε2, mul_one]
      _ = ε := by rw [← mul_assoc, hσ, one_mul]
  let εG : fixG B := ⟨ε, hεfix⟩
  refine ⟨(QuotientGroup.mk x, ⟨εG, hε2⟩), ?_⟩
  show QuotientGroup.mk (x₀ * εG) = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  refine ⟨y, ?_⟩
  apply Subtype.ext; apply Units.ext

  have hxy : ((x : fixG B) : B.Aˣ) = (x₀ : B.Aˣ) * y ^ 2 := by
    rw [hy]; simp
  show ((y : B.A) * B.σ (y : B.A)) = (((x₀ * εG)⁻¹ * x : fixG B) : B.Aˣ).val
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxy, εG, ε]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, sigU_val]
  have : ((x₀ : B.Aˣ)⁻¹ : B.Aˣ).val * (x₀ : B.Aˣ).val = 1 := Units.inv_mul _
  have hy1 : (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv y
  rw [sq]
  linear_combination (-(B.σ (y : B.A) * (y : B.A))) * hy1 +
    (-(B.σ (y : B.A) * (y : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A))) * this

def toCl : fixG B ⧸ (normHom B).range → B.Cl :=
  Quotient.lift (fun x : fixG B => (Quot.mk _ ⟨(x : B.Aˣ), x.2⟩ : B.Cl)) (by
    intro a b hab
    have h := QuotientGroup.leftRel_apply.mp hab
    obtain ⟨u, hu⟩ := h
    apply Quot.sound
    refine ⟨u, ?_⟩
    have hb : (b : B.Aˣ) = (a : B.Aˣ) * ((normHom B u : fixG B) : B.Aˣ) := by
      rw [hu]; simp
    show ((b : B.Aˣ) : B.A) = ((a : B.Aˣ) : B.A) * ((u : B.A) * B.σ (u : B.A))
    rw [hb, Units.val_mul]
    rfl)

theorem toCl_surjective : Function.Surjective (toCl B) := by
  intro k
  induction k using Quot.ind with
  | mk x => exact ⟨QuotientGroup.mk ⟨x.1, x.2⟩, rfl⟩

theorem finite_Cl (K : UQ) (B : InvAlg K) : Finite B.Cl := by
  have hsq := GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields K.E (GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic K) B.A
  have hmu := GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero K.E B.A
  haveI := finite_quot B hsq hmu
  exact Finite.of_surjective _ (toCl_surjective B)

theorem finite_Cl_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl :=
  fun K B _ => finite_Cl K B

end GlobalTheory.UnitLemma.ClFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthInvariantsNegTwistKmodO
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.FinInvKO

theorem isFiniteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem length_lt_top_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : Submodule O (KmodO O)) {c : O} (hc : c ≠ 0) (h : ∀ x ∈ S, c • x = 0) :
    Module.length O S < ⊤ := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (FractionRing O)).ne hc
  let x₀ : KmodO O := Submodule.Quotient.mk ((algebraMap O (FractionRing O) c)⁻¹)
  let ψ : O →ₗ[O] KmodO O := LinearMap.toSpanSingleton O _ x₀
  have hS : S ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := h _ hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : algebraMap O (FractionRing O) a = algebraMap O (FractionRing O) c * y := by
      rw [← Algebra.smul_def]; exact ha
    refine ⟨a, ?_⟩
    simp only [ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ha', mul_comm (algebraMap O (FractionRing O) c) y, mul_assoc,
      mul_inv_cancel₀ hc', mul_one]
  have hk : ∀ z : LinearMap.range ψ, c • z = 0 := by
    rintro ⟨_, a, rfl⟩
    ext1
    simp only [SetLike.val_smul, ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul,
      smul_smul, Submodule.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, mul_comm (algebraMap O (FractionRing O) c), mul_assoc, mul_inv_cancel₀ hc', mul_one]
  have hfl := isFiniteLength_of_killed hc hk
  exact lt_of_le_of_lt (Module.length_le_of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS))
    (lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 hfl))

theorem finiteLength_invariants_negTwist_KmodO : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants
      ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤ := by
  intro D i w hw e he
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := hgI.1
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  haveI : CharZero (FractionRing (D.nd.O i)) :=
    (D.nd.embK i).charZero_iff (D.nd.embK i).injective |>.1 inferInstance
  haveI : CharZero (D.nd.O i) := (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).charZero
  have hle : 1 ≤ (1 + D.nd.l i ^ D.nd.s0 i) ^ e := Nat.one_le_pow _ _ (by omega)
  have hlt : 1 < (1 + D.nd.l i ^ D.nd.s0 i) ^ e :=
    Nat.one_lt_pow he.ne' (by have := pow_pos hp.pos (D.nd.s0 i); omega)
  have hc : (((1 + D.nd.l i ^ D.nd.s0 i) ^ e - 1 : ℕ) : D.nd.O i) ≠ 0 :=
    Nat.cast_ne_zero.2 (by omega)
  refine length_lt_top_of_killed _ hc fun v hv => ?_
  have h1 := hv ⟨g, hgD⟩
  change ((((Glob.epsO D.nd i) ^ (-(e : ℤ))) g : (D.nd.O i)ˣ) : D.nd.O i) • v = v at h1
  have hu : ((Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) = 1 + (D.nd.l i : D.nd.O i) ^ D.nd.s0 i := by
    simp [Glob.epsO, hg]
  have h2 : (((Glob.epsO D.nd i g) ^ e : (D.nd.O i)ˣ) : D.nd.O i) • v = v := by
    conv_lhs => rw [← h1]
    rw [smul_smul, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  rw [Nat.cast_sub hle, Nat.cast_one, sub_smul, one_smul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h2, sub_self]

end GlobalTheory.FinInvKO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanVecSLe
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

section VecGen
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (a n : ℕ)

def vecS : (Fin a → Fin n → K) →ₛₗ[φ] (Fin a → Fin n → L) where
  toFun v := fun b j => φ (v b j)
  map_add' u v := by funext b j; simp
  map_smul' c v := by funext b j; simp

variable {φ a n}

theorem vecS_apply (v : Fin a → Fin n → K) (b : Fin a) (j : Fin n) : vecS φ a n v b j = φ (v b j) := rfl

theorem span_vecS_span (S : Set (Fin a → Fin n → K)) :
    Submodule.span L (vecS φ a n '' (Submodule.span K S : Set (Fin a → Fin n → K))) =
      Submodule.span L (vecS φ a n '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem finrank_span_vecS_le (W : Submodule K (Fin a → Fin n → K)) :
    finrank L (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))) ≤ finrank K W := by
  let b := Module.finBasis K W
  let g : Fin (Module.finrank K W) → (Fin a → Fin n → L) := fun i => vecS φ a n (b i)
  have hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K) := by
      have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
      rw [map_sum] at this
      exact this.symm
    rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W := by
    have := finrank_range_le_card (R := L) g
    simpa [Set.finrank] using this
  exact h1.trans h2

theorem span_vecS_top : Submodule.span L (Set.range (vecS φ a n)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0) := by
    funext b' j'
    simp only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite,
      mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem isCompl_span_vecS {W W' : Submodule K (Fin a → Fin n → K)} (h : IsCompl W W') :
    IsCompl (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))))
      (Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))) := by
  set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))
  set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))
  have h1 : finrank L A ≤ finrank K W := finrank_span_vecS_le W
  have h2 : finrank L B ≤ finrank K W' := finrank_span_vecS_le W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top] at h4
  have hK : finrank K (Fin a → Fin n → K) = a * n := by
    rw [Module.finrank_pi_fintype]; simp [Module.finrank_fin_fun]
  have hL : finrank L (Fin a → Fin n → L) = a * n := by
    rw [Module.finrank_pi_fintype]; simp [Module.finrank_fin_fun]
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; omega
  exact ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩

end VecGen

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isSummandTw_XG : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y),
    (∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧
    IsCompl (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))) C) →
    IsSummandTw i w hw r Xs (XG i w hw r Xs hr x Y hst) := by
  intro D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩
  have hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV ''
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i))) := by
    rw [span_vecS_span]; rfl
  refine ⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl,
    Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩
  · intro g u hu
    have hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap
          ((sumG i w hw r Xs hr x).ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈
        Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))
      rw [sumG_vecL]
      exact Submodule.subset_span ⟨_, hC _ v hv, rfl⟩
    exact hle hu
  · have key : IsCompl (spanL i w hw Y)
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))) := by
      rw [hspan]
      exact isCompl_span_vecS hYC
    convert key using 1
    exact Submodule.range_subtype _

end GlobalTheory.Pass.LocDual.OneX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRingsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_bounds_crystalline_deRham_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  first | exact @GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | exact GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | (intros; apply GlobalTheory.Per.FontaineTied.fontCore_all_of_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem fontaine_litFont_assembled :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.InvariantsGenerators.LitFont
  intro l _ K LL hA
  unfold Formalism.MainNotions.InvariantsGenerators.FontCore
  have hff := GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2
  have hex := GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2
  have hpd := GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2
  have hpe := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2
  have hfr := GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨hff, hex, ?_, hpd⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hpe
  refine ⟨ψ, h1, h2, ?_, ?_⟩
  · rw [hp]; exact h3
  · intro x
    obtain ⟨c, hc, -⟩ := hfr x
    rw [hp]
    exact ⟨c, hc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  first | exact @GlobalTheory.BK.Hom.frob_mem_ldivSet_target | exact GlobalTheory.BK.Hom.frob_mem_ldivSet_target | (intros; apply GlobalTheory.BK.Hom.frob_mem_ldivSet_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEisensteinMemPrimeMulDividedPowerSeriesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∃ B ∈ SdSet t K e, inclS t K (frobS l a (eis l a e)) = (l : ZMod a → K⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.frobS_eis_mem | exact GlobalTheory.CrysPrism.frobS_eis_mem | (intros; apply GlobalTheory.CrysPrism.frobS_eis_mem <;> assumption)
end


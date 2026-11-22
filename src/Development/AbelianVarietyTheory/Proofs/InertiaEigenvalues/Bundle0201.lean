import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfSmulEqZero
section
noncomputable section

namespace GlobalTheory.AdmLoc

open Formalism.WeaklyAdmissibleFiltrations
open scoped Pointwise

section Sub

variable {O G : Type} [CommRing O] [Group G] {M : Type} [AddCommGroup M] [Module O M]

def IsStab (π : Representation O G M) (X : Submodule O M) : Prop := ∀ g, ∀ x ∈ X, π g x ∈ X

variable {π : Representation O G M}

theorem IsStab.smul {X : Submodule O M} (h : IsStab π X) (c : O) : IsStab π (c • X) := by
  intro g x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x c X).mp hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h g y hy)

theorem IsStab.sup {X Y : Submodule O M} (h : IsStab π X) (h' : IsStab π Y) : IsStab π (X ⊔ Y) := by
  intro g x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (h g y hy) (h' g z hz)

def subquotRep {X Y : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) :
    Representation O G (↥Y ⧸ X.comap Y.subtype) :=
  (π.subrepresentation Y hY).quotient (X.comap Y.subtype) (fun g x hx => hX g x hx)

theorem subquot_sameSS_prod {X Y Z : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) (hZ : IsStab π Z)
    (hXY : X ≤ Y) (hYZ : Y ≤ Z) (h : IsFiniteLength O (↥Z ⧸ X.comap Z.subtype)) :
    SameSS (subquotRep hX hZ) ((subquotRep hX hY).prod (subquotRep hY hZ)) := by
  refine SameSS.of_exact
    (f := Submodule.mapQ _ _ (Submodule.inclusion hYZ) (fun _ hx => hx))
    (p := Submodule.mapQ _ _ LinearMap.id (fun _ hx => hXY hx)) ?_ ?_ ?_ ?_ ?_ h
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.inclusion hYZ x ∈ X.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr h1
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      have h1 : x ∈ Y.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
      exact ⟨Submodule.Quotient.mk ⟨x, h1⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero (Y.comap Z.subtype) (x := Submodule.inclusion hYZ y)).mpr y.2

def smulEquiv {c : O} (hc : IsSMulRegular M c) (Y : Submodule O M) : ↥Y ≃ₗ[O] ↥(c • Y) :=
  Submodule.equivMapOfInjective (DistribSMul.toLinearMap O M c) hc Y

theorem subquot_sameSS_smul {c : O} (hc : IsSMulRegular M c) {X Y : Submodule O M} (hX : IsStab π X)
    (hY : IsStab π Y) (h : IsFiniteLength O (↥Y ⧸ X.comap Y.subtype)) :
    SameSS (subquotRep hX hY) (subquotRep (hX.smul c) (hY.smul c)) := by
  refine SameSS.of_equiv h (Submodule.Quotient.equiv _ _ (smulEquiv hc Y) ?_) ?_
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx
    · intro hz
      obtain ⟨y, rfl⟩ := (smulEquiv hc Y).surjective z
      obtain ⟨x, hx, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c X).mp hz
      have hxy' : x = (y : M) := hc hxy
      exact ⟨y, (hxy' ▸ hx : (y : M) ∈ X), rfl⟩
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (map_smul (π g) c (x : M)).symm

theorem SameSS.prod_comm {A C : Type} [AddCommGroup A] [Module O A] [AddCommGroup C] [Module O C]
    (α : Representation O G A) (γ : Representation O G C) (hA : IsFiniteLength O A) (hC : IsFiniteLength O C) :
    SameSS (α.prod γ) (γ.prod α) :=
  ((SameSS.refl α hA).prod (SameSS.refl γ hC)).congr_right (LinearEquiv.prodComm O A C) (fun _ _ => rfl)

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem finiteLength_of_smul_eq_zero {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] {c : O}
    (hc : c ≠ 0) (h : ∀ x : N, c • x = 0) : IsFiniteLength O N := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O N (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) N := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) N := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem finiteLength_subquot {c : O} (hc : c ≠ 0) {X Y : Submodule O M} (hY : Y.FG) (h : c • Y ≤ X) :
    IsFiniteLength O (↥Y ⧸ X.comap Y.subtype) := by
  haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hY
  refine finiteLength_of_smul_eq_zero hc fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h (Submodule.smul_mem_pointwise_smul _ _ _ x.2)

theorem fg_smul {Y : Submodule O M} (hY : Y.FG) (c : O) : (c • Y).FG := hY.map _

theorem red_sameSS_step {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M} (hA : IsStab π A)
    (hB : IsStab π B) (fA : A.FG) (fB : B.FG) (h1 : c • A ≤ B) (h2 : B ≤ A) :
    SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have h3 : c • B ≤ c • A := Submodule.map_mono h2
  have e1 := subquot_sameSS_prod (hA.smul c) hB hA h1 h2 (finiteLength_subquot hc0 fA le_rfl)
  have e2 := subquot_sameSS_prod (hB.smul c) (hA.smul c) hB h3 h1 (finiteLength_subquot hc0 fB le_rfl)
  have l1 := finiteLength_subquot hc0 fB h3
  have l2 := finiteLength_subquot hc0 fA h1
  have e3 := subquot_sameSS_smul hc hB hA l2
  exact (e1.trans (SameSS.prod_comm _ _ l1 l2)).trans ((e3.prod (SameSS.refl _ l1)).trans e2.symm)

theorem red_sameSS_of_pow {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {B : Submodule O M} (hB : IsStab π B)
    (fB : B.FG) (n : ℕ) : ∀ {A : Submodule O M} (hA : IsStab π A), A.FG → c ^ n • A ≤ B → B ≤ A →
      SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  induction n with
  | zero =>
    intro A hA fA h1 h2
    rw [pow_zero, one_smul] at h1
    obtain rfl : A = B := le_antisymm h1 h2
    exact SameSS.refl _ (finiteLength_subquot hc0 fA le_rfl)
  | succ n ih =>
    intro A hA fA h1 h2
    have fA' : (B ⊔ c • A).FG := fB.sup (fg_smul fA c)
    refine (red_sameSS_step hc0 hc hA (hB.sup (hA.smul c)) fA fA' le_sup_right
      (sup_le h2 (Submodule.smul_le_self_of_tower c A))).trans (ih _ fA' ?_ le_sup_left)
    rw [Submodule.smul_sup', smul_smul, ← pow_succ]
    exact sup_le (Submodule.smul_le_self_of_tower _ B) h1

theorem red_sameSS_of_commensurable {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M}
    (hA : IsStab π A) (hB : IsStab π B) (fA : A.FG) (fB : B.FG) {m n : ℕ} (h1 : c ^ m • A ≤ B)
    (h2 : c ^ n • B ≤ A) : SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have fS : (A ⊔ B).FG := fA.sup fB
  refine (red_sameSS_of_pow hc0 hc hA fA n (hA.sup hB) fS ?_ le_sup_left).symm.trans
    (red_sameSS_of_pow hc0 hc hB fB m (hA.sup hB) fS ?_ le_sup_right)
  · rw [Submodule.smul_sup']
    exact sup_le (Submodule.smul_le_self_of_tower _ A) h2
  · rw [Submodule.smul_sup']
    exact sup_le h1 (Submodule.smul_le_self_of_tower _ B)

end Sub

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

def resScal (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) : Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

variable {ρ : Representation LL G V}

theorem isStab_lattice (L : Lattice (O := O) ρ) : IsStab (resScal O ρ) L.T := L.stable

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem modRep_sameSS_subquot (L : Lattice (O := O) ρ) {c : O} (hc : c ≠ 0) :
    SameSS (subquotRep ((isStab_lattice L).smul c) (isStab_lattice L)) (modRep (latRep L) c) := by
  refine SameSS.of_equiv (finiteLength_subquot hc L.fg le_rfl) (Submodule.quotEquivOfEq _ _ ?_) ?_
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c L.T).mp hx
      exact (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mpr ⟨⟨y, hy⟩, trivial, Subtype.ext hxy⟩
    · intro hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mp hx
      exact Submodule.smul_mem_pointwise_smul _ _ _ y.2
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

variable [IsFractionRing O LL]

theorem exists_pow_smul_mem (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) (v : V) :
    ∃ n : ℕ, lam ^ n • v ∈ L.T := by
  have hv : v ∈ Submodule.span LL (L.T : Set V) := by rw [L.span]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) v hv
  rw [Submodule.span_eq] at hs
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero s.2) hlam
  refine ⟨n, ?_⟩
  have h := L.T.smul_mem ((u⁻¹ : Oˣ) : O) hs
  rwa [Submonoid.smul_def, smul_smul, hu, Units.inv_mul_cancel_left] at h

theorem exists_pow_smul_le (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) {A : Submodule O V}
    (hA : A.FG) : ∃ n : ℕ, lam ^ n • A ≤ L.T := by
  induction A, hA using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := exists_pow_smul_mem L hlam x
    refine ⟨n, ?_⟩
    rw [Submodule.smul_span, Set.smul_set_singleton, Submodule.span_singleton_le_iff_mem]
    exact hn
  | sup A B _ _ hA hB =>
    obtain ⟨m, hm⟩ := hA
    obtain ⟨n, hn⟩ := hB
    refine ⟨m + n, ?_⟩
    rw [Submodule.smul_sup']
    refine sup_le ?_ ?_
    · rw [pow_add, mul_comm, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hm
    · rw [pow_add, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hn

theorem lattice_reduction_sameSS {lam : O} (hlam : Irreducible lam) (L L' : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) := by
  have h0 : lam ≠ 0 := hlam.ne_zero
  have hreg : IsSMulRegular V lam := by
    intro x y hxy
    have h1 : algebraMap O LL lam ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr h0
    have h2 : algebraMap O LL lam • x = algebraMap O LL lam • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V h1 h2
  obtain ⟨m, hm⟩ := exists_pow_smul_le L' hlam L.fg
  obtain ⟨n, hn⟩ := exists_pow_smul_le L hlam L'.fg
  exact ((modRep_sameSS_subquot L h0).symm.trans
    (red_sameSS_of_commensurable h0 hreg (isStab_lattice L) (isStab_lattice L') L.fg L'.fg hm hn)).trans
    (modRep_sameSS_subquot L' h0)

end Lat

end GlobalTheory.AdmLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPseudoCharacterOfApproximatedByTraces
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

noncomputable section

namespace GlobalTheory.PsChar

open MvPolynomial

theorem aeval_eq_zero_of_polyApprox {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type} {θ : J → k}
    {S : Set (J → k)} (h : PolyApprox θ S) (P : MvPolynomial J ℤ) (hP : ∀ η ∈ S, aeval η P = 0) :
    aeval θ P = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨s, c, hs, hb⟩ := h ε hε
  have hz : ∑ η ∈ s, c η * aeval η P = 0 :=
    Finset.sum_eq_zero fun η hη => by rw [hP η (hs hη), mul_zero]
  have := hb P
  rw [hz, sub_zero] at this
  simpa using this

theorem isPsChar_trc {Γ A : Type} [Group Γ] [CommRing A] (a : ℕ) (ρ : Γ →* GL (Fin a) A) : IsPsChar a (trc ρ) :=
  isPsChar_trace Γ A a ((Units.coeHom (Matrix (Fin a) (Fin a) A)).comp ρ)

theorem isPsChar_of_polyApprox_trc : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l)
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  intro l _ Γ _ a T C h
  have key : ∀ P : MvPolynomial Γ ℤ, (∀ ρ ∈ C, aeval (trc ρ) P = 0) → aeval T P = 0 := fun P hP =>
    aeval_eq_zero_of_polyApprox h P (by rintro η ⟨ρ, hρ, rfl⟩; exact hP ρ hρ)
  have hm : ∀ (η : Γ → PadicAlgCl l) (x : Fin (a + 1) → Γ),
      aeval η (alt (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x) = alt η (a + 1) x := fun η x => by
    have := map_alt (aeval η).toRingHom (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have := key (X 1 - (a : MvPolynomial Γ ℤ)) fun ρ _ => by simp [(isPsChar_trc a ρ).one]
    simpa [sub_eq_zero] using this
  · intro x y
    have := key (X (x * y) - X (y * x)) fun ρ _ => by simp [(isPsChar_trc a ρ).comm x y]
    simpa [sub_eq_zero] using this
  · intro x
    have := key _ fun ρ _ => by rw [hm]; exact (isPsChar_trc a ρ).alt_eq_zero x
    rwa [hm] at this

example : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l)
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T :=
  isPsChar_of_polyApprox_trc

end GlobalTheory.PsChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitAndIntegInvOfNormDetEqOne
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

theorem integ_det_le {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {m : ℕ}
    (y : Matrix (Fin m) (Fin m) E) (hy : ∀ i j, ‖y i j‖ ≤ 1) : ‖y.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hy _ _)

theorem isUnit_and_integ_inv_of_norm_det_eq_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ = 1 →
      IsUnit x ∧ ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro E _ _ n x hx hdet
  have hne : x.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hne)
  refine ⟨hu, fun i j => ?_⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hdet, inv_one, one_mul, Matrix.adjugate_apply]
  apply integ_det_le
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hx a b

end GlobalTheory.UnitDiscAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeTwistExactSequenceCohomologyStatement
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_twist_exact_sequence_cohomology : ∀ (G LL O V : Type) [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V) (L : Lattice (O := O) ρ) (χ : G →* Oˣ) (S X Y : Type) [AddCommGroup S] [Module O S] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (i : S →ₗ[O] X) (p : X →ₗ[O] Y), Function.Injective i → Function.Exact i p → Function.Surjective p → (∀ c x, tensCoc L χ X c x ∈ ReciprocityTheory.Def.Z1 (twCoef (latRep L) χ X) ⊤) → (∀ m, IsLocallyConstant fun g => twCoef (latRep L) χ X g m) → (twCoef (latRep L) χ Y).invariants = ⊥ → TensIso L χ S → TensIso L χ Y → TensIso L χ X := by
  first | exact @GlobalTheory.TensIsoExt.tensIso_of_exact | exact GlobalTheory.TensIsoExt.tensIso_of_exact | (intros; apply GlobalTheory.TensIsoExt.tensIso_of_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem linApprox_of_polyApprox_trc : ∀ (k Γ : Type) [NormedField k] [IsUltrametricDist k] [Group Γ] (a : ℕ)
    (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)), PolyApprox (trc r) (trc '' C) → LinApprox r C := by
  intro k Γ _ _ _ a r C h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  let f : (Γ → k) → (Γ →* GL (Fin a) k) := Function.invFunOn trc C
  have hf : ∀ η ∈ s, f η ∈ C ∧ trc (f η) = η := fun η hη =>
    ⟨Function.invFunOn_mem (hs hη), Function.invFunOn_eq (hs hη)⟩
  have hinj : Set.InjOn f (s : Set (Γ → k)) := fun x hx y hy hxy => by
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  refine ⟨s.image f, fun ρ => c (trc ρ), ?_, fun g => ?_⟩
  · intro ρ hρ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact (hf η hη).1
  · have := hP (MvPolynomial.X g)
    simp only [MvPolynomial.aeval_X] at this
    rw [Finset.sum_image hinj]
    have e : ∑ x ∈ s, c (trc (f x)) * trc (f x) g = ∑ η ∈ s, c η * η g :=
      Finset.sum_congr rfl fun η hη => by rw [(hf η hη).2]
    rw [e]
    exact this

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZeroStatement
section
open GlobalTheory.LogU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt : ∀ (n i j : ℕ), i + j < n → MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (GlobalTheory.LogU.logDefect n) = 0 := by
  first | (exact @GlobalTheory.LogU.logDefect_coeff_eq_zero) | (exact GlobalTheory.LogU.logDefect_coeff_eq_zero) | (intros; apply GlobalTheory.LogU.logDefect_coeff_eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapAevalNab
section
noncomputable section
namespace GlobalTheory.Models.EPolyModel
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem map_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a) (g' : Vc k b →ₗ[k] Vc k b)
    (h : ∀ x, φ (g x) = g' (φ x)) (x : Vc k a) : φ (nab g x) = nab g' (φ x) := by
  rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, h]

theorem map_aeval_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (f : Polynomial k) (x : Vc k a) :
    φ (Polynomial.aeval (nab g) f x) = Polynomial.aeval (nab g') f (φ x) := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact φ.map_smul_of_tower c x
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval (nab g')), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, map_nab φ g g' h]

theorem comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ)
    (hN : EPoly g' N s) : EPoly g (N.comap (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, fun x hx => ?_⟩
  have h1 := hN (φ x) hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  change φ _ ∈ N
  rwa [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem map {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k a)) (s : ℤ)
    (hN : EPoly g N s) : EPoly g' (N.map (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hN x hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  refine ⟨_, h1, ?_⟩
  change φ _ = _ • nab g' (Polynomial.aeval (nab g') f (φ x))
  rw [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem model_ePoly : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T3 l →
    ∀ (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i, Dt.ty i = LType.Bd →
      EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h3 A N hN i hi
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have oB := M.base_obj B Nb hB
  have o1 := F.obj_sub A₁ B j hj hji oB
  have oA := F.obj_quot A₁ A p hp hps o1
  exact map _ _ _ (F.map_γ A₁ A p o1 oA hp i) _ _
    (comap _ _ _ (F.map_γ A₁ B j o1 oB hj i) _ _ (M.base_e h1 h3 B Nb hB i hi))

end GlobalTheory.Models.EPolyModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem exact_of_finrank_add {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (h0 : p ∘ₗ f = 0)
    (hd : Module.finrank K V = Module.finrank K U + Module.finrank K W) : Function.Exact f p := by
  rw [LinearMap.exact_iff]
  have hle : LinearMap.range f ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h0, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at hrn
  have hrf := LinearMap.finrank_range_of_inj hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem finrank_add_of_exact {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (he : Function.Exact f p) :
    Module.finrank K V = Module.finrank K U + Module.finrank K W := by
  rw [LinearMap.exact_iff] at he
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [he, LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.finrank_range_of_inj hf] at hrn
  omega

theorem DFun.map_exact_middle {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k))
    (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hB : F.Obj B) (hf : IsHom A B f) (hp : IsHom B C p)
    (hi : Function.Injective f) (hs : Function.Surjective p) (he : Function.Exact f p) (i : ZMod n) :
    Function.Exact (F.map A B f i) (F.map B C p i) := by
  have hA : F.Obj A := F.obj_sub A B f hf hi hB
  have hC : F.Obj C := F.obj_quot B C p hp hs hB
  have hd := finrank_add_of_exact f p hi hs he
  simp only [Module.finrank_fin_fun] at hd
  have hpf : p ∘ₗ f = 0 := LinearMap.ext fun x => he.apply_apply_eq_zero x
  have h0hom : IsHom A C (0 : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) := fun g x => by simp
  have hcomp : F.map B C p i ∘ₗ F.map A B f i = 0 := by
    rw [← F.map_comp A B C f p hA hB hC hf hp i, hpf]
    refine LinearMap.ext fun x => ?_
    have h := F.map_smul A C 0 0 hA hC h0hom i x
    simpa using h
  refine exact_of_finrank_add (F.map A B f i) (F.map B C p i) (F.map_inj A B f hA hB hf hi i)
    (F.map_surj B C p hB hC hp hs i) hcomp ?_
  simp only [Vc, Module.finrank_fin_fun]
  exact hd

end GlobalTheory.Models
end


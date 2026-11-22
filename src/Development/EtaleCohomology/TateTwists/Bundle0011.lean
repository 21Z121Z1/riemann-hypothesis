import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0004
import Development.EtaleCohomology.TateTwists.Bundle0002

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsFlatOfQuotientIso
section
open Polynomial

noncomputable section
set_option linter.unusedSectionVars false

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact sub_eq_zero.1 h

theorem pow_mod_q (ζ : Prim q A) (n : ℕ) : ζ.1 ^ (n % q) = ζ.1 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, prim_pow_q, one_pow, one_mul]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ (1 : ZMod q).val = ζ.1 := by
  rw [ZMod.val_one_eq_one_mod, pow_mod_q, pow_one]

theorem pow_val_mul (ζ : Prim q A) (a b : ZMod q) : ζ.1 ^ (a * b).val = (ζ.1 ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_mod_q, pow_mul]

theorem val_inj [NeZero q] [Nontrivial A] (ζ : Prim q A) (a b : ZMod q) (h : ζ.1 ^ a.val = ζ.1 ^ b.val) : a = b := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have hu := ζ.2.1.map π
    rw [map_natCast] at hu
    exact hu.ne_zero⟩
  have hr : IsRoot (cyclotomic q (A ⧸ m)) (π ζ.1) := by
    have h2 := aeval_algHom_apply π.toIntAlgHom ζ.1 (cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h2
    rw [IsRoot, ← map_cyclotomic q (algebraMap ℤ (A ⧸ m)), eval_map_algebraMap]
    exact h2
  have hp : IsPrimitiveRoot (π ζ.1) q := (isRoot_cyclotomic_iff).1 hr
  have h3 : (π ζ.1) ^ a.val = (π ζ.1) ^ b.val := by rw [← map_pow, ← map_pow, h]
  exact ZMod.val_injective q (hp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h3)

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

def Rel (ζ ξ : Prim q A) : Prop := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

def St : Setoid (Prim q A) where
  r := Rel q A
  iseqv := by
    refine ⟨fun ζ => ⟨1, by rw [Units.val_one, pow_val_one]⟩, ?_, ?_⟩
    · rintro ζ ξ ⟨a, h⟩
      refine ⟨a⁻¹, ?_⟩
      rw [h, ← pow_val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, pow_val_one]
    · rintro ζ ξ η ⟨a, h⟩ ⟨b, h'⟩
      exact ⟨a * b, by rw [h', h, Units.val_mul, pow_val_mul]⟩

variable {q A}

def rep (ξ : Prim q A) : Prim q A := (Quotient.mk (St q A) ξ).out

theorem rep_rel (ξ : Prim q A) : Rel q A (rep ξ) ξ := Quotient.mk_out (s := St q A) ξ

def cc (ξ : Prim q A) : (ZMod q)ˣ := (rep_rel ξ).choose

theorem cc_spec (ξ : Prim q A) : ξ.1 = (rep ξ).1 ^ (cc ξ : ZMod q).val := (rep_rel ξ).choose_spec

theorem rep_eq {ζ ξ : Prim q A} (h : Rel q A ζ ξ) : rep ζ = rep ξ := by
  unfold rep; rw [Quotient.sound (s := St q A) h]

theorem cc_mul [Nontrivial A] {ζ ξ : Prim q A} (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    cc ξ = cc ζ * a := by
  apply Units.ext
  apply val_inj (rep ξ)
  rw [← cc_spec ξ, Units.val_mul, pow_val_mul, ← rep_eq ⟨a, h⟩, ← cc_spec ζ, h]

theorem cc_out [Nontrivial A] (o : Quotient (St q A)) : cc o.out = 1 := by
  have hr : rep o.out = o.out := by
    show (Quotient.mk (St q A) o.out).out = o.out
    rw [Quotient.out_eq]
  apply Units.ext
  apply val_inj o.out
  have h := cc_spec o.out
  rw [hr] at h
  rw [← h, Units.val_one, pow_val_one]

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

def wt (i : ℤ) (ξ : Prim q A) : ULift.{1} (ZMod q) := ULift.up (((cc ξ ^ i : (ZMod q)ˣ)) : ZMod q)

def psi0 (i : ℤ) : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Quotient (St q A) →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ fun ξ => Finsupp.single (Quotient.mk (St q A) ξ) (wt i ξ)

theorem primitive_roots_twisted_weight_map_single (i : ℤ) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    psi0 i (Finsupp.single ξ r) = Finsupp.single (Quotient.mk (St q A) ξ) (r * wt i ξ) := by
  rw [psi0, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]

theorem rel_le [Nontrivial A] (i : ℤ) : twRel q i A ≤ LinearMap.ker (psi0 i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, primitive_roots_twisted_weight_map_single]
  rw [sub_eq_zero, Quotient.sound (s := St q A) (⟨a, h⟩ : Rel q A ζ ξ)]
  congr 1
  apply ULift.ext
  simp only [wt, ULift.mul_down, cc_mul a h, mul_zpow, Units.val_mul, one_mul]
  ring

def phi [Nontrivial A] (i : ℤ) : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)]
    (Quotient (St q A) →₀ ULift.{1} (ZMod q)) := (twRel q i A).liftQ (psi0 i) (rel_le i)

def theta (i : ℤ) : (Quotient (St q A) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)]
    ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  (twRel q i A).mkQ ∘ₗ Finsupp.lmapDomain _ _ (fun o : Quotient (St q A) => o.out)

theorem phi_theta [Nontrivial A] (i : ℤ) : phi i ∘ₗ theta (q := q) (A := A) i = LinearMap.id := by
  refine Finsupp.lhom_ext fun o r => ?_
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  rw [Quotient.out_eq]
  congr 1
  rw [wt, cc_out, one_zpow, Units.val_one]
  apply ULift.ext
  simp

theorem theta_phi [Nontrivial A] (i : ℤ) : theta i ∘ₗ phi (q := q) (A := A) i = LinearMap.id := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ξ r => ?_)
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  refine (Submodule.Quotient.eq _).2 ?_
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single (rep ξ) (ULift.up ((cc ξ ^ i : (ZMod q)ˣ) : ZMod q))
      ∈ twRel q i A := Submodule.subset_span ⟨rep ξ, ξ, cc ξ, cc_spec ξ, rfl⟩
  have h2 := Submodule.smul_mem _ r hm
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one] at h2
  rw [← neg_mem_iff, neg_sub]
  exact h2

theorem flat_of_nontrivial [Nontrivial A] (i : ℤ) :
    Module.Flat (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Module.Flat.of_linearEquiv (LinearEquiv.ofLinearMap (phi i) (theta i) (phi_theta i) (theta_phi i))

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem shf_loc (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U),
      Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 →
      Loc U fun _ g => (P.map g.op).hom x = 0) := by
  constructor
  · intro U y
    refine ⟨Presheaf.imageSieve (toSheafify Scheme.etaleTopology P) y,
      Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    rintro V g ⟨t, ht⟩
    exact ⟨t, ht⟩
  · intro U x hx
    have h : (toSheafify Scheme.etaleTopology P).app (op U) x = (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
      change ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0
      rw [hx, map_zero]
    refine ⟨Presheaf.equalizerSieve (F := P) (X := op U) x 0,
      Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]

end LateralTheory.EtaleFoundations.TwFlat

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC in

theorem LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  intro q _ i
  obtain ⟨h1, h2⟩ := LateralTheory.EtaleFoundations.TwFlat.shf_loc (ZMod q) (Scheme.Γ ⋙ twF q i)
  refine ⟨Scheme.Γ ⋙ twF q i, toSheafify Scheme.etaleTopology _, h1, h2, fun U hU => ?_⟩
  have : Nonempty (⊤ : U.Opens) := ⟨⟨hU.some, trivial⟩⟩
  exact LateralTheory.EtaleFoundations.TwFlat.flat_of_nontrivial (A := Γ(U, ⊤)) i
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorHomDescendsAlongTensorPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensFam

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res h (Sec.res g y) = Sec.res (h ≫ g) y := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem sep {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (s s' : Sec M U)
    (h : Loc U fun V g => Sec.res g s = Sec.res g s') : s = s' := by
  obtain ⟨T, hT, h1⟩ := h
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  exact (hM T hT).isSeparatedFor.ext fun V g hg => h1 V g hg

theorem glue {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (T : Sieve U) (hT : T ∈ Scheme.etaleTopology U)
    (t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V)
    (ht : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      t W (k ≫ g) (T.downward_closed hg k) = Sec.res k (t V g hg)) :
    ∃ s : Sec M U, ∀ V g (hg : T.arrows g), Sec.res g s = t V g hg := by
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  let x : Presieve.FamilyOfElements (M.obj ⋙ forget _) T.arrows := fun V g hg => t V g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    exact ht V W g k hg
  exact ⟨(hM T hT).amalgamate x hx, fun V g hg => (hM T hT).valid_glue hx g hg⟩

theorem lift_res {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (τ.lift U w x) = τ.lift V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [Sec.res, map_add] at *; rw [ha, hb]
  | of i z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Sec.res, map_add] at *; rw [ha, hb]
    | tmul a c =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.lift.tmul, TensorProduct.map_tmul]
      exact τ.nat g _ _ w _ a c

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a c : Sec F U) :
    Sec.res g (a + c) = Sec.res g a + Sec.res g c := map_add _ _ _

section Main
variable {R S : Type} [CommRing R] [CommRing S] {I J K : Cx R}

def Good (τ : Pair I J K) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
    (U : Scheme.{0}) (y : Sec (K.X w) U) (s : Sec M U) : Prop :=
  Loc U fun V g => ∃ x, τ.lift V w x = Sec.res g y ∧ Sec.res g s = b V x

variable (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x))
include hτ hb

theorem key {U : Scheme.{0}} (x1 x2 : Tens I J U w) (h : τ.lift U w x1 = τ.lift U w x2) : b U x1 = b U x2 := by
  have h0 : τ.lift U w (x1 - x2) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨T, hT, hT'⟩ := hτ.2 U w _ h0
  apply sep M
  refine ⟨T, hT, fun V g hg => ?_⟩
  have h1 : Tens.res g w (x1 - x2) = 0 := hT' V g hg
  rw [map_sub, sub_eq_zero] at h1
  show Sec.res g (b U x1) = Sec.res g (b U x2)
  rw [hb, hb, h1]

theorem uniq {U : Scheme.{0}} {y : Sec (K.X w) U} {s s' : Sec M U}
    (h1 : Good τ w M b U y s) (h2 : Good τ w M b U y s') : s = s' := by
  apply sep M
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  rw [hs, hs']
  exact key τ hτ w M b hb x x' (hx.trans hx'.symm)

theorem good_exists (U : Scheme.{0}) (y : Sec (K.X w) U) : ∃ s, Good τ w M b U y s := by
  obtain ⟨T, hT, hc⟩ := hτ.1 U w y
  let t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hc V g hg).choose
  obtain ⟨s, hs⟩ := glue M T hT t (by
    intro V W g k hg
    simp only [t]
    rw [hb]
    apply key τ hτ w M b hb
    rw [(hc W (k ≫ g) (T.downward_closed hg k)).choose_spec, ← lift_res, (hc V g hg).choose_spec, res_res])
  exact ⟨s, T, hT, fun V g hg => ⟨(hc V g hg).choose, (hc V g hg).choose_spec, hs V g hg⟩⟩

omit hτ in
theorem good_add {U : Scheme.{0}} {y1 y2 : Sec (K.X w) U} {s1 s2 : Sec M U}
    (h1 : Good τ w M b U y1 s1) (h2 : Good τ w M b U y2 s2) : Good τ w M b U (y1 + y2) (s1 + s2) := by
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  exact ⟨x + x', by rw [map_add, hx, hx', res_add], by rw [res_add, hs, hs', map_add]⟩

omit hτ hb in
theorem good_zero (U : Scheme.{0}) : Good τ w M b U 0 0 :=
  loc_top fun V g => ⟨0, by simp, by simp⟩

omit hτ in
theorem good_nat {V U : Scheme.{0}} (g : V ⟶ U) {y : Sec (K.X w) U} {s : Sec M U}
    (h : Good τ w M b U y s) : Good τ w M b V (Sec.res g y) (Sec.res g s) := by
  obtain ⟨T, hT, h1⟩ := h
  refine ⟨T.pullback g, (Scheme.etaleTopology).pullback_stable g hT, fun W k hk => ?_⟩
  obtain ⟨x, hx, hs⟩ := h1 W (k ≫ g) hk
  exact ⟨x, by rw [res_res, hx], by rw [res_res, hs]⟩

omit hτ in
theorem good_lift (U : Scheme.{0}) (x : Tens I J U w) : Good τ w M b U (τ.lift U w x) (b U x) :=
  loc_top fun V g => ⟨Tens.res g w x, (lift_res τ g w x).symm, hb V U g x⟩

end Main

end LateralTheory.EtaleFoundations.TensFam

open LateralTheory.EtaleFoundations.TensFam in
theorem LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing : LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily := by
  intro R S _ _ I J K τ hτ w M b hb
  have ex := good_exists τ hτ w M b hb
  let φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U := fun U =>
    { toFun := fun y => (ex U y).choose
      map_zero' := uniq τ hτ w M b hb (ex U 0).choose_spec (good_zero τ w M b U)
      map_add' := fun y1 y2 => uniq τ hτ w M b hb (ex U _).choose_spec
        (good_add τ w M b hb (ex U y1).choose_spec (ex U y2).choose_spec) }
  refine ⟨φ, fun V U g y => ?_, fun U x => ?_⟩
  · exact uniq τ hτ w M b hb (good_nat τ w M b hb g (ex U y).choose_spec) (ex V _).choose_spec
  · exact uniq τ hτ w M b hb (ex U _).choose_spec (good_lift τ w M b hb U x)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorPreservesQuasiIsoOfAcyclicAndCone
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.tqis

def acyc : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic

def cone : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T'),
    τ.IsTensor → τ'.IsTensor → τ.Compat τ' f (𝟙 J) u → ∃ σ : Pair (mappingCone f) J (mappingCone u), σ.IsTensor

end LateralTheory.EtaleFoundations.tqis

theorem qis_iff_cone {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) : QuasiIso f ↔ (mappingCone f).Acyclic := by
  have h : HomotopyCategory.quasiIso (Shv R) (ComplexShape.up ℤ) ((HomotopyCategory.quotient _ _).map f) ↔ (HomotopyCategory.subcategoryAcyclic (Shv R)).trW ((HomotopyCategory.quotient _ _).map f) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at h
  change HomologicalComplex.quasiIso (Shv R) (ComplexShape.up ℤ) f ↔ _
  exact h.trans ((ObjectProperty.trW_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic (Shv R)) _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _))

theorem cone_ge {R : Type} [CommRing R] {I I' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] (f : I ⟶ I') :
    (mappingCone f).IsStrictlyGE (-1) :=
  CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)

theorem LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone (hA : LateralTheory.EtaleFoundations.tqis.acyc) (hC : LateralTheory.EtaleFoundations.tqis.cone) :
    LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  obtain ⟨σ, hσ⟩ := hC R τ τ' f u hτ hτ' hc
  have := cone_ge f
  rw [qis_iff_cone]
  exact hA R (-1) 0 σ hσ hJ ((qis_iff_cone f).1 inferInstance)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L),
    ∃ m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U,
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) ∧
      ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U),
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) →
      (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
      ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.map (L.d w (w + 1)) (m U s t w h a b) = m U (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) a) b +
          s.negOnePow • m U s (t + 1) (w + 1) (by omega) a (Sec.map (K.d t (t + 1)) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_of_family_and_leibniz (hfam : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists)
    (hleib : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz) : LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative := by
  intro R _ I J K T T3 τ τ' hτ _ M L μ' ν'
  obtain ⟨m, hnat, heq⟩ := hfam R τ hτ μ' ν'
  refine ⟨⟨m, hnat, hleib R τ hτ μ' ν' m hnat heq⟩, ?_⟩
  intro U s t u st tu w h1 h2 h3 h4 a b c
  exact heq U s t u st tu w h1 h2 h3 h4 a b c
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tt_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

def tt_tens_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → μ.IsTensor →
    K.IsStrictlyGE 0

def tt_twist_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {J M : Cx (ZMod q)}
    (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q j J e' → (∀ t, FlatS (J.X t)) →
    ∀ σ : Pair (sgl (tw q i)) J M, σ.IsTensor →
      IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ)

def tt_res_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) {I J M T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U),
    IsTwRes q i I e → J.IsStrictlyGE 0 → (∀ t, FlatS (J.X t)) →
    ∀ (σ : Pair (sgl (tw q i)) J M) (τ : Pair I J T), σ.IsTensor → τ.IsTensor →
      ∃ m : M ⟶ T, QuasiIso m ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec (J.X 0) U),
        Sec.map (m.f 0) (σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) b) =
          τ.mul U 0 0 0 (add_zero 0) (e U ζ) b

theorem etale_tensor_twisted_resolution_of_existence_bound_and_sides (hex : tt_tens_ex) (hge : tt_tens_ge) (htw : tt_twist_side) (hres : tt_res_side) :
    EtaleTensorPairTwistResolutionMul := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨M, σ, hσ⟩ := hex (ZMod q) (sgl (tw q i)) J
  obtain ⟨-, ε₁, hε₁, hgen₁⟩ := htw q i j k hk e' hJ hflat σ hσ
  obtain ⟨m, hm, hgen⟩ := hres q i e hI hJ.1 hflat σ τ hσ hτ
  refine ⟨hge (ZMod q) τ hI.1 hJ.1 hτ, ε₁ ≫ m, inferInstance, fun U ζ => ?_⟩
  refine Eq.trans ?_ (hgen U ζ (e' U ζ))
  refine Eq.trans ?_ (congrArg (Sec.map (m.f 0)) (hgen₁ U ζ))
  rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTwistExtendsThroughMonoToResolutionZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def EtaleKummerSectionsIntoTwistEmbeddingExist : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

def EtaleTwistExtendsThroughMonoToResolutionZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j →
    ∃ e : M ⟶ (res _ (tw q 1)).X 0, j ≫ e = resι _ (tw q 1)

theorem etale_kummer_torsor_class_exists_of_tors_and_ext (h1 : EtaleKummerSectionsIntoTwistEmbeddingExist) (h2 : EtaleTwistExtendsThroughMonoToResolutionZero) : EtaleKummerTriangleExists := by
  intro q _
  apply pick_spec
  obtain ⟨M, j, hj, s, hs1, hs2⟩ := h1 q
  obtain ⟨e, he⟩ := h2 q M j hj
  refine ⟨fun U v => Sec.map e (s U v), ?_, ?_⟩
  · intro V U g v hq
    show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)
    rw [← hs1 V U g v hq]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm
  · intro U ζ v w h
    show Sec.map e (s U w) = Sec.map e (s U v) + _
    rw [hs2 U ζ v w h]
    show (e.hom.app (op U)).hom (_ + _) = _
    rw [map_add]
    congr 1
    unfold resGen
    rw [← he]
    rfl
end LateralTheory.EtaleFoundations
end


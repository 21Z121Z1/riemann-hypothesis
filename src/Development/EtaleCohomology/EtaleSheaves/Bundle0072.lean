import Development.EtaleCohomology.EtaleSheaves.Bundle0063
import Development.EtaleCohomology.EtaleSheaves.Bundle0066
import Development.EtaleCohomology.EtaleSheaves.Bundle0067
import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Development.EtaleCohomology.EtaleSheaves.Bundle0058
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensQuot
section
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfQuot
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem hensQuot {A C : Type} [CommRing A] [HenselianLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) : HenselianLocalRing C := by
  have hloc : IsLocalHom g := IsLocalHom.of_surjective g hg
  refine { is_henselian := ?_ }
  intro p hp a0 h0 h1
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.mpr (fun n => hg _)) hp
  obtain ⟨b0, rfl⟩ := hg a0
  have e : ∀ (Q : A[X]) (x : A), g (Q.eval x) = (Q.map g).eval (g x) := fun Q x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  have hb0 : P.eval b0 ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map g
    rw [e, hPmap] at this
    exact (mem_maximalIdeal _).mp h0 this
  have hb1 : IsUnit ((derivative P).eval b0) := by
    apply (isUnit_map_iff g _).mp
    rw [e, ← derivative_map, hPmap]; exact h1
  obtain ⟨b, hb, hbm⟩ := HenselianLocalRing.is_henselian P hPm b0 hb0 hb1
  refine ⟨g b, ?_, ?_⟩
  · change p.eval (g b) = 0
    rw [← hPmap, ← e, hb.eq_zero, map_zero]
  · rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp hbm

theorem sepQuot {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) [IsLocalHom g] [IsSepClosed (ResidueField A)] : IsSepClosed (ResidueField C) := by
  have hbij : Function.Bijective (ResidueField.map g) := by
    refine ⟨(ResidueField.map g).injective, ?_⟩
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨residue A a, by simp⟩
  let e := RingEquiv.ofBijective _ hbij
  refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_eval₂_eq_zero_of_injective (e.symm : ResidueField C →+* ResidueField A)
    e.symm.injective p (degree_pos_of_irreducible hirr).ne' hsep
  refine ⟨e x, ?_⟩
  have h2 := congrArg e hx
  rw [map_zero] at h2
  rw [show (e : ResidueField A → ResidueField C) = (e : ResidueField A →+* ResidueField C) from rfl,
    Polynomial.hom_eval₂, RingEquiv.comp_symm] at h2
  exact h2

theorem shQuot : LeafSHQuot := by
  intro A _ hA W' ι' _
  obtain ⟨hH, hS⟩ := hA
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g :=
    hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  by_cases hC : Nontrivial Γ(W', ⊤)
  · right
    have hLC : IsLocalRing Γ(W', ⊤) := IsLocalRing.of_surjective' g.hom hg
    have hHC := hensQuot g.hom hg
    have : IsLocalHom g.hom := IsLocalHom.of_surjective g.hom hg
    exact ⟨hHC, sepQuot g.hom hg⟩
  · left
    rw [not_nontrivial_iff_subsingleton] at hC
    refine ⟨fun x => ?_⟩
    have h10 : (1 : Γ(W', ⊤)) = 0 := Subsingleton.elim _ _
    have := congrArg (W'.presheaf.germ ⊤ x trivial).hom h10
    rw [map_one, map_zero] at this
    exact one_ne_zero this

end LateralTheory.E.LeafClosedSH0PfQuot
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafActSheafPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafActSheafPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitActPfAug LateralTheory.E.LeafUnitPairPf LateralTheory.E.LeafUnitActPf

section Basic
variable {R : Type} [CommRing R]

theorem res_comp (F : Shv R) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom y) = (F.obj.map (k ≫ g).op).hom y
  rw [op_comp, Functor.map_comp]
  rfl

theorem res_smul (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (y : Sec F U) :
    Sec.res g (c • y) = c • Sec.res g y := map_smul (F.obj.map g.op).hom c y

theorem res_add (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (y z : Sec F U) :
    Sec.res g (y + z) = Sec.res g y + Sec.res g z := map_add (F.obj.map g.op).hom y z

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have h := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem map_smul' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ULift.{1} R) (y : Sec F U) :
    Sec.map φ (c • y) = c • Sec.map φ y := map_smul (φ.hom.app (op U)).hom c y

theorem sec_res (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res (F := ofRings R M) g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem glue (F : Shv R) {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology.{0} U)
    (s : ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ U), S.arrows g → Sec F V)
    (hs : ∀ ⦃V W : Scheme.{0}⦄ (g : V ⟶ U) (hg : S.arrows g) (h : W ⟶ V),
      Sec.res h (s g hg) = s (h ≫ g) (S.downward_closed hg h)) :
    ∃ t : Sec F U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), Sec.res g t = s g hg := by
  have hsh := F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS
  let x : Presieve.FamilyOfElements (F.obj ⋙ coyoneda.obj (op (ModuleCat.of (ULift.{1} R) (ULift.{1} R)))) S.arrows :=
    fun V g hg => ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (s g hg))
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g h hg
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton _ _ (s (h ≫ g) _)) 1 = (F.obj.map h.op).hom ((LinearMap.toSpanSingleton _ _ (s g hg)) 1)
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (hs g hg h).symm
  obtain ⟨t, ht, -⟩ := hsh x hx
  refine ⟨t.hom 1, fun V g hg => ?_⟩
  have h1 := congrArg (fun f => f.hom (1 : ULift.{1} R)) (ht g hg)
  change (F.obj.map g.op).hom (t.hom 1) = (LinearMap.toSpanSingleton _ _ (s g hg)) 1 at h1
  simpa [LinearMap.toSpanSingleton_apply] using h1

end Basic

variable {q : ℕ}

theorem etaleTwistZero_sheafifiedSection_of_ring_restrict {V U : Scheme.{0}} (g : V ⟶ U) (x : (twF q 0).obj Γ(U, ⊤)) :
    Sec.res (F := tw q 0) g (ofRings.sec (twF q 0) U x) = ofRings.sec (twF q 0) V (((twF q 0).map g.appTop).hom x) :=
  sec_res (twF q 0) g x

theorem etaleTwistZero_sheafifiedSection_of_ring_add {U : Scheme.{0}} (x y : (twF q 0).obj Γ(U, ⊤)) :
    ofRings.sec (twF q 0) U (x + y) = ofRings.sec (twF q 0) U x + ofRings.sec (twF q 0) U y := by
  unfold ofRings.sec; exact map_add _ x y

theorem sec_smul0 {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (x : (twF q 0).obj Γ(U, ⊤)) :
    ofRings.sec (twF q 0) U (c • x) = c • ofRings.sec (twF q 0) U x := by
  unfold ofRings.sec; exact map_smul _ c x

theorem etaleTwistZero_augmentation_map_add {V : Scheme.{0}} (x y : (twF q 0).obj Γ(V, ⊤)) :
    aug q Γ(V, ⊤) (x + y) = aug q Γ(V, ⊤) x + aug q Γ(V, ⊤) y := map_add _ _ _

theorem aug_smul0 {V : Scheme.{0}} (c : ULift.{1} (ZMod q)) (x : (twF q 0).obj Γ(V, ⊤)) :
    aug q Γ(V, ⊤) (c • x) = c • aug q Γ(V, ⊤) x := map_smul _ _ _

theorem aug_smul_eq (F : Shv (ZMod q)) {W : Scheme.{0}} (x y : (twF q 0).obj Γ(W, ⊤))
    (h : ofRings.sec (twF q 0) W x = ofRings.sec (twF q 0) W y) (z : Sec F W) :
    aug q Γ(W, ⊤) x • z = aug q Γ(W, ⊤) y • z := by
  apply sec_eq_of_loc
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_sections_eq_locally_of_sheafified_eq q x y h
  refine ⟨S, hS, fun V g hg => ?_⟩
  beta_reduce
  rw [res_smul, res_smul, ← aug_map q g.appTop x, ← aug_map q g.appTop y, hP V g hg]

def Good (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : (twF q 0).obj Γ(V, ⊤)), Sec.res g a = ofRings.sec (twF q 0) V x →
    Sec.res g t = aug q Γ(V, ⊤) x • Sec.res g b

theorem good_of_loc (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t : Sec F U)
    (h : Loc U fun V g => ∃ x : (twF q 0).obj Γ(V, ⊤), Sec.res g a = ofRings.sec (twF q 0) V x ∧
      Sec.res g t = aug q Γ(V, ⊤) x • Sec.res g b) : Good F a b t := by
  intro V g x hx
  obtain ⟨S, hS, hP⟩ := h
  refine sec_eq_of_loc F _ _ ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  obtain ⟨x', hx', ht⟩ := hP W (k ≫ g) hk
  rw [res_comp, ht, res_smul, res_comp, ← aug_map q k.appTop x]
  apply aug_smul_eq
  rw [← hx', ← res_comp, hx, etaleTwistZero_sheafifiedSection_of_ring_restrict]

theorem good_unique (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t₁ t₂ : Sec F U)
    (h₁ : Good F a b t₁) (h₂ : Good F a b t₂) : t₁ = t₂ := by
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  refine sec_eq_of_loc F t₁ t₂ ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [h₁ V g x hx, h₂ V g x hx]

theorem good_exists (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : ∃ t, Good F a b t := by
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  have key : ∀ {V W : Scheme.{0}} (g : V ⟶ U) (h : W ⟶ V) (x : (twF q 0).obj Γ(V, ⊤)) (x' : (twF q 0).obj Γ(W, ⊤)),
      Sec.res g a = ofRings.sec (twF q 0) V x → Sec.res (h ≫ g) a = ofRings.sec (twF q 0) W x' →
      Sec.res h (aug q Γ(V, ⊤) x • Sec.res g b) = aug q Γ(W, ⊤) x' • Sec.res (h ≫ g) b := by
    intro V W g h x x' e1 e2
    rw [res_smul, res_comp, ← aug_map q h.appTop x]
    apply aug_smul_eq
    rw [← etaleTwistZero_sheafifiedSection_of_ring_restrict, ← e1, res_comp, e2]
  obtain ⟨t, ht⟩ := glue F S hS (fun V g hg => aug q Γ(V, ⊤) (hP V g hg).choose • Sec.res g b)
    (fun V W g hg h => key g h _ _ (hP V g hg).choose_spec (hP W (h ≫ g) (S.downward_closed hg h)).choose_spec)
  exact ⟨t, good_of_loc F a b t ⟨S, hS, fun V g hg => ⟨_, (hP V g hg).choose_spec, ht V g hg⟩⟩⟩

def act (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : Sec F U := (good_exists F a b).choose

theorem act_good (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : Good F a b (act F a b) :=
  (good_exists F a b).choose_spec

theorem act_add_left (F : Shv (ZMod q)) {U : Scheme.{0}} (a₁ a₂ : Sec (tw q 0) U) (b : Sec F U) :
    act F (a₁ + a₂) b = act F a₁ b + act F a₂ b := by
  refine good_unique F _ b _ _ (act_good F _ b) (good_of_loc F _ b _ ?_)
  obtain ⟨S, hS, hP⟩ := loc_and (etale_tate_twist_zero_section_locally_lifts_to_ring_value q a₁) (etale_tate_twist_zero_section_locally_lifts_to_ring_value q a₂)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩⟩ := hP V g hg
  refine ⟨x₁ + x₂, by rw [res_add, h₁, h₂]; exact (etaleTwistZero_sheafifiedSection_of_ring_add x₁ x₂).symm, ?_⟩
  rw [res_add, act_good F a₁ b V g x₁ h₁, act_good F a₂ b V g x₂ h₂, etaleTwistZero_augmentation_map_add, add_smul]

theorem act_smul_left (F : Shv (ZMod q)) {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (a : Sec (tw q 0) U) (b : Sec F U) :
    act F (c • a) b = c • act F a b := by
  refine good_unique F _ b _ _ (act_good F _ b) (good_of_loc F _ b _ ?_)
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, h⟩ := hP V g hg
  refine ⟨c • x, by rw [res_smul, h]; exact (sec_smul0 c x).symm, ?_⟩
  rw [res_smul, act_good F a b V g x h, aug_smul0, smul_eq_mul, mul_smul]

theorem act_add_right (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b₁ b₂ : Sec F U) :
    act F a (b₁ + b₂) = act F a b₁ + act F a b₂ := by
  refine good_unique F a _ _ _ (act_good F a _) (fun V g x hx => ?_)
  rw [res_add, res_add, act_good F a b₁ V g x hx, act_good F a b₂ V g x hx, smul_add]

theorem act_smul_right (F : Shv (ZMod q)) {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (a : Sec (tw q 0) U) (b : Sec F U) :
    act F a (c • b) = c • act F a b := by
  refine good_unique F a _ _ _ (act_good F a _) (fun V g x hx => ?_)
  rw [res_smul, res_smul, act_good F a b V g x hx, smul_comm]

theorem act_res (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U) :
    Sec.res g (act F a b) = act F (Sec.res g a) (Sec.res g b) := by
  refine good_unique F _ _ _ _ (fun W k x hx => ?_) (act_good F _ _)
  rw [res_comp, res_comp]
  exact act_good F a b W (k ≫ g) x (by rw [← res_comp]; exact hx)

theorem act_map {F G : Shv (ZMod q)} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) :
    Sec.map φ (act F a b) = act G a (Sec.map φ b) := by
  refine good_unique G a _ _ _ (fun V g x hx => ?_) (act_good G a _)
  rw [map_res, act_good F a b V g x hx, map_smul', map_res]

theorem act_gen (F : Shv (ZMod q)) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : Sec F U) : act F (twGen 0 ζ) b = b := by
  refine good_unique F _ b _ _ (act_good F _ b) (fun V g x hx => ?_)
  let y : (twF q 0).obj Γ(U, ⊤) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have e : aug q Γ(V, ⊤) (((twF q 0).map g.appTop).hom y) = 1 := (aug_map q g.appTop y).trans (aug_mk_single q ζ)
  have hs : ofRings.sec (twF q 0) V (((twF q 0).map g.appTop).hom y) = ofRings.sec (twF q 0) V x := by
    rw [← hx]; exact (etaleTwistZero_sheafifiedSection_of_ring_restrict g y).symm
  exact (one_smul _ _).symm.trans ((congrArg (· • Sec.res g b) e).symm.trans (aug_smul_eq F _ x hs _))

theorem LeafActSheaf_of : LeafActSheaf := by
  intro q _
  refine ⟨fun F U => LinearMap.mk₂ (ULift.{1} (ZMod q)) (fun a b => act F a b)
    (act_add_left F) (act_smul_left F) (act_add_right F) (act_smul_right F), ?_, ?_, ?_⟩
  · intro F V U g a b
    exact act_res F g a b
  · intro F G φ U a b
    exact act_map φ a b
  · intro F U ζ b
    exact act_gen F ζ b

end LateralTheory.E.LeafActSheafPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExtTensPf

theorem res_isKInjective (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res; infer_instance

theorem res_injective (R : Type) [CommRing R] (F : Shv R) (n : ℤ) : Injective ((res R F).X n) := by
  unfold res
  rw [InjectiveResolution.cochainComplex]
  by_cases h : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    exact Injective.of_iso (HomologicalComplex.extendXIso _ _ hk).symm inferInstance
  · push_neg at h
    exact (HomologicalComplex.isZero_extend_X _ _ n h).injective

section
variable {C : Type*} [Category C] [Abelian C]

theorem exact_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [∀ n, Mono (ι.f n)] [∀ n, Injective (L.X n)]
    (u : S ⟶ L) (g0 : T ⟶ L) (H : Homotopy u (ι ≫ g0)) : ∃ g : T ⟶ L, ι ≫ g = u := by
  let h' : ∀ i j, T.X i ⟶ L.X j := fun i j => Injective.factorThru (H.hom i j) (ι.f i)
  have hh : (fun i j => ι.f i ≫ h' i j) = H.hom := by
    funext i j; exact Injective.comp_factorThru _ _
  refine ⟨g0 + Homotopy.nullHomotopicMap h', ?_⟩
  rw [Preadditive.comp_add, Homotopy.comp_nullHomotopicMap, hh]
  ext n
  rw [H.comm n]
  simp only [HomologicalComplex.add_f_apply]
  change _ + (dNext n H.hom + prevD n H.hom) = _
  abel

theorem homotopy_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [QuasiIso ι] [L.IsKInjective]
    (u : S ⟶ L) : ∃ g0 : T ⟶ L, Nonempty (Homotopy u (ι ≫ g0)) := by
  let _ := HasDerivedCategory.standard C
  let qt := (HomotopyCategory.quotient C (ComplexShape.up ℤ))
  have hi : IsIso (DerivedCategory.Qh.map (qt.map ι)) := by
    have e := (DerivedCategory.quotientCompQhIso C).hom.naturality ι
    have : IsIso (DerivedCategory.Q.map ι) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
    have e2 : DerivedCategory.Qh.map (qt.map ι) = (DerivedCategory.quotientCompQhIso C).hom.app S ≫
        DerivedCategory.Q.map ι ≫ (DerivedCategory.quotientCompQhIso C).inv.app T := by
      simp only [Functor.comp_map] at e
      rw [← reassoc_of% e]; simp [qt]
    rw [e2]; infer_instance
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) L).surjective
    (inv (DerivedCategory.Qh.map (qt.map ι)) ≫ DerivedCategory.Qh.map (qt.map u))
  obtain ⟨g0, rfl⟩ := qt.map_surjective g
  refine ⟨g0, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) L).injective
  rw [Functor.map_comp, Functor.map_comp, hg, IsIso.hom_inv_id_assoc]

theorem extAlongQIso {S T L : CochainComplex C ℤ} (ι : S ⟶ T) (hm : ∀ n, Mono (ι.f n)) (hq : QuasiIso ι)
    (hk : L.IsKInjective) (hinj : ∀ n, Injective (L.X n)) (u : S ⟶ L) : ∃ g : T ⟶ L, ι ≫ g = u := by
  obtain ⟨g0, ⟨H⟩⟩ := homotopy_lift ι u
  exact exact_lift ι u g0 H
end

def LeafTensMono : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ n, Mono (ι.f n)

def LeafTensQIso : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  QuasiIso ι

theorem LeafExtTens_of (hmono : LeafTensMono) (hqiso : LeafTensQIso) : LateralTheory.E.LeafPairExtPf2.LeafExtTens := by
  intro q _ i S T σ τ hσ hτ ι hι u
  exact extAlongQIso ι (hmono q i σ τ hσ hτ ι hι) (hqiso q i σ τ hσ hτ ι hι) (res_isKInjective _ _)
    (res_injective _ _) u

end LateralTheory.E.LeafExtTensPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueGenericPf
section
noncomputable section
open AlgebraicGeometry.StructureSheaf CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueGenericPf

example (A : Type) [CommRing A] : Sp A = Spec (CommRingCat.of A) := rfl

def eta (A : Type) [CommRing A] [IsDomain A] : Sp A := ⟨⊥, Ideal.isPrime_bot⟩

theorem eta_generic (A : Type) [CommRing A] [IsDomain A] : IsGenericPoint (eta A) (⊤ : Set (Sp A)) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact (PrimeSpectrum.le_iff_specializes (eta A) y).1 bot_le

def etaT (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum.Top A := ⟨⊥, Ideal.isPrime_bot⟩

def psi0 {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] :
    L →+* (structurePresheafInCommRingCat A).stalk (etaT A) := by
  have : (etaT A).asIdeal.IsPrime := Ideal.isPrime_bot
  exact IsLocalization.lift (M := nonZeroDivisors A) (S := L)
    (g := algebraMap A ((structurePresheafInCommRingCat A).stalk (etaT A))) (by
      intro y
      have hy : (y : A) ∈ (etaT A).asIdeal.primeCompl := by
        intro h0; exact nonZeroDivisors.ne_zero y.2 h0
      exact IsLocalization.map_units ((structurePresheafInCommRingCat A).stalk (etaT A))
        (⟨y, hy⟩ : (etaT A).asIdeal.primeCompl))

theorem fractionFieldToGenericStalk_algebraMap_eq {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] (a : A) :
    psi0 (L := L) (algebraMap A L a) = StructureSheaf.toStalk A (etaT A) a := by
  unfold psi0; simp only [IsLocalization.lift_eq]; rfl

example {A : Type} [CommRing A] [IsDomain A] : (structurePresheafInCommRingCat A).stalk (etaT A) = (Sp A).presheaf.stalk (eta A) := rfl

theorem glued_curve_generic_point_maps_to_function_field : LeafGlueGeneric := by
  intro Ω L _ _ _ A B u h G
  have := G.hiA
  have : IsFractionRing A L := h.2.2.2.2.2.2.2.2.2.1
  have : IsIntegral G.C0 := glued_affine_curve_is_integral_scheme Ω L A B u h G
  let s := G.iA.stalkMap (eta A)
  refine ⟨G.iA.base (eta A), Spec.map (inv s) ≫ Spec.map (CommRingCat.ofHom (psi0 (L := L))), ?_, ?_⟩
  · have hg := (eta_generic A).image G.iA.base.hom.continuous
    rw [Set.top_eq_univ, Set.image_univ,
      (G.iA.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq] at hg
    exact hg
  · have key := Scheme.SpecMap_stalkMap_fromSpecStalk G.iA (x := eta A)
    have hinv : G.C0.fromSpecStalk (G.iA.base (eta A)) =
        Spec.map (inv s) ≫ (Sp A).fromSpecStalk (eta A) ≫ G.iA := by
      rw [← key, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [Category.assoc, hinv, Category.assoc, Category.assoc, G.hcA]
    congr 1
    rw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    have ha : algebraMap Ω L a = algebraMap A L (algebraMap Ω A a) := rfl
    change psi0 (L := L) (algebraMap Ω L a) = StructureSheaf.toStalk A (etaT A) (algebraMap Ω A a)
    rw [ha, fractionFieldToGenericStalk_algebraMap_eq]

end LateralTheory.E.LeafGlueGenericPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueIsProperPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {A B : Subalgebra Ω L} {u : L}

def cov {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : G.C0.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool (fun b => cond b (Sp A) (Sp B))
    (fun | true => G.iA | false => G.iB)
    (by
      intro x
      have hx : x ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ x
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨true, z, rfl⟩
      · exact ⟨false, z, rfl⟩)
    (by intro b; cases b <;> [exact G.hiB; exact G.hiA])

set_option backward.isDefEq.respectTransparency false in
theorem lft (h : GH Ω L A B u) {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) :
    LocallyOfFiniteType G.c0 := by
  refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyOfFiniteType) (cov G) ?_
  intro b
  cases b
  · show LocallyOfFiniteType (G.iB ≫ G.c0)
    rw [G.hcB, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.2.1
  · show LocallyOfFiniteType (G.iA ≫ G.c0)
    rw [G.hcA, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
theorem qc {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : QuasiCompact G.c0 := by
  rw [HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.QuasiCompact)]
  refine ⟨?_⟩
  rw [← G.cover]
  exact (isCompact_range G.iA.base.hom.continuous).union (isCompact_range G.iB.base.hom.continuous)

def LeafGlueSep : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsSeparated G.c0

def LeafGlueExistence : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ValuativeCriterion.Existence G.c0

theorem LeafGlueIsProper_of (hS : LeafGlueSep) (hE : LeafGlueExistence) : LeafGlueIsProper := by
  intro Ω L _ _ _ A B u h G
  have := hS Ω L A B u h G
  have := qc G
  have := lft h G
  have : UniversallyClosed G.c0 := UniversallyClosed.of_valuativeCriterion _ (hE Ω L A B u h G)
  exact {}

end LateralTheory.E.LeafGlueIsProperPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkVanishing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StalkVanishing
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) : LateralTheory.E.LeafVan0Pf.LeafVanStalk := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m hsub y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i toK ι p hp U m y ?_
  intro A _ t hA
  have := hsub A t hA
  exact Subsingleton.elim _ _

end LateralTheory.E.StalkVanishing
end
end


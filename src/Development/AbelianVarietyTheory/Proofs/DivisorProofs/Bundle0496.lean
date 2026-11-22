import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBounded
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.AcycResLevel

theorem res_lift {R : Type} [CommRing R] (F : Shv R) {W : Shv R} (φ : W ⟶ (res R F).X 0)
    (hφ : φ ≫ (res R F).d 0 1 = 0) : ∃ g : W ⟶ F, g ≫ resι R F = φ := by
  let I := injectiveResolution F
  let e0 : (res R F).X 0 ≅ I.cocomplex.X 0 := I.cochainComplexXIso 0 0 rfl
  let e1 : (res R F).X 1 ≅ I.cocomplex.X 1 := I.cochainComplexXIso 1 1 rfl
  have hd : (res R F).d 0 1 = e0.hom ≫ I.cocomplex.d 0 1 ≫ e1.inv := I.cochainComplex_d 0 1 0 1 rfl rfl
  have hψ : (φ ≫ e0.hom) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [← cancel_mono e1.inv, zero_comp]
    rw [hd] at hφ
    simpa only [Category.assoc] using hφ
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' I.isLimitKernelFork (φ ≫ e0.hom) hψ
  let l' : W ⟶ F := l
  refine ⟨l', ?_⟩
  let ι0 : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  have h1 : resι R F = ι0 ≫ e0.inv := by
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ I.ι'.f 0 = _
    rw [InjectiveResolution.ι'_f_zero]
    simp [e0, ι0]
    rfl
  rw [h1]
  have h2 : l' ≫ ι0 = φ ≫ e0.hom := hl
  rw [← Category.assoc, h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem cocycle0_v_eq_zero {R : Type} [CommRing R] (G F : Shv R) (a : Cochain (sgl G) (res R F) 0)
    (h : ∃ m, ∃ _ : m + 1 = 0, ∃ b : Cochain (sgl G) (res R F) m, δ m 0 b = a) : a.v 0 0 (add_zero 0) = 0 := by
  obtain ⟨m, hm, b, rfl⟩ := h
  have hz : IsZero ((res R F).X m) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 m (by omega)
  have hsd : (sgl G).d 0 1 = 0 :=
    (HomologicalComplex.isZero_single_obj_X _ 0 G 1 (by simp)).eq_of_tgt _ _
  rw [δ_v m 0 (by omega) b 0 0 (add_zero 0) m 1 (by omega) rfl, hsd, zero_comp, smul_zero, add_zero]
  rw [hz.eq_of_tgt (b.v 0 m (by omega)) 0, zero_comp]

theorem ext_subsingleton_of_isZero : ∀ (R : Type) [CommRing R] (G Z : Shv R), IsZero Z → ∀ i : ℤ, Subsingleton (CohomologyClass (sgl G) (res R Z) i) := by
  intro R _ G Z hZ i
  haveI : (res R Z).IsKInjective := inferInstanceAs ((injectiveResolution Z).cochainComplex.IsKInjective)
  haveI : QuasiIso (resAug Z) := inferInstanceAs (QuasiIso (injectiveResolution Z).ι')
  have h0 : (sgl Z).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ ((CochainComplex.singleFunctor (Shv R) 0).map_isZero hZ)
  have h1 : (res R Z).Acyclic := by
    rw [HomologicalComplex.acyclic_iff]
    intro j
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have h2 := (h0 j)
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h2
    exact h2.of_iso (asIso (HomologicalComplex.homologyMap (resAug Z) j)).symm
  obtain ⟨H⟩ := IsKInjective.nonempty_homotopy_zero (𝟙 (res R Z)) h1
  have gen : ∀ a : Cochain (sgl G) (res R Z) i, δ i (i + 1) a = 0 →
      δ (i - 1) i (a.comp (Cochain.ofHomotopy H) (by omega)) = a := by
    intro a ha
    rw [δ_comp a (Cochain.ofHomotopy H) (by omega) (i + 1) 0 i (by omega) rfl (by omega), δ_ofHomotopy, ha,
      Cochain.zero_comp, smul_zero, add_zero, Cochain.ofHom_zero, sub_zero, Cochain.comp_id]
  have key : ∀ x : CohomologyClass (sgl G) (res R Z) i, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨i - 1, by omega, _, gen α.1 (Cocycle.δ_eq_zero α (i + 1))⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

theorem cycles_shortExact : ∀ (R : Type) [CommRing R] (M : Cx R) (k j : ℤ), k + 1 = j → M.ExactAt j → ∃ h : M.iCycles k ≫ M.toCycles k j = 0, (ShortComplex.mk _ _ h).ShortExact := by
  intro R _ M k j hkj hj
  have hw : M.iCycles k ≫ M.toCycles k j = 0 := by
    rw [← cancel_mono (M.iCycles j)]; simp
  refine ⟨hw, ?_⟩
  have hp : (ComplexShape.up ℤ).prev j = k := by simp; omega
  have he : Epi (M.toCycles k j) := by
    subst hp
    exact hj.epi_toCycles
  have hlim : IsLimit (KernelFork.ofι (M.iCycles k) hw) :=
    KernelFork.IsLimit.ofι _ _ (fun φ hφ => M.liftCycles φ j (by simp; omega) (by
        have := congrArg (· ≫ M.iCycles j) hφ
        simpa using this))
      (fun φ hφ => by simp) (fun φ hφ m hm => by rw [← cancel_mono (M.iCycles k)]; simpa using hm)
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hlim) (by dsimp; infer_instance) he

set_option backward.isDefEq.respectTransparency false in

theorem lift_of_ext_one_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) 1) → ∀ f : G ⟶ S.X₃, ∃ g : G ⟶ S.X₂, g ≫ S.g = f := by
  intro R _ G S hS h1 f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have hI3 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₃
  have hI2 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₂
  have hmono : Mono (resι R S.X₃) := hI3.2.2.2.2.2.1
  have hd3 : resι R S.X₃ ≫ (res R S.X₃).d 0 1 = 0 := hI3.2.2.2.2.2.2.1
  have hnat : resι R S.X₂ ≫ (resMap R S.g).f 0 = S.g ≫ resι R S.X₃ := (hI2.2.2.2.2.2.2.2 S.X₃ S.g).2
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have hz0 : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hsd : (sgl G).d 0 1 = 0 := (hz0 1 (by simp)).eq_of_tgt _ _
  let a3 : Cochain (sgl G) (res R S.X₃) 0 := Cochain.single (p := 0) (q := 0) (e.hom ≫ f ≫ resι R S.X₃) 0
  have ha3 : δ 0 1 a3 = 0 := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 1 := by omega
      rw [δ_v 0 1 rfl a3 0 1 hpq 0 1 (by omega) rfl, Cochain.single_v, hsd, zero_comp, smul_zero, add_zero,
        Cochain.zero_v, Category.assoc, Category.assoc, hd3, comp_zero, comp_zero]
    · exact (hz0 p hp).eq_of_src _ _
  let c3 : CohomologyClass (sgl G) (res R S.X₃) 0 := CohomologyClass.mk (Cocycle.mk a3 1 rfl ha3)
  have hc3 : HK.ext R (sgl G) z 0 (0 + 1) rfl c3 = 0 := h1.elim _ _
  obtain ⟨w, hw⟩ := ((hz (sgl G) 0).2.1 c3).1 hc3
  obtain ⟨β, rfl⟩ := w.mk_surjective
  have hw' : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0)) = c3 := hw
  have hdiff : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0) - Cocycle.mk a3 1 rfl ha3) = 0 := by
    rw [CohomologyClass.mk_sub, hw', sub_self]
  rw [CohomologyClass.mk_eq_zero_iff] at hdiff
  have hv := GlobalTheory.AcycResLevel.cocycle0_v_eq_zero G S.X₃ _ hdiff
  have hv' : β.1.v 0 0 (add_zero 0) ≫ (resMap R S.g).f 0 = e.hom ≫ f ≫ resι R S.X₃ := by
    have h := hv
    simp [zcomp, a3, Cochain.comp_zero_cochain_v, sub_eq_zero] at h
    exact h
  have hb : β.1.v 0 0 (add_zero 0) ≫ (res R S.X₂).d 0 1 = 0 := by
    have h := congrArg (fun c => c.v 0 1 (by simp)) (Cocycle.δ_eq_zero β 1)
    rw [δ_v 0 1 rfl _ 0 1 (by simp) 0 1 (by simp) (by simp)] at h
    rw [hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    exact h
  obtain ⟨g', hg'⟩ := GlobalTheory.AcycResLevel.res_lift S.X₂ (e.inv ≫ β.1.v 0 0 (add_zero 0))
    (by rw [Category.assoc, hb, comp_zero])
  refine ⟨g', ?_⟩
  rw [← cancel_mono (resι R S.X₃), ← cancel_epi e.hom, Category.assoc, ← hnat, ← Category.assoc g', hg', ← hv']
  simp

theorem ext_pos_subsingleton_of_shortExact : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₂) i)) → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) i)) → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₃) i) := by
  intro R _ G S hS h2 h1 i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have key : ∀ x : CohomologyClass (sgl G) (res R S.X₃) i, x = 0 := by
    intro x
    have e := (hz (sgl G) i).2.1
    have h0 : HK.ext R (sgl G) z i (i + 1) rfl x = 0 := (h1 (i + 1) (by omega)).elim _ _
    obtain ⟨w, hw⟩ := (e x).1 h0
    rw [← hw, (h2 i hi).elim w 0, map_zero]
  exact ⟨fun x y => (key x).trans (key y).symm⟩

theorem subsingleton_of_lifts : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (n : ℤ), (∀ f : G ⟶ M.X n, f ≫ M.d n (n + 1) = 0 → ∃ g : G ⟶ M.X (n - 1), g ≫ M.d (n - 1) n = f) → Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M n hlift
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hd : (sgl G).d 0 1 = 0 := (hz 1 (by simp)).eq_of_tgt _ _
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have gen : ∀ a : Cochain (sgl G) M n, δ n (n + 1) a = 0 → ∃ b : Cochain (sgl G) M (n - 1), δ (n - 1) n b = a := by
    intro a ha
    have h := congrArg (fun c => c.v 0 (n + 1) (by simp)) ha
    rw [δ_v n (n + 1) rfl _ 0 (n + 1) (by simp) n 1 (by simp) (by simp)] at h
    rw [hd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    have hf : (e.inv ≫ a.v 0 n (by simp)) ≫ M.d n (n + 1) = 0 := by
      rw [Category.assoc, h, comp_zero]
    obtain ⟨g, hg⟩ := hlift _ hf
    refine ⟨Cochain.single (p := 0) (q := n - 1) (e.hom ≫ g) (n - 1), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : n = q := by omega
      rw [δ_v (n - 1) n (by omega) _ 0 n hpq (n - 1) 1 (by omega) rfl, Cochain.single_v, hd, zero_comp,
        smul_zero, add_zero, Category.assoc, hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · exact (hz p hp).eq_of_src _ _
  have key : ∀ x : CohomologyClass (sgl G) M n, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨b, hb⟩ := gen α.1 (Cocycle.δ_eq_zero α (n + 1))
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, b, hb⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.AcycResLevel

theorem GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M a _ hM hExt n
  have hZ0 : ∀ k, k ≤ a → IsZero (M.cycles k) := by
    intro k hk
    obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (k - 1) k (by omega) (hM k)
    have : Epi (M.toCycles (k - 1) k) := hS.epi_g
    exact IsZero.of_epi (M.toCycles (k - 1) k) (M.isZero_of_isStrictlyGE a (k - 1))
  have hge : ∀ k, a ≤ k → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k hk
    induction k, hk using Int.le_induction with
    | base => intro i _; exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 a le_rfl) i
    | succ k hak ih =>
      obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M k (k + 1) rfl (hM (k + 1))
      exact GlobalTheory.AcycResLevel.ext_pos_subsingleton_of_shortExact R G _ hS (hExt k) ih
  have hZ : ∀ k, ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k
    rcases le_or_gt k a with hk | hk
    · intro i _
      exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 k hk) i
    · exact hge k hk.le
  refine GlobalTheory.AcycResLevel.subsingleton_of_lifts R G M n fun f hf => ?_
  obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (n - 1) n (by omega) (hM n)
  obtain ⟨g, hg⟩ := GlobalTheory.AcycResLevel.lift_of_ext_one_subsingleton R G _ hS ((hZ (n - 1) 1 one_pos)) (M.liftCycles f (n + 1) (by simp) hf)
  refine ⟨g, ?_⟩
  have := congrArg (· ≫ M.iCycles n) hg
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedSectionsTateTwistResolution
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppRes

open ClsSpec

variable {R : Type} [CommRing R]

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
private theorem shv_hom_ext_of_sec_map_eq {S : Type} [CommRing S] {F G : _root_.GlobalTheory.EtC.Shv S}
    (φ ψ : F ⟶ G)
    (h : ∀ U (a : _root_.GlobalTheory.EtC.Sec F U),
      _root_.GlobalTheory.EtC.Sec.map φ a = _root_.GlobalTheory.EtC.Sec.map ψ a) : φ = ψ := by
  ext U a
  exact h U.unop a

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
private theorem sec_map_zero_apply {S : Type} [CommRing S] {F G : _root_.GlobalTheory.EtC.Shv S}
    {U : Scheme} (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.map (0 : F ⟶ G) a = 0 := by
  simp [_root_.GlobalTheory.EtC.Sec.map]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
private theorem etLoc_of_forall {U : Scheme} {P : (V : Scheme) → (V ⟶ U) → Prop}
    (h : ∀ V g, P V g) : _root_.GlobalTheory.EtC.Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in

theorem _root_.GlobalTheory.EtC.SuppRes.supp_res : ∀ (q : ℕ) [NeZero q] (i : ℤ)
    (D : _root_.GlobalTheory.EtC.Cx (ZMod q))
    (ι : D ⟶ _root_.GlobalTheory.EtC.res _ (_root_.GlobalTheory.EtC.tw q i)),
    (∀ n U, Function.Injective (_root_.GlobalTheory.EtC.Sec.map (ι.f n) (U := U))) →
    (∀ n U (a : _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.res _ (_root_.GlobalTheory.EtC.tw q i)).X n) U),
      (∃ b, _root_.GlobalTheory.EtC.Sec.map (ι.f n) b = a) ↔
      _root_.GlobalTheory.EtC.Loc U fun V g =>
        IsUnit (q : Γ(V, ⊤)) ∨ _root_.GlobalTheory.EtC.Sec.res g a = 0) →
    ∃ e : ∀ U : Scheme.{0}, _root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) → _root_.GlobalTheory.EtC.Sec (D.X 0) U,
      _root_.GlobalTheory.EtC.IsTwRes q i D e ∧
      ∀ U ζ, _root_.GlobalTheory.EtC.Sec.map (ι.f 0) (e U ζ) = _root_.GlobalTheory.EtC.resGen i ζ := by
  intro q _ i D ι hinj himg
  haveI hmono : ∀ n, Mono (ι.f n) := fun n =>
    (_root_.GlobalTheory.EtC.mono_epi_sections (ZMod q) (ι.f n)).1.2 (fun U => hinj n U)
  obtain ⟨-, -, hIge, -, hterm, hAmono, hAd, -⟩ :=
    _root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (_root_.GlobalTheory.EtC.tw q i)
  haveI := hIge
  haveI := hAmono
  have hA : _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) ≫
      cokernel.π (ι.f 0) = 0 := by
    apply shv_hom_ext_of_sec_map_eq
    intro U y
    rw [sec_map_zero_apply, ← _root_.GlobalTheory.EtC.ClsSpec.map_comp]
    obtain ⟨b, hb⟩ := (himg 0 U (_root_.GlobalTheory.EtC.Sec.map
      (_root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) y)).2 (by
        refine _root_.GlobalTheory.EtC.ClsSpec.loc_mono
          ((_root_.GlobalTheory.EtC.twist_sections q i).1 U y) ?_
        rintro V g (h | ⟨ζ, c, -⟩)
        · right
          rw [_root_.GlobalTheory.EtC.ClsSpec.res_map, h,
            _root_.GlobalTheory.EtC.ClsSpec.smap_zero]
        · exact Or.inl ζ.2.1)
    rw [← hb, _root_.GlobalTheory.EtC.ClsSpec.map_comp, cokernel.condition, sec_map_zero_apply]
  have hA' : Abelian.monoLift (ι.f 0) _ hA ≫ ι.f 0 =
      _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) :=
    Abelian.monoLift_comp _ _ _
  have hd : Abelian.monoLift (ι.f 0) _ hA ≫ D.d 0 1 = 0 := by
    rw [← cancel_mono (ι.f 1), zero_comp, Category.assoc, ← ι.comm, ← Category.assoc, hA', hAd]
  let ε : _root_.GlobalTheory.EtC.sgl (_root_.GlobalTheory.EtC.tw q i) ⟶ D :=
    HomologicalComplex.mkHomFromSingle (Abelian.monoLift (ι.f 0) _ hA) (by
        intro k hk
        have hk1 : k = 1 := by simpa using hk.symm
        subst hk1
        exact hd)
  have hε0 : ε.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (_root_.GlobalTheory.EtC.tw q i)).hom ≫ Abelian.monoLift (ι.f 0) _ hA :=
    HomologicalComplex.mkHomFromSingle_f _ _
  have haug : (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)).hom ≫
        _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) := by
    rw [← hterm]
    unfold _root_.GlobalTheory.EtC.sglι
    erw [Iso.hom_inv_id_assoc]
  have hει : ε.f 0 ≫ ι.f 0 = (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 := by
    rw [haug]
    erw [hε0, Category.assoc, hA']
    all_goals rfl
  have hterm' : _root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i) ≫ ε.f 0 ≫ ι.f 0 =
      _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) := by
    rw [hει, hterm]
  refine ⟨fun U ζ => _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map
    (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) (_root_.GlobalTheory.EtC.twGen i ζ)), ?_, ?_⟩
  · unfold _root_.GlobalTheory.EtC.IsTwRes
    refine ⟨?_, ε, ?_, fun U ζ => rfl⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact @IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)
    · refine ⟨fun n => ?_⟩
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · rw [quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne)]
        exact ShortComplex.exact_of_isZero_X₂ _
          (@IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn))
      · rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp),
          ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_]
        · constructor
          · rw [_root_.GlobalTheory.EtC.exactIff]
            intro U b hb
            have hcyc : _root_.GlobalTheory.EtC.Sec.map
                ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d 0 1)
                (_root_.GlobalTheory.EtC.Sec.map (ι.f 0) b) = 0 := by
              erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm,
                ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]
              exact _root_.GlobalTheory.EtC.ClsSpec.smap_zero _
            obtain ⟨y, hy⟩ := ((_root_.GlobalTheory.EtC.resSec (ZMod q)
              (_root_.GlobalTheory.EtC.tw q i) U).1 _).1 hcyc
            have hb' : _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map
                (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y) = b := by
              apply hinj 0 U
              simp only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm', hy]
            exact etLoc_of_forall fun V g =>
              ⟨_root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map
                (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y),
                (_root_.GlobalTheory.EtC.ClsSpec.res_map (ε.f 0) g _).symm.trans
                  (congrArg (_root_.GlobalTheory.EtC.Sec.res g) hb')⟩
          · have hcomp : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (_root_.GlobalTheory.EtC.tw q i)).hom ≫
                _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) :=
              @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _ hAmono
            rw [← haug, ← hει] at hcomp
            exact @mono_of_mono _ _ _ _ _ (ε.f 0) (ι.f 0) hcomp
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)
            (-1) (by norm_num)).eq_of_src _ _
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)
            1 (by norm_num)).eq_of_tgt _ _
        · exact (@IsZero.of_mono _ _ _ _ _ (ι.f (-1)) (hmono (-1))
            (CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by simp))).eq_of_src _ _
      · rw [quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne'),
          D.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp),
          _root_.GlobalTheory.EtC.exactIff]
        intro U b hb
        have hcyc : _root_.GlobalTheory.EtC.Sec.map
            ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d n (n + 1))
            (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b) = 0 := by
          erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm,
            ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]
          exact _root_.GlobalTheory.EtC.ClsSpec.smap_zero _
        have hex := (_root_.GlobalTheory.EtC.resSec (ZMod q)
          (_root_.GlobalTheory.EtC.tw q i) U).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hcyc
        have hsupp := (himg n U (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b)).1 ⟨b, rfl⟩
        refine _root_.GlobalTheory.EtC.ClsSpec.loc_mono (_root_.GlobalTheory.EtC.ClsSpec.loc_and hex hsupp) ?_
        rintro V g ⟨⟨y, hy⟩, hq | hz⟩
        · obtain ⟨y', rfl⟩ := (himg (n - 1) V y).2
            (etLoc_of_forall fun W h => Or.inl (_root_.GlobalTheory.EtC.ClsSpec.unit_res h hq))
          refine ⟨y', hinj n V ?_⟩
          exact (_root_.GlobalTheory.EtC.ClsSpec.map_comp (D.d (n - 1) n) (ι.f n) y').trans
            ((congrArg (fun φ => _root_.GlobalTheory.EtC.Sec.map φ y') (ι.comm (n - 1) n).symm).trans
              ((_root_.GlobalTheory.EtC.ClsSpec.map_comp (ι.f (n - 1))
                ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d (n - 1) n)
                  y').symm.trans
                (hy.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map (ι.f n) g b))))
        · refine ⟨0, ?_⟩
          erw [_root_.GlobalTheory.EtC.ClsSpec.smap_zero]
          apply hinj n V
          exact (_root_.GlobalTheory.EtC.ClsSpec.smap_zero _).trans
            (hz.symm.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map _ g b))
  · intro U ζ
    simp only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm']
    rfl

end GlobalTheory.EtC.SuppRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallyInjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  first | (exact @GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective) | (exact GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective) | (intros; apply GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.tw_mul_locSurj) | (exact GlobalTheory.EtC.tw_mul_locSurj) | (intros; apply GlobalTheory.EtC.tw_mul_locSurj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Surjective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.etaS_surjective) | (exact GlobalTheory.EtC.MuTw.etaS_surjective) | (intros; apply GlobalTheory.EtC.MuTw.etaS_surjective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  first | (exact @GlobalTheory.EtC.TwResExt.twRes_ext) | (exact GlobalTheory.EtC.TwResExt.twRes_ext) | (intros; apply GlobalTheory.EtC.TwResExt.twRes_ext  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
open ClsSpec

theorem one_eq_of_ev (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0)
    (hα : ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) :
    CohomologyClass.mk α = one q E := by
  obtain ⟨β, hβ, hβv⟩ := one_spec q E hE
  rw [← hβ]
  congr 1
  refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using h.symm
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hE U ⟨x⟩)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1, hα _ _ ζ, hβv _ _ ζ]
  | succ p =>
    have hs : s < 0 := by omega
    haveI := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs
    exact Subsingleton.elim _ _

theorem pull_one (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') :
    pull _ f _ _ (one q E') = one q E := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨β, hβ, hβv⟩ := one_spec q E' hE'
  rw [← hβ]
  refine one_eq_of_ev q E hE _ fun U x ζ => ?_
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f β.1 0 0 _ U x).trans (hβv U (x.map f) ζ)

theorem rootClass_eq_secClass {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    rootClass i ζ = secClass (tw q i) (twGen i ζ) := by
  unfold rootClass secClass
  congr 1
  funext c
  apply propext
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α, hα, (h X (𝟙 X)).trans (ClsSpec.res_id _)⟩
  · rintro ⟨α, hα, h⟩
    refine ⟨α, hα, fun U x => ?_⟩
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1 0 0 (by simp) U X x (𝟙 X)
    rw [h] at e
    refine e.symm.trans ?_
    congr 1

theorem one_root_spec : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ∧ (∀ E : Spc, Inv q E → ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) → CohomologyClass.mk α = one q E) ∧ (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧ ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), rootClass i ζ = secClass (tw q i) (twGen i ζ) :=
  fun q _ => ⟨fun E hE => one_spec q E hE, fun E hE α hα => one_eq_of_ev q E hE α hα,
    fun f hE' => pull_one q f hE', fun i _ ζ => rootClass_eq_secClass i ζ⟩

end GlobalTheory.EtC

end
end


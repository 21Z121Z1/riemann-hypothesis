import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExp

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIsomorphismUnitConstantPlusEpsFunctio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitPart

open GlobalTheory.KS

section Calc

variable {X Y Z : Scheme.{0}}

theorem pbT_pbT' (h : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {O : Z.Opens} (h₁ : V ≤ f ⁻¹ᵁ U)
    (h₂ : O ≤ h ⁻¹ᵁ V) (s : Γ(X, U)) : pbT h (pbT f s V) O = pbT (h ≫ f) s O := by
  rw [pbT_of_le f h₁, pbT_of_le h h₂, pbT_of_le (h ≫ f) (h₂.trans (h.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE h f U V O h₁ h₂)

theorem app_eq_pbT' (f : Z ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) : (f.app U).hom s = pbT f s (f ⁻¹ᵁ U) := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.app_eq_appLE]

theorem val_res' {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rsT u.val V := (rsT_of_le h _).symm

theorem pbT_id_le' {O₀ O : X.Opens} (h : O ≤ O₀) (s : Γ(X, O₀)) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT, rsT, dif_pos (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O₀ from h), dif_pos h]
  rfl

theorem constFn_zero' {R : Type} [CommRing R] (q : X ⟶ Sp R) (O : X.Opens) : constFn q O 0 = 0 := by
  rw [constFn, map_zero, map_zero]

theorem constFn_comp_spMap' {R S : Type} [CommRing R] [CommRing S] (q : Y ⟶ Sp S) (x : R →+* S)
    (W : Y.Opens) (t : R) : constFn (q ≫ spMap x) W t = constFn q W (x t) := by
  have e1 : (q ≫ spMap x).appLE ⊤ W le_top = (spMap x).appLE ⊤ ⊤ le_top ≫ q.appLE ⊤ W le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := congrArg (fun k => k.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x))
  change ((q ≫ spMap x).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) =
    (q.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (x t))
  rw [e1, CommRingCat.comp_apply]
  congr 1
  simp only [CommRingCat.comp_apply] at h2
  exact h2.symm

theorem isUnit_of_mul_eq_one' {M : Type*} [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem isUnit_pbT (f : Z ⟶ Y) {U : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    IsUnit (pbT f u.val O) :=
  isUnit_of_mul_eq_one' _ (pbT f (u⁻¹).val O) (by rw [← pbT_mul, Units.mul_inv, pbT_one f h])

theorem exists_unit_glue {J : Type} (V : J → Y.Opens) (hV : ⨆ i, V i = ⊤) (a : ∀ i, Γ(Y, V i))
    (ha : ∀ i, IsUnit (a i)) (h : ∀ i l, rsT (a i) (V i ⊓ V l) = rsT (a l) (V i ⊓ V l)) :
    ∃ t : Γ(Y, ⊤), IsUnit t ∧ ∀ i, rsT t (V i) = a i := by
  choose b hb using fun i => (ha i).exists_right_inv
  obtain ⟨t, ht⟩ := exists_rsT_eq V (O := ⊤) (fun _ => le_top) hV.ge a h
  have hb' : ∀ i l, rsT (b i) (V i ⊓ V l) = rsT (b l) (V i ⊓ V l) := by
    intro i l
    have e1 : rsT (a i) (V i ⊓ V l) * rsT (b i) (V i ⊓ V l) = 1 := by
      rw [← rsT_mul, hb i, rsT_one inf_le_left]
    have e2 : rsT (a l) (V i ⊓ V l) * rsT (b l) (V i ⊓ V l) = 1 := by
      rw [← rsT_mul, hb l, rsT_one inf_le_right]
    rw [h i l] at e1
    calc rsT (b i) (V i ⊓ V l) = rsT (b i) (V i ⊓ V l) * (rsT (a l) (V i ⊓ V l) * rsT (b l) (V i ⊓ V l)) := by
          rw [e2, _root_.mul_one]
      _ = (rsT (a l) (V i ⊓ V l) * rsT (b i) (V i ⊓ V l)) * rsT (b l) (V i ⊓ V l) := by ring
      _ = rsT (b l) (V i ⊓ V l) := by rw [e1, _root_.one_mul]
  obtain ⟨t', ht'⟩ := exists_rsT_eq V (O := ⊤) (fun _ => le_top) hV.ge b hb'
  refine ⟨t, isUnit_of_mul_eq_one' t t' ?_, ht⟩
  refine eq_of_rsT_eq V (fun _ => le_top) hV.ge _ _ fun i => ?_
  rw [rsT_mul, ht, ht', hb, rsT_one le_top]

theorem pbT_mul_inv_eq_one (f : Z ⟶ Y) {U : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ U) (u v : Γ(Y, U)ˣ)
    (huv : pbT f u.val O = pbT f v.val O) : pbT f (u * v⁻¹).val O = 1 := by
  rw [Units.val_mul, pbT_mul, huv, ← pbT_mul, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, pbT_one f h]

theorem val_pull_g (L : LB X) (π : Y ⟶ X) (a b : PUnit → L.ι) :
    ((L.pull π).g a b).val = pbT π (L.g (a PUnit.unit) (b PUnit.unit)).val ((L.pull π).U a ⊓ (L.pull π).U b) := by
  show (∏ k : PUnit, (res _ (pullU π _ (L.g (a k) (b k)))) ^ (1 : ℤ)).val = _
  have hle : (L.pull π).U a ⊓ (L.pull π).U b ≤ π ⁻¹ᵁ (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) :=
    fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
  rw [Fintype.prod_unique, zpow_one, pbT_of_le π hle]
  rfl

theorem pbT_pull_g {W : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (j : W ⟶ Y) (a b : PUnit → L.ι) {O₁ : Y.Opens}
    (h₁ : O₁ ≤ (L.pull π).U a ⊓ (L.pull π).U b) {O : W.Opens} (hO : O ≤ j ⁻¹ᵁ O₁) :
    pbT j (res h₁ ((L.pull π).g a b)).val O = pbT (j ≫ π) (L.g (a PUnit.unit) (b PUnit.unit)).val O := by
  have hle : (L.pull π).U a ⊓ (L.pull π).U b ≤ π ⁻¹ᵁ (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) :=
    fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
  rw [val_res', pbT_rsT j h₁ hO, val_pull_g, pbT_pbT' j π hle (hO.trans (j.preimage_mono h₁))]

theorem pbT_div_g_pull {W : Scheme.{0}} (L : LB X) (π₁ π₂ : Y ⟶ X) (j : W ⟶ Y) (a b : PUnit → L.ι) (O : W.Opens)
    (hO : O ≤ j ⁻¹ᵁ ((LB.div (L.pull π₂) (L.pull π₁)).U (a, a) ⊓ (LB.div (L.pull π₂) (L.pull π₁)).U (b, b)))
    (hj : j ≫ π₁ = j ≫ π₂) :
    pbT j ((LB.div (L.pull π₂) (L.pull π₁)).g (a, a) (b, b)).val O = 1 := by
  refine pbT_mul_inv_eq_one j hO _ _ ?_
  refine (pbT_pull_g L π₂ j a b _ hO).trans ?_
  refine Eq.trans ?_ (pbT_pull_g L π₁ j a b _ hO).symm
  rw [hj]

end Calc

theorem pr_isPullback {k : Type} [Field k] {R : Type} [CommRing R] (ρ : R →+* DualNumber k) {X B A₀ : Scheme.{0}}
    {q : X ⟶ Sp R} {hB : B ⟶ Sp (DualNumber k)} {π₂ : B ⟶ X} {h0 : A₀ ⟶ Sp k} {m₀ : A₀ ⟶ X} {pr : B ⟶ A₀}
    (H₂ : IsPullback π₂ hB q (spMap (constHom ρ)))
    (H₀ : IsPullback m₀ h0 q (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
    (hpr : pr ≫ m₀ = π₂) (hpr' : pr ≫ h0 = hB ≫ spMap (algebraMap k (DualNumber k))) :
    IsPullback pr hB h0 (spMap (algebraMap k (DualNumber k))) := by
  refine IsPullback.of_right ?_ hpr' H₀
  have e : spMap (algebraMap k (DualNumber k)) ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) =
      spMap (constHom ρ) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  rw [hpr, e]; exact H₂

theorem unit_eq_const {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (u : Γ(A₀.left, ⊤)) (hu : IsUnit u) : ∃ c : kˣ, u = constFn A₀.hom ⊤ (c : k) := by
  have hb := GlobalTheory.allSixLaws.1.globalFns (Sp k) A₀ hA
  obtain ⟨x, hx⟩ := hb.2 u
  let e := RingEquiv.ofBijective A₀.hom.appTop.hom hb
  have hxu : IsUnit x := by
    have : x = e.symm u := by rw [← hx]; exact (e.symm_apply_apply x).symm
    rw [this]; exact hu.map e.symm
  have hc : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x) := hxu.map _
  refine ⟨hc.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hx]
  have hh : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  unfold constFn
  rw [hh]
  first
    | rfl
    | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; congr 2 <;> simp)

end GlobalTheory.UnitPart

namespace GlobalTheory.UnitPart

open GlobalTheory.KS

theorem unitPart : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ (a : kˣ) (b : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) (algebraMap k (DualNumber k) (a : k)) + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (b i) (π₂ ⁻¹ᵁ V i) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hagree A₀ _ m₀ hm₀ pr hpr hprA J V jj hV hVU w hw
  subst hpr
  have hpre : ∀ W : P.A.left.Opens, π₁ ⁻¹ᵁ W = (pr ≫ m₀) ⁻¹ᵁ W :=
    GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers k P.A.left B'.left B'.hom π₁ (pr ≫ m₀) hagree
  have HP : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) :=
    pr_isPullback ρ h₂.1 hm₀.1 rfl hprA
  have hfa : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; rfl
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  let j : A₀.left ⟶ B'.left := HP.lift (𝟙 A₀.left) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
    (by rw [Category.id_comp, Category.assoc, hfa, Category.comp_id])
  have hj1 : j ≫ pr = 𝟙 _ := HP.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := HP.lift_snd _ _ _
  have hj12 : j ≫ π₁ = j ≫ pr ≫ m₀ := hagree A₀.left j A₀.hom hj2
  have hjm : j ≫ pr ≫ m₀ = m₀ := by rw [← Category.assoc, hj1, Category.id_comp]
  have hjm1 : j ≫ π₁ = m₀ := hj12.trans hjm
  have hmj : ∀ U : P.A.left.Opens, m₀ ⁻¹ᵁ U = j ⁻¹ᵁ ((pr ≫ m₀) ⁻¹ᵁ U) := fun U => by
    conv_lhs => rw [← hjm]
    rfl
  let c : J → (PUnit → P.L.ι) := fun i _ => jj i
  let C : J → B'.left.Opens := fun i => (LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).U (c i, c i)
  have hWC : ∀ i, (pr ≫ m₀) ⁻¹ᵁ V i ≤ C i := by
    intro i x hx
    have hx1 : x ∈ π₁ ⁻¹ᵁ V i := by rw [hpre]; exact hx
    exact ⟨Set.mem_iInter.2 fun _ => hVU i hx, Set.mem_iInter.2 fun _ => hVU i hx1⟩
  have hOj : ∀ i (O : A₀.left.Opens), O ≤ m₀ ⁻¹ᵁ V i → O ≤ j ⁻¹ᵁ ((pr ≫ m₀) ⁻¹ᵁ V i) := by
    intro i O hO
    rw [← hmj]; exact hO

  have hdec : ∀ i, ∃ ab : Γ(A₀.left, m₀ ⁻¹ᵁ V i) × Γ(A₀.left, m₀ ⁻¹ᵁ V i),
      rsT (w.s (c i, c i)).val ((pr ≫ m₀) ⁻¹ᵁ V i) = pbT pr ab.1 ((pr ≫ m₀) ⁻¹ᵁ V i) +
        constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ V i) DualNumber.eps * pbT pr ab.2 ((pr ≫ m₀) ⁻¹ᵁ V i) := by
    intro i
    obtain ⟨ab, hab, -⟩ := GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening k A₀.left B'.left A₀.hom B'.hom pr HP (m₀ ⁻¹ᵁ V i)
      (rsT (w.s (c i, c i)).val (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V i)))
    refine ⟨ab, ?_⟩
    rw [app_eq_pbT', app_eq_pbT'] at hab
    exact hab
  choose ab hab using hdec

  have hmod : ∀ i (O : A₀.left.Opens), O ≤ m₀ ⁻¹ᵁ V i →
      pbT j (rsT (w.s (c i, c i)).val ((pr ≫ m₀) ⁻¹ᵁ V i)) O = rsT (ab i).1 O := by
    intro i O hO
    have hle : (pr ≫ m₀) ⁻¹ᵁ V i ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V i) := le_rfl
    rw [hab i, pbT_add, pbT_mul, pbT_pbT' j pr hle (hOj i O hO), pbT_pbT' j pr hle (hOj i O hO), hj1,
      pbT_constFn _ _ (hOj i O hO), hj2, constFn_comp_spMap']
    rw [show (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 from rfl, constFn_zero', zero_mul, add_zero,
      pbT_id_le' hO]
  have hagr : ∀ i i', rsT (ab i).1 (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i') = rsT (ab i').1 (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i') := by
    intro i i'
    have hOC : m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i' ≤ j ⁻¹ᵁ (C i ⊓ C i') := by
      intro x hx
      exact ⟨(hWC i) (hOj i _ le_rfl hx.1), (hWC i') (hOj i' _ le_rfl hx.2)⟩
    rw [← hmod i _ inf_le_left, ← hmod i' _ inf_le_right,
      pbT_rsT j (hWC i) ((hOj i _ inf_le_left)), pbT_rsT j (hWC i') ((hOj i' _ inf_le_right))]
    have hr := congrArg (fun u : Γ(B'.left, C i ⊓ C i')ˣ => pbT j u.val (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i')) (hw (c i, c i) (c i', c i'))
    rw [val_res', pbT_rsT j inf_le_left hOC, Units.val_mul, pbT_mul, val_res', pbT_rsT j inf_le_right hOC] at hr
    rw [hr]
    have hg : pbT j ((LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).g (c i, c i) (c i', c i')).val
        (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i') = 1 := by
      exact pbT_div_g_pull P.L π₁ (pr ≫ m₀) j (c i) (c i') _ hOC hj12
    rw [hg, _root_.one_mul]
  have hunit : ∀ i, IsUnit (ab i).1 := by
    intro i
    have h1 := hmod i (m₀ ⁻¹ᵁ V i) le_rfl
    rw [rsT_self, pbT_rsT j (hWC i) (hOj i _ le_rfl)] at h1
    rw [← h1]
    exact isUnit_pbT j ((hOj i _ le_rfl).trans (j.preimage_mono (hWC i))) (w.s (c i, c i))
  have hcov : ⨆ i, m₀ ⁻¹ᵁ V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have : m₀ x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨t, htu, ht⟩ := exists_unit_glue (fun i => m₀ ⁻¹ᵁ V i) hcov (fun i => (ab i).1) hunit hagr
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb hm₀
  obtain ⟨a, ha⟩ := unit_eq_const A₀ hA₀ t htu
  refine ⟨a, fun i => (ab i).2, fun i => ?_⟩
  have hle : (pr ≫ m₀) ⁻¹ᵁ V i ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V i) := le_rfl
  rw [hab i, ← ht i, ha, rsT_constFn _ le_top, pbT_constFn _ _ hle, hprA, constFn_comp_spMap']

end GlobalTheory.UnitPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDeriva
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FormalDer

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)

theorem isLocalRing_dual (Ω : Type) [CommRing Ω] [IsLocalRing Ω] : IsLocalRing (DualNumber Ω) := by
  have : Nontrivial (DualNumber Ω) := (TrivSqZeroExt.inl_injective (R := Ω) (M := Ω)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self y.fst

theorem mem_pow_map {Ω : Type} [CommRing Ω] (K : Ideal Ω) (n : ℕ) (y : DualNumber Ω)
    (hy : y ∈ (K.map (algebraMap Ω (DualNumber Ω))) ^ n) : y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n := by
  rw [← Ideal.map_pow] at hy
  let S : Ideal (DualNumber Ω) :=
    { carrier := {y | y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n}
      add_mem' := fun ha hb => ⟨by simpa using add_mem ha.1 hb.1, by simpa using add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c y hy => ⟨by simpa using Ideal.mul_mem_left _ c.fst hy.1, by
        simpa [TrivSqZeroExt.snd_mul, smul_eq_mul, _root_.mul_comm] using
          add_mem (Ideal.mul_mem_left _ c.fst hy.2) (Ideal.mul_mem_left _ c.snd hy.1)⟩ }
  have : (K ^ n).map (algebraMap Ω (DualNumber Ω)) ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun r hr => ⟨by simpa [TrivSqZeroExt.algebraMap_eq_inl] using hr, by
      simp [TrivSqZeroExt.algebraMap_eq_inl]⟩
  exact this hy

theorem isHausdorff_dual {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (I : Ideal R)
    [h : IsHausdorff (I.map φ) Ω] :
    IsHausdorff (I.map ((algebraMap Ω (DualNumber Ω)).comp φ)) (DualNumber Ω) := by
  rw [← Ideal.map_map]
  refine ⟨fun y hy => ?_⟩
  have h' : ∀ n, y.fst ∈ (I.map φ) ^ n ∧ y.snd ∈ (I.map φ) ^ n := fun n => mem_pow_map _ n y (by
    have := hy n
    rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this)
  ext
  · exact h.haus y.fst fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).1
  · exact h.haus y.snd fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).2

theorem exists_tangent_lift {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) : ∃ u : epsR R ⟶ G, u.left = (tv v).left ∧ IsTangent u := by
  have h := CoeffWt.isGrpPullback_self G
  obtain ⟨u, e⟩ := PullbackSections.push_surj h (tv v)
  exact ⟨u, (Category.comp_id _).symm.trans (congrArg (fun q => q.left) e),
    (PullbackSections.isTangent_iff h _).2 (by rw [e]; exact PullbackSections.tv_mem _)⟩

theorem epsHom_comp {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (δ : Derivation ℤ Ω Ω)
    (hδφ : ∀ r, δ (φ r) = 0) :
    letI : Algebra R Ω := φ.toAlgebra
    (epsHom δ).comp φ = algebraMap R (DualNumber Ω) := by
  letI : Algebra R Ω := φ.toAlgebra
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · show (epsHom δ (φ r)).fst = (algebraMap R (DualNumber Ω) r).fst
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
    rfl
  · show (epsHom δ (φ r)).snd = (algebraMap R (DualNumber Ω) r).snd
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl', hδφ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH dd hdd v' hv' dd' hdd' Ω _ _ _ φ x δ hcomp hx hδφ hδ x' hx' hxx' a O f hO
  letI : Algebra R Ω := φ.toAlgebra
  have hε : (inr 1 : DualNumber Ω) * inr 1 = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
  haveI := isLocalRing_dual Ω
  haveI : IsHausdorff ((maximalIdeal R).map (algebraMap R (DualNumber Ω))) (DualNumber Ω) :=
    isHausdorff_dual φ (maximalIdeal R)
  let jη : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp)
  obtain ⟨u₀, hu₀, hut₀⟩ := exists_tangent_lift Y.H (vH a)
  obtain ⟨u₁, hu₁, hut₁⟩ := exists_tangent_lift t.G (v' a)
  have eu₀ : u₀ = jη ≫ tv (vH a) := Over.OverMorphism.ext (hu₀.trans (Category.id_comp _).symm)
  have eu₁ : u₁ = jη ≫ tv (v' a) := Over.OverMorphism.ext (hu₁.trans (Category.id_comp _).symm)
  let T : Over (Sp R) := Over.mk (spMap φ)
  let xt : T ⟶ Y.H := Over.homMk x hx
  let xt' : T ⟶ t.G := Over.homMk x' hx'
  let kz : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (algebraMap Ω (DualNumber Ω))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    rfl)
  let kε : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (epsHom (δ a))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (epsHom_comp φ (δ a) (hδφ a)))
  let kk := Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη
  let z : sp (R₀ := R) (DualNumber Ω) ⟶ Y.H := kz ≫ xt
  let z' : sp (R₀ := R) (DualNumber Ω) ⟶ t.G := kz ≫ xt'
  let yH := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₀) * z
  let yG := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₁) * z'

  have e₁ : yH = kε ≫ xt := by
    refine CoeffWt.eq_of_valR Y yH (kε ≫ xt) ⊤ (x (closedPoint Ω)) trivial fun V' _ hp => ?_
    have m : ⊤ ≤ x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of Ω) x hp).ge
    obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x _ m
    obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x _ m
    obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₀ hut₀ (hdd a) (inr 1 : DualNumber Ω) hε z _ a₁
    refine ⟨c₁, b₁, fun α g _ => ?_⟩
    refine (c₂ g).trans (Eq.trans ?_ (b₂ g).symm)
    show valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ g +
      inr 1 * valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ (dd a _ g) = _
    rw [a₂, a₂, hδ a _ g m]
    ext <;> simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have pz := hxx'.pull kz (Y.rep.1 _ _ kz xt)
  have pu := (hv' a).pull (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη)
    (Y.rep.1 _ _ (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη) (tv (vH a)))
  rw [Category.assoc, Category.assoc, ← eu₀, ← eu₁] at pu
  have pm := FormalPoint.IsPointOf.mul hG pu pz (Y.rep.2 _ _ _)
  have pε := hxx'.pull kε (Y.rep.1 _ _ kε xt)
  have e₂ : yG = kε ≫ xt' := by
    have pm' : FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (kε ≫ xt)) yG := by
      rw [← e₁]; exact pm
    exact FormalPoint.IsPointOf.unique pm' pε
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x' O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x' O hO
  obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₁ hut₁ (hdd' a) (inr 1 : DualNumber Ω) hε z' O a₁
  have hz : ∀ g, valR z'.left O g = algebraMap Ω (DualNumber Ω) (valR x' O g) := a₂
  have k : valR yG.left O f = valR (spMap (epsHom (δ a)) ≫ x') O f := by
    rw [e₂]
    rfl
  have k2 : algebraMap Ω (DualNumber Ω) (valR x' O f) +
      inr 1 * algebraMap Ω (DualNumber Ω) (valR x' O (dd' a O f)) = epsHom (δ a) (valR x' O f) := by
    rw [← hz, ← hz, ← c₂, k, b₂]
  have k3 := congrArg TrivSqZeroExt.snd k2
  simpa [epsHom, TrivSqZeroExt.algebraMap_eq_inl'] using k3

end GlobalTheory.Heat.FormalDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_least_vector_norm_le_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → qW W c.T.β ν ≤ qW W c.T.β χ) → ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ ≤ Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.PartLe.main | exact GlobalTheory.Poinc.PartLe.main | (intros; apply GlobalTheory.Poinc.PartLe.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_unique_least_vector_attains_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.GSumEx.main | exact GlobalTheory.Poinc.GSumEx.main | (intros; apply GlobalTheory.Poinc.GSumEx.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartsOverDividingThetaConstantIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (x : D.X.S.Gam) (j : D.X.S.J) (z' : D.X.M.Z), D.q z' = z₁ → D.X.S.ev x j / D.X.S.th (D.lab (GSum.base X₁ z₁)) ∈ D.X.M.O z' := by
  first | exact @GlobalTheory.Poinc.GSumInt.main | exact GlobalTheory.Poinc.GSumInt.main | (intros; apply GlobalTheory.Poinc.GSumInt.main <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSquareDeterminantComparisonIsAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilDet

theorem eq_zero_of_eigen {K B G Y N : Type} [Field K] [CommRing B] [IsDomain B] [Monoid G] [Fintype N]
    (κ : K →+* B) (χ : N → G →* B) (hχ : Function.Injective χ) (act : G → Y → Y) (F : N → Y → B)
    (hF : ∀ i v y, F i (act v y) = χ i v * F i y) (hne : ∀ i, ∃ y, F i y ≠ 0) (c : N → K)
    (h : ∀ y, ∑ i, κ (c i) * F i y = 0) : c = 0 := by
  funext i
  obtain ⟨y, hy⟩ := hne i
  have li := (linearIndependent_monoidHom G B).comp χ hχ
  have := Fintype.linearIndependent_iff.1 li (fun j => κ (c j) * F j y) (by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
    rw [← h (act v y)]
    exact Finset.sum_congr rfl fun j _ => by rw [hF]; ring) i
  exact κ.injective (((mul_eq_zero.1 this).resolve_right hy).trans (map_zero κ).symm)

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

theorem gs_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (f : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (cst f ⊤ a) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (V := ⊤) le_top trivial _).trans (gs_pull r f z ⊤ trivial _)

section Map

variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ)

theorem mul_comp_alMap {Z : Over (Sp R)} (a b : Z ⟶ Out.powObj x.P.A 4) (r : Fin 4) (ζ : Pt x) :
    (a * b) ≫ alMap x al r ζ = (a ≫ alMap x al r 1) * (b ≫ alMap x al r ζ) := by
  haveI := x.P.isAb.comm
  have e : ∀ (a : Z ⟶ Out.powObj x.P.A 4) (ζ : Pt x), a ≫ alMap x al r ζ =
      (∏ c, (a ≫ Out.powPr x.P.A c) ^ al r c) * (toUnit Z ≫ ζ) := fun a ζ => by
    simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
      GrpObj.comp_zpow, MonObj.comp_one, Fin.prod_univ_succ, Fin.prod_univ_zero, comp_toUnit_assoc]
  simp only [e, MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib, MonObj.comp_one, _root_.mul_one,
    _root_.mul_assoc]

def ker : Submonoid (𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) where
  carrier := {v | ∀ r, v ≫ alMap x al r 1 = 1}
  one_mem' := fun r => by
    haveI := x.P.isAb.comm
    have := mul_comp_alMap x al (1 : 𝟙_ (Over (Sp R)) ⟶ _) 1 r 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  mul_mem' := fun {a b} ha hb r => by rw [mul_comp_alMap, ha r, hb r, _root_.mul_one]

abbrev tr (v : 𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) : Out.powObj x.P.A 4 ⟶ Out.powObj x.P.A 4 :=
  (toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)

theorem tr_alMap (v : ker x al) (r : Fin 4) (ζ : Pt x) : tr x v.1 ≫ alMap x al r ζ = alMap x al r ζ := by
  rw [mul_comp_alMap, Category.assoc, v.2 r, MonObj.comp_one, _root_.one_mul, Category.id_comp]

theorem pt_tr (y v : 𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) : y ≫ tr x v = v * y := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

end Map

theorem exists_transl_ratio (laws : Out.Laws) {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))))
    (hw : w.IsGen) (hw' : w'.IsGen) (v : ker x al) :
    ∃ a : Γ(Sp R, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) (J), Good x.P.L z J →
      (val w (r ≫ (tr x v.1).left) z J * (val w' (r ≫ (tr x v.1).left) z J)⁻¹ *
        (val w r z J * (val w' r z J)⁻¹)⁻¹).val = gs (r ≫ (Out.powObj x.P.A 4).hom) z ⊤ a := by
  have hu := DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.invGen_isGen _ _ _ _ hw')
  obtain ⟨a, ha⟩ := exists_ratio x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, tr_alMap, zpow_neg,
        Finset.prod_inv_distrib, zpow_one, inv_inv]
      simp only [mul_inv, inv_inv, mul_mul_mul_comm _ _⁻¹, inv_mul_cancel])
    (Out.powObj x.P.A 4).hom (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2
    (DVR.pullGen_isGen _ _ _ _ hu (tr x v.1).left) hu
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have := ha Z r z J hJ
  rwa [val_pull hJ, val_mul hJ, val_mul hJ, val_inv, val_inv] at this

theorem exists_l2Val : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  intro laws K _ _ x m al b hm hal hb
  classical
  have hm0 : m ≠ 0 := fun h => hm (by rw [h, Nat.cast_zero])
  have hL := x.P.isLB
  obtain ⟨ξ, hξ, hk⟩ := GlobalTheory.T.exists_enum_ker_transpose_similitude_points laws K x m al hm hal
  obtain ⟨mu, hmu, hmuv⟩ := GlobalTheory.T.exists_normalised_iso_pullback_mul_by_m laws K x m
  choose w hw using fun I => GlobalTheory.SimilPull.exists_gen_similitude_pull laws K x m al (ξ I) hal (hk I)
  choose rho hrho using fun I => GlobalTheory.T.exists_normalising_unit_similitude_origin K x m al (ξ I) mu (w I) hm0 hal (hk I) hmu (hw I)
  choose s hs using fun I => GlobalTheory.T.exists_section_boxProduct_div_generator _ _ x.P.L hL (Fin 4) (Fin 4) _ _ (m : ℤ) x.th (w I) (hw I)
  choose Q hQ using fun I => GlobalTheory.T.boxProducts_basis_span_powObj_sections K x m _ b hb 4 (s I)
  have hdet : (Matrix.of Q).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcQ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨I₀, -⟩ := Function.ne_iff.1 hc
    refine hc ?_
    let S : Over (Sp K) := 𝟙_ _
    let T := Out.powObj x.P.A 4
    haveI : IsIntegral S.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of K)))
    haveI : Subsingleton S.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    let p : S.left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : S.left ⟶ x.P.A.left => exists_chart hL (χ p)
    replace hJ : Good x.P.L p J := hJ
    let ev : Γ(S.left, ⊤) →+* S.left.presheaf.stalk p := (S.left.presheaf.germ ⊤ p trivial).hom
    have hev : ∀ (y : S ⟶ T) a, gs (y.left ≫ T.hom) p ⊤ a = ev a := fun y a => by
      rw [Over.w y]
      exact gs_eq (𝟙 S.left) p ⊤ trivial a
    let κ : K →+* S.left.presheaf.stalk p := ev.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    choose a ha using fun I v => exists_transl_ratio laws x m al (ξ I₀) (ξ I) (w I₀) (w I) (hw I₀) (hw I) v
    let u : (Fin 4 → Fin (m ^ x.P.g)) → (S ⟶ T) → (S.left.presheaf.stalk p)ˣ := fun I y =>
      val (w I₀) y.left p J * (val (w I) y.left p J)⁻¹
    have hu : ∀ I (v : ker x al) (y : S ⟶ T), (u I (v.1 * y)).val = ev (a I v) * (u I y).val := fun I v y => by
      have := ha I v _ y.left p J hJ
      rw [hev, ← Over.comp_left, pt_tr] at this
      rw [← this, ← Units.val_mul, inv_mul_cancel_right]
    let χ : (Fin 4 → Fin (m ^ x.P.g)) → ker x al →* S.left.presheaf.stalk p := fun I =>
      { toFun := fun v => ev (a I v)
        map_one' := by
          have := hu I 1 1
          rw [Submonoid.coe_one, _root_.one_mul] at this
          exact (Units.mul_left_inj (u I 1)).1 (this.symm.trans (_root_.one_mul _).symm)
        map_mul' := fun v v' => by
          have := hu I (v * v') 1
          rw [Submonoid.coe_mul, _root_.mul_assoc, hu, hu, ← _root_.mul_assoc] at this
          exact ((Units.mul_left_inj (u I 1)).1 this).symm }
    have hχ : Function.Injective χ := fun I I' h => by
      by_contra hne
      obtain ⟨r, hr⟩ := hξ I I' hne p
      have e := GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant laws K x m al (ξ I) (ξ I') (w I) (w I') hm hal (hw I) (hw I') (fun v hv Z r z J hJ => by
        have e₁ : a I ⟨v, hv⟩ = a I' ⟨v, hv⟩ := fn_ext (X := S.left) fun y _ => by
          obtain rfl : y = p := Subsingleton.elim _ _
          exact (gs_eq (𝟙 S.left) p ⊤ trivial _).trans ((DFunLike.congr_fun h ⟨v, hv⟩).trans
            (gs_eq (𝟙 S.left) p ⊤ trivial _).symm)
        have e₂ := Units.ext ((ha I ⟨v, hv⟩ Z r z J hJ).trans (e₁ ▸ (ha I' ⟨v, hv⟩ Z r z J hJ).symm))
        have alg : ∀ {U : Type} [CommGroup U] (A B B' C D D' : U),
            A * B⁻¹ * (C * D⁻¹)⁻¹ = A * B'⁻¹ * (C * D'⁻¹)⁻¹ → B * D' = B' * D := fun A B B' C D D' h => by
          rw [mul_inv, mul_inv, inv_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj, mul_left_comm,
            mul_left_comm B'⁻¹, mul_right_inj, inv_mul_eq_iff_eq_mul] at h
          rw [h, mul_left_comm B', mul_inv_cancel_left]
        exact alg _ _ _ _ _ _ e₂)
      exact hr (by rw [e])
    let θ : (Fin 4 → Fin (m ^ x.P.g)) → (S ⟶ T) → S.left.presheaf.stalk p := fun I y =>
      ∏ r, gs (y.left ≫ (alMap x al r (ξ I r)).left) p _ (x.th.f (J (y.left ≫ (alMap x al r (ξ I r)).left)))
    refine eq_zero_of_eigen κ χ hχ (fun v y => v.1 * y) (fun I y => θ I y * (u I y).val) (fun I v y => ?_)
      (fun I => ?_) c (fun y => ?_)
    · have e : θ I (v.1 * y) = θ I y := Finset.prod_congr rfl fun r _ =>
        congrArg (fun ψ : S.left ⟶ x.P.A.left => gs ψ p _ (x.th.f (J ψ))) (by
          rw [← Over.comp_left, ← Over.comp_left, ← pt_tr, Category.assoc, tr_alMap])
      simp only [hu, e]
      exact mul_left_comm _ _ _
    · obtain ⟨y, hy⟩ := GlobalTheory.T.exists_point_thetaPullbacks_isUnit laws K x m al (ξ I) hm hal
      exact ⟨y, mul_ne_zero (Finset.prod_ne_zero_iff.2 fun r _ => (hy p J hJ r).ne_zero) (Units.ne_zero _)⟩
    · have e : ∀ I, θ I y * (u I y).val = (val (w I₀) y.left p J).val * ∑ I', κ (Q I I') *
          ∏ c, gs (y.left ≫ (Out.powPr x.P.A c).left) p _ ((b (I' c)).f (J (y.left ≫ (Out.powPr x.P.A c).left))) :=
        fun I => by
        have e₁ : θ I y = _ := hs I _ y.left p J hJ
        rw [e₁, hQ I _ y.left p J hJ, mul_right_comm, ← Units.val_mul, mul_comm (val (w I) y.left p J),
          inv_mul_cancel_right]
        refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
        rw [gs_cst, hev]
        rfl
      simp only [e, mul_left_comm _ (val (w I₀) y.left p J).val, ← Finset.mul_sum]
      refine mul_eq_zero_of_right _ ?_
      simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun I' _ => ?_
      rw [← Finset.sum_mul, ← map_sum, show ∑ I, c I * Q I I' = 0 from congrFun hcQ I', map_zero, zero_mul]
  refine ⟨Units.mk0 _ hdet ^ (2 * m ^ 2) * ∏ I, rho I ^ 2, ξ, mu, w, Matrix.of Q, rho, hξ, hk, hmu, hw,
    fun p J hJ => ⟨hmuv p J hJ, fun I => hrho I p J hJ⟩, fun I y J hJ => ?_, by simp⟩
  have e := hs I _ (𝟙 _) y J hJ
  rw [hQ I _ (𝟙 _) y J hJ] at e
  have i : ∀ (f : ∀ j, Γ(x.P.A.left, x.P.L.U j)) (ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left),
      gs (𝟙 _ ≫ ψ) y _ (f (J (𝟙 _ ≫ ψ))) = gs ψ y _ (f (J ψ)) := fun f ψ => by rw [Category.id_comp]
  exact (Finset.prod_congr rfl fun r _ => (i _ _).symm).trans (e.trans (congrArg _ (Finset.sum_congr rfl fun I' _ =>
    congrArg _ (Finset.prod_congr rfl fun c _ => i (b (I' c)).f _))))

end GlobalTheory.SimilDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyNormalExists

def constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f j := constFn p _ a * s.f j
  compat j k := by
    rw [map_mul, map_mul, ThetaOnto.res_constFn, ThetaOnto.res_constFn, s.compat j k]
    ring

theorem mem_nonzeroLocus_constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : L.Sec) {z : X} (hz : z ∈ Out.nonzeroLocus s) : z ∈ Out.nonzeroLocus (constMul p a s) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have hu : IsUnit (constFn p (L.U i) a) := (ha.map _).map _
  change z ∈ X.basicOpen (constFn p (L.U i) a * s.f i)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
  exact ⟨X.basicOpen_le _ hi, hi⟩

theorem isFn_constMul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a : ℂ) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsFn (constMul A.hom a s) (fun z => a * θ z) := by
  intro i z hz
  change valAt' _ _ (constFn A.hom (L.U i) a * s.f i) = _
  rw [valAt'_mul, valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz, h i z hz, _root_.mul_assoc]

theorem exists_normalAt_one (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) :
    ∃ th hth v hv, KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (M⁻¹ i)).exists
  refine ⟨constMul x.P.A.hom c⁻¹ x.th, fun s => ?_, v,
    (hb M⁻¹ v x.basis hv).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit), u, h₁, h₂, h₃, h₄, ?_, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, mem_nonzeroLocus_constMul _ (inv_ne_zero hc).isUnit _ hz'⟩
  · have := isFn_constMul u c⁻¹ h₅
    simpa only [inv_mul_cancel_left₀ hc, _root_.one_mul] using this
  · have := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (M⁻¹ i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, M⁻¹ i j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) i := by
      rw [← Matrix.nonsing_inv_mul M hM.isUnit]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    exact this

theorem exists_normalAt :
    ThetaUnifAV → ∀ x : KeyIn ℂ, (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ M a b c) ∧ ∃ (th : x.P.L.Sec) (hth : _) (v : _) (hv : _) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ GlobalTheory.KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  intro hU x
  obtain ⟨u, Hm, χ, -, hA, hR, hd, -⟩ := hU x.P x.rig x.rig_gen
  choose W hW using fun i => (hd _ (x.basis.1 i)).exists
  obtain ⟨θ, hθ⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨Fd, hF⟩ := KeyPow.exists_isAddFundamentalDomain u
  obtain ⟨u', τ, M, a, b, c, h₁, h₂, ha, hb, h₃, h₄, hc, h₅, hM, h₆, -⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd _ _ hA hR hθ hW hF rfl rfl
  have hN : KeyPow.NormalAt x τ M a b c := ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨th, hth, v, hv, h⟩ := exists_normalAt_one x hc hM hN
  exact ⟨⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hM, hN⟩, th, hth, v, hv, τ, a, b, ⟨ha, hb⟩, h⟩

end GlobalTheory.KeyNormalExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.RigSymSubring

open GlobalTheory.CechPic

theorem pic_descends (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S)
    (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (c d : Pic X₀)
    (H : IsPullback π f f₀ (spMap R₀.subtype)) (e : pull π c = pull π d) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀),
        IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → pull π₁ c = pull π₁ d := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨F, hF⟩ := GlobalTheory.T.lineBundleIso_descends_to_subring_of_finset S R₀ X X₀ f f₀ π M N H hM hN
    ((cls_eq_iff (pull_isLB hM π) (pull_isLB hN π)).1 e)
  exact ⟨F, fun R₁ h hR X₁ f₁ π₁ H₁ =>
    (cls_eq_iff (pull_isLB hM π₁) (pull_isLB hN π₁)).2 (hF R₁ h hR X₁ f₁ π₁ H₁)⟩

variable {T : Scheme.{0}} {A : Over T} [GrpObj A] {L : LB A.left}

theorem rigidified_iff (hL : L.IsLB) : Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem gen_iff (hL : L.IsLB) {Y : Scheme.{0}} (r : Y ⟶ A.left) :
    (∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![r ≫ (GrpObj.inv : A ⟶ A).left, r] ![1, -1]), t.IsGen) ↔
      pull r (pull (GrpObj.inv : A ⟶ A).left (cls L hL)) = pull r (cls L hL) := by
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two, ← pull_comp]
  simp [← sub_eq_add_neg, sub_eq_zero]

theorem sym_of_cls (hL : L.IsLB) (e : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) : Out.Sym A L :=
  fun _ => ⟨⊤, trivial, (gen_iff hL _).2 (by rw [e])⟩

theorem cls_of_sym {S : Type} [CommRing S] [IsLocalRing S] {A : Over (Sp S)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, ht⟩ := hs (IsLocalRing.closedPoint S)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have i : ∀ c : Pic A.left, pull (inv (A.hom ⁻¹ᵁ ⊤).ι (I := inferInstanceAs (IsIso A.left.topIso.hom)))
      (pull (A.hom ⁻¹ᵁ ⊤).ι c) = c := fun c => by rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  exact (i _).symm.trans ((congrArg _ ((gen_iff hL _).1 ht)).trans (i _))

end GlobalTheory.RigSymSubring

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.RigSymSubring

theorem rigidified_sym_descend_to_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.Rigidified A₁ (L₀.pull π) ∧ Out.Sym A₁ (L₀.pull π) := by
  classical
  intro S _ _ R₀ P A₀ _ φ L₀ hA hL H hw
  have := hA.proper
  have hc : cls P.L P.isLB = pull φ (cls L₀ hL) := (cls_eq_iff P.isLB (pull_isLB hL φ)).2 hw
  have e₁ : pull (spMap R₀.subtype) (pull (X := A₀.left) (Y := Sp R₀) (eSec A₀) (cls L₀ hL)) =
      pull (spMap R₀.subtype) 0 := by
    have h₁ := (rigidified_iff P.isLB).1 P.rigid
    rw [hc, ← pull_comp, PolBaseChange.eSec_comm H] at h₁
    exact (pull_comp _ _ _).symm.trans (h₁.trans (map_zero _).symm)
  have e₂ : pull φ (pull (GrpObj.inv : A₀ ⟶ A₀).left (cls L₀ hL)) = pull φ (cls L₀ hL) := by
    have h₂ := cls_of_sym P.isLB P.sym
    rwa [hc, ← pull_comp, PolBaseChange.inv_comm H, pull_comp] at h₂
  obtain ⟨F₁, h₁⟩ := pic_descends S R₀ (Sp S) (Sp R₀) (𝟙 _) (𝟙 _) (spMap R₀.subtype) _ _
    (IsPullback.of_vert_isIso ⟨by simp⟩) e₁
  obtain ⟨F₂, h₂⟩ := pic_descends S R₀ _ _ P.A.hom A₀.hom φ _ _ H.1 e₂
  refine ⟨F₁ ∪ F₂, fun R₁ h hF A₁ _ π H₁ => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hF
  have a := h₁ R₁ h hF.1 (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h)) (IsPullback.of_vert_isIso ⟨by simp⟩)
  have b := h₂ R₁ h hF.2 _ A₁.hom π H₁.1
  refine ⟨(rigidified_iff (pull_isLB hL π)).2 ?_, sym_of_cls (pull_isLB hL π) ?_⟩
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.eSec_comm H₁]
    exact (pull_comp _ _ _).trans (a.trans (map_zero _))
  · rw [cls_pull hL, ← pull_comp, PolBaseChange.inv_comm H₁, pull_comp, b]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyComp

theorem stalk_of_appLE_eq {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (s : L.Sec)
    (s' : L'.Sec) (h : ∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun _ hy => mem_pull.1 hy.1
  have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have e := congrArg (gs r z _) (h (fun _ => j) k hle)
  refine (gs_appLE F _ _ hle r z hy _).symm.trans (e.trans ?_)
  rw [gs_mul _ z _ hy, gs_res _ z _ hy]
  exact congrArg (· * _) (gs_unit _ z _ hy _)

end GlobalTheory.KeyComp

namespace GlobalTheory

theorem keyPB_trans : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R') (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x' f' → KeyPB x'' x (f'.comp f) := by
  intro R R' R'' _ _ _ x x' x'' f f' H H'
  obtain ⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

end GlobalTheory
end
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusPullOn
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyNear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X Y : Scheme.{0}} {L : LB X}

theorem res_appLE (φ : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (e : V ≤ φ ⁻¹ᵁ U) (h : V' ≤ V) (s : Γ(X, U)) :
    resG Y h ((φ.appLE U V e).hom s) = (φ.appLE U V' (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map φ e (homOfLE h).op]; rfl

theorem appLE_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : U' ≤ U) (e : V ≤ φ ⁻¹ᵁ U') (s : Γ(X, U)) :
    (φ.appLE U' V e).hom (resG X h s) = (φ.appLE U V (e.trans (φ.preimage_mono h))).hom s := by
  rw [← Scheme.Hom.map_appLE φ e (homOfLE h).op]; rfl

def pullOn (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W) (θ : ∀ i, Γ(X, W ⊓ L.U i)) (hθ : θ ∈ secOn L W) :
    (L.pull φ).Sec where
  f j := (φ.appLE (W ⊓ L.U (j PUnit.unit)) ((L.pull φ).U j)
    (fun y hy => ⟨hW y, LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit hy⟩)).hom (θ _)
  compat i j := by
    have e : (L.pull φ).U i ⊓ (L.pull φ).U j ≤ φ ⁻¹ᵁ (W ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      fun y hy => ⟨⟨hW y, LB.wchart_le L (fun _ : PUnit => φ) i PUnit.unit hy.1⟩,
        LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit hy.2⟩
    have h := congrArg (φ.appLE _ _ e).hom (hθ (i PUnit.unit) (j PUnit.unit))
    rw [map_mul, appLE_res, appLE_res, appLE_res] at h
    refine (res_appLE φ _ _ _).trans (h.trans ?_)
    refine congrArg₂ (· * ·) ?_ (res_appLE φ _ _ _).symm
    have e₁ : ∀ {G : Type} [CommGroup G] (a : G), a = ∏ _k : PUnit.{1}, a ^ (1 : ℤ) := fun a => by simp
    exact congrArg Units.val (e₁ (res (e.trans (φ.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
      (pullU φ _ (L.g (i PUnit.unit) (j PUnit.unit)))))

theorem mem_nonzeroLocus_pullOn (φ : Y ⟶ X) {W : X.Opens} (hW : ∀ y, φ y ∈ W) (θ : ∀ i, Γ(X, W ⊓ L.U i))
    (hθ : θ ∈ secOn L W) {y : Y} {i : L.ι} (hy : φ y ∈ X.basicOpen (θ i)) :
    y ∈ Out.nonzeroLocus (pullOn φ hW θ hθ) := by
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  exact (Scheme.basicOpen_appLE φ _ _ _ (θ i)).ge ⟨mem_pull.2 (X.basicOpen_le _ hy).2, hy⟩

end Pull

open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

theorem main : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)), 1 ≤ P.g → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ r) → ∃ (y : KeyIn R') (π : y.P.A.left ⟶ P.A.left), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap ρ) π ∧ LBIso y.P.L (P.L.pull π) := by
  intro hL R _ _ P hg p
  obtain ⟨V, θ, hpV, hθ, hne⟩ := SecFamily.exists_secOn_nonvanishing hL (Sp R) P p
  have c₁ : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨r₁, hr₁, v, hv⟩ := LieLoc.lie_locally_free R P.A P.g P.smoothDim p
  obtain ⟨_, ⟨r₂, rfl⟩, hr₂, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) (u := V.1) hpV V.2
  refine ⟨r₁ * r₂, fun h => (p.2.mem_or_mem h).elim hr₁ hr₂, fun R' _ f hf => ?_⟩
  rw [map_mul] at hf
  have u₁ := isUnit_of_mul_isUnit_left hf
  have u₂ := isUnit_of_mul_isUnit_right hf
  have hV : ∀ s : Sp R', spMap f s ∈ V := fun s => hsub (show f r₂ ∉ s.asIdeal from fun h =>
    s.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h u₂))
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨rig, hrig⟩ := P'.rigid
  have hW : ∀ y, φ y ∈ P.A.hom ⁻¹ᵁ V := fun y => by
    have e : P.A.hom (φ y) = spMap f (P'.A.hom y) := congrArg (fun g => g y) h.1.w
    change P.A.hom (φ y) ∈ V
    rw [e]
    exact hV _
  let f' : Localization.Away r₁ →+* R' := IsLocalization.Away.lift r₁ u₁
  have hf' : spMap f' ≫ spMap (algebraMap R (Localization.Away r₁)) = spMap f := by
    rw [← IsLocalization.Away.lift_comp (S := Localization.Away r₁) r₁ u₁]
    exact (Spec.map_comp _ _).symm
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap R (Localization.Away r₁)))
  have w₁ : φ ≫ P.A.hom = (P'.A.hom ≫ spMap f') ≫ spMap (algebraMap R (Localization.Away r₁)) := by
    rw [Category.assoc, hf']; exact h.1.w
  have h₂ := IsGrpPullback.cancel h₁ (h.congr hf'.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  have a₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap R (Localization.Away r₁))) P.A P.isAb
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have c₃ := a₁.comm
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ R' f' _ P'.A _ h₂ a₁.smooth P.g v hv
  refine ⟨⟨P', hg, rig, hrig, pullOn φ hW θ hθ, fun s => ?_, v', hb'⟩, φ, rfl, h, idIso _, idIso_isGen hL'⟩
  obtain ⟨z, i, hz, hz'⟩ := hne _ (hV s)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  exact ⟨y, hy, mem_nonzeroLocus_pullOn φ hW θ hθ hz'⟩

end GlobalTheory.KeyNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyRow

theorem comb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (ψ : T'.left ⟶ T.left)
    (hψ : ψ ≫ T.hom = T'.hom ≫ f) {n : ℕ} (p : Fin n → (T ⟶ G)) (p' : Fin n → (T' ⟶ G'))
    (hp : ∀ c, (p' c).left ≫ φ = ψ ≫ (p c).left) (a : Fin n → ℤ) (ξ : 𝟙_ (Over S) ⟶ G) (ξ' : 𝟙_ (Over S') ⟶ G')
    (hξ : ξ'.left ≫ φ = f ≫ ξ.left) :
    ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')).left ≫ φ =
      ψ ≫ ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)).left := by
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk ψ hψ
  have e₁ : ∀ c, pushHom h T' (p' c) = preHom U (p c) := fun c => Over.OverMorphism.ext (hp c)
  have t : ∀ {B : Scheme.{0}} (V : Over B), (toUnit V).left = V.hom := fun V =>
    (Category.comp_id _).symm.trans (Over.w (toUnit V))
  have e₂ : pushHom h T' (toUnit _ ≫ ξ') = preHom U (toUnit _ ≫ ξ) := Over.OverMorphism.ext (by
    show ((toUnit T').left ≫ ξ'.left) ≫ φ = ψ ≫ (toUnit T).left ≫ ξ.left
    rw [Category.assoc, hξ, t, t]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ξ.left) hψ.symm).trans (Category.assoc _ _ _)))
  have e : pushHom h T' ((List.ofFn fun c => p' c ^ a c).prod * (toUnit _ ≫ ξ')) =
      preHom U ((List.ofFn fun c => p c ^ a c).prod * (toUnit _ ≫ ξ)) := by
    rw [map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, e₂]
    congr 3
    funext c
    simp only [Function.comp_apply, map_zpow, e₁]
  exact congrArg (fun z => z.left) e

theorem cancel_units {A K κ : Type} [CommRing A] [Fintype K] [Fintype κ] [DecidableEq κ] {N m : ℕ} (s : K → Aˣ)
    (t : κ → Aˣ) (v : Aˣ) (x : K → A) (c : (κ → Fin N) → A) (y : κ → Fin N → A)
    (h : ∏ r, (s r ^ 1).val * x r = (((∏ r, s r ^ (1 : ℤ)) * ∏ k, t k ^ (-(m : ℤ))) * v).val *
      ∑ I, c I * ∏ k, (t k ^ m).val * y k (I k)) :
    ∏ r, x r = v.val * ∑ I, c I * ∏ k, y k (I k) := by
  simp only [pow_one, zpow_one, zpow_neg, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    ← Units.coe_prod, mul_left_comm _ (∏ k, t k ^ m).val, ← Finset.mul_sum] at h
  refine (Units.mul_right_inj (∏ r, s r)).1 (h.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_comm (∏ k, t k ^ m), mul_right_comm, inv_mul_cancel_right]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  rintro R R' _ _ x x' f φ u m N al b b' ξ ξ' w q ⟨he, hg, F, hφ, hu, -, hth, -⟩ hb hξ hw H
  obtain ⟨ψ, hψ, hc⟩ := KeyPow.exists_isGrpPullback_pow hφ (Out.powIsPowGrp x.P.A 4) (Out.powIsPowGrp x'.P.A 4)
  have hc' : ∀ c : Fin 4, (Out.powPr x'.P.A c).left ≫ φ = ψ ≫ (Out.powPr x.P.A c).left := hc
  have ha : ∀ r, (alMap x' al r (ξ' r)).left ≫ φ = ψ ≫ (alMap x al r (ξ r)).left := fun r =>
    comb_push hφ ψ hψ.1.w _ _ hc' (al r) (ξ r) (ξ' r) (hξ r)
  obtain ⟨w', hw', P⟩ := H1.exists_gen_move x.P.isLB x'.P.isLB u ((isGen_iff u).1 hu) _
    (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) _ ψ
    (by rintro (r | c); exacts [ha r, hc' c]) w hw
  refine ⟨w', hw', fun Z ρ z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z ⟶ x.P.A.left => exists_chart x.P.isLB (χ z)
  have ha' : ∀ r, (ρ ≫ ψ) ≫ (alMap x al r (ξ r)).left = (ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, ha]
  have hc'' : ∀ c : Fin 4, (ρ ≫ ψ) ≫ (Out.powPr x.P.A c).left = (ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ := fun r => by
    rw [Category.assoc, Category.assoc, hc']
  have E := H Z (ρ ≫ ψ) z J hJ
  have hv := (val_of w (ρ ≫ ψ) z J (fun k => J ((ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k) ≫ φ)) (by rintro (r | c); exacts [congrArg J (ha' r), congrArg J (hc'' c)])).trans
    (P Z ρ z _ (fun k => J' (ρ ≫ Sum.elim (fun r => (alMap x' al r (ξ' r)).left)
    (fun c => (Out.powPr x'.P.A c).left) k)) (fun k => hJ _) (fun k => hJ' _))
  rw [Fintype.prod_sum_type] at hv
  have hth' : KeyVia.Via u 1 x'.th.f x.th.f := fun j i h => (hth j i h).trans (by rw [pow_one])
  have hq : ∀ a : R, gs (ρ ≫ ψ) z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ a) =
      gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f a)) := fun a =>
    (gs_appLE ψ ⊤ ⊤ le_top ρ z trivial _).symm.trans
      (congrArg (gs ρ z ⊤) (KeyVia.appLE_cst f _ _ hψ.1.w le_top a))
  rw [hv] at E
  refine cancel_units (m := m)
    (fun r => gw u (ρ ≫ (alMap x' al r (ξ' r)).left) z (J ((ρ ≫ (alMap x' al r (ξ' r)).left) ≫ φ))
      (J' (ρ ≫ (alMap x' al r (ξ' r)).left)))
    (fun c => gw u (ρ ≫ (Out.powPr x'.P.A c).left) z (J ((ρ ≫ (Out.powPr x'.P.A c).left) ≫ φ))
      (J' (ρ ≫ (Out.powPr x'.P.A c).left))) _ _ _
    (fun c k => gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J' (ρ ≫ (Out.powPr x'.P.A c).left)))
      ((b' k).f (J' (ρ ≫ (Out.powPr x'.P.A c).left)))) ?_
  refine Eq.trans (Finset.prod_congr rfl fun r _ => ?_) (E.trans (congrArg₂ (· * ·) rfl
    (Finset.sum_congr rfl fun I _ => congrArg₂ (· * ·) (hq _) (Finset.prod_congr rfl fun c _ => ?_))))
  · rw [ha']
    exact (KeyBasis.via_val hth' _ z (hJ _) (hJ' _)).symm
  · rw [hc'']
    exact KeyBasis.via_val (w := u) (hb (I c)) _ z (hJ _) (hJ' _)

end GlobalTheory.KeyRow
end
end


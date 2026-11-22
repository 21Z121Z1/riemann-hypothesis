import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChainVal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GtTors.base_pow {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) : g.b ^ k = 1 := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => h₀.1
    | succ i ih =>
      exact fun hi => (hs ⟨i, by omega⟩).1.trans ((congrArg (· * g.b) (ih (by omega))).trans (pow_succ _ _).symm)
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [← key k (Nat.lt_succ_self k), hl']; exact hz.1

theorem GtTors.chain_val {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) {T : Over (Spec (CommRingCat.of R))}
    (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    1 * cubN (th D z J) k 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hz.2 mu) σ.left).trans (val_one _)).symm rfl

theorem GtTors.val_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (ρ ≫ fst _ _).left z J :=
  (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).2 u hu hc T ρ z J hJ

theorem val_delta (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul])
    (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (pullGen_isGen _ _ _ _ hu _) (fun U _ h => by
      have p₃ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
      have p₄ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
      rw [z₂, _root_.mul_one] at p₃
      rw [z₃] at p₄
      simp only [Over.comp_left, Category.assoc] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)) ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  rw [← trF_eq] at H
  exact H.2 u hu (corr_of_val D.P.isLB fun _ _ _ => rfl) T ρ z J hJ

theorem phi_comm : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (g : GtPtF D F), GtTors D N g → ∀ (α mu : D.X) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (p : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (p' : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 (α + N • mu) g.b) (DegPre.deltaε N))), w.IsGen → u.IsGen → p.IsGen → p'.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p' (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s (α + N • mu)) w) → ∀ z J, Good D.P.L z J → val p' (𝟙 _) z J * val u (DegPre.trPt D F g.b).left z J = val u (𝟙 _) z J * val p (DegPre.trF D F mu).left z J) := by
  intro hG R _ _ D F _ _ k g hg α mu w u p p' hw hu hp hp' hc hc' y J hJ
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hm : fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D _ mu := comp_cP D _ mu
  have hy : (fst (TF (R := R) F) D.P.A ≫ g.b) ^ k = 1 :=
    (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _).symm.trans
      ((congrArg (preHom (fst (TF (R := R) F) D.P.A)) hg.base_pow).trans (map_one _))
  have t₁ := gt_nsmul (fst (TF (R := R) F) D.P.A) hJ g α mu k
  have t₃ := hg.chain_val (fst (TF (R := R) F) D.P.A) hJ mu
  have key := C.comm k _ _ _ (DegPre.prB D F) _ _ _ 1 1 1 t₁ (by rw [hy, C.face₂]) t₃
  have e₁ := hg.val_phi hG w hw (α + k • mu) p' hp' hc' _ (𝟙 _) y J hJ
  have e₂ := hg.val_phi hG w hw α p hp hc _ (DegPre.trPt D F (cP D _ mu)) y J hJ
  have e₃ := val_delta hG k α mu u hu _ (𝟙 _) y J hJ
  have e₄ := val_delta hG k α mu u hu _ (DegPre.trPt D F g.b) y J hJ
  rw [Category.id_comp, Over.id_left, uVal_id, val_mul hJ, cPoint_add, cPoint_nsmul] at e₁
  rw [tr_fst, uVal_tr, val_mul hJ, hm] at e₂
  rw [Category.id_comp, Over.id_left, uVal_id, hm] at e₃
  rw [tr_fst, uVal_tr, hm] at e₄
  rw [hy, _root_.mul_one (cP D _ α)] at key
  refine (congrArg₂ (· * ·) e₁ e₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃
    ((congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => val p q.left y J) (trF_eq D F mu)).trans e₂)).symm)
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key' ⊢
  linear_combination (norm := abel) key'

end GlobalTheory.UU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqClosedPointOfNotMemRange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericExt

universe u

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem exists_hom_specStalk {W Y T X : Scheme.{u}} (j : W ⟶ Y) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [X.IsSeparated] (F : W ⟶ X) (g' : T ⟶ Y) [Flat g'] (g : T ⟶ X)
    (H : ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) (p : T) :
    ∃ φ : Spec (Y.presheaf.stalk (g' p)) ⟶ X, ∀ (Z : Scheme.{u})
      (ρ : Z ⟶ Spec (Y.presheaf.stalk (g' p))) (r : Z ⟶ W),
      r ≫ j = ρ ≫ Y.fromSpecStalk (g' p) → r ≫ F = ρ ≫ φ := by
  let h := Spec.map (g'.stalkMap p)
  obtain ⟨h₁, h₂⟩ : Flat h ∧ Surjective h :=
    (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)
  have hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g' :=
    Scheme.SpecMap_stalkMap_fromSpecStalk g'
  have := flat_fromSpecStalk Y (g' p)
  have key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g := by
    let q := pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)
    have hq : Flat q := inferInstance
    refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_
      (terminal.hom_ext _ _)
    have e₁ := H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]; simp only [q, Category.assoc, hh])
    have e₂ := H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]
      simp only [q, Category.assoc, ← hh, pullback.condition_assoc])
    simpa only [Category.assoc] using e₁.symm.trans e₂
  let φ := EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hφ : h ≫ φ = T.fromSpecStalk p ≫ g := EffectiveEpi.fac _ _ _
  refine ⟨φ, fun Z ρ r hr => ?_⟩
  rw [← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]
  have := H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by
    rw [Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])
  simpa only [Category.assoc] using this

theorem exists_extension {W Y X S : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j] [IsIntegral Y] [S.IsSeparated] (sY : Y ⟶ S) (sX : X ⟶ S) [IsSeparated sX]
    [LocallyOfFiniteType sX] (F : W ⟶ X) (hF : F ≫ sX = j ≫ sY)
    (H : ∀ y : Y, y ∉ Set.range j → ∃ (T : Scheme.{u}) (g' : T ⟶ Y) (g : T ⟶ X), Flat g' ∧ y ∈ Set.range g' ∧
      ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) :
    ∃ ψ : Y ⟶ X, j ≫ ψ = F ∧ ψ ≫ sX = sY := by
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  let e₀ := Y.fromSpecStalk (genericPoint Y)
  have : IsDominant e₀ := isDominant_fromSpecStalk_genericPoint Y
  have hr : Set.range e₀ ⊆ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    intro z hz
    have hg : genericPoint Y ∈ Set.range j :=
      (genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2
        (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)
    exact Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg
  let e := IsOpenImmersion.lift j e₀ hr
  have he : e ≫ j = e₀ := IsOpenImmersion.lift_fac _ _ _
  have loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X)
      (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U),
      y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F := by
    intro y
    by_cases hy : y ∈ Set.range j
    · exact ⟨W, j, inferInstance, F, e, hy, he, rfl⟩
    obtain ⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩ := H y hy
    obtain ⟨φ, hφ⟩ := exists_hom_specStalk j F g' g hT p
    have := flat_fromSpecStalk Y (g' p)
    have hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY := by
      refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j)
        (terminal.from S) ?_ (terminal.hom_ext _ _)
      rw [← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]
    obtain ⟨U, hU, ψ, h₁, -⟩ := spread_out_of_isGermInjective' sY sX φ hover
    let m := Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))
    have hm : m ≫ Y.fromSpecStalk (g' p) = e₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    refine ⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]
    · rw [Category.assoc, ← h₁]
      exact (hφ _ m e (he.trans hm.symm)).symm
  choose U k hk ψ l hy hl hψ using loc
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk
  have hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b := by
    intro a b
    let m := pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)
    have : IsReduced (pullback (k a) (k b)) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)
    have : IsDominant (m ≫ pullback.fst _ _ ≫ k a) := by
      rw [pullback.lift_fst_assoc, hl]
      infer_instance
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)
    refine ext_of_isDominant m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]
  have hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a := fun a => 𝒰.ι_glueMorphisms ψ hc a
  have h1 : j ≫ 𝒰.glueMorphisms ψ hc = F := by
    have : IsReduced W := isReduced_of_isOpenImmersion j
    have : IsDominant (e ≫ j) := by rw [he]; infer_instance
    have : IsDominant e := .of_comp_of_isOpenImmersion e j
    refine ext_of_isDominant e ?_
    rw [reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]
  refine ⟨_, h1, ext_of_isDominant j ?_⟩
  rw [reassoc_of% h1, hF]

theorem isOpenImmersion_jK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion (jK R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem eq_closedPoint_of_not_mem_range (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : Spec (CommRingCat.of R)) (hs : s ∉ Set.range (jK R)) : s = IsLocalRing.closedPoint R := by
  by_cases h : s.asIdeal = ⊥
  · refine (hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X' X : Over (Spec (CommRingCat.of R))) [Flat X'.hom] [IsIntegral X'.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] (f : (Over.pullback (jK R)).obj X' ⟶ (Over.pullback (jK R)).obj X), (∀ x : X'.left, X'.hom x = IsLocalRing.closedPoint R → ∃ (T : Scheme.{0}) (g' : T ⟶ X'.left) (g : T ⟶ X.left), Flat g' ∧ x ∈ Set.range g' ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj X').left), r ≫ pullback.fst X'.hom (jK R) = ρ ≫ g' → r ≫ f.left ≫ pullback.fst X.hom (jK R) = ρ ≫ g) → ∃ ψ : X' ⟶ X, (Over.pullback (jK R)).map ψ = f := by
  intro R _ _ _ X' X _ _ _ _ f H
  have := isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst X'.hom (jK R)) := inferInstance
  have hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R) := Over.w f
  obtain ⟨ψ, h₁, h₂⟩ := exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom
    (f.left ≫ pullback.fst X.hom (jK R))
    (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1)
    (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by
      rw [Scheme.Pullback.range_fst]; exact h)))
  refine ⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (pullback.lift_fst _ _ _).trans h₁
  · exact (Over.w _).trans hf.symm

end GlobalTheory.GenericExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open TWM TWO

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem comp_generic_injective :
    Function.Injective fun q : (TO hϖ hv).left ⟶ D.toPre.P.A.left => (ιS hϖ hv).left ≫ q := fun f g h => by
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have e : f ≫ D.toPre.P.A.hom = g ≫ D.toPre.P.A.hom := by
    obtain ⟨a, ha⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (f ≫ D.toPre.P.A.hom)
    obtain ⟨b, hb⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (g ≫ D.toPre.P.A.hom)
    have e₁ : a ≫ CommRingCat.ofHom (algebraMap (Ov v) F) = b ≫ CommRingCat.ofHom (algebraMap (Ov v) F) :=
      Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_comp, ha, hb]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toPre.P.A.hom) h).trans (Category.assoc _ _ _)))
    have e₂ : a = b := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x))
    exact ha.symm.trans ((congrArg Spec.map e₂).trans hb)
  have hU : ValuativeCriterion.Uniqueness D.toPre.P.A.hom := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq D.toPre.P.A.hom :=
    { R := Ov v, K := F, i₁ := (ιS hϖ hv).left ≫ f, i₂ := f ≫ D.toPre.P.A.hom, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((hU S).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

theorem exists_unit_const {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      ∏ k, h ((ιS hϖ hv).left ≫ φ k) ^ ε k = 1) :
    ∃ u : F, v u = 0 ∧ ∀ z J, Good D.toPre.P.L z J → (val t (ιS hϖ hv).left z J).val = cst F z u := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TO hϖ hv).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.toPre.P.L D.toPre.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 t ht
    (fun U _ h => by
      have := hf U (Function.extend (fun q => (ιS hϖ hv).left ≫ q) h 1)
      simpa only [(comp_generic_injective hϖ hv).extend_apply] using this)
  have hu : IsUnit a := (TO hϖ hv).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.toPre.P.isLB y
    have q := ha _ (𝟙 _) y J hJ
    rw [Category.comp_id] at q
    exact (congrArg IsUnit (q.trans (gs_eq (𝟙 _) y ⊤ trivial a))).mp (Units.isUnit _)
  refine ⟨ιr (v := v) a, v_unit v (hu.map (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom).unit, fun z J hJ => ?_⟩
  rw [ha _ _ z J hJ, Category.comp_id, ← Category.id_comp (ιS hϖ hv).left]
  exact (gs_pull (𝟙 _) (ιS hϖ hv).left z ⊤ trivial a).symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap _ a))

theorem cst_gF {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (c : V) :
    Geo.Tor.cst ((ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom) z c = gs ρ z ⊤ (gF D.toPre F (algVF c)) := by
  have e : (ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom =
      (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
    rw [← TF_hom, Category.assoc, Category.assoc, Over.w, Over.w]
  rw [e]
  refine (gs_pull _ _ z ⊤ trivial _).symm.trans (Eq.trans ?_ (gs_pull ρ _ z ⊤ trivial _).symm)
  refine congrArg (gs _ z ⊤) ((appTop_specMap _ _).trans ?_)
  simp

include hϖ hv in

theorem vge_iff {k : ℕ} {χ : D.toPre.X} (b : D.toPre.SecB k χ)
    (hb : ∀ σ : D.toPre.SecB k χ, ∃ c : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval σ r z J = Geo.Tor.cst (r ≫ D.toPre.P.A.hom) z c * sval b r z J)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) {r : ℚ} (hs : VGe D F v k χ s r) :
    ∃ a : F, (r : WithTop ℚ) ≤ v a ∧ (∀ r' : ℚ, (r' : WithTop ℚ) ≤ v a → VGe D F v k χ s r') ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  choose c hc using fun i => hb (σ i)
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = gs ρ z ⊤ (gF D.toPre F (∑ i, a i * algVF (c i))) *
        sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) ρ z hJ, map_sum,
      SectionScalarValuation.gs_sum ρ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← SectionScalarValuation.secScal_sval (hscal i) ρ z hJ, hc i _ _ z J hJ, cst_gF, map_mul, gs_mul ρ z ⊤ trivial, _root_.mul_assoc]
  refine ⟨∑ i, a i * algVF (c i), AddValuation.map_le_sum v fun i _ => ?_, fun r' hr' => ?_, key⟩
  · rw [AddValuation.map_mul]
    exact le_add_of_le_of_nonneg (hva i) (v_of_V v hϖ hv (c i)).1
  · let bF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)) :=
      VVRank.pullTo b (DegPre.prB D.toPre F).left fun i => (GC.famφ_eq _ _ _ i).symm
    refine ⟨1, fun _ => _, fun _ => b, fun _ => bF, fun _ => SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
      (VVRank.sval_pullTo _ _ _ _ y hJ).symm, fun _ => hr', fun j => ?_⟩
    rw [Fin.sum_univ_one]
    refine sec_ext_val hL (s' := SecOps.secScale (gF D.toPre F _) bF) (fun y J hJ => ?_) j
    have hm := hJ.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    exact (key _ _ y J hJ).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hm _)
      (VVRank.sval_pullTo _ _ _ _ y hJ))).symm

theorem v_coef {χ : D.toPre.X} (b : D.toPre.SecB 1 χ) (s : Fam D.toPre F 1) (a : F)
    (hs : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval (s.s χ) ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J)
    (g : GtPtF D.toPre F) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = g.b)
    (hu : ∀ z J, Good D.toPre.P.L z J → IsUnit (sval b (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ m.left) z J))
    (w : Frm D.toPre F 1 g.b) (hw : w.IsGen) {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) :
    v (coef s g w χ) = v a + l + ω := by
  have hL := D.toPre.P.isLB
  obtain ⟨t₀, h₀, v₀⟩ := exists_gen_of_isUnit hL b m.left hu
  obtain ⟨φ₁, e₁, t₁, h₁, x₁, hx₁, v₁⟩ := hl
  obtain ⟨φ₂, e₂, t₂, h₂, x₂, hx₂, v₂⟩ := hω
  have hm' : (ιS hϖ hv).left ≫ m.left = g.b.left := congrArg (fun q => q.left) hm
  obtain ⟨u, hu₀, vu⟩ := exists_unit_const hϖ hv
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ t₀ t₁) t₂) (LB.invGen _ _ _
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TO hϖ hv).hom)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ h₁) h₂)
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _))) (fun U _ h => by
      have p₀ := SectionScalarValuation.prod_famB D.toPre g.b χ 1 h
      have p₁ := prod_gt g.b χ h
      have p₂ := CoefBasic.prod_line 1 g.b h
      have p₃ : (ιS hϖ hv).left ≫ (TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Category.assoc, Over.w]; rfl
      simp only [e₁] at p₁
      simp only [e₂] at p₂
      simp only [← hm', Category.assoc] at p₀
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, p₀, p₁, p₂, p₃]
      rw [mul_comm g.b, hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, SectionScalarValuation.cQ, cP]
      module)
  have e : coef s g w χ = a * x₁ * x₂ * u := CoefBasic.coef_eq fun z J hJ => by
    have q := vu z J hJ
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Over.w, Units.val_mul, Units.val_mul, Units.val_mul,
      v₀ _ _ z J hJ, hm', Units.mul_inv_eq_iff_eq_mul] at q
    replace q : _ = _ * (rigV D.toPre (TF (R := V) F).hom z J).val := q
    have q₁ : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F a) = cst F z a := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    rw [hs _ _ z J hJ, v₁ z J hJ, v₂ z J hJ, q₁, ← Over.comp_left, lift_snd, pow_one]
    simp only [CoefBasic.cst_eq, map_mul] at q ⊢
    exact Eq.symm (by linear_combination (CoefBasic.cstH z a * CoefBasic.cstH z x₁ * CoefBasic.cstH z x₂) * q)
  rw [e, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hx₁, hx₂, hu₀, add_zero]

theorem exact_term_after_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv ϑ hϑ n hn hnV g χ
  obtain ⟨b, hb, hb'⟩ := exists_secB_good hL.1 D.toPre χ
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := vge_iff hϖ hv b hb (ϑ.s χ) (hϑ.1 χ)
  have ha : v a = ((Q χ : ℚ) : WithTop ℚ) := by
    simp only [Nat.cast_one, div_one, zero_add] at ha₁
    refine le_antisymm (not_lt.1 fun h => ?_) ha₁
    obtain ⟨q, hq₁, hq₂⟩ := WithTop.lt_iff_exists_coe_btwn.1 h
    refine hϑ.2 (q - Q χ) (sub_pos.2 (WithTop.coe_lt_coe.1 hq₁)) ((n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {χ}
      (fun χ' => ⟨χ, Finset.mem_singleton_self _, χ' - χ, by simp⟩) ϑ _).2 fun α hα => ?_)
    rw [Finset.mem_singleton] at hα
    subst hα
    refine ha₂ _ ?_
    simpa using hq₂.le
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom) ⟶ TO hϖ hv := Over.homMk _ rfl
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀, hu⟩ := hb' (ResidueField (Ov v)) _ n hn hK (ρ ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    exists_torsion_lift (Ov v) D.toPre.P.A n (TO hϖ hv).hom x₀ hx₀
  have ex' : ρ ≫ x = x₀ := Over.OverMorphism.ext ex
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨h, hh₁, hh₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq (n := n) (by omega) (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨h, 0, g + h, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hh₂.symm,
    (TorusExt.isAdd_iff_eq _ _ _).2 rfl, fun w l ω hw hl hω => ?_⟩
  rw [v_coef hϖ hv b ϑ a ha₃ (g + h) (m * x) (by rw [MonObj.comp_mul, hm, TorusExt.add_b, hh₁]) (fun z J hJ => by
    have q := hu z J hJ
    rw [← ex', ← MonObj.comp_mul] at q
    exact q) w hw (hl χ) hω, ha]
  rfl

end GlobalTheory.UT.ExactTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevelStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_polarisations_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') := by
  first | exact @GlobalTheory.polarisations_agree_at_level | exact GlobalTheory.polarisations_agree_at_level | (intros; apply GlobalTheory.polarisations_agree_at_level <;> assumption)
end


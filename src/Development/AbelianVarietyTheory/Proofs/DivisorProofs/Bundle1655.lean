import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurve
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadCurve

open Polynomial

theorem group_sections_curve_descend : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  intro k _ G _ hG g hg m hm hmk s hs P hP u a b hu hab
  classical
  obtain ⟨hc, h1, h2, h3, h5⟩ := hG
  obtain ⟨R₀, G₀, i₀, ic₀, φ, -, hR₀, s₁, s₂, s₃, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring k G ∅ h1 h2 h3

  haveI := s₁; haveI := s₂; haveI := s₃
  set L := Localization.Away P with hL

  have hu₀ : (u ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ L) := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hu]
    exact ModelDescent.spMap_comp_eq (RingHom.ext fun r => (IsScalarTower.algebraMap_apply R₀ k L r).symm)
  obtain ⟨S, yS, hSfg, -, hyS⟩ := Spread.exists_fg_points G₀.hom (fun _ : Unit => u ≫ φ) (fun _ => hu₀) ⊥
    Subalgebra.fg_bot
  obtain ⟨T, hT⟩ := hSfg
  obtain ⟨Fc, hFc⟩ := GlobalTheory.T.exists_finset_away_lift_descent k P T

  set X' : L := algebraMap (Polynomial k) L X with hX'
  have haev : ∀ (c : L →ₐ[k] k) (q : Polynomial k), c (algebraMap (Polynomial k) L q) = q.eval (c X') := by
    intro c q
    have : (c : L →+* k).comp (algebraMap (Polynomial k) L) = Polynomial.evalRingHom (c X') := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
        have e : algebraMap (Polynomial k) L (C r) = algebraMap k L r := by
          rw [IsScalarTower.algebraMap_apply k (Polynomial k) L, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [e]
        exact c.commutes r
      · simp [hX']
    exact congrArg (fun f : Polynomial k →+* k => f q) this
  have hne : ∀ c : L →ₐ[k] k, P.eval (c X') ≠ 0 := by
    intro c
    rw [← haev]
    exact ((IsLocalization.Away.algebraMap_isUnit P).map c).ne_zero

  let F : Finset k := Fc ∪ P.coeffs ∪ {(m : k)⁻¹, a X', b X', (P.eval (a X'))⁻¹, (P.eval (b X'))⁻¹}

  have hx₀ : ∀ i : s, (i.1.left ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ k) := by
    intro i
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w i.1]
    exact Category.id_comp _
  obtain ⟨R, y, hRfg, hR₁R, hy⟩ := Spread.exists_fg_points G₀.hom (fun i : s => i.1.left ≫ φ) hx₀
    (Algebra.adjoin R₀ (F : Set k)) (Subalgebra.fg_adjoin_finset F)
  let R' : Subring k := R.toSubring
  have hFR : (F : Set k) ⊆ R' := fun x hx => hR₁R (Algebra.subset_adjoin hx)
  have hR₀R : R₀ ≤ R' := fun r hr => R.algebraMap_mem ⟨r, hr⟩
  let jn : R₀ →+* R' := Subring.inclusion hR₀R
  have hjn : R'.subtype.comp jn = R₀.subtype := rfl
  have hjnsp : spMap R'.subtype ≫ spMap jn = spMap R₀.subtype := ModelDescent.spMap_comp_eq hjn
  let G₁ : Over (Sp R') := (Over.pullback (spMap jn)).obj G₀
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁c : IsCommMonObj G₁ := Functor.isCommMonObj_obj
  have hψ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (spMap jn) (spMap R'.subtype)
    (hφ.congr hjnsp.symm rfl)
  set ψ := pullback.lift φ (G.hom ≫ spMap R'.subtype) (by rw [hφ.1.w, Category.assoc, hjnsp]) with hψdef
  have hψ₁ : ψ ≫ pullback.fst G₀.hom (spMap jn) = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G₀.hom (spMap jn) = G.hom ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hyR : ∀ i : s, (y i : Sp R' ⟶ G₀.left) ≫ G₀.hom = spMap jn := fun i => (hy i).1
  have hyk : ∀ i : s, spMap R'.subtype ≫ (y i : Sp R' ⟶ G₀.left) = i.1.left ≫ φ := fun i => (hy i).2

  have hsq : IsPullback hψ.1.isoPullback.inv (pullback.snd G₁.hom (spMap R'.subtype)) G.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hgc : GeometricallyConnected (pullback.snd G₁.hom (spMap R'.subtype)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h5
  have hgd : SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R'.subtype)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hsq hg
  have hunit : IsUnit (m : R') := by
    refine IsUnit.of_mul_eq_one (a := (m : R')) ⟨(m : k)⁻¹, hFR (by simp [F])⟩ (Subtype.ext ?_)
    simp [mul_inv_cancel₀ hmk]

  let sec : s → (𝟙_ (Over (Sp R')) ⟶ G₁) := fun i =>
    Over.homMk (pullback.lift (y i : Sp R' ⟶ G₀.left) (𝟙 _) (by rw [hyR i, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  have hsec₁ : ∀ i : s, (sec i).left ≫ pullback.fst G₀.hom (spMap jn) = y i := fun i => pullback.lift_fst _ _ _
  have hkey : ∀ i : s, i.1.left ≫ ψ = spMap R'.subtype ≫ (sec i).left := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hsec₁, hyk]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w i.1, Category.assoc]
      erw [pullback.lift_snd]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hdist : ∀ i j : s, spMap R'.subtype ≫ (sec i).left = spMap R'.subtype ≫ (sec j).left → i = j := by
    intro i j e
    have e' : i.1.left ≫ φ = j.1.left ≫ φ := by
      rw [← hψ₁, ← Category.assoc, ← Category.assoc, hkey, hkey, e]
    refine Subtype.ext (Over.OverMorphism.ext (hφ.1.hom_ext e' ?_))
    rw [Over.w i.1, Over.w j.1]
  have hsec_inj : Function.Injective sec := fun i j e => hdist i j (by rw [e])
  haveI hsep₁ : IsSeparated G₁.hom := show IsSeparated (pullback.snd _ _) from inferInstance
  have hpow : ∀ i : s, sec i ^ m = 1 := by
    intro i
    have A := GlobalTheory.FrameMove.pow_comm hψ (hkey i) m
    have B := GlobalTheory.FrameMove.pow_comm hψ (hkey i) 0
    rw [hs i.1 i.2] at A
    rw [pow_zero, pow_zero] at B
    refine Over.OverMorphism.ext (Spread.point_ext R'.subtype Subtype.val_injective G₁.hom ?_ (A.symm.trans B))
    rw [Over.w, Over.w]

  have hPl : P ∈ Polynomial.lifts R'.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts P).2 fun n => ?_
    by_cases hn : P.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨P.coeff n, hFR (by simp [F, Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨P₁, hP₁⟩ := Polynomial.mem_lifts P |>.1 hPl
  have hP₁0 : P₁ ≠ 0 := by
    rintro rfl
    exact hP (by rw [← hP₁, Polynomial.map_zero])
  have hPu : IsUnit (((algebraMap (Polynomial k) L).comp (Polynomial.mapRingHom R'.subtype)) P₁) := by
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, hP₁]
    exact IsLocalization.Away.algebraMap_isUnit P
  set Lm := IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hPu with hLm
  have hinj : Function.Injective Lm := GlobalTheory.T.localizationAway_polynomial_subring_lift_injective k P hP R' P₁ hPu hP₁
  have hrange : ∀ t ∈ T, t ∈ Lm.range := hFc R' (fun x hx => hFR (by simp [F, hx])) P₁ hPu hP₁
  have hLmC : ∀ r : R', Lm (algebraMap R' (Localization.Away P₁) r) = algebraMap k L r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R' (Polynomial R') (Localization.Away P₁), hLm,
      IsLocalization.Away.lift_eq]
    simp [Polynomial.algebraMap_apply, IsScalarTower.algebraMap_apply k (Polynomial k) L]

  have hcl : Subring.closure (Set.range (algebraMap R₀ L) ∪ (T : Set L)) ≤ Lm.range := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · refine ⟨algebraMap R' (Localization.Away P₁) (jn r), ?_⟩
      rw [hLmC]
      exact (IsScalarTower.algebraMap_apply R₀ k L r).symm
    · exact hrange z hz
  have hSr : ∀ z : S, S.val.toRingHom z ∈ Lm.range := by
    intro z
    apply hcl
    rw [← Algebra.adjoin_eq_ring_closure, hT]
    exact z.2
  obtain ⟨gS, hgS⟩ := ModelDescent.exists_factor S.val.toRingHom Lm hinj hSr
  have hcomp : gS.comp (algebraMap R₀ S) = (algebraMap R' (Localization.Away P₁)).comp jn := by
    refine RingHom.ext fun r => hinj ?_
    change Lm (gS (algebraMap R₀ S r)) = Lm (algebraMap R' _ (jn r))
    rw [← RingHom.comp_apply Lm gS, hgS, hLmC]
    change (algebraMap R₀ L r) = _
    exact IsScalarTower.algebraMap_apply R₀ k L r
  let u₁' : Sp (Localization.Away P₁) ⟶ G₀.left := spMap gS ≫ yS ()
  have hu₁' : u₁' ≫ G₀.hom = spMap (algebraMap R' (Localization.Away P₁)) ≫ spMap jn := by
    rw [Category.assoc, (hyS ()).1, ModelDescent.spMap_comp_eq hcomp]
    exact (ModelDescent.spMap_comp_eq rfl).symm
  let u₁ : Sp (Localization.Away P₁) ⟶ G₁.left :=
    pullback.lift u₁' (spMap (algebraMap R' (Localization.Away P₁))) hu₁'
  have hu₁f : u₁ ≫ pullback.fst G₀.hom (spMap jn) = u₁' := pullback.lift_fst _ _ _
  have hu₁s : u₁ ≫ G₁.hom = spMap (algebraMap R' (Localization.Away P₁)) := pullback.lift_snd _ _ _

  have hpt : ∀ c : L →ₐ[k] k, c X' ∈ R' → (P.eval (c X'))⁻¹ ∈ R' → ∃ (w0 : R')
      (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm := by
    intro c hc hci
    have hev : ((Polynomial.eval (⟨c X', hc⟩ : R') P₁ : R') : k) = P.eval (c X') := by
      refine Eq.trans ?_ (congrArg (Polynomial.eval (c X')) hP₁)
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply R'.subtype _).symm
    have hw0 : IsUnit (Polynomial.evalRingHom (⟨c X', hc⟩ : R') P₁) := by
      refine IsUnit.of_mul_eq_one (b := ⟨(P.eval (c X'))⁻¹, hci⟩) (Subtype.ext ?_)
      rw [Subring.coe_mul, Polynomial.coe_evalRingHom, hev]
      exact mul_inv_cancel₀ (hne c)
    refine ⟨⟨c X', hc⟩, hw0, IsLocalization.ringHom_ext (Submonoid.powers P₁) ?_⟩
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        haev]
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rfl

  obtain ⟨α, hα, hαe⟩ := hpt a (hFR (by simp [F])) (hFR (by simp [F]))
  obtain ⟨β, hβ, hβe⟩ := hpt b (hFR (by simp [F])) (hFR (by simp [F]))
  have key : ∀ (c : L →ₐ[k] k) (w0 : R') (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm →
      (spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) ≫ u₁) ≫
        pullback.fst G₀.hom (spMap jn) = spMap c.toRingHom ≫ u ≫ φ := by
    intro c w0 hw0 hce
    rw [Category.assoc, Category.assoc, hu₁f, ← Category.assoc, ModelDescent.spMap_comp_eq hce,
      ← ModelDescent.spMap_comp_eq (f := Lm) (g := c.toRingHom) rfl, Category.assoc, ← Category.assoc (spMap Lm),
      ModelDescent.spMap_comp_eq hgS, (hyS ()).2]
  have hcG : ∀ c : L →ₐ[k] k, spMap c.toRingHom ≫ u ≫ G.hom = 𝟙 _ := by
    intro c
    rw [hu, ModelDescent.spMap_comp_eq (h := RingHom.id k) (RingHom.ext c.commutes)]
    simp [spMap]
  have hdistc : spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠
      spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
    intro e
    apply hab
    have ea := key a α hα hαe
    have eb := key b β hβ hβe
    rw [e] at ea
    have e2 : spMap a.toRingHom ≫ u ≫ φ = spMap b.toRingHom ≫ u ≫ φ := ea.symm.trans eb
    refine hφ.1.hom_ext (by simpa only [Category.assoc] using e2) ?_
    rw [Category.assoc, hcG, Category.assoc, hcG]
  refine ⟨R', G₁, inferInstance, SpreadGroup.finiteType_of_fg hR₀ hRfg, hunit, hG₁c,
    show Smooth (pullback.snd _ _) from inferInstance, hsep₁, show QuasiCompact (pullback.snd _ _) from inferInstance,
    hgc, hgd, ⟨s.attach.image sec, ?_, ?_, ?_⟩, P₁, hP₁0, u₁, α, β, hα, hβ, hu₁s, hdistc⟩
  · rw [Finset.card_image_of_injective _ hsec_inj, Finset.card_attach]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hpow i
  · intro x hx z hz hxz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
    exact fun e => hxz (by rw [hdist i j e])

end GlobalTheory.SpreadCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace GlobalTheory.PrimFrameMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem exists_rightInverse {X : Matrix A D k} (hX : IsPrimFrame (SplitFlip.stdLat k D) X) :
    ∃ R : Matrix D A k, (∀ i j, R i j ∈ 𝒪[k]) ∧ X * R = 1 := by
  have hli : LinearIndependent k X.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, ← hX.1, rank_eq_finrank_span_row]; rfl
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let f : (A → 𝒪[k]) →ₗ[𝒪[k]] (D → 𝒪[k]) := X'.vecMulLinear
  have hf : ∀ v j, ((f v j : 𝒪[k]) : k) = (∑ i, (v i : k) • X.row i) j := fun v j => by
    simp [f, X', vecMul, dotProduct, Finset.sum_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ∑ i, (v i : k) • X.row i = 0 := by
      funext j; rw [← hf, hv]; rfl
    funext i
    exact Subtype.ext (Fintype.linearIndependent_iff.1 hli _ h1 i)
  have hsat : ∀ (r : 𝒪[k]) (x : D → 𝒪[k]), r ≠ 0 → r • x ∈ LinearMap.range f → x ∈ LinearMap.range f := by
    rintro r x hr ⟨v, hv⟩
    have hr' : (r : k) ≠ 0 := fun h => hr (Subtype.ext h)
    have h1 : (fun j => (x j : k)) = (r : k)⁻¹ • ∑ i, (v i : k) • X.row i := by
      funext j
      rw [Pi.smul_apply, ← hf, hv]
      simp [hr']
    have h2 : (fun j => (x j : k)) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      refine ⟨?_, mem_stdLat.2 fun j => (x j).2⟩
      rw [h1]
      exact Submodule.smul_mem (Submodule.span k _) _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    refine ⟨d, funext fun j => Subtype.ext ?_⟩
    rw [hf]
    exact congrFun hd j
  have : Module.IsTorsionFree 𝒪[k] ((D → 𝒪[k]) ⧸ LinearMap.range f) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q h => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact .inl hr
    · refine .inr ((Submodule.Quotient.mk_eq_zero _).2 (hsat r x hr ?_))
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  obtain ⟨l, hl⟩ : ∃ l : (D → 𝒪[k]) →ₗ[𝒪[k]] (A → 𝒪[k]), l ∘ₗ f = LinearMap.id := by
    have hs' : ∃ s : _ →ₗ[𝒪[k]] _, (LinearMap.range f).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
    have H := ((LinearMap.exact_map_mkQ_range f).split_tfae hinj (Submodule.mkQ_surjective _)).out 0 1
    exact H.1 hs'
  refine ⟨Matrix.of fun j i => (l (Pi.single j 1) i : k), fun j i => (l (Pi.single j 1) i).2, ?_⟩
  ext i i'
  have h1 : l (f (Pi.single i 1)) = Pi.single i 1 := LinearMap.congr_fun hl _
  have h2 : f (Pi.single i 1) = ∑ j, X' i j • Pi.single j 1 := by
    funext j; simp [f, Finset.sum_apply, Pi.single_apply]
  rw [h2, map_sum] at h1
  have h3 := congrArg Subtype.val (congrFun h1 i')
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  push_cast at h3
  rw [Matrix.mul_apply, Matrix.one_apply]
  refine h3.trans ?_
  rw [Pi.single_apply]
  by_cases h : i = i'
  · simp [h]
  · simp [h, Ne.symm h]

theorem exists_mem_glLatCong {u : kˣ} (hu : valuation k (u : k) < 1) {M : Matrix D D k}
    (hM : ∀ i j, valuation k (M i j) ≤ valuation k (u : k)) :
    ∃ κ ∈ glLatCong u (SplitFlip.stdLat k D), κ.val = 1 + M := by
  let M' : Matrix D D 𝒪[k] := Matrix.of fun i j => ⟨M i j, (hM i j).trans hu.le⟩
  have hK : IsUnit (1 + M') := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 0 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (hM r j).trans_lt hu
    rw [map_add, this]; simp
  obtain ⟨w, hw⟩ := hK
  have hv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w).val = 1 + M := by
    show (algebraMap 𝒪[k] k).mapMatrix w.val = _
    rw [hw, map_add, map_one]; rfl
  refine ⟨_, GlobalTheory.FunObj.GivenAdm.mem_glLatCong.2 ⟨⟨w, rfl⟩, ?_⟩, hv⟩
  rw [hv, add_sub_cancel_left]
  exact hM

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem vecMul_diagGL_mem (a b c : D → kˣ) (h : ∀ j, b j = a j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat b ↔ x ∈ diagLat a := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem exists_glLatCong_move (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (c : D → kˣ) (u : kˣ) (hu : valuation k (u : k) < 1) (X Z : Matrix A D k) (hX : IsPrimFrame (diagLat c) X)
    (hZ : Z ∈ matLat A (u • diagLat c)) : ∃ κ ∈ glLatCong u (diagLat c), X + Z = X * κ.val := by
  set g : GL D k := diagGL c with hg
  have h1 : ∀ x, x ᵥ* g.val ∈ diagLat c ↔ x ∈ SplitFlip.stdLat k D := vecMul_diagGL_mem 1 c c (by simp)
  have h2 : ∀ x, x ᵥ* g.val ∈ u • diagLat c ↔ x ∈ u • SplitFlip.stdLat k D := fun x => by
    rw [SplitFlip.stdLat, smul_diagLat, smul_diagLat]
    exact vecMul_diagGL_mem _ _ c (by simp) x
  have h1' : ∀ x, x ᵥ* (g⁻¹).val ∈ SplitFlip.stdLat k D ↔ x ∈ diagLat c := fun x => by
    rw [← h1, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have h2' : ∀ x, x ᵥ* (g⁻¹).val ∈ u • SplitFlip.stdLat k D ↔ x ∈ u • diagLat c := fun x => by
    rw [← h2, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨R, hR, hXR⟩ := exists_rightInverse (SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1')
  have hZ' : GlobalTheory.FunObj.GivenAdm.CongM u (Z * (g⁻¹).val) :=
    GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.1 fun i => (h2' (Z.row i)).2 (hZ i)
  obtain ⟨κ, ⟨hκ, hκ'⟩, hv⟩ := exists_mem_glLatCong hu (hZ'.mul_left (Y := R) hR)
  refine ⟨g⁻¹ * κ * g, ⟨fun x => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, h1, hκ, h1']
  · rw [show (g⁻¹ * κ * g).val - 1 = (g⁻¹).val * (κ.val - 1) * g.val by
      rw [mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul],
      ← vecMul_vecMul, ← vecMul_vecMul, h2]
    exact hκ' _ ((h1' x).2 hx)
  · rw [Units.val_mul, Units.val_mul, hv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_add,
      ← Matrix.mul_assoc _ R, hXR, Matrix.mul_one, Matrix.one_mul, ← Matrix.add_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]

end GlobalTheory.PrimFrameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealFactorIff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem exists_ideal_factor_iff {X Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y)
    (x₀ : X) :
    ∃ J : Ideal (X.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : X.presheaf.stalk x₀ →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z,
        z ≫ i = (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x₀) ≫ f) ↔
        J ≤ RingHom.ker ψ := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd i (X.fromSpecStalk x₀ ≫ f))).1
    inferInstance
  refine ⟨I, fun R' _ ψ => ?_⟩
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ : ∃ w : Spec (CommRingCat.of R') ⟶ pullback i (X.fromSpecStalk x₀ ≫ f),
        w ≫ pullback.fst i (X.fromSpecStalk x₀ ≫ f) = z ∧
          w ≫ pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) :=
      ⟨pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) (hz.trans (Category.assoc _ _ _)),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [he, ← Category.assoc] at hw
    set w' := w ≫ e.hom
    have h3 : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage w' = CommRingCat.ofHom ψ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hw
    intro a ha
    rw [RingHom.mem_ker]
    have h4 := congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at h4
    exact h4.symm
  · intro hI
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
      pullback.fst i (X.fromSpecStalk x₀ ≫ f), ?_⟩
    have key : Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
        pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [he, e.inv_hom_id_assoc, ← Spec.map_comp]
      congr 1
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% key]

end GlobalTheory.KerIdeal

namespace GlobalTheory.KerIdeal

theorem kernel_ideal : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B), IsAbelianScheme B → ∀ x₀ : A.left,
    ∃ J : Ideal (A.left.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ := by
  intro k _ A B _ π _ x₀
  haveI : IsClosedImmersion (η[B]).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) B.hom _ (Over.w _)
  exact exists_ideal_factor_iff (η[B]).left π.left x₀

end GlobalTheory.KerIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphismsStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_quotient_transition_isomorphisms : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) →
    ∃ b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) ∧
      (∀ j k, IsPullback (b j k) (pullback.fst _ _ ≫ (B j).hom) ((B k).hom ≫ 𝒰.f k) (𝒰.f j)) ∧
      ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left := by
  first | exact @GlobalTheory.QuotTransition.exists_transition | exact GlobalTheory.QuotTransition.exists_transition | (intros; apply GlobalTheory.QuotTransition.exists_transition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  first | exact @GlobalTheory.UPel.HT.exists_tateIsoO_of_period | exact GlobalTheory.UPel.HT.exists_tateIsoO_of_period | (intros; apply GlobalTheory.UPel.HT.exists_tateIsoO_of_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularAlterationArithmeticStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_alteration_arithmetic : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (ρ : Y' ⟶ Y), CxForm.IsRegVar (ρ ≫ q) e ∧ ρ (genericPoint Y') = genericPoint Y ∧ ρ.residueDegree (genericPoint Y') ≠ 0 := by
  first | exact @GlobalTheory.RegAlteration.exists_regular_alteration | exact GlobalTheory.RegAlteration.exists_regular_alteration | (intros; apply GlobalTheory.RegAlteration.exists_regular_alteration <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_bump_complexPoints_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)), IsOpen O → y ∈ O → ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ O := by
  first | exact @GlobalTheory.BumpPts.exists_cInf_bump | exact GlobalTheory.BumpPts.exists_cInf_bump | (intros; apply GlobalTheory.BumpPts.exists_cInf_bump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceChartIndepStatement
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extTrace_chart_indep : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} (T : HermSeq A 1 1) (a b : T.κ) (i : A.ι) {v : V n}, v ∈ chartSet T a i ∩ chartSet T b i → extTrace (midIn T a i) v = extTrace (midIn T b i) v := by
  first | exact @GlobalTheory.SecForm.extTrace_midIn_indep | exact GlobalTheory.SecForm.extTrace_midIn_indep | (intros; apply GlobalTheory.SecForm.extTrace_midIn_indep <;> assumption)
end


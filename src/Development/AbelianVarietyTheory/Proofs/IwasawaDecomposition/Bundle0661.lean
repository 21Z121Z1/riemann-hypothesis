import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormsArcCompareStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_forms_arc_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a₀ : ArcIn Dw l β A b) (γ γ' : levelForms H l.M' a₀.D₀.X) (h : γ ∈ admitted H l.M' a₀.D₀.X) (h' : γ' ∈ admitted H l.M' a₀.D₀.X) (χ : Sp (PowerSeries A) ⟶ Y.X) (g : PowerSeries A →+* PowerSeries A) (W : Wit Y (withForm a₀ γ h) χ) (W' : Wit Y (withForm a₀ γ' h') (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre) (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G) (w₁ : LB.Iso W'.P.D.toPre.P.L (a₀.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))), g.comp (PowerSeries.C (R := A)) = PowerSeries.C → g PowerSeries.X ∈ Ideal.span {PowerSeries.X} → Out.IsPullUnif g hD bc W.P.U W'.P.U → (∀ y, hD.xe (W'.e y) = W.e y) → W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ → HEq W'.w w₁ → Tri W.w hD.w w₁ → ∀ (ν : Out.GtPt a₀.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) (v' : epsR (PowerSeries A) ⟶ W'.t.G), LieImg W ν v → v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = spMap (dualMap g) ≫ v.left → LieImg W' ν v' := by
  first | exact @GlobalTheory.ArcSubst.lieImg_subst | exact GlobalTheory.ArcSubst.lieImg_subst | (intros; apply GlobalTheory.ArcSubst.lieImg_subst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllStepsHoldOfHasDRStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allSteps_hold_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), HasDR Z' → (∃ f, IsMap Z' Z f) → ∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z' := by
  first | exact @GlobalTheory.LocM.StepOfFrame.holds_of_hasDR | exact GlobalTheory.LocM.StepOfFrame.holds_of_hasDR | (intros; apply GlobalTheory.LocM.StepOfFrame.holds_of_hasDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmul
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.ProjVar GlobalTheory.CechPic GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjVar.Var

theorem ample_nsmul : ∀ (F : Type) [Field F] (Y : Var F) (Δ : Y.Dv) (n : ℕ), 0 < n → Y.ample Δ → Y.ample (n • Δ) := by
  intro F _ Y Δ n hn h
  have hL := isLB_toLB Δ
  refine (Var.ample_iff_of_toPic_eq (isLB_lbPow hL n) ?_).2 ((isAmpleLB_pow_iff hL hn).2 h)
  rw [cls_lbPow hL, map_nsmul, toPic_apply]

end GlobalTheory.ProjVar.Var
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.AmpleOverBase
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm
variable {X Y : Scheme.{0}}

theorem basicOpen_eq (O : Type) [CommRing O] (s : X ⟶ Sp O) (a : O) :
    (X.basicOpen (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) : Set X) =
      s ⁻¹' {x : Sp O | a ∉ x.asIdeal} := by
  have e := Scheme.preimage_basicOpen s (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)
  rw [basicOpen_eq_of_affine] at e
  exact congrArg (fun U : X.Opens => (U : Set X)) e.symm

theorem gm_val_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (f.stalkMap y).hom (gm (𝟙 X) (f y) U a).val := by
  rw [← gs_unit f y U h, ← gs_unit (𝟙 X) (f y) U h]
  exact gs_stalkMap f y U h a.val

theorem isUnit_gs_id_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) (f y) U a) ↔ IsUnit (gs f y U a) := by
  rw [isUnit_gs_iff (𝟙 X) (f y) U h, isUnit_gs_iff f y U h]
  rfl

theorem stalkMap_injective (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) : Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1

theorem cocycle_of_pull {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (hL : (L.pull f).IsLB) (y : Y) {i j k : L.ι}
    (hi : f y ∈ L.U i) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gm (𝟙 X) (f y) _ (L.g i j) * gm (𝟙 X) (f y) _ (L.g j k) = gm (𝟙 X) (f y) _ (L.g i k) := by
  have hi' : y ∈ (L.pull f).U (fun _ => i) := mem_pull.2 hi
  have hj' : y ∈ (L.pull f).U (fun _ => j) := mem_pull.2 hj
  have hk' : y ∈ (L.pull f).U (fun _ => k) := mem_pull.2 hk
  have e := gm_cocycle hL (𝟙 Y) y hi' hj' hk'
  rw [gm_pull_g L f (𝟙 Y) y _ _ hi' hj', gm_pull_g L f (𝟙 Y) y _ _ hj' hk', gm_pull_g L f (𝟙 Y) y _ _ hi' hk',
    Category.id_comp] at e
  apply Units.ext
  apply stalkMap_injective f y
  rw [Units.val_mul, map_mul, ← gm_val_stalkMap f y _ (show f y ∈ L.U i ⊓ L.U j from ⟨hi, hj⟩),
    ← gm_val_stalkMap f y _ (show f y ∈ L.U j ⊓ L.U k from ⟨hj, hk⟩),
    ← gm_val_stalkMap f y _ (show f y ∈ L.U i ⊓ L.U k from ⟨hi, hk⟩), ← Units.val_mul, e]

theorem isLB_of_germ (L : LB X) (hc : ∀ x : X, ∃ i, x ∈ L.U i)
    (h : ∀ (x : X) i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB where
  cover := top_le_iff.1 fun x _ => Opens.mem_iSup.2 (hc x)
  g_self i := unit_ext fun x hx => by
    refine (gm_res (𝟙 X) x _ hx _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (h x i i i hx hx hx)
  cocycle i j k := unit_ext fun x hx =>
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) x _ hx _) (gm_res (𝟙 X) x _ hx _))).trans
      ((h x i j k hx.1.1 hx.1.2 hx.2).trans (gm_res (𝟙 X) x _ hx _).symm)

theorem isLB_of_pull {I : Type} {Y : I → Scheme.{0}} (u : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (u i)]
    (L : LB X) (hL : ∀ i, (L.pull (u i)).IsLB) (hc : ∀ x : X, ∃ i y, u i y = x) : L.IsLB := by
  refine isLB_of_germ L (fun x => ?_) fun x a b c ha hb hc' => ?_
  · obtain ⟨i, y, rfl⟩ := hc x
    obtain ⟨J, hJ⟩ := exists_chart (hL i) y
    exact ⟨J PUnit.unit, mem_pull.1 hJ⟩
  · obtain ⟨i, y, rfl⟩ := hc x
    exact cocycle_of_pull (u i) (hL i) y ha hb hc'

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem exists_push {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) (hV : V = f.opensRange) {n : ℕ}
    (t : (lbPow (L.pull f) n).Sec) :
    ∃ T : ∀ J : PUnit → L.ι, Γ(X, V ⊓ powChart L J), T ∈ secOn (lbPow L n) V ∧
      ∀ (y : Y) (J : PUnit → L.ι), f y ∈ powChart L J →
        (IsUnit (gs (𝟙 X) (f y) _ (T J)) ↔ y ∈ nonzeroLocus t) := by
  let J' : (PUnit → L.ι) → PUnit → PUnit → L.ι := fun J _ _ => J PUnit.unit
  have hm : ∀ (y : Y) (J : PUnit → L.ι), y ∈ powChart (L.pull f) (J' J) ↔ f y ∈ powChart L J := fun y J =>
    mem_powChart.trans (mem_pull.trans mem_powChart.symm)
  have e : ∀ J, powChart (L.pull f) (J' J) ≤ f ⁻¹ᵁ (V ⊓ powChart L J) := fun J y hy =>
    ⟨hV ▸ ⟨y, rfl⟩, (hm y J).1 hy⟩
  have e' : ∀ J, f ⁻¹ᵁ (V ⊓ powChart L J) ≤ powChart (L.pull f) (J' J) := fun J y hy => (hm y J).2 hy.2
  choose T hT using fun J =>
    (bijective_appLE f (V ⊓ powChart L J) (inf_le_left.trans hV.le) _ (e J) (e' J)).2 (powFn t (J' J))
  have key : ∀ (y : Y) (J : PUnit → L.ι) (hJ : f y ∈ powChart L J),
      gs f y _ (T J) = gs (𝟙 Y) y _ (powFn t (J' J)) := fun y J hJ => by
    rw [← hT J, gs_appLE f _ _ (e J) (𝟙 Y) y ((hm y J).2 hJ), Category.id_comp]
  refine ⟨T, mem_secOn_of_germ (M := lbPow L n) (V := V) T fun x J K hx hJ hK => ?_, fun y J hJ => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, f y = x := by
      have : x ∈ f.opensRange := hV ▸ hx
      exact this
    change gs (𝟙 X) (f y) (V ⊓ powChart L J) (T J) =
      (gm (𝟙 X) (f y) ((lbPow L n).U J ⊓ (lbPow L n).U K) ((lbPow L n).g J K)).val *
        gs (𝟙 X) (f y) (V ⊓ powChart L K) (T K)
    replace hJ : f y ∈ powChart L J := hJ
    replace hK : f y ∈ powChart L K := hK
    have hJ' := (hm y J).2 hJ
    have hK' := (hm y K).2 hK
    apply stalkMap_injective f y
    rw [map_mul, ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L J from ⟨hx, hJ⟩),
      ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L K from ⟨hx, hK⟩), key y J hJ, key y K hK,
      gm_lbPow_g n (𝟙 X) (f y) J K hJ hK, Units.val_pow_eq_pow_val, map_pow,
      ← gm_val_stalkMap f y _ (show f y ∈ L.U (J PUnit.unit) ⊓ L.U (K PUnit.unit) from
        ⟨mem_powChart.1 hJ, mem_powChart.1 hK⟩),
      gs_powFn_compat t (𝟙 Y) y (J' J) (J' K) hJ' hK']
    have hJ'' : y ∈ (L.pull f).U (fun _ => J PUnit.unit) := mem_pull.2 (mem_powChart.1 hJ)
    have hK'' : y ∈ (L.pull f).U (fun _ => K PUnit.unit) := mem_pull.2 (mem_powChart.1 hK)
    rw [gm_pull_g L f (𝟙 Y) y _ _ hJ'' hK'', Category.id_comp]
  · rw [isUnit_gs_id_iff f y _ (show f y ∈ V ⊓ powChart L J from ⟨hV ▸ ⟨y, rfl⟩, hJ⟩), key y J hJ]
    exact (mem_nonzeroLocus_iff_powFn t ((hm y J).2 hJ)).symm

theorem exists_affine_of_pull [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    [IsOpenImmersion f] (r : Γ(X, ⊤)) (hr : X.basicOpen r = f.opensRange) (h : IsAmpleLB (L.pull f)) (y : Y) :
    ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, f y ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨n, hn, t, hty, hta⟩ := h.exists_affine y
  have hs₀ : nonzeroLocus (secOfFn L r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn L r)) hs₀ t
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn L r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : Y) (J : PUnit → L.ι), f y' ∈ powChart L J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t) := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn L r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn L r) ⊓ powChart L J := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy, gs_res (𝟙 X) (f y') _ hy] at e
    rw [mem_nonzeroLocus_iff_powFn u hJ, e, IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  have hloc : nonzeroLocus (secMul u (secOfFn L r)) = f ''ᵁ nonzeroLocus t := by
    rw [nonzeroLocus_secMul]
    ext x
    constructor
    · rintro ⟨hx, hx₀⟩
      obtain ⟨y', rfl⟩ : ∃ y', f y' = x := by
        have : x ∈ f.opensRange := hs₀ ▸ hx₀
        exact this
      obtain ⟨i, hi⟩ := exists_chart hL (f y')
      exact ⟨y', (key y' (fun _ => i) (mem_powChart.2 hi)).1 hx, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨i, hi⟩ := exists_chart hL (f y')
      exact ⟨(key y' (fun _ => i) (mem_powChart.2 hi)).2 hy', hs₀ ▸ ⟨y', rfl⟩⟩
  refine ⟨n + 0 * N + 0, by omega, secMul u (secOfFn L r), ?_, ?_⟩
  · rw [hloc]
    exact ⟨y, hty, rfl⟩
  · rw [hloc]
    exact hta.image_of_isOpenImmersion f

theorem isAmpleLB_of_basicOpen_cover : ∀ {X : Scheme.{0}} {O : Type} [CommRing O] {I : Type} [Finite I]
    {Y : I → Scheme.{0}} (s : X ⟶ Sp O) (u : ∀ i, Y i ⟶ X) (a : I → O) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X),
    CompactSpace X → QuasiSeparatedSpace X → Ideal.span (Set.range a) = ⊤ → (∀ i, IsOpenImmersion (u i)) →
    (∀ i, Set.range (u i) = s ⁻¹' {x : Sp O | a i ∉ x.asIdeal}) → (∀ i, GlobalTheory.IsAmpleLB (L.pull (u i))) →
    GlobalTheory.IsAmpleLB L := by
  intro X O _ I _ Y s u a L hX hXs hspan hu hrange hamp
  have hc : ∀ x : X, ∃ i y, u i y = x := fun x => by
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hne
      push Not at hne
      apply (s x).isPrime.ne_top
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    obtain ⟨i, hi⟩ := this
    have hx : x ∈ Set.range (u i) := by
      rw [hrange i]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  have hL : L.IsLB := isLB_of_pull u L (fun i => (hamp i).isLB) hc
  refine ⟨hL, hX, fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := hc x
  have hr : X.basicOpen ((s.appTop) ((Scheme.ΓSpecIso (CommRingCat.of O)).inv (a i))) = (u i).opensRange := by
    apply SetLike.coe_injective
    rw [basicOpen_eq O s (a i), ← hrange i]
    rfl
  exact exists_affine_of_pull hL (u i) _ hr (hamp i) y

end GlobalTheory.AmpleOverBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedIntMatrixTriangularGramAdjointWeightedSq
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  intro n A A' d u v hd hvu huv h
  set a := A.map (Int.cast : ℤ → ℝ) with ha
  set a' := A'.map (Int.cast : ℤ → ℝ) with ha'
  have key : (u * a * v)ᵀ * diagonal d = diagonal d * (u * a' * v) := by
    have h2 := congrArg (fun M => vᵀ * M * v) h
    simp only [gram] at h2
    have e1 : vᵀ * (aᵀ * (uᵀ * diagonal d * u)) * v = (u * a * v)ᵀ * diagonal d * (u * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    have e2 : vᵀ * (uᵀ * diagonal d * u * a') * v = (u * v)ᵀ * diagonal d * (u * a' * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e1, e2, huv] at h2
    simpa using h2
  have c1 : ∀ p q, d p * (u * a * v) p q = d q * (u * a' * v) q p := by
    intro p q
    have := congrFun (congrFun key q) p
    simp only [mul_diagonal, diagonal_mul, transpose_apply] at this
    linarith
  have htr : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = (((A' * A).trace : ℤ) : ℝ) := by
    have e : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = ((u * a' * v) * (u * a * v)).trace := by
      rw [Finset.sum_comm]; simp [Matrix.trace, Matrix.mul_apply]
    rw [e]
    have : (u * a' * v) * (u * a * v) = u * (a' * a) * v := by
      rw [show (u * a' * v) * (u * a * v) = u * a' * (v * u) * a * v by simp only [Matrix.mul_assoc], hvu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hvu, Matrix.one_mul]
    rw [ha, ha']
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]
    push_cast; rfl
  refine ⟨c1, ?_, ?_⟩
  · rw [← htr]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := (hd q).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hq, sq, ← mul_assoc, c1 p q]; ring
  · rw [← htr, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hp := (hd p).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hp, sq, ← mul_assoc, ← c1 p q]; ring

end GlobalTheory.RedTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorAmpleCriterion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitRank

theorem evalZ_comb' {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (a : ℕ)
    (ψ : InvFun O) (b : ℕ) (φ : InvFun O) (β : LinearMap.BilinForm ℤ X) :
    (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  unfold InvFun.evalZ
  rw [(comb a ψ b φ).eval_eq hr, ψ.eval_eq hr, φ.eval_eq hr]
  rfl

theorem exists_generic_of_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] [CharZero W]
    (χ : Sp W ⟶ Z.X) (hχ : Set.range (jK W ≫ χ) ⊆ Set.range Z.j) :
    ∃ y : Sp (FractionRing W) ⟶ Xo.XF c, y ≫ Z.j = jK W ≫ χ := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI : CharZero (FractionRing W) := by
    refine ⟨fun a b h => Nat.cast_injective (R := W) (IsFractionRing.injective W (FractionRing W) ?_)⟩
    simpa using h
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (jK W ≫ χ ≫ Z.s)
  let β' : 𝓞 c.F →+* FractionRing W := β₀.hom
  have hinj : Function.Injective β' := GlobalTheory.LieUnif.injective_of_charZero (E := c.F) β'
  let g : c.F →+* FractionRing W := IsFractionRing.lift (K := c.F) hinj
  have hsq : (jK W ≫ χ) ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    have hb : β₀ = CommRingCat.ofHom (g.comp (algebraMap (𝓞 c.F) c.F)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have := IsFractionRing.lift_algebraMap (K := c.F) hinj a
      exact this.symm
    rw [Category.assoc, ← hβ₀, hb]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let u : Sp (FractionRing W) ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (jK W ≫ χ) (spMap g) hsq
  have hu : Set.range u ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Z.ab_gen]
    obtain ⟨v, hv⟩ := hχ ⟨p, rfl⟩
    have e1 : (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (u p) = (jK W ≫ χ) p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    show (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (u p) ∈ abLocus Z.t.G
    rw [e1, ← hv]
    have : Z.jQ v ∈ (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) ⁻¹' abLocus Z.t.G := by
      rw [Z.ab_gen]; exact ⟨v, rfl⟩
    exact this
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ u hu, ?_⟩
  show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem finrank_le_min_of_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [CharZero R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (m : SABMap t Z.t ξ)
    (P : PELUnif (maximalIdeal R) t) (hξ : Set.range (jK R ≫ ξ) ⊆ Set.range Z.j) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  obtain ⟨y, hy⟩ := exists_generic_of_range Z R ξ hξ
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    show (spMap (algebraMap (FractionRing R) K) ≫ y) ≫ Z.j = _
    rw [Category.assoc, hy, ← Category.assoc]
    show (Spec.map _ ≫ Spec.map _) ≫ ξ = _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Z.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem order_nat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX _ _ href _ _ _ _ _ _ W _ _ _ hW _ ϖ _ χ t mt P hχ be
    hbe hmon
  obtain ⟨hdvr, -, hch⟩ := hW
  haveI := hdvr
  haveI := hch
  have hrk := finrank_le_min_of_range Z W χ t mt P hχ
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have hF := href.1 P.D.toPre.X hrk
  have hbal : be ∈ balForms H.bar P.D.toPre.X := by rw [balForms_eq_levelForms]; exact hbe
  obtain ⟨a, ha⟩ := hF.exists_nat hbal (fun y => hmon.nonneg 0 y)
  refine ⟨n * d' * a, ?_⟩
  rw [evalZ_comb', ha]
  push_cast
  ring

end GlobalTheory.TraitRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRows
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.combo_of_bounded_rows_bounded : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  intro X g r r₀ T lam u A C hu hC w hw
  rw [Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  refine ⟨∑ i, |c i| * C, fun x hx => ?_⟩
  have key : ∑ j, ((∑ i, c i • fun j => (A i j : ℝ)) j : ℂ) • lam x j = ∑ i, (c i : ℂ) • u x i := by
    simp_rw [hu x hx, Finset.smul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  rw [key]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (u x) i).trans (hC x hx)) (abs_nonneg _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIff
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

open GlobalTheory.ProjSpace (pt_eq_pt_iff pt_str span_range_eq_top_iff_ne_zero)

theorem plk_smul_all {S : Type} [CommRing S] {M k : ℕ} (u : S) (v : Fin k → Fin (M + 1) → S) :
    plk (fun l => u • v l) id = u ^ k • plk v id := by
  funext q
  have h : (Matrix.of fun l l' => (u • v l) (GlobalTheory.FlagEmb.plE M k q l')) =
      u • Matrix.of fun l l' => v l (GlobalTheory.FlagEmb.plE M k q l') := by
    ext; simp
  change (Matrix.of fun l l' => (u • v l) (GlobalTheory.FlagEmb.plE M k q l')).det =
    u ^ k * (Matrix.of fun l l' => v l (GlobalTheory.FlagEmb.plE M k q l')).det
  rw [h, Matrix.det_smul, Fintype.card_fin]

theorem exists_pt_eq_of_smul {O K : Type} [CommRing O] [Field K] {N : ℕ} (g : O →+* K) {v v' : Fin (N + 1) → K}
    (hv : Ideal.span (Set.range v) = ⊤) (r : Kˣ) (h : v' = (r : K) • v) : ∃ hv', pt g v hv = pt g v' hv' := by
  have h0 : v' ≠ 0 := h ▸ smul_ne_zero r.ne_zero (span_range_eq_top_iff_ne_zero.1 hv)
  exact ⟨span_range_eq_top_iff_ne_zero.2 h0, (pt_eq_pt_iff g _ _).2 ⟨r, h⟩⟩

theorem plk_point_iff {O K : Type} [CommRing O] [Field K] {N n k : ℕ} (A : Matrix (Fin (N + 1)) (Fin n) K)
    (A' : Matrix (Fin n) (Fin (N + 1)) K) (h1 : A' * A = 1) (y : Sp K ⟶ PSpace O (plN N k)) (ξ : Fin k → Fin n → K)
    (hξ : ∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => A.mulVec (ξ l)) id) hv) :
    LinearIndependent K ξ ∧ ∀ ξ' : Fin k → Fin n → K,
      (∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => A.mulVec (ξ' l)) id) hv) ↔
        LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ) := by
  obtain ⟨g, hv, hg⟩ := hξ
  have hinj : Function.Injective A.mulVecLin := by
    intro x y hxy
    have := congrArg A'.mulVec hxy
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  have hli : ∀ ξ' : Fin k → Fin n → K, LinearIndependent K (fun l => A.mulVec (ξ' l)) ↔ LinearIndependent K ξ' :=
    fun ξ' => LinearMap.linearIndependent_iff (v := ξ') A.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  have hsp : ∀ ξ' : Fin k → Fin n → K, Submodule.span K (Set.range fun l => A.mulVec (ξ' l)) =
      (Submodule.span K (Set.range ξ')).map A.mulVecLin := fun ξ' => by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hI := (GlobalTheory.T.plucker_nonzero_iff_independent K N k (fun l => A.mulVec (ξ l)) fun l => A.mulVec (ξ l)).1.1
    (span_range_eq_top_iff_ne_zero.1 hv)
  refine ⟨(hli ξ).1 hI, fun ξ' => ?_⟩
  have hk := (GlobalTheory.T.plucker_nonzero_iff_independent K N k (fun l => A.mulVec (ξ l)) fun l => A.mulVec (ξ' l)).2 hI
  rw [hli, hsp, hsp, (Submodule.map_injective_of_injective hinj).eq_iff] at hk
  rw [hk]
  constructor
  · rintro ⟨g', hv', hg'⟩
    have e := hg.symm.trans hg'
    have e1 : spMap g = spMap g' := by rw [← pt_str g _ hv, e, pt_str]
    obtain rfl : g = g' := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    exact (pt_eq_pt_iff g _ _).1 e
  · rintro ⟨r, hr⟩
    obtain ⟨hv', e⟩ := exists_pt_eq_of_smul g hv r hr
    exact ⟨g, hv', hg.trans e⟩

theorem plk_point_change {O K : Type} [CommRing O] [Field K] {N n n' k : ℕ} (A : Matrix (Fin (N + 1)) (Fin n) K)
    (B : Matrix (Fin (N + 1)) (Fin n') K) (T : Matrix (Fin n') (Fin n) K) (u : Kˣ) (hu : B * T = (u : K) • A)
    (y : Sp K ⟶ PSpace O (plN N k)) (ξ : Fin k → Fin n → K)
    (hξ : ∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => A.mulVec (ξ l)) id) hv) :
    ∃ (g : O →+* K) (hv : _), y = pt g (plk (fun l => B.mulVec (T.mulVec (ξ l))) id) hv := by
  obtain ⟨g, hv, hg⟩ := hξ
  have hr : plk (fun l => B.mulVec (T.mulVec (ξ l))) id = ((u ^ k : Kˣ) : K) • plk (fun l => A.mulVec (ξ l)) id := by
    simp only [Matrix.mulVec_mulVec, hu, Matrix.smul_mulVec]
    rw [plk_smul_all, Units.val_pow_eq_pow_val]
  obtain ⟨hv', e⟩ := exists_pt_eq_of_smul g hv _ hr
  exact ⟨g, hv', hg.trans e⟩

theorem car_span : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (K : Type) [Field K] (w : Sp K ⟶ Z') (β : C.A) (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) (ξ : Fin k → Fin (C.n β) → K), Car Em f q w β hβ ξ → LinearIndependent K ξ ∧ (∀ ξ' : Fin k → Fin (C.n β) → K, Car Em f q w β hβ ξ' ↔ LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ)) ∧ ∀ (α : C.A) (hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), Car Em f q w α hα fun l => (C.tr α β (w ≫ f) hα hβ).mulVec (ξ l) := by
  intro O _ Z Z' C N k Em f q K _ w β hβ ξ hξ
  obtain ⟨A', hA'⟩ := Em.linv β
  have h1 : A'.map (ev (w ≫ f) _ hβ) * (Em.A β).map (ev (w ≫ f) _ hβ) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  have h := plk_point_iff _ _ h1 (w ≫ q) ξ hξ
  refine ⟨h.1, h.2, fun α hα => ?_⟩
  obtain ⟨u, hu⟩ := Em.compat α β K (w ≫ f) hα hβ
  exact plk_point_change _ _ _ u hu (w ≫ q) ξ hξ

end GlobalTheory.GrCl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_holds_local_tangent_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z Z' : Mdl Y i₀) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ), Step.Holds ⟨Z, Lat.top Z, σ, r, hr⟩ Z' → ∀ x : Z'.X, ∃ (U : Z'.X.Opens) (hU : IsAffineOpen U) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Z'.X, U)) ⟶ (Y Z'.i).t.G.left)), x ∈ U ∧ (∀ j, IsTanAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) (v j)) ∧ (∀ u, IsTanAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) u → ∃! cf, IsCombAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) v cf u) ∧ ∀ (k : Type) [Field k] (φ : Γ(Z'.X, U) →+* k) (u : Vecs Dw (Y Z'.i).t k), Z'.FlagAt (spMap φ ≫ hU.fromSpec) u → ∀ i : Fin (Dw.mult σ), (i : ℕ) < r → ∃ cf : Fin n → k, (∀ j : Fin n, r ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z'.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ v j) cf (u σ i) := by
  first | exact @GlobalTheory.LocM.StepBasis.exists_basis | exact GlobalTheory.LocM.StepBasis.exists_basis | (intros; apply GlobalTheory.LocM.StepBasis.exists_basis <;> assumption)
end


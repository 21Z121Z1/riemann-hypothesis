import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstantsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFrame_change_by_constants : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th th' : a.D₀.P.L.Sec) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (r : A), ThNZ th → (∀ τ k, GtComb (g τ k) (e τ) (e' τ k)) → ThMul r th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y y' : FrPt Xo c S), Mono Y.j → IsArcFr W e th ι y → FrChg (fun τ => (g τ).map (ι.comp (PowerSeries.C (R := A)))) (ι (PowerSeries.C (R := A) r)) y y' → IsArcFr W e' th' ι y' := by
  first | exact @GlobalTheory.ArcQ.isArcFr_of_frChg_const | exact GlobalTheory.ArcQ.isArcFr_of_frChg_const | (intros; apply GlobalTheory.ArcQ.isArcFr_of_frChg_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtensionStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_model_witness_extension : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), IsTypeFn H Dw.p Dw.q ty → ∀ th : a.D₀.P.L.Sec, ThNZ th → Nonempty (ThetaDat Ha th) := by
  first | exact @GlobalTheory.ArcTheta.nonempty_thetaDat | exact GlobalTheory.ArcTheta.nonempty_thetaDat | (intros; apply GlobalTheory.ArcTheta.nonempty_thetaDat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChainLevelPtOfSection
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem chain_levelPt_of_section (h1 : Out.Laws) (h2 : Out.Laws2) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ)
    (k : ℕ) [NeZero k] (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (ξ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : Λ.A.La)
    (hξ : ξ.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ ξ₀.left)
    (hk : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v))
    (hrep : Λ.Rep k p₀ la) : C.Φ.LevelPt k (toUnit _ ≫ ξ₀) la := by
  have hξw : ξ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w ξ
  have hY : (C.yF ≫ ξ.left ≫ Y.m.φ) ≫ Y.t.G.hom = gen ≫ χ := by
    have := Y.m.cart.1.w
    rw [Category.assoc, Category.assoc, this, ← Category.assoc ξ.left, hξw, Category.id_comp]
    exact C.yF_j
  let p : Over.mk gen ⟶ W.t.G :=
    Over.homMk (W.m.cart.1.lift (C.yF ≫ ξ.left ≫ Y.m.φ) gen hY) (W.m.cart.1.lift_snd _ _ _)
  have hp : p.left ≫ W.m.φ = C.yF ≫ ξ.left ≫ Y.m.φ := W.m.cart.1.lift_fst _ _ _
  let pY : Over.mk (gen ≫ χ) ⟶ Y.t.G := Over.homMk (C.yF ≫ ξ.left ≫ Y.m.φ) hY
  let pF : Over.mk C.yF ⟶ Y.oF.t.G := toUnit _ ≫ ξ
  have hpF : pF.left = C.yF ≫ ξ.left := rfl
  have hW := GlobalTheory.T.levelPoints_of_arc_eq_period_div_level h1 h2 E H D l Xo c O β Y (bF.comp β) a χ W Λ C.Ξ C.ΦW C.yF k p₀ ξ la p C.isGen C.yF_j
    hk hrep hp
  have h₂ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ W.m C.w₂ _ _ C.ΦW C.ΦY C.rig₂.1 C.rel₂).1 k p pY la hp
  have h₁ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m C.w₁ _ _ C.ΦF C.ΦY C.rig₁.1 C.rel₁).1 k pF pY la
    (by rw [hpF, Category.assoc]; rfl)
  have h₀ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m0.toSABMap C.w₀ _ _ C.ΦF C.Φ C.rig₀.1 C.rel₀).1 k pF
    (toUnit _ ≫ ξ₀) la (by rw [hpF, Category.assoc, hξ, ← Category.assoc]; rfl)
  exact h₀.1 (h₁.2 (h₂.1 hW))

theorem chain_levels : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (laA laM : D.La → Λ.A.La), (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → (∀ v, C.Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) ∧ ∀ v ∈ idealPart D l, C.Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v) := by
  intro h1 h2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C laA laM hA hM
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.A (a.etaA v) (Y.oF.etaA v)
      (Xo.univ.etaA v) (laA v) (Y.m0.etaA v) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩) (hA v)
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.M (a.eta v) (Y.oF.eta v)
      (Xo.univ.eta v) (laM v) (Y.m0.eta v) (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩) (hM v)

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSum
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.WeightZero

theorem valR_pullGen_spMap {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A'] {Z : Scheme.{0}} (L : LB Z)
    {K : Type} [Fintype K] (φ : K → (Sp A ⟶ Z)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (f : A →+* A')
    (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j) :
    valR (𝟙 (Sp A')) (LB.wchart L (fun k => spMap f ≫ φ k) j) ((LB.pullGen L φ ε t (spMap f)).s j).val =
      f (valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val) := by
  have h₀ : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L φ j := h
  have h₁ : ⊤ ≤ (𝟙 (Sp A')) ⁻¹ᵁ LB.wchart L (fun k => spMap f ≫ φ k) j := fun z _ =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)) k
  apply toStkA_injective
  refine (toStkA_valR _ _ _ h₁ _).trans ((congrArg Units.val (gm_pullGen' L φ ε t (spMap f) (𝟙 _) _ j)).trans ?_)
  refine Eq.trans ?_ (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _))
  refine Eq.trans ?_ (toStkA_valR _ _ _ (FormalValue.top_le_comp h₀ (spMap f)) _).symm
  rw [Category.id_comp, Category.comp_id]

theorem coordVal_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {s : Sp S ⟶ Sp R} (g : Out.GtPt D.toPre (Over.mk s)) {jM : D.toPre.P.L.ι} {jf jt : Fin 4 → D.toPre.P.L.ι}
    (h : FormalValue.CohCharts g 0 jM jf jt) : FormalValue.coordVal g 0 jt = 1 := by
  have e := g.s_zero jt PEmpty.elim (fun a b hab => h.2.2 (.inr (.inr a)) (.inr (.inr b)) hab) (fun a => a.elim)
    (fun _ a => a.elim)
  have ht : ⊤ ≤ (𝟙 (Sp S)) ⁻¹ᵁ (LB.wchart D.toPre.P.L (FormalValue.coordφ g 0) jt ⊓
      LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim PEmpty.elim) := fun z hz =>
    ⟨h.2.1 hz, Set.mem_iInter.2 fun k => k.elim⟩
  refine (Points.valR_res (𝟙 (Sp S)) inf_le_left ht _).symm.trans ?_
  refine (congrArg (fun q => valR (𝟙 (Sp S)) _ (Units.val q)) (e.trans (map_one _))).trans ?_
  exact Points.valR_one _ _ ht

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

theorem basePt_comp (v : Λ.A.V) :
    FormalValue.basePt (Ξ.g v) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem b_eq {v v' : Λ.A.V} (h : v.2 = v'.2) : (Ξ.g v).b = (Ξ.g v').b := by
  refine Over.OverMorphism.ext (W.spec.1.1.hom_ext ?_ ?_)
  · exact (basePt_comp Ξ v).trans (h ▸ (basePt_comp Ξ v').symm)
  · exact (Over.w (Ξ.g v).b).trans (Over.w (Ξ.g v').b).symm

theorem exists_base_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (FormalValue.basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (basePt_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

omit Ξ in

theorem coordinate_complexConstantPoint_eq_char_mul (z : Fin Λ.A.gB → ℂ) (x : Λ.A.X) : ∃ (j₀ : Fin 4 → a.D₀.P.L.ι) (k : ℂ), ∀ l : Λ.A.X →+ ℂ,
    ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (l, z)).b (Λ.ε x)) j₀ ∧
      valR (𝟙 (Sp ℂ)) (LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (l, z)).b (Λ.ε x)) j₀)
        (((Λ.ex0 (l, z)).s (Λ.ε x)).s j₀).val = eTwoPi (l x) * k := by
  refine ⟨fun k => FrameValue.chartAt a.D₀.P.isLB
    ((show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (0, z)).b (Λ.ε x) k),
    FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + z, Λ.A.ct x, z, 0] fun k => FrameValue.chartAt a.D₀.P.isLB
    ((show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 (0, z)).b (Λ.ε x) k), fun l => ?_⟩
  have hb : (Λ.ex0 (0, z)).b = (Λ.ex0 (l, z)).b :=
    Over.OverMorphism.ext ((Λ.ex0_b (0, z)).trans (Λ.ex0_b (l, z)).symm)
  rw [hb]
  refine ⟨FrameValue.le_wchart_chartAt a.D₀.P.isLB _ (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)), ?_⟩
  have key : ∀ p q r : ℂ, p / q = r → r ≠ 0 → p = r * q := fun p q r h hr =>
    (div_eq_iff (by rintro rfl; exact hr (h.symm.trans (div_zero p)))).1 h
  exact key _ _ _ (Λ.arcDict_expZero_section (l, z) x) (AnArc.e_ne_zero _)

theorem coordVal_eq (z : Fin Λ.A.gB → ℂ) (x : Λ.A.X) (jt : Fin 4 → W.P.D.toPre.P.L.ι)
    (h : ⊤ ≤ LB.wchart W.P.D.toPre.P.L (FormalValue.coordφ (Ξ.g (0, z)) (W.e (Λ.ε x))) jt) (l : Λ.A.X →+ ℂ) :
    FormalValue.coordVal (Ξ.g (l, z)) (W.e (Λ.ε x)) jt =
      PowerSeries.C (eTwoPi (l x)) * FormalValue.coordVal (Ξ.g (0, z)) (W.e (Λ.ε x)) jt := by
  obtain ⟨j₀, k, hk⟩ := coordinate_complexConstantPoint_eq_char_mul (Λ := Λ) z x
  let P : (selfR ⟶ W.P.D.toPre.P.A) → ℂ⟦X⟧ := fun p => ∏ i, valR (A := ℂ⟦X⟧)
    (Out.DegPre.gtφT W.P.D.toPre selfR p (W.e (Λ.ε x)) i) _
      ((show (Γ(W.P.D.toPre.P.A.left, (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jt i)))ˣ from
        W.w.s (fun _ => j₀ i, jt i)) ^ (-Out.DegPre.gtε i)).val
  have key : ∀ l : Λ.A.X →+ ℂ, FormalValue.coordVal (Ξ.g (l, z)) (W.e (Λ.ε x)) jt =
      P (Ξ.g (0, z)).b * PowerSeries.C (eTwoPi (l x) * k) := by
    intro l
    have hb : (Ξ.g (0, z)).b = (Ξ.g (l, z)).b := b_eq Ξ rfl
    have h' : ⊤ ≤ LB.wchart W.P.D.toPre.P.L (Out.DegPre.gtφT W.P.D.toPre selfR (Ξ.g (l, z)).b (W.e (Λ.ε x))) jt :=
      hb ▸ h
    obtain ⟨r₁, r₂⟩ := Ξ.g_rel (l, z) (Λ.ε x)
    rw [hb, ← (hk l).2]
    refine (r₂ jt j₀ fun i y hy => ⟨mem_pull.2 ?_, Set.mem_iInter.1 (h' hy) i⟩).trans (congrArg (_ * ·) ?_)
    · exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (j₀ i)) (r₁ i)).mpr (Set.mem_iInter.1
        ((hk l).1 (show spMap (PowerSeries.C (R := ℂ)) y ∈ (⊤ : (Sp ℂ).Opens) from trivial)) i)
    · exact valR_pullGen_spMap (A := ℂ) a.D₀.P.L _ _ ((Λ.ex0 (l, z)).s (Λ.ε x)) _ j₀ (hk l).1
  rw [key, key]
  simp only [AddMonoidHom.zero_apply, AnArc.e_zero, _root_.one_mul, map_mul]
  ring

variable {th : a.D₀.P.L.Sec} {σ : Out.H0 W.P.U.LG.L 1} {fam : ∀ x, W.P.D.toPre.SecB 1 x}
  {θ : (Fin Λ.A.gB → ℂ) → ℂ}

theorem famVal_zero (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) (v : Λ.A.V) {jM : W.P.D.toPre.P.L.ι}
    {j₀ : a.D₀.P.L.ι} {jf jt : Fin 4 → W.P.D.toPre.P.L.ι} (hc : FormalValue.CohCharts (Ξ.g v) 0 jM jf jt)
    (hj : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM))
    (h₀ : ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀) :
    valR (FormalValue.basePt (Ξ.g v)) _ (W.w.s (fun _ => j₀, jM)).val * FormalValue.famVal (Ξ.g v) (fam 0) jf =
      PowerSeries.C (θ v.2 * Λ.u.fr j₀ v.2) := by
  have e₁ : W.P.D.toPre.famφB 0 1 = 𝟙 _ := by
    have : (𝟙 W.P.D.toPre.P.A) * DVR.cP W.P.D.toPre W.P.D.toPre.P.A 0 = 𝟙 _ := by rw [cPoint_zero, _root_.mul_one]
    exact congrArg Over.Hom.left this
  obtain rfl : jf 1 = jM := hc.2.2 (.inr (.inl 1)) (.inl PUnit.unit)
    ((congrArg (FormalValue.basePt (Ξ.g v) ≫ ·) e₁).trans (Category.comp_id _))
  have hV : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) jf ⊓
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jf 1) ⊓ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀) := fun y hy =>
    ⟨⟨hc.1 hy, hj hy⟩, mem_pull.1 (hj hy).1⟩
  have e := congrArg (valR (FormalValue.basePt (Ξ.g v)) _) (h.2.2 jf j₀ _ (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right
    (fun i i' hi => hc.2.2 (.inr (.inl i)) (.inr (.inl i')) (congrArg (FormalValue.basePt (Ξ.g v) ≫ ·) hi)))
  rw [Points.valR_appLE _ _ _ hV, Points.valR_mul _ _ hV, basePt_comp, FormalValue.valR_spMap _ _ _ h₀] at e
  refine (congrArg₂ (· * ·) (Points.valR_res _ _ hV _) (Points.valR_res _ _ hV _)).symm.trans (e.symm.trans ?_)
  exact congrArg _ (hθ j₀ v.2 h₀)

theorem cohCharts_congr {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {s : Sp S ⟶ Sp R} {g g' : Out.GtPt D.toPre (Over.mk s)} (e : g.b = g'.b) {α : D.toPre.X} {jM : D.toPre.P.L.ι}
    {jf jt : Fin 4 → D.toPre.P.L.ι} (h : FormalValue.CohCharts g α jM jf jt) : FormalValue.CohCharts g' α jM jf jt := by
  dsimp only [FormalValue.CohCharts, FormalValue.basePt, FormalValue.coordφ] at h ⊢
  rw [← e]
  exact h

theorem exists_expansion (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) {f : Λ.A.V → ℂ⸨X⸩} (hf : Ξ.Vals σ f)
    (z : Fin Λ.A.gB → ℂ) (e : ℕ) : ∃ (F : Finset Λ.A.X) (B : Λ.A.X → ℂ⟦X⟧), 0 ∈ F ∧ B 0 = PowerSeries.C (θ z) ∧
      ∀ l : Λ.A.X →+ ℂ, ∃ p : ℂ⟦X⟧, f (l, z) = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ p ∧
        PowerSeries.coeff e p = PowerSeries.coeff e (∑ x ∈ F, PowerSeries.C (eTwoPi (l x)) * B x) := by
  classical
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))) e
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq W.P.U.toUnifPre (h.2.1 e)
  let ι₀ : Λ.A.X ≃ W.P.D.toPre.X := (Λ.ε.trans W.e).toEquiv
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_base_charts Ξ (0, z)
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g (0, z)) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun y hy => (hj hy).2
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g (0, z)) jM hM
  have hfr : PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * PowerSeries.C (Λ.u.fr j₀ z) = (1 : ℂ⟦X⟧) := by
    rw [← map_mul, inv_mul_cancel₀ (Λ.u.fr_ne j₀ z h₀), map_one]
  obtain ⟨w, hw⟩ : ∃ w, w = valR (FormalValue.basePt (Ξ.g (0, z))) _ (W.w.s (fun _ => j₀, jM)).val := ⟨_, rfl⟩
  let B : W.P.D.toPre.X → ℂ⟦X⟧ := fun α => PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w *
    (FormalValue.famVal (Ξ.g (0, z)) (fam α) (jf α) * FormalValue.coordVal (Ξ.g (0, z)) α (jt α))
  refine ⟨insert 0 (F.map ι₀.symm.toEmbedding), fun x => B (ι₀ x), Finset.mem_insert_self _ _, ?_, fun l => ?_⟩
  · have : ι₀ 0 = 0 := map_zero (Λ.ε.trans W.e)
    have e₀ := famVal_zero Ξ h hθ (0, z) (hc 0) hj h₀
    rw [← hw, map_mul] at e₀
    simp only [this, B]
    rw [coordVal_zero _ (hc 0), _root_.mul_one, _root_.mul_assoc, e₀, mul_left_comm, hfr, _root_.mul_one]
  have hb : (Ξ.g (0, z)).b = (Ξ.g (l, z)).b := b_eq Ξ rfl
  have hb' : FormalValue.basePt (Ξ.g (0, z)) = FormalValue.basePt (Ξ.g (l, z)) := congrArg Over.Hom.left hb
  obtain ⟨jL, hL⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x (l, z)).left) (cpt ℂ⟦X⟧))
  replace hL := (top_le_iff_cpt _ _).2 hL
  rw [hb'] at hj hM hw
  have e₁ := Ξ.τ_eq (l, z) jL jM j₀ hL hj
  have e₂ := hf (l, z) jL hL
  have e₃ := (hF _ _ _ (Ξ.g (l, z)) _ (Ξ.x_fm (l, z)) _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((insert 0 (F.map ι₀.symm.toEmbedding)).map ι₀.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨ι₀.symm α, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hα),
      ι₀.apply_symm_apply α⟩) hL hM (fun α _ => cohCharts_congr hb (hc α))
  replace e₁ := (congrArg (· * _) hw).trans e₁
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (Ξ.x (l, z)).left jL jM = t at e₁ e₃
  generalize FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x (l, z)).left jL = s at e₂ e₃
  rw [pow_one] at e₂ e₃
  refine ⟨PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val * s, ?_, ?_⟩
  · have e₄ : PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val * Ξ.τ (l, z) jL = 1 := by
      have := t.inv_mul
      linear_combination (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * t⁻¹.val) * e₁ +
        (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * PowerSeries.C (Λ.u.fr j₀ z)) * this + hfr
    rw [map_mul, e₂, mul_left_comm, ← map_mul, e₄, map_one, _root_.mul_one]
  · have e₅ := Ideal.mul_mem_left _ (PowerSeries.C (Λ.u.fr j₀ z)⁻¹ * w * t⁻¹.val) (Ideal.Quotient.eq.1 e₃)
    rw [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at e₅
    have e₆ := e₅ e (Nat.lt_succ_self e)
    rw [mul_sub, map_sub, sub_eq_zero] at e₆
    refine e₆.trans (congrArg _ ?_)
    rw [_root_.mul_assoc _ t⁻¹.val, Units.inv_mul_cancel_left, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have a₁ : FormalValue.famVal (Ξ.g (l, z)) (fam (ι₀ x)) (jf (ι₀ x)) =
        FormalValue.famVal (Ξ.g (0, z)) (fam (ι₀ x)) (jf (ι₀ x)) := congrArg (fun q => valR q _ _) hb'.symm
    have a₂ : FormalValue.coordVal (Ξ.g (l, z)) (ι₀ x) (jt (ι₀ x)) =
        PowerSeries.C (eTwoPi (l x)) * FormalValue.coordVal (Ξ.g (0, z)) (ι₀ x) (jt (ι₀ x)) :=
      coordVal_eq Ξ z x _ (hc (ι₀ x)).2.1 l
    refine (congrArg (_ * ·) (congrArg₂ (· * ·) a₁ a₂)).trans ?_
    simp only [B]
    ring

theorem exists_coeff_expansion (h : ThetaHyp W th σ fam) (hθ : Λ.u.IsFn th θ) {f : Λ.A.V → ℂ⸨X⸩} (hf : Ξ.Vals σ f)
    (z : Fin Λ.A.gB → ℂ) (n : ℤ) : ∃ (F : Finset Λ.A.X) (b : Λ.A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : Λ.A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x) := by
  obtain ⟨F, B, hF, hB, hl⟩ := exists_expansion Ξ h hθ hf z n.natAbs
  refine ⟨F, fun x => if n < 0 then 0 else PowerSeries.coeff n.natAbs (B x), hF, ?_, fun l => ?_⟩
  · simp only [hB, PowerSeries.coeff_C, Int.natAbs_eq_zero]
    split_ifs with h₁ h₂
    · omega
    all_goals rfl
  · obtain ⟨p, hp, hc⟩ := hl l
    rw [hp, LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · rw [hc, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [PowerSeries.coeff_C_mul, mul_comm]

theorem vals_FSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ), ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → Λ.u.IsFn th θ → Ξ.Vals σ (fun v => Λ.A.FSum 1 0 θ v) := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ th σ fam θ h _ hθ
  obtain ⟨f, hc, hf, -⟩ := GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ 1 σ
  have e : f = fun v => Λ.A.FSum 1 0 θ v := funext (eq_FSum Λ.A hc θ (exists_coeff_expansion Ξ h hθ hf))
  exact e ▸ hf

end GlobalTheory.ArcPts.WeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValues
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GenericPoints

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  have g := GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  have f := GlobalTheory.T.constantPointFrame_isFrame_with_rigidification h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  exact exists_genPts Λ.A W.t W.P.U.LG W.P.bundle Ξ.x Ξ.τ g.1 g.2 f.1 f.2
    (fun j _ α th hth => GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth)
    (fun j _ σ => GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j σ)
    (fun k hk s => exists_clear W.P.U k hk s)

end GlobalTheory.GenericPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentConstantCoordsGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_constant_coords_generic_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  first | exact @GlobalTheory.ConstTan.isTan_of_diffHyp | exact GlobalTheory.ConstTan.isTan_of_diffHyp | (intros; apply GlobalTheory.ConstTan.isTan_of_diffHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamily
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FamilyUnique

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F)) (hw : IsRigIso m L' L w) (hw' : IsRigIso m' L'' L' w') :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F), IsRigIso n L'' L w'' ∧
      ∀ (F : Type) [Field F] (x : Sp F ⟶ G''.left) (x' : Sp F ⟶ G'.left) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        x ≫ m'.F = x' →
        ⊤ ≤ x' ⁻¹ᵁ (LB.div (L.L.pull m.F) L'.L).U (fun _ => j, i) →
        ⊤ ≤ x ⁻¹ᵁ (LB.div (L'.L.pull m'.F) L''.L).U (fun _ => i, k) →
        valR x _ (w''.s (fun _ => j, k)).val =
          valR x' _ (w.s (fun _ => j, i)).val * valR x _ (w'.s (fun _ => i, k)).val := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw'
  obtain ⟨g, r⟩ := hw
  obtain ⟨g', r'⟩ := hw'
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  refine ⟨w'', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_comp L'.isLB g g', T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r'⟩, ?_⟩
  rintro F _ x x' j i k rfl h₁ h₂
  have a₁ := h₁ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have a₂ := h₂ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have hj : m.F (m'.F (x (cpt F))) ∈ L.L.U j := mem_pull.1 a₁.1
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (LB.div (L.L.pull (m'.F ≫ m.F)) L''.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull₂.2 hj, a₂.2⟩
  apply toStkA_injective
  rw [map_mul]
  exact (toStkA_valR x _ _ h₃ _).trans ((congrArg Units.val (T _ x (cpt F) j i k hj a₁.2 a₂.2)).trans
    (congrArg₂ (· * ·) (toStkA_valR _ _ _ h₁ _).symm (toStkA_valR _ _ _ h₂ _).symm))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_eq {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap = m := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem points_frames_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  intro hL hL2 E _ _ _ H _ D l Xo F _ _ _ V _ act I φ y₁ y₂ Θ₁ Θ₂ hy hA hM
  obtain ⟨o₁, m₁, w₁, Θ₁', rw₁, p₁, lev₁⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₁ _ Θ₁ hy
  obtain ⟨o₂, m₂, w₂, Θ₂', rw₂, p₂, lev₂⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₂ _ Θ₂ rfl
  obtain ⟨m, w, rw₀, p⟩ := GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂'
  have key : ∀ (k : ℕ) (x₁ : 𝟙_ (Over (Sp F)) ⟶ o₁.t.G) (x₂ : 𝟙_ (Over (Sp F)) ⟶ o₂.t.G)
      (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G), 1 ≤ k → x₁.left ≫ m₁.φ = y₁ ≫ x.left → x₂.left ≫ m₂.φ = y₂ ≫ x.left →
      (∃ ψ, Θ₁.Lev k (toUnit _ ≫ x) ψ ∧ Θ₂.Lev k (toUnit _ ≫ x) ψ) → x₁.left ≫ m.φ = x₂.left := by
    rintro k x₁ x₂ x hk k₁ k₂ ⟨ψ, a₁, a₂⟩
    exact GlobalTheory.T.triple_iso_respects_level_ratio_points hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂' m w k ψ x₁ x₂ hk rw₀.1 p
      (lev₁ k ψ _ x₁ hk k₁ a₁) (lev₂ k ψ _ x₂ hk k₂ a₂)
  obtain ⟨n, rfl⟩ := exists_objMap_eq o₁ o₂ m
    (fun a ha => key l.M _ _ _ (le_trans (by norm_num) l.three_le) (m₁.eta a) (m₂.eta a) (hM a ha))
    (fun a => key l.A _ _ _ l.A_pos (m₁.etaA a) (m₂.etaA a) (hA a))
  obtain ⟨n', hn'⟩ := ObjComp.objMap_comp m₂ n
  have e : y₁ = 𝟙 _ ≫ y₂ := (Xo.rep _ _ inferInstance o₁).unique ⟨hy, ⟨m₁⟩⟩ ⟨by rw [Category.id_comp], ⟨n'⟩⟩
  subst e
  have hφ : m₁.toSABMap.φ = n.toSABMap.φ ≫ m₂.toSABMap.φ := (objMap_unique_of_field hL.serre m₁ n').trans hn'
  obtain ⟨w', rw', hval⟩ := exists_rigIso_comp m₂.cm n.cm m₁.cm hφ
    (m₁.base.trans (congrArg₂ (· ≫ ·) n.base m₂.base).symm) _ _ _ w₂ w rw₂ rw₀
  intro v
  have hx : (Θ₁.x v).left = (Θ₂.x v).left := by
    rw [← (p₁ v).1, ← (p₂ v).1, ← (p v).1, hφ, Category.assoc]
  refine ⟨hx, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart o₁.t.PP.isLB ((Θ₁'.x v).left (cpt F))
  obtain ⟨i, hi⟩ := exists_chart o₂.t.PP.isLB ((Θ₂'.x v).left (cpt F))
  have hj₀ := (top_le_iff_cpt _ _).1 hj
  have c₁ : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₁.toSABMap.φ) o₁.t.PP.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p₁ v).1] at hj₀; exact hj₀), hk⟩
  have c₂ : ⊤ ≤ (Θ₂'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₂.toSABMap.φ) o₂.t.PP.L).U (fun _ => j, i) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [hx, ← (p₂ v).1] at hj₀; exact hj₀), hi⟩
  have c : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull n.toSABMap.φ) o₁.t.PP.L).U (fun _ => i, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p v).1] at hi; exact hi), hk⟩
  have := o₁.proper
  have u := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t o₁.t _ m₁.toSABMap).2 w₁ w' rw₁ rw' F (𝟙 _) (Θ₁'.x v)
    inferInstance j k c₁
  rw [(p₁ v).2 j k c₁, (p₂ v).2 j i c₂, (p v).2 i k c, ← _root_.mul_assoc]
  exact congrArg (· * _) (u.trans (hval F _ _ j i k (p v).1 c₂ c))

end GlobalTheory.FamilyUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompareStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_l2_family_uniform_compare : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Pm' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (s : CAt σ) (v v' : ℝ), IsPeriod (Fu.Di i) ty Pm → IsPeriod (Fu.Di i') ty Pm' → y.x = Fu.u i Pm → y'.x = Fu.u i' Pm' → FrChg G s y y' → IsThetaL2NormSquared Fu i Pm y v → IsThetaL2NormSquared Fu i' Pm' y' v' → 0 < v ∧ v' = ‖toC s‖ ^ 2 * v := by
  first | exact @GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | exact GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | (intros; apply GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangentStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), (∀ ν, GtTanR ν → ∃! z₀, AnVec Ha ν z₀) ∧ (∀ z₀, ∃! ν, AnVec Ha ν z₀) ∧ (∀ ν z₀, AnVec Ha ν z₀ → GtTanR ν) ∧ ∀ (m : ℕ) (cf : Fin m → ℂ) (e : Fin m → Out.GtPt a.D₀ (epsR ℂ)) (z : Fin m → (Fin g → ℂ)) ν, (∀ i, AnVec Ha (e i) (z i)) → (GtComb cf e ν ↔ AnVec Ha ν (∑ i, cf i • z i)) := by
  first | exact @GlobalTheory.ExpTan.anVec_bijective | exact GlobalTheory.ExpTan.anVec_bijective | (intros; apply GlobalTheory.ExpTan.anVec_bijective <;> assumption)
end


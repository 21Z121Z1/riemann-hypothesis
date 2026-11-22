import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0018
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMul

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChangeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePeriods_along_isotropic_flow_and_block_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  first | exact @GlobalTheory.PerFlow.perFr_flow_block | exact GlobalTheory.PerFlow.perFr_flow_block | (intros; apply GlobalTheory.PerFlow.perFr_flow_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem evR_frBor_of_isDomain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsDomain S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  let φ : S →ₐ[c.F] FractionRing S := IsScalarTower.toAlgHom c.F S (FractionRing S)
  have hφ : Function.Injective φ := IsFractionRing.injective S (FractionRing S)
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (FractionRing S)ˣ := fun i => Units.map (φ : S →* FractionRing S) (t i)
  have hb : FrBor t' z z' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c (FractionRing S)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := hL.wt a n F hF _ t' z z' (hL.test _ _) (hL.test _ _) hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  apply hφ
  rw [hw, map_mul]
  congr 1
  simp [wchar, t']

theorem evR_natural_weight_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∀ (S : Type) [CommRing S] [Algebra c.F S] [IsReduced S], (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c F z = φ (evR Xo c F y)) ∧ (IsDomain S → (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y) ∧ ∀ (s : S) (y y' : FrPt Xo c S), FrChg (fun _ => 1) s y y' → evR Xo c F y' = s ^ n * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c hL a n F hF S _ _ _
  refine ⟨fun T _ _ φ y z h => GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S T φ y z h,
    fun hD => ⟨fun t y y' h => evR_frBor_of_isDomain hL hF t y y' h, fun s y y' h => ?_⟩⟩
  obtain ⟨u, rfl⟩ := ((GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [evR_frBor_of_isDomain hL hF t y y' hb]
  congr 1
  simp [wchar, t, ex, Fintype.prod_option]

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermMemConvLaurent
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcSectionValue

section General

variable {A B K : Type} [CommRing A] [CommRing B] [CommRing K] {Z : Scheme.{0}}

theorem spMap_cancel {ρ : A →+* B} (hρ : Function.Injective ρ) {f g : Sp A ⟶ Sp K}
    (h : spMap ρ ≫ f = spMap ρ ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact hρ (congrArg (fun q => q.hom a) h')

theorem valR_const (p : Z ⟶ Sp K) (f : K →+* A) (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) (U : Z.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq]
  exact Conv.valR_spMap_top f a

theorem exists_chart_local [IsLocalRing A] (x : Sp A ⟶ Z) {L : LB Z} (hL : L.IsLB) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have : x (IsLocalRing.closedPoint A) ∈ ⨆ j, L.U j := hL.cover ▸ trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨j, ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ L.U j)).1 hj).ge⟩

theorem le_div_iff {Z' : Scheme.{0}} (x : Sp A ⟶ Z') (φ : Z' ⟶ Z) (L : LB Z) (M : LB Z') (j : L.ι) (k : M.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) M).U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ M.U k :=
  ⟨fun h => ⟨fun _ hz => Set.mem_iInter.1 (h hz).1 PUnit.unit, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨Set.mem_iInter.2 fun _ => h.1 hz, h.2 hz⟩⟩

theorem exists_rigIso_of_eq {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) {L₁ L₂ : RigLB G'} (h : L₁ = L₂) (L : RigLB G)
    (w : LB.Iso L₁.L (L.L.pull m.F)) (hw : IsRigIso m L₁ L w) (k₁ : L₁.L.ι) :
    ∃ (w' : LB.Iso L₂.L (L.L.pull m.F)) (k₂ : L₂.L.ι), IsRigIso m L₂ L w' ∧ HEq k₁ k₂ ∧ L₁.L.U k₁ = L₂.L.U k₂ ∧
      ∀ (x : Sp A ⟶ G'.left) (j : L.L.ι),
        valR x _ (w.s (fun _ => j, k₁)).val = valR x _ (w'.s (fun _ => j, k₂)).val := by
  subst h
  exact ⟨w, k₁, hw, HEq.rfl, rfl, fun _ _ => rfl⟩

end General

section Germ

variable (Γ : Germs) (w : ℂ)

theorem isLocalRing_germ : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by simp [h]))
    · exact Or.inl (Γ.unit w _ h)

theorem germ_mem_convLaurent (f : Γ.R w) : (f : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  obtain ⟨T, hw, a, s, hs, h⟩ := Γ.frac w f
  have hs' : (s : ℂ⸨X⸩) ≠ 0 := fun e => hs (by rw [show s = 0 from Subtype.ext e, map_zero])
  have : (f : ℂ⸨X⸩) = a / s := by rw [← h]; field_simp
  rw [this]
  exact div_mem (Conv.halfRing_le_convLaurent T a.2) (Conv.halfRing_le_convLaurent T s.2)

theorem le_of_ev {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) {U : Z.Opens}
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  haveI := isLocalRing_germ Γ w
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← IsLocalRing.comap_closedPoint (Γ.ev w).toRingHom]
  exact this

end Germ

theorem exists_le_halfPlane {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ (T' : ℝ) (h : T ≤ T'), ⊤ ≤ (spMap (Subalgebra.inclusion (Conv.halfRing_mono h) :
      Conv.halfRing T →+* Conv.halfRing T') ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  refine Conv.exists_le_preimage_inclusion yT fun p _ => ?_
  rw [hfac] at hU
  obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
    Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
  exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial

theorem exists_fsum_ne_zero {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {θ : (Fin A.gB → ℂ) → ℂ} (h : θ ≠ 0) :
    ∃ v, A.FSum 1 0 θ v ≠ 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h
  refine ⟨(0, z), fun e => hz ?_⟩
  have hl : A.level 1 0 0 = {0} := by
    ext m
    rw [AnArc.mem_level, Finset.mem_singleton]
    have h2 := A.two_mul_exponent 1 0 m
    refine ⟨fun h0 => by_contra fun hm => ?_, fun h0 => by simp [h0, AnArc.exponent]⟩
    have := A.be_pos m hm
    simp [h0] at h2
    omega
  have := A.coeff_FSum 1 0 θ (0, z) 0
  rw [e, hl] at this
  simpa [AnArc.term] using this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_germ_lift (Y : Model Xo c β) (bF : c.F →+* ℂ) {A : AnArc (𝓞 E)} {yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c}
    (hover : yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    (ΦF : GenPts A Y.oF.t yF) {Φ : GenPts A Xo.univ.t (yF ≫ pullback.fst _ _)}
    (hx : ∀ v, (ΦF.x v).left ≫ Y.m0.toSABMap.φ = (Φ.x v).left) {Γ : Germs} (Ψ : SpecPts Φ Γ)
    (U : (Xo.XF c).Opens) (hU : ⊤ ≤ yF ⁻¹ᵁ U) :
    ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → ∃ hw : Ψ.T < w.im, ∀ v, ∃ xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left,
      xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left ∧ spMap (Γ.R w).val.toRingHom ≫ xg = (ΦF.x v).left ∧
      ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ U ∧
      ∀ x : Sp ℂ ⟶ Y.oF.t.G.left, x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left →
        x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → x = spMap (Γ.ev w).toRingHom ≫ xg := by
  have hb : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) =
      yF ≫ pullback.snd _ _ := by
    rw [hover, ← spMap_comp]; rfl
  have hs : Ψ.yT ≫ Xo.s = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    refine spMap_cancel (ρ := (Conv.halfRing Ψ.T).val.toRingHom) Subtype.val_injective ?_
    rw [← Category.assoc, Ψ.yT_gen, ← Category.assoc, hb, Category.assoc, Category.assoc, pullback.condition]
  let yT : Sp (Conv.halfRing Ψ.T) ⟶ Xo.XF c := pullback.lift _ _ hs
  have h1 : yT ≫ pullback.fst _ _ = Ψ.yT := pullback.lift_fst _ _ _
  have h2 : yT ≫ pullback.snd _ _ = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) := pullback.lift_snd _ _ _
  have hg : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ yT = yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, Ψ.yT_gen]
    · rw [Category.assoc, h2, hb]
  obtain ⟨T₁, hT, hU₁⟩ := exists_le_halfPlane yT (hg ▸ hU)
  refine ⟨T₁, fun w hw₁ => ⟨hT.trans_lt hw₁, fun v => ?_⟩⟩
  set hw := hT.trans_lt hw₁
  have hP := Y.m0.cart.1
  have hc : (Ψ.xt w hw v).left ≫ Xo.univ.t.G.hom =
      (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ yT) ≫ pullback.fst _ _ := by
    rw [Category.assoc, h1]
    exact Over.w (Ψ.xt w hw v)
  have e1 := hP.lift_fst _ _ hc
  have e2 := hP.lift_snd _ _ hc
  refine ⟨hP.lift _ _ hc, e1, ?_, ?_, fun x hx1 hx2 => ?_⟩
  · apply hP.hom_ext
    · rw [Category.assoc, e1, Ψ.xt_gen]
      exact (hx v).symm
    · rw [Category.assoc, e2, ← Category.assoc, ← spMap_comp]
      exact hg.trans (Over.w (ΦF.x v)).symm
  · rw [e2]
    have : spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom =
        spMap (Subalgebra.inclusion (Γ.le T₁ w hw₁)).toRingHom ≫ spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) :
          Conv.halfRing Ψ.T →+* Conv.halfRing T₁) := by
      rw [← spMap_comp]; rfl
    rw [this, Category.assoc]
    exact FormalValue.top_le_comp hU₁ _
  · have e3 : x ≫ Y.m0.toSABMap.φ = (spMap (Γ.ev w).toRingHom ≫ hP.lift _ _ hc) ≫ Y.m0.toSABMap.φ := by
      rw [hx1, Ψ.pi_eq w hw v, Category.assoc]
      exact congrArg _ e1.symm
    refine hP.hom_ext e3 (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, ← hP.w, ← Category.assoc, Category.assoc _ _ (pullback.fst _ _), ← hP.w, ← Category.assoc]
      exact congrArg (· ≫ Xo.univ.t.G.hom) e3
    · rw [Category.assoc, hx2, Category.assoc, Category.assoc, reassoc_of% e2, h2, ← spMap_comp, ← spMap_comp]
      congr 1
      ext a
      exact ((Γ.ev w).commutes (bF a)).symm

end GlobalTheory.ArcSectionValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.GermRing
open GlobalTheory.Conv

def Rep (w : ℂ) (f : ℂ⸨X⸩) (x : ℂ) : Prop :=
  ∃ (T : ℝ) (hw : T < w.im) (a s : halfRing T),
    ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s

theorem Rep.common {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hf : Rep w f x) (hg : Rep w g y) :
    ∃ (T : ℝ) (hw : T < w.im) (a s b t : halfRing T),
      (ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s) ∧
      (ev T w hw t ≠ 0 ∧ (t : ℂ⸨X⸩) * g = b ∧ ev T w hw b = y * ev T w hw t) := by
  obtain ⟨T, hw, a, s, h⟩ := hf
  obtain ⟨T', hw', b, t, h'⟩ := hg
  exact ⟨max T T', max_lt hw hw', ⟨a, halfRing_mono (le_max_left _ _) a.2⟩,
    ⟨s, halfRing_mono (le_max_left _ _) s.2⟩, ⟨b, halfRing_mono (le_max_right _ _) b.2⟩,
    ⟨t, halfRing_mono (le_max_right _ _) t.2⟩, h, h'⟩

theorem Rep.unique {w : ℂ} {f : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w f y) : x = y := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  have e : a * t = b * s := Subtype.ext (by
    push_cast
    rw [← h2, ← k2]; ring)
  have e' := congrArg (ev T w hw) e
  rw [map_mul, map_mul, h3, k3] at e'
  apply mul_right_cancel₀ (mul_ne_zero h1 k1)
  linear_combination e'

theorem Rep.add {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f + g) (x + y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * t + b * s, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_add, map_mul, map_mul, map_mul, h3, k3]; ring

theorem Rep.mul {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f * g) (x * y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * b, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_mul, map_mul, h3, k3]; ring

theorem rep_of_mem {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    Rep w (s : ℂ⸨X⸩) (ev T w hw s) :=
  ⟨T, hw, s, 1, by rw [map_one]; exact one_ne_zero, by simp, by rw [map_one, _root_.mul_one]⟩

theorem rep_algebraMap (w c : ℂ) : Rep w (algebraMap ℂ ℂ⸨X⸩ c) c := by
  have hw : w.im - 1 < w.im := sub_one_lt _
  have h := rep_of_mem hw (algebraMap ℂ (halfRing (w.im - 1)) c)
  rw [AlgHom.commutes] at h
  exact h

theorem Rep.inv {w : ℂ} {f : ℂ⸨X⸩} {x : ℂ} (hx : Rep w f x) (h0 : x ≠ 0) :
    ∃ g, Rep w g x⁻¹ ∧ f * g = 1 := by
  obtain ⟨T, hw, a, s, h1, h2, h3⟩ := hx
  have ha : ev T w hw a ≠ 0 := by rw [h3]; exact mul_ne_zero h0 h1
  have ha' : (a : ℂ⸨X⸩) ≠ 0 := fun h => ha (by rw [show a = 0 from Subtype.ext h, map_zero])
  have hf : f ≠ 0 := fun h => ha' (by rw [← h2, h, mul_zero])
  refine ⟨f⁻¹, ⟨T, hw, s, a, ha, ?_, ?_⟩, mul_inv_cancel₀ hf⟩
  · rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hf, _root_.mul_one]
  · rw [h3, ← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]

def ring (w : ℂ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ x, Rep w f x}
  mul_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.mul hy⟩
  add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.add hy⟩
  algebraMap_mem' c := ⟨c, rep_algebraMap w c⟩

def val (w : ℂ) (f : ring w) : ℂ := Classical.choose (show ∃ x, Rep w f x from f.2)

theorem rep_val (w : ℂ) (f : ring w) : Rep w f (val w f) := Classical.choose_spec (show ∃ x, Rep w f x from f.2)

def evRing (w : ℂ) : ring w →ₐ[ℂ] ℂ where
  toFun := val w
  map_one' := (rep_val w 1).unique (by simpa using rep_algebraMap w 1)
  map_mul' f g := (rep_val w (f * g)).unique ((rep_val w f).mul (rep_val w g))
  map_zero' := (rep_val w 0).unique (by simpa using rep_algebraMap w 0)
  map_add' f g := (rep_val w (f + g)).unique ((rep_val w f).add (rep_val w g))
  commutes' c := (rep_val w _).unique (rep_algebraMap w c)

def germs : Germs where
  R := ring
  ev := evRing
  unit w s hs := by
    obtain ⟨g, hg, h⟩ := (rep_val w s).inv hs
    exact IsUnit.of_mul_eq_one (⟨g, _, hg⟩ : ring w) (Subtype.ext h)
  le T w hw f hf := ⟨_, rep_of_mem hw ⟨f, hf⟩⟩
  ev_eq T w hw s := (rep_val w _).unique (rep_of_mem hw s)
  frac w f := by
    obtain ⟨T, hw, a, s, h1, h2, -⟩ := rep_val w f
    exact ⟨T, hw, a, s, h1, h2⟩

theorem germs_spec : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  refine ⟨⟨germs⟩, fun Γ w => ⟨?_, fun f => ?_, fun f g hf h => ?_⟩⟩
  · refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
    by_cases h : Γ.ev w f = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, map_one, h, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)
  · obtain ⟨T, hw, a, s, h1, h2⟩ := Γ.frac w f
    have hs : (s : ℂ⸨X⸩) ≠ 0 := fun h => h1 (by rw [show s = 0 from Subtype.ext h, map_zero])
    have e : (f : ℂ⸨X⸩) = (s : ℂ⸨X⸩)⁻¹ * a := by
      rw [← h2, ← _root_.mul_assoc, inv_mul_cancel₀ hs, _root_.one_mul]
    rw [e]
    exact mul_mem (convLaurent.inv_mem (halfRing_le_convLaurent T s.2)) (halfRing_le_convLaurent T a.2)
  · obtain ⟨k, hk⟩ := (Γ.unit w f hf).exists_left_inv
    have hk' : (k : ℂ⸨X⸩) * f = 1 := congrArg Subtype.val hk
    have e : g = k * (f * g) := by rw [← _root_.mul_assoc, hk', _root_.one_mul]
    rw [e]
    exact mul_mem k.2 h

end GlobalTheory.GermRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicCurve
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HalfPoint

theorem holomorphic_curve : ∀ (Z : Scheme.{0}) (T : ℝ) (yT : Sp (Conv.halfRing T) ⟶ Z) (yw : ℂ → (Sp ℂ ⟶ Z)), (∀ w (hw : T < w.im), yw w = spMap (Conv.ev T w hw).toRingHom ≫ yT) → IsHolTo {w : ℂ | T < w.im} yw ∧ ∀ (U : Z.Opens), ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U → (∃ T' ≥ T, ∀ (T'' : ℝ) (i : Conv.halfRing T →+* Conv.halfRing T''), T' ≤ T'' → (∀ r, (i r : ℂ⸨X⸩) = r) → ⊤ ≤ (spMap i ≫ yT) ⁻¹ᵁ U) ∧ ∀ f : Γ(Z, U), ∃ T' ≥ T, ∃ h : valR (spMap (Conv.halfRing T).val.toRingHom ≫ yT) U f ∈ Conv.halfRing T', ∀ w (hw : T' < w.im), ⊤ ≤ yw w ⁻¹ᵁ U ∧ valAt' (yw w) U f = Conv.ev T' w hw ⟨_, h⟩ := by
  intro Z T yT yw hyw
  have hc : ∀ w, T < w.im → yw w = Conv.halfCurve yT w := fun w hw =>
    (hyw w hw).trans (Conv.halfCurve_eq yT hw).symm
  refine ⟨fun U f => ?_, fun U hU => ?_⟩
  · have e : {b ∈ {w : ℂ | T < w.im} | ⊤ ≤ yw b ⁻¹ᵁ U} =
        {b ∈ {w : ℂ | T < w.im} | ⊤ ≤ Conv.halfCurve yT b ⁻¹ᵁ U} := by
      ext b
      exact and_congr_right fun hb => by rw [hc b hb]
    rw [e]
    obtain ⟨h1, h2⟩ := Conv.isHolTo_halfCurve yT U f
    exact ⟨h1, h2.congr fun b hb => by rw [hc b hb.1]⟩
  · have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
        spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
          (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
      rw [← Category.assoc, ← spMap_comp]
      rfl
    have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
      intro p _
      rw [hfac] at hU
      obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
        Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
      exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
    refine ⟨?_, fun f => ?_⟩
    · obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
      refine ⟨T', h, fun T'' i hle hi => ?_⟩
      have hi' : i = (Subalgebra.inclusion (Conv.halfRing_mono hle) :
          Conv.halfRing T' →+* Conv.halfRing T'').comp
          (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
        RingHom.ext fun r => Subtype.ext (hi r)
      rw [hi', spMap_comp, Category.assoc]
      exact fun p _ => hT' (x := spMap _ p) trivial
    · obtain ⟨T', h, h1, h2⟩ := Conv.exists_valAt'_halfCurve rfl hU'
      obtain ⟨hf, hv⟩ := h2 f
      have e : valR (spMap (Conv.halfRing T).val.toRingHom ≫ yT) U f =
          ((valR (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) U f :
            Conv.convLaurent) : ℂ⸨X⸩) := by
        rw [hfac, HolHom.valR_spMap _ _ U hU']
        rfl
      refine ⟨T', h, e ▸ hf, fun w hw => ?_⟩
      rw [hc w (h.trans_lt hw)]
      exact ⟨h1 w hw, (hv w hw).trans (Conv.ev_congr hw hw e.symm)⟩

end GlobalTheory.HalfPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnfStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_unifWitnessData_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → Nonempty (UnfWit U) := by
  first | exact @GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf | exact GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf | (intros; apply GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibreStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_section_generates_of_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  first | exact @GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | exact GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | (intros; apply GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorantStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_frame_periods_eq_majorant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), GoodEmb c σ → IsUnf U → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → (∀ v, (hermForm Hm (Uw.Pm k x v) (Uw.Pm k x v)).re = ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k v : Fin r → E))) ∧ (0 < r → (U.X k).κ0 = 2 * (U.X k).ξ0) ∧ ∀ (xi : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → (lieFac Dw xi a' * (U.X k).nfac (laU U a' 0 k) x.1)⁻¹ ≤ ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  first | exact @GlobalTheory.RiemMaj.riemann_eq_majorant | exact GlobalTheory.RiemMaj.riemann_eq_majorant | (intros; apply GlobalTheory.RiemMaj.riemann_eq_majorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorPowScaleInvEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters

theorem scale_tangent_pow (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ) (hn : 0 < n) (hv : IsTangent v) :
    spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  have h : GrpTangent.epsScale ((n : ℂ)⁻¹) ≫ (v ^ n) = v := by
    rw [GrpTangent.pow_eq_epsScale_comp hv, GrpTangent.epsScale_mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'),
      GrpTangent.epsScale_one, Category.id_comp]
  exact congrArg (fun φ => φ.left) h

end GlobalTheory.AbelianLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMulStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_generator_eq_rootOfUnity_mul_alt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra ℚ S] (t' : SAB H (Sp S)) (x : Sp S ⟶ Xo.X) (m m' : SABMap t' Xo.univ.t x) (w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ)) (w' : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m'.φ)) (σ σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m.φ)) (s1' : LB.Sec (Xo.univ.t.PP.L.pull m'.φ)) (s : LB.Sec (PPx x)), SecGen x s → RigIso m w → RigIso m' w' → IsoMaps w σ s1 → IsoMaps w' σ' s1' → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → (∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m'.φ → g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m'.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1'.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) → ∃ (ζ : S) (N : ℕ), 0 < N ∧ ζ ^ N = 1 ∧ ∀ i, σ'.f i = constFn t'.G.hom _ ζ * σ.f i := by
  first | exact @GlobalTheory.theta_generator_eq_rootOfUnity_mul | exact GlobalTheory.theta_generator_eq_rootOfUnity_mul | (intros; apply GlobalTheory.theta_generator_eq_rootOfUnity_mul <;> assumption)
end


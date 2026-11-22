import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3584
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem exists_model_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∃ (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S), Y.j ≫ ε.hom = j ∧ Y.s = ε.hom ≫ π ≫ zs ∧ ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hsi Z zs i OZ N d J S π j _ BD hU hSep hPre
  obtain ⟨oF, ⟨m0⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ
    (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  obtain ⟨G, _, _, e, hGs, hGp, hGab, hGc⟩ := GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap
  obtain ⟨t, htab, ⟨mt⟩, htc⟩ := GlobalTheory.T.exists_triple_on_descended_group Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap G e hGs hGp hGc
  obtain ⟨⟨-, -, -, -, hiz, -, -⟩, -, -, -, ⟨hNB, hproj, -, hjd, hji, -, -, -⟩, -⟩ := hU
  have eid : spMap (RingHom.id c.F) = 𝟙 _ := by simp [spMap]
  have hid : IsIso (spMap (RingHom.id c.F)) := by rw [eid]; infer_instance
  let g := pullback.fst (π ≫ zs) (spMap (RingHom.id c.F))
  have hg : IsIso g := inferInstance
  let jQ : Xo.XF c ⟶ pullback (π ≫ zs) (spMap (RingHom.id c.F)) := j ≫ inv g
  have hjQ : jQ ≫ g = j := by simp [jQ]
  have hab : abLocus t.G = Set.range j := htab.trans hGab
  let Y : Model Xo c (RingHom.id c.F) :=
    { X := S
      s := π ≫ zs
      normal := (GlobalTheory.isNormalScheme_iff S).1 hNB.1
      proj := hproj
      flat := inferInstance
      jQ := jQ
      jQ_over := by
        rw [← cancel_mono (spMap (RingHom.id c.F)), Category.assoc, ← pullback.condition, ← Category.assoc, hjQ,
          ← Category.assoc, hji, hiz, eid, Category.comp_id]
      jQ_open := inferInstance
      jQ_dense := by
        have hc : (⇑jQ) = (⇑(inv g)) ∘ ⇑j := by
          funext x
          simp [jQ]
        have h1 : DenseRange (⇑(inv g)) := (inv g).surjective.denseRange
        show DenseRange (⇑jQ)
        rw [hc]
        exact h1.comp hjd (inv g).continuous
      t := t
      oF := oF
      m0 := m0
      m := hjQ ▸ mt
      ab_gen := by
        show g ⁻¹' abLocus t.G = Set.range jQ
        rw [hab]
        ext x
        constructor
        · rintro ⟨y, hy⟩
          refine ⟨y, ?_⟩
          have h2 : (inv g) (g x) = x := by
            rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
          rw [← h2, ← hy]
          simp [jQ]
        · rintro ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          rw [← Scheme.Hom.comp_apply, hjQ] }
  refine ⟨Y, Iso.refl S, ?_, ?_, ?_⟩
  · show (jQ ≫ g) ≫ 𝟙 S = j
    rw [hjQ, Category.comp_id]
  · show π ≫ zs = 𝟙 S ≫ π ≫ zs
    rw [Category.id_comp]
  · intro k _ m n C hC ξ hξ
    have := htc C hC ξ hξ
    simpa using this

end GlobalTheory.UChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uMinSt_holds : UMinSt := GlobalTheory.T.unitary_integral_compactification_exists_via_theta

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingTransportGaloisConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_labelling_transport_galois_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.UPoinc.UGalTrans.isLab_conj | exact GlobalTheory.UPoinc.UGalTrans.isLab_conj | (intros; apply GlobalTheory.UPoinc.UGalTrans.isLab_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_thetaFourier_classSums_deeper_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') ∧ ∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → (∀ μ κ, ‖t ct yy₁ μ κ‖ ≤ Real.exp (-(ct.sc * (ct.T.be μ μ : ℝ) / 2))) ∧ (∀ μ, ∃ κ, ‖t ct yy₁ μ κ‖ = Real.exp (-(ct.sc * (ct.T.be μ μ : ℝ) / 2))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ := by
  first | exact @GlobalTheory.UPoinc.USum.main | exact GlobalTheory.UPoinc.USum.main | (intros; apply GlobalTheory.UPoinc.USum.main <;> assumption)
end


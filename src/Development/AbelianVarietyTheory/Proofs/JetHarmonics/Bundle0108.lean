import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0136
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrder
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0106

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowFrame
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.UnifJets

theorem exists_pow_frame {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {A B : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (ψ' : B →+* A) (hψ : ψ.comp ψ' = RingHom.id B) (hψ' : ψ'.comp ψ = RingHom.id A)
    (p : Sp A ⟶ X) (z : Sp B ⟶ X) (hz : z = spMap ψ ≫ p) (q : ℕ)
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => z) (fun _ => (1 : ℤ)))) (ht : t.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => (q : ℤ))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp B) (y : Z) (J), Good L y J → val τ (r ≫ spMap ψ) y J = val t r y J ^ q := by
  have e₁ : spMap ψ ≫ spMap ψ' = 𝟙 _ := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]; exact Spec.map_id _
  have e₂ : spMap ψ' ≫ spMap ψ = 𝟙 _ := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ']; exact Spec.map_id _
  obtain ⟨τ, hτ, hv⟩ := exists_gen hL (φ' := fun _ : Fin 1 => p ≫ 𝟙 X) (ε' := fun _ => (q : ℤ)) (fun U _ h => by
      simp only [hz, ← Category.assoc, e₂, Category.id_comp, Category.comp_id, _root_.mul_one])
    (LB.pullGen L _ _ (GeneratorPullback.powGen L _ _ t q) (spMap ψ'))
    (pullGen_isGen _ _ _ _ (SectionScalarValuation.powGen_isGen' L _ _ t ht q) _)
  refine ⟨τ, hτ, fun Z r y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_pull hJ, TWM.val_powGen, Category.assoc, e₁, Category.comp_id]

theorem sval_comp {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {q : ℕ} (σ : H0 L q) (p : Y ⟶ X)
    (τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => (q : ℤ)))) (a : Γ(Y, ⊤))
    (h : ∀ (y : Y) (J), Good L y J → sval σ p y J = gs (𝟙 _) y ⊤ a * (val τ (𝟙 _) y J).val)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval σ (r ≫ p) z J = gs r z ⊤ a * (val τ r z J).val := by
  have hj : p (r z) ∈ L.U (J (r ≫ p ≫ 𝟙 X)) := hJ (r ≫ p ≫ 𝟙 X)
  obtain ⟨J', hJ', e⟩ := exists_good L hL (r z) (K := Unit) (fun _ => p ≫ 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X))
    (fun _ _ _ => rfl) (fun _ => hj)
  have h₁ := h (r z) J' hJ'
  rw [sval_of σ p _ J' (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => e ()),
    val_of τ _ _ J' (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => by rw [Category.id_comp]; exact e ())] at h₁
  rw [sval_of σ _ _ J (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => by rw [Category.assoc]),
    val_of τ _ _ J (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => rfl)]
  have m₁ : p (r z) ∈ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X)) :=
    Set.mem_iInter.2 fun _ => hj
  have m₂ : r z ∈ LB.wchart L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X)) :=
    Set.mem_iInter.2 fun _ => hj
  have s₁ : ∀ f, gs (r ≫ p) z (LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X))) f =
      (r.stalkMap z).hom (gs p (r z) _ f) := fun f =>
    (gs_pull r p z _ m₁ f).symm.trans ((gs_stalkMap r z _ m₁ _).trans (congrArg (r.stalkMap z).hom
      ((gs_pull (𝟙 Y) p (r z) _ m₁ f).trans (congrArg (fun w => gs w (r z) _ f) (Category.id_comp p)))))
  have s₂ : ∀ u, (r.stalkMap z).hom (gm (𝟙 Y) (r z)
      (LB.wchart L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X))) u).val = (gm r z _ u).val := fun u =>
    (congrArg (r.stalkMap z).hom (gs_unit (𝟙 Y) (r z) _ m₂ u).symm).trans
      ((gs_stalkMap r z _ m₂ _).symm.trans (gs_unit r z _ m₂ u))
  exact (s₁ _).trans ((congrArg (r.stalkMap z).hom h₁).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gs_stalkMap r z ⊤ trivial a).symm (s₂ _))))

theorem cst_spMap {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  rw [← H1.cst_stalkMap, H1.gs_spec, H1.cst_stalkMap, Category.comp_id]

theorem cst_sum {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) {n : ℕ} (a : Fin n → A) :
    cst q z (∑ i, a i) = ∑ i, cst q z (a i) := by
  simp only [cst, gs_eq q z ⊤ trivial, map_sum]

theorem coeff_of_jet {V F κ : Type} [CommRing V] [CommRing F] [Fintype κ] [DecidableEq κ] (φ : V →+* F) (m : ℕ)
    (f : MvPowerSeries κ V) (g : MvPowerSeries κ F) (c : F)
    (h : psJet m g = algebraMap F _ c * jetCoef φ κ m (psJet m f)) (e : κ →₀ ℕ) (he : e.degree ≤ m) :
    MvPowerSeries.coeff e g = c * φ (MvPowerSeries.coeff e f) := by
  have h' : Ideal.Quotient.mk (orig F κ ^ (m + 1)) (psTrunc m g) =
      Ideal.Quotient.mk (orig F κ ^ (m + 1)) (MvPolynomial.C c * MvPolynomial.map φ (psTrunc m f)) := h
  have h2 := GermFun.coeff_eq_zero_of_mem (Ideal.Quotient.eq.1 h') (Nat.lt_succ_of_le he)
  rwa [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ he, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
    GermFun.coeff_psTrunc _ _ _ he, sub_eq_zero] at h2

theorem jetCoef_smul {V F κ : Type} [CommRing V] [CommRing F] (φ : V →+* F) (m : ℕ) (c : V) (a : Jet V κ m) :
    jetCoef φ κ m (c • a) = algebraMap F _ (φ c) * jetCoef φ κ m a := by
  rw [Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_C φ c))

theorem jets : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → AJetSt := by
  intro hL _ _ hT V _ _ _ _ ϖ hϖ D A G _ _ U κ _ _ z hz τ hτ hτT Q hQ Φ M0 r b hΦ0 hM0 hb hbw F _ _ _ _ _ v hv q n hq hn f
  have hLB := U.LG.isLB
  obtain ⟨x, hx, hM⟩ := GlobalTheory.T.universalJets_reindex_fin V G κ z hz _ (Fintype.equivFin κ).symm
  obtain ⟨ψ, -, hψ⟩ := hM n
  obtain ⟨τ', hτ', hvτ⟩ := exists_pow_frame hLB (ψ : Chart.JetR V (Fin (Fintype.card κ)) n →+* Jet V κ n)
    (ψ.symm : Jet V κ n →+* Chart.JetR V (Fin (Fintype.card κ)) n) (RingHom.ext fun a => ψ.apply_symm_apply a)
    (RingHom.ext fun a => ψ.symm_apply_apply a) (x n).left (z n).left hψ q (τ n) (hτ n)
  obtain ⟨l, σ, fa, χ, a, hexp, hΦ, hχ, hsupp, hval, hspan⟩ :=
    SmallJets.small_characters_span_jets hL (twistBCSpan_of hT) V ϖ hϖ D A G U Q hQ r b Φ M0 hΦ0 hM0 hb hbw
      q n hq hn _ x hx τ' hτ'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1
    (show ψ.symm (psJet n f) ∈ Submodule.span V (Set.range a) by rw [hspan]; trivial)
  have hθ := fun i => (hΦ i).elim fun Φ hΦ' =>
    FamBaseChange.main hL.globalFns V (maximalIdeal V) D q Φ (fa i) hΦ' F
  choose θ hθ using hθ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨gm, h0, hle, hge⟩ : ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Φ / q ∧
      ∀ i, (Q (χ i) : ℚ) / q ≤ gm := by
    refine ⟨(⌊(n : ℝ) ^ 2 * Φ⌋ : ℤ) / q, ?_, ?_, fun i => ?_⟩
    · have : 0 ≤ ⌊(n : ℝ) ^ 2 * Φ⌋ := Int.floor_nonneg.2 (mul_nonneg (sq_nonneg _) hΦ0)
      positivity
    · push_cast
      exact div_le_div_of_nonneg_right (Int.floor_le _) hq0.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast Int.le_floor.2 (hχ i)) (Nat.cast_nonneg q)
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : F, lam ≠ 0 ∧ v lam = (gm : WithTop ℚ) := by
    rcases h0.eq_or_lt with h | h
    · exact ⟨1, one_ne_zero, by rw [← h]; simp⟩
    · exact exists_val_eq hv h
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin (φ := fun _ : Fin 1 => 𝟙 G.left) (ε := fun _ => (q : ℤ)) hLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (UnifPre.gFK (R := V) (G := G) F)
    (fun _ => UnifPre.gFK (R := V) (G := G) F) (fun _ => (Category.comp_id _).symm) σ
    (fun i => lam * algebraMap V F (c i))
  obtain ⟨g, hg⟩ := (GlobalTheory.T.germ_existsUnique_linear V D A G U κ z hz τ hτ F q).2.2 hτT σ'
  refine ⟨∑ i, (lam * algebraMap V F (c i)) • θ i, σ', g, lam, GermJets.nuGe_sum _ _ _ fun i _ => ?_,
    ⟨l, _, σ, fa, hexp, hσ', GermJets.secLin_comb _ hθ⟩, hg, hlam0, ⟨gm, hlam, hle⟩, ?_⟩
  · have hci : (0 : WithTop ℚ) ≤ v (algebraMap V F (c i)) := by
      rw [IsScalarTower.algebraMap_apply V (FractionRing V) F]
      exact (TWO.v_of_V v hϖ hv (c i)).1
    have h2 := NuGe.smul Q (q := gm) (ζ := lam * algebraMap V F (c i))
      (by rw [AddValuation.map_mul, hlam]; exact le_add_of_nonneg_right hci) ((isSmul_iff _ _ _).2 rfl)
      (GermJets.nuGe_of_class hϖ hQ hv (by omega) (hθ i) (χ i) (hsupp i))
    exact NuGe.mono Q h2 (by have := hge i; linarith)
  · refine coeff_of_jet (algebraMap V F) n f g lam ?_
    obtain ⟨zF, e₁, e₂, hzF⟩ := hg n
    refine H1.cst_ext fun y => ?_
    obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hLB y (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
      (fun k => k.elim) (fun k => k.elim)
    have h₁ := (hzF y J hJ).symm.trans (BoxExpansion.secLin_val hσ' zF y hJ)
    have h₂ : ∀ i, gs zF y ⊤ (Out.scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left
          (lam * algebraMap V F (c i))) * sval (σ i) (zF ≫ UnifPre.gFK (R := V) (G := G) F) y J =
        cst (𝟙 _) y (algebraMap F (Jet F κ n) lam * jetCoef (algebraMap V F) κ n (ψ (c i • a i))) *
          (val (τ n) (spMap (jetCoef (algebraMap V F) κ n)) y J ^ q).val := fun i => by
      have k₁ : gs zF y ⊤ (Out.scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left
          (lam * algebraMap V F (c i))) = cst (𝟙 _) y (algebraMap F (Jet F κ n) (lam * algebraMap V F (c i))) :=
        (gs_pull zF _ y ⊤ trivial _).trans ((congrArg (fun w => cst w y (lam * algebraMap V F (c i))) e₁).trans
          (H1.gs_spec _ y _))
      have k₂ := sval_comp hLB (σ i) (x n).left τ' _ (hval i)
        (spMap (jetCoef (algebraMap V F) κ n) ≫ spMap (ψ : Chart.JetR V (Fin (Fintype.card κ)) n →+* Jet V κ n)) y J hJ
      rw [hvτ _ _ y J hJ] at k₂
      have k₃ : sval (σ i) (zF ≫ UnifPre.gFK (R := V) (G := G) F) y J =
          cst (𝟙 _) y (jetCoef (algebraMap V F) κ n (ψ (a i))) *
            (val (τ n) (spMap (jetCoef (algebraMap V F) κ n)) y J ^ q).val :=
        (congrArg (fun w => sval (σ i) w y J) (e₂.trans ((congrArg (_ ≫ ·) hψ).trans (Category.assoc _ _ _).symm))).trans
          (k₂.trans (congrArg (· * _) ((cst_spMap _ _ y _).trans (H1.gs_spec _ y _))))
      rw [k₁, k₃, map_smul, jetCoef_smul, ← _root_.mul_assoc, ← H1.cst_mul, map_mul, _root_.mul_assoc (algebraMap F (Jet F κ n) lam)]
    rw [Finset.sum_congr rfl fun i _ => h₂ i, ← Finset.sum_mul, ← cst_sum, ← Finset.mul_sum, ← map_sum, ← map_sum, hc,
      ψ.apply_symm_apply] at h₁
    exact (Units.mul_left_inj _).1 h₁

end GlobalTheory.UnifJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_regular_rep_vec_bigPt_eq_bessel :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  intro P Wp Wq _ _ _ _ _ _ p d hl0 hG
  have hd : ∀ a, d a ≠ 0 := fun a =>
    (hl0.1 (1, d a) (by unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨a, rfl⟩)).2
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := hl0
  have hG' : 0 < D.ptG (Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r
      (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
  have hpos : 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  refine ⟨h'.choose, ⟨hγ, fun l _ => ?_, hpos⟩, hZγ, fun F => ?_⟩
  · unfold Formalism.QuantumDeterminants.Dmin
    rw [hZγ, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hd _
  · show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dif_pos ⟨hl, hG'⟩, dif_pos h']
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZγ.trans hmono) F]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBoundStatement
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shifted_types_lower_bound_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  first | exact @GlobalTheory.WigSh.exists_shifted_types_lower_bound | exact GlobalTheory.WigSh.exists_shifted_types_lower_bound | (intros; apply GlobalTheory.WigSh.exists_shifted_types_lower_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.RatioMoment.ratio_moment | exact GlobalTheory.RatioMoment.ratio_moment | (intros; apply GlobalTheory.RatioMoment.ratio_moment <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyMomentStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.MomentStep.moment_step | exact GlobalTheory.MomentStep.moment_step | (intros; apply GlobalTheory.MomentStep.moment_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrderStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  first | exact @GlobalTheory.MomOne.FormalMul.padic_multiplications | exact GlobalTheory.MomOne.FormalMul.padic_multiplications | (intros; apply GlobalTheory.MomOne.FormalMul.padic_multiplications <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermOfFamHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem germOfFam_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → GermOfFamT := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c inst hstar
  obtain rfl := starSt E H inst hstar
  let := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ v hv q hq
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨τ, hτ, ht, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
    C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  refine ⟨fun σ' => ?_, fun s σ' hE hs g hg => ?_⟩
  · obtain ⟨f, hf⟩ := (GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hu τ hτ F q).2.2 (ht htr) σ'
    exact ⟨f, (hiff F q σ' f).2 hf⟩
  · exact GlobalTheory.IntegralGerm.main hL hL2 hL4 hT T.V ϖ hϖ D' A' G' U' _ _ hu τ hτ F v hv q hq σ' s g hE
      ((hiff F q σ' g).1 hg)
      (n1e T.V ϖ hϖ D' _ (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v q s hs)

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chart_directions_are_eigenvectors : EigDirSt := by
  first | exact @GlobalTheory.PowGerm.eigDirSt | exact GlobalTheory.PowGerm.eigDirSt | (intros; apply GlobalTheory.PowGerm.eigDirSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeriesStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_weierstrass_chart_xy_unit_series : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ → coeff 1 ℓ ≠ 0 ∧ ∃ v xs ys : ℂ_[q]⟦X⟧, Bd 1 v ∧ Bd 1 xs ∧ Bd 1 ys ∧ ‖constantCoeff v‖ = 1 ∧ ‖constantCoeff xs‖ = 1 ∧ ‖constantCoeff ys‖ = 1 ∧ hat M.ι ℓ M.u = X * v ∧ hat M.ι ℓ M.w * ys = -X ^ 3 ∧ xs = -v * ys ∧ ∀ (F : ℂ → ℂ) (A B : Polynomial ℂ) (k : ℕ), AnalyticAt ℂ F 0 → A.natDegree ≤ k → B.natDegree ≤ k → ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → ∀ (D : Polynomial ℂ) (j : ℕ), D.natDegree ≤ j → (∀ᶠ z in 𝓝[≠] (0 : ℂ), F z * D.eval (M.x z) = G z * (A.eval (M.x z) + B.eval (M.x z) * M.y z)) → hat M.ι ℓ F * X ^ (2 * k + 3) * (∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * xs ^ i) = hat M.ι ℓ G * X ^ (2 * j) * ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
  first | exact @GlobalTheory.MomOne.ChartXY.chart_xy | exact GlobalTheory.MomOne.ChartXY.chart_xy | (intros; apply GlobalTheory.MomOne.ChartXY.chart_xy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasureOfProducts
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ProdMeasure
variable {q : ℕ} [Fact q.Prime]

theorem hasSum_pi_prod : ∀ (g : ℕ) (u : Fin g → ℕ → ℂ_[q]) (s : Fin g → ℂ_[q]),
    (∀ i, HasSum (u i) (s i)) → HasSum (fun ν : Fin g → ℕ => ∏ i, u i (ν i)) (∏ i, s i) := by
  haveI : NonarchimedeanRing ℂ_[q] := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  intro g
  induction g with
  | zero =>
    intro u s _
    simpa using hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, u i (ν i))
  | succ g ih =>
    intro u s h
    have h1 := (h 0).mul_of_nonarchimedean (ih (fun i => u i.succ) (fun i => s i.succ) fun i => h _)
    rw [← (Fin.consEquiv (fun _ : Fin (g + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]
    convert h1 using 1
    funext p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih h).2
    rwa [mul_one, ← pow_succ] at this

theorem shiftS_pow {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) :
    shiftS ζ (f ^ a) = shiftS ζ f ^ a := by
  have H := Shift.shift_laws q ζ hζ
  induction a with
  | zero => simpa using H.2.2.1 1
  | succ a ih => rw [pow_succ, (H.2.1 _ _ ⟨1, bd_one_pow h a⟩ ⟨1, h⟩).2, ih, pow_succ]

theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hl : constantCoeff ℓ = 0) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) (a : ℕ) : hat ι ℓ (fun z => G z ^ a) = hat ι ℓ G ^ a := by
  have H := TaylorRead.hat_laws q ι ℓ hl
  induction a with
  | zero => simpa using H.2.1 1
  | succ a ih =>
    simp only [pow_succ]
    rw [(H.1 (fun z => G z ^ a) G (hG.pow a) hG).2.1, ih]

theorem prod_fiber_pow {g k : ℕ} (σ : Fin k → Fin g) (x : Fin g → ℂ_[q]) :
    ∏ l, x (σ l) = ∏ i, x i ^ (Finset.univ.filter (fun l => σ l = i)).card := by
  rw [← Finset.prod_fiberwise Finset.univ σ (fun l => x (σ l))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]

theorem measure_of_products : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ), 0 < d → δ ≠ 0 → Ω ≠ 0 → Differentiable ℂ θ → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j i, PrimeTo d q (t j i)) → ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ ν : Fin g → ℕ, ‖∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C (Ω / ι δ) * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B)) ∧ ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * t j i)) → (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])), (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) * ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * zc (A i))) → ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  intro d q _ ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  set ω : ℂ_[q] := Ω / ι δ with hω
  have hS : ∀ j i, Bd 1 (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) :=
    fun j i => bd_one_pow (hL.1 _ (ht j i)) _
  obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q g
    (fun ν => ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    ⟨∑ j, ‖ι (c j)‖, fun ν => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul, norm_prod]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hS j i _))⟩
  refine ⟨μ, hμ1, ?_⟩
  intro n s y hs hst hy k ys F hF
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    simp [logS, ← coeff_zero_eq_constantCoeff_apply]
  have hdiff : ∀ j i, Differentiable ℂ (W1 d (y i) (U1 d (t j i) θ)) := fun j i =>
    ((heisenbergOne d hd).2.2.1 _ _ ((heisenbergOne d hd).2.2.1 _ _ hθ).1).2
  have hroot : ∀ i, ι (kap1 d 1 (y i)) ^ (q ^ n) = 1 := fun i =>
    (hL.2.1 0 (y i) n s hs ⟨0, 0, by simp⟩ (hy i)).1
  have hf : ∀ (i : Fin g) (e : ℕ), ∃ f : C(ℤ_[q], ℂ_[q]),
      (∀ A, f A = ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n A).val * zc A ^ e) ∧
      ∀ j, HasSum (fun r : ℕ => coeff r (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) *
        (fwdDiff (1 : ℤ_[q]))^[r] f 0)
        (ω ^ e * ι (iteratedDeriv e (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro i e
    obtain ⟨f, hf, -⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q 0 _ n e ⟨0, fun r => by simp⟩ (hroot i)
    refine ⟨f, hf, fun j => ?_⟩
    obtain ⟨f', hf', h⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q _ _ n e ⟨1, hS j i⟩ (hroot i)
    obtain rfl : f' = f := by ext A; rw [hf, hf']
    have han := (hdiff j i).analyticAt 0
    rw [shiftS_pow (ShiftComp.norm_sub_one_lt_of_root (hroot i)) (hL.1 _ (ht j i)),
      ← (hL.2.1 _ _ n s hs (hst j i) (hy i)).2, ← hat_pow ι _ hl _ han,
      (hat_multiplicative_chart q ι ω (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i)
        (han.pow (a i))).2.1 e] at h
    exact h
  choose f hf1 hf2 using hf
  let P : (Fin k → Fin g) → C(Fin g → ℤ_[q], ℂ_[q]) := fun σ =>
    ⟨fun A => ∏ i, f i (Finset.univ.filter (fun l => σ l = i)).card (A i), by fun_prop⟩
  have hP : ∀ σ, μ (P σ) = ∑ j, ι (c j) * ∏ i, (ω ^ (Finset.univ.filter (fun l => σ l = i)).card *
      ι (iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro σ
    refine (hμ2 (fun i => f i (Finset.univ.filter (fun l => σ l = i)).card) (P σ) fun _ => rfl).unique ?_
    have := hasSum_sum (s := Finset.univ) fun j _ =>
      (hasSum_pi_prod g _ _ fun i => hf2 i (Finset.univ.filter (fun l => σ l = i)).card j).mul_left (ι (c j))
    simp only [Finset.sum_mul, mul_assoc]
    simp only [Finset.prod_mul_distrib] at this ⊢
    exact this
  have hFP : F = ∑ σ : Fin k → Fin g, (∏ l, Ω⁻¹ * ι (ys l (σ l))) • P σ := by
    ext A
    rw [hF]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, P, ContinuousMap.coe_mk, hf1, Finset.mul_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib (f := fun i => ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val),
      ← prod_fiber_pow σ (fun i => zc (A i))]
    simp only [← mul_assoc]
    rw [Finset.prod_mul_distrib (g := fun l => zc (A (σ l)))]
    ring
  have hcd : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) :=
    fun j => contDiff_prod fun i _ => (((hdiff j i).contDiff).comp (contDiff_apply ℂ ℂ i)).pow _
  have hit : iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0
      = ∑ j, c j • iteratedFDeriv ℂ k
        (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 := by
    rw [iteratedFDeriv_sum (fun j _ => contDiff_const.mul (hcd j)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hcd j).contDiffAt
  rw [hit, hFP, map_sum μ]
  simp only [map_smul, hP, smul_eq_mul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k
    (fun i z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) _ (fun i => (hdiff j i).pow _)]
  simp only [Finset.mul_sum, map_sum, map_mul, map_prod, Pi.smul_apply, smul_eq_mul, map_inv₀]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib (f := fun i => ω ^ (Finset.univ.filter (fun l => σ l = i)).card),
    ← prod_fiber_pow σ (fun _ => ω)]
  have e : ∏ l, (ι δ)⁻¹ * ι (ys l (σ l)) = (∏ l, Ω⁻¹ * ι (ys l (σ l))) * ∏ _l : Fin k, ω := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hω]; field_simp
  rw [e]
  ring

end GlobalTheory.MomOne.ProdMeasure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentWeightedStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_moment_weighted : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal ((∑ i, ‖(ρ (Matrix.of x)⁻¹ *ᵥ om) i‖ ^ 2) * ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
  first | exact @GlobalTheory.MomLem8.moment_lemma_pieri | exact GlobalTheory.MomLem8.moment_lemma_pieri | (intros; apply GlobalTheory.MomLem8.moment_lemma_pieri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGapStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weighted_bessel_gap : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDS ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  first | exact @GlobalTheory.BesselPieri.pieri_bessel | exact GlobalTheory.BesselPieri.pieri_bessel | (intros; apply GlobalTheory.BesselPieri.pieri_bessel <;> assumption)
end


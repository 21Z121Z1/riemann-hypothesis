import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0103
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0693
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0697

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUnifor
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh

theorem exists_comb_of_exp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} (hxx : x' = x) {g : ℕ} (ex : (Fin g → ℂ) → (Over.mk x' ⟶ Z.t.G))
    (hex : IsExpAt Z.t x' ex) (f : EigFrame Z σ x) (τ : E →+* ℂ) (δ : Fin (Dw.mult τ) → Fin g → ℂ)
    (hδ : ∀ b, IsDerivAt0 (fun z => (ex z).left) (δ b) (f.v τ b)) (v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left)
    (hv' : IsTanAtG Z.t x v') (heig : ∀ a, v' ≫ (Z.t.act.act a).left = spMap (epsMul (σ (embK c τ a))) ≫ v')
    (w : Fin g → ℂ) (hw : IsDerivAt0 (fun z => (ex z).left) w v') :
    ∃ a : Fin (Dw.mult τ) → ℂ, IsCombAtG Z.t x (f.v τ) a v' ∧ w = ∑ b, a b • δ b := by
  subst hxx
  obtain ⟨a, ha, -⟩ := f.basis τ v' hv' heig
  have e1 : ex 0 = 1 := by
    have h := hex.1 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hd := GlobalTheory.ShFam.Hor.ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e1) (f.tan τ) hδ hv' ha
  obtain ⟨w', -, hu⟩ := hex.2.2 v' hv'
  exact ⟨a, ha, (hu w hw).trans (hu _ hd).symm⟩

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom)

theorem coords_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hg hU d u₀ R _ φR xR fR ev k G τ hev hG hφ hpt
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  choose Pm h1 h2 h3 h4 _ using hP
  obtain ⟨h₀, -⟩ := hpt.self_of_nhds
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let x : (Fin d → ℂ) → (U.X k).dom := fun b =>
    if h : G (L.symm b) ∈ (U.X k).dom then ⟨G (L.symm b), h⟩ else ⟨G u₀, h₀⟩
  have hxb : ∀ b (h : G (L.symm b) ∈ (U.X k).dom), x b = ⟨G (L.symm b), h⟩ := fun b h => dif_pos h
  let P : (Fin d → ℂ) → ((F.Di (ik k)).La →+ (Fin g → ℂ)) := fun b => Pm k (x b)
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x b))
  have hu : ∀ b, F.u (ik k) (P b) =
      p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun b => (h3 k (x b)).symm.trans (ptF_fst (U.un k (x b))).symm
  have hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ := fun b => ptF_snd (U.un k (x b))
  have hgood : ∀ᶠ u in 𝓝 u₀, G u ∈ (U.X k).dom ∧
      ∀ τ' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    (hpt.mono fun u hu => hu.1).and
      (eventually_all.2 fun τ' => eventually_all.2 fun a => eventually_all.2 fun b => hG τ' a b)
  obtain ⟨B₀, hB₀, hB₀o, hu₀⟩ := eventually_nhds_iff.1 hgood
  let B : Set (Fin d → ℂ) := L.symm ⁻¹' B₀
  have hBo : IsOpen B := hB₀o.preimage L.symm.continuous
  have hb₀ : L u₀ ∈ B := by
    show L.symm (L u₀) ∈ B₀
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hu₀
  have hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B := fun a => differentiableOn_pi.2 fun j =>
    (TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun b => G (L.symm b)) (fun b hb => (hB₀ _ hb).1)
      (fun τ' a' c' b hb => (((hB₀ _ hb).2 τ' a' c').comp b L.symm.differentiableAt).differentiableWithinAt)
      _ _ _).congr fun b hb => by
        show Pm k (x b) a j = _
        rw [h1, hxb b (hB₀ _ hb).1]
  let ev' : (Fin d → ℂ) → (R →+* ℂ) := fun b => ev (L.symm b)
  let Ex : (Fin d → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun b z =>
    liftEx Z F (p b) (ik k) (P b) (hu b) z ≫ Z.m.φ
  let Wd : Fin (Dw.mult τ) → (Fin d → ℂ) → Fin g → ℂ := fun i b =>
    if h : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) then h.choose else 0
  have core : ∀ b (h : G (L.symm b) ∈ (U.X k).dom),
      (cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z = spMap (ev (L.symm b)) ≫ xR →
      (ev (L.symm b)).comp φR = σ → ∀ i,
      IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) ∧
      IsCombAtG Z.t ((cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z)
        ((cxFrame Z (U.un k ⟨G (L.symm b), h⟩)).v τ) (fun a => Wd i b (e.symm ⟨τ, a⟩))
        (spMap (dualMap (ev (L.symm b))) ≫ fR.v τ i) := by
    intro b h hx hφb i
    rw [← hxb b h] at hx ⊢
    obtain ⟨gF, hgF⟩ := HolFrames.exists_bc fR (ev (L.symm b)) (φ' := σ) hφb.symm hx
    have hxp : p b ≫ Z.jQ ≫ genι Z = (cxPt Z (U.un k (x b))).1 ≫ genι Z := (Category.assoc _ _ _).symm
    have hExp := isExpAt_pushEx E H Dw l Xo c O β Z g _ _ F (p b) (ik k) (P b) _ (hu b) rfl (h2 k (x b))
    have hδ : ∀ a, IsDerivAt0 (fun z => (pushEx Z F (p b) (ik k) (P b) _ (hu b) rfl z).left)
        (Pi.single (e.symm ⟨τ, a⟩) 1) ((cxFrame Z (U.un k (x b))).v τ a) := by
      intro a
      obtain ⟨w, hwt, hw0, hwm⟩ := EigFrame.ofFrPt_v Z (U.un k (x b))
        (x := (cxPt Z (U.un k (x b))).1 ≫ genι Z) (Category.assoc _ _ _).symm τ a
      have hw0' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m0.toSABMap.φ = (U.un k (x b)).u τ a := hw0
      have hwm' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m.φ = (cxFrame Z (U.un k (x b))).v τ a := hwm
      have hd : IsDerivAt0 (fun z => (F.ex (ik k) (P b) z).left) (Pi.single (e.symm ⟨τ, a⟩) 1)
          (w ≫ Z.m0.toSABMap.φ) := by
        exact (congrArg (IsDerivAt0 _ _) hw0').mpr (h4 k (x b) τ a)
      have := isDerivAt0_comp_hom (isDerivAt0_liftEx Z F (p b) (ik k) (P b) (h2 k (x b)) (hu b) hwt.1 hd) Z.m.φ
      exact (congrArg (IsDerivAt0 _ _) hwm').mp this
    have ht : IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (gF.v τ i) := by
      rw [hxp]; exact gF.tan τ i
    have hex : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      obtain ⟨w, hw, -⟩ := hExp.2.2 _ ht
      exact ⟨w, (hgF τ i) ▸ hw⟩
    have hW : IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      have e0 : Wd i b = hex.choose := dif_pos hex
      rw [e0]
      exact hex.choose_spec
    refine ⟨hW, ?_⟩
    obtain ⟨a, ha, hwa⟩ := exists_comb_of_exp hxp _ hExp (cxFrame Z (U.un k (x b))) τ _ hδ (gF.v τ i)
      (gF.tan τ i) (gF.eig τ i) (Wd i b) ((hgF τ i).symm ▸ hW)
    have hfa : (fun a' => Wd i b (e.symm ⟨τ, a'⟩)) = a := by
      funext a'
      rw [hwa]
      have hi : ∀ j j' : Fin (Dw.mult τ), e.symm ⟨τ, j⟩ = e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
      simp [Finset.sum_apply, Pi.single_apply, hi]
    rw [hfa, ← hgF τ i]
    exact ha
  have ht : Tendsto L.symm (𝓝 (L u₀)) (𝓝 u₀) := by
    simpa using L.symm.continuous.tendsto (L u₀)
  refine ⟨fun u a i => Wd i (L u) (e.symm ⟨τ, a⟩), fun a i => ?_, ?_⟩
  · have hev'' : ∀ t, ∀ᶠ b in 𝓝 (L u₀), DifferentiableAt ℂ (fun b => ev' b t) b := fun t => by
      filter_upwards [ht.eventually (hev t)] with b hb
      exact hb.comp b L.symm.differentiableAt
    have hW : ∀ᶠ b in 𝓝 (L u₀), IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      filter_upwards [ht.eventually hpt, ht.eventually hφ] with b ⟨h, hx⟩ hφb
      exact (core b h hx hφb i).1
    have hd := eventually_differentiableAt_dir Z σ F (ik k) hBo hu (fun b => h2 k (x b)) hPd hs (fR.v τ i) ev' hb₀
      hev'' (Wd i) hW
    filter_upwards [(L.continuous.tendsto u₀).eventually hd] with u hu
    exact (differentiableAt_pi.1 hu (e.symm ⟨τ, a⟩)).comp u L.differentiableAt
  · filter_upwards [hpt, hφ] with u ⟨h, hx⟩ hφu
    refine ⟨h, fun i => ?_⟩
    have c := core (L u)
    rw [ContinuousLinearEquiv.symm_apply_apply] at c
    exact (c h hx hφu i).2

end GlobalTheory.HolCoordEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFromTau

theorem exists_isTauCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X),
    ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x := by
  intro R _ _ _ D a b
  have pick : ∀ (z : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A), ∃ i, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsIntChart D z i := by
    intro z
    have hc : z.left (closedPoint R) ∈ ⨆ i, D.P.L.U i := by
      rw [D.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, ((closedPoint_mem_iff (R := R) (z.left ⁻¹ᵁ D.P.L.U i)).1 hi).ge⟩
  obtain ⟨i1, h1⟩ := pick (D.c (a + b))
  obtain ⟨i2, h2⟩ := pick (D.c a)
  obtain ⟨i3, h3⟩ := pick (D.c b)
  obtain ⟨i4, h4⟩ := pick η[D.P.A]
  let j : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → D.P.L.ι := Sum.elim (Sum.elim (Sum.elim (fun _ => i1) (fun _ => i2)) (fun _ => i3)) (fun _ => i4)
  refine ⟨_, j, ?_, h1, h2, h3, h4, rfl⟩
  intro y _
  refine Set.mem_iInter.2 ?_
  rintro (((⟨⟩ | ⟨⟩) | ⟨⟩) | ⟨⟩)
  · exact h1 (Set.mem_univ (jK R y))
  · exact h2 (Set.mem_univ (jK R y))
  · exact h3 (Set.mem_univ (jK R y))
  · exact h4 (Set.mem_univ ((toUnit (TK R)).left y))

theorem associated_of_tau : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W) (hg : Function.Injective g)
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
    (∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W)) →
    ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ g hg t' P' ρ hρ y r r' hr hr'
  letI := H.starRing
  obtain ⟨x, hx⟩ := exists_isTauCoord R P.D.toPre y (H.w0 • y)
  obtain ⟨x', hx'⟩ := exists_isTauCoord W P'.D.toPre (ρ y) (H.w0 • ρ y)
  have hx'' : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ y) (ρ (H.w0 • y)) x' := by rwa [ρ.map_smul]
  obtain ⟨u, hu⟩ := hρ y (H.w0 • y) x x' hx hx''
  obtain ⟨u1, hu1⟩ := GlobalTheory.T.psiCoordinate_eq_unit_mul_tauCoordinate R P.D.toPre (𝓞 E) P.oD H.w0 P.w0 y r x hr hx
  obtain ⟨u2, hu2⟩ := GlobalTheory.T.psiCoordinate_eq_unit_mul_tauCoordinate W P'.D.toPre (𝓞 E) P'.oD H.w0 P'.w0 (ρ y) r' x' hr' hx'
  set φ := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) with hφ
  have hφa : ∀ s : R, φ (algebraMap R (FractionRing R) s) = algebraMap W (FractionRing W) (g s) := fun s =>
    IsFractionRing.lift_algebraMap _ s
  have e1 := congrArg φ hu1
  rw [map_mul, hφa, hφa, hu] at e1
  let v : Wˣ := Units.map g.toMonoidHom u1 * u * u2⁻¹
  have key : g r = r' * (v : W) := by
    apply IsFractionRing.injective W (FractionRing W)
    have h2 : (x' : FractionRing W) = algebraMap W (FractionRing W) ((u2⁻¹ : Wˣ) : W) * algebraMap W (FractionRing W) r' := by
      rw [hu2, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e1, h2]
    simp only [v, Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  exact Associated.symm ⟨v, key.symm⟩

end GlobalTheory.PsiFromTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem isSplitPl_of_mem_levelPrimes {R : Ranks} (H : Host R)
    (hc : ∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) {p : ℕ} (hp : p ∈ H.levelPrimes)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  obtain ⟨hpr, hm⟩ := hc p hp
  have h := (GlobalTheory.HostSplit.split_of_one_mod R H p hpr hm).1
  obtain ⟨-, he, hf⟩ := GlobalTheory.unramified_degree_one_of_ncard_placesOver H.E p hpr h v hv
  exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSplitPl_of_degree_one H v hf he

theorem split_allSt : PrN → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x v hv => ?_
  have hc : ∀ p ∈ (Dof x).host.levelPrimes, p.Prime ∧ p % ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) = 1 :=
    (w.st x.o.Z).B.level_cond
  rcases hv with hv | hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.1 v hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.2 v hv

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.SplitPrimeAuxiliary

open scoped Pointwise

theorem eq_one_of_smul_eq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [P.IsPrime] (hP : (p : 𝓞 E) ∈ P) (σ : Gal(E/ℚ)) (hσ : σ • P = P) : σ = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpz.ne_zero).2 hpz).isMaximal (by simpa using hp.ne_zero)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hP
  have horb := Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 E) Gal(E/ℚ) (Ideal.span {(p : ℤ)}) P
  have hidx := MulAction.index_stabilizer Gal(E/ℚ) P
  rw [horb, h, ← IsGalois.card_aut_eq_finrank] at hidx
  have hmul := (MulAction.stabilizer Gal(E/ℚ) P).card_mul_index
  rw [hidx] at hmul
  have h1 : Nat.card (MulAction.stabilizer Gal(E/ℚ) P) = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hmul, one_mul])
  have hb := Subgroup.card_eq_one.1 h1
  have hm : σ ∈ MulAction.stabilizer Gal(E/ℚ) P := hσ
  rwa [hb, Subgroup.mem_bot] at hm

theorem conj_ne_one {R : Ranks} (H : Host R) : H.conj ≠ 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  intro h
  apply IsCMField.complexConj_ne_one H.E
  ext z
  have : IsCMField.complexConj H.E z = H.conj z := by
    apply H.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  rw [this, h]
  rfl

theorem isSplitPl_of_split {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime)
    (h : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E)
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ placesOver H.E p) : IsSplitPl H v := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  have := v.isPrime
  by_contra hs
  apply conj_ne_one H
  rw [← inv_eq_one]
  refine eq_one_of_smul_eq H.E hp h v.asIdeal hv _ (Eq.symm ?_)
  refine v.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  intro x hx
  rw [Ideal.mem_inv_pointwise_smul_iff]
  by_contra hx'
  refine hs ⟨x, hx, fun y hy => ?_⟩
  have : y = H.conj • x := RingOfIntegers.ext hy
  rwa [this]

theorem auxiliary_primes_split : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ _ : LC hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ v hv => ?_
  rcases hv with hv | hv
  · exact isSplitPl_of_split B.host B.host.pde_prime B.toPre.pde_split.1 v hv
  · exact isSplitPl_of_split B.host B.host.pde'_prime B.toPre.pde_split.2 v hv

end GlobalTheory.SplitPrimeAuxiliary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedEntriesBoundedSiegelReduced
section
noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem term_le_double_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ p q, 0 ≤ f p q) (p q : Fin n) :
    f p q ≤ ∑ p, ∑ q, f p q := by
  calc f p q ≤ ∑ q, f p q := Finset.single_le_sum (fun q _ => hf p q) (Finset.mem_univ q)
    _ ≤ ∑ p, ∑ q, f p q := Finset.single_le_sum (f := fun p => ∑ q, f p q)
        (fun p _ => Finset.sum_nonneg fun q _ => hf p q) (Finset.mem_univ p)

theorem step_chain {n : ℕ} {d : Fin n → ℝ} (hs : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q)
    (q : Fin n) : ∀ m (hm : (q : ℕ) + m < n), d q ≤ 4 ^ m * d ⟨q + m, hm⟩ := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hs ⟨q + m, by omega⟩ ⟨q + (m + 1), hm⟩ (by simp; omega)
    calc d q ≤ 4 ^ m * d ⟨q + m, by omega⟩ := h1
      _ ≤ 4 ^ m * (4 * d ⟨q + (m + 1), hm⟩) := by gcongr
      _ = 4 ^ (m + 1) * d ⟨q + (m + 1), hm⟩ := by ring

theorem gap_chain {n : ℕ} {d : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R) (p : Fin n) :
    ∀ m (hm : (p : ℕ) + m < n),
      (∀ k k' : Fin n, (k' : ℕ) = k + 1 → p ≤ k → (k' : ℕ) ≤ p + m → d k' ≤ R * d k) →
      d ⟨p + m, hm⟩ ≤ R ^ m * d p := by
  intro m
  induction m with
  | zero => intro hm _; simp
  | succ m ih =>
    intro hm h
    have h1 := ih (by omega) (fun k k' hk hpk hk' => h k k' hk hpk (by omega))
    have h2 := h ⟨p + m, by omega⟩ ⟨p + (m + 1), hm⟩ (by simp; omega)
      (by simp [Fin.le_def]) (by simp)
    calc d ⟨p + (m + 1), hm⟩ ≤ R * d ⟨p + m, by omega⟩ := h2
      _ ≤ R * (R ^ m * d p) := by gcongr
      _ = R ^ (m + 1) * d p := by ring

theorem balanced_entries_bounded : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) →
    (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) →
    (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  intro n K
  obtain ⟨c, hc⟩ := GlobalTheory.T.siegelUnipotent_inverse_entries_bounded n
  obtain ⟨R, hR1, hR⟩ := GlobalTheory.T.siegelDomain_lowerBlock_eq_zero_of_large_gap n K c
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hRn : (1 : ℝ) ≤ R ^ n := one_le_pow₀ hR1
  have hB : 0 ≤ 4 ^ n * R ^ n * max K 0 := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0
  refine ⟨(n : ℝ) ^ 2 * |c| * (1 + 4 ^ n * R ^ n * max K 0), ?_⟩
  intro A A' d u hS hd hbal htr i j
  obtain ⟨v, hvu, huv, hvl, hvc⟩ := hc u hS.diag hS.lower hS.upper
  obtain ⟨hsym, hsum, hsum'⟩ := GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace n A A' d u v hd hvu huv hbal
  have hK' : ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum']; exact htr
  have hK : ∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum]; exact htr
  set Ar := A.map (Int.cast : ℤ → ℝ) with hAr
  set W := u * Ar * v with hWdef
  set B := 4 ^ n * R ^ n * max K 0 with hBdef
  have hterm : ∀ p q, d p / d q * W p q ^ 2 ≤ max K 0 := fun p q =>
    (term_le_double_sum (fun p q => d p / d q * W p q ^ 2)
      (fun p q => mul_nonneg (div_nonneg (hd p).le (hd q).le) (sq_nonneg _)) p q).trans
      (hK.trans (le_max_left _ _))
  have hsq : ∀ p q, W p q ^ 2 ≤ d q / d p * max K 0 := by
    intro p q
    have hp := (hd p).ne'
    have hq := (hd q).ne'
    have e : W p q ^ 2 = d q / d p * (d p / d q * W p q ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hterm p q) (div_nonneg (hd q).le (hd p).le)
  have hW : ∀ p q, W p q ^ 2 ≤ B := by
    intro p q
    rcases le_or_gt q p with hqp | hpq
    · have hqp' : (q : ℕ) ≤ p := hqp
      have hm : (q : ℕ) + ((p : ℕ) - q) < n := by omega
      have h1 := step_chain hS.step q ((p : ℕ) - q) hm
      have hpe : (⟨(q : ℕ) + ((p : ℕ) - q), hm⟩ : Fin n) = p := by ext; simp; omega
      rw [hpe] at h1
      have h2 : (4 : ℝ) ^ ((p : ℕ) - q) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : d q ≤ 4 ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
      have h5 : d q / d p ≤ 4 ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
      calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
        _ ≤ 4 ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
        _ ≤ 4 ^ n * max K 0 * R ^ n := le_mul_of_one_le_right (by positivity) hRn
        _ = B := by rw [hBdef]; ring
    · have hpq' : (p : ℕ) < q := hpq
      by_cases hgap : ∃ k k' : Fin n, (k' : ℕ) = k + 1 ∧ p ≤ k ∧ k' ≤ q ∧ R * d k < d k'
      · obtain ⟨k, k', hk, hpk, hkq, hlt⟩ := hgap
        have h0 : (u * A'.map (Int.cast : ℤ → ℝ) * v) q p = 0 :=
          hR A' d u v hS hd hvu huv hvl hvc hK' k k' hk hlt q p hpk hkq
        have h1 := hsym p q
        rw [h0, mul_zero] at h1
        have hz : W p q = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (hd p).ne'
          · exact h
        rw [hz]
        simpa using hB
      · push_neg at hgap
        have hm : (p : ℕ) + ((q : ℕ) - p) < n := by omega
        have h1 := gap_chain (d := d) (by linarith) p ((q : ℕ) - p) hm
          (fun k k' hk hpk hk' => hgap k k' hk hpk (by rw [Fin.le_def]; omega))
        have hqe : (⟨(p : ℕ) + ((q : ℕ) - p), hm⟩ : Fin n) = q := by ext; simp; omega
        rw [hqe] at h1
        have h2 : R ^ ((q : ℕ) - p) ≤ R ^ n := pow_le_pow_right₀ hR1 (by omega)
        have h3 : d q ≤ R ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
        have h5 : d q / d p ≤ R ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
        calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
          _ ≤ R ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
          _ ≤ 4 ^ n * (R ^ n * max K 0) := le_mul_of_one_le_left (by positivity) h4
          _ = B := by rw [hBdef]; ring
  have hA : Ar = v * W * u := by
    calc Ar = (v * u) * Ar * (v * u) := by rw [hvu, Matrix.one_mul, Matrix.mul_one]
      _ = v * W * u := by rw [hWdef]; simp only [Matrix.mul_assoc]
  have hu1 : ∀ l j, |u l j| ≤ 1 := by
    intro l j
    rcases lt_trichotomy l j with h | h | h
    · exact (hS.upper l j h).trans (by norm_num)
    · subst h; rw [hS.diag]; simp
    · rw [hS.lower l j h]; simp
  have hWb : ∀ k l, |W k l| ≤ 1 + B := fun k l => by
    nlinarith [hW k l, abs_nonneg (W k l), sq_abs (W k l)]
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hentry : |Ar i j| ≤ (n : ℝ) ^ 2 * |c| * (1 + B) := by
    rw [hA, Matrix.mul_apply]
    calc |∑ l, (v * W) i l * u l j| ≤ ∑ l, |(v * W) i l * u l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, (n : ℝ) * (|c| * (1 + B)) := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, Matrix.mul_apply]
        have hin : |∑ k, v i k * W k l| ≤ (n : ℝ) * (|c| * (1 + B)) := by
          calc |∑ k, v i k * W k l| ≤ ∑ k, |v i k * W k l| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k : Fin n, |c| * (1 + B) := by
              apply Finset.sum_le_sum; intro k _
              rw [abs_mul]
              exact mul_le_mul ((hvc i k).trans (le_abs_self c)) (hWb k l) (abs_nonneg _) hc0
            _ = (n : ℝ) * (|c| * (1 + B)) := by simp
        calc |∑ k, v i k * W k l| * |u l j| ≤ (n : ℝ) * (|c| * (1 + B)) * 1 :=
              mul_le_mul hin (hu1 l j) (abs_nonneg _) (by positivity)
          _ = (n : ℝ) * (|c| * (1 + B)) := by ring
      _ = (n : ℝ) ^ 2 * |c| * (1 + B) := by simp; ring
  have hcast : ((|A i j| : ℤ) : ℝ) = |Ar i j| := by simp [hAr, Int.cast_abs]
  rw [hcast]
  exact hentry

end GlobalTheory.RedTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFramesStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carried_frame_triangular_through_stalkFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  first | exact @GlobalTheory.ShFam.CarriesAt.tri_of_carries | exact GlobalTheory.ShFam.CarriesAt.tri_of_carries | (intros; apply GlobalTheory.ShFam.CarriesAt.tri_of_carries <;> assumption)
end


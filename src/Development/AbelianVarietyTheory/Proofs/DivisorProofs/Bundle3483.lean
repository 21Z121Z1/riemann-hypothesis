import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3465
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.LocRegCmp
open GlobalTheory.FlagMod (ev)

theorem leibniz_ext_of_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) {C : Type} [CommRing C]
    (ψ : Γ(X, W.1) →+* C) (d : C → C) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ Γ(X, W.1) Γ(X, W.1))
    (h : ∀ r, d (ψ ((X.presheaf.map (homOfLE hW).op).hom r)) = ψ (D ((X.presheaf.map (homOfLE hW).op).hom r)))
    (b : Γ(X, W.1)) : d (ψ b) = ψ (D b) := by
  have d0 : d 0 = 0 := by simpa using hadd 0 0
  have d1 : d 1 = 0 := by simpa using hd 1 1
  let g₁ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (d (ψ r))
      map_one' := by ext <;> simp [d1]
      map_zero' := by ext <;> simp [d0]
      map_add' := fun a b => by ext <;> simp [hadd]
      map_mul' := fun a b => by ext <;> simp [hd, mul_comm] }
  let g₂ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (ψ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, mul_comm] }
  have e : g₁.comp (X.presheaf.map (homOfLE hW).op).hom = g₂.comp (X.presheaf.map (homOfLE hW).op).hom := by
    refine RingHom.ext fun r => ?_
    ext
    · simp [g₁, g₂]
    · simpa [g₁, g₂] using h r
  have : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e2 : spMap g₁ ≫ chart W = spMap g₂ ≫ chart W := by
    rw [← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp',
      GlobalTheory.LogKSLoc.spMap_comp', e]
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 ((cancel_mono (chart W)).1 e2))
  have e4 : g₁ b = g₂ b := congrArg (fun k => k b) e3
  simpa [g₁, g₂] using congrArg TrivSqZeroExt.snd e4

theorem isKS_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1))
    (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))
    (hD : ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r))
    (hKS : IsKS t V U v D Θ) :
    IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW
      ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  obtain ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    refine leibniz_ext_of_res U W hW _ _ ((hfld i).1 _ inf_le_left) ((hfld i).2.1 _ inf_le_left) DW (fun r => ?_) b
    rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp']

theorem ks_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm U W hW n v hv hb D DW Θ hDW hKS k _ _ m d ξ hx t φ hEt hbd vR hvR hvRφ D' hD' ΘR hKSR h hh hρh a b s N hs
  let ι0 : ChartRing k m d →+* FractionRing (ChartRing k m d) := algebraMap _ _
  let g : Sp (ChartRing k m d) ⟶ Y.X := ξ ≫ genι Y
  have hι0 : Function.Injective ι0 := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_ringHom (f := ι0.comp (algebraMap k (ChartRing k m d))) (hι0.comp (algebraMap k _).injective)
  obtain ⟨hg, hgρ⟩ := GlobalTheory.LocReg.chart_appLE_eq E H Dw l Xo c Y U k m d ξ hx
  have eR : ∀ x : ChartRing k m d, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv_hom_id_apply x
  have hgx : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r) =
      GlobalTheory.LocReg.chartHom Y U ξ hx r := by
    intro r; rw [hgρ]; exact eR _
  obtain ⟨hUW, D'', hDtop, hDW'⟩ := GlobalTheory.LocReg.deriv_ext_basicOpen Y.X U W (hW.le.trans inf_le_left) D.1 DW hDW h hh _ g hg D'
    (fun r => by rw [hgx, hgx]; exact hD' r)
  let U' : (Sp (ChartRing k m d)).affineOpens :=
    (Sp (ChartRing k m d)).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)
  have hU'U : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (g.preimage_mono (hW.le.trans inf_le_left))
  let v' : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), U'.1)) ⟶ t.G.left) := fun i =>
    spMap (dualMap ((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom) ≫ vR i
  have hv' : ∀ i, IsTanAtG t (chart U') (v' i) := fun i =>
    GlobalTheory.KSAgree.tan_res E H _ t ⟨⊤, isAffineOpen_top _⟩ U' le_top (vR i) (hvR i)
  have hcompU : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU'U).hom) ≫ v i := by
    intro i
    show (spMap _ ≫ vR i) ≫ φ.φ = _
    rw [Category.assoc, hvRφ i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap, ← hgρ,
      ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have hcompW : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE W.1 U'.1 hUW).hom) ≫
      (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) := by
    intro i
    rw [hcompU i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  let V' : (Sp (ChartRing k m d)).Opens := (Sp (ChartRing k m d)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))
  have hUV' : U'.1 ⊓ V' ≤ g ⁻¹ᵁ interior Y := by
    intro p hp
    have hp2 : p ∈ V' := hp.2
    have hnp : ∏ i, bdParam k m d i ∉ p.asIdeal := by
      have := hp2
      simp only [V'] at this
      rw [basicOpen_eq_of_affine] at this
      exact this
    have hnb : ξ p ∉ genBd Y := fun h' => hnp ((hbd p).1 h')
    obtain ⟨y, hy⟩ : ξ p ∈ Set.range Y.jQ := by
      by_contra h'
      exact hnb (mem_genBd.2 h')
    show g p ∈ (interior Y : Set Y.X)
    rw [GlobalTheory.LogKS.interior, Scheme.Hom.coe_opensRange]
    refine ⟨y, ?_⟩
    show (Y.jQ ≫ pullback.fst _ _) y = (ξ ≫ genι Y) p
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
  have hprod : ∏ i, bdParam k m d i ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  let x0 : Sp (FractionRing (ChartRing k m d)) ⟶ Y.X := spMap ι0 ≫ g
  have hevtop : ∀ (hK : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens)) r,
      ev (spMap ι0) ⊤ hK r = ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r) := by
    intro hK r
    unfold ev
    have : (spMap ι0).appLE ⊤ ⊤ hK = (spMap ι0).appTop := Scheme.Hom.appLE_eq_app _
    rw [this, Scheme.ΓSpecIso_naturality]
    rfl
  have hx0U : ⊤ ≤ x0 ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp (spMap ι0) hg
  have hevU : ∀ r, ev x0 U.1 hx0U r = ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx r) := by
    intro r
    rw [GlobalTheory.FlagMod.ev_spMap ι0 g U.1 hg hx0U]
    show ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = _
    rw [hgx]
  have htop : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens) := fun _ _ => trivial
  have hx0h : ⊤ ≤ x0 ⁻¹ᵁ Y.X.basicOpen h := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev x0 U.1 hx0U h
      (by rw [hevU]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hx0W : ⊤ ≤ x0 ⁻¹ᵁ W.1 := fun p hp => hh (hx0h hp)
  have hKU' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ U'.1 := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop ((g.appLE U.1 ⊤ hg).hom h)
      (by rw [hevtop, hgx]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hKV' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ V' := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop _
      (by rw [hevtop, eR]; exact ((map_ne_zero_iff ι0 hι0).2 hprod).isUnit) p
  have hint : ⊤ ≤ x0 ⁻¹ᵁ interior Y := fun p hp => hUV' ⟨hKU' hp, hKV' hp⟩
  obtain ⟨P₀, θ0, hpb, hiso⟩ := GlobalTheory.KSUniq.exists_polAV_interior Y x0 hint
  obtain ⟨mm, hmm, hiso'⟩ := GlobalTheory.PolAVPull.polAV_pull E H Y.X _ Y.t t g φ _ (spMap ι0) P₀ θ0 hpb hiso
  let φK := ev (spMap ι0) U'.1 hKU'
  have hpt : spMap φK ≫ chart U' = spMap ι0 := GlobalTheory.FlagMod.spMap_ev (spMap ι0) U'.2 hKU'
  have hvW : ∀ i, IsTanAtG Y.t (chart W) (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) :=
    fun i => GlobalTheory.KSAgree.tan_res E H Y.X Y.t U W _ (v i) (hv i)
  have hks1 := GlobalTheory.KSBaseChange.isKS_pull E H Y.X _ Y.t t g φ (interior Y) V' W U' hUW hUV' n _ v' hvW hv' hcompW DW D'' hDW' Θ hKS
  have hks2 := isKS_restrict t V' ⟨⊤, isAffineOpen_top _⟩ U' le_top vR _ D'' ΘR hDtop hKSR
  have hb' := GlobalTheory.BasisPull.tanBasis_pull E H Y.X _ Y.t t g φ U U' hU'U n v v' hv hb hv' hcompU
  have huniq := GlobalTheory.KSPtUniq.isKS_unique_at_point E H _ t V' U' n v' hv' hb' _ φK P₀ mm
    (by rw [hpt]; exact hKV') (by rw [hpt]; exact hmm) hiso' _ _ _ hks1 hks2
  have hab := congrFun (congrFun huniq a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hab
  have e1 : φK ((g.appLE W.1 U'.1 hUW).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_appLE (spMap ι0) g hUW hKU' hx0W (Θ a b)
  have e2 : φK (((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom (ΘR a b)) =
      ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b)) :=
    (GlobalTheory.FlagMod.ev_res (spMap ι0) le_top hKU' htop (ΘR a b)).trans (hevtop _ _)
  have r1 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx s) :=
    (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U s).trans (hevU s)
  have r2 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N)) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx h) ^ N := by
    rw [← map_pow, ← map_pow]
    exact (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U (h ^ N)).trans (hevU _)
  have r3 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_res x0 hh hx0h hx0W _
  have hsx := congrArg (ev x0 (Y.X.basicOpen h) hx0h) hs
  rw [map_mul, r1, r2, r3, ← e1, hab, e2] at hsx
  apply hι0
  rw [map_mul, map_pow]
  exact hsx

end GlobalTheory.LocRegCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefined
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem isometric_pull_pull' {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ}
    {h h' : Y → ℝ} (H : ∀ z : Y, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem dim_of_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] {p : X ⟶ Sp k} (hp : IsAmb p) (i : Y ⟶ X)
    [IsClosedImmersion i] {x : X} {d : ℕ} (hx : HasDim x d) (hg : i (genericPoint Y) = x) :
    topologicalKrullDim Y = d := by
  have H := (GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp).2.2.2.2
  rw [← H.2 Y d, ← H.1 Y i (genericPoint Y) d, hg]
  exact hx

theorem recVal_indep_section (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L : Fin m → HermLB q) (N : HermLB q) {r r' : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    (hr' : IsRatSec N.B r') : recVal (T m L) L N hr = recVal (T m L) L N hr' := by
  cases m with
  | zero =>
    have H : ∀ z : Y, Order.coheight z = 1 → T 0 L z = Real.log (Nat.card (Y.residueField z)) := fun z hz =>
      hT.zero L z (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq 0 hY).1 z).1 hz)
    rw [recVal_congr H, recVal_congr H]
    exact GlobalTheory.T.arithmetic_curve_degree_independent_of_section k Y q hq hY N L r hr r' hr'
  | succ e => exact GlobalTheory.T.mixedHeightInduction_independent_of_section hInt hRec k Y q hq e hY T hT N L r hr r' hr'

theorem recVal_indep (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L L' : Fin m → HermLB q) (hL : ∀ a, (L a).Isometric (L' a)) (M M' : HermLB q)
    (hM : M.Isometric M') {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : M'.B.ι → Y.functionFieldˣ}
    (hr' : IsRatSec M'.B r') : recVal (T m L) L M hr = recVal (T m L') L' M' hr' := by
  have H := GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hInt k Y q hq m hY T hT M r hr
  obtain ⟨r₃, hr₃, e₃⟩ := H.2.2 L' M' hM
  rw [H.1 L L' hL, ← e₃]
  exact recVal_indep_section hInt hRec m hq hY hT L' M' hr₃ hr'

end GlobalTheory.MixHt.StepVal

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem recVal_eq_of_same (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k}
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (hg : i (genericPoint Y) = x)
    (M' M'' : HermLB q) (L' L'' : Fin m → HermLB q) (hM' : (M.pull i hi).Isometric M')
    (hM'' : (M.pull i hi).Isometric M'') (hL' : ∀ a, ((L a).pull i hi).Isometric (L' a))
    (hL'' : ∀ a, ((L a).pull i hi).Isometric (L'' a)) {r' : M'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec M'.B r')
    {r'' : M''.B.ι → Y.functionFieldˣ} (hr'' : IsRatSec M''.B r'') :
    recVal (fun z => T m L (i z)) L' M' hr' = recVal (fun z => T m L (i z)) L'' M'' hr'' := by
  have hq : IsAmb q := by subst hi; exact hp.sub i
  have hY := dim_of_genericPoint hp i hx hg
  obtain ⟨T', hT'⟩ := hall k Y q hq
  have E : ∀ N : Fin m → HermLB q, (∀ a, ((L a).pull i hi).Isometric (N a)) → ∀ z : Y, Order.coheight z = 1 →
      T m L (i z) = T' m N z := fun N hN z hz =>
    GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X Y p q hp i hi m m T T' hT hT' m le_rfl le_rfl L N hN z
      (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq m hY).1 z).1 hz)
  rw [recVal_congr (E L' hL'), recVal_congr (E L'' hL'')]
  exact recVal_indep hInt hRec m hq hY hT' L' L'' (fun a => (hL' a).symm.trans (hL'' a)) M' M''
    (hM'.symm.trans hM'') hr' hr''

theorem recVal_eq_of_two (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p)
    {Y₁ : Scheme.{0}} [IsIntegral Y₁] [IsLocallyNoetherian Y₁] {q₁ : Y₁ ⟶ Sp k}
    (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ p = q₁) (hg₁ : i₁ (genericPoint Y₁) = x)
    (M₁ : HermLB q₁) (L₁ : Fin m → HermLB q₁) (hM₁ : (M.pull i₁ hi₁).Isometric M₁)
    (hL₁ : ∀ a, ((L a).pull i₁ hi₁).Isometric (L₁ a)) {r₁ : M₁.B.ι → Y₁.functionFieldˣ} (hr₁ : IsRatSec M₁.B r₁)
    {Y₂ : Scheme.{0}} [IsIntegral Y₂] [IsLocallyNoetherian Y₂] {q₂ : Y₂ ⟶ Sp k}
    (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ p = q₂) (hg₂ : i₂ (genericPoint Y₂) = x)
    (M₂ : HermLB q₂) (L₂ : Fin m → HermLB q₂) (hM₂ : (M.pull i₂ hi₂).Isometric M₂)
    (hL₂ : ∀ a, ((L a).pull i₂ hi₂).Isometric (L₂ a)) {r₂ : M₂.B.ι → Y₂.functionFieldˣ} (hr₂ : IsRatSec M₂.B r₂) :
    recVal (fun z => T m L (i₁ z)) L₁ M₁ hr₁ = recVal (fun z => T m L (i₂ z)) L₂ M₂ hr₂ := by
  obtain ⟨g, hiso, hgi, hη⟩ := GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint X Y₁ Y₂ i₁ i₂ (hg₁.trans hg₂.symm)
  have hgq : g ≫ q₁ = q₂ := by rw [← hi₁, ← hi₂, ← Category.assoc, hgi]
  have hq₁ : IsAmb q₁ := by subst hi₁; exact hp.sub i₁
  have hq₂ : IsAmb q₂ := by subst hi₂; exact hp.sub i₂
  have hY₁ := dim_of_genericPoint hp i₁ hx hg₁
  have tr := GlobalTheory.T.inductive_height_formula_rhs_transport_iso k Y₁ Y₂ q₁ q₂ hq₁ hq₂ g hgq hη hiso m hY₁ (fun z => T m L (i₁ z)) L₁ M₁ r₁ hr₁
  rw [← tr]
  have hfun : (fun w => T m L (i₁ (g w))) = fun w => T m L (i₂ w) := by
    funext w
    rw [← hgi]
    simp
  rw [hfun]
  refine recVal_eq_of_same hInt hRec m hall hp hT hx M L i₂ hi₂ hg₂ _ _ _ _ ?_ hM₂ (fun a => ?_) hL₂ _ hr₂
  · exact (isometric_pull_pull' M i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans (hM₁.pull g hgq)
  · exact (isometric_pull_pull' (L a) i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans ((hL₁ a).pull g hgq)

theorem step_val : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T,
    IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ,
    ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q),
    (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) →
    ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  intro hInt hRec m hall k _ X p hp T hT x hx M L
  classical
  by_cases H : ∃ v : ℝ, ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (q : Y ⟶ Sp k)
      (i : Y ⟶ X) (_ : IsClosedImmersion i) (hi : i ≫ p = q) (_ : i (genericPoint Y) = x) (M' : HermLB q)
      (L' : Fin m → HermLB q) (_ : (M.pull i hi).Isometric M') (_ : ∀ a, ((L a).pull i hi).Isometric (L' a))
      (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr
  · obtain ⟨v, Y₁, _, _, q₁, i₁, _, hi₁, hg₁, M₁, L₁, hM₁, hL₁, r₁, hr₁, rfl⟩ := H
    exact ⟨_, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      recVal_eq_of_two hInt hRec m hall hp hT hx M L i₁ hi₁ hg₁ M₁ L₁ hM₁ hL₁ hr₁ i hi hg M' L' hM hL hr⟩
  · exact ⟨0, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      absurd ⟨_, Y, ‹_›, ‹_›, q, i, ‹_›, hi, hg, M', L', hM, hL, r, hr, rfl⟩ H⟩

end GlobalTheory.MixHt.StepVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_unit_locus_open : ∀ (S' : Scheme.{0}) (d : ℕ), ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.UnitLocus.natCast_unit_locus) | (exact GlobalTheory.UnitLocus.natCast_unit_locus) | (intros; apply GlobalTheory.UnitLocus.natCast_unit_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Desc.OpenChart

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x ∧
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨hx, ?_, ?_⟩
  · rw [hψ]
    exact GlobalTheory.TorRef.isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

theorem nonempty_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  intro E _ _ _ H Dw l Xo c S j _ A _ hA x hx
  obtain ⟨x', rfl⟩ := hx
  haveI : Smooth Xo.s := by haveI := Xo.smooth; exact SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI hreg : IsRegularLocalRing ((Xo.XF c).presheaf.stalk x') :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  obtain ⟨hcen, hEt, hres⟩ := completedStalk_chart (Xo.XF c) x'
  obtain ⟨ιF⟩ := GlobalTheory.GenFan.exists_ringHom_stalk c.F (Xo.XF c)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  set St := (Xo.XF c).presheaf.stalk x'
  set R := AdicCompletion (maximalIdeal St) St
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion St
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  let g : Sp R ⟶ Xo.XF c := GlobalTheory.fromSpecCompletedStalk (Xo.XF c) x'
  have hcz : CharZero R := (RingHom.charZero_iff ((algebraMap St R).comp ιF).injective).1 inferInstance
  have hb : Function.Bijective (j.stalkMap (g (closedPoint R))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨{
    R := R
    complete := inferInstance
    charZero := hcz
    ξ := g ≫ j
    centre := by
      show j (g (closedPoint R)) = j x'
      rw [hcen]
    etc := GlobalTheory.MemberEt.isEtaleCompletion_comp_openImmersion _ _ j R g hEt
    unr := by
      apply RingHom.FormallyUnramified.of_surjective
      rw [Scheme.stalkClosedPointTo_comp]
      exact hres.comp hb.2
    G := (Over.pullback g).obj A
    semi := IsSemiAbelian.pullback (f := g) A hA
    y := jK R ≫ g
    hy := Category.assoc _ _ _
    α := pullback.fst ((Over.pullback g).obj A).hom (jK R) ≫ pullback.fst A.hom g
    gen := IsGrpPullback.comp (isGrpPullback_pullback _ (jK R)) (isGrpPullback_pullback A g) }⟩

end GlobalTheory.Desc.OpenChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OntoXAndLamLowOfPublishedUE
section
namespace GlobalTheory.Fc.S0

theorem ontoX_and_lamLow_of_classicalTheoremsUE :
    S0.HypothesesUE → GlobalTheory.BigOn.OntoX ∧ GlobalTheory.BigTop.LamLow := by
  intro P
  exact ⟨GlobalTheory.BigOn.ontoX_of_classicalTheorems P.greenCuspidal P.clozelCohomological P.cohomologicalCsdTempered
      P.heckeLAdicCharacter P.chebotarevDegreeOne P.discreteSpectrumGL
      P.galoisRepOfPolarizedCuspidal P.baseChangeDefiniteUnitary
      P.bhattScholzeCrystallineLattices P.heckeLAdicCharacterAbove P.cuspRapidDecay
      (GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc
      P.litN.loc.dzi P.litN.loc.brauer P.litN.loc.chev P.globalArtinReciprocity P.litN.loc.exh
      P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel P.litN.loc.geo P.litN.loc.bz)
      P.discreteSeriesCover P.casselmanWallach,
    GlobalTheory.BigTop.lamLow_of_classicalTheorems P.cuspRapidDecay P.weilSiegelFormulaUnitary
      P.siegelWeilUnitaryConvergent P.doublingMethod P.unramifiedDoublingGL
      P.bernsteinZelevinskyFiniteness P.formalDegreeCompactDual⟩

end GlobalTheory.Fc.S0
end


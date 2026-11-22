import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChart
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGener
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

namespace GlobalTheory.LocReg

theorem exists_basicOpen_chartHom_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y U W hW k _ m d ξ hx hbd
  let gp : Sp (ChartRing k m d) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (ChartRing k m d))
  have hprod : (∏ i, bdParam k m d i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ hX => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) hX
      simp at this
  have hgbd : ξ gp ∉ genBd Y := by
    rw [hbd]
    exact fun h => hprod ((Submodule.mem_bot _).1 h)
  have hgab : genι Y (ξ gp) ∈ interior Y := by
    have := (mem_genBd_iff (Y := Y) (x := ξ gp)).not.1 hgbd
    rw [not_not, ← coe_interior] at this
    exact this
  have hsp : gp ⤳ closedPoint (ChartRing k m d) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (fun x hx => by
      rw [(Submodule.mem_bot _).1 hx]; exact Ideal.zero_mem _)
  have hgU : ξ gp ∈ genι Y ⁻¹ᵁ U.1 :=
    (hsp.map ξ.continuous).mem_open (genι Y ⁻¹ᵁ U.1).isOpen hx
  have hyW : genι Y (ξ gp) ∈ W.1 := by
    rw [hW]; exact ⟨hgU, hgab⟩
  obtain ⟨h, hle, hmem⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨_, hyW⟩ hgU
  refine ⟨h, hle, fun h0 => ?_⟩
  have hg0 : gp ∈ ξ ⁻¹ᵁ (gen Y).basicOpen (((genι Y).app U.1).hom h) := by
    show ξ gp ∈ (gen Y).basicOpen _
    rw [← Scheme.preimage_basicOpen]; exact hmem
  rw [Scheme.preimage_basicOpen] at hg0
  have e := congrArg (fun q => q.hom (((genι Y).app U.1).hom h)) (Scheme.germ_stalkClosedPointTo ξ _ hx)
  simp only [chartHom, RingHom.comp_apply] at h0
  change (Scheme.stalkClosedPointTo ξ).hom (((gen Y).presheaf.germ _ _ hx).hom _) = 0 at h0
  rw [← CommRingCat.comp_apply] at h0
  rw [e] at h0
  have h1 := h0
  rw [CommRingCat.comp_apply] at h1
  have hz : (ξ.app (genι Y ⁻¹ᵁ U.1)).hom (((genι Y).app U.1).hom h) = 0 :=
    (ConcreteCategory.bijective_of_isIso _).1 (h1.trans (map_zero _).symm)
  rw [hz, Scheme.basicOpen_zero] at hg0
  exact hg0

end GlobalTheory.LocReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleSection_unit_at_closedPoint_torusChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ mu α : P.D.toPre.X, ∃ σ : P.D.toPre.SecB e α, ∀ zz J, Good P.D.toPre.P.L zz J → IsUnit (sval σ (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz J) := by
  first | exact @GlobalTheory.SecConst.exists_secB_isUnit_const | exact GlobalTheory.SecConst.exists_secB_isUnit_const | (intros; apply GlobalTheory.SecConst.exists_secB_isUnit_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorBundleSectionGenericFibreStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))), ∃ r : R, r ≠ 0 ∧ ∃ σ : Q.SecB k β, ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J = gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J := by
  first | exact @GlobalTheory.ClearSecB.exists_clear | exact GlobalTheory.ClearSecB.exists_clear | (intros; apply GlobalTheory.ClearSecB.exists_clear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedBoundaryPointMaximalIdeal
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

namespace GlobalTheory.BoundaryPoint

theorem isClosed_of_isMaximal {X : Scheme.{0}} [JacobsonSpace X] {U : X.Opens} (hU : IsAffineOpen U)
    {m : Ideal Γ(X, U)} (hm : m.IsMaximal) {x : X} (hx : x ∈ U) (h : ∀ f ∈ m, x ∉ X.basicOpen f) :
    IsClosed ({x} : Set X) := by
  have e := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hle : m ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun f hf => by
    by_contra hc
    refine h f hf ?_
    have h₁ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hc
    have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h₁
    rwa [e] at h₂
  have hmax : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hm.eq_of_le (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top hle ▸ hm
  have hc := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax
  have h₃ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹' closedPoints X := by
    rw [hU.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have h₄ : IsClosed ({hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)} : Set X) := h₃
  rwa [e] at h₄

theorem exists_closed_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y hs U m hm x hx hU h
  have hi : IsIso (genι Y) := GlobalTheory.LogKS.isIso_fst Y
  have : Smooth (genStr Y) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace (inv (genι Y) ≫ genStr Y)
  have hc := isClosed_of_isMaximal U.2 hm hU h
  obtain ⟨x', rfl⟩ := (genι Y).homeomorph.surjective x
  refine ⟨x', rfl, mem_genBd_iff.2 fun h' => hx ?_, ?_⟩
  · rw [← coe_interior] at h'
    exact h'
  · rw [← (genι Y).homeomorph.isClosed_image, Set.image_singleton]
    exact hc

end GlobalTheory.BoundaryPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffsTangentVectorTranslatedBasis
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertSpan

theorem exists_coeffs_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
  intro E _ _ _ H X t U n v hv hb S _ φ g₀ w hg hred hw
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', ← Spec.map_id]
    congr 1
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  let w' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G := Over.homMk w hw
  let s : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ _ ≫ _ = g₀ ≫ t.G.hom
      rw [← Category.assoc, e, Category.id_comp])
  have hs : s ≫ g' = s ≫ w' := by
    refine Over.OverMorphism.ext ?_
    change spMap _ ≫ spMap _ ≫ g₀ = spMap _ ≫ w
    rw [hred, ← Category.assoc, e, Category.id_comp]
  have hτ : IsTanAtG t (g₀ ≫ t.G.hom) (g'⁻¹ * w').left := by
    refine ⟨Over.w (g'⁻¹ * w'), ?_⟩
    change (s ≫ (g'⁻¹ * w')).left = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, hs, inv_mul_cancel]
  have hbas := (GlobalTheory.LineNorm.isTanBasis_of_basis E H X t _ (chart U) n v hv hb).2 S φ (g'⁻¹ * w').left
  rw [← hg] at hbas
  obtain ⟨c, ⟨u, hu, hux⟩, -⟩ := hbas hτ
  have hwu : w' = g' * (List.ofFn u).prod := by
    rw [show (List.ofFn u).prod = g'⁻¹ * w' from Over.OverMorphism.ext hux, mul_inv_cancel_left]
  refine ⟨c, fun S' _ ρ φ' wt hg' hwt O hO f => ?_⟩
  have h₃ : (spMap ρ ≫ g₀) ≫ t.G.hom = spMap (ρ.comp φ) ≫ chart U := by
    rw [Category.assoc, hg, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
  have hU : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    change ⊤ ≤ ((spMap ρ ≫ g₀) ≫ t.G.hom) ⁻¹ᵁ U.1
    rw [hg']
    exact GlobalTheory.Points.le_preimage_specMap_fromSpec U.2 (CommRingCat.ofHom φ')
  obtain rfl : φ' = ρ.comp φ := RingHom.ext fun r =>
    (GlobalTheory.LogKSLin.valR_base U le_rfl hg' hU r).symm.trans (GlobalTheory.LogKSLin.valR_base U le_rfl h₃ hU r)
  choose g'' v'' hg'' hv'' hw'' using hwt
  have e' : spMap (dualMap ρ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp']
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : tEpsG ((spMap ρ ≫ g₀) ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) := Over.homMk (spMap (dualMap ρ)) (by
    change _ ≫ _ ≫ _ = _ ≫ (_ ≫ _) ≫ _
    rw [← Category.assoc, e']
    simp only [Category.assoc])
  have hkg : (k ≫ g').left = spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ ≫ g₀ := by
    change spMap _ ≫ spMap _ ≫ g₀ = _
    rw [← Category.assoc, e', Category.assoc]
  have hgg : ∀ a, g'' a = k ≫ g' := fun a => Over.OverMorphism.ext ((hg'' a).trans hkg.symm)
  have hy0 : ∀ a, smT ((spMap ρ ≫ g₀) ≫ t.G.hom) 0 (v'' a) = 1 := fun a => by
    have ht := GlobalTheory.LieMet.isTan_map (ρ.comp φ) h₃.symm (hv a)
    rw [show v'' a = ovT ht from Over.OverMorphism.ext (hv'' a)]
    exact smT_zero_ovT ht
  have hku : ∀ a, k ≫ u a = smT ((spMap ρ ≫ g₀) ≫ t.G.hom) (ρ (c a)) (v'' a) := fun a => by
    refine Over.OverMorphism.ext ?_
    change spMap (dualMap ρ) ≫ (u a).left = spMap (epsMul (ρ (c a))) ≫ (v'' a).left
    rw [hu a, hv'' a]
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    refine RingHom.ext fun z => ?_
    ext <;> simp [epsMul, dualMap]
  have hmain : spMap (dualMap ρ) ≫ w = ((k ≫ g') * (List.ofFn fun a =>
      smT ((spMap ρ ≫ g₀) ≫ t.G.hom) (ρ (c a)) (v'' a)).prod).left := by
    change (k ≫ w').left = _
    rw [hwu, MonObj.comp_mul, GlobalTheory.FirstOrderValue.comp_prod_ofFn]
    simp only [hku]
  rw [hmain]
  refine (GlobalTheory.KSLin.snd_valR_translate_prod _ t.G (spMap ρ ≫ g₀) (k ≫ g') hkg v'' (fun a => ρ (c a)) hy0 O f
    hO).trans (Finset.sum_congr rfl fun a _ => ?_)
  rw [← hw'' a, hgg a]

end GlobalTheory.VertSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVariety
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HeatConst

theorem const_of_regular_on_cover : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  intro K _ P₀ F _ ψ ξ hξ hinj I W hW hWξ y hy
  choose h hh using hy
  have hagree : ∀ i j, rsT (h i) (W i ⊓ W j) = rsT (h j) (W i ⊓ W j) := by
    intro i j
    have hij : ⊤ ≤ ξ ⁻¹ᵁ (W i ⊓ W j) := fun p hp => ⟨hWξ i hp, hWξ j hp⟩
    refine sub_eq_zero.1 (hinj _ _ hij ?_)
    rw [GlobalTheory.LogKSBal.valR_eq ξ hij, map_sub, ← GlobalTheory.LogKSBal.valR_eq ξ hij, ← GlobalTheory.LogKSBal.valR_eq ξ hij,
      GlobalTheory.LogKSBal.valR_rsT ξ inf_le_left hij, GlobalTheory.LogKSBal.valR_rsT ξ inf_le_right hij, hh, hh, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq W (O := ⊤) (fun _ => le_top) hW.ge h hagree
  obtain ⟨u, hu⟩ := (GlobalTheory.globalFns_holds (Sp K) P₀.A P₀.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u, ?_⟩
  obtain ⟨i, -⟩ : ∃ i, ξ.base (IsLocalRing.closedPoint F) ∈ W i := by
    have : ξ.base (IsLocalRing.closedPoint F) ∈ (⨆ i, W i) := by rw [hW]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop : ⊤ ≤ ξ ⁻¹ᵁ (⊤ : P₀.A.left.Opens) := fun _ _ => trivial
  have hc : t = constFn P₀.A.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u) := by
    rw [← hu]
    simp [constFn, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [← hh i, ← ht i, GlobalTheory.LogKSBal.valR_rsT ξ le_top (hWξ i), hc, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ htop hξ]

end GlobalTheory.HeatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem genPt_mem_cover : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  intro R _ G Ω _ _ φ x' hx c hc J W hW
  set K := FractionRing Ω
  have hK : (⊤ : (Sp K).Opens) ≤ (spMap (algebraMap Ω K) ≫ x') ⁻¹ᵁ (⨆ i, W i) := by
    rw [hW, ← Scheme.Hom.comp_preimage]
    rw [Category.assoc, hx]
    simp only [GlobalTheory.HeatV.bo, Scheme.affineBasicOpen_coe, Scheme.preimage_basicOpen_top]
    rw [Scheme.basicOpen_of_isUnit]
    have e : spMap (algebraMap Ω K) ≫ spMap φ = Spec.map (CommRingCat.ofHom ((algebraMap Ω K).comp φ)) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e]
    have h1 := congrArg (fun f => f.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((algebraMap Ω K).comp φ)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [← h1]
    refine IsUnit.map _ ?_
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    exact hc ((IsFractionRing.injective Ω K) (by simpa using h0))
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hp := hK (Set.mem_univ p)
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim _ _
  subst this
  exact hi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationAway
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg

theorem exists_derivation_away {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f : A)
    (hloc : letI := φ.toAlgebra; IsLocalization.Away f B) (d : A → A)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = x * d y + y * d x) :
    ∃ D : Derivation ℤ B B, ∀ a, D (φ a) = φ (d a) := by
  letI := φ.toAlgebra
  have h0 : d 0 = 0 := by
    have e := hadd 0 0
    rw [add_zero] at e
    linear_combination -e
  have h1 : d 1 = 0 := by
    have e := hmul 1 1
    rw [_root_.mul_one, _root_.one_mul] at e
    linear_combination -e
  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (φ (d a))
      map_one' := by ext <;> simp [h1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul]
          ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun x y => by ext <;> simp [hadd] }
  have hu : IsUnit (ψ f) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [ψ, RingHom.algebraMap_toAlgebra] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let Λ : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hΛ : ∀ a, Λ (φ a) = ψ a := fun a => IsLocalization.lift_eq (M := Submonoid.powers f) (S := B) _ a
  have hfst : ∀ x, (Λ x).fst = x := by
    have : (TrivSqZeroExt.fstHom ℤ B B).toRingHom.comp Λ = RingHom.id B := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [RingHom.algebraMap_toAlgebra, hΛ, ψ]
    intro x
    exact congr($this x)
  let L : B →+ B :=
    { toFun := fun x => (Λ x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨Derivation.mk' L.toIntLinearMap (fun x y => ?_), fun a => ?_⟩
  · show (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · show (Λ (φ a)).snd = φ (d a)
    rw [hΛ]
    simp [ψ]

theorem deriv_ext_basicOpen : ∀ (X : Scheme.{0}) (U W : X.affineOpens) (hWU : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)), (∀ r, DW ((X.presheaf.map (homOfLE hWU).op).hom r) = (X.presheaf.map (homOfLE hWU).op).hom (D r)) → ∀ (h : Γ(X, U.1)), X.basicOpen h ≤ W.1 → ∀ (R : Type) [CommRing R] [Algebra ℤ R] (g : Sp R ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1) (D' : Derivation ℤ R R), (∀ r, D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom (D r))) → ∃ (hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ g ⁻¹ᵁ W.1) (D'' : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1)), (∀ r, D'' (((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom r) = ((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)))) ∧ (∀ θ, D'' ((g.appLE W.1 _ hUW).hom θ) = (g.appLE W.1 _ hUW).hom (DW θ)) := by

  intro X U W hWU D DW hDW h hhW R _ _ g hg D' hD'
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  set f := (g.appLE U.1 ⊤ hg).hom h with hf
  have hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f).1 ≤ g ⁻¹ᵁ W.1 := by
    show (Sp R).basicOpen f ≤ _
    rw [hf, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact fun x hx => hhW hx.2
  refine ⟨hUW, ?_⟩
  set U' := ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f) with hU'
  let φ := ((Sp R).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom
  have hloc : letI := φ.toAlgebra; IsLocalization.Away f Γ(Sp R, U'.1) :=
    (isAffineOpen_top (Sp R)).isLocalization_basicOpen f
  obtain ⟨D'', hD''⟩ := exists_derivation_away φ f hloc (fun r => e.inv.hom (D' (e.hom.hom r)))
    (fun x y => by simp only [map_add]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
      simp)
  refine ⟨D'', hD'', ?_⟩

  set resUW := (X.presheaf.map (homOfLE hWU).op).hom with hresUW
  set ψW := (g.appLE W.1 U'.1 hUW).hom with hψW
  have hUU : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (fun x hx => hWU hx)
  set ψU := (g.appLE U.1 U'.1 hUU).hom with hψU
  have hψ : ∀ y, ψW (resUW y) = ψU y := fun y => by
    rw [hψW, hresUW, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hψU' : ∀ y, ψU y = φ ((g.appLE U.1 ⊤ hg).hom y) := fun y => by
    rw [hψU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hDU : ∀ y, D'' (ψU y) = ψU (D y) := fun y => by
    rw [hψU', hD'', hψU', hD']
    simp
  have hres : ∀ y, D'' (ψW (resUW y)) = ψW (DW (resUW y)) := fun y => by
    rw [hψ, hDU, hDW, hψ]
  have hunit : IsUnit (ψU h) := by
    rw [hψU']
    letI := φ.toAlgebra
    exact IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, U'.1)) f
  have key : ∀ θ : Γ(X, W.1), ∃ (a : Γ(X, U.1)) (M : ℕ), resUW (h ^ M) * θ = resUW a := by
    intro θ
    set V := X.basicOpen (resUW h) with hVdef
    have hV : V = X.basicOpen h := by
      rw [hVdef, hresUW, Scheme.basicOpen_res]
      exact inf_eq_right.2 hhW
    have hVW : V ≤ W.1 := X.basicOpen_le _
    have hVU : V ≤ U.1 := hVW.trans hWU
    let resUV := (X.presheaf.map (homOfLE hVU).op).hom
    let resWV := (X.presheaf.map (homOfLE hVW).op).hom
    have hcomp : ∀ y, resWV (resUW y) = resUV y := fun y => by
      rw [hresUW, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have hlocU : letI := resUV.toAlgebra; IsLocalization.Away h Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen h (homOfLE hVU) hV
    have hlocW : letI := resWV.toAlgebra; IsLocalization.Away (resUW h) Γ(X, V) :=
      W.2.isLocalization_basicOpen (resUW h)
    obtain ⟨⟨a, _, N, rfl⟩, hN⟩ := (letI := resUV.toAlgebra; IsLocalization.surj (Submonoid.powers h) (resWV θ))
    simp only [RingHom.algebraMap_toAlgebra] at hN
    rw [← hcomp, ← hcomp, ← map_mul] at hN
    letI := resWV.toAlgebra
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (resUW h)) (S := Γ(X, V))
      (x := θ * resUW (h ^ N)) (y := resUW a) (by simpa only [RingHom.algebraMap_toAlgebra] using hN)
    refine ⟨h ^ k * a, k + N, ?_⟩
    simp only [map_mul, map_pow] at hc ⊢
    linear_combination hc
  intro θ
  obtain ⟨a, M, hM⟩ := key θ
  have e2 := congrArg (fun x => D'' (ψW x)) hM
  have e3 := congrArg (fun x => ψW (DW x)) hM
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add] at e2 e3
  rw [hres, hres] at e2
  have hu : IsUnit (ψW (resUW (h ^ M))) := by rw [hψ, map_pow]; exact hunit.pow M
  exact hu.mul_left_cancel (by linear_combination e2 - e3)

end GlobalTheory.LocReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChartStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extension_completedEtaleChart : ∀ (A : Type) [CommRing A] [IsLocalRing A] (k : Type) [Field k] [CharZero k] (m d : ℕ) (ψ : A →+* ChartRing k m d), IsEtaleCompletion ψ → ∀ δ : Derivation ℤ A A, ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), ∀ a, D' (ψ a) = ψ (δ a) := by
  first | exact @GlobalTheory.ChartDerivation.main | exact GlobalTheory.ChartDerivation.main | (intros; apply GlobalTheory.ChartDerivation.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSeriesOfCoboundaryDvdPStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalSeries_of_coboundary_dvd_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  first | exact @GlobalTheory.QLog.exists_series_of_cobOne_dvd | exact GlobalTheory.QLog.exists_series_of_cobOne_dvd | (intros; apply GlobalTheory.QLog.exists_series_of_cobOne_dvd <;> assumption)
end


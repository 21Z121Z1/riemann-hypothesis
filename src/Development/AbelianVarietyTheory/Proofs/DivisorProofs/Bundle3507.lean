import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmul
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem ker_mod_eq_perp_range_add : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ y n hn Z Z' h hsurj t ht hiso hdiv a
  have hW : IsOpp D (LinearMap.range t) Z' := (h.symm.shear t ht hiso).symm

  have hdivZ : ∀ b ∈ Z', (∀ z : Z, (n : ℤ) ∣ D.EF (t z) b) → ∃ b'', b = n • b'' := by
    intro b hb hbd
    have hx : ∀ x : LinearMap.range t, (n : ℤ) ∣ D.EF x b := by
      rintro ⟨_, z, rfl⟩
      exact hbd z
    let φ : LinearMap.range t →+ ℤ := AddMonoidHom.mk' (fun x => D.EF x b / n) fun x x' => by
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
      exact Int.add_ediv_of_dvd_left (hx x)
    obtain ⟨b'', hb'', -⟩ := hW.2.2.1 φ
    refine ⟨b'', ?_⟩
    have h0 : (n • (b'' : D.La)) - b = 0 := by
      refine hW.eq_zero (sub_mem (Z'.nsmul_mem b''.2 n) hb) fun w hw => ?_
      have e1 := hb'' ⟨w, hw⟩
      simp only [φ, AddMonoidHom.mk'_apply] at e1
      have e2 : (n : ℤ) ∣ D.EF w b := hx ⟨w, hw⟩
      rw [ef_swap, map_sub, map_nsmul, e1, nsmul_eq_mul, Int.mul_ediv_cancel' e2]
      simp
    exact (sub_eq_zero.1 h0).symm
  have hperp0 : ∀ (k : D.La), k ∈ perp D (LinearMap.range t) → ∀ z : Z, D.EF (t z) k = 0 := by
    intro k hk z
    rw [ef_swap, hk _ ⟨z, rfl⟩, neg_zero]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨b, hb, hk⟩ := hW.exists_sub_mem_perp a
    obtain ⟨b'', hb''⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z a ⟨e, he⟩
      have h2 : D.EF (t z) b = D.EF (t z) a - D.EF (t z) (a - b) := by
        rw [map_sub]; ring
      rw [h2, hperp0 _ hk z, sub_zero]
      exact h1
    refine ⟨a - b, hk, b'', ?_⟩
    rw [← hb'', sub_add_cancel]
  · rintro ⟨k, hk, e, rfl⟩
    obtain ⟨b, hb, e₁, hb1⟩ := hsurj (y k)
    obtain ⟨b'', rfl⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z (k - b) ⟨-e₁, by rw [map_sub, hb1, smul_neg]; abel⟩
      rw [map_sub, hperp0 _ hk z, zero_sub, Int.dvd_neg] at h1
      exact h1
    refine ⟨y b'' - e₁ + y e, ?_⟩
    rw [map_nsmul] at hb1
    rw [map_add, map_nsmul, smul_add, smul_sub, hb1]
    abel

end GlobalTheory.LowFilt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOne
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthHtOne

open Module

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem le_finrank_coker_omegaMap [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h1 : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1))
    (he : HasLogDeg q e) : e ≤ finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  obtain ⟨N, hN⟩ := he
  have hlev : finrank k (G.A 1 ⧸ kerIdeal (q.app 1)) = p ^ e := by
    rw [← GlobalTheory.Dieu.finrank_quot_kerIdeal_eq p k G H 1 (max N 1) q q' (by rw [pow_one]; exact h1)
      (le_max_right _ _)]
    exact hN _ (le_max_left _ _)
  obtain ⟨C, _, _, _, _, π, hπ, hker, hnil, hFaug⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G H q
  have hker' : RingHom.ker π = kerIdeal (q.app 1) := by rw [hker]; exact sup_eq_left.2 hF
  have hC : finrank k C = p ^ e := by
    rw [← hlev, ← hker']
    exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : G.A 1 →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq).symm
  have hfrobC : frobKerIdeal p k C = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hnil a ha]
  have hCq : finrank k C = finrank k (C ⧸ frobKerIdeal p k C) := by
    refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (frobKerIdeal p k C)).toLinearMap
      ⟨fun a b h => ?_, Ideal.Quotient.mkₐ_surjective k _⟩)
    have h' := Ideal.Quotient.eq.1 h
    rwa [hfrobC, Ideal.mem_bot, sub_eq_zero] at h'
  have hle := GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p k C
  rw [← hCq, hC] at hle
  have hcot := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G H q C π hπ).2.1 (by rw [hker]; exact sup_le_sup_left hFaug _) hker'.ge
  rw [hcot]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

theorem finrank_coker_lieMap {A B : PDivGroup p k} (f : A ⟶ B) [FiniteDimensional k A.omega]
    [FiniteDimensional k B.omega] (hd : finrank k A.omega = finrank k B.omega) :
    finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) =
      finrank k (A.omega ⧸ LinearMap.range (omegaMap A B f)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (lieMap A B f))
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (omegaMap A B f))
  have h3 : finrank k (LinearMap.range (lieMap A B f)) = finrank k (LinearMap.range (omegaMap A B f)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (omegaMap A B f)
  have h4 : finrank k B.Lie = finrank k B.omega := Subspace.dual_finrank_eq
  omega

theorem finrank_coker_lieMap_congr {A B A' B' : PDivGroup p k} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B)
    (f' : A' ⟶ B') (hc : eA.hom ≫ f' = f ≫ eB.hom) :
    finrank k (B'.Lie ⧸ LinearMap.range (lieMap A' B' f')) =
      finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) := by
  let L : B.Lie ≃ₗ[k] B'.Lie := LinearEquiv.ofLinear (lieMap B B' eB.hom) (lieMap B' B eB.inv)
    (by rw [← lieMap_comp, eB.inv_hom_id, lieMap_id]) (by rw [← lieMap_comp, eB.hom_inv_id, lieMap_id])
  have hA : LinearMap.range (lieMap A A' eA.hom) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x => ⟨lieMap A' A eA.inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← lieMap_comp, eA.inv_hom_id, lieMap_id, LinearMap.id_apply]
  have hr : LinearMap.range (lieMap A' B' f') = (LinearMap.range (lieMap A B f)).map (L : B.Lie →ₗ[k] B'.Lie) := by
    rw [← LinearMap.range_comp_of_range_eq_top _ hA, ← lieMap_comp, hc, lieMap_comp, LinearMap.range_comp]
    rfl
  rw [hr]
  exact (Submodule.Quotient.equiv _ _ L rfl).finrank_eq.symm

end GlobalTheory.Dieu.ColengthHtOne

open GlobalTheory.Dieu.ColengthHtOne in

theorem GlobalTheory.Dieu.le_colength_of_htOne : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G →
    q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
    e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  intro p _ T k _ _ _ G H q q' e h1 h2 hF he
  have h3 := le_finrank_coker_omegaMap G H q q' e h1 hF he
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 G
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 H
  have hiso : IsIsog q := ⟨1, q', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
  have hd := (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hiso).2.2.1
  have hL := (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k H.dual G.dual (dualHom G H q)).2
  rw [finrank_coker_lieMap_congr G.bidual H.bidual q _ (bidual_hom_dualHom_dualHom q),
    finrank_coker_lieMap q hd] at hL
  refine ⟨le_trans (by exact_mod_cast h3) (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G H q).1, le_trans (by exact_mod_cast h3) hL, h3⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenClosing

theorem keyGlob : KeyGlob := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : MBLow.Rule4 κ := ⟨hH, hF, hT, hU⟩
  exact GlobalTheory.T.key_formula_even_degeneration_global_of_local_units κ hH hF (GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits κ hU (GlobalTheory.T.keyValue_unit_traits_of_uniformised_traits κ (GlobalTheory.T.keyValue_unit_uniformised_of_absValueOne κ (GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one κ h4))))

end GlobalTheory.KeyEvenClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPointStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_chart_eq_at_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  first | exact @GlobalTheory.LocRegCmp.ks_chart_eq | exact GlobalTheory.LocRegCmp.ks_chart_eq | (intros; apply GlobalTheory.LocRegCmp.ks_chart_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirst
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.ShortSpanUnitCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem abs_kap_le (Dw : Datum H) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    |(FlagTan.kap Dw τ k : ℝ)| ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
  have hk := k.2
  have h : |FlagTan.kap Dw τ k| ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
    simp only [FlagTan.kap]
    rw [abs_le]
    split_ifs <;> push_cast <;> constructor <;> omega
  rw [← Int.cast_abs]; exact_mod_cast h

theorem sum_abs_kap_le (Dw : Datum H) :
    ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
  calc ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ ∑ _τ : Psi H, ∑ _k : Fin (Dw.p + Dw.q), ((Dw.p + Dw.q : ℕ) : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => abs_kap_le Dw τ k
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem sum_abs_weightZero_le_components (Dw : Datum H) (P : WtPar Dw) :
    ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| ≤ ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| + ∑ τ, ∑ k, |(P.u₂ τ k : ℝ)| +
      (FlagTan.dimFlag Dw : ℝ) * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => ?_
  have e : (P.wt 0 τ k : ℝ) = (FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ) + (FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ) := by
    simp only [WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply]
    simp only [nsmul_eq_mul]
    push_cast; ring
  rw [e]
  calc _ ≤ |(FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ)| + |(FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, Nat.abs_cast]
      linarith [abs_add_le (FlagTan.kap Dw τ k : ℝ) (P.u₂ τ k : ℝ)]

theorem consecutiveGap_weightZero_ge (Dw : Datum H) (P : WtPar Dw) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) (g : ℤ)
    (hg : g ≤ gap (P.u₁ τ) k) : ((FlagTan.dimFlag Dw : ℤ) + 1) * g - 2 ≤ gap (P.wt 0 τ) k := by
  have hr := (P.gap_rem τ k).1
  have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
    simp only [FlagTan.kap, Fin.val_mk]
    split_ifs <;> push_cast <;> omega
  rw [gap, dif_pos h] at hr hg ⊢
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply] at hr ⊢
  simp only [nsmul_eq_mul] at hr ⊢
  have hD : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg hD]

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

theorem final_le {C Zr S Dc PP X abelian₂ L : ℝ} (hC : 0 ≤ C) (hL : 4 * C + 1 ≤ L) (hZL : L ≤ Zr) (hPP : Zr ^ 12 ≤ PP)
    (hDc : 1 ≤ Dc) (hX : 1 ≤ X) (hS : S ≤ 3 * Dc * Zr ^ 2 * X) (hLam : Real.log abelian₂ ≤ C * (Zr ^ 3 * S + Zr ^ 5)) :
    Real.log abelian₂ ≤ Dc * PP * X := by
  have hZ1 : 1 ≤ Zr := by linarith
  have hZ0 : 0 ≤ Zr := by linarith
  have hZ5 : 0 ≤ Zr ^ 5 := by positivity
  have hDX : 1 ≤ Dc * X := by nlinarith
  have h1 : Zr ^ 3 * S ≤ 3 * (Dc * X) * Zr ^ 5 := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ Zr ^ 3)
    nlinarith
  have h2 : Zr ^ 5 ≤ (Dc * X) * Zr ^ 5 := by nlinarith
  have h3 : C * (Zr ^ 3 * S + Zr ^ 5) ≤ (Dc * X) * (4 * C * Zr ^ 5) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    nlinarith
  have h4 : 4 * C * Zr ^ 5 ≤ PP := by
    have a : Zr ≤ Zr ^ 7 := by
      calc Zr = Zr ^ 1 := (pow_one _).symm
        _ ≤ Zr ^ 7 := pow_le_pow_right₀ hZ1 (by norm_num)
    have b : 4 * C ≤ Zr ^ 7 := by linarith
    have c : 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := mul_le_mul_of_nonneg_right b hZ5
    calc 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := c
      _ = Zr ^ 12 := by ring
      _ ≤ PP := hPP
  have h5 : (Dc * X) * (4 * C * Zr ^ 5) ≤ (Dc * X) * PP := mul_le_mul_of_nonneg_left h4 (by linarith)
  calc Real.log abelian₂ ≤ _ := hLam
    _ ≤ _ := h3
    _ ≤ _ := h5
    _ = Dc * PP * X := by ring

theorem sum_le {S K A1 A2 Dc W : ℝ} (hSle : S ≤ K + A2 + Dc * A1) (hK : K ≤ W) (h1 : A1 ≤ W) (h2 : A2 ≤ W)
    (hDc : 1 ≤ Dc) (hW : 0 ≤ W) : S ≤ 3 * Dc * W := by
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Dc)
  nlinarith

theorem log_sum_le {S k fr L : ℝ} (hS0 : 0 ≤ S) (hSk : S ≤ (fr * L) ^ 2 * k) (hk : Real.log k ≤ 2 * L)
    (hfr : Real.log fr ≤ L) (hL1 : 1 ≤ L) (hfr1 : 1 ≤ fr) : Real.log S ≤ 10 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hZ : 0 < fr * L := by positivity
  have hk0 : 0 < k := by
    by_contra hk0
    push_neg at hk0
    have : (fr * L) ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk0
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc Real.log S ≤ Real.log ((fr * L) ^ 2 * k) := Real.log_le_log h hSk
    _ = 2 * (Real.log fr + Real.log L) + Real.log k := by
      rw [Real.log_mul (by positivity) hk0.ne', Real.log_pow, Real.log_mul (by linarith) (by linarith)]; push_cast; ring
    _ ≤ 10 * L := by linarith

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

set_option maxHeartbeats 1000000 in

theorem short_span_uc : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  intro hP2 _hDG hSz hFD
  obtain ⟨C, hC0, hH3⟩ := GlobalTheory.T.flat_constant_abs_le_nine_explicit hP2
  have hGd := GlobalTheory.T.good_weight_antitone_gap hP2
  refine ((((((GlobalTheory.T.size_bounds_for_family hSz).and (GlobalTheory.T.weight_parameter_strict_antitone hSz)).and (Sizes.hostN (4 * C + 1))).and WtShape.wtN).and
    GlobalTheory.HSApp.wtBig_run).and hFD).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩⟩, ⟨C4, -, a4, h4⟩⟩, ⟨C5, -, a5, h5⟩⟩, ⟨C6, -, a6, h6⟩⟩ := hh
  refine ⟨0, le_rfl, max a1 (max a2 (max a3 (max a4 (max a5 a6)))), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have s1 := h1 x hx (le_trans (by simp) hle) ι p hp i hi Y hY
  have s2 := h2 x hx (le_trans (by simp) hle) ι p hp i hi
  have s3 := h3 x hx (le_trans (by simp) hle) ι p hp i
  have s4 := h4 x hx (le_trans (by simp) hle) ι p hp i
  have s5 := h5 x hx (le_trans (by simp) hle) ι p hp i hi
  have s6 := h6 x hx (le_trans (by simp) hle) ι p hp i hi Y hY

  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, hkap, hPP, -, -, -, hu12, hwt⟩ := s1
  obtain ⟨hp1, hq1, hfin, -, hsa, -⟩ := s2
  intro Z
  set P : WtPar (dat p i) := (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ :
    WtPar (dat p i)) with hP
  have hpq : (dat p i).p + (dat p i).q = (Fm.D x ι).R.r := s4.sig.2.2
  have hr2 : 0 < (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
  have hDf : (Fm.D x ι).R.f ≤ FlagTan.dimFlag (dat p i) := by
    rw [← GlobalTheory.CompHS.dimFlag_eq, s4.dim]; exact Nat.le_mul_of_pos_right _ hr2
  have hD2 : 2 ≤ FlagTan.dimFlag (dat p i) + 0 := by omega
  have hAnt := fun τ => GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P 0 (fun τ => (hsa τ).1) hD2 hp1 hq1 τ
  have hgap : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.wt 0 τ) ((dat p i).p - 1) := by
    intro τ
    have hk : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
    obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (FlagTan.dimFlag (dat p i) + 3) * ((FlagTan.dimFlag (dat p i) + 1).choose 2 +
        4 * ((dat p i).p + (dat p i).q) + FlagTan.dimFlag (dat p i) + 3) := ⟨_, rfl⟩
    have hg : (G : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := hG ▸ s5.gaps τ _ hk
    have h1 := consecutiveGap_weightZero_ge (dat p i) P τ hk _ hg
    have hG12 : 12 * (Fm.D x ι).R.r ≤ G := by
      rw [hG, hpq]
      have := Nat.mul_le_mul (show 3 ≤ FlagTan.dimFlag (dat p i) + 3 by omega)
        (show 4 * (Fm.D x ι).R.r ≤ (FlagTan.dimFlag (dat p i) + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          FlagTan.dimFlag (dat p i) + 3 by omega)
      omega
    have hN : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 ≤ (FlagTan.dimFlag (dat p i) + 1) * G := by
      have := Nat.mul_le_mul (show (Fm.D x ι).R.f + 1 ≤ FlagTan.dimFlag (dat p i) + 1 by omega) hG12
      nlinarith
    have hN' : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 12 : ℕ) : ℤ) ≤ (((FlagTan.dimFlag (dat p i) + 1) * G : ℕ) : ℤ) := by
      exact_mod_cast hN
    push_cast at hN' ⊢
    linarith
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hfr1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| := by positivity
  have hw0 := hwt 0 (Nat.zero_le _)
  have hlog := log_sum_le hS0 hw0 hkap hfr hL1 hfr1
  obtain ⟨n, w, abelian₂, hSG, hLam, -⟩ := hH3 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 _ hL1 hM hfs
    hfr le_rfl _ s6 (by rw [abs_neg]; exact hflat) (P.wt 0) (fun τ => (hAnt τ).1) hgap hlog Z
  refine ⟨n, w, fun q => (hSG.gen _).2 (Submodule.subset_span ⟨q, rfl⟩), ?_, fun q σ => ?_⟩
  · have hGO := ((hGd (Fm.D x ι) p.T hLaws _ hp1 hq1 hfin hInR Y _ _ hY.1 (P.wt 0) (fun τ => (hAnt τ).1)
      (fun τ => (hAnt τ).2)).2 Z).2.2
    rw [eq_top_iff, ← hGO]
    exact Submodule.span_le.2 fun y hy => Submodule.span_le_restrictScalars ℤ _ _ ((hSG.gen y).1 hy)
  · refine (hSG.le q σ).trans ?_
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hSG.one_le), GlobalTheory.CompHS.dimFlag_eq]
    refine Real.exp_le_exp.2 ?_
    have hZ : 0 < zBase (Fm.L x ι) := by unfold zBase; positivity
    have hkap0 : 0 ≤ kap p i := by
      have : 0 ≤ zBase (Fm.L x ι) ^ 2 * kap p i := hS0.trans hw0
      exact (mul_nonneg_iff_of_pos_left (by positivity)).1 this
    have hX : 1 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
      have := div_nonneg hkap0 (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP)); linarith
    have hW : 0 ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by positivity
    have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := by rw [← Nat.card_eq_fintype_card]; exact s4.card
    have hK : ∑ τ, ∑ k, |(FlagTan.kap (dat p i) τ k : ℝ)| ≤
        zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
      refine (sum_abs_kap_le (dat p i)).trans ?_
      rw [hcard, hpq]
      have a : 1 ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2 := by nlinarith
      have b : ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 ≤ zBase (Fm.L x ι) ^ 2 := by
        unfold zBase
        calc ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * 1 :=
              (mul_one _).symm
          _ ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * (((Fm.D x ι).R.f : ℝ) * (Fm.L x ι).sc.L ^ 2) :=
              mul_le_mul_of_nonneg_left a (by positivity)
          _ = _ := by ring
      calc _ ≤ zBase (Fm.L x ι) ^ 2 := by push_cast; exact b
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hX
    have hDc : (1 : ℝ) ≤ (FlagTan.dimFlag (dat p i) : ℝ) := by exact_mod_cast (by omega : 1 ≤ FlagTan.dimFlag (dat p i))
    have hSs := sum_le (sum_abs_weightZero_le_components (dat p i) P) hK (hu12 _ (Set.mem_insert _ _))
      (hu12 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hDc hW
    have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := le_mul_of_one_le_left (by linarith) hfr1
    exact final_le hC0 s3.big.1 hZL hPP hDc hX (by linarith) hLam

end GlobalTheory.CovTop.ShortSpanUnitCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfLbIsoFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.lbIso_of_lbIso_fieldExt : ∀ (k₀ K : Type) [Field k₀] [Field K] (i₀ : k₀ →+* K) (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ L L' : LB B.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst B.hom (spMap i₀))) (L'.pull (pullback.fst B.hom (spMap i₀))) → LBIso L L' := by
  intro k₀ K _ _ i₀ B _ hB L L' hL hL' h
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap i₀) B hB hL hL' h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
section
noncomputable section

namespace GlobalTheory.BalRank

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

def balBil : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β β' h k a y z
    simp only [LinearMap.add_apply, h a y z, k a y z]
  zero_mem' := by simp
  smul_mem' := by
    rintro n β h a y z
    simp only [LinearMap.smul_apply, h a y z]

variable {bar X}

end GlobalTheory.BalRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torsRat_of_canon : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → TorsRat G n := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hu ζ hζ Q e hD hQB G _ _ P hC
  haveI : CharZero R := hCN.2.2.2
  have hfix := GlobalTheory.T.torsion_galoisFixed_canonical_nDivided_family T R iw s ε n hCN hn hu ζ hζ Q e hD hQB G P hC
  obtain ⟨_, D', F, A', G', _, _, U', oA, oG, inc, pr, _, _, hinc, hpr, hip, _, _⟩ := hC
  exact GlobalTheory.T.torsionRational_of_retract_galoisFixed_points G G' A' U'.gen inc pr n U'.gen_hom hinc hpr hip hn hfix

end GlobalTheory.Mum
end


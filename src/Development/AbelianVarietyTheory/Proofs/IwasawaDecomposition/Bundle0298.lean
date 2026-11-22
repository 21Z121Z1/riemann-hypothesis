import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLevelOfStepZeroFormsLevelTrueColumns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardBaseRowsLabelEqRowsPartFinrank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCount

theorem card_filter_eq_finrank {V Q ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Fintype ι] [Fintype Q] [DecidableEq Q] (x : ι → V) (hx : LinearIndependent ℂ x) (lab : ι → Q)
    (P : Q → Submodule ℂ V) (hmem : ∀ k, x k ∈ P (lab k))
    (hsum : ∑ q, Module.finrank ℂ (P q) ≤ Fintype.card ι) (p : Q) :
    (Finset.univ.filter (fun k => lab k = p)).card = Module.finrank ℂ (P p) := by
  have hle : ∀ q, (Finset.univ.filter (fun k => lab k = q)).card ≤ Module.finrank ℂ (P q) := by
    intro q
    let y : {k // lab k = q} → P q := fun k => ⟨x k.1, by have h := hmem k.1; rwa [k.2] at h⟩
    have hy : LinearIndependent ℂ y := by
      apply LinearIndependent.of_comp (P q).subtype
      exact hx.comp Subtype.val Subtype.val_injective
    have := hy.fintype_card_le_finrank
    rwa [Fintype.card_subtype] at this
  have htot : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card = Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (lab k))]
  by_contra hne
  have hlt : (Finset.univ.filter (fun k => lab k = p)).card < Module.finrank ℂ (P p) := lt_of_le_of_ne (hle p) hne
  have : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card < ∑ q, Module.finrank ℂ (P q) :=
    Finset.sum_lt_sum (fun q _ => hle q) ⟨p, Finset.mem_univ _, hlt⟩
  omega

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : (Tw.sub s V) ≃+ V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      invFun := fun x => ⟨Tw.mk s x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hb : Function.Bijective (cj s) :=
    Function.bijective_iff_has_inverse.2 ⟨cj s, cj_cj s, cj_cj s⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hb (fun _ _ => rfl)
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := Submodule.ext fun _ => Iff.rfl

theorem cnt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ cOf : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, HasLab Y σ (cOf σ)) → ∀ p : A3.fam3.base3.Ix, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost cOf hLab p
  have hR := complex_data_conditions_base_level_of_primitive_links hHo.ok hHo.sep hP.char hHo.prim
  have hRow := hR.rowHyp false
  have hE : (R.toCx3 F).PartsE false := hHo.prim.sumE false
  have hinj : Function.Injective R.HE.e := hP.char.base.models.HE.1
  set L : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e with hL
  have hpart : ∀ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) =
      Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) := by
    intro q
    rw [← finrank_twSub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H), twSub_inf]
    rfl
  have hEp : Module.finrank D.what₂.LL ((s0Of R F).Ep p) = Module.finrank ℂ (R.EEp3 p ⊓ L : Submodule ℂ R.HE.H) := by
    rw [← hpart p]
    exact (R.toCx3 F).finrank_Ep F.cr false hRow.wf hRow.h2 hRow.h3 hE p
  let C := toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop
  let lf : Mult.MMap (R.MY 0) ≃ₗ[ℂ] C.Amb 0 := PiTensorProduct.lift
  let φ : R.HE.H →ₗ[ℂ] C.Amb 0 := lf.toLinearMap ∘ₗ R.HE.e
  have hφ : Function.Injective φ := lf.injective.comp hinj
  have hmemL : ∀ y : R.HE.H, φ y ∈ C.EEc false → y ∈ L := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy
    have : z = R.HE.e y := lf.injective hzy
    subst this
    exact hz
  choose x hxP hxe using fun k => (hLab (D.what₂.ft0 k)).2 k rfl
  have hxφ : ∀ k, φ (x k) = (Y.Iz.jE (D.what₂.onb0 k)).1 := fun k => (hxe k).symm
  have hli0 : LinearIndependent ℂ (fun k => ((Y.Iz.jE (D.what₂.onb0 k)).1 : C.Amb 0)) := by
    have h1 := D.what₂.onb0.toBasis.linearIndependent.map' Y.Iz.jE.toLinearMap Y.Iz.jE.ker
    have h2 := h1.map' (C.EEc false).subtype (Submodule.ker_subtype _)
    exact h2
  have hli : LinearIndependent ℂ x := by
    apply LinearIndependent.of_comp φ
    convert hli0 using 1
    funext k
    exact hxφ k
  have hxL : ∀ k, x k ∈ L := fun k => hmemL _ (by rw [hxφ k]; exact (Y.Iz.jE (D.what₂.onb0 k)).2)

  have hDim : Module.finrank ℂ L ≤ Fintype.card (Fin D.what₂.D0) := by
    let g0 : L →ₗ[ℂ] C.EEc false :=
      (φ.domRestrict L).codRestrict (C.EEc false) (fun y => Submodule.mem_map_of_mem (f := lf.toLinearMap) y.2)
    let g : L →ₗ[ℂ] D.what₂.EE0 := Y.Iz.jE.symm.toLinearMap ∘ₗ g0
    have hg : Function.Injective g := by
      intro a b h
      have h1 : g0 a = g0 b := Y.Iz.jE.symm.injective h
      have h2 : φ a = φ b := congrArg Subtype.val h1
      exact Subtype.ext (hφ h2)
    calc Module.finrank ℂ L ≤ Module.finrank ℂ D.what₂.EE0 := LinearMap.finrank_le_finrank_of_injective hg
      _ = Fintype.card (Fin D.what₂.D0) := Module.finrank_eq_card_basis D.what₂.onb0.toBasis
  have hsum : ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) ≤ Fintype.card (Fin D.what₂.D0) := by
    calc ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H)
        = ∑ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          Finset.sum_congr rfl fun q _ => (hpart q).symm
      _ = Module.finrank ℂ (⨆ q, (R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          (Formalism.IndefR.Cx.finrank_iSup_eq_sum _ (CxData.indep_of_orth _ hE.1)).symm
      _ ≤ Module.finrank ℂ ((R.toCx3 F).EEl false) := Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = Module.finrank ℂ L := finrank_twSub _ L
      _ ≤ Fintype.card (Fin D.what₂.D0) := hDim
  have hcard := card_filter_eq_finrank x hli (fun k => cOf (D.what₂.ft0 k)) (fun q => (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H))
    (fun k => ⟨hxP k, hxL k⟩) hsum p
  have hcount : ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ =
      (Finset.univ.filter (fun k => cOf (D.what₂.ft0 k) = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := D.what₂.ft0) (t := Finset.univ.filter (fun σ => cOf σ = p))
      (fun k hk => by simpa using hk)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [Formalism.BasicNotions.Rows.Data.nRows0, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hσ.2, h⟩
    · intro h; exact h.2
  rw [hEp, ← hcard]
  exact hcount

end GlobalTheory.Mem.R3.LabCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommon
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.Cartier.CommonEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add {D : CartierDiv X} {x : X} {f f' : X.functionField}
    (h : D.GeneratesAt x f) (h' : D.VanishesAt x f') : D.GeneratesAt x (f + f') := by
  obtain ⟨g, hg, a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := hg.vanishesAt_iff.1 h'
  refine ⟨g, hg, a + b, ?_, by rw [map_add, e, e', add_mul]⟩
  by_contra hu
  have : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact (show a ∈ IsLocalRing.maximalIdeal _ from by simpa using sub_mem this hb) ha

theorem exists_pow_mul_eq [IsAffine X] (t : Γ(X, ⊤)) (ht : genericPoint X ∈ X.basicOpen t)
    {f : X.functionField} (h : ∀ x ∈ X.basicOpen t, RegAt x f) :
    ∃ (n : ℕ) (a : Γ(X, ⊤)), fnOf ⊤ trivial t ^ n * f = fnOf ⊤ trivial a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := (isAffineOpen_top X).isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, ⊤)) : fnOf _ ht (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen t) c) =
      fnOf ⊤ trivial c := fnOf_resG le_top ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

theorem exists_regularAt [IsAffine X] {D : CartierDiv X} {x : X} {g : X.functionFieldˣ}
    (hg : D.IsEqn x g) (y : X) : ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹) := by
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htU, ht⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hU⟩ trivial
  obtain ⟨t', htV, ht'⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨y, hV⟩ trivial
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgU z (htU hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf ⊤ trivial (t' ^ n)) := by
    refine (unitAt_fnOf_iff (U := ⊤) trivial _ _).2 ?_
    rw [X.mem_basicOpen_top, map_pow]
    exact ((X.mem_basicOpen_top _ _).1 ht').pow n
  refine ⟨t ^ n, ?_, g', hgV y hV, ?_⟩
  · rw [X.mem_basicOpen_top, map_pow]
    exact ((X.mem_basicOpen_top _ _).1 ht).pow n
  · have := (regAt_fnOf (U := ⊤) (x := y) trivial trivial a).mul hu.inv.regAt
    rw [← e] at this
    convert this using 1
    have h0 := hu.ne_zero
    rw [map_pow] at h0
    rw [map_mul, map_pow, map_pow, mul_pow]
    field_simp

theorem exists_vanishesAt [IsAffine X] {D : CartierDiv X} {x : X} {g : X.functionFieldˣ}
    (hg : D.IsEqn x g) {y : X} (hy : IsClosed ({y} : Set X)) (hxy : y ≠ x) :
    ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hg y
  obtain ⟨t, htU, ht⟩ := (isAffineOpen_top X).exists_basicOpen_le
    (V := ⟨{y}ᶜ, hy.isOpen_compl⟩) ⟨x, hxy.symm⟩ trivial
  have hz : ZeroAt y (fnOf ⊤ trivial t) := zeroAt_iff.2 ⟨regAt_fnOf (U := ⊤) trivial _ _,
    fun h => htU ((unitAt_fnOf_iff (U := ⊤) trivial _ _).1 h) rfl⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf ⊤ trivial s)]
  exact hz.mul hr

theorem exists_generatesAt_vanishesAt [IsAffine X] (D : CartierDiv X) (x : X) (T : Finset X)
    (hT : ∀ y ∈ T, IsClosed ({y} : Set X)) :
    ∃ f, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, ⊤), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff (U := ⊤) trivial _ _).2 hs
  have key (y : X) (s t : Γ(X, ⊤))
      (h : D.VanishesAt y (fnOf ⊤ trivial s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf ⊤ trivial (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf (U := ⊤) (x := y) trivial trivial t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hg (hT y (Finset.mem_insert_self _ _)) hyx
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ _ _ h'
    · exact key _ _ _ (h z hz hzx)

theorem exists_generatesAt [IsAffine X] (D : CartierDiv X) (T : Finset X)
    (hT : ∀ y ∈ T, IsClosed ({y} : Set X)) : ∃ f, ∀ x ∈ T, D.GeneratesAt x f := by
  classical
  choose F hF hF' using fun x => exists_generatesAt_vanishesAt D x T hT
  refine ⟨∑ x ∈ T, F x, fun x hx => ?_⟩
  rw [← Finset.add_sum_erase T F hx]
  refine generatesAt_add (hF x) (Finset.sum_induction _ (D.VanishesAt x) (fun _ _ h h' => h.add h')
    (D.vanishesAt_zero x) fun y hy => hF' y x hx (Finset.ne_of_mem_erase hy).symm)

theorem exists_isEqn_of_finite [IsAffine X] (D : CartierDiv X) (S : Set X) (hS : S.Finite) :
    ∃ g : X.functionFieldˣ, ∀ z ∈ S, D.IsEqn z g := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨1, by simp⟩
  have hc (z : X) : ∃ c : X, c ∈ closure ({z} : Set X) ∧ IsClosed ({c} : Set X) :=
    isClosed_closure.exists_closed_singleton ⟨z, subset_closure rfl⟩
  choose c hc hc' using hc
  obtain ⟨f, hf⟩ := exists_generatesAt D (hS.toFinset.image c) fun y hy => by
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact hc' z
  have hf' (z : X) (hz : z ∈ S) : D.GeneratesAt (c z) f :=
    hf _ (Finset.mem_image_of_mem c (hS.mem_toFinset.2 hz))
  have h0 := (hf' z₀ hz₀).ne_zero
  refine ⟨(Units.mk0 f h0)⁻¹, fun z hz => ?_⟩
  have h1 : D.IsEqn (c z) (Units.mk0 f h0)⁻¹ :=
    CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa using hf' z hz)
  obtain ⟨U, hU, h⟩ := h1.exists_nhds
  exact h z ((specializes_iff_mem_closure.2 (hc z)).mem_open U.isOpen hU)

theorem exists_isEqn_curve : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsAffine Z], topologicalKrullDim Z ≤ 1 → ∀ (D : CartierDiv Z) (S : Set Z), S.Finite → ∃ g : Z.functionFieldˣ, ∀ z ∈ S, D.IsEqn z g :=
  fun _ _ _ _ _ D S hS => exists_isEqn_of_finite D S hS

end GlobalTheory.Cartier.CommonEqn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs
section
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

set_option autoImplicit false

namespace GlobalTheory.CayleyBlock

theorem dList_append' {σ : Type} [DecidableEq σ] (l₁ l₂ : List σ) :
    dList (l₁ ++ l₂) = dList l₁ * dList l₂ := by
  simp [dList, List.map_append, List.prod_append]

theorem smallList_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (List.finRange p).map (fun j => (σ j, j)) ++ smallList τ := by
  simp [smallList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem sgnProd_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (Equiv.Perm.sign σ : ℤ) * sgnProd τ := by
  simp [sgnProd, Fin.prod_univ_succ]

theorem cayMono_eq_dList' {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    cayMono p ℂ σ = dList ((List.finRange p).map fun j => (σ j, j)) := by
  simp [cayMono, dList, List.map_map]
  rfl

theorem cayOp_pow_eq_sum (p q : ℕ) :
    cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  induction q with
  | zero => simp [smallList, sgnProd, dList]
  | succ q ih =>
    rw [pow_succ', ih, cayOp, Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => Equiv.Perm (Fin p))).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    change _ = sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) •
      dList (smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)))
    rw [smallList_cons', sgnProd_cons', dList_append', cayMono_eq_dList', smul_mul_smul, mul_smul]

end GlobalTheory.CayleyBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquare
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign

theorem curvPoly_eq_smul_sum {n m : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) :
    curvPoly G v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem sqPoly_eq_smul_sum {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    sqPoly T = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (T (coordVec a) * (T (coordVec b))ᴴ).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [sqPoly, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]

theorem curvPoly_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    curvPoly G v = S⁻¹.map C * (-(sqPoly T)) * S.map C := by
  have key : ∀ M : Matrix (Fin m) (Fin m) ℂ,
      (S⁻¹ * (-M) * S).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = -(S⁻¹.map C * M.map C * S.map C) := by
    intro M
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg C a), Matrix.mul_neg, Matrix.neg_mul]
  rw [curvPoly_eq_smul_sum, sqPoly_eq_smul_sum]
  simp only [h, key]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem charpolyRev_neg_coeff_dim {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (P : Matrix (Fin m) (Fin m) R) :
    (Matrix.charpolyRev (-P)).coeff m = P.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self]
  have h := Matrix.det_eq_sign_charpoly_coeff (-P)
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have h2 : ((-1 : R) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  calc (-P).charpoly.coeff 0 = ((-1) ^ m * (-1) ^ m) * (-P).charpoly.coeff 0 := by rw [h2, one_mul]
    _ = P.det := by rw [mul_assoc, ← h, ← mul_assoc, h2, one_mul]

theorem chernPoly_top_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  rw [chernPoly, charpolyRev_neg_coeff_dim, curvPoly_of_negSq G v S T h, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_neg, Fintype.card_fin]
  have h1 : (S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, ← map_mul,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hS, Matrix.det_one, map_one]
  calc (S⁻¹.map C).det * ((-1) ^ m * (sqPoly T).det) * (S.map C).det
      = ((S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det) * ((-1) ^ m * (sqPoly T).det) := by ring
    _ = (-1) ^ m * (sqPoly T).det := by rw [h1, one_mul]

end GlobalTheory.PointFormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup
section
set_option autoImplicit false

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

theorem coeff_dList_of_nodup {σ : Type} [DecidableEq σ] (l : List σ) (hl : l.Nodup) (m : σ →₀ ℕ)
    (hm : ∀ v ∈ l, m v = 0) (G : MvPolynomial σ ℂ) :
    coeff m (dList l G) = coeff (m + (l.map fun v => Finsupp.single v 1).sum) G := by
  induction l generalizing m with
  | nil => simp [dList]
  | cons v l ih =>
    have hc : dList (v :: l) G = pderiv v (dList l G) := by
      simp [dList]
    rw [List.nodup_cons] at hl
    have h0 : m v = 0 := hm v (List.mem_cons_self ..)
    have h1 : ∀ w ∈ l, (m + Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
      intro w hw
      have hne : w ≠ v := fun h => hl.1 (h ▸ hw)
      rw [Finsupp.add_apply, hm w (List.mem_cons_of_mem _ hw), Finsupp.single_eq_of_ne hne, add_zero]
    rw [hc, MvPolynomial.coeff_pderiv, ih hl.2 _ h1, h0, List.map_cons, List.sum_cons, add_assoc]
    simp

end GlobalTheory.CayleyBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLevelOfStepZeroFormsLevelTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLevel_of_stepZeroFormsLevel_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F →
  ∃ L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u),
    SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb
      L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc
      L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) ∧
    F.gl.sp = L.splitG ∧ ∀ i v h, F.glev0.fr i v h = reGL (rank_eq_first_level (I.rec7 l Z).R) _ (L.frG i v h) := by
  first | exact @GlobalTheory.Mem.LevZero.colLevel_of_forms | exact GlobalTheory.Mem.LevZero.colLevel_of_forms | (intros; apply GlobalTheory.Mem.LevZero.colLevel_of_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ArInt

theorem isometric_comb_unit_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L : HermLB p) (m : ℕ), (ArInt.comb (fun _ : Unit => L) (fun _ => (m : ℤ))).Isometric (L.pow m) := by
  intro k _ X _ p L m
  rw [← HermLB.icls_eq_iff, icls_comb, HermLB.icls_pow]
  simp

end GlobalTheory.ArInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsLiftModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory

theorem ringOfIntegers_hom_complex_injective (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem model_cxPts_from_generic_fibre :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (τ : 𝓞 F →+* ℂ) (y' : CxPts M.p τ),
      ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ ∧ ∃ y : Pts Y σ, y'.1 = y.1 ≫ M.j := by
  intro F _ _ Y M τ y'
  have hτ := ringOfIntegers_hom_complex_injective F τ
  obtain ⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩
  refine ⟨σ, hσ, ?_⟩
  have hw : y'.1 ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) :=
    y'.2.trans ((congrArg spMap hσ.symm).trans (spMap_comp _ _))
  exact ⟨⟨M.pb.lift y'.1 _ hw, M.pb.lift_snd _ _ _⟩, (M.pb.lift_fst _ _ _).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTopStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  first | exact @GlobalTheory.SlabFinVol.covol_unitSlab_lt_top | exact GlobalTheory.SlabFinVol.covol_unitSlab_lt_top | (intros; apply GlobalTheory.SlabFinVol.covol_unitSlab_lt_top <;> assumption)
end


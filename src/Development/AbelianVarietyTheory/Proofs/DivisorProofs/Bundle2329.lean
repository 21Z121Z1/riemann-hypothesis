import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFiltrationSectionCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TopForm

namespace FrameBasis

theorem bijective_of_isFreeGen {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A) {m : ℕ}
    (hA : α.IsStandardSmoothOfRelativeDimension m) (x : Fin m → A)
    (hx : IsFreeGen A (dForm α x)) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension m k A := hA
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Omega α)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = m := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) m)
    let b := Module.finBasisOfFinrankEq A (Omega α) hr
    let v : Fin m → Omega α := fun i => dFun α (x i)
    obtain ⟨a, ha⟩ := hx.2 (exteriorPower.ιMulti A m b)
    have e := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) ha
    simp only [map_smul, dForm_eq, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, smul_eq_mul] at e
    have hu : IsUnit (b.det v) := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact e)
    obtain ⟨hli, hsp⟩ := (b.is_basis_iff_det).2 hu
    let b' := Module.Basis.mk hli hsp.ge
    have : (Fintype.linearCombination A fun i => dFun α (x i)) = b'.equivFun.symm.toLinearMap := by
      ext c
      simp [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply, b', v]
    rw [this]
    exact b'.equivFun.symm.bijective

end FrameBasis

end TopForm

end GlobalTheory

namespace GlobalTheory.TopForm.FrameBasis

theorem bijective_of_isLocalization_span {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {m : ℕ} (x : Fin m → A) (s : Set A) (hs : Ideal.span s = ⊤) (B : s → Type*)
    [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)] [∀ t : s, IsLocalization.Away t.1 (B t)]
    (H : ∀ t : s, Function.Bijective (Fintype.linearCombination (B t)
      fun i => dFun ((algebraMap A (B t)).comp α) (algebraMap A (B t) (x i)))) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  letI (t : s) : Algebra k (B t) := ((algebraMap A (B t)).comp α).toAlgebra
  haveI (t : s) : IsScalarTower k A (B t) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (t : s) : Algebra.FormallyEtale A (B t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t.1)
  let g : ∀ t : s, Ω[A⁄k] →ₗ[A] Ω[B t⁄k] := fun t => KaehlerDifferential.map k k A (B t)
  haveI H₁ (t : s) : IsLocalizedModule.Away t.1 (g t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (g t)).2
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A (B t))
  let π : ∀ t : s, (Fin m → A) →ₗ[A] (Fin m → B t) := fun t => (Algebra.linearMap A (B t)).compLeft (Fin m)
  haveI H₂ (t : s) : IsLocalizedModule.Away t.1 (π t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (π t)).2
      (IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap A (B t)))
  let e : ∀ t : s, (Fin m → B t) ≃ₗ[A] Ω[B t⁄k] := fun t =>
    (LinearEquiv.ofBijective _ (H t)).restrictScalars A
  haveI H₃ (t : s) : IsLocalizedModule.Away t.1 ((e t).toLinearMap ∘ₗ π t) :=
    IsLocalizedModule.of_linearEquiv _ _ _
  have hcomp (t : s) : g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i)) =
      (e t).toLinearMap ∘ₗ π t := by
    ext c
    simp [g, e, π, Fintype.linearCombination_apply, algebraMap_smul]
  haveI H₄ (t : s) : IsLocalizedModule.Away t.1
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) := by
    rw [hcomp t]; exact H₃ t
  refine bijective_of_isLocalized_span s hs (fun t => Ω[B t⁄k])
    (fun t => g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (fun t => Ω[B t⁄k]) g
    (Fintype.linearCombination A fun i => dFun α (x i)) fun t => ?_
  have : IsLocalizedModule.map (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t)
      (Fintype.linearCombination A fun i => dFun α (x i)) = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id

end GlobalTheory.TopForm.FrameBasis

namespace GlobalTheory.TopForm.FrameBasis

theorem exists_basis_of_isFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ),
    SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)),
    GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) →
    ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)),
      ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  intro k _ X p m hp U x hx
  have hU := hx.affine
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  haveI (t : (s : Set Γ(X, U))) := hU.isLocalization_basicOpen t.1
  have hbij : Function.Bijective
      (Fintype.linearCombination Γ(X, U) fun i => dFun (algX p U) (x i)) := by
    refine bijective_of_isLocalization_span (algX p U) x (s : Set Γ(X, U)) hs
      (fun t => Γ(X, X.basicOpen t.1)) fun t => ?_
    have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      (h t t.2 Γ(X, X.basicOpen t.1))
    have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen t.1)).comp (algX p U) =
        algX p (X.basicOpen t.1) := resG_comp_algX p (X.basicOpen_le t.1)
    have h₂ : (algX p (X.basicOpen t.1)).IsStandardSmoothOfRelativeDimension m := by
      rw [← resG_comp_algX p (X.basicOpen_le t.1)]
      exact h₁
    have hfr := (hx.res (hU.basicOpen t.1) (X.basicOpen_le t.1)).gen
    rw [resForm_dOn] at hfr
    have := bijective_of_isFreeGen _ h₂ _ hfr
    rw [e]
    exact this
  let eq := LinearEquiv.ofBijective _ hbij
  refine ⟨Module.Basis.ofEquivFun eq.symm, fun i => ?_⟩
  simp [eq, Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply, Pi.single_apply]

end GlobalTheory.TopForm.FrameBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergence
section
noncomputable section

namespace GlobalTheory.ArcQZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasSum_evR_of_chart_natural (hL : GlobalTheory.Reg.EvLaws Xo c) (σ : c.F →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (hK : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    {v : ℂ} (hv : v ≠ 0) {R : Type} [CommRing R] [Algebra c.F R] (φ : R →ₐ[c.F] ℂ⸨X⸩) (ψ : R →ₐ[c.F] CAt σ)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩)
    (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ)
    {y₀ : FrPt Xo c R} {y₁ y : FrPt Xo c ℂ⸨X⸩} {yw₁ yw : FrPt Xo c (CAt σ)}
    (h₁ : FrMap φ y₀ y₁) (hy : FrChg G s y₁ y) (hw₁ : FrMap ψ y₀ yw₁) (hyw : FrChg Gw sw yw₁ yw)
    (hφ : ∀ f, HasSum (fun n : ℤ => (φ f).coeff n * v ^ n) (toC (ψ f)))
    (hG : ∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * v ^ n) (toC (Gw τ i k)))
    (hs : HasSum (fun n : ℤ => s.coeff n * v ^ n) (toC sw))
    (hG' : ∀ τ, Summable fun n : ℤ => ((G τ).det⁻¹).coeff n * v ^ n)
    (hs' : Summable fun n : ℤ => (s⁻¹).coeff n * v ^ n) (F : Rul Xo c)
    (hF : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F) :
    HasSum (fun m : ℤ => (evR Xo c F y).coeff m * v ^ m) (toC (evR Xo c F yw)) := by
  let A := ptRing σ hK hv
  let φA : R →ₐ[c.F] A := φ.codRestrict A fun f => (hφ f).summable
  let GA : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A :=
    fun τ i k => ⟨G τ i k, (hG τ i k).summable⟩
  let sA : A := ⟨s, hs.summable⟩
  obtain ⟨hu1, hu2⟩ := (frChg_exists_unique_units E H Dw l Xo c _ G s y₁).2.2.1 y hy
  have hdet : ∀ τ, ((GA τ).det : ℂ⸨X⸩) = (G τ).det := fun τ => A.val.map_det (GA τ)
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ φA y₀
  obtain ⟨u, hu⟩ := (frChg_exists_unique_units E H Dw l Xo c A GA sA u₁).1
    (fun τ => isUnit_ptRing σ hK hv _ (by rw [hdet]; exact (hu1 τ).ne_zero) (by rw [hdet]; exact hG' τ))
    (isUnit_ptRing σ hK hv sA hu2.ne_zero hs')
  have e₁ : FrMap A.val u y := frMap_of_frChg_map φA A.val GA sA hu₁ hu h₁ hy
  have eψ : (ptEv σ hK hv).comp φA = ψ := AlgHom.ext fun f => ptEv_eq σ hK hv _ (hφ f)
  have eG : (fun τ => (GA τ).map (ptEv σ hK hv)) = Gw := by
    funext τ
    ext i k
    exact ptEv_eq σ hK hv _ (hG τ i k)
  have es : ptEv σ hK hv sA = sw := ptEv_eq σ hK hv _ hs
  have e₂ : FrMap (ptEv σ hK hv) u yw :=
    frMap_of_frChg_map φA (ptEv σ hK hv) GA sA hu₁ hu (by rw [eψ]; exact hw₁) (by rw [eG, es]; exact hyw)
  rw [GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₁, GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₂]
  exact hasSum_ptEv σ hK hv _

theorem hasSum_evR_arc_natural : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ F : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) := by
  intro hL1 hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ z hL hK hχ hβ hP hth hy hz
  obtain ⟨pt, -, -, -, -, hpt1, hpt2, -⟩ := id hy
  have hpt3 : pt ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ⸨X⸩) := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.jQ_over, Category.assoc, ← pullback.condition,
      ← Category.assoc Y.jQ, ← Category.assoc]
    show (pt ≫ Y.j) ≫ Y.s = _
    rw [hpt1, Category.assoc, hχ]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (hK (β x)).symm
  obtain ⟨p, j, y₀, hch, hmem⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hL1.secBaseChange E H Dw l Xo c (pt (IsLocalRing.closedPoint ℂ⸨X⸩))
  haveI := hch.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.ArcQ.exists_algHom_of_mem_range j hch.2.2 pt hpt3 hmem
  obtain ⟨y₁, hy₁⟩ := hL.bc _ _ φ y₀
  obtain ⟨G, s, hGs⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 y₁).2.2.2 y
    (by rw [hy₁.1, ← hch.2.1, ← Category.assoc, hφ, hpt2])
  obtain ⟨T₁, h₁⟩ := GlobalTheory.T.holArc_chart_coordinates_hasSum E H Dw l Xo c σ O β Y a χ W g ty Fu Ha p j φ hK hχ hβ hch.1 hch.2.2
    (by rw [← Category.assoc, hφ, hpt1])
  obtain ⟨T₂, h₂⟩ := GlobalTheory.T.frame_matrix_hasSum_alt hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th z p j y₀ φ y₁ G s
    hK hχ hβ hy hz hch hy₁ hGs
  obtain ⟨T₃, h₃⟩ := GlobalTheory.T.hasSum_thetaGenerator_chart_ratio hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th Θ p j y₀ φ y₁ G s
    hK hχ hβ hP hth hy hch hy₁ hGs
  have key : ∀ w : ℂ, max T₁ (max T₂ T₃) < w.im → ∀ yw, AnFr Ha Θ z w yw →
      ∃ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ : FrPt Xo c (CAt σ))
        (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ),
        FrMap ψ y₀ yw₁ ∧ FrChg Gw sw yw₁ yw ∧
        (∀ f, HasSum (fun n : ℤ => (φ f).coeff n * eTwoPi w ^ n) (toC (ψ f))) ∧
        (∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * eTwoPi w ^ n) (toC (Gw τ i k))) ∧
        HasSum (fun n : ℤ => s.coeff n * eTwoPi w ^ n) (toC sw) := by
    intro w hw yw hyw
    rw [max_lt_iff, max_lt_iff] at hw
    obtain ⟨ψ, hψ1, hψ2⟩ := h₁ w hw.1
    obtain ⟨yw₁, hyw₁⟩ := hL.bc _ _ ψ y₀
    obtain ⟨Gw, sw, hw'⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 yw₁).2.2.2 yw
      (by rw [hyw₁.1, ← hch.2.1, hψ1]; exact hyw.1.1)
    exact ⟨ψ, yw₁, Gw, sw, hyw₁, hw', hψ2, h₂ w hw.2.1 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1 hw',
      h₃ w hw.2.2 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1.1 hyw.2 hw'⟩
  by_cases hex : ∃ w : ℂ, max T₁ (max T₂ T₃) < w.im ∧ ∃ yw, AnFr Ha Θ z w yw
  · obtain ⟨w₀, hw₀, yw₀, hyw₀⟩ := hex
    obtain ⟨-, -, Gw₀, sw₀, -, -, -, hG₀, hs₀⟩ := key w₀ hw₀ yw₀ hyw₀
    have hv₀ := GlobalTheory.Conv.eTwoPi_ne_zero w₀
    have cs : s⁻¹ ∈ GlobalTheory.Conv.convLaurent :=
      inv_mem (GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ hs₀.summable)
    have cG : ∀ τ, (G τ).det⁻¹ ∈ GlobalTheory.Conv.convLaurent := fun τ => by
      refine inv_mem ?_
      rw [Matrix.det_apply']
      exact sum_mem fun π _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ =>
        GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ (hG₀ τ _ _).summable)
    obtain ⟨T₄, h₄⟩ := GlobalTheory.Conv.exists_forall_mem_halfRing
      (S := insert s⁻¹ (Set.range fun τ => (G τ).det⁻¹)) ((Set.finite_range _).insert _)
      (by rintro _ (rfl | ⟨τ, rfl⟩); exacts [cs, cG τ])
    refine ⟨max T₄ (max T₁ (max T₂ T₃)), fun w hw yw hyw F hF => ?_⟩
    rw [max_lt_iff] at hw
    obtain ⟨ψ, yw₁, Gw, sw, k₁, k₂, k₃, k₄, k₅⟩ := key w hw.2 yw hyw
    exact hasSum_evR_of_chart_natural hL σ hK (GlobalTheory.Conv.eTwoPi_ne_zero w) φ ψ G s Gw sw hy₁ hGs k₁ k₂ k₃ k₄ k₅
      (fun τ => h₄ _ (Or.inr ⟨τ, rfl⟩) w hw.1) (h₄ _ (Or.inl rfl) w hw.1) F hF
  · exact ⟨_, fun w hw yw hyw => absurd ⟨w, hw, yw, hyw⟩ hex⟩

end GlobalTheory.ArcQZ

namespace GlobalTheory.CuspFrom

section SecZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem evR_frChg_one_secZ {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {ex : Ix Dw → ℤ}
    (hex : ex none = 0) {F : Rul Xo c} (hF : F ∈ GlobalTheory.AllWt.secZ Xo c ex) {s : S} {y y' : FrPt Xo c S}
    (h : FrChg (fun _ => 1) s y y') : evR Xo c F y' = evR Xo c F y := by
  obtain ⟨u, rfl⟩ := ((GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [GlobalTheory.FlagTan.evR_frBor hF hb]
  simp [t, Fintype.prod_option, hex]

theorem exists_arc_secZ' [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) :
    ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ),
      BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im →
        (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex,
          HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m)
            (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  letI := FractionRing.liftAlgebra ℂ ℂ
  haveI := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hK := GlobalTheory.ArcCM.known_holds
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨aC, htie⟩ := GlobalTheory.CuspFrom.exists_input Uw hσ hU hξ hx
  obtain ⟨Wp, Y, h4, hpush⟩ := GlobalTheory.CuspFrom.exists_model Xo c (by omega)
  have hmono := mono_spMap_subtype (c.V Wp)
  obtain ⟨χ, hχ, -⟩ := h4 ℂ _ 1 (aC.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField ℂ, rfl⟩)
  obtain ⟨hover, hab, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 hW
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ Y σ _ χ W Uw.g _ Uw.F hσ hty (GlobalTheory.ArcInTest.exists_values c Wp) hover
    (fun q hq => hj q (by simpa using hq))
  obtain ⟨T, s, d, z, hd, hz, hflow⟩ := htie _ _ Y χ W Ha
  obtain ⟨-, v₂, -, -⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c _ _ _ Y _ _ W _ _ Uw.F Ha
  choose e he using fun τ i => (v₂ (z τ i)).exists
  have hB := GlobalTheory.T.constant_vectors_lieBasis_of_complex_arc E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha e z hσ hz he
  obtain ⟨-, -, th, hth⟩ := GlobalTheory.ThetaOverField.nonzero_generates h1 h2 ℂ (aC.restrict (c.V Wp).subtype).D₀
    DVR.SecOps.secZero
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha hty th hth
  have hc : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ≫ Y.s = spMap (algebraMap c.F ℂ⸨X⸩) ≫ spMap (c.V Wp).subtype := by
    rw [Category.assoc, hover, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp]
    congr 1
    exact RingHom.ext fun t => (halg _).symm
  haveI := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ hc : Sp ℂ⸨X⸩ ⟶ gen Y) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hq
    have h0 : HahnSeries.ofPowerSeries ℤ ℂ PowerSeries.X ∈ q.asIdeal := hq
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal q.isPrime, Ideal.mem_bot] at h0
    exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm))
  let z₀ := IsOpenImmersion.lift Y.jQ _ hr
  have hz₀ : z₀ ≫ Y.jQ = _ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨y, -, hy⟩ := GlobalTheory.ArcQ.exists_isArcFr h1 h2 E H Dw l Xo c _ _ Y ℂ _ _ χ W _ e th hB hth (Or.inr hpush) ℂ⸨X⸩
    (HahnSeries.ofPowerSeries ℤ ℂ) z₀ (by unfold RingHom.Flat; infer_instance)
    (by rw [Model.j, ← Category.assoc, hz₀, pullback.lift_fst])
    (by
      rw [pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hz₀, pullback.lift_snd,
        GlobalTheory.ArcId.sp_comp]
      rfl)
    (fun τ t => halg _)
  have hbd := GlobalTheory.T.arc_framed_point_extends_to_model_boundary E H Dw l Xo c σ _ _ Y _ χ W e th y halg hover hmono hB hy (fun h =>
    (hab _).1 h (by
      change _ ∈ IsLocalRing.maximalIdeal _
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.mem_span_singleton_self _))
  obtain ⟨T', hT'⟩ := GlobalTheory.ArcQZ.hasSum_evR_arc_natural h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha y e th Θ z hev halg hover
    hmono hpush hth hy he
  refine ⟨y, max T (max T' Ha.T), s, d, GlobalTheory.T.boundaryExtension_independent_of_model E H Dw l Xo c _ _ Z _ _ Y _ _ _ y
    (RingHom.ext fun t => (halg t).symm) hbd, hd, fun w hw => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨hxw, hlie⟩ := hflow w hw.1
  refine ⟨hxw, fun ex hex0 F hF => ?_⟩
  obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr h1 h2 E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha th Θ z hσ hz w
    hw.2.2
  obtain ⟨t, ht⟩ := GlobalTheory.ArcCoeff.frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw.2.2) _ _ z hlie hyw.1
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have e1 := evR_frChg_one_secZ hex0 hF ht
  have := hT' w hw.2.1 yw hyw F hF.1
  rw [e1] at this
  convert this using 1
  exact dif_pos hxw

end SecZ

end GlobalTheory.CuspFrom

section Final

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_arc_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ halg hσ hU k ξ' hξ x hx O _ β Z
  exact GlobalTheory.CuspFrom.exists_arc_secZ' halg hσ hU hξ hx Z

end Final
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemesStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π →
    ∀ (g g' : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (i' : A₀.left ⟶ A'.left) (j' : B₀.left ⟶ B'.left),
    IsGrpPullback A₀ A' (spMap π) i' → IsGrpPullback B₀ B' (spMap π) j' → IsAbelianScheme A' → IsAbelianScheme B' →
    SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g' B'.hom →
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j B₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
    ∀ (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ schemeFil (divided₂ hI) A₀ X i h.w, push (divided₂ hI) (spMap π) f₀ d ∈ schemeFil (divided₂ hI) B₀ Y j k.w) →
    ∃ φ : X ⊗ Y ⟶ Y, l ≫ φ.left = ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀).left ≫ j := by
  first | exact @GlobalTheory.ShearLift.exists_lift_shear | exact GlobalTheory.ShearLift.exists_lift_shear | (intros; apply GlobalTheory.ShearLift.exists_lift_shear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecValLin
open GlobalTheory.SecJet.Orders

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valR x U (f + g) = valR x U f + valR x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, valR_eq x U h, map_add]
  · simp only [valR, dif_neg h, add_zero]

theorem valR_scal_mul {R A : Type} [CommRing R] [CommRing A] {X : Scheme.{0}} (ψ : R →+* A) (p : X ⟶ Sp R)
    (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ) (U : X.Opens) (c : R) (f : Γ(X, U)) :
    valR x U (resTop U (scal p c) * f) = ψ c * valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, map_mul]
    have e : resTop U (scal p c) = Geo.Tor.constFn p U c := rfl
    rw [e, vh_const ψ p x hx U h c]
  · simp only [valR, dif_neg h, mul_zero]

theorem exists_linear_valR_sec : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  intro K _ x N i B _ _ y hy
  refine ⟨⟨⟨fun s => valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i),
    fun s t => valR_add' y _ _ _⟩, fun c s => ?_⟩, fun s => rfl⟩
  show valR y _ (resTop _ (scal _ c) * s.sec.f i) = _
  rw [valR_scal_mul (algebraMap K B) _ y hy, RingHom.id_apply, Algebra.smul_def]

end GlobalTheory.SecValLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasisStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logKS_symPair_basis_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (φU : c.F →+* Γ(TF.Y.X, U.1)), (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) → (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') → (∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v (Pi.single (e ⟨τ, i⟩) (φU (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)) → ∃ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), ∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j)) := by
  first | exact @GlobalTheory.LogKSDiv.exists_logKS_symPair_basis | exact GlobalTheory.LogKSDiv.exists_logKS_symPair_basis | (intros; apply GlobalTheory.LogKSDiv.exists_logKS_symPair_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatioStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_genDer_extend | exact GlobalTheory.LogKSDiv.exists_genDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_genDer_extend <;> assumption)
end


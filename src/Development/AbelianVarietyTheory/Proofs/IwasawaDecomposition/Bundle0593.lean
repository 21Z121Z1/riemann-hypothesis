import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRdUFlat
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrueCx.FlatConst

section Hol

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_generic_units (hpq : 1 ≤ Dw.p + Dw.q) (h : GenFrEx Xo c) :
    ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ u : (C.R)ˣ, ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  obtain ⟨κ, h₁, h₂, -, -, -, h₃, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => exists_tied E H Dw l Xo c _ e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := exists_tied E H Dw l Xo c _ e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := exists_tied E H Dw l Xo c _ e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨u, ?_⟩
  rw [← rule_frBor κ h₁ h₂ E H Dw l Xo c _ e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (tied_keyPB E H Dw l Xo c _ e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem exists_key_four (hpq : 1 ≤ Dw.p + Dw.q) (σ : c.F →+* ℂ) :
    ∃ ρ ∈ secZ Xo c (fun i => keyEx Dw i * 4), ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c ρ y) ≠ 0 := by
  obtain ⟨-, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_generic_units hpq h
  have hk : ∀ C : FChart h, (∏ i, C.t i ^ (keyEx Dw i * 4) : (Om C.Z)ˣ) = kch C.t ^ 4 := fun C => by
    rw [kch, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_mul]; rfl
  obtain ⟨ρ, hρ, hρv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (fun i => keyEx Dw i * 4)
    (fun Z => v Z) fun C => by
      obtain ⟨u, hu⟩ := hv C
      rw [hk, ← Units.val_mul, ← hu]
      exact u.1.2
  refine ⟨ρ, hρ, fun y => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  obtain ⟨u, hu⟩ := hv C
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.DegCmp.fChart_exists_val C hρ
  have hbu : b = u := Subtype.ext (by
    rw [hb₁, hu, hk, GlobalTheory.CompHt.genVal_apply h, hρv, Units.val_mul])
  show evR Xo c ρ y ≠ 0
  rw [GlobalTheory.FlagTan.evR_frBor hρ hb, hb₂ _ ψ z hz, hbu]
  exact mul_ne_zero (Units.ne_zero _) (u.isUnit.map ψ).ne_zero

theorem exists_sec_four (hpq : 1 ≤ Dw.p + Dw.q) {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) :
    ∃ n, Even n ∧ ∃ g ∈ sec Xo c (fun _ => 4) n, toC (evR Xo c g y) ≠ 0 := by
  obtain ⟨ρ, hρ, h0⟩ := exists_key_four (Xo := Xo) hpq σ
  obtain ⟨n, hn, ⟨m, rfl⟩, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ y
  rw [← secZ_nat] at hη
  have h2 := mul_mem_secZ hη hη
  have h3 := mul_mem_secZ (mul_mem_secZ h2 h2) hρ
  refine ⟨2 * (4 * m - 4), even_two_mul _, η * η * (η * η) * ρ, ?_, ?_⟩
  · rw [← secZ_nat]
    convert h3 using 2
    funext i
    cases i with
    | none => simp only [ex, keyEx, Pi.add_apply]; omega
    | some i => simp [ex, keyEx]
  · have h1 : toC (evR Xo c η y) ≠ 0 := hη0
    simp only [CompSplitPfB.cspB_evR_mul]
    exact mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) h1 h1) (mul_ne_zero (M₀ := ℂ) h1 h1)) (h0 y)

open Classical in

def flatFour (τ : Psi H) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => if x.1 = τ.1 then 3 else if x.1 = conjEmb τ.1 then 5 else 4

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

end Hol

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end Main

end GlobalTheory.TrueCx.FlatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.ChartValue

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem exists_evR_eq_of_tri {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, ∀ (K : Type) [CommRing K] [IsLocalRing K] [Algebra c.F K] (ψ : R →ₐ[c.F] K)
      (v0 : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (y0 : FrPt Xo c K),
      (∀ τ i, ∃ cf : Fin (Dw.mult τ) → K, cf i = t τ i ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Z.t (spMap ψ.toRingHom ≫ x) (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) cf (v0 τ i)) →
      GlobalTheory.AllWt.ptF y0 = spMap ψ.toRingHom ≫ xF →
      (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
        w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
          w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = v0 τ i) →
      evR Xo c g y0 = ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ψ a := by
  obtain ⟨y, w, hyx, hw⟩ := exists_frPt_of_eigFrame xF hs hx f
  refine ⟨evR Xo c g y, fun K _ _ _ ψ v0 t y0 hT hy hu => ?_⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap ψ y
  have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = y0.x := pullback.lift_fst _ _ _
  have h1 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = z.x := by rw [hz.1, hyx, hy, Category.assoc]
  have h2 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ ≫ pullback.fst _ _ = spMap ψ.toRingHom ≫ x := by rw [hy, ← hx, Category.assoc]
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c K z y0).1 (h0.symm.trans h1)
  choose cf hcf1 hcf2 hcf3 using hT
  have hcomb : ∀ τ i, IsCombAt z.x (z.u τ) (cf τ i) (y0.u τ i) := fun τ i => by
    obtain ⟨w0, a1, a2, a3⟩ := hu τ i
    have hv : ∀ k, (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.oF.t.G.hom =
        spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 := fun k => by
      rw [Category.assoc, (hw τ k).1, hy, ← Category.assoc, ← Category.assoc, OpenReg.spMap_comp, OpenReg.spMap_comp,
        GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]
    have e1 : z.u τ = fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m0.toSABMap.φ := funext fun k => by
      rw [hz.2.1, Category.assoc, (hw τ k).2.1]
    have e2 : (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) =
        fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m.φ := funext fun k => by
      rw [Category.assoc, (hw τ k).2.2]
    have b := hcf3 τ i
    rw [e2, ← a3] at b
    rw [e1, ← a2]
    exact (comb_iff Z.m0.toSABMap h1 hv _ a1).2 ((comb_iff Z.m h2 hv _ a1).1 b)
  let T : Ix Dw → Kˣ := fun k => k.elim a fun k => t k.1 k.2
  have hb : FrBor T z y0 := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).2.2.2 T z y0).2
    ⟨fun τ => Matrix.of (cf τ), fun τ i => hcf1 τ i, fun τ i j hij => hcf2 τ i j hij, hc.1, hcomb, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, GlobalTheory.FlagTan.evR_frMap hg.1 hz, Fintype.prod_option, hex, zpow_zero,
    _root_.one_mul]
  rfl

theorem exists_value_local {A R K L : Type} [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [CommRing L] [IsLocalRing L]
    [Algebra c.F K] [Algebra c.F L] (j : A →+* R) (ι : R →+* K) (hι : Function.Injective ι) (ψ : R →+* L) [IsLocalHom ψ]
    (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) {x' : Sp K ⟶ Z.X}
    (f0 : EigFrame Z (algebraMap c.F K) x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (hT : fr.Tri (ι.comp j) f0 t)
    (y0 : FrPt Xo c K) (hy0 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ = spMap (ι.comp j) ≫ x)
    (hu0 : ∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
        w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i)
    (hσ : (ψ.comp j).comp φ = algebraMap c.F L) (y : FrPt Xo c L)
    (hy : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (ψ.comp j) ≫ x)
    (hu : ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ GlobalTheory.AllWt.ptF y ∧
        w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (ψ.comp j)) ≫ fr.v τ i)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, evR Xo c g y0 = ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ι a ∧
      evR Xo c g y = ψ a := by
  letI : Algebra c.F R := (j.comp φ).toAlgebra
  haveI := Z.jQ_open
  obtain ⟨f, hf⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A R φ _ fr j
  let ι' : R →ₐ[c.F] K := { ι with commutes' := fun r => (RingHom.congr_fun hT.2.1 r).symm }
  let ψ' : R →ₐ[c.F] L := { ψ with commutes' := fun r => RingHom.congr_fun hσ r }
  have hr : Set.range (spMap j ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have h1 : p ⤳ spMap ψ (IsLocalRing.closedPoint L) := by
      have : spMap ψ (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint ψ
      rw [this]
      exact IsLocalRing.specializes_closedPoint p
    refine (h1.map (spMap j ≫ x).continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
      ⟨GlobalTheory.AllWt.ptF y (IsLocalRing.closedPoint L), ?_⟩
    have h2 : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap ψ ≫ spMap j ≫ x := by rw [hy, ← Category.assoc, OpenReg.spMap_comp]
    exact congrArg (fun m : Sp L ⟶ gen Z => m (IsLocalRing.closedPoint L)) h2
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap j ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF y0 = spMap ι ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, OpenReg.spMap_comp, hy0]
  have hpt : GlobalTheory.AllWt.ptF y = spMap ψ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, OpenReg.spMap_comp, hy]
  have hs : xF ≫ pullback.snd _ _ = spMap (j.comp φ) := by
    obtain ⟨φ₁, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have h1 : spMap ι ≫ spMap φ₁.hom = spMap (algebraMap c.F K) := by
      have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [OpenReg.spMap_comp] at h1
    have h2 : ι.comp φ₁.hom = algebraMap c.F K := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : φ₁.hom = j.comp φ := RingHom.ext fun r =>
      hι ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))
    rw [← h, ← h3]
    rfl
  obtain ⟨a, ha⟩ := exists_evR_eq_of_tri xF hs (by rw [← Category.assoc, hxF, Category.assoc]) f hex hg
  have e0 : ∀ {M : Type} [CommRing M] (χ : R →+* M) (τ : E →+* ℂ),
      (fun k => spMap (dualMap χ) ≫ f.v τ k) = fun k => spMap (dualMap (χ.comp j)) ≫ fr.v τ k := fun χ τ =>
    funext fun k => by rw [hf, ← Category.assoc, OpenReg.spMap_comp, dualMap_comp']
  refine ⟨a, ha K ι' f0.v t y0 (fun τ i => ?_) hpt0 hu0, ?_⟩
  · obtain ⟨cf, h1, h2, h3⟩ := hT.2.2 τ i
    refine ⟨cf, h1, h2, ?_⟩
    have e1 : x' = spMap ι ≫ spMap j ≫ x ≫ genι Z := by rw [hT.1, ← Category.assoc (spMap ι), OpenReg.spMap_comp]
    subst e1
    rw [← e0 ι τ] at h3
    exact h3
  · have := ha L ψ' (fun τ i => spMap (dualMap (ψ.comp j)) ≫ fr.v τ i) 1 y (fun τ i => ?_) hpt hu
    · exact this.trans (by simp; rfl)
    · refine ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩
      obtain ⟨f', hf'⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R L _ _ f ψ
      have h := isCombAtG_single Z.t _ (fun k => hf' τ k ▸ f'.tan τ k) i
      rw [← congrFun (e0 ψ τ) i]
      exact h

theorem value_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (ex : Ix Dw → ℤ) (g : Rul Xo c) (σ : c.F →+* ℂ) (ψ : Γ(C.Y.X, U) →+* ℂ) (y : FrPt Xo c (CAt σ)) (a b : Γ(C.Y.X, U)), fr.Tri (fnOf U hg) C.f0 t → ex none = 0 → g ∈ GlobalTheory.AllWt.secZ Xo c ex → ψ.comp φ = σ → Matches fr ψ y → fnOf U hg a = C.val g * ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : C.Y.Fnˣ)⁻¹ : C.Y.Fnˣ) * fnOf U hg b → ψ a = toC (evR Xo c g y) * ψ b := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C U hU hg φ fr t ex g σ ψ y a b hT hex hsec hσ hM hab
  letI := (constF e C.Y).toAlgebra
  have hinj : Function.Injective (fnOf U hg) := fnOf_injective U hg
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime (RingHom.ker ψ)
  have u1 : ∀ s : (RingHom.ker ψ).primeCompl, IsUnit (fnOf U hg s) := fun s =>
    IsUnit.mk0 _ fun h => s.2 (by rw [(injective_iff_map_eq_zero _).1 hinj _ h]; exact zero_mem _)
  let ψ₀ : Γ(C.Y.X, U) →+* CAt σ := ψ
  have u2 : ∀ s : (RingHom.ker ψ).primeCompl, IsUnit (ψ₀ s) := fun s => IsUnit.mk0 (G₀ := ℂ) _ s.2
  let ι : R →+* C.Y.Fn := IsLocalization.lift u1
  let χ : R →+* CAt σ := IsLocalization.lift u2
  have e1 : ι.comp (algebraMap _ R) = fnOf U hg := IsLocalization.lift_comp u1
  have e2 : χ.comp (algebraMap _ R) = ψ₀ := IsLocalization.lift_comp u2
  haveI : IsDomain Γ(C.Y.X, U) := hinj.isDomain _
  have hι : Function.Injective ι := (IsLocalization.lift_injective_iff u1).2 fun p q =>
    (IsLocalization.injective R (RingHom.ker ψ).primeCompl_le_nonZeroDivisors).eq_iff.trans hinj.eq_iff.symm
  haveI : IsLocalHom χ := ⟨fun r hr => by
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (RingHom.ker ψ).primeCompl r
    have h1 : χ r * ψ₀ s = ψ₀ p := by
      rw [← e2]; simpa using congrArg χ h
    have h2 : p ∈ (RingHom.ker ψ).primeCompl := IsUnit.ne_zero (M₀ := ℂ) (show IsUnit (ψ₀ p) from h1 ▸ hr.mul (u2 s))
    have h3 := IsLocalization.map_units R (⟨p, h2⟩ : (RingHom.ker ψ).primeCompl)
    exact isUnit_of_mul_isUnit_left (h ▸ h3)⟩
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hgen : genericPt C.Y = spMap (fnOf U hg) ≫ (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) :=
    (hU.fromSpecStalk_eq_fromSpecStalk hg).symm
  obtain ⟨a₀, h1, h2⟩ := exists_value_local (algebraMap _ R) ι hι χ φ _ fr C.f0 t (e1 ▸ hT) C.y0
    (by rw [e1, ← Category.assoc, ← hgen]; exact C.y0_x) C.flagComponentFramedPoint_frame (by rw [e2]; exact hσ) y
    (by rw [e2]; exact hM.1) (by rw [e2]; exact hM.2) hex hsec
  have h3 : algebraMap _ R a = a₀ * algebraMap _ R b := hι (by
    rw [map_mul]
    refine (RingHom.congr_fun e1 a).trans (hab.trans ?_)
    rw [show ι (algebraMap _ R b) = fnOf U hg b from RingHom.congr_fun e1 b, show C.val g = _ from h1,
      mul_right_comm _ (ι a₀), Units.mul_inv, _root_.one_mul])
  have h4 := congrArg χ h3
  rw [map_mul, ← h2] at h4
  exact (RingHom.congr_fun e2 a).symm.trans (h4.trans (congrArg (evR Xo c g y * ·) (RingHom.congr_fun e2 b)))

end GlobalTheory.ShFam.ChartValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbRtSq
section
open NumberField

namespace GlobalTheory.ConjugateMultiplicity

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by

  have hsq := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have hprod : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
    have him0 : H.rt0.im = 0 := (mul_eq_zero.1 hprod).resolve_left hne
    rw [him0] at hre
    nlinarith [sq_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
  have h : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h' := congrArg ((↑) : 𝓞 E → E) H.rt_sq
    push_cast at h'
    exact h'
  rw [← map_pow, h, map_neg, map_natCast, H.sqrt_neg_disc_sq]

private theorem mult_conjEmb_eq_ite {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) = if τ (H.rt : E) = H.rt0 then Datum.q D else Datum.p D := by

  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have hsq := H.sqrt_neg_disc_sq
    rw [h0] at hsq
    have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact hd (by linear_combination hsq)
  have hc : conjEmb τ (H.rt : E) = starRingEnd ℂ (τ (H.rt : E)) := rfl
  unfold Datum.mult

  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (emb_rt_sq H τ) with h | h
  · have h2 : ¬ conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, rt0_conj_neg_ne_zero]
      exact fun e => hne e.symm
    rw [if_pos h, if_neg h2]
  · have h2 : conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have h3 : ¬ τ (H.rt : E) = H.rt0 := by
      rw [h]
      exact fun e => hne e.symm
    rw [if_pos h2, if_neg h3]

theorem main {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) + Datum.mult D τ = Datum.p D + Datum.q D := by
  rw [mult_conjEmb_eq_ite]
  unfold Datum.mult
  split_ifs <;> omega

end GlobalTheory.ConjugateMultiplicity

theorem GlobalTheory.ConjugateMultiplicity.target : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (τ : E →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.p D + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.q D := by
  intro E _ _ _ H D τ
  rw [GlobalTheory.ConjugateMultiplicity.mult_conjEmb_eq_ite]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
  split_ifs <;> omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycle
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem exists_finset_basicOpen_le {X : Scheme.{0}} (C : Coc X) {R : Type} [CommRing R] (χ : Sp R ⟶ X) :
    ∃ s : Finset R, (∀ g ∈ s, ∃ α, ∀ x : PrimeSpectrum R, g ∉ x.asIdeal → χ x ∈ C.B α) ∧
      ∀ x : PrimeSpectrum R, ∃ g ∈ s, g ∉ x.asIdeal := by
  classical
  have h : ∀ x : PrimeSpectrum R, ∃ g : R, g ∉ x.asIdeal ∧ ∃ α, ∀ y : PrimeSpectrum R, g ∉ y.asIdeal → χ y ∈ C.B α := by
    intro x
    obtain ⟨α, hα⟩ := C.cover (χ x)
    obtain ⟨_, ⟨g, rfl⟩, hx, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := x) (u := ((χ ⁻¹ᵁ C.B α : (Sp R).Opens) : Set (Sp R))) hα (χ ⁻¹ᵁ C.B α).2
    exact ⟨g, hx, α, fun y hy => hsub hy⟩
  choose g hg hα using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum R => (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hg x⟩)
  refine ⟨t.image g, fun a ha => ?_, fun x => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    exact hα x
  · obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨g y, Finset.mem_image_of_mem g hy, hx⟩

theorem isOpenImmersion_spMap_away {R : Type} [CommRing R] (g : R) :
    IsOpenImmersion (spMap (algebraMap R (Localization.Away g))) :=
  IsOpenImmersion.of_isLocalization g

theorem mem_range_spMap_away {R : Type} [CommRing R] (g : R) (x : PrimeSpectrum R) :
    x ∈ Set.range (spMap (algebraMap R (Localization.Away g))) ↔ g ∉ x.asIdeal :=
  Set.ext_iff.1 (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g) x

theorem Atlas.exists_refine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (C : Coc X), ∃ A' : Atlas M π ty, (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), A'.FlagAt w u ↔ A.FlagAt w u) ∧ ∃ α : A'.ch.ι → C.A, ∀ a, ⊤ ≤ A'.ch.χ a ⁻¹ᵁ C.B (α a) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A C
  choose s hs hcov using fun a => exists_finset_basicOpen_le C (A.ch.χ a)
  let P : PreAtlas M X :=
    { ch :=
        { ι := Σ a : A.ch.ι, {g // g ∈ s a}
          R := fun k => Localization.Away k.2.1
          χ := fun k => spMap (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) ≫ A.ch.χ k.1
          opn := fun k => by
            have := isOpenImmersion_spMap_away k.2.1
            infer_instance }
      alg := fun k => (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)).comp (A.alg k.1)
      fr := fun k => (A.fr k.1).bc (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) }
  have key : ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), P.FlagAt π ty w u ↔ A.FlagAt w u := by
    intro K _ w u
    constructor
    · rintro ⟨k, φ, e, hf, hS⟩
      refine ⟨k.1, φ.comp (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)), ?_, hf, ?_⟩
      · rw [← spMap_comp', Category.assoc]; exact e
      · rw [← Vecs.bc_bc]; exact hS
    · rintro ⟨a, φ, e, hf, hS⟩
      obtain ⟨g, hg, hφ⟩ := hcov a ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
      have hu : IsUnit (φ g) := IsUnit.mk0 _ hφ
      have hψ : (IsLocalization.Away.lift (S := Localization.Away g) g hu).comp (algebraMap _ _) = φ :=
        IsLocalization.Away.lift_comp g hu
      refine ⟨⟨a, g, hg⟩, IsLocalization.Away.lift (S := Localization.Away g) g hu, ?_, ?_, ?_⟩
      · show spMap _ ≫ spMap _ ≫ _ = _
        rw [← Category.assoc, spMap_comp', hψ, e]
      · show LocM.IsFrame M.t (RingHom.comp _ (RingHom.comp _ _)) _ _
        rw [← RingHom.comp_assoc, hψ]; exact hf
      · show SameFlag ty M.t _ (((A.fr a).bc _).bc _) _
        rw [Vecs.bc_bc, hψ]; exact hS
  refine ⟨{ toPreAtlas := P, cover := ?_, alg_s := fun k => ?_, smooth := fun k => ?_, frame := fun k => ?_,
            glue := fun K _ k k' φ φ' e => ?_, bij := fun K _ f y hy u hu => ?_ }, key, ?_⟩
  · rw [← A.cover]
    ext x
    simp only [Charts.carrier, Set.mem_iUnion]
    constructor
    · rintro ⟨k, y, rfl⟩
      exact ⟨k.1, spMap (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨a, y, rfl⟩
      obtain ⟨g, hg, hy⟩ := hcov a y
      obtain ⟨z, rfl⟩ := (mem_range_spMap_away g y).2 hy
      exact ⟨⟨a, g, hg⟩, z, Scheme.Hom.comp_apply _ _ _⟩
  · exact A.affineOpenChart_comp_structure_eq_spMap (a := k.1) rfl
  · have := isOpenImmersion_spMap_away k.2.1
    have := A.smooth k.1
    show Smooth ((spMap (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) ≫ A.ch.χ k.1) ≫ π)
    rw [Category.assoc]
    infer_instance
  · exact A.isFrame_bc (a := k.1) rfl
  · have e' : spMap φ ≫ spMap _ ≫ A.ch.χ k.1 = spMap φ' ≫ spMap _ ≫ A.ch.χ k'.1 := e
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp'] at e'
    have h := A.glue K k.1 k'.1 _ _ e'
    rw [← Vecs.bc_bc, ← Vecs.bc_bc, ← spMap_comp', Category.assoc] at h
    show SameFlag ty M.t (spMap φ ≫ (spMap _ ≫ A.ch.χ k.1) ≫ π) _ _
    rw [Category.assoc]
    exact h
  · exact (existsUnique_congr fun w => and_congr_right' (key K w u)).2 (A.bij K f y hy u hu)
  · choose α hα using fun k : P.ch.ι => hs k.1 k.2.1 k.2.2
    refine ⟨α, fun k z _ => ?_⟩
    have := hα k _ ((mem_range_spMap_away k.2.1 _).1 ⟨z, rfl⟩)
    rw [← Scheme.Hom.comp_apply] at this
    exact this

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegral
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

theorem exists_common_denominator (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩
  have hj := h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))
  rw [zsmul_eq_mul] at hj
  rcases Int.natAbs_eq y with e | e
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this]; exact hj
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this, neg_mul]; exact hj.neg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlagStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_graded_line_divisors_full_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  first | exact @GlobalTheory.ShFam.GradedDiv.exists_gr | exact GlobalTheory.ShFam.GradedDiv.exists_gr | (intros; apply GlobalTheory.ShFam.GradedDiv.exists_gr <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0832
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0830
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0828
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0806
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedAdd
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false
noncomputable section

open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CombInd.Tens

theorem commGroup_coboundary_relation_identity {G : Type} [CommGroup G] (a b x y z : G) : a * b * z⁻¹ = a * x⁻¹ * (b * y⁻¹) * (x * y * z⁻¹) := by
  rw [show a * x⁻¹ * (b * y⁻¹) * (x * y * z⁻¹) = a * b * z⁻¹ * (x⁻¹ * x) * (y⁻¹ * y) by ac_rfl]
  simp

theorem group_pow_mul_identity {G : Type} [CommGroup G] (x y z r₁ r₂ : G) (m : ℕ) :
    z⁻¹ ^ m * (r₁ * r₂) = x⁻¹ ^ m * r₁ * (y⁻¹ ^ m * r₂) * (x * y * z⁻¹) ^ m := by
  rw [mul_pow, mul_pow, show x⁻¹ ^ m * r₁ * (y⁻¹ ^ m * r₂) * (x ^ m * y ^ m * z⁻¹ ^ m) =
    z⁻¹ ^ m * (r₁ * r₂) * (x⁻¹ ^ m * x ^ m) * (y⁻¹ ^ m * y ^ m) by ac_rfl]
  simp

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem prod_expo_add (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (w₁ w₂ : Sym E →₀ ℤ) :
    (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (w₁ + w₂) x) =
      (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w₁ x) * ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w₂ x := by
  rw [LineTest.expo_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => zpow_add _ _ _

theorem unitAt_prod (w : Sym E →₀ ℤ) (b : Y.Y.X) :
    UnitAt b (((∏ x : Letter Dw, (Y.gr_spec b).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf Y (expo Dw w)) b)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
  have := (Base.isEqn_eqn (divOf Y (expo Dw w)) b).iff_unitAt.1 (LineTest.isEqn_divOf Y (expo Dw w) b)
  rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this

theorem lgOf_add (w₁ w₂ : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    lgOf Y (w₁ + w₂) v ε y = lgOf Y w₁ v ε y + lgOf Y w₂ v ε y +
      Real.log (ε.w (TrueGeo.valAt y.1 ((eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
        (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) := by
  classical
  have hp := LineTest.residueCharacteristic_prime v
  have U₁ := unitAt_prod Y w₁ (below y.1)
  have U₂ := unitAt_prod Y w₂ (below y.1)
  have hE : (divOf Y (expo Dw (w₁ + w₂))).IsEqn (below y.1)
      (eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1)) := by
    rw [LineTest.expo_add, LineTest.divOf_add]; exact (Base.isEqn_eqn _ _).add (Base.isEqn_eqn _ _)
  have Uc : UnitAt (below y.1) ((eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
      (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn _ _).iff_unitAt.1 hE
    rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  simp only [lgOf, dif_pos hp]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring), prod_expo_add Y _ w₁ w₂,
    commGroup_coboundary_relation_identity _ _ (eqn (divOf Y (expo Dw w₁)) (below y.1)) (eqn (divOf Y (expo Dw w₂)) (below y.1)) _]
  generalize (∏ x : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w₁ x) *
    (eqn (divOf Y (expo Dw w₁)) (below y.1))⁻¹ = u₁ at U₁ ⊢
  generalize (∏ x : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w₂ x) *
    (eqn (divOf Y (expo Dw w₂)) (below y.1))⁻¹ = u₂ at U₂ ⊢
  generalize eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
      (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ = c at Uc ⊢
  rw [Units.val_mul (u₁ * u₂) c, Units.val_mul u₁ u₂, SmallSec.valAt_mul (U₁.mul U₂).regAt Uc.regAt,
    SmallSec.valAt_mul U₁.regAt U₂.regAt, map_mul, map_mul,
    Real.log_mul (mul_ne_zero (ε.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (ε.w.pos (SmallSec.valAt_ne_zero U₂)).ne')
      (ε.w.pos (SmallSec.valAt_ne_zero Uc)).ne',
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (ε.w.pos (SmallSec.valAt_ne_zero U₂)).ne']
  ring

end Free

theorem a3field_of_a2indep_of_a3one {K : Type} [Field K] (f g₁ g₂ r₁ r₂ : K) (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) (m : ℕ) :
    f * (r₁ * r₂) = f * (g₁ * g₂) ^ m * (g₁⁻¹ ^ m * r₁) * (g₂⁻¹ ^ m * r₂) := by
  rw [mul_pow, inv_pow, inv_pow]
  field_simp

set_option maxHeartbeats 1000000 in

theorem induced_tens : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+) (R : ℝ) (w₁ w₂ : Sym D.host.E →₀ ℤ) (L₁ L₂ : GlobalTheory.HermLB M.p), (∀ a ∈ w₁.support, a.2.1 = some R) → (∀ a ∈ w₂.support, a.2.1 = some R) → (adlOf (Φ.C k) (metsOf x Φ k) w₁).Induced M L₁ m 0 → (adlOf (Φ.C k) (metsOf x Φ k) w₂).Induced M L₂ m 0 → (adlOf (Φ.C k) (metsOf x Φ k) (w₁ + w₂)).Induced M (L₁.tens L₂) m 0 := by
  intro D A N j S κ s x Φ k M m R w₁ w₂ L₁ L₂ hw₁ hw₂ h₁ h₂
  classical
  obtain ⟨-, r₁, hr₁, hinf₁, hv₁⟩ := h₁
  obtain ⟨-, r₂, hr₂, hinf₂, hv₂⟩ := h₂
  refine ⟨by simp, fun i => r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2), ?_, ?_, ?_⟩
  · dsimp only [adlOf] at hr₁ hr₂ ⊢
    rw [LineTest.expo_add, LineTest.divOf_add, nsmul_add]
    exact GlobalTheory.LineNorm.Add.presents_tens L₁.isLB L₂.isLB M.j hr₁ hr₂
  · intro σ y y' i f hy hi hf
    dsimp only [adlOf] at hinf₁ hinf₂ hf hr₁ hr₂ ⊢
    have hw : ∀ a ∈ (w₁ + w₂).support, a.2.1 = some R := fun a ha =>
      (Finset.mem_union.1 (Finsupp.support_add ha)).elim (hw₁ a) (hw₂ a)
    rw [metsOf_parOf x Φ k σ hw]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]
    have cA : under y ∈ (L₁.B.pull M.j).U (fun _ => (i PUnit.unit).1) :=
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hi PUnit.unit).1
    have cB : under y ∈ (L₂.B.pull M.j).U (fun _ => (i PUnit.unit).2) :=
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hi PUnit.unit).2
    obtain ⟨g₁, hg₁⟩ := (divOf (Φ.C k) (expo S.Dw w₁)).exists_isEqn (under y)
    obtain ⟨g₂, hg₂⟩ := (divOf (Φ.C k) (expo S.Dw w₂)).exists_isEqn (under y)
    have hG : (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))).IsEqn (under y) (g₁ * g₂) := by
      rw [LineTest.expo_add, LineTest.divOf_add]; exact hg₁.add hg₂
    have gen {Δ : (Φ.C k).Y.Dv} {g : (Φ.C k).Y.Fnˣ} (hg : Δ.IsEqn (under y) g) (p : ℕ) :
        (p • Δ).GeneratesAt (under y) (((g : (Φ.C k).Y.Fn))⁻¹ ^ p) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hg.nsmul p)
      rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
    have gen1 {Δ : (Φ.C k).Y.Dv} {g : (Φ.C k).Y.Fnˣ} (hg : Δ.IsEqn (under y) g) :
        Δ.GeneratesAt (under y) ((g : (Φ.C k).Y.Fn))⁻¹ := CartierDiv.isEqn_iff_generatesAt_inv.1 hg
    have e₁ := hinf₁ σ y y' _ _ hy cA (gen hg₁ m).regularAt
    have e₂ := hinf₂ σ y y' _ _ hy cB (gen hg₂ m).regularAt
    rw [metsOf_parOf x Φ k σ hw₁] at e₁
    rw [metsOf_parOf x Φ k σ hw₂] at e₂
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at e₁ e₂
    rw [(cxSt D.what₂.LL).pn_mPow _ σ _ _ _ _ y (gen1 hg₁)] at e₁
    rw [(cxSt D.what₂.LL).pn_mPow _ σ _ _ _ _ y (gen1 hg₂)] at e₂
    have u₁ := (hr₁.isEqn _ _ cA).generatesAt_iff.1 (gen hg₁ m)
    have u₂ := (hr₂.isEqn _ _ cB).generatesAt_iff.1 (gen hg₂ m)
    have ha : RegAt (under y) (f * ((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) ^ (m : ℕ)) := by
      have := (hG.nsmul _).regularAt_iff.1 hf
      rwa [Units.val_pow_eq_pow_val] at this
    have h₂ := (cxSt D.what₂.LL).pn_mul _ σ _ ((cxSt D.what₂.LL).mPow _ σ _ (m : ℕ)
      (metsOf x Φ k (some R) σ (expo S.Dw (w₁ + w₂)))) _ _ y ha (gen hG m).regularAt
    have hcanc : f * ((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) ^ (m : ℕ) *
        (((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))⁻¹ ^ (m : ℕ) = f := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (g₁ * g₂).ne_zero, one_pow, mul_one]
    rw [hcanc, (cxSt D.what₂.LL).pn_mPow _ σ _ _ _ _ y (gen1 hG)] at h₂
    have hsplit : (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (some R) σ (expo S.Dw (w₁ + w₂)))
        ((cxSt D.what₂.LL).cx _ σ (((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))⁻¹) y =
        (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (some R) σ (expo S.Dw w₁))
          ((cxSt D.what₂.LL).cx _ σ ((g₁ : (Φ.C k).Y.Fn))⁻¹) y *
        (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k (some R) σ (expo S.Dw w₂))
          ((cxSt D.what₂.LL).cx _ σ ((g₂ : (Φ.C k).Y.Fn))⁻¹) y := by
      rw [Units.val_mul, mul_inv, ← (cxSt D.what₂.LL).pn_mAdd _ σ _ _ _ _ _ _ y (gen1 hg₁).regularAt
        (gen1 hg₂).regularAt, LineTest.expo_add]
      exact congrFun (congrFun (pn_metsOf_add x Φ k (some R) σ _ _) _) y
    have hf' : f * ((r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2) : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) =
        f * ((g₁ * g₂ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) ^ (m : ℕ) *
          (((g₁ : (Φ.C k).Y.Fn))⁻¹ ^ (m : ℕ) * (r₁ (fun _ => (i PUnit.unit).1) : (Φ.C k).Y.Fn)) *
          (((g₂ : (Φ.C k).Y.Fn))⁻¹ ^ (m : ℕ) * (r₂ (fun _ => (i PUnit.unit).2) : (Φ.C k).Y.Fn)) := by
      simp only [Units.val_mul]
      exact a3field_of_a2indep_of_a3one _ _ _ _ _ g₁.ne_zero g₂.ne_zero _
    rw [h₂, hsplit, hf', ratVal_mul (ha.mul u₁.regAt) u₂.regAt, ratVal_mul ha u₁.regAt, mul_pow, e₁, e₂]
    change _ = _ * Real.exp (-((L₁.φ _).φ (i PUnit.unit).1 y' + (L₂.φ _).φ (i PUnit.unit).2 y'))
    rw [neg_add, Real.exp_add, norm_mul, norm_mul, mul_pow, mul_pow]
    ring
  · intro v e y yt i h hi
    dsimp only [adlOf] at hv₁ hv₂ hr₁ hr₂ ⊢
    have hi₁ : ⊤ ≤ yt ⁻¹ᵁ L₁.B.U (i PUnit.unit).1 := fun x hx => (hi hx).1
    have hi₂ : ⊤ ≤ yt ⁻¹ᵁ L₂.B.U (i PUnit.unit).2 := fun x hx => (hi hx).2
    have e₁ := hv₁ v e y yt (fun _ => (i PUnit.unit).1) h hi₁
    have e₂ := hv₂ v e y yt (fun _ => (i PUnit.unit).2) h hi₂
    have q₁ := GlobalTheory.LineNorm.Add.unitAt_quot (i := fun _ => (i PUnit.unit).1)
      (fun z => Base.isEqn_eqn (divOf (Φ.C k) (expo S.Dw w₁)) z) hr₁ h hi₁
    have q₂ := GlobalTheory.LineNorm.Add.unitAt_quot (i := fun _ => (i PUnit.unit).2)
      (fun z => Base.isEqn_eqn (divOf (Φ.C k) (expo S.Dw w₂)) z) hr₂ h hi₂
    have hE : (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))).IsEqn (below y.1)
        (eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1) * eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1)) := by
      rw [LineTest.expo_add, LineTest.divOf_add]; exact (Base.isEqn_eqn _ _).add (Base.isEqn_eqn _ _)
    have Uc : UnitAt (below y.1) ((eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1) *
        eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1) *
        (eqn (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) := by
      have := (Base.isEqn_eqn _ _).iff_unitAt.1 hE
      rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
    rw [lgOf_add, group_pow_mul_identity (eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1))
      (eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1))]
    simp only [Pi.zero_apply, mul_zero, sub_zero] at e₁ e₂ ⊢
    generalize (eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1))⁻¹ ^ (m : ℕ) * r₁ (fun _ => (i PUnit.unit).1) = u₁
      at q₁ e₁ ⊢
    generalize (eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1))⁻¹ ^ (m : ℕ) * r₂ (fun _ => (i PUnit.unit).2) = u₂
      at q₂ e₂ ⊢
    generalize eqn (divOf (Φ.C k) (expo S.Dw w₁)) (below y.1) * eqn (divOf (Φ.C k) (expo S.Dw w₂)) (below y.1) *
      (eqn (divOf (Φ.C k) (expo S.Dw (w₁ + w₂))) (below y.1))⁻¹ = c at Uc ⊢
    have w₁p := (e.w.pos (SmallSec.valAt_ne_zero q₁)).ne'
    have w₂p := (e.w.pos (SmallSec.valAt_ne_zero q₂)).ne'
    have wcp := (e.w.pos (SmallSec.valAt_ne_zero Uc)).ne'
    rw [Units.val_mul (u₁ * u₂) (c ^ (m : ℕ)), Units.val_mul u₁ u₂, Units.val_pow_eq_pow_val,
      SmallSec.valAt_mul (q₁.mul q₂).regAt (InducedPow.unitAt_pow Uc _).regAt,
      SmallSec.valAt_mul q₁.regAt q₂.regAt, SmallSec.valAt_pow Uc.regAt, map_mul, map_mul, map_pow,
      Real.log_mul (mul_ne_zero w₁p w₂p) (pow_ne_zero _ wcp), Real.log_mul w₁p w₂p, Real.log_pow]
    push_cast
    linear_combination e₁ + e₂

end GlobalTheory.CombInd.Tens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CombInd.DualComb

theorem inv_pow_mul_inv_eq {G : Type} [CommGroup G] (a b c : G) (m : ℕ) :
    b⁻¹ ^ m * c⁻¹ = (a⁻¹ ^ m * c * (a * b) ^ m)⁻¹ := by
  rw [mul_pow, inv_pow, inv_pow, mul_comm (a ^ m)⁻¹ c, mul_assoc, inv_mul_cancel_left, mul_inv_rev]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

variable (Dw) in

theorem expo_neg (w : Sym E →₀ ℤ) : expo Dw (-w) = -expo Dw w := by
  rw [eq_neg_iff_add_eq_zero, ← LineTest.expo_add, neg_add_cancel, LineTest.expo_zero]

theorem parOf_neg (w : Sym E →₀ ℤ) : parOf (-w) = parOf w := by
  simp only [parOf, Finsupp.support_neg]

theorem divOf_neg (n : Letter Dw → ℤ) : divOf Y (-n) = -divOf Y n := by
  simp only [divOf, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

variable {σ : F →+* ℂ} (G : EigMet Z (embOf e σ))

theorem met_neg_h (n : Letter Dw → ℤ) {p : Y.Y.pts σ} {g : Y.Y.Fnˣ} (hg : p ∈ Var.eqnSet σ (divOf Y n) g) :
    (Y.met G (-n)).h g⁻¹ p * (Y.met G n).h g p = 1 := by
  have h' : p ∈ Var.eqnSet σ (divOf Y (-n)) g⁻¹ := by
    show (divOf Y (-n)).IsEqn _ _
    rw [divOf_neg]
    exact CartierDiv.IsEqn.neg hg
  have h := FlagCpt.met_add_h G (-n) n h' hg
  rw [neg_add_cancel, inv_mul_cancel] at h
  rw [← h]
  simp [FlagCpt.met, FlagCpt.genSq, prodPow, Var.tv, Var.hasVal_one.val_eq]

theorem unitAt_eqn_mul (w : Sym E →₀ ℤ) (b : Y.Y.X) :
    UnitAt b ((eqn (divOf Y (expo Dw w)) b * eqn (divOf Y (expo Dw (-w))) b : Y.Y.Fnˣ) : Y.Y.Fn) := by
  have h0 : (divOf Y (expo Dw w) + divOf Y (expo Dw (-w))).IsEqn b
      (eqn (divOf Y (expo Dw w)) b * eqn (divOf Y (expo Dw (-w))) b) :=
    (Base.isEqn_eqn _ b).add (Base.isEqn_eqn _ b)
  rw [← LineTest.divOf_add, ← LineTest.expo_add, add_neg_cancel, LineTest.expo_zero] at h0
  have h00 : (0 : Y.Y.Dv).IsEqn b (eqn (divOf Y (expo Dw w)) b * eqn (divOf Y (expo Dw (-w))) b) := by
    simpa [divOf] using h0
  simpa using (CartierDiv.isEqn_zero b).iff_unitAt.1 h00

open Classical in

theorem lgOf_neg (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) :
    lgOf Y (-w) v ε y = -lgOf Y w v ε y - Real.log (ε.w (valAt y.1
      ((eqn (divOf Y (expo Dw w)) (below y.1) * eqn (divOf Y (expo Dw (-w))) (below y.1) : Y.Y.Fnˣ) : Y.Y.Fn))) := by
  have hp := LineTest.residueCharacteristic_prime v
  have key : ∀ K : Sym E → ℝ, ((-w).sum fun a n => (n : ℝ) * K a) = -(w.sum fun a n => (n : ℝ) * K a) := fun K => by
    rw [Finsupp.sum_neg_index (fun _ => by simp)]
    simp [Finsupp.sum, Finset.sum_neg_distrib]
  unfold lgOf
  rw [dif_pos hp, dif_pos hp]
  dsimp only
  rw [key]
  set b := below y.1 with hb
  set t := (Y.gr_spec b).choose_spec.choose_spec.choose with ht
  set P := ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x with hP
  have hP' : ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-w) x = P⁻¹ := by
    rw [expo_neg, hP]
    simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  set e1 := eqn (divOf Y (expo Dw w)) b with he1
  set e2 := eqn (divOf Y (expo Dw (-w))) b with he2
  have hu1 : UnitAt b ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn (divOf Y (expo Dw w)) b).iff_unitAt.1 (LineTest.isEqn_divOf Y (expo Dw w) b)
    rwa [← Units.val_div_eq_div_val, div_eq_mul_inv] at this
  have hu2 : UnitAt b ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn (divOf Y (expo Dw (-w))) b).iff_unitAt.1 (LineTest.isEqn_divOf Y (expo Dw (-w)) b)
    rwa [← Units.val_div_eq_div_val, div_eq_mul_inv, hP'] at this
  have hu : UnitAt b ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn) := unitAt_eqn_mul Y w b
  have hprod : ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) * ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      (((e1 * e2)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    rw [← Units.val_mul, mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_inv]
  have hv1 := (Base.valAt_zpow y.1 hu1).1
  have hv2 := (Base.valAt_zpow y.1 hu2).1
  have hvals : valAt y.1 ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) * valAt y.1 ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      (valAt y.1 ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn))⁻¹ := by
    rw [← OfModel.valAt_mul y.1 hu1.regAt hu2.regAt, hprod, Units.val_inv_eq_inv_val,
      GlobalTheory.LineNorm.Neg.valAt_inv hu]
  have hlog : Real.log (ε.w (valAt y.1 ((P * e1⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      Real.log (ε.w (valAt y.1 ((P⁻¹ * e2⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) =
      -Real.log (ε.w (valAt y.1 ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn))) := by
    rw [← Real.log_mul (ε.w.pos hv1).ne' (ε.w.pos hv2).ne', ← map_mul, hvals, map_inv₀, Real.log_inv]
  rw [hP']
  linear_combination hlog

theorem lg_neg_step (w : Sym E →₀ ℤ) (m : ℕ+) {Lp : LB Y.Y.X} {r : Lp.ι → Y.Y.Fnˣ}
    (hr : Presents ((m : ℕ) • divOf Y (expo Dw w)) Lp r) {i : Lp.ι} {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (y : AlgPt Y.Y) (h₂ : below y.1 ∈ Lp.U i)
    (h1 : ((m : ℕ) : ℝ) * lgOf Y w v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Y.Fnˣ) : Y.Y.Fn))) -
        ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : HeightOneSpectrum (𝓞 F) → ℝ) v) :
    ((m : ℕ) : ℝ) * lgOf Y (-w) v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw (-w))) (below y.1))⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) -
        ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : HeightOneSpectrum (𝓞 F) → ℝ) v := by
  simp only [Pi.zero_apply, mul_zero, sub_zero] at h1 ⊢
  set b := below y.1 with hb
  set e1 := eqn (divOf Y (expo Dw w)) b with he1
  set e2 := eqn (divOf Y (expo Dw (-w))) b with he2
  have hX : UnitAt b ((e1⁻¹ ^ (m : ℕ) * r i : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := ((Base.isEqn_eqn (divOf Y (expo Dw w)) b).nsmul (m : ℕ)).iff_unitAt.1 (hr.isEqn _ _ h₂)
    rwa [← Units.val_div_eq_div_val, div_eq_inv_mul, ← inv_pow] at this
  have hU : UnitAt b ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn) := unitAt_eqn_mul Y w b
  have hXU : UnitAt b ((e1⁻¹ ^ (m : ℕ) * r i * (e1 * e2) ^ (m : ℕ) : Y.Y.Fnˣ) : Y.Y.Fn) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    exact hX.mul (InducedPow.unitAt_pow hU _)
  have hprod : (e2⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Y.Fnˣ) = (e1⁻¹ ^ (m : ℕ) * r i * (e1 * e2) ^ (m : ℕ))⁻¹ :=
    inv_pow_mul_inv_eq e1 e2 (r i) (m : ℕ)
  have hv1 := (Base.valAt_zpow y.1 hX).1
  have hv2 := (Base.valAt_zpow y.1 hU).1
  have hval : valAt y.1 ((e2⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      (valAt y.1 ((e1⁻¹ ^ (m : ℕ) * r i : Y.Y.Fnˣ) : Y.Y.Fn) *
        valAt y.1 ((e1 * e2 : Y.Y.Fnˣ) : Y.Y.Fn) ^ (m : ℕ))⁻¹ := by
    rw [hprod, Units.val_inv_eq_inv_val, GlobalTheory.LineNorm.Neg.valAt_inv hXU, Units.val_mul, Units.val_pow_eq_pow_val,
      OfModel.valAt_mul _ hX.regAt (InducedPow.unitAt_pow hU _).regAt, InducedPow.valAt_pow _ hU.regAt]
  rw [hval, map_inv₀, map_mul, map_pow, Real.log_inv, Real.log_mul (ε.w.pos hv1).ne'
    (pow_ne_zero _ (ε.w.pos hv2).ne'), Real.log_pow, lgOf_neg]
  linear_combination -h1

theorem pn_neg_step {σ : F →+* ℂ} (G G' : EigMet Z (embOf e σ)) (hG : G = G') (n n' : Letter Dw → ℤ) (hn : n' = -n)
    (m : ℕ+) {Lp : LB Y.Y.X} {r : Lp.ι → Y.Y.Fnˣ} (hr : Presents ((m : ℕ) • divOf Y n) Lp r) {i : Lp.ι}
    (y : Pts Y.Y σ) (hi : under y ∈ Lp.U i) (φ₀ : ℝ)
    (hinf : ∀ f : Y.Y.Fn, ((m : ℕ) • divOf Y n).RegularAt (under y) f →
      Real.exp (-(2 * ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : InfinitePlace F → ℝ) (InfinitePlace.mk σ))) *
        Var.pn Y.Y σ _ (Var.mPow Y.Y σ _ (m : ℕ) (Y.met G n)) (Var.cx Y.Y σ f) y =
          ‖ratVal (f * (r i : Y.Y.Fn)) y‖ ^ 2 * Real.exp (-φ₀))
    (f : Y.Y.Fn) (hf : ((m : ℕ) • divOf Y n').RegularAt (under y) f) :
    Real.exp (-(2 * ((m : ℕ) : ℝ) * (((1 : ℕ+) : ℕ) : ℝ) * (0 : InfinitePlace F → ℝ) (InfinitePlace.mk σ))) *
      Var.pn Y.Y σ _ (Var.mPow Y.Y σ _ (m : ℕ) (Y.met G' n')) (Var.cx Y.Y σ f) y =
        ‖ratVal (f * (((r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn)) y‖ ^ 2 * Real.exp (-(-φ₀)) := by
  subst hG hn
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at hinf ⊢
  set g := eqn (divOf Y n) (under y) with hgdef
  have hg : (divOf Y n).IsEqn (under y) g := Base.isEqn_eqn _ _
  have hgm := hg.nsmul (m : ℕ)
  have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hgm
  have h1 := hinf _ hgen.regularAt
  rw [← Units.val_inv_eq_inv_val, Var.pn_frame (show y ∈ Var.eqnSet σ _ (g ^ (m : ℕ)) from hgm),
    Var.mPow_h (show y ∈ Var.eqnSet σ _ g from hg), ← Units.val_mul] at h1
  have hu : UnitAt (under y) (((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := hgm.iff_unitAt.1 (hr.isEqn i _ hi)
    rwa [← Units.val_div_eq_div_val, div_eq_inv_mul] at this
  have hgn : (divOf Y (-n)).IsEqn (under y) g⁻¹ := by rw [divOf_neg]; exact hg.neg
  have hg' := hgn.nsmul (m : ℕ)
  rw [Var.pn_eq (show y ∈ Var.eqnSet σ _ (g⁻¹ ^ (m : ℕ)) from hg'),
    Var.mPow_h (show y ∈ Var.eqnSet σ _ g⁻¹ from hgn), Var.fval_cx]
  have hN := met_neg_h Y G n (show y ∈ Var.eqnSet σ _ g from hg)
  have hinvh : (Y.met G (-n)).h g⁻¹ y = ((Y.met G n).h g y)⁻¹ := eq_inv_of_mul_eq_one_left hN
  rw [hinvh, inv_pow ((Y.met G n).h g y) (m : ℕ), h1]
  have hf' : RegAt (under y) (f * ((g⁻¹ ^ (m : ℕ) : Y.Y.Fnˣ) : Y.Y.Fn)) := hg'.regularAt_iff.1 hf
  have hU : ((r i)⁻¹ : Y.Y.Fnˣ) = g⁻¹ ^ (m : ℕ) * ((g ^ (m : ℕ))⁻¹ * r i)⁻¹ := by
    rw [inv_pow, mul_inv_rev, inv_inv, mul_comm (r i)⁻¹, inv_mul_cancel_left]
  have hsplit : f * (((r i)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) =
      f * ((g⁻¹ ^ (m : ℕ) : Y.Y.Fnˣ) : Y.Y.Fn) * (((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn)⁻¹ := by
    rw [hU, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]
  have hinvr : ratVal ((((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn))⁻¹ y =
      (ratVal (((g ^ (m : ℕ))⁻¹ * r i : Y.Y.Fnˣ) : Y.Y.Fn) y)⁻¹ := by
    have := ratVal_mul hu.regAt hu.inv.regAt (y := y)
    rw [mul_inv_cancel₀ (Units.ne_zero _), Base.ratVal_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  rw [hsplit, ratVal_mul hf' hu.inv.regAt, hinvr, norm_mul, norm_inv, mul_pow, inv_pow, mul_inv, neg_neg,
    Real.exp_neg, inv_inv]
  ring

end Free

theorem induced_neg : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+) (R : ℝ) (w : Sym D.host.E →₀ ℤ) (L : GlobalTheory.HermLB M.p), (∀ a ∈ w.support, a.2.1 = some R) → (adlOf (Φ.C k) (metsOf x Φ k) w).Induced M L m 0 → (adlOf (Φ.C k) (metsOf x Φ k) (-w)).Induced M L.dual m 0 := by
  intro D A N j S κ s x Φ k M m R w L _ hL
  obtain ⟨hfin, r, hr, hinf, hv⟩ := hL
  unfold Adl.Induced
  refine ⟨hfin, fun i => (r i)⁻¹, ?_, ?_, ?_⟩
  · show Presents ((m : ℕ) • divOf (Φ.C k) (expo S.Dw (-w))) _ _
    rw [expo_neg, divOf_neg, smul_neg]
    exact GlobalTheory.LineNorm.Neg.presents_neg L.isLB M.j hr
  · intro σ y y' i f hy hi hf
    exact pn_neg_step (Φ.C k) (x.eigMetAt (embOf κ.e σ) (parOf w)) (x.eigMetAt (embOf κ.e σ) (parOf (-w)))
      (by rw [parOf_neg]) (expo S.Dw w) (expo S.Dw (-w)) (expo_neg S.Dw w) m hr y hi
      ((L.φ _).φ (i PUnit.unit) y') (fun f hf => hinf σ y y' i f hy hi hf) f hf
  · intro v ε y yt i h hi
    exact lg_neg_step (Φ.C k) w m hr ε y (OfModel.le_chart M L.B ε y yt h (i := i) hi trivial) (hv v ε y yt i h hi)

end GlobalTheory.CombInd.DualComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCellsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.barycentricSubdivision_star_step_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  first | exact @GlobalTheory.PolFan.baryStep | exact GlobalTheory.PolFan.baryStep | (intros; apply GlobalTheory.PolFan.baryStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedAdelicDataWithIntertwinersOverEnla
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.RSideW.wk_image {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
    {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} {z : Dat (w.st Z) w.I hX T Wt} {Wt' : Set B'.places.Pl}
    {R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks} (h : RSideW z Wt' R')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    ∀ x' ∈ (R'.FW i').WK, ∃ x ∈ (z.R.FW i).WK, ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) → CrdOver ι x x' := by
  intro x' hx'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, rI, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rι⟩ := rI i i' hi
  by_cases hex : ∃ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y
  · obtain ⟨ι, hι⟩ := hex
    obtain ⟨-, ⟨a, b⟩, -⟩ := rι ι hι
    obtain ⟨x, hx⟩ := b x' hx'
    refine ⟨x, (a x x' hx).1 hx', fun ι' hι' => ?_⟩
    have e : ι' = ι := RingHom.ext fun y => (w'.st Z').toD7.what₂.embLL.injective ((hι' y).trans (hι y).symm)
    rw [e]
    exact hx
  · exact ⟨0, Submodule.zero_mem _, fun ι hι => absurd ⟨ι, hι⟩ hex⟩

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.datExt_rest : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, z'.core = core' ∧
        z'.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z'.geo ∧ z'.Std ∧ ExtN z z') := by
  refine GlobalTheory.Mem.R3.Rw.datExt_rest_of_parts GlobalTheory.T.exists_analyticData_enlargedBase_tupleFree GlobalTheory.T.exists_characterisedData_weil_enlargedBase fun h1 h2 h3 h4 h5 h6 h7 => ?_
  refine (GlobalTheory.T.geometricHalf_to_analyticData_enlargedBase h1 h2 h3 h4 h5 h6 h7).trans (Step.of_all fun K B' f' T' _ _ _ _ w' hd => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1
  exact hd B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1
    (@GlobalTheory.Mem.R3.Rw.RSideW.wk_image _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ alg' _ _ _ _ _ s1.2.2.2.2.2.2.2.1)
end


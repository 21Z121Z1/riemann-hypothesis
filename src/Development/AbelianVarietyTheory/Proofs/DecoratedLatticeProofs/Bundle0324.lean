import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LastStepsX

variable {D : D7}

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (a : ℂ)
    (G : GA D T → ℂ) (f : WO S T → ℂ) : liftS om ν 𝓕 (a • G) f = a • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS, Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (a : ℂ) (f : GA D V → ℂ) : trc e (a • f) = a • trc e f := by
  funext x
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem perF_smul {c : Comm D} (t : Tup c) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (a : ℂ) (f : GA D (c.V j) → ℂ) : t.perF j ρ h φ (a • f) = a * t.perF j ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e := GlobalTheory.HandHom.per_smul (c.B j ρ h) c.ψ 1 a (φ α) (trc (t.e j α) f)
  rw [one_smul, one_mul] at e
  exact e

theorem contAut_trc {V : HSp D} (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hf.1 γ hγ]
  · have e : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := by
      funext x
      simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact continuous_finset_sum _ fun g _ => continuous_const.mul (hf.2.comp (continuous_mul_right g))

theorem contAut_emb {S A B : HSp D} (o : OrthDec S A B) {f : GA D S → ℂ} (hf : IsContAut S f) :
    Continuous (fun h : GA D A => f (o.emb (h, 1))) ∧ ∀ γ ∈ GQ A, ∀ g, f (o.emb (γ * g, 1)) = f (o.emb (g, 1)) := by
  refine ⟨hf.2.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const)), fun γ hγ g => ?_⟩
  have e : o.emb (γ * g, 1) = o.emb (γ, 1) * o.emb (g, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, hf.1 _ (o.emb_mem_GQ hγ (one_mem _))]

theorem integrableOn_contAut {V : HSp D} (hV : CoCpt V) (vol : Vol V) {f : GA D V → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : IntegrableOn f vol.𝓕 vol.μ :=
  (GlobalTheory.CocompactParam.continuous_integral_param D V hV vol Unit (fun g _ => f g) (hc.comp continuous_fst)
    (fun γ hγ g _ => hi γ hγ g)).1 ()

theorem io_ioT {c : Comm D} (t : Tup c) (ht : t.Is) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (F : t.CT)
    (P₁ : PolF D (c.V (j + 1)).rank (c.V j).rank) (P₂ : PolF D c.T.rank (c.V (j + 1)).rank) (v : SmT c.MT) :
    (t.cI j * t.cI (j + 1)) • ((t.io j (t.ioT j h F)).1 (c.It j P₁ (c.ItT j h P₂ v))) =
      liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P₂)) (t.pt j P₁) := by
  rw [ht.ioT j h F P₂ v, liftS_smul, ht.io j (by omega) (t.ioT j h F) P₁ (c.ItT j h P₂ v), smul_smul, mul_comm]

theorem perT_comb {c : Comm D} (t : Tup c) (n : ℕ) (h : n = D.R.m) {Y : Type} (S : Finset Y) (k : ℂ) (a : Y → ℂ)
    (φ : Y → t.Ch n → GA D (c.X n) → ℂ) (f : GA D c.T → ℂ)
    (hi : ∀ y' β, IntegrableOn (fun h' => trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) c.volT.𝓕 c.volT.μ) :
    t.perT n h (fun β => k • ∑ y' ∈ S, a y' • φ y' β) f = k * ∑ y' ∈ S, a y' * t.perT n h (φ y') f := by
  have e1 : ∀ β, ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1)) ∂c.volT.μ
      = ∑ y' ∈ S, k * a y' * ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1)) ∂c.volT.μ := by
    intro β
    have e2 : (fun h' => trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1))) =
        fun h' => ∑ y' ∈ S, (k * a y') * (trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) := by
      funext h'
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y' _ => by ring
    rw [e2, integral_finset_sum _ (fun y' _ => (hi y' β).const_mul _)]
    simp_rw [integral_const_mul]
  simp only [Tup.perT, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun β _ => by ring

end GlobalTheory.SeeSaw.LastStepsX

set_option maxHeartbeats 4000000 in
open GlobalTheory.SeeSaw.LastStepsX in

theorem GlobalTheory.SeeSaw.lastX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), RapidVal D → c.Is → (∀ s, (t s).Is) → ValLastX t → TwoX t → PerX t → RdX t → LastX t := by
  intro hHC D c 𝒯 t hRV hc ht hVL hTX hPX hRD
  intro j h I _ s α ψ F hψ hF y v
  obtain ⟨χ, hχ⟩ := hRD j (by omega)
  obtain ⟨χ₂, hχ₂⟩ := hRD (j + 1 + 1) (by omega)
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j 0 h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i β => (t (s i)).rd j β (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).ioT j h (F i))) ht
    (fun i β => (hχ (s i) (ψ i) (hψ i) β y).1) c.T c.T c.parT c.MT (c.ItT j h) (hc.spanT j h) ?_ v
  intro P₁ P₂ w
  obtain ⟨C, hCr, hC⟩ := hVL j h P₁ P₂
  obtain ⟨a, ha⟩ := hTX j (by omega) C hCr y
  choose b hb using fun y' => hPX (j + 1 + 1) h y' w
  have hterm : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j 0 h (fun β => (t (s i)).rd j β (ψ i) y)
      (((t (s i)).io j ((t (s i)).ioT j h (F i))).1 (c.It j P₁ (c.ItT j h P₂ w))) =
      ∑ y' ∈ a.support, a y' * b y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1) * (t (s i)).cP) *
        (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i)) := by
    intro i
    have hSψ : (t (s i)).S j (ψ i) ∈ (t (s i)).Ram j := (ht (s i)).stabS j (by omega) _ (hψ i)
    have hψ₁ := (ht (s i)).stabK j (by omega) _ hSψ
    have hψ₂ := (ht (s i)).stabK (j + 1) (by omega) _ hψ₁
    rw [mul_assoc, ← perF_smul, io_ioT (t (s i)) (ht (s i)) j h (F i) P₁ P₂ w, hC (s i) (ψ i) (hψ i) y (F i) w]
    have e2 : (t (s i)).two j (fun β => (t (s i)).rd j β ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ a.support, a y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext fun β => ha (s i) _ hSψ β
    have hE : RapidDec c.T ((F i).1 w) := by
      obtain ⟨J, χ', hle⟩ := (ht (s i)).CT
      exact hRV c.θ hc.inf c.T c.parT c.MT J χ' _ (hle (F i).2) w
    have e3 := perT_comb (t (s i)) (j + 1 + 1) h a.support ((t (s i)).cK j * (t (s i)).cK (j + 1)) a
      (fun y' β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w)
      (fun y' β => by
        have ht' := contAut_trc ((t (s i)).eT (j + 1 + 1) h β) ⟨hE.1, hE.2.1⟩
        obtain ⟨hcont, hinv⟩ := contAut_emb (c.oT (j + 1 + 1) h) (hχ₂ (s i) _ hψ₂ β y').1
        exact integrableOn_contAut hc.cpt c.volT (ht'.2.mul hcont) (fun γ hγ g => by rw [ht'.1 γ hγ g, hinv γ hγ g]))
    beta_reduce at e3
    have hb' : ∀ y', (t (s i)).perT (j + 1 + 1) h
        (fun β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w) =
        (t (s i)).cP * b y' * (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i) :=
      fun y' => hb y' (s i) _ hψ₂ (F i)
    rw [e2, e3]
    simp only [hb', Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hF, mul_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTotalConstantRatioOfFactorRatios
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ratio_total_unitRatio_of_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  intro D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s
  obtain ⟨hrefl, hmul, -, hprod⟩ := GlobalTheory.Fam.unitRatio_laws (S s)
  have split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j =
      ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, mul_assoc]
  have hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0 := fun s j hj => (hIs s).cI j hj
  have hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) =
      κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i) := by
    intro i hi
    by_cases hlast : i + 1 = n
    · refine ⟨1, one_ne_zero, fun s => ?_⟩
      rw [one_mul]
      exact (hCV s).2 (2 * i) (by omega)
    · exact ⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩
  have hB : ∀ i, i < n → UnitRatio (S s)
      ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1)))
      ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1))) := by
    intro i hi
    obtain ⟨κ, hκ0, hκs⟩ := hκ i hi
    have hK0 : κ * v.cG (2 * i) ≠ 0 := mul_ne_zero hκ0 (hcG _)
    have hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) /
        ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) =
        κ * v.cG (2 * i) *
          ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) *
            ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) *
            ((t s').cK (2 * i) * (t s').cK (2 * i + 1))) := by
      intro s'
      rw [hκs s']
      ring
    rw [hform s, hform s₀]
    have hsc1 := (hscK s (2 * i) (by omega)).1
    have hsc2 := (hscK s (2 * i + 1) (by omega)).1
    have homogComponent_comm_first_action := (hscK s (2 * i) (by omega)).2
    have homogComponent_comm_second_action := (hscK s (2 * i + 1) (by omega)).2
    have hcT := (hTQ s (2 * i) (n - i - 1) (by omega)).1
    have hcQ := (hTQ s (2 * i) (n - i - 1) (by omega)).2
    exact (hmul _ _ _ _ (hrefl _ hK0)
      (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1
        (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1
  have hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n,
      ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) *
      (t s').cP := by
    intro s'
    unfold Tup.cTop Tup.cBot
    rw [← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]
    ring
  have hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
    rw [hq s, hq s₀]
    exact (hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1
  have hbot : (t s).cBot ≠ 0 := by
    unfold Tup.cBot
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)
  have hne := (hmul _ _ _ _ hall hall).2.2
  refine ⟨fun h0 => hne ?_, hbot, hall⟩
  rw [h0, zero_div]

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawRhs

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hv' => hv v (fun hp => hv' (h v hp)), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono S T _ _ h hu),
    fun e he u hu hh => hf.2.2 e he u (latO_mono S T _ _ h hu) hh⟩

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : idAt D P ≤ idAt D P' := by
  intro x hx
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {c : WO S T →₀ ℂ}
    (hc : CombAt P c) : CombAt P' c := fun u hu i j => idAt_mono h (hc u hu i j)

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp [comb, heisO, Finset.sum_apply]

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • C) = a • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, Pi.smul_apply, smul_eq_mul, comb_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem comb_comm2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (e : WO A S →₀ ℂ) (d' : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' d' (fun v' => comb ψ A S e (fun u'' => G u'' v') u) v =
      comb ψ A S e (fun u'' => comb ψ S A' d' (G u'') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (d e : WO A S →₀ ℂ) (d' e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' d d' (biComb ψ A S A' e e' C) u v =
      comb ψ A S d (comb ψ A S e (fun u'' => comb ψ S A' d' (comb ψ S A' e' (C u'')) v)) u := by
  simp only [biComb]
  congr 1
  funext u'
  exact comb_comm2 ψ A S A' e d' (fun u'' v' => comb ψ S A' e' (C u'') v') u' v

theorem biLift_smul {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h1 : ∀ h₀ h₁ v, oma (h₀, h₁) (fun u => a * C u v) 0 = a * oma (h₀, h₁) (fun u => C u v) 0 := by
    intro h₀ h₁ v
    rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
    rfl
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => h1 h₀ h₁ v
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem theta_comb_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (c : WO S A' →₀ ℂ) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => comb ψ S A' c (Y u) v) := by
  classical
  have key : ∀ s : Finset (WO S A'),
      IsThetaFunO ψ A S (fun u => ∑ x ∈ s, c x * (ψ (symplOH S A' v x) * Y u (v + x))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact Formalism.IndefR.Fock.CCR.theta_zero ψ A S
    · intro x s hx ih
      have := Formalism.IndefR.Fock.CCR.theta_add_smul ih (hY (v + x)) (c x * ψ (symplOH S A' v x))
      convert this using 1
      funext u
      simp only [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simpa only [comb_apply] using key c.support

end GlobalTheory.SeeSawRhs

namespace GlobalTheory.SeeSawRhs

theorem unfolded_eq_kernel_data : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  intro D c v t w hc hv _ hF hG hT _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ β
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have top : ∀ (P : Pl D → Prop) p, P p → True := fun _ _ _ => trivial
  simp only [Comm.bl]
  rw [hG.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)]
  obtain ⟨hBV, hTL⟩ := hT.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)
  simp only [Comm.bl] at hTL
  set X₀ := c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ with hX₀
  set Y := (v.op j).app c.ψ X₀ with hY
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hoff : ∀ p, (p ∈ w.Q ∨ p ∈ v.gP) → p ∉ v.tP := by
    rintro p (hp | hp)
    · exact Finset.disjoint_left.mp hF.disjT hp
    · exact Finset.disjoint_left.mp hv.disj hp
  have prod := fun (S T : HSp D) => (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).2.2.2.1
  unfold Tup.two
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  obtain ⟨d₁, hd₁, ed₁⟩ := prod _ _ (w.dQ j α γ) (v.dG j)
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ j).2.2 α γ)) (combAt_mono (fun p hp => Or.inr hp) (hv.atG j).2.1)
  obtain ⟨d₂, hd₂, ed₂⟩ := prod _ _ (w.dQ (j + 1) γ β) (v.dG (j + 1))
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ (j + 1)).2.2 γ β))
    (combAt_mono (fun p hp => Or.inr hp) (hv.atG (j + 1)).2.1)
  have e1 : biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) X₀) =
      biComb c.ψ _ _ _ d₁ d₂ X₀ := by
    funext u v'
    rw [biComb_biComb]
    simp only [biComb, ed₁, ed₂]
  have e2 : biComb c.ψ _ _ _ d₁ d₂ (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) Y) =
      biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) Y := by
    funext u v'
    rw [biComb_biComb, ed₁]
    have hF' : (fun u'' => comb c.ψ _ _ d₂ (comb c.ψ _ _ (v.dT (j + 1)) (Y u'')) v') =
        fun u'' => comb c.ψ _ _ (t.dd (j + 1) γ β) (Y u'') v' := by
      funext u''
      rw [ed₂, ← hF.dd (j + 1) hj1 γ β _ (hBV.2 u'').1]
    rw [hF', ← hF.dd j hj α γ _ (theta_comb_left Y (fun v'' => (hBV.1 v'').1) _ v')]
    rfl
  rw [biComb_smul, biLift_smul, e1, hTL d₁ d₂ (combAt_mono hoff hd₁) (combAt_mono hoff hd₂) (φ α) (hφ α), e2,
    smul_smul]

end GlobalTheory.SeeSawRhs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GSuppFirst

theorem gsupp1_at : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F hF x hx hflat
  have hs := Gi.hs
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1))
    (Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)) (Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond
    (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Gi.latY j _ _) (Gi.latY (j + 1) _ _)).2 F hF
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Gi.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  have H2 : j + (2 * σ + 1 + 1) = Gi.s := by omega
  let Φ : GlobalTheory.SplitWeil.SB _ := ⟨_, (GModel.phi_sb Gi).1 j (2 * σ + 1 + 1) H2⟩
  have hcomb : Tm Φ = comb c.ψ _ _ (Gi.eg j) F := by
    rw [← hTmO O hO]; exact (Gi.eg_is j (2 * σ + 1 + 1) H2).2 Tm hTm O Φ hO rfl
  obtain ⟨μ, hμt, hμu, hBF, -⟩ := hch
  have hW := MuUnits.withMu_eq Gi.k Gi.s D.R.k Gi.S (Fin D.R.t) μ hμt hμu
  let Fd : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by have := Gi.sc_unit j; rw [h0, map_zero] at this; exact zero_ne_one this
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)
      G₁ := Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)
      G₂ := Gi.FY (j + 1 + 1) (2 * σ + 1) (by omega)
      bes := Gi.bes j (σ + 1) h _ _
      jac := Gi.jac j (σ + 1) h _ _
      bes' := by rw [← Gi.sc_step j]; exact Gi.bes (j + 1 + 1) σ (idx_step h) _ _ }
  have hΦ : Φ.1 = ((withMu Gi.S μ hμt).T (Fin D.R.t)).Phi j (2 * σ + 1 + 1) (by omega) := (hW.1 j _ _).symm
  have hflat' : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (1, x) (Tm Φ)) ≠ 0 := by
    rw [(ht.sBF j (σ + 1) h).1, hcomb]; exact hflat
  obtain ⟨r, hr, hrs, u, uk, hloc, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμt) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ Fd (t.sBF j (σ + 1) h) (hBF j (σ + 1) h).1 Tm hTm Φ hΦ x hx hflat'
  refine ⟨r, hr, hrs, u, uk, hloc, ?_, hxr⟩
  rw [← (hW.2 (j + 1) (2 * σ + 1 + 1) (by omega)).1]; exact huk

end GlobalTheory.SeeSaw.GSuppFirst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaCenterActionLeft
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.CenS

variable {D : D7} {S T : HSp D}

def Carried (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (A : (GA D S → ℂ) → (GA D S → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ w, A (fun g => om (g, 1) f w) = fun g => om (g, 1) f' w

variable {ψ : AddChar (AF D.host.F) ℂ} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem Carried.comp {A B : (GA D S → ℂ) → (GA D S → ℂ)} (hA : Carried ψ om A) (hB : Carried ψ om B) :
    Carried ψ om fun φ => A (B φ) := fun f hf => by
  obtain ⟨f₁, hf₁, e₁⟩ := hB f hf
  obtain ⟨f₂, hf₂, e₂⟩ := hA f₁ hf₁
  exact ⟨f₂, hf₂, fun w => by simp only [e₁ w, e₂ w]⟩

theorem Carried.smul {A : (GA D S → ℂ) → (GA D S → ℂ)} (hA : Carried ψ om A) (c : ℂ) :
    Carried ψ om fun φ => c • A φ := fun f hf => by
  obtain ⟨f₁, hf₁, e₁⟩ := hA f hf
  refine ⟨c • f₁, (GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c hf₁, fun w => funext fun g => ?_⟩
  simp only [e₁ w, Pi.smul_apply, map_smul]

variable {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}

end GlobalTheory.Core.Rk.CenS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  first | exact @GlobalTheory.OffPlaceWeil.main | exact GlobalTheory.OffPlaceWeil.main | (intros; apply GlobalTheory.OffPlaceWeil.main <;> assumption)
end


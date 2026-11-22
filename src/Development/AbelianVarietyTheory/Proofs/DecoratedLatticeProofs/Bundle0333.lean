import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSum

variable {D : D7}

theorem ontoUni_inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {n : ℕ} (hn : V.rank = n)
    (h : OntoUni fun k : GinfC V => inN θ V B hn k.1) : OntoUni fun k : GinfC V => inB θ V B k.1 := by
  subst hn
  exact h

theorem castP_surj {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp hq
  exact ⟨Q, MvPolynomial.rename_id_apply Q⟩

theorem det_ne_zero_of_isUni {ι : Type} {a : ℕ} {u : ι → Matrix (Fin a) (Fin a) ℂ} (hu : IsUni u) (τ : ι) :
    (u τ).det ≠ 0 := by
  have := Matrix.mem_unitaryGroup_iff.1 (hu τ)
  intro h0
  have h1 := congrArg Matrix.det this
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

def trF {n : ℕ} {u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) (y : FrN D n) : FrN D n :=
  ⟨fun τ => u τ * y.1 τ, fun τ => by
    rw [Matrix.det_mul]
    exact (isUnit_iff_ne_zero.2 (det_ne_zero_of_isUni hu τ)).mul (y.2 τ)⟩

theorem isTr_trF {n : ℕ} {u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) (y : FrN D n) :
    IsTr u y (trF hu y) := fun _ => rfl

section Weil

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem theta_snd (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D T} (hγ : γ ∈ GQ T)
    (g : GA D S) (x κ : GA D T) {p : ℂ} (hp : om (1, κ) f = p • f) : om (g, γ * x * κ) f 0 = p * om (g, x) f 0 := by
  have : ((g, γ * x * κ) : GA D S × GA D T) = (1, γ) * ((g, x) * (1, κ)) := by
    simp [mul_assoc]
  rw [this, map_mul, Module.End.mul_apply, hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hf), map_mul, Module.End.mul_apply,
    hp, map_smul]
  rfl

theorem theta_fst_left (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S}
    (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) : om (γ * g, x) f 0 = om (g, x) f 0 := by
  have : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  rw [this, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hf)]

theorem theta_fst_right {f : WO S T → ℂ} (g κ : GA D S) (x : GA D T) {p : ℂ} (hp : om (κ, 1) f = p • f) :
    om (g * κ, x) f 0 = p * om (g, x) f 0 := by
  have : ((g * κ, x) : GA D S × GA D T) = (g, x) * (κ, 1) := by simp
  rw [this, map_mul, Module.End.mul_apply, hp, map_smul]
  rfl

theorem theta_mul {f f' : WO S T → ℂ} (g k : GA D S) (x k' : GA D T) {p : ℂ} (hp : om (k, k') f = p • f') :
    om (g * k, x * k') f 0 = p * thetaKO om g x f' := by
  have : ((g * k, x * k') : GA D S × GA D T) = (g, x) * (k, k') := rfl
  rw [this, map_mul, Module.End.mul_apply, hp, map_smul]
  rfl

end Weil

def formAt {ι : Type} {a b : ℕ} (Λ : FP ι a b →ₗ[ℂ] ℂ) (s : ι → ℂ) (u : ι → Matrix (Fin b) (Fin b) ℂ) : FP ι a b →ₗ[ℂ] ℂ :=
  Λ ∘ₗ (mvZ (fun _ => 1) fun τ => s τ • u τ).toLinearMap

theorem formAt_mvZ {ι : Type} [Fintype ι] {a b : ℕ} (hab : a ≤ b) (Λ : FP ι a b →ₗ[ℂ] ℂ) (s : ι → ℂ)
    (u : ι → Matrix (Fin b) (Fin b) ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (Q : FP ι a b) :
    Λ (mvZ (fun _ => 1) (fun τ => s τ • 1) (mvZ g u Q)) = formAt Λ s u (mvZ g (fun _ => 1) Q) := by
  unfold formAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, (substIdentities ι a b hab).2.1, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem formAt_subY {ι : Type} {a b : ℕ} (hab : a ≤ b) (Λ : FP ι a b →ₗ[ℂ] ℂ) (s : ι → ℂ)
    (u y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a) :
    formAt Λ s u (subY hab y' F) = Λ (subY hab (fun τ => u τ * s τ • y' τ) F) := by
  unfold formAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, mvZ_subY, Matrix.smul_mul, Matrix.mul_smul]

theorem prod_det_cancel {ι : Type} [Fintype ι] {a : ℕ} (u y : ι → Matrix (Fin a) (Fin a) ℂ) (hu : ∀ τ, (u τ).det ≠ 0) (s : ι → ℤ)
    (d : ι → ℂ) : (∏ τ, (u τ).det ^ s τ * d τ) * ∏ τ, (u τ * y τ).det ^ (-s τ) = (∏ τ, d τ) * ∏ τ, (y τ).det ^ (-s τ) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Matrix.det_mul, mul_zpow, _root_.zpow_neg (u τ).det]
  have := zpow_ne_zero (s τ) (hu τ)
  field_simp

theorem prod_det_cancel' {ι : Type} [Fintype ι] {a : ℕ} (u y : ι → Matrix (Fin a) (Fin a) ℂ) (hy : ∀ τ, (y τ).det ≠ 0) (s : ι → ℤ) :
    (∏ τ, (y τ).det ^ s τ) * ∏ τ, (u τ * y τ).det ^ (-s τ) = ∏ τ, (u τ).det ^ (-s τ) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Matrix.det_mul, mul_zpow, _root_.zpow_neg (y τ).det]
  have := zpow_ne_zero (s τ) (hy τ)
  field_simp

variable {c : Comm D} {ρ : RealD c} {t : Tup c} {A : ClsK ρ t}

theorem lev_pt (hc : c.Is) (ht : t.Is) (hA : A.Is) {j : ℕ} (hj : j + 1 ≤ D.R.m) (α γ P) (κ : A.U j α) (κ' : A.U (j + 1) γ) :
    t.kom j (κ.1, κ'.1) ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      (((A.chi j α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)) • (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P :=
  (GlobalTheory.T.finiteElements_act_fockVectors_through_datum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (t.ker j α γ) (hc.x j (Nat.le_of_succ_le hj)) (hc.x _ hj)
    (ht.ker j hj α γ) P).2 _ ((hA.1.reps j (Nat.le_of_succ_le hj) α).le κ.2) _ ((hA.1.reps _ hj γ).le κ'.2) _
    (hA.2.2.1 j hj α γ κ κ')

theorem integrand_eq (hρ : ρ.Is) (hA : A.Is) {j : ℕ} (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1)) {ψ} (hψ : ψ ∈ t.Ram j)
    (α γ a a' y P) (F : PY D.what₂.Tau (ρ.N j))
    (hF : ∀ z, A.val j α ψ a z = GlobalTheory.KJInf.evalAt z.1 F * ∏ τ, (z.1 τ).det ^ (-ρ.sS j τ))
    (k : GinfC (c.X j)) (k' : GinfC (c.X (j + 1))) :
    (volLev (c.x j).vol (A.U j α) : ℂ) *
      (t.kom j (A.h j α a * k.1, A.h (j + 1) γ a' * k'.1) ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) 0 *
        t.rd j α ψ y (A.h j α a * k.1)) =
    (t.cK j * (∏ τ, (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)) * ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)) *
      (formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k'.1)
        (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P)) *
        GlobalTheory.KJInf.evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ) F) := by
  have hu : IsUni (ρ.r j (Nat.le_of_succ_le hj) k.1) := (hρ.uni j (Nat.le_of_succ_le hj)).uni k
  obtain ⟨P', hP'⟩ := castP_surj (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj)
    (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (ρ.r (j + 1) hj k'.1)
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))
  have h1 := hA.2.1 j hj α γ k.1 k.2 k'.1 k'.2 P P' hP'
  have h2 := hA.2.2.2.1 j hj α γ a a' P'
  have h3 := hA.1.rd j (Nat.le_of_succ_le hj) ψ hψ α y 1 (one_mem _) a k.1 k.2 1 _ (isTr_trF hu (ρ.fr j y))
  rw [hF] at h3
  simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one] at h3
  rw [hP', formAt_mvZ hab] at h2
  have h4 := prod_det_cancel (ρ.r j (Nat.le_of_succ_le hj) k.1) (ρ.fr j y).1 (det_ne_zero_of_isUni hu) (ρ.sS j)
    fun τ => (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)
  rw [theta_mul _ _ _ _ h1, h3]
  simp only [trF]
  set e := GlobalTheory.KJInf.evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ) F
  linear_combination
    ((∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k.1 τ).det ^ ρ.sS j τ * (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)) * e *
      ∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)) * h2 +
    (t.cK j * e * formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k'.1)
        (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))) * h4

theorem lift_eq (hc : c.Is) (hρ : ρ.Is) (ht : t.Is) (hA : A.Is) {j : ℕ} (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1))
    {ψ} (hψ : ψ ∈ t.Ram j) (α γ a' y P) (ν : Measure (GinfC (c.X j)))
    (hcl : ∀ Φ : GA D (c.X j) → ℂ, Continuous Φ → (∀ γ ∈ GQ (c.X j), ∀ g, Φ (γ * g) = Φ g) →
      (∀ κ ∈ A.U j α, ∀ g, Φ (g * κ) = Φ g) → ∫ g in (c.x j).vol.𝓕, Φ g ∂(c.x j).vol.μ =
        (volLev (c.x j).vol (A.U j α) : ℂ) * ∑ a, ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹ * ∫ k, Φ (A.h j α a * k.1) ∂ν)
    (F : A.cl j α → PY D.what₂.Tau (ρ.N j))
    (hF : ∀ a z, A.val j α ψ a z = GlobalTheory.KJInf.evalAt z.1 (F a) * ∏ τ, (z.1 τ).det ^ (-ρ.sS j τ))
    {g' : GA D (c.X (j + 1))} (hg' : g' ∈ GQ (c.X (j + 1))) (k' : GinfC (c.X (j + 1))) (κ' : A.U (j + 1) γ) :
    (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P (t.rd j α ψ y) (g' * (A.h (j + 1) γ a' * k'.1) * κ'.1) =
      ∑ a, (((A.chi (j + 1) γ κ' : ℂˣ) : ℂ) * t.cK j * (∏ τ, (ρ.r (j + 1) hj k'.1 τ).det ^ (-ρ.sD j τ)) *
        ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹) * ((∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k'.1)
          (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1)
            (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P)) *
          GlobalTheory.KJInf.evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j y).1 τ) (F a) ∂ν) := by
  obtain ⟨χS, χT, hw⟩ := (ht.ker j hj α γ).weil
  have hw' : IsWeilDatumO c.ψ _ _ χS χT (t.kom j) := hw
  have hf := (GlobalTheory.T.finiteElements_act_fockVectors_through_datum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (t.ker j α γ) (hc.x j (Nat.le_of_succ_le hj)) (hc.x _ hj)
    (ht.ker j hj α γ) P).1
  obtain ⟨hr1, hr2, -, -⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c t ρ A hc hρ hA.1 j (Nat.le_of_succ_le hj) ψ hψ α
  have hk' := lev_pt hc ht hA hj α γ P 1 κ'
  simp only [OneMemClass.coe_one, map_one, Units.val_one, inv_one, one_mul] at hk'
  have hI := fun a (k : GinfC (c.X j)) => integrand_eq hρ hA hj hab hψ α γ a a' y P (F a) (hF a) k k'
  have hk : ∀ κ : A.U j α, t.kom j (κ.1, 1) ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      ((A.chi j α κ : ℂˣ) : ℂ)⁻¹ • (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P := fun κ => by
    have := lev_pt hc ht hA hj α γ P κ 1
    simpa only [OneMemClass.coe_one, map_one, Units.val_one, mul_one] using this
  unfold KerDat.lift
  rw [liftT_apply]
  generalize (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P = f at *
  change ∫ g in (c.x j).vol.𝓕, t.kom j (g, g' * (A.h (j + 1) γ a' * k'.1) * κ'.1) f 0 * t.rd j α ψ y g ∂(c.x j).vol.μ = _
  simp only [theta_snd hw' hf hg' _ _ _ hk', mul_assoc ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)]
  rw [integral_const_mul, hcl (fun g => t.kom j (g, A.h (j + 1) γ a' * k'.1) f 0 * t.rd j α ψ y g)]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 := congrArg (fun φ : GinfC (c.X j) → ℂ => ∫ k, φ k ∂ν) (funext (hI a))
    simp only [integral_const_mul] at h1
    linear_combination (((A.chi (j + 1) γ κ' : ℂˣ) : ℂ) * ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹) * h1
  · exact ((hw'.om_cont f hf 0).comp (continuous_id.prodMk continuous_const)).mul (hr1 y).2
  · intro γ₀ hγ₀ g
    simp only [theta_fst_left hw' hf hγ₀, (hr1 y).1 γ₀ hγ₀ g]
  · intro κ hκ g
    have h1 := hr2 y g ⟨κ, hκ⟩
    have h2 := theta_fst_right g κ (A.h (j + 1) γ a' * k'.1) (hk ⟨κ, hκ⟩)
    simp only at h1 ⊢
    rw [h1, h2]
    have := (A.chi j α ⟨κ, hκ⟩).ne_zero
    field_simp

end GlobalTheory.SeeSaw.LiftSum

namespace GlobalTheory.SeeSaw

open LiftSum

theorem lift_eq_classSum : ∀ (D : D7) (c : Comm D) (ρ : RealD c), c.Is → ρ.Is → ∀ j (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1)), BorelSpace (GinfC (c.X j)) ∧ ∃ ν : Measure (GinfC (c.X j)), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (m : ℕ) (y : Fin m → c.Fr j) (P : Fin m → PolF D (c.X (j + 1)).rank (c.X j).rank) (m' : ℕ) (y' : Fin m' → D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ) (y'' : Fin m' → c.Fr (j + 1)) (s : Fin m' → ℂ), (∀ i τ, (ρ.fr (j + 1) (y'' i)).1 τ = ρ.sc j τ • y' i τ) → (∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ, ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1) (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) (P i))) * evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν = ∑ i, s i * Λ (subY hab (y' i) F)) → ∀ (t : Tup c) (A : ClsK ρ t), t.Is → A.Is → ∀ ψ ∈ t.Ram j, ∀ γ, ∑ i, ∑ α, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) (t.rd j α ψ (y i)) = t.cK j • ∑ i, (s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ) • t.rd (j + 1) γ (t.K j ψ) (y'' i) := by
  intro D c ρ hc hρ j hj hab
  obtain ⟨hB, -, -, ν, hν1, hν2, hcl⟩ := integral_eq_classSum D c.θ (c.X j) (c.x j).B hc.inf
    (ontoUni_inB _ _ _ _ (hρ.uni j (Nat.le_of_succ_le hj)))
  refine ⟨hB, ν, hν1, hν2, ?_⟩
  intro m y P m' y' y'' s hy hav t A ht hA ψ hψ γ
  have hV := fun α a => ((valC_poly _ _ _ (ρ.lam j)).1 (ρ.n j) (ρ.sS j) (hρ.n j hj) _).1
    (hA.1.valC j (Nat.le_of_succ_le hj) ψ hψ α a)
  choose F hF1 hF2 using hV
  funext h
  obtain ⟨g', hg', a', k', hk', κ', hκ', rfl⟩ := (hA.1.reps (j + 1) hj γ).dec h
  have hu : IsUni (ρ.r (j + 1) hj k') := (hρ.uni (j + 1) hj).uni ⟨k', hk'⟩
  have hL := fun i α => lift_eq hc hρ ht hA hj hab hψ α γ a' (y i) (P i) ν
    (hcl (c.x j).vol (A.U j α) _ (A.h j α) (hA.1.reps j (Nat.le_of_succ_le hj) α)).2.2 (F α) (hF2 α) hg' ⟨k', hk'⟩ ⟨κ', hκ'⟩
  have hR := fun i => hA.1.rd (j + 1) hj _ (ht.stabK j hj ψ hψ) γ (y'' i) g' hg' a' k' hk' ⟨κ', hκ'⟩ _
    (isTr_trF hu (ρ.fr (j + 1) (y'' i)))
  have hK := fun i => hA.2.2.2.2 j hj hab ψ hψ F hF1 hF2 γ a' (trF hu (ρ.fr (j + 1) (y'' i)))
  simp only at hL hR
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hL, hR, hK]
  rw [Finset.sum_comm]
  conv_rhs =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, hav (F α a) (hF1 α a) (formAt (A.abelian₂ j α γ a a') (ρ.sc j) (ρ.r (j + 1) hj k')), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := prod_det_cancel' (ρ.r (j + 1) hj k') (ρ.fr (j + 1) (y'' i)).1
    (fun τ => ((ρ.fr (j + 1) (y'' i)).2 τ).ne_zero) (ρ.sD j)
  rw [formAt_subY]
  simp only [trF, ← hy i]
  rw [← h1]
  ring

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.ThetaOf

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem exists_symplO_eq (d : HypDec S S₀ ρ) (T : HSp D) {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E} (hξ : ξ ≠ 0)
    (t : AF D.host.F) : ∃ a, symplO S T (d.extX T (rat ξ)) (d.extY T a) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hv : T.gram * ξ ≠ 0 := fun h => hξ (by
    rw [← Matrix.nonsing_inv_mul_cancel_left T.gram ξ (gram_isUnit_det T), h, Matrix.mul_zero])
  obtain ⟨i, j, hij⟩ : ∃ i j, (T.gram * ξ) i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Matrix.ext h)
  let c : AE D := t ⊗ₜ[D.host.F] ((2 * D.host.xi0 * (T.gram * ξ) i j)⁻¹)
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have h := d.hO_ext T (rat ξ) 0 0 (adj (Matrix.single j i c)) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_adj, gA, ← rat_mul,
    Matrix.trace_single_mul, smul_eq_mul]
  have e : incA D D.host.xi0 * (c * rat (T.gram * ξ) i j) = t ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (1 / 2)) := by
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] D.host.xi0) * (c * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (T.gram * ξ) i j)) = _
    simp only [c, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [map_div₀, map_one, map_ofNat]
    field_simp
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem integral_char_eq_zero {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (χ : Mx D m n → ℂ) (hmul : ∀ a b, χ (a + b) = χ a * χ b)
    (hγ : ∀ γ ∈ ratMx D m n, χ γ = 1) {u : Mx D m n} (hu : χ u ≠ 1) : ∫ a in 𝓕, χ a ∂μ = 0 := by
  have h1 := covolOne_integral_add h χ (fun γ hg a => by rw [hmul, hγ γ hg, one_mul]) u
  simp only [hmul, integral_mul_const] at h1
  by_contra h0
  exact hu (mul_left_cancel₀ h0 (h1.trans (mul_one _).symm))

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO_eq_add, GlobalTheory.OrientedHeis.symplOH_add_left]; ring

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO_eq_add, GlobalTheory.OrientedHeis.symplOH_add_right]; ring

theorem continuous_symplO {S T : HSp D} {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplO S T (x t) (y t) := by
  simp only [symplO_eq_add]
  exact (GlobalTheory.OrientedHeis.continuous_symplOH hx hy).add (GlobalTheory.OrientedHeis.continuous_symplOH hx hy)

theorem integral_pair (hψ : IsStdChar D ψ (-1)) (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (h : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E}
    (hξ : ξ ≠ 0) : ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) ∂μ = 0 := by
  obtain ⟨t, ht⟩ := hψ.1.2.2.2
  obtain ⟨u, hu⟩ := exists_symplO_eq d T hξ t
  refine integral_char_eq_zero h _ (fun a b => ?_) (fun γ hγ => ?_) (u := u) (by rw [hu]; exact ht)
  · rw [map_add, symplO_add_right, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T _).2 (ratMx_mul (rat_mem _) (rat_mem _)) _
      (ratMx_mul hγ (rat_mem _))

theorem bound_translates (hψ : IsStdChar D ψ (-1)) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) : Continuous φ ∧ ∀ Q : Set (Mx D m n), IsCompact Q →
      ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨hc, K, hK, hb⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨C, hC⟩ := hb N
  refine ⟨hc, fun Q hQ => ?_⟩
  obtain ⟨b, hs, hb⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hs.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem theta_series (hψ : IsStdChar D ψ (-1)) (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (h : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {φ : Mx D T.rank ρ → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {f : WO S T → ℂ}
    (hf : ∀ w : WO S T, f w = ψ (-(symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (w ⬝ d.jY)))) *
      ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
        ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ)) :
    Continuous f ∧ ∀ x, d.mixS T ψ μ 𝓕 f x 0 = φ x := by
  obtain ⟨hc, hb⟩ := bound_translates hψ hφ
  have hψc : Continuous ψ := hψ.1.1
  have hn : ∀ t, ‖ψ t‖ = 1 := hψ.1.2.1
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hjX : Continuous fun w : WO S T => (w ⬝ d.jX : Mx D T.rank ρ) := continuous_id.matrix_mul continuous_const
  have hjY : Continuous fun w : WO S T => (w ⬝ d.jY : Mx D T.rank ρ) := continuous_id.matrix_mul continuous_const
  constructor
  · obtain ⟨i1, i2, -⟩ := lattice_Mx D T.rank S.rank
    obtain ⟨j1, -⟩ := lattice_Mx D T.rank ρ
    rw [funext hf]
    refine (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp hjX) (hY.comp hjY)).neg).mul ?_
    refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨Q, hQ, hw⟩ := exists_compact_mem_nhds w
    obtain ⟨b, hs, hb⟩ := hb _ (hQ.image hjX)
    refine ContinuousOn.continuousAt (continuousOn_tsum (fun ξ => Continuous.continuousOn ?_) hs fun ξ y hy => ?_) hw
    · exact (hψc.comp (continuous_symplO (hX.comp (hjX.add continuous_const)) (hY.comp hjY))).mul
        (hc.comp (hjX.add continuous_const))
    · rw [norm_mul, hn, one_mul]
      exact hb _ ⟨y, hy, rfl⟩ ξ
  · intro x
    obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D T.rank ρ
    haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
    haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
    haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
    haveI : Countable (Matrix (Fin T.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (_ → _ → D.host.E))
    obtain ⟨b, hs, hb⟩ := hb {x} isCompact_singleton
    have hone : μ.real 𝓕 = 1 := by rw [Measure.real, h.2.2, ENNReal.toReal_one]
    have key : ∀ a, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T 0) f)) 0 =
        ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ) := by
      intro a
      have e1 : ((d.extY T a + d.extX T x : WO S T) ⬝ d.jX : Mx D T.rank ρ) = x := by
        simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pY_jX,
          Matrix.mul_one, Matrix.mul_zero, zero_add]
      have e2 : ((d.extY T a + d.extX T x : WO S T) ⬝ d.jY : Mx D T.rank ρ) = a := by
        simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY, HypDec.pY_jY,
          Matrix.mul_one, Matrix.mul_zero, add_zero]
      rw [d.integrandS_eq, map_zero, add_zero, hf, e1, e2, ← mul_assoc, ← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.extX T), symplO_add_left,
        symplOH_skew S T (d.extX T x), symplO_eq_add S T (d.extX T x)]
      congr 2
      ring
    have hF := hasSum_integral_of_summable_integral_norm (μ := μ.restrict 𝓕)
      (F := fun (ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E) a =>
        ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ)) (fun ξ => ?_) ?_
    · rw [HypDec.mixS]
      simp only [key]
      refine hF.unique ?_
      have h0 : ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat 0)) (d.extY T a)) * φ (x + rat 0) ∂μ = φ x := by
        simp only [rat_zero, map_zero, symplO_eq_add, symplOH_zero_left, add_zero, AddChar.map_zero_eq_one, one_mul,
          setIntegral_const, hone, one_smul]
      rw [← h0]
      refine hasSum_single (f := fun ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
        ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ) ∂μ) 0 fun ξ hξ => ?_
      rw [integral_mul_const, integral_pair hψ d T h hξ, zero_mul]
    · refine Integrable.mul_const (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun a => (hn _).le)) _
      exact (hψc.comp (continuous_symplO continuous_const hY)).measurable.aestronglyMeasurable
    · simp only [norm_mul, hn, one_mul, setIntegral_const, hone, one_smul]
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb x rfl ξ) hs

theorem theta_series_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → Continuous f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 h φ hφ f hf
  obtain ⟨h1, h2⟩ := theta_series hψ (dblDec A) B h hφ hf
  exact ⟨h1, funext h2⟩

end GlobalTheory.Core.Rk.ThetaOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw
variable {D : D7}

theorem t_fd {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (hFD : FiniteDimensional ℂ ((flat c w j s hr).CC c)) :
    FiniteDimensional ℂ (s.CC c) := by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  exact @FiniteDimensional.of_injective ℂ _ _ _ _ _ _ _ ι (Submodule.inclusion_injective hle) hFD

theorem t_met {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (h : ∃ ipD ip, IsMet c (flat c w j s hr) ipD ip) :
    ∃ ipD ip, IsMet c s ipD ip := by
  obtain ⟨ipD, ipF, hm⟩ := h
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ := (ipF.comp ι).compl₂ ι
  have hι : ∀ x : s.CC c, ι x ≠ 0 ↔ x ≠ 0 := fun x => (Submodule.inclusion_injective hle).ne_iff' (map_zero ι)
  exact ⟨ipD, ip, hm.pure, hm.hermD, hm.posD, fun x y => hm.herm (ι x) (ι y),
      fun x hx => hm.pos (ι x) ((hι x).2 hx), fun x y v v' => hm.integ (ι x) (ι y) v v',
      fun x y v v' => hm.schur (ι x) (ι y) v v'⟩

theorem t_van {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0) :
    ∀ (x : s.CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0 := by
  intro x v hv h0
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  by_contra hx
  exact (Submodule.inclusion_injective hle).ne_iff' (map_zero ι) |>.2 hx (h (ι x) v hv h0)

theorem t_par {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c (flat c w j s hr) (PiLocalization₂.val x v) B → IsPar x B) :
    ∀ (x : s.CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c s (PiLocalization₂.val x v) B → IsPar x B := fun x v B hv hP => by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  have h' := h (ι x) v B hv hP
  exact ⟨fun h0 => h'.1 (by rw [h0]; exact map_zero ι), fun v' hv' => h'.2 v' hv'⟩

theorem softQ_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := by
  intro hHC hCR D c w hw j hj s hs
  obtain ⟨hr, hL, hf⟩ := hs
  have hle : s.CC c ≤ (flat c w j s hr).CC c := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw j hj s ⟨hr, hL, hf⟩ hr
  have hMet : MetEx D := GlobalTheory.ChainMetric.metEx hCR D
  have hLev : LevFacts D := LevelFacts.levFacts D
  exact ⟨t_fd hle (finDim_of_levFacts hHC D hLev c hw.com j hj _ hf), t_met hle (hMet c hw.com j hj _ hf),
    t_van hle (val_eq_zero_imp D hMet c hw.com j hj _ hf), t_par hle (GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value hCR D hMet hLev c hw.com j hj _ hf)⟩

example : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := softQ_all

end GlobalTheory.ChainTw
end
end


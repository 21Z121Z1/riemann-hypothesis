import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsEmptyPlacesReferenceTuple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.MeasTuple

theorem one_sub_pos {q : ℝ} (hq : 1 < q) {i : ℕ} (hi : 1 ≤ i) : 0 < 1 - q ^ (-(i : ℤ)) := by
  have : q ^ (-(i : ℤ)) < 1 := zpow_lt_one_of_neg₀ hq (by omega)
  linarith

theorem prod_pos' {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 n, (1 - q ^ (-(i : ℤ))) :=
  Finset.prod_pos fun _ hi => one_sub_pos hq (Finset.mem_Icc.1 hi).1

theorem parIdx_pos {q : ℝ} (hq : 1 < q) (r s : ℕ) : 0 < parIdx q r s := by
  unfold parIdx
  have := prod_pos' hq (r + s); have := prod_pos' hq r; have := prod_pos' hq s
  have : 0 < q := by linarith
  positivity

theorem parIdx_zero {q : ℝ} (hq : 1 < q) (r : ℕ) : parIdx q r 0 = 1 := by
  unfold parIdx
  have := (prod_pos' hq r).ne'
  simp only [mul_zero, pow_zero, add_zero, one_mul]
  rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.prod_empty, mul_one, div_self this]

variable {D : D7}

theorem isEmpty_places_reference_tuple (Z : DivX D) : IsEmpty (Z.QPl D.what₂.mu0) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨p, hp, -⟩ := Z.qv_char _ (Or.inl rfl) v
  rw [Z.degreeZero_partial_set_empty] at hp
  simp at hp

def setMY (X : ThetaX D) (Z : DivX D) : ThetaX D :=
  { X with
    mY := fun μ j => ∏ v : Z.QPl μ, parIdx (Z.qv μ v) D.R.r (j * D.R.t)
    mY_pos := fun μ j => Finset.prod_pos fun v _ => parIdx_pos (by exact_mod_cast Z.qv_gt μ v) _ _
    adelicDataRowMeasureScale_trivialTuple := fun j => by
      haveI := isEmpty_places_reference_tuple Z
      exact Fintype.prod_empty _
    mY_zero := fun μ => Finset.prod_eq_one fun v _ => by
      rw [zero_mul]; exact parIdx_zero (by exact_mod_cast Z.qv_gt μ v) _ }

theorem myTied_setMY (X : ThetaX D) (Z : DivX D) : ThetaDivisorCompatibility (setMY X Z) Z := fun _ _ _ => rfl

def thetaDivisorRestriction {X : ThetaX D} (T : ThetaTied D X) (Z : DivX D) : ThetaTied D (setMY X Z) :=
  { T with }

def rep (Z : DivX D) (n : ℕ) : DivX D :=
  { Z with
    QPl := fun μ => Fin n × Z.QPl μ
    finQ := fun _ => inferInstance
    qv := fun μ v => Z.qv μ v.2
    qv_gt := fun μ v => Z.qv_gt μ v.2
    qv_char := fun μ h v => Z.qv_char μ h v.2
    nu := fun μ v => Z.nu μ v.2
    nu_ne := fun μ v => Z.nu_ne μ v.2
    nu_abs := fun μ v => Z.nu_abs μ v.2
    ZQ := fun μ v => Z.ZQ μ v.2
    quotientLocalValueFirst := fun μ v => Z.quotientLocalValueFirst μ v.2
    typeDim := fun μ v => Z.typeDim μ v.2 }

theorem mY_rep (X : ThetaX D) (Z : DivX D) (n : ℕ) (μ : D.what₂.Tup) (j : ℕ) :
    (setMY X (rep Z n)).mY μ j = (setMY X Z).mY μ j ^ n := by
  change ∏ v : Fin n × Z.QPl μ, parIdx (Z.qv μ v.2) D.R.r (j * D.R.t) =
    (∏ v : Z.QPl μ, parIdx (Z.qv μ v) D.R.r (j * D.R.t)) ^ n
  rw [Fintype.prod_prod_type]
  simp

theorem trivial_factor (X : ThetaX D) (Z : DivX D) :
    ThetaDivisorCompatibility (setMY X (rep Z 0)) (rep Z 0) ∧ (rep Z 0).Qp = Z.Qp ∧ ∀ μ j, (setMY X (rep Z 0)).mY μ j = 1 :=
  ⟨myTied_setMY _ _, rfl, fun μ j => by rw [mY_rep, pow_zero]⟩

open IsDedekindDomain NumberField in

def PlacesTied {X : ThetaX D} (T : ThetaTied D X) (Z : DivX D) : Prop :=
  ∀ μ, ∃ e : Z.QPl μ ↪ HeightOneSpectrum (𝓞 D.host.F), (∀ v, Z.qv μ v = Ideal.absNorm (e v).asIdeal) ∧
    ∀ S, UnramOutside D (T.eChr (X.chrOf μ 1 * (X.chrOf D.what₂.mu0 1)⁻¹)) S ↔ ∀ v, e v ∈ S

end GlobalTheory.MeasTuple

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.TypeAtTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rep
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dRep_char (m : ℤ) (θ : ℝ) (w : ℂ) :
    dRep (n := 1) (fun g => (g 0 0 ^ m) • ContinuousLinearMap.id ℂ ℂ) (diagonal fun _ => (θ : ℂ) * Complex.I) w =
      ((m : ℂ) * θ * Complex.I) * w := by
  have hexp : ∀ s : ℝ, NormedSpace.exp (s • (diagonal fun _ : Fin 1 => (θ : ℂ) * Complex.I)) 0 0 =
      Complex.exp ((s : ℂ) * ((θ : ℂ) * Complex.I)) := by
    intro s
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.diagonal_apply_eq, Pi.exp_def,
      ← Complex.exp_eq_exp_ℂ]
    simp [Complex.real_smul]
  have hd : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * ((m : ℂ) * ((θ : ℂ) * Complex.I))) * w)
      (((m : ℂ) * θ * Complex.I) * w) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * ((m : ℂ) * ((θ : ℂ) * Complex.I)))
        (((1 : ℝ) : ℂ) * ((m : ℂ) * ((θ : ℂ) * Complex.I))) 0 :=
      (hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const _
    refine (h1.cexp.mul_const w).congr_deriv ?_
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, Complex.exp_zero, one_mul]
    ring
  unfold dRep
  refine HasDerivAt.deriv (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, hexp]
  rw [← Complex.exp_int_mul]
  congr 2
  ring

end Rep

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem isTypeAt_zero {τ : D.what₂.Tau} {S : SPar} : IsTypeAt θ V τ S 0 ↔
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ := by
  constructor
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, -⟩
    exact ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
    refine ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, fun x => ⟨fun _ => 0, fun i => ?_, fun _ => 0,
      fun i => ?_, ⟨[], fun _ => 0, by simp, fun i w _ => by simp, fun S' _ => by simp,
        ⟨fun _ => 0, continuous_const, fun g _ w _ => by simp⟩⟩, fun g _ => by simpa using hasSum_zero⟩⟩
    · intro k Xs _
      simp only [map_zero]
      exact contDiff_const
    · exact ⟨[], 0, by simp, fun w _ => by simp⟩

end GlobalTheory.TypeAtTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.SymplHAddRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

namespace GlobalTheory.WeilVacCollapse

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hHom_add_left (V W : HSp D) (x x' y : WA V W) : hHom V W (x + x') y = hHom V W x y + hHom V W x' y := by
  unfold hHom
  split_ifs <;> simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hHom_add_right (V W : HSp D) (x y y' : WA V W) : hHom V W x (y + y') = hHom V W x y + hHom V W x y' := by
  unfold hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  simp only [symplH, sympl, hHom_add_right, mul_add, map_add]

theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  simp only [symplH, sympl, hHom_add_left, mul_add, map_add]

theorem heis_heis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u u' : WA V W) (f : WA V W → ℂ) (w : WA V W) :
    Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W u' f) w = ψ (symplH V W u u') * Heisenberg₂ ψ V W (u + u') f w := by
  simp only [Heisenberg₂, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem eq_zero_of_fixed (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : AddSubgroup (WA V W))
    {u u' : WA V W} (hu : u ∈ L) (hu' : u' ∈ L) (hne : ψ (symplH V W u u') ≠ 1)
    (f : WA V W → ℂ) (hf : ∀ x ∈ L, Heisenberg₂ ψ V W x f = f) : f = 0 := by
  funext w
  have h := heis_heis ψ V W u u' f w
  rw [hf u' hu', hf u hu, hf _ (L.add_mem hu hu')] at h
  have : (ψ (symplH V W u u') - 1) * f w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hne
  · exact h1

theorem unr_void {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) (V W : HSp D)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {u u' : WA V W} (hu : u ∈ latVWS V W S) (hu' : u' ∈ latVWS V W S)
    (hne : Wl.ψ (symplH V W u u') ≠ 1) (Φ : X.Sch V W)
    (hΦ : ∀ x ∈ latVWS V W S, Heisenberg₂ Wl.ψ V W x (Wl.evS V W Φ) = Wl.evS V W Φ) :
    Φ = 0 ∧ ∀ χ χ' (p : GA D V × GA D W), Wl.om V W χ χ' p Φ = Φ := by
  have h0 : Φ = 0 := Wl.evS_inj V W (by
    rw [eq_zero_of_fixed Wl.ψ V W _ hu hu' hne _ hΦ, map_zero])
  exact ⟨h0, fun χ χ' p => by rw [h0, map_zero]⟩

end GlobalTheory.WeilVacCollapse

end
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.SerTransport

open PowerSeries

theorem taylorCoeff_add_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z + G z) n = coef1 F n + coef1 G n := by
  simp only [coef1]
  rw [iteratedDeriv_fun_add hF.contDiff.contDiffAt hG.contDiff.contDiffAt, add_div]

theorem taylorCoeff_mul_entire {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (n : ℕ) :
    coef1 (fun z => F z * G z) n =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, coef1 F q.1 * coef1 G q.2 := by
  simp only [coef1]
  rw [iteratedDeriv_fun_mul hF.contDiff.contDiffAt hG.contDiff.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : ((n.choose i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

theorem taylorCoeff_const_function (c : ℂ) (n : ℕ) : coef1 (fun _ => c) n = if n = 0 then c else 0 := by
  simp only [coef1, iteratedDeriv_const]
  split_ifs with h
  · simp [h]
  · simp

theorem taylorCoeff_zero_eq_value (F : ℂ → ℂ) : coef1 F 0 = F 0 := by simp [coef1]

theorem taylorCoeff_scale_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (β : ℂ) (n : ℕ) :
    coef1 (fun z => F (β * z)) n = β ^ n * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_comp_const_mul hF.contDiff]
  simp [mul_div_assoc]

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem coeff_padicTransportSeries (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (n : ℕ) :
    coeff n (GL3Theta.ser1 lam F) = lamC lam (coef1 F n) := by
  simp [GL3Theta.ser1, coef1]

theorem exists_coef {F : ℂ → ℂ} (hF : AlgEnt F) : ∃ a : ℕ → Qbar, ∀ n, coef1 F n = a n :=
  ⟨fun n => ⟨_, hF.2 n⟩, fun _ => rfl⟩

theorem padicTransportSeries_add (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z + G z) ∧
      GL3Theta.ser1 lam (fun z => F z + G z) = GL3Theta.ser1 lam F + GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z + G z) n = ((a n + b n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_add_entire hF.1 hG.1, ha, hb]; rfl
  refine ⟨⟨hF.1.add hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [map_add, coeff_padicTransportSeries, e, ha, hb, lamC_coe]

theorem padicTransportSeries_mul (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) :
    AlgEnt (fun z => F z * G z) ∧
      GL3Theta.ser1 lam (fun z => F z * G z) = GL3Theta.ser1 lam F * GL3Theta.ser1 lam G := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, hb⟩ := exists_coef hG
  have e : ∀ n, coef1 (fun z => F z * G z) n =
      ((∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, a q.1 * b q.2 : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_mul_entire hF.1 hG.1]
    simp [ha, hb]
  refine ⟨⟨hF.1.mul hG.1, fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [coeff_mul, coeff_padicTransportSeries, e, ha, hb, lamC_coe, map_sum, map_mul]

theorem padicTransportSeries_const (lam : Qbar →+* ℂ_[p]) {c : ℂ} (hc : c ∈ Qbar) :
    AlgEnt (fun _ => c) ∧ GL3Theta.ser1 lam (fun _ => c) = C (lamC lam c) := by
  refine ⟨⟨differentiable_const c, fun n => ?_⟩, ?_⟩
  · rw [taylorCoeff_const_function]
    split_ifs
    exacts [hc, zero_mem _]
  · ext n
    rw [coeff_padicTransportSeries, taylorCoeff_const_function, coeff_C]
    split_ifs
    · rfl
    · exact (lamC_coe lam 0).trans (map_zero lam)

theorem taylorSeriesInParameter_rescale_of_algebraic (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) {β : ℂ} (hβ : β ∈ Qbar) :
    AlgEnt (fun z => F (β * z)) ∧
      GL3Theta.ser1 lam (fun z => F (β * z)) = rescale (lamC lam β) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := exists_coef hF
  obtain ⟨b, rfl⟩ : ∃ b : Qbar, (b : ℂ) = β := ⟨⟨β, hβ⟩, rfl⟩
  have e : ∀ n, coef1 (fun z => F (b * z)) n = ((b ^ n * a n : Qbar) : ℂ) := fun n => by
    rw [taylorCoeff_scale_entire hF.1, ha]
    simp
  refine ⟨⟨hF.1.comp (by fun_prop), fun n => e n ▸ Subtype.property _⟩, ?_⟩
  ext n
  simp only [coeff_rescale, coeff_padicTransportSeries, e, ha, lamC_coe, map_pow, map_mul]

theorem const_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    constantCoeff (f.subst a : PowerSeries ℂ_[p]) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

theorem one_subst {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    coeff 1 (f.subst a : PowerSeries ℂ_[p]) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, const_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

variable (g : GL3Theta.G1 p)

theorem const_l : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_Cl (c : ℂ_[p]) : constantCoeff (C c * g.l) = 0 := by
  rw [map_mul, const_l, mul_zero]

theorem atU_eq (F : ℂ → ℂ) : g.atU F =
    subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l : PowerSeries ℂ_[p]) (GL3Theta.ser1 g.lam F) := rfl

theorem mulBy_X (c : ℂ_[p]) : (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
    subst (C c * g.l : PowerSeries ℂ_[p]) g.ex := by
  have : g.lg (GL3Theta.Xv ()) = g.l := X_subst g.l
  rw [GL3Theta.G1.mulBy, this]
  rfl

theorem transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), (∀ F G : ℂ → ℂ, AlgEnt F → AlgEnt G → (AlgEnt (fun z => F z * G z) ∧ g.atU (fun z => F z * G z) = g.atU F * g.atU G) ∧ (AlgEnt (fun z => F z + G z) ∧ g.atU (fun z => F z + G z) = g.atU F + g.atU G)) ∧ (∀ c ∈ Qbar, AlgEnt (fun _ => c) ∧ g.atU (fun _ => c) = PowerSeries.C (lamC g.lam c)) ∧ (∀ F : ℂ → ℂ, AlgEnt F → F 0 ∈ Qbar ∧ PowerSeries.constantCoeff (g.atU F) = lamC g.lam (F 0)) ∧ (g.Ok → ∀ β ∈ Qbar, ∃ h : PowerSeries ℂ_[p], h = (g.mulBy (lamC g.lam β) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧ PowerSeries.constantCoeff h = 0 ∧ PowerSeries.coeff 1 h = lamC g.lam β ∧ ∀ F : ℂ → ℂ, AlgEnt F → AlgEnt (fun z => F (β * z)) ∧ g.atU (fun z => F (β * z)) = PowerSeries.subst h (g.atU F)) := by
  intro p _ g
  have hs := HasSubst.of_constantCoeff_zero' (const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  refine ⟨fun F G hF hG => ⟨⟨(padicTransportSeries_mul g.lam hF hG).1, ?_⟩, (padicTransportSeries_add g.lam hF hG).1, ?_⟩,
    fun c hc => ⟨(padicTransportSeries_const g.lam hc).1, ?_⟩, fun F hF => ⟨taylorCoeff_zero_eq_value F ▸ hF.2 0, ?_⟩, fun hg β hβ => ?_⟩
  · simp only [atU_eq, (padicTransportSeries_mul g.lam hF hG).2, subst_mul hs]
  · simp only [atU_eq, (padicTransportSeries_add g.lam hF hG).2, subst_add hs]
  · rw [atU_eq, (padicTransportSeries_const g.lam hc).2, subst_C]; rfl
  · rw [atU_eq, const_subst (const_Cl g _), ← coeff_zero_eq_constantCoeff_apply, coeff_padicTransportSeries, taylorCoeff_zero_eq_value]
  · set b := lamC g.lam β with hb
    have hbl := HasSubst.of_constantCoeff_zero' (const_Cl g b)
    have he := HasSubst.of_constantCoeff_zero' hg.2.2.1
    have h0 : constantCoeff (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) = 0 := by
      rw [const_subst (const_Cl g b), hg.2.2.1]
    have hh := HasSubst.of_constantCoeff_zero' h0
    refine ⟨subst (C b * g.l : PowerSeries ℂ_[p]) g.ex, (mulBy_X g b).symm, h0, ?_, fun F hF =>
      ⟨(taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).1, ?_⟩⟩
    · have e := congrArg (coeff 1) hg.2.2.2
      rw [one_subst hg.2.2.1, coeff_one_X] at e
      rw [one_subst (const_Cl g b), coeff_C_mul]
      linear_combination b * e
    · have e : subst (subst (C b * g.l : PowerSeries ℂ_[p]) g.ex : PowerSeries ℂ_[p]) g.l = C b * g.l := by
        rw [← subst_comp_subst_apply he hbl, hg.2.2.2, subst_X hbl]
      rw [atU_eq, atU_eq, (taylorSeriesInParameter_rescale_of_algebraic g.lam hF hβ).2, rescale_eq_subst,
        subst_comp_subst_apply (HasSubst.smul_X' _) hs, subst_comp_subst_apply hs hh,
        subst_smul hs, subst_X hs, subst_mul hh, e, subst_C]
      congr 1
      rw [smul_eq_C_mul]
      exact mul_left_comm _ _ _

end GlobalTheory.SerTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaLatImage

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem pt_apply (z : Matrix (Fin N') (Fin N) D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_zero : pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt_apply]

theorem pt_add (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt_apply, mul_add]

theorem pt_neg (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt_apply]

theorem pt_smulK (c : D.host.K) (A : Matrix (Fin N') (Fin N) D.host.E) :
    (δ * D.host.φ₀ (c : D.host.E)) • embV D (tor0 D cc δ) A =
      pt D (tor0 D cc δ) δ ((c : D.host.E) • A) := by
  funext τ i j
  change (δ * D.host.φ₀ (c : D.host.E)) * embT D τ (A i j) = δ * embT D τ ((c : D.host.E) * A i j)
  rw [map_mul, (GlobalTheory.InducedType.induced_type D).1.1 τ c, mul_assoc]

theorem pt_injective (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  rw [pt_apply, pt_apply] at h1
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem mem_homL {L : Lat D N} {L' : Lat D N'} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ homL D L L' ↔ ∀ x ∈ L, A.mulVec x ∈ L' := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; rw [Matrix.zero_mulVec]; exact L'.zero_mem
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul o A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem o (hA x hx)

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ i, IntE D (x i) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one, IntE, RingHom.mem_range]

theorem smul_mem_RL {L : Lat D N} {L' : Lat D N'} {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L') :
    ((c : D.host.K) : D.host.E) • A ∈ RL D cc L L' := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, ha, B, hB, rfl⟩ := hA
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, a, ha, rfl⟩, B, hB, smul_smul _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [smul_add]; exact Submodule.add_mem _ hA hB
  | smul o A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ o hA

theorem La_sub {L : Lat D N} {L' : Lat D N'} {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L') :
    ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨_, smul_mem_RL hc hA, pt_smulK _ _⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by rw [zero_smul, pt_zero]⟩
    | add w w' _ _ h h' =>
      obtain ⟨z, hz, e⟩ := h
      obtain ⟨z', hz', e'⟩ := h'
      exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [add_smul, e, e', pt_add]⟩
    | neg w _ h =>
      obtain ⟨z, hz, e⟩ := h
      exact ⟨-z, Submodule.neg_mem _ hz, by rw [neg_smul, e, pt_neg]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, pt_zero.symm⟩
  | add w w' _ _ h h' =>
    obtain ⟨z, hz, e⟩ := h
    obtain ⟨z', hz', e'⟩ := h'
    exact ⟨z + z', Submodule.add_mem _ hz hz', by rw [e, e', pt_add]⟩
  | neg w _ h =>
    obtain ⟨z, hz, e⟩ := h
    exact ⟨-z, Submodule.neg_mem _ hz, by rw [e, pt_neg]⟩

theorem pt_mem_La {L : Lat D N} {L' : Lat D N'} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ RL D cc L L') (o : 𝓞 D.host.E) :
    pt D (tor0 D cc δ) δ (o • z) ∈ La D (tor0 D cc δ) L L' := by
  induction hz using Submodule.span_induction generalizing o with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    induction ht using Submodule.span_induction generalizing o with
    | mem t ht =>
      obtain ⟨c, hc, a, ha, rfl⟩ := ht
      rw [mul_smul, smul_comm, ← pt_smulK]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, _,
        Submodule.smul_mem _ o (Submodule.subset_span ⟨a, ha, A, hA, rfl⟩), rfl⟩
    | zero => rw [zero_smul, smul_zero, pt_zero]; exact zero_mem _
    | add t t' _ _ h h' => rw [add_smul, smul_add, pt_add]; exact add_mem (h o) (h' o)
    | smul o' t _ h => rw [smul_assoc, smul_smul]; exact h _
  | zero => rw [smul_zero, pt_zero]; exact zero_mem _
  | add t t' _ _ h h' => rw [smul_add, pt_add]; exact add_mem (h o) (h' o)
  | smul o' t _ h => rw [smul_smul]; exact h _

def colM (D : D7) {N N' : ℕ} (j : Fin N) :
    (Fin N' → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun i k => if k = j then v i else 0
  map_add' v w := by ext i k; by_cases h : k = j <;> simp [h]
  map_smul' a v := by ext i k; by_cases h : k = j <;> simp [h]

def rowM (D : D7) {N N' : ℕ} (i : Fin N') :
    (Fin N → D.host.E) →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun v := Matrix.of fun k j => if k = i then v j else 0
  map_add' v w := by ext k j; by_cases h : k = i <;> simp [h]
  map_smul' a v := by ext k j; by_cases h : k = i <;> simp [h]

theorem map_span_mem {M M' : Type} [AddCommGroup M] [Module D.host.E M] [Module (𝓞 D.host.E) M]
    [IsScalarTower (𝓞 D.host.E) D.host.E M] [AddCommGroup M'] [Module D.host.E M']
    [Module (𝓞 D.host.E) M'] [IsScalarTower (𝓞 D.host.E) D.host.E M'] (f : M →ₗ[D.host.E] M')
    {S : Set M} {S' : Set M'} (h : ∀ x ∈ S, f x ∈ S') {x : M}
    (hx : x ∈ Submodule.span (𝓞 D.host.E) S) : f x ∈ Submodule.span (𝓞 D.host.E) S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul o x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o hx

theorem mem_RL_cols (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈
      Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y} := by
  constructor
  · intro hz j
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N' → D.host.E) :=
      { toFun := fun z i => z i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, f A, ?_, map_smul _ _ _⟩
    have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ stdL D N := by
      refine mem_stdL.2 fun i => ?_
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h2 := mem_homL.1 hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · intro h
    have e : z = ∑ j, colM D j (fun i => z i j) := by
      ext i k
      simp [colM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun j _ => map_span_mem (colM D j) ?_ (h j)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, colM D j y, mem_homL.2 fun x hx => ?_, map_smul _ _ _⟩
    obtain ⟨o, ho⟩ := mem_stdL.1 hx j
    have : (colM D j y).mulVec x = o • y := by
      funext i
      simp [colM, Matrix.mulVec, dotProduct, ← ho, Algebra.smul_def, mul_comm]
    rw [this]
    exact L'.smul_mem o hy

theorem mem_RL_rows (L : Lat D N) (hL : SD D L) (z : Matrix (Fin N') (Fin N) D.host.E) :
    z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E)
      {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  have hs := ((sd_iff D L).1 hL).2.2
  constructor
  · intro hz i
    let f : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] (Fin N → D.host.E) :=
      { toFun := fun z => z i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine map_span_mem f ?_ hz
    rintro _ ⟨t, ht, A, hA, rfl⟩
    refine ⟨t, ht, fun j => D.host.conj (A i j), (hs _).2 fun x hx => ?_, ?_⟩
    · have h2 := (mem_stdL.1 (mem_homL.1 hA x hx) i).conj
      have e : hE D (fun j => D.host.conj (A i j)) x = D.host.conj (A.mulVec x i) := by
        simp only [hE, Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e]; exact h2
    · simp only [conj_conj]; rfl
  · intro h
    have e : z = ∑ i, rowM D i (z i) := by
      ext i k
      simp [rowM, Matrix.sum_apply]
    rw [e]
    refine Submodule.sum_mem _ fun i _ => map_span_mem (rowM D i) ?_ (h i)
    rintro _ ⟨t, ht, y, hy, rfl⟩
    refine ⟨t, ht, rowM D i _, mem_homL.2 fun x hx => mem_stdL.2 fun k => ?_, map_smul _ _ _⟩
    by_cases hk : k = i
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = hE D x y := by
        simp [rowM, Matrix.mulVec, dotProduct, hk, hE, mul_comm]
      rw [e]; exact (hs x).1 hx y hy
    · have e : (rowM D i fun j => D.host.conj (y j)).mulVec x k = 0 := by
        simp [rowM, Matrix.mulVec, dotProduct, hk]
      rw [e]; exact zero_mem _

theorem theta_lattice_image : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), δ ≠ 0 → ∀ (N N' : ℕ), Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') ∧ (∀ (L : Lat D N) (L' : Lat D N') (x : VC D N N'), x ∈ La D (tor0 D cc δ) L L' ↔ ∃ z ∈ RL D cc L L', x = pt D (tor0 D cc δ) δ z) ∧ (∀ (L' : Lat D N') (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc (stdL D N) L' ↔ ∀ j, (fun i => z i j) ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L', v = t • y}) ∧ ∀ (L : Lat D N), SD D L → ∀ (z : Matrix (Fin N') (Fin N) D.host.E), z ∈ RL D cc L (stdL D N') ↔ ∀ i, z i ∈ Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} := by
  intro D cc δ hδ N N'
  refine ⟨pt_injective hδ, fun L L' x => ⟨La_sub, ?_⟩, mem_RL_cols, mem_RL_rows⟩
  rintro ⟨z, hz, rfl⟩
  simpa using pt_mem_La (δ := δ) hz 1

end GlobalTheory.ThetaLatImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZero
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.ThetaTranslateCoef

theorem sum_trivial_char_eq_zero {G ι : Type} [Monoid G] [Fintype ι] (κ : ι → (G →* ℂ)) (c : ι → ℂ)
    (h : ∀ y, ∑ i, c i * κ i y = 0) : ∑ i, (if κ i = 1 then c i else 0) = 0 := by
  have li := linearIndependent_monoidHom G ℂ
  rw [linearIndependent_iff] at li
  have h0 := li (∑ i, Finsupp.single (κ i) (c i)) (by
    rw [map_sum]
    funext y
    simp only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h y)
  have h1 := congrArg (fun l : (G →* ℂ) →₀ ℂ => l 1) h0
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by congr

def kap (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) (z : VC D N N') :
    Multiplicative A →* ℂ where
  toFun y := bc D T ((Multiplicative.toAdd y : A) : VC D N N') z / bc D T z ((Multiplicative.toAdd y : A) : VC D N N')
  map_one' := by
    simp only [toAdd_one, ZeroMemClass.coe_zero, bc_zero_left, bc_zero_right, div_one]
  map_mul' x y := by
    simp only [toAdd_mul, AddMemClass.coe_add, bc_add_left, bc_add_right, mul_div_mul_comm]

theorem kap_eq_one_iff {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (z : VC D N N') : kap D T A z = 1 ↔ z ∈ A := by
  constructor
  · intro hk
    refine h.2.2 z fun y hy => ?_
    have := DFunLike.congr_fun hk (Multiplicative.ofAdd (⟨y, hy⟩ : A))
    change bc D T y z / bc D T z y = 1 at this
    exact ((div_eq_one_iff_eq (bc_ne_zero D T z y)).1 this).symm
  · intro hz
    refine MonoidHom.ext fun y => ?_
    change bc D T _ z / bc D T z _ = 1
    rw [h.2.1 _ (Multiplicative.toAdd y).2 z hz, h.2.1 z hz _ (Multiplicative.toAdd y).2, div_one]

theorem Wd_Wd_fixed (D : D7) (T : Tor D) {N N' : ℕ} (y z : VC D N N') (e : VC D N N' → ℂ)
    (he : Wd D T y e = e) : Wd D T y (Wd D T z e) = (bc D T y z / bc D T z y) • Wd D T z e := by
  have h1 := Wd_Wd D T z y e
  rw [he, add_comm] at h1
  rw [Wd_Wd]
  conv_rhs => rw [h1]
  rw [smul_smul, div_mul_cancel₀ _ (bc_ne_zero D T z y)]

def WdL (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T y
  map_add' := Wd_add D T y
  map_smul' := Wd_smul D T y

theorem coef_eq_zero : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), Nice D T A →
    ∀ e ∈ ThSp D T A, e ≠ 0 → ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (z : ι → VC D N N'),
      (∀ v, ∑ i, a i * Wd D T (z i) e v = 0) → ∑ i, (if z i ∈ A then a i else 0) = 0 := by
  intro D T N N' A hA e he hne ι _ a z hrel
  have hfix := ((hA.mem_ThSp e).1 he).2
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hsum : ∑ i, a i • Wd D T (z i) e = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hrel w
  have key := sum_trivial_char_eq_zero (fun i => kap D T A (z i)) (fun i => a i * Wd D T (z i) e v) (by
    intro y
    have h1 := congrArg (WdL D T ((Multiplicative.toAdd y : A) : VC D N N')) hsum
    rw [map_sum, map_zero] at h1
    have h2 := congrFun h1 v
    rw [Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change _ = a i * Wd D T _ (Wd D T (z i) e) v
    rw [Wd_Wd_fixed D T _ _ e (hfix _ (Multiplicative.toAdd y).2)]
    change a i * Wd D T (z i) e v * (bc D T _ _ / bc D T _ _) = a i * ((bc D T _ _ / bc D T _ _) * Wd D T (z i) e v)
    ring)
  have h3 : (∑ i, (if z i ∈ A then a i else 0)) * e v = 0 := by
    refine Eq.trans ?_ key
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hz : z i ∈ A
    · rw [if_pos hz, if_pos ((kap_eq_one_iff hA _).2 hz), hfix _ hz]
    · rw [if_neg hz, if_neg (fun h => hz ((kap_eq_one_iff hA _).1 h)), zero_mul]
  exact (mul_eq_zero.1 h3).resolve_right hv

end GlobalTheory.ThetaTranslateCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryFiniteGaussSumPhaseRootOfUnityStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_finite_gaussSum_phase_rootOfUnity : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsPosHerm H → ∀ (a : V ≃ₗ[ℂ] V), (∀ z w, H (a z) (a w) = H z w) → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → (∀ x, B (x - a x) = x) → ∀ (Λ Λ' : AddSubgroup V), Λ.FG → Λ' ≤ Λ → (Λ'.addSubgroupOf Λ).FiniteIndex → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∃ (M : Type) (_ : Fintype M) (s : M → V), (∀ m, s m ∈ Λ) ∧ (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) ∧ GlobalTheory.Phase.Ph (∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ))) := by
  first | exact @GlobalTheory.UnitaryTheta.GaussPhase.gauss_phase | exact GlobalTheory.UnitaryTheta.GaussPhase.gauss_phase | (intros; apply GlobalTheory.UnitaryTheta.GaussPhase.gauss_phase <;> assumption)
end


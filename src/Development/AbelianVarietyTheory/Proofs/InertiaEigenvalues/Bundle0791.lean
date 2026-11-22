import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedEntriesIntegral
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrimeLat

variable {E : Type} [Field E] [NumberField E]

theorem val_intMul_le_one (c : 𝓞 E) (z : FiniteAdeleRing (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E))
    (hz : Valued.v (z Q) ≤ 1) :
    Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) * z) Q) ≤ 1 := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, Valuation.map_mul, ← hev, ← hev]
  refine mul_le_one' ?_ hz
  exact (GlobalTheory.CharLocProd.val_algebraMap Q (c : E)).trans_le (Q.valuation_le_one c)

theorem val_smul_mulVec_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (m : ℕ)
    (hM : ∀ i j (Q : HeightOneSpectrum (𝓞 E)), Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * M i j)) Q) ≤ 1)
    (y : Fin n → FiniteAdeleRing (𝓞 E) E) (hy : ∀ j (Q : HeightOneSpectrum (𝓞 E)), Valued.v (y j Q) ≤ 1)
    (c : 𝓞 E) (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E)) * (m : FiniteAdeleRing (𝓞 E) E)) •
      (M *ᵥ y)) i Q) ≤ 1 := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have e : (((algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E)) * (m : FiniteAdeleRing (𝓞 E) E)) • (M *ᵥ y)) i =
      ∑ j, algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) * (((m : FiniteAdeleRing (𝓞 E) E) * M i j) * y j) := by
    rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, hev, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← hev]
  refine val_intMul_le_one c _ Q ?_
  rw [hev, map_mul, Valuation.map_mul, ← hev, ← hev]
  exact mul_le_one' (hM i j Q) (hy j Q)

end GlobalTheory.StdAtPrimeLat

open GlobalTheory.StdAtPrimeLat in

theorem GlobalTheory.StdAtPrimeLat.trivAt_hLat_of_bnd : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (p : ℕ) (g : Bridge.Gf V), Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 → Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 → (⟨Bridge.hLat V g⟩ : GenLat D.host.E V.rank).TrivAt p := by
  intro D ι h1 h2 V hL p g hA hB
  obtain ⟨m₁, hm₁, hA⟩ := hA
  obtain ⟨m₂, hm₂, hB⟩ := hB
  set A := (Matrix.GeneralLinearGroup.map ι.toRingHom g.1).1 with hAdef
  set B := (Matrix.GeneralLinearGroup.map ι.toRingHom g.1)⁻¹.1 with hBdef
  have hAB : A * B = 1 := Units.mul_inv _
  have memH := fun x => GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL g x
  have memS : ∀ x : Fin V.rank → D.host.E, x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank ↔
      ∀ i Q, Valued.v ((fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i Q) ≤ 1 := by
    intro x
    rw [← hL, GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL 1 x]
    simp
  have hsm : ∀ (r : 𝓞 D.host.E) (x : Fin V.rank → D.host.E),
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((r • x) j)) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (r : D.host.E) •
          fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j) :=
    fun r x => funext fun j => map_mul _ (r : D.host.E) (x j)
  refine ⟨m₁ * m₂, Nat.Coprime.mul hm₁ hm₂, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [memS, hsm]
    rw [memH] at hx
    have ex : (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) =
        A *ᵥ (B *ᵥ fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) := by
      rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    have ec : algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * ((m₁ * m₂ : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * (m₂ : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) *
          (m₁ : FiniteAdeleRing (𝓞 D.host.E) D.host.E) := by
      push_cast
      ring
    intro i Q
    rw [ec, ex]
    exact val_smul_mulVec_le_one A m₁ hA _ hx _ i Q
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [memH, hsm]
    rw [memS] at hx
    have ec : algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * ((m₁ * m₂ : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((a * (m₁ : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) *
          (m₂ : FiniteAdeleRing (𝓞 D.host.E) D.host.E) := by
      push_cast
      ring
    intro i Q
    rw [ec, Matrix.mulVec_smul]
    exact val_smul_mulVec_le_one B m₂ hB _ hx _ i Q
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem mspanR_rt {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_kerOp {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    kerOp ν k γ F ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk

theorem word_nil (φ : Sm E a) : GlobalTheory.GLFin.word [] φ = φ := by simp [GlobalTheory.GLFin.word]

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by simp [GlobalTheory.GLFin.word]

theorem word_append (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.map_append, List.prod_append]

theorem word_single (X : Lie E a) (φ : Sm E a) : GlobalTheory.GLFin.word [X] φ = lie E a X φ := by simp [GlobalTheory.GLFin.word]

def adH (h : GA E a) (X : Lie E a) : Lie E a :=
  toL ((GeneralLinearGroup.map (pInf E) h)⁻¹.val * Matrix.of X * (GeneralLinearGroup.map (pInf E) h).val)

theorem lie_rt (h : GA E a) (X : Lie E a) (φ : Sm E a) :
    lie E a X (rt E a h φ) = rt E a h (lie E a (adH h X) φ) := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have eh : h = infGL E a y * finGL E a k := (infGL_mul_finGL h).symm
  have e1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e2 : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e2] at e1
  have e3 := lie_rt_fin (adH h X) k
  have key : lie E a X * rt E a h = rt E a h * lie E a (adH h X) := by
    have e4 : rt E a h = rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [← map_mul, ← eh]
    rw [e4, ← mul_assoc, ← e1, mul_assoc]
    change _ * (lie E a (adH h X) * _) = _
    rw [e3, ← mul_assoc]
  exact LinearMap.congr_fun key φ

theorem word_rt (h : GA E a) : ∀ (l : List (Lie E a)) (φ : Sm E a),
    GlobalTheory.GLFin.word l (rt E a h φ) = rt E a h (GlobalTheory.GLFin.word (l.map (adH h)) φ)
  | [], φ => by simp [GlobalTheory.GLFin.word]
  | X :: l, φ => by rw [word_cons, word_rt h l, lie_rt, List.map_cons, word_cons]

variable (E a) in

def bccSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsBCC F}
  zero_mem' := (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).1
  add_mem' {F G} hF hG := by simpa using (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).2 1 F G hF hG
  smul_mem' c F hF := by simpa using (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).2 c F 0 hF (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).1

def dSub (π : CuspSub E a) : Submodule ℂ (Sm E a) :=
  ⨅ l : List (Lie E a), (mspanR π ⊓ bccSub E a).comap ((Sm E a).subtype ∘ₗ GlobalTheory.GLFin.word l)

theorem mem_dSub {π : CuspSub E a} {φ : Sm E a} :
    φ ∈ dSub π ↔ ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  simp only [dSub, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_inf, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rfl

theorem lie_mem_dSub {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ dSub π) (X : Lie E a) : lie E a X φ ∈ dSub π :=
  mem_dSub.2 fun l => by rw [← word_append]; exact mem_dSub.1 h _

theorem isBCC_rt {F : GA E a → ℂ} (hF : IsBCC F) (h : GA E a) : IsBCC (fun g => F (g * h)) where
  cont := hF.cont.comp (continuous_mul_right h)
  bdd := let ⟨C, hC⟩ := hF.bdd; ⟨C, fun g => hC _⟩
  cusp := by
    intro r h0 h1 _ _ μ 𝓕 hμ hF' g
    simpa only [mul_assoc] using hF.cusp r h0 h1 μ 𝓕 hμ hF' (g * h)
  left γ g := by simpa only [mul_assoc] using hF.left γ (g * h)

theorem rt_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) (h : GA E a) : rt E a h φ ∈ dSub π :=
  mem_dSub.2 fun l => by
    rw [word_rt]
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ (l.map (adH h))
    exact ⟨mspanR_rt h1 h, isBCC_rt h2 h⟩

theorem isBCC_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : IsBCC φ.1 where
  cont := (π.cusp φ h).1.continuous
  bdd := hB.of_isUnitary hπ h
  cusp := (π.cusp φ h).2
  left := (π.cusp φ h).1.left

theorem word_mem (π : CuspSub E a) : ∀ (l : List (Lie E a)) {φ : Sm E a}, φ ∈ π.V → GlobalTheory.GLFin.word l φ ∈ π.V
  | [], _, h => by rw [word_nil]; exact h
  | X :: l, _, h => by rw [word_cons]; exact π.stable (.lie X) _ (word_mem π l h)

theorem mem_dSub_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : φ ∈ dSub π :=
  mem_dSub.2 fun l => ⟨mem_mspanR_of_mem (word_mem π l h), isBCC_of_mem hB hπ (word_mem π l h)⟩

theorem isBCC_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : IsBCC φ.1) :
    IsBCC (kerOp ν k γ φ.1) where
  cont := (GlobalTheory.T.kernelOperator_integrable_continuous_smooth E a X ν k γ hk φ hφ.cont hφ.bdd).2
  bdd := by
    obtain ⟨C, hC⟩ := hφ.bdd
    have hi : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
    refine ⟨C * ∫ x, ‖k x‖ ∂ν, fun g => ?_⟩
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  cusp := GlobalTheory.T.isCuspidal_archimedeanKernelConvolutionOperator E a X ν k γ hk φ hφ
  left γ' g := by simp only [kerOp, mul_assoc, hφ.left]

theorem hasFDerivAt_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (hk : IsRapidInf ν k γ) (φ : Sm E a) (hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2)
      (oneL E a) := by
  rw [← GlobalTheory.T.integral_fderiv_realLieChart_eq_sum_kernelOperators E a X ν k γ hk φ hd g]
  exact GlobalTheory.T.hasFDerivAt_realLieChart_kernelOperator_at_one E a X ν k γ hk φ hb hd g

theorem kerOp_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    ∃ ψ ∈ dSub π, ψ.1 = kerOp ν k γ φ.1 := by
  let K : Set (GA E a → ℂ) := {f | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (φ : Sm E a), IsRapidInf ν k γ ∧ φ ∈ dSub π ∧ f = kerOp ν k γ φ.1}
  have hder : ∀ f ∈ K, ∃ fs : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a)) → GA E a → ℂ,
      (∀ p, fs p ∈ K) ∧ ∀ g, HasFDerivAt (chart f g) (∑ p, fs p g • lieCoord E a p.2) (oneL E a) := by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    have hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by simpa [word_nil] using (mem_dSub.1 hφ []).2.bdd
    have hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C := fun i => by
      simpa [word_single] using (mem_dSub.1 hφ [lieBasis E a i]).2.bdd
    exact ⟨fun p => kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1,
      fun p => ⟨X, _, ν, inferInstance, _, γ, _, GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient E a X ν k γ hk p, lie_mem_dSub hφ _, rfl⟩,
      hasFDerivAt_kerOp ν k γ hk φ hb hd⟩
  have hSm : ∀ f ∈ K, f ∈ Sm E a := GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity E a K fun f hf => by
    obtain ⟨fs, h1, h2⟩ := hder f hf
    exact ⟨_, inferInstance, fs, fun p => lieCoord E a p.2, h1, h2⟩
  have hspan : Submodule.span ℂ K ≤ Sm E a := Submodule.span_le.2 hSm
  have hlie : ∀ f ∈ Submodule.span ℂ K, ∀ (h : f ∈ Sm E a) (Y : Lie E a),
      (lie E a Y ⟨f, h⟩).1 ∈ Submodule.span ℂ K := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      intro h Y
      obtain ⟨fs, h1, h2⟩ := hder f hf
      have e : (lie E a Y ⟨f, h⟩).1 = ∑ p, (lieCoord E a p.2 Y) • fs p := by
        funext g
        rw [CuspRep.lie_apply, lieD, (h2 g).fderiv]
        simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
          smul_eq_mul, mul_comm]
      rw [e]
      exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (h1 p))
    | zero =>
      intro h Y
      have : (⟨0, h⟩ : Sm E a) = 0 := rfl
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | add f f' hf hf' ihf ihf' =>
      intro h Y
      have : (⟨f + f', h⟩ : Sm E a) = ⟨f, hspan hf⟩ + ⟨f', hspan hf'⟩ := rfl
      rw [this, map_add]
      exact Submodule.add_mem _ (ihf _ Y) (ihf' _ Y)
    | smul c f hf ihf =>
      intro h Y
      have : (⟨c • f, h⟩ : Sm E a) = c • ⟨f, hspan hf⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem _ c (ihf _ Y)
  have hword : ∀ (l : List (Lie E a)) (ψ : Sm E a), ψ.1 ∈ Submodule.span ℂ K →
      (GlobalTheory.GLFin.word l ψ).1 ∈ Submodule.span ℂ K := by
    intro l
    induction l with
    | nil => intro ψ h; rwa [word_nil]
    | cons Y l ih => intro ψ h; rw [word_cons]; exact hlie _ (ih ψ h) _ Y
  have hgood : Submodule.span ℂ K ≤ mspanR π ⊓ bccSub E a := Submodule.span_le.2 (by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ []
    rw [word_nil] at h1 h2
    exact ⟨mspanR_kerOp h1 ν k γ hk, isBCC_kerOp ν k γ hk φ h2⟩)
  have hmem : kerOp ν k γ φ.1 ∈ K := ⟨X, _, ν, inferInstance, k, γ, φ, hk, hφ, rfl⟩
  exact ⟨⟨_, hSm _ hmem⟩, mem_dSub.2 fun l => hgood (hword l _ (Submodule.subset_span hmem)), rfl⟩

theorem mspanR_le (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    mspanR π ≤ (dSub π).map (Sm E a).subtype := by
  refine sInf_le ⟨fun φ hφ => ⟨φ, mem_dSub_of_mem hB hπ hφ, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩ h
    exact ⟨rt E a h φ, rt_mem_dSub hφ h, rfl⟩
  · rintro _ ⟨φ, hφ, rfl⟩ X _ ν _ k γ hk
    obtain ⟨ψ, h1, h2⟩ := kerOp_mem_dSub hφ ν k γ hk
    exact ⟨ψ, h1, h2⟩

theorem mspanR_words (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  intro F hF
  obtain ⟨φ, hφ, rfl⟩ := mspanR_le hB hπ hF
  exact ⟨φ, rfl, mem_dSub.1 hφ⟩

theorem mspanR_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    GlobalTheory.Published.CuspFormsBoundedGL → ∀ π : CuspSub E a, π.IsUnitary → ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      (∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  intro E _ _ _ a hB π hπ F hF
  obtain ⟨φ, rfl, h⟩ := mspanR_words hB hπ F hF
  have h0 := (h []).2
  rw [word_nil] at h0
  exact ⟨φ, rfl, fun l => (h l).1, h0.cusp, h0.bdd⟩

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstantIntegralArcFrames
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts
  GlobalTheory.GoodTransfer

namespace GlobalTheory.ArcFrame

open Matrix GlobalTheory.LieEigen MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem iwasawa_lower {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (L : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ (∀ i j, i < j → L i j = 0) ∧
      (∀ i, L i i ≠ 0) ∧ A = L * k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, e⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) Aᵀ (by rwa [det_transpose])
  refine ⟨kᵀ, Uᵀ, by rwa [det_transpose], fun i j h => hU h, hd, ?_⟩
  rw [← transpose_transpose A, e, transpose_mul, transpose_map]

section Lie

variable {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] (act : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem eig_prodPts (hv : ∀ i, IsTangent (v i)) (x : O) (s : R)
    (he : ∀ i, (v i ≫ act.act x).left = spMap (epsScaleR s) ≫ (v i).left) (c : Fin n → R) :
    (prodPts c v ≫ act.act x).left = spMap (epsScaleR s) ≫ (prodPts c v).left := by
  have := act.hom x
  have e : prodPts c v ≫ act.act x = prodPts c fun i => v i ≫ act.act x := by
    refine (map_list_prod (IsMonHom.monoidHom (act.act x) _) _).trans ?_
    rw [prodPts, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Category.assoc _ (v i) (act.act x))
  have e₁ : ∀ i, v i ≫ act.act x = prodPts (s • Pi.single i 1) v := fun i => by
    rw [prodPts_smul, ← (Chart.isLieComb_iff _ _ _).1 (IntModelExists.isLieComb_single hv i)]
    exact Over.OverMorphism.ext (he i)
  have e₂ : ∑ i, c i • (s • Pi.single i (1 : R) : Fin n → R) = s • c := by
    ext j; simp [Pi.single_apply, mul_comm]
  rw [e, funext e₁, prodPts_prodPts hv, e₂, prodPts_smul]
  rfl

omit [IsLocalRing R] [Smooth G.hom] in

theorem existsUnique_change (hv : ∀ i, IsTangent (v i)) (k : Matrix (Fin n) (Fin n) R) (hk : IsUnit k.det)
    {w : epsR R ⟶ G} (h : ∃! cf : Fin n → R, IsLieComb cf v w) :
    ∃! cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w := by
  have key : ∀ cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w ↔ IsLieComb (cf ᵥ* k) v w := fun cf => by
    rw [Chart.isLieComb_iff, Chart.isLieComb_iff, vecMul_eq_sum]
    exact Eq.congr_right (prodPts_prodPts hv cf fun i => k i)
  obtain ⟨d, hd, hu⟩ := h
  refine ⟨d ᵥ* k⁻¹, (key _).2 ?_, fun cf hcf => ?_⟩
  · rwa [vecMul_vecMul, nonsing_inv_mul _ hk, vecMul_one]
  · rw [← hu _ ((key _).1 hcf), vecMul_vecMul, mul_nonsing_inv _ hk, vecMul_one]

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem arcBasis_change (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)
    (hk : ∀ τ, IsUnit (k τ).det) (he : ∀ τ i, GtComb (k τ i) (e τ) (e' τ i)) :
    ArcBasis W ρ e' ∧ ∀ τ i, GtTanR (e' τ i) := by
  obtain ⟨v, hi, hb⟩ := h
  have := W.t.semi.smooth
  let k' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (PowerSeries A) :=
    fun τ => (k τ).map (PowerSeries.C (R := A))
  have hk' : ∀ τ, IsUnit (k' τ).det := fun τ => by
    have := (hk τ).map (PowerSeries.C (R := A))
    rwa [RingHom.map_det] at this
  have ht : ∀ τ i, IsTangent (v τ i) := fun τ i => ((hb τ).1 i).1
  have img : ∀ τ i, LieImg W (e' τ i) (prodPts (k' τ i) (v τ)) := fun τ i =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ _ (e τ) _ (v τ) _ (hi τ) (he τ i)).2
      ((Chart.isLieComb_iff _ _ _).2 rfl)
  refine ⟨⟨_, img, fun τ => ⟨fun i => ⟨isTangent_prodPts (ht τ) _, fun x => ?_⟩, fun w hw hw' => ?_⟩⟩, fun τ i =>
    ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W _).2 _ (img τ i)).2 (isTangent_prodPts (ht τ) _)⟩
  · exact eig_prodPts W.t.act (ht τ) x _ (fun j => ((hb τ).1 j).2 x) _
  · exact existsUnique_change (ht τ) (k' τ) (hk' τ) ((hb τ).2 w hw hw')

theorem exists_values (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ V := fun x n hn m h =>
    IntModelExists.mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

theorem exists_arcFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  intro E _ _ _ H Dw l Xo c V Y T io b a χ W ev z hP hb hχ hev hz hj
  letI := io.toAlgebra
  intro y hy
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let em : (E →+* ℂ) → (𝓞 E →+* V) := fun τ => (embK c τ).codRestrict V.toSubring fun x =>
    IntModelExists.mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)
  let ρ : (E →+* ℂ) → (𝓞 E →+* T.V) := fun τ => b.comp (em τ)
  have hρ : ∀ τ x, algebraMap T.V T.Fr (ρ τ x) = io (embK c τ x) := fun τ x => RingHom.congr_fun hb (em τ x)
  have hC : ((algebraMap T.V T.Fr).comp ev).comp (PowerSeries.C (R := T.V)) = algebraMap T.V T.Fr :=
    RingHom.ext fun x => congrArg (algebraMap T.V T.Fr) (hev x)
  have hm : Mono Y.j := by
    have : IsPreimmersion (spMap V.subtype) :=
      IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
    have := Y.jQ_open
    unfold Model.j
    infer_instance
  obtain ⟨e₁, -, he₁⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ io hb.symm hρ
    (exists_values c V)
  obtain ⟨th, hth, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange a.D₀.P
  obtain ⟨y₁, hx₁, hy₁⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ e₁ th he₁ hth (Or.inr hP)
    T.Fr ((algebraMap T.V T.Fr).comp ev) z (by rw [hC]; exact IntModelExists.flat_of_injective _ hinj) hj
    (by rw [← Category.assoc, hy]; exact y.2)
    (fun τ x => ((RingHom.congr_fun hC (ρ τ x)).trans (hρ τ x)).symm)
  obtain ⟨g, s, hg⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun _ => 1) 1 y₁).2.2.2 y (hx₁.trans hy).symm
  obtain ⟨hgu, hsu⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr g s y₁).2.2.1 y hg
  choose k L hk hL0 hLd hkL using fun τ => iwasawa_lower (V := T.V) (g τ) (hgu τ).ne_zero
  choose e he using fun τ i => ConstLie.exists_gtComb (k τ i) (e₁ τ)
  obtain ⟨hbe, hte⟩ := arcBasis_change hG W he₁ k hk he
  obtain ⟨y₀, hy₀⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun τ => (k τ).map (algebraMap T.V T.Fr)) 1
    y₁).1 (fun τ => by
      have := (hk τ).map (algebraMap T.V T.Fr)
      rwa [RingHom.map_det] at this) isUnit_one
  obtain ⟨hcomp, -, -, hbor⟩ := frChg_calculus E H Dw l Xo c T.Fr
  refine ⟨ρ, e, th, y₀, fun i => match i with
    | none => hsu.unit
    | some p => Units.mk0 _ (hLd p.1 p.2), hbe, hth, hte, fun τ x => (hρ τ x).symm, ?_, ?_⟩
  · refine GlobalTheory.T.arcFrame_change_by_constants hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W e₁ e th th k 1 hth he (ThMul.refl th) T.Fr _ y₁ y₀
      hm hy₁ ?_
    rw [hC, map_one, map_one]
    exact hy₀
  · refine (hbor _ _ _).2 ⟨L, fun _ _ => rfl, hL0, (hcomp _ L _ _ y₁ y₀ y hy₀).2 ?_⟩
    rw [_root_.mul_one, ← funext hkL]
    exact hg

end GlobalTheory.ArcFrame
end
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0152
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
import Formalism.HermitianCurvature.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFamiStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  first | exact @GlobalTheory.besselJ_family_aestronglyMeasurable | exact GlobalTheory.besselJ_family_aestronglyMeasurable | (intros; apply GlobalTheory.besselJ_family_aestronglyMeasurable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjEntrySmulCapelliEigenSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem conj_entry_smul_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ s t, s ≠ t → 2 * ((d : ℕ) : ℝ) < |lam s - lam t|) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d + 1 : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => star (g i j) • F g) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A i j F hsep hF
  obtain ⟨N₀, Fi, ν, hν, hcl, heig, hsum⟩ := hF
  obtain ⟨⟨co, hco⟩, -⟩ := GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear k r i j
  refine GlobalTheory.T.capelliEigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1)
    (Fin N₀ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) Finset.univ
    (fun x => co x.2.1 x.2.2) (fun x g => g⁻¹ x.2.1 x.2.2 • Fi x.1 g)
    (fun g => star (g i j) • F g) ?_ ?_
  · rintro ⟨x, a, b⟩ -
    refine ⟨d + 1, A - 1, le_rfl, le_rfl, ?_⟩
    have hinj : Function.Injective (fun s => lam s + (ν x s : ℝ)) := by
      intro s t hst
      by_contra hne
      have h1 := hsep s t hne
      have h2 : |(ν x s : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x s
      have h3 : |(ν x t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x t
      have h4 : lam s - lam t = (ν x t : ℝ) - (ν x s : ℝ) := by
        simp only at hst
        linarith
      rw [h4] at h1
      have h5 := abs_sub (ν x t : ℝ) (ν x s : ℝ)
      linarith
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum k r Wp Wq (fun s => lam s + (ν x s : ℝ)) A a b
      (Fi x) hinj (hcl x) (by
        intro Y g hg
        rw [heig x Y g hg]
        simp only [add_assoc])
    refine ⟨2 * r + k + 1, G, fun t s => ν x s - if s = t then 1 else 0, ?_, hG1, ?_, hG3⟩
    · intro t s
      have h := abs_le.mp (hν x s)
      rw [abs_le]
      push_cast
      split_ifs <;> constructor <;> omega
    · intro t Y g hg
      rw [hG2 t Y g hg]
      congr 2
      refine Finset.prod_congr rfl fun s _ => ?_
      push_cast
      split_ifs <;> ring
  · intro g hg
    beta_reduce
    rw [hco g hg, hsum g hg, Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormTranslatePowerCombLeCoprimeTranslation
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

theorem even_of_inOK_half {d : ℕ} (hd : 0 < d) {s : ℕ} (h : InOK d ((s : ℂ) / 2)) : 2 ∣ s := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.mpr this).ne'
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso
      first | exact hs h | omega
  subst hv
  have h2 : (s : ℝ) = 2 * u := by
    simp at hre
    linarith
  have h3 : (s : ℤ) = 2 * u := by exact_mod_cast h2
  omega

theorem inOK_add {d : ℕ} {x y : ℂ} (hx : InOK d x) (hy : InOK d y) : InOK d (x + y) := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  exact ⟨u + u', v + v', by push_cast; ring⟩

theorem inOK_int_mul {d : ℕ} (k : ℤ) {x : ℂ} (hx : InOK d x) : InOK d ((k : ℂ) * x) := by
  obtain ⟨u, v, rfl⟩ := hx
  exact ⟨k * u, k * v, by push_cast; ring⟩

theorem primeTo_add {d q : ℕ} {x y : ℂ} (hx : PrimeTo d q x) (hy : PrimeTo d q y) :
    PrimeTo d q (x + y) := by
  obtain ⟨s, hs, hsq, hx⟩ := hx
  obtain ⟨r, hr, hrq, hy⟩ := hy
  refine ⟨s * r, Nat.mul_pos hs hr, Nat.Coprime.mul_left hsq hrq, ?_⟩
  have := inOK_add (inOK_int_mul (r : ℤ) hx) (inOK_int_mul (s : ℤ) hy)
  convert this using 1
  push_cast
  ring

theorem norm_law : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q hq M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht hB
  have law0 := GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm d q M ω θ hd hd16 hsp hL hM hθ a m
  by_cases hhalf : InOK d (t - 1 / 2)
  swap
  · exact law0 c s t B hs ht hhalf hB
  have hd0 : 0 < d := hd.pos
  obtain ⟨hUU, -, hdiff, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd0
  obtain ⟨hlaws, hconst, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hM.2.1
  have hcm : ∀ (r : ℂ) (F : ℂ → ℂ), Differentiable ℂ F →
      hat M.ι (C ω * logS) (fun z => r * F z) = C (M.ι r) * hat M.ι (C ω * logS) F := by
    intro r F hF
    rw [← hconst r]
    exact (hlaws (fun _ => r) F analyticAt_const (hF.analyticAt 0)).2.1
  have hτ : PrimeTo d q (t / 2) := by
    obtain ⟨n, hn, hnq, hnt⟩ := ht
    have h2 : 2 ∣ n := by
      apply even_of_inOK_half hd0
      have := inOK_add hnt (inOK_int_mul (-(n : ℤ)) hhalf)
      convert this using 1
      push_cast
      ring
    refine ⟨n * n, Nat.mul_pos hn hn, Nat.Coprime.mul_left hnq hnq, ?_⟩
    obtain ⟨k, hk⟩ := h2
    have := inOK_int_mul (k : ℤ) hnt
    convert this using 1
    have hk' : (n : ℂ) = 2 * k := by exact_mod_cast hk
    push_cast
    rw [hk']
    ring
  have hτ' : ¬ InOK d (t / 2 - 1 / 2) := by
    intro h
    have h1 : InOK d 1 := ⟨1, 0, by simp⟩
    have h2 : 2 ∣ 1 := by
      apply even_of_inOK_half hd0
      have := inOK_add (inOK_add (inOK_int_mul 2 h) h1) (inOK_int_mul (-1) hhalf)
      convert this using 1
      push_cast
      ring
    omega
  have hdouble : ∀ F : ℂ → ℂ, U1 d (t / 2) (U1 d (t / 2) F) = U1 d t F := by
    intro F
    rw [hUU]
    have him : (h1 d (t / 2) (t / 2)).im = 0 := by
      rw [h1, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]
    funext z
    rw [him, add_halves]
    simp
  set r : Fin m → ℂ := fun j =>
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d (t / 2) (s j)).im : ℝ) : ℂ)) with hr
  have hstep : ∀ j, U1 d (t / 2) (U1 d (s j) θ) = fun z => r j * U1 d (t / 2 + s j) θ z :=
    fun j => hUU _ _ _
  have hD : ∀ j, Differentiable ℂ (U1 d (t / 2 + s j) θ) := fun j => (hdiff _ _ hθ.1).1
  have h1 := law0 c s (t / 2) B hs hτ hτ' hB
  have h2 : Bd B (∑ j, C (c j * M.ι (r j) ^ a) *
      hat M.ι (C ω * logS) (U1 d (t / 2 + s j) θ) ^ a) := by
    convert h1 using 2 with j
    rw [hstep j, hcm _ _ (hD j), mul_pow, map_mul, map_pow, mul_assoc]
  have h3 := law0 _ _ (t / 2) B (fun j => primeTo_add hτ (hs j)) hτ hτ' h2
  convert h3 using 2 with j
  have : U1 d t (U1 d (s j) θ) = fun z => r j * U1 d (t / 2) (U1 d (t / 2 + s j) θ) z := by
    rw [← hdouble, hstep j]
    funext z
    simp only [U1]
    ring
  rw [this, hcm _ _ (hdiff _ _ (hD j)).1, mul_pow, map_mul, map_pow, mul_assoc]

end GlobalTheory.MomOne.TranslNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelationsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  first | exact @GlobalTheory.HatNF.MulRelActual.mulRel_actual | exact GlobalTheory.HatNF.MulRelActual.mulRel_actual | (intros; apply GlobalTheory.HatNF.MulRelActual.mulRel_actual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPairStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  first | exact @GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | exact GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | (intros; apply GlobalTheory.HatNF.RaiseAdj.ptAdj_SS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoTopVectorCompactApproximantsBigCellStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_topVector_compactApproximants_bigCell : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, Tendsto (fun n : ℕ => tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w c) atTop (𝓝 (tv p (D.cutF p.T.base χ f ε) w c)) := by
  first | exact @GlobalTheory.TopVec.tv_approx_tendsto | exact GlobalTheory.TopVec.tv_approx_tendsto | (intros; apply GlobalTheory.TopVec.tv_approx_tendsto <;> assumption)
end


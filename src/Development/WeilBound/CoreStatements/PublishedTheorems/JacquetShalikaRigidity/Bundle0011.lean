import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle0005

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphericalIntegralStep
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SphericalFunctionIntegral

open Formalism.UG GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem le_one (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_Ov (w : Pl E) {x : w.adicCompletion E} (h : x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer) :
    x ∈ Ov E w :=
  (le_one w x).1 ((Valuation.mem_integer_iff _ _).1 h)

theorem int_KGL (w : Pl E) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : x ∈ KGL w k := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, mem_Ov w (h1 i j)⟩, Matrix.of fun i j => ⟨(x⁻¹ : GL (Fin k) (w.adicCompletion E)).1 i j, mem_Ov w (h2 i j)⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem fix {w : Pl E} {B : Multiset ℂˣ} {φ : XB E k} (h : SatFn w B φ) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Rt E k (fl k w x) φ = φ := by
  rcases h with rfl | h
  · exact map_zero _
  · exact GlobalTheory.LGrp.mem_fixed.1 h.2.1 x (int_KGL w hx)

variable [IsTotallyComplex E]

theorem step (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k) (g κ : GA E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ)
    (hinf : cInf κ = 1) (hS : ∀ w ∈ S, cLoc w κ = 1)
    (hint : ∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) (T : Finset (Pl E)) :
    ∃ h : GA E k, φ (g * h) = φ g ∧ cInf h = cInf κ ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w κ) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E k
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [mul_one], by rw [map_one, hinf], fun w hw => ?_, fun w _ _ => map_one _⟩
    rcases hw with hw | hw
    · rw [map_one, hS w hw]
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl k w (cLoc w κ), ?_, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · have e := congrArg (fun ψ : XB E k => ψ (g * h)) (hfix w hwS _ (hint w))
        simp only [Rt_apply] at e
        rw [← mul_assoc, e, hf0]
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')

open jumpWindows.GeneralLinearEntryConvergence in

theorem sph (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ) :
    SphOff S (φ : GA E k → ℂ) := by
  intro g κ hinf hS hint
  choose H hH using step hG S φ g κ hfix hinf hS hint
  have hT : Tendsto H atTop (𝓝 κ) := by
    refine tendsto_gl κ H (tendsto_entry S κ H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S κ⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have hc : Continuous fun x : GA E k => φ (g * x) := φ.continuous.comp (continuous_const.mul continuous_id)
  have h1 := (hc.tendsto κ).comp hT
  have h2 : Tendsto ((fun x : GA E k => φ (g * x)) ∘ H) atTop (𝓝 (φ g)) := by
    have e : (fun x : GA E k => φ (g * x)) ∘ H = fun _ => φ g := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end SphericalFunctionIntegral

theorem spherical_function_of : jumpWindows.G0 → jumpWindows.G5 → C0 → K7 → K8 := by
  intro hG0 hG5 hC0 hK7 E _ _ _ k ψ hψ S hcond α φ hgood hsat
  obtain ⟨-, hrt, -, hreg⟩ := hG5 E k ψ hψ
  have hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ :=
    fun w hw x hx => SphericalFunctionIntegral.fix (hsat ⟨w, hw⟩) hx
  have hφ := SphericalFunctionIntegral.sph hG0 S φ hfix
  have hcont := (hreg φ hgood).1
  refine ⟨hφ, fun g κ hinf hS hint => ?_, fun g hg => ⟨fun g₀ hi hS hIn h0 => ?_, fun w hw => ?_⟩⟩
  · have e : Rt E k κ φ = φ := by
      ext x
      simp only [Rt_apply]
      exact hφ x κ hinf hS hint
    rw [← hrt, e]
  · refine hg (jumpWindows.convergence_entries_general_linear hG0 E k S (Wh ψ φ) hcont (fun w hw h hh h0 u => ?_) g g₀ hi hS hIn h0)
    obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    rw [hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) h hh u, h0, zero_mul]
  · obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    obtain ⟨g', hg', e, -, -⟩ := (hC0 E k S).2.2.2.2.2.2 w g
    have h1 := hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) g' hg' (cLoc w g)
    rw [← e] at h1
    rw [h1] at hg
    have h2 := right_ne_zero_of_mul hg
    by_contra hA
    apply h2
    rw [sphericalWhittaker, if_neg hA]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SquareIntegralBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SquareIntegralBound

theorem sqle (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem intMul {X : Type} [MeasurableSpace X] {ν : Measure X} {F G : X → ℂ}
    (hF : AEStronglyMeasurable F ν) (hG : AEStronglyMeasurable G ν)
    (hF2 : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ∞) (hG2 : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun x => F x * conj (G x)) ν := by
  refine ⟨hF.mul (Complex.continuous_conj.comp_aestronglyMeasurable hG), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖F x * conj (G x)‖ₑ ∂ν ≤ ∫⁻ x, (‖F x‖ₑ ^ 2 + ‖G x‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [enorm_mul]
        have : ‖conj (G x)‖ₑ = ‖G x‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
        rw [this]; exact sqle _ _
    _ = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν := lintegral_add_left' (hF.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hF2, hG2⟩

theorem bnd (D B C1 C2 s : ℝ) (N : ℕ) (hD : 0 < D) (hB : 0 ≤ B) (hs : 2 ≤ s) (hN : s + 1 ≤ N) (T : ℝ≥0∞)
    (h1 : T ≤ ENNReal.ofReal (C1 * D ^ (-1 : ℝ))) (h2 : T ≤ ENNReal.ofReal (C2 * D ^ (-(N : ℝ)))) :
    ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * max (max C1 C2) 0 * min D D⁻¹ ^ (1 : ℝ)) := by
  set K := max (max C1 C2) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hC1 : C1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hBs : 0 ≤ B * D ^ s := mul_nonneg hB (Real.rpow_nonneg hD.le _)
  rw [Real.rpow_one]
  rcases le_or_gt D 1 with hD1 | hD1
  · have hmin : min D D⁻¹ = D := min_eq_left (le_trans hD1 (one_le_inv₀ hD |>.mpr hD1))
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C1 * D ^ (-1 : ℝ)) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C1 * D ^ (-1 : ℝ))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-1 : ℝ) = D ^ (s - 1) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - 1) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - 1) ≤ D := by
            calc D ^ (s - 1) ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith)
              _ = D := Real.rpow_one D
          calc B * D ^ s * (C1 * D ^ (-1 : ℝ)) = B * C1 * (D ^ s * D ^ (-1 : ℝ)) := by ring
            _ = B * C1 * D ^ (s - 1) := by rw [e]
            _ ≤ B * K * D ^ (s - 1) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC1 hB) hP0
            _ ≤ B * K * D := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)
  · have hmin : min D D⁻¹ = D⁻¹ := min_eq_right (le_trans (inv_le_one_of_one_le₀ hD1.le) hD1.le)
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C2 * D ^ (-(N : ℝ))) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C2 * D ^ (-(N : ℝ)))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-(N : ℝ)) = D ^ (s - N) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - N) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - N) ≤ D⁻¹ := by
            calc D ^ (s - N) ≤ D ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by linarith)
              _ = D⁻¹ := Real.rpow_neg_one D
          calc B * D ^ s * (C2 * D ^ (-(N : ℝ))) = B * C2 * (D ^ s * D ^ (-(N : ℝ))) := by ring
            _ = B * C2 * D ^ (s - N) := by rw [e]
            _ ≤ B * K * D ^ (s - N) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2 hB) hP0
            _ ≤ B * K * D⁻¹ := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)

end SquareIntegralBound

open SquareIntegralBound in
theorem moderate_growth_of : D0 → N0 → P2 → U0 → U2 → V1 → ThetaDecaying → M0 := by
  intro hD0 hN0 hP2 hU0 hU2 hV1 hG4 E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hd
  obtain ⟨β₁, hβ₁, hU0a, hU0b⟩ := hU0 E k μ hk β hβ
  obtain ⟨β', hβ', hU2'⟩ := hU2 E k μ ψ hψ (k - 1) (by omega) β₁ hβ₁
  obtain ⟨hDpos, hDmul, hDcont, hDrat, hDU, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, hPchi, hGoodPre, hLu, hLmir, hLcont, hLsupp⟩ := hP2 E k ψ hψ
  obtain ⟨C, hC, hfC⟩ := hd.supp
  obtain ⟨a, ε, Cf, hε, hsq⟩ := hd.sq
  obtain ⟨Φ₀, hΦ1, -, hΦc, hΦI⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  obtain ⟨-, -, hV1c⟩ := hV1 E k μ hk β hβ
  have hk1 : k - 1 < k := by omega
  have hDu : ∀ u g : GA E k, UU 0 u → Dt (u * g) = Dt g := fun u g hu => by
    rw [hDmul, hDU 0 u hu, one_mul]
  have hDr : ∀ γ (g : GA E k), Dt (ratGL E k γ * g) = Dt g := fun γ g => by
    rw [hDmul, hDrat, one_mul]
  obtain ⟨Bφ, hBφ⟩ : ∃ B, ∀ g, ‖φ g‖ ≤ B := by
    obtain ⟨B, hB⟩ := hd.dec 0
    have hne : (fun _ => (1 : E) : Fin k → E) ≠ 0 := fun h => by
      have := congrFun h ⟨0, hk⟩; simp at this
    exact ⟨B, fun g => by simpa using hB g _ hne⟩
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 1)
  refine ⟨β', a / 2 + 1, hβ', fun z hz => ?_⟩
  set χ₁ : GA E k → ℂ := fun g => ((Dt g ^ (a / 2) : ℝ) : ℂ) with hχ₁
  set χ₂ : GA E k → ℂ := fun g => conj ((Dt g : ℂ) ^ (z - ((a / 2 : ℝ) : ℂ))) * (Φ₀ (lastRow g) : ℂ) with hχ₂
  have hχ₁c : Continuous χ₁ := Complex.continuous_ofReal.comp
    (hDcont.rpow_const fun g => Or.inl (hDpos g).ne')
  have hχ₂c : Continuous χ₂ := by
    refine (Complex.continuous_conj.comp ?_).mul (Complex.continuous_ofReal.comp (Φ₀.continuous.comp hLcont))
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  have hχ₁u : ∀ u, UU 0 u → ∀ g, χ₁ (u * g) = χ₁ g := fun u hu g => by simp only [hχ₁, hDu u g hu]
  have hχ₁m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₁ (ratGL E k γ * g) = χ₁ g := fun γ _ g => by simp only [hχ₁, hDr]
  have hχ₂u : ∀ u, UU 0 u → ∀ g, χ₂ (u * g) = χ₂ g := fun u hu g => by simp only [hχ₂, hDu u g hu, hLu u g hu]
  have hχ₂m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₂ (ratGL E k γ * g) = χ₂ g := fun γ hγ g => by
    simp only [hχ₂, hDr, hLmir γ g (by simpa using hγ)]
  obtain ⟨hpre1, hwf, -⟩ := hPchi (k - 1) hk1 f χ₁ hd.pre hχ₁c hχ₁u hχ₁m
  obtain ⟨hpre2, hwφ, hgood2⟩ := hPchi (k - 1) hk1 φ χ₂ (hGoodPre _ _ hd.good) hχ₂c hχ₂u hχ₂m
  have hgood2 := hgood2 hd.good
  have hK : ∀ g, lastRow g ∈ C → χ₁ g * conj (χ₂ g) = (Dt g : ℂ) ^ z := fun g hg => by
    have h1 : Φ₀ (lastRow g) = 1 := hΦ1 hg
    simp only [hχ₁, hχ₂, map_mul, Complex.conj_conj, Complex.conj_ofReal, h1, Complex.ofReal_one, mul_one]
    rw [Complex.ofReal_cpow (hDpos g).le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hDpos g).ne')]
    congr 1; ring
  have hW : ∀ g, whit ψ (k - 1) (fun g => χ₁ g * f g) g * conj (whit ψ (k - 1) (fun g => χ₂ g * φ g) g) =
      PW ψ f φ g * (Dt g : ℂ) ^ z := fun g => by
    rw [hwf, hwφ]
    by_cases h0 : whit ψ (k - 1) f g = 0
    · simp [PW, h0]
    · rw [PW, ← hK g (hLsupp (k - 1) hk1 f C hfC g h0), map_mul]; ring
  have hF : ∀ g, χ₁ g * f g * conj (χ₂ g * φ g) = f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    by_cases h0 : f g = 0
    · simp [h0]
    · rw [← hK g (hfC g h0), map_mul]; ring
  have hL2f : ∫⁻ g, ‖χ₁ g * f g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    rw [hU0a (fun g => ‖χ₁ g * f g‖ₑ ^ 2) (hpre1.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre1.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (((hV1c ε hε).const_mul Cf).lintegral_lt_top)
    have hterm : ∀ x, ‖χ₁ x * f x‖ₑ ^ 2 = ENNReal.ofReal (Dt x ^ a) * ‖f x‖ₑ ^ 2 := fun x => by
      rw [enorm_mul, mul_pow]
      congr 1
      rw [hχ₁]
      simp only
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hDpos x).le _),
        ← ENNReal.ofReal_pow (Real.rpow_nonneg (hDpos x).le _), ← Real.rpow_mul_natCast (hDpos x).le]
      norm_num
    simp only [hterm, hDr, ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (Dt g ^ a) * ∑' ξ : RowT E k k, ‖f (ratGL E k (gam ξ) * g)‖ₑ ^ 2
        ≤ ENNReal.ofReal (Dt g ^ a) * ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a)) := by
          gcongr; exact hsq g
      _ = ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hDpos g).le _)]
        congr 1
        have hp := Real.rpow_pos_of_pos (hDpos g) a
        rw [Real.rpow_neg (hDpos g).le]
        field_simp
  have hL2φ : ∫⁻ g, ‖χ₂ g * φ g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    obtain ⟨-, hG4b⟩ := hG4 E k hk φ hd.dec
    obtain ⟨s, hs⟩ : ∃ s, s = 2 * z.re - a := ⟨_, rfl⟩
    have hs2 : 2 ≤ s := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈s⌉₊ + 1 := ⟨_, rfl⟩
    have hNs : s + 1 ≤ (N : ℝ) := by rw [hN]; push_cast; linarith [Nat.le_ceil s]
    obtain ⟨C1, hC1⟩ := hG4b _ hΦc.isCompact k le_rfl
    obtain ⟨C2, hC2⟩ := hG4b _ hΦc.isCompact (k * N) (Nat.le_mul_of_pos_right k (by omega))
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e1 : -((k : ℕ) : ℝ) / k = -1 := by field_simp
    have e2 : -(((k * N : ℕ)) : ℝ) / k = -(N : ℝ) := by push_cast; field_simp
    rw [e1] at hC1; rw [e2] at hC2
    rw [hU0a (fun g => ‖χ₂ g * φ g‖ₑ ^ 2) (hpre2.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre2.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_)
      (((hV1c 1 one_pos).const_mul (Bφ * max (max C1 C2) 0)).lintegral_lt_top)
    refine le_trans ?_ (SquareIntegralBound.bnd (Dt g) Bφ C1 C2 s N (hDpos g) hBφ0 hs2 hNs _ (hC1 g) (hC2 g))
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ξ => ?_
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    rw [hφ]
    have hDx : Dt (ratGL E k (gam ξ) * g) = Dt g := hDr _ _
    by_cases hx : lastRow (ratGL E k (gam ξ) * g) ∈ tsupport Φ₀
    · rw [Set.indicator_of_mem hx, one_mul]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg hBφ0 (Real.rpow_nonneg (hDpos g).le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hχn : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ≤ Dt g ^ (z.re - a / 2) := by
        rw [hχ₂]; simp only
        rw [norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos (hDpos _), Complex.norm_real, hDx]
        simp only [Complex.sub_re, Complex.ofReal_re]
        have h0 := hΦI (lastRow (ratGL E k (gam ξ) * g))
        rw [Real.norm_of_nonneg h0.1]
        exact mul_le_of_le_one_right (Real.rpow_nonneg (hDpos g).le _) h0.2
      have hsq' : Dt g ^ s = (Dt g ^ (z.re - a / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hDpos g).le]; congr 1; rw [hs]; push_cast; ring
      rw [norm_mul, mul_pow, hsq']
      have hφg := hBφ g
      have h3 : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ^ 2 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hχn 2
      have h4 : 0 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 := by positivity
      nlinarith [norm_nonneg (φ g), mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖φ g‖),
        mul_le_mul_of_nonneg_left hφg (mul_nonneg h4 (norm_nonneg (φ g)))]
    · have : Φ₀ (lastRow (ratGL E k (gam ξ) * g)) = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hχ₂, this]
  obtain ⟨hint, heq⟩ := hU2' _ _ hpre1 hgood2 hL2f hL2φ
  have hmeas : Measurable fun g => χ₁ g * f g * conj (χ₂ g * φ g) :=
    (hpre1.cont.mul (Complex.continuous_conj.comp hpre2.cont)).measurable
  have hinv : ∀ γ, IsMir (k - 1) γ → ∀ g, (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (ratGL E k γ * g) =
      (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g := fun γ hγ g => by
    have h1 := hpre1.left γ hγ g
    have h2 := hpre2.left γ hγ g
    simp only at h1 h2 ⊢
    rw [h1, h2]
  have hintF : Integrable (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (μ.withDensity β₁) :=
    intMul hpre1.cont.aestronglyMeasurable hpre2.cont.aestronglyMeasurable hL2f hL2φ
  have hsum : ∀ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g =
      sumF f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    simp only [sumF, hF]
    simp only [hφ, hDr, tsum_mul_right]
  refine ⟨hint.congr (Filter.Eventually.of_forall hW), ?_⟩
  calc ∫ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ z ∂μ.withDensity β
      = ∫ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g ∂μ.withDensity β := by simp only [hsum]
    _ = ∫ g, χ₁ g * f g * conj (χ₂ g * φ g) ∂μ.withDensity β₁ := (hU0b _ hmeas hinv hintF).symm
    _ = _ := heq
    _ = ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ z ∂μ.withDensity β' := by simp only [hW]

end PositivityTheory.AdelicQuotientData

end
end


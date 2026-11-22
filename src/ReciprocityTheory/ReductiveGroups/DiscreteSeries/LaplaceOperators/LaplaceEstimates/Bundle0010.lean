import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0009
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirValueSubSingle
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0012
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TMapSpec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ThreeAddLeGapBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0011

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMF
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace ConjugateTransportSingles

variable {k r : ℕ}

theorem inv_conj (P G : Mat k r) (hP : IsUnit P.det) : (P * G * P⁻¹)⁻¹ = P * G⁻¹ * P⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

theorem cJd_transport (P : Mat k r) (hP : IsUnit P.det) (x1 β : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJd (P *ᵥ x1) β (P * G * P⁻¹) = (β ᵥ* P) ⬝ᵥ (G⁻¹ *ᵥ x1) := by
  unfold cJd
  rw [inv_conj P G hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ P⁻¹ P,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec, Matrix.dotProduct_mulVec]

theorem cJd_sinv (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (β : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r) (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z)
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    cJd (xJ P z) β (P * (s * x) * P⁻¹) = cJd (xJ P z) β (P * x * P⁻¹) := by
  unfold xJ
  rw [cJd_transport P hP, cJd_transport P hP]
  exact ((mult k r z hz).1 (0 : Fin (2 * r + k + 1) → ℂ) (β ᵥ* P) s hs x hx).2

theorem cJd_single (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (d : Fin (2 * r + k + 1))
    (x : Mat k r) :
    cJd (xJ P z) (Pi.single d 1) (P * x * P⁻¹) = (P *ᵥ (x⁻¹ *ᵥ xOne k r z)) d := by
  unfold xJ
  rw [cJd_transport P hP, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Pi.single_apply]

theorem tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMapD σ x1 x₀ w (Pi.single d m) G = cJd x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMapD
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc, coefX]
  · simp

theorem tMapD_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMapD σ x1 x₀ w f G = ∑ d, tMapD σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMapD_single σ x1 x₀ w d (f d) G]
  rfl

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem perI_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    CapelliMinorRestriction.perI P ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =ᵐ[μW.prod μN]
      fun p => (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • CapelliMinorRestriction.perI P ψ π (coefX σ x₀ w m) ξ g p := by
  filter_upwards [CapelliMinorRestriction.ae_S hW hN] with p hp
  simp only [CapelliMinorRestriction.perI]
  rw [tMapD_single, cJd_sinv P hP z hz _ _ g hp hg, cJd_single P hP, mul_smul]

theorem per_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_smul]
  exact integral_congr_ae (perI_tMapD_single σ z hz P hP μW μN hW hN ψ π x₀ w d m ξ g hg)

theorem per_add (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F₁ F₂ : Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (h₁ : Integrable (CapelliMinorRestriction.perI P ψ π F₁ ξ x) (μW.prod μN))
    (h₂ : Integrable (CapelliMinorRestriction.perI P ψ π F₂ ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => F₁ G + F₂ G) ξ x = per P μW μN ψ π F₁ ξ x + per P μW μN ψ π F₂ ξ x := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_add h₁ h₂]
  congr 1
  funext p
  simp [CapelliMinorRestriction.perI, add_smul]

end ConjugateTransportSingles

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotM
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS TransportMapLinear

theorem quotM : QuotMStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ s x hx₀ hHC' hGap' hx hper
  classical
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  have hmin : 1 ≤ min (pOf ε) (qOf ε) := hq0
  have hp1 : 1 ≤ pOf ε := le_trans hmin (min_le_left _ _)
  have hq1 : 1 ≤ qOf ε := le_trans hmin (min_le_right _ _)
  have hGL : GapLap ε lam h := ⟨hHC.1, hGap, hNeed⟩
  have hstd : StdGap ε (lam - Pi.single s 1) :=
    ⟨hHC'.1, h, hGap', by linarith [LemK.three_add_le_gapBound_dual ε]⟩
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  have hUR : IsInfUnitary ε (smE ε (rreg ε)) := Base.smInfUnitary _ ε (L2 ε) (rreg ε) hR
  set G : Submodule ℂ (Fin (2 * r + k + 1) → D) := Submodule.pi Set.univ (fun _ => genSub E V) with hGdef
  set X : Submodule ℂ (Fin (2 * r + k + 1) → D) := LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s)
    with hXdef
  set L := tMapDL (D := D) σ (xJ P z) x₀ ((w : D) : H) with hLdef
  have hmemG : ∀ f, f ∈ G ↔ ∀ c, f c ∈ genSub E V := fun f => LemK.mem_pi_submodule_iff
  have hXG : X ≤ G := fun f hf => (hmemG f).2 (LemK.mem_euler_eigenspace_iff.1 hf).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => LemK.generated_submodule_stable_under_action V a b hv
  have hGA : ∀ a b, ∀ f ∈ G, LemK.tensVd E a b f ∈ G := fun a b f hf =>
    (hmemG _).2 (LemK.dualTensorAction_mem hGs a b ((hmemG f).1 hf))
  have hXA : ∀ a b, ∀ f ∈ X, LemK.tensVd E a b f ∈ X := fun a b f hf => LemK.euler_eigenspace_stable_under_action hE hGs a b hf
  have hspec := fun (f : Fin (2 * r + k + 1) → D) (hf : f ∈ G) =>
    tMapD_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) x₀ w hx₀ f
      ((hmemG f).1 hf)
  have hsm : ∀ f ∈ G, IsSmoothL2 ε (L f) := fun f hf => (hspec f hf).1
  have hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (LemK.tensVd E a b f) g :=
    fun f hf a b g hg => (hspec f hf).2.1 a b g hg
  obtain ⟨Tl, hTl, hTint⟩ := exists_lin ε (LemK.tensVd E) G L hsm hGA hder
  have hbd : ∀ f ∈ G, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖L f g‖ ≤ C * frob g ^ (1 - aExp ε h) := fun f hf => by
    obtain ⟨C, hC⟩ := (hspec f hf).2.2 []
    exact ⟨C, hC⟩
  have hcont : ∀ f ∈ G, ContinuousOn (L f) (UJset ε) := fun f hf => QuotA.contOn_of_smooth (hsm f hf).1
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  let Z : Submodule ℂ (Fin (2 * r + k + 1) → D) :=
    { carrier := {y | y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0}
      add_mem' := by
        rintro y₁ y₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.add_mem h1X h2X, fun g hg => ?_⟩
        rw [map_add, QuotA.per_add hP hB hp hq hsg (hcont _ (hXG h1X)) (hbd _ (hXG h1X)) (hcont _ (hXG h2X))
          (hbd _ (hXG h2X)) ξ hg, h1 g hg, h2 g hg, add_zero]
      zero_mem' := by
        refine ⟨X.zero_mem, fun g hg => ?_⟩
        have := QuotA.per_smul P μW μN ψ π 0 0 ξ g
        rw [zero_smul, zero_smul] at this
        rw [map_zero, this]
      smul_mem' := by
        rintro a y ⟨hyX, hy⟩
        refine ⟨X.smul_mem a hyX, fun g hg => ?_⟩
        rw [map_smul, QuotA.per_smul, hy g hg, smul_zero] }
  have hmemZ : ∀ y, y ∈ Z ↔ y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0 :=
    fun y => Iff.rfl
  have hZX : Z ≤ X := fun y hy => ((hmemZ y).1 hy).1
  have hZA : ∀ a b, ∀ y ∈ Z, LemK.tensVd E a b y ∈ Z := by
    intro a b y hy
    obtain ⟨hyX, hy0⟩ := (hmemZ y).1 hy
    refine (hmemZ _).2 ⟨hXA a b y hyX, fun g hg => ?_⟩
    rw [← QuotA.per_congr hP hB ψ (fun g' hg' => hder y (hXG hyX) a b g' hg') ξ hg,
      (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hsg).2 (L y) (hsm y (hXG hyX)).1
        (fun wd => (hspec y (hXG hyX)).2.2 wd) a b g hg ξ]
    exact QuotA.eabB_zero hP (fun y' hy' => hy0 y' hy') a b hg
  have hZφ : ∀ y ∈ X, ∀ y' ∈ Z, Tl y = Tl y' → y ∈ Z := by
    intro y hy y' hy' he
    have e := congrArg Subtype.val he
    rw [hTl y (hXG hy), hTl y' (hXG (hZX hy'))] at e
    have hEq := QuotA.eqOn_unitary_of_toL2_eq (hsm y (hXG hy)) (hsm y' (hXG (hZX hy'))) e
    refine (hmemZ y).2 ⟨hy, fun g hg => ?_⟩
    rw [QuotA.per_congr hP hB ψ hEq ξ hg]
    exact ((hmemZ y').1 hy').2 g hg
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨g, hg, hne⟩ := hper
    exact hne (((hmemZ x).1 hxZ).2 g hg)
  have hkfin : ∀ x' ∈ X, ∃ S : Submodule ℂ (Fin (2 * r + k + 1) → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ x' ∈ S := fun x' hx' => LemK.eigenspace_K_finite hE hV.1 hV.2.1 hx'
  have hK2 := (LemK.k2Vd _ ε lam h H σ D E V s hσ hD hV hc hVK hHC.2 hHC.1 hGL hp1 hq1).2
  have hK3 : ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensVd E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ x' ∈ X, ψ' x' ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ' ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal (lam - Pi.single s 1) : ℂ) • v := by
    intro ψ' hψ' x' hx' hψx'
    exact LemK.k3Vd _ ε lam h H σ D E V s (smD ε (rreg ε)) (smE ε (rreg ε)) ψ' x' hσ hD hV hc hVK hHC.2
      hHC.1 hGL hp1 hq1 hHC'.1 hDR.glRep hUR (fun a b f hf => hψ' a b f ((hmemG f).2 hf)) hx' hψx'
  have hline : ∃ ys ∈ X, ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensVd E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ w' ∈ X.map ψ', IsKHWVec ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) w' →
        ∃ c : ℂ, w' = c • ψ' ys := by
    obtain ⟨ys, hys, hl⟩ := line (isKUnitary_of_isInfUnitary hU) X (lowK ε (lam - Pi.single s 1)) hkfin hK2
    exact ⟨ys, hys, fun ψ' hψ' w' hw' hwK =>
      hl _ (smE ε (rreg ε)) ψ' (fun a b _ x' hx' => hψ' a b x' (hXG hx')) w' hw' hwK⟩
  obtain ⟨Y', W, hY'X, hW, hY'Z, hirr, hcas, hK⟩ :=
    QuotA.quot_generic (LemK.tensVd E) G X Z (lam - Pi.single s 1) hstd Tl hXG hTint hK3 hline hkfin hZX hZA
      hZφ hx hxZ
  refine ⟨Y'.map L, W, ?_, ?_, hirr, hcas, hK, ?_⟩
  · rintro F hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    exact ⟨y, hY'X hy, rfl⟩
  · intro v
    rw [hW]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨L y, Submodule.mem_map_of_mem hy, hTl y (hXG (hY'X hy))⟩
    · rintro ⟨F, hF, hv⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
      exact ⟨y, hy, Subtype.ext (hv.trans (hTl y (hXG (hY'X hy))).symm)⟩
  · rintro F hF hF0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    have hyZ : y ∈ Z := (hmemZ y).2 ⟨hY'X hy, hF0⟩
    rw [hY'Z y hy hyZ, map_zero]
    intro g _
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotP
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS TransportMapLinear

theorem quotP : QuotPStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ s x hx₀ hHC' hGap' hx hper
  classical
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  have hmin : 1 ≤ min (pOf ε) (qOf ε) := hq0
  have hp1 : 1 ≤ pOf ε := le_trans hmin (min_le_left _ _)
  have hq1 : 1 ≤ qOf ε := le_trans hmin (min_le_right _ _)
  have hGL : GapLap ε lam h := ⟨hHC.1, hGap, hNeed⟩
  have hstd : StdGap ε (lam + Pi.single s 1) :=
    ⟨hHC'.1, h, hGap', by linarith [LemK.three_add_le_gapBound ε]⟩
  have hE := hD.glRep
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  have hUR : IsInfUnitary ε (smE ε (rreg ε)) := Base.smInfUnitary _ ε (L2 ε) (rreg ε) hR
  set G : Submodule ℂ (Fin (2 * r + k + 1) → D) := Submodule.pi Set.univ (fun _ => genSub E V) with hGdef
  set X : Submodule ℂ (Fin (2 * r + k + 1) → D) := LemK.Xs (LemK.eeV E) (genSub E V) (LemK.thV lam s)
    with hXdef
  set L := QuotA.tL (D := D) ε σ (xJ P z) x₀ ((w : D) : H) with hLdef
  have hmemG : ∀ f, f ∈ G ↔ ∀ c, f c ∈ genSub E V := fun f => LemK.mem_pi_submodule_iff
  have hXG : X ≤ G := fun f hf => (hmemG f).2 (LemK.mem_eigenTensorSpace_gen_iff.1 hf).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => LemK.generated_submodule_stable_under_action V a b hv
  have hGA : ∀ a b, ∀ f ∈ G, LemK.tensV E a b f ∈ G := fun a b f hf => by
    refine (hmemG _).2 fun c' => ?_
    rw [LemK.entry_bounds_of_partialSum]
    refine add_mem (hGs a b _ ((hmemG f).1 hf c')) ?_
    split_ifs
    · exact (hmemG f).1 hf b
    · exact zero_mem _
  have hXA : ∀ a b, ∀ f ∈ X, LemK.tensV E a b f ∈ X := fun a b f hf => LemK.eigenTensorSpace_stable hE a b hf
  have hspec := fun (f : Fin (2 * r + k + 1) → D) (hf : f ∈ G) =>
    tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) x₀ w hx₀ f
      ((hmemG f).1 hf)
  have hsm : ∀ f ∈ G, IsSmoothL2 ε (L f) := fun f hf => (hspec f hf).1
  have hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (LemK.tensV E a b f) g :=
    fun f hf a b g hg => (hspec f hf).2.1 a b g hg
  obtain ⟨Tl, hTl, hTint⟩ := exists_lin ε (LemK.tensV E) G L hsm hGA hder
  have hbd : ∀ f ∈ G, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖L f g‖ ≤ C * frob g ^ (1 - aExp ε h) := fun f hf => by
    obtain ⟨C, hC⟩ := (hspec f hf).2.2 []
    exact ⟨C, hC⟩
  have hcont : ∀ f ∈ G, ContinuousOn (L f) (UJset ε) := fun f hf => QuotA.contOn_of_smooth (hsm f hf).1
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  let Z : Submodule ℂ (Fin (2 * r + k + 1) → D) :=
    { carrier := {y | y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0}
      add_mem' := by
        rintro y₁ y₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.add_mem h1X h2X, fun g hg => ?_⟩
        rw [map_add, QuotA.per_add hP hB hp hq hsg (hcont _ (hXG h1X)) (hbd _ (hXG h1X)) (hcont _ (hXG h2X))
          (hbd _ (hXG h2X)) ξ hg, h1 g hg, h2 g hg, add_zero]
      zero_mem' := by
        refine ⟨X.zero_mem, fun g hg => ?_⟩
        have := QuotA.per_smul P μW μN ψ π 0 0 ξ g
        rw [zero_smul, zero_smul] at this
        rw [map_zero, this]
      smul_mem' := by
        rintro a y ⟨hyX, hy⟩
        refine ⟨X.smul_mem a hyX, fun g hg => ?_⟩
        rw [map_smul, QuotA.per_smul, hy g hg, smul_zero] }
  have hmemZ : ∀ y, y ∈ Z ↔ y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0 :=
    fun y => Iff.rfl
  have hZX : Z ≤ X := fun y hy => ((hmemZ y).1 hy).1
  have hZA : ∀ a b, ∀ y ∈ Z, LemK.tensV E a b y ∈ Z := by
    intro a b y hy
    obtain ⟨hyX, hy0⟩ := (hmemZ y).1 hy
    refine (hmemZ _).2 ⟨hXA a b y hyX, fun g hg => ?_⟩
    rw [← QuotA.per_congr hP hB ψ (fun g' hg' => hder y (hXG hyX) a b g' hg') ξ hg,
      (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hsg).2 (L y) (hsm y (hXG hyX)).1
        (fun wd => (hspec y (hXG hyX)).2.2 wd) a b g hg ξ]
    exact QuotA.eabB_zero hP (fun y' hy' => hy0 y' hy') a b hg
  have hZφ : ∀ y ∈ X, ∀ y' ∈ Z, Tl y = Tl y' → y ∈ Z := by
    intro y hy y' hy' he
    have e := congrArg Subtype.val he
    rw [hTl y (hXG hy), hTl y' (hXG (hZX hy'))] at e
    have hEq := QuotA.eqOn_unitary_of_toL2_eq (hsm y (hXG hy)) (hsm y' (hXG (hZX hy'))) e
    refine (hmemZ y).2 ⟨hy, fun g hg => ?_⟩
    rw [QuotA.per_congr hP hB ψ hEq ξ hg]
    exact ((hmemZ y').1 hy').2 g hg
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨g, hg, hne⟩ := hper
    exact hne (((hmemZ x).1 hxZ).2 g hg)
  have hkfin : ∀ x' ∈ X, ∃ S : Submodule ℂ (Fin (2 * r + k + 1) → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x' ∈ S := fun x' hx' => QuotA.exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hx'
  have hK3 : ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensV E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ x' ∈ X, ψ' x' ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ' ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal (lam + Pi.single s 1) : ℂ) • v := by
    intro ψ' hψ' x' hx' hψx'
    exact LemK.k3V _ ε lam h H σ D E V s (smD ε (rreg ε)) (smE ε (rreg ε)) ψ' x' hσ hD hV hc hVK hHC.2
      hHC.1 hGL hp1 hq1 hHC'.1 hDR.glRep hUR (fun a b f hf => hψ' a b f ((hmemG f).2 hf)) hx' hψx'
  have hline : ∃ ys ∈ X, ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensV E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ w' ∈ X.map ψ', IsKHWVec ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) w' →
        ∃ c : ℂ, w' = c • ψ' ys :=
    QuotA.line_V hσ hD hV hc hVK hHC.2 hHC.1 hGL hp1 hq1 s (smE ε (rreg ε))
  obtain ⟨Y', W, hY'X, hW, hY'Z, hirr, hcas, hK⟩ :=
    QuotA.quot_generic (LemK.tensV E) G X Z (lam + Pi.single s 1) hstd Tl hXG hTint hK3 hline hkfin hZX hZA
      hZφ hx hxZ
  refine ⟨Y'.map L, W, ?_, ?_, hirr, hcas, hK, ?_⟩
  · rintro F hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    exact ⟨y, hY'X hy, rfl⟩
  · intro v
    rw [hW]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨L y, Submodule.mem_map_of_mem hy, hTl y (hXG (hY'X hy))⟩
    · rintro ⟨F, hF, hv⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
      exact ⟨y, hy, Subtype.ext (hv.trans (hTl y (hXG (hY'X hy))).symm)⟩
  · rintro F hF hF0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    have hyZ : y ∈ Z := (hmemZ y).2 ⟨hY'X hy, hF0⟩
    rw [hY'Z y hy hyZ, map_zero]
    intro g _
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end


import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0221
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0127
import Formalism.FormalDegreeBessel.Bundle0001

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpCapLOfOf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def wfam {d : ℕ} {α : Type} (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d :=
  L.map (fun t => (t.1, t.2.map F)) ++ [(c, [])]

def WFamApp : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ)
    (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ),
    WOp.app (wfam L F c) v x = (L.map fun t => t.1 * vfW (t.2.map F) v x).sum + c * v x

def WFamSymb : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ)
    (x ξ : Fin d → ℝ) (τ : α → ℂ), 1 ≤ j → (∀ t ∈ L, ∀ X ∈ t.2, ((ξ ⬝ᵥ F X x : ℝ) : ℂ) = τ X) →
    WOp.symb (wfam L F c) j x ξ = (L.map fun t => if t.2.length = j then t.1 * (t.2.map τ).prod else 0).sum

def TrRealLie : Prop :=
  ∀ (k r : ℕ) (A X : B.Mat k r), B.inLie k r A → B.inLie k r X →
    (((Matrix.trace (A * X)).re : ℝ) : ℂ) = Matrix.trace (A * X)

def CkLevOn : Prop :=
  ∀ (k r m : ℕ) (Dm : Set (B.Mat k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E),
    Q.CkLev k r 0 m Dm f → B.CkOn (m : ℕ∞) (B.GV k r ∩ Dm) f

theorem wfam_ok {d : ℕ} {α : Type} {O : Set (Fin d → ℝ)} (L : List (ℂ × List α))
    (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ) (hL : ∀ t ∈ L, t.2.length ≤ j)
    (hF : ∀ X, ContDiffOn ℝ ∞ (F X) O) : FamOK O (wfam L F c) j := by
  intro t ht
  rw [wfam, List.mem_append] at ht
  rcases ht with ht | ht
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    refine ⟨by simpa using hL t0 ht0, ?_⟩
    intro V hV
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hV
    exact hF X
  · simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, by simp⟩

theorem opCVOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCVOf := by
  intro hRw hCW k r z z' d O U κ Φ u hC hOm hCk hev j hj1 hjn
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨Ys, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r j hj1 hjn
  choose c hc using hev
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (Ys i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapROf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapROf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z' Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapLOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapLOf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VL κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).2), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VL κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • t.2.foldr Q.LdV u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).2, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ hΞ hcov
    rw [hS d _ L (VL κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ X hΞ ((hL t ht).2 X hX)])]
    exact hsym Ξ hΞ

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ParFamIntegrable
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Fam

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
  [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}

theorem parFam_add {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) (hg : PBI.ParFam k ρ U₀ g) :
    PBI.ParFam k ρ U₀ (fun q => f q + g q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', F', hU', hqU', hF', hgF⟩ := hg q₀ hq hG
  exact ⟨U ∩ U', fun q => F q + F' q, hU.inter hU', ⟨hqU, hqU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun q hq hG => by show f q + g q = F q + F' q; rw [hfF q hq.1 hG, hgF q hq.2 hG]⟩

theorem parFam_smul (a : ℂ) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U, fun q => a • F q, hU, hqU, hF.const_smul a, fun q hq hG => by show a • f q = a • F q; rw [hfF q hq hG]⟩

theorem parFam_zero : PBI.ParFam k ρ U₀ (fun _ => (0 : E)) := fun q₀ _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem parFam_sum {ι : Type} (s : Finset ι) {f : ι → Par × Mt k ρ → E}
    (hf : ∀ i ∈ s, PBI.ParFam k ρ U₀ (f i)) : PBI.ParFam k ρ U₀ (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (parFam_zero (E := E) (U₀ := U₀))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := parFam_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem parFam_contAt {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) {Z : Par} {y : Mt k ρ} (hq : (Z, y) ∈ U₀)
    (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun Z' => f (Z', y)) Z := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf (Z, y) hq hy
  have hci : Continuous fun Z' : Par => ((Z', y) : Par × Mt k ρ) := continuous_id.prodMk continuous_const
  have hm : {Z' | (Z', y) ∈ U} ∈ 𝓝 Z := hci.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  have hcF : ContinuousAt (fun Z' => F (Z', y)) Z :=
    ContinuousAt.comp (g := F) (f := fun Z' : Par => ((Z', y) : Par × Mt k ρ)) (x := Z)
      (hF.continuousOn.continuousAt (hU.mem_nhds hqU)) hci.continuousAt
  refine hcF.congr ?_
  filter_upwards [hm] with Z' hZ'
  exact (hfF (Z', y) hZ' hy).symm

theorem parFam_integrable [MeasurableSpace Par] [BorelSpace Par] {f : Par × Mt k ρ → E}
    (hf : PBI.ParFam k ρ U₀ f) {ν : Measure Par} [IsFiniteMeasure ν] {Kp : Set Par} (hK : IsCompact Kp)
    (hν : ν Kpᶜ = 0) {y : Mt k ρ} (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) (hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀) :
    Integrable (fun Z => f (Z, y)) ν := by
  have hc : ContinuousOn (fun Z => f (Z, y)) Kp := fun Z hZ =>
    (parFam_contAt hf (hKU Z hZ) hy).continuousWithinAt
  have hI : IntegrableOn (fun Z => f (Z, y)) Kp ν := hc.integrableOn_compact hK
  have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
    rw [ae_iff]
    simpa [Set.compl_def] using hν
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hI

end Fam

section Cls

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

def Rep {Par : Type} (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Z c y, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z y

def GGpos (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) : Set (Mt k ρ) := {y | 0 < Q.GGl k ρ z z' (Matrix.of y)}

variable (z z' π π') in

def Good (A : Module.End ℂ (Q.RadSp k ρ z z' π π')) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ → U₀ ⊆ Set.univ ×ˢ GGpos k ρ z z' →
  ∀ (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)), Rep Ψ Ψf →
    PBI.ParFam k ρ U₀ (fun q => Ψf q.1 q.2) →
  ∃ Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp), Rep (fun Z => A (Ψ Z)) Φf ∧ PBI.ParFam k ρ U₀ (fun q => Φf q.1 q.2) ∧
    (∀ K : Set (Par × Mt k ρ), (∀ q, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ K → Ψf q.1 q.2 = 0) →
      ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ closure K → Φf q.1 q.2 = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (Ψi : Q.RadSp k ρ z z' π π') (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Ψf Z y' ∂ν) →
      ∀ c, (A Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z y ∂ν

theorem good_id : Good z z' π π' (LinearMap.id : Module.End ℂ (Q.RadSp k ρ z z' π π')) := by
  intro Par _ _ _ _ _ U₀ _ _ Ψ Ψf hR hF
  refine ⟨Ψf, fun Z c y hy => hR Z c y hy, hF, fun K hK q _ hG hq => hK q hG (fun h => hq (subset_closure h)),
    fun ν _ Kp _ _ Ψi y V _ hyV hyG _ hi c => hi c y hyV hyG⟩

theorem good_comp {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A * B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hA Par U₀ hU₀ hUpos (fun Z => B (Ψ Z)) Φ₁ hR₁ hF₁
  refine ⟨Φ₂, fun Z c y hy => hR₂ Z c y hy, hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · have hK' : ∀ q', Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → q' ∉ closure K ∪ U₀ᶜ → Φ₁ q'.1 q'.2 = 0 := by
      intro q' hG' hq'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hq'
      exact hS₁ K hK q' hq'.2 hG' hq'.1
    refine hS₂ _ hK' q hq hG ?_
    rw [closure_union, hU₀.isClosed_compl.closure_eq, closure_closure]
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨hqK, hq⟩
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hi' : ∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (B Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Φ₁ Z y' ∂ν :=
      fun c y' hy' hG' => hW₁ ν Kp hKp hν Ψi y' V hV hy' hG' hKV hi c
    exact hW₂ ν Kp hKp hν (B Ψi) y V hV hyV hyG hKV hi' c

theorem good_add {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A + B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => Φ₁ Z y + Φ₂ Z y, fun Z c y hy => ?_, parFam_add hF₁ hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hR₁ Z c y hy, hR₂ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, hS₂ K hK q hq hG hqK, add_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, hW₂ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c,
      ← integral_add (parFam_integrable hF₁ hKp hν hyG hKU) (parFam_integrable hF₂ hKp hν hyG hKU)]

theorem good_smul (a : ℂ) {A : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) :
    Good z z' π π' (a • A) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => a • Φ₁ Z y, fun Z c y hy => ?_, parFam_smul a hF₁, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hR₁ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, integral_smul]

variable (z z' π π') in

def PGood (x : Q.Pr (Q.RadSp k ρ z z' π π')) : Prop := Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop

variable (z z' π π') in

def goodAlg : StarSubalgebra ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) where
  carrier := {x | PGood z z' π π' x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_comp hx1 hy1, good_comp hy2 hx2⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_add hx1 hy1, good_add hx2 hy2⟩
  algebraMap_mem' := by
    intro a
    have e1 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1 = a • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) a = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ a
    have e2 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop = (starRingEnd ℂ a) • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) (starRingEnd ℂ a) = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ _
    refine ⟨?_, ?_⟩
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1
      rw [e1]; exact good_smul a good_id
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop
      rw [e2]; exact good_smul _ good_id
  star_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, hx1⟩

theorem mem_goodAlg {x : Q.Pr (Q.RadSp k ρ z z' π π')} :
    x ∈ goodAlg z z' π π' ↔ Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop := Iff.rfl

theorem good_mkP {X Xs : Module.End ℂ (Q.RadSp k ρ z z' π π')} (h1 : Good z z' π π' X) (h2 : Good z z' π π' Xs) :
    Q.mkP X Xs ∈ goodAlg z z' π π' := ⟨h1, h2⟩

end Cls

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cell

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

open Classical in

def resW (h : Mx k r → V) (g : Mx k r) : (Fin r → ℂ) → V :=
  fun c' => if c' ∈ OmX r then resG k r (Fin.last r) h c' g else 0

theorem resG_contDiffAt (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V}
    (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r Bs.z Bs.z' g) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => resG k r (Fin.last r) h c' g) c₀ := by
  have hsf := Formalism.FourierDecayAlt.P5.Rad.sf_resG hh
  obtain ⟨U, F, hU, hxU, hF, hE⟩ := hsf (c₀, g)
    ⟨hc₀, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc₀ hg hG⟩ hg
  have hpre : IsOpen ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) := hU.preimage (by fun_prop)
  have hmem : c₀ ∈ (fun c : Fin r → ℂ => (c, g)) ⁻¹' U := hxU
  have hcd : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) c₀ := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) :=
      hF.comp (by fun_prop : ContDiff ℝ ∞ (fun c : Fin r → ℂ => (c, g))).contDiffOn (fun c hc => hc)
    exact h1.contDiffAt (hpre.mem_nhds hmem)
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [hpre.mem_nhds hmem] with c hc
  exact hE (c, g) hc hg

theorem resG_wsm (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) :
    resW h g ∈ WSm r V := by
  refine ⟨?_, fun x hx => by simp [resW, hx]⟩
  intro c hc
  have h1 := (resG_contDiffAt Bs hh hg hG hc).contDiffWithinAt (s := OmX r)
  refine h1.congr (fun c' hc' => by simp [resW, hc']) (by simp [resW, hc])

theorem wsm_resG_eq (h : Mx k r → V) (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    resW h g c = resG k r (Fin.last r) h c g := by
  simp [resW, hc]

theorem cell_diff (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : DifferentiableAt ℝ (fun c' => h (wCell k r (Fin.last r) c' * g)) c := by
  have hgl : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' * g ∈ Glev k r 0 := fun c' hc' =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc' _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hh (wCell k r (Fin.last r) c * g)
    ⟨hgl c hc, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hg hG⟩
  have hw : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (hw.continuousOn).continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  have hd : DifferentiableAt ℝ (fun c' => F (wCell k r (Fin.last r) c' * g)) c := by
    have hFd : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    have hwd : DifferentiableAt ℝ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
      (hw.differentiableOn (by simp)).differentiableAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
    exact hFd.comp c hwd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hU.mem_nhds hgU)]
    with c' h1 h2
  exact hE _ h2 (hgl c' h1)

end cell

section chain

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wsm_sub {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) : f - g ∈ WSm r V :=
  (WSm r V).sub_mem hf hg

theorem opL_mem (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) : opL l i f ∈ WSm r V :=
  preserved_operators_holds r V l i f hf

theorem opL_sub (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f - g) = opL l i f - opL l i g := by
  have hng : (-1 : ℂ) • g ∈ WSm r V := (WSm r V).smul_mem _ hg
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, (linear_operators_holds r V l i f _ 1 hf hng).1, (linear_operators_holds r V l i g g (-1) hg hg).2, neg_one_smul,
    sub_eq_add_neg]

theorem opL_add (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f + g) = opL l i f + opL l i g :=
  (linear_operators_holds r V l i f g 1 hf hg).1

theorem opL_smul (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (a : ℂ) :
    opL l i (a • f) = a • opL l i f :=
  (linear_operators_holds r V l i f f a hf hf).2

theorem pOp_zero (l : Fin r) : pOp l (fun _ : Fin r → ℂ => (0 : V)) = fun _ => 0 := by
  funext x; unfold pOp wirt; split_ifs <;> simp

theorem vAB_mem (y : ℂ) : ∀ (i : ℕ) {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V
  | 0, G, hG => ⟨hG, (WSm r V).zero_mem⟩
  | i + 1, G, hG => by
    obtain ⟨hA, hB⟩ := vAB_mem y i hG
    by_cases hi : i < r
    · simp only [vAB, dif_pos hi]
      refine ⟨wsm_sub ((WSm r V).add_mem ((WSm r V).smul_mem y hA) (opL_mem ⟨i, hi⟩ 0 hA))
        (opL_mem ⟨i, hi⟩ 1 hB), opL_mem ⟨i, hi⟩ 2 hA⟩
    · simp only [vAB, dif_neg hi]
      exact ⟨hA, hB⟩

theorem vAB_lin (y : ℂ) : ∀ (i : ℕ) {G₁ G₂ : (Fin r → ℂ) → V}, G₁ ∈ WSm r V → G₂ ∈ WSm r V → ∀ s : ℂ,
    (vAB r y i).1 (G₁ + s • G₂) = (vAB r y i).1 G₁ + s • (vAB r y i).1 G₂ ∧
      (vAB r y i).2 (G₁ + s • G₂) = (vAB r y i).2 G₁ + s • (vAB r y i).2 G₂
  | 0, G₁, G₂, _, _, s => ⟨rfl, by show (0 : (Fin r → ℂ) → V) = 0 + s • 0; simp⟩
  | i + 1, G₁, G₂, h₁, h₂, s => by
    obtain ⟨ih1, ih2⟩ := vAB_lin y i h₁ h₂ s
    obtain ⟨hA₁, hB₁⟩ := vAB_mem y i h₁
    obtain ⟨hA₂, hB₂⟩ := vAB_mem y i h₂
    have hsA := (WSm r V).smul_mem s hA₂
    have hsB := (WSm r V).smul_mem s hB₂
    by_cases hi : i < r
    · simp only [vAB, dif_pos hi]
      rw [ih1, ih2]
      refine ⟨?_, ?_⟩
      · have e1 : pOp ⟨i, hi⟩ ((vAB r y i).1 G₁ + s • (vAB r y i).1 G₂) =
            pOp ⟨i, hi⟩ ((vAB r y i).1 G₁) + s • pOp ⟨i, hi⟩ ((vAB r y i).1 G₂) := by
          rw [show pOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 0 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
        have e2 : cOp ⟨i, hi⟩ ((vAB r y i).2 G₁ + s • (vAB r y i).2 G₂) =
            cOp ⟨i, hi⟩ ((vAB r y i).2 G₁) + s • cOp ⟨i, hi⟩ ((vAB r y i).2 G₂) := by
          rw [show cOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 1 from rfl, opL_add _ _ hB₁ hsB, opL_smul _ _ hB₂]
        rw [e1, e2]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add, smul_sub]
        rw [smul_comm y s]
        abel
      · rw [show ciOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 2 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
    · simp only [vAB, dif_neg hi]
      exact ⟨ih1, ih2⟩

theorem vAB_comm (y : ℂ) (j : Fin r) : ∀ (i : ℕ), i ≤ j.val → ∀ {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V ∧
      (vAB r y i).1 (pOp j G) = pOp j ((vAB r y i).1 G) ∧ (vAB r y i).2 (pOp j G) = pOp j ((vAB r y i).2 G)
  | 0, _, G, hG => ⟨hG, (WSm r V).zero_mem, rfl, by simp only [vAB]; exact (pOp_zero j).symm⟩
  | i + 1, hij, G, hG => by
    obtain ⟨hA, hB, c1, c2⟩ := vAB_comm y j i (by omega) hG
    have hpG : pOp j G ∈ WSm r V := opL_mem j 0 hG
    have hi : i < r := by have := j.isLt; omega
    have hne : (⟨i, hi⟩ : Fin r) ≠ j := by intro h; rw [← h] at hij; simp at hij
    obtain ⟨hm1, hm2⟩ := vAB_mem y (i + 1) hG
    refine ⟨hm1, hm2, ?_, ?_⟩
    · simp only [vAB, dif_pos hi]
      rw [c1, c2]
      have hpA : pOp ⟨i, hi⟩ ((vAB r y i).1 G) ∈ WSm r V := opL_mem _ 0 hA
      have hcB : cOp ⟨i, hi⟩ ((vAB r y i).2 G) ∈ WSm r V := opL_mem _ 1 hB
      have hyA : y • (vAB r y i).1 G ∈ WSm r V := (WSm r V).smul_mem y hA
      rw [show pOp j = opL j 0 from rfl, opL_sub _ _ ((WSm r V).add_mem hyA hpA) hcB,
        opL_add _ _ hyA hpA, opL_smul _ _ hA]
      have k1 : opL j 0 (pOp ⟨i, hi⟩ ((vAB r y i).1 G)) = pOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).1 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 0 _ hA (Or.inl (Ne.symm hne)))
      have k2 : opL j 0 (cOp ⟨i, hi⟩ ((vAB r y i).2 G)) = cOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).2 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 1 _ hB (Or.inl (Ne.symm hne)))
      rw [k1, k2]
    · simp only [vAB, dif_pos hi]
      rw [c1]
      exact (commuting_functional_holds r V j ⟨i, hi⟩ 0 2 _ hA (Or.inl (Ne.symm hne))).symm

end chain

end Formalism.FourierDecayAlt.P.PBN.MC
end
end


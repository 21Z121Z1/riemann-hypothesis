import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersection
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.CloseLevi

variable {n : ℕ} {ε : Fin n → Bool}

theorem isClosed_stab {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) := GlobalTheory.FlagLeviGroup.continuous_uMat
  have h : {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} =
      ⋂ i, ⋂ y ∈ (W i : Set (Fin n → ℂ)),
        (fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  exact (W i).closed_of_finiteDimensional.preimage (hc.matrix_mulVec continuous_const)

theorem mem_flagM_of_keeps {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {l : Formalism.REAL.UJ ε}
    (hl : l ∈ maxK ε) (h : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i) : l ∈ flagM ε W := by
  have hl' : (uMat l)ᴴ * uMat l = 1 := hl
  show ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i
  intro i y hy
  exact ⟨h i y hy, GlobalTheory.FlagLeviGroup.inv_keeps hl' (W i) (h i) y hy⟩

private theorem exists_unit_valuation_le_subset_nhds {G : Type} [Group G] [TopologicalSpace G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {O : Set G} (hO : IsOpen O) (h1O : (1 : G) ∈ O) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ g, f g < ρ → g ∈ O := by
  have hC : IsCompact ({g | f g ≤ 1} ∩ Oᶜ) := hB.inter_right hO.isClosed_compl
  rcases ({g | f g ≤ 1} ∩ Oᶜ).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨le_of_lt hg, hgO⟩
    rw [hE] at hgC
    simpa using hgC
  · obtain ⟨c, ⟨_, hcO⟩, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
    have hc : 0 < f c := by
      rcases (h0 c).lt_or_eq with h | h
      · exact h
      · exfalso
        have hc1 : c = 1 := (h1 c).1 h.symm
        rw [hc1] at hcO
        exact absurd h1O hcO
    refine ⟨min 1 (f c), lt_min one_pos hc, fun g hg => ?_⟩
    by_contra hgO
    have hgC : g ∈ ({g | f g ≤ 1} ∩ Oᶜ) := ⟨(lt_of_lt_of_le hg (min_le_left _ _)).le, hgO⟩
    have hcg : f c ≤ f g := isMinOn_iff.1 hmin g hgC
    exact absurd (lt_of_lt_of_le hg (min_le_right _ _)) (not_lt.2 hcg)

theorem close_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) (h1 : ∀ g, f g = 0 ↔ g = 1) (hB : IsCompact {g | f g ≤ 1})
    {K P L : Set G} (hK : IsCompact K) (hP : IsClosed P) (hL : ∀ k ∈ K, k⁻¹ ∈ P → k⁻¹ ∈ L) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ P, ∀ k ∈ K, f (p * k) ≤ r → ∃ l ∈ L, f (l * k) < t := by

  have hloc : ∀ k ∈ K, ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k),
      ∀ p ∈ P, f (p * z.2) ≤ z.1 → ∃ l ∈ L, f (l * z.2) < t := by
    intro k hk
    by_cases hkP : k⁻¹ ∈ P
    ·
      have hkL := hL k hk hkP
      have hc : Continuous fun x : G => f (k⁻¹ * x) := hf.comp (continuous_const.mul continuous_id)
      have hopen : IsOpen {x : G | f (k⁻¹ * x) < t} := isOpen_lt hc continuous_const
      have hmem : k ∈ {x : G | f (k⁻¹ * x) < t} := by
        show f (k⁻¹ * k) < t
        rw [inv_mul_cancel, (h1 1).2 rfl]
        exact ht
      have hev : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ {x : G | f (k⁻¹ * x) < t} :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hopen.mem_nhds hmem)
      filter_upwards [hev] with z hz
      intro p _ _
      exact ⟨k⁻¹, hkL, hz⟩
    ·
      have hcont : Continuous (fun q : G × G => q.1 * q.2⁻¹) := continuous_fst.mul continuous_snd.inv
      have hopen : IsOpen ((fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ) := hP.isOpen_compl.preimage hcont
      have hmem : ((1 : G), k) ∈ (fun q : G × G => q.1 * q.2⁻¹) ⁻¹' Pᶜ := by
        show (1 : G) * k⁻¹ ∈ Pᶜ
        rw [one_mul]
        exact hkP
      obtain ⟨O, V, hO, hV, h1O, hkV, hOV⟩ := isOpen_prod_iff.1 hopen 1 k hmem
      obtain ⟨ρ, hρ, hρO⟩ := exists_unit_valuation_le_subset_nhds hf h0 h1 hB hO h1O
      have e1 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.1 < ρ :=
        (continuous_fst.tendsto ((0 : ℝ), k)).eventually (gt_mem_nhds hρ)
      have e2 : ∀ᶠ z : ℝ × G in nhds ((0 : ℝ), k), z.2 ∈ V :=
        (continuous_snd.tendsto ((0 : ℝ), k)).eventually_mem (hV.mem_nhds hkV)
      filter_upwards [e1, e2] with z hz1 hz2
      intro p hp hpz
      exfalso
      have hO' : p * z.2 ∈ O := hρO _ (lt_of_le_of_lt hpz hz1)
      have hmem' := hOV (Set.mk_mem_prod hO' hz2)
      simp only [Set.mem_preimage, mul_inv_cancel_right, Set.mem_compl_iff] at hmem'
      exact hmem' hp
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun r x => ∀ p ∈ P, f (p * x) ≤ r → ∃ l ∈ L, f (l * x) < t) hloc
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := eventually_mem_nhdsWithin
  obtain ⟨r, hr, hrK⟩ := (hpos.and (hev.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨r, hr, fun p hp k hk hpk => hrK k hk p hp hpk⟩

theorem nrm_uMat_eq_zero (g : Formalism.REAL.UJ ε) : nrm (uMat g - 1) = 0 ↔ g = 1 := by
  rw [nrm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    apply Subtype.ext
    exact Units.ext h
  · rintro rfl
    exact GlobalTheory.FlagLeviGroup.uMat_one

theorem close_levi : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧
    ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r →
      ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  intro n ε a j W hW t ht

  have hL : ∀ k ∈ maxK ε, k⁻¹ ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} →
      k⁻¹ ∈ maxK ε ∩ flagM ε W := by
    intro k hk hkP
    have hk' : k⁻¹ ∈ maxK ε := (GlobalTheory.FlagLeviGroup.compactSub ε).inv_mem hk
    exact Set.mem_inter hk' (mem_flagM_of_keeps W hk' hkP)
  obtain ⟨r, hr, hrP⟩ := close_of_compact (G := Formalism.REAL.UJ ε) (f := fun g => nrm (uMat g - 1))
    (continuous_nrm_uMat ε) (fun g => nrm_nonneg _) (fun g => nrm_uMat_eq_zero g) (isCompact_hsBall ε 1)
    (isCompact_maxK ε) (isClosed_stab W) hL ht
  refine ⟨r, hr, fun u hu m hm k hk hle => ?_⟩
  have hm' : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
  have hum : u * m ∈ {g : Formalism.REAL.UJ ε | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i} := by
    rw [Set.mem_setOf_eq]
    intro i y hy
    rw [GlobalTheory.FlagLeviGroup.uMat_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FlagMeas.UnipRad.keeps hW u hu i _ (hm' i y hy).1
  exact hrP (u * m) hum k hk hle

end GlobalTheory.IwConst.CloseLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwDelta

variable {n : ℕ}

theorem exists_cont_detOn (V : Submodule ℂ (Fin n → ℂ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ → ℝ, Continuous D ∧
      ∀ X, (∀ y ∈ V, X *ᵥ y ∈ V) → detOn X V = D X := by
  obtain ⟨U, hVU⟩ := Submodule.exists_isCompl V
  let p := Submodule.projectionOnto V U hVU
  let b := Module.finBasis ℂ V
  refine ⟨fun X => ‖(Matrix.of fun i k => b.repr (p (X *ᵥ (b k : Fin n → ℂ))) i).det‖, ?_, ?_⟩
  · apply Continuous.norm
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i k
    have hlin : Continuous fun y : Fin n → ℂ => b.repr (p y) i :=
      ((b.coord i).comp p).continuous_of_finiteDimensional
    exact hlin.comp (continuous_id.matrix_mulVec continuous_const)
  · intro X hX
    have h' : ∀ y ∈ V, Matrix.toLin' X y ∈ V := fun y hy => by
      simpa [Matrix.toLin'_apply] using hX y hy
    have e : ∀ k, p (X *ᵥ (b k : Fin n → ℂ)) = (Matrix.toLin' X).restrict h' (b k) := by
      intro k
      have hp : p (X *ᵥ (b k : Fin n → ℂ)) = ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩ :=
        Submodule.projectionOnto_apply_left hVU ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩
      rw [hp]
      apply Subtype.ext
      simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
    rw [detOn, dif_pos h', ← LinearMap.det_toMatrix b]
    congr 2
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.of_apply, e k]

theorem detOn_one (V : Submodule ℂ (Fin n → ℂ)) : detOn (1 : Matrix (Fin n) (Fin n) ℂ) V = 1 := by
  have h' : ∀ y ∈ V, Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) y ∈ V := fun y hy => by simpa using hy
  rw [detOn, dif_pos h']
  have hid : (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ)).restrict h' = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by simp [LinearMap.restrict_apply])
  rw [hid, LinearMap.det_id, norm_one]

private theorem detOn_le_one_of_unitary_of_invariant (U : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ))
    (hU : Uᴴ * U = 1) (hV : ∀ y ∈ V, U *ᵥ y ∈ V) : detOn U V ≤ 1 := by
  obtain ⟨D, hDc, hD⟩ := exists_cont_detOn V
  have hKc : IsCompact {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} := by
    have hcl : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
        Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin n) (Fin n) ℂ)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset hcl ?_
    intro X hX
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i k
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hX) i k
  have hUg : U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hU
  have hpow : ∀ k : ℕ, (∀ y ∈ V, U ^ k *ᵥ y ∈ V) ∧ detOn (U ^ k) V = detOn U V ^ k := by
    intro k
    induction k with
    | zero => exact ⟨fun y hy => by simpa using hy, by simpa using detOn_one V⟩
    | succ k ih =>
      have hs : ∀ y ∈ V, U ^ (k + 1) *ᵥ y ∈ V := fun y hy => by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih.1 _ (hV y hy)
      refine ⟨hs, ?_⟩
      rw [pow_succ, GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ V ih.1 hV, ih.2, pow_succ]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hDc.continuousOn
  by_contra hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have hmem : (U ^ k)ᴴ * U ^ k = 1 := Matrix.mem_unitaryGroup_iff'.1 (pow_mem hUg k)
  have hb := hC (U ^ k) hmem
  rw [← hD _ (hpow k).1, (hpow k).2, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (GlobalTheory.FlagMeas.SizeMove.detOn_nonneg U V) k)] at hb
  linarith

theorem detOn_le_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) ≤ 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  exact detOn_le_one_of_unitary_of_invariant _ _ hl.1 (fun y hy => (hl2 i y hy).1)

theorem detOn_eq_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) = 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  have hU : (uMat l)ᴴ * uMat l = 1 := hl.1
  have hU' : (uMat l)ᴴᴴ * (uMat l)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have h1 := detOn_le_one hl i
  have h2 := detOn_le_one_of_unitary_of_invariant _ (W i) hU' (fun y hy => (hl2 i y hy).2)
  have hprod : detOn ((uMat l)ᴴ) (W i) * detOn (uMat l) (W i) = 1 := by
    rw [← GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ _ (fun y hy => (hl2 i y hy).2) (fun y hy => (hl2 i y hy).1), hU,
      detOn_one]
  have h3 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg (uMat l) (W i)
  have h4 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg ((uMat l)ᴴ) (W i)
  exact le_antisymm h1 (by nlinarith)

theorem measurable_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n 1 j τ id := by
  unfold layerProd
  fun_prop

theorem continuousAt_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Filter.Tendsto (fun τ : Fin a → ℝ => layerProd n 1 j τ id) (nhds 1) (nhds 1) := by
  have hc : ContinuousAt (fun τ : Fin a → ℝ => layerProd n 1 j τ id) 1 := by
    unfold layerProd
    fun_prop (disch := simp)
  have h1 : layerProd n 1 j (1 : Fin a → ℝ) id = 1 := by simp [layerProd]
  simpa [h1] using hc.tendsto

open scoped Matrix.Norms.Frobenius in
theorem exists_ball {s : Set (Matrix (Fin n) (Fin n) ℂ)} (hs : s ∈ nhds 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ X, nrm (X - 1) < t → X ∈ s := by
  obtain ⟨t, ht, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨t, ht, fun X hX => hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← nrm_eq]
  exact hX

theorem dlt_props : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  intro n ε a j W
  refine ⟨?_, ?_, ?_⟩
  · unfold dlt
    exact ENNReal.measurable_ofReal.comp ((measurable_layerProd j).comp
      (measurable_pi_lambda _ fun i => measurable_locSize_uMat n ε a j W i))
  · intro l hl m hm
    have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hmul : uMat (m * l) = uMat m * uMat l := rfl
    have hloc : locSize j W (uMat (m * l)) = locSize j W (uMat m) := by
      funext i
      simp only [locSize]
      rw [hmul,
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.succ) (fun y hy => (hm2 i.succ y hy).1)
          (fun y hy => (hl2 i.succ y hy).1),
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.castSucc) (fun y hy => (hm2 i.castSucc y hy).1)
          (fun y hy => (hl2 i.castSucc y hy).1),
        detOn_eq_one hl i.succ, detOn_eq_one hl i.castSucc, mul_one, mul_one]
    unfold dlt
    rw [hloc]
  · intro η hη
    choose D hDc hD using fun i : Fin (a + 1) => exists_cont_detOn (W i)
    have hD1 : ∀ i, D i 1 = 1 := fun i => by
      rw [← hD i 1 (fun y hy => by simpa using hy), detOn_one]
    set G : Matrix (Fin n) (Fin n) ℂ → Fin a → ℝ :=
      fun X i => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i) with hGdef
    have hG : Filter.Tendsto G (nhds 1) (nhds 1) := by
      rw [tendsto_pi_nhds]
      intro i
      have hc : ContinuousAt (fun X => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i)) 1 :=
        ((hDc _).continuousAt.div (hDc _).continuousAt (by simp [hD1])).rpow_const
          (Or.inl (by simp [hD1]))
      have ht := hc.tendsto
      simp only [hD1, div_one, Real.one_rpow] at ht
      exact ht
    have hF := (continuousAt_layerProd (n := n) j).comp hG
    have hpos : 0 < 1 + η := by linarith
    have hU : Set.Ioo (1 / (1 + η)) (1 + η) ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds ((div_lt_one hpos).2 (by linarith)) (by linarith)
    obtain ⟨t, ht, hball⟩ := exists_ball (Filter.tendsto_def.1 hF _ hU)
    refine ⟨t, ht, fun m hm hmt => ?_⟩
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hin := hball _ hmt
    have hGm : G (uMat m) = locSize j W (uMat m) := by
      funext i
      simp only [hGdef, locSize]
      rw [hD i.succ _ (fun y hy => (hm2 i.succ y hy).1), hD i.castSucc _ (fun y hy => (hm2 i.castSucc y hy).1)]
    simp only [Set.mem_preimage, Function.comp_apply, hGm, Set.mem_Ioo] at hin
    obtain ⟨hlo, hhi⟩ := hin
    unfold dlt
    refine ⟨ENNReal.ofReal_le_ofReal hhi.le, ?_⟩
    rw [← ENNReal.ofReal_mul hpos.le, ENNReal.one_le_ofReal]
    rw [div_lt_iff₀ hpos] at hlo
    linarith [mul_comm (layerProd n 1 j (locSize j W (uMat m)) id) (1 + η)]

end GlobalTheory.IwDelta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebra
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwTangent

variable {n : ℕ}

open scoped Matrix.Norms.Frobenius

theorem coe_smul_eq (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : (t : ℂ) • X = t • X := by
  ext i j; simp

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hs' := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at hs'
  have hc : IsClosed (A : Set (Matrix (Fin n) (Fin n) ℂ)) := A.closed_of_finiteDimensional
  exact hc.mem_of_tendsto hs'.tendsto_sum_nat (Filter.Eventually.of_forall fun m =>
    A.sum_mem fun k _ => A.smul_mem _ (hp k))

theorem mem_of_exp_sub_one_mem (T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) - 1 ∈ T) : X ∈ T := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  have hc : IsClosed (T : Set (Matrix (Fin n) (Fin n) ℂ)) := T.closed_of_finiteDimensional
  refine hc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  simp only [zero_add, zero_smul, NormedSpace.exp_zero]
  exact T.smul_mem _ (h t)

theorem exists_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    ∃ g : Formalism.REAL.UJ ε, uMat g = NormedSpace.exp (t • X) :=
  ⟨GlobalTheory.GaugeConst.expJ ε ⟨t • X, (GlobalTheory.GaugeConst.lieJ ε).smul_mem t hX⟩, rfl⟩

theorem lie_algebra_of_isCut : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  rintro n ε S d E ⟨A, hA, -, hE, rfl⟩
  simp only [coe_smul_eq]
  have h1 : ∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ,
      ∃ g ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A}, uMat g = NormedSpace.exp (t • X) := by
    intro X hX t
    obtain ⟨hXA, hXG⟩ := (hE X).2 hX
    obtain ⟨g, hg⟩ := exists_exp hXG t
    refine ⟨g, ?_, hg⟩
    change uMat g - 1 ∈ A
    rw [hg]
    exact exp_sub_one_mem A hA (A.smul_mem t hXA)
  refine ⟨h1, fun T hT i => mem_of_exp_sub_one_mem T _ fun t => ?_, fun X hX h => (hE X).1 ⟨?_, hX⟩⟩
  · obtain ⟨g, hg, hg'⟩ := h1 (E i) (Submodule.subset_span ⟨i, rfl⟩) t
    rw [← hg']
    exact hT g hg
  · refine mem_of_exp_sub_one_mem A _ fun t => ?_
    obtain ⟨g, hg⟩ := exists_exp hX t
    rw [← hg]
    exact h t g hg

end GlobalTheory.IwTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAdaptedIsometryFrameUpperTriangularExpansio
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Sloc.AdaptExpand

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem exists_coeff {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ l : Fin D.R.rS → D.host.E, (∀ i, b.val ≤ i.val → l i = 0) ∧ x = ∑ i, l i • F.fl.e i := by
  have hx' : x ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < b.val}) := hx
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx'
  obtain ⟨l, hl, rfl⟩ := hx'
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra h
    have := hl (Finsupp.mem_support_iff.2 h)
    simp only [Set.mem_setOf_eq] at this
    omega
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

theorem exists_coeff_frame {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ u : Fin (D.R.rS + 1) → D.host.E, (∀ c, b ≤ c → u c = 0) ∧ x = ∑ c, u c • frame F c := by
  obtain ⟨l, hl, rfl⟩ := exists_coeff F b x hx
  refine ⟨Fin.snoc (α := fun _ => D.host.E) l 0, fun c hc => ?_, ?_⟩
  · induction c using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hl i (by simpa [Fin.le_def] using hc)
  · rw [Fin.sum_univ_castSucc]
    simp [frame_castSucc]

theorem adapt_expand : ∀ (D : D7) {T : D.host.E} (F0 F : LFlag (VS D) D.R.rS T) (g : GV D), Adapt g F0 F → ∀ (Z : LocDat D) (p : PlF D) (Af : Fin (D.R.rS + 1) → Vp D p), Af = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) → ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = Ring.inverse (frFac Z.δ p a)) ∧ ∀ b, baseChange₂ D p (g (frame F0 b)) = ∑ a, B a b • Af a := by
  intro D T F0 F g hg Z p Af hAf
  subst hAf
  have hu := fun c => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p c
  choose u hu0 hux using fun b => exists_coeff_frame F b _ (hg.2 b)
  refine ⟨fun a b => ((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a),
    fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp [hu0 b a hab.le, (ne_of_lt hab).symm]
  · simp [hu0 a a le_rfl]
  · have e1 : g (frame F0 b) = frame F b + ∑ c, u b c • frame F c := by
      rw [← hux b]; abel
    rw [e1, map_add, map_sum]
    simp only [baseChange_smul₂]
    have e2 : ∀ a, (((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a)) •
        (frFac Z.δ p a • baseChange₂ D p (frame F a)) =
        (D.s.atP p).ιE (u b a) • baseChange₂ D p (frame F a) + if a = b then baseChange₂ D p (frame F a) else 0 := by
      intro a
      rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel _ (hu a), mul_one, add_smul]
      split_ifs <;> simp
    simp only [e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel

end GlobalTheory.Sloc.AdaptExpand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFactsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_tuples_topological_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  first | exact @GlobalTheory.LocalUnitaryTop.top_facts | exact GlobalTheory.LocalUnitaryTop.top_facts | (intros; apply GlobalTheory.LocalUnitaryTop.top_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSumStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_bound_low_types_sum : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν (q : ℕ), n1 ν + (r + 1) * q ≤ q0 → (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) := by
  first | exact @GlobalTheory.MomOne.moment_one | exact GlobalTheory.MomOne.moment_one | (intros; apply GlobalTheory.MomOne.moment_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedRowLatticeTermIsLatticeStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedRowLattice_term_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  first | exact @GlobalTheory.HL.term_lat_isLattice | exact GlobalTheory.HL.term_lat_isLattice | (intros; apply GlobalTheory.HL.term_lat_isLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isometry_extends_local_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (p : PlF D), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃ g, Ext p γ g ∧ LocNG.IsUnitary (locH Z p) g ∧ (∀ g', Ext p γ g' → g' = g) ∧ (∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap γ Λ)) ∧ ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), γ ∈ Formalism.L2.SG.NGData.NRat F → g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  first | exact @GlobalTheory.LocExt.ext_isometry | exact GlobalTheory.LocExt.ext_isometry | (intros; apply GlobalTheory.LocExt.ext_isometry <;> assumption)
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0198
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInvLower
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeProdLayersUnipotent
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool} {d : ℕ}

theorem continuous_uMat_sub_one : Continuous fun g : UJ ε => uMat g - 1 :=
  (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

theorem continuous_coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1) :=
  continuous_pi fun i => (ipL (E i)).continuous_of_finiteDimensional.comp continuous_uMat_sub_one

theorem continuous_hs_sub_one : Continuous fun g : UJ ε => hs (uMat g - 1) := by
  unfold hs
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_uMat_sub_one.matrix_elem i j).norm).pow 2

theorem mul_sub_one (g h : UJ ε) :
    uMat (g * h) - 1 = (uMat g - 1) + (uMat h - 1) + (uMat g - 1) * (uMat h - 1) := by
  have : uMat (g * h) = uMat g * uMat h := rfl
  rw [this]; noncomm_ring

theorem measurePreserving_coord {m : ℕ} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}
    (hle : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {ν : Measure (UJ ε)} (hν : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ν) :
    MeasurePreserving (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ν volume := by
  have hE0 : ∀ i, E i ∈ A 0 ∧ inG ε (E i) := fun i =>
    (hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hsp0 : ∀ X, (X ∈ A 0 ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E) := fun X => by
    simpa using hsp 0 X
  have hmul0 : ∀ X ∈ A 0, ∀ Y ∈ A 0, X * Y ∈ A 0 := fun X hX Y hY => hle 0 (hmul 0 X hX Y hY).1
  obtain ⟨σ, hσc, hσ⟩ := GlobalTheory.T.exists_orthonormal_lie_coordinates n d m ε A E hm hmul hle hinv hE hE0
  have hσ2 : ∀ x i, ipL (E i) (uMat (σ x) - 1) = x i := fun x => (hσ x).2
  have hinj : ∀ g h : UJ ε, uMat g - 1 ∈ A 0 → uMat h - 1 ∈ A 0 →
      (∀ i, ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) → g = h := by
    intro g h hg hh hc
    have := sub_mem_of_coord_eq hmul hinv hE hsp hg hh m fun i _ => hc i
    rw [hm, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext (Units.ext this)
  have hS : MeasurableSet {g : UJ ε | uMat g - 1 ∈ A 0} :=
    ((A 0).closed_of_finiteDimensional.preimage continuous_uMat_sub_one).measurableSet
  have hμ : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ((volume : Measure (Fin d → ℝ)).map σ) := by
    refine ⟨?_, fun s hs => ?_, ?_⟩
    · rw [Measure.map_apply hσc.measurable hS.compl]
      convert measure_empty (μ := (volume : Measure (Fin d → ℝ)))
      ext x
      simpa using (hσ x).1
    · have hs' : uMat s - 1 ∈ A 0 := hs
      have hT := GlobalTheory.T.measurePreserving_add_of_triangular d deg (fun x i => ipL (E i) (uMat (s * σ x) - 1) - x i)
        (((continuous_coord E).comp (continuous_const.mul hσc)).sub continuous_id).measurable (by
          intro x y i hxy
          have h1 := sub_mem_of_coord_eq hmul hinv hE hsp (hσ x).1 (hσ y).1 (deg i) fun k hk => by
            rw [hσ2, hσ2, hxy k hk]
          have h2 := ipL_eq_zero_of_mem hE (fun i => (hE0 i).2) (hinv (deg i + 1))
            (fun X => (hsp (deg i + 1) X).1) (i := i) (by simp) (hmul _ _ h1 _ hs').2
          have h3 : (uMat s - 1) * (uMat (σ x) - uMat (σ y)) =
              (uMat s - 1) * (uMat (σ x) - 1) - (uMat s - 1) * (uMat (σ y) - 1) := by noncomm_ring
          rw [h3, map_sub] at h2
          simp only [mul_sub_one, map_add, hσ2]
          linarith)
      have he : (fun g => s * g) ∘ σ =
          σ ∘ fun x => x + fun i => ipL (E i) (uMat (s * σ x) - 1) - x i := by
        funext x
        refine hinj _ _ ?_ (hσ _).1 fun i => ?_
        · simp only [Function.comp, mul_sub_one]
          exact (A 0).add_mem ((A 0).add_mem hs' (hσ x).1) (hmul0 _ hs' _ (hσ x).1)
        · simp only [Function.comp, hσ2, Pi.add_apply]
          ring
      rw [Measure.map_map (measurable_const_mul s) hσc.measurable, he,
        ← Measure.map_map hσc.measurable hT.measurable, hT.map_eq]
    · have hest := fun x => GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup n d ε E hE (fun i => (hE0 i).2) (σ x)
        ((hsp0 _).1 ⟨(A 0).sub_mem (hσ x).1 (hinv 0 _ (hσ x).1), inG_sub_inv _⟩)
      simp only [(hσ _).2] at hest
      have h0 : σ 0 = 1 := hinj _ _ (hσ 0).1 (by simp [uMat]) fun i => by
        rw [hσ2]; simp [uMat]
      have := GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball d (fun x => hs (uMat (σ x) - 1))
        (continuous_hs_sub_one.comp hσc).continuousAt (by simp [h0, uMat, hs])
        (fun x => (hest x).1) (fun x => (hest x).2)
      refine this.congr fun r => ?_
      rw [Measure.map_apply hσc.measurable
        (isClosed_le continuous_hs_sub_one.sqrt continuous_const).measurableSet]
      rfl
  have heq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε (A 0) d E hmul0 hE hsp0 ν hν).2.2.1 _ hμ
  refine ⟨(continuous_coord E).measurable, ?_⟩
  rw [← heq, Measure.map_map (continuous_coord E).measurable hσc.measurable]
  have : (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ∘ σ = id := by
    funext x i
    exact hσ2 x i
  rw [this, Measure.map_id]

theorem covol_le_prod_layers : ∀ (ι : Type) [Fintype ι] (n d m : ℕ) (ε : ι → Fin n → Bool) (A : ι → ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), (∀ v c, A v (c + 1) ≤ A v c) → (∀ v, A v m = ⊥) → (∀ v c, ∀ X ∈ A v c, ∀ Y ∈ A v 0, X * Y ∈ A v (c + 1) ∧ Y * X ∈ A v (c + 1)) → (∀ v c, ∀ X ∈ A v c, Formalism.REAL.Jm (ε v) * Xᴴ * Formalism.REAL.Jm (ε v) ∈ A v c) → (∀ v i k, ((E v i * (E v k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ v c X, (X ∈ A v c ∧ Formalism.REAL.inG (ε v) X) ↔ X ∈ Submodule.span ℝ (E v '' {i | c ≤ deg i})) → ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (ε v))) [∀ v, SigmaFinite (ν v)], (∀ v, IsGaugeSub {g | uMat g - 1 ∈ A v 0} d (ν v)) → ∀ (Γ : Subgroup (∀ v, Formalism.REAL.UJ (ε v))) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (∀ γ ∈ Γ, ∀ v, uMat (γ v) - 1 ∈ A v 0) → (∀ c, MeasurableSet (D c)) → (∀ (c : ℕ) (x : ι → {i : Fin d // deg i = c} → ℝ), ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ A v c) ∧ (fun v (i : {i : Fin d // deg i = c}) => (((uMat (γ v) - 1) * (E v i.1)ᴴ).trace).re + x v i) ∈ D c) → covol (Γ : Set (∀ v, Formalism.REAL.UJ (ε v))) (Measure.pi ν) {g | ∀ v, uMat (g v) - 1 ∈ A v 0} ≤ ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ n d m ε A E deg hle hm hmul hinv hE hsp ν _ hν Γ D hΓ hD hcov
  have hE0 : ∀ v i, E v i ∈ A v 0 ∧ inG (ε v) (E v i) := fun v i =>
    (hsp v 0 (E v i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hanti : ∀ v, Antitone (A v) := fun v => antitone_nat_of_succ_le (hle v)
  have horth : ∀ v c i, deg i < c → ∀ X ∈ A v c, ipL (E v i) X = 0 := fun v c i hi X hX =>
    ipL_eq_zero_of_mem (hE v) (fun i => (hE0 v i).2) (hinv v c) (fun X => (hsp v c X).1)
      (by simpa using hi) hX
  have hdeg : ι → ∀ i, deg i < m := by
    intro v i
    by_contra hi
    have h1 := ((hsp v m (E v i)).2 (Submodule.subset_span ⟨i, not_lt.1 hi, rfl⟩)).1
    rw [hm, Submodule.mem_bot] at h1
    have := hE v i i
    simp [h1] at this
  have hmp := measurePreserving_pi ν (fun _ => (volume : Measure (Fin d → ℝ))) fun v =>
    measurePreserving_coord (hle v) (hm v) (hmul v) (hinv v) (hE v) (hsp v) (hν v)
  have hB : MeasurableSet {x : ι → Fin d → ℝ |
      ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (show Measurable fun (x : ι → Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => x v i.1 by
      fun_prop) (hD c)
  rw [← GlobalTheory.T.volume_product_over_grading_layers ι d m deg D hdeg hD]
  refine le_trans ?_ (hmp.measure_preimage hB.nullMeasurableSet).le
  refine iInf_le_of_le _ (iInf_le_of_le (hmp.measurable hB) (iInf_le_of_le ?_ le_rfl))
  intro x hx
  have key : ∀ k : ℕ, ∃ γ ∈ Γ, (∀ v, uMat ((γ * x) v) - 1 ∈ A v 0) ∧ ∀ c < k,
      (fun v (i : {i : Fin d // deg i = c}) => ipL (E v i.1) (uMat ((γ * x) v) - 1)) ∈ D c := by
    intro k
    induction k with
    | zero => exact ⟨1, Γ.one_mem, by simpa using hx, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    | succ k ih =>
      obtain ⟨γ, hγ, h0, hc⟩ := ih
      obtain ⟨δ, hδ, hδk, hδD⟩ := hcov k fun v i => ipL (E v i.1) (uMat ((γ * x) v) - 1)
      have hexp : ∀ v, uMat ((δ * γ * x) v) - 1 = (uMat (δ v) - 1) + (uMat ((γ * x) v) - 1) +
          (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) := fun v => by
        rw [mul_assoc, Pi.mul_apply, mul_sub_one]
      have hprod : ∀ v, (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) ∈ A v (k + 1) := fun v =>
        (hmul v k _ (hδk v) _ (h0 v)).1
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, fun v => ?_, fun c hck => ?_⟩
      · rw [hexp]
        exact (A v 0).add_mem ((A v 0).add_mem (hΓ δ hδ v) (h0 v)) (hanti v (Nat.zero_le _) (hprod v))
      · rcases (Nat.lt_succ_iff.1 hck).lt_or_eq with h | rfl
        · convert hc c h using 1
          funext v i
          rw [hexp, map_add, map_add, horth v k i.1 (by rw [i.2]; exact h) _ (hδk v),
            horth v (k + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), zero_add, add_zero]
        · convert hδD using 1
          funext v i
          rw [hexp, map_add, map_add, horth v (c + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), add_zero]
          rfl
  obtain ⟨γ, hγ, -, hc⟩ := key m
  exact ⟨γ, hγ, hc⟩

end GlobalTheory.NilCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
section
noncomputable section

namespace GlobalTheory.TypeAsm.NFEx

section Mat
variable {K : Type} [Field K] [StarRing K]

open Classical in

noncomputable def cb (b : K × ℕ) : Kˣ × ℕ+ :=
  if h : b.1 ≠ 0 ∧ 1 ≤ b.2 then (Units.mk0 (star b.1) (star_ne_zero.2 h.1), ⟨b.2, h.2⟩) else (1, 1)

theorem entry_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (a c : ℕ) :
    Formalism.MainNotions.S.Loc.ptEntryL (bs.map cb) a c = star (Formalism.MainNotions.S.ptEntry bs a c) := by
  induction bs generalizing a c with
  | nil => simp [Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have h := hb (t, s) (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, cb, dif_pos h, Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry, PNat.mk_coe, Units.val_mk0]
    simp only [ih', apply_ite star, star_zero]
    exact if_congr Iff.rfl (if_congr Iff.rfl rfl rfl) (if_congr Iff.rfl rfl rfl)

theorem size_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ((bs.map cb).map (fun b => (b.2 : ℕ))).sum = (bs.map Prod.snd).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have h := hb b (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, List.sum_cons, cb, dif_pos h, PNat.mk_coe, ih']

end Mat
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
section Mat2
variable {K : Type} [Field K] [StarRing K]

noncomputable def toPt {n : ℕ} (p : Formalism.MainNotions.S.Point K n) : Formalism.MainNotions.S.Loc.Pt K n where
  blocks := p.1.map cb
  size := (size_cb p.1 p.2.1).trans p.2.2

theorem toPt_mat {n : ℕ} (p : Formalism.MainNotions.S.Point K n) (a b : Fin n) :
    (toPt p).mat a b = star (Formalism.MainNotions.S.ptMat p a b) :=
  entry_cb p.1 p.2.1 a.val b.val

def sgnR (r : ℕ) {n : ℕ} (b : Fin n) : ℤˣ := (-1) ^ (r - b.val)

theorem decomp {n r : ℕ} (Z : Matrix (Fin n) (Fin n) K) (p : Formalism.MainNotions.S.Point K n)
    (h : Formalism.MainNotions.S.IsInCell (fun a b => (-1 : K) ^ (r - b.val) * Z a b) p) :
    ∃ A B : Matrix (Fin n) (Fin n) K, (∀ a b, a < b → A a b = 0 ∧ B b a = 0) ∧ (∀ a, A a a = 1 ∧ B a a = 1) ∧
      Z.map star = A * Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) * B := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h
  set s : Fin n → K := fun b => (-1 : K) ^ (r - b.val) with hs_def
  have hs : ∀ b, s b * s b = 1 := fun b => by
    simp only [hs_def, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hss : ∀ b, star (s b) = s b := fun b => by simp [hs_def]
  have hsg : ∀ b : Fin n, (((sgnR r b : ℤˣ) : ℤ) : K) = s b := fun b => by
    simp [sgnR, hs_def]
  have hZ' : Z = L * Formalism.MainNotions.S.ptMat p * U * Matrix.diagonal s := by
    ext a b
    rw [Matrix.mul_diagonal, ← hZ]
    show Z a b = s b * Z a b * s b
    rw [mul_comm (s b), mul_assoc, hs, mul_one]
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hs]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  have hDs : (Matrix.diagonal s).map star = Matrix.diagonal s := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hss]
    · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨L.map star, Matrix.diagonal s * U.map star * Matrix.diagonal s, fun a b hab => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_⟩
  · simp [(hL a b).1 hab]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU b a).1 hab]
  · simp [(hL a a).2 rfl]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU a a).2 rfl, hs]
  · have hP : Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) =
        (Formalism.MainNotions.S.ptMat p).map star * Matrix.diagonal s := by
      ext a b
      rw [Matrix.mul_diagonal, Matrix.of_apply, toPt_mat, hsg, Matrix.map_apply]
    have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map star = M.map star * N.map star := fun M N =>
      (Matrix.map_mul (f := starRingEnd K) (L := M) (M := N))
    rw [hP, hZ', hmap, hmap, hmap, hDs]
    calc L.map star * (Formalism.MainNotions.S.ptMat p).map star * U.map star * Matrix.diagonal s
        = L.map star * (Formalism.MainNotions.S.ptMat p).map star * (Matrix.diagonal s * Matrix.diagonal s) * U.map star *
            Matrix.diagonal s := by rw [hD, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end Mat2
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zhat_eq {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word} (t : GTu Y u)
    (j : ℕ) (hj : j ≤ D.R.rS + 1) :
    (Formalism.HermitianLatticeCounting.S6.Zhat (F0 X u) (Ft t)).submatrix (Fin.castLE hj) (Fin.castLE hj) =
      ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (star : D.host.E → D.host.E) := by
  refine Matrix.ext fun a b => ?_
  exact a_herm (S := VS D) ((F0 X u).e (Fin.castLE hj a)) ((Ft t).e (Fin.castLE hj b))

end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfExC (hHost : HostC) : NFExC := by
  intro D large₂ X Y u hStd t ht
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hH := hHost D large₂ hStd
  obtain ⟨hrel, -⟩ := relRepC D X Y u u t hr hG
  have hTu := tie_Tu_pos D u
  have hj' : j ≤ D.R.rS + 1 := hj.trans (Nat.le_succ _)
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl (frq X t.rep).fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu (frq X t.rep)) hrel
  have hDG : Formalism.MainNotions.S.Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := by
    rw [nf_Dl _ _ (fixedFlag_level_ne_zero D u) (nf_T_ne D u) j hj']
    exact star_ne_zero.2 hN.2.2.1
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point hj'
    ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj') (Fin.castLE hj'))
    (by rw [← tie_Dl_eq']; exact hDG) (geo j hj' (Or.inl ⟨hj, hDG⟩))
  obtain ⟨A, B, h0, h1, hZ⟩ := decomp _ p hp
  obtain ⟨N, hNj, -, hNT, hN𝔡, hF, hF'⟩ := GlobalTheory.DegCnt.RatNormal.exists_nf D.host.E (VS D).V (HV D) hH.1 D.R.rS
    (F0 X u) (Ft t) j hj c (Tu D u) (dI D) (toPt p) (fun b => sgnR D.R.rS b) A B hN rfl rfl
    (fun σ => nf_pos _ _ (p_posX D _ hTu _) σ) hH.2.2.2.2.2.2.2.1 hH.2.2.2.2.2.2.2.2.1 h0 h1
    (by rw [zhat_eq t j hj']; exact hZ)
  exact ⟨N, ⟨hN𝔡, hF, hF'⟩, hNj.trans hjT.symm, hNT⟩

end GlobalTheory.TypeAsm.NFEx

theorem GlobalTheory.TypeAsm.nfExC_holds : GlobalTheory.TypeAsm.NFExC := GlobalTheory.TypeAsm.NFEx.nfExC GlobalTheory.T.unitaryHostFieldArithmeticConditions
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGardingKMap
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.SmoothKType

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem exists_garding_kMap (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKTypeOf ε σ μ S) :
    ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : S →ₗ[ℂ] H), SmoothOnG ε α ∧
      HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
      (∀ (s : S) (u : H), ⟪u, T s⟫_ℂ = ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε)) ∧
      (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ k (T x)) ∧ T ≠ 0 := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha, ha0, ha1, hac, haU, haK⟩ := exists_conjInvariant_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add, smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨fun y => (a y : ℂ), T, ?_, hsuppC, hT, ?_, ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun y => (a y : ℂ), isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    exact (Complex.ofRealCLM.contDiff.comp ha).contDiffOn
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [h0, LinearMap.zero_apply, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4

theorem exists_isDer_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ μ S → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (S' : Submodule ℂ H), IsDer ε σ V E ∧ IsKTypeOf ε σ μ S' ∧ S' ≤ V := by
  intro n ε μ H _ _ _ σ S hσ hK
  let G : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ G, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ G,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := GlobalTheory.DerEx.smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ G, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using GlobalTheory.DerEx.smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using GlobalTheory.DerEx.smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ G) hσ hder hsm
  obtain ⟨α, T, h1, h2, h3, h4, h5⟩ := exists_garding_kMap n ε μ H σ S hσ hK
  haveI := hK.1
  refine ⟨_, E, _, hE, GlobalTheory.Dec.FormF.rangeType n ε μ H σ S H σ (LinearMap.toContinuousLinearMap T) hK h4
    (fun h => h5 (LinearMap.ext fun x => DFunLike.congr_fun h x)), ?_⟩
  rintro _ ⟨s, rfl⟩
  exact Submodule.subset_span ⟨α, s, h1, h2, fun y => (h3 s y).symm⟩

end GlobalTheory.SmoothKType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramifiedStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  first | exact @GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified | exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified | (intros; apply GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLatticeStabiliserRealGroupMulMemStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLatticeStabiliserRealGroup_mul_mem : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  first | exact @GlobalTheory.FlagStabMul.flagGroup_mul | exact GlobalTheory.FlagStabMul.flagGroup_mul | (intros; apply GlobalTheory.FlagStabMul.flagGroup_mul <;> assumption)
end


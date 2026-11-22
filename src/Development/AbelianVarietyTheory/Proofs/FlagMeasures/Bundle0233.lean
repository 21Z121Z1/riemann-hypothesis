import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0224
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinNeZeroOfCwCont
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_param_maxCompact {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    ∃ κ : Formalism.REAL.KG ε → Mx k r, Continuous κ ∧ (∀ x, κ x ∈ GG k r) ∧ κ 1 = 1 ∧
      (∀ x y, κ (x * y) = κ x * κ y) ∧
      ∀ g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _),
        ∃ x, κ x = g := by
  obtain ⟨⟨-, hPJ⟩, hPU⟩ := hP
  have h1 : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcong : ∀ A B : Mx k r, (Pᴴ * A * P) * (Pᴴ * B * P) = Pᴴ * (A * B) * P := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
  have hherm : ∀ A : Mx k r, (Pᴴ * A * P)ᴴ = Pᴴ * Aᴴ * P := by
    intro A
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hJ : Formalism.QuantumDeterminants.Hpk k r = Pᴴ * Formalism.REAL.Jm ε * P := hPJ.symm
  refine ⟨fun x => Pᴴ * Formalism.REAL.toMK x * P, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun x : Formalism.REAL.KG ε => Formalism.REAL.toMK x) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  · intro x
    have hx : (Formalism.REAL.toMK x)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK x = Formalism.REAL.Jm ε :=
      (x : Formalism.REAL.UJ ε).2
    show (Pᴴ * Formalism.REAL.toMK x * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Pᴴ * Formalism.REAL.toMK x * P) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [hJ, hherm, hcong, hcong, hx]
  · show Pᴴ * Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) * P = 1
    rw [show Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 from rfl, Matrix.mul_one, h1]
  · intro x y
    show Pᴴ * Formalism.REAL.toMK (x * y) * P = (Pᴴ * Formalism.REAL.toMK x * P) * (Pᴴ * Formalism.REAL.toMK y * P)
    rw [hcong]
    rfl
  · rintro g ⟨hgH, hgU⟩
    have hgH' : gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P := by
      have h : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hgH
      rw [← hPJ] at h
      exact h
    have g1 : gᴴ * g = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    have g2 : g * gᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    set M := P * g * Pᴴ with hM
    have hMH : Mᴴ = P * gᴴ * Pᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have M1 : Mᴴ * M = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc gᴴ g, g1, Matrix.one_mul, h2]
    have M2 : M * Mᴴ = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc g gᴴ, g2, Matrix.one_mul, h2]
    have MJ : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := by
      calc Mᴴ * Formalism.REAL.Jm ε * M = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
            rw [hMH, hM]
            simp only [Matrix.mul_assoc]
        _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by rw [hgH']
        _ = Formalism.REAL.Jm ε := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul, Matrix.mul_one]
    have MK : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
      calc M * Formalism.REAL.Jm ε = M * (Mᴴ * Formalism.REAL.Jm ε * M) := by rw [MJ]
        _ = (M * Mᴴ) * Formalism.REAL.Jm ε * M := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * M := by rw [M2, Matrix.one_mul]
    have MU : M ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact M2
    let u : (Mx k r)ˣ := ⟨M, Mᴴ, M2, M1⟩
    have hu : u ∈ Formalism.REAL.UJ ε := MJ
    have hk : (⟨u, hu⟩ : Formalism.REAL.UJ ε) ∈ Formalism.REAL.KG ε := (⟨MU, MK⟩ : M ∈ Formalism.REAL.Kset ε)
    refine ⟨⟨⟨u, hu⟩, hk⟩, ?_⟩
    show Pᴴ * M * P = g
    rw [hM]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, Matrix.mul_one]

theorem exists_kFin_ne_zero_of_cwCont : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → (∃ v ∈ R.sm, Bm v ≠ 0) → ∃ x, R.KFin x ∧ Bm x ≠ 0 := by
  intro hKS k r ε mu R hR V _ _ _ _ Bm hadd hsmul hcw hex
  obtain ⟨v, hv, hBv⟩ := hex
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  by_contra hcon
  push_neg at hcon
  obtain ⟨P, hP, -⟩ := hR.2
  obtain ⟨κ, hκc, hκG, hκ1, hκm, hκs⟩ := exists_param_maxCompact hP
  obtain ⟨hmul, hone, -, -, -, -, -, -, hσc⟩ := rep_basic_of_isDS hKS k r ε mu R hR
  have hBc := (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1
  have hf : Continuous (fun x => Bm (R.σ (κ x) v)) := hBc.comp_continuous hκc hκG
  have hw : Continuous (fun x => R.σ (κ x) v) := (hσc v).comp_continuous hκc hκG
  have hint : ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      Integrable (fun x => q x • R.σ (κ x) v) (Formalism.REAL.muK ε) := fun q hq =>
    (hq.smul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsig : ∀ y, ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)) =
        ∫ x, q (y⁻¹ * x) • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := by
    intro y q hq
    calc R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε))
        = ∫ x, R.σ (κ y) (q x • R.σ (κ x) v) ∂(Formalism.REAL.muK ε) :=
          ((R.σ (κ y)).integral_comp_comm (hint q hq)).symm
      _ = ∫ x, (fun z => q (y⁻¹ * z) • R.σ (κ z) v) (y * x) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp only [map_smul, inv_mul_cancel_left, hκm, hmul _ (hκG y) _ (hκG x)]
      _ = _ := integral_mul_left_eq_self (μ := Formalism.REAL.muK ε) (fun z => q (y⁻¹ * z) • R.σ (κ z) v) y
  let φ : C(Formalism.REAL.KG ε, ℂ) := ⟨fun x => ⟪Bm v, Bm (R.σ (κ x) v)⟫_ℂ, continuous_const.inner hf⟩
  have hφ : φ = 0 := by
    refine KHolExt.eq_zero_of_orth φ (fun p hp => ?_)
    obtain ⟨ι, _, a, b, -, hab⟩ := hp
    obtain ⟨u, hu⟩ : ∃ u, u = ∫ x, p x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ι → R.H, ∀ i, c i = ∫ x, b i x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) :=
      ⟨_, fun _ => rfl⟩
    have hdec : ∀ y, R.σ (κ y) u = ∑ i, a i y • c i := by
      intro y
      rw [hu, hsig y p p.continuous]
      have hx : ∀ x, p (y⁻¹ * x) • R.σ (κ x) v = ∑ i, a i y • (b i x • R.σ (κ x) v) := by
        intro x
        rw [hab, Finset.sum_smul]
        simp only [mul_smul]
      simp_rw [hx]
      rw [integral_finset_sum Finset.univ (f := fun i x => a i y • (b i x • R.σ (κ x) v))
        (fun i _ => (hint _ (b i).continuous).smul (a i y))]
      simp only [integral_smul, hc]
    have hFT : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
    let S := Submodule.span ℂ (Set.range fun y => R.σ (κ y) u)
    have hST : S ≤ Submodule.span ℂ (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      show R.σ (κ y) u ∈ Submodule.span ℂ (Set.range c)
      rw [hdec y]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hKF : R.KFin u := by
      unfold BranchingSupport.Rep.KFin PI.UpqRep.IsKFinHpk
      refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
      · have h1 : R.σ (κ 1) u ∈ S := Submodule.subset_span ⟨1, rfl⟩
        rwa [hκ1, hone] at h1
      · intro g hg x hx
        obtain ⟨y', rfl⟩ := hκs g hg
        have hmap : S.map (R.σ (κ y') : R.H →ₗ[ℂ] R.H) ≤ S := by
          rw [Submodule.map_span_le]
          rintro _ ⟨y, rfl⟩
          refine Submodule.subset_span ⟨y' * y, ?_⟩
          simp [hκm, hmul _ (hκG y') _ (hκG y)]
        exact hmap (Submodule.mem_map_of_mem hx)
    have hus : u ∈ R.sm := hKS k r ε mu R.H R.σ hR.1 hR.2 u hKF
    have hB0 : Bm u = 0 := hcon u hKF
    have hI := GlobalTheory.T.cwCont_integral_comm_alt hKS k r ε mu R hR V Bm hadd hsmul hcw (Formalism.REAL.KG ε) (Formalism.REAL.muK ε) κ p
      hκc hκG p.continuous v hv (hu ▸ hus)
    have hfi : Integrable (fun x => p x • Bm (R.σ (κ x) v)) (Formalism.REAL.muK ε) :=
      (p.continuous.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ∫ x, p x * φ x ∂(Formalism.REAL.muK ε)
        = ∫ x, innerSL ℂ (Bm v) (p x • Bm (R.σ (κ x) v)) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp [φ, inner_smul_right]
      _ = innerSL ℂ (Bm v) (∫ x, p x • Bm (R.σ (κ x) v) ∂(Formalism.REAL.muK ε)) :=
          (innerSL ℂ (Bm v)).integral_comp_comm hfi
      _ = 0 := by rw [← hI, ← hu, hB0, map_zero]
  have h1 := DFunLike.congr_fun hφ 1
  change ⟪Bm v, Bm (R.σ (κ 1) v)⟫_ℂ = 0 at h1
  rw [hκ1, hone, inner_self_eq_zero] at h1
  exact hBv h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem IsChoice.eq_of_mem {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {k k' : Fin 2}
    (u : HeightOneSpectrum (𝓞 I.E)) (h1 : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal) (h2 : ((g k' : ℕ) : 𝓞 I.E) ∈ u.asIdeal) :
    k = k' := by
  by_contra hkk
  have hg : g k ≠ g k' := by
    intro e
    apply hkk
    fin_cases k <;> fin_cases k'
    · rfl
    · exact absurd e h.2.1
    · exact absurd e.symm h.2.1
    · rfl
  obtain ⟨a, b, hab⟩ : IsCoprime (g k : ℤ) (g k') :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (h.1 k) (h.1 k')).mpr hg)
  have e : (a : 𝓞 I.E) * ((g k : ℕ) : 𝓞 I.E) + (b : 𝓞 I.E) * ((g k' : ℕ) : 𝓞 I.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 I.E) hab
    push_cast at this
    exact this
  apply u.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem IsChoice.ne_of_ne {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {a b : Σ k, Pl k} (hab : b ≠ a) :
    w b.1 b.2 ≠ w a.1 a.2 ∧ ¬ IsConj I (w a.1 a.2) (w b.1 b.2) := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  dsimp only
  have hmem := h.2.2.2.1
  by_cases hk : kb = ka
  · subst hk
    have hv : vb ≠ va := fun e => hab (by rw [e])
    exact ⟨fun e => hv (h.2.2.2.2.1 kb e), h.2.2.2.2.2.1 kb va vb⟩
  · refine ⟨fun e => hk (h.eq_of_mem (w kb vb) (hmem kb vb).1 (by rw [e]; exact (hmem ka va).1)), fun hcj => hk ?_⟩
    have hx := (hcj ((g ka : ℕ) : 𝓞 I.E) ((g ka : ℕ) : 𝓞 I.E) (by simp)).mp (hmem ka va).1
    exact (h.eq_of_mem (w kb vb) hx (hmem kb vb).1).symm

theorem PlFrame.actsAs_one_of_mem {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf) : fr.ActsAs x 1 := by
  intro y h
  rw [Matrix.one_mulVec, ← sub_eq_zero, ← map_sub]
  refine (fr.c_ker _).mpr ?_
  have e : ((⟨_, h⟩ - y : I.Lf) : Fin I.n → _) = (I.fmat x - 1) *ᵥ (y : Fin I.n → _) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Submodule.coe_sub]
  rw [e]
  exact hx _ y.2

private theorem val_eq_lemma {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} {fr : ∀ k v, PlFrame I N (g k) (w k v)}
    {ρ : I.Gf → GProd N g Pl} (hρ : ActsBy fr ρ) {x : I.Gf} (hx : x ∈ I.Kset) (kv : Σ k, Pl k)
    {M : GL (Fin N) (ZMod (g kv.1))} (hM : (fr kv.1 kv.2).ActsAs x (M : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))) :
    ρ x kv = M :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (hρ x hx kv.1 kv.2) hM)

theorem exists_red_actsBy : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)) [∀ k, Finite (Pl k)],
    I.n = N → IsChoice I g Pl w → ∃ ρ : Red I (g 0 * g 1) (GProd N g Pl), ActsBy fr ρ.toFun := by
  intro I N g Pl w fr _ hn hc
  classical
  obtain ⟨ρ, hρ, hmul⟩ := exists_actsBy fr
  have hK1 : (1 : I.Gf) ∈ I.Kset := (Inhab.mem_Ksub I 1).mp (Inhab.Ksub I).one_mem
  have hKmul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, x * y ∈ I.Kset := fun x hx y hy =>
    (Inhab.mem_Ksub I _).mp
      ((Inhab.Ksub I).mul_mem ((Inhab.mem_Ksub I x).mpr hx) ((Inhab.mem_Ksub I y).mpr hy))
  have hone : ∀ x ∈ I.Kset, ∀ kv : (Σ k, Pl k), (fr kv.1 kv.2).ActsAs x 1 → ρ x kv = 1 :=
    fun x hx kv h => val_eq_lemma hρ hx kv (M := 1) (by rw [Units.val_one]; exact h)
  have : Fintype (Σ k, Pl k) := Fintype.ofFinite _
  refine ⟨⟨ρ, hmul, fun x hx => ?_, fun q => ?_⟩, hρ⟩
  · rw [← GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg I N g Pl w fr hn hc x hx]
    constructor
    · intro h1 k v y h
      rw [hρ x hx k v y h, h1]
      simp
    · intro h
      funext kv
      exact hone x hx kv (fun y hy => by rw [h kv.1 kv.2 y hy, Matrix.one_mulVec])
  · have key : ∀ s : Finset (Σ k, Pl k), ∃ x ∈ I.Kset, ρ x = fun kv => if kv ∈ s then q kv else 1 := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · exact ⟨1, hK1, funext fun kv => by simpa using hone 1 hK1 kv (fr kv.1 kv.2).actsAs_one⟩
      · intro a s ha ih
        obtain ⟨xs, hxs, es⟩ := ih
        obtain ⟨xa, hxa, hact, hoth⟩ := GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime I N (g a.1) (w a.1 a.2) (fr a.1 a.2) hn (hc.1 a.1)
          (hc.2.2.2.1 a.1 a.2).2 (hc.2.2.2.2.2.1 a.1 a.2 a.2) (q a)
        refine ⟨xa * xs, hKmul xa hxa xs hxs, ?_⟩
        rw [hmul xa hxa xs hxs, es]
        funext kv
        by_cases hk : kv = a
        · rw [hk, Pi.mul_apply, val_eq_lemma hρ hxa a hact]
          simp [ha]
        · have hne := IsChoice.ne_of_ne hc hk
          rw [Pi.mul_apply, hone xa hxa kv (PlFrame.actsAs_one_of_mem _ (hoth _ hne.1 hne.2))]
          simp [hk]
    obtain ⟨x, hx, e⟩ := key Finset.univ
    exact ⟨x, hx, by rw [e]; simp⟩

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem exists_smooth_average_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro B d hD hK P u hu
  have hσ : IsURep B.σs := (tensorRep B d hD).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => by
    obtain ⟨_, hds, _, _⟩ := hD v
    obtain ⟨_, _, h, _⟩ := hds
    exact h
  have hw : ∀ v, B.w v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) ∧ B.w v ≠ 0 := fun v => by
    obtain ⟨_, _, ⟨h1, h2⟩, _⟩ := hD v
    refine ⟨h2, fun h0 => ?_⟩
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

  let A : Set B.Hs := {y | ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
    HasCompactSupport F ∧ y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)}
  have hint : ∀ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w)) (muInf B.I) :=
    fun F hF hc => integrable_inf B hσ (B.tens B.w) hF.continuous hc
  have hzero : (0 : B.Hs) ∈ A := ⟨0, contDiff_const, HasCompactSupport.zero, by simp⟩
  have hadd : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A := by
    rintro x y ⟨F, hF, hFc, rfl⟩ ⟨G, hG, hGc, rfl⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc, ?_⟩
    rw [← integral_add (hint F hF hFc) (hint G hG hGc)]
    congr 1
    funext g
    simp [add_smul]
  have hsmul : ∀ (c : ℂ) x, x ∈ A → c • x ∈ A := by
    rintro c x ⟨F, hF, hFc, rfl⟩
    refine ⟨fun z => c * F z, contDiff_const.mul hF, hFc.mul_left (f := fun _ => c), ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have htens : ∀ u' : ∀ v, B.H v, (∀ v, u' v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → B.tens u' ∈ A := by
    intro u' hu'
    have hloc := fun v => GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v)
      (B.w v) (hU v) (hK v) (hw v).1 (hw v).2 (u' v) (hu' v)
    choose F hF hFc hFe using hloc
    obtain ⟨G, hG, hGc, hGe⟩ := tens_average B hU hσ B.w F hF hFc
    refine ⟨G, hG, hGc, ?_⟩
    rw [← hGe]
    congr 1
    funext v
    exact hFe v

  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (y : B.Hs), y ∈ A → wordAct B l y ∈ A := by
    intro l
    induction l with
    | nil => intro y hy; exact hy
    | cons X l ih =>
      intro y hy
      obtain ⟨F, hF, hFc, hFe⟩ := ih y hy
      obtain ⟨F', hF', hF'c, hd⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B F (atPlace B X.1 X.2) (B.tens B.w)
        hσ hF hFc
      refine ⟨F', hF', hF'c, ?_⟩
      show dAct B (atPlace B X.1 X.2) (wordAct B l y) = _
      rw [hFe]
      exact hd.deriv

  let S : Submodule ℂ B.Hs :=
    { carrier := A
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      smul_mem' := fun c x hx => hsmul c x hx }
  have hle : VP B P ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨l, u', -, hu', rfl⟩
    exact hword l _ (htens u' hu')
  exact hle hu

end GlobalTheory.StepAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplitStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_places_over_typePrimes_split : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  first | exact @GlobalTheory.TypedPlacesProduct.finprod_typed_places | exact GlobalTheory.TypedPlacesProduct.finprod_typed_places | (intros; apply GlobalTheory.TypedPlacesProduct.finprod_typed_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.FrameDual

section Det

variable {A : Type} [CommRing A]

end Det

section Ideals

variable {E : Type} [Field E] [NumberField E]

def Stab (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) : Prop := ∀ x ∈ I, σ x ∈ I

theorem stab_one (σ : E →+* E) : Stab σ 1 := by
  intro x hx
  obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact (FractionalIdeal.mem_one_iff _).2 ⟨RingOfIntegers.mapRingHom σ d, rfl⟩

theorem Stab.mul {σ : E →+* E} {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (hJ : Stab σ J) :
    Stab σ (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)
  · rw [map_add]; exact Submodule.add_mem (I * J).coeToSubmodule ha hb

theorem Stab.pow {σ : E →+* E} {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (j : ℕ) :
    Stab σ (I ^ j) := by
  induction j with
  | zero => simpa using stab_one σ
  | succ j ih => rw [pow_succ]; exact ih.mul hI

theorem Stab.inv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I)
    (h0 : I ≠ 0) : Stab σ I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have := stab_one σ _ (hx _ (hI y hy))
  rwa [map_mul, hσ] at this

theorem diff_ne_zero : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem dInv_ne_zero (j : ℕ) : dInv E j ≠ 0 := pow_ne_zero _ (inv_ne_zero diff_ne_zero)

theorem stab_dInv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (j : ℕ) : Stab σ (dInv E j) := by
  refine Stab.pow ?_ j
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  intro x hx
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h10] at hx ⊢
  intro a ha
  have h1 := hx _ (stab_one σ a ha)
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have h2 : Algebra.traceForm ℚ E (σ x) a = Algebra.traceForm ℚ E x (σ a) := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv e (x * σ a)]
    congr 1
    change _ = σ (x * σ a)
    rw [map_mul, hσ]
  rwa [h2]

end Ideals

section Frame

variable {E : Type} [Field E] [NumberField E]

theorem frameDualTupleIdeals_castAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.castAdd r b.castSucc) = dInv E (r - b) := by
  simp [id1]

theorem frameDualTupleIdeals_natAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.natAdd (r + 1) b) = (dInv E (r - b))⁻¹ := by
  simp [id1]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem natAbs_discr_sq (h2 : Module.finrank F E = 2) [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] :
    (discr E).natAbs = (discr F).natAbs ^ 2 := by
  have h0 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact not_dvd_differentIdeal_iff.2 (inferInstance : Algebra.IsUnramifiedAt (𝓞 F) P)
      (Ideal.dvd_iff_le.2 hle)
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rwa [h0, Ideal.absNorm_top, one_mul, h2] at h1

theorem absNorm_dInv (j : ℕ) :
    ((FractionalIdeal.absNorm (dInv E j) : ℚ) : ℝ) = |(discr E : ℝ)|⁻¹ ^ j := by
  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E (𝓞 E)]
  simp

end Frame

end GlobalTheory.SnMass.FrameDual
end


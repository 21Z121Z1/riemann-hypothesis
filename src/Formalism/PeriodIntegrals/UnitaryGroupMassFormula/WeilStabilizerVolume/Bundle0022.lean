import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FinTheta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0006

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.EventuallyStruct
section
noncomputable section

namespace PI.VolStabW

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabW.FiniteThetaCoordinates
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_mem_HR (φ : R →ₐ[F] S) {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR S σ J := by
  set ψ : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hg' : Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := hg
  have hcT : (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))).map ψ =
      Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, ψ, tmap_sigR]
  have hJ : (JR R J).map ψ = JR S J := by
    ext i j
    simp [JR, Matrix.map_apply, ψ, tmap_inclR]
  show Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) * JR S J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ = JR S J
  rw [← hcT, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def haMap (φ : R →ₐ[F] S) : HA R σ J →* HA S σ J :=
  MonoidHom.codRestrict
    ((Formalism.UG.bc (n := Fin M) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).comp
      (HR R σ J).subtype) (HR S σ J) (fun h => map_mem_HR σ J φ h.2)

theorem mat_haMap_apply (φ : R →ₐ[F] S) (h : HA R σ J) (i j : Fin M) :
    ((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j =
      Algebra.TensorProduct.map φ (AlgHom.id F E)
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j) := rfl

theorem map_smul_tup (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  show Algebra.TensorProduct.map φ (AlgHom.id F E)
      ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)) i) =
    (((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
      (fun j => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x j))) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, mat_haMap_apply]

theorem tmap_comp {T : Type} [CommRing T] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem crd_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by
  rw [crd_mulVec]
  exact sum_mem fun j _ => sum_mem fun p _ => sum_mem fun q _ =>
    mul_mem (mul_mem (hm i j p) (hy j q)) (hc p q k)

theorem smul_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by
  simp only [latV, Set.mem_ofPred_eq] at hY ⊢
  intro x i k
  exact crd_mulVec_mem v b _ (Y x) hm (fun j q => hY x j q) hc i k

theorem eventually_int (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j p
  exact (eventually_piV_le_one F _).mono fun v hv => (norm_le_one_iff_mem F v _).1 hv

theorem eventually_struct {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  refine (eventually_piV_le_one F (algebraMap F (AF F) (b.repr (b p * b q) k))).mono fun v hv => ?_
  rw [AlgHom.commutes] at hv
  exact (norm_le_one_iff_mem F v _).1 hv

theorem compG_gen (a : ℕ) (g : HA (AF F) σ J) :
    ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v := by
  refine ⟨haMap σ J (fstA F) g, fun v => haMap σ J (piV F v) g, ?_, ?_, ?_⟩
  · intro X
    exact map_smul_tup σ J (fstA F) g X
  · intro v X
    have e : ∀ Z : Fin a → Fin M → AF F ⊗[F] E, projV v (projFin Z) =
        fun x i => Algebra.TensorProduct.map (piV F v) (AlgHom.id F E) (Z x i) := by
      intro Z
      funext x i
      exact tmap_comp (sndA F) (evalV F v) (Z x i)
    rw [e, e, map_smul_tup]
  · intro d b
    filter_upwards [eventually_int σ J g b, eventually_int σ J g⁻¹ b, eventually_struct b]
      with v h1 h2 h3
    have hm : ∀ g' : HA (AF F) σ J, (∀ i j p, piV F v (crd b (AF F)
        (((HA.mat (AF F) σ J g' : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
          v.adicCompletionIntegers F) → ∀ i j p, crd b (Fv F v)
        (((HA.mat (Fv F v) σ J (haMap σ J (piV F v) g') : GL (Fin M) _) :
          Matrix (Fin M) (Fin M) _) i j) p ∈ v.adicCompletionIntegers F := by
      intro g' hg' i j p
      rw [mat_haMap_apply, crd_map]
      exact hg' i j p
    intro Y
    constructor
    · intro hY
      have := smul_mem_latV σ J v b (haMap σ J (piV F v) g⁻¹) (hm g⁻¹ h2) h3 _ hY
      rwa [map_inv, inv_smul_smul] at this
    · intro hY
      exact smul_mem_latV σ J v b (haMap σ J (piV F v) g) (hm g h1) h3 Y hY

end Loc

end CompGAux

theorem compG_holds : CompG := by
  intro F E _ _ _ _ _ σ _hCM M J _hJ _ha _hc a _ha1 _ha2 _X0 _hT _hdet g
  exact CompGAux.compG_gen σ J a g

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensPos
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal

namespace LocPosW

theorem pos_of_lb {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} (hι : Function.Injective ι)
    {U : Set V} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    {f' : V → X} (hf' : Continuous f') (hff : ∀ v, f v = ι (f' v))
    {φ : V → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ v, 0 ≤ φ v) {W : Set V} (hWU : W ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hWφ : ∀ v ∈ W, δ ≤ φ v) {b0 : X} {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ⊤) {N : Set X}
    (hN : N ∈ 𝓝 b0) (hlb : ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W))
    (hνpos : ∀ O : Set X, IsOpen O → O.Nonempty → ν O ≠ 0) (hνfin : ∃ N' ∈ 𝓝 b0, ν N' < ⊤) :
    0 < ∫ v, φ v ∂(fib b0) := by
  obtain ⟨hsupp, hdis, hcont⟩ := hfib
  obtain ⟨hint, hIc⟩ := hcont φ hφc hφs hφU
  have hIcont : Continuous (fun b => ∫ v, φ v ∂(fib b)) := continuousOn_univ.mp hIc
  have hI0 : ∀ b, 0 ≤ ∫ v, φ v ∂(fib b) := fun b => integral_nonneg hφ0
  by_contra hneg
  push_neg at hneg
  have hb0 : ∫ v, φ v ∂(fib b0) = 0 := le_antisymm hneg (hI0 b0)
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hc'
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = c.toReal * δ / 2 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hO : {b | ∫ v, φ v ∂(fib b) < ε} ∈ 𝓝 b0 :=
    hIcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hb0]; exact hεpos))
  obtain ⟨N', hN', hN'fin⟩ := hνfin
  obtain ⟨S, hSdef⟩ : ∃ S : Set X,
      S = interior N ∩ interior N' ∩ interior {b | ∫ v, φ v ∂(fib b) < ε} := ⟨_, rfl⟩
  have hSo : IsOpen S := by
    rw [hSdef]
    exact (isOpen_interior.inter isOpen_interior).inter isOpen_interior
  have hb0S : b0 ∈ S := by
    rw [hSdef]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr hN, mem_interior_iff_mem_nhds.mpr hN'⟩,
      mem_interior_iff_mem_nhds.mpr hO⟩
  have hSN : S ⊆ N := by
    rw [hSdef]
    exact fun b hb => interior_subset hb.1.1
  have hSN' : S ⊆ N' := by
    rw [hSdef]
    exact fun b hb => interior_subset hb.1.2
  have hSε : ∀ b ∈ S, ∫ v, φ v ∂(fib b) < ε := by
    rw [hSdef]
    exact fun b hb => interior_subset (s := {b | ∫ v, φ v ∂(fib b) < ε}) hb.2
  have hSm : MeasurableSet S := hSo.measurableSet
  have hνS0 : ν S ≠ 0 := hνpos S hSo ⟨b0, hb0S⟩
  have hνSfin : ν S ≠ ⊤ := ne_top_of_le_ne_top hN'fin.ne (measure_mono hSN')
  have hlbS := hlb S hSN hSm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V → ℝ≥0∞, ψ = (f' ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ v)) :=
    ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact (ENNReal.measurable_ofReal.comp hφc.measurable).indicator (hf'.measurable hSm)
  have hA : ENNReal.ofReal δ * μ (f ⁻¹' (ι '' S) ∩ W) ≤ ∫⁻ v in U, ψ v ∂μ := by
    calc ENNReal.ofReal δ * μ (f ⁻¹' (ι '' S) ∩ W)
        = ∫⁻ v in f ⁻¹' (ι '' S) ∩ W, ENNReal.ofReal δ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' S) ∩ W, ψ v ∂μ := by
          apply setLIntegral_mono hψm
          intro v hv
          obtain ⟨⟨s, hs, hsv⟩, hvW⟩ := hv
          have hsf : s = f' v := hι (hsv.trans (hff v))
          have hvS : v ∈ f' ⁻¹' S := by
            rw [Set.mem_preimage, ← hsf]
            exact hs
          rw [hψ, Set.indicator_of_mem hvS]
          exact ENNReal.ofReal_le_ofReal (hWφ v hvW)
      _ ≤ ∫⁻ v in U, ψ v ∂μ := lintegral_mono_set (fun v hv => hWU hv.2)
  have hfibψ : ∀ b, ∫⁻ v, ψ v ∂(fib b) ≤ S.indicator (fun _ => ENNReal.ofReal ε) b := by
    intro b
    have hae : ∀ᵐ v ∂(fib b), f' v = b := by
      refine ae_iff.mpr (measure_mono_null ?_ (hsupp b))
      intro v hv hv'
      exact hv (hι ((hff v).symm.trans hv'.1))
    by_cases hbS : b ∈ S
    · rw [Set.indicator_of_mem hbS]
      have heq : ∫⁻ v, ψ v ∂(fib b) = ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        have hvS : v ∈ f' ⁻¹' S := by
          rw [Set.mem_preimage, hv]
          exact hbS
        rw [hψ, Set.indicator_of_mem hvS]
      rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hint b (Set.mem_univ b))
        (Eventually.of_forall hφ0)]
      exact ENNReal.ofReal_le_ofReal (hSε b hbS).le
    · have heq : ∫⁻ v, ψ v ∂(fib b) = ∫⁻ _v, (0 : ℝ≥0∞) ∂(fib b) := by
        apply lintegral_congr_ae
        filter_upwards [hae] with v hv
        have hvS : v ∉ f' ⁻¹' S := by
          rw [Set.mem_preimage, hv]
          exact hbS
        simp [hψ, hvS]
      rw [heq, lintegral_zero]
      exact bot_le
  have hU : ∫⁻ v in U, ψ v ∂μ ≤ ENNReal.ofReal ε * ν S := by
    rw [hdis ψ hψm]
    calc ∫⁻ b, ∫⁻ v, ψ v ∂(fib b) ∂ν ≤ ∫⁻ b, S.indicator (fun _ => ENNReal.ofReal ε) b ∂ν :=
          lintegral_mono hfibψ
      _ = ENNReal.ofReal ε * ν S := lintegral_indicator_const hSm _
  have hlt : ENNReal.ofReal ε < c * ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal hc', ← ENNReal.ofReal_mul hcr.le,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have := mul_pos hcr hδ
    linarith
  have h0 : ENNReal.ofReal δ * (c * ν S) ≤ ENNReal.ofReal δ * μ (f ⁻¹' (ι '' S) ∩ W) := by
    gcongr
  have h1 : ENNReal.ofReal δ * (c * ν S) ≤ ENNReal.ofReal ε * ν S := h0.trans (hA.trans hU)
  have h2 : ν S * ENNReal.ofReal ε < ν S * (c * ENNReal.ofReal δ) :=
    ENNReal.mul_lt_mul_right hνS0 hνSfin hlt
  have h3 : ENNReal.ofReal δ * (c * ν S) = ν S * (c * ENNReal.ofReal δ) := by ring
  have h4 : ENNReal.ofReal ε * ν S = ν S * ENNReal.ofReal ε := by ring
  rw [h3, h4] at h1
  exact lt_irrefl _ (h1.trans_lt h2)

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X0 : Fin n → Fin M → E) :
    gramR R σ J (ratTup R X0) = (gramE σ J X0).map (inclR R) := by
  have hs : ∀ e : E, sigR R σ (inclR R e) = inclR R (σ e) := by
    intro e
    simp [sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  ext a b
  simp only [gramR, gramE, hR, hE, Formalism.UG.hform, ratTup, JR, Matrix.map_apply, hs, map_sum, map_mul,
    AlgHom.coe_toRingHom]

end LocPosW

open LocPosW

def LBInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a)),
    μinf.IsAddHaarMeasure → νinf.IsAddHaarMeasure →
    ∀ W : Set (Fin a → Fin M → Ainf F ⊗[F] E), IsOpen W → ratTup (F := F) (Ainf F) X0 ∈ W →
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT),
      ∀ S ⊆ N, MeasurableSet S →
        c * νinf S ≤ μinf ((gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W)

theorem archPos_of_lb (hL : LBInf) : ArchPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Ainf F) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  have hX1U : X1 ∈ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset t7 hX1U
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := X1)) isOpen_interior.isClosed_compl
    (disjoint_singleton_left.2 fun h => h hxK)
  have hsupp : Function.support φ ⊆ interior K := fun X hX => by
    by_contra h
    exact hX (hφ0 h)
  have hts : tsupport φ ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    (closure_mono hsupp).trans ((closure_minimal interior_subset hK.isClosed).trans hKU)
  let W : Set (Fin a → Fin M → Ainf F ⊗[F] E) := {X | (1 / 2 : ℝ) < φ X}
  have hWo : IsOpen W := isOpen_lt continuous_const φ.continuous
  have hX1W : X1 ∈ W := by
    show (1 / 2 : ℝ) < φ X1
    rw [hφ1 (mem_singleton X1)]
    norm_num
  have hWU : W ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    fun X hX => hts (subset_tsupport _ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hX).ne')
  obtain ⟨c, hc0, hctop, N, hN, hlb⟩ :=
    hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ.1 hν.1 W hWo hX1W
  have hpos := pos_of_lb (f' := gramH (Ainf F) σ hσ J hJ.1) Subtype.val_injective hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) φ.continuous hφc hts
    (fun X => (hφr X).1) hWU (by norm_num : (0 : ℝ) < 1 / 2) (fun X hX => hX.le) hc0 hctop hN hlb
    (fun O hO hne => (hO.measure_pos νinf hne).ne') (νinf.finiteAt_nhds _)
  refine ⟨fun X => ((φ X : ℝ) : ℂ), Complex.continuous_ofReal.comp φ.continuous,
    hφc.comp_left Complex.ofReal_zero, ?_⟩
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end PI.VolStabW
end
end


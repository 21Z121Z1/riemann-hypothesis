import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizer

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActio
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeEx.ProdTransport

theorem tprod_tail_split {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (hf : Summable fun v => |f v - 1|)
    (S S' : Finset ι) (h : S ⊆ S') :
    ∏' v : {v // v ∉ S}, f v.1 = (∏ v ∈ S' \ S, f v) * ∏' v : {v // v ∉ S'}, f v.1 := by
  have hm : Multipliable fun v : {v // v ∉ S'} => f v.1 := by
    have h1 : Summable fun v : {v // v ∉ S'} => ‖f v.1 - 1‖ := hf.subtype _
    simpa using multipliable_one_add_of_summable h1
  have e1 : ∀ T : Finset ι, ∀ a, HasProd (fun v : {v // v ∉ T} => f v.1) a ↔
      HasProd (Set.mulIndicator {v | v ∉ T} f) a := fun T a =>
    hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})
  have h2 := (e1 S' _).1 hm.hasProd
  have h3 : HasProd (Set.mulIndicator (↑(S' \ S) : Set ι) f) (∏ v ∈ S' \ S, f v) :=
    hasProd_subtype_iff_mulIndicator.1 ((S' \ S).hasProd f)
  have h4 := h3.mul h2
  refine ((e1 S _).2 ?_).tprod_eq
  convert h4 using 1
  funext v
  by_cases h5 : v ∈ S
  · simp [Set.mulIndicator, h5, h h5]
  · by_cases h6 : v ∈ S' <;> simp [Set.mulIndicator, h5, h6]

theorem abstract_transport {ι X Xi : Type*} {Xv : ι → Type*} [MeasurableSpace X] [MeasurableSpace Xi]
    [∀ v, MeasurableSpace (Xv v)] (pI : X → Xi) (pv : ∀ v, X → Xv v) (hpv : ∀ v, Measurable (pv v))
    (L : ∀ v, Set (Xv v)) (hL : ∀ v, MeasurableSet (L v))
    (T : X ≃ᵐ X) (Ti : Xi → Xi) (Tv : ∀ v, Xv v → Xv v) (hTi : Measurable Ti)
    (hTv : ∀ v, Measurable (Tv v)) (hci : ∀ x, pI (T x) = Ti (pI x))
    (hcv : ∀ v x, pv v (T x) = Tv v (pv v x)) (S₀ : Finset ι) (hS₀ : ∀ v ∉ S₀, Tv v ⁻¹' L v = L v)
    (ν : Measure X) (mi : Measure Xi) (mv : ∀ v, Measure (Xv v))
    (hfin : ∀ v, mv v (Tv v ⁻¹' L v) ≠ ∞)
    (hsum : Summable fun v => |((mv v).map (Tv v) (L v)).toReal - 1|)
    (H : ∀ (S : Finset ι) (fi : Xi → ℝ≥0∞) (fv : ∀ v, Xv v → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pI x) * ∏ v ∈ S, fv v (pv v x) ∂ν =
        (∫⁻ y, fi y ∂mi) * (∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v)) *
          ENNReal.ofReal (∏' v : {v // v ∉ S}, (mv v.1 (L v.1)).toReal))
    (S : Finset ι) (fi : Xi → ℝ≥0∞) (fv : ∀ v, Xv v → ℝ≥0∞)
    (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pI x) * ∏ v ∈ S, fv v (pv v x) ∂(ν.map T) =
      (∫⁻ y, fi y ∂(mi.map Ti)) * (∏ v ∈ S, ∫⁻ y, fv v y ∂((mv v).map (Tv v))) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, ((mv v.1).map (Tv v.1) (L v.1)).toReal) := by
  classical
  have hsub : S ⊆ S ∪ S₀ := Finset.subset_union_left
  have hTL : ∀ v, MeasurableSet (Tv v ⁻¹' L v) := fun v => hTv v (hL v)
  let gv : ∀ v, Xv v → ℝ≥0∞ := fun v =>
    if v ∈ S then fv v ∘ Tv v else (Tv v ⁻¹' L v).indicator 1
  have hgv : ∀ v, Measurable (gv v) := by
    intro v
    by_cases h : v ∈ S
    · simpa [gv, h] using (hfv v).comp (hTv v)
    · simpa [gv, h] using (measurable_one.indicator (hTL v))
  have key := H (S ∪ S₀) (fi ∘ Ti) gv (hfi.comp hTi) hgv
  let B : Set X := {x | ∀ v ∈ (S ∪ S₀) \ S, pv v x ∈ Tv v ⁻¹' L v}
  have hB : MeasurableSet B := by
    have : B = ⋂ v ∈ (S ∪ S₀) \ S, pv v ⁻¹' (Tv v ⁻¹' L v) := by
      ext x; simp only [B, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact Finset.measurableSet_biInter _ fun v _ => hpv v (hTL v)
  have hset : T ⁻¹' {x | ∀ v ∉ S, pv v x ∈ L v} = B ∩ {x | ∀ v ∉ S ∪ S₀, pv v x ∈ L v} := by
    ext x
    simp only [B, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff, hcv]
    constructor
    · intro h
      refine ⟨fun v hv => h v (Finset.mem_sdiff.1 hv).2, fun v hv => ?_⟩
      rw [← hS₀ v fun h' => hv (Finset.mem_union_right _ h')]
      exact h v fun h' => hv (hsub h')
    · rintro ⟨h1, h2⟩ v hv
      by_cases h : v ∈ S ∪ S₀
      · exact h1 v (Finset.mem_sdiff.2 ⟨h, hv⟩)
      · have := h2 v h
        rwa [← hS₀ v fun h' => h (Finset.mem_union_right _ h')] at this
  have hl : ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pI x) * ∏ v ∈ S, fv v (pv v x) ∂(ν.map T) =
      ∫⁻ x in {x | ∀ v ∉ S ∪ S₀, pv v x ∈ L v},
        (fi ∘ Ti) (pI x) * ∏ v ∈ S ∪ S₀, gv v (pv v x) ∂ν := by
    rw [T.restrict_map, lintegral_map_equiv, hset, ← Measure.restrict_restrict hB,
      ← lintegral_indicator hB]
    refine lintegral_congr fun x => ?_
    rw [← Finset.prod_sdiff hsub]
    have e1 : ∏ v ∈ S, gv v (pv v x) = ∏ v ∈ S, fv v (pv v (T x)) :=
      Finset.prod_congr rfl fun v hv => by simp [gv, hv, hcv]
    rw [e1]
    by_cases hx : x ∈ B
    · have e2 : ∏ v ∈ (S ∪ S₀) \ S, gv v (pv v x) = 1 :=
        Finset.prod_eq_one fun v hv => by
          simp only [gv, if_neg (Finset.mem_sdiff.1 hv).2]
          exact Set.indicator_of_mem (hx v hv) _
      rw [Set.indicator_of_mem hx, e2, one_mul, hci]; rfl
    · rw [Set.indicator_of_notMem hx]
      simp only [B, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hv, hv'⟩ := hx
      have e2 : ∏ v ∈ (S ∪ S₀) \ S, gv v (pv v x) = 0 :=
        Finset.prod_eq_zero hv (by
          simp only [gv, if_neg (Finset.mem_sdiff.1 hv).2]
          exact Set.indicator_of_notMem hv' _)
      rw [e2, zero_mul, mul_zero]
  rw [hl, key, tprod_tail_split _ hsum S (S ∪ S₀) hsub, ← Finset.prod_sdiff hsub,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg), lintegral_map hfi hTi]
  have e1 : ∏ v ∈ S, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ S, ∫⁻ y, fv v y ∂((mv v).map (Tv v)) :=
    Finset.prod_congr rfl fun v hv => by
      rw [lintegral_map (hfv v) (hTv v)]; simp [gv, hv]
  have e2 : ∏ v ∈ (S ∪ S₀) \ S, ∫⁻ y, gv v y ∂(mv v) =
      ∏ v ∈ (S ∪ S₀) \ S, ENNReal.ofReal ((mv v).map (Tv v) (L v)).toReal :=
    Finset.prod_congr rfl fun v hv => by
      simp only [gv, if_neg (Finset.mem_sdiff.1 hv).2]
      rw [lintegral_indicator_one (hTL v), Measure.map_apply (hTv v) (hL v),
        ENNReal.ofReal_toReal (hfin v)]
  have e3 : ∏' v : {v // v ∉ S ∪ S₀}, (mv v.1 (L v.1)).toReal =
      ∏' v : {v // v ∉ S ∪ S₀}, ((mv v.1).map (Tv v.1) (L v.1)).toReal :=
    tprod_congr fun v => by
      rw [Measure.map_apply (hTv v) (hL v), hS₀ v.1 fun h' => v.2 (Finset.mem_union_right _ h')]
  rw [e1, e2, e3]
  simp only [Function.comp]
  ring

section Lr
variable {S : Type} [CommRing S] {n M : ℕ}

theorem lrAct_eq (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) :
    lrAct g γ X = fun a i => (g * (Matrix.of X).transpose * γ) i a := by
  funext a i
  rw [Matrix.mul_assoc]
  simp [lrAct, Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem lrAct_lrAct (g g' : Matrix (Fin M) (Fin M) S) (γ γ' : Matrix (Fin n) (Fin n) S)
    (hg : g' * g = 1) (hγ : γ * γ' = 1) (X : Fin n → Fin M → S) :
    lrAct g' γ' (lrAct g γ X) = X := by
  rw [lrAct_eq, lrAct_eq]
  have : (Matrix.of fun a i => (g * (Matrix.of X).transpose * γ) i a).transpose =
      g * (Matrix.of X).transpose * γ := by ext; rfl
  rw [this]
  have : g' * (g * (Matrix.of X).transpose * γ) * γ' = (Matrix.of X).transpose := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul, Matrix.mul_assoc, hγ,
      Matrix.mul_one]
  rw [this]; rfl

theorem map_lrAct {S' : Type} [CommRing S'] (φ : S →+* S') (g : Matrix (Fin M) (Fin M) S)
    (γ : Matrix (Fin n) (Fin n) S) (X : Fin n → Fin M → S) :
    (fun a i => φ (lrAct g γ X a i)) = lrAct (g.map φ) (γ.map φ) fun a i => φ (X a i) := by
  funext a i
  simp [lrAct, Matrix.mulVec, dotProduct]

theorem continuous_lrAct [TopologicalSpace S] [IsTopologicalRing S] (g : Matrix (Fin M) (Fin M) S)
    (γ : Matrix (Fin n) (Fin n) S) : Continuous (lrAct g γ) := by
  unfold lrAct Matrix.mulVec dotProduct
  fun_prop

def lrHomeo [TopologicalSpace S] [IsTopologicalRing S] (g : GL (Fin M) S) (γ : GL (Fin n) S) :
    (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S) where
  toFun := lrAct g.val γ.val
  invFun := lrAct g⁻¹.val γ⁻¹.val
  left_inv := lrAct_lrAct _ _ _ _ g.inv_mul γ.mul_inv
  right_inv := lrAct_lrAct _ _ _ _ g.mul_inv γ.inv_mul
  continuous_toFun := continuous_lrAct _ _
  continuous_invFun := continuous_lrAct _ _

theorem lrAct_mem (A : AddSubmonoid S) (hA : ∀ y ∈ A, ∀ z ∈ A, y * z ∈ A)
    (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S) (hg : ∀ i j, g i j ∈ A)
    (hγ : ∀ i j, γ i j ∈ A) (X : Fin n → Fin M → S) (hX : ∀ a i, X a i ∈ A) (a : Fin n) (i : Fin M) :
    lrAct g γ X a i ∈ A := by
  change ∑ j, g i j * ∑ c, X c j * γ c a ∈ A
  exact A.sum_mem fun _ _ => hA _ (hg _ _) _ (A.sum_mem fun _ _ => hA _ (hX _ _) _ (hγ _ _))

theorem finiteOnCompacts_map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : Y ≃ₜ Y) (m : Measure Y) (hm : IsFiniteMeasureOnCompacts m) :
    IsFiniteMeasureOnCompacts (m.map e) where
  lt_top_of_isCompact K hK := by
    have := e.toMeasurableEquiv.map_apply (μ := m) K
    rw [show m.map e K = m (e ⁻¹' K) from this]
    exact (e.isCompact_preimage.2 hK).measure_lt_top

end Lr

def intVAdd {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : AddSubmonoid (Fv F v ⊗[F] E) where
  carrier := intV b v
  zero_mem' := fun k => by simp
  add_mem' := fun {x y} hx hy k => by
    rw [map_add, Finsupp.add_apply]
    exact add_mem (hx k) (hy k)

theorem isProd_map_lrAct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : GL (Fin M) (AF F ⊗[F] E)) (γ : GL (Fin n) (AF F ⊗[F] E)), IsProd b ν mi mv → IsProd b (ν.map (lrAct g.val γ.val)) (mi.map (lrAct (g.val.map prInf) (γ.val.map prInf))) (fun v => (mv v).map (lrAct (g.val.map (prV v)) (γ.val.map (prV v)))) := by
  intro F E _ _ _ _ _ d b n M ν mi mv g γ ⟨⟨hmi, hmv, hsum⟩, H⟩
  classical
  obtain ⟨-, -, -, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  obtain ⟨hco, hsr, hz, -⟩ := GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d b
  let eI := lrHomeo (Matrix.GeneralLinearGroup.map (prInf (F := F) (E := E)) g)
    (Matrix.GeneralLinearGroup.map (prInf (F := F) (E := E)) γ)
  let eV := fun v : HeightOneSpectrum (𝓞 F) =>
    lrHomeo (Matrix.GeneralLinearGroup.map (prV (F := F) (E := E) v) g)
      (Matrix.GeneralLinearGroup.map (prV (F := F) (E := E) v) γ)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F), (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => Set.univ.pi fun _ => intV b v := fun v => by
    ext Y; simp only [mem_latV_iff, Set.mem_univ_pi]
  have hlc : ∀ v : HeightOneSpectrum (𝓞 F),
      IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := fun v => by
    rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hco v).1
  have hL : ∀ v : HeightOneSpectrum (𝓞 F),
      MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := fun v =>
    (hlc v).isClosed.measurableSet
  have hmat : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)),
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, prV v (A i j) ∈ intV b v := fun A =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hz _
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, eV v ⁻¹' latV b v = latV b v := by
    filter_upwards [hsr, hmat g.val, hmat γ.val, hmat g⁻¹.val, hmat γ⁻¹.val] with v h0 h1 h2 h3 h4
    ext Y
    constructor
    · intro hY
      have := lrAct_mem (intVAdd b v) h0.2.1 (g⁻¹.val.map (prV v)) (γ⁻¹.val.map (prV v)) h3 h4 _ hY
      have e : lrAct (g⁻¹.val.map (prV v)) (γ⁻¹.val.map (prV v)) (eV v Y) = Y := by
        refine lrAct_lrAct (g.val.map (prV v)) _ (γ.val.map (prV v)) _ ?_ ?_ Y
        · rw [← Matrix.map_mul, g.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        · rw [← Matrix.map_mul, γ.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [e] at this
      exact this
    · intro hY
      exact lrAct_mem (intVAdd b v) h0.2.1 (g.val.map (prV v)) (γ.val.map (prV v)) h1 h2 _ hY
  have hfinS := Filter.eventually_cofinite.1 hev
  have hS₀ : ∀ v ∉ hfinS.toFinset, eV v ⁻¹' latV b v = latV b v := fun v hv => by
    simpa using hv
  have hsum' : Summable fun v => |((mv v).map (eV v) (latV b v)).toReal - 1| := by
    refine (summable_congr_cofinite ?_).1 hsum
    filter_upwards [hev] with v hv
    rw [Measure.map_apply (eV v).continuous.measurable (hL v), hv]
  refine ⟨⟨finiteOnCompacts_map eI mi hmi, fun v => finiteOnCompacts_map (eV v) (mv v) (hmv v), hsum'⟩,
    fun S fi fv hfi hfv => ?_⟩
  exact abstract_transport projInf (fun v X => projV v (projFin X)) (fun v => (hcv v).measurable)
    (fun v => latV b v) hL (lrHomeo g γ).toMeasurableEquiv eI (fun v => eV v) eI.continuous.measurable
    (fun v => (eV v).continuous.measurable) (fun X => map_lrAct prInf g.val γ.val X)
    (fun v X => map_lrAct (prV v) g.val γ.val X) hfinS.toFinset hS₀ ν mi mv
    (fun v => by
      have := hmv v
      exact ((eV v).isCompact_preimage.2 (hlc v)).measure_lt_top.ne) hsum' H S fi fv hfi hfv

end GlobalTheory.GaugeEx.ProdTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeight
section
open Matrix Formalism.MainNotions.S GlobalTheory.JointHarm

noncomputable section

namespace GlobalTheory.JointHarm.Sph

variable {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ}

theorem entire_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∀ t : ℝ, f t = 0) (z : ℂ) : f z = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) ?_
    (Set.mem_univ z)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall h).frequently

theorem diag_mem {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => hd a

theorem mul_mem {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) (hb : b ∈ GlobalTheory.Dec.KC ε) :
    a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem ct_mem {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) : aᴴ ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
  exact this.symm

section One

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P}

theorem diff_curve (h : IsHolRep ε B π) {c : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hc : ∀ i j, Differentiable ℂ fun z => c z i j) (hm : ∀ z, c z ∈ GlobalTheory.Dec.KC ε) (x y : P) :
    Differentiable ℂ fun z => B x (π (c z) y) := by
  have h1 : Differentiable ℂ fun z => (fun i j => c z i j : Fin n → Fin n → ℂ) :=
    differentiable_pi.2 fun i => differentiable_pi.2 fun j => hc i j
  have := (h.2.2.2.2 x y).comp (s := Set.univ) h1.differentiableOn (fun z _ => hm z)
  exact differentiableOn_univ.1 this

theorem real_torus (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) (s : Fin n → ℝ) :
    π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x = Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x := by
  rw [← sub_eq_zero]
  apply h.1
  generalize hw : π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x -
    Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x = w
  have hd := diff_curve h (c := fun z => Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I))
    (fun i j => by
      by_cases e : i = j
      · subst e; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ e]; fun_prop)
    (fun z => diag_mem fun a => Complex.exp_ne_zero _) w x
  have h0 := entire_eq_zero (f := fun z => B w (π (Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I)) x) -
      Complex.exp (z * ((∑ a, μ a * s a : ℝ) : ℂ) * Complex.I) * B w x) (hd.sub (by fun_prop))
    (fun t => by
      have := hx.2 (fun a => t * s a)
      have e : (∑ a, μ a * (t * s a)) = t * ∑ a, μ a * s a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [e] at this
      simp only [Complex.ofReal_mul] at this
      simp only [this, map_smul, smul_eq_mul, sub_self]) (-Complex.I)
  have e : ∀ u : ℂ, -Complex.I * u * Complex.I = u := fun u => by
    linear_combination (-u) * Complex.I_mul_I
  simp only [e] at h0
  conv_lhs => enter [2]; rw [← hw]
  rw [map_sub, map_smul, smul_eq_mul, h0]

theorem borel {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ GlobalTheory.Dec.KC ε) (hl : GlobalTheory.Dec.IsLo b)
    (hp : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ))
    (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) :
    π b x = Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ) • x := by
  have hne : ∀ i, b i i ≠ 0 := fun i => by rw [hp i]; exact Complex.exp_ne_zero _
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ GlobalTheory.Dec.KC ε :=
    mul_mem (diag_mem fun a => inv_ne_zero (hne a)) hb
  have hlu : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := fun i j =>
    ⟨fun hij => by rw [Matrix.diagonal_mul, hl i j hij, mul_zero],
      fun hij => by subst hij; rw [Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]⟩
  have e : b = Matrix.diagonal (fun a => Complex.exp (Real.log (b a a).re : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, ← hp i, mul_inv_cancel_left₀ (hne i)]
  conv_lhs => rw [e]
  rw [h.2.2.1 _ (diag_mem fun a => Complex.exp_ne_zero _) _ hu, Module.End.mul_apply, hx.1 _ hu hlu,
    real_torus h hx]

end One

open scoped ComplexOrder in

theorem gram {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) (μ : Fin n → ℝ) :
    ∃ c : ℂ, ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
      (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (x y : P), IsHolRep ε B π → IsBottom ε π μ x →
      IsBottom ε π μ y → B x (π (gᴴ * g) y) = c * B x y := by
  obtain ⟨k, b, hk, hb, hl, hp, rfl⟩ := GlobalTheory.Dec.IwKC.exists_decomp ε hg
  have hp' : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ) := fun i => by
    have := Complex.pos_iff.1 (hp i)
    rw [← Complex.ofReal_exp, Real.exp_log this.1]
    exact Complex.ext rfl (by simpa using this.2.symm)
  refine ⟨star (Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ)) *
    Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ), fun P _ _ B π x y h hx hy => ?_⟩
  rw [GlobalTheory.Dec.IwKC.gram_unitary_mul hk.1, h.2.2.1 _ (ct_mem hb) _ hb, Module.End.mul_apply,
    ← h.2.2.2.1 _ hb, borel hb hl hp' h hx, borel hb hl hp' h hy]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
  ring

section Exp

open scoped Matrix.Norms.Operator

theorem exp_mem {H : Matrix (Fin n) (Fin n) ℂ} (hJ : H * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * H) (z : ℂ) :
    NormedSpace.exp (z • H) ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨Matrix.isUnit_exp _, ?_⟩
  have : Commute (z • H) (Formalism.REAL.Jm ε) := Commute.smul_left hJ z
  exact this.exp_left.eq

theorem exp_diff (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) i j := by
  have h1 : Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) :=
    fun z => (hasDerivAt_exp_smul_const H z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp h1

theorem exp_gram {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • H) =
      (NormedSpace.exp (((t : ℂ) / 2) • H))ᴴ * NormedSpace.exp (((t : ℂ) / 2) • H) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH]
  have e : star ((t : ℂ) / 2) = (t : ℂ) / 2 := by simp
  rw [e, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, add_halves]

end Exp

theorem coeff_eq (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P]
    (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P']
    [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P)
    (x' y' : P') (h : IsHolRep ε B π) (h' : IsHolRep ε B' π') (hx : IsBottom ε π μ x) (hy : IsBottom ε π μ y)
    (hx' : IsBottom ε π' μ x') (hy' : IsBottom ε π' μ y') :
    ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  intro k hk
  obtain ⟨Y, ⟨hG, hY⟩, rfl, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  have hs : Yᴴ = -Y := by
    have h1 : (Yᴴ + Y) * Formalism.REAL.Jm ε = 0 := by
      rw [Matrix.add_mul, hY]; exact hG
    have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hH : ((-Complex.I) • Y)ᴴ = (-Complex.I) • Y := by
    rw [Matrix.conjTranspose_smul, hs]; simp
  have hJ : ((-Complex.I) • Y) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((-Complex.I) • Y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hY]
  have h0 := entire_eq_zero (f := fun z => B x (π (NormedSpace.exp (z • (-Complex.I) • Y)) y) * B' x' y' -
      B x y * B' x' (π' (NormedSpace.exp (z • (-Complex.I) • Y)) y'))
    (((diff_curve h (exp_diff _) (exp_mem hJ) x y).mul_const _).sub
      ((diff_curve h' (exp_diff _) (exp_mem hJ) x' y').const_mul _))
    (fun t => by
      obtain ⟨c, hc⟩ := gram (exp_mem hJ ((t : ℂ) / 2)) μ
      simp only [exp_gram hH t, hc P B π x y h hx hy, hc P' B' π' x' y' h' hx' hy']
      ring) Complex.I
  have e : Complex.I • (-Complex.I) • Y = Y := by rw [smul_smul]; simp
  simp only [e] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.JointHarm.Sph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductTailSplitFiniteFactorsStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProduct_tail_split_finite_factors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → tailProd b mv S = (∏ v ∈ T, mv v (latV b v)) * tailProd b mv S' := by
  first | exact @GlobalTheory.GaugeEx.TailSplit.main | exact GlobalTheory.GaugeEx.TailSplit.main | (intros; apply GlobalTheory.GaugeEx.TailSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_bounded_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧ ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  first | exact @GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | exact GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | (intros; apply GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  first | exact @GlobalTheory.Mem.InfGroup.real_points | exact GlobalTheory.Mem.InfGroup.real_points | (intros; apply GlobalTheory.Mem.InfGroup.real_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamondStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardHeckeOperator_commute_diamond : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  first | exact @GlobalTheory.LevelHecke.UpDia.upAd_dia | exact GlobalTheory.LevelHecke.UpDia.upAd_dia | (intros; apply GlobalTheory.LevelHecke.UpDia.upAd_dia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizerStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_haar_orbit_stabilizer : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), ∀ (μ' : Measure (MulAction.stabilizer G x₀)) (ν : Measure X), μ'.IsHaarMeasure → IsFiniteMeasureOnCompacts ν → ν ≠ 0 → (∀ g : G, ν.map (fun y => g • y) = ν) → ν {y | ¬ ∃ g : G, g • x₀ = y} = 0 → ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s y * (h : G)) ∂μ' ∂ν := by
  first | exact @GlobalTheory.GaugeWeil.weil_formula | exact GlobalTheory.GaugeWeil.weil_formula | (intros; apply GlobalTheory.GaugeWeil.weil_formula <;> assumption)
end


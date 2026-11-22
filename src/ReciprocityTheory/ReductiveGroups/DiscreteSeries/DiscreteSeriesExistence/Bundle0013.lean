import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0010
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0012
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEab
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eab_cpart1_eq (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z = S7.cpart1 ε Z := rfl

theorem eab_cpart2_eq (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart2 ε Z = S7.cpart2 ε Z := rfl

theorem eab_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε Z + Complex.I • S7.cpart2 ε Z = Z := by
  unfold S7.cpart1 S7.cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = (1 / 2 : ℂ) by field_simp]
  rw [← smul_add]
  rw [show Z - Jm ε * Zᴴ * Jm ε + (Z + Jm ε * Zᴴ * Jm ε) = (2 : ℂ) • Z by rw [two_smul]; abel]
  rw [smul_smul]; norm_num

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def dinj_jLin (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := uniformisationL2 ε Ψ v₀
  map_add' := datumEmbedding_add hP v₀
  map_smul' := datumEmbedding_smul hP v₀

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dinj_continuousOn_of_smoothOnGV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg₀U)] with g hg
  exact hfF g hg.2 hg.1

end

theorem dinj_one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show inUJ ε 1
  simp [inUJ]

theorem uniformisationL2_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (uniformisationL2 ε Ψ v₀) := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat g ∈ UJset ε := fun g => g.2
  have hum : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hΨu : Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
    (dinj_continuousOn_of_smoothOnGV hP.2.2.1).comp_continuous hum hmem
  have hfc : ∀ v, Continuous (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) := by
    intro v
    simp only [jfun]
    exact continuous_const.inner (hΨu.clm_apply continuous_const)
  have hML : ∀ v, MemLp (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) 2
      (Formalism.REAL.muG ε) := by
    intro v
    have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
    have h0 := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
    have h2 := ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h0
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun g => ?_) h2
    simp [jfun] <;> rfl
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by unfold Formalism.REAL.muG; infer_instance
  have hz : ∀ v, uniformisationL2 ε Ψ v₀ v = 0 ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 := by
    intro v
    have hm := hML v
    have e1 : uniformisationL2 ε Ψ v₀ v = hm.toLp _ := by
      unfold uniformisationL2 toL2
      exact dif_pos hm
    rw [e1, Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h g
      have h5 := ((hfc v).ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).mp
        (hm.coeFn_toLp.symm.trans h)
      exact congrFun h5 g
    · intro h
      exact hm.coeFn_toLp.trans (Filter.Eventually.of_forall fun g => h g)
  have hstab : ∀ (k : S7.KG ε) (v : T.V),
      (∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0) →
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ (T.op k v) (Formalism.MainNotions.S.umat g) = 0 := by
    intro k v hv g
    have hk := hP.1 1 k (Formalism.MainNotions.S.umat g) (hmem g)
    have ht1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    have ho1 : T.op 1 = 1 := by simp [S7.KType.op]
    rw [ht1, ho1, one_mul, one_mul] at hk
    let y : Formalism.REAL.UJ ε := (k : S7.UJ ε)
    have hy : Formalism.MainNotions.S.umat (g * y) = Formalism.MainNotions.S.umat g * S7.toMK k := rfl
    have h3 := hv (g * y)
    rw [hy] at h3
    simp only [jfun] at h3 ⊢
    rw [hk] at h3
    simpa using h3
  have hne : uniformisationL2 ε Ψ v₀ v₀ ≠ 0 := by
    intro h0
    have h6 : jfun Ψ v₀ v₀ 1 = 0 := (hz v₀).1 h0 1
    simp only [jfun, hP.2.1, ContinuousLinearMap.one_apply] at h6
    exact hv₀ (inner_self_eq_zero.mp h6)
  have hker : ∀ v, v ∈ LinearMap.ker (dinj_jLin hP v₀) ↔
      ∀ g : Formalism.REAL.UJ ε, jfun Ψ v₀ v (Formalism.MainNotions.S.umat g) = 0 :=
    fun v => LinearMap.mem_ker.trans (hz v)
  rcases T.irred (LinearMap.ker (dinj_jLin hP v₀))
      (fun k v hv => (hker _).2 (hstab k v ((hker v).1 hv))) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    have hv : v₀ ∈ LinearMap.ker (dinj_jLin hP v₀) := by
      rw [h]
      exact Submodule.mem_top
    exact hne (LinearMap.mem_ker.1 hv)

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsSchur
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem propsSchur_kset_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ UJset ε := by
  rw [mir_Kset_eq] at hg
  obtain ⟨hu, hc⟩ := hg
  show gᴴ * Jm ε * g = Jm ε
  have h1 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem propsSchur_maps (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) (A : H →L[ℂ] H)
    (hA : ∀ g ∈ UJset ε, ∀ x, A (σ g x) = σ g (A x)) : ∀ x ∈ V.map D.subtype, A x ∈ V.map D.subtype := by
  have hS := data_isKTypeOf hgap hσ hD hV hc hVK
  have htop := data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0
  have hlow := data_lowK_eq hgap hσ hD hV hc hVK
  set S := V.map D.subtype with hSdef
  obtain ⟨hfd, hKs, hirrK, ⟨v0, hv0S, hv0, hv0w⟩, hcd⟩ := hS
  have hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ UJset ε := fun g hg => propsSchur_kset_mem hg
  let N : Submodule ℂ H := S ⊓ LinearMap.ker (A : H →ₗ[ℂ] H)
  have hNK : Formalism.MainNotions.S.IsKStableOn ε σ N := by
    intro g hg v hv
    refine ⟨hKs g hg v hv.1, ?_⟩
    have h2 : A v = 0 := by simpa using hv.2
    show (A : H →ₗ[ℂ] H) (σ g v) = 0
    simp [hA g (hKU g hg), h2]
  rcases hirrK N inf_le_left hNK with hN | hN
  · have hinj : ∀ x ∈ S, A x = 0 → x = 0 := fun x hx h0 => by
      have hxN : x ∈ N := ⟨hx, by simpa using h0⟩
      rw [hN] at hxN
      simpa using hxN
    let T : Submodule ℂ H := S.map (A : H →ₗ[ℂ] H)
    have hT : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) T := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · haveI := hfd
        infer_instance
      · intro g hg w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨σ g x, hKs g hg x hx, by simp [hA g (hKU g hg)]⟩
      · intro S' hS'T hS'K
        let P : Submodule ℂ H := S ⊓ S'.comap (A : H →ₗ[ℂ] H)
        have hPK : Formalism.MainNotions.S.IsKStableOn ε σ P := by
          intro g hg v hv
          refine ⟨hKs g hg v hv.1, ?_⟩
          have h2 : A v ∈ S' := hv.2
          show A (σ g v) ∈ S'
          rw [hA g (hKU g hg)]
          exact hS'K g hg _ h2
        rcases hirrK P inf_le_left hPK with hP | hP
        · left
          rw [eq_bot_iff]
          intro w hw
          obtain ⟨x, hx, rfl⟩ := hS'T hw
          have hxP : x ∈ P := ⟨hx, hw⟩
          rw [hP] at hxP
          have : x = 0 := by simpa using hxP
          simp [this]
        · right
          refine le_antisymm hS'T ?_
          rintro w ⟨x, hx, rfl⟩
          have hxP : x ∈ P := hP ▸ hx
          exact hxP.2
      · refine ⟨A v0, ⟨v0, hv0S, rfl⟩, fun h => hv0 (hinj v0 hv0S h), ?_⟩
        intro θ hθ
        rw [← hA _ (hKU _ hθ), hv0w θ hθ, map_smul]
      · intro μ w hw hw0 hww
        obtain ⟨x, hx, rfl⟩ := hw
        refine hcd μ x hx (fun h => hw0 (by simp [h])) ?_
        intro θ hθ
        have h1 := hww θ hθ
        have h3 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) x -
            Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x) = 0 := by
          rw [map_sub, map_smul, hA _ (hKU _ hθ)]
          exact sub_eq_zero.mpr h1
        have hmem : σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) x -
            Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x ∈ S :=
          S.sub_mem (hKs _ hθ x hx) (S.smul_mem _ hx)
        exact sub_eq_zero.mp (hinj _ hmem h3)
    have hTle : T ≤ closGen E V := by rw [htop]; exact le_top
    have hTS := hlow T hTle hT
    intro x hx
    rw [← hTS]
    exact ⟨x, hx, rfl⟩
  · intro x hx
    have hxN : x ∈ N := hN ▸ hx
    have h0 : A x = 0 := by simpa using hxN.2
    rw [h0]
    exact S.zero_mem

theorem data_schur (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) (A : H →L[ℂ] H)
    (hA : ∀ g ∈ UJset ε, ∀ x, A (σ g x) = σ g (A x)) : ∃ c : ℂ, A = c • 1 := by
  have hAS := propsSchur_maps hgap hσ hD hV hc hVK hirr hV0 A hA
  obtain ⟨hfd, -, -, ⟨v0, hv0S, hv0, -⟩, -⟩ := data_isKTypeOf hgap hσ hD hV hc hVK
  set S := V.map D.subtype with hSdef
  let AS : Module.End ℂ S := (A : H →ₗ[ℂ] H).restrict hAS
  haveI := hfd
  haveI : Nontrivial S := ⟨⟨⟨v0, hv0S⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue AS
  obtain ⟨u, hu⟩ := hc'.exists_hasEigenvector
  have hAu : A u = c • (u : H) := congrArg Subtype.val hu.apply_eq_smul
  let K0 : Submodule ℂ H := LinearMap.ker ((A - c • 1 : H →L[ℂ] H) : H →ₗ[ℂ] H)
  have hK0c : IsClosed (K0 : Set H) := ContinuousLinearMap.isClosed_ker _
  have hK0s : ∀ g ∈ UJset ε, ∀ v ∈ K0, σ g v ∈ K0 := by
    intro g hg v hv
    have hv' : A v - c • v = 0 := by simpa [K0] using hv
    show ((A - c • 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) (σ g v) = 0
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    rw [hA g hg, ← map_smul, ← map_sub, hv', map_zero]
  rcases hirr K0 hK0c hK0s with h0 | h0
  · exfalso
    have hu0 : (u : H) ∈ K0 := by simp [K0, hAu]
    rw [h0] at hu0
    exact hu.2 (Subtype.ext (by simpa using hu0))
  · refine ⟨c, ?_⟩
    ext x
    have hx : x ∈ K0 := h0 ▸ Submodule.mem_top
    have : A x - c • x = 0 := by simpa [K0] using hx
    simpa [sub_eq_zero] using this

end ReciprocityTheory.ChartRestriction.DS
end
end


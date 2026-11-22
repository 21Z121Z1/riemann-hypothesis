import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0006

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def RPAbs : Prop :=
  ∀ (ι : Type) [Countable ι] (W : ι → Type) [∀ i, MeasurableSpace (W i)]
    (m : ∀ i, Measure (W i)) [∀ i, SigmaFinite (m i)] (L : ∀ i, Set (W i)),
    (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ⊤) →
    (∀ S : Finset ι, ∃ c : ENNReal, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c) →
    ∃ ρ : Measure (∀ i, W i), SFinite ρ ∧
      ρ {x | ¬ ∀ᶠ i in Filter.cofinite, x i ∈ L i} = 0 ∧
      (∀ i (C : Set (W i)), MeasurableSet C → m i Cᶜ = 0 → ρ {x | x i ∉ C} = 0) ∧
      ∀ f : ∀ i, W i → ℂ, (∀ i, Integrable (f i) (m i)) →
        (∀ᶠ i in Filter.cofinite, f i = (L i).indicator 1) →
        Integrable (fun x => ∏ᶠ i, f i (x i)) ρ ∧
        HasProd (fun i => ∫ w, f i w ∂(m i)) (∫ x, ∏ᶠ i, f i (x i) ∂ρ)

def RPFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
      (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E)),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Ainf F) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
      (fib : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib →
    SigmaFinite (fib (hermOf (Fv F v) σ (gramE σ J X0) hT)) ∧
    ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf (Fv F v) σ (gramE σ J X0) hT))

def RPGlue : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (M a d : ℕ) (b : Module.Basis (Fin d) F E),
  ∃ Γ : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) →
      (Fin a → Fin M → AF F ⊗[F] E),
    Measurable Γ ∧ ∀ p, (∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v) →
      projInf (Γ p) = p.1 ∧ ∀ v, projV v (projFin (Γ p)) = p.2 v

def RPGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
  MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} ∧
  MeasurableSet {X : Fin a → Fin M → Ainf F ⊗[F] E |
    gramR (Ainf F) σ J X = T.map (inclR (Ainf F))} ∧
  (∀ v : HeightOneSpectrum (𝓞 F), MeasurableSet {X : Fin a → Fin M → Fv F v ⊗[F] E |
    gramR (Fv F v) σ J X = T.map (inclR (Fv F v))}) ∧
  ∀ X : Fin a → Fin M → AF F ⊗[F] E, gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) →
    (∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) →
    gramR (AF F) σ J X = T.map (inclR (AF F))

def RPTail : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a →
      Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (d : ℕ) (b : Module.Basis (Fin d) F E),
    (∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) →
    (∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ →
      ∫ X, Φ X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} =>
        fibV v.1 (hermOf (Fv F v.1) σ (gramE σ J X0) hT) (latV b v.1)) c

def LatCofin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a M d d' : ℕ)
    (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E),
    ∀ᶠ v in Filter.cofinite, latV (M := M) (n := a) b v = latV b' v

theorem restrProd_of (hA : RPAbs) (hF : RPFib) (hG : RPGlue) (hGr : RPGram) (hTl : RPTail)
    (hL : LatCofin) : RestrProd := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμi νinf hνi μv hμv νv hνv
    fibInf hfi fibV hfv hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have cF := hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨hsfI, hintI⟩ := cF.1 μinf νinf fibInf hfi
  have hFv := fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)
  have hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    fun v Φ h => (hFv v).2 Φ h.1.continuous h.2
  let b := Module.finBasis F E
  rcases hTl F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV _ b hSB (hmult _ b) with
    ⟨v0, hv0⟩ | hconv
  · refine ⟨0, by simp, fun d' b' Φ Φinf Φf Φv _ _ hp _ => ⟨integrable_zero_measure, ?_⟩⟩
    have h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0 :=
      hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩
    rw [integral_zero_measure, h0.tprod_eq, mul_zero]
  · let W : HeightOneSpectrum (𝓞 F) → Type := fun v => Fin a → Fin M → Fv F v ⊗[F] E
    let m : ∀ v, Measure (W v) := fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)
    have : ∀ v, SigmaFinite (m v) := fun v => (hFv v).1
    have := hsfI
    have hLm : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
    have hLf : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
      have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
      rw [integrable_indicator_iff (hLm v)] at h
      exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
    obtain ⟨ρ, hρsf, hρgood, hρmarg, hρint⟩ :=
      hA (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv
    have := hρsf
    obtain ⟨Γ, hΓm, hΓ⟩ := hG F E M a _ b
    have cG := hGr F E σ M J a (gramE σ J X0)
    let P : Measure ((Fin a → Fin M → Ainf F ⊗[F] E) × ∀ v, W v) :=
      (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)).prod ρ
    have hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0 := by
      rw [Measure.prod_prod, hρgood, mul_zero]
    refine ⟨P.map Γ, ?_, ?_⟩
    · rw [Measure.map_apply hΓm cG.1]
      have h1 : (fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))
          {y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) (hfi.1 _)
      have h2 : ∀ v, m v {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        fun v => measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hfv v).1 _)
      have hbad : Γ ⁻¹' {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} ⊆
          ({y | gramR (Ainf F) σ J y = (gramE σ J X0).map (inclR (Ainf F))}ᶜ ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) ∪
            ⋃ v, Set.univ ×ˢ {x : ∀ v, W v | x v ∉
              {x | gramR (Fv F v) σ J x = (gramE σ J X0).map (inclR (Fv F v))}}) := by
        intro p hp
        by_contra hn
        have hi : gramR (Ainf F) σ J p.1 = (gramE σ J X0).map (inclR (Ainf F)) := by
          by_contra h; exact hn (Or.inl ⟨h, Set.mem_univ _⟩)
        have hg : ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
          by_contra h; exact hn (Or.inr (Or.inl ⟨Set.mem_univ _, h⟩))
        have hv : ∀ v, gramR (Fv F v) σ J (p.2 v) = (gramE σ J X0).map (inclR (Fv F v)) := by
          intro v; by_contra h
          exact hn (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨v, Set.mem_univ _, h⟩)))
        obtain ⟨e1, e2⟩ := hΓ p hg
        apply hp
        apply cG.2.2.2 (Γ p)
        · rw [e1]; exact hi
        · intro v; rw [e2 v]; exact hv v
      refine measure_mono_null hbad (measure_union_null ?_ (measure_union_null hgood
        (measure_iUnion_null fun v => ?_)))
      · rw [Measure.prod_prod, h1, zero_mul]
      · rw [Measure.prod_prod, hρmarg v _ (cG.2.2.1 v) (h2 v), mul_zero]
    · intro d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have hΦm : Measurable Φ :=
        TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      have hf : ∀ v, Integrable (Φv v) (m v) := fun v => hSB v _ (hp.1 v)
      have hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 :=
        (hp.2.1.and (hL F E a M d' _ b' b)).mono fun v h => h.1.trans (by rw [h.2])
      obtain ⟨hIρ, hHP⟩ := hρint Φv hf hfc
      have hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
        rw [ae_iff]
        exact measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood
      have hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v) := by
        filter_upwards [hae'] with p hp'
        obtain ⟨e1, e2⟩ := hΓ p hp'
        rw [hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]
        congr 1
        exact finprod_congr fun v => by rw [e2 v]
      have hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P :=
        (hintI Φinf hc1 hc2).mul_prod hIρ
      refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2
        (hPI.congr hae.symm), ?_⟩
      rw [integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae,
        integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)),
        ← hHP.tprod_eq]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
section
noncomputable section

namespace PI.VolStabS.TopoNuFin

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabS.PositiveNearLattice
open scoped TensorProduct ENNReal

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem eventually_int_of_compact {C : Set (Af F)} (hC : IsCompact C) :
    ∀ᶠ v in cofinite, ∀ x ∈ C, x v ∈ v.adicCompletionIntegers F := by
  classical
  let U : Set (Af F) := {y | ∀ v, y v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U :=
    RestrictedProduct.isOpen_forall_mem (fun v => PI.VolStabS.TopoAF.isOpen_integers (F := F) v)
  have h0 : (0 : Af F) ∈ U := fun v => zero_mem _
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => (fun y => y - (x : Af F)) ⁻¹' U)
    (fun x => hU.preimage (continuous_sub_right _))
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using h0⟩)
  have hfin : ∀ᶠ v in cofinite, ∀ i ∈ t, ((i : C) : Af F) v ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset t).mpr fun i _ => i.1.2
  filter_upwards [hfin] with v hv x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  have h1 : (x - (i : Af F)) v ∈ v.adicCompletionIntegers F := hxi v
  have h2 := hv i hi
  have he : x v = (x - (i : Af F)) v + (i : Af F) v := by
    first
    | (rw [RestrictedProduct.sub_apply]; ring)
    | (show x v = (x v - (i : Af F) v) + (i : Af F) v; ring)
  rw [he]
  exact add_mem h1 h2

end Adele

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem zero_mem_latV (a M : ℕ) : (0 : Fin a → Fin M → Fv F v ⊗[F] E) ∈ latV b v := by

  simp only [latV, Set.mem_setOf_eq, Pi.zero_apply, map_zero, Finsupp.zero_apply]
  exact fun _ _ _ => zero_mem _

include b in

theorem exists_clopen_compact {a M : ℕ} {K : Set (Fin a → Fin M → Fv F v ⊗[F] E)}
    (hK : IsCompact K) : ∃ C, IsClopen C ∧ IsCompact C ∧ K ⊆ C := by
  classical
  let L := latV (M := M) (n := a) b v
  have hLo := isClopen_latV b v a M
  have hLc := isCompact_latV b v a M
  let tr : (Fin a → Fin M → Fv F v ⊗[F] E) → Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun y => (Homeomorph.subRight y) ⁻¹' L
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => tr (y : Fin a → Fin M → Fv F v ⊗[F] E))
    (fun y => hLo.isOpen.preimage (Homeomorph.subRight _).continuous)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by
      show z - z ∈ L
      rw [sub_self]
      exact zero_mem_latV b v a M⟩)
  refine ⟨⋃ y ∈ t, tr (y : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_, ht⟩
  · exact isClopen_biUnion_finset fun y _ => hLo.preimage (Homeomorph.subRight _).continuous
  · exact t.isCompact_biUnion fun y _ => (Homeomorph.subRight _).isCompact_preimage.2 hLc

end Local

end PI.VolStabS.TopoNuFin

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabS.PositiveNearLattice PI.VolStabS.TopoNuFin
open scoped TensorProduct ENNReal

theorem nuFin_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (ψ : AddChar (AF F) ℂ)
    (νX : Measure (Fin a → Fin M → AF F ⊗[F] E)) (hν : IsOmT F E σ M J ψ T hT νX)
    (K : Set (Fin a → Fin M → AF F ⊗[F] E)) (hK : IsCompact K) : νX K < ⊤ := by
  classical
  obtain ⟨⟨μinf, hμinf⟩, h1⟩ := hν.2
  obtain ⟨⟨νinf, hνinf⟩, h2⟩ := h1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, h3⟩ := h2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, h4⟩ := h3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, h5⟩ := h4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, h6⟩ := h5 fibInf hfi
  have key := h6 fibV hfv
  let b := Module.finBasis F E

  have hKi : IsCompact (projInf '' K) := hK.image (continuous_projInf b)
  obtain ⟨f, hf1, -, hfc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hKi isClosed_empty (Set.disjoint_empty _)
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f Y : ℝ) : ℂ)
  have hΦic : Continuous Φinf := Complex.continuous_ofReal.comp f.continuous
  have hΦis : HasCompactSupport Φinf := hfc.comp_left Complex.ofReal_zero

  have hKf : IsCompact (projFin '' K) := hK.image (continuous_projFin b)
  let Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun v => projV v '' (projFin '' K)
  have hKv : ∀ v, IsCompact (Kv v) := fun v => hKf.image (TopoMeas.continuous_projV b v)
  have hev : ∀ᶠ v in cofinite, Kv v ⊆ latV b v := by
    have h := fun (x : Fin a) (i : Fin M) (k : Fin (Module.finrank F E)) =>
      eventually_int_of_compact (hKf.image
        (f := fun Y : Fin a → Fin M → Af F ⊗[F] E => crd b (Af F) (Y x i) k)
        ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply x))))
    filter_upwards [eventually_all.2 fun x => eventually_all.2 fun i => eventually_all.2 fun k =>
      h x i k] with v hv
    rintro _ ⟨Y, hY, rfl⟩ x i k
    have e := crd_map b (evalV F v) (Y x i) k
    change crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Y x i)) k ∈ _
    rw [e]
    exact hv x i k _ ⟨Y, hY, rfl⟩
  choose C hCo hCc hKC using fun v => exists_clopen_compact b v (hKv v)
  let Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun v => if Kv v ⊆ latV b v then latV b v else C v
  have hCvo : ∀ v, IsClopen (Cv v) := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact isClopen_latV b v a M
    · rw [show Cv v = C v from if_neg h]; exact hCo v
  have hCvc : ∀ v, IsCompact (Cv v) := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact isCompact_latV b v a M
    · rw [show Cv v = C v from if_neg h]; exact hCc v
  have hKCv : ∀ v, Kv v ⊆ Cv v := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact h
    · rw [show Cv v = C v from if_neg h]; exact hKC v
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (Cv v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v =>
    ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (hCvo v)).isLocallyConstant,
      HasCompactSupport.intro' (hCvc v) (hCvo v).isClosed fun Y hY => Set.indicator_of_notMem hY _⟩
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hev] with v hv
    simp only [Φv, Cv, hv, if_true]
  obtain ⟨hint, -, -⟩ := key _ b Φ Φinf Φf Φv hΦic hΦis hpure (fun _ => rfl)
  have hone : ∀ X ∈ K, Φ X = 1 := by
    intro X hX
    have h1 : Φinf (projInf X) = 1 := by
      simp only [Φinf, hf1 ⟨X, hX, rfl⟩, Pi.one_apply, Complex.ofReal_one]
    have h2 : Φf (projFin X) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      exact Set.indicator_of_mem (hKCv v ⟨projFin X, ⟨X, hX, rfl⟩, rfl⟩) _
    simp only [Φ, h1, h2, mul_one]
  calc νX K ≤ νX {X | 1 ≤ ‖Φ X‖ₑ} := measure_mono fun X hX => by
        simp [hone X hX]
    _ ≤ ∫⁻ X, ‖Φ X‖ₑ ∂νX := by
        have := mul_meas_ge_le_lintegral₀ hint.aestronglyMeasurable.enorm 1
        simpa using this
    _ < ⊤ := hint.2

theorem nuFin_holds : NuFin := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν K hK
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  exact nuFin_gen σ J (gramE σ J X0) hT ψ νX hν K hK

end PI.VolStabS
end
end


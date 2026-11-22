import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.AdmCpt
section
noncomputable section

namespace PI.VolStabW.AdmissibleCompactSupport

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabW PI.VolStabW.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem crd_projV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by
  simp only [projV]
  rw [crd_map]
  rfl

theorem eventually_mem_latV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in cofinite, projV v Y ∈ latV b v := by
  have h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite,
      (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F :=
    fun i j k => (crd b (Af F) (Y i j) k).2
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    h i j k] with v hv
  intro i j k
  have := crd_projV b Y v i j k
  simp only [crd] at this
  rw [this]
  exact hv i j k

variable {a M : ℕ} (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)

end PI.VolStabW.AdmissibleCompactSupport

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.VolStabW.AdmissibleCompactSupport

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfSt
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def SubmDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      DensAll μ f id ν {x | Function.Surjective (fderiv ℝ f x)}

def SubmLocal : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      ∀ x0, Function.Surjective (fderiv ℝ f x0) → ∃ N, IsOpen N ∧ x0 ∈ N ∧ DensAll μ f id ν N

def CoordInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
    (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
      gramR (Ainf F) σ J X) ∧
    ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X))

section Transport

variable {V X Y V' X' : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace V'] [MeasurableSpace V']
  [BorelSpace V'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']

theorem densAll_transport (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V)
    (eV : V ≃ₜ V') (eX : X ≃ₜ X') (f' : V' → X') (hι : Function.Injective ι)
    (hf : ∀ v, ι (eX.symm (f' (eV v))) = f v)
    (h : DensAll (μ.map eV) f' id (ν.map eX) (eV '' U)) : DensAll μ f ι ν U := by
  intro φ hc hs hU
  have hc' : Continuous (φ ∘ eV.symm) := hc.comp eV.symm.continuous
  have hs' : HasCompactSupport (φ ∘ eV.symm) := hs.comp_homeomorph eV.symm
  have hU' : tsupport (φ ∘ eV.symm) ⊆ eV '' U := by
    intro y hy
    have : eV.symm y ∈ tsupport φ := by
      have e : tsupport (φ ∘ eV.symm) = eV.symm ⁻¹' tsupport φ := by
        simpa using (tsupport_comp_eq_preimage φ eV.symm)
      rw [e] at hy; exact hy
    exact ⟨eV.symm y, hU this, by simp⟩
  obtain ⟨g', hg'c, hg'⟩ := h _ hc' hs' hU'
  refine ⟨g' ∘ eX, hg'c.comp eX.continuous, fun S hS => ?_⟩
  have e1 := hg' (eX '' S) (hS.image eX.continuous)
  rw [show ((μ.map eV)) = μ.map eV.toMeasurableEquiv from rfl,
    show ((ν.map eX)) = ν.map eX.toMeasurableEquiv from rfl,
    setIntegral_map_equiv, setIntegral_map_equiv] at e1
  have p1 : (eV.toMeasurableEquiv : V → V') ⁻¹' (f' ⁻¹' (id '' (eX '' S))) = f ⁻¹' (ι '' S) := by
    ext v
    simp only [Set.mem_preimage, Set.image_id, Set.mem_image, Homeomorph.toMeasurableEquiv_coe]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hf v, ← hxe]; simp
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hf v] at hxe
      have := hι hxe
      rw [this]; simp
  have p2 : (eX.toMeasurableEquiv : X → X') ⁻¹' (eX '' S) = S := by
    ext x; simp
  rw [p1, p2] at e1
  simpa [Homeomorph.toMeasurableEquiv_coe] using e1

end Transport

section Local

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

theorem densAll_mono {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X} {U U' : Set V}
    (h : DensAll μ f ι ν U') (hU : U ⊆ U') : DensAll μ f ι ν U := by
  intro φ hc hs hφ
  exact h φ hc hs (hφ.trans hU)

theorem densAll_of_local [T2Space V] [LocallyCompactSpace V] [OpensMeasurableSpace V]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure V} [IsFiniteMeasureOnCompacts μ] {ν : Measure X}
    [IsFiniteMeasureOnCompacts ν] {f : V → Y} {ι : X → Y} {U : Set V}
    (h : ∀ x ∈ U, ∃ N, IsOpen N ∧ x ∈ N ∧ DensAll μ f ι ν N) : DensAll μ f ι ν U := by
  intro φ hc hs hU
  choose N hNo hNx hND using h
  let K := tsupport φ
  have hK : IsCompact K := hs
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => N x.1 (hU x.2))
    (fun x => hNo _ _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hNx _ _⟩)
  let n := t.card
  let N' : K → Set V := fun x => N x.1 (hU x.2)
  let s : Fin n → Set V := fun i => N' (t.equivFin.symm i).1
  have hso : ∀ i, IsOpen (s i) := fun i => hNo _ _
  have hcov : K ⊆ ⋃ i, s i := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨j, hj⟩, ?_⟩
    have e : s (t.equivFin ⟨j, hj⟩) = N' j := by simp only [s, Equiv.symm_apply_apply]
    rw [e]; exact hxj
  obtain ⟨ρ, hρs, hρ1, -, hρc⟩ := exists_continuous_sum_one_of_isOpen_isCompact hso hK hcov
  have hsum : ∀ x, φ x = ∑ i, φ x * ρ i x := by
    intro x
    by_cases hx : x ∈ K
    · have := hρ1 hx
      simp only [Finset.sum_apply, Pi.one_apply] at this
      rw [← Finset.mul_sum, this, mul_one]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hi : ∀ i, ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ = ∫ b in S, g b ∂ν := by
    intro i
    exact hND _ _ (fun v => φ v * ρ i v) (hc.mul (ρ i).continuous) (hs.mul_right)
      ((tsupport_mul_subset_right).trans (hρs i))
  choose g hgc hg using hi
  refine ⟨fun b => ∑ i, g i b, continuous_finsetSum _ fun i _ => hgc i, fun S hS => ?_⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∑ i, ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ := by
    rw [← integral_finsetSum]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsum x)
    · intro i _
      exact ((hc.mul (ρ i).continuous).integrable_of_hasCompactSupport hs.mul_right).integrableOn
  rw [e1, integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => hg i S hS
  · intro i _
    exact (hgc i).continuousOn.integrableOn_compact hS

end Local

theorem densInf_of (hSub : SubmDens) (hCo : CoordInf) : DensInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ :=
    hCo F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet
  have := hμ.1
  have := hν.1
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := hSub n m _ _ hμ' hν' f' hC
  refine densAll_transport μinf νinf (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExFDStab
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def SCHA : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def DiscHF : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  DiscreteTopology (HFinIn (AF F) σ J)

theorem exFDStab_of (h1 : SCHA) (h2 : DiscHF) : ExFDStab := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'
  have i1 : SecondCountableTopology (HA (AF F) σ J) := h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i2 : DiscreteTopology (HFinIn (AF F) σ J) := h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i3 : SecondCountableTopology (stabT (AF F) σ J X0) :=
    TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0)) := DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))
  exact ⟨𝓕, h𝓕 μ'⟩

theorem discHF_of_discHA (h : PI.VolSemiDirect.W.DiscHA) : DiscHF := by
  intro F E _ _ _ _ _ σ hE M J hJ _ _ _ _ _ _ _ _
  exact (h F E σ hE M J hJ).2

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabTop
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem orb_cont (x0 : X) (hc : Continuous fun g : G => g • x0) :
    Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  rw [(QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff]
  have : ((fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ∘ QuotientGroup.mk) =
      fun g => g • x0 := funext (orb_mk x0)
  rw [this]
  exact hc

theorem orb_inj (x0 : X) :
    Function.Injective (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  intro q q' h
  simp only at h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

end Abstract

def LCSCPolish : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] [SecondCountableTopology Y],
    PolishSpace Y

def SecCtblW : Prop := InCtx fun F E _ _ _ _ _ _σ _M _J _a _X0 _hT =>
  SecondCountableTopology (AF F ⊗[F] E)

theorem stabClosed_holds : StabClosed := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hmat : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0) := by
    show Continuous (fun g : HA (AF F) σ J => actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0))
    unfold actTup
    exact continuous_pi fun i => hmat.matrix_mulVec continuous_const
  exact isClosed_eq hcont continuous_const

theorem smul_ratTup_cont (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) {a : ℕ}
    (X0 : Fin a → Fin M → E) :
    Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0) := by
  have hmat : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  show Continuous (fun g : HA (AF F) σ J => actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0))
  unfold actTup
  exact continuous_pi fun i => hmat.matrix_mulVec continuous_const

theorem secCtblG_of (hW : SecCtblW) : SecCtblG := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology (GL (Fin M) (AF F ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have h2 : SecondCountableTopology (HR (AF F) σ J) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact h2

theorem orbEmb_of (hW : SecCtblW) (hP : LCSCPolish) : OrbEmb := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have := secCtblG_of hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : IsClosed ((MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0) : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) :=
    stabClosed_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : PolishSpace (HA (AF F) σ J) := hP _
  have : PolishSpace (HA (AF F) σ J ⧸ MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := hP _
  have : BorelSpace (HA (AF F) σ J ⧸ MulAction.stabilizer (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := CosetSpace.borelSpace
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hcont := orb_cont (G := HA (AF F) σ J) (ratTup (F := F) (AF F) X0)
    (smul_ratTup_cont F E σ M J X0)
  exact ⟨hcont.measurableEmbedding (orb_inj _), hcont⟩

theorem exStab_of_alt (hW : SecCtblW) (hP : LCSCPolish) (hO : OrbTup) (hH : StabUni) (hI : NuInv)
    (hF : NuFin) (hN : NuNeZero) (hU : Unimod) : ExStab :=
  exStab_of (secCtblG_of hW) hO stabClosed_holds hH hI hF hN (orbEmb_of hW hP) hU

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibFour
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology

section Four

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

def DensOn (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) : Prop :=
  ∀ φ : V → ℝ, P φ → ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def IsCcOn (U : Set V) (φ : V → ℝ) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

theorem densAll_iff (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν := by
  constructor
  · intro h φ hφ; exact h φ hφ.1 hφ.2.1 hφ.2.2
  · intro h φ h1 h2 h3; exact h φ ⟨h1, h2, h3⟩

def fourT (μ : Measure V) (f : V → Y) (χ : Y → X → ℂ) (φ : V → ℝ) (S : X) : ℂ :=
  ∫ v, (φ v : ℂ) * χ (f v) S ∂μ

def invT (μ : Measure V) (f : V → Y) (ι : X → Y) (χ : Y → X → ℂ) (ν : Measure X) (φ : V → ℝ)
    (b : X) : ℂ :=
  ∫ S, fourT μ f χ φ S * starRingEnd ℂ (χ (ι b) S) ∂ν

def NSPhase (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (χ : Y → X → ℂ) (ν : Measure X) :
    Prop :=
  ∀ φ, P φ → Integrable (fourT μ f χ φ) ν

def InvDens (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (χ : Y → X → ℂ)
    (ν : Measure X) : Prop :=
  ∀ φ, P φ → Integrable (fourT μ f χ φ) ν →
    Continuous (invT μ f ι χ ν φ) ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), (φ v : ℂ) ∂μ = ∫ b in S, invT μ f ι χ ν φ b ∂ν

def DensApprox (P : (V → ℝ) → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  DensOn P μ f ι ν → DensOn (IsCcOn U) μ f ι ν

end Four

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PosTest
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem integrable_of_isOmT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {ψ : AddChar (AF F) ℂ}
    {a : ℕ} {T : Matrix (Fin a) (Fin a) E} {hT : ∀ i j, σ (T j i) = T i j}
    {νX : Measure (Fin a → Fin M → AF F ⊗[F] E)} (hν : IsOmT F E σ M J ψ T hT νX)
    {Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : IsAdm F E Φ) : Integrable Φ νX := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpf, hprod⟩ := hΦ
  obtain ⟨μinf, h1⟩ := hν.2.1
  have k1 := hν.2.2 μinf h1
  obtain ⟨νinf, h2⟩ := k1.1
  have k2 := k1.2 νinf h2
  obtain ⟨μv, h3⟩ := k2.1
  have k3 := k2.2 μv h3
  obtain ⟨νv, h4⟩ := k3.1
  have k4 := k3.2 νv h4
  obtain ⟨fibInf, h5⟩ := k4.1
  have k5 := k4.2 fibInf h5
  obtain ⟨fibV, h6⟩ := k5.1
  exact (k5.2 fibV h6 d b Φ Φinf Φf Φv hc hcs hpf hprod).1

theorem posTest_of (hN : TestNear) : PosTest := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ _hψ μ hμ νX hν μ' _hμ' hC
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, fun hI0 => ?_⟩
  have hint : Integrable (fun X => (φ X : ℂ)) νX := integrable_of_isOmT hν hadm
  have hintR : Integrable φ νX := by simpa using hint.re
  have hI : ∫ X, φ X ∂νX = 0 := by
    rw [integral_complex_ofReal] at hI0
    exact_mod_cast hI0
  have hae : φ =ᵐ[νX] 0 := (integral_eq_zero_iff_of_nonneg (fun X => hφ0 X) hintR).1 hI
  obtain ⟨hnull, hform⟩ := hC
  classical
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) →
      s y • ratTup (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hf : Measurable (U.indicator (1 : HA (AF F) σ J → ENNReal)) :=
    measurable_one.indicator hUo.measurableSet
  have e := hform _ hf s hs
  have hL : ∫⁻ g, U.indicator (1 : HA (AF F) σ J → ENNReal) g ∂μ = μ U :=
    lintegral_indicator_one hUo.measurableSet
  have : μ.IsHaarMeasure := hμ
  have hpos : 0 < μ U := hUo.measure_pos μ hUne
  have hR : ∫⁻ y, ∫⁻ h', U.indicator (1 : HA (AF F) σ J → ENNReal)
      (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_iff.2 hnull] with y hy0 hyo
    simp only [Pi.zero_apply] at hy0
    have hz : ∀ h' : stabT (AF F) σ J X0,
        U.indicator (1 : HA (AF F) σ J → ENNReal) (s y * (h' : HA (AF F) σ J)) = 0 := by
      intro h'
      refine Set.indicator_apply_eq_zero.2 fun hm => ?_
      exfalso
      have hh : (h' : HA (AF F) σ J) • ratTup (AF F) X0 = ratTup (AF F) X0 := h'.2
      have h0 := hUpos _ hm
      rw [mul_smul, hh, hs y hyo, hy0] at h0
      exact lt_irrefl _ h0
    simp only [hz, lintegral_zero]
  rw [hL, hR] at e
  exact hpos.ne' e

theorem posTest_holds : PosTest := posTest_of testNear_holds

end PI.VolStabW
end
end


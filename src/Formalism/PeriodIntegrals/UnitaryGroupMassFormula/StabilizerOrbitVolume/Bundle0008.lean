import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSt
section
noncomputable section

namespace PI.VolStabSW

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

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExFDStab
section
noncomputable section

namespace PI.VolStabSW

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

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExStabTop
section
noncomputable section

namespace PI.VolStabSW

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

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibFour
section
noncomputable section

namespace PI.VolStabSW

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
    DensAll μ f ι ν U ↔ DensOn (IsCcOn U) μ f ι ν :=
  ⟨fun h φ hφ => h φ hφ.1 hφ.2.1 hφ.2.2, fun h φ h1 h2 h3 => h φ ⟨h1, h2, h3⟩⟩

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

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocExOf
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem multFib_of (h2 : DensFibV) : MultFib := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μv hμv νv hνv fibV hfibV d b Φf Φv hp
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) Φf Φv
    continuous_const (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp
    (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  obtain ⟨ginf, gv, _, hdv, hm, _⟩ := (((h3.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv
  convert hm using 1
  funext v
  exact (h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
    (fibV v) (hfibV v) (Φv v) (gv v) (hp.1 v) (hdv v)).symm

def LatSB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M n : ℕ)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)),
    IsSB ((latV (M := M) (n := n) b v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ))

theorem fibPin_of (h1 : DensFibInf) (h2 : DensFibV) (hL : LatSB) : FibPin := by
  classical
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  refine ⟨fun μinf hμinf νinf hνinf fib1 fib2 hf1 hf2 Φinf hci hsi => ?_, ?_⟩
  · have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
      ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
    have hS := hc a ha2 (gramE σ J X0) hT hdet _ b
      (fun X => Φinf (projInf X) * (fun X => ∏ᶠ v, Lv v (projV v X)) (projFin X)) Φinf _ Lv
      hci (rapidDecay_of_compact b Φinf hci hsi) hp (fun X => rfl)
    obtain ⟨μ, hμ⟩ := hS.1
    obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
    have h3 := (((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf)
    obtain ⟨μv, hμv⟩ := h3.1
    obtain ⟨νv, hνv⟩ := (h3.2 μv hμv).1
    obtain ⟨ginf, gv, hdi, _, _, _⟩ := (h3.2 μv hμv).2 νv hνv
    rw [← h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fib1 hf1
      Φinf ginf hci hsi hdi, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf
      hνinf fib2 hf2 Φinf ginf hci hsi hdi]
  · intro v0 μ0 hμ0 ν0 hν0 fib1 fib2 hf1 hf2 Φ0 hΦ0
    let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
      Function.update Lv v0 Φ0
    have hp : IsPureFin b (fun X => ∏ᶠ v, Φv v (projV v X)) Φv := by
      refine ⟨fun v => ?_, ?_, fun X => rfl⟩
      · by_cases hv : v = v0
        · subst hv; simp only [Φv, Function.update_self]; exact hΦ0
        · simp only [Φv, Function.update_of_ne hv]; exact hL F E _ M a b v
      · filter_upwards [(Set.finite_singleton v0).compl_mem_cofinite] with v hv
        simp only [Φv, Function.update_of_ne (show v ≠ v0 from hv)]
        rfl
    have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
      (fun X => ∏ᶠ v, Φv v (projV v X)) Φv continuous_const
      (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)
    obtain ⟨μ, hμ⟩ := hS.1
    obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
    have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
    obtain ⟨μinf, hμinf⟩ := h3.1
    obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
    have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
    obtain ⟨μv', hμv'⟩ := h4.1
    let μv := Function.update μv' v0 μ0
    have hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v) := by
      intro v
      by_cases hv : v = v0
      · subst hv; simp only [μv, Function.update_self]; exact hμ0
      · simp only [μv, Function.update_of_ne hv]; exact hμv' v
    obtain ⟨νv', hνv'⟩ := (h4.2 μv hμv).1
    let νv := Function.update νv' v0 ν0
    have hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v) := by
      intro v
      by_cases hv : v = v0
      · subst hv; simp only [νv, Function.update_self]; exact hν0
      · simp only [νv, Function.update_of_ne hv]; exact hνv' v
    obtain ⟨ginf, gv, _, hdv, _, _⟩ := (h4.2 μv hμv).2 νv hνv
    have hd0 := hdv v0
    simp only [μv, νv, Φv, Function.update_self] at hd0
    rw [← h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib1 hf1 Φ0 (gv v0)
      hΦ0 hd0, h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib2 hf2 Φ0
      (gv v0) hΦ0 hd0]

theorem locEx_of (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) : LocEx := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
    ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
  have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
    (fun X => ∏ᶠ v, Lv v (projV v X)) Lv continuous_const
    (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
  obtain ⟨μv, hμv⟩ := h4.1
  obtain ⟨νv, hνv⟩ := (h4.2 μv hμv).1
  obtain ⟨fibInf, hfi⟩ := hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
  choose fibV hfv using fun v =>
    hV F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
  exact ⟨μinf, νinf, μv, νv, fibInf, fibV, hμinf, hνinf, hμv, hνv, hfi, hfv⟩

theorem exOmT_of_steps (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) (hU : SdUniq)
    (hDI : DensFibInf) (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of (locEx_of hI hV hL) hU (fibPin_of hDI hDV hL) (multFib_of hDV) hR

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAFTop
section
namespace PI.VolStabSW.TopoAF

theorem afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := fun F _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩

end PI.VolStabSW.TopoAF
end


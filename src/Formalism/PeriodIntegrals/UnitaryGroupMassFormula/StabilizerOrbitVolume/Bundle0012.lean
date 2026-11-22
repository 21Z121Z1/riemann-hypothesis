import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Unfold

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoNuFin
section
noncomputable section

namespace PI.VolStabSW.TopoNuFin

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabSW.PositiveNearLattice
open scoped TensorProduct ENNReal

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem eventually_int_of_compact {C : Set (Af F)} (hC : IsCompact C) :
    ∀ᶠ v in cofinite, ∀ x ∈ C, x v ∈ v.adicCompletionIntegers F := by
  let U : Finset (HeightOneSpectrum (𝓞 F)) → Set (Af F) :=
    fun S => {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    RestrictedProduct.isOpen_forall_imp_mem (TopoAF.isOpen_integers F) (p := fun v => v ∉ S)
  have hcov : C ⊆ ⋃ S, U S := by
    intro x _
    have hx : {v | x v ∉ v.adicCompletionIntegers F}.Finite := x.eventually
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun v hv => ?_⟩
    by_contra h
    exact hv (hx.mem_toFinset.2 h)
  have hdir : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le fun S S' hSS' x hx v hv => hx v fun h => hv (Finset.mem_of_subset hSS' h)
  obtain ⟨S, hS⟩ := hC.elim_directed_cover U hUo hcov hdir
  refine eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
  by_contra h
  exact hv fun x hx => hS hx v h

end Adele

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem zero_mem_latV (a M : ℕ) : (0 : Fin a → Fin M → Fv F v ⊗[F] E) ∈ latV b v := by
  intro x i k
  simp

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

end PI.VolStabSW.TopoNuFin

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Filter Topology
  PI.VolFromSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.TopoNuFin
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
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν K hK
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact nuFin_gen σ J _ hT ψ νX hν K hK

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldMain
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gram_orbit_equiv {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩

end Main

section Of

theorem unfold_of (hW : Witt) (hFT : FinTheta) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) :
    Unfold := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C
    𝓕' h𝓕' φ hφ0 hadm hθ
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ'.IsHaarMeasure := hμ'H
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : μ'.IsInvInvariant :=
    (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : (GamA σ J) =>
        (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J)
      (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hint : Integrable (fun X => (φ X : ℂ)) νX := by
    obtain ⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩ := id hadm
    obtain ⟨⟨μinf, hμinf⟩, k1⟩ := hν.2
    obtain ⟨⟨νinf, hνinf⟩, k2⟩ := k1 μinf hμinf
    obtain ⟨⟨μv, hμv⟩, k3⟩ := k2 νinf hνinf
    obtain ⟨⟨νv, hνv⟩, k4⟩ := k3 μv hμv
    obtain ⟨⟨fI, hfI⟩, k5⟩ := k4 νv hνv
    obtain ⟨⟨fV, hfV⟩, k6⟩ := k5 fI hfI
    exact (k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1
  have hφae : AEMeasurable φ νX := by
    have h2 := Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX
      (fun X => ENNReal.ofReal (φ X)) hφae.ennreal_ofReal hmφ.ennreal_ofReal hμ'C.1 hμ'C.2 𝓕 h𝓕 𝓕' h𝓕'
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by
    intro h
    have hF := hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h
    rw [hθS h]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_finite_support ?_)
    refine (hF.preimage Subtype.val_injective.injOn).subset ?_
    intro X hX
    simp only [Function.mem_support, ne_eq, Real.toNNReal_eq_zero, not_le] at hX
    show (φ _ : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.2 hX.ne'
  have hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by
    refine Measurable.ennreal_tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal
          : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]
  have hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφae.aestronglyMeasurable]
  rw [hI1] at hθ ⊢
  rw [hI2, key]
  rw [key] at hθ
  have hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0 := fun h0 => hθ (by rw [h0]; simp)
  have hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0 := fun h => hL0 (by simp [h])
  have hμ'top : μ' 𝓕' ≠ ⊤ := fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)
  refine ⟨hμ'top, ?_⟩
  rw [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]

end Of

end PI.VolStabSW
end
end


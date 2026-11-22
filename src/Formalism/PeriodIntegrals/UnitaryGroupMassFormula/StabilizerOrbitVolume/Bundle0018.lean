import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.NuInvLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.KapIntegral

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmB
section
noncomputable section

namespace PI.VolStabSW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Boxes

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

def boxS (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (ι → Af F) :=
  {y | ∀ c v, y c v ∈ D c v}

def IsBoxD (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Prop :=
  (∀ c v, IsClopen (D c v) ∧ IsCompact (D c v)) ∧
    ∀ᶠ v in cofinite, ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))

variable (F ι) in

def boxes : Set (Set (ι → Af F)) := {s | ∃ D, IsBoxD D ∧ s = boxS D}

theorem boxS_eq (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) :
    boxS D = Set.pi univ fun c => {x : Af F | ∀ v, x v ∈ D c v} := by
  ext y
  simp [boxS]

theorem isCompact_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsCompact (boxS D) := by
  rw [boxS_eq]
  exact isCompact_univ_pi fun c => isCompact_finite_adele_box (fun v => (hD.1 c v).2)
    (by filter_upwards [hD.2] with v hv using hv c)

theorem isOpen_boxS {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsOpen (boxS D) := by
  rw [boxS_eq]
  exact isOpen_set_pi finite_univ fun c _ => isOpen_finite_adele_box (fun v => (hD.1 c v).1.isOpen)
    (by filter_upwards [hD.2] with v hv using hv c)

theorem boxes_inter {s t : Set (ι → Af F)} (hs : s ∈ boxes F ι) (ht : t ∈ boxes F ι) :
    s ∩ t ∈ boxes F ι := by
  obtain ⟨D, hD, rfl⟩ := hs
  obtain ⟨D', hD', rfl⟩ := ht
  refine ⟨fun c v => D c v ∩ D' c v, ⟨fun c v => ⟨(hD.1 c v).1.inter (hD'.1 c v).1,
    (hD.1 c v).2.inter_right (hD'.1 c v).1.isClosed⟩, ?_⟩, ?_⟩
  · filter_upwards [hD.2, hD'.2] with v h1 h2 c
    rw [h1 c, h2 c, inter_self]
  · ext y
    simp only [boxS, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ c v
      exact ⟨h1 c v, h2 c v⟩
    · intro h
      exact ⟨fun c v => (h c v).1, fun c v => (h c v).2⟩

theorem exists_box_mem (y : ι → Af F) : ∃ D, IsBoxD D ∧ y ∈ boxS D := by
  classical
  let D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun c v =>
    if y c v ∈ v.adicCompletionIntegers F then (v.adicCompletionIntegers F : Set (Fv F v))
    else (Homeomorph.subRight (y c v)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  refine ⟨D, ⟨fun c v => ?_, ?_⟩, fun c v => ?_⟩
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact ⟨isClopen_intV v, isCompact_intV v⟩
    · rw [show D c v = _ from if_neg h]
      exact ⟨isClopen_translate v _, isCompact_translate v _⟩
  · filter_upwards [eventually_all.2 fun c => (y c).eventually] with v hv c
    exact if_pos (hv c)
  · by_cases h : y c v ∈ v.adicCompletionIntegers F
    · rw [show D c v = _ from if_pos h]
      exact h
    · rw [show D c v = _ from if_neg h]
      exact mem_translate v _

theorem boxes_seq : ∃ bs : ℕ → Set (ι → Af F), (∀ n, bs n ∈ boxes F ι) ∧ ⋃ n, bs n = univ := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun s : {s // s ∈ boxes F ι} => (s.1 : Set (ι → Af F)))
    (fun s => by obtain ⟨D, hD, e⟩ := s.2; rw [e]; exact isOpen_boxS hD)
  have hU : ⋃ s ∈ T, (s.1 : Set (ι → Af F)) = univ := by
    rw [he]
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨D, hD, hy⟩ := exists_box_mem y
    exact mem_iUnion.2 ⟨⟨boxS D, D, hD, rfl⟩, hy⟩
  have hne : T.Nonempty := by
    have h0 : (0 : ι → Af F) ∈ ⋃ s ∈ T, (s.1 : Set (ι → Af F)) := by
      rw [hU]
      trivial
    obtain ⟨s, hs, -⟩ := mem_iUnion₂.1 h0
    exact ⟨s, hs⟩
  obtain ⟨g, hg⟩ := hT.exists_eq_range hne
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_⟩
  rw [← hU, hg]
  ext y
  simp

open Classical in

def upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
  fun c' => if c' = c then Function.update (D c) v (D c v ∩ C) else D c'

open Classical in
theorem upd_self (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) :
    upd D c v C c = Function.update (D c) v (D c v ∩ C) := if_pos rfl

open Classical in
theorem upd_ne (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) {c' : ι} (h : c' ≠ c) :
    upd D c v C c' = D c' := if_neg h

open Classical in
theorem mem_upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) (y : ι → Af F) :
    y ∈ boxS (upd D c v C) ↔ y ∈ boxS D ∧ y c v ∈ C := by
  classical
  constructor
  · intro hy
    refine ⟨fun c' w => ?_, ?_⟩
    · have h := hy c' w
      by_cases hc : c' = c
      · subst hc
        rw [upd_self] at h
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self] at h
          exact h.1
        · rw [Function.update_of_ne hw] at h
          exact h
      · rw [upd_ne D c v C hc] at h
        exact h
    · have h := hy c v
      rw [upd_self, Function.update_self] at h
      exact h.2
  · rintro ⟨hy, hC⟩ c' w
    by_cases hc : c' = c
    · subst hc
      rw [upd_self]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        exact ⟨hy _ _, hC⟩
      · rw [Function.update_of_ne hw]
        exact hy _ _
    · rw [upd_ne D c v C hc]
      exact hy _ _

open Classical in
theorem isBoxD_upd {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (c : ι) (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)}
    (hC : IsClopen C ∧ IsCompact C) : IsBoxD (upd D c v C) := by
  classical
  refine ⟨fun c' w => ?_, ?_⟩
  · by_cases hc : c' = c
    · subst hc
      rw [upd_self]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        exact ⟨(hD.1 _ _).1.inter hC.1, (hD.1 _ _).2.inter_right hC.1.isClosed⟩
      · rw [Function.update_of_ne hw]
        exact hD.1 _ _
    · rw [upd_ne D c v C hc]
      exact hD.1 _ _
  · filter_upwards [hD.2, eventually_cofinite_ne v] with w hw hwv c'
    by_cases hc : c' = c
    · subst hc
      rw [upd_self, Function.update_of_ne hwv]
      exact hw _
    · rw [upd_ne D c v C hc]
      exact hw c'

open Classical in
theorem pre_mem (c : ι) (v : HeightOneSpectrum (𝓞 F)) (W : Set (Fv F v)) (hW : IsOpen W) :
    MeasurableSet[generateFrom (boxes F ι)] ((fun y : ι → Af F => y c v) ⁻¹' W) := by
  classical
  let m' : MeasurableSpace (ι → Af F) := generateFrom (boxes F ι)
  obtain ⟨T, hT, hTc, rfl⟩ := open_eq_sUnion v hW
  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  choose Db hDb hbe using hbs
  have e : (fun y : ι → Af F => y c v) ⁻¹' ⋃₀ T = ⋃ C ∈ T, ⋃ n, boxS (upd (Db n) c v C) := by
    ext y
    simp only [mem_preimage, mem_sUnion, mem_iUnion, mem_upd, exists_prop]
    constructor
    · rintro ⟨C, hC, hy⟩
      have hy' : y ∈ ⋃ n, bs n := by
        rw [hbU]
        trivial
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy'
      exact ⟨C, hC, n, by rw [← hbe n]; exact hn, hy⟩
    · rintro ⟨C, hC, n, -, hy⟩
      exact ⟨C, hC, hy⟩
  rw [e]
  exact MeasurableSet.biUnion hT fun C hC => MeasurableSet.iUnion fun n =>
    measurableSet_generateFrom ⟨_, isBoxD_upd (hDb n) c v (hTc C hC), rfl⟩

theorem generateFrom_boxes : generateFrom (boxes F ι) = (MeasurableSpace.pi : MeasurableSpace (ι → Af F)) := by
  classical
  refine le_antisymm (generateFrom_le ?_) ?_
  · rintro _ ⟨D, hD, rfl⟩
    exact (isCompact_boxS hD).isClosed.measurableSet
  · intro s hs
    let Ev : (ι → Af F) → (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v) := fun y c v => y c v
    have hcont : Continuous Ev := continuous_pi fun c => continuous_pi fun v =>
      (RestrictedProduct.continuous_eval v).comp (continuous_apply c)
    have hinj : Function.Injective Ev := fun y y' h =>
      funext fun c => Subtype.ext (funext fun v => congrFun (congrFun h c) v)
    haveI : PolishSpace (ι → Af F) := TopoPolish.polish_of_lcsc _
    have hE := hcont.measurableEmbedding hinj
    have hc : ∀ c v, (borel (Fv F v)).comap (fun y : ι → Af F => y c v) ≤ generateFrom (boxes F ι) := by
      intro c v
      rw [borel, MeasurableSpace.comap_generateFrom]
      refine generateFrom_le ?_
      rintro _ ⟨W, hW, rfl⟩
      exact pre_mem c v W hW
    have hEv : (MeasurableSpace.pi : MeasurableSpace (ι → ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)).comap Ev
        ≤ generateFrom (boxes F ι) := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      exact iSup_le fun c => iSup_le fun v => hc c v
    rw [← hinj.preimage_image s]
    exact hEv _ ⟨_, hE.measurableSet_image.2 hs, rfl⟩

end Boxes

end PI.VolStabSW.DeterminantAdmissible
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PullLocSt
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Matrix
open scoped TensorProduct

def CompG : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ g : HA (AF F) σ J, ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v

def FibInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (h : HA (Ainf F) σ J) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      ∫ X, Φinf (h • X) ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))

def FibInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (h : HA (Fv F v) σ J) (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
      ∫ X, Φv (h • X) ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))

def smulHomeo {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  continuous_toFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)
  continuous_invFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)

theorem pullLoc_of (hC : CompG) (hI : FibInvInf) (hV : FibInvV) : PullLoc := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs
    hpure hprod
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hInf, hv, h1, h2, h3⟩ := hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  let eI := smulHomeo (Ainf F) σ (a := a) J hInf
  let eV := fun v => smulHomeo (Fv F v) σ (a := a) J (hv v)
  refine ⟨fun Y => Φinf (hInf • Y), fun Y => ∏ᶠ v, Φv v (hv v • projV v Y),
    fun v Y => Φv v (hv v • Y), hcΦ.comp eI.continuous, hcs.comp_homeomorph eI, ⟨?_, ?_, fun _ => rfl⟩,
    ?_, ?_, ?_⟩
  · intro v
    exact ⟨(hpure.1 v).1.comp_continuous (eV v).continuous, (hpure.1 v).2.comp_homeomorph (eV v)⟩
  · filter_upwards [hpure.2.1, h3 d b] with v hv1 hv2
    funext Y
    simp only [hv1, Set.indicator, Pi.one_apply]
    by_cases hY : Y ∈ latV b v
    · rw [if_pos ((hv2 Y).2 hY), if_pos hY]
    · rw [if_neg (fun h => hY ((hv2 Y).1 h)), if_neg hY]
  · intro X
    show Φ (g • X) = Φinf (hInf • projInf X) * ∏ᶠ v, Φv v (hv v • projV v (projFin X))
    rw [hprod (g • X), h1 X, hpure.2.2]
    congr 1
    refine finprod_congr fun v => ?_
    rw [h2 v X]
  · exact fun μinf hμinf νinf hνinf fibInf hfi =>
      hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi hInf Φinf
        hcΦ hcs
  · exact fun v μv hμv νv hνv fibV hfv =>
      hV F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμv νv hνv fibV hfv (hv v) (Φv v)
        (hpure.1 v)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RpAbsHolds
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Filter Finset PI.VolStabSW.RPA
open scoped NNReal ENNReal

theorem rpAbs_holds : RPAbs := by
  intro ι _ W _ m _ L hLm hfin hT
  classical
  have hT' : TailH m L := hT
  refine ⟨Measure.sum (kap m L), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    have := kap_ae (m := m) (L := L) hLm S
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx => ?_) this
    intro hgood
    apply hx
    rw [Filter.eventually_cofinite]
    refine (S.finite_toSet).subset (fun i hi => ?_)
    by_contra hiS
    exact hi ((hgood i).2 hiS)
  · intro i C hC hC0
    rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    refine kap_eval_null (m := m) (L := L) (S := S) (A := Cᶜ) hC.compl ?_
    unfold mu
    split_ifs <;> exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hC0.le)
  · intro f hf hcof
    have hfin0 := Filter.eventually_cofinite.1 hcof
    set S0 := hfin0.toFinset with hS0def
    have hS0 : ∀ i, i ∉ S0 → f i = (L i).indicator 1 := fun i hi => by
      by_contra h; exact hi (hfin0.mem_toFinset.2 h)
    set G : (∀ i, W i) → ℂ := fun x => ∏ i ∈ S0, f i (x i) with hG
    have hae : ∀ S : Finset ι, (fun x => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => if S ⊆ S0 then G x else 0 := by
      intro S
      filter_upwards [kap_ae (m := m) (L := L) hLm S] with x hx
      have hsupp : Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ S0) := by
        intro i hi
        by_contra hn
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
        apply hi
        simp only [hS0 i hn.2, Set.indicator_of_mem ((hx i).2 hn.1), Pi.one_apply]
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
      by_cases hsub : S ⊆ S0
      · rw [if_pos hsub, Finset.union_eq_right.2 hsub]
      · rw [if_neg hsub]
        obtain ⟨j, hjS, hj0⟩ := Finset.not_subset.1 hsub
        refine Finset.prod_eq_zero (Finset.mem_union_left _ hjS) ?_
        simp [hS0 j hj0, (hx j).1 hjS]
    have hK : ∀ S ⊆ S0, Integrable G (kap m L S) ∧
        ∫ x, G x ∂kap m L S = (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) :=
      fun S hS => kap_integral hfin hT' hS f hf
    have hIntS : ∀ S, Integrable (fun x => ∏ᶠ i, f i (x i)) (kap m L S) := by
      intro S
      refine Integrable.congr ?_ (hae S).symm
      by_cases hs : S ⊆ S0
      · simp only [hs, if_true]; exact (hK S hs).1
      · simp only [hs, if_false]; exact integrable_zero _ _ _
    have hzero : ∀ S, S ∉ S0.powerset → ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S = 0 ∧
        ∫ x, ‖∏ᶠ i, f i (x i)‖ ∂kap m L S = 0 := by
      intro S hS
      have hs : ¬ S ⊆ S0 := fun h => hS (Finset.mem_powerset.2 h)
      refine ⟨?_, ?_⟩
      · rw [integral_congr_ae (hae S)]; simp [hs]
      · refine (integral_congr_ae ((hae S).fun_comp norm)).trans ?_
        simp [hs, Function.comp_def]
    have hint : Integrable (fun x => ∏ᶠ i, f i (x i)) (Measure.sum (kap m L)) :=
      integrable_sum_measure hIntS (summable_of_ne_finset_zero (s := S0.powerset)
        (fun S hS => (hzero S hS).2))
    refine ⟨hint, ?_⟩
    rw [integral_sum_measure hint, tsum_eq_sum (s := S0.powerset) (fun S hS => (hzero S hS).1)]
    have hsumS : ∑ S ∈ S0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        ∑ S ∈ S0.powerset, (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [integral_congr_ae (hae S)]
      simp only [hs, if_true]
      exact (hK S hs).2
    rw [hsumS, ← Finset.sum_mul]
    have hsplit : ∀ i, ∫ w, f i w ∂(m i) =
        (∫ w, f i w ∂(m i).restrict (L i)ᶜ) + ∫ w, f i w ∂(m i).restrict (L i) := fun i => by
      rw [add_comm]; exact (integral_add_compl (hLm i) (hf i)).symm
    have hprodadd : ∑ S ∈ S0.powerset, ∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i) =
        ∏ i ∈ S0, ∫ w, f i w ∂(m i) := by
      rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_add]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [← Finset.prod_sdiff hs, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_pos hi]
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [hprodadd]
    have h1 : HasProd (fun i => (((({i | i ∉ S0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        (((tl m L S0 : ℝ≥0) : ℝ) : ℂ) := by
      have := (hasProd_ind hT' S0).map
        (((Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom).comp (NNReal.toRealHom.toMonoidHom))
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
      exact this
    have h2 : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
        (∏ i ∈ S0, ∫ w, f i w ∂(m i)) := by
      have : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
          (∏ i ∈ S0, (if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)) :=
        hasProd_prod_of_ne_finset_one (fun b hb => if_neg hb)
      convert this using 1
      exact (Finset.prod_congr rfl (fun i hi => if_pos hi)).symm
    have h3 := h2.mul h1
    convert h3 using 1
    funext i
    by_cases hi : i ∈ S0
    · simp [hi]
    · have hmem : i ∈ ({i | i ∉ S0} : Set ι) := hi
      rw [if_neg hi, one_mul, Set.mulIndicator_of_mem hmem, hS0 i hi,
        integral_indicator (hLm i)]
      simp [am, Measure.real]
      exact (ENNReal.coe_toNNReal_eq_toReal _).symm

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoGram
section
noncomputable section

namespace PI.VolStabSW.TopoGram

open Matrix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : A →+* A) (J G : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (G *ᵥ x) (G *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ G * J * G) x y := by
  rw [hform_eq, hform_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, Formalism.UG.cT, vecMul_transpose]
  congr 1
  funext i
  exact RingHom.map_mulVec σ G x i

end PI.VolStabSW.TopoGram

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Matrix
open scoped TensorProduct

theorem gramPres_holds : GramPres := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g X
  have hg : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR (AF F) J *
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _) =
      JR (AF F) J := g.2
  funext x y
  change hR (AF F) σ J (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR (AF F) σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

end PI.VolStabSW
end
end


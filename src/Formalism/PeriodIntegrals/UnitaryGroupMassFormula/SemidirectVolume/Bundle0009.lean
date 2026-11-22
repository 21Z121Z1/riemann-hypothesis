import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0006

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CoordW
section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

def Ug (D : PG.Dat A n r) : AddSubgroup (n → A) := (LinearMap.ker D.pW).toAddSubgroup

theorem map_eq_of_sum (D : PG.Dat A n r) (H : D.Hyp) (W : AddSubgroup (n → A))
    (hW : ∀ w, w ∈ W ↔ D.IsW w) (g : (n → A) →ₗ[A] (n → A))
    (hgU : ∀ v, g (D.pU v) = D.pU v)
    (hV : ∀ μ : Measure (n → A), μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : n → A) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  have hcU : Continuous D.pU := LinearMap.continuous_on_pi _
  have hcW : Continuous D.pW := LinearMap.continuous_on_pi _
  have hcg : Continuous g := LinearMap.continuous_on_pi _
  have hWmem : ∀ w ∈ W, D.pU w = 0 := fun w hw => PG.Dat.pU_of_isW ((hW w).1 hw)
  have hUmem : ∀ u ∈ Ug D, D.pU u = u := fun u hu => by
    have h0 : D.pW u = 0 := hu
    rw [PG.Dat.pW_apply, sub_eq_zero] at h0
    exact h0.symm
  have hWc : IsClosed (W : Set (n → A)) := by
    have : (W : Set (n → A)) = D.pU ⁻¹' {0} := by
      ext w
      simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun h => hWmem w h, fun h => (hW w).2 ?_⟩
      have := PG.Dat.isW_pW H w
      rwa [PG.Dat.pW_apply, h, sub_zero] at this
    rw [this]
    exact isClosed_singleton.preimage hcU
  have hUc : IsClosed ((Ug D : AddSubgroup (n → A)) : Set (n → A)) := by
    have : ((Ug D : AddSubgroup (n → A)) : Set (n → A)) = D.pW ⁻¹' {0} := by
      ext v
      simp [Ug]
    rw [this]
    exact isClosed_singleton.preimage hcW
  have : LocallyCompactSpace W := hWc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (Ug D) := hUc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hμ
  have : SecondCountableTopology (n → A) := inferInstance
  have : BorelSpace (n → A) := Pi.borelSpace
  have : BorelSpace W := Subtype.borelSpace (· ∈ W)
  have : BorelSpace (Ug D) := Subtype.borelSpace (· ∈ Ug D)
  have : SecondCountableTopology W := TopologicalSpace.secondCountableTopology_induced W (n → A) Subtype.val
  have : SecondCountableTopology (Ug D) :=
    TopologicalSpace.secondCountableTopology_induced (Ug D) (n → A) Subtype.val
  have : BorelSpace (Ug D × W) := Prod.borelSpace
  let Ψ : (Ug D × W) ≃ₜ+ (n → A) :=
    { toFun := fun p => (p.1 : n → A) + (p.2 : n → A)
      invFun := fun v => (⟨D.pU v, by
          show D.pW (D.pU v) = 0
          exact PG.Dat.pW_pU H v⟩, ⟨D.pW v, (hW _).2 (PG.Dat.isW_pW H v)⟩)
      left_inv := by
        rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show D.pU (u + w) = u
          rw [map_add, hUmem u hu, hWmem w hw, add_zero]
        · show D.pW (u + w) = w
          rw [PG.Dat.pW_apply, map_add, hUmem u hu, hWmem w hw, add_zero, add_sub_cancel_left]
      right_inv := fun v => by
        show D.pU v + D.pW v = v
        rw [PG.Dat.pW_apply, add_sub_cancel]
      map_add' := by
        rintro ⟨u, w⟩ ⟨u', w'⟩
        show ((u + u' : Ug D) : n → A) + ((w + w' : W) : n → A) = _ + _
        simp only [AddSubgroup.coe_add]
        abel
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun :=
        (hcU.subtype_mk fun v => (show D.pW (D.pU v) = 0 from PG.Dat.pW_pU H v)).prodMk
          (hcW.subtype_mk fun v => (hW _).2 (PG.Dat.isW_pW H v)) }
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  have hΨsm : Measurable Ψ.symm := Ψ.symm.continuous.measurable
  have hgm : Measurable g := hcg.measurable
  have hfc : Continuous f := by
    refine continuous_induced_rng.2 ?_
    have : (Subtype.val ∘ f : W → n → A) = g ∘ Subtype.val := funext hf
    rw [this]
    exact hcg.comp continuous_subtype_val
  have hfm : Measurable f := hfc.measurable
  let μU : Measure (Ug D) := Measure.addHaar
  have : μU.IsAddHaarMeasure := inferInstance
  have : SigmaFinite μU := inferInstance
  have : SigmaFinite μ := inferInstance
  let ρ : Measure (Ug D × W) := μU.prod μ
  have hcomm : (g ∘ Ψ) = Ψ ∘ Prod.map id f := by
    funext p
    obtain ⟨⟨u, hu⟩, w⟩ := p
    show g (u + (w : n → A)) = u + (f w : n → A)
    have := hgU u
    rw [hUmem u hu] at this
    rw [map_add, this, hf]
  have h1 : (ρ.map (Prod.map id f)).map Ψ = ρ.map Ψ := by
    rw [Measure.map_map hΨm (measurable_id.prodMap hfm), ← hcomm, ← Measure.map_map hgm hΨm]
    exact hV _ inferInstance
  have h2 : ρ.map (Prod.map id f) = ρ := by
    have h3 := congrArg (Measure.map Ψ.symm) h1
    have hid : (Ψ.symm ∘ Ψ) = id := funext Ψ.symm_apply_apply
    rwa [Measure.map_map hΨsm hΨm, Measure.map_map hΨsm hΨm, hid, Measure.map_id,
      Measure.map_id] at h3
  have h4 : μU.prod (μ.map f) = μU.prod μ := by
    have h6 := Measure.map_prod_map μU μ measurable_id hfm
    rw [Measure.map_id] at h6
    rw [h6]
    exact h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : Ug D)
  have hpos : μU K ≠ 0 := (Measure.measure_pos_of_mem_nhds μU hK0).ne'
  have hfin : μU K ≠ ⊤ := hK.measure_lt_top.ne
  ext s _
  have h5 : μU K * (μ.map f) s = μU K * μ s := by
    rw [← Measure.prod_prod, ← Measure.prod_prod, h4]
  exact (ENNReal.mul_right_inj hpos hfin).1 h5

end Gen

theorem wMod_of (hV : Cj.VMod) : WMod := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T _ hP h hh μ hμ
  obtain ⟨t1, t2, t3, t4⟩ := Lc.tensor_adele_topology_holds F E
  have := t1
  have := t2
  have := t3
  have := t4
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  let D := datR (AF F) σ J P T
  have H : D.Hyp := datR_hyp (sigma_invol hCM) hJ hP
  have hS := heisenberg_le_stabilizer (AF F) σ J P hh
  have he : ∀ a, lin (AF F) σ J h (D.e a) = D.e a := fun a => stabilizer_fixes_frame_vector (AF F) σ J P hS a
  have hf : ∀ a, lin (AF F) σ J h (D.f a) = D.f a := fun a => by
    have h0 := hh
    rw [Hsub, mem_stabT] at h0
    have h1 := h0 (Fin.natAdd (r + 1) a)
    rwa [tupH_f] at h1
  have hz : lin (AF F) σ J h D.z = D.z := stabilizer_fixes_normal_vector hS
  refine map_eq_of_sum D H (Wsub (AF F) σ J P) (fun w => Iff.rfl) (lin (AF F) σ J h) ?_
    (fun ν hν => hV F E σ hCM M J hJ h ν hν) (actW hh) (fun w => rfl) μ hμ
  intro v
  rw [PG.Dat.pU_apply, PG.Dat.pX_apply, PG.Dat.pXv_apply, PG.Dat.pz_apply]
  simp only [map_add, map_sum, map_smul, he, hf, hz]

end PI.VolSemiDirect.W.Md
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModOne
section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_hermitian_form_left [IsTopologicalRing (R ⊗[F] E)] (u : Fin M → R ⊗[F] E) :
    Continuous fun w : Fin M → R ⊗[F] E => hR R σ J u w := by
  unfold hR Formalism.UG.hform
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_apply j)

theorem isClosed_Wsub [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {r : ℕ}
    (P : Frame E M r) : IsClosed (Wsub R σ J P : Set (Fin M → R ⊗[F] E)) := by
  have : (Wsub R σ J P : Set (Fin M → R ⊗[F] E)) =
      ((⋂ a, {w | hR R σ J (ratV (F := F) R (P.e a)) w = 0}) ∩
        (⋂ a, {w | hR R σ J (ratV (F := F) R (P.f a)) w = 0})) ∩
        {w | hR R σ J (ratV (F := F) R P.z) w = 0} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [this]
  exact ((isClosed_iInter fun a => isClosed_eq (continuous_hermitian_form_left σ J _) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_hermitian_form_left σ J _) continuous_const)).inter
    (isClosed_eq (continuous_hermitian_form_left σ J _) continuous_const)

theorem continuous_tensor_conj [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous (sigR R σ) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Lc.sigL R σ)

theorem isClosed_Sk [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)]
    (r : ℕ) : IsClosed (Sk R σ r : Set (Fin r → Fin r → R ⊗[F] E)) := by
  have : (Sk R σ r : Set (Fin r → Fin r → R ⊗[F] E)) =
      ⋂ a, ⋂ b, {c | c a b + sigR R σ (c b a) = 0} := by
    ext c
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    rfl
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
  have hc : Continuous fun c : Fin r → Fin r → R ⊗[F] E => c a b + sigR R σ (c b a) :=
    (continuous_apply_apply a b).add ((continuous_tensor_conj σ).comp (continuous_apply_apply b a))
  exact isClosed_eq hc continuous_const

end Gen

theorem modOne_of (hC : HeisenbergCoordinates) (hW : WMod) : Cj.ModOne := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hP h hh
  obtain ⟨Φ, hmul, hconj⟩ := hC F E σ hCM M J hJ r P T hr hP
  obtain ⟨htr, ht2, hlc, hsc⟩ := Lc.tensor_adele_topology_holds F E
  obtain ⟨hXlc, hXsc, hXt2, hXtg⟩ := Lc.locally_compact_adelic_unitary F E σ hCM M J hJ
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hAFtr : IsTopologicalRing (AF F) := inferInstance
  have : LocallyCompactSpace (Wsub (AF F) σ J P) :=
    (isClosed_Wsub σ J P).locallyCompactSpace
  have : LocallyCompactSpace (Sk (AF F) σ r) := (isClosed_Sk σ r).locallyCompactSpace
  have scV : SecondCountableTopology (Fin M → AF F ⊗[F] E) := inferInstance
  have scW : SecondCountableTopology (Wsub (AF F) σ J P) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have scK : SecondCountableTopology (Fin r → Fin r → AF F ⊗[F] E) := inferInstance
  have scS : SecondCountableTopology (Sk (AF F) σ r) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have scP : SecondCountableTopology (Fin r → Wsub (AF F) σ J P) := inferInstance
  have scE : SecondCountableTopologyEither (Fin r → Wsub (AF F) σ J P) (Sk (AF F) σ r) :=
    inferInstance
  have bV : BorelSpace (Fin M → AF F ⊗[F] E) := Pi.borelSpace
  have bW : BorelSpace (Wsub (AF F) σ J P) := Subtype.borelSpace _
  have bK : BorelSpace (Fin r → Fin r → AF F ⊗[F] E) := Pi.borelSpace
  have bS : BorelSpace (Sk (AF F) σ r) := Subtype.borelSpace _
  have bP : BorelSpace (Fin r → Wsub (AF F) σ J P) := Pi.borelSpace
  have bX : BorelSpace ((Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r) := Prod.borelSpace
  have bN : BorelSpace (FrameUnipotentSubgroup (AF F) σ J P) := Subtype.borelSpace _
  obtain ⟨νW, hνW⟩ : ∃ ν : Measure (Wsub (AF F) σ J P), ν.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨νS, hνS⟩ : ∃ ν : Measure (Sk (AF F) σ r), ν.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  have cW : SigmaCompactSpace (Wsub (AF F) σ J P) := inferInstance
  have cS : SigmaCompactSpace (Sk (AF F) σ r) := inferInstance
  have sW : SigmaFinite νW := inferInstance
  have sS : SigmaFinite νS := inferInstance
  let νP : Measure (Fin r → Wsub (AF F) σ J P) := Measure.pi fun _ => νW
  have hνP : νP.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have sP : SigmaFinite νP := Measure.pi.sigmaFinite _
  let ν : Measure ((Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r) := νP.prod νS
  have hν : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hΦsm : Measurable Φ.symm := Φ.symm.continuous.measurable

  have key : ∀ g : FrameUnipotentSubgroup (AF F) σ J P, MeasurePreserving (fun x => Φ (g * Φ.symm x)) ν ν := by
    intro g
    have hcont : Continuous fun p : (Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r =>
        (Φ (g * Φ.symm (p.1, 0))).2 + p.2 :=
      (continuous_snd.comp (Φ.continuous.comp (continuous_const.mul
        (Φ.symm.continuous.comp (continuous_fst.prodMk continuous_const))))).add continuous_snd
    have hsk := MeasurePreserving.skew_product (μa := νP) (μb := νP) (μc := νS) (μd := νS)
      (f := fun w => (Φ g).1 + w) (g := fun w c => (Φ (g * Φ.symm (w, 0))).2 + c)
      (measurePreserving_add_left νP (Φ g).1) hcont.measurable
      (ae_of_all _ fun w => map_add_left_eq_self νS _)
    convert hsk using 1
    funext p
    obtain ⟨w, c⟩ := p
    have h1 := (hmul g (Φ.symm (w, c))).1
    have h2 := (hmul g (Φ.symm (w, c))).2
    have h3 := (hmul g (Φ.symm (w, 0))).2
    simp only [Homeomorph.apply_symm_apply] at h1 h2 h3
    refine Prod.ext (funext fun a => Subtype.ext ?_) (Subtype.ext ?_)
    · have := congrFun h1 a
      simpa using this
    · show ((Φ (g * Φ.symm (w, c))).2 : Fin r → Fin r → AF F ⊗[F] E) =
        (((Φ (g * Φ.symm (w, 0))).2 + c : Sk (AF F) σ r) : Fin r → Fin r → AF F ⊗[F] E)
      rw [h2, AddSubgroup.coe_add, h3]
      simp only [AddSubgroup.coe_zero, add_zero]
      abel
  let μ : Measure (FrameUnipotentSubgroup (AF F) σ J P) := ν.map Φ.symm
  have hinvN : ∀ g : FrameUnipotentSubgroup (AF F) σ J P, μ.map (g * ·) = μ := by
    intro g
    have hcomp : (fun n => g * n) ∘ Φ.symm = Φ.symm ∘ (fun x => Φ (g * Φ.symm x)) := by
      funext x; simp
    rw [Measure.map_map (continuous_const_mul g).measurable hΦsm, hcomp,
      ← Measure.map_map hΦsm (key g).measurable, (key g).map_eq]
  have i1 : μ.IsMulLeftInvariant := ⟨hinvN⟩
  have i2 : IsFiniteMeasureOnCompacts μ := Measure.IsFiniteMeasureOnCompacts.map ν Φ.symm
  have i3 : μ.IsOpenPosMeasure := Φ.symm.continuous.isOpenPosMeasure_map Φ.symm.surjective
  have hμ : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := i2, toIsMulLeftInvariant := i1, toIsOpenPosMeasure := i3 }
  refine ⟨μ, hμ, fun f hf => ?_⟩

  let c : FrameUnipotentSubgroup (AF F) σ J P → FrameUnipotentSubgroup (AF F) σ J P := fun n =>
    ⟨h * (n : HA (AF F) σ J) * h⁻¹, norm_gen (AF F) σ J P h hh n n.2⟩
  have hc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hA : MeasurePreserving (fun x => Φ (c (Φ.symm x))) ν ν := by
    have hact : MeasurePreserving (actW hh) νW νW :=
      ⟨(((lin (AF F) σ J h).continuous_on_pi.comp continuous_subtype_val).subtype_mk _).measurable,
        hW F E σ hCM M J hJ r P T hr hP h hh νW inferInstance⟩
    have hpi : MeasurePreserving (fun (w : Fin r → Wsub (AF F) σ J P) a => actW hh (w a)) νP νP :=
      measurePreserving_pi _ _ fun _ => hact
    have hsk := hpi.prod (MeasurePreserving.id νS)
    convert hsk using 1
    funext x
    obtain ⟨h1, h2⟩ := hconj h hh (Φ.symm x) (c (Φ.symm x)) rfl
    simp only [Homeomorph.apply_symm_apply] at h1 h2
    exact Prod.ext (funext fun a => Subtype.ext (h1 a)) h2
  have hmapc : μ.map c = μ := by
    have hcomp : c ∘ Φ.symm = Φ.symm ∘ (fun x => Φ (c (Φ.symm x))) := by
      funext x; simp
    rw [Measure.map_map hc.measurable hΦsm, hcomp, ← Measure.map_map hΦsm hA.measurable,
      hA.map_eq]
  have hfm : Measurable fun n : FrameUnipotentSubgroup (AF F) σ J P => f (n : HA (AF F) σ J) :=
    hf.comp measurable_subtype_coe
  calc ∫⁻ n, f (h * (n : HA (AF F) σ J) * h⁻¹) ∂μ
      = ∫⁻ n, (fun m : FrameUnipotentSubgroup (AF F) σ J P => f (m : HA (AF F) σ J)) (c n) ∂μ := rfl
    _ = ∫⁻ m, f (m : HA (AF F) σ J) ∂(μ.map c) := (lintegral_map hfm hc.measurable).symm
    _ = ∫⁻ m, f (m : HA (AF F) σ J) ∂μ := by rw [hmapc]

end PI.VolSemiDirect.W.Md
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
section
namespace PI.VolSemiDirect.W.Cj

theorem orthogonal_invariance_of_stable_rank_one (h1 : AdeleStableRankOne) : OrthInv :=
  orthInv_of h1 gl_generated_transvections_diag transvection_preserves_haar

theorem unipotent_modulus_of_stable_rank_one (h1 : AdeleStableRankOne) : VMod :=
  vMod_of (orthogonal_invariance_of_stable_rank_one h1) trace_basis_holds trace_gram_nondegenerate

theorem unipotent_modulus_holds : VMod := unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles

end PI.VolSemiDirect.W.Cj
end


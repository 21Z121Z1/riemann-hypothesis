import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HenselCountHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0015

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSS
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

theorem isReduced_tens_field (F E C : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Field C] [Algebra F C] : IsReduced (C ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[F] E)

theorem semisimpleTens_holds : SemisimpleTens := by
  intro F E _ _ _ _ _ σ _
  classical
  have : IsArtinianRing (Ainf F) :=
    inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))
  have : IsArtinianRing (Ainf F ⊗[F] E) := IsArtinianRing.of_finite (Ainf F) (Ainf F ⊗[F] E)
  let e1 : Ainf F ⊗[F] E ≃ₐ[F] E ⊗[F] Ainf F := Algebra.TensorProduct.comm F (Ainf F) E
  let e2 : E ⊗[F] ((v : InfinitePlace F) → v.Completion) ≃ₐ[F]
      ((v : InfinitePlace F) → E ⊗[F] v.Completion) :=
    Algebra.TensorProduct.piRight F F E (fun v : InfinitePlace F => v.Completion)
  have : ∀ v : InfinitePlace F, IsReduced (E ⊗[F] v.Completion) := fun v =>
    have := isReduced_tens_field F E v.Completion
    isReduced_of_injective (Algebra.TensorProduct.comm F E v.Completion).toRingHom
      (Algebra.TensorProduct.comm F E v.Completion).injective
  have : IsReduced (Ainf F ⊗[F] E) :=
    isReduced_of_injective ((e2.toRingHom).comp e1.toRingHom) (e2.injective.comp e1.injective)
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem densInf_of_tensR (h : TensR) : DensInf := densInf_of_ss h semisimpleTens_holds

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSec
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem exists_leftInv_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let f : (Fin a → K) →ₗ[K] (Fin M → K) := ∑ i, (LinearMap.proj i).smulRight (Z i)
  have hf_apply : ∀ c, f c = ∑ i, c i • Z i := by
    intro c
    simp [f, LinearMap.sum_apply]
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [hf_apply] at hc
    funext i
    exact Fintype.linearIndependent_iff.1 hZ c hc i
  obtain ⟨g, hg⟩ : ∃ g : (Fin M → K) →ₗ[K] (Fin a → K), g ∘ₗ f = LinearMap.id := by
    first
    | exact IsSemisimpleModule.extension_property f hf LinearMap.id
    | (obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.range f)
       exact ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
         Submodule.linearProjOfIsCompl _ _ hC, by
           ext c : 1
           simp [Submodule.linearProjOfIsCompl_apply_left]⟩)
  refine ⟨fun k i' => g (fun j => if k = j then 1 else 0) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (fun j => if k = j then (1 : K) else 0) := pi_eq_sum_univ (Z i)
  have key : g (Z i) = fun j => if i = j then 1 else 0 := by
    have hZf : Z i = f (fun j => if i = j then 1 else 0) := by
      rw [hf_apply]
      simp
    rw [hZf, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have h2 := congrFun key i'
  rw [hZi, map_sum] at h2
  simpa [Finset.sum_apply, map_smul] using h2

theorem secGram_holds : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  classical
  have hs2 : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσ]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  have hsF : ∀ c : F, sigR R σ (algebraMap F (R ⊗[F] E) c) = algebraMap F (R ⊗[F] E) c := by
    intro c
    simp [sigR]
  have hJR : ∀ k l, sigR R σ (JR (F := F) R J l k) = JR (F := F) R J k l := by
    intro k l
    simp [JR, inclR, sigR, hJ]
  have hJunit : IsUnit (JR (F := F) R J).det := by
    have hd : (JR (F := F) R J).det = inclR (F := F) R J.det := (RingHom.map_det (inclR (F := F) R) J).symm
    rw [hd]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  set s := sigR R σ with hs
  let w : Fin a → Fin M → R ⊗[F] E := fun i l => ∑ k, s (x i k) * JR (F := F) R J k l
  have hw : LinearIndependent (R ⊗[F] E) w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    set v : Fin M → R ⊗[F] E := fun k => ∑ i, c i * s (x i k) with hv
    have hvJ : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext l
      have hl := congrFun hc l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, Finset.mul_sum] at hl
      simp only [Matrix.vecMul, dotProduct, hv, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      simpa [mul_assoc] using hl
    have hv0 : v = 0 := by
      have h3 := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hvJ
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJunit] using h3
    have hx0 : ∑ i, s (c i) • x i = 0 := by
      funext k
      have h4 := congrArg s (congrFun hv0 k)
      simp only [hv, map_sum, map_mul, hs2, map_zero, Pi.zero_apply] at h4
      simpa [Finset.sum_apply, smul_eq_mul] using h4
    have h5 := Fintype.linearIndependent_iff.1 hx _ hx0 i
    rw [← hs2 (c i), h5, map_zero]
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep w hw
  refine ⟨q, fun S hS => ?_⟩
  have hS' : ∀ i j, s (S j i) = S i j := hS
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  set Y : Fin a → Fin M → R ⊗[F] E := fun j k => ∑ i', c * S i' j * q k i' with hY
  have hsum3 : ∀ f : Fin M → Fin M → Fin a → R ⊗[F] E,
      ∑ k, ∑ l, ∑ i', f k l i' = ∑ i', ∑ l, ∑ k, f k l i' := by
    intro f
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
  have h1 : ∀ i j, hR R σ J (x i) (Y j) = c * S i j := by
    intro i j
    have e1 : hR R σ J (x i) (Y j) =
        ∑ k, ∑ l, ∑ i', s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i') := by
      simp only [hR, Formalism.UG.hform, hY, Finset.mul_sum, ← hs]
    have e2 : ∑ i', c * S i' j * ∑ l, w i l * q l i' =
        ∑ i', ∑ l, ∑ k, s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i') := by
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e1, hsum3 (fun k l i' => s (x i k) * JR (F := F) R J k l * (c * S i' j * q l i')), ← e2]
    simp [hq]
  have h2 : ∀ i j, hR R σ J (Y i) (x j) = s (hR R σ J (x j) (Y i)) := by
    intro i j
    simp only [hR, Formalism.UG.hform, ← hs, map_sum, map_mul, hs2, hJR]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsc : s c = c := hsF _
  have hcc : c + c = 1 := by
    rw [hc, ← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  unfold gramB
  funext i j
  show hR R σ J (x i) (Y j) + hR R σ J (Y i) (x j) = S i j
  rw [h2, h1, h1, map_mul, hsc, hS', ← add_mul, hcc, one_mul]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVTop
section
namespace PI.VolStabSW

theorem densV_of_gram (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF

end PI.VolStabSW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdm
section
noncomputable section

namespace PI.VolStabSW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabSW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

theorem detAdm_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH F E a M
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU

end PI.VolStabSW.DeterminantAdmissible

namespace PI.VolStabSW

theorem detAdm_holds : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolC
section
noncomputable section

namespace PI.VolStabSW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem crd_sigR (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) (l : Fin d) :
    crd b (Fv F v) (sigR (Fv F v) σ z) l =
      ∑ k, crd b (Fv F v) z k * algebraMap F (Fv F v) (b.repr (σ (b k)) l) := by
  set B := Algebra.TensorProduct.basis (Fv F v) b with hBdef
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hs : ∀ k, sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) = (1 : Fv F v) ⊗ₜ[F] σ (b k) := by
    intro k
    simp [sigR]
  conv_lhs => rw [← B.sum_repr z]
  rw [map_sum]
  simp only [sigR_smul, hB, hs, crd, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply, one_smul]
  rfl

theorem ev_sig (σ : E →ₐ[F] E) :
    ∀ᶠ v in cofinite, ∀ z ∈ latA v b, sigR (Fv F v) σ z ∈ latA v b := by
  filter_upwards [ev_int_all (fun q : Fin d × Fin d => b.repr (σ (b q.1)) q.2)] with v h
  intro z hz l
  rw [crd_sigR]
  exact sum_mem fun k _ => mul_mem (hz k) (h (k, l))

theorem mem_hermO_iff (σ : E →ₐ[F] E) {a : ℕ} (T : HermR (Fv F v) σ a) :
    T ∈ hermO b v σ a ↔
      (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) ∈ latV (M := a) (n := a) b v := by
  constructor
  · intro h p i k
    exact h i p k
  · intro h i j k
    exact h j i k

theorem ev_dualH [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    ∀ᶠ v in cofinite, {T : HermR (Fv F v) σ a | ∀ S ∈ hermO b v σ a,
      pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} = hermO b v σ a := by
  filter_upwards [ev_dual b σ hσ (1 : Matrix (Fin a) (Fin a) E) (by simp) (a := a), ev_sig b σ,
    ev_int (1 / 2 : F)] with v hD hS hh
  ext T
  constructor
  · intro hT
    rw [Set.mem_setOf_eq] at hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD]
    intro X hX
    rw [← pairHerm_iota v σ hσ X T]
    apply hT
    intro i j k
    have h1 : X i j ∈ latA v b := fun k => hX i j k
    have h2 : X j i ∈ latA v b := fun k => hX j i k
    exact (add_mem (hS _ h1) h2) k
  · intro hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD] at hT
    rw [Set.mem_setOf_eq]
    intro S hS
    set c : Fv F v := algebraMap F (Fv F v) (1 / 2) with hc
    let X : Fin a → Fin a → Fv F v ⊗[F] E := fun p q =>
      c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p
    have hX : X ∈ latV (M := a) (n := a) b v := by
      intro p q k
      have := crd_smul v b c ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k
      simp only [crd] at this
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
        (c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k ∈ _
      rw [this]
      exact mul_mem hh (hS q p k)
    have hcc : c + c = 1 := by
      rw [hc, ← map_add]
      norm_num
    have hSX : S = ⟨iota v σ X, iota_mem v σ hσ X⟩ := by
      apply Subtype.ext
      funext p q
      simp only [iota, X, sigR_smul]
      rw [S.2 p q, ← add_smul, hcc, one_smul]
    rw [hSX, pairHerm_iota v σ hσ X T]
    exact hT X hX

theorem isCompact_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) ∧
      IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  have hcl := (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
  have e : (hermO b v σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹'
      ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latA v b : Set (Fv F v ⊗[F] E))) :
        Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) := by
    ext S
    exact ⟨fun h p _ q _ k => h p q k, fun h p q k => h p (Set.mem_univ _) q (Set.mem_univ _) k⟩
  have hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latA v b
  have hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_latA v b
  rw [e]
  exact ⟨hcl.isCompact_preimage hKc, hKo.preimage continuous_subtype_val⟩

theorem smul_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ S ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
      ∃ S' ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
        ∀ T, pairHerm (Fv F v) σ a S' T = s * pairHerm (Fv F v) σ a S T := by
  intro s hs S hS
  have hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a := by
    intro p q
    simp only [Matrix.smul_apply, sigR_smul, S.2 p q]
  refine ⟨⟨_, hmem⟩, ?_, fun T => ?_⟩
  · intro p q k
    have := crd_smul v b s ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k
    simp only [crd] at this
    show (Algebra.TensorProduct.basis (Fv F v) b).repr
      (s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k ∈ _
    rw [this]
    exact mul_mem hs (hS p q k)
  · simp only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
      smul_eq_mul]
    ring

theorem smul_latV (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ latV (M := M) (n := a) b v,
      ∃ x' ∈ latV (M := M) (n := a) b v, ∀ y, BR (Fv F v) σ J x' y = s * BR (Fv F v) σ J x y := by
  intro s hs x hx
  refine ⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩
  intro p i l
  have := crd_smul v b s (x p i) l
  simp only [crd] at this
  rw [Pi.smul_apply, Pi.smul_apply, this]
  exact mul_mem hs (hx p i l)

end VolAAW

end PI.VolStabSW
end
end


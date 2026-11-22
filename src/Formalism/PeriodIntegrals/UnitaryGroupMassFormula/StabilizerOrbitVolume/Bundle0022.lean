import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExistsUnifFv

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfTR
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := exists_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := exists_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

theorem exists_coord_sub {X : Type} [AddCommGroup X] [TopologicalSpace X] {N : ℕ}
    (e : X ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (H : AddSubgroup X)
    (hH : IsClosed (H : Set X)) (hdiv : ∀ n : ℕ, 0 < n → ∀ x ∈ H, ∃ y ∈ H, n • y = x) :
    ∃ (m : ℕ) (eH : H ≃ₜ (Fin m → ℝ)), ∀ x y, eH (x + y) = eH x + eH y := by
  let eA : X →+ (Fin N → ℝ) := AddMonoidHom.mk' e he
  have hq : ∀ (q : ℚ), ∀ x ∈ H, (q : ℝ) • e x ∈ e '' (H : Set X) := by
    intro q x hx
    obtain ⟨y, hy, hyx⟩ := hdiv q.den q.den_pos x hx
    refine ⟨q.num • y, H.zsmul_mem hy _, ?_⟩
    have e1 : e (q.num • y) = (q.num : ℝ) • e y := by
      rw [show e (q.num • y) = eA (q.num • y) from rfl, map_zsmul, Int.cast_smul_eq_zsmul]; rfl
    have e2 : e x = (q.den : ℝ) • e y := by
      rw [← hyx, show e (q.den • y) = eA (q.den • y) from rfl, map_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    rw [e1, e2, smul_smul]
    congr 1
    exact_mod_cast (Rat.mul_den_eq_num q).symm
  have hcl : IsClosed (e '' (H : Set X)) := e.isClosedMap _ hH
  let W : Submodule ℝ (Fin N → ℝ) :=
    { carrier := e '' (H : Set X)
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, H.add_mem hx hy, he x y⟩
      zero_mem' := ⟨0, H.zero_mem, map_zero eA⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        have hc : IsClosed {s : ℝ | s • e x ∈ e '' (H : Set X)} :=
          hcl.preimage (continuous_id.smul continuous_const)
        have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {s : ℝ | s • e x ∈ e '' (H : Set X)} := by
          rintro _ ⟨q, rfl⟩; exact hq q x hx
        have := (hc.closure_subset_iff.2 hsub) (Rat.denseRange_cast (𝕜 := ℝ) r)
        exact this }
  let e0 : H ≃ₜ W := e.subtype (p := fun x => x ∈ H) (q := fun y => y ∈ W) (fun x => by
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hx'e⟩; rw [← e.injective hx'e]; exact hx')
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := W)
    (F := Fin (Module.finrank ℝ W) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e0.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e0 (x + y)) = L (e0 x) + L (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from Subtype.ext (he x y), map_add]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVDx
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem gramR_add_sub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J (x + W) - gramR R σ J x - gramR R σ J W = gramB R σ J x W := by
  funext i j
  simp [gramR, gramB, hR, Formalism.UG.hform, Matrix.sub_apply, Matrix.add_apply, map_add, add_mul, mul_add,
    Finset.sum_add_distrib] <;> ring

theorem gramB_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W W' : Fin n → Fin M → R ⊗[F] E) :
    gramB R σ J x (W + W') = gramB R σ J x W + gramB R σ J x W' := by
  funext i j
  simp [gramB, hR, Formalism.UG.hform, Matrix.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] <;> ring

theorem dxOpen_of (h : SecGram) : DxOpen := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet a _h1 _h2 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := isReduced_tens_field F E (Fv F v)
  have hss : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  obtain ⟨q, hq⟩ := h F E σ hσ M J hJ hdet (Fv F v) hss a x hx
  set T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun S j k => ∑ i', (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * S i' j) * q k i' with hT
  have hTc : Continuous T := by
    refine continuous_pi fun j => continuous_pi fun k => continuous_finsetSum _ fun i' _ => ?_
    exact (continuous_const.mul (continuous_id.matrix_elem i' j)).mul continuous_const
  have hT0 : T 0 = 0 := by
    funext j k
    simp [hT]
  set L := latSub b v a M with hL
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  set Dx : (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a := fun W =>
    gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W
    with hDx
  have hDB : ∀ W, (Dx W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J x W := by
    intro W
    rw [← gramR_add_sub]
    rfl
  have hDadd : ∀ W W', Dx (W + W') = Dx W + Dx W' := by
    intro W W'
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hDB, hDB, hDB, gramB_add_right]
  have hDT : ∀ S : HermR (Fv F v) σ a, Dx (T S) = S := by
    intro S
    apply Subtype.ext
    rw [hDB]
    exact hq S.1 S.2
  show IsOpen (Dx '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨l, hl, rfl⟩
  have hU : IsOpen {S : HermR (Fv F v) σ a | T ((S - Dx l : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L} :=
    hLo.preimage (hTc.comp (continuous_subtype_val.comp (continuous_id.sub continuous_const)))
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show T ((Dx l - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L
    rw [sub_self, AddSubgroup.coe_zero, hT0]
    exact L.zero_mem
  · intro S hS
    refine ⟨l + T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)),
      L.add_mem hl hS, ?_⟩
    rw [hDadd, hDT]
    abel

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVol
section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW PositiveNearLattice SdDualW VolAAW

theorem volAA_of (hC : CondAA) : VolAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  filter_upwards [hC F ψ hψ, ev_dual b σ hσ J hJ.2 (a := a), ev_dualH b σ hσ a] with v hCv hDW hDH
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  refine ⟨fun μv hμ => ?_, fun νv hν => ?_⟩
  · have hA := ann_eq v (psiV F ψ v) (BR (Fv F v) σ J (n := a)) (latV (M := M) (n := a) b v) hCv
      (smul_latV b v σ J) hDW
    exact vol_one_of_ann hμ (fun X T Y => by rw [BR_add, psiV_add]) (SdDualW.latSub v b a M)
      (isCompact_latV b v a M) (isClopen_latV b v a M).isOpen hA
  · have hA := ann_eq v (psiV F ψ v) (pairHerm (Fv F v) σ a)
      (hermO b v σ a : Set (HermR (Fv F v) σ a)) hCv (smul_hermO b v σ a) hDH
    exact vol_one_of_ann hν (fun S T U => by rw [pairHerm_add, psiV_add]) (hermO b v σ a)
      (isCompact_hermO b v σ a).1 (isCompact_hermO b v σ a).2 hA

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def unifV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fv F v :=
  ((v.valuation_exists_uniformizer F).choose : Fv F v)

theorem unifV_val {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := by
  rw [unifV, v.valuedAdicCompletion_eq_valuation', (v.valuation_exists_uniformizer F).choose_spec]

theorem unifV_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    unifV v ≠ 0 ∧ Tendsto (fun k : ℕ => unifV v ^ k) atTop (𝓝 0) ∧
      unifV v ∈ v.adicCompletionIntegers F := by
  have hv := unifV_val v
  have h1 : Valued.v (unifV v) < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖unifV v‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

def lamF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) (n : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) :=
  smulSub (unifV v ^ (n + 1)) (latSub b v a M)

def hF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    (n : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  smulSub (unifV v ^ (n + 1)) (hermO b v σ a)

def LatFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (a M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)),
    (∀ n, IsOpen (lamF b v a M n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
    (∀ n, IsCompact (lamF b v a M n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
    Antitone (lamF b v a M) ∧ lamF b v a M 0 ≤ latSub b v a M ∧
    (∀ n, IsOpen (hF b v σ a n : Set (HermR (Fv F v) σ a))) ∧
    (∀ n, IsCompact (hF b v σ a n : Set (HermR (Fv F v) σ a))) ∧
    (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (hF b v σ a n : Set (HermR (Fv F v) σ a)) ⊆ N')

def HensAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1 F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ y ∈ latSub b v a M, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ hF b v σ a 0 →
      ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
        (∀ n, (lamF b v a M n).map D = hF b v σ a n) ∧ ∀ n, ∀ Z ∈ lamF b v a M 0,
          ∀ W ∈ lamF b v a M n, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈ hF b v σ a (n + 1)

def IdxAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1 F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure →
      ν.IsAddHaarMeasure →
      μ (latV b v) = (Nat.card (𝓞 F ⧸ v.asIdeal) : ENNReal) ^ (2 * M * a) * μ (lamF b v a M 0) ∧
      ν (hermO b v σ a) = (Nat.card (𝓞 F ⧸ v.asIdeal) : ENNReal) ^ (a ^ 2) * ν (hF b v σ a 0)

def CntAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1 F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure →
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
        Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
        μ (latV b v ∩ gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ hF b v σ a 0}) =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
            μ (lamF b v a M 0)

theorem resAA_of (hV : VolAA) (hL : LatFacts) (hH : HensAA) (hI : IdxAA) (hC : CntAA) :
    ResAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  filter_upwards [hV F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b,
    hH F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hI F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hC F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b] with v hv hh hi hc
  intro μv hμ νv hν
  have := hμ.1
  have := hν.1
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hL F E σ d b a M v
  refine ⟨latSub b v a M, lamF b v a M, hF b v σ a, rfl,
    (PositiveNearLattice.isClopen_latV b v a M).isOpen, PositiveNearLattice.isCompact_latV b v a M, l4, l1, l2, l3,
    l5, l6, l7, hh, ?_⟩
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, hcard, hcnt⟩ :=
    hc μv hμ.1
  refine ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, ?_, ?_⟩
  · rw [hcard]; rfl
  obtain ⟨e1, e2⟩ := hi μv νv hμ.1 hν.1
  rw [hv.1 μv hμ, ← hcard] at e1
  rw [hv.2 νv hν, ← hcard] at e2
  show (μv (latV b v ∩ _) / νv _).toReal = _
  rw [hcnt, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have f1 := congrArg ENNReal.toReal e1
  have f2 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_one] at f1 f2
  have hq : (0 : ℝ) < Nat.card k := by exact_mod_cast Nat.card_pos
  have hle : a ^ 2 ≤ 2 * M * a := by nlinarith
  have hp : (Nat.card k : ℝ) ^ (2 * M * a) = (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
      (Nat.card k : ℝ) ^ (a ^ 2) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hA : (0 : ℝ) < (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) := pow_pos hq _
  have hB : (0 : ℝ) < (Nat.card k : ℝ) ^ (a ^ 2) := pow_pos hq _
  rw [hp] at f1
  have hn : (νv (hF b v σ a 0)).toReal = 1 / (Nat.card k : ℝ) ^ (a ^ 2) := by
    field_simp; linarith
  have hm : (μv (lamF b v a M 0)).toReal =
      1 / ((Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) * (Nat.card k : ℝ) ^ (a ^ 2)) := by
    field_simp; linarith
  rw [hm, hn]
  field_simp

end PI.VolStabSW
end
end


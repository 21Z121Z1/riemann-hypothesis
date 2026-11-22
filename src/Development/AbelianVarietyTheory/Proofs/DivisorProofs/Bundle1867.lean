import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
section
open Filter Topology
open scoped SchwartzMap Pointwise

namespace GlobalTheory
namespace FrechetOpenMapping

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]

theorem tendsto_inv_nat_complex : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)

theorem closure_image_mem_nhds [BaireSpace F] (T : E →L[ℂ] F) (hT : Function.Surjective T)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) : closure (T '' U) ∈ 𝓝 (0 : F) := by
  obtain ⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (0 : E), ∀ a ∈ W, ∀ b ∈ W, a - b ∈ U := by
    have : Tendsto (fun p : E × E => p.1 - p.2) (𝓝 (0, 0)) (𝓝 0) := by
      exact (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 (this hU)
    exact ⟨A ∩ B, inter_mem hA hB, fun a ha b hb => hAB (Set.mk_mem_prod ha.1 hb.2)⟩
  set A := closure (T '' W) with hAdef
  have hcov : ⋃ n : ℕ, ((n + 1 : ℕ) : ℂ) • A = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hT y
    have ht : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹ • x) atTop (𝓝 0) := by
      simpa using tendsto_inv_nat_complex.smul_const x
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ht hW)
    have hmem := hN (N + 1) (Nat.le_succ N)
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    have hne : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    refine ⟨T (((N + 1 : ℕ) : ℂ)⁻¹ • x), subset_closure ⟨_, hmem, rfl⟩, ?_⟩
    simp only [map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hcl : ∀ n : ℕ, IsClosed (((n + 1 : ℕ) : ℂ) • A) := fun n =>
    isClosed_closure.smul_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  haveI : Nonempty F := ⟨0⟩
  obtain ⟨n, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [interior_smul₀ hne] at hy
  obtain ⟨y, hy, -⟩ := hy
  have hnb : {z : F | y + z ∈ interior A} ∈ 𝓝 (0 : F) := by
    have hc : Continuous fun z : F => y + z := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hy)
  refine mem_of_superset hnb fun z hz => ?_
  have h1 : y + z ∈ closure (T '' W) := interior_subset hz
  have h2 : y ∈ closure (T '' W) := interior_subset hy
  have := map_mem_closure₂ (f := fun a b : F => a - b) (u := T '' U)
    (continuous_fst.sub continuous_snd) h1 h2 (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a - b, hWU a ha b hb, map_sub T a b⟩)
  simpa using this

theorem sum_Ico_mem {U : ℕ → Set E} (h0 : ∀ k, (0 : E) ∈ U k)
    (hadd : ∀ k, ∀ a ∈ U (k + 1), ∀ b ∈ U (k + 1), a + b ∈ U k) {x : ℕ → E}
    (hx : ∀ j, x j ∈ U (j + 1)) : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U m := by
  intro n
  induction n with
  | zero => intro m; simpa using h0 m
  | succ n ih =>
    intro m
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show m + (n + 1) = m + 1 + n by omega]
    exact hadd m _ (hx m) _ (ih (m + 1))

theorem exists_halving [(𝓝 (0 : E)).IsCountablyGenerated] {U₀ : Set E} (h : U₀ ∈ 𝓝 (0 : E)) :
    ∃ U : ℕ → Set E, U 0 = U₀ ∧ (∀ k, U k ∈ 𝓝 (0 : E)) ∧
      (∀ k, ∀ a ∈ U (k + 1), ∀ b ∈ U (k + 1), a + b ∈ U k) ∧
      (∀ k, ∀ a ∈ U (k + 1), -a ∈ U (k + 1)) ∧ ∀ N ∈ 𝓝 (0 : E), ∃ k, U k ⊆ N := by
  classical
  obtain ⟨B, hB⟩ := (𝓝 (0 : E)).exists_antitone_basis
  let half : Set E → Set E := fun S =>
    if hS : S ∈ 𝓝 (0 : E) then Classical.choose (exists_nhds_zero_half hS) ∩
      -Classical.choose (exists_nhds_zero_half hS) else Set.univ
  have hhalf : ∀ S ∈ 𝓝 (0 : E), half S ∈ 𝓝 (0 : E) ∧ (∀ v ∈ half S, ∀ w ∈ half S, v + w ∈ S) ∧
      ∀ v ∈ half S, -v ∈ half S := by
    intro S hS
    obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_nhds_zero_half hS)
    simp only [half, dif_pos hS]
    refine ⟨inter_mem h1 (neg_mem_nhds_zero E h1), fun v hv w hw => h2 v hv.1 w hw.1, ?_⟩
    rintro v ⟨hv1, hv2⟩
    exact ⟨hv2, by simpa using hv1⟩
  let U : ℕ → Set E := fun n => Nat.rec U₀ (fun k Uk => half Uk ∩ (B k ∩ -B k)) n
  have hU : ∀ k, U k ∈ 𝓝 (0 : E) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih => exact inter_mem (hhalf _ ih).1 (inter_mem (hB.mem k) (neg_mem_nhds_zero E (hB.mem k)))
  refine ⟨U, rfl, hU, fun k a ha b hb => (hhalf _ (hU k)).2.1 a ha.1 b hb.1, ?_, fun N hN => ?_⟩
  · rintro k a ⟨ha1, ha2, ha3⟩
    exact ⟨(hhalf _ (hU k)).2.2 a ha1, by simpa using ha3, by simpa using ha2⟩
  · obtain ⟨k, -, hk⟩ := hB.toHasBasis.mem_iff.1 hN
    exact ⟨k + 1, fun a ha => hk ha.2.1⟩

theorem image_mem_nhds [CompleteSpace E] [(𝓝 (0 : E)).IsCountablyGenerated] [T2Space F] [BaireSpace F]
    (T : E →L[ℂ] F) (hT : Function.Surjective T) {U₀ : Set E} (h : U₀ ∈ 𝓝 (0 : E)) :
    T '' U₀ ∈ 𝓝 (0 : F) := by
  classical
  obtain ⟨U, rfl, hU, hadd, hneg, hbas⟩ := exists_halving h
  have h0 : ∀ k, (0 : E) ∈ U k := fun k => mem_of_mem_nhds (hU k)
  have hanti : ∀ k, U (k + 1) ⊆ U k := fun k a ha => by simpa using hadd k a ha 0 (h0 _)
  have hmono : ∀ k l, k ≤ l → U l ⊆ U k := by
    intro k l hkl
    induction hkl with
    | refl => exact le_rfl
    | step _ ih => exact (hanti _).trans ih
  let V : ℕ → Set F := fun k => closure (T '' U k)
  have hVn : ∀ k, V k ∈ 𝓝 (0 : F) := fun k => closure_image_mem_nhds T hT (hU k)
  have pick : ∀ k, ∀ r ∈ V k, ∃ x ∈ U k, r - T x ∈ V (k + 1) := by
    intro k r hr
    have hnb : {w : F | r - w ∈ V (k + 1)} ∈ 𝓝 r := by
      have hc : Continuous fun w : F => r - w := continuous_const.sub continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hVn (k + 1))
    obtain ⟨_, hw, ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hr _ hnb
    exact ⟨x, hx, hw⟩
  refine mem_of_superset (hVn 2) fun y hy => ?_
  let step : ℕ → F → E := fun k r => if hr : r ∈ V k then Classical.choose (pick k r hr) else 0
  have hstep : ∀ k r, r ∈ V k → step k r ∈ U k ∧ r - T (step k r) ∈ V (k + 1) := by
    intro k r hr
    simp only [step, dif_pos hr]
    exact Classical.choose_spec (pick k r hr)
  let r : ℕ → F := fun n => Nat.rec y (fun n rn => rn - T (step (n + 2) rn)) n
  have hr : ∀ n, r n ∈ V (n + 2) := by
    intro n
    induction n with
    | zero => exact hy
    | succ n ih => exact (hstep _ _ ih).2
  let x : ℕ → E := fun n => step (n + 2) (r n)
  have hx : ∀ n, x n ∈ U (n + 2) := fun n => (hstep _ _ (hr n)).1
  let s : ℕ → E := fun n => ∑ j ∈ Finset.range n, x j
  have hrs : ∀ n, r n = y - T (s n) := by
    intro n
    induction n with
    | zero => simp [r, s]
    | succ n ih =>
      show r n - T (x n) = _
      rw [ih]
      simp only [s, Finset.sum_range_succ, map_add]
      abel
  have htail : ∀ n m, ∑ j ∈ Finset.Ico m (m + n), x j ∈ U (m + 1) :=
    sum_Ico_mem (U := fun k => U (k + 1)) (fun k => h0 _) (fun k => hadd (k + 1)) hx
  have hdiff : ∀ m n, m ≤ n → s n - s m ∈ U (m + 1) := by
    intro m n hmn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := htail d m
    rwa [Finset.sum_Ico_eq_sub _ hmn] at this
  have hs1 : ∀ n, s n ∈ U 1 := fun n => by simpa [s] using hdiff 0 n (Nat.zero_le n)
  have hcau : CauchySeq s := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
    intro N hN
    obtain ⟨k, hk⟩ := hbas N hN
    refine mem_map.2 (mem_atTop_sets.2 ⟨(k, k), fun p hp => hk ?_⟩)
    obtain ⟨hp1, hp2⟩ := hp
    show s p.2 - s p.1 ∈ U k
    rcases le_total p.1 p.2 with hle | hle
    · exact hmono k (p.1 + 1) (by simp at hp1; omega) (hdiff _ _ hle)
    · have := hneg p.2 _ (hdiff _ _ hle)
      rw [neg_sub] at this
      exact hmono k (p.2 + 1) (by simp at hp2; omega) this
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  have hzU : z ∈ closure (U 1) := mem_closure_of_tendsto hz (Eventually.of_forall hs1)
  have hz0 : z ∈ U 0 := by
    have hnb : {q : E | z - q ∈ U 1} ∈ 𝓝 z :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU 1)
    obtain ⟨q, hq, hq1⟩ := mem_closure_iff_nhds.1 hzU _ hnb
    simpa using hadd 0 _ hq _ hq1
  refine ⟨z, hz0, ?_⟩
  have h1 : Tendsto (fun n => T (s n)) atTop (𝓝 (T z)) := (T.continuous.tendsto z).comp hz
  have h2 : Tendsto r atTop (𝓝 0) := by
    intro N hN
    obtain ⟨N', ⟨hN', hN'c⟩, hN'N⟩ := (closed_nhds_basis (0 : F)).mem_iff.1 hN
    have hpre : T ⁻¹' N' ∈ 𝓝 (0 : E) :=
      T.continuous.continuousAt.preimage_mem_nhds (by simpa using hN')
    obtain ⟨k, hk⟩ := hbas _ hpre
    refine mem_map.2 (mem_atTop_sets.2 ⟨k, fun n hn => hN'N ?_⟩)
    have hsub : V (n + 2) ⊆ N' := closure_minimal (by
      rintro _ ⟨a, ha, rfl⟩
      exact hk (hmono k (n + 2) (by omega) ha)) hN'c
    exact hsub (hr n)
  have h3 : Tendsto (fun n => T (s n)) atTop (𝓝 y) := by
    have := (tendsto_const_nhds (x := y)).sub h2
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    rw [hrs n]
    abel
  exact tendsto_nhds_unique h1 h3

theorem exists_inverse [CompleteSpace E] [(𝓝 (0 : E)).IsCountablyGenerated] [T2Space F]
    [BaireSpace F] (T : E →L[ℂ] F) (hT : Function.Bijective T) :
    ∃ S : F →L[ℂ] E, ∀ f, T (S f) = f := by
  let e := LinearEquiv.ofBijective (T : E →ₗ[ℂ] F) hT
  have hc : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro U hU
    rw [mem_map]
    refine mem_of_superset (image_mem_nhds T hT.2 hU) ?_
    rintro _ ⟨x, hx, rfl⟩
    show e.symm (e x) ∈ U
    rw [e.symm_apply_apply]
    exact hx
  exact ⟨⟨e.symm.toLinearMap, hc⟩, fun f => e.apply_symm_apply f⟩

theorem baireSpace_of_complete (X : Type*) [UniformSpace X] [AddGroup X] [IsUniformAddGroup X]
    [(𝓝 (0 : X)).IsCountablyGenerated] [CompleteSpace X] : BaireSpace X := by
  haveI := IsUniformAddGroup.uniformity_countably_generated (α := X)
  letI := UniformSpace.pseudoMetricSpace X
  infer_instance

theorem schwartz_exists_inverse : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    Function.Bijective T → ∃ S : SchwartzMap W ℂ →L[ℂ] SchwartzMap V ℂ, ∀ f, T (S f) = f := by
  intro V W _ _ _ _ T hT
  haveI : BaireSpace (SchwartzMap W ℂ) := baireSpace_of_complete _
  exact exists_inverse T hT

end FrechetOpenMapping
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SeesawSumTarget

variable {D : D7}

theorem isHeckeChar_mul {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((χ * η : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => χ x * η x := by
      funext x; simp
    rw [this]
    exact hχ.1.mul hη.1
  · simp only [MonoidHom.mul_apply, hχ.2 x, hη.2 x, mul_one]

theorem exists_scalar {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, GlobalTheory.WeilUniq.om_om_inv, map_smul] at this

section Std
open GlobalTheory.MixModel

theorem qA_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qA = (fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) 0).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qA, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A)]
  · simp only [fromCols_apply_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem qB_sumDec (A B : HSp D) :
    (GlobalTheory.BiTransfer.sumDec A B).qB = (fromCols (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E) 1).submatrix id finSumFinEquiv.symm := by
  rw [OrthDec.qB, GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat]
  simp only [GlobalTheory.BiTransfer.sumDec, Matrix.conjTranspose_submatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k
  · simp only [fromCols_apply_inl, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp only [fromCols_apply_inr]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det B)]

theorem pA_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pA ⬝ x = topR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pA, rat, qA_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, topR]
  simp [apply_ite (incA D)]

theorem pB_sumDec {S A B : HSp D} (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    (GlobalTheory.BiTransfer.sumDec A B).pB ⬝ x = botR (A := A) (B := B) x := by
  ext i j
  simp only [OrthDec.pB, rat, qB_sumDec, Matrix.mul_apply, Matrix.map_apply, submatrix_apply, id, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply, botR]
  simp [apply_ite (incA D)]

theorem boxT_sumDec (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    (GlobalTheory.BiTransfer.sumDec A B).boxT S φ φ' = box2 φ φ' := by
  funext x
  simp only [OrthDec.boxT, OrthDec.resT_apply, box2]
  rw [pA_sumDec, pB_sumDec]

theorem emb_sumDec (A B : HSp D) (g : GA D A) (g₁ : GA D B) :
    (GlobalTheory.BiTransfer.sumDec A B).emb (g, g₁) = GlobalTheory.SquareComm.blk A B (g, g₁) := by
  apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum A B)
  rw [(GlobalTheory.BiTransfer.sumDec A B).mt_emb, GlobalTheory.SquareComm.mt_blk]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.Doubling.blkMat, submatrix_apply, Equiv.symm_apply_apply, Matrix.add_apply, Matrix.mul_apply,
    OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, qA_sumDec, qB_sumDec, Matrix.map_apply, id]
  simp only [GlobalTheory.BiTransfer.sumDec, submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> rcases t with t | t <;>
    simp [Matrix.one_apply, apply_ite (incA D), ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

end Std

theorem seesaw_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B : HSp D) (χ₁ χ₁' χ₂ χ₂' : (AE D)ˣ →* Circle)
    (ω₁ : GA D S × GA D A →* Module.End ℂ (WO S A → ℂ)) (ω₂ : GA D S × GA D B →* Module.End ℂ (WO S B → ℂ)),
    IsWeilDatumO ψ S A χ₁ χ₁' ω₁ → IsWeilDatumO ψ S B χ₂ χ₂' ω₂ →
    ∃ (ω : GA D S × GA D (GlobalTheory.Doubling.hsum A B) →* Module.End ℂ (WO S (GlobalTheory.Doubling.hsum A B) → ℂ))
      (χ χ' : (AE D)ˣ →* Circle) (c : GA D S → GA D A → GA D B → ℂ),
      IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum A B) χ χ' ω ∧ (∀ u g g₁, ‖c u g g₁‖ = 1) ∧
      ∀ φ φ', IsThetaFunO ψ S A φ → IsThetaFunO ψ S B φ' → IsThetaFunO ψ S (GlobalTheory.Doubling.hsum A B) (box2 φ φ') ∧
        ∀ u g g₁, thetaKO ω u (GlobalTheory.SquareComm.blk A B (g, g₁)) (box2 φ φ') =
          c u g g₁ * (thetaKO ω₁ u g φ * thetaKO ω₂ u g₁ φ') := by
  intro D ψ hψ S A B χ₁ χ₁' χ₂ χ₂' ω₁ ω₂ H₁ H₂
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨ω₂', H₂'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S B χ₁ χ₂' hη H₁.hecS H₂.hecT H₁.resS H₂.resT
  obtain ⟨ω, H⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.Doubling.hsum A B) χ₁ (χ₁' * χ₂') hη H₁.hecS
    (isHeckeChar_mul H₁.hecT H₂.hecT) H₁.resS (resEta_mul H₁.resT H₂.resT)
  choose c hc using fun p => exists_scalar H₂' H₂ p
  refine ⟨ω, χ₁, χ₁' * χ₂', fun u _ g₁ => (c (u, g₁) : ℂ), H, fun u _ g₁ => Circle.norm_coe _,
    fun φ φ' hφ hφ' => ⟨?_, fun u g g₁ => ?_⟩⟩
  · rw [← boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec A B).isThetaFunO_boxT hφ hφ'
  · have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ A B (GlobalTheory.BiTransfer.sumDec A B) S).om_box χ₁ χ₁' χ₂' ω ω₁
      ω₂' H H₁ H₂' u g g₁ φ φ' hφ hφ'
    simp only [thetaKO]
    rw [← emb_sumDec, ← boxT_sumDec, key, GlobalTheory.MixModel.OrthDec.boxT_zero, hc (u, g₁) φ' hφ', Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.SeesawSumTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewGramInrInl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.VacFix

theorem isHalf_of_mulG {D : D7} (S : HSp D) {n : ℕ} (ε : AE D) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (h : ∀ a b, ε * mulG S x a b = mulG S x a b) (a : Fin n) (b : Fin S.rank) : ε * x a b = x a b := by
  have h1 : ε • mulG S x = mulG S x := Matrix.ext h
  have h2 : divG S (ε • mulG S x) = ε • divG S (mulG S x) := Matrix.smul_mul _ _ _
  rw [h1, divG_mulG] at h2
  exact (congrFun (congrFun h2 a) b).symm

theorem hTens_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (hc : ∀ a, c (c a) = a)
    {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A)
    (h₁ : ∀ a b, JB (e (.inl a)) (e (.inr b)) = 0) (h₂ : ∀ a b, JB (e (.inr a)) (e (.inl b)) = 0)
    (ε : A) (hε : ε * c ε = 0) (x : Matrix (Fin n) (Fin d) A)
    (hl : ∀ a b, ε * x a (e (.inl b)) = x a (e (.inl b)))
    (hr : ∀ a b, ε * c (x a (e (.inr b))) = c (x a (e (.inr b)))) : hTens c JA JB x x = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  obtain ⟨b | b, rfl⟩ := e.surjective b <;> obtain ⟨l | l, rfl⟩ := e.surjective l
  · have u := congrArg c (hl k l)
    rw [map_mul] at u
    rw [← u, ← hl a b]
    linear_combination (x a (e (.inl b)) * JA a k * JB (e (.inl b)) (e (.inl l)) * c (x k (e (.inl l)))) * hε
  · rw [h₁, mul_zero, zero_mul]
  · rw [h₂, mul_zero, zero_mul]
  · have u := congrArg c (hr a b)
    rw [map_mul, hc] at u
    rw [← u, ← hr k l]
    linear_combination (x a (e (.inr b)) * JA a k * JB (e (.inr b)) (e (.inr l)) * c (x k (e (.inr l)))) * hε

theorem skewGram_inl_inr {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    skewGram A B e (e (.inl a)) (e (.inr b)) = 0 := by
  simp [skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem skewGram_inr_inl {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    skewGram A B e (e (.inr a)) (e (.inl b)) = 0 := by
  simp [skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem hTens_mixHalf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : Pt G i j) (hγ : γ ∈ mixHalf e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact isHalf_of_mulG (negSp (spW G i j)) ε (colV e γ)ᵀ hγ.1 b a
  · refine isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem psi_double {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ)
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (θ : 𝓞 E)
    (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (hγ : γ ∈ latAtV X Y v) :
    B.ψ (⅟(2 : AF F) * symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (2 • γ) (2 • γ)) = 1 := by
  have h2 : (2 : ℕ) • γ = (2 : AF F) • γ := by rw [two_smul, two_smul]
  rw [h2, GlobalTheory.LatVac.symp_smul_smul, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul]
  refine GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 2 ?_ γ hγ γ hγ
  rw [map_ofNat]
  exact ofNat_mem _ 2

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v) →
      ∀ γ ∈ genPt e v, Acts (evFin D.host.F v) (Γ.M.co.rho W.ψ γ) (Γ.M.vac v) (Γ.M.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM.vac v
  have h1 := hθ γ (hL γ (genPt_subset e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact psi_double _ Bs Γ.V Γ.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalf e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.BigDat.VacFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSelfDualLatticeLocalisedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewSelfDual_lattice_localised_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d r s : ℕ} (Y : Spc F E d), Y.IsSkew σ B r s → ∀ (v : Pl F) (u : Fin d → E),
    (∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * form σ Y.J u y)) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • u ∈ Y.L := by
  first | exact @GlobalTheory.SkewLocDual.exists_smul_mem_of_integral | exact GlobalTheory.SkewLocDual.exists_smul_mem_of_integral | (intros; apply GlobalTheory.SkewLocDual.exists_smul_mem_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCompactUnderWittChartStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_under_witt_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ K : Subgroup (UD D J₂), IsStdK D.sp.cm.sig T K → ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ GlobalTheory.StdUnn.K D n := by
  first | exact @GlobalTheory.SWLink.stdK_iff | exact GlobalTheory.SWLink.stdK_iff | (intros; apply GlobalTheory.SWLink.stdK_iff <;> assumption)
end


import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import GroundTheory.PAdicHodge.TiltValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasis
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualTop

theorem eq_zero_of_forall_pow_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ c : O} (hϖ : Irreducible ϖ) (h : ∀ n : ℕ, ϖ ^ n ∣ c) : c = 0 := by
  by_contra hc
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  obtain ⟨d, hd⟩ := h (k + 1)
  have hk : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hu : (u : O) = ϖ * d := by
    apply mul_right_cancel₀ hk
    rw [hd]; ring
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro d hu.symm) u.isUnit)

section Lat

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem bT_smul_left (k : FractionRing O) (x : VT) (y : VT') :
    D.bT (k • x) y = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT
    (FractionRing O)).map_smul (D.bT.flip y) k x

theorem bT_smul_right (k : FractionRing O) (x : VT) (y : VT') :
    D.bT x (k • y) = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT'
    (FractionRing O)).map_smul (D.bT x) k y

theorem eq_zero_of_bT (hP : PerfectRight D.bT) {y : VT'} (h : ∀ x, D.bT x y = 0) : y = 0 :=
  (hP 0).unique h (fun x => by simp)

theorem dualLatticePairing_eq_zero_of_mem_lattice (hL : IsLatticeIn D.T) {y : VT'} (h : ∀ x ∈ D.T, D.bT x y = 0) (x : VT) :
    D.bT x y = 0 := by
  let ψ := (D.bT.flip y).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
  have hs : Submodule.span (FractionRing O) (D.T : Set VT) ≤ LinearMap.ker ψ :=
    Submodule.span_le.2 fun z hz => LinearMap.mem_ker.2 (h z hz)
  have hx : x ∈ Submodule.span (FractionRing O) (D.T : Set VT) := hL.2 ▸ Submodule.mem_top
  exact LinearMap.mem_ker.1 (hs hx)

theorem cont_bT (x : VT) : Continuous fun y : VT' => D.bT x y :=
  D.contbT.comp (continuous_const.prodMk continuous_id)

theorem isOpen_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsOpen ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
  have : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext t; simp [Submodule.mem_one]
  rw [this]; exact hemb.isOpen_range

theorem isClosed_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) :=
  AddSubgroup.isClosed_of_isOpen (1 : Submodule O (FractionRing O)).toAddSubgroup (isOpen_one hemb)

theorem isClosed_dualLattice_of_pairing (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed (D.T' : Set VT') := by
  have : (D.T' : Set VT') = ⋂ x ∈ D.T,
      (fun y => D.bT x y) ⁻¹' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext y
    exact ⟨fun h => Set.mem_iInter₂.2 fun x hx => h x hx, fun h x hx => Set.mem_iInter₂.1 h x hx⟩
  rw [this]
  exact isClosed_biInter fun x _ => (isClosed_one hemb).preimage (cont_bT D x)

end Lat

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem isCompact_dualLattice_of_pairing [CompactSpace O] (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) : IsCompact (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hL.1
  have hsK : Submodule.span (FractionRing O) (s : Set VT) = ⊤ := by
    rw [eq_top_iff, ← hL.2]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [← hs] at hx
    exact Submodule.span_subset_span O (FractionRing O) (s : Set VT) hx
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (FractionRing O) (s : Set VT)
  haveI : Fintype b := (s.finite_toSet.subset hbs).fintype
  obtain ⟨e, he⟩ : ∃ e : Module.Basis b (FractionRing O) VT, ∀ i, e i = (i : VT) :=
    ⟨Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hsK])),
      fun i => Module.Basis.mk_apply _ _ i⟩
  have hbT : ∀ i : b, (i : VT) ∈ D.T := fun i => hs ▸ Submodule.subset_span (hbs i.2)
  choose f hf using fun i : b => (hP (e.coord i)).exists
  let Φ : (b → O) → VT' := fun c => ∑ i, c i • f i
  have hΦ : Continuous Φ := continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hsub : (D.T' : Set VT') ⊆ Set.range Φ := by
    intro y hy
    have hy' : ∀ i : b, D.bT (i : VT) y ∈ (1 : Submodule O (FractionRing O)) := fun i => hy _ (hbT i)
    choose c hc using fun i => Submodule.mem_one.1 (hy' i)
    refine ⟨c, ?_⟩
    symm
    rw [← sub_eq_zero]
    apply eq_zero_of_bT D hP
    intro x
    have hx : D.bT x y = ∑ i, e.coord i x * algebraMap O (FractionRing O) (c i) := by
      conv_lhs => rw [← e.sum_repr x]
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bT_smul_left, he, ← hc i, Module.Basis.coord_apply]
    rw [map_sub, map_sum, hx, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hf, Algebra.smul_def, mul_comm]
  exact (isCompact_range hΦ).of_isClosed_subset (isClosed_dualLattice_of_pairing D hemb) hsub

end Lat2

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat3

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem isOpen_powSub (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
  obtain ⟨s, hs⟩ := hL.1
  set a : FractionRing O := algebraMap O (FractionRing O) ϖ ^ n with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ (fun h => hϖ.ne_zero
    (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero])))
  let W : Set ↥D.T' := ⋂ x ∈ s, (fun z : ↥D.T' => D.bT (a⁻¹ • x) (z : VT')) ⁻¹'
    ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))
  have hW : IsOpen W := isOpen_biInter_finset fun x _ =>
    (isOpen_one hemb).preimage ((cont_bT D _).comp continuous_subtype_val)
  have h0 : (0 : ↥D.T') ∈ W := Set.mem_iInter₂.2 fun x _ => by
    simp only [Set.mem_preimage, ZeroMemClass.coe_zero, map_zero, SetLike.mem_coe]
    exact Submodule.zero_mem _
  have hWsub : W ⊆ ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
    intro z hz
    have hz' := Set.mem_iInter₂.1 hz
    have hyT : a⁻¹ • (z : VT') ∈ D.T' := by
      intro x hx
      have hle : Submodule.span O (s : Set VT) ≤
          (1 : Submodule O (FractionRing O)).comap (D.bT.flip (a⁻¹ • (z : VT'))) := by
        refine Submodule.span_le.2 fun x hx => ?_
        have := hz' x hx
        simp only [Set.mem_preimage, SetLike.mem_coe] at this
        show D.bT x (a⁻¹ • (z : VT')) ∈ (1 : Submodule O (FractionRing O))
        rwa [bT_smul_right, ← bT_smul_left]
      rw [hs] at hle
      exact hle hx
    refine mem_powSub.2 ⟨⟨a⁻¹ • (z : VT'), hyT⟩, Subtype.ext ?_⟩
    show ϖ ^ n • a⁻¹ • (z : VT') = z
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n), smul_smul, map_pow, ← ha, mul_inv_cancel₀ ha0,
      one_smul]
  exact AddSubgroup.isOpen_of_mem_nhds (powSub (M := ↥D.T') ϖ n).toAddSubgroup
    (Filter.mem_of_superset (hW.mem_nhds h0) hWsub)

theorem eq_zero_of_mem_powSub (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) {ϖ : O}
    (hϖ : Irreducible ϖ) {z : ↥D.T'} (hz : ∀ n, z ∈ powSub (M := ↥D.T') ϖ n) : z = 0 := by
  refine Subtype.ext (eq_zero_of_bT D hP (dualLatticePairing_eq_zero_of_mem_lattice D hL (fun x hx => ?_)))
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (z.2 x hx)
  have hdvd : ∀ n : ℕ, ϖ ^ n ∣ c := by
    intro n
    obtain ⟨w, hw⟩ := mem_powSub.1 (hz n)
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (w.2 x hx)
    refine ⟨d, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [hc, ← hw, map_mul, hd]
    show D.bT x (ϖ ^ n • (w : VT')) = _
    rw [map_smul, Algebra.smul_def]
  rw [← hc, eq_zero_of_forall_pow_dvd hϖ hdvd, map_zero]

end Lat3

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

theorem dualLat_compact_powSub_nhds : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D hO hemb hL hP hT2 ϖ hϖ
  have hK : IsCompact (D.T' : Set VT') := isCompact_dualLattice_of_pairing D hemb hL hP
  haveI : CompactSpace ↥D.T' := isCompact_iff_compactSpace.1 hK
  have hopen := isOpen_powSub D hemb hL hϖ
  refine ⟨inferInstance, hopen, fun U hU => ?_⟩
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.1 hU
  obtain ⟨n, hn⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed
    (fun n : ℕ => ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T'))
    (fun n => AddSubgroup.isClosed_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n))
    (by
      rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
      intro z hz hz'
      have : z = 0 := eq_zero_of_mem_powSub D hL hP hϖ fun n => Set.mem_iInter.1 hz' n
      exact hz (this ▸ h0V))
    (fun a b => ⟨max a b, fun x hx => powSub_anti ϖ (le_max_left a b) hx,
      fun x hx => powSub_anti ϖ (le_max_right a b) hx⟩)
  refine ⟨n, fun z hz => hVU ?_⟩
  by_contra hc
  exact Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hn) hc hz

end GlobalTheory.LocDualTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerEAddSmulMemEisensteinShiftGraded
section
noncomputable section

namespace GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ}

omit [CompleteSpace K] in

theorem conn_mem_ext_Rpi (D : BKDat O K l e a ι η H) {y : Vec K a ι}
    (hy : y ∈ D.ext (Rpi O K l e)) : D.conn y ∈ D.ext (Rpi O K l e) := by
  have hf : ∀ i τ, (Matrix.mulVec (D.mxInv τ) (y τ)) i ∈ Rpi O K l e := fun i τ =>
    D.mem_extc_iff.1 (mem_tot.1 hy τ) i
  rw [D.eq_sum_phi_bas y, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hL : D.phi (bas i) ∈ D.L := D.phi_mem_L (D.bas_mem_M i)
  have hM : D.phi (bas i) ∈ D.MM := D.ext_mono (A_le_S l e) hL
  rw [PhiMod.conn_smul_tot]
  refine Submodule.add_mem _ ?_ ?_
  · exact D.smul_tot_mem_ext (fun τ => N_mem (derivative_mem_R l (hf i τ)))
      (D.ext_mono (S_le_R l e) hM)
  · exact D.smul_tot_mem_ext (hf i) (D.ext_mono (S_le_R l e) (D.conn_mem_MM hM))

omit [CompleteSpace K] in
theorem EN_add_smul_mem_shiftE' (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι)
    (hx : x ∈ shiftE l e j (D.ext (Rpi O K l e))) :
    D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  rw [mem_shiftE] at hx ⊢
  set y := Ezpow K l e (-j) • x with hy
  have hxy : x = Ezpow K l e j • y := by
    rw [hy, smul_smul, mul_comm, Ezpow_neg_mul, one_smul]
  clear_value y
  clear hy
  have h1 : Ezpow K l e (j + 1) = Ezpow K l e j * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  have hc : ((j * e * l : ℤ) : K) • x = ((j * e * l : ℤ) : K⟦X⟧) • x := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hN : E K l e * N K (Ezpow K l e j) + ((j * e * l : ℤ) : K⟦X⟧) * Ezpow K l e j =
      Ezpow K l e (j + 1) * ((j * e : ℤ) : K⟦X⟧) := by
    rw [E_mul_N_Ezpow, N_E, h1, E]
    push_cast
    ring
  have key : D.EN x + ((j * e * l : ℤ) : K) • x =
      Ezpow K l e (j + 1) • ((j * e : ℤ) • y + D.conn y) := by
    rw [hc, PhiMod.EN_apply, hxy, PhiMod.conn_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      ← Int.cast_smul_eq_zsmul K⟦X⟧ (j * e : ℤ), smul_smul, ← hN, add_smul, h1, mul_comm (E K l e) (Ezpow K l e j)]
    abel
  rw [key, smul_smul, Ezpow_neg_mul, one_smul]
  exact Submodule.add_mem _ (zsmul_mem hx _) (conn_mem_ext_Rpi D hx)

theorem EN_add_smul_mem_shiftE :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j x hx
  exact EN_add_smul_mem_shiftE' D j x hx

end GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatible
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.CocycleLimit

theorem exists_continuous_cocycle_lift_of_compatible : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  intro O _ G _ _ M _ _ _ _ _ _ _ ρ a r hopen hbasis w hw hstep
  set N : ℕ → Submodule O M := fun n => powSub (M := M) a n with hN

  have hclosedN : ∀ n, IsClosed ((N n : Submodule O M) : Set M) := fun n =>
    AddSubgroup.isClosed_of_isOpen (N n).toAddSubgroup (hopen n)

  have hex : ∀ g, ∃ x, ∀ k, x - w k g ∈ N (r + k) := by
    intro g
    let C : ℕ → Set M := fun k => {x | x - w k g ∈ N (r + k)}
    have hsub : ∀ k, C (k + 1) ⊆ C k := by
      intro k x hx
      have h1 : x - w (k + 1) g ∈ N (r + k) :=
        powSub_anti a (by omega : r + k ≤ r + (k + 1)) hx
      have h2 := hstep k g
      show x - w k g ∈ N (r + k)
      have : x - w k g = (x - w (k + 1) g) + (w (k + 1) g - w k g) := by abel
      rw [this]; exact (N (r + k)).add_mem h1 h2
    have hne : ∀ k, (C k).Nonempty := fun k => ⟨w k g, by simp [C, (N (r + k)).zero_mem]⟩
    have hcl : ∀ k, IsClosed (C k) := fun k =>
      (hclosedN (r + k)).preimage (continuous_id.sub continuous_const)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub hne
      (hcl 0).isCompact hcl
    exact ⟨x, fun k => Set.mem_iInter.1 hx k⟩
  choose e he using hex

  have hzero : ∀ x : M, (∀ k, x ∈ N (r + k)) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := hbasis ({x}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    have : x ∈ N (r + n) := hx n
    exact hn (powSub_anti a (by omega : n ≤ r + n) this) rfl

  have hcoc : ∀ k g h, w k (g * h) - (w k g + ρ g (w k h)) ∈ N (r + k) := by
    intro k g h
    have := (hw k).2 g h
    simp only [quotRep_mk] at this
    rw [← Submodule.Quotient.mk_add] at this
    exact (Submodule.Quotient.eq _).1 this
  refine ⟨e, ⟨?_, ?_⟩, fun k g => he g k⟩
  ·
    rw [continuous_iff_continuousAt]
    intro g0 U hU
    have hV : {y : M | y + e g0 ∈ U} ∈ nhds (0 : M) :=
      (continuous_add_right (e g0)).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨n, hn⟩ := hbasis _ hV
    let q : G → M ⧸ powSub (M := M) a (r + n) := fun g => Submodule.Quotient.mk (w n g)
    have hq : Continuous q := (hw n).1
    have hsing : IsOpen ({q g0} : Set (M ⧸ powSub (M := M) a (r + n))) := by
      rw [← (Submodule.isOpenQuotientMap_mkQ (powSub (M := M) a (r + n))).isQuotientMap.isOpen_preimage]
      have : (Submodule.mkQ (powSub (M := M) a (r + n))) ⁻¹' {q g0} =
          (fun y => y - w n g0) ⁻¹' ((N (r + n) : Submodule O M) : Set M) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, q,
          SetLike.mem_coe, N]
        exact Submodule.Quotient.eq _
      rw [this]
      exact (hopen (r + n)).preimage (continuous_id.sub continuous_const)
    have hS : q ⁻¹' {q g0} ∈ nhds g0 := (hsing.preimage hq).mem_nhds rfl
    show e ⁻¹' U ∈ nhds g0
    refine Filter.mem_of_superset hS ?_
    intro g hg
    have hg' : w n g - w n g0 ∈ N (r + n) := (Submodule.Quotient.eq _).1 hg
    have hmem : e g - e g0 ∈ N (r + n) := by
      have : e g - e g0 = (e g - w n g) + (w n g - w n g0) - (e g0 - w n g0) := by abel
      rw [this]
      exact (N (r + n)).sub_mem ((N (r + n)).add_mem (he g n) hg') (he g0 n)
    have := hn (powSub_anti a (by omega : n ≤ r + n) hmem)
    simpa using this
  ·
    intro g h
    rw [← sub_eq_zero]
    apply hzero
    intro k
    have : e (g * h) - (e g + ρ g (e h)) =
        (e (g * h) - w k (g * h)) - (e g - w k g) - ρ g (e h - w k h) +
          (w k (g * h) - (w k g + ρ g (w k h))) := by
      rw [map_sub]; abel
    rw [this]
    refine (N (r + k)).add_mem ((N (r + k)).sub_mem ((N (r + k)).sub_mem (he _ k) (he _ k))
      (powSub_stable ρ a _ g _ (he h k))) (hcoc k g h)

end GlobalTheory.CocycleLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCokerStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_smul_mem_range_of_finiteLength_coker : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (G : GlobalTheory.BK.Hom Q T), IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  first | exact @GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker | exact GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker | (intros; apply GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntiltStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l, ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  first | exact @GlobalTheory.PSer.exists_flEquiv_untilt | exact GlobalTheory.PSer.exists_flEquiv_untilt | (intros; apply GlobalTheory.PSer.exists_flEquiv_untilt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionPairingEqInvUniformizer
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem linK_smul {O : Type} [CommRing O] [IsDomain O] {V : Type} [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (φ : V →ₗ[O] FractionRing O) (c : FractionRing O) (v : V) : φ (c • v) = c * φ v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) φ).map_smul c v

theorem exists_pairKO_eq_inv_unif : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D ϖ hϖ n f hf
  set π : (FractionRing O) := algebraMap O (FractionRing O) ϖ with hπ
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero
  have hpn : ∀ y : VT', ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  have hpnT : ∀ y : VT, ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  set f' : VT' := (π ^ n)⁻¹ • (f : VT') with hf'
  have hff' : ϖ ^ n • f' = f := by
    rw [hpn, hf', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul]
  clear_value f' π
  have hnot : f' ∉ D.T' := by
    intro h
    apply hf
    refine mem_powSub.2 ⟨⟨f', h⟩, ?_⟩
    ext
    simp [hff']
  have hnot' : ¬ ∀ x ∈ D.T, D.bT x f' ∈ (1 : Submodule O (FractionRing O)) := hnot
  push_neg at hnot'
  obtain ⟨v, hvT, hu⟩ := hnot'
  set u := D.bT v f' with hu_def
  have hu0 : u ≠ 0 := by
    intro h; apply hu; rw [h]; exact Submodule.zero_mem _
  have hnotint : ¬ IsLocalization.IsInteger O u := by
    rintro ⟨o, ho⟩; exact hu (Submodule.mem_one.2 ⟨o, ho⟩)
  obtain ⟨w, hw⟩ : IsLocalization.IsInteger O u⁻¹ :=
    (ValuationRing.isInteger_or_isInteger O u).resolve_left hnotint
  have hwnu : w ∉ nonunits O → False := by
    intro h
    rw [mem_nonunits_iff, not_not] at h
    obtain ⟨w', hw'⟩ := h
    apply hnotint
    refine ⟨(w'⁻¹ : Oˣ), ?_⟩
    have : algebraMap O (FractionRing O) (w' : O) * u = 1 := by
      rw [hw', hw, inv_mul_cancel₀ hu0]
    have h2 : algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * algebraMap O (FractionRing O) (w' : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) = algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * (algebraMap O (FractionRing O) (w' : O) * u) := by rw [this, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    by_contra h
    exact hwnu h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at hwm
  obtain ⟨o, ho⟩ := hwm
  have hkey : D.bT (o • v) f' = π⁻¹ := by
    rw [D.bT.map_smul o v, LinearMap.smul_apply, Algebra.smul_def, ← hu_def]
    have h1 : algebraMap O (FractionRing O) o * π = u⁻¹ := by rw [hπ, ← map_mul, ho, hw]
    have : algebraMap O (FractionRing O) o = u⁻¹ * π⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    rw [this, mul_comm u⁻¹, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  refine ⟨Submodule.Quotient.mk ((π ^ n)⁻¹ • (o • v)), ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_smul, hpnT, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact D.T.smul_mem o hvT
  · rw [pairKO_mk, ← hkey]
    congr 1
    have e1 : D.bT ((π ^ n)⁻¹ • (o • v)) f = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT.flip (f : VT')) ((π ^ n)⁻¹) (o • v)
    have e2 : D.bT (o • v) ((π ^ n)⁻¹ • (f : VT')) = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT (o • v)) ((π ^ n)⁻¹) (f : VT')
    rw [e1, hf', e2]

end GlobalTheory.LocDualInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueMaxTermUntiltFrobeniusSeriesStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_max_term_untiltFrobeniusSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 → ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) < ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  first | exact @GlobalTheory.PSer.Uniq.exists_unique_max_term | exact GlobalTheory.PSer.Uniq.exists_unique_max_term | (intros; apply GlobalTheory.PSer.Uniq.exists_unique_max_term <;> assumption)
end


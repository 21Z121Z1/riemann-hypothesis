import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExte
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeak
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosed

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem hausdorff_tilt_witt : letI := cbTop l; T2Space (Cb l) := by
  letI := cbValued l
  infer_instance

theorem ring_cb : letI := cbTop l; IsTopologicalRing (Cb l) := by
  letI := cbValued l
  infer_instance

theorem jD_piN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := GlobalTheory.T.exists_image_aN_eq_range_sum ((F l).E K s LL h) T
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisGal

open Filter Topology

variable {l : ℕ} [hl : Fact l.Prime]

private theorem sigO_coe_pt (g : Per.Gq l) (y : Per.OC l) :
    ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) := by
  apply GlobalTheory.RingIface.sigO_coe

private theorem tower_pt (x : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) x) = ainfToAcris l x := by
  change _ = algebraMap (Per.Ainf l) (Per.Acris l) x
  symm
  apply GlobalTheory.RingIface.tower

theorem eventually_norm_σC_sub_lt (y : ℂ_[l]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g : GQ l in 𝓝 1, ‖Per.σC g y - y‖ < ε := by
  have hd : DenseRange (fun x : Om l => (x : ℂ_[l])) := UniformSpace.Completion.denseRange_coe
  obtain ⟨x, hx⟩ := hd.exists_dist_lt y (half_pos hε)
  rw [dist_eq_norm] at hx
  filter_upwards [GlobalTheory.Cyc.eventually_apply_eq x 1] with g hg
  have e : Per.σC g y - y = Per.σC g (y - x) - (y - x) := by
    rw [map_sub, GlobalTheory.RingBasics.σC_coe, hg, AlgEquiv.one_apply]; ring
  rw [e]
  calc ‖Per.σC g (y - x) - (y - x)‖ ≤ ‖Per.σC g (y - x)‖ + ‖y - x‖ := norm_sub_le _ _
    _ < ε := by rw [GlobalTheory.RingBasics.norm_σC]; linarith

theorem exists_eq_l_mul (z : Per.OC l) (hz : ‖(z : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖) :
    ∃ c : Per.OC l, z = (l : Per.OC l) * c := by
  have h0 : ((l : ℕ) : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  refine ⟨⟨(z : ℂ_[l]) / l, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
  · change (z : ℂ_[l]) = ((l : Per.OC l) : ℂ_[l]) * ((z : ℂ_[l]) / l)
    have : ((l : Per.OC l) : ℂ_[l]) = l := by simp
    rw [this]; field_simp

variable {ξ : Per.Ainf l}

theorem eventually_sub_mem_one (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} := by
  have hl0 : (0 : ℝ) < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  filter_upwards [eventually_norm_σC_sub_lt ((Per.θ l y : Per.OC l) : ℂ_[l]) hl0] with g hg
  have h1 : Per.θ l (Per.σA g y - y) = Per.σO g (Per.θ l y) - Per.θ l y := by rw [map_sub, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨c, hc⟩ := exists_eq_l_mul (Per.σO g (Per.θ l y) - Per.θ l y)
    (by rw [AddSubgroupClass.coe_sub, sigO_coe_pt]; exact hg.le)
  obtain ⟨c', rfl⟩ := GlobalTheory.MemLoc.ThetaD.θ_surj l c
  have hk : Per.σA g y - y - (l : Per.Ainf l) * c' ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, h1, hc, map_mul, map_natCast, sub_self]
  rw [hξ, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  rw [Ideal.mem_span_pair]
  exact ⟨c', d, by linear_combination hd⟩

theorem eventually_sub_mem_pow (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + 1) := by
  set I : Ideal (Per.Ainf l) := Ideal.span {((l : ℕ) : Per.Ainf l), ξ} with hI
  have hlI : ((l : ℕ) : Per.Ainf l) ∈ I := Ideal.subset_span (by simp)
  have ht : ∀ z : Per.Fl l, ∀ᶠ g : GQ l in 𝓝 1,
      Per.σA g (WittVector.teichmuller l z) - WittVector.teichmuller l z ∈ I ^ (N + 1) := by
    intro z
    obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv (Per.Fl l) l N).surjective z
    filter_upwards [eventually_sub_mem_one hξ (WittVector.teichmuller l w)] with g hg
    have := SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one hlI N)
    rw [iterateFrobeniusEquiv_def, map_pow, map_pow]
    exact this
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y N
  have hall := (Filter.eventually_all_finset (Finset.Iic N)).2
    (fun i _ => ht ((((_root_.frobeniusEquiv (Per.Fl l) l).symm ^ i) (y.coeff i))))
  filter_upwards [hall] with g hg
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add, map_mul, map_pow, map_natCast, map_sum, add_sub_add_comm, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlI _)) (sum_mem fun i hi => ?_)
  rw [map_mul, map_pow, map_natCast, ← sub_mul]
  exact Ideal.mul_mem_right _ _ (hg i hi)

theorem dvd_of_mem (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) {z : Per.Ainf l}
    (hz : z ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + l * N)) :
    (l : Per.Acris l) ^ N ∣ ainfToAcris l z := by
  have hθ : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, hξ]; exact Ideal.mem_span_singleton_self ξ
  have hxl : (l : Per.Acris l) ∣ ainfToAcris l ξ ^ l := by
    rw [← factorial_mul_dpow ξ hθ l]
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hl.out.pos le_rfl
    rw [hk]; push_cast
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  rw [Ideal.span_insert] at hz
  have h1 := Ideal.sup_pow_add_le_pow_sup_pow hz
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Submodule.mem_sup] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, pow_mul]
  exact dvd_add (Dvd.intro_left _ rfl) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hxl N) _)

theorem eventually_dvd_ainf (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (ainfToAcris l y) - ainfToAcris l y := by
  obtain ⟨ξ, hξ, -, -⟩ := GlobalTheory.Prism.exists_generator l
  filter_upwards [eventually_sub_mem_pow hξ (N + l * N) y] with g hg
  have h := dvd_of_mem hξ N (Ideal.pow_le_pow_right (Nat.le_succ _) hg)
  have e : galC g (ainfToAcris l y) = ainfToAcris l (Per.σA g y) := (GlobalTheory.CrisMaps.sigA_extends g).alg y
  rwa [e, ← map_sub]

theorem eventually_dvd_dpow {x : Per.Ainf l} (hx : Per.θ l x = 0) (k N : ℕ) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (dpow x hx k) - dpow x hx k := by
  choose c hc using GlobalTheory.RingBasics.exists_pow_div_factorial l
  have hc' : ∀ n : ℕ, (n.factorial : Per.Acris l) * algebraMap ℤ_[l] _ (c n) = (l : Per.Acris l) ^ n :=
    fun n => by
      simpa only [map_mul, map_natCast, map_pow] using congrArg (algebraMap ℤ_[l] (Per.Acris l)) (hc n)
  filter_upwards [eventually_dvd_ainf (N + 1) x] with g ⟨D, hD⟩
  set X := ainfToAcris l x with hX
  set Y := ∑ m ∈ Finset.range (k + 1), dpow x hx m * (algebraMap ℤ_[l] (Per.Acris l) (c (k - m)) *
    (l : Per.Acris l) ^ (N * (k - m)) * D ^ (k - m)) with hYdef
  have hY : (k.factorial : Per.Acris l) * Y = (X + (l : Per.Acris l) ^ (N + 1) * D) ^ k := by
    rw [hYdef, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← Nat.choose_mul_factorial_mul_factorial hmk, ← factorial_mul_dpow x hx m, mul_pow, ← pow_mul,
      show (N + 1) * (k - m) = (k - m) + N * (k - m) by ring, pow_add, ← hc' (k - m)]
    push_cast
    ring
  have hσ : galC g (dpow x hx k) = Y := by
    have h1 := congrArg (galC g) (factorial_mul_dpow x hx k)
    rw [map_mul, map_natCast, map_pow, ← hX, show galC g X = X + (l : Per.Acris l) ^ (N + 1) * D by
      rw [← hD]; ring] at h1
    exact sub_eq_zero.1 (acris_nat_cancel k.factorial_ne_zero (by rw [mul_sub, h1, hY, sub_self]))
  have hc0 : algebraMap ℤ_[l] (Per.Acris l) (c 0) = 1 := by simpa using hc' 0
  rw [hσ, hYdef, Finset.sum_range_succ, Nat.sub_self, hc0, pow_zero, mul_zero, pow_zero, mul_one, mul_one,
    mul_one, add_sub_cancel_right]
  refine Finset.dvd_sum fun m hm => Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left
    (pow_dvd_pow _ (Nat.le_mul_of_pos_right N (by have := Finset.mem_range.1 hm; omega))) _) _) _

variable (l) in

def fixNear : Subring (Per.Acris l) where
  carrier := {x | ∀ N : ℕ, ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g x - x}
  mul_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨galC g a * v + u * b, ?_⟩
    rw [map_mul]
    linear_combination galC g a * hv + b * hu
  one_mem' N := .of_forall fun g => ⟨0, by simp⟩
  add_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by rw [map_add]; linear_combination hu + hv⟩
  zero_mem' N := .of_forall fun g => ⟨0, by simp⟩
  neg_mem' {a} ha N := by
    filter_upwards [ha N] with g ⟨u, hu⟩
    exact ⟨-u, by rw [map_neg]; linear_combination -hu⟩

theorem algebraMap_mem_fixNear (s : Per.Acris0 l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) s ∈ fixNear l := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.exists_isEps_for_inj l
  have hx : Per.θ l (GlobalTheory.MemLoc.xi e) = 0 := (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he _).2 dvd_rfl
  obtain ⟨s, hs⟩ := s
  have key : ∀ y ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n},
      ∀ hy : y ∈ Per.Acris0 l, algebraMap (Per.Acris0 l) (Per.Acris l) ⟨y, hy⟩ ∈ fixNear l := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro hy0
      obtain ⟨n, hn⟩ := hy
      have h1 : (n.factorial : Per.Acris0 l) * ⟨y, hy0⟩ =
          algebraMap (Per.Ainf l) (Per.Acris0 l) (GlobalTheory.MemLoc.xi e) ^ n := Subtype.ext (by simpa using hn)
      have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
      rw [map_mul, map_natCast, map_pow, tower_pt] at h2
      rw [eq_dpow hx h2]
      exact fun N => eventually_dvd_dpow hx n N
    | zero =>
      intro h0
      have e0 : (⟨0, h0⟩ : Per.Acris0 l) = 0 := Subtype.ext rfl
      rw [e0, map_zero]; exact zero_mem _
    | add y z hy hz ihy ihz =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have hz0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he z).2 hz
      have e0 : (⟨y + z, h0⟩ : Per.Acris0 l) = ⟨y, hy0⟩ + ⟨z, hz0⟩ := Subtype.ext rfl
      rw [e0, map_add]; exact add_mem (ihy hy0) (ihz hz0)
    | smul r y hy ihy =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have e0 : (⟨r • y, h0⟩ : Per.Acris0 l) = algebraMap (Per.Ainf l) (Per.Acris0 l) r * ⟨y, hy0⟩ :=
        Subtype.ext (Algebra.smul_def r y)
      rw [e0, map_mul, tower_pt]
      exact mul_mem (fun N => eventually_dvd_ainf N r) (ihy hy0)
  exact key s ((GlobalTheory.MemLoc.mem_Acris0_iff_span l e he s).1 hs) hs

theorem galC_sub_dvd_mem_nhds : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Acris l) (n : ℕ),
    {g : GQ l | (l : Per.Acris l) ^ n ∣ galC g x - x} ∈ nhds (1 : GQ l) := by
  intro l _ x n
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
  filter_upwards [algebraMap_mem_fixNear s n] with g ⟨u, hu⟩
  refine ⟨u + (galC g z - z), ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast]
  linear_combination hu

end GlobalTheory.AcrisGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_linear_retraction_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  first | exact @GlobalTheory.BKLim.AinfRetraction.main | exact GlobalTheory.BKLim.AinfRetraction.main | (intros; apply GlobalTheory.BKLim.AinfRetraction.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResidues
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PSer

theorem iterate_phiB_eB_symm (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (j : ℕ) (a : Formalism.Per.Acris l) :
    P.φB^[j] (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
        ((GlobalTheory.MemLoc.phiA l)^[j] a)) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have h1 : P.φB (T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) a)) =
        T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) (GlobalTheory.MemLoc.phiA l a)) := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact GlobalTheory.CrisMaps.φB_phiA l a
    rw [h1, ih]

theorem iterate_phiB_algebraMap_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (c : ℚ_[l]) (j : ℕ)
    (x : P.R.B) : P.φB^[j] (algebraMap ℚ_[l] P.R.B c * x) = algebraMap ℚ_[l] P.R.B c * P.φB^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes]

theorem series_residues : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) →
        ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
          ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y := by
  intro l _ P AI T
  obtain ⟨S, θ, Θ, hS, hθ1, hθc, hΘn, hΘt, hΘ⟩ := GlobalTheory.T.exists_theta_deRhamFiltration_acris l P AI T
  refine ⟨S, θ, hS, hθ1, hθc, ?_⟩
  intro h r y hh hr hy
  have hp : l.Prime := Fact.out
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hy 0)
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlpos hr
  have hNle : N ≤ l ^ (h * N) :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_left N (by omega)))
  have key : ∀ k, ‖sh (y k ^ l ^ (h * N))‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro k
    rw [(GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.2.2.1, norm_pow]
    calc ‖sh (y k)‖ ^ (l ^ (h * N)) ≤ r ^ (l ^ (h * N)) := pow_le_pow_left₀ (norm_nonneg _) (hy k) _
      _ ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hNle
      _ ≤ ‖(l : ℂ_[l])‖ := hN.le
  obtain ⟨w, hwφ, hwΘ⟩ := GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series l h (fun k => y k ^ l ^ (h * N)) hh key
  set c : ℚ_[l] := ((l : ℚ_[l]) ^ N)⁻¹ with hcdef
  set b' : P.R.B := T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) w) with hb'
  refine ⟨algebraMap ℚ_[l] P.R.B c * b', ?_, ?_, ?_⟩
  · refine ⟨N, w, ?_⟩
    have hc : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B c = 1 := by
      rw [← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_pow, ← map_mul, hcdef,
        mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one]
    rw [← mul_assoc, hc, one_mul, hb', RingEquiv.apply_symm_apply]
  · rw [iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, hwφ, map_mul, map_natCast, map_mul,
      map_natCast]
    ring
  · intro j
    obtain ⟨hm1, e1⟩ := hθc c
    obtain ⟨hm2, e2⟩ := hΘ ((GlobalTheory.MemLoc.phiA l)^[j] w)
    have heq : ev P j (algebraMap ℚ_[l] P.R.B c * b') = algebraMap ℚ_[l] P.R.BdR c *
        P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
          ((GlobalTheory.MemLoc.phiA l)^[j] w))) := by
      rw [ev, iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, map_mul, AlgHom.commutes]
    refine ⟨heq ▸ S.mul_mem hm1 hm2, ?_⟩
    have hsub : (⟨ev P j (algebraMap ℚ_[l] P.R.B c * b'), heq ▸ S.mul_mem hm1 hm2⟩ : ↥S) =
        ⟨algebraMap ℚ_[l] P.R.BdR c, hm1⟩ * ⟨_, hm2⟩ := Subtype.ext heq
    rw [hsub, map_mul, e1, e2, hwΘ Θ hΘn hΘt j,
      (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h j r y (by omega) hr hy).2.2.2 N, hcdef, map_inv₀, map_pow, map_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero))]

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLatticeFrameOfLinkedPreframeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinLatticeFrame_of_linked_preframe : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  first | exact @GlobalTheory.BKLim.frame_of_links | exact GlobalTheory.BKLim.frame_of_links | (intros; apply GlobalTheory.BKLim.frame_of_links <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefRingTaken_of_localisationCoefficientExtension : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → ∀ S : Set ℂ, Chosen N₀ A₀ i₀ S → Contains N₁ A₁ i₁ S → ∃ r ρ, GoodR N₁ i₁ r ∧ TakenWild N₁ i₁ r ρ := by
  first | exact @GlobalTheory.CoefDuty.Take.takenWild_of_locExt | exact GlobalTheory.CoefDuty.Take.takenWild_of_locExt | (intros; apply GlobalTheory.CoefDuty.Take.takenWild_of_locExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescen
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoeff

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l,
    (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  intro l _ a e _ h1 h2 LL
  refine ⟨?_, fun hU => ?_⟩
  · have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : FiniteDimensional ℚ_[l] ↥(Kunr l a) := (unrExt l a).2
    exact ⟨⟨LL.1 ⊔ Kunr l a, inferInstance⟩, le_sup_left, ⟨le_sup_right⟩⟩
  · obtain ⟨_, ω, hω, -, -⟩ := exists_gen l a
    have hlt := one_lt_pow_l l a
    have hmem : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
      rw [← Nat.sub_add_cancel hlt.le, pow_succ, hω.pow_eq_one, one_mul]))
    have he : e = l ^ a - 1 := by omega
    exact
      { succ_eq := h1
        not_dvd := h2
        finite := LL.2
        prim := ⟨⟨ω, hmem⟩, he ▸ (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val)
          Subtype.val_injective).1 hω⟩ }

end GlobalTheory.TameCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobeniusStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_coords_unramified_frobenius : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  first | exact @GlobalTheory.PMon.coef_unr_continuous | exact GlobalTheory.PMon.coef_unr_continuous | (intros; apply GlobalTheory.PMon.coef_unr_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZlStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_gen_degree_hom_to_Zl : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧ ν F = Multiplicative.ofAdd 1 ∧ (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  first | exact @GlobalTheory.UnramGen.exists_gen_degree | exact GlobalTheory.UnramGen.exists_gen_degree | (intros; apply GlobalTheory.UnramGen.exists_gen_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisMovesFlatByUnitRootStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_moves_flat_by_unit_root : ∀ (l : ℕ) [Fact l.Prime], (∀ (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x) → ∀ (K : FinExt l) (bk : BK K) (e : OCb l), e.untilt = 1 → ∃ g : ↥(GK K), Per.σF (g : GQ l) bk.flat = e * bk.flat := by
  first | exact @GlobalTheory.BSP.galois_moves_flat_by_unit_root | exact GlobalTheory.BSP.galois_moves_flat_by_unit_root | (intros; apply GlobalTheory.BSP.galois_moves_flat_by_unit_root; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_model_rep_coeffRing : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | exact GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep | (intros; apply GlobalTheory.IntegralModelOverCoeff.exists_integral_model_rep <;> assumption)
end


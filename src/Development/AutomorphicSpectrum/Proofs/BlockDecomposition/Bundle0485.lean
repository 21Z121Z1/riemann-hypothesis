import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0453
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal Topology

namespace GlobalTheory.CompanionTheory.QuotU

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def coset (U : Subgroup G) (r : G) : Set G := {x | r⁻¹ * x ∈ U}

theorem isOpen_coset {U : Subgroup G} (hU : IsOpen (U : Set G)) (r : G) : IsOpen (coset U r) :=
  hU.preimage (continuous_const.mul continuous_id)

theorem mem_coset_self (U : Subgroup G) (r : G) : r ∈ coset U r := by
  simp [coset, U.one_mem]

def conjSet (H U : Subgroup G) (r : G) : Set H := {h | r⁻¹ * (h : G) * r ∈ U}

theorem isOpen_conjSet {H U : Subgroup G} (hU : IsOpen (U : Set G)) (r : G) :
    IsOpen (conjSet H U r) :=
  hU.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem one_mem_conjSet (H U : Subgroup G) (r : G) : (1 : H) ∈ conjSet H U r := by
  simp [conjSet, U.one_mem]

theorem isCompact_conjSet {H U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hH : IsClosed (H : Set G)) (r : G) : IsCompact (conjSet H U r) := by
  have hK : IsCompact ((fun u => r * u * r⁻¹) '' (U : Set G)) :=
    hUc.image (by fun_prop)
  have hs : conjSet H U r = Subtype.val ⁻¹' ((fun u => r * u * r⁻¹) '' (U : Set G)) := by
    ext h
    constructor
    · intro hh
      exact ⟨_, hh, by group⟩
    · rintro ⟨u, hu, e⟩
      have e' : r⁻¹ * (h : G) * r = u := by
        have e2 : r * u * r⁻¹ = (h : G) := e
        rw [← e2]; group
      show r⁻¹ * (h : G) * r ∈ U
      rw [e']; exact hu
  rw [hs]
  exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK

theorem rep_eq_of_mem {H U : Subgroup G} {Rp : Set G}
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r')
    {r r' x : G} (hr : r ∈ Rp) (hr' : r' ∈ Rp) (hx : x ∈ coset U r) (hx' : x ∈ coset U r') :
    r = r' := by
  have h1 : r⁻¹ * x ∈ U := hx
  have h2 : r'⁻¹ * x ∈ U := hx'
  refine huniq r hr r' hr' ⟨1, H.one_mem, (r⁻¹ * x) * (r'⁻¹ * x)⁻¹,
    U.mul_mem h1 (U.inv_mem h2), by group⟩

theorem countable_reps [SecondCountableTopology G] {H U : Subgroup G} {Rp : Set G}
    (hU : IsOpen (U : Set G))
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    Countable Rp := by
  have hd : Rp.PairwiseDisjoint (coset U) := by
    intro r hr r' hr' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    exact rep_eq_of_mem huniq hr hr' hx hx'
  exact (hd.countable_of_isOpen (fun r _ => isOpen_coset hU r)
    (fun r _ => ⟨r, mem_coset_self U r⟩)).to_subtype

variable [MeasurableSpace G] [BorelSpace G]

noncomputable def rho {H : Subgroup G} (μH : Measure H) (U : Subgroup G) (Rp : Set G) (g : G) :
    ℝ≥0∞ :=
  ∑' r : Rp, (coset U (r : G)).indicator (fun _ => (μH (conjSet H U r))⁻¹) g

theorem rho_of_mem {H U : Subgroup G} {μH : Measure H} {Rp : Set G}
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r')
    {r x : G} (hr : r ∈ Rp) (hx : x ∈ coset U r) :
    rho μH U Rp x = (μH (conjSet H U r))⁻¹ := by
  rw [rho, tsum_eq_single (⟨r, hr⟩ : Rp)]
  · exact Set.indicator_of_mem hx _
  · intro r' hne
    refine Set.indicator_of_notMem (fun hx' => hne ?_) _
    exact Subtype.ext (rep_eq_of_mem huniq r'.2 hr hx' hx)

theorem rho_of_notMem {H U : Subgroup G} {μH : Measure H} {Rp : Set G} {x : G}
    (hx : ∀ r ∈ Rp, x ∉ coset U r) : rho μH U Rp x = 0 := by
  rw [rho]
  convert tsum_zero with r
  exact Set.indicator_of_notMem (hx r r.2) _

theorem measurable_rho {H U : Subgroup G} {μH : Measure H} {Rp : Set G} [Countable Rp]
    (hU : IsOpen (U : Set G)) : Measurable (rho μH U Rp) := by
  refine Measurable.ennreal_tsum fun r => ?_
  exact measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet

theorem rho_isQuotNormaliser [SecondCountableTopology G] {H U : Subgroup G} {μH : Measure H}
    [μH.IsHaarMeasure] {Rp : Set G}
    (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) (hH : IsClosed (H : Set G))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hcov : ∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ)
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    IsQuotNormaliser H μH (rho μH U Rp) := by
  haveI : Countable Rp := countable_reps hU huniq
  refine ⟨measurable_rho hU, fun g => ?_⟩
  obtain ⟨r, hr, h0, hh0, κ, hκ, rfl⟩ := hcov g
  have hpos : μH (conjSet H U r) ≠ 0 :=
    ((isOpen_conjSet hU r).measure_pos μH ⟨1, one_mem_conjSet H U r⟩).ne'
  have htop : μH (conjSet H U r) ≠ ∞ := (isCompact_conjSet hUc hH r).measure_lt_top.ne
  have hiff : ∀ h : H, (h : G) * (h0 * r * κ) ∈ coset U r ↔
      (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r := by
    intro h
    have e : r⁻¹ * ((h : G) * (h0 * r * κ)) = (r⁻¹ * (h0 * (h : G)) * r) * κ := by
      rw [show (h : G) * (h0 * r * κ) = ((h : G) * h0) * r * κ by group, hcomm _ h.2 _ hh0]
      group
    show r⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U ↔ r⁻¹ * (h0 * (h : G)) * r ∈ U
    rw [e]
    exact U.mul_mem_cancel_right hκ
  have hS : (fun h : H => rho μH U Rp ((h : G) * (h0 * r * κ))) =
      ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r).indicator
        (fun _ => (μH (conjSet H U r))⁻¹) := by
    funext h
    by_cases hm : (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r
    · rw [Set.indicator_of_mem (show h ∈ _ from hm)]
      exact rho_of_mem huniq hr ((hiff h).mpr hm)
    · rw [Set.indicator_of_notMem (show h ∉ _ from hm)]
      refine rho_of_notMem fun r' hr' hx => hm ((hiff h).mp ?_)
      have hu : r'⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U := hx
      have := huniq r hr r' hr' ⟨(h : G) * h0, H.mul_mem h.2 hh0,
        κ * (r'⁻¹ * ((h : G) * (h0 * r * κ)))⁻¹, U.mul_mem hκ (U.inv_mem hu), by group⟩
      rw [← this] at hx; exact hx
  have hmeas : MeasurableSet ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r) :=
    ((isOpen_conjSet hU r).preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hS, lintegral_indicator_const hmeas, measure_preimage_mul]
  exact ENNReal.inv_mul_cancel hpos htop

theorem measurable_of_right_invariant {U : Subgroup G} (hU : IsOpen (U : Set G))
    {Fn : G → ℝ≥0∞} (hFU : ∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) : Measurable Fn := by
  intro s _
  refine IsOpen.measurableSet (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  refine Filter.mem_of_superset ((isOpen_coset hU x).mem_nhds (mem_coset_self U x)) ?_
  intro y hy
  have : Fn (x * (x⁻¹ * y)) = Fn x := hFU x _ hy
  rw [mul_inv_cancel_left] at this
  show Fn y ∈ s
  rw [this]; exact hx

theorem quotLIntegral_eq_tsum [SecondCountableTopology G] [T2Space G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) [μG.IsHaarMeasure]
    (hH : IsClosed (H : Set G)) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) [μH.IsHaarMeasure]
    (Fn : G → ℝ≥0∞) (hFH : ∀ h ∈ H, ∀ g, Fn (h * g) = Fn g)
    (hFU : ∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) (Rp : Set G)
    (hcov : ∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ)
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    quotLIntegral μG H μH Fn =
      ∑' r : Rp, Fn r * μG (U : Set G) / μH {h : H | (r : G)⁻¹ * (h : G) * r ∈ U} := by
  haveI : LocallyCompactSpace G :=
    hUc.locallyCompactSpace_of_mem_nhds_of_group (hU.mem_nhds U.one_mem)
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : Countable Rp := countable_reps hU huniq
  haveI : μH.IsInvInvariant := by
    letI : CommGroup H := { (inferInstance : Group H) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
    haveI : μH.Regular := inferInstance
    exact Measure.IsHaarMeasure.isInvInvariant_of_regular μH
  have hFm : Measurable Fn := measurable_of_right_invariant hU hFU
  rw [quotLIntegral_eq hFm hFH (rho_isQuotNormaliser hU hUc hH hcomm hcov huniq)]
  have hpt : ∀ g, Fn g * rho μH U Rp g =
      ∑' r : Rp, (coset U (r : G)).indicator
        (fun _ => Fn r * (μH (conjSet H U r))⁻¹) g := by
    intro g
    rw [rho, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun r => ?_
    by_cases hg : g ∈ coset U (r : G)
    · have e : Fn ((r : G) * ((r : G)⁻¹ * g)) = Fn r := hFU _ _ hg
      rw [mul_inv_cancel_left] at e
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, e]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]
  rw [lintegral_congr hpt, lintegral_tsum]
  · refine tsum_congr fun r => ?_
    have hms : MeasurableSet (coset U (r : G)) := (isOpen_coset hU (r : G)).measurableSet
    have hvol : μG (coset U (r : G)) = μG (U : Set G) :=
      measure_preimage_mul μG (r : G)⁻¹ (U : Set G)
    rw [lintegral_indicator_const hms, hvol, div_eq_mul_inv, mul_right_comm]
    rfl
  · intro r
    exact (measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet).aemeasurable

end Abstract

theorem h2U : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  intro F _ _ _ _ n _ _ μG H μH U hUo hUc hμG hH hcomm hμH Fn hFH hFU Rp hcov huniq
  haveI := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_GL F n
  obtain ⟨_, _⟩ := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_t2_local_field F
  haveI : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  haveI : T2Space (GL (Fin n) F) := inferInstance
  exact quotLIntegral_eq_tsum μG H μH U hUo hUc hH hcomm Fn hFH hFU Rp hcov huniq

end GlobalTheory.CompanionTheory.QuotU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

open GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_val {a b : ℕ} (e : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k e m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst e
  rfl

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (Fin.cast (by omega) (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  show eGP (i + 1) t ((ePG i (t + 1)).symm (Fin.cast (by omega) (Fin.cast (by omega) (ePG i (t + 1) s)))) = _
  simp

theorem conj_entry (i t : ℕ) (r : GL (Fin ((i + 1) + t + 1)) k) (x y : Fin ((i + 1) + t + 1)) :
    (wGL k i t * r * (wGL k i t)⁻¹).val (piPerm i t x) (piPerm i t y) = r.val x y := by
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * r.val * Equiv.Perm.permMatrix k (piPerm i t)) _ _ = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

theorem conj_block (i t : ℕ) (h : Mir k (i + (t + 1))) (s s' : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    (wGL k i t * ((castM k (by omega) h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val
        (eGP (i + 1) t s) (eGP (i + 1) t s') =
      (h : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) s') := by
  rw [← piPerm_cast, ← piPerm_cast, conj_entry, castM_val]
  rfl

theorem eta_val (i t : ℕ) (m : Mir k ((i + 1) + t)) (x y : Fin ((i + 1) + t + 1 + 1)) :
    ((wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) :
        GL (Fin ((i + 1) + t + 1 + 1)) k).val x y =
      glEmbMat k ((i + 1) + t + 1) (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x y := by
  have e : wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ =
      levi k _ (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  rfl

theorem eta_mem (i t : ℕ) (h : HPG k i (t + 1)) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈
      HPG k (i + 1) (t + 1) := by
  have hh := mem_parab_iff.1 (show ((h : Mir k (i + (t + 1))) : GL (Fin (i + (t + 1) + 1)) k) ∈ parab k (ePG i (t + 1)) from h.2)
  show ((wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ :
    Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  intro x y b a hxy
  cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
  refine (eta_val i t _ _ _).trans ?_
  rw [ePG_true_eq]
  induction a using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact glEmbMat_cl k _ _ _
  | cast a =>
    rw [ePG_false_castSucc, glEmbMat_cc, conj_block]
    exact hh true false b a hxy

theorem eta_mem_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  intro k _ _ _ _ i t h
  refine ⟨eta_mem i t h, ?_⟩
  have hent : ∀ x z : Fin ((i + 1) + t + 1 + 1),
      ((hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩ : parab k (ePG (i + 1) (t + 1))) :
        GL (Fin ((i + 1) + (t + 1) + 1)) k).val x z =
        glEmbMat k ((i + 1) + t + 1) (wGL k i t * ((castM k (by omega) (h : Mir k (i + (t + 1))) : Mir k ((i + 1) + t)) :
          GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x z :=
    fun x z => eta_val i t _ x z
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) false).val a b =
      glEmbMat k (i + 1) (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) false).val a b
    rw [leviProj_apply, hent]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last]
        exact (glEmbMat_ll k _ _).trans (glEmbMat_ll k _ _).symm
      | cast b =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_lc k _ _ _).trans (glEmbMat_lc k _ _ _).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_cl k _ _ _).trans (glEmbMat_cl k _ _ _).symm
      | cast b =>
        rw [ePG_false_castSucc, ePG_false_castSucc, glEmbMat_cc, glEmbMat_cc, leviProj_apply, conj_block]
        rfl
  · apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) true).val a b =
      (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) true).val a b
    rw [leviProj_apply, hent, ePG_true_eq, ePG_true_eq, glEmbMat_cc, leviProj_apply, conj_block]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCell
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem piPerm_last_val (i t : ℕ) : ((piPerm i t (Fin.last ((i + 1) + t)) : Fin ((i + 1) + t + 1)) : ℕ) = i := by
  have key : ∀ x : Fin (i + (t + 1) + 1), (x : ℕ) = i + 1 + t →
      ((GlobalTheory.BZMir.Leib.eGP (i + 1) t ((GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm x) :
        Fin ((i + 1) + t + 1)) : ℕ) = i := by
    intro x hx
    have hxl : x = Fin.last (i + (t + 1)) := Fin.ext (by rw [Fin.val_last]; omega)
    subst hxl
    have h2 : (GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm (Fin.last (i + (t + 1))) =
        ⟨false, Fin.last i⟩ := by
      rw [Equiv.symm_apply_eq, GlobalTheory.BZMir.Leib.ePG_false_last]
    rw [h2]
    exact GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val (i + 1) t (Fin.last i)
  first
    | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]; exact key _ rfl)
    | exact key _ rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wEl_inv_entry (i t : ℕ) (c : Fin ((i + 1) + t + 1)) (hc : (c : ℕ) = i) :
    ((((wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1 := by
  have hσ : GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t (Fin.last ((i + 1) + t)) = c :=
    Fin.ext ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.piPerm_last_val i t).trans hc.symm)
  rw [GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv]
  change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
      (((GlobalTheory.CompanionTheory.BZPhiPG.wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
  change Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t) (Fin.last ((i + 1) + t)) c = 1
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  apply Subtype.ext
  change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
  rw [h, ofAdd_zero, map_one]

theorem wEl_notMem_Cl (i t : ℕ) : wEl k i t ∉ Cl k i t := by
  intro hmem
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hmem
  have h := hmem (Fin.last i)
  have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 1 + 1)) =
      Fin.castSucc (⟨i, by omega⟩ : Fin ((i + 1) + t + 1)) := Fin.ext rfl
  rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_inv_entry k i t ⟨i, by omega⟩ rfl] at h
  exact one_ne_zero h

theorem wEl_notMem_Cl_and_dEmb_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), wEl k i t ∉ Cl k i t ∧ dEmb k i t 0 = 1 := by
  intro k _ _ _ _ i t
  exact ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl k i t, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.dEmb_zero k i t⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {X : Type} [AddCommGroup X] [Module ℂ X]

def whitImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (T : Subrepresentation J) : Subrepresentation (whit2 ψ d J) :=
  ⟨T.toSubmodule.map (whitKer ψ d J).mkQ, fun g v hv => by
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨J (firstEmb d g) t, T.apply_mem_toSubmodule _ ht, rfl⟩⟩

theorem whitImg_mono (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {T T' : Subrepresentation J} (h : T' ≤ T) : whitImg ψ d J T' ≤ whitImg ψ d J T :=
  Submodule.map_mono (f := (whitKer ψ d J).mkQ) h

end

end GlobalTheory.CompanionTheory.BZNuPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockIntertwinersSpan
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def whitFirstLin (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : X 0 →ₗ[ℂ] (PiTensorProduct ℂ X ⧸ whitKer ψ d (piTensor ρ)) :=
  (whitKer ψ d (piTensor ρ)).mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v 0

theorem whitFirstLin_apply (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) (x : X 0) :
    whitFirstLin ψ d ρ v x = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ (Function.update v 0 x)) := rfl

def whitFirstMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)) :=
  .mk (whitFirstLin ψ d ρ v) (fun g => by
    ext x
    have h : ∀ a, Function.update v 0 (ρ 0 g x) a = ρ a (firstEmb d g a) (Function.update v 0 x a) :=
      Fin.forall_fin_two.2 ⟨by simp [firstEmb], by simp [firstEmb]⟩
    simp only [LinearMap.comp_apply, whitFirstLin_apply, whit2_mk, piTensor_tprod]
    rw [funext h])

theorem whit_iSup_range_eq_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d X _ _ ρ
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have hmem : Submodule.Quotient.mk (PiTensorProduct.tprod ℂ v) ∈
        ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap := by
      refine Submodule.mem_iSup_of_mem (whitFirstMap ψ d ρ v) (LinearMap.mem_range.2 ⟨v 0, ?_⟩)
      show whitFirstLin ψ d ρ v (v 0) = _
      rw [whitFirstLin_apply, Function.update_eq_self]
    rw [Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem _ r hmem
  | add a b ha hb =>
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ ha hb

end GlobalTheory.CompanionTheory.BZNuPair
end
end


import ReciprocityTheory.AnalyticForms.PotentialTheory.MIntSumCont
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveB

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartRestrOpen
section
namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]

omit [T2Space X] [CompactSpace X] in
theorem restrOpen_source' (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {V : Set X} (hV : IsOpen V) :
    (ψ.restrOpen V hV).source = ψ.source ∩ V := by
  rfl

omit [T2Space X] [CompactSpace X] in
theorem isCompatChart_restrOpen {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {V : Set X} (hV : IsOpen V) : IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro y ⟨hy1, hy2⟩
    have h' : (A.chart j).symm y ∈ ψ.source ∩ V := hy2
    exact ⟨hy1, h'.1⟩
  · rintro y ⟨hy1, hy2⟩
    have h' : y ∈ ψ.target ∩ ψ.symm ⁻¹' V := hy1
    exact ⟨h'.1, hy2⟩

theorem pl_exists_chart (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)) (hL : IsPotential A L)
    (hs : IsSection A L s) (hSNC : IsSNC A L s m W) (hB : ∀ k, HoloMap (B k) A Subtype.val)
    (Φ : Fin e → LocPot X) (hΦ : ∀ k, IsPotential A (Φ k)) (x : X) :
    ∃ ψ' : OpenPartialHomeomorph X (Fin (e + 1) → ℂ), IsCompatChart A ψ' ∧ x ∈ ψ'.source ∧
      ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ'.source →
        mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
          ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
            (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v := by
  classical
  obtain ⟨ψ, hψ, hx, hψL, σ, -, hWψ, u, hu, hu0, hsu⟩ := hSNC x
  have hsu' : ∀ y ∈ ψ.source, s x y = u y * ∏ k, (σ k).elim 1 (fun i => ψ y i ^ m k) := by
    intro y hy
    rw [hsu y hy]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases σ k with _ | i <;> rfl
  obtain ⟨V, hVdef⟩ : ∃ V : Set X, V = ψ.source ∩ (⋂ k, (Φ k).U x) ∩
      ⋂ k, (if x ∈ W k then Set.univ else (W k)ᶜ) := ⟨_, rfl⟩
  have hVo : IsOpen V := by
    rw [hVdef]
    refine (ψ.open_source.inter (isOpen_iInter_of_finite fun k => (Φ k).isOpen_U x)).inter
      (isOpen_iInter_of_finite fun k => ?_)
    split_ifs
    · exact isOpen_univ
    · exact (sncClosed A L s m W hSNC k).isOpen_compl
  have hxV : x ∈ V := by
    rw [hVdef]
    refine ⟨⟨hx, Set.mem_iInter.2 fun k => (Φ k).mem_U x⟩, Set.mem_iInter.2 fun k => ?_⟩
    split_ifs with h
    · exact Set.mem_univ _
    · exact h
  refine ⟨ψ.restrOpen V hVo, isCompatChart_restrOpen hψ hVo, ?_, fun v hv hvV => ?_⟩
  · rw [restrOpen_source']
    exact ⟨hx, hxV⟩
  · have hvV' : tsupport v ⊆ V := hvV.trans (by rw [restrOpen_source']; exact Set.inter_subset_right)
    refine pl_good A L s m W B hL hs hSNC hB Φ hΦ x ψ hψ hψL σ hWψ u hu hu0 hsu' hVo
      (fun p hp => by rw [hVdef] at hp; exact hp.1.1)
      (fun k p hp => by rw [hVdef] at hp; exact Set.mem_iInter.1 hp.1.2 k) (fun k hk => ?_) hv hvV'
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hpW
    rw [hVdef] at hp
    have := Set.mem_iInter.1 hp.2 k
    rw [if_neg hk] at this
    exact this hpW

theorem pl_global : PoincareLelongStatement := by
  intro e X _ _ _ A L s r m W B hL hs hSNC hB v hv Φ hΦ
  classical
  choose ψ hψ hxψ hpl using fun x => pl_exists_chart A L s m W B hL hs hSNC hB Φ hΦ x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source)
    (fun x => (ψ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, hxψ x⟩)
  have hcov : ∀ y, ∃ i, y ∈ (ψ (t.equivFin.symm i : X)).source := by
    intro y
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨t.equivFin ⟨x, hxt⟩, by simpa using hy⟩
  obtain ⟨AC, hAC, -, hAC2⟩ :=
    atlasOfCompat A (fun i => ψ (t.equivFin.symm i : X)) (fun i => hψ _) hcov
  obtain ⟨P⟩ := existsPartition AC
  obtain ⟨f, hf⟩ : ∃ f : Fin AC.n → X → ℝ, f = fun j p => P.χ j p * v p := ⟨_, rfl⟩
  have hfs : ∀ j, A.Smooth (f j) := by
    intro j
    have h1 : A.Smooth (P.χ j) := smoothOn_of_compatible ⟨hAC.2, hAC.1⟩ isOpen_univ (P.smooth j)
    rw [hf]
    exact smoothOn_mul h1 hv
  have hfpl : ∀ j, mInt A (Fin.cons (LocPot.ofFun (f j)) Φ) (logNormSec L s) =
      ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (f j ∘ Subtype.val) - mInt A (Fin.cons L Φ) (f j) := by
    intro j
    obtain ⟨i, hi⟩ := hAC2 j
    refine hpl (t.equivFin.symm i : X) (f j) (hfs j) ?_
    have h2 := P.tsupport_subset j
    rw [hi] at h2
    rw [hf]
    exact tsupport_mul_subset_left.trans h2
  have hvsum : v = fun p => ∑ j ∈ Finset.univ, f j p := by
    funext p
    rw [hf]
    simp only [← Finset.sum_mul, P.sum_eq_one, one_mul]
  have hpot : ∀ i, IsPotential A ((Fin.cons L Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hL
    · exact hΦ k
  have : ∀ k, CompactSpace (W k) := fun k =>
    isCompact_iff_compactSpace.1 (sncClosed A L s m W hSNC k).isCompact
  have hΦB : ∀ k i, IsPotential (B k) ((Φ i).pullback Subtype.val continuous_subtype_val) :=
    fun k i => isPotentialPullback A (B k) Subtype.val (hB k) (Φ i) (hΦ i)
  have hc : ∀ j, Continuous (f j) := fun j => smooth_continuous (hfs j)
  have hk : ∀ k, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
      ((fun p => ∑ j ∈ Finset.univ, f j p) ∘ Subtype.val) =
      ∑ j, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (f j ∘ Subtype.val) := fun k =>
    mInt_sum_cont (B k) _ (hΦB k) Finset.univ (fun j => f j ∘ Subtype.val)
      (fun j => (hc j).comp continuous_subtype_val)
  rw [hvsum, lhs_sum A L s (fun Φ' hΦ' => logNormIntegrable A L s m W hL hs hSNC Φ' hΦ') Φ hΦ
    Finset.univ f hfs, mInt_sum_cont A (Fin.cons L Φ) hpot Finset.univ f hc,
    Finset.sum_congr rfl fun j _ => hfpl j, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hk k, Finset.mul_sum]

end

end ReciprocityTheory.AnForm.M.PLAux
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurve
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def PLCurveLocalStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X)
    (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X),
    Function.Injective p → IsPotential A L → IsSection A L s → IsSNC A L s m (fun k => {p k}) →
    ∀ (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)), IsCompatChart A ψ →
    ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ.source →
      mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v

namespace PLC

variable {X : Type} [TopologicalSpace X]

theorem plDefect_add [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m (fun k => {p k}))
    {f f' : X → ℝ} (hf : A.Smooth f) (hf' : A.Smooth f') :
    plDefect A L s m p (fun z => f z + f' z) = plDefect A L s m p f + plDefect A L s m p f' := by
  have hPf := isPotential_ofFun A f hf
  have hPf' := isPotential_ofFun A f' hf'
  have hI : ∀ {h : X → ℝ}, IsPotential A (LocPot.ofFun h) →
      MIntegrable A (Fin.cons (LocPot.ofFun h) ![]) (logNormSec L s) := fun hP =>
    logNormIntegrable A L s m _ hL hs hsnc _ (Fin.forall_fin_one.2 hP)
  have h1 : mInt A ![LocPot.ofFun (fun z => f z + f' z)] (logNormSec L s) =
      mInt A ![LocPot.ofFun f] (logNormSec L s) + mInt A ![LocPot.ofFun f'] (logNormSec L s) := by
    exact (mInt_congr_phi A _ (Fin.cons (LocPot.ofFun f + LocPot.ofFun f') ![])
      (fun i a b => by fin_cases i; rfl) _).trans
      (mIntAdd (e := 0) A _ _ ![] hPf hPf' (fun i => i.elim0) _ (hI hPf) (hI hPf'))
  have hLp : ∀ i, IsPotential A (![L] i) := Fin.forall_fin_one.2 hL
  have h2 : mInt A ![L] (fun z => f z + f' z) = mInt A ![L] f + mInt A ![L] f' := by
    have := mIntLinear A ![L] hLp 1 f f' (mIntegrableCont A _ hLp f (continuous_of_smooth A hf))
      (mIntegrableCont A _ hLp f' (continuous_of_smooth A hf'))
    simpa using this
  unfold plDefect
  rw [h1, h2]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem plDefect_zero (A : FinHolAtlas 1 X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (p : Fin r → X) : plDefect A L s m p (fun _ => 0) = 0 := by
  unfold plDefect
  have h0 : mInt A ![LocPot.ofFun fun _ => (0 : ℝ)] (logNormSec L s) = 0 :=
    mIntConstPot (e := 0) A 0 ![] _
  rw [h0, mInt_zero]
  simp

theorem plc_global [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m (fun k => {p k}))
    (v : X → ℝ) (hv : A.Smooth v) :
    mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v := by
  classical
  choose ψ hψ hxψ hloc using fun x => plc_local A L s m p hL hs hsnc x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source)
    (fun x => (ψ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, hxψ x⟩)
  let F : Fin t.card → OpenPartialHomeomorph X (Fin 1 → ℂ) := fun i => ψ (t.equivFin.symm i)
  obtain ⟨B, hAB, -, hB⟩ := atlasOfCompat A F (fun i => hψ _) (by
    intro x
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [F] using hx⟩)
  obtain ⟨P⟩ := existsPartition B
  have hχ : ∀ j, A.Smooth (P.χ j) := fun j =>
    smoothOn_of_compatible hAB.symm' isOpen_univ (P.smooth j)
  have hpiece : ∀ j, plDefect A L s m p (fun z => P.χ j z * v z) = 0 := by
    intro j
    obtain ⟨i, hi⟩ := hB j
    have hsub : tsupport (P.χ j) ⊆ (ψ (t.equivFin.symm i)).source := by
      have := P.tsupport_subset j
      rwa [hi] at this
    have := hloc (t.equivFin.symm i) (fun z => P.χ j z * v z) (smooth_mul A (hχ j) hv)
      (tsupport_mul_subset_left.trans hsub)
    unfold plDefect
    rw [this]
    ring
  have hind : ∀ S : Finset (Fin B.n),
      plDefect A L s m p (fun z => ∑ j ∈ S, P.χ j z * v z) = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using plDefect_zero A L s m p
    · intro a S ha ih
      have hfun : (fun z => ∑ j ∈ insert a S, P.χ j z * v z) =
          fun z => P.χ a z * v z + ∑ j ∈ S, P.χ j z * v z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun, plDefect_add A L s m p hL hs hsnc (smooth_mul A (hχ a) hv)
        (smooth_sum A S fun j => smooth_mul A (hχ j) hv), hpiece a, ih, add_zero]
  have hv' : (fun z => ∑ j, P.χ j z * v z) = v := by
    funext z
    rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
  have h := hind Finset.univ
  rw [hv'] at h
  unfold plDefect at h
  linarith

end PLC

theorem plCurve : PoincareLelongCurveStatement := by
  intro X _ _ _ A L s r m p _ hL hs hsnc v hv
  exact PLC.plc_global A L s m p hL hs hsnc v hv

end

end ReciprocityTheory.AnForm.M
end


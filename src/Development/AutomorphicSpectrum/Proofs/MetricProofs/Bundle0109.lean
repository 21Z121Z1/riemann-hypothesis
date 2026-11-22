import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormLowerBoundNearCusp
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_flagPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), M.IsFrame F → b ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal b) → (∀ τ', IsBlockDiag j (h τ')) → M.blk p = some k → FC.plk M F b (FC.flagPt M F b h) p = minorIJ (h p.1) (stepCols N j p.2) (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h p k hF hb hG hh hp
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (CovMap.LocImg.stepCols_ne_empty M.j_le)
  have hI₀ : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
  have hdelta : ∀ J, IsStepRows N j p.2 J →
      ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b =
        if stepCols N j p.2 = J then 1 else 0 := by
    intro J hJ
    have hu' := fun m : ι k => (hG.2.1 ⟨k, m⟩ (stepCols N j p.2)).2
    have hu := fun m : ι k => (hG.2.1 ⟨k, m⟩ J).1
    have e1 := (CovMap.LocImg.reg_sum hb Finset.univ (fun m : ι k => F.u' (stepCols N j p.2) ⟨k, m⟩ * F.u ⟨k, m⟩ J)
      fun m _ => (CovMap.LocImg.reg_mul hb (hu' m) (hu m)).1).2
    rw [hF.2.2.1 p k hp _ J hI₀ hJ] at e1
    rw [Finset.sum_congr rfl fun m _ => ((CovMap.LocImg.reg_mul hb (hu' m) (hu m)).2).symm, ← e1]
    split_ifs
    · exact map_one (CovMap.LocImg.regVal M.x hb)
    · exact map_zero (CovMap.LocImg.regVal M.x hb)
  have e1 : FC.plk M F b (FC.flagPt M F b h) p =
      ∑ J, (∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b) *
        minorIJ (h p.1) J (stepCols N j p.2) := by
    simp only [FC.plk, hp, Option.elim_some]
    simp_rw [flagPt_step M F b h hp, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e1, Finset.sum_eq_single (stepCols N j p.2)]
  · rw [hdelta _ hI₀, if_pos rfl, one_mul]
  · intro J _ hne
    by_cases hJ : IsStepRows N j p.2 J
    · rw [hdelta J hJ, if_neg hne.symm, zero_mul]
    · rw [hoff J hJ, mul_zero]
  · simp

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PrimesBelowParams
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem {I : Ideal (MvPolynomial (Fin m) ℂ)} (t : Fin m → ℂ)
    {h : MvPolynomial (Fin m) ℂ} (hh : h ∈ I) : algebraMap _ (locRing I t) h = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) h) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hh

theorem map_ptIdeal_eq_maximalIdeal {I : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hI]
    simpa using RingHom.mem_ker.mp hg
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hI b).mpr hb
    have ha : a ∈ ptIdeal t := by
      refine RingHom.mem_ker.mpr ?_
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hI a).mpr hne
      rw [← hab] at hau
      exact ((IsLocalRing.mem_maximalIdeal _).mp hx) (isUnit_of_mul_isUnit_left hau)
    obtain ⟨v, hv⟩ := hbu.exists_right_inv
    have : x = algebraMap _ (locRing I t) a * v := by
      rw [← hab, mul_assoc, hv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

theorem chPrime_le_of_mem {I 𝔮 : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    {f : MvPolynomial (Fin m) ℂ} (h𝔮 : 𝔮.IsPrime) (hI𝔮 : I ≤ 𝔮) (h𝔮t : 𝔮 ≤ ptIdeal t)
    (hf : f ∈ 𝔮) : chPrime I t f ≤ 𝔮 := by
  intro g hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hg)
  obtain ⟨a₀, b₀, hb₀, hab⟩ := exists_mk_locRing I t a
  have hz : algebraMap _ (locRing I t) (b₀ * g - a₀ * f) = 0 := by
    rw [map_sub, map_mul, map_mul, ← ha, ← hab]
    ring
  obtain ⟨s, hs, hsI⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
  have hmem : (s * b₀) * g ∈ 𝔮 := by
    have h1 := 𝔮.add_mem (hI𝔮 hsI) (𝔮.mul_mem_left (s * a₀) hf)
    have h2 : s * (b₀ * g - a₀ * f) + s * a₀ * f = (s * b₀) * g := by ring
    rwa [h2] at h1
  refine (h𝔮.mem_or_mem hmem).resolve_left fun hc => ?_
  have := RingHom.mem_ker.mp (h𝔮t hc)
  rw [map_mul] at this
  exact mul_ne_zero hs hb₀ this

theorem primes_below_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  intro m e I Dc t r Jf hIDc hI hreg hdim hspan hDc i hi
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hmax := map_ptIdeal_eq_maximalIdeal hI
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := hspan.trans hmax
  have hprime : ∀ l, Prime (algebraMap _ (locRing I t) (r l)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnassoc := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hIt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hRi : r i ∈ chPrime I t (r i) := Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  have hle : chPrime I t (r i) ≤ ptIdeal t := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) (r i)} :=
      Ideal.mem_comap.mp hg
    have hsub : Ideal.span {algebraMap _ (locRing I t) (r i)} ≤ IsLocalRing.maximalIdeal (locRing I t) := by
      rw [Ideal.span_singleton_le_iff_mem, ← hspan']
      exact Ideal.subset_span ⟨i, rfl⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp (hsub hg')
    refine RingHom.mem_ker.mpr ?_
    by_contra hne
    exact hnu ((isUnit_algebraMap_locRing_iff I t hI g).mpr hne)
  have hpr : (chPrime I t (r i)).IsPrime := by
    haveI : (Ideal.span {algebraMap _ (locRing I t) (r i)}).IsPrime :=
      (Ideal.span_singleton_prime (hprime i).ne_zero).mpr (hprime i)
    exact Ideal.comap_isPrime _ _
  have hIle : I ≤ chPrime I t (r i) := by
    intro h hh
    refine Ideal.mem_comap.mpr ?_
    rw [algebraMap_locRing_eq_zero_of_mem t hh]
    exact Ideal.zero_mem _
  refine ⟨hpr, hIle, hle, (hDc _ hpr hIle hle).mpr ⟨i, hi, hRi⟩, hRi, ?_, ?_⟩
  · intro j _ hji hj
    have hd : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (r j) :=
      Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hj)
    exact hnassoc i j (Ne.symm hji) ((hprime i).associated_of_dvd (hprime j) hd)
  · intro 𝔮 h𝔮 hI𝔮 h𝔮t hr
    exact chPrime_le_of_mem h𝔮 hI𝔮 h𝔮t hr

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotential
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos

theorem isPsh_add_zero_add (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  unfold ReciprocityTheory.AnForm.M.IsPsh
  intro x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _
    rw [smul_eq_mul]
    ring
  have hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v =
      2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v := by
    intro z v
    unfold ReciprocityTheory.AnForm.levi
    have h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) =
        (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm) := fderiv_const_smul_of_field (2 : ℝ)
    have h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) =
        (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) := fderiv_const_smul_of_field (2 : ℝ)
    rw [h1, h2]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hfun, hlevi]
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi]
  · exact mul_nonneg (by norm_num) (hpos x j y hy' w hw).le

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRing
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ I) : algebraMap _ (locRing I t) a = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) a) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

theorem map_ptIdeal_eq_maximalIdeal (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hp : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hp, not_not]
    exact RingHom.mem_ker.mp ha
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hp b).mpr hb
    have hxn : ¬ IsUnit x := hx
    have ha : eval t a = 0 := by
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hp a).mpr hne
      rw [← hab] at hau
      exact hxn (isUnit_of_mul_isUnit_left hau)
    obtain ⟨u, hu⟩ := hbu
    have hx' : x = algebraMap _ (locRing I t) a * ↑u⁻¹ := by
      rw [← hab, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exists_den_of_mem_map (I D : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (hID : I ≤ D)
    (hp : ∀ h ∈ I, eval t h = 0) {f : MvPolynomial (Fin m) ℂ}
    (hf : algebraMap _ (locRing I t) f ∈ Ideal.map (algebraMap _ (locRing I t)) D) :
    ∃ s, eval t s ≠ 0 ∧ s * f ∈ D := by
  have key : ∀ x ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) D,
      ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧ x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧
      x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, ha, 1, by simp, by simp⟩
    · exact ⟨0, D.zero_mem, 1, by simp, by simp⟩
    · rintro x y _ _ ⟨a, ha, b, hb, hab⟩ ⟨c, hc, d, hd, hcd⟩
      refine ⟨a * d + c * b, D.add_mem (D.mul_mem_right _ ha) (D.mul_mem_right _ hc), b * d,
        by simpa using ⟨hb, hd⟩, ?_⟩
      simp only [map_add, map_mul, ← hab, ← hcd]
      ring
    · rintro c x _ ⟨a, ha, b, hb, hab⟩
      obtain ⟨u, v, hv, huv⟩ := exists_mk_locRing I t c
      refine ⟨u * a, D.mul_mem_left _ ha, v * b, by simpa using ⟨hv, hb⟩, ?_⟩
      simp only [smul_eq_mul, map_mul, ← hab, ← huv]
      ring
  obtain ⟨a, ha, b, hb, hab⟩ := key _ hf
  have h0 : algebraMap _ (locRing I t) (f * b - a) = 0 := by
    rw [map_sub, map_mul, hab, sub_self]
  obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
  refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
  have : s * b * f = s * (f * b - a) + s * a := by ring
  rw [this]
  exact D.add_mem (hID hsm) (D.mul_mem_left _ ha)

theorem radical_span_prod_eq {O ι : Type*} [CommRing O] [IsDomain O] (R : ι → O) (J : Finset ι)
    (hpr : ∀ i, Prime (R i)) (hna : ∀ i j, i ≠ j → ¬ Associated (R i) (R j)) :
    (Ideal.span {∏ i ∈ J, R i}).radical = Ideal.span {∏ i ∈ J, R i} := by
  classical
  apply le_antisymm _ Ideal.le_radical
  rintro g ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  have hdiv : ∀ i ∈ J, R i ∣ g := fun i hi =>
    (hpr i).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem R hi).trans hn)
  clear hn
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨c, rfl⟩ := ih fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    have hac := hdiv a (Finset.mem_insert_self _ _)
    rcases (hpr a).dvd_or_dvd hac with h | h
    · exfalso
      obtain ⟨j, hj, hd⟩ := (Prime.exists_mem_finset_dvd (hpr a) h)
      have hne : a ≠ j := fun e => ha (e ▸ hj)
      exact hna a j hne (((hpr a).dvd_prime_iff_associated (hpr j)).mp hd)
    · obtain ⟨d, rfl⟩ := h
      exact ⟨d, by ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

theorem exists_den_prod_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  classical
  intro m e I Dc t r Jf hID hp hreg hdim hspan hprime
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  set alg : MvPolynomial (Fin m) ℂ →+* locRing I t := algebraMap _ (locRing I t) with halg
  set R : Fin e → locRing I t := fun l => alg (r l) with hR
  have hspan' : Ideal.span (Set.range R) = IsLocalRing.maximalIdeal (locRing I t) := by
    rw [← map_ptIdeal_eq_maximalIdeal I t hp]
    exact hspan
  have hpr : ∀ i, Prime (R i) := prime_of_regular_params R hspan' hdim.symm
  have hna := (regular_params_spec R hspan' hdim.symm).2
  set Q : MvPolynomial (Fin m) ℂ := ∏ l ∈ Jf, r l with hQ
  have hPQ : alg Q = ∏ l ∈ Jf, R l := map_prod alg _ _

  have hpr2 : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (Ideal.map alg Dc ≤ 𝔓 ↔ alg Q ∈ 𝔓) := by
    intro 𝔓 h𝔓
    have hq1 : (Ideal.comap alg 𝔓).IsPrime := Ideal.comap_isPrime alg 𝔓
    have hq2 : I ≤ Ideal.comap alg 𝔓 := fun a ha => by
      rw [Ideal.mem_comap, halg, algebraMap_locRing_eq_zero_of_mem I t ha]
      exact 𝔓.zero_mem
    have hq3 : Ideal.comap alg 𝔓 ≤ ptIdeal t := fun a ha => by
      by_contra hne
      have hu := (isUnit_algebraMap_locRing_iff I t hp a).mpr fun h => hne (RingHom.mem_ker.mpr h)
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    rw [Ideal.map_le_iff_le_comap, hprime _ hq1 hq2 hq3, hPQ, Ideal.IsPrime.prod_mem_iff]
    rfl
  have hrad : (Ideal.map alg Dc).radical = Ideal.span {alg Q} := by
    rw [hPQ, ← radical_span_prod_eq R Jf hpr hna, ← hPQ, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
    congr 1
    ext 𝔓
    simp only [Set.mem_setOf_eq, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mpr h1, h2⟩⟩

  obtain ⟨h', hh', hQrad⟩ : ∃ h', eval t h' ≠ 0 ∧ h' * Q ∈ Dc.radical := by
    have h1 : alg Q ∈ (Ideal.map alg Dc).radical := by
      rw [hrad]; exact Ideal.mem_span_singleton_self _
    obtain ⟨N, hN⟩ := h1
    rw [← map_pow] at hN
    obtain ⟨s, hs, hsm⟩ := exists_den_of_mem_map I Dc t hID hp hN
    refine ⟨s, hs, N + 1, ?_⟩
    have : (s * Q) ^ (N + 1) = s ^ N * Q * (s * Q ^ N) := by ring
    rw [this]
    exact Dc.mul_mem_left _ hsm

  have hone : ∀ g ∈ Dc.radical, ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := by
    rintro g ⟨n, hn⟩
    have h1 : alg g ∈ (Ideal.map alg Dc).radical :=
      ⟨n, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hn⟩
    rw [hrad, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t c
    have h0 : algebraMap _ (locRing I t) (g * b - Q * a) = 0 := by
      change alg (g * b - Q * a) = 0
      have hab' : c * alg b = alg a := hab
      rw [map_sub, map_mul, map_mul, hc, ← hab']
      ring
    obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
    have : s * b * g = s * (g * b - Q * a) + Q * (s * a) := by ring
    rw [this, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right hsm)

  obtain ⟨S, hS⟩ : Dc.radical.FG := IsNoetherian.noetherian _
  have hSm : ∀ g, g ∈ S → ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := fun g hg =>
    hone g (hS ▸ Submodule.subset_span hg)
  choose! f hf0 hf1 using hSm
  set H : MvPolynomial (Fin m) ℂ := ∏ g ∈ S, f g with hH
  have hH0 : eval t H ≠ 0 := by
    rw [hH, map_prod]
    exact Finset.prod_ne_zero_iff.mpr hf0
  have hHS : Dc.radical ≤
      Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin m) ℂ) H) (Ideal.span {Q} ⊔ I) := by
    rw [← hS]
    refine Submodule.span_le.mpr fun g hg => ?_
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem f hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    rw [hH, hw, mul_comm (f g) w, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hf1 g hg)
  refine ⟨h' * H, by simpa using ⟨hh', hH0⟩, ?_, fun g hg => ?_⟩
  · have : h' * H * Q = H * (h' * Q) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hQrad
  · have h1 := hHS hg
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ h1

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoUniformly
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem tendstoUniformlyOn_regWeight_of_isTied :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ J _ P n M Xo A S hS K' hK'Y hK'
  refine hK'.induction_on (p := fun s => TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) s)
    ?_ ?_ ?_ ?_
  · intro u _
    simp
  · intro s t hst ht
    exact ht.mono hst
  · intro s t hs ht
    intro u hu
    filter_upwards [hs u hu, ht u hu] with a ha hb y hy
    exact hy.elim (ha y) (hb y)
  · intro x hx
    obtain ⟨j, hj⟩ := M.atlas.cover x
    have hopen : (M.atlas.chart j).source ∈ 𝓝 x := (M.atlas.chart j).open_source.mem_nhds hj
    obtain ⟨C, hCn, hCs, hCc⟩ := local_compact_nhds hopen
    refine ⟨C ∩ K', ?_, ?_⟩
    · exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hCn) self_mem_nhdsWithin
    · have hcpt : IsCompact (C ∩ K') := hCc.inter hK'
      have himg : IsCompact ((M.atlas.chart j) '' (C ∩ K')) :=
        hcpt.image_of_continuousOn
          ((M.atlas.chart j).continuousOn.mono fun y hy => hCs hy.1)
      have hsub : (M.atlas.chart j) '' (C ∩ K') ⊆
          (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨(M.atlas.chart j).map_source (hCs hy.1), ?_⟩
        show (M.atlas.chart j).symm ((M.atlas.chart j) y) ∈ S.R.Yo
        rw [(M.atlas.chart j).left_inv (hCs hy.1)]
        exact hK'Y hy.2
      have hu := (GlobalTheory.T.regularized_weight_tendsto_C2 K J P n M Xo A S hS j _ hsub himg).1
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with t ht y hy
      have h := ht _ (Set.mem_image_of_mem _ hy)
      simpa [Function.comp, (M.atlas.chart j).left_inv (hCs hy.1)] using h

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompact
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ ι _ P n M Xo B S hS K' hK' hc
  have hYo : IsOpen S.R.Yo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas S.R).1
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc]
  intro u hu x hx
  obtain ⟨j, hj⟩ := M.atlas.cover x
  have hO : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm hYo
  have hy : M.atlas.chart j x ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    ⟨(M.atlas.chart j).map_source hj, by
      simpa [Set.mem_preimage, (M.atlas.chart j).left_inv hj] using hK' hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hy
  have hsub : Metric.closedBall (M.atlas.chart j x) (ε / 2) ⊆
      (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hU := (GlobalTheory.T.regularized_weight_tendsto_C2 K ι P n M Xo B S hS j _ hsub (isCompact_closedBall _ _)).1
  refine ⟨(M.atlas.chart j).source ∩ (M.atlas.chart j) ⁻¹' Metric.ball (M.atlas.chart j x) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (((M.atlas.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hj, by simp [hε]⟩), ?_⟩
  filter_upwards [hU u hu] with t ht y hy'
  have h := ht (M.atlas.chart j y) (Metric.ball_subset_closedBall hy'.2)
  simpa [Function.comp, (M.atlas.chart j).left_inv hy'.1] using h

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormLowerBoundNearCuspStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_lower_bound_near_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (L : ActPeriods E n a g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsCMFam σ → 1 ≤ m → IsEigFrames (Metric.ball 0 1) L.B σ b → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < ρ → 1 ≤ C * Flat.logSize a (expCover a w) * (L.riem w hw).lam1 ^ 2 ∧ (L.riem w hw).cuspW σ ≤ C * (1 + Real.log (Flat.logSize a (expCover a w))) ∧ |(L.riem w hw).logDet (fun τ i => b τ i (expCover a w))| ≤ C * (1 + Real.log (Flat.logSize a (expCover a w))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound | exact GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.uLogBound <;> assumption)
end


import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0030

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointSurj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section

open CurveVerticalPointSurjective in

theorem CurveVertPointSurj.proof (hFin : CurveRingFinite.Statement) (hC : CurveClosedPointChart.Statement) :
    CurveVertPointSurj.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP m hm hlen
  have hfin := hFin K ι Ω y hP
  obtain ⟨c, hyc, hrat⟩ := hC K ι Ω y hP m hm
  have hrat' := hrat
  have : m.IsPrime := hm.isPrime
  have hYne : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)

  have hunit : ∀ b : m.primeCompl, IsUnit ((curveRing y).subtype (b : curveRing y)) := by
    intro b
    refine isUnit_iff_ne_zero.mpr fun h => b.2 ?_
    have hb0 : (b : curveRing y) = 0 := Subtype.ext h
    rw [hb0]
    exact m.zero_mem
  let L := Localization.AtPrime m
  let φ : L →+* Ω := IsLocalization.lift hunit
  have hinj0 : Function.Injective (algebraMap (curveRing y) L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors m)
  have hφinj : Function.Injective φ :=
    (IsLocalization.lift_injective_iff hunit).mpr fun x x' =>
      ⟨fun h => by rw [hinj0 h], fun h => by rw [Subtype.val_injective h]⟩
  have hφB : ∀ x : curveRing y, φ (algebraMap _ L x) = x := fun x => IsLocalization.lift_eq hunit x
  have hφmk : ∀ (a : curveRing y) (b : m.primeCompl) (v : Ω),
      φ (IsLocalization.mk' L a b) = v ↔ (a : Ω) = ((b : curveRing y) : Ω) * v :=
    fun a b v => IsLocalization.lift_mk'_spec hunit a v b

  choose α β hβ hαβ using hrat
  let ρ : (Σ k, ι k) → L := fun p => IsLocalization.mk' L (α p) (⟨β p, hβ p⟩ : m.primeCompl)
  have hφρ : ∀ p, φ (ρ p) = y p / y ⟨p.1, c p.1⟩ := fun p => (hφmk _ _ _).mpr (hαβ p).symm
  have hφev : ∀ {g : MRing ι} {e : K → ℕ}, IsMultiHomog g e →
      φ (aeval ρ g) = aeval y g * (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro g e hg
    rw [ringHom_aeval φ ρ g, show (fun p => φ (ρ p)) = fun p => y p / y ⟨p.1, c p.1⟩ from funext hφρ]
    exact CurveVerticalPointResidue.aeval_div y c g e hg
  have hevB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → aeval ρ g = algebraMap _ L x := by
    intro g e x hg hgx
    apply hφinj
    rw [hφev hg, hφB, hgx, mul_assoc, mul_inv_cancel₀ (hYne e), mul_one]

  let r : (Σ k, ι k) → IsLocalRing.ResidueField L := fun p => IsLocalRing.residue L (ρ p)
  have hWform : ∀ {g : MRing ι} {e : K → ℕ}, IsMultiHomog g e →
      (g ∈ mCoordIdeal r ↔ aeval ρ g ∈ IsLocalRing.maximalIdeal L) := by
    intro g e hg
    rw [mem_mCoordIdeal_iff r hg, ← IsLocalRing.residue_eq_zero_iff, ringHom_aeval]
  have hWB : ∀ {g : MRing ι} {e : K → ℕ} (x : curveRing y), IsMultiHomog g e →
      aeval y g = (x : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ mCoordIdeal r ↔ x ∈ m) := by
    intro g e x hg hgx
    rw [hWform hg, hevB x hg hgx]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff L m x
  have hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal r := by
    intro k
    have hρ1 : ρ ⟨k, c k⟩ = 1 := hφinj (by rw [hφρ, map_one, div_self (hyc k)])
    rw [hWform (homog_X ⟨k, c k⟩), aeval_X, hρ1]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hWprime : (mCoordIdeal r).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal y ≤ mCoordIdeal r := by
    obtain ⟨S, hS, hPS⟩ := CoordinateConeArithVar.isMultiHomogIdeal y
    intro f hfP
    rw [hPS] at hfP
    refine (Ideal.span_le.mpr ?_) hfP
    intro f hf
    obtain ⟨e, he⟩ := hS f hf
    have hfP' : f ∈ mCoordIdeal y := by rw [hPS]; exact Ideal.subset_span hf
    have hf0 : aeval y f = ((0 : curveRing y) : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [(mem_mCoordIdeal_iff y he).mp hfP']
      simp
    exact (hWB 0 he hf0).mpr m.zero_mem

  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ s)
  dsimp only at hab
  have hbx : ((b : curveRing y) : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k := by
    have h1 := hφev hs
    rw [← hab] at h1
    rw [(hφmk a b _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne d)]
  have hlenA : locLen m (curveRing y ⧸ Ideal.span {a}) ≠ 0 := by
    rwa [← CurveSectionQuotLocal.proof K ι Ω y s d hP hs hsP m c hm.isPrime hyc hrat' a b b.2 hbx]
  have ham : a ∈ m := by
    by_contra h
    exact hlenA (locLen_quot_eq_zero m h)
  have hsW : s ∈ mCoordIdeal r := by
    rw [hWform hs, ← hab]
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a b).mpr ham
  have hJW : mCoordIdeal y ⊔ Ideal.span {s} ≤ mCoordIdeal r :=
    sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)

  have hcurve : curvePtIdeal y (mCoordIdeal r) = m := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro x ⟨e, g, h, hg, hh, hgW, hhW, hx⟩
      have heq : algebraMap _ L x * aeval ρ h = aeval ρ g := by
        apply hφinj
        rw [map_mul, hφB, hφev hh, hφev hg, ← hx]
        ring
      have hmem : algebraMap _ L x * aeval ρ h ∈ IsLocalRing.maximalIdeal L := by
        rw [heq]
        exact (hWform hg).mp hgW
      rcases (IsLocalRing.maximalIdeal.isMaximal L).isPrime.mem_or_mem hmem with h1 | h1
      · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L m x).mp h1
      · exact absurd ((hWform hh).mpr h1) hhW
    · intro x hx
      obtain ⟨e, g, hg, hgx⟩ := exists_form y c hyc x
      have hgW : g ∈ mCoordIdeal r := (hWB x hg hgx).mpr hx
      have hXW : chartMon c e ∉ mCoordIdeal r := chartMon_notMem hWprime hXc e
      have hval : (x : Ω) * aeval y (chartMon c e) = aeval y g := by
        rw [aeval_chartMon, hgx]
      have key : x ∈ {b : curveRing y | ∃ (d : K → ℕ) (g h : MRing ι),
          IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ mCoordIdeal r ∧ h ∉ mCoordIdeal r ∧
            (b : Ω) * aeval y h = aeval y g} :=
        ⟨e, g, chartMon c e, hg, homog_chartMon c e, hgW, hXW, hval⟩
      exact Ideal.subset_span key
  have ha0 : a ≠ 0 := by
    intro h0
    have hx0 : aeval y s ≠ 0 := fun h => hsP ((mem_mCoordIdeal_iff y hs).mpr h)
    have hb0 : ((b : curveRing y) : Ω) ≠ 0 := by
      intro h
      apply b.2
      rw [show (b : curveRing y) = 0 from Subtype.ext h]
      exact m.zero_mem
    have h2 := hbx
    rw [h0, ZeroMemClass.coe_zero, zero_mul] at h2
    exact mul_ne_zero hb0 hx0 h2
  have hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, IsMultiHomog f n → f ∈ mCoordIdeal r →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧
        (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k := by
    intro f n hf hfW
    obtain ⟨⟨a', b'⟩, hab'⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval ρ f)
    dsimp only at hab'
    refine ⟨a', b', ?_, b'.2, ?_⟩
    · have h1 := (hWform hf).mp hfW
      rw [← hab'] at h1
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff L m a' b').mp h1
    · have h1 := hφev hf
      rw [← hab'] at h1
      rw [(hφmk a' b' _).mp h1, mul_assoc, inv_mul_cancel_right₀ (hYne n)]

  have hmin : ∀ Q : Ideal (MRing ι), Q.IsPrime → mCoordIdeal y ⊔ Ideal.span {s} ≤ Q →
      Q ≤ mCoordIdeal r → mCoordIdeal r ≤ Q := by
    intro Q hQ hJQ hQW
    have hPQ : mCoordIdeal y ≤ Q := le_trans le_sup_left hJQ
    have hsQ : s ∈ Q := hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    exact le_of_minimal y c hyc hfin m hm (mCoordIdeal r) Q hQ hPQ hQW hXc hWB hWfrac
      (CoordinateConeArithVar.isMultiHomogIdeal r) ha0 hs hsQ hbx
  have hmp : mCoordIdeal r ∈ (mCoordIdeal y ⊔ Ideal.span {s}).minimalPrimes :=
    ⟨⟨hWprime, hJW⟩, fun Q hQ hQW => hmin Q hQ.1 hQ.2 hQW⟩
  exact ⟨mCoordIdeal r, ⟨hmp, fun k => ⟨c k, hXc k⟩⟩, hcurve⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)

namespace GoodChartDim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreCone (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, x = fun a => segre z (σ a)}

theorem segreCone_smul {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ segreCone P σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ segreCone P σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := GoodChartZeroSet.exists_segre_smul P hP.2.1.2.1 hz ha
    (fun h => absurd hP.1 (not_nonempty_iff.2 h))
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩

open Classical in

def psiCoeffs {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin m → ℂ :=
  fun a => Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0

theorem projChartSet_eq (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩

theorem linForm_single' {m : ℕ} (a : Fin m) : linForm (Pi.single a (1 : ℂ)) = X a := by
  classical
  simp [linForm, Pi.single_apply]

omit [∀ k, Fintype (ι k)] in

theorem segreChartSet_eq (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [segreChartSet, segreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

theorem linForm_sub_one_not_mem {m : ℕ} {V : Ideal (MvPolynomial (Fin m) ℂ)} (hV : IsHomogIdeal V) (hne : V ≠ ⊤)
    (t : Fin m → ℂ) : linForm t - 1 ∉ V := by
  intro h
  have h0 := hV _ h 0
  rw [homogeneousComponent_zero] at h0
  have hc : coeff 0 (linForm t - 1) = -1 := by
    simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
  rw [hc] at h0
  exact hne (Ideal.eq_top_of_isUnit_mem _ h0 (by simp))

theorem exists_X_not_mem {m : ℕ} {W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (h : linForm t ∉ W) :
    ∃ a, X a ∉ W := by
  by_contra hall
  push Not at hall
  exact h (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hall a))

theorem le_of_homog_le_sup {m : ℕ} {V W : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (hle : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof ℂ m W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d f) (hle (hV f hf d))

theorem eq_of_add_one_eq {x : WithBot ℕ∞} {e : ℕ} (h : x + 1 = (e : WithBot ℕ∞) + 1) : x = e := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← Nat.cast_succ] at h
    exact absurd h (WithBot.bot_ne_natCast _)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((e + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_inj, top_add] at h'
      exact absurd h' (by exact_mod_cast (ENat.top_ne_natCast (e + 1)))
    | coe x =>
      have h' : ((x + 1 : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h'' : x + 1 = e + 1 := by exact_mod_cast h'
      exact_mod_cast (show x = e by omega)

end GoodChartDim

open GoodChartDim

theorem GoodChartDim.proof (h₁ : ConeVanishingHomog.Statement) (h₂ : ConeSliceIdeal.Statement)
    (h₃ : ChartDehomogPrime.Statement) : GoodChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ Ψ hP J hJ
  have hC := segreCone_smul hP σ
  set t := psiCoeffs σ Ψ
  have hS : projChartSet P σ Ψ = {x | x ∈ segreCone P σ ∧ eval x (linForm t) = 1} := projChartSet_eq P σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : projChartIdeal P σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (segreCone P σ)
  have hH : IsHomogIdeal H := h₁ m _ hC
  have hHI : H ≤ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : linForm t - 1 ∈ projChartIdeal P σ Ψ := by
    rw [projChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : segreChartSet P σ (σ a) = {x | x ∈ segreCone P σ ∧ eval x (linForm u) = 1} :=
    segreChartSet_eq P σ a

  have := h₃ ℂ m W u hW huW
  have hTJ' : segreChartIdeal P σ (σ a) ≤ W ⊔ Ideal.span {linForm u - 1} := by
    rw [segreChartIdeal, hT]; exact h₂ m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := SegreChartDim.proof K ι P e m σ (σ a) hP Q₀ (mem_segreChartComponents.2 hQ₀)
  have hu1 : linForm u - 1 ∈ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ segreChartIdeal P σ (σ a) := by
    rw [segreChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : projChartIdeal P σ Ψ ≤ V ⊔ Ideal.span {linForm t - 1} := by
    rw [projChartIdeal, hS]; exact h₂ m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar)

theorem PtsChartDim.proof : PtsChartDim.Statement := by
  classical
  intro K _ ι _ P e i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩

  let g : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
    (rename (PtsSegreChart.coordEquiv (ι := ι))).toRingHom
  let f : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →+* MvPolynomial (Σ k, ι k) ℂ :=
    (rename (PtsSegreChart.coordEquiv (ι := ι)).symm).toRingHom
  have hfg : ∀ b, f (g b) = b := fun b => by simp [f, g, rename_rename]
  have hgf : ∀ a, g (f a) = a := fun a => by simp [f, g, rename_rename]
  have hI : PtsSegreChart.ideal P i = (ReciprocityTheory.AnForm.R.chartIdeal PC i).map g := by
    rw [PtsSegreChart.ideal, ReciprocityTheory.AnForm.R.chartIdeal, Ideal.map_sup, Ideal.map_span, hPC, Ideal.map_map,
      ← Set.range_comp]
    congr 3
    funext k
    simp [g]
  obtain ⟨hmin, hd⟩ := SegreChartDim.minimalPrimes_transfer f g (PtsSegreChart.ideal P i)
    (ReciprocityTheory.AnForm.R.chartIdeal PC i)
    (by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_comap, hfg]
      exact hb)
    (by rw [hI]; exact Ideal.le_comap_map)
    (fun a => by rw [hgf, sub_self]; exact Ideal.zero_mem _)
    (fun b => by rw [hfg, sub_self]; exact Ideal.zero_mem _) J hJ
  rw [hd]
  exact SegreChartDim.ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin

end GroundTheory.Heights₂.Heights
end
end


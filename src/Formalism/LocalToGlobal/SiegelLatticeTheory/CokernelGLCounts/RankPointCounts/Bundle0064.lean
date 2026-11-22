import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0061
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0062

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieFD
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieFD

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Pf.AlTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

def DiscriminantAbsEq : Prop := |(NumberField.discr X.B.I.F : ℝ)| = |(NumberField.discr D.host.F : ℝ)|

def InfinitePlacesCardEq : Prop := Fintype.card (NumberField.InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F

def EulerProductEta : Prop :=
  ∀ i : ℕ, 2 ≤ i → HasProd (fun v : PlX X =>
      (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)⁻¹)
      (Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i)

def LocalFactorProduct : Prop :=
  HasProd (fun v : PlX X => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k else 1)
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1))

def VInvEqHalfRootDiscriminant : Prop :=
  Formalism.HermitianLatticesTheory.vInv D.host.E = |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2

def QuadraticInfinitePlaces : Prop := Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F

def DifferentGeneratorUnit : Prop := ∀ p : TypX X, absV p.1 (dV p.1) = 1

def TypedGeneratorProduct : Prop := ∏ p : TypX X, (gAt X p.1 : ℝ) = ((Lat.gS D : ℕ) : ℝ) ^ Module.finrank ℚ D.host.F

theorem discriminant_abs_eq : DiscriminantAbsEq X := by
  unfold DiscriminantAbsEq
  rw [NumberField.discr_eq_discr_of_algEquiv X.B.I.F (RingEquiv.toRatAlgEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X))]

theorem finrank_eq : Module.finrank ℚ X.B.I.F = Module.finrank ℚ D.host.F :=
  (RingEquiv.toRatAlgEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)).toLinearEquiv.finrank_eq

theorem infinite_places_card : InfinitePlacesCardEq X := by
  unfold InfinitePlacesCardEq
  rw [← finrank_eq X]
  haveI := X.B.I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank X.B.I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h1
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, h1]

theorem T_not_mem (w : D.what₂.Word) (p : TypX X) : ¬ ((((D.mem w).A.T : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal) := by
  intro hw
  have hc := (resChar_eq_iff (plEquiv X p.1) (D.mem w).A.T_prime).2 ((natCast_mem_plEquiv X p.1 _).2 hw)
  rcases (typAt_iff X p.1).1 p.2 with h | h
  · exact D.T_ne_g w 0 (hc.symm.trans h)
  · exact D.T_ne_g w 1 (hc.symm.trans h)

theorem local_a_factor_symmetric : ∀ p : TypX X,
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u') = aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) := by
  intro p
  unfold aP Tw
  rw [if_neg (T_not_mem X u' p), if_neg (T_not_mem X u p)]

theorem fieldDict_of (h3 : EulerProductEta X) (h4 : LocalFactorProduct X u) (h5 : VInvEqHalfRootDiscriminant (D := D)) (h6 : QuadraticInfinitePlaces (D := D)) (h8 : DifferentGeneratorUnit X)
    (h10 : TypedGeneratorProduct X) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' := by
  unfold Formalism.L2.SG.Pf.NcVal.FieldDict
  exact ⟨discriminant_abs_eq X, infinite_places_card X, h3, h4, h5, h6, X.n_eq, h8, local_a_factor_symmetric X u u', h10⟩

theorem over_g_of_typed (p : TypX X) : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have h := (mem_typSet X.B.I.F _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero p.1).1 p.2
  rcases h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 X.B.I.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 X.B.I.F) := by
  let _ : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 X.B.I.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem different_generator_unit : DifferentGeneratorUnit X := by
  intro p
  obtain ⟨i, hi⟩ := over_g_of_typed X p
  have hnd := not_dvd_diff X p.1 i hi
  have hex : ∃ x ∈ differentIdeal ℤ (𝓞 X.B.I.F), x ∉ p.1.asIdeal := by
    by_contra hc
    push Not at hc
    exact hnd (Ideal.dvd_iff_le.2 hc)
  have hval : ∀ x : 𝓞 X.B.I.F,
      Valued.v (algebraMap X.B.I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv X.B.I.F p.1) (x : X.B.I.F)) = p.1.intValuation x := by
    intro x
    have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := X.B.I.F) p.1 x
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at h
    exact h
  have hv1 : Valued.v (dV p.1) = 1 := by
    unfold dV
    split_ifs with hd
    · obtain ⟨-, hle, x0, -, heq⟩ := hd.choose_spec
      obtain ⟨x1, hx1, hx1n⟩ := hex
      have h1 := hle x1 hx1
      rw [hval, (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hx1n] at h1
      rw [hval] at heq
      have h2 := p.1.intValuation_le_one x0
      rw [heq] at h2
      exact le_antisymm h2 h1
    · exact map_one _
  unfold absV
  split_ifs with h0
  · exact absurd (hv1 ▸ h0) one_ne_zero
  · have e2 : WithZero.unzero h0 = 1 := by
      apply WithZero.coe_inj.1
      rw [WithZero.coe_unzero, hv1, WithZero.coe_one]
    rw [e2]
    simp

theorem not_both (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr D.host.g_ne
  obtain ⟨a, b, hab⟩ := hcop
  have hone : (1 : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 X.B.I.F) hab
    push_cast at e
    rw [← e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h0) (v.asIdeal.mul_mem_left _ h1)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem card_over (i : Fin 2) :
    ({v : HeightOneSpectrum (𝓞 X.B.I.F) | ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}).ncard =
      Module.finrank ℚ X.B.I.F := by
  let _ : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  have hp := D.host.g_prime i
  have := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp
  have hq0 := Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp
  have hsum := Ideal.sum_ramification_inertia (𝓞 X.B.I.F) ℚ X.B.I.F hq0
  have hall : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((D.host.g i : ℕ) : ℤ)}) (𝓞 X.B.I.F),
      (Ideal.span {((D.host.g i : ℕ) : ℤ)}).ramificationIdx' Q * (Ideal.span {((D.host.g i : ℕ) : ℤ)}).inertiaDeg' Q = 1 := by
    intro Q hQ
    rw [IsDedekindDomain.mem_primesOverFinset_iff hq0] at hQ
    have hQ' : Q ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 X.B.I.F) := hQ
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp] at hQ'
    obtain ⟨v, hv, rfl⟩ := hQ'
    obtain ⟨he, hf⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split i) v hv
    rw [he, hf]
  rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [← hsum, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0,
    Formalism.L2.SG.Pf.TypedLoc.primesOver_eq X.B.I.F hp]
  exact (Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)).symm

theorem typed_generator_product : TypedGeneratorProduct X := by
  unfold TypedGeneratorProduct
  have hg0 := (D.host.g_prime 0).ne_zero
  have hg1 := (D.host.g_prime 1).ne_zero
  have hA0 := finite_over X.B.I.F (D.host.g 0) hg0
  have hA1 := finite_over X.B.I.F (D.host.g 1) hg1
  have hT : typSet X.B.I.F (D.host.g 0) (D.host.g 1) = hA0.toFinset ∪ hA1.toFinset := by
    ext v
    rw [mem_typSet _ _ _ hg0 hg1, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rfl
  have hdisj : Disjoint hA0.toFinset hA1.toFinset :=
    Finset.disjoint_left.2 fun v h0 h1 =>
      not_both X v (hA0.mem_toFinset.1 h0) (hA1.mem_toFinset.1 h1)
  have hc0 : hA0.toFinset.card = Module.finrank ℚ D.host.F := by
    rw [← Set.ncard_eq_toFinset_card _ hA0, card_over X 0, finrank_eq X]
  have hc1 : hA1.toFinset.card = Module.finrank ℚ D.host.F := by
    rw [← Set.ncard_eq_toFinset_card _ hA1, card_over X 1, finrank_eq X]
  have hg0v : ∀ v ∈ hA0.toFinset, (gAt X v : ℝ) = (D.host.g 0 : ℝ) := by
    intro v hv
    rw [gAt, if_pos (show ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal from hA0.mem_toFinset.1 hv)]
  have hg1v : ∀ v ∈ hA1.toFinset, (gAt X v : ℝ) = (D.host.g 1 : ℝ) := by
    intro v hv
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := hA1.mem_toFinset.1 hv
    rw [gAt, if_neg (fun h0 => not_both X v h0 h1)]
  show ∏ p : ↥(typSet X.B.I.F (D.host.g 0) (D.host.g 1)), (gAt X p.1 : ℝ) = _
  rw [Finset.prod_coe_sort (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) (fun v => (gAt X v : ℝ)), hT,
    Finset.prod_union hdisj, Finset.prod_congr rfl hg0v, Finset.prod_congr rfl hg1v, Finset.prod_const,
    Finset.prod_const, hc0, hc1, ← mul_pow]
  unfold Lat.gS
  push_cast
  rfl

theorem totally_complex_quadratic : QuadraticInfinitePlaces (D := D) := by
  unfold QuadraticInfinitePlaces Formalism.HermitianLatticesTheory.fDeg
  have : IsTotallyComplex D.host.E := (Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D).1.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
  have h4 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [Formalism.BasicNotions.Examples₂.finrank_FE D.host] at h4
  omega

theorem field_dictionary_of_leaves (h3 : EulerProductEta X) (h4 : LocalFactorProduct X u) (h5 : VInvEqHalfRootDiscriminant (D := D)) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' := fieldDict_of X u u' h3 h4 h5 (totally_complex_quadratic (D := D)) (different_generator_unit X) (typed_generator_product X)

theorem discriminant_sq_relation : VInvEqHalfRootDiscriminant (D := D) := by
  unfold VInvEqHalfRootDiscriminant Formalism.HermitianLatticesTheory.vInv
  have h6 : Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F := totally_complex_quadratic
  rw [h6, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  congr 1
  push_cast
  rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  have hf : (0 : ℝ) < Module.finrank ℚ D.host.F := by exact_mod_cast Module.finrank_pos
  field_simp
  norm_num

end Formalism.L2.SG.Pf.AlTieFD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneCOf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covolOneC_of (hC : ChartC) (hL : LatC) : Formalism.L2.SG.Pf.VolPinAsm.CovolOneC := by
  intro D X Y u u' t hrel hG w hat F' L U hNR γw s s' μw hIs hs hs' hpt hHaar hmap c Φ hD
  obtain ⟨BX, hBm, hBd, hB0, hstm, hStm, hinj, hsurj, hmul, hconj⟩ :=
    hC D X Y u u' t hrel hG w hat γw s s' hIs hs hs' hpt
  have hΦR : ∀ β, c⁻¹ * Φ β * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t := hD.2.1
  obtain ⟨σ, h', I, Λ, k, τ, σι, hh', hφ, hΛ, hk, hk0, hs0, hτ, hset, hc0, hconst⟩ :=
    hL D X Y u u' t hrel hG w hat F' L U hNR γw s s' hIs hs hs' hpt c Φ hD
  have hTC := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)) w.2⟩
  set St := Formalism.L2.SG.RealObj.StInf X u u' γw with hStdef
  set sc := Formalism.L2.SG.RealObj.stCoord X u' w γw with hscdef
  let gβ : Formalism.L2.SG.Pf.VolPinAsm.StG w → X.B.I.Ginf := fun β => s⁻¹ * (c⁻¹ * Φ β * c) * s
  have hgSt : ∀ β, gβ β ∈ St := fun β => hconj _ (hΦR β)
  have hg_inv : ∀ β, gβ β⁻¹ = (gβ β)⁻¹ := by
    intro β; simp only [gβ, map_inv]; group
  have hg_mul : ∀ β (y : X.B.I.Ginf), s⁻¹ * (c⁻¹ * (Φ β * y) * c) * s = gβ β * (s⁻¹ * (c⁻¹ * y * c) * s) := by
    intro β y; simp only [gβ]; group
  let A : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup (InfinitePlace X.B.I.F → ℂ) :=
    fun p => (Λ p).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p))
  have hΓ : ∀ x, (∀ p, (fun v => x v p) - τ p x ∈ A p) ↔
      ∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
        x = sc (gβ β) := by
    intro x
    exact (hset x).symm
  have hBd' : ∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, h' q < h' p → x q = x' q ∧ y q = y' q) →
      BX p x y = BX p x' y' :=
    fun p x x' y y' hxy => hBd p x x' y y' fun q hq => hxy q (hh' p q hq)
  have hinv : ∀ γ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) → ∃ γ', (∀ p, (fun v => γ' v p) - τ p γ' ∈ A p) ∧
      ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x := by
    intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := (hΓ γ).1 hγ
    have hβi : ((β⁻¹ : Formalism.L2.SG.Pf.VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) ∈
        Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w := by
      rw [Subgroup.coe_inv]; exact Subgroup.inv_mem _ hβ
    refine ⟨sc (gβ β⁻¹), (hΓ _).2 ⟨β⁻¹, hβi, rfl⟩, fun x => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hsurj x
    have h1 := hmul (gβ β) (hgSt β) z hz
    have h1' := hmul (gβ β⁻¹) (hgSt _) z hz
    constructor
    · have h2 := hmul (gβ β⁻¹) (hgSt _) (gβ β * z) h1.1
      rw [← h1.2, ← h2.2, hg_inv, inv_mul_cancel_left]
    · have h2 := hmul (gβ β) (hgSt β) (gβ β⁻¹ * z) h1'.1
      rw [← h1'.2, ← h2.2, hg_inv, mul_inv_cancel_left]

  have hfd : ∀ p, ∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! b : A p, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro p
    obtain ⟨F, hF, hFd⟩ := exists_fd D.host.E (InfinitePlace X.B.I.F) (Formalism.L2.SG.Pf.VolPinAsm.phiV X) σι hφ (I p) (Λ p)
      (hΛ p) (by rw [hk p]; exact hk0 p) (σ p) (hs0 p)
    refine ⟨F, hF, fun v => ?_⟩
    obtain ⟨a, ha, hau⟩ := hFd v
    refine ⟨⟨Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨y, hy⟩ hyF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hy
    have := hau ⟨a', ha'⟩ hyF
    apply Subtype.ext
    show Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a' = Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a
    rw [show a' = (a : D.host.E) from congrArg Subtype.val this]
  choose F hF hFd using hfd
  set K' : Set (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) := {y | ∀ p, (fun v => y v p) ∈ F p} with hK'def
  have hK'm : MeasurableSet K' := by
    rw [hK'def, Set.setOf_forall]
    exact MeasurableSet.iInter fun p =>
      (measurable_pi_lambda _ fun v => (measurable_pi_apply p).comp (measurable_pi_apply v)) (hF p)
  have hKd := box_fundX h' BX hBd' τ hτ A F hFd
  have hone := covol_one_eq_one D.host.E (InfinitePlace X.B.I.F) (Formalism.L2.SG.Pf.VolPinAsm.phiV X) σι hφ
    (Formalism.L2.SG.RealObj.FreeE w) h' BX hBm hBd' hB0 _ hc0 I Λ hΛ k hk hk0 σ hs0 hconst τ hτ hinv K' hK'm hKd

  have hQm : Measurable (fun y : X.B.I.Ginf => s⁻¹ * (c⁻¹ * y * c) * s) :=
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const).measurable
  set KA := (fun y : X.B.I.Ginf => s⁻¹ * (c⁻¹ * y * c) * s) ⁻¹' (St ∩ sc ⁻¹' K') with hKAdef
  have hKAm : MeasurableSet KA := hQm (hStm.inter (hstm hK'm))
  refine ⟨KA, hKAm, fun y hy => ?_, ?_⟩
  · set z := s⁻¹ * (c⁻¹ * y * c) * s
    have hz : z ∈ St := hconj _ hy
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (sc z)
    obtain ⟨β, hβ, rfl⟩ := (hΓ γ).1 hγΓ
    refine ⟨Φ β, ⟨⟨β, (Subgroup.mem_subgroupOf).2 hβ, rfl⟩, ?_⟩, ?_⟩
    · show s⁻¹ * (c⁻¹ * (Φ β * y) * c) * s ∈ St ∩ sc ⁻¹' K'
      rw [hg_mul]
      have h1 := hmul (gβ β) (hgSt β) z hz
      exact ⟨h1.1, by show sc (gβ β * z) ∈ K'; rw [h1.2]; exact hγK⟩
    · rintro x' ⟨hx'm, hx'K⟩
      obtain ⟨β', hβ', rfl⟩ := Subgroup.mem_map.1 hx'm
      have hβ'' : (β' : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w :=
        (Subgroup.mem_subgroupOf).1 hβ'
      have hK2 : s⁻¹ * (c⁻¹ * (Φ β' * y) * c) * s ∈ St ∩ sc ⁻¹' K' := hx'K
      rw [hg_mul] at hK2
      have h1 := hmul (gβ β') (hgSt β') z hz
      have hin : lawX BX (sc (gβ β')) (sc z) ∈ K' := by rw [← h1.2]; exact hK2.2
      have heq := hγu (sc (gβ β')) ⟨(hΓ _).2 ⟨β', hβ'', rfl⟩, hin⟩
      have hgg : gβ β' = gβ β := hinj (hgSt β') (hgSt β) heq
      have : Φ β' = Φ β := by
        have e : c⁻¹ * Φ β' * c = c⁻¹ * Φ β * c := by
          have := congrArg (fun g => s * g * s⁻¹) hgg
          simpa [gβ, mul_assoc] using this
        have := congrArg (fun g => c * g * c⁻¹) e
        simpa [mul_assoc] using this
      exact this
  · have hc1m : Measurable (fun y : X.B.I.Ginf => c * y * c⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    have hs1m : Measurable (fun y : X.B.I.Ginf => s * y * s⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    rw [Measure.map_apply hc1m hKAm, Measure.map_apply hs1m (hc1m hKAm)]
    have hset' : (fun y : X.B.I.Ginf => s * y * s⁻¹) ⁻¹' ((fun y : X.B.I.Ginf => c * y * c⁻¹) ⁻¹' KA) =
        St ∩ sc ⁻¹' K' := by
      ext y
      simp only [Set.mem_preimage, hKAdef]
      have e : s⁻¹ * (c⁻¹ * (c * (s * y * s⁻¹) * c⁻¹) * c) * s = y := by group
      rw [e]
    rw [hset', Set.inter_comm, measure_inter_conull hHaar.2.2.1, ← Measure.map_apply hstm hK'm, hmap]
    exact hone

end Formalism.L2.SG.NGCut.StabilizerCovolume
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂)
  (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))

include hu in
theorem baseChangeAt_frame_eq (a : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame (lf D F0) a) = ((hu a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) • (tLoc Zd p γ).f a := by
  rw [tf, Units.smul_def, smul_smul, (hu a).val_inv_mul, one_smul]

include hu in
theorem bcP_X {x : (VS D).V} (hx : x ∈ Xsp (lf D F0)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f := by
  change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_cs, baseChangeAt_frame_eq Zd p γ hu, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChange_mem_perp_sup {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp (lf D F0))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f, (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf, frame_cs, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

theorem h_X_perp {w v : Vp D p} (hw : w ∈ (locH Zd p).X (tLoc Zd p γ).f)
    (hv : v ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f)) : (locH Zd p).h w v = 0 := by
  rw [(locH Zd p).h_herm v w, (show (locH Zd p).h v w = 0 from hv w hw), map_zero]

end Place

theorem pair_int (γ : TermDef.Term D u u' F0 what₂) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hSD₁ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₁))
    (hL : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f ⊆
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₁) (tLoc Zd p γ).f)
    {x m : (VS D).V} (hx : x ∈ Λ₂) (hxo : x ∈ orth (VS D) (Xsp (lf D F0))) (hm : m ∈ Λ₁)
    (hmo : m ∈ orth (VS D) (Xsp (lf D F0))) : IsIntegral ℤ ((VS D).hT m x) := by
  refine int_of_loc Zd fun p => ?_
  rw [← localForm_baseChange]
  have hv := baseChange_mem_perp_sup Zd p γ hxo
  have hmem : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p x, hv⟩ ∈
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := ⟨⟨baseChange₂ D p x, hv⟩, baseChange_mem_localLattice Zd hx p, rfl⟩
  obtain ⟨x'', hx''Λ, hx''eq⟩ := hL p hmem
  have hdiff : (baseChange₂ D p x) - (x'' : Vp D p) ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := (Submodule.Quotient.eq _).1 hx''eq.symm
    simpa using this
  have e : baseChange₂ D p x = (x'' : Vp D p) + ((baseChange₂ D p x) - (x'' : Vp D p)) := by abel
  rw [e, (locH Zd p).h_add_left, h_X_perp Zd p γ hdiff (baseChange_mem_perp_sup Zd p γ hmo), add_zero]
  exact ((hSD₁ p).2.2 x'').1 hx''Λ (baseChange₂ D p m) (baseChange_mem_localLattice Zd hm p)

theorem memX (γ : TermDef.Term D u u' F0 what₂) {Λa Λb : Submodule (𝓞 D.host.E) (VS D).V}
    (ha : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λa) (tLoc Zd p γ).f)
    (hb : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λb) (tLoc Zd p γ).f) (hΛb : Submodule.IsLattice D.host.E Λb)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) {x : (VS D).V} (hx : x ∈ Xsp (lf D F0))
    (hxa : x ∈ Λa) : x ∈ Λb := by
  refine mem_of_bcP Zd hΛb fun p => ?_
  have h1 : baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) (bcP_X Zd p γ (hu p) hx)
  have h2 := (ha p).2.2 _ (baseChange_mem_localLattice Zd hxa p) h1
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun a => (hb p).1 a) h2

theorem z_mem (γ : TermDef.Term D u u' F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (tLoc Zd p γ).f) :
    F0.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← tf_last Zd p γ]; exact (h p).1 _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFull
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem patchC_of_full (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ :=
  patchC_of Formalism.L2.SG.Pf.LocalDenominators.latPatch_holds hL

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLift
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def SRLift : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R)
    (K : Submodule M.R (Fin (n + 1) → M.R)),
    (∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0) →
    (∀ v : Fin (n + 1) → M.R, ∃ x, v - A.mulVec x ∈ K) →
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) M.R, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      IsUnit (A + H).det

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end


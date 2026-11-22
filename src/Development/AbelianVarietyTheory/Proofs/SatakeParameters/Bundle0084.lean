import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRangeSplit
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopExcess

theorem sum_range_split (f : ℕ → ℝ) (k M : ℕ) (hk : 2 ≤ k) :
    ∑ r ∈ Finset.range (k + M), f r =
      f 0 + ∑ r ∈ Finset.Ico 1 (k - 1), f r + f (k - 1) + ∑ r ∈ Finset.Ico k (k + M), f r := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Finset.sum_range_add_sum_Ico f (Nat.le_add_right (n + 1) M), Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico f (by omega : 1 ≤ n), Finset.sum_range_one]

theorem sum_Ico_bounds (f : ℕ → ℝ) (a b : ℕ) (lo hi : ℝ) (h : ∀ r, a ≤ r → r < b → lo ≤ f r ∧ f r ≤ hi) :
    ((b - a : ℕ) : ℝ) * lo ≤ ∑ r ∈ Finset.Ico a b, f r ∧ ∑ r ∈ Finset.Ico a b, f r ≤ ((b - a : ℕ) : ℝ) * hi := by
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.Ico a b) f lo
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).1)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (Finset.Ico a b) f hi
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).2)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this

theorem top_excess : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x5, h5⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩ := hx
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := h1 x g1 hx1 i
  obtain ⟨b1, -, b3⟩ := h2 x g2 hx1 i j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := h3 x g3 hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := h4 x g4 hx1 i u j hj z hz
  have e := h5 x g5 hx1 i u j hj z
  clear h1 h2 h3 h4 h5
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

end GlobalTheory.TopExcess
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.InertCompare

section Emb

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom

def rhoH (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem rhoH_apply (τ : D.what₂.Tau) (x : D.host.E) : rhoH D lam τ x = lamC lam (embT D τ x) := by
  unfold lamC
  rw [dif_pos (embT_mem D τ x)]
  rfl

theorem coe_rhoH (τ : D.what₂.Tau) : (rhoH D lam τ : D.host.E → ℂ_[l]) = tauEmb D lam τ :=
  funext fun x => rhoH_apply D lam τ x

def rhoC (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] := (rhoH D lam τ).comp (D.host.conj : D.host.E →+* D.host.E)

theorem rhoC_apply (τ : D.what₂.Tau) (x : D.host.E) :
    rhoC D lam τ x = lamC lam (embT D τ (D.host.conj x)) := rhoH_apply D lam τ _

def parProj (r : Bool × HH D) (ε : ℕ) (y : D.what₂.Tau → ℂ_[l] × ℂ_[l]) : ZMod (nP D l) → ℂ_[l] :=
  fun s => if s.val % 2 = ε then (y (tauPl D (posPl D l r s.val))).1 else 0

end Emb

def SamePrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ ρ' : E →+* ℂ_[l]) : Prop :=
  ∀ a : 𝓞 E, ‖ρ (a : E)‖ < 1 ↔ ‖ρ' (a : E)‖ < 1

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) := by
  have hinj := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h1 : plGG D (b, t) = plGG D (b', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases b <;> cases b' <;> simp only [plGG, if_true, if_false, Bool.false_eq_true] at h1
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
    · exact absurd h1 (hP.2 _ _)
    · exact absurd h1.symm (hP.2 _ _)
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨(false, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])
    · refine ⟨(true, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])

def plEquiv (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bijective D)

theorem plEquiv_apply (D : D7) (z : Bool × HH D) : plEquiv D z = tauPl D z := rfl

theorem inertK_iff (D : D7) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) : GL3Theta.InertK D l ↔ (IsResidueClassZero D l ∨ IsSg D l) := by
  have hq : jacobiSym (-(D.host.d : ℤ)) D.host.q = 1 := by
    have := D.host.hyp
    unfold Formalism.FrobeniusOrbits.HostHyp at this
    tauto
  have hd := D.host.hyp.2.1
  unfold GL3Theta.InertK IsResidueClassZero IsSg Host.cls primeClass
  have h2 : l ≠ 2 := by omega
  by_cases hs : l ∈ D.host.small
  · rw [if_pos hs, D.host.QS_split l hl h2 (Nat.dvd_of_mem_primeFactors hs)]; simp
  rw [if_neg hs]
  by_cases h1 : l = D.host.q
  · rw [if_pos h1, h1, hq]; simp
  rw [if_neg h1]
  by_cases h3 : l = D.host.d
  · rw [if_pos h3, h3]
    have : jacobiSym (-(D.host.d : ℤ)) D.host.d = 0 := by
      haveI : NeZero D.host.d := ⟨hd.ne_zero⟩
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.neg_gcd, Int.gcd_self]
      simpa using hd.ne_one
    rw [this]; simp
  rw [if_neg h3]
  have cop : Int.gcd (-(D.host.d : ℤ)) (l : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hd hl).mpr (Ne.symm h3)
  rcases jacobiSym.eq_one_or_neg_one cop with h | h
  · rw [if_pos h, h]; simp
  · rw [if_neg (by rw [h]; decide)]
    split_ifs <;> simp [h]

theorem case_iff (D : D7) (l : ℕ) (hl : l.Prime) : IndefiniteRowSideFullHecke.ShapeDegreeParity.CaseA D l ↔ IndefiniteRowSideFullHecke.TeichmullerFactorisation.InertNotConj D l := by
  unfold IndefiniteRowSideFullHecke.ShapeDegreeParity.CaseA IndefiniteRowSideFullHecke.TeichmullerFactorisation.InertNotConj
  exact and_congr_right fun h5 => and_congr_left' (inertK_iff D l hl h5)

theorem even_nP (D : D7) (l : ℕ) (h : IndefiniteRowSideFullHecke.TeichmullerFactorisation.InertNotConj D l) : Even (nP D l) := by
  unfold nP
  split_ifs with hs
  · exact even_two_mul _
  · exact h.2.2 (h.2.1.resolve_right hs)

end GlobalTheory.InertCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorDirLinear
section
open Filter Topology

namespace GlobalTheory.PSerLin

theorem map_subst_linear {σ κ R S : Type*} [Finite σ] [Fintype κ] [CommRing R] [CommRing S]
    (h : R →+* S) (c : σ → κ → R) (F : MvPowerSeries σ R) :
    MvPowerSeries.map h (MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (c k x) * (MvPowerSeries.X x : MvPowerSeries κ R)) F) =
    MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (h (c k x)) * (MvPowerSeries.X x : MvPowerSeries κ S))
      (MvPowerSeries.map h F) := by
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp)]
  simp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing

open Classical in

theorem taylorDir_linear (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ)
    (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ)
    (hG : Differentiable ℂ G) :
    taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) (fun z : VC D N N' => G (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) =
    MvPowerSeries.subst (fun k => ∑ x, MvPowerSeries.C (c k x) *
      (MvPowerSeries.X x : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ))
      (taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G) := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : Formalism.MainNotions.TaylorLogMetric.coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.single_apply]
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hG)
  have han' : AnalyticAt ℂ (fun z => G (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  let ev : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun x =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) x.2.2).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) x.2.1).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) x.1))
  let ℓ : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun k => ∑ x, c k x • ev x
  have hℓ : ∀ k z, ℓ k z = ∑ x, c k x * z x.1 x.2.1 x.2.2 := fun k z => by
    simp [ℓ, ev]
  have h := taylorDir_comp (Formalism.MainNotions.TaylorLogMetric.coordV D) (φ := fun z k => ℓ k z)
    (analyticAt_pi_iff.2 fun k => (ℓ k).analyticAt 0) (funext fun k => map_zero (ℓ k)) han'
  rw [taylor_comp_clm L han, ← hc] at h
  convert h using 2
  · funext z
    refine congrArg G ?_
    funext τ i j
    exact (hℓ (τ, i, j) z).symm
  · funext k
    rw [show (fun z => ℓ k z) = ⇑(ℓ k) from rfl, taylorDir_clm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, hℓ, hc]
    simp [hL, Pi.single_apply]

theorem pSer_linear : ∀ (D : D7) (N N' p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : VC D N N' → ℂ) (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ), Differentiable ℂ G → CoefIn D G Qbar → (∀ k x, c k x ∈ Qbar) → pSer D lam (fun z : VC D N N' => G (fun τ i j => ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) = linAt (fun k x => lamC lam (c k x)) (pSer D lam G) := by
  intro D N N' p _ lam G c hG hco hc
  let F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) Qbar := fun α => ⟨_, hco α⟩
  let c₀ : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → Qbar :=
    fun k x => ⟨_, hc k x⟩
  have hl : ∀ x : Qbar, lamC lam x = lam x := fun x => by simp [lamC]
  have h1 : MvPowerSeries.map (algebraMap Qbar ℂ) F₀ = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
    ext α
    rw [MvPowerSeries.coeff_map, ← ConjSeries.taylor_eq_coeff]
    rfl
  have h2 : MvPowerSeries.map lam F₀ = pSer D lam G := by
    ext α
    rw [MvPowerSeries.coeff_map, ← hl]
    rfl
  have h3 := map_subst_linear (algebraMap Qbar ℂ) c₀ F₀
  have h4 := map_subst_linear lam c₀ F₀
  rw [h1] at h3
  rw [h2] at h4
  have h5 := h3.trans (taylorDir_linear D G c hG).symm
  simp only [← hl] at h4
  refine Eq.trans ?_ h4
  ext α
  rw [MvPowerSeries.coeff_map, ← hl]
  change lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D _ α) = _
  rw [ConjSeries.taylor_eq_coeff, ← h5, MvPowerSeries.coeff_map]
  rfl

end GlobalTheory.PSerLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory

namespace ThetaCosetSum

open Formalism.L2.Th1.H

theorem xiL_eq_kernel {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB Φ e z = (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) *
      ∑ x ∈ SX, ∑ y ∈ SB, ∑ t ∈ SA, Φ (t - x) *
        (α x * ((SA.card : ℂ)⁻¹ * (brk H y t)⁻¹ * α y * opU H y e (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) := by
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [opU]
  simp only [xiS, sumU, hatS, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem sum_xiL {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (hv : 0 < vol)
    (SX SA SB : Finset V) (c : ι → ℂ) (Φ : ι → V → ℂ) (Ψ e : V → ℂ) (hΨ : ∀ t, Ψ t = ∑ i, c i * Φ i t) (z : V) :
    ∑ i, c i * (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiL H α vol SX SA SB (Φ i) e z) = xiL H α 1 SX SA SB Ψ e z := by
  have hs : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have h2 : ((vol : ℝ) : ℂ) = ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hv.le).symm
  have h3 : ∀ w : ℂ, ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) * w) = w := by
    intro w
    generalize ((Real.sqrt vol : ℝ) : ℂ) = s at hs h2
    rw [h2]; field_simp
  simp only [xiL_eq_kernel, h3, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, hΨ, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

open Classical in

theorem eq_sum_coset {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A B : Submodule R M) (hBA : B ≤ A)
    [Fintype (↥A ⧸ B.comap A.subtype)] (Ξ : M → ℂ) (h1 : ∀ x, Ξ x ≠ 0 → x ∈ A) (h2 : ∀ x, ∀ y ∈ B, Ξ (x + y) = Ξ x)
    (r : (↥A ⧸ B.comap A.subtype) → ↥A) (hr : ∀ q, Submodule.Quotient.mk (r q) = q) (t : M) :
    Ξ t = ∑ q, Ξ (r q) * (if t - (r q : M) ∈ B then 1 else 0) := by
  by_cases ht : t ∈ A
  · have key : ∀ q, t - (r q : M) ∈ B ↔ q = Submodule.Quotient.mk (⟨t, ht⟩ : ↥A) := by
      intro q
      rw [eq_comm]
      conv_rhs => rw [← hr q]
      rw [Submodule.Quotient.eq]
      rfl
    rw [Finset.sum_eq_single (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A))]
    · have hm := (key _).mpr rfl
      rw [if_pos hm, mul_one, ← h2 (r (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A)) : M) _ hm, add_sub_cancel]
    · intro q _ hq
      rw [if_neg (fun h => hq ((key q).mp h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : Ξ t = 0 := by
      by_contra h
      exact ht (h1 t h)
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg, mul_zero]
    intro h
    apply ht
    have := A.add_mem (hBA h) (r q).2
    simpa using this

end ThetaCosetSum

open ThetaCosetSum in

theorem latSum_thInd_eq_thC : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndTieD a b S (cA * cB) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → 0 < volC A.AA S N N' → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → ∀ z, latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) (fun x => Ξ x * A.thInd S N N' cB x z) = thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) Ξ (A.e a b N N') z := by
  intro X A a b S N N' cA cB Ξ hT hN hN' hA hB hv hfin h1 h2 z
  classical
  let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  have hle : mulLat cB (homAt S N N') ≤ divLat cA (homAt S N N') := by
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy)
  have hdiv : ∀ x ∈ divLat cA (homAt S N N'), x ∈ divLat (cA * cB) (homAt S N N') := by
    intro x hx
    have h : (cB : 𝓞 X.E) • (cA : 𝓞 X.E) • x ∈ homAt S N N' := Submodule.smul_mem _ _ hx
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at h
    exact h
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)) with hr
  have hrq : ∀ q, Submodule.Quotient.mk (r q) = q := fun q => Function.surjInv_eq _ q
  have hx : ∀ q, A.thInd S N N' cB (r q : HomE X.E a b) z = _ := fun q =>
    hT N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, hdiv _ (r q).2⟩ (Nat.mul_pos hA hB) z
  simp only [hx]
  unfold xiC thC xiV
  refine sum_xiL _ _ _ hv _ _ _ (fun q => Ξ (r q)) (fun q => onV (X.embC A.σ₀) A.δ (cosInd S N N' cB (r q))) _ _ ?_ z
  intro v
  unfold onV
  split_ifs with h
  · have := eq_sum_coset _ _ hle Ξ h1 h2 r hrq h.choose
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cosInd
    congr
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordJumpsInWindowsStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_jumps_in_windows : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  first | exact @GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | exact GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | (intros; apply GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeightStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  first | exact @GlobalTheory.HTW.pageWord_Mi_add_hi_le | exact GlobalTheory.HTW.pageWord_Mi_add_hi_le | (intros; apply GlobalTheory.HTW.pageWord_Mi_add_hi_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordSmallJumpsCardStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  first | exact @GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | exact GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | (intros; apply GlobalTheory.HTW.twistedDualPageWord_small_jumps_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG), Roomy L C → ∀ a : ZMod (orderOf ψ), (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧ (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧ (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧ (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | exact GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | (intros; apply GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoWLeFirstRow
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopFirstRow

theorem two_w_le_first_row : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x1 (max x2 x3), fun x hx hx1 i u j hj z hz => ?_⟩
  have hxa : x ≥ x1 := le_trans (le_max_left _ _) hx
  have hxb : x ≥ x2 := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hxc : x ≥ x3 := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := h1 x hxa hx1 i
  obtain ⟨e1, e2, e3, -⟩ := h2 x hxb hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := h3 x hxc hx1 i j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dif_pos hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dif_pos hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

end GlobalTheory.TopFirstRow
end


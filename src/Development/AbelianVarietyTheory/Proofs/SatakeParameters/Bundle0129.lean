import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopLawSym

open GlobalTheory.DatumLaw GlobalTheory.TwU

section Res

variable {κ K : Type} [CommRing κ] [Field K]

theorem sum_pred (n : ℕ) (f : ℕ → κ) (c : ℕ → Prop) [DecidablePred c] (h : ∀ p, p < n → (c p ↔ p + 1 < n)) :
    (∑ p ∈ Finset.range n, if c p then f p else 0) = ∑ p ∈ Finset.range (n - 1), f p := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    have := (h p h1).1 h2
    omega
  · intro h1
    exact ⟨by omega, (h p (by omega)).2 (by omega)⟩

theorem chiSymF_val (ψ : AddChar κ K) {r k rS : ℕ} (hr : k + rS ≤ r) (M : HPsymF κ r k rS) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin r, A i.1 j.1 = (M.1 : Matrix (Fin r) (Fin r) κ) i j) :
    ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) := by
  have h0 : ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (supSum r (SPsym r k rS) ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) *
        ψ (offSum k rS ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) := rfl
  rw [h0, ← AddChar.map_add_eq_mul]
  congr 1
  unfold supSum offSum
  rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
  have h1 : ∀ p : Fin r, ((∑ j : Fin r, if (symPerm r k rS p).1 + 1 = j.1 ∧ j.1 < r ∧ (symPerm r k rS p).1 ∈ SPsym r k rS then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) +
      ∑ j : Fin r, if (symPerm r k rS p).1 + 1 = rS ∧ j.1 = rS + k then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) =
      if p.1 + 1 < r ∧ p.1 + 1 ≠ k then A p.1 (p.1 + 1) else 0 := fun p => by
    rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
    have h2 : ∀ p' : Fin r, ((if (symPerm r k rS p).1 + 1 = (symPerm r k rS p').1 ∧ (symPerm r k rS p').1 < r ∧
        (symPerm r k rS p).1 ∈ SPsym r k rS then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) +
        if (symPerm r k rS p).1 + 1 = rS ∧ (symPerm r k rS p').1 = rS + k then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) =
        if p.1 + 1 = p'.1 then (if p.1 + 1 ≠ k then A p.1 p'.1 else 0) else 0 := fun p' => by
      rw [toSymOrd_val', ← hA, symPerm_val hr, symPerm_val hr]
      have e1 := SymLevelInv.symIdx_cases k rS p.1
      have e2 := SymLevelInv.symIdx_cases k rS p'.1
      have := p.2
      have := p'.2
      simp only [SPsym, Finset.mem_filter, Finset.mem_range]
      split_ifs <;> first | omega | simp
    rw [Finset.sum_congr rfl fun p' _ => h2 p',
      Fin.sum_univ_eq_sum_range (fun p' => if p.1 + 1 = p' then (if p.1 + 1 ≠ k then A p.1 p' else 0) else 0) r,
      Finset.sum_ite_eq]
    simp only [Finset.mem_range, ite_and]
  rw [Finset.sum_congr rfl fun p _ => h1 p,
    Fin.sum_univ_eq_sum_range (fun p => if p + 1 < r ∧ p + 1 ≠ k then A p (p + 1) else 0) r]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [sum_pred k _ _ fun p hp => by omega,
      sum_pred d (fun p => A (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_eq {r m t i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem lamPar_val (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (M : HPar n κ h (List.replicate m t) (HPsymF κ r k rS)) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) = lamF ψ χ k r t m A := by
  have h0 : ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  rw [h0, chiSymF_val ψ hr (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply, List.length_replicate,
    Units.coe_prod]
  unfold lamF
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_ ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases hir : i < r
    · rw [coarse_of_lt hir]
      omega
    · rw [coarse_eq ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

end Res

section Lev

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem red_entB (k₀ : ℕ) (ex : ℕ → ℕ) (g : GLint E n P) (i j : Fin n) :
    red P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k₀ 0 n 0 n ex ex g.1.toLinearMap) i.1 j.1 =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
  unfold red
  rw [entB_zero _ _ _ _ _ rfl, dif_pos ⟨i.2, j.2⟩]
  rfl

theorem lamY_eq (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  rw [show stdAt E n P = LocE.lamY P (qOf P) n 0 0 from stdAt_eq (c := 0)]
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, LastSteps.mem_sclLat]
  refine forall_congr' fun l => ?_
  have hl : l.1 < n := l.2
  simp only [LocE.scE, if_pos hl]

theorem levG_of_HPar (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (ex : ℕ → ℕ) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) :
    LevG P k rS r t (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) := by
  obtain ⟨hB, h0⟩ := mem_HPar.1 hg
  rw [mem_btG] at hB
  obtain ⟨s1, s2, s3⟩ := (mem_HPsymF_iff hr).1 h0
  have hI : IntM P (n + 0) (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) :=
    ent_int (c := 0) (g := g.1) (by rw [lamY_eq]; exact g.2)
  have e : ∀ p p' (hp : p < n) (hp' : p' < n),
      redP P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap p p') =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) ⟨p, hp⟩ ⟨p', hp'⟩ :=
    fun p p' hp hp' => red_entB k ex g ⟨p, hp⟩ ⟨p', hp'⟩
  refine ⟨hI, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' h1 h2 h3 => ?_⟩
  · rw [e _ _ (by omega) (by omega)]
    exact s2 ⟨p', hp'⟩
  · rw [e _ _ hp (by omega)]
    by_cases hpr : p < r
    · rcases hz with hz | hz | hz
      · omega
      · exact s1 ⟨p, hpr⟩ ⟨p', hp'⟩ hz
      · exact s3 ⟨p, hpr⟩ ⟨p', hp'⟩ hz.2 hz.1
    · refine hB _ _ ?_
      show coarse r _ p' < coarse r _ p
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (hI _ _ h2 (by omega)) ?_
    rw [e _ _ h2 (by omega)]
    refine hB _ _ ?_
    show coarse r _ p' < coarse r _ p
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr, coarse_of_le (by omega)]
      omega
    · rw [coarse_eq ht (by omega) (by omega), coarse_eq ht (by omega) (by omega), Nat.add_lt_add_iff_right]
      have a1 : (p' - r) / t < i := by rw [Nat.div_lt_iff_lt_mul ht]; omega
      have a2 : i ≤ (p - r) / t := by rw [Nat.le_div_iff_mul_le ht]; omega
      omega

variable {K : Type} [Field K]

theorem phiGS_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {r k rS m i t c' n' : ℕ} (hm : m = i + 1) (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n (g.1.toLinearMap ∘ₗ x) * LocE.unitV (χ i) ((LinearEquiv.det g.1 : Eˣ) : E) =
      ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ ⟨_, hg⟩ : Kˣ) : K) * LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n x := by
  have hL := levG_of_HPar hq hn h ht hr (fun i => i + 1) g hg
  rw [lamPar_val ψ χ hn h ht hr ⟨_, hg⟩ _ (red_entB k (fun i => i + 1) g),
    ← lamGvS_eq ψ χ (by omega) hL.1 (by omega) (by omega)]
  subst hm
  rw [phiGS_eq]
  refine phiM_target (c := 0) ψ χ (by omega) hr (by rw [hn, add_mul]; omega)
    (((HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate (i + 1) t) (HPsymF _ r k rS)).comap (redGL n P)).map (GLint E n P).subtype)
    ?_ ?_ ⟨g, hg, rfl⟩ x
  · rintro _ ⟨g', -, rfl⟩
    rw [lamY_eq]
    exact g'.2
  · rintro _ ⟨g', hg', rfl⟩
    exact levG_of_HPar hq hn h ht hr _ g' hg'

end Lev

theorem phiTop_target_sym : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu true m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu true m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have ht : 0 < R.t := R.t_odd.pos
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  unfold PhiTop
  rw [if_pos hP, if_pos rfl, e1, e2]
  exact phiGS_target hq _ _ hm (rank_X'_eq R) (r_le_X' R) ht a4.le j h x

end GlobalTheory.TopLawSym

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrime
section
namespace GlobalTheory

open Formalism.L2.G.Pend in
theorem wittKbar_eq_zero_of_forall_dvd (p : ℕ) [Fact p.Prime] (z : WW p)
    (h : ∀ N : ℕ, (p : WW p) ^ N ∣ z) : z = 0 := by
  have hc : wToC p z = wToC p 0 := by
    rw [map_zero]
    apply eq_of_close
    intro N
    obtain ⟨b, hb⟩ := h N
    rw [sub_zero, hb]
    exact norm_wToC_pow_mul p N b
  exact wToC_injective p hc

theorem dvd_pow_pow_sub_self_of_dvd {W : Type} [CommRing W] (p n : ℕ)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (x : W) :
    ∀ j : ℕ, (p : W) ∣ x ^ (p ^ (n * j)) - x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (p ^ (n * (j + 1))) = (x ^ (p ^ (n * j))) ^ (p ^ n) := by
      rw [← pow_mul, ← pow_add, mul_add, mul_one]
    rw [e]
    have := dvd_add (h (x ^ (p ^ (n * j)))) ih
    simpa [sub_add_sub_cancel] using this

theorem ringHom_wittKbar_eq_of_modp (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W] (hn : 0 < n)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (f g : W →+* Formalism.L2.G.Pend.WW p)
    (hfg : ∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) : f = g := by
  have key : ∀ k : ℕ, ∀ x : W, (p : Formalism.L2.G.Pend.WW p) ^ k ∣ f x - g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := dvd_pow_pow_sub_self_of_dvd p n h x k
      have hx : x = x ^ (p ^ (n * k)) - (p : W) * y := by rw [← hy]; ring
      have h1 : (p : Formalism.L2.G.Pend.WW p) ^ (n * k + 1) ∣ (f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k)) :=
        dvd_sub_pow_of_dvd_sub (hfg x) (n * k)
      have hk : k + 1 ≤ n * k + 1 := by
        have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
        omega
      have h1' := (pow_dvd_pow (p : Formalism.L2.G.Pend.WW p) hk).trans h1
      have h2 : (p : Formalism.L2.G.Pend.WW p) ^ (k + 1) ∣ (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        rw [pow_succ']
        exact mul_dvd_mul_left _ (ih y)
      have e : f x - g x = ((f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))) - (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        conv_lhs => rw [hx]
        simp only [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e]
      exact dvd_sub h1' h2
  refine RingHom.ext fun x => ?_
  have := wittKbar_eq_zero_of_forall_dvd p (f x - g x) (fun N => key N x)
  exact sub_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinatesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_unitary_logarithmic_coordinates : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  first | exact @GlobalTheory.KerStd.HostLog.subst_unitary | exact GlobalTheory.KerStd.HostLog.subst_unitary | (intros; apply GlobalTheory.KerStd.HostLog.subst_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistLocC
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AmbientDual

theorem twist_locC (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ = TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) := by
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hχ : TruncatedSeriesCountingIdentities.chi1C C g = Units.map (ψ : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (j g)) :=
    Units.ext rfl
  show (((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ g : (↥C.LL.1)ˣ) : ↥C.LL.1) * ψ (rO D.nd i r x (j g) a b) =
    ψ ((((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (j g) a b)
  rw [MonoidHom.inv_apply, hχ, map_mul, MonoidHom.inv_apply, ← map_inv]
  rfl

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambDual (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hD _ w hw _ C τ a
  have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  have hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) := by
    rw [← twist_locC]
    exact (hG w hw C).2 π
  have := D.nd.lPrime i
  have := C.LL.2
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ hc).1
  exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd).2 hdr).2.2 τ a).2

end GlobalTheory.AmbientDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.TameType

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (h : ρ.IsIrreducible) (ν : Γ →* ℂˣ) : (twist ρ ν).IsIrreducible := by
  let f : Subrepresentation (twist ρ ν) → Subrepresentation ρ := fun S =>
    ⟨S.toSubmodule, fun g v hv => by
      have h1 := S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)
      simpa [smul_smul] using h1⟩
  have hn : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
    (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
  have : Nontrivial (Subrepresentation (twist ρ ν)) := ⟨⊥, ⊤, fun e =>
    hn (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with e | e
  · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))

theorem charpoly_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (z : ℂ) :
    (z • (1 : Module.End ℂ V)).charpoly = (X - C z) ^ Module.finrank ℂ V := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

section WD

open GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem weilDeligneParameter_monodromy_zero_of_unramified {a : WD h} (ha : a.unr) : a.mono0 := by
  induction a using WD.ind
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1

theorem inePol_of_unr {a : WD h} (ha : a.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) :
    a.inePol σ = (X - 1) ^ a.lpDim := by
  induction a using WD.ind
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]

theorem inePol_char_of_unr {a c : WD h} (ha : a.unr) (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (X - C z) ^ a.lpDim := by
  rw [← WD.lpDim_char a c hc]
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ,
      ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]

end WD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inertialType_of_tame : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), TameSplitAll H.E → Laws S → TypeTame S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := L.twist _ _ c π₂ τ hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]

end GlobalTheory.TameType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbitStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordBase_of_jumpIn | exact GlobalTheory.HTW.Rec.wordBase_of_jumpIn | (intros; apply GlobalTheory.HTW.Rec.wordBase_of_jumpIn <;> assumption)
end


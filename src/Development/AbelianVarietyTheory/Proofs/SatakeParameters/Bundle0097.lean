import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstInLettersJetLogG
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section
namespace GlobalTheory.OnePlace.Letters

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (n' : ℕ) {β : Type} (v : ZMod n' × β) :
    MvPowerSeries.constantCoeff (jetLogG p n' v) = 0 := by
  show jetLogG p n' v 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  have h2 := congrArg (fun m : ZMod n' × β →₀ ℕ => m (v.1 - 2 * (e : ZMod n'), v.2)) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h2
  exact (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)) h2.symm

def posEquiv (n r0 r1 : ℕ) [NeZero n] : Zidx n r0 r1 ≃ ZMod n × Fin r0 × Fin r1 where
  toFun z := (((z.1 : ℕ) : ZMod n), z.2)
  invFun v := (toFin v.1, v.2)
  left_inv z := by
    ext <;> simp [toFin, ZMod.val_natCast, Nat.mod_eq_of_lt z.1.2]
  right_inv v := by
    ext <;> simp [toFin, ZMod.natCast_zmod_val]

theorem coeff_inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R)
    (m : ZMod n × Fin r0 × Fin r1 →₀ ℕ) :
    MvPowerSeries.coeff m (inLetters f) = MvPowerSeries.coeff (Finsupp.mapDomain (posEquiv n r0 r1).symm m) f := rfl

theorem inLetters_eq_rename {n r0 r1 : ℕ} [NeZero n] {R : Type} [CommRing R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    inLetters f = MvPowerSeries.rename (posEquiv n r0 r1) f := by
  ext m
  have hm : m = Finsupp.mapDomain (posEquiv n r0 r1) (Finsupp.mapDomain (posEquiv n r0 r1).symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have h1 := MvPowerSeries.coeff_embDomain_rename (posEquiv n r0 r1).toEmbedding f
    (Finsupp.mapDomain (posEquiv n r0 r1).symm m)
  rw [Finsupp.embDomain_eq_mapDomain] at h1
  rw [coeff_inLetters]
  conv_rhs => rw [hm]
  exact h1.symm

theorem map_inLetters {n r0 r1 : ℕ} [NeZero n] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries.map φ (inLetters f) = inLetters (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, coeff_inLetters, coeff_inLetters, MvPowerSeries.coeff_map]

theorem subst_inLetters_jetLogG {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} [NeZero n'] (F : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) :
    (∀ z, MvPowerSeries.constantCoeff (jetZ p n' r0 r1 z) = 0) ∧
    MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v)
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters F)) =
    MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F) := by
  refine ⟨fun z => constantCoeff_jetLogG p n' _, ?_⟩
  have ha : MvPowerSeries.HasSubst
      (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by
      rw [map_mul, constantCoeff_jetLogG, mul_zero]
  rw [map_inLetters, inLetters_eq_rename, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) ha]
  congr 1
  funext z
  rw [Function.comp_apply, MvPowerSeries.subst_X ha, map_one, one_mul]
  rfl

end GlobalTheory.OnePlace.Letters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstSumCMul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem pow_wToC (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w))
    (k : ℕ) (w : FormalGroupSystem.WW p) : (σ ^ k) (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] w) := by
  have h : Function.Semiconj (Formalism.L2.G.Pend.wToC p) (sigW p) σ := fun w => (hσ w).symm
  rw [RingHom.coe_pow]
  exact (h.iterate_right k w).symm

theorem comb {κ ι ρ : Type} [Fintype ρ] (S : Finset ι) (a : ι → ℂ_[p]) (b : ι → ρ → ℂ_[p])
    (L : ρ → MvPowerSeries κ ℂ_[p]) (r : ρ) (h : ∀ r', ∑ i ∈ S, a i * b i r' = if r' = r then 1 else 0) :
    ∑ i ∈ S, C (a i) * ∑ r', C (b i r') * L r' = L r := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, h]
  simp

theorem sum_even {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i) := by
  obtain ⟨m, rfl⟩ := he
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i, by simp at hi; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp [IsOddPos] at hs ⊢; omega
  · intro i hi; simp [IsOddPos]
  · intro s hs; simp [IsOddPos] at hs; ext; simp; omega
  · intro i hi; simp
  · intro s hs; simp [IsOddPos] at hs; congr 1; omega

theorem sum_odd {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i + 1) := by
  obtain ⟨m, rfl⟩ := he
  have hm : (m + m) / 2 = m := by omega
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i + 1, by rw [Finset.mem_range, hm] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs; have := s.isLt; rw [Finset.mem_range, hm]; omega
  · intro i hi; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩; show (2 * i + 1) % 2 = 1; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; ext; show 2 * (s.val / 2) + 1 = s.val; omega
  · intro i hi; show (2 * i + 1) / 2 = i; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; congr 1; omega

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem eq_subst_subst {n' : ℕ} [NeZero n'] (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (ht0 : ∀ s, constantCoeff (t s) = 0)
    (hx0 : ∀ r, constantCoeff (x r) = 0) (hxt : ∀ s, subst x (t s) = X s) (f : MvPowerSeries (ZMod n') ℂ_[p]) :
    f = subst x (subst t f) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ht0) (hasSubst_of_constantCoeff_zero hx0),
    show (fun s => subst x (t s)) = X from funext hxt, subst_self]
  rfl

theorem subst_sum_C_mul {κ τ ι : Type} (x : κ → MvPowerSeries τ ℂ_[p]) (hx : HasSubst x) (S : Finset ι)
    (c : ι → ℂ_[p]) (f : ι → MvPowerSeries κ ℂ_[p]) :
    subst x (∑ i ∈ S, C (c i) * f i) = ∑ i ∈ S, C (c i) * subst x (f i) := by
  rw [← coe_substAlgHom hx]
  simp only [map_sum, map_mul, coe_substAlgHom, subst_C]

theorem subst_lg {κ τ : Type} [Finite κ] (x : κ → MvPowerSeries τ ℂ_[p]) (hx0 : ∀ r, constantCoeff (x r) = 0) (k : κ) :
    subst x (GlobalTheory.ThBe0.lg (l := p) k) = PowerSeries.subst (x k) (Formalism.MainNotions.GL3Theta.logF p) := by
  have hx := hasSubst_of_constantCoeff_zero hx0
  rw [GlobalTheory.ThBe0.lg, GlobalTheory.BeProps.subst_psubst hx (constantCoeff_X k), subst_X hx]

theorem hasSubst_jetZ (n' r0 r1 : ℕ) [NeZero n'] : HasSubst (jetZ p n' r0 r1) :=
  hasSubst_of_constantCoeff_zero fun z => by
    rw [jetZ, ← GlobalTheory.BiextInhab.bridge]
    exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_copy {n' r0 r1 : ℕ} [NeZero n'] (a : Fin r0) (b : Fin r1) :
    HasSubst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem subst_jetZ_lin {n' r0 r1 : ℕ} [NeZero n'] (S : Finset (Fin n')) (c : Fin n' → ℂ_[p]) (a : Fin r0) (b : Fin r1) :
    subst (jetZ p n' r0 r1) (∑ s ∈ S, C (c s) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p])) =
      subst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (∑ s ∈ S, C (c s) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n')) := by
  rw [subst_sum_C_mul _ (hasSubst_jetZ n' r0 r1), subst_sum_C_mul _ (hasSubst_copy a b)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subst_X (hasSubst_jetZ n' r0 r1), jetZ, ← GlobalTheory.BiextInhab.bridge]
  rfl

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

theorem zOm_even (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inl r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_pos he]

theorem zOm_odd (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : ¬ Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om' r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inr r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_neg he]

theorem coordZ_jetZ : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w)) → ∀ {n' : ℕ} [NeZero n'], Even n' → ∀ (B : OmBasis p n'), GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) → ∀ (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → ∀ (r0 r1 : ℕ) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1), MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) = PowerSeries.subst (xiE x i) (Formalism.MainNotions.GL3Theta.logF p) := by
  intro p _ σ hσ n' _ he B hD t x ht0 hx0 ht hxt r0 r1 i
  have hx : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  have key : ∀ s : ZMod n', GlobalTheory.ThStr.laS p n' s = subst x (GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r))
      (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) := fun s => by
    rw [← ht s]; exact eq_subst_subst t x ht0 hx0 hxt _
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inl (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by
      simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
        pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r'))) *
            PowerSeries.subst (x (Sum.inl r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : ¬ s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_even p σ _ _ s.val s.isLt (Nat.even_iff.mpr (by omega)), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_even he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')))]
      have hk : ∀ k : ℕ, (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')) =
          (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r') * Formalism.L2.G.Pend.wToC p (B.omS r)) := fun k => by
        rw [map_mul, mul_comm]
      simp only [hk]
      rw [hD.dual r' r]
      by_cases h : r' = r <;> simp [h]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inr (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by
      simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
        pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r'))) *
            PowerSeries.subst (x (Sum.inr r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_odd p σ _ _ s.val s.isLt (Nat.not_even_iff.mpr hs2), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_odd he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r')))]
      have hk : ∀ k : ℕ, (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.omS r')) =
          σ ((σ ^ (2 * k)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r'))) := fun k => by
        rw [← map_mul, pow_succ']; rfl
      simp only [hk]
      rw [← map_sum, hD.dual r r']
      by_cases h : r = r' <;> simp [h, eq_comm]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl

end GlobalTheory.OnePlace.Ident
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateJets
section
noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def TranslateJets (D : D7) (X : ErrX D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  InducedCMType D → HostFieldConditions D →
  ∀ (ig : Fin 2), FamTie D ig cc δ e →
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.g ig →
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → StdAt D (D.host.g ig) L → StdAt D (D.host.g ig) L' →
  ∀ (s : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D s →
  ∀ (t y : VC D N N'), TorsPrime D (D.host.g ig) (La D (tor0 D cc δ) L L') t →
    D.host.φ₀ ((X.piG ig : 𝓞 D.host.E) : D.host.E) • y ∈ La D (tor0 D cc δ) L L' →
  ∀ (P : MvPolynomial (Idx D N N') ℂ) (dg : D.what₂.Tau → ℕ), (∀ m, IntAt lam (P.coeff m)) →
    P.IsWeightedHomogeneous (typeWt D N N') dg → (∑ τ, dg τ) + 1 < D.host.g ig →
    IntAt lam ((∏ τ, embT D τ (D.host.conj ((X.piG ig : 𝓞 D.host.E) : D.host.E)) ^ dg τ) *
      applyAt0 D (inLetters D s P) (U D (tor0 D cc δ) (t + y) (e N N' L L')))

end GlobalTheory.LiftTypePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsW
section
noncomputable section

namespace GlobalTheory.CoefWfUnram

open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

theorem inWf_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : InWf x := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur ..)

theorem coefWf_phW_of_kur (W : WeierstrassCurve ℂ_[p]) (h1 : W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h2 : W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h3 : W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h4 : W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h6 : W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) {s2 : ℂ_[p]} (hs : s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) :
    CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  let K := Formalism.L2.Th1.CM.MaximalUnramifiedExtension p
  let W' : WeierstrassCurve K := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hWW : W'.map K.subtype = W := rfl
  obtain ⟨hl, -, hwp, -, -⟩ := Formalism.L2.Th1.A.zMap K ℂ_[p] K.subtype W'
  obtain ⟨h0, h1', -, -⟩ := Formalism.L2.Th1.A.logSpec K W'
  have hB := (Formalism.L2.Th1.B.baseChange K ℂ_[p] K.subtype ⟨s2, hs⟩ 0 0 (Formalism.L2.Th1.A.wpReg W') 0
    (Formalism.L2.Th1.A.logSer W') 0 h0 h1' (by simp)).2.2.2.2.1
  have e : Formalism.L2.Th1.B.phW W s2 =
      PowerSeries.map K.subtype (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W') (Formalism.L2.Th1.A.logSer W')) := by
    rw [hB, hl, hwp, hWW]
    rfl
  intro n
  rw [e]
  refine inWf_of_kur ?_
  rw [show MvPowerSeries.coeff n (PowerSeries.map K.subtype
      (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W') (Formalism.L2.Th1.A.logSer W')) : MvPowerSeries Unit ℂ_[p]) =
      K.subtype (MvPowerSeries.coeff n (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W')
        (Formalism.L2.Th1.A.logSer W') : MvPowerSeries Unit K)) from MvPowerSeries.coeff_map _ _ _]
  exact (MvPowerSeries.coeff n _ : K).2

theorem coefWf_phW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) :=
  fun _ _ W h1 h2 h3 h4 h6 _ hs => coefWf_phW_of_kur W h1 h2 h3 h4 h6 hs

end GlobalTheory.CoefWfUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDual
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem applyWord_hw_cofRel (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) :
    (∃ μ : Fin (m + 1) → ℕ, IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (applyWord R w (hw R le_rfl ν)) μ) ∧
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (applyWord R w (hw R le_rfl ν)) g := by
  induction w with
  | nil => exact ⟨⟨_, hwRowWeight R _ _ le_rfl ν hν⟩, GlobalTheory.T.exists_cofactorTwist_highestWeight R m ν hν h0⟩
  | cons x w ih =>
    obtain ⟨a, b, k⟩ := x
    obtain ⟨⟨μ, hμ⟩, g, hg, hrel⟩ := ih
    have hstep : applyWord R ((a, b, k) :: w) (hw R le_rfl ν) =
        rowDiv R a b k (applyWord R w (hw R le_rfl ν)) := rfl
    rw [hstep]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul R _ _ μ _ hμ
    refine ⟨h1 a b k, ?_⟩
    by_cases hab : a = b
    · subst hab
      refine ⟨((μ a).choose k) • g, nsmul_mem hg _, ?_⟩
      rw [h2 a k]
      unfold CofRel at hrel ⊢
      rw [map_nsmul, ← hrel, mul_smul_comm]
    · exact ⟨_, zsmul_mem (weylRowDivStable R _ _ le_rfl _ b a k g hg) _, GlobalTheory.T.cofactorTwistRelation_rowDiv_swap R m ν a b k _ g hab hrel⟩

theorem weyl_exists_cofRel : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν,
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν hν h0 f hf
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact (applyWord_hw_cofRel R m ν hν h0 w).2
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hr⟩ := hx
    obtain ⟨g', hg', hr'⟩ := hy
    refine ⟨g + g', add_mem hg hg', ?_⟩
    unfold CofRel at hr hr' ⊢
    rw [map_add, ← hr, ← hr', mul_add]
  | smul c x _ hx =>
    obtain ⟨g, hg, hr⟩ := hx
    refine ⟨c • g, Submodule.smul_mem _ c hg, ?_⟩
    unfold CofRel at hr ⊢
    rw [map_smul, ← hr, mul_smul_comm]

end GlobalTheory.ValCmp
end


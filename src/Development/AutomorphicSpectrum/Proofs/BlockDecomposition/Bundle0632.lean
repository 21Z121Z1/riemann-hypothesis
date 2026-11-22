import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0568
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
section
noncomputable section

open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

def LocConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  (∀ x ∈ twCent θ d, ∀ y ∈ twCent θ d, x * y = y * x) ∧
  (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0) ∧
  {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
    ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite ∧
  (∀ y : G, twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent θ d) ∧
    (twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ d)) ≠ 0)

def UnitConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  f = (K : Set G).indicator 1 ∧ d ∈ K ∧ cptPart (twCent θ d) ≤ K ∧
    ∀ y, y⁻¹ * d * θ y ∈ K → ∃ t ∈ twCent θ d, ∃ k ∈ K, y = t * k

end Generic

section Split

variable {H : Type} [Group H]

def swTw (σ : H →* H) : H × H →* H × H :=
  (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom

@[simp] theorem swTw_apply (σ : H →* H) (y : H × H) : swTw σ y = (σ y.2, σ y.1) := rfl

theorem mem_twCent_swTw (σ : H →* H) (hσ : ∀ g, σ (σ g) = g) (d d' : H) (g : H × H) :
    g ∈ twCent (swTw σ) (d, d') ↔
      g.1 ∈ twCent (MonoidHom.id H) (d * σ d') ∧ g.2 = d' * σ g.1 * d'⁻¹ := by
  obtain ⟨g₁, g₂⟩ := g
  show (g₁, g₂) * (d, d') = (d, d') * (σ g₂, σ g₁) ↔ g₁ * (d * σ d') = d * σ d' * g₁ ∧ g₂ = d' * σ g₁ * d'⁻¹
  simp only [Prod.mk_mul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have e : g₂ = d' * σ g₁ * d'⁻¹ := by rw [← h₂]; group
    refine ⟨?_, e⟩
    rw [← mul_assoc, h₁, e]
    simp only [map_mul, map_inv, hσ]
    group
  · rintro ⟨h₁, rfl⟩
    refine ⟨?_, by group⟩
    simp only [map_mul, map_inv, hσ]
    have : g₁ * d = d * σ d' * g₁ * (σ d')⁻¹ := by
      rw [← h₁]; group
    rw [this]; group

end Split

section Place

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E]

def sgP (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w :=
  (thetaGL a (RingHom.id _)).prodMap (thetaGL b (RingHom.id _))

def ratW (n : ℕ) (w : Pl E) : GL (Fin n) E →* GLw n w := GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))

end Place

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShift
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.ConjEv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_box_iff_forall_valuation_le {m : ℕ} {s : kˣ} {x : Fin m → k} :
    x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s ↔ ∀ j, valuation k (x j) ≤ valuation k (s : k) :=
  Iff.rfl

theorem exists_mulVec_box (m : ℕ) (g : Matrix (Fin m) (Fin m) k) (t : kˣ) :
    ∃ t' : kˣ, ∀ x ∈ box m t, g *ᵥ x ∈ box m t' := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact ⟨t, fun x _ => mem_box_iff_forall_valuation_le.2 fun j => isEmptyElim j⟩
  obtain ⟨ij, hij⟩ := Finite.exists_max (fun ij : Fin m × Fin m => valuation k (g ij.1 ij.2))
  by_cases h0 : g ij.1 ij.2 = 0
  · refine ⟨t, fun x _ => ?_⟩
    have hg : g = 0 := by
      ext i j
      simpa [h0] using hij (i, j)
    rw [hg, Matrix.zero_mulVec]
    exact zero_mem _
  · refine ⟨Units.mk0 _ h0 * t, fun x hx => ?_⟩
    rw [mem_box_iff_forall_valuation_le] at hx ⊢
    intro i
    show valuation k (∑ j, g i j * x j) ≤ _
    refine Finset.sum_induction _ (fun y => valuation k y ≤ valuation k ((Units.mk0 _ h0 * t : kˣ) : k))
      (fun a b ha hb => (valuation k).map_add_le ha hb) (by simp) (fun j _ => ?_)
    rw [map_mul, Units.val_mul, map_mul, Units.val_mk0]
    exact mul_le_mul' (hij (i, j)) (hx j)

theorem box_mono {m : ℕ} {t t' : kˣ} (h : valuation k (t : k) ≤ valuation k (t' : k)) :
    ∀ x ∈ box m t, x ∈ box m t' := by
  intro x hx
  rw [mem_box_iff_forall_valuation_le] at hx ⊢
  exact fun j => le_trans (hx j) h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_mul_inv_le {c r t : kˣ} (h : valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t : k)) :
    valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  have e1 : c * t⁻¹ = (c * r⁻¹) * (r * t⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left]
  have e2 : t * (r * t⁻¹) = r := by
    rw [mul_comm r, ← mul_assoc, mul_inv_cancel, one_mul]
  calc valuation k ((c * t⁻¹ : kˣ) : k)
      = valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((r * t⁻¹ : kˣ) : k) := by
        rw [e1, Units.val_mul, map_mul]
    _ ≤ valuation k (t : k) * valuation k ((r * t⁻¹ : kˣ) : k) := mul_le_mul' h le_rfl
    _ = valuation k (r : k) := by
        rw [← map_mul, ← Units.val_mul, e2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem wt_mir (ψ : AddChar k Circle) {n : ℕ} (p : Mir k n) (y : Fin (n + 1) → k) :
    wt ψ n (((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) = wt ψ n y := by
  unfold GlobalTheory.CompanionTheory.MirPair.wt
  rw [GlobalTheory.BZMir.mulVec_last_of_mem k _ p.2]

theorem absPow_succ_val (s : ℕ) (u : kˣ) :
    ((absPow k ((s + 1 : ℕ) : ℂ) u : ℂˣ) : ℂ) = ((absPow k (s : ℂ) u : ℂˣ) : ℂ) * ((nabs k u : ℝ) : ℂ) := by
  rw [show ((s + 1 : ℕ) : ℂ) = (s : ℂ) + 1 by push_cast; ring, GlobalTheory.SmGL.absPow_add,
    MonoidHom.mul_apply, Units.val_mul, GlobalTheory.SmGL.val_absPow k 1, Complex.cpow_one]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
  (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ)

theorem JJ_conj (hB : TwInv T T' B s) (p : Mir k n) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') :
    JJ ν ψ T B M (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
        (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') =
      ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
        JJ ν ψ T B {y | ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} v v' := by
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hw : ∀ x : Fin (n + 1) → k, GlobalTheory.CompanionTheory.MirPair.wt ψ n x =
      GlobalTheory.CompanionTheory.MirPair.wt ψ n
        ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := GlobalTheory.CompanionTheory.MirPair.ConjEv.wt_mir ψ p⁻¹ x
    rw [Subgroup.coe_inv] at h
    exact h.symm
  have hF := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (p : GL (Fin (n + 1)) k) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n y * GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  have key : ∀ x : Fin (n + 1) → k,
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x *
                   GlobalTheory.CompanionTheory.MirPair.coef T B (T (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
                     (T' (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') x =
        ((GlobalTheory.SmGL.detChar (Fin (n + 1)) (GlobalTheory.SmGL.absPow k (s : ℂ))
            (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
          (GlobalTheory.CompanionTheory.MirPair.wt ψ n
                       ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) *
            GlobalTheory.CompanionTheory.MirPair.coef T B v v'
              ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
    intro x
    rw [hlevi, ← hw]
    ring
  unfold GlobalTheory.CompanionTheory.MirPair.JJ
  simp only [key]
  rw [integral_const_mul, hF, ← mul_assoc]
  congr 1
  rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.ConjEv.absPow_succ_val]

end GlobalTheory.CompanionTheory.MirPair.ConjEv

namespace GlobalTheory.CompanionTheory.MirPair

theorem evVal_conj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB p v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB
    (p : GL (Fin (n + 1)) k) v v'
  obtain ⟨t₁, ht₁₀, ht₁r⟩ : ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t₁ : k) := by
    rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
    · exact ⟨c * r⁻¹, h, le_rfl⟩
    · exact ⟨t₀, le_rfl, h⟩
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.CompanionTheory.MirPair.ConjEv.exists_mulVec_box (n + 1)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) t₁
  refine ⟨t₂, fun t ht => ?_⟩
  rw [GlobalTheory.CompanionTheory.MirPair.ConjEv.JJ_conj ν ψ T T' B s hB p]
  congr 1
  rw [← ht₀ t₁ ht₁₀]
  exact hr t₁ (GlobalTheory.CompanionTheory.MirPair.ConjEv.val_mul_inv_le ht₁r) t
    (fun x hx => GlobalTheory.CompanionTheory.MirPair.ConjEv.box_mono ht _ (ht₂ x hx))

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishing
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem exists_evVal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB v v'
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB 1 v v'
  refine ⟨JJ ν ψ T B (box (n + 1) (c * r⁻¹) : Set (Fin (n + 1) → k)) v v', c * r⁻¹, fun t ht => ?_⟩
  have hc' : valuation k ((c * (c * r⁻¹)⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
    have : c * (c * r⁻¹)⁻¹ = r := by
      rw [_root_.mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
  have hsub : ∀ x ∈ box (n + 1) (c * r⁻¹), ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t := by
    intro x hx
    rw [Units.val_one, one_mulVec]
    rw [mem_box] at hx ⊢
    exact fun i => show valuation k (x i) ≤ valuation k (t : k) from
      le_trans (show valuation k (x i) ≤ valuation k ((c * r⁻¹ : kˣ) : k) from hx i) ht
  have h := hr (c * r⁻¹) hc' t hsub
  rw [← h]
  simp only [Units.val_one, one_mulVec]
  rfl

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_block_ne_zero_of_isUnder {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : IsUnder y z) (k : Fin (m + 1)) :
    ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨ptChart _ k, (h k _).1.1 (CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩

theorem combLine_unit_a (A : HermLine (Bk n)) : (combLine (fun _ : Unit => A) 1).a = A.a := by
  simp [combLine]

theorem combLine_unit_h (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = A.h z := by
  simp [combLine, if_pos hz]

theorem combLine_unit_h_off (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = 0 :=
  if_neg hz

theorem isHermRep_combLine_unit {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hA : IsHermRep M A) :
    IsHermRep M (combLine (fun _ : Unit => A) 1) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hA
  refine ⟨u, h₁, fun i c c' => ?_, fun i c y z hu hy => ?_⟩
  · rw [combLine_unit_a]
    exact h₂ i c c'
  · rw [combLine_unit_h A (exists_block_ne_zero_of_isUnder hu), combLine_unit_a]
    exact h₃ i c y z hu hy

theorem existsRead : ExistsRead := by
  rintro m n M ⟨c, t, e⟩
  obtain ⟨A, hA, -⟩ := GlobalTheory.T.hermRep_twisted_bundle_exists m n M c t e
  have hs : IsSmoothHerm A := GlobalTheory.CompanionTheory.MPDict.SmoothRep.isSmoothHerm_of_isHermRep m n M A hA
  exact ⟨combLine (fun _ : Unit => A) 1, isSmoothHerm_combLine (fun _ => hs) 1, isHermRep_combLine_unit hA,
    fun z hz => combLine_unit_h_off A hz⟩

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem det_dia (γ : GL (Fin 2) ℚ) : GeneralLinearGroup.det (dia2 γ) = pri (GeneralLinearGroup.det γ) := by
  ext
  simp only [pri, dia2, AdelicGLn.diagonal]
  simpa using (RingHom.map_det (algebraMap ℚ 𝔸[ℚ]) (γ : Matrix (Fin 2) (Fin 2) ℚ)).symm

theorem Dt_pos (g : G2) : 0 < Dt g := (IdeleGroup.ideleModule ℚ (GeneralLinearGroup.det g)).2

theorem Dt_ne (g : G2) : ((Dt g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Dt_pos g).ne'

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_inv (a : Jd) : md a⁻¹ = (md a)⁻¹ := by
  simp [md, map_inv]

theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp [Dt, md_mul, map_mul]

theorem md_pri (α : ℚˣ) : md (pri α) = 1 := by
  have : pri α = IdeleGroup.diagonal ℚ α := rfl
  rw [md, this, IdeleGroup.ideleModule_diagonal]; rfl

theorem toIdele_pri (c : HeckeCharacter ℚ) (α : ℚˣ) : c.toIdele (pri α) = 1 := by
  have : pri α = IdeleGroup.diagonal ℚ α := rfl
  rw [this, HeckeCharacter.toIdele_diagonal]

theorem det_dg (z : Jd) : GeneralLinearGroup.det (dg2 z z : G2) = z * z := by
  ext
  simp [dg2, Matrix.det_fin_two]

theorem continuous_Dt : Continuous Dt :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det ℚ 2))

theorem measurable_Dt : Measurable Dt := continuous_Dt.measurable

theorem continuous_cdet (c : HeckeCharacter ℚ) : Continuous (cdet c) :=
  continuous_induced_dom.comp ((c.continuous_toIdele).comp (AdelicGLn.continuous_det ℚ 2))

theorem measurable_cdet (c : HeckeCharacter ℚ) : Measurable (cdet c) := (continuous_cdet c).measurable

theorem norm_cdet (c : HeckeCharacter ℚ) (g : G2) : ‖cdet c g‖ = 1 := by
  simp [cdet, Circle.norm_coe]

theorem Dt_dia (γ : GL (Fin 2) ℚ) (g : G2) : Dt (dia2 γ * g) = Dt g := by
  rw [Dt_mul, Dt, det_dia, md_pri, one_mul]

theorem Dt_dg (z : Jd) (g : G2) : Dt (dg2 z z * g) = md z ^ 2 * Dt g := by
  rw [Dt_mul, Dt, det_dg, md_mul, sq]

theorem cdet_mul (c : HeckeCharacter ℚ) (g h : G2) : cdet c (g * h) = cdet c g * cdet c h := by
  simp [cdet, map_mul]

theorem cdet_dia (c : HeckeCharacter ℚ) (γ : GL (Fin 2) ℚ) (g : G2) : cdet c (dia2 γ * g) = cdet c g := by
  rw [cdet_mul, cdet, det_dia, toIdele_pri]; simp

theorem cdet_dg (c : HeckeCharacter ℚ) (z : Jd) (hz : c.toIdele z = 1) (g : G2) : cdet c (dg2 z z * g) = cdet c g := by
  rw [cdet_mul, cdet, det_dg, map_mul, hz]; simp

theorem dg_mul (a b : Jd) : (dg2 a a * dg2 b b : G2) = dg2 (a * b) (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_one : (dg2 1 1 : G2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem det_det_inverse_twist (g : G2) : GeneralLinearGroup.det (inv2 g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [inv2, map_mul, det_dg]
  group

theorem det_inverse_twist_involutive (g : G2) : inv2 (inv2 g) = g := by
  rw [inv2, det_det_inverse_twist, inv_inv, inv2, ← mul_assoc, dg_mul]
  simp [dg_one]

theorem module_det_inverse_twist (g : G2) : Dt (inv2 g) = (Dt g)⁻¹ := by
  rw [Dt, det_det_inverse_twist, md_inv]; rfl

theorem character_det_inverse_twist (c : HeckeCharacter ℚ) (g : G2) : cdet c (inv2 g) = cdet c⁻¹ g := by
  simp only [cdet, det_det_inverse_twist, map_inv]
  rfl

theorem module_cpow_det_inverse_twist (s : ℂ) (g : G2) : ((Dt (inv2 g) : ℝ) : ℂ) ^ s = ((Dt g : ℝ) : ℂ) ^ (-s) := by
  rw [module_det_inverse_twist, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (Dt_pos g).le]; exact Real.pi_pos.ne)]

theorem cpow_dg (s : ℂ) (z : Jd) (g : G2) :
    ((Dt (dg2 z z * g) : ℝ) : ℂ) ^ s = ((md z ^ 2 : ℝ) : ℂ) ^ s * ((Dt g : ℝ) : ℂ) ^ s := by
  rw [Dt_dg, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (Dt_pos g).le]

theorem Aut.inv2 {H : G2 → ℂ} (hH : Aut H) (g : G2) : H (Ad3.R.inv2 g) = H g := hH.cen _ _

def Zp (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ {g | 1 ≤ Dt g}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ

def Bd (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ band, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s ∂μ

def Jl (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s ∂μ

theorem measurable_w {H : G2 → ℂ} (hH : Aut H) (c : HeckeCharacter ℚ) (s : ℂ) :
    Measurable fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s :=
  (hH.cont.measurable.mul (measurable_cdet c)).mul
    ((Complex.measurable_ofReal.comp measurable_Dt).pow_const s)

theorem linv_w {H : G2 → ℂ} (hH : Aut H) (c : HeckeCharacter ℚ) (s : ℂ) :
    LInv fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s := fun γ g => by
  simp only [hH.left γ g, cdet_dia, Dt_dia]

theorem linv_ind {X : Type} [Zero X] {F : G2 → X} (hF : LInv F) (A : Set ℝ) :
    LInv (Set.indicator {g | Dt g ∈ A} F) := fun γ g => by
  simp only [Set.indicator, Set.mem_setOf_eq, Dt_dia, hF γ g]

end GlobalTheory.CompanionTheory.RSZeta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvarietyStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multicone_point_descends_to_subvariety : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts | exact GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinatesStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_chart_holomorphic_coordinates : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
  ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
    {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo | exact GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.mchart_affine_holo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroupStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mem_norm_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  first | exact @GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | exact GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | (intros; apply GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUniformLimitStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_uniform_limit : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  first | exact @GlobalTheory.CompanionTheory.FJLim.fj_tendsto | exact GlobalTheory.CompanionTheory.FJLim.fj_tendsto | (intros; apply GlobalTheory.CompanionTheory.FJLim.fj_tendsto <;> assumption)
end


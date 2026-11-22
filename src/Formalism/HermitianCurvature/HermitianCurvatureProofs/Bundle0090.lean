import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_of (k r o : ℕ) (A : ℝ)
    (h : 12 * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  push_cast at h
  constructor <;>
    nlinarith [mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hr), mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hk),
      mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr, mul_nonneg (mul_nonneg hr hr) hk, mul_nonneg hr hk,
      mul_nonneg (mul_nonneg hr hr) ho, mul_nonneg hr ho]

theorem inCC_pred {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {o : ℕ}
    {F : Mat k r → E} (h : InCC A (o + 1) F) : InCC A o F := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast Nat.le_succ o), hfe⟩

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem bigPos_sub (D : RealPlaceData k r Wp Wq) : Formalism.FourierDecayAlt.C6.bigPos D ⊆ Om k r D.z D.z' := by
  intro g hg
  simp only [Formalism.FourierDecayAlt.C6.bigPos, Formalism.FourierDecayAlt.C6.domL, Set.mem_ofPred_eq] at hg
  obtain ⟨hgv, hgf, hd⟩ := hg
  show g ∈ GV k r ∩ Q.OmPlus k r D.z D.z'
  exact ⟨hgv, fun l _ => hd l (Finset.mem_univ l), hgf⟩

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 := by
  refine ⟨hg, fun a ha => ?_⟩
  simp at ha

theorem psi_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n : Mat k r} (hn : n ∈ Nset k r) :
    psi k r z cStd n⁻¹ = (psi k r z cStd n)⁻¹ := by
  have h := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z cStd hz n hn
  rw [← h]
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal]

theorem xiTau_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) :
    xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * (psi k r D.z' cStd (Matrix.of p.2.2))⁻¹ := by
  unfold xiTau lam psi
  push_cast
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp]

theorem jf_equiv (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (hp : D.inSS p)
    (g : Mat k r) : rho D p (JF D F) g = (xiTau D (1, 1) p)⁻¹ • JF D F g := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z'
  have hU := Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarW.conc D.haarW'.conc D.haarW.left D.haarW'.left
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep
  have hNe := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarN.left
  have key : JF D F (sgs p g) =
      (psi k r D.z cStd (Matrix.of p.1.2)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2)) •
        (D.π (Matrix.of p.1.1)⁻¹).comp ((JF D F g).comp (D.π' (Matrix.of p.2.1))) := by
    unfold Formalism.FourierDecayAlt.B.JF Formalism.FourierDecayAlt.B.sgs
    rw [show (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 by
      simp only [Matrix.mul_assoc]]
    rw [hU _ _ (hW.inv_mem _ h1) _ h3, hNe _ _ (hN.inv_mem _ h2) _ h4,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  ext x
  simp only [rho, key, ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]
  rw [Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π'_rep h3 (hW'.inv_mem _ h3) (Matrix.mul_nonsing_inv _ (hW'.unit _ h3)) x,
    Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π_rep h1 (hW.inv_mem _ h1) (Matrix.mul_nonsing_inv _ (hW.unit _ h1))]
  congr 1
  rw [xiTau_eq, psi_inv D.z_mem h2, mul_inv, inv_inv]

end

end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_integral_commutes_large : Formalism.FourierDecayAlt.C6.JCommuteBig := by
  refine ⟨12, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D Θ A F _ hcomm hA hF
  have hthr := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.thrW_of k r (opOrder Θ) A hA
  have hF' := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.inCC_pred hF
  obtain ⟨hck, -⟩ := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq D A (opOrder Θ) F hthr hF'
  refine ⟨?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hO := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.bigPos_sub D hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hck g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hO.1, hO.2⟩
    exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgv => hfe g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgv)⟩
  · intro p hp g _
    exact Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.jf_equiv D F p hp g
  · intro g hg
    exact (Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set k r Wp Wq D A (opOrder Θ) F Θ _ (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.bigPos_sub D) le_rfl
      hthr hF' hcomm g hg).symm

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZCompLeft
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

abbrev Coef (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] : Type :=
  (j : ℕ) → ℂ → (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))

abbrev AnnZ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Set ℂ :=
  {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}

abbrev Dj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (j : ℕ)
    (q : (Fin P.r → ℂ) × ℂ) : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) :=
  iteratedFDeriv ℝ j (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec Φ (q.1, ζ)) q.2

def Rep (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (n : ℕ) (A : Coef Wp Wq) : Prop :=
  (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j) (AnnZ P Bs)) ∧
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q.2 (Dj P Bs (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) j q)

theorem rep_ext {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {n m : ℕ} (hnm : n ≤ m) {A : Coef Wp Wq}
    (h : Rep P Bs T n A) : Rep P Bs T m (fun j ζ => if j ≤ n then A j ζ else 0) := by
  refine ⟨fun j => ?_, fun Φ q hq => ?_⟩
  · by_cases hj : j ≤ n
    · simp only [hj, if_true]; exact h.1 j
    · simp only [hj, if_false]; exact contDiffOn_const
  · rw [h.2 Φ q hq]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ m + 1))]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≤ n := by simp at hj; omega
      simp only [this, if_true]
    · intro j _ hj
      have : ¬ j ≤ n := by simp at hj; omega
      simp only [this, if_false, ContinuousLinearMap.zero_apply]

theorem radR_smul' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : ℂ) (F : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (c • F) x = c • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec F x := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radR_zero'' (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x = 0 := by
  unfold NF.radR
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z' <;> simp [hx]

theorem radDZ_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  have : (((0 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = 0 := rfl
  rw [this, radR_zero'']
  simp

theorem radDZ_one (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    RadDZ P Bs (1 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) := by
  refine ⟨0, fun j _ => ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun _ => 0),
    fun _ => contDiffOn_const, fun Φ q _ => ?_⟩
  rw [Finset.sum_range_one]
  show _ = (iteratedFDeriv ℝ 0 (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2)
    (fun _ => 0)
  rw [iteratedFDeriv_zero_apply]
  rfl

theorem radDZ_add {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T1 T2 : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (h1 : RadDZ P Bs T1) (h2 : RadDZ P Bs T2) :
    RadDZ P Bs (T1 + T2) := by
  obtain ⟨n1, A1, hr1⟩ := h1
  obtain ⟨n2, A2, hr2⟩ := h2
  have e1 := rep_ext (by omega : n1 ≤ n1 + n2) hr1
  have e2 := rep_ext (by omega : n2 ≤ n1 + n2) hr2
  refine ⟨n1 + n2, fun j ζ => (if j ≤ n1 then A1 j ζ else 0) + (if j ≤ n2 then A2 j ζ else 0),
    fun j => (e1.1 j).add (e2.1 j), fun Φ q hq => ?_⟩
  have hc : ((T1 + T2) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = (T1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) + (T2 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
  rw [hc, Formalism.FourierDecayAlt.P.NFRO.radR_add, e1.2 Φ q hq, e2.2 Φ q hq, ← Finset.sum_add_distrib]
  rfl

theorem radDZ_sum {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (h : ∀ i ∈ s, RadDZ P Bs (T i)) :
    RadDZ P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radDZ_zero P Bs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact radDZ_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem radDZ_comp_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T)
    (Mf : ℂ → ((Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp)))
    (hM : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Mf (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        Mf q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) :
    RadDZ P Bs T' := by
  obtain ⟨n, A, hA, hTA⟩ := hT
  refine ⟨n, fun j ζ => (Mf ζ).comp (A j ζ), fun j => hM.clm_comp (hA j), fun Φ q hq => ?_⟩
  rw [h Φ q hq, hTA Φ q hq, map_sum]
  rfl

theorem radDZ_fun_left {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T T' : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (s : ℂ → ℂ)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s (AnnZ P Bs))
    (h : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
      NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T' Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
        s q.2 • NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) :
    RadDZ P Bs T' :=
  radDZ_comp_left hT (fun ζ => s ζ • ContinuousLinearMap.id ℝ (Wq →L[ℂ] Wp)) (hs.smul contDiffOn_const)
    fun Φ q hq => by rw [h Φ q hq]; rfl

theorem radDZ_smul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) (c : ℂ) :
    RadDZ P Bs (c • T) :=
  radDZ_fun_left hT (fun _ => c) contDiffOn_const fun Φ q _ => by
    have : ((c • T) Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) = c • (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl
    rw [this, radR_smul']

theorem radDZ_neg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) : RadDZ P Bs (-T) := by
  have := radDZ_smul hT (-1)
  rwa [neg_one_smul] at this

end closure

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Formalism.FourierDecayAlt.ThreeDimData

section Basic

variable {k r : ℕ}

theorem psi_norm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1 := by
  simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : Mx k r => Formalism.QuantumDeterminants.psi k r z c g) := by
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  refine continuous_finset_sum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    fun_prop

theorem isClosed_UH : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) : Set (Mx k r)) := by
  show IsClosed {g : Mx k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) := by
  have h1 : IsClosed {g : Mx k r | g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := isClosed_UH
  have h2 : IsClosed {g : Mx k r | ∀ a : Fin r, g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧ g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h3 : IsClosed {g : Mx k r | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact h1.inter (h2.inter h3)

theorem aesm_of_contOn {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] [NormedAddCommGroup E] [SecondCountableTopology E]
    {μ : Measure α} {f : α → E} {s : Set α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) : AEStronglyMeasurable f μ := by
  have h := hf.aestronglyMeasurable hs (μ := μ)
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h

theorem key_bound {A S X Y a : ℝ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hS0 : 0 < S) (ha : 0 < a)
    (hS : S ≤ A * X * Y) : Y ^ (-a) * A ^ (-a) ≤ X ^ (a / 2) * (Y ^ (-(a / 2)) * S ^ (-(a / 2))) := by
  have hA0 : 0 < A := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have y1 : 0 < Y ^ (-a) := Real.rpow_pos_of_pos hY0 _
  have a1 : 0 < A ^ (-a) := Real.rpow_pos_of_pos hA0 _
  have x2 : 0 < X ^ (a / 2) := Real.rpow_pos_of_pos hX0 _
  have y2 : 0 < Y ^ (-(a / 2)) := Real.rpow_pos_of_pos hY0 _
  have s2 : 0 < S ^ (-(a / 2)) := Real.rpow_pos_of_pos hS0 _
  have h1 : Real.log S ≤ Real.log A + Real.log X + Real.log Y := by
    have e1 : Real.log (A * X * Y) = Real.log A + Real.log X + Real.log Y := by
      rw [Real.log_mul (mul_pos hA0 hX0).ne' hY0.ne', Real.log_mul hA0.ne' hX0.ne']
    rw [← e1]
    exact Real.log_le_log hS0 hS
  have h2 : 0 ≤ Real.log A := Real.log_nonneg hA
  rw [← Real.log_le_log_iff (mul_pos y1 a1) (mul_pos x2 (mul_pos y2 s2)),
    Real.log_mul y1.ne' a1.ne', Real.log_mul x2.ne' (mul_pos y2 s2).ne', Real.log_mul y2.ne' s2.ne',
    Real.log_rpow hY0, Real.log_rpow hA0, Real.log_rpow hX0, Real.log_rpow hY0, Real.log_rpow hS0]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_nonneg ha.le h2]

end Basic

section Repro

end Repro

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.of fun a b => star (M a b)).det = star M.det := by
  have e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

theorem keyS_sR (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by
  simp only [sR]
  rw [keyS_esI]
  rfl

theorem AAv_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (ell : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → p ∉ Set.range (sR k r i0 hi0) → y a p = 0)
    (hh : ∀ a b : Fin i0, y (Fin.castLE hi0 a) (sR k r i0 hi0 b) = star (h a b)) :
    AAv k r E y i0 hi0 ell = star h.det • qminor E (sR k r i0 hi0) (sR k r i0 hi0) (ell + (i0 : ℂ) - 1) := by
  classical
  have hsv : ∀ l : Fin i0, (sR k r i0 hi0 l).val = 2 * r + k - l.val := by
    intro l
    simp [sR, Formalism.QuantumDeterminants.esI]
  have he : StrictMono (fun l => keyS k r (sR k r i0 hi0 l)) := by
    intro a b hab
    simp only [keyS_sR]
    exact hab
  have hX : ∀ (a : Fin i0) (p : Fin (2 * r + k + 1)), p ∉ Set.range (sR k r i0 hi0) →
      y (Fin.castLE hi0 a) p = 0 := by
    intro a p hp
    exact hz _ p a.isLt hp
  have hu : ∀ c : Fin i0 → Fin (2 * r + k + 1), StrictMono (fun l => keyS k r (c l)) →
      (∀ l, c l ∈ Set.range (sR k r i0 hi0)) → c = sR k r i0 hi0 := by
    intro c hc hS
    exact uniq_key (keyS k r) (keyS_inj k r) (sR k r i0 hi0) c he hc hS
  have hs := sum_single (M := A) (fun B : Fin i0 → Fin (2 * r + k + 1) => StrictMono (fun l => keyS k r (B l)))
    (fun a p => y (Fin.castLE hi0 a) p) (Set.range (sR k r i0 hi0)) hX (sR k r i0 hi0) he hu
    (fun B => qminor E B (sR k r i0 hi0) (ell + (i0 : ℂ) - 1))
  have hdet : (Matrix.of fun a l : Fin i0 => y (Fin.castLE hi0 a) (sR k r i0 hi0 l)).det = star h.det := by
    rw [← det_star]
    congr 1
    ext a b
    exact hh a b
  unfold AAv
  rw [← hdet]
  convert hs using 1

theorem second_expansion_identity : ExpansionDualColumn := by
  intro A _ _ M _ _ k r z' E La y i0 s h t ell hs hj hG hR hh ht hy
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  have hm' : i0 + s' + 1 ≤ r := by omega
  rw [AAv_congr k r E y (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm]
  set e2 : Fin (i0 + s') → Fin (2 * r + k + 1) :=
    fun l => sR k r (i0 + s' + 1) hm' ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) with he2def
  have he2v : ∀ l, (e2 l).val = 2 * r + k - ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp [e2, sR, esI]
  have he2k : ∀ l, keyS k r (e2 l) = ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp only [e2]; rw [keyS_sR]
  have he2 : StrictMono (fun l => keyS k r (e2 l)) := by
    intro a b hab
    simp only [he2k]; exact Fin.strictMono_succAbove _ hab
  have hAA : AAv k r E y (i0 + s') hm ell =
      star (h.det * t ^ s' * sgnW s') • qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1) := by
    unfold AAv
    rw [sum_single (fun B => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hm a) p)
      (Set.range e2) ?_ e2 he2 ?_]
    · congr 1
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp, ← det_star]
      congr 1
      ext a l
      simp only [Matrix.of_apply]
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      rw [hy _ _ (by simp; omega), if_pos (by rw [he2v]; omega), he2v]
      congr 2 <;> (try simp) <;> omega
    · intro a p hp
      rw [hy _ _ (by simp; omega)]
      split_ifs with h1
      · by_cases hpi : 2 * r + k - p.val = i0
        · rw [hpi, zb_col_zero i0 s' h t _ (by simp), star_zero]
        · exfalso; apply hp
          refine ⟨⟨if 2 * r + k - p.val < i0 then 2 * r + k - p.val else 2 * r + k - p.val - 1,
            by split_ifs <;> omega⟩, ?_⟩
          ext; rw [he2v, succAbove_val]; simp only; split_ifs <;> omega
      · rfl
    · intro c hc hS; exact uniq_key (keyS k r) (keyS_inj k r) _ _ he2 hc hS
  have hhead : AAv k r E y i0 (by omega) ell =
      star h.det • qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hy _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * r + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * r + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dif_pos ha, dif_neg hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hy _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k r i0 (by omega) b).val = 2 * r + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ r) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dif_pos a.isLt, dif_pos (by omega)]
      congr 2
      apply Fin.ext; simp only [Fin.val_mk]; omega
  have hP := third_peeling_identity A k r z' E hG (i0 + s') hm' ⟨i0, by omega⟩ ell
  have hLa : La (qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)) =
      La (qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1)) := la_congr hR hP
  rw [hAA, hhead, map_smul, map_smul, hLa, (derivative_leading_zb i0 (s' + 1) h t).1, (derivative_leading_zb i0 (s' + 1) h t).2,
    smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [star_mul', star_pow, star_sgnW, sgnW_succ, Nat.add_sub_cancel, star_neg, star_one]
  rw [scal_E (star h.det) (star t) (sgnW s') ((-1) ^ s') s' (star_ne_zero.mpr hh) (star_ne_zero.mpr ht)
    (sgnW_sq s') (neg_one_sq' s')]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end


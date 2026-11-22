import Formalism.LocalToGlobal.InertKernelTheory.Bundle0008
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HalfTorsionNotMemCmLattice
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KappaSelfDualFourthPowerLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.Bundle0001
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConstantCoeffFormalSum
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
section
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4 stdChar)
open Formalism.L2.Th1.Top (IsLTNorm)

namespace ReBase

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} (hcc : TaylorLogMetric.IsCurveIdeal D cc) : Odd (Ideal.absNorm cc) := by
  have hc2 : Nat.Coprime (Ideal.absNorm cc) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 _) hcc.2
  rcases Nat.even_or_odd (Ideal.absNorm cc) with he | ho
  · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 he) hc2) (by decide)
  · exact ho

theorem cm_change_of_base : CmReBase := by
  intro D cc δ B hcc hδ
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, -, hlat⟩ := curve_lattice_compatible D cc δ hcc.1 (odd_norm hcc) hδ
  have hlat' : (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := hlat.symm
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat', KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat', ?_⟩
  have e : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    rw [KS.theta_val']; ring
  have h := KS.half_period_unique_CM a₀ b₀ c₀ D.host.d ha hd _ hl hcm (B.ω₀ / 2)
    ((KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat' _).1 B.t0.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', KS.theta_val']; exact B.t0.2.1)
    (by rw [← KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat', ← e]; exact B.t0.2.2)
  rw [KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat',
    show (B.ω₀ - (g : ℂ) * δ * a₀) / 2 = B.ω₀ / 2 - (g : ℂ) * δ * a₀ / 2 by ring]
  exact h

theorem isThMM_eq {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B B' : Base D cc δ) (hγ : B'.gC = B.gC)
    (hκ : B'.kappa = B.kappa) (hω : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice) : B'.IsThMM = B.IsThMM := by
  have h := KS.lattice_eq B B'
  have e : IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa = IsThM B'.L B'.ω₀ B.cq B.lamM B.gC B.kappa := by
    funext θ
    unfold IsThM kernel4 Formalism.L2.Th1.H.F0 Formalism.L2.Th1.H.stdLat
    rw [KS.hOne_congr h, KS.stdH_congr h, KS.thetaNull_congr_lattice h hω (Base.half_not_mem B'), h]
  show IsThM B'.L B'.ω₀ B.cq B.lamM B'.gC B'.kappa = IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa
  rw [hγ, hκ, e]

theorem theta_change_of_base : ThMMReBase := by
  intro D cc δ B hcc
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, hcm, hN, hlat, ht, hω⟩ := cm_change_of_base D cc δ B hcc (delta_ne_of_base B)
  have hω' : (B.ω₀ - (g : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice :=
    (KS.mem_lam_iff a₀ b₀ ha hd _ hl hlat _).1 hω
  refine ⟨a₀, g, b₀, c₀, ha, hd, hl, KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat, hcm, hN,
    KS.cmBase_isCm B a₀ b₀ c₀ ha hd _ hl hcm hlat, KS.lattice_eq _ B, rfl, rfl, rfl,
    (KS.lattice_eq B (KS.cmBase B a₀ b₀ c₀ ha hd ((g : ℂ) * δ) hl hcm hlat)) ▸ hω',
    isThMM_eq B _ rfl rfl hω', (KS.thMM_reBase B _ hlat _ (KS.isTorsionPoint_standard_CM a₀ b₀ c₀ ha hd _ hl hcm hlat) hω').symm⟩

theorem stdLat_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : Type) : stdLat L n = stdLat L' n := by
  unfold Formalism.L2.Th1.H.stdLat; rw [h]

theorem isLTNorm_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 s2 ε : MaximalUnramifiedExtension l) : IsLTNorm l L ι g2 g3 s2 ε ↔ IsLTNorm l L' ι g2 g3 s2 ε := by
  obtain ⟨-, -, -, -, hs, -, -, h2, h3⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  unfold IsLTNorm
  rw [h2, h3, hs]

theorem th0Char_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    {x : ℂ} (hx : x ∈ L'.lattice) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x = Formalism.L2.Th1.F.thetaZeroCharacter L' ω₀' x := by
  obtain ⟨-, -, -, hA, -, -, -, -, -⟩ := Formalism.L2.Th1.F.latticeOnly L L' h
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L' x ((ω₀ - ω₀') / 2) hx hω
  have e0 : x * (starRingEnd ℂ) ω₀ / (Formalism.L2.Th1.F.area L' : ℂ) = x * (starRingEnd ℂ) ω₀' / (Formalism.L2.Th1.F.area L' : ℂ) +
      2 * (x * (starRingEnd ℂ) ((ω₀ - ω₀') / 2) / (Formalism.L2.Th1.F.area L' : ℂ)) := by
    simp only [map_div₀, map_sub, map_ofNat]; ring
  have e1 : Formalism.L2.Th1.F.altE L x ω₀ = Formalism.L2.Th1.F.altE L' x ω₀' + 2 * Formalism.L2.Th1.F.altE L' x ((ω₀ - ω₀') / 2) := by
    simp only [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm, hA]
    rw [e0]
    simp [Complex.add_im, Complex.mul_im]
  unfold Formalism.L2.Th1.F.thetaZeroCharacter Formalism.L2.Th1.F.semiChar
  rw [h, e1, hk]
  congr 1
  rw [show ((Formalism.L2.Th1.F.altE L' x ω₀' + 2 * (k : ℝ) : ℝ) : ℂ) = (Formalism.L2.Th1.F.altE L' x ω₀' : ℂ) + (k : ℂ) * 2 by
    push_cast; ring]
  rw [mul_add, Complex.exp_add, show (Real.pi : ℂ) * Complex.I * ((k : ℂ) * 2) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem stdData_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ} (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice)
    (hn : ω₀ / 2 ∉ L.lattice) {n : Type} [Fintype n] [DecidableEq n] {hh : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)}
    {α : (n → ℂ) → ℂ} {β : (Fin 4 × n → ℂ) → ℂ} {g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)}
    (S : StdData L' ω₀' hh Λ α β g) : StdData L ω₀ hh Λ α β g := by
  have hS := KS.stdH_congr h (Fin 4 × n)
  have hL := stdLat_congr h (Fin 4 × n)
  refine ⟨?_, hn, ?_, S.alpha0, ?_, ?_, S.betaAlpha, ?_, ?_, ?_⟩
  · rw [h, show ω₀ = ω₀' + ((ω₀ - ω₀') / 2 + (ω₀ - ω₀') / 2) by ring]
    exact add_mem S.per (add_mem hω hω)
  · rw [hS]; exact S.isom
  · intro x hx
    have hx' : x ∈ stdLat L' (Fin 4 × n) := hL ▸ hx
    rw [S.betaStd x hx']
    unfold Formalism.L2.Th1.H.stdChar
    exact (Finset.prod_congr rfl fun i _ => th0Char_congr h hω (hx' i (Set.mem_univ i))).symm
  · rw [hS]; exact S.betaSemi
  · rw [hS]; exact S.selfDual
  · rw [hL]; exact S.idx₁
  · rw [hL]; exact S.idx₂

theorem k1ThetaAllBases : FirstKernelThetaAllBases := by
  intro D cc δ B hcc hδ l _ h5 hj ι
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, B', hcm, -, hIs, hlat, -, -, -, hω, -, hth⟩ := theta_change_of_base D cc δ B hcc
  have h : B.L.lattice = B'.L.lattice := hlat.symm
  have hω' : (B.ω₀ - B'.ω₀) / 2 ∈ B'.L.lattice := h ▸ hω
  obtain ⟨G, hS, hidx, hK⟩ := Kap.K1_theta_inert_prime D cc δ B' hcc hδ a₀ b₀ c₀ ha hd _ hl hcm hIs l h5 hj ι
  refine ⟨G, ?_, ?_, ?_⟩
  · have hS' := hS
    rw [← KS.hOne_congr h, ← KS.stdH_congr h] at hS'
    exact stdData_congr h hω' (Base.half_not_mem B) hS'
  · rw [stdLat_congr h]; exact hidx
  · intro g2 g3 ε s2 hN hg2 hg3 hD hε hth' t N hN0 hlN hNt σ γ B'' hF
    have := hK g2 g3 ε s2 ((isLTNorm_congr h l ι g2 g3 s2 ε).1 hN) hg2 hg3 hD hε hth' t N hN0 hlN hNt σ γ B'' hF
    rw [← KS.hOne_congr h, hth] at this
    exact this

end ReBase

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepAsm
section
noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem k1gen_of_orth {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) {be : MvPowerSeries (Fin 2) (K0 l)} (hB : BeProp l be)
    {g2 g3 ε s2 : MaximalUnramifiedExtension l} (hC : CurveAt l be g2 g3 ε s2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]} (hO : OrthInt l g2 g3 s2 ε Th) :
    @ExtensionGeneratorCondition l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be Th := by
  obtain ⟨hg2, hg3, hε, hθ, hN, hbe0, F, hF, hTie⟩ := hC
  obtain ⟨r, Θ, σ, f, f', hσ, hP, rfl, hI⟩ := hO
  have hInt := hyperbolic_of_orthogonal l h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF (hN σ hσ) ι (Fin r) f f' hP be hbe0 hTie Θ hI
  exact @first_kernel_of_sum l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be _ hB (sum_beta_even l (by omega) ι be hB) hInt

theorem representativeCondition_of_curve_orthAll {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (be : MvPowerSeries (Fin 2) (K0 p))
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p be) (g2 g3 ε s2 : MaximalUnramifiedExtension p) (hC : CurveAt p be g2 g3 ε s2)
    (hO : OrthAll X E hfin pos F g2 g3 s2 ε) :
    Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.RepresentativeCondition X E hfin be pos F := by
  intro j _ L0 h0 La' hL' φ
  exact k1gen_of_orth h5 hB hC (hO j L0 h0 La' hL' φ)

theorem adm2b_of_prv (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : Formalism.L2.G.Pend.FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT)) (g2 g3 ε s2 : MaximalUnramifiedExtension p)
    (hC : CurveAt p (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2) (hO : OrthAll X E hfin pos F g2 g3 s2 ε) :
    adm2b D X (Formalism.L2.G.Pend.pendT X E hfin hst hLT pos F) :=
  (Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.adm_two_pendant_iff_representative D X E hfin hst hLT pos F).2
    (representativeCondition_of_curve_orthAll h5 X E hfin _ pos F hB g2 g3 ε s2 hC hO)

theorem curveAt_of_beCob (H : Formalism.L2.KerInert.BeCob.BeCobTie) (D : Formalism.BasicNotions.D7)
    (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) {l : ℕ} [Fact l.Prime] {g : Formalism.MainNotions.GL3Theta.G1 l}
    (hLT : Formalism.L2.G.Pend.LTIso g) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (h5 : 5 ≤ l) (hI : Formalism.MainNotions.GL3Theta.InertK D l)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) :
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension l, CurveAt l (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 := by
  obtain ⟨-, ⟨F, hF⟩, g2, g3, ε, s2, h1, h2, h3, h4, h6, h7, h8⟩ := H D cc δ l g hLT hA h5 hI hM
  exact ⟨g2, g3, ε, s2, h1, h2, h3, h4, h6, h7, F, hF, h8 F hF⟩

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem orthAll_of {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (T : Tor D) (e : FamE D) (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p)
    (hI : ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → Formalism.L2.KerInert.IntFirst D T e p lam N N' L L')
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hComb : CombAt X hfin D large₂ Lg' F T e lam) (hFr : FrameHyp X E hfin D pos large₂ Lg' F S lam c)
    (hD : DictInt D lam T.abelian₂ c g2 g3 s2 ε) :
    OrthAll X E hfin pos (fun j La La' => linSub (S j La La') (F j La La')) g2 g3 s2 ε := by
  intro j L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFr j L0 h0 La' hL' φ
  obtain ⟨C, wq, hM, hW, hDi⟩ := hD
  obtain ⟨hAdm, hCb⟩ := hComb j L0 h0 La' hL'
  exact ⟨r, thOrth D lam c b (F j L0 La'), σ, f, f', hσ, hP, hEq,
    hDi _ _ r b _ (hI _ _ _ _ hAdm (F j L0 La') hCb C wq r b hM hW hLB hON)⟩

theorem orthAll_of_intInert (hInt : Formalism.L2.KerInert.IntInert) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (h5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p)
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hComb : CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) lam) (hFr : FrameHyp X E hfin D pos large₂ Lg' F S lam c)
    (hD : DictInt D lam B.tor.abelian₂ c g2 g3 s2 ε) :
    OrthAll X E hfin pos (fun j La La' => linSub (S j La La') (F j La La')) g2 g3 s2 ε :=
  orthAll_of X E hfin D pos large₂ Lg' F B.tor (B.eNat χ) lam c g2 g3 s2 ε
    (fun N N' L L' hA => hInt D cc δ B hcc hδ χ hχ p h5 hin lam N N' L L' hA) S hComb hFr hD

theorem curveDict_data (hCD : CurveDict) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime]
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (h5 : 5 ≤ p)
    (hIn : Formalism.MainNotions.GL3Theta.InertK D p) (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) :
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension p, CurveAt p (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : D7, DictInt D' g.lam g.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
  obtain ⟨g2, g3, ε, s2, h⟩ := hCD D cc δ p g hLT hA h5 hIn hM
  exact ⟨g2, g3, ε, s2, by tauto⟩

theorem adm2b_of_curve_dictionary (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (hst : Formalism.L2.G.Pend.FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFr : FrameHyp X E hfin D pos large₂ Lg' F S g.lam
      (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹)) :
    adm2b D X (Formalism.L2.G.Pend.pendT X E hfin hst hLT pos (fun j La La' => linSub (S j La La') (F j La La'))) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  exact adm2b_of_prv D h5 X E hfin hst hLT pos _ hB g2 g3 ε s2 hC
    (orthAll_of_intInert hInt X E hfin D pos large₂ Lg' F cc δ B hcc hδ χ hχ h5 hin g.lam _ g2 g3 s2 ε S hComb hFr hD')

theorem thOrth_sclY {p : ℕ} [Fact p.Prime] {N N' r : ℕ} (D : D7) (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    thOrth D lam 1 b (sclY c G) = thOrth D lam c b G := by
  have ha : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      ∑ i, MvPowerSeries.C ((1 : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold thOrth sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, one_mul]

theorem adm2b_of_curve_dictionary_one (hCD : CurveDict) (hInt : Formalism.L2.KerInert.IntInert) (D : D7) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (hst : Formalism.L2.G.Pend.FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (hIn : Formalism.MainNotions.GL3Theta.InertK D p)
    (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) (B : Base D cc δ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : IdE D → ℂ) (hχ : IsChi D χ) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1) (hLam : g.abelian₂ = B.tor.abelian₂)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F Fr : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (hFr : ∀ j La La', Fr j La La' =
      sclY (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) (F j La La'))
    (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (hB : BeProp p (Formalism.L2.G.Pend.beLT hLT))
    (hComb : CombAt X hfin D large₂ Lg' F B.tor (B.eNat χ) g.lam)
    (hFH : FrameHyp X E hfin D pos large₂ Lg' Fr S g.lam 1) :
    adm2b D X (Formalism.L2.G.Pend.pendT X E hfin hst hLT pos (fun j La La' => linSub (S j La La') (Fr j La La'))) := by
  obtain ⟨g2, g3, ε, s2, hC, hD⟩ := curveDict_data hCD D cc δ hLT hA h5 hIn hM
  have hD' : DictInt D g.lam B.tor.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
    rw [← hLam]
    exact hD D
  obtain ⟨C, wq, hMod, hW, hDi⟩ := hD'
  refine adm2b_of_prv D h5 X E hfin hst hLT pos _ hB g2 g3 ε s2 hC ?_
  intro j L0 h0 La' hL' φ
  obtain ⟨r, b, hLB, hON, σ, f, f', hσ, hP, hEq⟩ := hFH j L0 h0 La' hL' φ
  obtain ⟨hAdm, hCb⟩ := hComb j L0 h0 La' hL'
  refine ⟨r, thOrth D g.lam (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) b (F j L0 La'), σ, f, f', hσ,
    hP, ?_, hDi _ _ r b _ (hInt D cc δ B hcc hδ χ hχ p h5 hin g.lam _ _ _ _ hAdm (F j L0 La') hCb C wq r b hMod hW hLB hON)⟩
  rw [hEq, hFr, thOrth_sclY]
end Glob

end Formalism.L2.KerInert.Rep
end
end


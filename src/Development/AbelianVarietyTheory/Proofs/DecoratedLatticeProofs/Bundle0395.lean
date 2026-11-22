import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem sphFun_of_isParamFun : ∀ (D : D7) (V : HSp D) (Λ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat V) (Sf : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) (f : GA D V → ℂ)
    (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) f B →
    GlobalTheory.Core.Rk.IP.SphFun V Λ Sf f := by
  intro D V Λ Sf f B hf v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem upNe_of_heckeForm : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  intro D hHF _ _ hZ hgap c hc k hk s s' hs hs' p hp u B hB hL
  obtain ⟨mX, hmX⟩ : ∃ mX : Measure (WO s.V s'.V) × Set (WO s.V s'.V), IsCovolOne (ratL s'.V s.V) mX.1 mX.2 := by
    obtain ⟨ξ, f₀, hv⟩ := hp.vec
    exact hv.1.2.norm.1
  obtain ⟨φ, v, hvK, hZ'⟩ := hZ hgap c hc k hk s s' hs hs' p hp mX.1 mX.2 hmX
  refine ⟨φ, v, hvK, ?_⟩
  obtain ⟨hu0, hpar⟩ := hB
  obtain ⟨hI, hInt⟩ := hZ' u hu0
  have hF : PiLocalization₂.val u v ≠ 0 := by
    intro h0
    apply hI
    have : ∀ g, p.zint mX.1 mX.2 φ (PiLocalization₂.val u v) g = 0 := by
      intro g; simp [Step.zint, h0, PiLocalization₂.pet, Lift.pet, rTr]
    simp [this]
  have hparF := hpar v hF
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms D c hc k hk.le s hs
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms D c hc (k + 1) hk s' hs'
  have hu1 : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 u v hvK
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split D c (k + 1) s' hk hs'
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.thetaChainStep_fockVector_sphericalOffS D hgap c hc k hk s s' hs hs' p hp
  obtain ⟨-, -, hoff⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D s.V s.Λ a hs.selfDual hmaj
  have hmeas : MeasurableSet (intOff c s) := (hoff c.S).1.measurableSet
  have hr1 : 1 ≤ s.V.rank := by
    rw [hs.rank]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht1 : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      mX.1 mX.2 :=
    { setting := ⟨hr1, ht1, hrk, hc.inf, hs.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hs.selfDual, hs'.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2, (hfock φ).2⟩
  have hsph := sphFun_of_isParamFun D s.V s.Λ c.S _ B hparF
  set F := PiLocalization₂.val u v with hFdef
  have hAut : Formalism.L2.Theta.IsAutFunSm c.θ s.V (fun g => conj (F g)) := hu1.1.1
  have hFl : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hAut.left γ hγ g)
  have hFc : Continuous F := by simpa using hAut.cont.star
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := (hfock φ).1.1
  have hθl : ∀ h, ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro h γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hθc : ∀ h, Continuous fun g => thetaKO p.ω g h (p.pt φ) := fun h =>
    (hp.weil.om_cont _ hΦ 0).comp (continuous_id.prodMk continuous_const)
  have hrc : ∀ g, GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = conj (s.pet (rTr s.V g F) F) := by
    intro g
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun x => conj (F (x * g)) * conj (conj (F x)))
      (fun γ hγ x => by simp only [mul_assoc, hFl γ hγ]) (by fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.rcoef, PiLocalization₂.pet, Lift.pet, rTr]
    rw [← integral_conj]
    simp only [map_mul]
    exact this
  have hup : ∀ h, GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) h = conj (p.up φ F h) := by
    intro h
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g))
      (fun γ hγ x => by simp only [hθl h γ hγ, hFl γ hγ]) (by have := hθc h; fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
    rw [← integral_conj]
    simp only [map_mul, Complex.conj_conj]
    exact this
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hwz : ∀ g, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = p.zint mX.1 mX.2 φ F g := by
    intro g; simp only [Step.zint, hrc]; rfl
  have hint : ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν mX.1 mX.2 s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F x)) (fun x => conj (F x)) s₁) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    obtain ⟨s₁, hs₁, hi⟩ := hInt a hmaj hmaj_eq
    refine ⟨s₁, hs₁, hi.congr_fun (fun g hg => ?_) hmeas⟩
    simp only [GlobalTheory.Core.Rk.IP.integrand, GlobalTheory.Doubling.npow, (hoff c.S).2 g hg, hsZ, hrc]
    simp only [Step.zint, coefW, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hgtS]
    ring
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    mX.1 mX.2 hPair (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hs.haar hs'.haar
    _ hu1 _ hu1 B hparF hsph hint
  obtain ⟨l, hl0, hlv⟩ := hL
  have key := hval l hlv
  intro hup0
  have hz : GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = 0 := by
    funext h; rw [hup, hup0]; simp
  rw [hz] at key
  have hlhs : GlobalTheory.Cusp.petersson s'.V s'.ν (0 : GA D s'.V → ℂ) 0 = 0 := by
    simp [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]
  rw [hlhs] at key
  have hvol : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν := by
    have := hs'.haar; exact GlobalTheory.RallisIP.Model.vol_pos s'.ν
  have hd : GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (c.S : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) s.V.rank s'.V.rank
      ((D.R.t : ℂ) / 2) ≠ 0 := by
    refine ((GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D _ _ _).2 _ ?_).1
    simp only [Complex.div_ofNat_re, Complex.natCast_re]; positivity
  have hI' : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g ∂s.ν ≠ 0 := by
    simp only [hwz]; exact hI
  have hvolC : ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
  exact hI' (by
    have := key.symm
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hvolC
      · exact absurd h (div_ne_zero hl0 hd)
    · exact h)

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

variable {v : Pl D}

theorem intAt_mul {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem intAt_zero : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [(finPart D).map_neg]; exact neg_mem ha.2⟩

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [zero_mul]

theorem evalV_single_self (v : Pl D) : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1

theorem evalV_single_ne {v w : Pl D} (hw : w ≠ v) : evalV D.host.F w (singleV D.host.F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw

theorem single_int (v : Pl D) : singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self]; exact one_mem _
  · rw [evalV_single_ne hw]; exact zero_mem _

theorem mul_single {α : Af D.host.F} (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * singleV D.host.F v 1 = α := by
  apply RestrictedProduct.ext
  intro w
  change evalV D.host.F w (α * singleV D.host.F v 1) = evalV D.host.F w α
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self, mul_one]
  · rw [hα w hw, zero_mul]

theorem gen_mem {𝔞 : FI D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ 𝔞) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, rfl⟩

theorem tmul_mem_idAt {α : Af D.host.F} (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hαv _ w.2, TensorProduct.zero_tmul]

theorem tmul_one_mem_intAt {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨tmul_mem_idAt hαv 1, ?_⟩
  change α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D
  exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩

theorem tmul_mul_tmul' (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
      (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]

theorem incA_mul_tmul (x : D.host.E) (α : AF D.host.F) (b : D.host.E) :
    incA D x * (α ⊗ₜ[D.host.F] b : AE D) = α ⊗ₜ[D.host.F] (x * b) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * (α ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_mem_idV {𝔞 𝔟 : FI D} {a b : AE D} (ha : a ∈ idV 𝔞 v) (hb : b ∈ idV 𝔟 v) : a * b ∈ idV (𝔞 * 𝔟) v := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨α, hα, hαv, a, ha, rfl⟩ := ha'
    induction hb using AddSubgroup.closure_induction with
    | mem b' hb' =>
      obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hb'
      rw [tmul_mul_tmul']
      refine gen_mem (fun w => ?_) (fun w hw => ?_) (FractionalIdeal.mul_mem_mul ha hb)
      · rw [map_mul]; exact mul_mem (hα w) (hβ w)
      · rw [map_mul, hαv w hw, zero_mul]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg x _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem incA_mul_mem {𝔞 𝔟 : FI D} {x : D.host.E} (hx0 : x ≠ 0)
    (hx : ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (𝔞 * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem t' ht' =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := ht'
    have e : incA D x * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
        ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] x : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
      rw [incA_mul_tmul, tmul_mul_tmul', mul_single hβv]
    rw [e]
    refine mul_mem_idV ((hx _).2 ⟨?_, tmul_mem_idAt hβv x⟩)
      (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
    rw [incA_mul_tmul, inv_mul_cancel₀ hx0]
    exact tmul_one_mem_intAt hβ hβv
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem idV_mul_gen : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D) (x y : D.host.E), x ≠ 0 → y ≠ 0 → (∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → (∀ s, s ∈ idV 𝔟 v ↔ incA D y⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → ∀ s, s ∈ idV (𝔞 * 𝔟) v ↔ incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 𝔟 x y hx0 hy0 hx hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  intro s
  constructor
  · intro hs
    refine AddSubgroup.closure_induction (p := fun s _ => incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v))
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨α, hα, hαv, c, hc, rfl⟩
      refine FractionalIdeal.mul_induction_on (C := fun c => incA D (x * y)⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] c) ∈
        intAt D (· = v) ∧ (pairA D.host.F 0 α) ⊗ₜ[D.host.F] c ∈ idAt D (· = v)) hc ?_ ?_
      · intro a ha b hb
        have hA := (hx _).1 (gen_mem hα hαv ha)
        have hB := (hy _).1 (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
        have e : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * b) =
            ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
          rw [tmul_mul_tmul', mul_single hαv]
        rw [e]
        refine ⟨?_, Ideal.mul_mem_right _ _ hA.2⟩
        have e2 : incA D (x * y)⁻¹ * (((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) *
            ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) =
            (incA D x⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a)) *
              (incA D y⁻¹ * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) := by
          rw [mul_inv, (incA D).map_mul]; ring
        rw [e2]
        exact intAt_mul hA.1 hB.1
      · intro c d hc hd
        rw [TensorProduct.tmul_add, mul_add]
        exact ⟨intAt_add hc.1 hd.1, add_mem hc.2 hd.2⟩
    · rw [mul_zero]; exact ⟨intAt_zero, zero_mem _⟩
    · intro a b _ _ ha hb
      rw [mul_add]; exact ⟨intAt_add ha.1 hb.1, add_mem ha.2 hb.2⟩
    · intro a _ ha
      rw [mul_neg]; exact ⟨intAt_neg ha.1, neg_mem ha.2⟩
  · rintro ⟨ho, hs⟩
    have hso : s = incA D x * (incA D y * (incA D (x * y)⁻¹ * s)) := by
      rw [← mul_assoc, ← mul_assoc, ← (incA D).map_mul, ← (incA D).map_mul, mul_inv_cancel₀ hxy0, (incA D).map_one,
        one_mul]
    have ht : incA D y * (incA D (x * y)⁻¹ * s) ∈ idV 𝔟 v := by
      refine (hy _).2 ⟨?_, Ideal.mul_mem_left _ _ ho.1⟩
      rw [← mul_assoc, ← (incA D).map_mul, inv_mul_cancel₀ hy0, (incA D).map_one, one_mul]
      exact ho
    rw [hso]
    exact incA_mul_mem hx0 hx ht

end GlobalTheory.SeeSaw.IdVMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVOne

variable {D : D7}

def finIncl (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finIncl_tmul (y : Af D.host.F) (x : D.host.E) :
    finIncl D (y ⊗ₜ[D.host.F] x) = pairA D.host.F 0 y ⊗ₜ[D.host.F] x := rfl

theorem mul_eq_mul_finIncl (v : Pl D) (b : AE D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * b =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * finIncl D (finPart D b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul x c =>
    have h : finPart D (x ⊗ₜ[D.host.F] c) = sndA D.host.F x ⊗ₜ[D.host.F] c := rfl
    rw [h, finIncl_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * x.1 = 0 * 0
      rw [zero_mul, zero_mul]
    · rfl
  | add x y hx hy => rw [mul_add, hx, hy, RingHom.map_add, LinearMap.map_add, mul_add]

theorem mul_finIncl_mem (v : Pl D) (t : Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ intAE D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * finIncl D t ∈ idV (1 : FI D) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP (· = v) * α, ?_, ?_, (x : D.host.E), ?_, ?_⟩
    · intro w
      rw [map_mul]
      refine mul_mem ?_ (hα w)
      rw [GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro w hw
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hw, zero_mul]
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
    · rw [finIncl_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add, mul_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, mul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.IdVOne

open GlobalTheory.SeeSaw.IdVOne in

theorem GlobalTheory.SeeSaw.idV_one_eq_intAt :
    ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  intro D v a
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hv, x, hx, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      refine ⟨?_, ?_⟩
      · rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
        refine ⟨?_, fun w => ?_⟩
        · rw [RingHom.mem_ker]
          show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
          exact TensorProduct.zero_tmul _ _
        · rw [RingHom.mem_ker]
          show evalV D.host.F w.1 (sndA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
          have : evalV D.host.F w.1 α = 0 := hv w.1 w.2
          rw [show sndA D.host.F (pairA D.host.F 0 α) = α from rfl, this]
          exact TensorProduct.zero_tmul _ _
      · exact AddSubgroup.subset_closure ⟨α, hα, x', rfl⟩
    | zero => exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    | add x y _ _ h1 h2 => exact ⟨add_mem h1.1 h2.1, by rw [RingHom.map_add]; exact add_mem h1.2 h2.2⟩
    | neg x _ h => exact ⟨neg_mem h.1, by rw [RingHom.map_neg]; exact neg_mem h.2⟩
  · rintro ⟨ha, hf⟩
    rw [← GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) a ha, mul_eq_mul_finIncl]
    exact mul_finIncl_mem v _ hf

example : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) :=
  GlobalTheory.SeeSaw.idV_one_eq_intAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.WeilLines

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

variable {D : D7}

theorem charUnram_mul {χ χ' : (AE D)ˣ →* Circle} {v} (h : CharUnramAt D χ v) (h' : CharUnramAt D χ' v) :
    CharUnramAt D (χ * χ') v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, mul_one]

theorem charUnram_inv {χ : (AE D)ˣ →* Circle} {v} (h : CharUnramAt D χ v) : CharUnramAt D χ⁻¹ v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

end GlobalTheory.SeeSaw.WeilLines

namespace GlobalTheory.SeeSaw.WeilLines

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

end GlobalTheory.SeeSaw.WeilLines
end
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0108
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsTranslateRationalPointUnitDenominator
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.UnitTr

theorem lamC_mul_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy), ← map_mul]
  rfl

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem coc_nat_left (n : ℕ) (x y : HomE X.E a b) : coc A ((n : X.E) • x) y = n * coc A x y := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h 0 0 y).1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).1, ih]; push_cast; ring

theorem coc_nat_right (n : ℕ) (x y : HomE X.E a b) : coc A x ((n : X.E) • y) = n * coc A x y := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h x 0 0).2.1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).2.1, ih]; push_cast; ring

theorem coc_rat (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hX : X.Ok) (hL : A.LaHyp a b ∅)
    (hA : A.AA ≠ ⊥) (hN : IsSdLat N) (hN' : IsSdLat N') (x y : HomE X.E a b) : ∃ r : ℚ, coc A x y = (r : ℝ) := by
  obtain ⟨hδ, -, -, -, hFG, hLa⟩ := hL
  have hfull := (GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hA hN hN').2.1
  have hint := (GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  obtain ⟨n, hn, hx⟩ := hfull x
  obtain ⟨n', hn', hy⟩ := hfull y
  obtain ⟨k, hk⟩ := hint ((n : X.E) • x) ((n' : X.E) • y) fun Q =>
    ⟨1, one_ne_zero, by simpa using le_locP Q _ hx, by simpa using le_locP (conjPrime₂ Q) _ hy⟩
  rw [coc_nat_left, coc_nat_right] at hk
  refine ⟨(k : ℚ) / (n * n'), ?_⟩
  have h1 : (n : ℝ) ≠ 0 := by positivity
  have h2 : (n' : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← hk]
  field_simp

theorem Wx_const_mul (x : HomE X.E a b) (c : ℂ) (F : VCx X.Tau a b → ℂ) :
    Wx A x (fun z => c * F z) = fun z => c * Wx A x F z := by
  funext z
  simp only [Wx, opU]
  ring

theorem Wx_per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hL : A.LaHyp a b ∅)
    (hN : IsSdLat N) (hN' : IsSdLat N') (l : HomE X.E a b) (hl : l ∈ per A N N') :
    Wx A l (A.e a b N N') = A.e a b N N' := by
  funext z
  exact (hL.2.2.2.2.2 N N' hN hN').1 (emb A l) ⟨l, hl, rfl⟩ z

theorem moments_unit_translate : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  intro X A a b ϖ p N N' _ lam ι un hX hL hA hS hϖ hcop hN hN' hP t n hn ht
  have hp : p.Prime := Fact.out
  have hH := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  have hroot := (GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam
  have hϖE : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E) := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hϖ
    simpa [Fields.conjO, starRingEnd_apply] using this
  have hϖ0 : (ϖ : X.E) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hϖE
    exact hp.ne_zero (by exact_mod_cast hϖE.symm)
  have hbar : ((X.conjO ϖ : 𝓞 X.E) : X.E) = star (ϖ : X.E) := by
    simp [Fields.conjO, starRingEnd_apply]
  have hnϖ : IsCoprime (n : 𝓞 X.E) ϖ := by
    have h1 : IsCoprime (n : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hn
    rw [← hϖ] at h1
    exact h1.of_mul_right_left
  obtain ⟨α, β, hαβ⟩ := hnϖ.mul_left hcop.symm
  have hαβE : (α : X.E) * (n * star (ϖ : X.E)) + β * ϖ = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hαβ
    simpa [hbar] using this
  have hsm : ∀ (r : 𝓞 X.E) (x : HomE X.E a b), x ∈ per A N N' → (r : X.E) • x ∈ per A N N' := fun r x hx =>
    Submodule.smul_mem _ r hx
  set t' : HomE X.E a b := ((β : X.E) * ϖ) • t with ht'
  have ht'M : (n : X.E) • t' ∈ per A N N' := by
    have := hsm β _ ht
    rw [smul_smul] at this
    rw [ht', smul_smul]
    convert this using 2
    ring
  obtain ⟨N₀, hN₀, hJ, hC⟩ := hP N N' hN hN' t' ⟨n, hn, ht'M⟩
  obtain ⟨α', β', h'⟩ : IsCoprime (N₀ : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hN₀
  have h'E : (α' : X.E) * N₀ + β' * (ϖ * star (ϖ : X.E)) = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) h'
    rw [hϖE]
    simpa using this
  set m₁ : HomE X.E a b := ((α' * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hm₁
  set l : HomE X.E a b := ((β' * X.conjO ϖ * X.conjO ϖ * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hl
  have hm₁M : m₁ ∈ per A N N' := hsm _ _ ht
  have hlM : l ∈ per A N N' := hsm _ _ ht
  set y : HomE X.E a b := ((N₀ : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • m₁ with hy
  have hdec : y + (t' + l) = t := by
    rw [hy, hm₁, hl, ht']
    simp only [smul_smul, ← add_smul]
    conv_rhs => rw [← one_smul X.E t]
    congr 1
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hbar hαβE h'E hϖ0 ⊢
    rw [hbar]
    field_simp
    linear_combination (α * n * star (ϖ : X.E)) * h'E + hαβE
  obtain ⟨r₁, hr₁⟩ := coc_rat A N N' hX hL hA hN hN' t' l
  obtain ⟨r₂, hr₂⟩ := coc_rat A N N' hX hL hA hN hN' y (t' + l)
  set ζ : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ)) with hζ
  have hkey : Wx A t (A.e a b N N') = fun z => ζ * Wx A y (Wx A t' (A.e a b N N')) z := by
    have e1 := hH.1 t' l (A.e a b N N')
    rw [Wx_per A N N' hL hN hN' l hlM] at e1
    rw [e1, Wx_const_mul, hH.1 y (t' + l), hdec, hr₁, hr₂]
    funext z
    rw [hζ, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    have : -(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ) + -(2 * (Real.pi : ℂ)) * Complex.I * ((r₁ : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ)) * Complex.I * ((r₂ : ℝ) : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  have hjet : ∀ m, jetC A.cD (Wx A t (A.e a b N N')) m = ζ * jetC A.cD (Wx A y (Wx A t' (A.e a b N N'))) m := by
    intro m
    have := hH.2.2.2.2.2.2.2 Unit {()} (fun _ => ζ) (fun _ => Wx A y (Wx A t' (A.e a b N N')))
      (fun _ _ => hH.2.2.2.2.2.2.1 _ _ (hH.2.2.2.2.2.2.1 _ _ (hS N N' hN hN'))) m
    rw [hkey]
    simpa only [Finset.sum_singleton] using this
  have hζQ := hroot (-(r₁ + r₂))
  refine ⟨fun m => ?_, ?_⟩
  · rw [hjet]
    exact mul_mem hζQ.1 (hJ m₁ hm₁M m)
  · have hbrk : ∀ x, ‖TaylorLogMetric.lamC lam (brkE A y x)‖ = 1 := by
      intro x
      obtain ⟨s₁, hs₁⟩ := coc_rat A N N' hX hL hA hN hN' x y
      obtain ⟨s₂, hs₂⟩ := coc_rat A N N' hX hL hA hN hN' y x
      have := (hroot (s₁ - s₂)).2
      rw [hH.2.2.2.2.1, hH.2.2.1, hs₁, hs₂]
      rwa [Rat.cast_sub] at this
    have := clo_comb (Sup' := (per A N N' : Set (HomE X.E a b))) (tab' := ptTab ι un) (M' := Set.univ) hC ({()} : Finset Unit)
      (fun _ _ => TaylorLogMetric.lamC lam ζ) (fun _ m => (m₁, m)) (fun _ _ _ _ => hm₁M)
      (fun x => TaylorLogMetric.lamC lam ζ * TaylorLogMetric.lamC lam (brkE A y x))
      (fun x _ => by rw [norm_mul, hbrk, hζQ.2, one_mul]) (fun _ h h' => absurd h h')
      (fun x _ m _ => by simp only [Finset.sum_singleton]; rw [mul_assoc])
    refine clo_congr this subset_rfl subset_rfl fun m _ => ?_
    simp only [Finset.sum_singleton]
    rw [hjet, lamC_mul_of_mem lam hζQ.1 (hJ m₁ hm₁M m)]

end GlobalTheory.MomT.UnitTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove
  GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.ThetaMove.LatticeFacts

theorem exp_pi_int (b : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))
    = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))) := by
  have h : (Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)
      = -((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)) + (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1
  push_cast; ring

theorem al_sign (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T x = 1 ∨ TaylorLogMetric.al D T x = -1 := by
  unfold TaylorLogMetric.al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem latAll {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.LatAll := by
  have h0 : δ ≠ 0 := delta_ne_zero B
  refine ⟨fun N N' L L' hA => ⟨?_, fun x _ => al_sign D _ x, ?_⟩, fun N N' L₁ L₁' L₂ L₂' h₁ h₂ =>
    ⟨IO.La_index_ne_zero cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂, IO.La_index_ne_zero cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁⟩⟩
  · have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    apply le_antisymm
    · intro v hv
      exact self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA v (fun y hy => hv y hy)
    · intro v hv y hy
      obtain ⟨a, b, -, hab⟩ := hI v hv y hy
      refine ⟨b, ?_⟩
      show (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) v y).im = (b : ℝ)
      rw [hab]; simp
  · intro x hx y hy
    have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    have hs := IO.semiChar_of_HfInt _ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im = (b : ℝ) := by rw [hab]; simp
    rw [hs]
    congr 1
    show Complex.exp (-((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ)))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ))
    rw [him]; exact (exp_pi_int b).symm

theorem laHyp_and_eSmooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  intro D X s cc δ B χ cD a b hX hs hcc hδ hV ha hb
  have hL := latAll B hcc hδ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hV a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hV a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.ThetaMove.LatticeFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedAreaClassInvariant
section
noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in

theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dif_pos (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumInvCardStabEq
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedDoubleCoset

def stabConjEquiv {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Unfold.stab Γ K ((γ₀ : G) * g * k) ≃ Unfold.stab Γ K g where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, by
    have h := K.mul_mem (K.mul_mem k.2 δ.2) (K.inv_mem k.2)
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, by
    have h := K.mul_mem (K.mul_mem (K.inv_mem k.2) δ.2) k.2
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  left_inv δ := by ext; simp [mul_assoc]
  right_inv δ := by ext; simp [mul_assoc]

theorem card_stab_eq {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Nat.card (Unfold.stab Γ K ((γ₀ : G) * g * k)) = Nat.card (Unfold.stab Γ K g) :=
  Nat.card_congr (stabConjEquiv Γ K g γ₀ k)

theorem sum_inv_card_stab_eq : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n m : ℕ) (g : Fin n → G) (g' : Fin m → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) → (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g' i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g' i * k = (γ' : G) * g' j * k' → i = j) → ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ∑ j, ((Nat.card (Unfold.stab Γ K (g' j)) : ℝ))⁻¹ := by
  intro G _ Γ K n m g g' hcov hdisj hcov' hdisj'
  choose e γe ke he using fun i => hcov' (g i)
  choose f γf kf hf using fun j => hcov (g' j)
  have hfe : ∀ i, f (e i) = i := by
    intro i
    symm
    refine hdisj i (f (e i)) 1 (γe i * γf (e i)) 1 (kf (e i) * ke i) ?_
    have h1 := he i
    rw [hf (e i)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  have hef : ∀ j, e (f j) = j := by
    intro j
    symm
    refine hdisj' j (e (f j)) 1 (γf j * γe (f j)) 1 (ke (f j) * kf j) ?_
    have h1 := hf j
    rw [he (f j)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  let σ : Fin n ≃ Fin m := ⟨e, f, hfe, hef⟩
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  show ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ((Nat.card (Unfold.stab Γ K (g' (e i))) : ℝ))⁻¹
  rw [he i, card_stab_eq]

end GlobalTheory.WeightedDoubleCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_numAt :
    SzRow (fun C D L => HostArith D.host → Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  refine szRow_and_imp.2 _ _ (szRow_and_imp.1 _ _ (szRow_and_imp.1 _ _ explicitConstants_parameterConditions_large szRow_blockLengthParams)
    (szRow_and_imp.1 _ _ szRow_sizesAt szRow_band_lambda_primes)) ?_
  rintro C cD ch D L hC hV ⟨⟨h5, hT⟩, hS, hrho, hLa, hg, hp, hp', hTT, hCode⟩ hA
  obtain ⟨P, hPK, hPW⟩ := h5 hA
  obtain ⟨T, hTK, hTe⟩ := hT P hPW
  have hCt : C.Ct = 401 := hC.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn, hm, hk, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, -, hLw, hcc, -⟩ := hV.host
  refine ⟨⟨{ params := P
             params_K := hPK
             CnW_eq := hPW
             parT := T
             parT_K := hTK
             eP_eq := hTe
             sizes := hS
             rho_le := hrho
             CGam_eq := hV.CGam_eq
             Cc_eq := hV.Cc_eq
             Ct_eq := hV.Ct_eq
             secondConstant_eq := hV.secondConstant_eq
             LaG_ge := hLa
             bT_le := hV.bT_le
             ccK_top := hcc
             g_le := hg
             pde_lt := ⟨hp, hp'⟩
             logFiveDepth_eq := hV.logFiveDepth_eq
             Lw_eq := ?_
             cloud1 := fun τ τ' => ?_
             win := ⟨hn, hm, hk⟩ }⟩, hTT, hCode⟩
  · rw [hLw, hCt]; unfold Lwv; norm_num
  · funext i
    rw [hV.hc.1 τ i, hV.hc.1 τ' i]

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TopsChoiceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tops_choice : TopsChoice := by
  first | exact @GlobalTheory.EX.exists_tops | exact GlobalTheory.EX.exists_tops | (intros; apply GlobalTheory.EX.exists_tops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryGroupNegFormCompatible
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem uj_neg_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) : Formalism.UG.UJ s (-J) = Formalism.UG.UJ s J := by
  ext g
  show Formalism.UG.cT s (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem hR_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HR R σ (-J) = HR R σ J := by
  unfold HR JR
  rw [Matrix.map_neg _ (map_neg _), uj_neg_eq]

theorem hFin_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HFin R σ (-J) = HFin R σ J := by
  unfold HFin
  rw [uj_neg_eq]

theorem unitary_neg_same : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E), J' = -J → ∃ φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ J', (∀ h, HA.mat (AF F) σ J' (φ h) = HA.mat (AF F) σ J h) ∧ (∀ h, h ∈ HFinIn (AF F) σ J ↔ φ h ∈ HFinIn (AF F) σ J') ∧ ∀ (L : Set (Fin M → E)) h, h ∈ StabFin.SFin σ J L ↔ φ h ∈ StabFin.SFin σ J' L := by
  intro F E _ _ _ _ _ σ M J J' hJ
  subst hJ
  have e := (hR_neg_eq (AF F) σ J).symm
  let ψ : HA (AF F) σ J ≃* HA (AF F) σ (-J) := MulEquiv.subgroupCongr e
  have hψ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (ψ h) = HA.mat (AF F) σ J h := fun h => rfl
  let φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ (-J) :=
    { ψ with
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }
  have hφ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (φ h) = HA.mat (AF F) σ J h := fun h => rfl
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro h
    show (HA.mat (AF F) σ J h) ∈ HFin (AF F) σ J ↔ (HA.mat (AF F) σ (-J) (φ h)) ∈ HFin (AF F) σ (-J)
    rw [hFin_neg_eq]
    exact Iff.rfl
  · intro L h
    exact Iff.rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcoveStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
end


import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0210
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0217
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0247
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyIdentityOfLengthFunction
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.Vanish

variable {n : ℕ} {W : Type} [NormedAddCommGroup W]

theorem dens_nonneg [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : 0 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  positivity

theorem sq_le_dens [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) :
    ‖u s y‖ ^ 2 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith [sq_nonneg ‖dt u s y‖]

theorem dens_continuousOn [NormedSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) :
    ContinuousOn (dens u s) (GLs n) := by
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu
  have a : ContinuousOn (dt u s) (GLs n) := ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (dt u) h1).2.2.1 s).continuousOn
  have b : ContinuousOn (u s) (GLs n) := (h3 s).continuousOn
  have c : ∀ p : Ix n, ContinuousOn (Rt (hm p) u s) (GLs n) := fun p =>
    ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (Rt (hm p) u) (h2 (hm p))).2.2.1 s).continuousOn
  unfold dens
  refine ((a.norm.pow 2).add (continuousOn_const.mul ?_)).add (b.norm.pow 2)
  exact continuousOn_finsetSum _ (fun p _ => (c p).norm.pow 2)

theorem weighted_zero [NormedSpace ℝ W] (ℓ : Mat n → ℝ) (hℓ : ContinuousOn ℓ (GLs n))
    (χ : ℝ → ℝ) (hχ : ∀ x, 1 ≤ x → χ x = 0) (u : ℝ → Mat n → W) (r : ℝ)
    (h0 : ∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) (h1 : ∀ y ∈ GLs n, dt u 0 y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : χ (ℓ y - r) * dens u 0 y = 0 := by
  by_cases hc : 1 ≤ ℓ y - r
  · rw [hχ _ hc, zero_mul]
  · have hlt : ℓ y < r + 1 := by linarith
    have hnh : GLs n ∈ nhds y := isOpen_GLs.mem_nhds hy
    have hca : ContinuousAt ℓ y := hℓ.continuousAt hnh
    have hev : u 0 =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hca.eventually_lt continuousAt_const hlt, hnh] with z hz hzG
      exact h0 z hzG hz
    have hR : ∀ p : Ix n, Rt (hm p) u 0 y = 0 := fun p => by
      change fderiv ℝ (u 0) y (y * hm p) = 0
      rw [hev.fderiv_eq]
      simp
    have hd : dens u 0 y = 0 := by
      unfold dens
      simp [hR, h1 y hy, h0 y hy hlt]
    rw [hd, mul_zero]

theorem energy_vanish : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) →
    ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) →
    (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) →
      ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) →
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) →
    (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W),
    (∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) →
    ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), (∀ x, x ≤ 0 → χ x = 1) →
    (∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) → (∀ y ∈ GLs n, dt u 0 y = 0) →
    ∀ t : ℝ, 0 ≤ t → ∀ y ∈ GLs n, ℓ y + C * t ≤ r → u t y = 0 := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r hχ2 h0 h1
    t ht y hy hyt
  obtain ⟨K, hK⟩ := GlobalTheory.T.energy_estimate_of_length_function μ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r
  choose e' he' hle using hK
  have hℓc : ContinuousOn ℓ (GLs n) := hℓ.continuousOn
  have hnn : ∀ (s : ℝ) (z : G n), 0 ≤ χ (ℓ z.val + C * s - r) * dens u s z.val := fun s z =>
    mul_nonneg (hχ0 _) (dens_nonneg u s _)
  have hzero : (∫ z : G n, χ (ℓ z.val + C * t - r) * dens u t z.val ∂μ) = 0 := by
    refine GlobalTheory.CompanionTheory.WaveSpd.GronwallZero.eq_zero_of_deriv_le_mul
      (fun s => ∫ z : G n, χ (ℓ z.val + C * s - r) * dens u s z.val ∂μ) e' K t ht he' hle
      (fun s => integral_nonneg (hnn s)) ?_
    have : ∀ z : G n, χ (ℓ z.val + C * 0 - r) * dens u 0 z.val = 0 := fun z => by
      have := weighted_zero ℓ hℓc χ hχ1 u r h0 h1 z.val (val_mem_GLs z)
      simpa using this
    simp only [this, integral_zero]
  have hval : Continuous (fun z : G n => z.val) := Units.continuous_val
  have hcont : Continuous (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    have c1 : Continuous (fun z : G n => ℓ z.val) := hℓc.comp_continuous hval val_mem_GLs
    have c2 : Continuous (fun z : G n => dens u t z.val) :=
      (dens_continuousOn u hu t).comp_continuous hval val_mem_GLs
    exact (hχs.continuous.comp ((c1.add continuous_const).sub continuous_const)).mul c2
  have hsupp : HasCompactSupport (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    refine HasCompactSupport.intro (hcpt (1 + r - C * t)) ?_
    intro z hz
    have hz' : 1 + r - C * t < ℓ z.val := not_le.1 hz
    have : χ (ℓ z.val + C * t - r) = 0 := hχ1 _ (by linarith)
    simp only [this, zero_mul]
  let yu : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero y hy
  have hyu : yu.val = y := rfl
  have hat : χ (ℓ y + C * t - r) * dens u t y = 0 := by
    by_contra hne
    have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := yu) hsupp
      (fun z => hnn t z) (by simpa [hyu] using hne)
    exact this.ne' hzero
  rw [hχ2 _ (by linarith), one_mul] at hat
  have hsq := sq_le_dens u t y
  rw [hat] at hsq
  have : ‖u t y‖ ^ 2 = 0 := le_antisymm hsq (by positivity)
  simpa using this

end GlobalTheory.CompanionTheory.WaveSpd.Vanish
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtNil

theorem isNilpotent_of_fg_of_le {B : Type} [CommRing B] {J J' : Ideal B}
    (hJ : ∀ x ∈ J, IsNilpotent x) (hfg : J'.FG) (hle : J' ≤ J) : IsNilpotent J' :=
  (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 fun x hx => mem_nilradical.2 (hJ x (hle hx))

theorem exists_lift {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallySmooth P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (g : E →ₐ[P] B ⧸ J) :
    ∃ h : E →ₐ[P] B, (Ideal.Quotient.mkₐ P J).comp h = g := by
  obtain ⟨n, π, hπ, hK⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  choose b hb using fun i => Ideal.Quotient.mk_surjective (g (π (MvPolynomial.X i)))
  let φ : MvPolynomial (Fin n) P →ₐ[P] B := MvPolynomial.aeval b
  have hφ : (Ideal.Quotient.mkₐ P J).comp φ = g.comp π :=
    MvPolynomial.algHom_ext fun i => by simp [φ, hb]
  have hφ' : ∀ p, Ideal.Quotient.mk J (φ p) = g (π p) := fun p => DFunLike.congr_fun hφ p
  let J' : Ideal B := (RingHom.ker π.toRingHom).map φ.toRingHom
  have hle : J' ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    have hp0 : π p = 0 := hp
    refine Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    change Ideal.Quotient.mk J (φ p) = 0
    rw [hφ', hp0, map_zero]
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ (hK.map _) hle
  have hkill : ∀ a ∈ RingHom.ker π, ((Ideal.Quotient.mkₐ P J').comp φ) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ.toRingHom ha)
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let g' : E →ₐ[P] B ⧸ J' :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill).comp
      e.symm.toAlgHom
  have hg' : ∀ p, g' (π p) = Ideal.Quotient.mk J' (φ p) := fun p => by
    have : e.symm (π p) = Ideal.Quotient.mk (RingHom.ker π) p := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ p).symm
    change Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill
      (e.symm (π p)) = _
    rw [this]
    rfl
  refine ⟨Algebra.FormallySmooth.lift J' hnil g', AlgHom.ext fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hπ x
  have h1 := Algebra.FormallySmooth.mk_lift J' hnil g' (π p)
  rw [hg', Ideal.Quotient.eq] at h1
  change Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J' hnil g' (π p)) = g (π p)
  rw [← hφ', Ideal.Quotient.eq]
  exact hle h1

theorem lift_unique {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallyUnramified P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (h₁ h₂ : E →ₐ[P] B)
    (H : ∀ x, Ideal.Quotient.mk J (h₁ x) = Ideal.Quotient.mk J (h₂ x)) : h₁ = h₂ := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  let d : Fin n → B := fun i => h₁ (π (MvPolynomial.X i)) - h₂ (π (MvPolynomial.X i))
  let J' : Ideal B := Ideal.span (Set.range d)
  have hfg : J'.FG := Submodule.fg_span (Set.finite_range d)
  have hle : J' ≤ J := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq.1 (H _)
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ hfg hle
  have hc : (Ideal.Quotient.mkₐ P J').comp (h₁.comp π) =
      (Ideal.Quotient.mkₐ P J').comp (h₂.comp π) :=
    MvPolynomial.algHom_ext fun i =>
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
  refine Algebra.FormallyUnramified.ext J' hnil fun x => ?_
  obtain ⟨p, rfl⟩ := hπ x
  exact DFunLike.congr_fun hc p

end GlobalTheory.CompanionTheory.EtNil

theorem GlobalTheory.CompanionTheory.EtNil.etLift_of_nil : ∀ {B : Type} [CommRing B] (J : Ideal B),
    (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g hg
  letI := ψ.toAlgebra
  letI := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let gA : E →ₐ[P] B ⧸ J :=
    { g with commutes' := fun p => DFunLike.congr_fun hg p }
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.EtNil.exists_lift J hJ gA
  have hh' : ∀ x, Ideal.Quotient.mk J (h x) = g x := fun x => DFunLike.congr_fun hh x
  refine ⟨h.toRingHom, ⟨RingHom.ext fun p => h.commutes p, RingHom.ext hh'⟩, ?_⟩
  rintro h' ⟨h1, h2⟩
  let hA : E →ₐ[P] B := { h' with commutes' := fun p => DFunLike.congr_fun h1 p }
  have : hA = h := GlobalTheory.CompanionTheory.EtNil.lift_unique J hJ hA h fun x => by
    change Ideal.Quotient.mk J (h' x) = _
    rw [hh']
    exact DFunLike.congr_fun h2 x
  exact RingHom.ext fun x => DFunLike.congr_fun this x
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueLiftOfNilpotent
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem existsUnique_lift_of_nilpotent {P E C D : Type} [CommRing P] [CommRing E] [CommRing C] [CommRing D]
    (ψ : P →+* E) (hψ : ψ.Etale) (u : C →+* D) (hu : Function.Surjective u)
    (hn : IsNilpotent (RingHom.ker u)) (f : P →+* C) (g : E →+* D) (h : g.comp ψ = u.comp f) :
    ∃! l : E →+* C, l.comp ψ = f ∧ u.comp l = g := by
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P C := f.toAlgebra
  letI : Algebra P D := (u.comp f).toAlgebra
  haveI : Algebra.Etale P E := hψ
  let uA : C →ₐ[P] D := { u with commutes' := fun _ => rfl }
  let gA : E →ₐ[P] D := { g with commutes' := fun r => congrArg (fun t : P →+* D => t r) h }
  have hn₁ : IsNilpotent (RingHom.ker (uA : C →+* D)) := hn
  have hn₂ : IsNilpotent (RingHom.ker uA) := hn
  let lA : E →ₐ[P] C := Algebra.FormallySmooth.liftOfSurjective gA uA hu hn₁
  have hl : ∀ x, u (lA x) = g x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply gA uA hu hn₂ x
  refine ⟨(lA : E →+* C), ⟨RingHom.ext fun r => lA.commutes r, RingHom.ext hl⟩, ?_⟩
  rintro l' ⟨h1, h2⟩
  let lA' : E →ₐ[P] C := { l' with commutes' := fun r => congrArg (fun t : P →+* C => t r) h1 }
  have : lA' = lA := Algebra.FormallyUnramified.ext' u hn lA' lA fun x => by
    rw [hl]; exact congrArg (fun t : E →+* D => t x) h2
  exact congrArg (fun t : E →ₐ[P] C => (t : E →+* C)) this

variable {B : Type} [CommRing B] (J : Ideal B)

abbrev toBase (n : ℕ) : B ⧸ J ^ (n + 1) →+* B ⧸ J :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))

theorem toBase_mk (n : ℕ) (x : B) : toBase J n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk J x := rfl

theorem isNilpotent_ker_toBase (n : ℕ) : IsNilpotent (RingHom.ker (toBase J n)) := by
  refine ⟨n + 1, ?_⟩
  have hk : RingHom.ker (toBase J n) = J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    rw [Ideal.Quotient.factor_ker]
  rw [hk, ← Ideal.map_pow]
  simp

theorem existsUnique_level {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E) (hψ : ψ.Etale)
    (f : P →+* B) (g : E →+* B ⧸ J) (h : g.comp ψ = (Ideal.Quotient.mk J).comp f) (n : ℕ) :
    ∃! l : E →+* B ⧸ J ^ (n + 1), l.comp ψ = (Ideal.Quotient.mk _).comp f ∧ (toBase J n).comp l = g :=
  existsUnique_lift_of_nilpotent ψ hψ (toBase J n) (Ideal.Quotient.factor_surjective _)
    (isNilpotent_ker_toBase J n) _ g h

theorem iInf_pow_eq_bot (hJ : IsAdicComplete J B) : ⨅ i : ℕ, J ^ i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  refine (Ideal.mem_bot).2 (IsHausdorff.haus hJ.toIsHausdorff x fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact (Ideal.mem_iInf.1 hx) n

end GlobalTheory.CompanionTheory.EtaleLift

open GlobalTheory.CompanionTheory.EtaleLift in

theorem GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete :
    ∀ {B : Type} [CommRing B] (J : Ideal B), IsAdicComplete J B → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g h
  haveI := hJ
  choose l hl hu using existsUnique_level J ψ hψ f g h
  have hcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J (Nat.succ_le_succ hle)).comp (l n) = l m := by
    intro m n hle
    refine (hu m _ ⟨?_, ?_⟩).symm ▸ rfl
    · rw [RingHom.comp_assoc, (hl n).1]
      rfl
    · rw [← (hl n).2, ← RingHom.comp_assoc]
      congr 1
      exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let F : (n : ℕ) → E →+* B ⧸ J ^ n := fun n => (Ideal.Quotient.factorPow J (Nat.le_succ n)).comp (l n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (F n) = F m := by
    intro m n hle
    simp only [F]
    rw [← hcomp hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let H : E →+* B := IsAdicComplete.liftRingHom J F hF
  have hH : ∀ n x, Ideal.Quotient.mk (J ^ n) (H x) = F n x := fun n x =>
    IsAdicComplete.mk_liftRingHom J F hF n x
  have h1 : H.comp ψ = f := by
    ext p
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hJ.toIsHausdorff _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      RingHom.comp_apply, hH, sub_eq_zero]
    have := congrArg (fun t : P →+* B ⧸ J ^ (n + 1) => Ideal.Quotient.factorPow J (Nat.le_succ n) (t p)) (hl n).1
    exact this
  have h2 : (Ideal.Quotient.mk J).comp H = g := by
    ext x
    have e1 : (toBase J 0).comp (Ideal.Quotient.factorPow J (Nat.le_succ 1)) = toBase J 1 :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    have e2 : Ideal.Quotient.mk J (H x) = toBase J 0 (F 1 x) := by
      rw [← hH 1 x]
      rfl
    rw [RingHom.comp_apply, e2, ← (hl 1).2, ← e1]
    rfl
  refine ⟨H, ⟨h1, h2⟩, ?_⟩
  rintro H' ⟨h1', h2'⟩
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P B := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let A : E →ₐ[P] B := { H with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1 }
  let A' : E →ₐ[P] B := { H' with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1' }
  have : A' = A := Algebra.FormallyUnramified.ext_of_iInf J (iInf_pow_eq_bot J hJ) fun x => by
    exact (congrArg (fun t : E →+* B ⧸ J => t x) h2').trans (congrArg (fun t : E →+* B ⧸ J => t x) h2).symm
  exact congrArg (fun t : E →ₐ[P] B => (t : E →+* B)) this
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedDividedPowers
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDMap

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_anti (δ : DividedPowers J) {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m := by
  refine Ideal.span_mono ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact ⟨l, h1, h.trans h2, rfl⟩

theorem fil_zero_top (δ : DividedPowers J) : fil δ 0 = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], ?_, ?_, ?_⟩) <;> simp

theorem dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n := by
  refine Ideal.subset_span ⟨[(n, x)], ?_, ?_, ?_⟩ <;> simp [hx]

theorem fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ⟨l, h1, h2, rfl⟩, b, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h1 p hp
    · exact h1' p hp
  · simpa using Nat.add_le_add h2 h2'
  · simp

theorem map_fil_le' {C : Type} [CommRing C] {J' : Ideal C} (δ : DividedPowers J) (δ' : DividedPowers J')
    (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) : (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_le_map {C : Type} [CommRing C] (δ : DividedPowers J) (f : B →+* C)
    (δ' : DividedPowers (J.map f)) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    fil δ' N ≤ (fil δ N).map f := by
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (fil_mul_le δ m n)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (dpow_mem_fil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (fil_anti δ h2) (hprod l h1)

theorem extended_dividedPowers : ∀ {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} (δ : DividedPowers J) (φ : B →+* B') (δ' : DividedPowers (J.map φ)), IsDPMorphism δ δ' φ → (∀ r, fil δ' r = (fil δ r).map φ) ∧ ∀ {B'' : Type} [CommRing B''] {J'' : Ideal B''} (δ'' : DividedPowers J'') (ψ : B' →+* B''), IsDPMorphism δ δ'' (ψ.comp φ) → IsDPMorphism δ' δ'' ψ := by
  intro B B' _ _ J δ φ δ' hφ
  refine ⟨fun r ↦ le_antisymm (fil_le_map δ φ δ' hφ r) (map_fil_le' δ δ' φ hφ r), ?_⟩
  intro B'' _ J'' δ'' ψ hψ
  refine IsDPMorphism.on_span δ' δ'' (S := φ '' (J : Set B)) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hψ.ideal_comp (Ideal.mem_map_of_mem (ψ.comp φ) ha)
  · rintro n _ ⟨a, ha, rfl⟩
    have h1 := hφ.dpow_comp (n := n) a ha
    have h2 := hψ.dpow_comp (n := n) a ha
    rw [h1]
    exact h2.symm

end GlobalTheory.CompanionTheory.PDMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftHomExistsUnique
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem lift_hom_existsUnique {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ}
    (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I) (𝓛 : Lift a T Λ I κ) {B : Type} [CommRing B]
    (J : Ideal B) : EtLift J → ∀ (h : Λ →+* B) (g : R →+* B ⧸ J) (u : Fin d → B), I ≤ J.comap h →
    (∀ o x, Ideal.Quotient.mk I x = κ o → g (a o) = Ideal.Quotient.mk J (h x)) →
    (∀ k, Ideal.Quotient.mk J (u k) = g (T k)) →
    ∃! f : 𝓛.D →+* B, f.comp 𝓛.i = h ∧ (∀ k, f (𝓛.t k) = u k) ∧
      ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk J (f z) = g r := by
  intro hEt h g u hIJ hg hu
  obtain ⟨g0, ⟨hg0i, hg0j⟩, hg0u⟩ := 𝓛.univ (B ⧸ J) ((Ideal.Quotient.mk J).comp h) g
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx)) (fun o x hx => hg o x hx)
  have hcomm : g0.comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) =
      (Ideal.Quotient.mk J).comp (MvPolynomial.eval₂Hom h u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hg0i c
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hu k]
      exact hg0j (T k) (𝓛.t k) (𝓛.hT k).symm
  obtain ⟨F, ⟨hFψ, hFg⟩, hFu⟩ :=
    hEt _ _ (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) 𝓛.et (MvPolynomial.eval₂Hom h u) g0 hcomm
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact RingHom.ext fun c => by simpa using RingHom.congr_fun hFψ (MvPolynomial.C c)
  · exact fun k => by simpa using RingHom.congr_fun hFψ (MvPolynomial.X k)
  · intro r z hz
    rw [← hg0j r z hz]
    exact RingHom.congr_fun hFg z
  · rintro f' ⟨hf'i, hf't, hf'j⟩
    apply hFu
    refine ⟨?_, ?_⟩
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact RingHom.congr_fun hf'i c
      · intro k
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact hf't k
    · apply hg0u
      refine ⟨?_, ?_⟩
      · rw [RingHom.comp_assoc, hf'i]
      · intro r z hz
        exact hf'j r z hz

end GlobalTheory.CompanionTheory.EtaleLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishingStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.satPowNonvan | exact GlobalTheory.CompanionTheory.SatPow.satPowNonvan | (intros; apply GlobalTheory.CompanionTheory.SatPow.satPowNonvan <;> assumption)
end


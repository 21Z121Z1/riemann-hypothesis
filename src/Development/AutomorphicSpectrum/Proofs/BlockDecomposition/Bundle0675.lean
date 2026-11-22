import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0655
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedRestrictPullBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmLoc

open Pb

theorem mor_mk_congr {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'} (G : C' ⥤ C)
    (τ τ' : (T : C') → F.obj (G.obj T) →ₛₗ[σ] F'.obj T) (n n') (h : τ = τ') :
    (⟨G, τ, n⟩ : CH.Mor F F' σ) = ⟨G, τ', n'⟩ := by
  subst h; rfl

theorem sq_incl_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    (incl h).sq (incl_fil h r) (incl_fil h r') =
      (CH.Mor.restrict (sq (sFil Q r) (sFil Q r')) (ObjectProperty.ιOfLE h) :) := by
  refine mor_mk_congr _ _ _ _ _ ?_
  funext T
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem chain {b : Base} {L : b.Fun} (r r' : ℤ) (Q1 Q2 Q3 : ObjectProperty (Thick L)) (h12 : Q2 ≤ Q1) (h23 : Q3 ≤ Q2) (n : ℕ)
    (b1 : Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n))
    (b2 : Function.Bijective (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n))
    (b3 : Function.Bijective (((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n)) :
    Function.Bijective ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) := by
  have e : CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι =
      (CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).comp
        (F' := sq (sFil Q1 r) (sFil Q1 r')) (σ' := RingHom.id _) (σ'' := RingHom.id _)
        (((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).comp (σ'' := RingHom.id _) ((incl h23).sq (incl_fil h23 r) (incl_fil h23 r'))) := by
    rw [sq_incl_eq, sq_incl_eq]
    rfl
  have f : ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q3.ι).pull n) =
      ⇑(((incl h23).sq (incl_fil h23 r) (incl_fil h23 r')).pull n) ∘
        ⇑(((incl h12).sq (incl_fil h12 r) (incl_fil h12 r')).pull n) ∘
          ⇑((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q1.ι).pull n) := by
    funext x
    rw [e]
    exact (P.pull_comp _ _ n x).1.trans ((P.pull_comp _ _ n _).1)
  rw [f]
  exact b3.comp (b2.comp b1)

theorem grT_restrict_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ →
    ∀ (a s : ℕ), a < s → ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (Pb.KS q s 𝒱).ι).pull n) := by
  intro K _ X q 𝒱 h𝒱 a s has n
  have hI : ∀ T : Thick (nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)), InU ⊤ T := fun T => le_of_eq rfl
  have h12 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {⊤} ≤ St ⊤ {⊤} :=
    fun T hT => ⟨trivial, hT.2⟩
  have h23 : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱 ≤ St (TF 1 s) {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, hI T⟩
  exact chain (L := nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)) (a : ℤ) ((a : ℤ) + 1) _ _ _ h12 h23 n
    (GlobalTheory.CompanionTheory.OmRes.restrict_pull_bijective_of_forall _ _ (fun T => ⟨trivial, ⊤, rfl, hI T⟩) n)
    (Pb.refl ⊤ 1 s (Or.inl ⟨rfl, rfl⟩) {⊤} h12 (a : ℤ) ((a : ℤ) + 1) (by omega) n)
    ((Pb.zar (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) 𝒱 {⊤} h23 (by rintro W rfl; exact h𝒱.ge) n).1 (a : ℤ) ((a : ℤ) + 1))

end GlobalTheory.CompanionTheory.OmLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentitiesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_polynomial_identity : ZpEq := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq | exact GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.zp_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponent
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeBound

theorem norm_lt_of_norm_mul_cpow_lt (q e : ℕ) (hq : 0 < q) (μ : ℂ)
    (h : ‖μ * (q : ℂ) ^ ((e : ℂ) / 2)‖ < 1) : ‖μ‖ < (q : ℝ) ^ (-((e : ℝ) / 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : (((e : ℂ) / 2)).re = (e : ℝ) / 2 := by
    have : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre] at h
  have hp : 0 < (q : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_pos_of_pos hq' _
  rw [Real.rpow_neg hq'.le, ← one_div, lt_div_iff₀ hp]
  exact h

theorem heckeSpectral_of_maxExpStrict (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hM : Zls.MaxExpStrict π) : Zls.HeckeSpectral π := by
  intro m hm j hj hjN T hT μ hμ
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  by_cases hμ0 : μ = 0
  · subst hμ0
    simpa using Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ)) _
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  let d : Fin 2 → ℕ := ![j, N - j]
  have hd : ∑ a, d a = N := by
    simp only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have d0 : d 0 = j := rfl
  have d1 : d 1 = N - j := rfl
  have hd0 : 0 < d 0 := hj
  have hd1 : 0 < d 1 := by rw [d1]; omega
  have hT' : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T := hT
  have hTw : T w = μ • w := hw.apply_eq_smul
  have hmk : (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := GlobalTheory.T.hecke_operator_jacquet_eigen_left k N V π hs m hm d hd hd0 hd1 T hT' w h0
    rw [hw.pow_apply r] at hr
    exact (smul_ne_zero (pow_ne_zero r hμ0) hw.2) hr
  have hjac := GlobalTheory.T.hecke_operator_jacquet_eigen_right k N V π hs m hm d hd hd0 hd1 T hT' w
  have heig : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (w : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) := by
    rw [← hjac, hTw]
    rfl
  obtain ⟨x, hx, hxd, hjm, hs0, c1, hs1⟩ :=
    GlobalTheory.T.jacquet_quotient_eigenvector k N V π hs hi hA hF d hd hd0 hd1 μ w hmk heig
  have hpos : ∀ a, 0 < (x a).1 := by
    intro a
    rw [hxd a]
    fin_cases a
    · exact hd0
    · exact hd1
  have hE := hM x hx hpos hjm
  have hc := (hE (Zls.unifU k) (GlobalTheory.T.uniformizer_pow_tendsto_zero k)
    ![μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2), c1]
    (by
      intro i
      fin_cases i
      · exact hs0
      · exact hs1)).1 0 (by simp)
  have hfil : Finset.univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [hfil, Finset.prod_singleton] at hc
  have := norm_lt_of_norm_mul_cpow_lt (Nat.card 𝓀[k]) (d 0 * d 1) hq μ hc
  simpa [d0, d1] using this

end GlobalTheory.CompanionTheory.HeckeBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem smooth_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → Geo.IsSmoothHerm A := by
  rintro m n M A ⟨u, -, -, hA⟩ z₀ hz₀
  choose c hc using hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z : (Σ k, Bk n k) → ℂ | z ⟨k, c k⟩ ≠ 0} := by ext; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hz : z₀ ∈ T := hc
  let s := multiprojectivePoint (m := m) (n := n) c
  obtain ⟨haff, hgen⟩ := GlobalTheory.T.multiprojective_chart_holomorphic_coordinates m n c
  have hmem : ∀ z ∈ T, s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := fun z h => (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z h).2
  obtain ⟨hcont, hholo⟩ := holo_of_affine haff hT hmem hgen
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)
  have hV : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hi, hmem z₀ hz⟩

  let F : CxPts (mpStr ℤ m n) σ₀ → ℝ := fun y =>
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)
  have hF : CInfAt F (s z₀) := by
    have h1 : CInfAt (fun y => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
        (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖) (s z₀) := by
      refine ⟨M.B.U i ⊓ mchart c, Unit, inferInstance, fun _ => (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)),
        fun v => ‖v ()‖, {v | v () ≠ 0}, hV, isOpen_ne_fun (continuous_apply _) continuous_const,
        ev_ne_zero hV (u i c).isUnit, ?_, Filter.EventuallyEq.rfl⟩
      intro v hv
      exact ((contDiffAt_norm ℝ hv).comp v ((contDiff_apply ℝ ℂ ()).contDiffAt)).contDiffWithinAt
    have h2 := (M.cInf σ₀) i (s z₀) hi
    exact h1.comp₂ h2 (G := fun x => x.1 * Real.exp (x.2 / 2))
      (contDiff_fst.mul (Real.contDiff_exp.comp (contDiff_snd.div_const 2)))
  have hFs := GlobalTheory.T.holomorphic_section_smooth_composition hT hcont hholo hz hF
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiffAt_norm ℝ (hc k)).comp z₀ ((contDiff_apply ℝ ℂ (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt)
    have hx : ‖z₀ ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hc k)
    cases h : A.a k with
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact hn.pow j
    | negSucc j =>
      simp only [zpow_negSucc]
      exact (hn.pow (j + 1)).inv (pow_ne_zero _ hx)
  refine (hP.mul hFs).congr_of_eventuallyEq ?_
  have hnb : ∀ᶠ z in nhds z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    Filter.Eventually.and (hT.mem_nhds hz) ((hcont.continuousAt (hT.mem_nhds hz)).preimage_mem_nhds ((isOpen_ptsIn _).mem_nhds hV))
  filter_upwards [hnb] with z hz'
  rw [hA i c (s z) z (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z hz'.1).1 hz'.2]
  simp only [F, Function.comp_apply]
  ring

end GlobalTheory.CompanionTheory.MPSmooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedgeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_cup_wedge : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  first | exact @GlobalTheory.CompanionTheory.OmCup.main | exact GlobalTheory.CompanionTheory.OmCup.main | (intros; apply GlobalTheory.CompanionTheory.OmCup.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_iso_of_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormTop.main | exact GlobalTheory.CompanionTheory.HodgeFormTop.main | (intros; apply GlobalTheory.CompanionTheory.HodgeFormTop.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOneStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_one : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | exact GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | (intros; apply GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_pullback_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  first | exact @GlobalTheory.CompanionTheory.OmNatT.pull_nat | exact GlobalTheory.CompanionTheory.OmNatT.pull_nat | (intros; apply GlobalTheory.CompanionTheory.OmNatT.pull_nat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem hasInfChar_conj_eq (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) (hB : IsHerm π B) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : π.HasInfChar τ m) (hm' : π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨φ, hφ⟩ := hB.2
  refine GlobalTheory.T.multiset_conjugate_neg_of_prod a m m' hm.1 hm'.1 fun u => ?_
  have val : ∀ (σ : E →+* ℂ) (l : Multiset ℂ), π.HasInfChar σ l → ∀ w : ℂ,
      Formalism.REAL.qdet (EopV π σ) (w + ((a : ℂ) - 1) / 2) φ = (l.map (w + ·)).prod • φ := by
    intro σ l hl w
    apply Subtype.ext
    rw [GlobalTheory.T.quantum_det_capelli_operator E a π σ w φ, hl.2 w φ.1 φ.2]
    rfl
  have key := GlobalTheory.T.quantum_det_adjoint_form π.V B a (EopV π τ) (EopV π (NumberField.ComplexEmbedding.conjugate τ))
    (GlobalTheory.T.lie_operator_gl_relations E a π _) (GlobalTheory.T.lie_operator_hermitian_skew E a π B hB τ) (u + ((a : ℂ) - 1) / 2) φ φ
  have arg : (a : ℂ) - 1 - (starRingEnd ℂ) (u + ((a : ℂ) - 1) / 2) =
      -(starRingEnd ℂ) u + ((a : ℂ) - 1) / 2 := by
    simp only [map_add, map_div₀, map_sub, map_one, Complex.conj_natCast, map_ofNat]
    ring
  rw [arg, val τ m hm u, LinearMap.smul_apply, val _ m' hm' (-(starRingEnd ℂ) u)] at key
  simp only [map_smul, LinearMap.smul_apply, smul_smul, map_smulₛₗ, smul_eq_mul] at key
  exact mul_right_cancel₀ hφ key

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnLowerZetaIntegrandStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_lower_zeta_integrand : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ, 0 < s.re →
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.integrableOn_low | exact GlobalTheory.CompanionTheory.RSZeta.integrableOn_low | (intros; apply GlobalTheory.CompanionTheory.RSZeta.integrableOn_low <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
section
noncomputable section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PerUInt

def phi (x : ℝ) : ℝ := ((1 + |x|) ^ 2)⁻¹

def gk (k : ℕ) (σ Y : ℝ) : ℝ :=
  if 0 < Y then Y ^ ((k : ℝ) - 1 - σ) * Real.exp (-(2 * Real.pi * Y)) else 0

theorem measurable_phi : Measurable phi := by
  unfold phi
  fun_prop

theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := by
  unfold phi
  positivity

theorem phi_le_one (x : ℝ) : phi x ≤ 1 := by
  unfold phi
  have h0 := abs_nonneg x
  apply inv_le_one_of_one_le₀
  nlinarith

theorem integrable_phi : Integrable phi := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [phi, Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem measurable_gk (k : ℕ) (σ : ℝ) : Measurable (gk k σ) := by
  unfold gk
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

theorem gk_nonneg (k : ℕ) (σ Y : ℝ) : 0 ≤ gk k σ Y := by
  unfold gk
  split_ifs with h
  · positivity
  · exact le_rfl

theorem integrable_gk (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) (hσ : σ < 1) : Integrable (gk k σ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb := GlobalTheory.CompanionTheory.WmFE.integrableOn_rpow_exp (σ := (k : ℝ) - 1 - σ) (by linarith)
    (show 0 < 2 * Real.pi by positivity)
  have hs : Function.support (gk k σ) ⊆ Ioi 0 := by
    intro x hx
    by_contra hn
    exact hx (by simp [gk, show ¬ 0 < x from hn])
  rw [← integrableOn_iff_integrable_of_support_subset hs]
  refine IntegrableOn.congr_fun hb (fun x hx => ?_) measurableSet_Ioi
  simp [gk, mem_Ioi.1 hx]

end GlobalTheory.CompanionTheory.PerUInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightRealStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_power_weight_real : ∀ (r N : ℝ), -1 < r → r + 1 < N → MeasureTheory.Integrable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) := by
  first | exact @GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow | exact GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow | (intros; apply GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow <;> assumption)
end


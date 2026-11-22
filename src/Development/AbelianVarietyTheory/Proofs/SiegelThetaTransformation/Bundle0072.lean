import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HalfIntegralGeneratorAddConjEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortRead

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem halfIntegralGenerator_add_conj_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ h1
  have h4 : 2 * τ H.w0 = 1 + τ H.rt := by simpa [map_ofNat] using congrArg τ h2
  have h5 : (τ H.rt).re = 0 := by
    have a := congrArg Complex.re h3
    have b := congrArg Complex.im h3
    have c : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [pow_two, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, neg_zero] at a b
    by_contra h
    have : (τ H.rt).im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at a
    nlinarith [mul_self_nonneg (τ H.rt).re]
  apply τ.injective
  rw [map_add, cc, IsCMField.complexEmbedding_complexConj, map_one, Complex.add_conj]
  have h6 := congrArg Complex.re h4
  simp only [add_re, one_re, h5, add_zero, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h6
  exact_mod_cast h6

theorem sb_smul (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) :=
  (isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 a

theorem sb_finsum {Q : Type} (f : Q → TF n g) (hf : ∀ q, IsSB (f q)) : IsSB (∑ᶠ q, f q) :=
  finsum_induction (fun φ : TF n g => IsSB φ) isSB_zero
    (fun φ ψ h h' => (isSB_algebra_haar_linear ℚ _ _ φ ψ h h').1) hf

theorem sb_gphi (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {M : ℕ} {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {v : TF n g} (hv : IsSB v) {Q : Type} (W : Q → ℂ)
    (Y : Q → Matrix (Fin n) (Fin r) E) : IsSB (gphi X bas w Λ L v W Y) := by
  obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r X g bas idx n hs hn w hw hw' L hL M Λ hΛ
  refine sb_finsum _ fun q => sb_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 _ _ ?_).1
  rw [h v hv v' hv']
  exact sb_smul _ hv'.1

theorem theta_smul₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {k : X.Ψ → Fin q0 → ℕ} {k' : X.Ψ → Fin X.p0 → ℕ} {φ : TF n g} (hφ : IsSB φ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : P ∈ Harm.rowHighest ℂ k k') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (a : ℂ) : thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hφ P hP).2.2.2 x hx
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP
  rw [h, I2.polyDeriv_smul_fun _ _ han.contDiff]

theorem rdU_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (Λ : GenLat E n) (N : ℕ) (rk : Bool) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → AdmX (l := l) rk x0 → P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ f ∈ sec Xo c a n, IsShortRule Xo c d Λ N x0 P f → ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hlev ⟨sr, hnab⟩ hunit hpin W k a hdom Dc hDe Λ N rk x0 P
    hΛ1 hΛ2 hΛ3 hadm hP f hf hshort
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hn : Even n := hdom.2
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨hle, hmap⟩ := admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpq := hle rk x0 hadm
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin hpq
  obtain ⟨-, hL, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hN : 0 < N := hΛ3.1.pos
  obtain ⟨Λ⟩ := Λ
  have hΛ : Λ ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ).2.1 _ N hM hΛ1 hΛ2 hΛ3
  obtain ⟨v, hv⟩ := (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv
  have hroots : ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ →
      ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ (U.X k).Λ mk₂ N Y := fun mk₂ h =>
    (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hL h (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hN

  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E,
      ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ → MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ →
      ∀ Y', IsRoots d.l₂ (U.X k).Λ mk₂ N Y' → ∃ t : ℂ, ‖t‖ = 1 ∧
        gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y' =
          t • gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y := by
    by_cases hex : ∃ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₃ ∧
        MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₃
    · obtain ⟨mk₃, h1, h2⟩ := hex
      obtain ⟨Y, hY⟩ := hroots mk₃ h1
      refine ⟨Y, fun mk₂ h3 h4 Y' hY' => ?_⟩
      obtain ⟨t, ht, h⟩ := GlobalTheory.Dict.MarkMove.gphi_move E H Dw l Xo c n d hlev ph ψ x₀ hph r _ _ Dc.bas Dc.idx Dc.sympl hn hrpq
        (hrpq ▸ hpq) _ hL (W.mark k) mk₂ mk₃ hmk h3 h1 h4 h2
      exact ⟨t, ht, h x0 v hv Λ hΛ N hΛ3 Y' Y hY' hY⟩
    · exact ⟨fun _ => 0, fun mk₂ h3 h4 => absurd ⟨mk₂, h3, h4⟩ hex⟩
  have hG := sb_gphi Dc.idx Dc.sympl hn hw hw' hL hΛ hv.1 (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y
  generalize gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = G at hY hG
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c ⟨Λ⟩))⁻¹ *
    (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
    ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) := ⟨_, rfl⟩
  have hP' := Dc.mem P hP
  have huG := sb_smul u hG
  have hsec := hU.2.2.2.2.1 a n hdom f hf k
  have hth := theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ huG _ hP'
  rw [Dc.wt_eq] at hth
  obtain ⟨C, -, hC⟩ := const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (u • G) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hsec.1, hth.1, fun x hx b hb => ⟨hsec.2.1 x hx b hb, hth.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC U k ⟨x, hx⟩)
      obtain ⟨B, hB, mk₂, hmk₂, hBm, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e x _
        _ A Dc.sympl hx hL y₂ hy₂ _ hA
      have hT := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hL θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv x hx θ hT
      have hκn := hnorm x hx hux θ κ hT hmean hκ
      obtain ⟨Y', hY'⟩ := hroots mk₂ hmk₂
      obtain ⟨t, ht, hmove⟩ := hY mk₂ hmk₂ hover Y' hY'
      obtain ⟨v0, hv0, hev⟩ := hshort ℂ halg _ y₂ hy₂
      have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hL _ n
        Dc.hr Dc.eL hrpq hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v κ (hB θ hθ) hv hκ mk₂ hmk₂ hBm Λ hΛ N hΛ3 Y' hY'
        a _ (hmap a P hP) _ _ v0 hv0
      have hmm : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
          MvPolynomial.map σ P := by
        rw [MvPolynomial.map_map]
        exact congrArg (fun s : c.F →+* ℂ => MvPolynomial.map s P) (RingHom.ext halg)
      rw [hmm, hmove, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx, ← hu] at hval
      refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ * t, by rw [norm_mul, norm_mul, hunit A₂ y₂, hκn, ht]; ring, fun _ => ?_⟩
      have hrd : rdU U f k x = evR Xo c f (unC U k ⟨x, hx⟩) := dif_pos hx
      beta_reduce
      rw [hrd, hev, hval, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx]
      ring)
  refine ⟨C • u • G, sb_smul C huG, fun x hx => ?_⟩
  rw [theta_smul₂ Dc.hr Dc.idx Dc.sympl hn huG hP' hx]
  exact hC () x hx

end GlobalTheory.Dict.ShortRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadingEqThP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThRead

theorem cmHost_idempotent_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (C : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r)
    (h : AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ) :
    thP X hr bas idx (C • φ) P x = C * thP X hr bas idx φ P x := by
  have e : thA X bas idx (C • φ) x = C • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
    ring
  rw [thP, thP, e, I2.polyDeriv, I2.polyDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply ((h 0 trivial).contDiffAt)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem isSB_smul {n g : ℕ} (C : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (C • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thValAt_evR (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (xs : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) {f : Rul Xo c} (hf : IsThRule Xo c nab xs P f)
    (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    ThValAt Xo c nab y xs P (evR Xo c f y) := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S y
  obtain ⟨w, hw, -⟩ := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn S y a n xs P hP
  have e : evR Xo c f y = w := by
    unfold evR evalAt
    rw [dif_pos ht]
    exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ S _ _ y ht.choose_spec.choose_spec.choose_spec
      a n xs P hP _ w (hf _ _) hw
  rw [e]
  exact hw

theorem reading_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ n : ℕ, ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (xs : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xs P f → f ∈ sec Xo c a n ∧ ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hC E _ _ _ H Dw l Xo c σ r U hσ hU hr1 _ nab hn n W k a hD Dc he xs P hP f hf
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hsec : f ∈ sec Xo c a n := GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xs, P, hP, hf⟩
  refine ⟨hsec, ?_⟩
  have hev : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw1 := cmHost_idempotent_trace_eq_one H
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv
  set Y₀ := Y (fun b => Submodule.Quotient.mk (xs b)) with hY₀
  have hsb : IsSB (heisG (U.X k) Dc.bas Y₀ v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev).2.2.2 Y₀ v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev Dc.k Dc.k'
    _ hsb _ (Dc.mem P hP.1)
  have hS := hU.2.2.2.2.1 a n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = laU U a n k := Dc.wt_eq
  rw [hwt] at hhol
  obtain ⟨C, -, hCeq⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit
    (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (heisG (U.X k) Dc.bas Y₀ v)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hS.1, hhol.1, fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      letI : Algebra c.F ℂ := σ.toAlgebra
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      have h1 := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv x hx θ h1
      refine ⟨κ, hnorm x hx hux θ κ h1 hmean hκ, fun _ => ?_⟩
      have hval := thValAt_evR hC Xo c nab hn xs hP hf ℂ (unC U k ⟨x, hx⟩)
      have := GlobalTheory.Dict.thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd Dw.p n Dc.hr
        Dc.eL hU.1 hev (he ▸ Dc.dir_eq) nab hn θ v κ hθ hv hκ (W.mark k) hmk hA xs Y₀ (fun b => by
          obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY (fun b => Submodule.Quotient.mk (xs b)) b
          exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hy⟩, hj⟩) a P hP _ hval
      refine Eq.trans ?_ this
      show (if h : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) = _
      rw [dif_pos hx]
      rfl)
  refine ⟨C • heisG (U.X k) Dc.bas Y₀ v, isSB_smul C hsb, fun x hx => ?_⟩
  rw [theta_smul₂ _ _ _ _ _ _ _ _ (hhol.2.2.2 x hx)]
  exact hCeq () x hx

end GlobalTheory.Dict.ThRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (wq : (Fin n → LevQ Dw l) → c.F) (β : c.F) (v0 : ℂ), ShortValAt Xo c nab wq (⟨Λ⟩ : GenLat E n) β N P y v0 → v0 = algebraMap c.F ℂ (β⁻¹ * (((⟨Λ⟩ : GenLat E n).mIdx N r : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((⟨Λ⟩ : GenLat E n).zCard N r : c.F)) * κ * thP X hr bas idx (gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap c.F ℂ (wq q)) Y) (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  first | exact @GlobalTheory.Dict.shortValAt_eq_thP | exact GlobalTheory.Dict.shortValAt_eq_thP | (intros; apply GlobalTheory.Dict.shortValAt_eq_thP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_standardLattice_eq_classicalTheta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → ∀ (xs : Fin n → Dw.La) (Y : Matrix (Fin n) (Fin r) E), (∀ b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), a - xs b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧ Y b - ((l.M : E)⁻¹) • mk a ∈ L) ∧ ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • Y b = (2 * l.M) • u) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 : ℂ, ThValAt Xo c nab y xs P v0 → v0 = κ * thP X hr bas idx (heisG X bas Y v) (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  first | exact @GlobalTheory.Dict.thVal_eq_thP | exact GlobalTheory.Dict.thVal_eq_thP | (intros; apply GlobalTheory.Dict.thVal_eq_thP <;> assumption)
end


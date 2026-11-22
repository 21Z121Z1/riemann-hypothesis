import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverProductIndepOfLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelMapsRankZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0076
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOneClassSeriesDescends
section
section Descent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.CoverDescent GlobalTheory.ClsVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClsDescent

theorem value_descends (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hlev : d.IsLev)
    (hA : d.l₂.A = l.A) [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (ψ₀ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (hψ₀ : d.PsiTie ψ₀) (w : (Fin n → LevQ Dw d.l₂) → c.F)
    (hw₀ : DatEq d ψ₀ w) (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod) (hTr : Λ.TrivAt d.l₂.M) (hLv : Λ.LevOK N d.l₂.M)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F)
    (hP : P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (β : d.c₂.F)
    (p : TRing c.F) (y : FrPt Xo c p.R) :
    ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P z₂ v →
        χ u = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hN := GlobalTheory.LevelMapsAnyRank.levelMaps Dw
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hTr hLv a P hP
    (fun q => d.eF (w q)) β
  have hinv := GlobalTheory.EquivariantLiftInvariance.cover_product_indep_of_lift hC E H Dw l Xo c n d hlev hA ⟨_, hnab⟩ ψ₀ hψ₀ w hw₀ Λ N hU hTr hLv a P hP β
  have hbc := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c
  have hbc₂ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂
  have hcomp := (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1
  obtain ⟨hdvd, hM, -, -, -, -, hlift, hsec, -⟩ := id hlev
  obtain ⟨r, jK, m, -, -, he, heA, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h1, h2, _, _, _, -⟩ := hF c d.c₂ d.hF.symm
  have hEta : DeltaDat.EtaOK { d with r := r, m := m } := by
    refine ⟨fun b => ?_, heA⟩
    have := he b
    rwa [hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)] at this
  obtain ⟨hov1, hov2, -⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n { d with r := r, m := m }
  obtain ⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩ :=
    exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over
  letI : Algebra p.R S := φ.toAlgebra
  letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra
  letI : Algebra d.c₂.F S := j.toAlgebra
  haveI : Module.Finite p.R S := f1
  haveI : Algebra.Smooth p.R S := f2
  haveI : Module.FaithfullyFlat p.R S := f3
  haveI := isReduced_of_smooth_algebra p.R S
  have hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := fun a =>
    RingHom.congr_fun hj a
  let φa : p.R →ₐ[c.F] S := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := hbc p.R S φa y
  obtain ⟨y₂, -, hy₂⟩ := hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'
  obtain ⟨v₀, hv₀, -⟩ := hval S y₂
  have core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom →
      ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P z₂ v →
        χ' (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
    intro k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂ v hv
    have c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a := fun a =>
      (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)
    let ψ : S →ₐ[c.F] k := { χ' with commutes' := c1 }
    let ψ₂ : S →ₐ[d.c₂.F] k := { χ' with
      commutes' := fun b => by
        obtain ⟨a, rfl⟩ := d.eF.surjective b
        exact (congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }
    have hψ : ψ.comp φa = χ := AlgHom.ext fun x => RingHom.congr_fun hχ x
    have hz' : FrMap ψ y' z := (hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)
    obtain ⟨w₂, hw₂⟩ := hbc₂ S k ψ₂ y₂
    have hw' := hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂
    obtain ⟨v', hv', -⟩ := hval k w₂
    rw [hinv r m hEta k hk z z₂ w₂ hz₂ hw' v v' hv hv', ← hnat S k ψ₂ y₂ w₂ hw₂ v₀ v' hv₀ hv',
      evR_baseChange hWD hAT d.cδ hsec.1 ψ₂ y₂ w₂ hw₂]
    exact map_mul χ' _ _
  have pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k),
      ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k)
        (z₂ : FrPt d.Xo₂ d.c₂ k) (v : k),
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧
        FrMap χa y z ∧ FrOver d z₂ z ∧ ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P z₂ v := by
    intro k _ _ χ
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hbc p.R k χa y
    obtain ⟨z₂, hz₂⟩ := hlift k hk z
    obtain ⟨v, hv, -⟩ := hval k z₂
    exact ⟨i1, i2, χa, z, z₂, v, hk, rfl, hz, hz₂, hv⟩
  obtain ⟨u, hu⟩ := exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) (by
    intro k _ _ χ₁ χ₂ h12
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k (χ₁.comp φ)
    exact (core k hk χa χ₁ hχ.symm z z₂ hz hz₂ v hv).trans
      (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂ v hv).symm)
  refine ExistsUnique.intro u ?_ ?_
  · intro k _ _ _ _ hk χ z z₂ hz hz₂ v hv
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ.toRingHom
    rw [← core k hk χ χ' hχ' z z₂ hz hz₂ v hv, ← hu]
    exact (RingHom.congr_fun hχ' u).symm
  · intro u' hu'
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k χ
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ
    subst hχ
    have e := core k hk χa χ' hχ' z z₂ hz hz₂ v hv
    rw [← hu] at e
    exact (hu' k hk χa z z₂ hz hz₂ v hv).trans (e.symm.trans (RingHom.congr_fun hχ' u))

end GlobalTheory.ClsDescent

end Descent

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsDescent

open GlobalTheory.ShortDescent in

theorem exists_sec_oneClass : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d (fun _ : Unit => w) (fun _ => Λ) (fun _ => N) (fun _ => 1) 1 (fun _ => 1) LinearMap.id (fun _ => P) f := by
  intro hC E _ _ _ H Dw l Xo c n d hLev hA hnab ψ hψ w₀ hw₀ Λ N hU hT hO a P hP
  obtain ⟨_, hnab⟩ := hnab
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hAll := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hP₂ := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP
  obtain ⟨hex, -⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hO a _ hP₂
    (fun q => d.eF (w₀ q)) 1
  have hd := value_descends hC d hLev hA hnab ψ hψ w₀ hw₀ Λ N hU hT hO a _ hP₂ 1
  obtain ⟨hlift, -, hbor⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d
  refine ⟨fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩
  · refine (hd q z).unique (hd q z).exists.choose_spec ?_
    intro k _ _ _ _ hk χ w w₂ hw ho v hv
    exact (hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho v hv
  · refine (hd p y').unique (hd p y').exists.choose_spec ?_
    intro k _ _ _ _ hk χ w' w₂' hw' ho' v' hv'
    obtain ⟨w, hw⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y
    have hb := frBorBC _ _ χ t y y' w w' h hw hw'
    obtain ⟨w₂, hx₂, ho⟩ := hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over
    have hb₂ := hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb
    obtain ⟨v, hv, -⟩ := hex k w₂
    have hv₂ := (GlobalTheory.thetaValue_weight hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k w₂ w₂' _ hb₂ n a _).2 hP₂
      _ Λ _ N v hv
    have e := (hd p y).exists.choose_spec k hk χ w w₂ hw ho v hv
    rw [(hex k w₂').unique hv' hv₂, map_mul, map_wchar, evR_eq_of_point_eq d hψ w₂ w₂' hx₂.symm]
    refine (congrArg (_ * ·) e).trans ?_
    ring
  · intro k _ _ _ _ hk y y₂ ho
    obtain ⟨v, hv, -⟩ := hex k y₂
    refine ⟨fun _ => v, fun _ => hv, ?_⟩
    have hy := hAll k y
    have e : ∑ _cl : Unit, algebraMap c.F k (1 * (((1 : ℕ) : c.F))⁻¹ * 1) * v = v := by simp
    rw [e]
    unfold evR evalAt
    rw [dif_pos hy]
    exact (hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho v hv

end GlobalTheory.ClsDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SpanInhab

theorem exists_imag_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  have h0 : (H.rt : E) ≠ 0 := by
    intro h
    rw [h] at hE
    have : (H.d : E) = 0 := by linear_combination hE
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, h0, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 h0, fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    have : cc (-(H.rt : E)) = -cc (H.rt : E) := by simp [cc]
    rw [this, hcc]

theorem exists_prime_jacobi_neg {d : ℕ} (hd : Odd d) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ jacobiSym (-(d : ℤ)) p = 1 := by
  obtain ⟨p, hp, hN, hm⟩ := Nat.exists_prime_gt_modEq_one (k := 4 * d) N (by have := hd.pos; omega)
  have h4 : p % 4 = 1 := hm.of_mul_right d
  have hpd : p ≡ 1 [MOD d] := hm.of_mul_left 4
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  refine ⟨p, hN, hp, ?_⟩
  rw [jacobiSym.neg _ hodd, ZMod.χ₄_nat_one_mod_four h4, _root_.one_mul,
    ← jacobiSym.quadratic_reciprocity_one_mod_four h4 hd,
    jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast hpd), jacobiSym.one_left]

theorem exists_split_cover {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) :
    ∃ (pd : ℕ) (J : Ideal (𝓞 E)) (l₂ : Geo.Tor.Level H) (c : Coeff l) (c₂ : Coeff l₂), pd.Prime ∧ 3 < pd ∧
      c₂.F = c.F ∧ l.Dvd l₂ ∧ l₂.M = l.M * pd ∧ pd.Coprime l.M ∧ l₂.Mb = l.Mb * J ∧
      J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ l₂.A = l.A := by
  have hM := l.three_le
  obtain ⟨p, hN, hp, hj⟩ := exists_prime_jacobi_neg (d := H.d) (Nat.odd_iff.2 (by have := H.d_mod; omega)) l.M
  have hco : p.Coprime l.M := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  obtain ⟨J, h1, h2, h3⟩ := (GlobalTheory.exists_level_mul_split E H l).2 p hp (by omega) hj
  obtain ⟨l₂, hd, hM₂, hMb, hA⟩ := (GlobalTheory.exists_level_mul_split E H l).1 p J (hp.odd_of_ne_two (by omega)) hco h1 h2 h3
  let c₂ : Coeff l₂ := LevelExist.minCoeff l₂
  have hz : zeta l.M' ∈ c₂.F := by
    obtain ⟨k, hk⟩ := LevelExist.zeta_eq_pow_of_dvd (LevelExist.M'_pos l₂)
      (show l.M' ∣ l₂.M' from Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)))
    rw [hk]
    exact pow_mem c₂.zeta_mem k
  have hle : KA l ≤ c₂.F := by
    have := c₂.le
    unfold KA at this ⊢
    rwa [hA] at this
  exact ⟨p, J, l₂, ⟨c₂.F, c₂.fin, c₂.conj, hz, hle⟩, c₂, hp, by omega, rfl, hd, hM₂, hco, hMb, h3, hA⟩

end GlobalTheory.SpanInhab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.Dict

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ σ, GoodEmb c σ → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → GlobalTheory.Dict.holSub0 (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU (U σ) '' (Formalism.L2.PjFree.cusp Xo c U a n : Set (Rul Xo c))) := by
  intro hC E _ _ _ H Dw l Xo c r U hr hA hU σ hσ hG hP a n hdom hlast hn hχ
  have hrk : r = Dw.p + Dw.q := (hU σ hσ).1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂.A = l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine (GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta hC E H Dw l Xo c n d σ r (U σ) hσ (hU σ hσ) hr hA hG hP hlev hnab hunit h3
    (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hχ htot).trans
    (Submodule.span_mono (Set.image_mono ?_))
  exact GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC E H Dw l Xo c n d r U hr hU hlev hnab hunit (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a hdom hlast

end GlobalTheory.Dict
end


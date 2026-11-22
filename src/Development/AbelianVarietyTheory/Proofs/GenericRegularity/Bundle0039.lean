import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0027
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspOfIntegralAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_of_integral_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ h : GenFrEx Xo c, ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (Z : Comp Xo c) (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F) (b : Om Z), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → b ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval (fun s => evC h Z (w s)) (cf i) * b ^ i = 0 → ∃ g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n), evC h Z g = b := by
  intro E _ _ _ H Dw l Xo c h r U hU a n N w hDom hw Z k m cf b hk hcf hb
  obtain ⟨hEv, -, -, hAt⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  have hws : ∀ i, w i ∈ sec Xo c a n := fun i => (hw i).1
  obtain ⟨g, hg, hgZ, -, hgeq⟩ :=
    GlobalTheory.T.exists_modularSection_of_integral_genericValue E H Dw l Xo c hEv h (hAt h) a n N w hws Z k m cf b hcf hb
  exact ⟨g, GlobalTheory.T.isCuspForm_of_integral_over_dominantWeight E H Dw l Xo c hEv.test r U hU a n N w hDom hw k m cf hk hcf g hg hgeq, hgZ⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictCompInt
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_cusp_restrict_comp_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (h : GenFrEx Xo c) (Z : Comp Xo c) a n, ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ (∀ Z', Z' ≠ Z → evC h Z' g' = 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), evI y g' = evI y g ∨ evI y g' = 0 := by
  intro E _ _ _ H Dw l Xo c r U hU h Z a n g hg
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := exists_idem_section E H Dw l Xo c hL h (hA h) Z

  have hm : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f f' : Rul Xo c),
      evR Xo c (f * f') y = evR Xo c f y * evR Xo c f' y := by
    intro S _ _ y f f'
    unfold evR
    exact evalAt_mul _ _ f f' y
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_, ?_⟩
  · unfold evC at h1 ⊢
    rw [hm, h1, one_mul]
  · intro Z' hZ'
    have h0' := h0 Z' hZ'
    unfold evC at h0' ⊢
    rw [hm, h0', zero_mul]
  · intro T io y
    letI := io.toAlgebra
    unfold evI

    have hy : IsIdempotentElem (evR Xo c χ y.1) := by
      unfold IsIdempotentElem
      rw [← hm, hidem]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hy with h' | h'
    · right
      rw [hm, h', zero_mul]
    · left
      rw [hm, h', one_mul]

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSection
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.GenFactor

open GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_factor (hT : Out.SecTwistSt) {Z : Type} (x u : Sp ℂ ⟶ Xo.X) (hxu : x = u) (s : LB.Sec (PPx x))
    (hs : SecGen x s) (e : Z → (Over.mk u ⟶ Xo.univ.t.G)) (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ)
    (hθ : ∃ z, θ z ≠ 0) (hfr : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (t : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).Sec)
    (ht : ∀ j z (p : Sp ℂ ⟶ pullback Xo.univ.t.G.hom u), p ≫ pullback.fst _ _ = (e z).left →
      p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' p ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom u)).U (fun _ => j)) (t.f (fun _ => j)) =
        θ z * fr j z) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (e z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z := by
  subst hxu
  obtain ⟨s', hs'⟩ := GlobalTheory.FibreSection.exists_sec_same_values E H Dw l Xo x t
  obtain ⟨a, ha, -⟩ := hs s'
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (e z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      a * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z := by
    intro j z pt e₁ e₂ hj
    have hw : (e z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ x := (Over.w (e z)).trans (Category.id_comp _).symm
    have p₁ := pullback.lift_fst (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    have p₂ := pullback.lift_snd (f := Xo.univ.t.G.hom) (g := x) (e z).left (𝟙 _) hw
    refine ((sec_values_complex_fibre hT E H Dw l Xo x s).1 a (fun _ => j) pt e₂).symm.trans ?_
    refine (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).symm.trans ?_
    exact (hs' j pt _ (p₁.trans e₁.symm) p₂ e₂).trans (ht j z _ p₁ p₂ hj)
  obtain ⟨z₀, hz₀⟩ := hθ
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e z₀).left
  obtain ⟨pt₀, e₁, e₂⟩ := exists_pt (R := ℂ) x (𝟙 _) (e z₀).left
    ((Category.id_comp _).trans (Over.w (e z₀)).symm)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := key j₀ z₀ pt₀ e₁ e₂ hj₀
    rw [zero_mul] at this
    exact mul_ne_zero hz₀ (hfr j₀ z₀ hj₀) this.symm
  refine ⟨a⁻¹, inv_ne_zero ha0, fun j z pt e₁ e₂ hj => ?_⟩
  rw [mul_assoc, ← key j z pt e₁ e₂ hj, inv_mul_cancel_left₀ ha0]

end

theorem exists_holomorphic_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) ty B P → (∀ b ∈ B, (y b).x = F.u k (P b)) → (∀ z, DifferentiableOn ℂ (fun b => θ b z) B) → (∀ b ∈ B, ∃ z, θ b z ≠ 0) → IsThetaFrame Xo.univ.t.PP B (fun b => F.u k (P b)) (fun b z => (F.ex k (P b) z).left) θ → ∃ (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (κ : (Fin m → ℂ) → ℂ), RigFrame F k B P fr ∧ DifferentiableOn ℂ κ B ∧ ∀ b ∈ B, κ b ≠ 0 ∧ SecVal F k (P b) (y b).x (y b).s (fun z => κ b * θ b z) (fun j z => fr j (b, z)) := by
  intro E _ _ _ H Dw l Xo c σ σ' g ty F k A _ _ yA m B ψ y P θ hB hψ hb hP hxu hθ hθ0 hfr
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨fr, f₁, f₂, f₃, f₄, f₅⟩ := hfr
  have hκ₁ : ∀ b, ∃ κ : ℂ, b ∈ B → κ ≠ 0 ∧
      SecVal F k (P b) (y b).x (y b).s (fun z => κ * θ b z) (fun j z => fr j (b, z)) := fun b => by
    by_cases h : b ∈ B
    · obtain ⟨t, ht⟩ := f₅ b h
      obtain ⟨κ, h₁, h₂⟩ := exists_factor hT (y b).x (F.u k (P b)) (hxu b h) (y b).s (y b).gen (F.ex k (P b)) (θ b)
        (fun j z => fr j (b, z)) (hθ0 b h) (fun j z hz => f₂ j b z h hz) t ht
      exact ⟨κ, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose κ hκ using hκ₁
  refine ⟨fr, κ, ⟨f₁, f₂, f₃, f₄⟩, fun b₀ hb₀ => ?_, hκ⟩
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd yA.x) (gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have d₁ : DifferentiableOn ℂ (fun b => θ b w₀) W := (hθ w₀).mono fun b h => h.1
  have d₂ : DifferentiableOn ℂ (fun b => fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) (g := fr j)
      (f₁ j) hι.differentiableOn fun b h => ⟨h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      κ b * (θ b w₀ * fr j (b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hκ b h.1).2 j w₀ pt e₁ e₂ (m₂ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, θ b w₀ * fr j (b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : DifferentiableOn ℂ κ W := (d₃.mul ((d₁.mul d₂).inv nz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.GenFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwiseStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  first | exact @GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | exact GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm | (intros; apply GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Comparison₂

theorem isReduced_cAt {K : Type} [Field K] (σ : K →+* ℂ) : IsReduced (CAt σ) :=
  inferInstanceAs (IsReduced ℂ)

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (z w : CAt σ) : cabs (z * w) = cabs z * cabs w :=
  norm_mul (show ℂ from z) (show ℂ from w)

theorem cabs_wchar {K : Type} [Field K] {σ : K →+* ℂ} {ι : Type} [Fintype ι] (e : ι → ℕ) (t : ι → (CAt σ)ˣ) :
    cabs (wchar e t) = ∏ i, cabs (t i : CAt σ) ^ e i := by
  have h := norm_prod (α := ℂ) Finset.univ (fun i => (show ℂ from (t i : CAt σ)) ^ e i)
  exact h.trans (Finset.prod_congr rfl fun i _ => norm_pow (α := ℂ) _ _)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (u : (CAt σ)ˣ) : 0 < cabs (u : CAt σ) :=
  norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) u)

theorem cabs_conjAlg {K : Type} [Field K] (σ : K →+* ℂ) (z : CAt σ) : cabs (conjAlg σ z) = cabs z :=
  Complex.norm_conj (show ℂ from z)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem baseNorm_pos (Dw : Datum H) {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some p => exact Real.sqrt_pos.2 (by positivity)

theorem prod_baseNorm (Dw : Datum H) {x : ℝ} (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∏ i, (baseNorm Dw x i)⁻¹ ^ ex Dw a n i = Formalism.L2.PjFree.lieFac Dw x a := by
  classical
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hs : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, ← Real.exp_neg]
    congr 1; ring
  rw [Fintype.prod_option]
  simp only [baseNorm, ex, inv_one, one_pow, one_mul, hs, ← Real.exp_nat_mul]
  rw [← Real.exp_sum, Formalism.L2.PjFree.lieFac, ← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_sigma]
  ring

theorem ptNorm_eq_pnorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hP
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ y i, fn σ y i ≠ 0 := by
    intro σ hσ y i
    obtain ⟨k, x, t, hx1, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).2 y
    have h := hP.1 σ hσ k x hx1 t y ht i
    rw [← abs_pos, h]
    exact mul_pos (cabs_unit_pos _) (baseNorm_pos Dw hx i)
  refine ⟨fun σ y i => ?_, fun σ hσ k x t y ht a n hd f hf => ?_, fun σ y y' hm a n f hf => ?_⟩
  · by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · exact hgood σ hσ y i
    · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
        have h := Formalism.L2.PjFree.goodEmb_goodOf c σ
        rwa [Formalism.L2.PjFree.goodOf, if_neg hσ] at h
      obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
      rw [← abs_pos, ← hP.2 σ y y' hy' i, abs_pos]
      exact hgood _ hσ' y' i
  · obtain ⟨x', hx', -, ⟨t', ht'⟩, hpn⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).1 k x
    have htt := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).2.1 t' t _ _ _ ht' ht
    have hfn := hP.1 σ hσ k x' hx' _ y htt
    have hev := hwt (CAt σ) (isReduced_cAt σ) a n f hf _ _ _ htt
    rw [hpn _ _ ((hU σ hσ).2.2.2.2.1 a n hd f hf k)]
    have hrd : ‖Formalism.L2.PjFree.rdU (U σ) f k x'.1‖ = cabs (evR Xo c f ((U σ).un k x')) := by
      have e : Formalism.L2.PjFree.rdU (U σ) f k x'.1 = Formalism.L2.PjFree.toC (evR Xo c f ((U σ).un k x')) :=
        dif_pos x'.2
      rw [e]; rfl
    rw [hrd, ← prod_baseNorm Dw hx a n]
    change cabs (evR Xo c f y) * _ = _
    rw [hev, cabs_mul, cabs_wchar, mul_right_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hfn i, ← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (cabs_unit_pos _).ne', one_mul]
  · have := isReduced_cAt σ
    have hev := evR_frMap hWD f hf.1 (conjAlg σ) y (hT _ y) y' hm
    change cabs (evR Xo c f y') * _ = cabs (evR Xo c f y) * _
    rw [hev, cabs_conjAlg]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [hP.2 σ y y' hm i]

end GlobalTheory.FrameNorm.Comparison₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem sCharts_and_transfer_of_good_level : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) ∧ (∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U) ∧ ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro hP hN E _ _ _ H Dw l Xo c hr hg
  classical
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨hE, hI, -⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  have hM : ∀ la, ModelAt Xo c la := by
    intro la
    have h := modelAt_of_good_level hP E H Dw hr
      (Function.update (fun l' => Classical.choice (hN E H Dw l' hr)) l Xo) l c la (fun p hp _ => hg p hp)
    rwa [Function.update_self] at h
  exact ⟨fun la => GlobalTheory.T.exists_normalCharts_everyFinitePlace hT E H Dw l Xo c hE hI la (hM la), GlobalTheory.T.transfer_bounds_algebraic_to_all_points_of_models hT E H Dw l Xo c hE hI hM⟩

end GlobalTheory.Reg
end


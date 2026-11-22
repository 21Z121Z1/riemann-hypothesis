import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopie
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def deg1 (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) : Submodule ℂ (Polynomial (HA M)) :=
  (W.comap (HA M).val.toLinearMap).map ((Polynomial.monomial 1).restrictScalars ℂ)

theorem mem_homogeneousExponentsOneBlock (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (p : Polynomial (HA M)) :
    p ∈ deg1 M W ↔ ∃ f : HA M, (f : C → M.dom → ℂ) ∈ W ∧ Polynomial.monomial 1 f = p := Iff.rfl

def deg1Equiv (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) :
    W ≃ₗ[ℂ] deg1 M W :=
  LinearEquiv.ofBijective
    ({ toFun := fun f => ⟨Polynomial.monomial 1 ⟨f, hW f f.2⟩, (mem_homogeneousExponentsOneBlock M W _).2 ⟨⟨f, hW f f.2⟩, f.2, rfl⟩⟩
       map_add' := fun f g => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((f + g : W) : C → M.dom → ℂ), hW _ (f + g).2⟩ : HA M) =
           Polynomial.monomial 1 ⟨f, hW _ f.2⟩ + Polynomial.monomial 1 ⟨g, hW _ g.2⟩
         rw [← map_add]
         rfl)
       map_smul' := fun z f => Subtype.ext (by
         show Polynomial.monomial 1 (⟨((z • f : W) : C → M.dom → ℂ), hW _ (z • f).2⟩ : HA M) =
           z • Polynomial.monomial 1 ⟨f, hW _ f.2⟩
         rw [Polynomial.smul_monomial]
         rfl) } :
      W →ₗ[ℂ] deg1 M W)
    ⟨fun f g hfg => by
      have := congrArg Subtype.val hfg
      have := Polynomial.monomial_injective 1 this
      exact Subtype.ext (congrArg (fun q : HA M => (q : C → M.dom → ℂ)) this),
     fun p => by
      obtain ⟨f, hf, hp⟩ := (mem_homogeneousExponentsOneBlock M W p.1).1 p.2
      exact ⟨⟨f, hf⟩, Subtype.ext hp⟩⟩

theorem deg1Equiv_coe (M : TwoLevels E r U C) (W : Submodule ℂ (C → M.dom → ℂ)) (hW : ∀ f ∈ W, f ∈ HA M) (f : W) :
    ((deg1Equiv M W hW f : deg1 M W) : Polynomial (HA M)) = Polynomial.monomial 1 ⟨f, hW f f.2⟩ := rfl

theorem mul_pb_mem_cusp (M : TwoLevels E r U C) (ka mu : Wt M.Ψ r) (u0 : C → Frame M.Ψ r → ℂ) (hu0 : u0 ∈ M.SS mu)
    (k h : U) {f : C → M.dom → ℂ} (hf : f ∈ M.cusp ka) :
    f * pb M k (M.res u0) * pb M h (M.res u0) ∈ M.cusp (ka + 2 • mu) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, rfl⟩ := hf
    have e : M.res F * pb M k (M.res u0) * pb M h (M.res u0) = M.res (F * M.pull k u0 * M.pull h u0) := rfl
    rw [e, two_smul, ← add_assoc]
    exact Submodule.subset_span ⟨_, GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ (GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight E r U C M _ _ _ _ hF
      (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 k hu0)) (GlobalTheory.T.twoLevelCuspForms_pull_mem E r U C M mu u0 h hu0), rfl⟩
  | zero => simp
  | add f g _ _ hf hg => rw [add_mul, add_mul]; exact add_mem hf hg
  | smul z f _ hf => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ z hf

end GlobalTheory.CuspEmb

open GlobalTheory.CuspEmb in

theorem GlobalTheory.CuspEmb.cusp_embReg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∀ ep c : ℝ, Ranks M ka (sOf M) ep c → ∀ H : Subgroup U, LevelHyp (sub M H) →
    ∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ ep c0 hR H hL
  classical
  haveI : Fintype U := Fintype.ofFinite U
  obtain ⟨u0, hu0, hdet⟩ := GlobalTheory.T.exists_cuspForm_independent_translates E r H C (sub M H) hL (sOf M) (even_sOf M) (le_sOf M)
  have hu0' : u0 ∈ M.SS (deMul M.Ψ r M.p0 (sOf M)) := hu0
  have hVHA : ∀ f ∈ M.cusp ka, f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M ka F hF
  have h2HA : ∀ f ∈ M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)), f ∈ HA M := fun f hf => by
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (HA M))).2 ?_ hf
    rintro _ ⟨F, hF, rfl⟩
    exact GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ F hF
  obtain ⟨a, hcoc, hform⟩ := GlobalTheory.T.exists_cocycle_pullbackRepresentation E r U C M ka ρ hρ (fun f hf => (hVHA f hf).2)
  obtain ⟨h1, hlaw⟩ := GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle E r U C M a hcoc
  let act : U →* (Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M)) :=
    { toFun := fun k => tw M (fun c => (a k⁻¹ c : ℂ)) k⁻¹
      map_one' := by
        show tw M (fun c => (a 1⁻¹ c : ℂ)) 1⁻¹ = 1
        rw [inv_one]
        exact h1
      map_mul' := fun g h => by
        simp only [mul_inv_rev]
        rw [← hlaw]
        rfl }
  let ut : HA M := ⟨M.res u0, GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant E r U C M _ u0 hu0'⟩
  have hact : ∀ k, act k (Polynomial.C ut) = Polynomial.C (pbA M k⁻¹ ut) := fun k => tw_C M _ _ _
  have hactm : ∀ k (f : HA M), act k (Polynomial.monomial 1 f) =
      Polynomial.monomial 1 (cst M (fun c => (a k⁻¹ c : ℂ)) * pbA M k⁻¹ f) := fun k f => tw_monomial_one M _ _ _

  have hnz : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)).det ∈ nonZeroDivisors (Polynomial (HA M)) := by
    have e : (Matrix.of fun h g : H => act ((h : U) * g) (Polynomial.C ut)) =
        (Polynomial.C : HA M →+* Polynomial (HA M)).mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) := by
      refine Matrix.ext fun h g => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hact, mul_inv_rev]
    rw [e, ← RingHom.map_det]
    refine GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors E r U C M _ fun c => ?_
    obtain ⟨x, hx, hne⟩ := hdet c
    refine ⟨⟨x, hx⟩, ?_⟩
    let φ : HA M →+* ℂ := ((Pi.evalRingHom _ (⟨x, hx⟩ : M.dom)).comp (Pi.evalRingHom _ c)).comp (HA M).val.toRingHom
    have e2 : ((Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det : C → M.dom → ℂ) c ⟨x, hx⟩ =
        φ (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut).det := rfl
    rw [e2, RingHom.map_det]
    have e3 : φ.mapMatrix (Matrix.of fun h g : H => pbA M ((h : U) * g)⁻¹ ut) =
        ((Matrix.of fun h h' : H => M.pull ((h : U) * h') u0 c x).submatrix (Equiv.inv H) (Equiv.inv H)).transpose := by
      ext h g
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
        Equiv.inv_apply, mul_inv_rev]
      rfl
    rw [e3, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hne

  let V := deg1 M (M.cusp ka)
  let V2 := deg1 M (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M)))
  let V1 : Submodule ℂ (Polynomial (HA M)) :=
    Submodule.span ℂ {p | ∃ x ∈ V, ∃ h : H, p = x * act h (Polynomial.C ut)}
  let e := deg1Equiv M (M.cusp ka) hVHA
  let e2 := deg1Equiv M _ h2HA
  haveI : Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (sOf M))) := hR.2.1
  haveI : FiniteDimensional ℂ V2 := LinearEquiv.finiteDimensional e2
  let ρ' : Representation ℂ U V :=
    { toFun := fun k => e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }
  have hρ' : ∀ g x, ((ρ' g x : V) : Polynomial (HA M)) = act g x := by
    intro g x
    obtain ⟨f, rfl⟩ := e.surjective x
    have e1 : ρ' g (e f) = e (ρ g f) := by simp [ρ']
    rw [e1, deg1Equiv_coe, deg1Equiv_coe, hactm]
    congr 1
    apply Subtype.ext
    funext c x
    have := hform g⁻¹ f c x
    rw [inv_inv] at this
    exact this
  have hV1 : ∀ h : H, ∀ x ∈ V, x * act h (Polynomial.C ut) ∈ V1 := fun h x hx => Submodule.subset_span ⟨x, hx, h, rfl⟩
  have hactV : ∀ (k : U), ∀ x ∈ V, act k x ∈ V := fun k x hx => by
    have := hρ' k ⟨x, hx⟩
    rw [← this]
    exact (ρ' k ⟨x, hx⟩).2
  have hV1s : ∀ h : H, ∀ x ∈ V1, act h x ∈ V1 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      refine Submodule.subset_span ⟨act h y, hactV h y hy, h * k, ?_⟩
      rw [map_mul, Subgroup.coe_mul, map_mul act]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx => rw [map_smul]; exact Submodule.smul_mem _ z hx
  have hV2 : ∀ h : H, ∀ x ∈ V1, x * act h (Polynomial.C ut) ∈ V2 := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, k, rfl⟩ := hp
      obtain ⟨f, hf, rfl⟩ := (mem_homogeneousExponentsOneBlock M _ y).1 hy
      rw [hact, hact, Polynomial.monomial_mul_C, Polynomial.monomial_mul_C]
      refine (mem_homogeneousExponentsOneBlock M _ _).2 ⟨_, ?_, rfl⟩
      exact mul_pb_mem_cusp M ka _ u0 hu0' _ _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul z x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ z hx
  obtain ⟨n, ⟨j, hj, hjeq⟩, hn⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant ℂ U (Polynomial (HA M)) act H (Polynomial.C ut) hnz V V1 V2 ρ' hρ' hV1
    hV1s hV2
  refine ⟨n, ⟨j ∘ₗ e.toLinearMap, hj.comp e.injective, fun h v i => ?_⟩, ?_⟩
  · have := hjeq h (e v) i
    have e1 : ρ' h (e v) = e (ρ h v) := by simp [ρ']
    rw [e1] at this
    exact this
  · rw [← e2.finrank_eq] at hn
    exact hn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAtInvertibleP
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem unitChartAt_of_mem_basicOpen_p : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X),
    x ∈ X.basicOpen (p : Γ(X, ⊤)) → UnitChartAt p Xw K x := by
  intro p _ X Xw K x hx
  obtain ⟨W', hW', hxW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  have hW'a : IsAffineOpen W' := hW'
  refine ⟨Γ(X, W'), inferInstance, hW'a.fromSpec, 1, inferInstance, ?_, ?_⟩
  · rw [hW'a.range_fromSpec]; exact hxW
  · intro φ _
    exfalso
    have hu : IsUnit ((p : ℕ) : Γ(X, W')) := by
      have := (X.toRingedSpace.isUnit_res_basicOpen (p : Γ(X, ⊤))).map
        (X.presheaf.map (homOfLE hWle).op).hom
      simp only [map_natCast] at this
      erw [map_natCast] at this
      exact this
    have h2 := hu.map φ
    rw [map_natCast] at h2
    exact GlobalTheory.PadicComplexHost.not_isUnit_p p h2

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsGoodLevel
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.UnramCM

theorem unramPts_of_cm : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) := by
  intro hP E _ _ _ H Dw l Xo c hpq hcase hg
  refine UnramPts.of_index_one fun Z w hw => ?_
  have hch : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal := by
    haveI := w.isMaximal
    haveI : Finite (𝓞 c.F ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    letI := Ideal.Quotient.field w.asIdeal
    refine ⟨ringChar (𝓞 c.F ⧸ w.asIdeal), CharP.char_is_prime (𝓞 c.F ⧸ w.asIdeal) _, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  obtain ⟨q, hq, hqw⟩ := hch
  have hqB : q ∉ badPrimes H l := fun h => hw q h hqw
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have h3 : 3 ≤ l.M' := le_trans l.three_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.dvd_lcm_left _ _))
  have hqd : ¬ q ∣ 2 * l.M' * H.d := fun h => hqB <| by
    have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) hD) hM
    rw [badPrimes, Nat.mem_primeFactors_of_ne_zero hne]
    refine ⟨hq, ?_⟩
    have : 2 * l.M' * H.d ∣ 2 * H.d * (discr E).natAbs * l.M' :=
      ⟨(discr E).natAbs, by ring⟩
    exact h.trans this
  obtain ⟨F', _, hdisc, hcurve⟩ := GlobalTheory.T.exists_field_unramified_curve hP E H l.M' q h3 hq hqd
  let K : IntermediateField ℚ ℂ := c.F ⊔ F'
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  have hle : c.F ≤ K := le_sup_left
  have hK : GlobalTheory.CompRat.CurveOver H K l.M' := fun τ hτ =>
    hcurve τ fun x hx => hτ x (le_sup_right (a := c.F) hx)
  obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.T.compositum_intermediateField_exists_place_valuation_eq c.F F' K hle rfl q hq hdisc w hqw
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field E H Dw l Xo c hpq hcase K hle hK Z
  exact GlobalTheory.T.exists_integralFramedPoint_completion_index_one E H Dw l Xo c hpq hg Z K y hy w 𝔭 h𝔭

end GlobalTheory.UnramCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRPowIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseChRig

theorem valR_map {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom s) = valR x U s := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => h (hV hq)
  unfold valR
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE x hV (homOfLE h).op]
  rfl

theorem valR_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : Γ(X, U)) :
    valR x (g ⁻¹ᵁ U) ((g.app U).hom s) = valR (x ≫ g) U s := by
  have hU' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := hU
  unfold valR
  rw [dif_pos hU, dif_pos hU', Scheme.Hom.comp_appLE]
  rfl

theorem valR_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valR (spMap f ≫ x) U s = f (valR x U s) := by
  have hU' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun q _ => hU (Set.mem_univ _)
  unfold valR
  rw [dif_pos hU, dif_pos hU']
  have e : (spMap f ≫ x).appLE U ⊤ hU' = x.appLE U ⊤ hU ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e]
  exact congrArg (fun φ => φ.hom ((x.appLE U ⊤ hU).hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s t : Γ(X, U)) : valR x U (s * t) = valR x U s * valR x U t := by
  unfold valR
  simp only [dif_pos hU, map_mul]

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) : valR x U (s ^ n) = valR x U s ^ n := by
  unfold valR
  simp only [dif_pos hU, map_pow]

theorem valR_gen {A : Type} [CommRing A] {X : Scheme.{0}} (L : LB X) (e : Sp A ⟶ X) (r : (L.pull e).Gen)
    (hr : r.IsGen) (j i : L.ι) (hj : ⊤ ≤ e ⁻¹ᵁ L.U j) (hi : ⊤ ≤ e ⁻¹ᵁ L.U i) :
    valR (𝟙 _) _ (r.s fun _ => j).val = valR e _ (L.g j i).val * valR (𝟙 _) _ (r.s fun _ => i).val := by
  have hB : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ ((L.pull e).U (fun _ => j) ⊓ (L.pull e).U (fun _ => i)) :=
    fun q hq => ⟨Set.mem_iInter.2 fun _ => hj hq, Set.mem_iInter.2 fun _ => hi hq⟩
  have h := congrArg (fun v => valR (𝟙 (Sp A)) _ (Units.val v)) (hr (fun _ => j) (fun _ => i))
  replace h := h.trans (valR_mul' _ hB _ _)
  refine (valR_map _ _ hB _).symm.trans (h.trans (congrArg₂ (· * ·) ?_ (valR_map _ _ hB _)))
  show valR _ _ (Units.val (∏ _k : PUnit, (res _ (pullU e _ (L.g j i))) ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (valR_map _ _ hB _).trans ((valR_app (𝟙 _) e (U := L.U j ⊓ L.U i) (fun q hq => ⟨hj hq, hi hq⟩) _).trans ?_)
  rw [Category.id_comp]

theorem valR_powIso {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X)
    (e : Sp A ⟶ X) (e' : Sp B ⟶ Y) (he : e' ≫ φ = spMap f ≫ e) (n : ℕ) (i : L.ι) (i' : PUnit → L.ι)
    (hj : ⊤ ≤ e ⁻¹ᵁ L.U (i' PUnit.unit)) (hi : ⊤ ≤ e ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ e' ⁻¹ᵁ (L.pull φ).U i') :
    valR e' _ ((BaseCh.powIso L φ n).s (fun _ => i', fun _ _ => i)).val =
      f (valR e _ (L.g (i' PUnit.unit) i).val) ^ n := by
  have h2 : ∀ q, φ (e' q) ∈ L.U i := fun q => by
    show (e' ≫ φ) q ∈ L.U i
    rw [he]; exact hi (Set.mem_univ _)
  have hB : ⊤ ≤ e' ⁻¹ᵁ (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).U (fun _ => i', fun _ _ => i) :=
    fun q hq => ⟨Set.mem_iInter.2 fun _ => hi' hq, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h2 q⟩
  show valR e' _ (Units.val (res (BaseCh.powIso_le L φ n (fun _ => i', fun _ _ => i))
      (pullU φ _ (L.g (i' PUnit.unit) i)) ^ (n : ℤ))) = _
  rw [zpow_natCast, Units.val_pow_eq_pow_val, valR_pow' _ hB]
  congr 1
  refine (valR_map _ _ hB _).trans ((valR_app e' φ (U := L.U (i' PUnit.unit) ⊓ L.U i)
    (fun q hq => BaseCh.powIso_le L φ n (fun _ => i', fun _ _ => i) (hB hq)) _).trans ?_)
  rw [he]
  exact valR_spMap f e (U := L.U (i' PUnit.unit) ⊓ L.U i) (fun q hq => ⟨hj hq, hi hq⟩) _

theorem powIso_rig : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (x : KeyIn K) (n : ℕ) (i : x.P.L.ι) (i' : (GlobalTheory.MBLow.BaseCh.key x f).P.L.ι), ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (eSec (GlobalTheory.MBLow.BaseCh.key x f).P.A) ⁻¹ᵁ (GlobalTheory.MBLow.BaseCh.key x f).P.L.U i' → valR (X := (GlobalTheory.MBLow.BaseCh.key x f).P.A.left) (eSec (GlobalTheory.MBLow.BaseCh.key x f).P.A) _ ((GlobalTheory.MBLow.BaseCh.powIso x.P.L (GlobalTheory.MBLow.BaseCh.prj x f) n).s (fun _ => i', fun _ _ => i)).val * f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val) ^ n = valR (X := Sp K') (𝟙 _) _ ((GlobalTheory.MBLow.BaseCh.key x f).rig.s fun _ => i').val ^ n := by
  intro K K' _ _ f x n i i' hi hi'
  have he := BaseCh.eSec_prj x f
  have hj : ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U (i' PUnit.unit) := by
    intro q _
    have h1 : (eSec (BaseCh.pol x f).A ≫ BaseCh.prj x f) (default : Sp K') ∈ x.P.L.U (i' PUnit.unit) :=
      Set.mem_iInter.1 (hi' (Set.mem_univ (default : Sp K'))) PUnit.unit
    rw [he] at h1
    have h2 : (q : Sp K) = spMap f (default : Sp K') := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [h2]
    exact h1
  have a := valR_powIso f x.P.L (BaseCh.prj x f) (eSec x.P.A) (eSec (BaseCh.pol x f).A) he n i i' hj hi hi'
  have b := valR_gen x.P.L (eSec x.P.A) x.rig x.rig_gen (i' PUnit.unit) i hj hi
  have hB : ⊤ ≤ (𝟙 (Sp K')) ⁻¹ᵁ ((BaseCh.pol x f).L.pull (eSec (BaseCh.pol x f).A)).U (fun _ => i') :=
    fun q hq => Set.mem_iInter.2 fun _ => hi' hq
  have hC : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ (x.P.L.pull (eSec x.P.A)).U (fun _ => i' PUnit.unit) :=
    fun q hq => Set.mem_iInter.2 fun _ => hj hq
  have c : valR (X := Sp K') (𝟙 _) _ ((BaseCh.key x f).rig.s fun _ => i').val =
      f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i' PUnit.unit).val) := by
    refine (valR_map (𝟙 (Sp K')) _ hB _).trans ((valR_app (𝟙 (Sp K')) (spMap f)
      (fun q _ => hC (Set.mem_univ _)) _).trans ?_)
    rw [Category.id_comp, ← Category.comp_id (spMap f)]
    exact valR_spMap f (𝟙 _) hC _
  rw [c]
  refine (congrArg (· * _) a).trans ?_
  rw [← mul_pow, ← map_mul]
  exact congrArg (fun t => f t ^ n) b.symm

end GlobalTheory.MBLow.BaseChRig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShiftStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_section_exponent_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ)
    (k : (E →+* ℂ) → ℕ) (a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ), e none = 0 →
    (∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ)) →
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∃ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      G.IsHomogeneous (∑ b, ∑ i, a b i) ∧
      ∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (s : Kˣ),
        (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : K) y₀ y' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := by
  first | exact @GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ | exact GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ | (intros; apply GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ <;> assumption)
end


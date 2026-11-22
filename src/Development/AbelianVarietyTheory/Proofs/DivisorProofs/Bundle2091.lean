import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0058
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0045
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0093
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CoefFnEqZeroOfNotPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0080
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.StrLeStrAddTwo
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentation
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.PullCocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem formula_span (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka))
    (a : U → C → ℂˣ)
    (ha : ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp ka) : C → M.dom → ℂ) c x =
        (a h c : ℂ) * M.pull h F c x.1)
    (h : U) (c : C) (x : M.dom) (g : C → M.dom → ℂ) (hg : g ∈ Submodule.span ℂ (M.res '' M.SS ka)) :
    ((ρ h⁻¹ ⟨g, hg⟩ : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * g (h • c) (Lmap M h c x) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact ha h F hF c x
  | zero =>
    show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _
    simp
  | add y z hy hz ihy ihz =>
    show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]
    simp [mul_add]
  | smul t y hy ih =>
    show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem rho_inv_rho (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (h : U)
    (f : M.cusp ka) : ρ h⁻¹ (ρ h f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem pull_mul_eq (M : TwoLevels E r U C) (f : C → M.dom → ℂ) (hf : IsInv M f) (g h : U) (c : C) (x : M.dom) :
    f ((h * g) • c) (Lmap M (h * g) c x) = f (h • g • c) (Lmap M h (g • c) (Lmap M g c x)) := by
  set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef
  have hγ : γ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1 := by
    show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c),
      ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]
  have hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom := e ▸ (Lmap M (h * g) c x).2
  have := hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx
  have e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x := Subtype.ext e
  rw [e2] at this
  rw [this, mul_smul]

theorem exists_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  intro E _ _ _ r U C _ _ M ka ρ hρ hinv
  obtain ⟨a, ha⟩ := hρ
  have hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
    rintro h ⟨g, hg⟩ c x
    exact formula_span M ka ρ a ha h c x g hg
  classical
  let C0 : C → Prop := fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0
  have hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c) := by
    rintro h c ⟨f, x, hfx⟩
    refine ⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩
    calc (f : C → M.dom → ℂ) c x = ((ρ h⁻¹ (ρ h f) : M.cusp ka) : C → M.dom → ℂ) c x := by
          rw [rho_inv_rho]
      _ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x
      _ = 0 := by rw [h0, mul_zero]
  have hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c) := fun h c hc h1 => hc (by
    have := hstab h⁻¹ (h • c) h1
    rwa [inv_smul_smul] at this)
  have hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka),
      (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) =
        (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) := by
    intro g h c x f
    have L := hform (h * g) f c x
    have R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x =
        (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x))) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]
    rw [← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]
    ring
  refine ⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩
  · intro g h c
    by_cases hc : C0 c
    · have hgc : C0 (g • c) := hstab g c hc
      have hhgc : C0 ((h * g) • c) := hstab (h * g) c hc
      simp only [hc, hgc, if_true]
      obtain ⟨f', x, hfx⟩ := hc
      set f := ρ (h * g) f' with hfdef
      have hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0 := by
        intro h0
        apply hfx
        calc (f' : C → M.dom → ℂ) c x = ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x := by
              rw [hfdef, rho_inv_rho]
          _ = 0 := by rw [hform, h0, mul_zero]
      ext
      push_cast
      exact mul_right_cancel₀ hV (hcoc g h c x f)
    · have hgc : ¬ C0 (g • c) := hstab' g c hc
      simp [hc, hgc]
  · intro h f c x
    by_cases hc : C0 c
    · simp only [hc, if_true]
      exact hform h f c x
    · have hhc : ¬ C0 (h • c) := hstab' h c hc
      simp only [hc, if_false, Units.val_one, one_mul]
      have l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0 := by
        by_contra hne
        exact hc ⟨ρ h⁻¹ f, x, hne⟩
      have r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0 := by
        by_contra hne
        exact hhc ⟨f, _, hne⟩
      rw [l0, r0]

end GlobalTheory.PullCocycle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtension
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan

theorem finite_of_finRes {T₀ T : CDVR} (hT : T.FinRes) (g : T₀.V →+* T.V) (hg : Function.Injective g)
    [IsLocalHom g] : g.Finite := by
  letI := g.toAlgebra
  haveI : Finite (T.V ⧸ maximalIdeal T.V) := hT
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  refine GlobalTheory.finite_of_forall_prime_mem (R := T₀.V) (B := T.V) hp.ne_zero (fun P hP h0 => ?_) ?_ ?_
  · rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hp.not_isUnit
  · exact fun h => IsDiscreteValuationRing.not_a_field _ ((Ideal.map_eq_bot_iff_of_injective hg).1 h)
  · exact ne_top_of_le_ne_top (maximalIdeal.isMaximal T.V).ne_top (map_maximalIdeal_le g)

theorem exists_common_extension {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T T' : CDVR}
    (hT' : T'.FinRes) {j : K →+* T.Fr} {j' : K →+* T'.Fr} {e e' : ℕ} (ho : OverLa la T.V j e)
    (ho' : OverLa la T'.V j' e') :
    ∃ (W : CDVR) (i : T.Fr →+* W.Fr) (i' : T'.Fr →+* W.Fr) (r r' : ℕ), 0 < r ∧ 0 < r' ∧ r * e = r' * e' ∧
      (∀ x, vV W.V (i x) = (r : ℤ) * vV T.V x) ∧ (∀ x, vV W.V (i' x) = (r' : ℤ) * vV T'.V x) ∧
      ∀ a, i' (j' a) = i (j a) := by
  obtain ⟨T₀, j₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K la
  obtain ⟨g, χ, -, h₁, h₂, -⟩ := hini T j e ho
  obtain ⟨g', χ', hl, h₁', h₂', -⟩ := hini T' j' e' ho'
  replace h₂ := RingHom.congr_fun h₂
  replace h₂' := RingHom.congr_fun h₂'
  simp only [RingHom.comp_apply] at h₂ h₂'
  obtain ⟨s, hs, -, hv, -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho₀ ho' χ' (RingHom.congr_fun h₁')
    fun a => ⟨_, (h₂' a).symm⟩
  have hg' : g'.Finite := finite_of_finRes hT' g' fun a b h => IsFractionRing.injective T₀.V T₀.Fr
    (χ'.injective (by rw [h₂', h₂', h]))
  letI := χ.toAlgebra
  letI := χ'.toAlgebra
  haveI : Module.Finite T₀.Fr T'.Fr := GlobalTheory.AlgLawsCompare.finite_of_finite_residueField χ' hs hv hT'
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (T.Fr ⊗[T₀.Fr] T'.Fr)
  letI := Ideal.Quotient.field m
  obtain ⟨W, i, r, ψ, α, hr, hi, hψ, hα, -⟩ :=
    GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T ((T.Fr ⊗[T₀.Fr] T'.Fr) ⧸ m)
  let i' : T'.Fr →+* W.Fr := ψ.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight : T'.Fr →ₐ[T₀.Fr] T.Fr ⊗[T₀.Fr] T'.Fr).toRingHom)
  have hc : ∀ a, i' (χ' a) = i (χ a) := fun a => by
    rw [← hψ]
    refine congrArg ψ (congrArg (Ideal.Quotient.mk m) ?_)
    exact (Algebra.TensorProduct.includeRight : T'.Fr →ₐ[T₀.Fr] T.Fr ⊗[T₀.Fr] T'.Fr).commutes a
  have hc' : ∀ a, i' (j' a) = i (j a) := fun a => by
    rw [← h₁, ← h₁']
    exact hc _
  obtain ⟨r', hr', he, hi', -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho' (ho.bc i hr hi) i' hc' fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := W.V) (K := W.Fr) (by
      letI := g'.toAlgebra
      exact IsIntegral.map_of_comp_eq (α.comp g) (i'.comp (algebraMap T'.V T'.Fr)) (RingHom.ext fun b => by
        show algebraMap W.V W.Fr (α (g b)) = i' (algebraMap T'.V T'.Fr (g' b))
        rw [hα, ← h₂, ← h₂', hc]) (hg'.to_isIntegral a))
  exact ⟨W, i, i', r, r', hr, hr', he, hi, hi', hc'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K}
  {v : FinitePlace K}

theorem FinFr.exists_baseChange (F : FinFr y v) {W : CDVR} (i : F.T.Fr →+* W.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV W.V (i x) = (r : ℤ) * vV F.T.V x) (io : c.F →+* W.Fr) (φ : CoefHom c io K)
    (hφ : ∀ a, i (F.φ a) = φ a) : ∃ z : IntFr Xo c W io, letI := io.toAlgebra
      Reframes φ y (fun k => Units.map (i : F.T.Fr →* W.Fr) (F.t k)) z.1 := by
  obtain rfl : i.comp F.io = io := RingHom.ext fun a => by
    letI := io.toAlgebra
    exact (congrArg i (F.φ.commutes a).symm).trans ((hφ _).trans (φ.commutes a))
  letI := (i.comp F.io).toAlgebra
  obtain ⟨z, ψ, hψ, hz⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c F.T W F.io F.pt i r hr
    fun a _ => hi a
  obtain rfl : ψ = ⟨i, fun _ => rfl⟩ := AlgHom.ext (RingHom.congr_fun hψ)
  obtain ⟨w, h₁, h₂⟩ := F.tri
  obtain ⟨w', hw'⟩ := exists_frMap (⟨i, fun _ => rfl⟩ : F.T.Fr →ₐ[c.F] W.Fr) w
  exact ⟨z, w', frMap_comp h₁ hw' hφ, GlobalTheory.SupGeneric.frBor_of_frMap _ h₂ hw' hz⟩

theorem FinFr.abs_t_eq (F F' : FinFr y v) (k : Ix Dw) : F.abs (F.t k) = F'.abs (F'.t k) := by
  obtain ⟨W, i, i', r, r', hr, hr', he, hi, hi', hc⟩ := exists_common_extension F'.fin F.lies F'.lies
  letI := (i.comp F.io).toAlgebra
  let φ : K →ₐ[c.F] W.Fr := ⟨i.comp F.φ.toRingHom, fun a => congrArg i (F.φ.commutes a)⟩
  obtain ⟨z, w, h₁, h₂⟩ := F.exists_baseChange i hr hi (i.comp F.io) φ fun _ => rfl
  obtain ⟨z', w', h₁', h₂'⟩ := F'.exists_baseChange i' hr' hi' (i.comp F.io) φ hc
  obtain rfl := frMap_unique h₁ h₁'
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c W.Fr
  have hu := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).2.1 W _ z z' _ (hmul _ _ _ _ _ (hinv _ _ _ h₂) h₂') k
  have h0 : i (F.t k) ≠ 0 := (map_ne_zero i).2 (F.t k).ne_zero
  have h0' : i' (F'.t k) ≠ 0 := (map_ne_zero i').2 (F'.t k).ne_zero
  have hv : valV W.V (i (F.t k)) = valV W.V (i' (F'.t k)) := by
    refine (inv_mul_eq_one₀ (valV_ne_zero h0)).1 ?_
    simpa using hu
  rw [FinFr.abs_apply, FinFr.abs_apply, ← nval_bc i hr hi, ← nval_bc i' hr' hi', nval_of_ne h0, nval_of_ne h0', vV, vV,
    hv, he]

theorem FinFr.fac_indep (F F' : FinFr y v) (e : Ix Dw → ℤ) : F.fac e = F'.fac e := by
  simp only [FinFr.fac, Units.coe_prod, Units.val_zpow_eq_zpow_val, map_prod, map_zpow₀, F.abs_t_eq F']

theorem FinFr.nrm_indep (F F' : FinFr y v) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    F.nrm f = F'.nrm f := by
  rw [F.nrm_eq hf, F'.nrm_eq hf, F.fac_indep F']

theorem FinFr.fac_nrm_indep (F F' : FinFr y v) (e : Ix Dw → ℤ) :
    F.fac e = F'.fac e ∧ ∀ f ∈ secZ Xo c e, F.nrm f = F'.nrm f :=
  ⟨F.fac_indep F' e, fun _ => F.nrm_indep F'⟩

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPower
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.RuleIntegral

theorem vLa_int_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K}
    (hr : (r : K) ≠ 0) : 0 ≤ vLa w (r : K) := by
  unfold vLa
  have h1 := w.valuation_le_one (K := K) r
  have h2 : (w.valuation K) (r : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

theorem nonneg_of_four {x : EReal} (hx : x ≠ ⊥) (h : 0 ≤ x + x + x + x) : 0 ≤ x := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe r =>
    have : (0 : EReal) ≤ ((r + r + r + r : ℝ) : EReal) := by simpa [EReal.coe_add] using h
    have h' : (0 : ℝ) ≤ r + r + r + r := EReal.coe_nonneg.1 this
    exact EReal.coe_nonneg.2 (by linarith)

theorem eq_zero_or_top_of_double {x : EReal} (hx : x ≠ ⊥) (h : x = x + x) : x = 0 ∨ x = ⊤ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact Or.inr rfl
  | coe r =>
    left
    have h' : r = r + r := by exact_mod_cast h
    have : r = 0 := by linarith
    simp [this]

theorem exists_common_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (a : ι → K) :
    ∃ s : 𝓞 K, (s : K) ≠ 0 ∧ ∀ i, ∃ r : 𝓞 K, (r : K) = (s : K) * a i := by
  classical
  have h := fun i => IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) (a i)
  choose d hd using h
  refine ⟨∏ i, (d i : 𝓞 K), ?_, fun i => ?_⟩
  · have hm : (∏ i, (d i : 𝓞 K)) ∈ nonZeroDivisors (𝓞 K) :=
      Submonoid.prod_mem _ fun i _ => (d i).2
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
  · obtain ⟨r, hr⟩ := hd i
    refine ⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 K)) * r, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 K)) (Finset.mem_univ i)]
    have e1 : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
    rw [e1, e1, map_mul, map_mul, hr, Algebra.smul_def]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_idem_zero {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) w) : ∃ Z, v (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨y, rfl⟩ := hv
  have h1 : vAtV y 1 = 0 := by
    rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
    show nval T.V e (evI y 1) = 0
    have h1 : evI y 1 = 1 := by
      letI := io.toAlgebra
      exact evalAt_one _ _ y.1 y.2.1
    rw [h1, nval_of_ne one_ne_zero]
    simp [vV]
  by_contra hne
  push_neg at hne
  have htop : ∀ Z, vAtV y (GlobalTheory.FlatLine.idem Z) = ⊤ := fun Z => by
    have hd := vAtV_mul y (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)
    rw [GlobalTheory.FlatLine.idem_mul_idem] at hd
    exact (eq_zero_or_top_of_double (vAtV_ne_bot y _) hd).resolve_left (hne Z)
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  classical
  have hs : ∀ s : Finset (Comp Xo c), vAtV y (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z) = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using vAtV_zero y
    | insert Z s hZ ih =>
      rw [Finset.sum_insert hZ]
      have := vAtV_add y (GlobalTheory.FlatLine.idem Z) (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z)
      rw [htop Z, ih, min_self] at this
      exact top_le_iff.1 this
  have h2 := hs Finset.univ
  rw [GlobalTheory.FlatLine.sum_idem] at h2
  rw [h2] at h1
  exact EReal.top_ne_zero h1

theorem exists_smul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  intro E _ _ _ H Dw l Xo c K ρ a ha hρ hK
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  obtain ⟨s, hs0, hsa⟩ := exists_common_denom a
  refine ⟨(s : c.F), hs0, fun w v hv => ?_⟩
  have hKv := hK w v hv
  obtain ⟨Z, hZ⟩ := exists_idem_zero hv
  obtain ⟨y, rfl⟩ := hv
  obtain ⟨r, hr⟩ := hsa Z
  have hb : (((s ^ 3 * r : 𝓞 c.F)) : c.F) = (s : c.F) ^ 4 * a Z := by
    have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F s * a Z := hr
    show algebraMap (𝓞 c.F) c.F (s ^ 3 * r) = (algebraMap (𝓞 c.F) c.F s) ^ 4 * a Z
    rw [map_mul, map_pow, hr']; ring
  have hb0 : (((s ^ 3 * r : 𝓞 c.F)) : c.F) ≠ 0 := by
    rw [hb]; exact mul_ne_zero (pow_ne_zero _ hs0) (ha Z)
  have hid : GlobalTheory.FlatLine.idem Z * ((s : c.F) • ρ) ^ 4 =
      (((s ^ 3 * r : 𝓞 c.F)) : c.F) • (GlobalTheory.FlatLine.idem Z * K) := by
    rw [smul_pow, mul_smul_comm, hρ Z, smul_smul, hb]
  have h4 : ∀ x : Rul Xo c, x ^ 4 = x * x * x * x := fun x => by ring
  have e := congrArg (vAtV y) hid
  rw [h4, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_smul _ _ _ hb0, vAtV_mul, hZ, zero_add, zero_add] at e
  refine nonneg_of_four (vAtV_ne_bot _ _) ?_
  rw [e]
  refine add_nonneg ?_ hKv
  exact EReal.coe_nonneg.2 (by exact_mod_cast vLa_int_nonneg w hb0)

end GlobalTheory.RuleIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ReadingSec
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem castFrame_mem_GG {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) :
    castFrame hΨ x ∈ GG Ψ' G p0 ↔ x ∈ GG Ψ G p0 := by
  subst hΨ; rfl

variable {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
  [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
  {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}

theorem psi_eq (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (c : C) :
    M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ := by
  rw [← ha c]; exact (M.comp_Ψ c).symm

def rdFun (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) : C → Frame M.Ψ D.R.r → ℂ :=
  fun c x => rdR (h.laws v).p ((i : ℕ) + 1) F (e c) (castFrame (psi_eq ha c) x)

theorem mem_dom_iff (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (c : C) (x : Frame M.Ψ D.R.r) :
    castFrame (psi_eq ha c) x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom ↔ x ∈ M.dom := by
  have hG : (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Gm = M.Gm := by
    rw [← ha c]; exact M.comp_Gm c
  have hp : (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).p0 = M.p0 := by
    rw [← ha c]; exact M.comp_basePoint c
  show castFrame (psi_eq ha c) x ∈ GG _ _ _ ↔ x ∈ GG _ _ _
  rw [hG, hp, castFrame_mem_GG]

end ReadingSec

section ReadingSec2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
variable {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
  [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
  {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}

def rdLin (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) :
    (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] (C → M.dom → ℂ) where
  toFun F := M.res (rdFun h ha F)
  map_add' F G := by
    funext c x
    simp only [TwoLevels.res, rdFun, rdR, Pi.add_apply, Submodule.coe_add, map_add]
  map_smul' a F := by
    funext c x
    simp only [TwoLevels.res, rdFun, rdR, Pi.smul_apply, Submodule.coe_smul, map_smulₛₗ, smul_eq_mul]

theorem rdLin_apply (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (c : C) (x : M.dom) :
    rdLin h ha F c x = rdFun h ha F c x.1 := rfl

end ReadingSec2

section LP
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lastPos_kappa (p : PtAt ex Csz) (i : Fin D.R.m) : (p.κ i).LastPos := by
  intro τ k hk
  rw [(p.fw.kap i τ).1 k, Formalism.IndefR.Fock.KV.sig_Wc i τ]
  have e1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ); omega
  have e2 : D.R.k + (i : ℕ) - 1 = (k : ℕ) := by omega
  have h0 := GlobalTheory.PtStringTest.aPl_last_pos i τ
  rw [e2, ← e1] at h0
  exact h0
end LP

theorem exists_ext_embedding {K LL : Type} [Field K] [NumberField K] [Field LL] [NumberField LL] [Algebra K LL]
    (σ₀ : K →+* ℂ) : ∃ σ : LL →+* ℂ, ∀ a, σ (algebraMap K LL a) = σ₀ a := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  haveI : Algebra.IsAlgebraic K LL := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  exact ⟨(IsAlgClosed.lift : LL →ₐ[K] ℂ).toRingHom, fun a => (IsAlgClosed.lift : LL →ₐ[K] ℂ).commutes a⟩

section Card
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem card_of_runModel {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {h : RunsOk (fw2 p) r} {i : Fin D.R.m} {C : Type}
    [Finite C] [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r}
    (hM : RunModel p r h i M ka) : M.Ψ.card = D.R.f := by
  obtain ⟨v, e, -⟩ := hM
  obtain ⟨k⟩ : Nonempty ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp :=
    ⟨((r.used v).full.dict ((i : ℕ) + 1) (r.used v).full.σ₀ 1).1⟩
  have h2 := Formalism.L2.Pj.DatLin.two_card (M.comp (e.symm k)).cmType
  rw [M.comp_Ψ, Formalism.L2.S.Pv.MSTypP.finrank_hostE' D] at h2
  omega

end Card

end GlobalTheory.ShareOn.Reading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPairStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittaker_character_pair : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.Rows → ∃ (lam : (p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom) →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), GlobalTheory.BadCount.IsWhit D _ lam ψ ∧ (∀ (g : p.P.P0) (h : (p.R.eG.trans p.cG) g ∈ p.P.P0.map (p.R.eG.trans p.cG).toMonoidHom), ((lam ⟨_, h⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((p.P.ψ0⁻¹ g : D.what₂.LLˣ) : D.what₂.LL)) ∧ HalfUnip p p.P.P0 := by
  first | exact @GlobalTheory.ShareOn.baseLevel_isWhit | exact GlobalTheory.ShareOn.baseLevel_isWhit | (intros; apply GlobalTheory.ShareOn.baseLevel_isWhit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimePowerLatticeInclusionOfLocalModelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePowerLatticeInclusion_of_localModels : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  first | exact @GlobalTheory.ExpTie.lIncl_of_models | exact GlobalTheory.ExpTie.lIncl_of_models | (intros; apply GlobalTheory.ExpTie.lIncl_of_models <;> assumption)
end


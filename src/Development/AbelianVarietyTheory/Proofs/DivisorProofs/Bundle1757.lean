import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOne
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.MuLattice

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}

def muMap (hε : IsPrimitiveSystem ε) (a : Ainf p O) : TDual (PDivGroup.mu p O) where
  toFun t := ofPadic p O ((epsEquiv hε).symm t) * a
  map_add' s t := by rw [map_add, map_add, add_mul]
  map_smul' c t := by
    rw [map_smul, smul_eq_mul, map_mul, mul_assoc]; rfl

theorem muMap_apply (hε : IsPrimitiveSystem ε) (a : Ainf p O) (t) :
    muMap hε a t = ofPadic p O ((epsEquiv hε).symm t) * a := rfl

theorem epsEquiv_symm_eps (hε : IsPrimitiveSystem ε) : (epsEquiv hε).symm (epsTate hε) = 1 := by
  rw [LinearEquiv.symm_apply_eq]
  exact (one_smul ℤ_[p] (epsTate hε)).symm

theorem muMap_mem (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : muMap hε (Sandwich.mu ε * a) ∈ latt (PDivGroup.mu p O) := fun n =>
  ⟨0, fun t => by
    rw [muMap_apply, ghost_mul, ghost_mul, hμ, zero_mul, mul_zero, LinearMap.zero_apply]⟩

def toLatt (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0) :
    Ainf p O →ₗ[Ainf p O] latt (PDivGroup.mu p O) where
  toFun a := ⟨muMap hε (Sandwich.mu ε * a), muMap_mem hε hμ a⟩
  map_add' a b := by
    ext t
    simp only [muMap_apply, Submodule.coe_add, LinearMap.add_apply]
    ring_nf
  map_smul' c a := by
    ext t
    simp only [muMap_apply, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

theorem toLatt_eps (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : (toLatt hε hμ a).1 (epsTate hε) = Sandwich.mu ε * a := by
  change ofPadic p O ((epsEquiv hε).symm (epsTate hε)) * _ = _
  rw [epsEquiv_symm_eps, map_one, one_mul]

theorem latt_mu_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  have hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0 :=
    (GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε).2.2.1
  have hdom := GlobalTheory.ainf_isDomain_and_mu_ne_zero p C v O hv ε (by simpa [zeta] using hε 1)
  haveI := hdom.1
  have hbij : Function.Bijective (toLatt hε hμ) := by
    constructor
    · intro a b hab
      have h := congrArg (fun y : latt (PDivGroup.mu p O) => y.1 (epsTate hε)) hab
      simp only [toLatt_eps] at h
      exact mul_left_cancel₀ hdom.2 h
    · intro y
      have hg : ∀ n, ghost p O n (y.1 (epsTate hε)) = 0 := fun n => by
        obtain ⟨x, hx⟩ := y.2 n
        rw [hx, Subsingleton.elim (hodgeTate (PDivGroup.mu p O) (epsTate hε)) 0, map_zero]
      obtain ⟨a, ha⟩ := GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ hg
      refine ⟨a, Subtype.ext (LinearMap.ext fun t => ?_)⟩
      obtain ⟨c, rfl⟩ := (epsEquiv hε).surjective t
      change ofPadic p O ((epsEquiv hε).symm (epsEquiv hε c)) * (Sandwich.mu ε * a) = y.1 (epsEquiv hε c)
      rw [LinearEquiv.symm_apply_apply, ← ha]
      have hc : epsEquiv hε c = c • epsTate hε := rfl
      rw [hc, LinearMap.map_smulₛₗ, smul_eq_mul]
  refine ⟨(LinearEquiv.ofBijective _ hbij).symm, fun y => ?_⟩
  have h := toLatt_eps hε hμ ((LinearEquiv.ofBijective _ hbij).symm y)
  rw [← h]
  congr 2
  exact (LinearEquiv.ofBijective _ hbij).apply_symm_apply y

end GlobalTheory.MuLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open GlobalTheory.CxForm

variable {n : ℕ}

theorem delAt_pull_comp {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) {β : V n → Alt n}
    (hβ : ∀ S, DifferentiableAt ℝ (fun u => (bas n).repr (β u) S) (φ v)) :
    delAt (fun w => pull (fderiv ℂ φ w) (β (φ w))) v = pull (fderiv ℂ φ v) (delAt β (φ v)) := by
  have hφ1 : DifferentiableAt ℂ φ v := hφ.differentiableAt two_ne_zero
  have e : (fun w => pull (fderiv ℂ φ w) (β (φ w))) =
      fun w => ∑ T, (bas n).repr (β (φ w)) T • pull (fderiv ℂ φ w) (bas n T) := funext fun w => by
    conv_lhs => rw [← (bas n).sum_repr (β (φ w))]
    simp only [map_sum, map_smul]
  rw [e, GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz (fun T w => (bas n).repr (β (φ w)) T) (fun T w => pull (fderiv ℂ φ w) (bas n T))
    (fun T => (hβ T).comp v (hφ1.restrictScalars ℝ)) (fun T S => GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv hφ (bas n T) S)]
  simp only [GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero hφ, smul_zero, add_zero]
  rw [delAt_eq_sum_dOne β (φ v), map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_mul, GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic (c := fun u => (bas n).repr (β u) T) (hβ T) hφ1]

variable {M : Type} [TopologicalSpace M] {A : HolAtlas M n}

theorem del_compat {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.del α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.del α x') := by
  set φ : V n → V n := x'.ch ∘ x.ch.symm with hφdef
  have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hv : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  have hφ : ContDiffAt ℂ 2 φ x.crd := by
    have hd : DifferentiableOn ℂ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := A.holo x.1.1 x'.1.1
    have hs : ContDiffOn ℂ ∞ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := (contDiffOn_piLp 2).2 fun c =>
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hW
        ((EuclideanSpace.proj c : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hd)
    exact (hs.contDiffAt (hW.mem_nhds hv)).of_le (WithTop.coe_le_coe.2 le_top)
  have hφv : φ x.crd = x'.crd := by simp only [hφdef, Function.comp_apply, x.ch.left_inv x.2, h]
  have hloc : A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun w => pull (fderiv ℂ φ w) (A.loc α x'.1.1 (φ w)) := by
    filter_upwards [hW.mem_nhds hv] with w hw
    let p : A.Pt := ⟨(x.1.1, x.ch.symm w), x.ch.map_target hw.1⟩
    let p' : A.Pt := ⟨(x'.1.1, x.ch.symm w), hw.2⟩
    have hc := hα.compat p p' rfl
    have hp : p.crd = w := x.ch.right_inv hw.1
    rw [HolAtlas.loc, dif_pos hw.1]
    refine hc.trans ?_
    rw [hp, ← A.loc_crd α p']
    rfl
  show delAt (A.loc α x.1.1) x.crd = pull (fderiv ℂ φ x.crd) (delAt (A.loc α x'.1.1) x'.crd)
  rw [delAt_congr hloc, delAt_pull_comp hφ (fun S => hφv ▸ FormMul.differentiableAt_coef hα x' S), hφv]

theorem isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld),
    A.IsForm α → A.IsForm (A.del α) :=
  fun A α hα => ⟨GlobalTheory.T.del_loc_repr_contDiffOn_target A α hα, fun x x' h => del_compat hα x x' h⟩

end GlobalTheory.CxForm.DelForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDom
section
namespace GlobalTheory.FlatPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem holAlg_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  intro E _ _ _ r X hne
  obtain ⟨y0, hy0⟩ := hne
  haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩
    simp at this⟩⟩
  haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨F, hF, hFa⟩ := a.2
    obtain ⟨G, hG, hGb⟩ := b.2
    have ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (Subtype.ext (funext h))
    obtain ⟨y, hy⟩ := ha'
    have hfg : ∀ w ∈ X.dom, F w * G w = 0 := by
      intro w hw
      have := congrFun (congrArg Subtype.val hab) ⟨w, hw⟩
      rw [← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]
      simpa using this
    have hFy : F y.1 ≠ 0 := by rw [← hFa y]; exact hy
    have key := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy
    apply hb
    apply Subtype.ext
    funext z
    rw [hGb z]
    simpa using key z.1 z.2⟩
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FlatPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbedding
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false
namespace GlobalTheory.ConjHostChar

theorem embK_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ (H.bar a) = embK c (conjEmb τ) a := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, conjEmb, RingHom.comp_apply]
  rw [← ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  simp

theorem conj_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ a, ((t.comp (H.bar : 𝓞 E →+* 𝓞 E) a : 𝓞 K) : K) = algebraMap c.F K (embK c (conjEmb τ.1) a) := by
  intro E _ _ _ H Dw l Xo c τ K _ _ _ t ht a
  rw [RingHom.comp_apply, ht]
  exact congrArg _ (embK_bar H c τ.1 a)

end GlobalTheory.ConjHostChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceId
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedIdeleBasePlace

theorem ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 →
      ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hL t v e he hv i j hU
  subst hv
  have hw : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ G.pl.v0 e he hU _ hw
  exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j
    ((GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) _).1 h1)

end GlobalTheory.RamifiedIdeleBasePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterTrivialOnCongruence
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeckeSignLevel

theorem sign_char_trivial_on_congruence : ∀ (F : Type) [Field F] [NumberField F] (φ : (AdeleRing (𝓞 F) F)ˣ →* Circle),
    Continuous φ → (∀ b, φ b = 1 ∨ φ b = -1) → (∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → φ b = 1) →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (b : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      φ b = 1 := by
  intro F _ _ φ hφ hpm hinf
  classical

  have hK : {u : (AdeleRing (𝓞 F) F)ˣ | φ u = 1} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
    have hopen : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
    have h1 : φ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) :=
      hφ.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp [map_one]))
    refine Filter.mem_of_superset h1 fun u hu => ?_
    rcases hpm u with h | h
    · exact h
    · exfalso
      have : (0 : ℝ) < ((φ u : Circle) : ℂ).re := hu
      rw [h] at this
      norm_num at this
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hK
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hK
  let g : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F →
      AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    fun p => (((1 : InfiniteAdeleRing F), 1 + p.1), MulOpposite.op ((1 : InfiniteAdeleRing F), 1 + p.2))
  have hg : Continuous g :=
    (continuous_const.prodMk (continuous_const.add continuous_fst)).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.prodMk (continuous_const.add continuous_snd)))
  have hg0 : g (0, 0) = Units.embedProduct _ 1 := by
    rw [map_one]
    simp [g]
    rfl
  have h1 : g ⁻¹' t ∈ 𝓝 ((0, 0) : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact ht)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨N, hN, hNuv⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (u ∩ v) (Filter.inter_mem hu hv)
  refine ⟨N, hN, fun n hn hdvd b hb hb' => ?_⟩
  obtain ⟨q, rfl⟩ := hdvd
  obtain ⟨s, hs, hbs⟩ := hb
  obtain ⟨s', hs', hbs'⟩ := hb'

  have hint : ∀ x ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ∀ w : HeightOneSpectrum (𝓞 F),
      ((q : FiniteAdeleRing (𝓞 F) F) * x) w ∈ w.adicCompletionIntegers F := by
    intro x hx w
    have hxw : x w ∈ w.adicCompletionIntegers F := hx w
    have : ((q : FiniteAdeleRing (𝓞 F) F) * x) w = (q : w.adicCompletion F) * x w := by
      rfl
    rw [this]
    exact mul_mem (natCast_mem _ q) hxw
  have key : ∀ x ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * x) ∈ u ∩ v := by
    intro x hx
    have e : ((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * x = N • ((q : FiniteAdeleRing (𝓞 F) F) * x) := by
      rw [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
    rw [e]
    exact hNuv _ (hint x hx)

  have hinv : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
    have h := congrArg Prod.snd b.mul_inv
    exact h
  have hinv' : ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 := by
    have h := congrArg Prod.snd b.inv_mul
    exact h
  let bf : (AdeleRing (𝓞 F) F)ˣ :=
    { val := ((1 : InfiniteAdeleRing F), (b : AdeleRing (𝓞 F) F).2)
      inv := ((1 : InfiniteAdeleRing F), ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2)
      val_inv := Prod.ext (mul_one _) hinv
      inv_val := Prod.ext (mul_one _) hinv' }
  have hbf : φ bf = 1 := by
    have hmem : Units.embedProduct _ bf ∈ t := by
      have : Units.embedProduct _ bf = g (((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * s,
          ((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * s') := by
        show (((1 : InfiniteAdeleRing F), (b : AdeleRing (𝓞 F) F).2),
          MulOpposite.op ((1 : InfiniteAdeleRing F), ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2)) = _
        rw [hbs, hbs']
        rfl
      rw [this]
      exact huv ⟨(key s hs).1, (key s' hs').2⟩
    exact hts hmem
  have hrest : φ (b * bf⁻¹) = 1 := by
    apply hinf
    show (b : AdeleRing (𝓞 F) F).2 * ((bf⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
    exact hinv
  have : b = (b * bf⁻¹) * bf := by group
  rw [this, map_mul, hrest, hbf, one_mul]

end GlobalTheory.HeckeSignLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.ClassCover

variable {L : Type} [Field L] [NumberField L]

def toIdeles : (FiniteAdeleRing (𝓞 L) L)ˣ →* Neutral.B1.Ideles L :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem eq_diag_mul_of_classOf (y : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles y) = 1) :
    ∃ (k : Lˣ) (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((u : FiniteAdeleRing (𝓞 L) L) P) = 1) ∧
      y = Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom k * u := by
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 L) L).2, ((u⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2, ?_, ?_⟩,
    fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((toIdeles y : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 =
        ((Neutral.B1.diagUnits L k * u : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 := by rw [he]
    exact h2

theorem eq_ratId_mul_of_classOf (ι : AfE ℚ L ≃+* FiniteAdeleRing (𝓞 L) L) (hι : GlobalTheory.TwU.IsAdIso ι) (x : (AfE ℚ L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles (Units.map ι.toRingHom.toMonoidHom x)) = 1) :
    ∃ (a : Lˣ) (k : (AfE ℚ L)ˣ), k ∈ intU ℚ L ∧ x = ratId ℚ L a * k := by
  obtain ⟨h1, h2⟩ := hι
  obtain ⟨a, u, hu, he⟩ := eq_diag_mul_of_classOf _ hc
  have hinv : ∀ P : HeightOneSpectrum (𝓞 L), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) P) * ((u : FiniteAdeleRing (𝓞 L) L) P) = 1 := by
      exact congrArg (fun t : FiniteAdeleRing (𝓞 L) L => t P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩
  · rw [intU, Submonoid.mem_units_iff]
    constructor
    · show ι.symm (u : FiniteAdeleRing (𝓞 L) L) ∈ RInt ℚ L
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hu P]
    · show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) ∈ RInt ℚ L
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hinv P]
  · apply Units.ext
    apply ι.injective
    have e := congrArg (fun t : (FiniteAdeleRing (𝓞 L) L)ˣ => (t : FiniteAdeleRing (𝓞 L) L)) he
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    rw [e, Units.val_mul, map_mul]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    congr 1
    rw [ratId, Units.coe_map]
    show _ = ι (inclE (F := ℚ) (E := L) (FiniteAdeleRing (𝓞 ℚ) ℚ) (a : L))
    rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]

theorem exists_finset_cover : ∀ (L : Type) [Field L] [NumberField L],
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ x : (AfE ℚ L)ˣ, ∃ s ∈ S, ∃ a : Lˣ, ∃ k ∈ intU ℚ L, x = s * ratId ℚ L a * k := by
  intro L _ _
  classical
  obtain ⟨ι, hι⟩ := GlobalTheory.TwU.exists_isAdIso ℚ L
  let ψ : (AfE ℚ L)ˣ →* ClassGroup (𝓞 L) :=
    (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).comp (toIdeles.comp (Units.map ι.toRingHom.toMonoidHom))
  let sel : ClassGroup (𝓞 L) → (AfE ℚ L)ˣ := fun c => if h : ∃ y, ψ y = c then h.choose else 1
  have hsel : ∀ x, ψ (sel (ψ x)) = ψ x := by
    intro x
    have h : ∃ y, ψ y = ψ x := ⟨x, rfl⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  refine ⟨Finset.univ.image sel, fun x => ⟨sel (ψ x), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
  have hk : ψ ((sel (ψ x))⁻¹ * x) = 1 := by rw [map_mul, map_inv, hsel, inv_mul_cancel]
  obtain ⟨a, k, hk, he⟩ := eq_ratId_mul_of_classOf ι hι _ hk
  refine ⟨a, k, hk, ?_⟩
  rw [mul_assoc, ← he, mul_inv_cancel_left]

end GlobalTheory.ClassCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegEqDel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.ImageDegree

theorem imageDeg_eq_del : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → (CompHt.imageDeg ev T.D : ℤ) = T.del := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hG hB hP
  obtain ⟨-, hdeg, hdim⟩ := GlobalTheory.T.degree_image_birational_linearSystem_eq_selfInt hQ F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F T.N T.D T.imageIdeal T.toLinSys.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hG.alg.variety) hdim
  rw [hP.imageDeg_eq hf]
  exact hdeg

end GlobalTheory.HSCore.ImageDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPowStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  first | exact @GlobalTheory.SkewIndex.index_inter_skew | exact GlobalTheory.SkewIndex.index_inter_skew | (intros; apply GlobalTheory.SkewIndex.index_inter_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrameStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_level_height_scales_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  first | exact @GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales | exact GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales | (intros; apply GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales <;> assumption)
end


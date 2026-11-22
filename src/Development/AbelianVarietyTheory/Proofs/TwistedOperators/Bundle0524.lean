import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownConv

open GlobalTheory.Grid

variable {D : D7}

theorem MeasDat.haar_fd {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem integrableOn_thetaKO_mul_cusp (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T}
    (hω : IsWeilDatumO ψ (sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ (sgn ε S) T Φ)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) (hc : IsCuspFun S φ) (h : GA D T) :
    IntegrableOn (fun g => thetaKO ω g h Φ * φ g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S φ := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  have e : ∀ g, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((ofSgn ε S).symm g) h Φ := fun g => by
    show ω (g, h) Φ 0 = ω (ofSgn ε S ((ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hcont : Continuous fun g => thetaKO ω g h Φ := by
    simp only [e]
    exact (hω.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε S).prodMk continuous_const)
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hg : GlobalTheory.Grow.ModGrowth S fun g => thetaKO ω g h Φ := by
    obtain ⟨C, A, hC⟩ := GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hΦ h
    exact ⟨C, A, fun g => by simp only [e]; exact hC _⟩
  exact hR.integrableOn_modGrowth_mul hν h𝓕 hg hinv hcont.measurable.aestronglyMeasurable

end GlobalTheory.DownConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DefiniteClassReal

theorem isReps_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) {I : Type} (y : I → A)
    (h : Bridge.IsReps ι J y) : Bridge.IsReps ι' J' (fun i => e (y i)) := by
  intro b
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := h (e.symm b)
  refine ⟨i, ⟨γ, ⟨e k, (hJ k).2 k.2⟩, ?_⟩, ?_⟩
  · have := congrArg e hk
    rw [e.apply_symm_apply] at this
    rw [this, map_mul, map_mul, he]
  · rintro j ⟨γ', k', hk'⟩
    refine hu j ⟨γ', ⟨e.symm k', (hJ _).1 (by rw [e.apply_symm_apply]; exact k'.2)⟩, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hk', map_mul, map_mul, he, e.apply_symm_apply]

theorem stab_transfer {Γ A B : Type} [Group Γ] [Group A] [Group B] (ι : Γ →* A) (ι' : Γ →* B) (e : A ≃* B)
    (he : ∀ γ, e (ι γ) = ι' γ) (J : Subgroup A) (J' : Subgroup B) (hJ : ∀ a, e a ∈ J' ↔ a ∈ J) (x : A) :
    Bridge.stab ι' J' (e x) = Bridge.stab ι J x := by
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← he, ← map_inv, ← map_mul, ← map_mul, hJ]

end GlobalTheory.DefiniteClassReal

namespace GlobalTheory.DefiniteClassReal
open GlobalTheory.FunObj GlobalTheory.ClassRegroup GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral GlobalTheory.DefiniteClassAvg

theorem integral_eq_finClSum_avg : ∀ {D : D7} (V : HSp D), (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) →
    ∀ (K K'' : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpenCompactLevel V K → IsOpenCompactLevel V K'' → K'' ≤ K →
    ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsMeasDef V K μ 𝓕 → ∀ (Φ : GA D V → ℂ),
    (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) → (∀ k ∈ Lev.levA V K'', ∀ g, Φ (g * k) = Φ g) →
    (∀ z, Continuous fun k : GinfC V => Φ (z * k)) →
    Finite (FinCl V K'') ∧ ∃ κ : Measure (GinfC V), κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
      ∫ g in 𝓕, Φ g ∂μ = ∑ᶠ c : FinCl V K'',
        ((μ ((K''.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))).toReal : ℂ) / (gamOrd V K'' c.out : ℂ) *
          ∫ k, Φ ((c.out : GA D V) * k) ∂κ := by
  intro D V hV K K'' hK hK'' hle μ 𝓕 hμ Φ hl hr hc

  let V' : HSp D := { V with sig := fun _ => (V.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC V : Set (GA D V)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have hHaar := hμ.1.1
  have hfin0 : Finite (FinCl V K'') := (finite_finCl_and_gamOrd V K'' hV hK'').1
  letI : Fintype (FinCl V K'') := Fintype.ofFinite _

  let κ : Measure (GinfC V) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC V))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  refine ⟨hfin0, κ, hκH, inferInstance, ?_⟩

  let e := finEquiv V
  have he : ∀ γ, e (((finPt V).comp (GQ V).subtype) γ) = Bridge.ratF V γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ levelFin V K'' ↔ a ∈ K''.comap (finG V) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out V K'')
  let y : FinCl V K'' → Bridge.Gf V := fun c => e (Quotient.out c)
  let z : FinCl V K'' → GA D V := fun c => ((Quotient.out c : GfC V) : GA D V)
  have hz : ∀ c, (finHom V).rangeRestrict (z c) = y c := fun c => rfl

  let J : Subgroup (GA D V) := K''.comap (Lev.finE V)
  let JK : Subgroup (GA D V) := K.comap (Lev.finE V)
  have hJo : IsOpen (J : Set (GA D V)) := hK''.1
  have hJJK : J ≤ JK := fun x hx => hle hx
  have hJK1 : μ JK = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have hJtop : μ J ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hJK1]; exact ENNReal.one_ne_top) (measure_mono (fun x hx => hJJK hx))
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC V ≤ J := by
    show GinfC V ≤ K''.comap (Lev.finE V)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  have hcont : Continuous Φ := continuous_of_level V K'' hK''.1 Φ hr hc
  have hu : ∀ x : GA D V, ∃! c, ∃ γ ∈ GQ V, ∃ k ∈ J, x = γ * z c * k :=
    existsUnique_doubleCoset (finHom V).rangeRestrict (GQ V) (levelFin V K'') y hy z hz
  have hs : ∀ c, (classGroupAt V K'' (y c) : Set (GQ V)) = {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    rw [SetLike.mem_coe, ← hz c, mem_classGroupAt]
    rfl
  have hfinΓ : ∀ c, {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J}.Finite := fun c =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ V) J hμ.2 hJ0 hJtop (z c)
  have him : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J} =
      Subtype.val '' {γ : GQ V | (z c)⁻¹ * (γ : GA D V) * z c ∈ J} := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ c, {γ : GA D V | γ ∈ GQ V ∧ (z c)⁻¹ * γ * z c ∈ J}.Finite := fun c =>
    him c ▸ (hfinΓ c).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA V K'', ∃ w : GinfC V, k = k' * (GinfC V).subtype w := fun k hk =>
    ⟨finPart V k, finPart_mem_levA V hk, ⟨realPart V k, realPart_mem V k⟩, (finPart_mul_realPart V k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA V K'', ∀ w : GinfC V, k * (GinfC V).subtype w = (GinfC V).subtype w * k :=
    fun k hk w => (Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC V, MeasurePreserving (· * (GinfC V).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D V) μ (GQ V) J (Lev.levA V K'') 𝓕 hμ.2 hJo hJtop (GinfC V) κ
    (GinfC V).subtype continuous_subtype_val hrt hdec hcomm (FinCl V K'') z hu hfin Φ hcont hl hr
  rw [heq, Finset.mul_sum, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcard : Nat.card (classGroupAt V K'' (y c)) = gamOrd V K'' (Quotient.out c) := by
    show Nat.card (Bridge.stab (Bridge.ratF V) (levelFin V K'') (e (Quotient.out c))) = _
    rw [stab_transfer _ _ e he _ _ hJe]
    exact card_stab V K'' _
  have hcard' : ((classGroupAt V K'' (y c) : Set (GQ V))).ncard = gamOrd V K'' (Quotient.out c) :=
    (Nat.card_coe_set_eq _).symm.trans hcard
  rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, hcard', div_eq_mul_inv, mul_assoc]
  rfl

end GlobalTheory.DefiniteClassReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

noncomputable section

namespace GlobalTheory.RowEx

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1000000 in

theorem inj_of_sep_conv {ch : Choice R} (hM : R.IsModels) (hsep : Separates R ch.W ch.M ch.w ch.ρ ch.ξ)
    (hconv : ∀ a u, ConvK ch a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ch.ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2

set_option maxHeartbeats 1000000 in

theorem isEx_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) (hB : BaseEx) : IsEx := by
  obtain ⟨C1, hL⟩ := hL
  obtain ⟨C2, hB⟩ := hB
  refine ⟨max 6510 (max C1 C2), fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨x3, hB⟩ := hB ε CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max x1 (max x2 x3), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset G W hW S₀ => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_of_max_le_left hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_max_left _ _) (le_of_max_le_right hx)
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_max_right _ _) (le_of_max_le_right hx)
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS0, hbase⟩ := hB D large₂ hε hx3 Γ Pl0 T A Ks R F hset G W hW S₀
  obtain ⟨ρ', ξ', hsep⟩ := hS D large₂ hε hx1 hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W hbase.weil M
    hbase.vol _ hbase.w_ne
  have hconv := hL D large₂ hε hx2 Γ Pl0 T A Ks R F hset _ rfl (hbase.withReal ρ' ξ')
  exact ⟨M, ρ', ξ', cv, rm, S, rp, n, e, c, hS0,
    hbase.is_withReal (inj_of_sep_conv hset.core.models hsep hconv)⟩

example : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → LinB → BaseEx → IsEx := isEx_of_separates

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section
namespace GlobalTheory.RowEx

theorem exists_nf_of_finite (S : Set ℂ) (hS : S.Finite) (hi : ∀ z ∈ S, IsIntegral ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ S ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hi, fun z hz => ?_⟩
  exact ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩

theorem rootsOne_finite {n : ℕ} (hn : 0 < n) : {z : ℂ | z ^ n = 1}.Finite :=
  (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
    simpa [Polynomial.mem_nthRoots hn] using hz

theorem isIntegral_of_pow_eq_one {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ^ n = 1) : IsIntegral ℚ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by simp [hz]⟩

theorem isIntegral_sqrt_nat (k : ℕ) : IsIntegral ℚ ((Real.sqrt k : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ((k : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  have h0 : ((Real.sqrt k : ℝ) : ℂ) ^ 2 = (k : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  simp [Polynomial.eval₂_sub, h0]

end GlobalTheory.RowEx
end

namespace GlobalTheory.RowEx

theorem nfRoot : NFRoot := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hs ch _ _ => ?_⟩⟩
  haveI : Finite T := hs.fin
  classical
  set G := ch.G
  set S := ch.S.toGridChoice
  have hN : ∀ w : Pl D.host.E, 0 < Ideal.absNorm w.asIdeal ^ depthAt G w := fun w =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)) _
  let P : Set (Pl D.host.E) := {w | w ∈ S.PA ∨ ∃ t, w ∈ locPl G t}
  have hP : P.Finite := by
    refine ((S.PA.finite_toSet).union (Set.finite_iUnion fun t => (locPl G t).finite_toSet)).subset ?_
    rintro w (hw | ⟨t, hw⟩)
    · exact Or.inl hw
    · exact Or.inr (Set.mem_iUnion.2 ⟨t, hw⟩)
  let Q : Set (Pl D.host.E) := ⋃ t, (locPl G t : Set (Pl D.host.E))
  have hQ : Q.Finite := Set.finite_iUnion fun t => (locPl G t).finite_toSet
  let X : Set ℂ := {z | z ^ 8 = 1} ∪ (⋃ w ∈ Q, {z : ℂ | z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1}) ∪
    (fun w : Pl D.host.E => ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)) '' P
  have hX : X.Finite :=
    ((rootsOne_finite (by norm_num)).union (hQ.biUnion fun w _ => rootsOne_finite (hN w))).union (hP.image _)
  have hi : ∀ z ∈ X, IsIntegral ℚ z := by
    rintro z ((hz | hz) | ⟨w, -, rfl⟩)
    · exact isIntegral_of_pow_eq_one (by norm_num) hz
    · obtain ⟨w, -, hz⟩ := Set.mem_iUnion₂.1 hz
      exact isIntegral_of_pow_eq_one (hN w) hz
    · exact isIntegral_sqrt_nat _
  obtain ⟨M, hM, hMX⟩ := exists_nf_of_finite X hX hi
  refine ⟨M, hM, fun z hz => hMX (Or.inl (Or.inl hz)), fun t w hw z hz => hMX (Or.inl (Or.inr ?_)), fun w hw => hMX (Or.inr ⟨w, hw, rfl⟩)⟩
  exact Set.mem_iUnion₂.2 ⟨w, Set.mem_iUnion.2 ⟨t, hw⟩, hz⟩

end GlobalTheory.RowEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipMatch

section Generic

def pairM {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) : k := ∑ i, ∑ j, X i j * Y i j

def chart {k k' A C A' C' : Type} [Field k] [Field k'] [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C') (g : GL A k') (h : GL C k') (X : Matrix A C k) : Matrix A' C' k' :=
  reindex eA eC (g.val * X.map j * h.val)

def IsLocIso {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    (j : k ≃+* k') : Prop :=
  Continuous j ∧ Continuous j.symm ∧ ∀ x, j x ∈ (ValuativeRel.valuation k').integer ↔ x ∈ (ValuativeRel.valuation k).integer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coX {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

def coY (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :
    Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1)

def IsMixChart {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (A A' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
    {k R C : Type} [Add k] [Zero k] (co tr mu : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Matrix R C k) (P : Finset C) : Prop :=
  (∀ u ∈ A, At (evFin F v) u ∧ (∀ r, ∀ s ∈ P, tr u r s = 0) ∧ (∀ r, ∀ s ∉ P, mu u r s = 0) ∧ co u = tr u + mu u) ∧
    ∀ u ∈ A', At (evFin F v) u ∧ (∀ r, ∀ s ∉ P, tr u r s = 0) ∧ ∀ r, ∀ s ∈ P, mu u r s = 0

end Generic

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def mixHalfS {i j : ℕ} (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (spW₁ G i j) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCoS (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      ((mulG (spW₁ G i j) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def colsEq (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) :
    Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ (locGrid G t w).Cols i j :=
  e.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))

variable (G) in

theorem rankW (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW G i j).rank = (locGrid G t w).rank (i + 1, j + 1) := by
  rw [rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨Nat.succ_le_of_lt i.2, Nat.succ_le_of_lt j.2⟩]

variable (G) in

theorem rankW₁ (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW₁ G i j).rank = (locGrid G t w).rank (i, j) := by
  rw [rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨le_of_lt i.2, le_of_lt j.2⟩]

def IsPlaceIso {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (j : Fv D.host.F v ≃+* Kw w) : Prop :=
  ∀ a : AE D, j (piW τ a) = cpt w (toEAf D a)

def xiAt (w : Pl D.host.E) : Kw w := algebraMap D.host.E (Kw w) D.host.xi0

def basCols (B : Frames G) {i j : ℕ} (e : Num G i j) (w : Pl D.host.E) :
    Matrix (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
  GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val)

def IsDoublyCompatible (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : Chars D.host.F D.host.E) : Prop :=
  IsTied t i j e Bs Γ X ∧ Γ.V'.L = GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))

end Grid

end GlobalTheory.FlipMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionFunctionIsUnfoldingNoCompactCoreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiActionFunction_isUnfolding_noCompactCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  first | exact @GlobalTheory.th_isTh_lev | exact GlobalTheory.th_isTh_lev | (intros; apply GlobalTheory.th_isTh_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizeGap_of_sizes : SizeGap :=
  fun _ => ⟨0, fun _ large₂ _ _ h => GlobalTheory.RowSizes.sizes_of_sizeRows large₂ h⟩

example : SizeGap := sizeGap_of_sizes

end GlobalTheory.SepRows

end
end


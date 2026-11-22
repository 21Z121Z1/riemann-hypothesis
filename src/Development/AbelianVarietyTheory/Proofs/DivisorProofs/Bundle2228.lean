import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientLatticeSpan
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Exp

open GlobalTheory.TraceIncl in

theorem clSum_equiv_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (g : G) (f : (A.MtCSD i t).Forms) :
    clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g f) = actS R i g (clSum (presV R i t) (kern R i t) f) := by
  refine clSum_act (presV R i t) (kernelLaws hS.models hS.thP hS.typ) (R.B.L i t).act_tie (envV R i t).J_le (actS R i)
    (fun q y w => funext fun v => ?_) g f
  exact (GlobalTheory.T.thetaKernelFiniteAdelic_laws R i t hS.models.inf hS.models.cV hS.thP.ωP hS.thP.pt_theta hS.thP.ioP hS.typ).2.2.2 _ q (hS.red i t q)
    (hl _) y w v

open GlobalTheory.TraceIncl in

theorem clSum_trU_of_lift {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : (∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (f : (A.MtCSD i t).Forms)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    clSum (presV R i t) (kern R i t) (trU (A.leftGroupActionLift i t) U ψ f) v =
      levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
  unfold levelTrace gaL
  rw [trU_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, clSum_equiv_of_lift hS hl, LinearMap.smul_apply, invChar, apply_dite D.what₂.embLL, map_zero]
  rfl

open GlobalTheory.TraceIncl in
set_option maxHeartbeats 4000000 in

theorem exists_adForm_levelTrace {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    (hS : HidaSetting R i t) (hl : ∀ g0 : G0 R.Pg D.R.r, ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ')
    (hχ : ∀ k, ∃ a : D.what₂.LL, D.what₂.embLL a = (((envV R i t).χ k : ℂˣ) : ℂ))
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {θ : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t U ψ 1 θ) {h : GA D (Vc D i)} (hh : h ∈ GfC (Vc D i)) {w : (R.cV i).W} (hw : InCoefLat R i h w) :
    ∃ y ∈ LinearMap.range θ, ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
      adForm R i y (fun ρ => v ρ) = levelTrace R i U ψ (singleSeries R i (R.ωP i t) (R.vP i t) h w v) := by
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  obtain ⟨e, r, h1, hL⟩ := exists_latSys (i := i) (t := t) hS.lev hT
  obtain ⟨f, hf, j, hj⟩ := hL.exists_trace (GlobalTheory.LevelCharOrder.levEnv_chi_isOfFinOrder _ _ _)
    (kernelLaws hS.models hS.thP hS.typ) (h := fin _ h) (x := e.symm P)
    (Submodule.mem_comap.2 ((e.apply_symm_apply P).symm ▸ hP : e (e.symm P) ∈ nabAtr (labLL D) (lamV D i) _))
  obtain ⟨y, -, ey⟩ := exists_src_trU i t U ψ hS.act hf
  have hcw : (presV R i t).coef (e.symm P) = c0L i P := (h1 _).trans (congrArg (c0L i) (e.apply_symm_apply P))
  obtain ⟨a, ha⟩ := hχ j
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  refine ⟨θ (a⁻¹ • y), LinearMap.mem_range_self _ _, fun v => ?_⟩
  have e1 : singleSeries R i (R.ωP i t) (R.vP i t) h (c0L i P) v =
      ((((envV R i t).χ j)⁻¹ : ℂˣ) : ℂ) • clSum (presV R i t) (kern R i t) f v :=
    (hS.kern_fin hh _ v).symm.trans ((congrArg (fun w' => kern R i t (fin _ h) w' v) hcw.symm).trans (congrFun hj v))
  have e2 : adForm R i (θ y) (fun ρ => v ρ) = (1 : ℂ) • levelTrace R i U ψ (clSum (presV R i t) (kern R i t) f v) := by
    rw [hS.adForm_theta hθ y v, ey, clSum_trU_of_lift hS hl]
  have e3 : adForm R i (θ (a⁻¹ • y)) (fun ρ => v ρ) = D.what₂.embLL a⁻¹ • adForm R i (θ y) (fun ρ => v ρ) := by
    rw [map_smul, adForm_smul]
    rfl
  rw [e3, e2, one_smul, e1, (levelTrace R i U ψ).map_smul, map_inv₀, ha, Units.val_inv_eq_inv_val]

theorem levelTraced_series_rational : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → AtTw fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  intro _ _ _ _
  have hR := GlobalTheory.T.rational_estimate_statement
  have hC := GlobalTheory.T.twisted_character_rational_values
  have hN := GlobalTheory.T.level_zero_lift_exists
  unfold RatSt AtPts at hR
  unfold AtTw AtPts at hC hN ⊢
  refine ((hR.and hC).and hN).imp fun Fm CH _ H => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := H
  obtain ⟨x0, hE⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx hle i p hp hM w hw j h hh w' hw' => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hE x hx hle i p hp
  obtain ⟨θ, hθ⟩ := a1 hM _ hw j
  obtain ⟨hCh, hOk, hU, -⟩ := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hS : GlobalTheory.TraceIncl.HidaSetting (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w)) :=
    ⟨hCh.lev, hCh.grp.red_L, hCh.fam.tie, hCh.models, hCh.thP, hU, ⟨_, ((fw2 p).hv₀ j _).1⟩, (hOk.lifts _ _).act,
      fun g0 κ κ' k1 k2 => GlobalTheory.VecInv.omega_lifts_vP (R2 p) hCh.lev hCh.models.inf hCh.thP.ωP hCh.thP.vP j _ g0 κ κ' k1 k2⟩
  obtain ⟨y, -, hy⟩ := exists_adForm_levelTrace hS (a3 hM w hw j) (a2 hM w hw j) hθ hh hw'
  refine ⟨y, ?_, hy⟩
  obtain ⟨n, b, hbK, -, -, -, hsp⟩ := (fw2 p).ks j
  have hy0 := hsp.symm ▸ (Submodule.mem_top (x := y))
  refine Submodule.span_le.2 ?_ hy0
  rintro _ ⟨k, rfl⟩
  have hk : (p.nexp.fi j).e ((p.nexp.fi j).e.symm (b k)) = b k := (p.nexp.fi j).e.apply_symm_apply (b k)
  refine Submodule.subset_span ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 ?_, hk⟩
  first
    | exact hk.symm ▸ hbK k
    | exact (congrArg (fun z => z ∈ (p.R.FW j).WK) hk).mpr (hbK k)
    | (rw [hk]; exact hbK k)

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFramedPointOverComponentGenericPoin
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.AllWt (ptF)

namespace GlobalTheory.GenCxPt

open Cardinal

theorem mk_le_aleph0 (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] : #K ≤ ℵ₀ := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  rw [Cardinal.mkRat, max_self] at h
  exact h

theorem transcendental_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    Algebra.Transcendental K ℂ := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  have h := Algebra.IsAlgebraic.cardinalMk_le_max K ℂ
  rw [Cardinal.mk_complex, max_eq_right (mk_le_aleph0 K)] at h
  exact absurd h (not_le.2 Cardinal.aleph0_lt_continuum)

theorem infinite_of_isTranscendenceBasis (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {κ : Type}
    {w : κ → ℂ} (hw : IsTranscendenceBasis K w) : Infinite κ := by
  haveI : Nonempty κ := hw.nonempty_iff_transcendental.2 (transcendental_complex K)
  have h := hw.lift_cardinalMk_eq_max_lift
  simp only [Cardinal.lift_id, Cardinal.mk_complex] at h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have h1 : #κ ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite κ).le
  have h2 : #K ⊔ #κ ⊔ ℵ₀ ≤ ℵ₀ := sup_le (sup_le (mk_le_aleph0 K) h1) le_rfl
  rw [← h] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

theorem nonempty_algHom_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (L : Type) [Field L]
    [Algebra K L] (n : ℕ) (hn : Algebra.trdeg K L = n) : Nonempty (L →ₐ[K] ℂ) := by
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' K L
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' K ℂ
  haveI := infinite_of_isTranscendenceBasis K hw
  have hι : #ι < ℵ₀ := by rw [hv.cardinalMk_eq_trdeg, hn]; exact Cardinal.natCast_lt_aleph0
  haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.1 hι
  have hle : #ι ≤ #κ := hι.le.trans (Cardinal.infinite_iff.1 inferInstance)
  obtain ⟨f⟩ := hle
  obtain ⟨j, -⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hv (hw.1.comp f f.injective)
  exact ⟨j⟩

end GlobalTheory.GenCxPt

namespace GlobalTheory.GenCxPt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

end GlobalTheory.GenCxPt

open GlobalTheory.GenCxPt in

theorem GlobalTheory.GenCxPt.exists_frPt_ptF_eq_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c),
    ∃ y : FrPt Xo c ℂ, ∀ s, ptF y s = genPt Z := by
  intro E _ _ _ H Dw l Xo c Z
  haveI := c.fin
  obtain ⟨e⟩ := nonempty_algHom_complex c.F (kap Z) Dw.dim ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2 Z)
  have hsnd : spMap (e : kap Z →+* ℂ) ≫ genSp Z ≫ strK = spMap (algebraMap c.F ℂ) := by
    rw [genSp_strK, spMap_comp_spMap, AlgHom.comp_algebraMap]
  have hx : (spMap (e : kap Z →+* ℂ) ≫ xGen Z) ≫ Xo.s = sOf c ℂ := by
    rw [xGen, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (genSp Z),
      ← Category.assoc, hsnd, sOf, spMap_comp_spMap]
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt _ hx
  refine ⟨y, fun s => ?_⟩
  have hpt : ptF y = spMap (e : kap Z →+* ℂ) ≫ genSp Z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hy, xGen, Category.assoc]
    · rw [ptF, pullback.lift_snd, Category.assoc, ← hsnd]
  rw [hpt]
  have : (spMap (e : kap Z →+* ℂ) ≫ genSp Z) s ∈ Set.range (genSp Z) :=
    ⟨spMap (e : kap Z →+* ℂ) s, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [genSp, Scheme.range_fromSpecResidueField] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantExponentsMatchingWeightBarGapStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_exponents_matching_weight_bar_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), 1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  first | exact @GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar | exact GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar | (intros; apply GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullDominant

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]

theorem unitAt_map {x : M} {u : W.functionField} (h : UnitAt (f x) u) :
    UnitAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨f.stalkMap x a, ha.map _, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

theorem regAt_map {x : M} {u : W.functionField} (h : RegAt (f x) u) :
    RegAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

abbrev unitsMap : W.functionFieldˣ →* M.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap f).toMonoidHom

theorem germOf_map_eq {D₀ : CartierDiv W} {x : M} {g g' : W.functionFieldˣ}
    (h : D₀.IsEqn (f x) g) (h' : D₀.IsEqn (f x) g') :
    germOf x (unitsMap f g) = germOf x (unitsMap f g') := by
  rw [germOf_eq_iff]
  have := unitAt_map f (h.iff_unitAt.1 h')
  simpa [map_div₀] using this

def pullGerm (D₀ : CartierDiv W) (x : M) : Germ x :=
  germOf x (unitsMap f (D₀.exists_isEqn (f x)).choose)

theorem pullGerm_eq {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    pullGerm f D₀ x = germOf x (unitsMap f g) :=
  germOf_map_eq f (D₀.exists_isEqn (f x)).choose_spec h

def pull (D₀ : CartierDiv W) : CartierDiv M :=
  show cartierGroup M from ⟨pullGerm f D₀, fun x => by
    obtain ⟨U, hU, g, hg⟩ := D₀.exists_isEqn_nhds (f x)
    exact ⟨f ⁻¹ᵁ U, hU, unitsMap f g, fun y hy => pullGerm_eq f (hg (f y) hy)⟩⟩

theorem isEqn_pull {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    (pull f D₀).IsEqn x (unitsMap f g) :=
  pullGerm_eq f h

theorem eff_pull {D₀ : CartierDiv W} (hD : D₀.Eff) : (pull f D₀).Eff := by
  intro x
  obtain ⟨g, hg⟩ := D₀.exists_isEqn (f x)
  refine ⟨unitsMap f g, isEqn_pull f hg, ?_⟩
  rw [one_mul]
  exact regAt_map f (CartierDiv.eff_iff.1 hD _ _ hg)

end GlobalTheory.Cartier.PullDominant

open GlobalTheory.Cartier.PullDominant in

theorem GlobalTheory.Cartier.exists_pull_dominant :
    ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  intro M W _ _ f _ D₀ hD
  exact ⟨pull f D₀, eff_pull f hD, fun x g h => isEqn_pull f h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEvenUnimodularCharZero
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.PowEightField

open GlobalTheory.EighthPowerFactor GlobalTheory.CechPic

theorem exists_eighthPower_evenUnimodular_charZero : ∃ d : ℕ, 1 ≤ d ∧ ∀ (K : Type) [Field K] [CharZero K] (P : PolAV (Sp K)), ∃ (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ P.A)) (inc : P.A ⟶ Q.A), Q.g = 8 * P.g ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsPow8 P Q d pr inc := by
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  have hW0 : 0 < W 0 0 := by
    have h := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h
    have : (0 : ℝ) < (W 0 0 : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(2 * W 0 0).toNat, by omega, ?_⟩
  intro K _ _ P
  have := P.isAb.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hb⟩ := hbas P.g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase K 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns P.isAb P.isLB P.g).Principal :=
    ⟨relAmple_diag_lam P.isAb P.isLB (Moduli.cube_of_isLB _ P P.L P.isLB) P.ample,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam P.isLB P.ktriv x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, hL, -⟩, h₁, h₂, h₃⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB P.g _ W _ a w w'
    bas hW hb hw hw' hs 1 K b _ (𝟙 _) (siegOne L₁.globalFns P.isAb P.isLB P.g) (one_pow _) odd_one hc P.smoothDim
  obtain ⟨inc, hinc, -⟩ := hu P.A fun u => if u = 0 then 𝟙 P.A else 1
  refine ⟨t.pol, pr, inc, rfl, ⟨t.act w, t.act w', t.hom w, t.hom w', h₁, h₃, h₂⟩, hpr, ?_, hu, hinc, ?_⟩
  · refine isMonHom_of_coord hpr hu fun u => ?_
    rw [hinc u]
    by_cases h : u = 0
    · subst h; simp only [↓reduceIte]; exact inferInstanceAs (IsMonHom (𝟙 P.A))
    · simp only [h, ↓reduceIte]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
  ·
    have hP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
    have hQ : t.pol.L.IsLB := t.pol.isLB
    have hlam : cls _ hP = lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) := cls_cube_two P.isLB _ _ hP
    have hdiag := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hP _)).2 (SiegelOfPolarised.lbIso_diag L₁ P)
    rw [cls_lbPow P.isLB, cls_pull hP, hlam, pull_lam, lift_fst, lift_snd] at hdiag
    have e1 := ((cls_eq_iff hQ (LB.isLB_linComb hP _ _)).2 hL).trans (cls_linComb hP _ _ _)
    refine (cls_eq_iff (pull_isLB hQ _) (LB.isLB_linComb P.isLB _ _)).1 ?_
    refine ((congrArg (pull inc.left) e1).trans ?_).trans (cls_lbPow P.isLB _ _).symm
    rw [hlam]
    erw [map_sum]
    rw [Fintype.sum_eq_single ((0 : Fin 8), (0 : Fin 8))]
    · erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      erw [hinc]
      simp only [↓reduceIte]
      rw [← hdiag, ← natCast_zsmul, ← natCast_zsmul, smul_smul, Int.toNat_of_nonneg (by omega)]
      congr 1
      push_cast
      ring
    · rintro ⟨u, v⟩ huv
      erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      have hi1 : ∀ u : Fin 8, u ≠ 0 → inc ≫ pr u = 1 := fun u h => (hinc u).trans (if_neg h)
      by_cases hu0 : u = 0
      · subst hu0
        have hv0 : v ≠ 0 := fun h => huv (by rw [h])
        erw [hi1 v hv0, lam_one_right, smul_zero]
      · erw [hi1 u hu0, lam_one_left, smul_zero]

end GlobalTheory.MBLow.PowEightField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerSemiAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_eighthPower_semiAbelianScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∃ (G₈ : Over (Sp R)) (_ : GrpObj G₈) (prG : Fin 8 → (G₈ ⟶ G)), IsSemiAbelian G₈ ∧ (∀ u, IsMonHom (prG u)) ∧ ∀ (T : Over (Sp R)) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ G₈, ∀ u, x ≫ prG u = y u := by
  intro R _ G _ hG
  haveI : IsCommMonObj G := hG.comm
  refine ⟨powObj G 8, inferInstance, powPr G, ?_, fun u => inferInstance, fun T y => ?_⟩
  · exact GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G 8) G 8 (powIsPowGrp G 8) hG
  · refine ⟨(powIsLimit G 8).lift (Fan.mk T y), fun u => (powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩, ?_⟩
    intro x hx
    apply (powIsLimit G 8).hom_ext
    rintro ⟨u⟩
    exact (hx u).trans ((powIsLimit G 8).fac (Fan.mk T y) ⟨u⟩).symm

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtendMulSimplePoleOfVanishingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extend_mul_simplePole_of_vanishing : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) → ∃ G : H0 p N ⊤, H0.restr le_top G = C.mul ω (H0.restr le_top g) := by
  first | exact @GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole | exact GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole | (intros; apply GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderLevelMoveUniversalSemiAbelian
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.MoveOrder

theorem finite_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) («γ» : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsIso ρ → IsLevMove ρ ν (liftLa «γ») LinearMap.id → ∃ n : ℕ, 0 < n ∧ (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[n] (𝟙 _) = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c γ ρ ν hpq hl hρ hm
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  obtain ⟨⟨ι, hι, -⟩, hmul, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  have h₀ : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  have key : ∀ k : ℕ, ∃ (ρk : Xo.X ⟶ Xo.X) (μ : SABMap Xo.univ.t Xo.univ.t ρk), IsIso ρk ∧
      IsLevMove ρk μ (liftLa («γ» ^ k)) LinearMap.id ∧
      μ.φ = (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[k] (𝟙 _) := by
    intro k
    induction k with
    | zero => exact ⟨𝟙 _, ι, inferInstance, by rw [pow_zero]; exact h₀, by rw [hι]; rfl⟩
    | succ k ih =>
      obtain ⟨ρk, μ, ik, hk, hφ⟩ := ih
      obtain ⟨κ, hκ, -⟩ := hmul ρk ρ μ ν
      refine ⟨ρk ≫ ρ, κ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, ?_⟩
      · rw [Category.assoc, hm.1, hk.1]
      · rw [pow_succ, GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub («γ» ^ k) «γ» a), hκ,
          ← Category.assoc, hk.2.1, Category.assoc, hm.2.1, Category.assoc]
      · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
            (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
        rw [e, hκ, ← Category.assoc, hk.2.2, Category.assoc, hm.2.2, Category.assoc]
      · rw [hκ, hφ, Function.iterate_succ_apply']
  refine ⟨orderOf «γ», orderOf_pos «γ», ?_⟩
  obtain ⟨ρn, μ, i, h, hφ⟩ := key (orderOf «γ»)
  rw [pow_orderOf_eq_one] at h
  rw [← hφ, (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h h₀).2, hι]

end GlobalTheory.MoveOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  first | exact @GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev | exact GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev | (intros; apply GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev <;> assumption)
end


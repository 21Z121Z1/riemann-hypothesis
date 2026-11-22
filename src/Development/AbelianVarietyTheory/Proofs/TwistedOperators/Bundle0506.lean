import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0498
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusUnip

variable {D : D7}

theorem setIntegral_mul_right {B : HSp D} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e)
    {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)} (hN : GlobalTheory.Per.IsUnitN B e ν 𝓝) (f : NFlag B e → ℂ)
    (hf : ∀ γ ∈ NFlagQ B e, ∀ n, f (γ * n) = f n) (y : NFlag B e) :
    ∫ n in 𝓝, f (n * y) ∂ν = ∫ n in 𝓝, f n ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B he
  obtain ⟨u1, u2, u3⟩ := hN
  haveI : DiscreteTopology (NFlagQ B e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcov' : ∀ x : NFlag B e, ∃ s ∈ NFlagQ B e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : NFlag B e, ν.map (· * a) = ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice ν (NFlagQ B e) hK hcov' a
  have hmp : MeasurePreserving (· * y) ν ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) ν ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) f 𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B e) ((· * y⁻¹) ⁻¹' 𝓝) ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hf γ γ.2 x).symm

theorem bplus_rTr_unip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  intro D T L sc G W M hM φ F hF u hu
  have hn : ∀ n, ‖besChar W.ψ G.besTop n‖ = 1 := fun n => by
    unfold besChar
    split_ifs with h
    · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
      rw [e]
      exact W.ψ_std.1.2.1 _
    · exact norm_one
  have hu1 : besChar W.ψ G.besTop u * star (besChar W.ψ G.besTop u) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have inner : ∀ h, ∫ n in M.fdN, besInt W φ (rTr _ u F) h n ∂M.νN =
      besChar W.ψ G.besTop u * ∫ n in M.fdN, besInt W φ F h n ∂M.νN := fun h => by
    have hs : EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h := (embRel_iff _ h _).2 rfl
    obtain ⟨hy, hyc⟩ := GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop (embTop G h) h hs u hu
    let y : NFlag (G.V (.grid D.R.m 0)) G.besTop.e := ⟨_, hy⟩
    have hinv : ∀ γ ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n,
        besInt W φ F h (γ * n) = besInt W φ F h n := fun γ hγ n => by
      have hγQ : (γ : GA D (G.V (.grid D.R.m 0))) ∈ GQ (G.V (.grid D.R.m 0)) := Subgroup.mem_subgroupOf.1 hγ
      simp only [besInt, Subgroup.coe_mul]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ.2 n.2,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ.2 hγQ, one_mul, mul_assoc (γ : GA D (G.V (.grid D.R.m 0))) (n : GA D (G.V (.grid D.R.m 0))) (embTop G h),
        hF.2 _ hγQ]
    have hpt : ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e, besInt W φ (rTr _ u F) h n =
        besChar W.ψ G.besTop u * besInt W φ F h (n * y) := fun n => by
      simp only [besInt, rTr, Subgroup.coe_mul, y]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ n.2 hy, hyc, star_mul]
      have e1 : (n : GA D (G.V (.grid D.R.m 0))) * (embTop G h * u * (embTop G h)⁻¹) * embTop G h =
          (n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u := by group
      rw [e1]
      linear_combination (-(φ h * F ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u) *
        star (besChar W.ψ G.besTop (n : GA D (G.V (.grid D.R.m 0)))))) * hu1
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_mul_right G.besTop.e_iso hM.unip _ hinv y]
  unfold Bplus
  simp_rw [inner]
  exact integral_const_mul _ _

end GlobalTheory.BplusUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section

namespace GlobalTheory.BplusShift

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem embTop_mul (a b : GA D (G.V (.top 0))) : embTop G (a * b) = embTop G a * embTop G b := by
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  rw [e, e, e, map_mul]

theorem inner_left (W : G.Weil) (M : Vol G) (hM : M.IsRow) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)}
    (hφ : φ ∈ contLeft (G.V (.top 0))) (hF : F ∈ contLeft (G.V (.grid D.R.m 0))) {γ : GA D (G.V (.top 0))}
    (hγ : γ ∈ GQ (G.V (.top 0))) (h : GA D (G.V (.top 0))) :
    ∫ n in M.fdN, besInt W φ F (γ * h) n ∂M.νN = ∫ n in M.fdN, besInt W φ F h n ∂M.νN := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  have r1 := (hs γ (s γ)).2 rfl
  have r2 := (hs γ⁻¹ (s γ)⁻¹).2 (map_inv s _).symm
  have hδ : s γ ∈ GQ (G.V (.grid D.R.m 0)) := hq _ hγ
  let c : NFlag (G.V (.grid D.R.m 0)) G.besTop.e ≃ₜ* NFlag (G.V (.grid D.R.m 0)) G.besTop.e :=
    { toFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).1⟩
      invFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r2 n n.2).1⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e ↔ n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e := fun n => by
    change s γ * n.1 * (s γ)⁻¹ ∈ GQ (G.V (.grid D.R.m 0)) ↔ n.1 ∈ GQ (G.V (.grid D.R.m 0))
    rw [Subgroup.mul_mem_cancel_right _ (inv_mem hδ), Subgroup.mul_mem_cancel_left _ hδ]
  have hl : ∀ γ' ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      besInt W φ F (γ * h) (γ' * n) = besInt W φ F (γ * h) n := fun γ' hγ' n => by
    have hq' := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besInt, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ'.2 n.2, GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ'.2 hq',
      one_mul, mul_assoc γ'.1, hF.2 _ hq']
  refine (GlobalTheory.Mem.TrueRecord.integral_aut _ hM.unip.1 hM.unip.2.1 hM.unip.2.2 c hc _ hl).symm.trans ?_
  congr 1
  funext n
  change φ (γ * h) * F ((s γ * n * (s γ)⁻¹) * embTop G (γ * h)) * star (besChar W.ψ G.besTop (s γ * n * (s γ)⁻¹)) =
    φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)
  rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).2, hφ.2 γ hγ h, e, e, map_mul,
    show s γ * n * (s γ)⁻¹ * (s γ * s h) = s γ * (n * s h) by group, hF.2 _ hδ]

end GlobalTheory.BplusShift

open GlobalTheory.BplusShift in

theorem GlobalTheory.BplusShift.bplus_rTr : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  intro D T L sc G W M hM φ hφ F hF a
  have hshift : ∀ h n, besInt W (rTr _ a φ) (rTr _ (embTop G a) F) h n = besInt W φ F (h * a) n := fun h n => by
    simp only [besInt, rTr]
    rw [embTop_mul, mul_assoc (n : GA D (G.V (.grid D.R.m 0)))]
  simp only [Bplus, hshift]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  haveI := hμ
  haveI : (M.ν (.top 0)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hμ
  have hmp : MeasurePreserving (· * a) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a
  have hmp' : MeasurePreserving (· * a⁻¹) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a⁻¹
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a)
    (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)), Set.image_mul_right]
  have hF' : IsFundamentalDomain (GQ (G.V (.top 0))) ((· * a⁻¹) ⁻¹' M.fd (.top 0)) (M.ν (.top 0)) :=
    h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (h𝓕.setIntegral_eq hF' fun γ x => inner_left W M hM hφ hF γ.2 x).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActionsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainCompositeLift_intertwines_finiteGroupActions : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) → ∀ t g κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ → ∀ y y' : (R.HX t).H, (∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ)) → R.Th t y' = R.gE g (R.Th t y) := by
  first | exact @GlobalTheory.ChainLiftEquiv.th_intertwines | exact GlobalTheory.ChainLiftEquiv.th_intertwines | (intros; apply GlobalTheory.ChainLiftEquiv.th_intertwines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientPoincareSeries_move_real_point : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  first | exact @GlobalTheory.PoinConj.poin_conj | exact GlobalTheory.PoinConj.poin_conj | (intros; apply GlobalTheory.PoinConj.poin_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitaryEmbeddingColumns

open GlobalTheory.FinPl GlobalTheory.SeeSaw

theorem gram_star {D : D7} (B : HSp D) (i j : Fin B.rank) : star (B.gram i j) = B.gram j i := by
  have := B.herm.eq (B.frame i) (B.frame j)
  simpa [HSpace.gram, starRingEnd_apply] using this

theorem incA_mul_tmul' {D : D7} (e : D.host.E) (y : AF D.host.F) (z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA {D : D7} (y : AF D.host.F) (t e : D.host.E) :
    (y ⊗ₜ[D.host.F] t) * incA D e = y ⊗ₜ[D.host.F] (t * e) := by
  show (y ⊗ₜ[D.host.F] t) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

set_option maxHeartbeats 1000000 in

theorem mem_idV_of_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v)) : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  classical
  set r : Fin c := q.rev with hr
  set κ : D.host.E := antiDiagonalSignGramMatrix c ε r q with hκdef
  have hcond : ∀ p : Fin c, (r.1 + p.1 + 1 = c ↔ p = q) := by
    intro p
    have := q.2; have := p.2
    rw [hr, Fin.val_rev, Fin.ext_iff]; omega
  have hκ : κ ≠ 0 := by
    rw [hκdef, antiDiagonalSignGramMatrix, if_pos ((hcond q).2 rfl)]
    split_ifs
    · exact hε
    · exact one_ne_zero
  let π : Fin B.rank → D.host.E := fun j => κ⁻¹ * ∑ l, star (d.a l r) * B.gram l j
  have hπa : ∀ p, ∑ j, π j * d.a j p = if p = q then 1 else 0 := by
    intro p
    have e := congrFun (congrFun d.gram r) p
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply] at e
    have e2 : ∑ j, π j * d.a j p = κ⁻¹ * antiDiagonalSignGramMatrix c ε r p := by
      rw [← e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc]
      congr 2
    rw [e2]
    split_ifs with hp
    · subst hp; rw [← hκdef]; exact inv_mul_cancel₀ hκ
    · rw [antiDiagonalSignGramMatrix, if_neg (fun h' => hp ((hcond p).1 h')), mul_zero]
  have hπM : ∀ i, ∑ j, π j * frameMat B A d.ι j i = 0 := by
    intro i
    have e := congrFun (congrFun d.perp i) r
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, Matrix.zero_apply] at e
    have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
    have e3 : ∑ j, π j * frameMat B A d.ι j i =
        κ⁻¹ * ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc, Finset.sum_mul]
    rw [e3]
    have e4 : ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i =
        star (∑ l, (∑ x, (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι x i) * B.gram x l) * d.a l r) := by
      simp only [star_sum, star_mul', Finset.sum_mul, hsig, star_star, gram_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e4, e, star_zero, mul_zero]
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun Y => ∑ k, incA D (π k) * Y k
      map_zero' := by simp
      map_add' := fun Y Z => by simp [mul_add, Finset.sum_add_distrib] }
  have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), Φ Y ∈ idV (𝔟 q) v := by
    intro Y hY
    induction hY using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) i)) =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] u q := by
        show ∑ k, incA D (π k) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k)) = _
        simp only [incA_mul_tmul', one_mul]
        rw [← TensorProduct.tmul_sum]
        congr 1
        have h1 : ∑ k, π k * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k =
            ∑ i, (∑ j, π j * frameMat B A d.ι j i) * y i + ∑ p, (∑ j, π j * d.a j p) * u p := by
          simp only [Pi.add_apply, mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          congr 1
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h1]
        simp only [hπM, hπa, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e]
      exact AddSubgroup.subset_closure ⟨α, hα, hαv, u q, hu q, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add Y Z _ _ hY hZ => rw [map_add]; exact add_mem hY hZ
    | neg Y _ hY => rw [map_neg]; exact neg_mem hY
  have key := hΦ _ h
  have e : Φ (fun k => b * incA D (d.a k q)) = b := by
    show ∑ k, incA D (π k) * (b * incA D (d.a k q)) = b
    have : ∀ k, incA D (π k) * (b * incA D (d.a k q)) = b * incA D (π k * d.a k q) := fun k => by
      rw [map_mul (incA D) (π k) (d.a k q)]; ring
    rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, ← map_sum, hπa q, if_pos rfl, map_one, mul_one]
  rwa [e] at key

set_option maxHeartbeats 1000000 in

theorem mem_of_mem_idV {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) := by
  classical
  let Ψ : AE D →+ (Fin B.rank → AE D) := AddMonoidHom.pi fun k => AddMonoidHom.mulRight (incA D (d.a k q))
  have hle : idV (𝔟 q) v ≤ (latV B (d.lat Λ 𝔟) (· = v)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, t, ht, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hαv, 1, Set.mem_singleton _, d.a *ᵥ Pi.single q t, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q t, fun p => ?_, by simp⟩
      by_cases hp : p = q
      · subst hp; simpa using ht
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] t) * incA D (d.a k q) = _
      rw [tmul_mul_incA, one_mul]
      congr 1
      rw [mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply, mul_comm]
  exact hle h

theorem mem_latV_iff {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D) :
    (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v :=
  ⟨mem_idV_of_mem d hε Λ 𝔟 v q b, mem_of_mem_idV d Λ 𝔟 v q b⟩

end GlobalTheory.UnitaryEmbeddingColumns

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianListStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_element_gaussian_list : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  first | exact @GlobalTheory.KInfLines.prod_lines | exact GlobalTheory.KInfLines.prod_lines | (intros; apply GlobalTheory.KInfLines.prod_lines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomaiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  first | exact @GlobalTheory.HaarConjImage.map_isHaarFD | exact GlobalTheory.HaarConjImage.map_isHaarFD | (intros; apply GlobalTheory.HaarConjImage.map_isHaarFD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerConstTermObj

theorem towerConstTerm : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by

  intro D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  have hcomp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.Compatible ψ V V' W C B ω ω' :=
    GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  exact GlobalTheory.T.thetaLift_constantTerm_compatibleWeil D V V' W r C B hsplit ψ χS χT χS χT' ω ω' hω hω' hcomp

end GlobalTheory.TowerConstTermObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThetaSeparates

theorem eq_zero_of_thetaSum_rho : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
    (∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = 0) → Φ = 0 := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Φ hΦ h
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  obtain ⟨𝓕₁, hF, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain F (Fin n × Fin d) μ inferInstance
  funext x
  have hP := GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq F ψ (GlobalTheory.StdCharFromIsStd.isCharAF hψ)
    (Fin n × Fin d) μ inferInstance 𝓕₁ hF htop Φ hΦ x
  have hz : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = 0 := by
    intro y
    have := h (M.co.e.symm (x, y))
    simpa [GlobalTheory.WeilM.Darboux.rho] using this
  simp only [hz, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, MeasureTheory.lintegral_zero] at hP
  have hs := (mul_eq_zero.mp hP.symm).resolve_left h0
  have h1 := ENNReal.tsum_eq_zero.mp hs 0
  have e : ((fun _ => (0 : AF F)) : Fin n × Fin d → AF F) + x = x := zero_add x
  simp only [map_zero, enorm_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h1
  simpa [e] using h1

end GlobalTheory.ThetaSeparates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeIsogenyFamily_pullback_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X), x = h ≫ Z.π₁ → x' = h ≫ Z.π₂ → ∃ Ψ : Gx x ⟶ Gx x', IsHeckeFam P p i Ψ ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
  first | exact @GlobalTheory.HeckeEx.exists_isHeckeFam_carries | exact GlobalTheory.HeckeEx.exists_isHeckeFam_carries | (intros; apply GlobalTheory.HeckeEx.exists_isHeckeFam_carries <;> assumption)
end


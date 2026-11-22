import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0414
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0068
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0707
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0386
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0712
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftFiniteVectorEqTranslateLevelDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in

theorem thP_vec_eq_translate : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (hn : T.rank ≤ S.rank) (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ f₀ f, IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → ∃ (Lv : SW.Level C.X) (M : ℕ) (f' : WO S T → ℂ) (k₀ : GA D S), IdemTwo Lv.w ∧ 0 < M ∧ (M : 𝓞 D.host.E) ∈ Lv.𝔪 ∧ C.IsBase Lv B f' ∧ k₀ ∈ GfC S ∧ f = om (k₀, 1) (C.uVec Lv hn f') ∧ C.IsTh (C.uVec Lv hn f') ∧ C.IsFock B (C.uVec Lv hn f') ∧ C.uVec Lv hn f' ≠ 0 ∧ ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C om hom hn B hB ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd f₀ f hf
  have hf0 : f ≠ 0 := GlobalTheory.T.theta_kernel_finite_vector_ne_zero D S T C hn B hB ΛT hsd βS βT hβS hβT Pg Q ξ f₀ f hf
  have hfc := hf
  obtain ⟨hvac, e, he, hθ⟩ := hf
  obtain ⟨Lv, k₀, Λ', L, hw2, hmP, hJ, hk₀, hmov, hfin, hA, hB', hC, hD, hE, hF⟩ :=
    GlobalTheory.T.thetaLift_level_datum_sum_of_translates D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd e he
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hfT : f = Tm (thPDatum S T βS βT Pg Q ξ e) := hall Tm hTm
  obtain ⟨hSB, hTh, hFock, hLat⟩ := GlobalTheory.T.placeModel_indicator_theta_fock_latticeVacuum D S T C B hB ΛT hsd (Pg ∪ Q) e he f₀ hvac Tm hTm L hA hB' hC
  have hLat'' := hLat _ hD
  haveI := Fintype.ofFinite (LvCls C Lv)
  set f'' := Tm (indL L) with hf''
  have hee : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hhalf : ∀ w : WO S T, IsHalf (cA D e) (partAt (cA D e) w) := fun w i j => by
    simp only [partAt, Matrix.map_apply]
    rw [← mul_assoc, hee]
  set t : LvCls C Lv → WO S T := fun c =>
    partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) with ht
  have hfsum : f = ∑ c : LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) •
      heisO C.ψ S T (t c) f'' := by
    rw [hfT]
    have hΦ : thPDatum S T βS βT Pg Q ξ e = ∑ c : LvCls C Lv,
        Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) • fun x => indL L (x + t c) := by
      funext x
      rw [hF x, finsum_eq_sum_of_fintype, Finset.sum_apply]
      rfl
    rw [hΦ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hTm.trans _ hSB _ (hhalf _)]
  set f' := om (k₀⁻¹, 1) f'' with hf'
  have hinv : ∀ g : GA D S, ∀ x, om (g, 1) (om (g⁻¹, 1) x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    exact congrArg (fun E : Module.End ℂ (WO S T → ℂ) => E x) om.map_one
  have hinv' : ∀ g : GA D S, ∀ x, om (g⁻¹, 1) (om (g, 1) x) = x := fun g x => by
    simpa using hinv g⁻¹ x
  have hom1 : om (k₀, 1) f' = f'' := hinv k₀ f''
  have hTh' : C.IsTh f' := hom.om_pres _ _ hTh
  have hu : om (k₀, 1) (C.uVec Lv hn f') = f := by
    rw [hfsum, Ctx.uVec, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
    congr 1
    rw [Ctx.rho, hom.om_heis _ _ _ _ hTh', hom1]
    obtain ⟨v, hv, hv1, hv2⟩ := hE _ (c.out).2
    have h2 : heisO C.ψ S T (2 • v) f'' = f'' := hLat''.1 v hv
    have h3 := GlobalTheory.FinTranslate.heisO_heisO S T C.ψ (t c) (2 • v) f''
    rw [h2, show C.ψ (symplOH S T (t c) (2 • v)) = 1 from hv2, one_smul] at h3
    calc heisO C.ψ S T (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) f''
        = heisO C.ψ S T (t c + 2 • v) f'' := congrArg (fun w => heisO C.ψ S T w f'') hv1
      _ = heisO C.ψ S T (t c) f'' := h3.symm
  have hmt1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
  have hmvB : C.mvB 1 B = B := by
    funext τ
    simp [Ctx.mvB, hmt1, compAt]
  have hfmt1 : fmt T 1 = 1 := by simp [fmt, hmt1]
  have hmov1 : IsMov (fmt T 1) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) := by
    rw [hfmt1]
    intro u
    exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, fun ⟨u₀, h, e⟩ => by rw [e, Matrix.one_mulVec]; exact h⟩
  have hne' : f' ≠ 0 := by
    intro h0
    apply hf0
    have : f'' = 0 := by rw [← hom1, h0, map_zero]
    rw [hfsum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [this]
    have : heisO C.ψ S T (t c) (0 : WO S T → ℂ) = 0 := by
      funext w
      simp [heisO]
    rw [this, smul_zero]
  have hFock' : C.IsFock B f' := by
    have := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f'' hTh).2 B hB).1 hFock)
    rwa [hmvB] at this
  have hlat' : IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ))) f' :=
    (GlobalTheory.TensLatMove.hatA_move D S T C k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmov hmov1).2
      om hom f'' hTh hLat''
  have hbase : C.IsBase Lv B f' := ⟨hTh', hne', hFock', hlat'⟩
  have hu1 : C.IsTh (C.uVec Lv hn f') := GlobalTheory.Ker.KernelCompare.isTh_uVec C Lv hn hTh'
  have hfth : C.IsTh f := hu ▸ hom.om_pres _ _ hu1
  have hfF : C.IsFock B f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_thPVec C.ψ C.θ S T _ _ _ _ βS βT Pg Q ξ f₀ f hfc hfth τ
  have hu2 : C.IsFock B (C.uVec Lv hn f') := by
    have h := (((GlobalTheory.Ker.WeakMove.om_move D S T C om hom k₀⁻¹ 1 f hfth).2 B hB).1 hfF)
    rw [hmvB, ← hu, hinv'] at h
    exact h
  have hu3 : C.uVec Lv hn f' ≠ 0 := fun h0 => hf0 (by rw [← hu, h0, map_zero])
  refine ⟨Lv, Ideal.absNorm Lv.𝔪, f', k₀, hw2, ?_, Ideal.absNorm_mem Lv.𝔪, hbase, hk₀, hu.symm, hu1, hu2, hu3,
    GlobalTheory.T.hermitianThetaLevelGroup_stabilizes_selfDualLatticeFrame D S T C Lv ΛT hsd hAA βT hβT Pg hmP hJ⟩
  exact Nat.pos_of_ne_zero fun h => Lv.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalOfCuspType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowApprox

theorem thetaLift_approx_of (hL1 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) (hL2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨hν, hfd⟩ := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hvol := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν hfd
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (G.V i j).V.rank (G.V i (j + 1)).V.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (G.V i j).V (G.V i (j + 1)).V
  obtain ⟨C0, hC0, hK⟩ := (H _ _ rfl rfl).real R.ψ hRB.inf hU
  obtain ⟨Hc, hHc⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ hC
  have hrd := GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  obtain ⟨B, hB⟩ := hrd.2.2 Ae
  set M : ℝ := max Hc 1 with hM
  set Kc : ℝ := C0 * M ^ Ae * 2 ^ Ae with hKc
  have hKc0 : 0 ≤ Kc := by positivity

  have kb : ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ h ∈ C, ∀ g,
      ‖thetaKO (G.th t i j).ω h g f‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * GlobalTheory.Grow.quotHeight _ g ^ Ae := by
    intro f hf h hh g
    have hM1 : 0 ≤ GlobalTheory.Grow.height _ h := (GlobalTheory.Grow.height_pos _ h).le
    have hMh : GlobalTheory.Grow.height _ h ^ Ae ≤ M ^ Ae := pow_le_pow_left₀ hM1 ((hHc h hh).trans (le_max_left _ _)) Ae
    have h1 : ∀ g', ‖thetaKO (G.th t i j).ω h g' f‖ ≤
        (C0 * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * M ^ Ae) * GlobalTheory.Grow.height _ g' ^ Ae := by
      intro g'
      refine ((hK _ _ _ hω μ 𝓕 hμ f hf).2 h g').trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMh (mul_nonneg hC0 ENNReal.toReal_nonneg))
        (pow_nonneg (GlobalTheory.Grow.height_pos _ g').le _)
    have := GlobalTheory.Grow.norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf.1 h) h1 g
    refine this.trans (le_of_eq ?_)
    rw [hKc]; ring
  set s0 : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hs0
  set Vl : ℝ := (G.meas t i (j + 1)).ν.real (G.meas t i (j + 1)).fd with hVl
  have hVl0 : 0 ≤ Vl := measureReal_nonneg
  have hs00 : 0 ≤ s0 := ENNReal.toReal_nonneg
  set K0 : ℝ := Kc * s0 with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg hKc0 hs00
  set ε1 : ℝ := δ / (3 * (K0 * Vl + 1)) with hε1
  have hε10 : 0 < ε1 := by positivity
  obtain ⟨n1, F, v, hF, happ⟩ := hL1 D R.θ hRB.inf hP (G.V i (j + 1)) φ hφ Ae ε1 hε10
  set B' : ℝ := max B 0 with hB'
  set η : ℝ := δ / (3 * (Kc * (B' + ε1) * Vl + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n2, f, p, hf, hlev, hsob⟩ :=
    hL2 D R.ψ R.θ hRB.inf hω.std false (G.V i j) (G.V i (j + 1)) U hU Φ hΦU μ 𝓕 hμ d η hη0
  have hsob' : (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d
      (Φ - ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l))).toReal < η :=
    ENNReal.toReal_lt_of_lt_ofReal hsob

  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB0 : ∀ g, ‖φ g‖ * GlobalTheory.Grow.quotHeight _ g ^ Ae ≤ B' := fun g => (hB g).trans (le_max_left _ _)
  let e := (finProdFinEquiv : Fin n1 × Fin n2 ≃ Fin (n1 * n2))
  refine ⟨n1 * n2, fun l => f (e.symm l).2, fun l => p (e.symm l).2, fun l => F (e.symm l).1,
    fun l => v (e.symm l).1, fun l => hf _, fun l => hF _, fun h hh => ?_⟩
  have hLCa := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).th t i j hi hj
  have hintl : ∀ l : Fin (n1 * n2), IntegrableOn (fun g => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν := by
    intro l
    obtain ⟨_, _, hall⟩ := hLCa _ (hf (e.symm l).2) _ (hF (e.symm l).1)
    exact (hall _ _ h).1
  rw [← integral_finset_sum _ (fun l _ => hintl l),
    ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hintl l)]
  set Φ' := ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l) with hΦ'
  have hsum : ∀ g, ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g = thetaKO (G.th t i j).ω h g Φ' * ∑ a, F a (v a) g := by
    intro g
    refine (Equiv.sum_comp e.symm (fun ab : Fin n1 × Fin n2 => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f ab.2) (p ab.2)) * F ab.1 (v ab.1) g)).trans ?_
    rw [Fintype.sum_prod_type, hΦ']
    unfold thetaKO
    rw [map_sum, Finset.sum_apply, Finset.sum_mul_sum, Finset.sum_comm]
  have hq : ∀ g, 0 < GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := fun g => pow_pos (GlobalTheory.Grow.quotHeight_pos _ g) _
  have bound : ∀ g, ‖thetaKO (G.th t i j).ω h g Φ * φ g - ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g‖ ≤ K0 * ε1 + Kc * η * (B' + ε1) := by
    intro g
    rw [hsum g]
    have hab : thetaKO (G.th t i j).ω h g Φ - thetaKO (G.th t i j).ω h g Φ' =
        thetaKO (G.th t i j).ω h g (Φ - Φ') := by
      unfold thetaKO; rw [map_sub, Pi.sub_apply]
    have e1 : ∀ a b x y : ℂ, a * x - b * y = a * (x - y) + (a - b) * y := fun a b x y => by ring
    rw [e1, hab]
    have ha : ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := kb Φ hΦU h hh g
    have hxy : ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ ε1 := happ g
    have hd : ‖thetaKO (G.th t i j).ω h g (Φ - Φ')‖ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
      (kb _ hlev h hh g).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsob'.le hKc0) (hq g).le)
    have hy : ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ B' + ε1 := by
      have h3 : ‖∑ a, F a (v a) g‖ ≤ ‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖ := by
        simpa using norm_sub_le (φ g) (φ g - ∑ a, F a (v a) g)
      calc ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae
          ≤ (‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖) * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
            mul_le_mul_of_nonneg_right h3 (hq g).le
        _ = ‖φ g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae +
            ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := add_mul _ _ _
        _ ≤ B' + ε1 := add_le_add (hB0 g) hxy
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖φ g - ∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = K0 * (‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ K0 * ε1 := mul_le_mul_of_nonneg_left hxy hK00
    · rw [norm_mul]
      calc _ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        _ = Kc * η * (‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * η * (B' + ε1) := mul_le_mul_of_nonneg_left hy (by positivity)
  refine (norm_setIntegral_le_of_norm_le_const hvol fun g _ => bound g).trans_lt ?_
  have t1 : K0 * ε1 * Vl ≤ δ / 3 := by
    have h0 : K0 * Vl + 1 ≠ 0 := by positivity
    calc K0 * ε1 * Vl = (K0 * Vl) * ε1 := by ring
      _ ≤ (K0 * Vl + 1) * ε1 := mul_le_mul_of_nonneg_right (by linarith) hε10.le
      _ = δ / 3 := by rw [hε1]; field_simp
  have t2 : Kc * η * (B' + ε1) * Vl ≤ δ / 3 := by
    have h0 : Kc * (B' + ε1) * Vl + 1 ≠ 0 := by positivity
    calc Kc * η * (B' + ε1) * Vl = (Kc * (B' + ε1) * Vl) * η := by ring
      _ ≤ (Kc * (B' + ε1) * Vl + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη0.le
      _ = δ / 3 := by rw [hη]; field_simp
  have : (K0 * ε1 + Kc * η * (B' + ε1)) * Vl = K0 * ε1 * Vl + Kc * η * (B' + ε1) * Vl := by ring
  rw [this]
  linarith

theorem thetaLift_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ :=
  thetaLift_approx_of GlobalTheory.T.cusp_form_uniform_height_approx GlobalTheory.FockApprox.theta_approx_fock

end GlobalTheory.ThetaArrowApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactAction
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KExpLine

section Abstract

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def zeroOn (S : Submodule ℂ (SchwartzMap Y ℂ)) (P : Finset Y) : Submodule ℂ S where
  carrier := {s | ∀ y ∈ P, (s : SchwartzMap Y ℂ) y = 0}
  add_mem' := by
    intro a b ha hb y hy
    simp [ha y hy, hb y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c a ha y hy
    simp [ha y hy]

theorem exists_finset_sep (S : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S] :
    ∃ P : Finset Y, ∀ s ∈ S, (∀ y ∈ P, s y = 0) → s = 0 := by
  classical
  obtain ⟨P, -, hmin⟩ := (measure fun P : Finset Y => Module.finrank ℂ (zeroOn S P)).wf.has_min Set.univ
    ⟨∅, trivial⟩
  refine ⟨P, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (SchwartzMap.ext h)
  have hlt : zeroOn S (insert y P) < zeroOn S P := by
    refine lt_of_le_of_ne (fun a ha z hz => ha z (Finset.mem_insert_of_mem hz)) fun heq => ?_
    have hmem : (⟨s, hs⟩ : S) ∈ zeroOn S P := h0
    rw [← heq] at hmem
    exact hy (hmem y (Finset.mem_insert_self y P))
  exact hmin (insert y P) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem sub_mem_of_hasDerivAt (S T : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S]
    (c d : ℝ → SchwartzMap Y ℂ) (hc : ∀ u, c u ∈ S) (hd : ∀ t, d t ∈ T)
    (hder : ∀ y t, HasDerivAt (fun u => c u y) (d t y) t) : c 1 - c 0 ∈ T := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_sep S
  let E : S →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun s p => (s : SchwartzMap Y ℂ) p
      map_add' := by intro a b; funext p; simp
      map_smul' := by intro a b; funext p; simp }
  have hE : LinearMap.ker E = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    exact Subtype.ext (hP s s.2 fun y hy => congrFun hs ⟨y, hy⟩)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective E hE
  let C : ℝ → (P → ℂ) := fun u p => c u p
  have hCd : ∀ t, HasDerivAt C (fun p => d t p) t := fun t => hasDerivAt_pi.2 fun p => hder p t
  have hLC : ∀ u, L (C u) = ⟨c u, hc u⟩ := fun u => LinearMap.congr_fun hL ⟨c u, hc u⟩
  let ev : SchwartzMap Y ℂ → Y → ℂ := fun g y => g y
  have hcomp : ∀ φ : (P → ℂ) →ₗ[ℂ] ℂ, ∀ t, HasDerivAt (fun u => φ (C u)) (φ (fun p => d t p)) t := fun φ t => by
    have h := (((LinearMap.toContinuousLinearMap φ).restrictScalars ℝ).hasFDerivAt (x := C t)).comp_hasDerivAt t (hCd t)
    simpa [Function.comp_def] using h

  have hdS : ∀ t, ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) = d t := by
    intro t
    ext y
    let evy : S →ₗ[ℂ] ℂ :=
      { toFun := fun s => (s : SchwartzMap Y ℂ) y
        map_add' := by intro a b; simp
        map_smul' := by intro a b; simp }
    have h1 := hcomp (evy ∘ₗ L) t
    have h2 : (fun u => (evy ∘ₗ L) (C u)) = fun u => c u y := by
      funext u
      simp only [LinearMap.comp_apply, hLC u]
      rfl
    rw [h2] at h1
    exact (hder y t).unique h1 |>.symm
  let T' : Submodule ℂ S := T.comap S.subtype
  have hdT : ∀ t, L (fun p => d t p) ∈ T' := fun t => by
    show ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) ∈ T
    rw [hdS t]
    exact hd t
  have key : (⟨c 1, hc 1⟩ : S) - ⟨c 0, hc 0⟩ ∈ T' := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let ψ : (P → ℂ) →ₗ[ℂ] ℂ := φ ∘ₗ T'.mkQ ∘ₗ L
    have hg : ∀ t, HasDerivAt (fun u => ψ (C u)) 0 t := by
      intro t
      have := hcomp ψ t
      have h0 : ψ (fun p => d t p) = 0 := by
        show φ (T'.mkQ (L (fun p => d t p))) = 0
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T').2 (hdT t), map_zero]
      rwa [h0] at this
    have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
    have e1 : ∀ u, ψ (C u) = φ (Submodule.Quotient.mk ⟨c u, hc u⟩) := fun u => by
      show φ (T'.mkQ (L (C u))) = _
      rw [hLC u]
      rfl
    rw [e1, e1] at hconst
    rw [Submodule.Quotient.mk_sub, map_sub, hconst, sub_self]
  exact key

end Abstract

end GlobalTheory.KExpLine

namespace GlobalTheory.KExpLine

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem sub_mem_span_derivs : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f hf f₁ hact
  obtain ⟨hDer, hOp, -, -⟩ := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨γ, hγL, hγ1, hγK⟩ := GlobalTheory.T.exists_oneParameter_in_unitaryArchimedeanMaxCompact F E σ B n X r s hP.base hP.herm k hk
  obtain ⟨S, hSfin, hS⟩ := GlobalTheory.T.theta_pair_polynomial_compact hPr F E σ B n d X W M χX χW om r s r' s' hP f hf
  haveI := hSfin
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let c : ℝ → SInf F (Fin n × Fin d) := fun t => D t f
  have hcP : ∀ t, c t ∈ M.Pol B.ψ B.emb := fun t => hDP t f hf
  have hcA : ∀ t, Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (c t) := fun t => (hD t f hf (c t)).2 rfl
  have hc1 : c 1 = f₁ := ((hD 1 f hf f₁).1 (by rw [hγ1]; exact hact)).symm
  have hc0 : c 0 = f := by
    have h1 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by
      rw [ofAdd_zero, map_one]
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd (0 : ℝ)), 1)) f f := by
      intro ρ _
      rw [h1]
      show om 1 _ = _
      rw [map_one]
      rfl
    exact ((hD 0 f hf f).1 hA).symm
  have hder : ∀ y t, HasDerivAt (fun u => c u y) (Dg (c t) y) t := by
    intro y t
    let ρ := GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)
    let x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (y, 0)
    have hx : (fun i => evI F (x i)) = y := funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv _ _ i
    have hρ : ρ x = 1 := by
      show GlobalTheory.ArchIsom.g0 F (Fin n × Fin d) (fun i => (x i).2) = 1
      have : (fun i => (x i).2) = (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := rfl
      rw [this]
      exact Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts _) _
    have htens : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) ρ x = g y := by
      intro g
      show g (fun i => evI F (x i)) * ρ x = g y
      rw [hx, hρ, mul_one]
    have hom : ∀ u, om (γ (Multiplicative.ofAdd u), 1) (tens (evI F) (⇑f) ρ) = tens (evI F) (⇑(c u)) ρ :=
      fun u => hcA u ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)
    have hsplit : ∀ s', om (γ (Multiplicative.ofAdd (s' + t)), 1) (tens (evI F) (⇑f) ρ) =
        om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) := by
      intro s'
      have e : ((γ (Multiplicative.ofAdd (s' + t)), (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) =
          (γ (Multiplicative.ofAdd s'), 1) * (γ (Multiplicative.ofAdd t), 1) := by
        rw [ofAdd_add, map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, map_mul, Module.End.mul_apply, hom t]
    have h0 := (hDg (c t) (hcP t) (Dg (c t))).2 rfl ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ (c t)) x
    have h0' : HasDerivAt (fun s' => c (s' + t) y) (Dg (c t) y) 0 := by
      have e1 : (fun s' : ℝ => om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) x) =
          fun s' => c (s' + t) y := by
        funext s'
        rw [← hsplit s', hom, htens]
      rw [e1, htens] at h0
      exact h0
    have h2' : HasDerivAt (fun u => c (u - t + t) y) (Dg (c t) y) t := by
      have := h0'
      rw [show (0 : ℝ) = t - t from (sub_self t).symm] at this
      exact this.comp_sub_const t t
    simpa only [sub_add_cancel] using h2'
  rw [← hc1, ← hc0]
  refine sub_mem_of_hasDerivAt S _ c (fun t => Dg (c t)) (fun u => hS _ (hγK _) (c u) (hcA u)) (fun t => ?_) hder
  exact Submodule.subset_span ⟨hDgP _ (hcP t), γ, hγL, c t, hcP t, (hDg (c t) (hcP t) _).2 rfl⟩

end GlobalTheory.KExpLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_siegelTorusElement_le_sobolevSeminorm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (c : ℝ) (hc : 0 < c) (K₀ : Set (WO M X)) (hK₀ : K₀ ∈ nhds (0 : WO M X)) (hK₀c : IsCompact K₀)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO M X → ℂ, IsThetaFunO ψ (sgn ε M) X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ‖ω (a, 1) Ψ 0‖ ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal *
          ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  first | exact @GlobalTheory.SiegelTorusTheta.torus_bound | exact GlobalTheory.SiegelTorusTheta.torus_bound | (intros; apply GlobalTheory.SiegelTorusTheta.torus_bound <;> assumption)
end


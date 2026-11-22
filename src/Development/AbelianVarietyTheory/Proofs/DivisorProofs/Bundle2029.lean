import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnrT
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem eventually_unrT : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (π : CG E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (locParT hT π h).unr := by
  intro hF hT E Ω _ _ _ _ _ _ a π
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  obtain ⟨ah, hah, H⟩ := isRecT_locRecT hT h
  have e : locParT hT (Quotient.mk _ π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
    have h1 : CG.IsLoc (Quotient.mk _ π : CG E a) w (Quotient.mk _ σ) := hσ
    unfold locParT
    rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
    rfl
  rw [e]
  refine (GlobalTheory.RecT.isSpherical_iff_unr_of_lawsT E Ω A w h ah hah _ ((GlobalTheory.RecT.lawsT_iff ah hah _).2 H) _).1 ?_
  refine fixed_ne_bot_of_equiv (equivRep (ParLaws.toRep σ)) ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm

end GlobalTheory.CuspRep.ParLawsT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerCore

open GlobalTheory.PtId

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def serConst (D : D7) (ka : ℂ) (δ : ℤˣ) (d : ℕ) : ℂ :=
  ka * (((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d)

set_option maxHeartbeats 2000000 in

theorem ad_value_core (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (hR : RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t)) (y : (R.HV i (tup t)).H)
    (xs : O.Cl' t → VsV D i O.c'.F) (hpl : Place R i (tup t) h O.c0' y xs) (g' γ : GA D (Wc D i)) (hγ : γ ∈ GQ (Wc D i))
    (X : Data D.host.E D.R.r) (g : ℕ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hX : IsMod (Wc D i) (rank_Wc i) X) (hp : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q)
    (hrt : (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD) (x₀ : Frame X.Ψ D.R.r) (hon : IsONFr X x₀)
    (hinv : IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))))
    (hbas : IsBasOf (Wc D i) (rank_Wc i) X Dc.hr x₀ (onb (R.MW i (sg0 D A))))
    (hΛ : latR (rank_Wc i) (latG (Wc D i) (γ * g')) = X.Λ)
    (mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (ha₂ : MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) (γ * g') mk₂) (v : TF (Vc D i).rank g) (a : ℂ)
    (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    (hrd : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X Dc.bas Dc.idx (R.ωP i (tup t) (1, γ * g') (R.vacP i)) (a • v)
      (frMove R.θ (Wc D i) (rank_Wc i) X (γ * g') x₀))
    (Y : O.Cl' t → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E)
    (hY : ∀ j, IsRoots (O.dδ t).l₂ X.Λ mk₂ (O.Nc t j) (Y j)) :
    R.thF i (tup t) y (v₀ i (sg0 D A)) g' = serConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * a *
      clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
        (fun j => O.io (xs j)) X.Λ v Y (frMove R.θ (Wc D i) (rank_Wc i) X (γ * g') x₀) := by
  let u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hP.lift.v0.1 ρ).2.1⟩
  have hun := GlobalTheory.T.thetaLift_eq_classSum_thetaKernels_lowestKType D G Pl0 T0 A _ R F hC i (tup t) _ (inC O.c') O.c0' _ h _ J' _ _ _ hP.lift.std hR y xs hpl u g'
  refine hun.trans ?_
  rw [clsSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) X hX _ Dc.hr
  have hlt := letters_eq_fockVars_core D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP X g Dc vr hX hp hvr
  have hω := hC.thP.ωP i (tup t)
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      thetaKO (R.ωP i (tup t)) (h j) g' f = thetaKO (R.ωP i (tup t)) (h j) (γ * g') f := fun f hf => by
    have e1 : ((h j, γ * g') : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h j, g') := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  rw [hmove _ (hC.thP.pt_theta i (tup t) _), hka (fun ℓ => vr (Dc.eL ℓ)) hlt u (fun _ => rfl) (tup t) (xs j)]
  obtain ⟨⟨hfin, e, Ps, he, hPs, hsupp⟩, hLh, -⟩ := hR.2.2.2.2.2.2 j
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) (h j)
  obtain ⟨hlev, -, -⟩ := hP.cov t
  obtain ⟨-, cga, hio⟩ := hP.io
  have hH := mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self O.io (xs j))
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io (xs j)))).IsHomogeneous
      (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hhalf : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → (O.dδ t).l₂.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP => by
    obtain ⟨k1, k2, k3⟩ := (hP.tuple t).half
    refine ⟨?_, k3 PP hPP⟩
    rw [hlev.2.2.2.1]
    rcases hPP with hPP | hPP
    · exact Ideal.mul_le_left.trans (k1.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP)))
    · exact Ideal.mul_le_right.trans (k2 PP hPP)
  have hla : ∀ w, w ∈ (O.La t j).La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) (h j)) := fun w => by
    rw [← hLh]
    exact (hP.reps t).2 j w
  have hcl := hδ (tup t) (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) (hP.tuple t).phi hhalf hrt g _ X Dc.hr Dc.bas Dc.idx x₀ vr hX
    Dc.sympl hon hinv hbas hvr (O.bad t) (O.Nc t j) (h j) (γ * g') (O.La t j) mk₂ e Ps yd hR.2.1 he hPs hfin hsupp hyd hla
    ((hP.reps t).1 j).2.2.1 ((hP.reps t).1 j).2.2.2.1 ha₂ (Y j) (hΛ ▸ hY j) v a (hΛ ▸ hv) hrd _ _ hhom
  have hep := GlobalTheory.ClassScalarValueCore.class_scalar_value_core D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP t j (h j) e Ps yd he hPs hsupp hyd hLh hR.2.1
  have hw : hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) = fun q => inC O.c' (O.w t j q) := funext fun q =>
    (PairModel.hatC_phiHat (O.dδ t).c₂ (fun x => (O.dδ t).eF (O.φ t x)) q).symm.trans
      (congrArg (inC (O.dδ t).c₂) (hP.w t j q).symm)
  rw [← hep, hw, hΛ, MvPolynomial.rename_rename] at hcl
  have hsm : ∀ f, thetaKO (R.ωP i (tup t)) (h j) (γ * g') (ka • f) = ka * thetaKO (R.ωP i (tup t)) (h j) (γ * g') f :=
    fun f => by rw [thetaKO, thetaKO, map_smul]; rfl
  rw [hsm]
  refine (congrArg (fun z => inC O.c' (O.vol t * ((O.gam t j : O.c'.F))⁻¹) * (ka * z)) hcl).trans ?_
  simp only [serConst, map_mul, map_inv₀, map_natCast]
  ring

set_option maxHeartbeats 2000000 in

theorem exact_identity_core (hC : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) {c0 : ℂ} (hc : CovAt O c0) {cst : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hcc : CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
      (R.ωP i A.μ0) (R.vacP i) cst)
    (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (hR : RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t)) (y : (R.HV i (tup t)).H)
    (xs : O.Cl' t → VsV D i O.c'.F) (hpl : Place R i (tup t) h O.c0' y xs) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c')
    (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) (g' : GA D (Wc D i)) :
    c0 * R.thF i (tup t) y (v₀ i (sg0 D A)) g' = serConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) *
      cst (O.dict g').1 * (O.mu g' * rdU (unfO O) f (O.dict g').1 (O.dict g').2) := by
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := hs ▸ T.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs
  obtain ⟨hemb, -, hroot, hmk⟩ := dict_cast T hT.laws _ (inR i) O.s0 hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨hX, hon, hinv, hp, hrk, hpq, h1, hrt, -, hbas, hD, -⟩ := hmod (O.dict g').1
  have hU : IsUnf (unfO O) := GlobalTheory.OneMapAll.isUnf_unfExt O.hle (inC O.c') (fun _ => rfl) (hT.laws.unf _ (inR i) O.s0 hσ)
  obtain ⟨hx, g, Dc, γ, mk, v, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hv, hκ, hrd⟩ :=
    exists_point (unfO O) hσ hU h1 hT.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) O.dict (iotaW T i)
      (T.x₀ ((i : ℕ) + 1) O.s0)
      (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, Wt.isom, Wt.pt⟩ k)
      (wtA (κ i)) hD O.mu (R.ωP i A.μ0) (R.vacP i) cst (CcIs.unfBC _ _ _ _ O.hle _ (inC O.c') _ _ _ _ _ _ hcc) g'
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  obtain ⟨xk, hxk⟩ := hroot (γ * g')
  have hlev := (hP.cov t).1
  obtain ⟨mk₂, hm₂, ha₂, hov⟩ := GlobalTheory.AdMark.exists_marking D _ _ T.Q.l (O.dδ t).l₂ (Wc D i) _ (rank_Wc i) (iotaW T i) hemb
    (hlev.2.1 ▸ dvd_mul_right _ _) (hlev.2.2.2.1 ▸ Ideal.mul_le_left) (γ * g')
  rw [hΛ] at hm₂ hov
  have hM : 0 < (O.dδ t).l₂.M := lt_of_lt_of_le (by norm_num) (O.dδ t).l₂.three_le
  choose Y hY using fun j : O.Cl' t => (DualMark.dual_marking _ _ _ (O.dδ t).l₂ _ _ _ mk₂ _ hsd hm₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank (O.Nc t j) ((hP.reps t).1 j).2.2.2.1.1.pos
  have hgeo := geo_value hT O hP hc t _ g Dc (γ * g') xk hxk hX hp hpq hrk hD.2 hΛ hsd _ hx hfr mk mk₂ hm hm₂ ha₂
    (hov mk hm.mem hma) v ϑ κ' hv hκ Y hY xs f hf _ B hBm hϑ
  have htw := GlobalTheory.AdThCore.weil_twist_base D G Pl0 T0 A _ R F hC i (tup t) (γ * g') xk hxk (R.vacP i) (hC.thP.vP i (tup t)).1.2.theta
  have hrd' : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) ((unfO O).X (O.dict g').1) Dc.bas Dc.idx
      (R.ωP i (tup t) (1, γ * g') (R.vacP i)) ((((R.xi (tup t) xk : Circle) : ℂ) * (cst (O.dict g').1 * O.mu g' * κ')) • v)
      (O.dict g').2 := by
    obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ _ g _ _ Dc.bas Dc.idx Dc.sympl hD.2 _ hx _ hrd.1).2.2 v hv.1).1
      ((R.xi (tup t) xk : Circle) : ℂ) 0
    rw [zero_smul, add_zero, smul_smul] at s1 s2
    rw [zero_smul, add_zero] at s2
    refine ⟨s1, fun w hw => ?_⟩
    rw [htw, s2, Pi.smul_apply, Pi.smul_apply, hrd.2 w hw, smul_eq_mul, smul_eq_mul]
    ring
  have had := ad_value_core hC hT O hP hka hδ t h J' hR y xs hpl g' γ hγ _ g Dc hX hp hrt _ hon hinv (hbas _) hΛ mk₂ ha₂ v _ hv
    (hfr ▸ hrd') Y hY
  have hrdU : rdU (unfO O) f (O.dict g').1 (O.dict g').2 = _ := (dif_pos hx).trans hgeo
  have e1 := congrArg (clsSum (inC O.c') ((unfO O).X (O.dict g').1) Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t)
    (O.vol t) (O.ep t) (fun j => O.io (xs j)) ((unfO O).X (O.dict g').1).Λ v Y) hfr
  rw [had.trans (congrArg (fun z => _ * z) e1.symm), hrdU]
  ring

end

theorem lieFac_eq_sqrt_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ GlobalTheory.PtId.degW Dw a := by
  have h : 0 < 2 * Real.pi * x := by positivity
  have e : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(Real.log (2 * Real.pi * x) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  rw [e, ← Real.exp_nat_mul, lieFac, GlobalTheory.PtId.degW]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1000000 in

theorem exists_serOf_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro _ D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hI i Tp tup O hP cc hcc
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.PtId.dict_cast T hT.laws _ (inR i) O.s0 (hs ▸ T.toCore.good_σ₀) (Wc D i) O.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.thetaKernel_oneClass_eq_classicalShortSeries D G Pl0 T0 A _ R F hR i hP.lift.std _ _ (iotaW T i) h1 h2
  obtain ⟨ka, hka, hio⟩ := GlobalTheory.T.fockCoefficientMap_extremal_eq_phase_smul_letters D G Pl0 T0 A T R F κ v₀ hR hT hI i Tp tup O hP
  obtain ⟨c0, hc0, hcov⟩ := GlobalTheory.AdTh.CoverVal.cover_value_core D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP
  have hd : ‖((δ : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> simp
  have hu : ‖ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹‖ = 1 := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_inv, hka, hc0, hd]
    simp
  refine ⟨_, hu, fun k => ?_, norm_one, fun t h J' hrep y x hpl f _ hf g => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hu, hcc.1 k, one_mul]
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (hc0 ▸ one_ne_zero)
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have key := exact_identity_core hR hT O hP hio hδ hcov hcc t h J' hrep y x hpl f hf g
  refine mul_left_cancel₀ hne ?_
  rw [one_mul, key, lieFac_eq_sqrt_pow _ hx, serConst, Pi.smul_apply, smul_eq_mul, neg_pow]
  have hre : rdU (GlobalTheory.PtId.unfO O) f (O.dict g).1 (O.dict g).2 =
      rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 := rfl
  rw [hre]
  generalize rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2 = z
  rw [Complex.ofReal_pow, Complex.ofReal_inv]
  generalize ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) = s
  have e : c0 * c0⁻¹ = 1 := mul_inv_cancel₀ hne
  linear_combination (-(ka * ((-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * ((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * cc (O.dict g).1 * s * O.mu g * z)) * e

end GlobalTheory.AdTh.SerCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseKernel
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnCmp

open Classical in

theorem exists_baseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∃ ω φ, IsBaseKernel R i v (ownAt D v) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu
  obtain ⟨ψw, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hδ : R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = R.xiH (R.mu v) * ψw⁻¹ := by rw [hxi, mul_inv_cancel_right]
  have htame : ∀ P, (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TameAt P := by
    intro P
    unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
    intro x hx hle
    rw [hδ, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hL.xi_tame (R.mu v) P x hx hle, hψ.tame P x hx hle,
      inv_one, mul_one]
  have htriv : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TrivOn D.host.F := by
    rw [hδ]; exact (hL.xi_triv (R.mu v)).mul hψ.triv.inv
  have hunit : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).IsUnitary := by
    obtain ⟨n, hn, hno⟩ := hL.xi_fin (R.mu v)
    obtain ⟨a, ha⟩ := hψ.ord
    refine Formalism.L2.Host.HChar.isUnitary_of_order (n := n * Formalism.EigenvalueLevelCeiling.plc v ^ a)
      (Nat.mul_pos hn (pow_pos (Formalism.EigenvalueLevelCeiling.plc_prime v).pos a)) ?_
    show _ ^ (n * _) = 1
    rw [hδ, mul_pow, inv_pow, pow_mul, hno, one_pow, one_mul, mul_comm n, pow_mul, ha, one_pow, inv_one]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CharTransport.exists_chrEq D _ hunit
  have hF : ∀ a, χ (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hχ htriv
  have hr0 : ResEta D χ 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ a => by rw [hF a, pow_zero]⟩
  have h0 := hC.thP.ωP i A.μ0
  obtain ⟨ω, hω, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D R.ψ h0.std _ _ _ _ χ χ _ h0 hχ.1 hχ.1 hr0 hr0
  have hx0 : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  have hω' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
    convert hω using 2
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
      exact mul_right_comm _ _ _
  choose ξR hξR using fun PP => GlobalTheory.exists_isRes_of_tameAt D _ PP (htame PP)
  have hsub : placesOver R (R.mu v) (ownAt D v) ⊆ R.Q (R.mu v) := Finset.filter_subset _ _
  obtain ⟨e0, he0, -⟩ := (hC.thP.vP i (R.mu v)).2
  have hsub' : R.Pg ∪ placesOver R (R.mu v) (ownAt D v) ⊆ R.Pg ∪ R.Q (R.mu v) := Finset.union_subset_union le_rfl hsub
  have hnc : ∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ P' ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v),
      ¬ Lev.IsConjPl P P' := fun P hP P' hP' =>
    GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0 P (hsub' hP) P' (hsub' hP')
  obtain ⟨cV, hcV⟩ := hL.βV i
  obtain ⟨cW, hcW⟩ := hL.βW i
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i)
    (R.ΛW i) (R.βV i) (R.βW i) R.Pg (placesOver R (R.mu v) (ownAt D v)) ξR (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcV)
    (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcW) hcV.1 hcW.1 ((Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL (R.mu v)).mono_right hsub)
    (Formalism.IndefR.Fin.idemSum_of_noConj _ hnc) (R.vacP i) (hC.thP.vP i (R.mu v)).1
  refine ⟨ω, φ, ?_⟩
  unfold IsBaseKernel IsKernel
  exact ⟨χ, ξR, hχ, fun PP _ => hξR PP, hω', hφ⟩

end GlobalTheory.OnCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorRationalMatricesInBox
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaConv

theorem exists_den_of_inBox : ∀ (D : D7) (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ (x : Mx D m n) (ξ : Matrix (Fin m) (Fin n) D.host.E), x.map (finPart D) = (ξ.map (incA D) : Mx D m n).map (finPart D) → GlobalTheory.Unf.InBox K x → ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j) := by
  intro D m n K hK
  have hK1 : IsCompact (⋃ p : Fin m × Fin n, (fun x : Mx D m n => x p.1 p.2) '' K) :=
    isCompact_iUnion fun p => hK.image (continuous_id.matrix_elem p.1 p.2)
  obtain ⟨L, hL, h⟩ := GlobalTheory.T.rational_finPart_in_compact_bounded_denominator D _ hK1
  refine ⟨L, hL, fun x ξ hx ⟨k, hk, hxk⟩ i j => ?_⟩
  refine h (k i j) (Set.mem_iUnion.2 ⟨(i, j), k, hk, rfl⟩) (ξ i j) ?_
  have h1 : finPart D (x i j) = finPart D (incA D (ξ i j)) := congrFun (congrFun hx i) j
  have h2 : finPart D (x i j - k i j) = 0 := congrFun (congrFun hxk i) j
  have h3 : finPart D (x i j) - finPart D (k i j) = 0 :=
    ((finPart D).map_sub (x i j) (k i j)).symm.trans h2
  exact h1.symm.trans (sub_eq_zero.1 h3)

end GlobalTheory.ThetaConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.BumpShintani

theorem map_comp_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  ext i j; rfl

theorem pInf_tl {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, _, rfl⟩ := hx
  simp

theorem loc_tl {E : Type} [Field E] [NumberField E] {a : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ l.support) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hne : v ≠ w := fun h => hv (h ▸ (Finset.mem_toList.1 hw))
  simp only [Function.comp_apply, map_comp_eq, pFin_finGL]
  exact pLoc_locGL_of_ne hne _

theorem exists_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  intro E _ _ _ m S hcond
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m S
  refine ⟨b, hb1, hbN, hbC, ?_⟩
  intro π α hSat
  obtain ⟨φ, hφV, hφK, hφx⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π α hSat
  obtain ⟨F, hFV, hFb, hFU, hFinv, hFeig⟩ := GlobalTheory.T.kirillov_semilocal_smooth_bump E m S b hbN hbC hbU hbS π φ hφV hφx
  refine ⟨F, hFV, hFU, ?_, ?_⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g') (hφK w hw k hk)
  · intro ϖ hϖ l hl p hp
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π α hSat φ hφV hφK ϖ hϖ l hl
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 :=
      fun w hw => loc_tl ϖ l w (fun h => hl w h hw)
    rw [hFeig _ _ (pInf_tl ϖ l) hS hC p hp.1, hFb p hp, mul_comm]

end GlobalTheory.JSW.BumpShintani
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCoreStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameConstants_of_characterisationCore : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  first | exact @GlobalTheory.AdTh.CcExCore.exists_ccIs_core | exact GlobalTheory.AdTh.CcExCore.exists_ccIs_core | (intros; apply GlobalTheory.AdTh.CcExCore.exists_ccIs_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsBottomOfIsCoprime
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.SqNum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem exists_isBottom_of_isCoprime (hL : L.Is μ₀) (G : GridData L sc)
    (hm : IsCoprime (condE G.pl) D.host.𝔟) (hm' : IsCoprime (D.host.conj • condE G.pl) D.host.𝔟) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' := by
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D ⊤ δ hδ).1
  refine ⟨δ, t0, fun i j => ?_⟩
  obtain ⟨χν, hν, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨χβ, hβ⟩ := exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := exists_heckeU_alphaH hL G i j
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_reference_tuple hL G hm hδ ht i j χβ hβ χν hν hw
  obtain ⟨P', h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_reference_tuple hL G hm' hδ ht i j χα hα χν hν hw
  exact ⟨P, P', ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

theorem exists_isBottom (hL : L.Is μ₀) (G : GridData L sc) (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' :=
  exists_isBottom_of_isCoprime hL G (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).1
    (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).2

end GlobalTheory.FunObj.SqNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepthStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_row_of_dictionary_depth : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinRowK := by
  first | exact @GlobalTheory.SumSize.finRowK | exact GlobalTheory.SumSize.finRowK | (intros; apply GlobalTheory.SumSize.finRowK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAction_isLocallyBlockUnitary : ∀ P Q R S : ℕ, LocU (fun a : Ix R S => a.isLeft) (units (fockAct2 P Q R S)) := by
  first | exact @GlobalTheory.HoweR.fock_locU | exact GlobalTheory.HoweR.fock_locU | (intros; apply GlobalTheory.HoweR.fock_locU <;> assumption)
end


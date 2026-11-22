import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMapExtension
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def cmpConst (D : D7) (ka : ℂ) (δ : ℤˣ) (d : ℕ) : ℂ :=
  ka * (((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d)

set_option maxHeartbeats 2000000 in

theorem ad_value (hC : R.Char F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
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
    R.thF i (tup t) y (v₀ i (sg0 D A)) g' = cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * a *
      clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
        (fun j => O.io (xs j)) X.Λ v Y (frMove R.θ (Wc D i) (rank_Wc i) X (γ * g') x₀) := by
  let u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hP.lift.v0.1 ρ).2.1⟩
  have hun := GlobalTheory.T.oscillator_model_values_fourth D G Pl0 T0 A _ R F hC i (tup t) _ (inC O.c') O.c0' _ h _ J' _ _ _ hP.lift.std hR y xs hpl u g'
  refine hun.trans ?_
  rw [clsSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) X hX _ Dc.hr
  have hlt := letters_eq_fockVars D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP X g Dc vr hX hp hvr
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
  have hep := GlobalTheory.T.oscillator_model_values_third D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP t j (h j) e Ps yd he hPs hsupp hyd hLh hR.2.1
  have hw : hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) = fun q => inC O.c' (O.w t j q) := funext fun q =>
    (PairModel.hatC_phiHat (O.dδ t).c₂ (fun x => (O.dδ t).eF (O.φ t x)) q).symm.trans
      (congrArg (inC (O.dδ t).c₂) (hP.w t j q).symm)
  rw [← hep, hw, hΛ, MvPolynomial.rename_rename] at hcl
  have hsm : ∀ f, thetaKO (R.ωP i (tup t)) (h j) (γ * g') (ka • f) = ka * thetaKO (R.ωP i (tup t)) (h j) (γ * g') f :=
    fun f => by rw [thetaKO, thetaKO, map_smul]; rfl
  rw [hsm]
  refine (congrArg (fun z => inC O.c' (O.vol t * ((O.gam t j : O.c'.F))⁻¹) * (ka * z)) hcl).trans ?_
  simp only [cmpConst, map_mul, map_inv₀, map_natCast]
  ring

set_option maxHeartbeats 2000000 in

theorem exact_identity (hC : R.Char F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) {c0 : ℂ} (hc : CovAt O c0) {cst : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hcc : CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
      (R.ωP i A.μ0) (R.vacP i) cst)
    (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (hR : RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t)) (y : (R.HV i (tup t)).H)
    (xs : O.Cl' t → VsV D i O.c'.F) (hpl : Place R i (tup t) h O.c0' y xs) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c')
    (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) (g' : GA D (Wc D i)) :
    c0 * R.thF i (tup t) y (v₀ i (sg0 D A)) g' = cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) *
      cst (O.dict g').1 * (O.mu g' * rdU (unfO O) f (O.dict g').1 (O.dict g').2) := by
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := hs ▸ T.toCore.good_σ₀
  have hmod := models_at_record D G Pl0 T0 A T R F κ v₀ hC hT i O.s0 hs
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
  have htw := GlobalTheory.T.theta_action_determinant_root D G Pl0 T0 A _ R F hC i (tup t) (γ * g') xk hxk (R.vacP i) (hC.thP.vP i (tup t)).1.2.theta
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
  have had := ad_value hC hT O hP hka hδ t h J' hR y xs hpl g' γ hγ _ g Dc hX hp hrt _ hon hinv (hbas _) hΛ mk₂ ha₂ v _ hv
    (hfr ▸ hrd') Y hY
  have hrdU : rdU (unfO O) f (O.dict g').1 (O.dict g').2 = _ := (dif_pos hx).trans hgeo
  have e1 := congrArg (clsSum (inC O.c') ((unfO O).X (O.dict g').1) Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t)
    (O.vol t) (O.ep t) (fun j => O.io (xs j)) ((unfO O).X (O.dict g').1).Λ v Y) hfr
  rw [had.trans (congrArg (fun z => _ * z) e1.symm), hrdU]
  ring

theorem cmpConst_ne_zero {ka : ℂ} (hka : ka ≠ 0) (δ : ℤˣ) (d : ℕ) : cmpConst D ka δ d ≠ 0 := by
  have h1 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have h2 : ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  have h3 : ((δ : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 δ.ne_zero
  exact mul_ne_zero hka (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ (inv_ne_zero h2)))

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem ccIs_transport {θ : InfFam D} {V W : HSp D} {hr : W.rank = D.R.r} {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ')
    (hV : T.V j σ = W) (hV' : T.V j σ' = W) {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ}
    {cst : (T.U j σ).Comp → ℂ}
    (h : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.x₀ j σ) om f₀ cst) :
    ∃ cst' : (T.U j σ').Comp → ℂ,
      CcIs θ V W hr (T.U j σ') (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.x₀ j σ') om f₀ cst' ∧
      ∀ g, cst' (castDict hV' (T.dict j σ') g).1 = cst (castDict hV (T.dict j σ) g).1 := by
  subst e
  exact ⟨cst, h, fun _ => rfl⟩

set_option maxHeartbeats 2000000 in
open Formalism.L2.DIV GlobalTheory.OneMapTuples in

theorem point_identity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨tie⟩ _ hio i lev gramR c0R c0L _
  have hT : TieIn T R κ v₀ := ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨fun _ => 1, 1, fun _ => one_ne_zero, fun Tp tup O _ hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := GlobalTheory.T.exists_level_of_linear_map D G Pl0 T0 A T R F κ v₀ hC hT hio i (c0L i)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.oscillator_model_exists_ccIs_of_pins GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC hT i Tp₀ tup₀ O₀ hP₀
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.lattice_isometry_sign_third D G Pl0 T0 A _ R F hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  refine ⟨fun q => cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * c₀ (O₀.dict q.out).1, 1, fun q => ?_, ?_⟩
  · exact mul_ne_zero (cmpConst_ne_zero (norm_ne_zero_iff.1 (hka1 ▸ one_ne_zero)) _ _)
      (norm_ne_zero_iff.1 (hc₀.1 _ ▸ one_ne_zero))
  intro Tp tup O _ hP _ hbc c0 hxi t
  obtain ⟨cst, hcst, hceq⟩ := ccIs_transport (hs₀.trans (sOv_eq _ O.c' O.hle).symm) O₀.hV O.hV hc₀
  refine ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx f hf hcl q => ?_⟩
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hP.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := exact_identity hC hT O hP (hka Tp tup O hP hbc) hδ
    (GlobalTheory.T.omega_data_pinned_forms D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP c0 hxi) hcst t h J' hR _ x hx₀ f hcl q.out
  rw [rdQ, h1, hA _ x hx₀, one_mul]
  exact h2.trans (congrArg (fun z => _ * z * _) (hceq q.out))

end GlobalTheory.PtId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoTies

def BarAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (jf : T.cuspA j (wtA w) w.n → Hm.H) (Z : Prop) : Prop :=
  ¬ GoodEmb T.Q.c s → ∀ hV : T.V j ((starRingEnd ℂ).comp s) = W,
    ((∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) →
      ∃ v : M.Vec, IsUnitV v ∧ ∀ f, Hm.e (jf f) v = fun g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g)) ∧
    (¬ (∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) → Z)

theorem barTie_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) :
    BarTie t ↔ ∀ (i : Fin D.R.m) σ, BarAtOne T ((i : ℕ) + 1) (κ i) (res T σ) (R.MW i σ) (R.HW i σ) (fun f => t.jK i σ f) ((R.FW i).j σ = 0) :=
  Iff.rfl

theorem BarAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm)
    (jf : T.cuspA j (wtA w) w.n → Hm.H) (jf' : T'.cuspA j (wtA w') w'.n → Hm'.H)
    (hj : ∀ f f', HEq f' f → HEq (jf' f') (jf f)) {Z Z' : Prop} (hZ : Z → Z') :
    BarAtOne T j w s M Hm jf Z → BarAtOne T' j w' s' M' Hm' jf' Z' := by
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hH' : Hm' = Hm := eq_of_heq hH
  subst hH'
  have hj' : jf' = jf := funext fun f => eq_of_heq (hj f f HEq.rfl)
  subst hj'
  intro h hg hV
  exact ⟨(h hg hV).1, fun h' => hZ ((h hg hV).2 h')⟩

theorem reading_eq_zero {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hn : n = n')
    {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) (j' : (Fin n' → L') →ₛₗ[σ'] A')
    (h : ∀ x x', CrdOver ι x x' → HEq (j' x') (j x)) (h0 : j = 0) : j' = 0 := by
  subst hn
  subst h0
  have hz : HEq (j' 0) (0 : A) := h 0 0 ⟨rfl, fun k k' _ => (map_zero ι).symm⟩
  have hk : ∀ k, j' (Pi.single k 1) = 0 := fun k => by
    have h1 : HEq (j' (Pi.single k 1)) (0 : A) := h (Pi.single k 1) (Pi.single k 1) ⟨rfl, fun a b hab => by
      obtain rfl : a = b := Fin.ext hab
      by_cases hak : a = k
      · subst hak
        simp
      · simp [Pi.single_apply, hak]⟩
    exact (eq_of_heq (h1.trans hz.symm)).trans (map_zero j')
  refine LinearMap.ext fun x => ?_
  rw [pi_eq_sum_univ' x, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smulₛₗ, hk, smul_zero]

theorem barTie_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
        GeoTies.MWOver z.R.toRealDat R'.toRealDat → BarTie fw' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hpins hRS κ' hκ v₀' fw' hcrd hMW
  letI := alg'
  letI := z.alg
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hE.1) :))
  refine (barTie_iff fw').2 fun i' σ' => ?_
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (by with_unfolding_all exact ((enlEmb hE.2.2.2) :))
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))
  have hb := (barTie_iff z.geo.fw).1 z.geo.bar i (σ'.comp ι)
  have hMM := hMW i i' hi ι hι σ'
  have hnW := hRS.1.2.2.2.2.2.1
  have hcl := ((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hH := hcl.2.1
  have hjj := hcl.2.2.2
  have hs : ∀ (y : z.core.Q.c.F) (y' : core'.Q.c.F), (y' : ℂ) = (y : ℂ) →
      res core' σ' y' = res z.core (σ'.comp ι) y := fun y y' hy =>
    congrArg σ' ((w'.st Z').toD7.what₂.embLL.injective
      (((by with_unfolding_all exact ((halg y') :)) : (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y') = (y' : ℂ)).trans
        (hy.trans ((hι _).trans ((by with_unfolding_all exact ((z.alg_eq y) :)) :
          (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))).symm)))
  have hgen : ∀ {m m' : ℕ} (_ : m' = m) (a : Fin m → ℕ) (a' : Fin m' → ℕ), HEq a' a → ∀ (k : Fin m) (k' : Fin m'),
      (k : ℕ) = k' → a k = a' k' := by
    intro m m' h a a' ha k k' hk
    subst h
    cases ha
    rw [Fin.ext hk]
  have hn : z.R.nW i = R'.nW i' := hgen hm _ _ hnW i i' hi
  have hj : ∀ φ φ', HEq φ' φ → HEq (fw'.jK i' σ' φ') (z.geo.fw.jK i (σ'.comp ι) φ) := fun φ φ' hφ =>
    hjj _ _ ⟨hn, fun k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hcrd i i' hi φ φ' hφ k k' hk).trans (hι _).symm)⟩
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  have h1 := hE.1
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (by with_unfolding_all exact (z.core.Q.H :)), l := (by with_unfolding_all exact (z.core.Q.l :)), c := (by with_unfolding_all exact (z.core.Q.c :)), Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (σ'.comp ι)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).H :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_gram :)))
  let H₀ : Links.HMod (MMap M₀) := (by with_unfolding_all exact ((z.R.HW i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let j₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → H₀.H := (by with_unfolding_all exact ((fun φ => z.geo.fw.jK i (σ'.comp ι) φ) :))
  exact BarAtOne.congr core₀ core' ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :))) ((by with_unfolding_all exact (c4 :))) ((by with_unfolding_all exact (c5 :))) ((by with_unfolding_all exact (c6 :))) ((by with_unfolding_all exact (c7 :))) ((by with_unfolding_all exact (c8 :))) ((by with_unfolding_all exact (c9 :))) ((by with_unfolding_all exact (c10 :)))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((by with_unfolding_all exact (hP :))) ((by with_unfolding_all exact (hM :))) ((by with_unfolding_all exact (hnn :))) s₀ (res core' σ') ((by with_unfolding_all exact (hs :))) M₀ (R'.MW i' σ') ((by with_unfolding_all exact (hMM :)))
    H₀ (R'.HW i' σ') ((by with_unfolding_all exact (hH :))) j₀ _ ((by with_unfolding_all exact (hj :))) hZ ((by with_unfolding_all exact (hb :)))

end GlobalTheory.Mem.R3.Rw.GeoTies
end
end


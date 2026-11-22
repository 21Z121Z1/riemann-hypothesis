import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0326
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueCharIsOfFinOrder
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharOrder

theorem prod_isOfFinOrder {ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, IsOfFinOrder (f i)) :
    IsOfFinOrder (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one h

theorem residue_char_isOfFinOrder {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E)
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (u : (Formalism.L2.DIV.kP PP)ˣ) : IsOfFinOrder (χ u) := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact χ.isOfFinOrder (isOfFinOrder_of_finite u)

theorem levFn_flag1_isOfFinOrder {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    IsOfFinOrder (Formalism.L2.DIV.levFn β (flag1L L) x) := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1]
  refine (IsOfFinOrder.one.mul ?_).mul ?_
  · exact prod_isOfFinOrder _ _ fun PP _ => prod_isOfFinOrder _ _ fun c _ => residue_char_isOfFinOrder PP _ _
  · exact prod_isOfFinOrder _ _ fun PP _ => residue_char_isOfFinOrder PP _ _

theorem levEnv_chi_isOfFinOrder : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), IsOfFinOrder ((levEnv V β L).χ k) := by
  intro D V β L k
  exact levFn_flag1_isOfFinOrder V β L _

end GlobalTheory.LevelCharOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cx_eq_zero {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (hZ : X.RatZ) (j : Bs.J) (t : Bs.Tup) (f : A.FL j t)
    (hf : ∀ z ∈ X.Zl j t, inner ℂ (X.jL j t z) (X.jL j t f) = 0) : X.θ' j t (X.jL j t f) = 0 := by
  have h1 : ∀ y ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)), inner ℂ y (X.jL j t f) = 0 := by
    rw [← hZ.2 j t]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨z, hz, rfl⟩ := hy; exact hf z hz
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have h2 := h1 _ ⟨X.θ' j t (X.jL j t f), rfl⟩
  rwa [LinearMap.adjoint_inner_left, inner_self_eq_zero] at h2

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_jV (hM : R.IsModels) (i : Fin D.R.m) (t : T0) (x y : (A.MtCSD i t).Forms) :
    inner ℂ (jVx R i t x) (jVx R i t y) = D.what₂.embLL ((A.MtCSD i t).csum x.1 y.1) :=
  ((hM.HV i t).2.2 (jVx R i t x) (jVx R i t y)).trans
    ((congrArg₂ (Bridge.adInner _ _ _) (hM.jV i t x) (hM.jV i t y)).trans (GlobalTheory.PresBasic.isom (R.B.L i t).pres x y))

theorem thG_eq_zero (hM : R.IsModels) (hZ : R.LRatZ F) (i : Fin D.R.m) (t : T0) (f : (A.MtCSD i t).Forms)
    (hf : ∀ z : (A.MtCSD i t).Forms, z ∈ liftSub R F i t → (A.MtCSD i t).csum z.1 f.1 = 0) :
    R.thG i t (jVx R i t f) = 0 :=
  cx_eq_zero (R.toCx F) hZ i t f fun z hz =>
    (congrArg (cj (twAt D.what₂.embLL A.v0)) ((inner_jV hM i t z f).trans
      ((congrArg D.what₂.embLL (hf z hz)).trans (map_zero _)))).trans (map_zero _)

theorem jVx_sub (i : Fin D.R.m) (t : T0) (x y : (A.MtCSD i t).Forms) :
    jVx R i t (x - y : (A.MtCSD i t).Forms) = jVx R i t x - jVx R i t y := map_sub (R.jV i t) x y

theorem thG_good {s : ℕ} (hOk : A.fam.Ok s) (hM : R.IsModels) (hS : R.LStable F) (hZ : R.LRatZ F) (i : Fin D.R.m) (t : T0)
    (x : Fin (srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) :
    R.thG i t (jVx R i t (srcForm A i t F.P0 F.ψ0⁻¹
      (((A.MtCSD i t).lvlOp (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ (idemOf A.X)).mulVec x))) =
    R.thG i t (jVx R i t ((A.fam.L i t).toF (liftLvl F) (liftSub R F i t)
      (((A.fam.L i t).lPr (liftLvl F) (liftSub R F i t)).mulVec x))) := by
  refine sub_eq_zero.1 ((map_sub (R.thG i t) _ _).symm.trans ((congrArg (R.thG i t) (jVx_sub i t _ _).symm).trans ?_))
  refine thG_eq_zero hM hZ i t _ fun z hz => ?_
  have h := orth_good_sub_proj (OntoChain.blockHyp (F := F) hOk i t) (Z := liftSub R F i t)
    (fun g => hS.2 i t (Sum.inr g)) x ⟨z, hz, rfl⟩
  rw [CyclotomicLifting.hform_eq_csum, CSD.I_apply, CSD.I_apply, map_sub] at h
  unfold BlockDat.fE at h
  rw [← Matrix.mulVec_mulVec] at h
  refine Eq.trans (congrArg₂ (fun a b => (A.MtCSD i t).csum a b) ?_ rfl) h
  exact congrArg Subtype.val ((A.MtCSD i t).basis.equivFun.symm_apply_apply z).symm

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem adForm_injective (hM : R.IsModels) (hU : R.LUnif) (i : Fin D.R.m) : Function.Injective (adForm R i) := by
  refine (hM.HW i _).1.comp ((injective_iff_map_eq_zero ((R.FW i).j (sg0 D A))).2 fun x hx => ?_)
  by_contra hne
  exact ((hU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hx

theorem adForm_eOp (hU : R.LUnif) (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) :
    adForm R i ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) x) =
      Mult.postOn _ (R.eWf i (sg0 D A)) (adForm R i x) := by
  unfold adForm
  rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  simp only [map_smulₛₗ, RingHom.id_apply, (hU i (sg0 D A)).2.2, smul_smul]
  have e : ∀ g, (sg0 D A) ((idemOf A.X).coeff g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) *
      (sg0 D A) (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = RealDat.eC (A := A) (sg0 D A) g := fun g => by
    rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]; rfl
  simp only [e]
  refine MultilinearMap.ext fun v => ?_
  rw [sum_apply]
  show _ = (R.eWf i (sg0 D A)) ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x) v)
  unfold RealDat.eWf gaL
  rw [LinearMap.sum_apply]
  rfl

theorem eOp_classSum {s : ℕ} (hOk : A.fam.Ok s) (hM : R.IsModels) (hP : R.IsThP) (hU : R.LUnif) (hS : R.LStable F)
    (hZ : R.LRatZ F) (h5 : R.LTheta F) (hr : R.LRatTh F) (i : Fin D.R.m) (t : T0) (a : D.what₂.LL)
    {θ : (Fin (srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t F.P0 F.ψ0⁻¹ (D.what₂.embLL a) θ) (x : Fin (srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) :
    (R.FW i).eOp (fun g => (idemOf A.X).coeff g)
      (θ (((A.MtCSD i t).lvlOp (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ (idemOf A.X)).mulVec x)) = a • thetaOp R F i t x := by
  apply adForm_injective hM hU i
  have h1 : adForm R i (a • thetaOp R F i t x) = D.what₂.embLL a • adForm R i (thetaOp R F i t x) := by
    unfold adForm
    rw [map_smulₛₗ, map_smul, sign_at_base_place_eq_embedding R]
  rw [adForm_eOp hU, hθ, map_smul, h1]
  refine congrArg _ ((hP.thG i t _).symm.trans (congrArg (R.HW i (sg0 D A)).e ?_))
  exact (thG_good hOk hM hS hZ i t x).trans (OntoChain.j_thetaOp h5 hr i t x).symm

theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernel
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType
open GlobalTheory.DepthZeroJac GlobalTheory.IwahoriInj GlobalTheory.StepData

theorem unipRad_points_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    unipRad k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) = unipB k (Fin n) := by
  ext g
  rw [mem_unipB, mem_unipRad, mem_parab]
  simp only [blk, Equiv.sigmaUnique_symm_apply, Equiv.sigmaUnique_apply]
  refine and_congr Iff.rfl ⟨fun h i => (h i 0 0).trans (by simp), fun h a i j => ?_⟩
  rw [h a, Subsingleton.elim i j]
  simp

theorem eq_zero_of_fixed_KO_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  intro k _ _ _ _ n V _ _ π hπ v h1 hfix
  rw [← unipRad_points_eq] at h1
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  refine claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v ?_ hM
  exact mem_fixed.2 fun g hg => hfix g ((sup_le KOne_le_KO inf_le_right) hg)

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLaws
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl.KernLaws

theorem exists_finite_lift {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ κ ∈ GfC V, fin V κ = q := by
  obtain ⟨_, g, rfl⟩ := q
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  exact ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩⟩, k1, Subtype.ext k2⟩

theorem fin_mul {D : D7} (V : HSp D) (a b : GA D V) : fin V a * fin V b = fin V (a * b) :=
  (map_mul (finHom V).rangeRestrict a b).symm

theorem ratF_eq {D : D7} (V : HSp D) (γ : GQ V) : Bridge.ratF V γ = fin V γ := rfl

theorem lift_of_mem_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {κ : GA D V}
    (hκ : κ ∈ GfC V) (hk : fin V κ ∈ (levEnv V β L).J) :
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ ⟨_, hk⟩)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine ⟨⟨hκ, hk.1, Subgroup.mem_bot.1 hk.2⟩, ?_⟩
  unfold levChi
  rw [← levFn_flag1, Units.val_inv_eq_inv_val]
  rfl

theorem exists_lift_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨κ, hκ, rfl⟩ := exists_finite_lift V k
  exact ⟨κ, rfl, lift_of_mem_J V β L hκ hk⟩

theorem finE_of_fin {D : D7} (V : HSp D) {κ : GA D V} {x : Bridge.Gf V} (e : fin V κ = x) :
    finE V κ = Formalism.UG.bc (swapAE D) (x : GL _ _) := by
  have : finHom V κ = x.1 := congrArg Subtype.val e
  rw [finE_eq, this]

theorem exists_lift_Q {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).Q) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf V) : GL _ _))) κ ∧
      ((((levEnv V β L).ch k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨κ, hκ, e⟩ := exists_finite_lift V k.1
  have e' := finE_of_fin V e
  refine ⟨κ, e, ⟨hκ, ?_, congrArg (rTup β L) e'⟩, ?_⟩
  · rw [e']
    exact k.2.1
  · have e2 : (levEnv V β L).ch k = levFn β (flagL L) (finE V κ) := (congrArg (levFn β (flagL L)) e').symm
    rw [Units.val_inv_eq_inv_val, e2, levChi]

theorem lift_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem exists_actL {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (hex : ∃ κ, IsLevelLift V β L g0 κ) : ∃ κ, IsLevelLift V β L g0 κ ∧
      ∀ F h, actL V β L g0 F h = (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  refine ⟨hex.choose, hex.choose_spec, fun F h => ?_⟩
  change actG0 V β L g0 F h = _
  unfold actG0
  rw [dif_pos hex]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

theorem kernA_apply (h : GA D (Vc D i)) (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t h w v g =
      Datum.thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))) := rfl

theorem kernA_mul_real (hio : R.thP_ioP) (h : GA D (Vc D i)) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) :
    kernA R i t (h * u) = kernA R i t h := by
  ext w v g
  rw [kernA_apply, kernA_apply]
  unfold Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, (hio i t).1 u hu, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem kern_fin (hio : R.thP_ioP) (h : GA D (Vc D i)) : kern R i t (fin (Vc D i) h) = kernA R i t h := by
  unfold kern
  have e := (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose_spec
  generalize (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose = h' at e
  have hu : h⁻¹ * h' ∈ GinfC (Vc D i) := by
    change finHom (Vc D i) (h⁻¹ * h') = 1
    rw [map_mul, map_inv, e]
    exact inv_mul_cancel _
  rw [← kernA_mul_real R i t hio h hu, mul_inv_cancel_left]

theorem kernA_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (γ : GQ (Vc D i)) (h : GA D (Vc D i)) (w : (R.cV i).W) :
    kernA R i t (γ * h) ((R.cV i).ρ γ w) = kernA R i t h w := by
  funext v g
  rw [kernA_apply, kernA_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _
    (hpt i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))).1 γ γ.2 1 (one_mem _) h g
  rwa [one_mul] at this

theorem kernA_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t (h * κ) w v (g * κ') = c * kernA R i t h w v g := by
  rw [kernA_apply, kernA_apply, mul_inv_rev, map_mul, (hc i).1 _ (inv_mem hκ), one_mul]
  exact (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _ (hpt i t _)).2 κ κ' c
    (GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hθ (hω i t) _ _ _ _ _ (hpt i t) κ hκ κ' hκ' c e _) h g

theorem levChi_flag_datWp (κ' : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ' = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ')) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2, show (flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem kern_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP) (γ : GQ (Vc D i)) (h : Bridge.Gf (Vc D i))
    (w : (R.cV i).W) : kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = kern R i t h w := by
  obtain ⟨h', -, e⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (Bridge.ratF (Vc D i) γ * h) = kernA R i t (γ * h') := by
    rw [← e, ratF_eq, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_rat R i t hω hpt γ h' w

theorem kern_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kern R i t (h * fin (Vc D i) κ) w v (g * κ') = c * kern R i t h w v g := by
  obtain ⟨h', -, e0⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (h * fin (Vc D i) κ) = kernA R i t (h' * κ) := by
    rw [← e0, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e0, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_eigen R i t hθ hc hω hpt hκ hκ' e h' w v g

theorem eq_smul_of_mul_one {X Y : Type} [Monoid Y] (F F' : X → Y → ℂ) (c : ℂ) (h : ∀ v g, F v (g * 1) = c * F' v g) :
    F = c • F' := by
  funext v g
  rw [← mul_one g, h, mul_one]
  rfl

theorem eq_smul_of_mul {Y : Type} [Monoid Y] (B F F' : Y → ℂ) (a c : ℂ) (y : Y) (ha : a = 1) (h1 : ∀ g, B g = a⁻¹ * F (g * y))
    (h : ∀ g, F (g * y) = c * F' g) : B = c • F' := by
  funext g
  rw [h1, ha, inv_one, one_mul, h]
  rfl

theorem kern_level (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (h : Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) (w : (R.cV i).W) :
    kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • kern R i t h w := by
  obtain ⟨κ, e1, l1, e2⟩ := exists_lift_J (Vc D i) (R.βV i) (R.datVt i t) k
  rw [e2, ← e1]
  exact eq_smul_of_mul_one _ _ _ (kern_eigen R i t hθ hc hω hpt hio l1.1 (GfC (Wc D i)).one_mem
    (hD 1 κ 1 l1 (lift_one _ (R.βW i) (R.datWp i R.triv))) h w)

theorem kern_act (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q)
    (hg : g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)))
    (hex : ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (kern R i t (h * q) w v) =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • kern R i t h w v := by
  refine (exists_lift_Q (Vc D i) (R.βV i) (R.datVt i t) q).elim fun κ H => ?_
  refine (exists_actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 hex).elim fun κ' H' => ?_
  have l1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ := ⟨H.2.1.1, H.2.1.2.1, H.2.1.2.2.trans hg.symm⟩
  have := kern_eigen R i t hθ hc hω hpt hio l1.1 H'.1.1 (hD g0 κ κ' l1 H'.1) h w v
  rw [H.2.2, ← H.1]
  exact eq_smul_of_mul _ _ _ _ _ κ' (levChi_flag_datWp R i κ') (H'.2 _) this

end GlobalTheory.TraceIncl.KernLaws

namespace GlobalTheory.TraceIncl

open KernLaws

theorem kern_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i t hθ hc hω hpt hio hD
  exact ⟨kern_fin R i t hio, kern_rat R i t hω hpt hio, kern_level R i t hθ hc hω hpt hio hD,
    kern_act R i t hθ hc hω hpt hio hD⟩

end GlobalTheory.TraceIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddingsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings : ∀ D : D7, useNorm D := by
  first | exact @GlobalTheory.ConjNorm.useNorm_all | exact GlobalTheory.ConjNorm.useNorm_all | (intros; apply GlobalTheory.ConjNorm.useNorm_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlacesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places : ∀ D : D7, odd3 D := by
  first | exact @GlobalTheory.InertSign.vacuum_inert | exact GlobalTheory.InertSign.vacuum_inert | (intros; apply GlobalTheory.InertSign.vacuum_inert <;> assumption)
end


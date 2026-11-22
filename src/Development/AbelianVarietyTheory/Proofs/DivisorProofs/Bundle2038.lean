import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped Matrix TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassSumIdentity

theorem sub_orthProj_perp_mem {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hH : (H.map v0.embedding).PosDef) (N : Submodule K (Fin n → K)) (x : Fin n → K) :
    x - orthProj H (perpOf H N) x ∈ N := by
  have hd : ∀ Z : Submodule K (Fin n → K), Hᴴ = H ∧ IsUnit ((subE Z)ᴴ * H * subE Z).det := fun Z =>
    have k := orthogonal_projection_exists K v0 h0 _ _ H hH (subE Z) (subspace_image_spec K n Z).1
    ⟨k.1, k.2.2.1⟩
  have h1 : ∀ u y : Fin n → K, hform H u y = star u ⬝ᵥ H.mulVec y := fun u y => by
    simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_assoc,
      mul_comm, mul_left_comm]
  have hs : ∀ u y : Fin n → K, hform H u y = 0 → hform H y u = 0 := fun u y e => by
    rw [h1] at e ⊢
    have := congrArg star e
    rwa [star_zero, ← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, (hd N).1, ← Matrix.dotProduct_mulVec] at this
  set y := x - orthProj H (perpOf H N) x
  have hy : y ∈ perpOf H (perpOf H N) := sub_orthProj_mem_perpOf H _ (hd _).2 x
  have hq : orthProj H N y ∈ N := orthProj_mem H N y
  have hw : y - orthProj H N y ∈ perpOf H N := sub_orthProj_mem_perpOf H _ (hd _).2 y
  have hw' : y - orthProj H N y ∈ perpOf H (perpOf H N) :=
    Submodule.sub_mem _ hy fun z hz => hs _ _ (hz _ hq)
  obtain ⟨a, ha⟩ := (subspace_image_spec K n (perpOf H N)).2.ge hw
  have h2 : ((subE (perpOf H N))ᴴ * H * subE (perpOf H N)).mulVec a = 0 := by
    funext i
    have := hw' _ ((subspace_image_spec K n (perpOf H N)).2.le ⟨Pi.single i 1, rfl⟩)
    rw [← ha, h1, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [← Pi.single_star] using this
  have h3 : a = 0 := by
    rw [← Matrix.one_mulVec a, ← Matrix.nonsing_inv_mul _ (hd (perpOf H N)).2, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  rw [h3, map_zero] at ha
  exact sub_eq_zero.1 ha.symm ▸ hq

theorem lvlE_lvlOp {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) (S : CSD K)
    (hH : (S.H.map v0.embedding).PosDef) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (hr : S.ActGood r)
    (U : Subgroup G) (ψ : U →* Kˣ) (a : MonoidAlgebra K G) (ha : ∀ b, b * a = a * b) (x : Fin (S.lvlDim r U ψ) → K) :
    S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec ((S.lvlOp r U ψ a).mulVec x)) =
      ∑ g, a.coeff g • r g (S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec x)) := by
  rw [Matrix.mulVec_mulVec, (level_operator_spec K v0 h0 S hH G r hr U ψ a (ha _).symm).1, ← Matrix.mulVec_mulVec, CSD.gaMat,
    Matrix.sum_mulVec, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec K S G r g _))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

open GlobalTheory.TraceIncl in

theorem classSum_eOp {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} (h : HidaSetting R i t) {θ} (hθ : OnTies.IsClassSum R i t U ψ ph θ)
    (c : G → D.what₂.LL) {x y : Fin (OnTies.srcDim A i t U ψ) → D.what₂.LL}
    (e : srcForm A i t U ψ y = ∑ g, c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) : θ y = (R.FW i).eOp c (θ x) := by
  rcases subsingleton_or_nontrivial (Fin (R.nW i) → D.what₂.LL) with hs | hs
  · exact Subsingleton.elim _ _
  refine h.eq_of_adForm fun v => ?_
  have e0 : adForm R i ((R.FW i).eOp c (θ x)) = ∑ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) := by
    unfold adForm
    rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  have e4 : ∀ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) (fun ρ => v ρ) =
      ph • (clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x))) v := fun g => by
    have e1 : adForm R i ((R.FW i).ρ g (θ x)) (fun ρ => v ρ) = sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (adForm R i (θ x) fun ρ => v ρ) :=
      DFunLike.congr_fun ((h.unif i _).2.2 g (θ x)) _
    have e2 : clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
          (clSum (presV R i t) (kern R i t) (srcForm A i t U ψ x) v) :=
      congrFun (h.clSum_equiv g (srcForm A i t U ψ x)) v
    have e3 : sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) = D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) :=
      congrArg (fun s : D.what₂.LL →+* ℂ => s _) (sign_at_base_place_eq_embedding R)
    have e5 : clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        D.what₂.embLL (c g) • clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
      congrFun (LinearMap.map_smulₛₗ _ _ _) v
    have e6 : D.what₂.embLL (c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) * D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) =
        D.what₂.embLL (c g) := by rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [e5, e2, adForm_smul, MultilinearMap.smul_apply, e1, e3, h.adForm_theta hθ, smul_smul, e6, LinearMap.map_smul, smul_comm]
  have e7 : clSum (presV R i t) (kern R i t) (srcForm A i t U ψ y) v =
      ∑ g, clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
    (congrArg (fun f => clSum (presV R i t) (kern R i t) f v) e).trans
      ((congrFun (map_sum (clSum (presV R i t) (kern R i t)) _ _) v).trans (Finset.sum_apply _ _ _))
  refine (h.adForm_theta hθ y v).trans (((congrArg (fun F => ph • F) e7).trans Finset.smul_sum).trans (Eq.symm ?_))
  exact (DFunLike.congr_fun e0 _).trans ((MultilinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun g _ => e4 g))

section Comparison₂

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem identity_of_tie (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y)
    (hS : GlobalTheory.TraceIncl.HidaSetting R ι (R.mu v)) {s : ℕ} (hOk : A.fam.Ok s) (hr : ClassSumRational R ι (R.mu v) U ψ ph) :
    O.θ' v i ∘ₗ O.eX v i = O.e i ∘ₗ O.θ' v i ∧
      ∀ x ∈ LinearMap.range (O.eX v i), x - O.pr v i x ∈ LinearMap.ker (O.θ' v i) := by
  have hθy : ∀ x, (toForms h fw ι z ∘ₗ O.θ' v i ∘ₗ y.symm.toLinearMap) (y x) = toForms h fw ι z (O.θ' v i x) := fun x =>
    congrArg (fun a => toForms h fw ι z (O.θ' v i a)) (y.symm_apply_apply x)
  refine ⟨LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_, fun x _ => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, t.e_eOp, ← hθy, ← hθy]
    refine classSum_eOp hS (t.θ'_eq hr) _ ?_
    refine (congrArg (srcForm A ι (R.mu v) U ψ) (LinearMap.congr_fun t.eX_eq x)).trans ?_
    exact lvlE_lvlOp hOk.conj (A.MtCSD ι (R.mu v)) ((hOk.lifts ι (R.mu v)).hpos _) (A.leftGroupActionLift ι (R.mu v)) hS.act U ψ _
      (idempotent_central _ _ A.X hOk.irr).2 (y x)
  · have hpos : (((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ).map A.v0.embedding).PosDef :=
      BlockDat.lf_lvlH_pos (B := A.fam.L ι (R.mu v)) (ℓ := ⟨A.X, U, ψ⟩) ⟨hOk.conj, hOk.irr, hOk.lifts ι (R.mu v)⟩ A.v0
    obtain ⟨a, ha, e⟩ := sub_orthProj_perp_mem hOk.conj hpos ((LinearMap.ker (O.θ' v i)).map y.toLinearMap) (y x)
    have e' : y a = y (x - O.pr v i x) :=
      e.trans ((congrArg (fun b => y x - b) (LinearMap.congr_fun t.pr_eq x).symm).trans (y.map_sub _ _).symm)
    exact y.injective e' ▸ ha

end Comparison₂

attribute [local instance] GlobalTheory.BigOn.runAlg' in

theorem leafIdentity_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → TwistedRational R F (fun _ => 1) → LeafIdentity O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO s hOk hC hU hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1 →
      O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j) := fun v j hr =>
    identity_of_tie (T := (r.used v).full) (inst := inst) (R := R) (ht v j).1
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩ hOk hr
  exact fun w hw => ⟨fun j => key w j (hrat w hw j), fun j => key _ j (by rw [hC.tup.mu_conj w]; exact hrat w hw j)⟩

end GlobalTheory.ClassSumIdentity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuum
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio.CosetNorm

open Formalism.MainNotions.TaylorLogMetric (VC tor0 La Iop U al YYl embV)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt La0 Wd wdPh Crv)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := by
  have e : symplO S T x y + symplOH S T y x = symplOH S T x y := by
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
    unfold symplOH
    rw [GlobalTheory.OrientedHeis.symplO_skew x y]
    linear_combination (-symplO S T x y) * h2
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, e, add_comm]

theorem heisO_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_heisO_eq_zero {ΛS : Lat S} {ΛT : Lat T} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {u u' : WO S T}
    (hu : u.map (infPart D) = 0) (hu' : u'.map (infPart D) = 0) (hn : u - u' ∉ latO S T ΛS ΛT fun _ => True) :
    GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f) = 0 := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have h0 : (u - u').map (infPart D) = 0 := by
    funext i j
    have a : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    have b : infPart D (u' i j) = 0 := congrFun (congrFun hu' i) j
    show infPart D (u i j - u' i j) = 0
    rw [RingHom.map_sub, a, b, sub_self]
  rw [h1 _ h0] at hn
  push_neg at hn
  obtain ⟨l, hl, hne⟩ := hn
  obtain ⟨ε, hε, hεf⟩ := h3 f hv l hl
  have t1 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu
  have t2 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu'
  have e := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 t1 t2 l
  rw [heisO_comm l u, heisO_comm l u', hεf f hv, heisO_smul, heisO_smul, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left,
    GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right] at e
  have hεε : ε * starRingEnd ℂ ε = 1 := by rcases hε with rfl | rfl <;> simp
  have n1 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (symplO S T l u'))
  have e2 : ψ (symplO S T (u - u') l) * ψ (symplO S T l u) = ψ (symplO S T l u') := by
    rw [← AddChar.map_add_eq_mul, GlobalTheory.OrientedHeis.symplO_skew u l, GlobalTheory.OrientedHeis.symplO_skew u' l]
    congr 1
    have : symplO S T (u - u' + u') l = symplO S T (u - u') l + symplO S T u' l := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]
    rw [sub_add_cancel] at this
    linear_combination -this
  refine (mul_eq_zero.1 (?_ : (ψ (symplO S T (u - u') l) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 hne)
  set I := GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f)
  set A := ψ (symplO S T (u - u') l)
  set B := ψ (symplO S T l u)
  set C := ψ (symplO S T l u')
  linear_combination (-A) * e + (ε * starRingEnd ℂ C * starRingEnd ℂ ε * I) * e2 +
    (C * starRingEnd ℂ C * I) * hεε + I * n1

theorem ip_sum (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (h : ι → WO S T → ℂ) (c : ℂ) (ht : ∀ i, IsThetaFunO ψ S T (h i))
    (ha : ∀ i, a i * starRingEnd ℂ (a i) = 1)
    (ho : ∀ i j, i ≠ j → GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) = 0) (hc : ∀ i, GlobalTheory.Ker.ipO μ 𝓕 (h i) (h i) = c) :
    GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) = s.card * c := by
  have e : ∀ w, (∑ i ∈ s, a i • h i) w * starRingEnd ℂ ((∑ i ∈ s, a i • h i) w) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w)) := fun w => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hi : ∀ i j, Integrable (fun w => (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w))) (μ.restrict 𝓕) :=
    fun i j => Integrable.const_mul (GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (ht i) (ht j)) _
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) := by
    unfold GlobalTheory.Ker.ipO
    simp only [e]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [e2, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hj => by rw [ho i j hj.symm, mul_zero], ha, hc, one_mul]

theorem selfDual_stdLat (hS : S.gram = 1) : IsSelfDualC S (stdLat S) := by
  convert GlobalTheory.Ker.Base.selfDualC_stdL hS using 1
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL, stdLat, stdL, Submodule.mem_pi]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h trivial)
    rw [← hb]
    exact b.2
  · exact Submodule.mem_one.2 ⟨⟨x i, h⟩, rfl⟩

theorem reads_sum {θ : InfFam D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}
    {ι : Type} (s : Finset ι) {G : ι → VC D a d → ℂ} {f : ι → WO S T → ℂ} (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

theorem finPt_sub {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z z' : Matrix (Fin d) (Fin a) D.host.E) :
    finPt hS hT r (z - z') = finPt hS hT r z - finPt hS hT r z' := by
  unfold finPt
  rw [← AddMonoidHom.map_sub]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.sub_apply]
  ring_nf

theorem pt_sub_mem {a d : ℕ} (δ : ℂ) {z z' : Matrix (Fin d) (Fin a) D.host.E} (h : z - z' ∈ YYl D (stdL D a) (stdL D d)) :
    pt D (tor0 D ⊤ δ) δ z - pt D (tor0 D ⊤ δ) δ z' ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, h, ?_⟩
  funext τ i j
  simp only [pt, embV, tor0, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub]
  ring

set_option maxHeartbeats 1000000 in

theorem ip_cosetVec : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ hf₀ hsph hφ ν 𝓕 hcov
  have hset := hX.setup
  have hψ := hset.std
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ P.crv 𝔪 hG.1 (Ideal.isCoprime_iff_sup_eq.2 hG.2.1) P.a P.d
  have hpts := fun y hy => GlobalTheory.FunObj.StdDatum.SkewPoints.points D δ P.crv 𝔪 hG.1 (a := P.a) (d := P.d) y hy
  unfold cosetVec at hφ
  generalize La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d) = L at hidx hpts hφ
  have hne : ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index ≠ 0 := by rw [hidx]; positivity
  haveI : Finite (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  letI : Fintype (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := Fintype.ofFinite _
  choose z hz _ using fun q : L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L => hpts _ (Quotient.out q).2
  have hlv : IsLatVac (heisO X.ψ X.A X.B) (latO X.A X.B (stdLat X.A) LB fun _ => True) f₀ := by
    have e : (fun v : FinPl D => v ∉ (∅ : Finset (FinPl D))) = fun _ => True := by funext v; simp
    rw [← e]
    exact hsph
  have hfin : ∀ y, (finPt X.rkA X.rkB r y).map (infPart D) = 0 := fun y => GlobalTheory.VacUnique.finRat_inf _ _ _
  have hrd := GlobalTheory.NormExact.heisO_finPt_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r hset
  set n := ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index with hn
  have eI : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) L P.e0 = ((Real.sqrt (n : ℝ) : ℂ))⁻¹ •
      ∑ q, al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) • U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) P.e0 := by
    funext y
    simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hz, ← hn]
  have hg := reads_sum Finset.univ fun q => (hrd _ _ hf₀ (z q)).smul (al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
  have hg2 := hg.smul ((Real.sqrt (n : ℝ) : ℂ))⁻¹
  rw [← eI] at hg2
  have hw := ((hrd _ _ hg2 (unitBlock D o P.a P.d)).smul
    (wdPh D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d)))).smul
    ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹
  have hsum := ip_sum hψ hcov Finset.univ (fun q => al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
    (fun q => heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (z q)) f₀) (GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀) (fun q => (hrd _ _ hf₀ (z q)).1)
    (fun q => by
      rw [al, map_zpow₀, ← mul_zpow]
      simp)
    (fun q q' hq => ip_heisO_eq_zero hψ (selfDual_stdLat hset.gS) hLB hf₀.1 hlv hcov (hfin _) (hfin _) fun h => hq (by
      rw [← finPt_sub, ← hY] at h
      have h2 := pt_sub_mem δ h
      rw [← hz, ← hz] at h2
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
      exact h2))
    fun q => GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hf₀.1 hf₀.1 _
  have hph : ∀ x : VC D P.a P.d, wdPh D (tor0 D ⊤ δ) x * starRingEnd ℂ (wdPh D (tor0 D ⊤ δ) x) = 1 := fun x =>
    GlobalTheory.HeisOrtho.mul_conj_of_norm_one (by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.norm_exp])
  have hsq : ∀ t : ℝ, 0 ≤ t → ((Real.sqrt t : ℂ))⁻¹ * starRingEnd ℂ ((Real.sqrt t : ℂ))⁻¹ = (t : ℂ)⁻¹ := fun t ht => by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have e1 := hsq n (Nat.cast_nonneg n)
  have e2 := hsq ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) (by positivity)
  have e3 := hph (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
  have e4 : ((n : ℝ) : ℂ)⁻¹ * (n : ℂ) = 1 := by
    rw [Complex.ofReal_natCast]; exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hne)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, ← hn] at hsum
  have eW : ∀ (x : VC D P.a P.d) G, Wd D (tor0 D ⊤ δ) x G = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G := fun _ _ => rfl
  rw [eW] at hφ
  rw [Reads.unique hφ hw]
  show GlobalTheory.Ker.ipO ν 𝓕 _ _ = _ * GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀
  rw [GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right,
    GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hg2.1 hg2.1, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, hsum,
    ← mul_assoc, e2, ← mul_assoc (wdPh _ _ _), e3, one_mul, ← mul_assoc _ (starRingEnd ℂ _), e1, ← mul_assoc _ (n : ℂ), e4, one_mul]
  push_cast
  rfl

end GlobalTheory.NormRatio.CosetNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_mul_transpose {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (ξ : A) (JA : Matrix α α A)
    (JB : Matrix β β A) (g : Matrix β β A) (hg : gᵀ * JB * g.map c = JB) (x : Matrix α β A) :
    symp c ξ JA JB (x * gᵀ) (x * gᵀ) = symp c ξ JA JB x x := by
  have e : (x * gᵀ) * JB * ((x * gᵀ).map c)ᵀ = x * JB * (x.map c)ᵀ := by
    have hm : (x * gᵀ).map c = x.map c * (gᵀ).map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    calc x * gᵀ * JB * (g.map c * (x.map c)ᵀ) = x * (gᵀ * JB * g.map c) * (x.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq, hTens_eq, e]

variable {σ : E →ₐ[F] E}

theorem vecMulVec_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {w : Fin d → AE F E} (hw : w ∈ latAt W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) w ∈ latAtV X W v := by
  let f : (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun w => Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) w
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun w w' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add] }
  have : latAt W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hw

theorem mul_transpose_inv_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {h : UA σ W.J}
    (hh : h ∈ KAt σ W v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    γ * (mat h⁻¹)ᵀ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => γ * (mat h⁻¹)ᵀ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.add_mul] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show (a • incM F (Matrix.vecMulVec x y)) * (mat h⁻¹)ᵀ ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
    have e : (a • incM F (Matrix.vecMulVec x y)) * (mat h⁻¹)ᵀ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
          (mat h⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (y i))) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_latAtV X W v hx (hh.2 _ hz).2
  exact this hγ

end GlobalTheory.InertSph

namespace GlobalTheory.InertSph

theorem acts_vacCond_of_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ hθ k hk φ hφ φ₁ hφ₁ hAct hvac γ hγ r hr
  have hS := IsUWeilPair.isUSplitting hTr.weil'
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ₁ φ r h0 hφ hr
  set γ' := actAB (cA σ) ((1 : UA σ G.V'.J), k⁻¹) γ
  have eγ' : γ' = γ * (mat k⁻¹)ᵀ := by
    simp [γ', actAB, mat]
  have hγ' : γ' ∈ latAtV G.V' G.W v := by
    rw [eγ']; exact mul_transpose_inv_mem_latAtV G.V' G.W v hk hγ
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
    rw [eγ']
    exact symp_mul_transpose (cA σ) _ _ _ (mat k⁻¹) (k⁻¹).2 γ
  have e1 : actAB (cA σ) ((1 : UA σ G.V'.J), k) γ' = γ := by
    simp only [γ', actAB]
    simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have hi := hS.impl ((1 : UA σ G.V'.J), k) γ' _ hrφ.2
  rw [e1] at hi
  rw [← hAct r hrφ, ← hi, hvac γ' hγ' r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.InertSph
end
end


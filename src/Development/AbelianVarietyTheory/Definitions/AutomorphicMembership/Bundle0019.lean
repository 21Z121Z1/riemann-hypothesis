import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingOneApplyDivThree
section
noncomputable section

open Formalism.BasicNotions NumberField Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.Mem.R3.MjModel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem unitMap_norm (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (x : (unitLat K (Module.finrank ℂ W)).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X
      (InfinitePlace.mk σ) x) = ‖unitMap σ W x‖ := by
  have h1 : unitMap σ W x = ∑ i, σ (x i) • stdOrthonormalBasis ℂ W i :=
    Fintype.linearCombination_apply ℂ (stdOrthonormalBasis ℂ W) (cpt σ x)
  have h2 : ‖unitMap σ W x‖ ^ 2 = ∑ i, ‖σ (x i)‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℂ W).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, (stdOrthonormalBasis ℂ W).orthonormal.inner_right_fintype]
  rw [← Real.sqrt_sq (norm_nonneg (unitMap σ W x)), h2, Formalism.HermitianLatticesTheory.cnorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X (InfinitePlace.mk σ) x i =
      (InfinitePlace.mk σ).embedding (x i) := by
    have h4 : ∀ (n : ℕ) (u : Fin n → ℂ), Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ u = u := fun n u => by
      rw [inv_one, Matrix.one_mulVec]
    exact congrFun (h4 _ _) i
  rw [h3, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

def twoLat : Submodule (𝓞 ℚ) (Fin 1 → ℚ) := Submodule.span (𝓞 ℚ) {fun _ => 2}

def frame3 : InfinitePlace ℚ → Matrix (Fin 1) (Fin 1) ℂ := fun _ => Matrix.diagonal fun _ => 3

def third : (Fin 1 → ℚ) →ₛₗ[algebraMap ℚ ℂ] ℂ where
  toFun x := (x 0 : ℂ) / 3
  map_add' x y := by simp [add_div]
  map_smul' a x := by simp [mul_div_assoc]

abbrev seq1 : ℕ → HLat ℚ := latSeq (m := 1) (d := fun _ => 1) (fun _ => twoLat) (fun _ => frame3) (fun _ => ℂ)

abbrev map1 : ∀ j, (seq1 j).V →ₛₗ[algebraMap ℚ ℂ] ℂ :=
  mapSeq (m := 1) (d := fun _ => 1) (fun _ => twoLat) (fun _ => frame3) (fun _ => ℂ) (fun _ => third)

theorem embedding_one_apply_div_three (x : Fin 1 → ℚ) : map1 1 x = (x 0 : ℂ) / 3 := rfl

theorem one_not_mem : (fun _ => 1 : Fin 1 → ℚ) ∉ (seq1 1).L := by
  show (fun _ => 1 : Fin 1 → ℚ) ∉ twoLat
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
  have h1 : (a : ℚ) * 2 = 1 := congrFun ha 0
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective a
  rw [Rat.ringOfIntegersEquiv_symm_apply_coe] at h1
  have h2 : z * 2 = 1 := by exact_mod_cast h1
  omega

theorem metric_one (x : Fin 1 → ℚ) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (seq1 1).b (seq1 1).X (InfinitePlace.mk (algebraMap ℚ ℂ)) x) = ‖map1 1 x‖ := by
  rw [embedding_one_apply_div_three]
  show Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun ℚ (Fin 1)) frame3 (InfinitePlace.mk (algebraMap ℚ ℂ)) x) = _
  have h : (frame3 (InfinitePlace.mk (algebraMap ℚ ℂ)))⁻¹ = Matrix.diagonal fun _ => (3 : ℂ)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [frame3, Matrix.diagonal_mul_diagonal]
    simp
  rw [Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, h, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _), Matrix.mulVec_diagonal]
  simp [Formalism.HermitianLatticesTheory.vecAt, div_eq_inv_mul]

theorem good_one : (seq1 1).Good := by
  refine ofCoord_good (L := twoLat) (X := frame3) ⟨Submodule.fg_span (Set.finite_singleton _), ?_⟩ fun v => by simp [frame3]
  rw [twoLat, Submodule.span_span_of_tower, eq_top_iff]
  intro x _
  exact Submodule.mem_span_singleton.2 ⟨x 0 / 2, by funext i; rw [Subsingleton.elim i 0]; simp⟩

theorem rank_off : Module.finrank ℚ (seq1 0).V = 1 ∧ Module.finrank ℚ (seq1 2).V = 1 :=
  ⟨(Module.finrank_fin_fun ℚ).trans (Module.finrank_self ℂ), (Module.finrank_fin_fun ℚ).trans (Module.finrank_self ℂ)⟩

section Record

open Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)

theorem jM_metric_all (hH : Holds R F) (j : ℕ) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => MjCoord.jW_norm Z hH i) (fun _ => unitMap_norm _ _) j x

theorem card_mjH (hH : Holds R F) (j : ℕ) : Fintype.card (mjH Z j).ι = Module.finrank ℂ (D.what₂.Mj j) :=
  (Module.finrank_eq_card_basis (Module.Basis.mk (jM_basis Z hH j).1 (jM_basis Z hH j).2.ge)).symm

theorem exists_tied {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (hP : Pins R F cG) (hH : Holds R F) (Xd : DivX D) :
    ∃ X : DivX D, X.geo = Xd.geo ∧ X.MjH = mjH Z ∧ ∃ JM, MjHTie D A3.A X (A3.indefDown (s0Of R F)) Z.jW JM :=
  ⟨withMj Z hP hH Xd (fun _ _ => 0) (fun _ _ _ => Submodule.zero_mem _), rfl, rfl, _, mjHTie_withMj Z hP hH Xd _ _⟩

end Record

end GlobalTheory.Mem.R3.MjModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
section
noncomputable section

namespace GlobalTheory.HeightCounting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.L2 Formalism.L2.NT

set_option synthInstance.maxHeartbeats 400000 in

structure NAllC (D : D7) (C : NChoice D) where
  gal : NGalTied D
  n : NormalizedHeckeDataPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : ChoiceC D C
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y

def GoodCl (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, TwistedAt D w →
    (Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace (C.twI w) ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w) ∧ I.Ok (C.twI w)) →
    ExpGood D I (avD D (avDesign D) (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩

variable {D : D7} {C : NChoice D} {I : TwIn D}

def NAllC.toAll (A : NAllC D C) (h : GoodCl D C I) : NormalizedTwistCompatibility D C I :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, h, A.choice.conj⟩ }

def NAllC.ofAll (A : NormalizedTwistCompatibility D C I) : NAllC D C :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, A.choice.conj⟩ }

theorem goodCl_of_all (A : NormalizedTwistCompatibility D C I) : GoodCl D C I := A.choice.good

theorem nonempty_all_iff : Nonempty (NormalizedTwistCompatibility D C I) ↔ Nonempty (NAllC D C) ∧ GoodCl D C I :=
  ⟨fun ⟨A⟩ => ⟨⟨NAllC.ofAll A⟩, goodCl_of_all A⟩, fun ⟨⟨A⟩, h⟩ => ⟨A.toAll h⟩⟩

example (A : NAllC D C) (h : GoodCl D C I) : NAllC.ofAll (A.toAll h) = A := rfl

example (A : NormalizedTwistCompatibility D C I) : (NAllC.ofAll A).toAll (goodCl_of_all A) = A := rfl

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

structure PhtOn {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (Wd : WDSide D T) (fr : OmFrame D)
    (p : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ), (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → Prop) : Prop where
  card : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (τ : D.host.E →+* Qbar l) (w : PlE D.host), p l a r →
    (∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ ‖τ (x : D.host.E)‖ < 1) → Wd.IsdRW l ι r w → Multiset.card (Wd.jumpsW l ι r τ) = a

def PhtCmp : Prop :=
  ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Wd : WDSide D T), PhtOn Wd fr fun l _ a r =>
    Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))

def LpCmp (_hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  ∀ (D : D7) (_T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (LPTiedPlaceholder D)

def CgCmp (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop :=
  ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → Nonempty (NormalizedHeckeDataPlaceholder D)

structure ArchCmp (hL : GlobalTheory.Published.LocalLanglandsGL) : Prop where
  pht : PhtCmp
  lp : LpCmp hL
  cg : CgCmp hL

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.FWT GlobalTheory.RealGeo

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}

abbrev setCd (c : CDHaar) : Late B C := { b with G := { b.G with cd := c } }

theorem lawsM_tr {T : Core a.D} (h : LawsM T) : LawsM (core b T) := by
  have key : ∀ c : CDHaar, c = a.G.cd → LawsM (core (setCd b c) T) := by
    rintro _ rfl
    constructor
    case pins => exact (by with_unfolding_all exact (h.pins :))
    case half => exact (by with_unfolding_all exact (h.half :))
    case evalWD => exact (by with_unfolding_all exact (h.evalWD :))
    case unf => exact (by with_unfolding_all exact (h.unf :))
    case unTest => exact (by with_unfolding_all exact (h.unTest :))
    case chiTriv => exact (by with_unfolding_all exact (h.chiTriv :))
    case dictU => exact (by with_unfolding_all exact (h.dictU :))
    case spaceW => exact (by with_unfolding_all exact (h.spaceW :))
    case levelK => exact (by with_unfolding_all exact (h.levelK :))
    case xiAbs => exact (by with_unfolding_all exact (h.xiAbs :))
    case muUnit => exact (by with_unfolding_all exact (h.muUnit :))
    case muCont => exact (by with_unfolding_all exact (h.muCont :))
    case finVol => exact (by with_unfolding_all exact (h.finVol :))
    case cuspFD => exact (by with_unfolding_all exact (h.cuspFD :))
    case supDef => exact (by with_unfolding_all exact (h.supDef :))
    case cuspidalL2Subspace => exact (by with_unfolding_all exact (h.cuspidalL2Subspace :))
    case l2Def => exact (by with_unfolding_all exact (h.l2Def :))
    case unitIndep => exact (by with_unfolding_all exact (h.unitIndep :))
    case ptNe => exact (by with_unfolding_all exact (h.ptNe :))
  exact (by with_unfolding_all exact ((key b.G.cd (cd_eq _ _)) :))

theorem lawsJ_tr {T : CoreJ a.D} (h : LawsJ T) : LawsJ (coreJ b T) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cUnit => exact (by with_unfolding_all exact (h.cUnit :))
  case muVal => exact (by with_unfolding_all exact (h.muVal :))
  case muConj => exact (by with_unfolding_all exact (h.muConj :))
  case intAll => exact (by with_unfolding_all exact (h.intAll :))
  case modelW => exact (by with_unfolding_all exact (h.modelW :))
  case familyUniformisationBasePointOrthogonal => exact (by with_unfolding_all exact (h.familyUniformisationBasePointOrthogonal :))
  case kfHalf => exact (by with_unfolding_all exact (h.kfHalf :))
  case adPin => exact (by with_unfolding_all exact (h.adPin :))

variable {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m}

section Theta

variable {T : Core a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F} {i : Fin a.D.R.m} {Tp : Type} {tup : Tp → T0}

def omDat (O : OMDat T R i Tp tup) :
    @OMDat b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T))) iK A R)) ((i)) Tp tup :=
  @OMDat.mk b.D G _ _ Pl0 T0 (famM b A) (core b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (i :))) Tp tup
    (c' := (by with_unfolding_all exact (O.c' :)))
    (hle := (by with_unfolding_all exact (O.hle :)))
    (jL := (by with_unfolding_all exact (O.jL :)))
    (hV := (by with_unfolding_all exact (O.hV :)))
    (c0' := (by with_unfolding_all exact (O.c0' :)))
    (lev := (by with_unfolding_all exact (O.lev :)))
    (dδ := (by with_unfolding_all exact (O.dδ :)))
    (Cl' := (by with_unfolding_all exact (O.Cl' :)))
    (fCl := (by with_unfolding_all exact (O.fCl :)))
    (bad := (by with_unfolding_all exact (O.bad :)))
    (Lh := (by with_unfolding_all exact (O.Lh :)))
    (La := (by with_unfolding_all exact (O.La :)))
    (Nc := (by with_unfolding_all exact (O.Nc :)))
    (gam := (by with_unfolding_all exact (O.gam :)))
    (vol := (by with_unfolding_all exact (O.vol :)))
    (ep := (by with_unfolding_all exact (O.ep :)))
    (B := (by with_unfolding_all exact (O.B :)))
    (epF := (by with_unfolding_all exact (O.epF :)))
    (io := (by with_unfolding_all exact (O.io :)))
    (hw := (by with_unfolding_all exact (O.hw :)))
    (φ := (by with_unfolding_all exact (O.φ :)))
    (w := (by with_unfolding_all exact (O.w :)))
    (U₂ := (by with_unfolding_all exact (O.U₂ :)))
    (dict₂ := (by with_unfolding_all exact (O.dict₂ :)))
    (xi := (by with_unfolding_all exact (O.xi :)))
    (thAd := (by with_unfolding_all exact (O.thAd :)))
    (Plc := (by with_unfolding_all exact (O.Plc :)))

theorem omPins_tr {O : OMDat T R i Tp tup} {κ v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) :
    @OMDat.Pins b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T))) iK A R)) ((i)) Tp tup (omDat b O) ((@wt B C a b (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Late.D B C a).R.m i) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) κ)) ((v₀))
      ((ι)) ((x₀)) := by
  apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
  case lift =>
    apply (config := { synthAssignedInstances := false }) ThPinsR.mk
    case field => exact (by with_unfolding_all exact (h.lift.field :))
    case std => exact (by with_unfolding_all exact (h.lift.std :))
    case v0 => exact (by with_unfolding_all exact (h.lift.v0 :))
    case lev => exact (by with_unfolding_all exact (h.lift.lev :))
    case c0 =>
      obtain ⟨x, y, z, h1, h2⟩ := h.lift.c0
      refine ⟨(by with_unfolding_all exact (x :)), (by with_unfolding_all exact (y :)), (by with_unfolding_all exact (z :)), ?_, (by with_unfolding_all exact (h2 :))⟩
      exact (by with_unfolding_all exact ((famTie_imp b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1) :))
  case tuple =>
    intro t
    apply (config := { synthAssignedInstances := false }) ThPinsT.mk
    case reps => exact (by with_unfolding_all exact ((h.tuple t).reps :))
    case B => exact (by with_unfolding_all exact ((h.tuple t).B :))
    case xi => exact (by with_unfolding_all exact ((h.tuple t).xi :))
    case phi => exact (by with_unfolding_all exact ((h.tuple t).phi :))
    case half => exact (by with_unfolding_all exact ((h.tuple t).half :))
  case act => exact (by with_unfolding_all exact (h.act :))
  case bad => exact (by with_unfolding_all exact (h.bad :))
  case reps => exact (by with_unfolding_all exact (h.reps :))
  case ep => exact (by with_unfolding_all exact (h.ep :))
  case io => exact (by with_unfolding_all exact (h.io :))
  case w => exact (by with_unfolding_all exact (h.w :))
  case cov => exact (by with_unfolding_all exact (h.cov :))
  case cxi => exact (by with_unfolding_all exact (h.cxi :))
  case model₂ => exact (by with_unfolding_all exact (h.model₂ :))

end Theta

variable {T : CoreJ a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F}

def fwTie {κ v₀} (x : FWTie T R κ v₀) :
    @FWTie b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) (by with_unfolding_all exact (alg b iK :)) (by with_unfolding_all exact (real b R :)) (fun i => by with_unfolding_all exact (wt b (κ (by with_unfolding_all exact (i :))) :)) (by with_unfolding_all exact (v₀ :)) :=
  @FWTie.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) (fun i => (by with_unfolding_all exact ((wt b (κ ((i)))) : _))) ((by with_unfolding_all exact (v₀ :)))
    (alg_eq := (by with_unfolding_all exact (x.alg_eq :)))
    (e := (by with_unfolding_all exact (x.e :)))
    (ks := (by with_unfolding_all exact (x.ks :)))
    (kap := (by with_unfolding_all exact (x.kap :)))
    (pt := (by with_unfolding_all exact (x.pt :)))
    (nrm_eq := (by with_unfolding_all exact (x.nrm_eq :)))
    (laws := lawsJ_tr b x.laws)
    (chiR := (by with_unfolding_all exact (x.chiR :)))
    (hv₀ := (by with_unfolding_all exact (x.hv₀ :)))
    (x0 := (by with_unfolding_all exact (x.x0 :)))
    (ev0 := (by with_unfolding_all exact (x.ev0 :)))
    (ev := (by with_unfolding_all exact (x.ev :)))

def geoHalf {ph : Fin a.D.R.m → ℂ} (x : GeoHalf T R ph) :
    @GeoHalf b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T)))) iK A R)) ((ph)) :=
  @GeoHalf.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (ph :)))
    (κ := fun i => (by with_unfolding_all exact ((wt b (x.κ ((i)))) : _)))
    (v₀ := (by with_unfolding_all exact (x.v₀ :)))
    (fw := (by with_unfolding_all exact ((fwTie b x.fw) :)))
    (bar := (by with_unfolding_all exact (x.bar :)))
    (O := fun i => (by with_unfolding_all exact ((omDat b (x.O ((i)))) : _)))
    (pins := fun i => (by with_unfolding_all exact ((And.intro (x.pins ((i))).1 (omPins_tr b (x.pins ((i))).2)) : _)))
    (rhoGeo := (by with_unfolding_all exact (x.rhoGeo :)))
    (equivAll := (by with_unfolding_all exact (x.equivAll :)))
    (cTie := (by with_unfolding_all exact (x.cTie :)))
    (phase := (by with_unfolding_all exact (x.phase :)))

theorem inGeo_tr {ph : Fin a.D.R.m → ℂ} {x : GeoHalf T R ph} (h : InGeo x) :
    @InGeo b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T)))) iK A R)) ((ph)) (geoHalf b x) := by
  apply (config := { synthAssignedInstances := false }) InGeo.mk
  case jEvExists => exact (by with_unfolding_all exact (h.jEvExists :))
  case jEvBar => exact (by with_unfolding_all exact (h.jEvBar :))
  case evInj => exact (by with_unfolding_all exact (h.evInj :))
  case jUnif => exact (by with_unfolding_all exact (h.jUnif :))
  case geoAct => kexactB h.geoAct
  case latFull => exact (by with_unfolding_all exact (h.latFull :))
  case dimMatch => exact (by with_unfolding_all exact (h.dimMatch :))

end GlobalTheory.Mem.R3.Tr

end
end


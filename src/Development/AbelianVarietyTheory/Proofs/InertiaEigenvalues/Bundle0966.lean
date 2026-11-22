import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0961
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0963
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0956
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateHalfVacuumTranslateSumIsThetaFockVacuum
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.ConjHalfVac

theorem sum_conj_half_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y) → IsThetaFunO ψ V W (∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) (∑ y ∈ Y, heisO ψ V W y f₀) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT _ _ _ Y hY
  obtain ⟨hpair, _, _, _, _, _, _, _, hvac⟩ := hP
  have hstd : IsStdChar D ψ (-1) := hvac.1
  have hth0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  have hinf : infPart D (cA D eT) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hT)
  have hfin : ∀ y ∈ Y, map y ⇑(infPart D) = 0 := fun y hy =>
    GlobalTheory.DatumFock.infPart_of_isHalf hinf (hY y hy)
  refine ⟨?_, fun τ => ?_⟩
  · classical
    induction Y using Finset.induction_on with
    | empty => simpa using GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := V) (T := W)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact GlobalTheory.OrientedHeis.theta_add
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hth0 a)
        (ih (fun y hy => hY y (Finset.mem_insert_of_mem hy)) (fun y hy => hfin y (Finset.mem_insert_of_mem hy)))
  · have hF : IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) f₀ :=
      hvac.2.fock τ
    have := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hstd.1 hpair.inf f₀ hth0 τ _ hF
      (WO V W) Y id (fun _ => 1) (fun y hy => hfin y hy)
    simpa using this

end GlobalTheory.ConjHalfVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverConstantsUniqueOnDictionaryComponentsStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverConstants_unique_on_dictionaryComponents : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ c : C.U₂.Comp → ℂ, (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → (∀ a, Dom a (κ i).n → ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n) → ∀ h, C.cc₂ (C.dict₂ h).1 = c (C.dict₂ h).1 := by
  first | exact @GlobalTheory.LevelSeries.cc_unique_of_pinned | exact GlobalTheory.LevelSeries.cc_unique_of_pinned | (intros; apply GlobalTheory.LevelSeries.cc_unique_of_pinned <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphicStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  first | exact @GlobalTheory.CoverHol.cover_pull_holSub0 | exact GlobalTheory.CoverHol.cover_pull_holSub0 | (intros; apply GlobalTheory.CoverHol.cover_pull_holSub0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDominantWeightCuspSectionsNoCommonZeroStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom b m ∧ LastPos (T.Q.Dw j) b ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ m ∧ ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ P ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) b m), P k x ≠ 0 := by
  first | exact @GlobalTheory.BpfUniform.exists_weight_noCommonZero | exact GlobalTheory.BpfUniform.exists_weight_noCommonZero | (intros; apply GlobalTheory.BpfUniform.exists_weight_noCommonZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev moveForms {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] {W : (LL →+* ℂ) → Type}
    [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (B : Arith.FormsL LL Ks WL W G) (w : (LL →+* ℂ) → G) : Arith.FormsL LL Ks WL W G :=
  { B with j := fun σ => (B.j σ).comp (B.ρ (w σ)) }

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev moveR {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) : RealDat D A Ks :=
  updFW R R.nW fun i => moveForms (R.FW i) (w i)

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}

open Classical in
variable (T) in

def overEmb (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : G :=
  if GoodEmb T.Q.c (res T σ) then w i (res T σ) else w i (resC T σ)

section Half

variable (B : GeoHalf T R fun _ => 1) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
  (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G)

def Moves : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n,
      phiC (setCE T c') hV (wtA (B.κ i)) f = phiC T hV (wtA (B.κ i)) (actLev T.Q.c (B.O i).lev2 (w i σ) f)

variable {B c' w}

theorem rho_e (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (i : Fin D.R.m) (g : G) (f : Cu T B.κ i) :
    (R.FW i).ρ g ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (B.fw.e i ⟨actLev T.Q.c (B.O i).lev2 g f, hK i g f f.2⟩ : (R.FW i).WK) :=
  (((B.rhoGeo i).1 (hK i) g f).choose_spec).symm

set_option maxHeartbeats 1600000 in
theorem ev_move (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (f : Cu T B.κ i) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)))
      (B.v₀ i σ) = phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) := by
  rw [overEmb, if_pos hσ, rho_e hK, hM i _ hσ hV f f.2]
  exact B.fw.evaluates hJ i σ hσ hV ⟨_, hK i _ f f.2⟩

set_option maxHeartbeats 1600000 in
theorem bar_move (hJ : JEvBar T R B.κ) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) :
    ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f : Cu T B.κ i,
      (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) v =
        fun g => starRingEnd ℂ (phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) g) := by
  obtain ⟨v, hv, h⟩ := (B.bar i σ hσ hV).1 (hJ i σ hσ hV)
  refine ⟨v, hv, fun f => ?_⟩
  rw [overEmb, if_neg hσ, rho_e hK, hM i _ (good_resC T hσ) hV f f.2]
  exact h ⟨_, hK i _ f f.2⟩

set_option maxHeartbeats 3200000 in

def tieMove (hL : LawsJ (setCE T c')) (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) :
    @FWTie D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ B.fw.alg_eq B.fw.e B.fw.ks B.fw.kap B.fw.pt
    B.fw.nrm_eq hL B.fw.chiR B.fw.hv₀ B.fw.x0
    (fun i σ hσ hV h => absurd ⟨((R.FW i).j σ).comp ((R.FW i).ρ (overEmb T w i σ)), ev_move hJ hK hM i σ hσ hV⟩ h)
    (fun i σ hσ hV _ => ev_move hJ hK hM i σ hσ hV)

set_option maxHeartbeats 3200000 in

theorem exists_geoHalf_move (hL : LawsJ (setCE T c')) (hI : InGeo B) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w)
    (hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1) :
    ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) fun _ => 1,
      @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  have hF' := @Half.fired_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ R.nW (fun i => moveForms (R.FW i) (overEmb T w i)) B.O _ hF
  refine ⟨@GeoHalf.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) _ B.κ B.v₀ (tieMove hL hI.jEvExists hK hM)
    (fun i σ hσ hV => ?_) (fun i => @Half.updO D G _ _ Pl0 T0 A (setCE T c') iA R _ _ _ _ _ (B.O i))
    (fun i => @Half.omPins_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ _ _ B.O i (B.pins i)) B.rhoGeo
    (fun i σ hσ hV _ => hF'.2 i σ hσ hV) (fun i _ => ⟨1, hF'.1 i⟩) (fun i _ _ => hF'.1 i), rfl⟩
  obtain ⟨v, hv, h⟩ := bar_move hI.jEvBar hK hM i σ hσ hV
  exact ⟨fun _ => ⟨v, hv, h⟩, fun h' => absurd ⟨v, hv, (tieMove hL hI.jEvExists hK hM).jK i σ, h⟩ h'⟩

end Half

omit iA in
theorem phiC_setCE_of_eq {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) (e : c' j σ = T.cE j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC (setCE T c') hV a f = phiC T hV a f := by
  funext h
  rw [phiC_apply, phiC_apply]
  exact congrArg (fun c => (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) c) (rdU (T.U j σ) f) h) e

set_option maxHeartbeats 3200000 in

theorem exists_framed_half (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A}
    (hC : GlobalTheory.Core5 R F) (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hI : InGeo B) :
    ∃ (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G),
      (∀ i σ, w i σ ∈ Subgroup.center G) ∧
      (∀ (i : Fin D.R.m) hV, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R w) fun _ => 1,
        @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  classical
  choose c1 z hz hO hfr hs using exists_shift hP hsz hC B hU hI.jEvExists
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R B.fw.laws.toLawsM hC.lev ((B.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R B.κ B.v₀ B.O hC.lev ht hpb B.pins
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (c1 ⟨n, hn⟩)) ∧ (σ ≠ T.σ₀ → c = T.cE (n + 1) σ) := by
    intro n σ
    by_cases hσ : σ = T.σ₀
    · subst hσ
      by_cases hn : n < D.R.m
      · exact ⟨c1 ⟨n, hn⟩, fun _ => ⟨fun _ => HEq.rfl, fun h => absurd rfl h⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hn⟩
    · exact ⟨T.cE (n + 1) σ, fun _ => ⟨fun h => absurd h hσ, fun _ => rfl⟩⟩
  choose c hc using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = c1 i := fun i => eq_of_heq ((hc i T.σ₀ i.2).1 rfl)
  have h1 : ∀ (i : Fin D.R.m) σ, σ ≠ T.σ₀ → c i σ = T.cE ((i : ℕ) + 1) σ := fun i σ => (hc i σ i.2).2
  let c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ :=
    fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c
  let w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G := fun i σ => if σ = T.σ₀ then z i else 1
  have hK : ∀ i, ActKeeps (κ := B.κ) B.O i := fun i g f hf => by
    obtain ⟨k, hk, -⟩ := (B.pins i).2.lift.lev g
    exact ((hO i).1 g k hk f hf).1
  have hL : LawsJ (setCE T c') := lawsJ_setCE B.fw.laws fun j hj σ hσ => by
    cases j with
    | zero => exact fun _ => norm_one
    | succ n =>
      by_cases e : σ = T.σ₀
      · subst e
        have h : CUnit (c1 ⟨n, hj.2⟩) := (hO ⟨n, hj.2⟩).2.1.2.2.2.1
        rw [← h0 ⟨n, hj.2⟩] at h
        exact h
      · have h := B.fw.laws.cUnit _ hj σ hσ
        have e2 : c n σ = T.cE (n + 1) σ := h1 ⟨n, hj.2⟩ σ e
        rw [← e2] at h
        exact h
  have hM : Moves B c' w := fun i σ hσ hV f hf => by
    by_cases e : σ = T.σ₀
    · subst e
      rw [show w i T.σ₀ = z i from if_pos rfl]
      funext h
      rw [phiC_apply, phiC_apply]
      have h2 := hs i f hf h
      rw [← h0 i] at h2
      exact congrArg (_ * ·) h2
    · rw [show w i σ = 1 from if_neg e, phiC_setCE_of_eq hV (h1 i σ e)]
      have h2 := rho_e hK i 1 ⟨f, hf⟩
      rw [map_one] at h2
      have h3 := congrArg Subtype.val ((B.fw.e i).injective (Subtype.ext h2))
      exact congrArg _ h3
  have hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1 := by
    refine ⟨fun i => ?_, fun i σ hσ hV => ?_⟩
    · have h := hO i
      rw [← h0 i] at h
      exact h
    · by_cases e : σ = T.σ₀
      · subst e
        have h := GlobalTheory.RealGeoConst.eqAt_base T R B.κ B.v₀ hC.lev ht i (B.O i) (c1 i) (hO i).1 hV
        rw [← h0 i] at h
        exact h
      · have h := B.equivAll i σ hσ hV (hx i σ hσ hV)
        rw [← h1 i σ e] at h
        exact h
  refine ⟨c', overEmb T w, fun i σ => ?_, fun i hV => hfr i c' (h0 i) hV, exists_geoHalf_move hL hI hK hM hF⟩
  have key : ∀ s, w i s ∈ Subgroup.center G := fun s => by
    by_cases e : s = T.σ₀
    · rw [show w i s = z i from if_pos e]
      exact hz i
    · rw [show w i s = 1 from if_neg e]
      exact one_mem _
  unfold overEmb
  split_ifs
  · exact key _
  · exact key _

end GlobalTheory.Unframe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodBase
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist.BaseInhab

open GlobalTheory.ExportSeries

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

end GlobalTheory.ConjTwist.BaseInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitConstantCoverPullbackReadingStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitConstant_coverPullbackReading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ u : C.U₂.Comp → ℂ, (∀ k, ‖u k‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ h : GA D (T.V j σ), rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = u (C.dict₂ h).1 * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  first | exact @GlobalTheory.CoverConstAt.cover_read_const | exact GlobalTheory.CoverConstAt.cover_read_const | (intros; apply GlobalTheory.CoverConstAt.cover_read_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSideStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_preserves_supLattice_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D) j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j := by
  first | exact @GlobalTheory.HeckeSupReal.hkSupAt_realSide | exact GlobalTheory.HeckeSupReal.hkSupAt_realSide | (intros; apply GlobalTheory.HeckeSupReal.hkSupAt_realSide <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeStableAt

theorem heckeStable : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw)
    (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw)
    (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]),
    (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) →
    ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  intro hI D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j k P hk z C
  obtain ⟨hHP, hne⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace D T0 fw.laws i k P hk
  have hP' := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP
  obtain ⟨z', hz'⟩ := GlobalTheory.HeckePointLaw.heckePointLaws.2.1 D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l
    (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP' (PAt (embC YS iC b)) z.1 C
  obtain ⟨T, io, kk, h, y, u, hy, hu, w, hw, hb⟩ := z.2
  obtain ⟨C₀, w', hw', hb'⟩ := GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change _ _ _ _ _ _ P.asIdeal (charAt P) k hHP _ u w z.1 hb C z' hz'
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h
  have hpla : ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ∉ (placeAt (embC YS iC b)).asIdeal := by
    intro hm
    have hl := natCast_mem_placeAt (embC YS iC b)
    have hcop : Nat.Coprime (charAt P) (D.ntw.l i) :=
      (Nat.coprime_primes (charAt_prime P) (Fact.out : (D.ntw.l i).Prime)).2 hne
    obtain ⟨a, c, hac⟩ : IsCoprime ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T0.Q.c.F) :=
      Nat.Coprime.cast hcop
    exact (placeAt (embC YS iC b)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hac ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hl)))
  letI := io.toAlgebra
  have hint := GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField hI D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c
    (placeAt (embC YS iC b)) P.asIdeal (charAt P) k hHP hpla T io e he y hy (PAt (embC YS iC b)) h.alg w hw C₀ w' hw'
  obtain ⟨T', i', hi', j', hj', y', hy', -, w2, u2, hw2, hb2⟩ := hint
  letI := (i'.comp io).toAlgebra
  let jj : T'.Fr →+* ℂ_[D.ntw.l i] := (toCp (embC YS iC b)).comp j'.toRingHom
  have hjj : jj.comp i' = kk := RingHom.ext fun a => congrArg (toCp (embC YS iC b)) (DFunLike.congr_fun hj' a)
  have hR := GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h T' i' hi' jj hjj
  have hRa : hR.alg = j' := AlgHom.ext fun _ => rfl
  let u2' : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ :=
    fun a => Units.map (j'.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u2 a)
  have hbor := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ _ w2 w' z').2.2.1 u2' u hb2 hb'
  have hunit : ∀ a, ‖toCp (embC YS iC b) (u2' a)‖ = 1 := fun a => by
    have h1 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h2 : ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h3 : jj (algebraMap T'.V T'.Fr (u2 a : T'.V)) * jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    have h5 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ = 1 := by
      refine le_antisymm h1 (by_contra fun hlt => ?_)
      push_neg at hlt
      have : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ * ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ < 1 :=
        (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt
      exact this.ne h4
    exact h5
  have hnorm : ∀ a, ‖toCp (embC YS iC b) ((u * u2') a)‖ = 1 := fun a => by
    rw [Pi.mul_apply, Units.val_mul, map_mul, norm_mul, hu a, hunit a, one_mul]
  refine ⟨⟨z', T', i'.comp io, jj, hR, y', u * u2', hy', hnorm, w2, hRa ▸ hw2, hbor⟩, hz'⟩

end GlobalTheory.HeckeStableAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX Formalism.IndefR.FWT GlobalTheory.TwInputs NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTransform_cuspForms_reads_cosetSum : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D) (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i), GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV := by
  first | exact @GlobalTheory.HeckeSupReal.readsCusp_realSide | exact GlobalTheory.HeckeSupReal.readsCusp_realSide | (intros; apply GlobalTheory.HeckeSupReal.readsCusp_realSide <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlacesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_pullback_uniformisedLevelCover_places : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, (∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ la₂ ∈ S₂, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la₂, 0 ≤ v f₂ := by
  first | exact @GlobalTheory.CoverUpInt.pull_integral | exact GlobalTheory.CoverUpInt.pull_integral | (intros; apply GlobalTheory.CoverUpInt.pull_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadraticStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_of_weilField | exact GlobalTheory.JR.unitMatch_of_weilField | (intros; apply GlobalTheory.JR.unitMatch_of_weilField <;> assumption)
end


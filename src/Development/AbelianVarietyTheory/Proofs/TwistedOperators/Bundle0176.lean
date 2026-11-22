import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPlaces

theorem pg_nonempty {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) : L.Pg.Nonempty := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty ((L.C.P.pb 0).asIdeal.primesOver (𝓞 D.host.E)))
  have hne : W ≠ ⊥ := by
    rintro rfl
    have := hWQ.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
    exact (L.C.P.pb 0).ne_bot this
  exact ⟨⟨W, hW, hne⟩, (hL.Pg _).2 ⟨0, HeightOneSpectrum.ext hWQ.over.symm⟩⟩

theorem two_not_mem {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (t : T0) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : PP ∈ L.Pg ∨ PP ∈ L.Q t) : (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
  rcases h with hm | hm
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
    have hn := GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
      (Formalism.L2.Pj.g_ne_two D k) hgk
    simpa using hn
  · intro h2
    apply (hL.Q_off t PP hm).1
    push_cast
    have hQS : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      rw [hc]
      push_cast
      exact Ideal.mul_mem_right _ _ h2
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hQS))

theorem mem_levG {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i))
    (hk : k ∈ GfC (Wc D i)) (hS : Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i))
    (hr : ∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) :
    k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) := by
  refine Subgroup.mem_inf.2 ⟨hk, ?_⟩
  show Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Wc D i).gram (L.βW i) (L.datWp i L.triv)
  refine GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (L.βW i) (L.datWp i L.triv) _
    (GlobalTheory.LevSplit.finE_mem_UA _ k) hS (fun PP hP => ?_)
  rcases hP with hP | hP
  · exact hr PP hP
  · exact absurd hP (Finset.notMem_empty _)

theorem places_level : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → L.Pg.Nonempty ∧ (∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ ∀ (i : Fin D.R.m) (k : GA D (Wc D i)), k ∈ GfC (Wc D i) → Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i) → (∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) → k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  intro D T0 L μ0 hL
  refine ⟨pg_nonempty hL, fun t PP h => two_not_mem hL t PP h, fun i k hk hS hr => ⟨mem_levG L i k hk hS hr, ?_⟩⟩
  exact GlobalTheory.HolRead.PrincLevelSub.levChi_triv L i k

end GlobalTheory.SpanPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalIffRecord
section
noncomputable section

open Module NumberField
open scoped InnerProductSpace

namespace GlobalTheory.LiftTestCompare

section Lin

open Matrix

variable {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

def FunTest (S : Set W) : Prop :=
  ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ W), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧ ∀ s ∈ S, ∀ i, ψ i s ∈ Set.range σ

def SpanTest (S : Set W) : Prop :=
  ∃ (m : ℕ) (v : Fin m → W), LinearIndependent ℂ v ∧ ∀ s ∈ S, ∃ a : Fin m → K, s = ∑ i, σ (a i) • v i

end Lin

section Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

def liftsAll (j : Bs.J) : Set (X.W j) := {w | ∃ (t : Bs.Tup) (x : A.FL j t), X.θ' j t (X.jL j t x) = w}

def liftsAt (j : Bs.J) (t : Bs.Tup) : Set (X.W j) := {w | ∃ x : A.FL j t, X.θ' j t (X.jL j t x) = w}

def levelBasis (b : Bool) (j : Bs.J) : Set (X.W j) := Set.range fun k : Fin (X.dW b j) => X.w0C b j (Pi.single k 1)

def LevelIn (b : Bool) (V : ∀ j t, Submodule K (A.FL j t)) : Prop :=
  ∀ j t, ∀ x ∈ V j t, X.θ' j t (X.jL j t x) ∈ LinearMap.range (X.w0C b j)

theorem liftTest_of_liftTestB {b : Bool} (h : LiftTestB X b) : LiftTest X := fun j => by
  obtain ⟨N, ψ, h1, h2, -⟩ := h j
  exact ⟨N, ψ, h1, h2⟩

end Cx

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Real

section ArchimedeanLeafBounds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem toCx3_liftTestB (b : Bool) :
    LiftTestB (R.toCx3 F) b ↔ LiftTestB (cxPhase R.toRealDat F.lv2 fun j => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j)) b := by
  rw [cxPhase_eq]
  simp only [cj_cj]
  exact Iff.rfl

end ArchimedeanLeafBounds

end GlobalTheory.LiftTestCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalFactorUnitary

variable {D : D7}

theorem actO_gAt_of_wAt_eq_zero (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : wAt p u = 0) : actO S T (gAt S p g) (gAt T p h) u = u := by
  obtain ⟨hsplit, hcomm⟩ := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g h u
  have hz : idem D p • actO S T g h u = 0 := by
    rw [← wAt_eq_smul, hcomm, hu]
    unfold actO
    simp
  have hrest : (1 - idem D p) • u = u := by
    rw [sub_smul, one_smul, ← wAt_eq_smul, hu, sub_zero]
  rw [hsplit, hz, hrest, zero_add]

theorem compAt_mt_gAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (p : Place D) (g : GA D V) (τ : D.what₂.Tau)
    (hτ : Sum.inr τ ≠ p) : compAt θ τ (Formalism.L2.Theta.mt V (gAt V p g)) = 1 := by
  have h0 : (θ τ) ((infPart D) (idem D p)) = 0 := by
    obtain ⟨-, -, -, hfin, -, -, hinf⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
    rcases p with v | τ'
    · rw [(hfin v).1, map_zero]
    · have hne : τ' ≠ τ := fun e => hτ (by subst e; rfl)
      exact (hinf θ hθ τ).2 τ' hne
  unfold compAt
  rw [((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1 V p g).1]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
    map_one, h0, zero_mul, zero_add, sub_zero, one_mul]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLocal_om_gAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT hW hθ p f hf g h
  unfold IsLocal IsLatVac IsFockVacAt at hf ⊢
  obtain ⟨hth, ⟨hdbl, hhalf⟩, hfock⟩ := hf
  have hoff : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun v => Sum.inl v ≠ p), wAt p u = 0 := fun u hu =>
    (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 (fun _ hv => hv)
  refine ⟨hW.om_pres _ f hth, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have hw2 : wAt p (2 • u) = 0 := by
      rw [wAt_eq_smul, smul_comm, ← wAt_eq_smul, hoff u hu, smul_zero]
    have key := hW.om_heis (gAt S p g) (gAt T p h) (2 • u) f hth
    rw [hdbl u hu, actO_gAt_of_wAt_eq_zero S T p g h (2 • u) hw2] at key
    exact key.symm
  · intro e he u hu hu'
    have key := hW.om_heis (gAt S p g) (gAt T p h) u f hth
    rw [hhalf e he u hu hu', actO_gAt_of_wAt_eq_zero S T p g h u (hoff u hu)] at key
    exact key.symm
  · intro τ hτ z
    have hT1 : compAt θ τ (Formalism.L2.Theta.mt T (gAt T p h)) = 1 := compAt_mt_gAt hθ T p h τ hτ
    have hS1 : compAt θ τ (Formalism.L2.Theta.mt S (gAt S p g)⁻¹) = 1 := by
      rw [← gAt_inv]
      exact compAt_mt_gAt hθ S p g⁻¹ τ hτ
    have e1 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ z hth
    have e2 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ (cplxO (sS τ) (sT τ) z) hth
    rw [hT1, hS1, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have hz := hfock τ hτ z
    unfold annih at hz ⊢
    rw [← e1, ← e2, ← map_smul, ← map_add, hz, map_zero]

end GlobalTheory.LocalFactorUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLevelDatumEqFunctionOfResidueReductionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLevelDatum_eq_function_of_residueReduction : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  first | exact @GlobalTheory.StepVec.locDatum_eq_viaRed | exact GlobalTheory.StepVec.locDatum_eq_viaRed | (intros; apply GlobalTheory.StepVec.locDatum_eq_viaRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem frPinv_mul_frP : frPinv S b * frP S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem frameMatrix_mul_frameMatrixInv : frP S b * frPinv S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

def frPinvGL : GL (Fin S.rank) (Lev.EAf D) :=
  ⟨(frPinv S b).map (eToEAf D), (frP S b).map (eToEAf D),
    by rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _),
    by rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)⟩

theorem frPinvGL_inv_val : (frPinvGL S b)⁻¹.val = (frP S b).map (eToEAf D) := rfl

def reWi (x : WO S T) : WO (reS S b) T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frP S b).map (incA D))

theorem mapA_frPinv_mul_frP : (frPinv S b).map (incA D) * (frP S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_frP_mul_map_frPinv : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem reW_reWi (x : WO S T) : reW S T b (reWi S T b x) = x := by
  unfold reW reWi
  rw [Matrix.mul_assoc, map_frP_mul_map_frPinv, Matrix.mul_one]

theorem reWi_reW (x : WO (reS S b) T) : reWi S T b (reW S T b x) = x := by
  have h := Matrix.mul_assoc (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x) ((frPinv S b).map (incA D))
    ((frP S b).map (incA D))
  rw [mapA_frPinv_mul_frP, Matrix.mul_one] at h
  exact h

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul _ _ _

def reWHom : WO (reS S b) T →+ WO S T := AddMonoidHom.mk' (reW S T b) (reW_add S T b)

theorem reW_nsmul (k : ℕ) (x : WO (reS S b) T) : reW S T b (k • x) = k • reW S T b x :=
  map_nsmul (reWHom S T b) k x

theorem reW_bijective : Function.Bijective (reW S T b) :=
  Function.bijective_iff_has_inverse.2 ⟨reWi S T b, reWi_reW S T b, reW_reWi S T b⟩

theorem isHalf_reW_iff (e : AE D) (x : WO (reS S b) T) : IsHalf e (reW S T b x) ↔ IsHalf e x := by
  have key : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) (AE D)),
      IsHalf e M → IsHalf e (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) M N) := by
    intro M N h i j
    simp only [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, h i l]
  constructor
  · intro h
    have h2 := key _ ((frP S b).map (incA D)) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · intro h
    exact key x _ h

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ)
    (hs : ∀ x y, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T u (reF S T b f) = reF S T b (heisO ψ S T (reW S T b u) f) := by
  funext w
  simp only [heisO, reF_apply, symplOH, hs, reW_add]

end GlobalTheory.AdSpan.ReVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.ParabConj

theorem stdBlocks_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s} (i : Fin (d a)) (j : Fin (d b))
    (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_stdMaxParab_of_le_conjBy (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r) (g : GL (Fin r) F) (H : parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h)) :
    g ∈ stdMaxParab F h := by
  by_contra hg
  have hg' := hg
  rw [mem_stdMaxParab] at hg'
  push Not at hg'
  obtain ⟨q, j, hj, hq, hne⟩ := hg'
  refine hg (inv_mem_iff.1 ((mem_stdMaxParab h).2 fun i p hp hi => ?_))
  have hpq : p < q := by rw [Fin.lt_def]; omega
  let t : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection p q (1 : F))
    (by rw [Matrix.det_transvection_of_ne p q hpq.ne]; exact one_ne_zero)
  have ht : (t : Matrix (Fin r) (Fin r) F) = 1 + Matrix.single p q 1 := rfl
  have htP : t ∈ parab F (stdBlocks d hd) := by
    refine mem_parab_iff.2 fun x y u v hyx => ?_
    have hlt := stdBlocks_lt d hd u v hyx
    rw [ht, Matrix.add_apply, Matrix.one_apply_ne hlt.ne', zero_add]
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨e1, e2⟩
    rw [← e1, ← e2] at hlt
    exact lt_asymm hlt hpq
  have h0 := (mem_stdMaxParab h).1 (mem_conjBy.1 (H htP)) i j hj hi
  have hij : i ≠ j := by rintro rfl; omega
  have hmul : ((g⁻¹ * t * g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * Matrix.single p q (1 : F) *
        (g : Matrix (Fin r) (Fin r) F) := by
    rw [Units.val_mul, Units.val_mul, ht, mul_add, add_mul, mul_one, Units.inv_mul]
  rw [hmul, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, Matrix.mul_apply,
    Finset.sum_eq_single q (fun x _ hx => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]) (by simp),
    Matrix.mul_single_apply_same, mul_one] at h0
  exact (mul_eq_zero.1 h0).resolve_right hne

end GlobalTheory.ParabConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
section
noncomputable section

namespace GlobalTheory.GaussLine

open Complex NumberField

def heisFun {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p)

def dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : V → ℂ)
    (x : V) : ℂ :=
  fderiv ℝ f x w.1 - 2 * Real.pi * Complex.I * (β x w.2 : ℂ) * f x

variable (F : Type) [Field F] [NumberField F]

def pairInf (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun c x y => by simp [smul_mul_assoc, ← Finset.smul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c x y => by simp [mul_smul_comm, ← Finset.smul_sum])

theorem pairInf_apply (κ : Type) [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    pairInf F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

theorem heisFun_apply {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) (x : V) :
    heisFun β p q f x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p) := rfl

end GlobalTheory.GaussLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOverStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeIdempotent_under_eq_of_lies_over : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → PP.under (𝓞 D.host.F) = v := by
  first | exact @GlobalTheory.IdemUnder.under_eq_of_isIdemAt | exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt | (intros; apply GlobalTheory.IdemUnder.under_eq_of_isIdemAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdResidueFunctionsHalfSumIdempotentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_residueFunctions_half_sum_idempotents : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (s : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D),
    (∀ PP ∈ s, Formalism.L2.NTheta.IsIdemAt (es PP) PP) →
    ∀ (ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) (t : WO S T),
      IsHalf (∑ PP ∈ s, es PP) t →
      (open Classical in (if IsIntM (frMapO S T βS βT t) then ∏ PP ∈ s, ω PP (redM PP (frMapO S T βS βT t)) else 0)) =
        ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t) := by
  first | exact @GlobalTheory.StepVec.prod_locFn_half | exact GlobalTheory.StepVec.prod_locFn_half | (intros; apply GlobalTheory.StepVec.prod_locFn_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
section
noncomputable section

namespace GlobalTheory.HoweGlobalPair

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def opInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Set (Module.End ℂ ↥(M.Pol ψ emb)) :=
  {g | (∃ k ∈ KInf σ W emb, ∀ f : ↥(M.Pol ψ emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin n × Fin d)) ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ W, ∀ f : ↥(M.Pol ψ emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin n × Fin d))
        ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)}

def relInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Submodule ℂ ↥(M.Pol ψ emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ X, ∃ f ∈ M.Pol ψ emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin n × Fin d))) ∨
    ∃ k ∈ KInf σ X emb, ∃ f f₁ : ↥(M.Pol ψ emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin n × Fin d)) ⇑(f₁ : SInf F (Fin n × Fin d)) ∧ x = f₁ - f}

def opFin (om : Rep σ X W) (v : Pl F) : Set (Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v))) :=
  {g | ∃ h ∈ UAt σ W (evFin F v), ∀ φ : ↥(SB (Fin n × Fin d → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin n × Fin d → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ)}

def relFin (om : Rep σ X W) (v : Pl F) : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
  (augAt om v).comap (SB (Fin n × Fin d → Fv F v)).subtype

end GlobalTheory.HoweGlobalPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidueStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TameSplitChar.char_eq_prod_res | exact GlobalTheory.TameSplitChar.char_eq_prod_res | (intros; apply GlobalTheory.TameSplitChar.char_eq_prod_res <;> assumption)
end


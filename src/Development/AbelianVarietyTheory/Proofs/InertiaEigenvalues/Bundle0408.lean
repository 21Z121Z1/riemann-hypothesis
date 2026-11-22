import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModel

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CobCrisLift

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem tmul_mem (v : V) {a : ℤ} {b : BdR} (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] (⟨b, hb⟩ : (PD.Fil a).restrictScalars Qp), by simp⟩

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [AlgebraTensorModule.map_tmul]
    exact tmul_mem PD _ (PD.Fil_anti a b.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem filV_exhaustive (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem PD v ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem φVB_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ιV_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sub_φ_mem_Dcris (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  refine (Submodule.mem_iInf _).2 fun g => ?_
  have h1 : φVB PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : B) := by
    simp [φVB]
  rw [hx g, map_sub, φVB_act] at h1
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_sub_sub_comm, h1,
    sub_self]

theorem act_ιV_sub_mem (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g : G) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) - ιV PD (LL := LL) (V := V) x ∈
      FilV PD (LL := LL) (V := V) 0 := by
  rw [← ιV_act, ← map_sub, ← hx g]
  have h1 : ιV PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : BdR) := by
    simp [ιV]
  rw [h1]
  exact tmul_mem PD _ PD.one_mem

end General

theorem coboundary_lift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → ∀ (c : ↥(GK K) → A.V) (x : A.V ⊗[ℚ_[l]] P.R.B), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x) → x - φVB (P.PD K) (LL := LL) (V := A.V) x ∈ Dcris (P.PD K) A.ρ ∧ ∃ d ∈ DdR (P.PD K) A.ρ, ιV (P.PD K) (LL := LL) (V := A.V) x - d ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 := by
  intro l _ P AI hT K LL _ _ _ O _ _ hO A hdR c x hx
  refine ⟨sub_φ_mem_Dcris (P.PD K) A.ρ c x hx, ?_⟩
  obtain ⟨a, ha⟩ := filV_exhaustive (P.PD K) (LL := LL) (ιV (P.PD K) (LL := LL) (V := A.V) x)
  obtain ⟨w, hw, hw'⟩ := GlobalTheory.TateFilQuotTied.tied_tate_fil_quot l P AI hT K LL O hO A hdR a 0 _ ha
    (act_ιV_sub_mem (P.PD K) A.ρ c x hx)
  exact ⟨w, hw.1, hw'⟩

end GlobalTheory.CobCrisLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupCoboundary
section
namespace GlobalTheory.BKCup

section Bridge

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.BKDimNoInv
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in
theorem cup_cob {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hr' : Continuous fun g => ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hBK : bkACore (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (c c' : ↥(GK Bw.Kw) → Fin m → ↥Bw.LL.1) (y y' : ↥Gw → Fin m → O)
    (hc : c ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r)) (hc' : c' ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r'))
    (hy : ∀ g a, c (Bw.e g) a = Bw.toLL (y g a)) (hy' : ∀ g a, c' (Bw.e g) a = Bw.toLL (y' g a)) :
    ∃ f : ↥Gw → ↥Bw.LL.1, Continuous f ∧ ∀ g h : ↥Gw,
      Bw.toLL (y g ⬝ᵥ ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).mulVec (y' h)) =
        Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  let A' := grepOf Bw r' hr'
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  let Q : (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] ↥Bw.LL.1 :=
    dotProductBilin ↥Bw.LL.1 ↥Bw.LL.1
  have hD : IsDual1 (P.PD Bw.Kw) (Bw.rep r) (Bw.rep r') Q := by
    refine ⟨fun g x z => ?_, fun x hx => ?_, fun z hz => ?_, rfl⟩
    · change Bw.rep r g x ⬝ᵥ Bw.rep r' g z = _ * (x ⬝ᵥ z)
      rw [rep_apply, rep_apply, hd, dot_dual, cycLL_eq]
    · exact dotProduct_eq_zero x hx
    · exact dotProduct_eq_zero z fun x => (dotProduct_comm _ _).trans (hz x)
  obtain ⟨f, hf, hf'⟩ := (((hBK _ _ hG A A' Q hA hD).1 c hc.1).1 hc) c' hc'
  refine ⟨f ∘ Bw.e, hf.comp Bw.e_cont, fun g h => ?_⟩
  have h1 : ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) * f (Bw.e h) - f (Bw.e g * Bw.e h) +
      f (Bw.e g) = c (Bw.e g) ⬝ᵥ Bw.rep r' (Bw.e g) (c' (Bw.e h)) := congrFun hf' (Bw.e g, Bw.e h)
  rw [cycLL_eq, rep_apply, MulEquiv.symm_apply_apply, ← map_mul] at h1
  refine Eq.trans ?_ h1.symm
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, hy, hy']

end Bridge

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem cup_coboundary : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (c c' : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1) (y y' : ↥(DecV N v) → Fin D.R.r → X.O0 i), c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) → c' ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) → (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) → (∀ g a, c' ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y' g a)) → ∃ f : ↥(DecV N v) → ↥(bkP.br i v hv).LL.1, Continuous f ∧ ∀ g h : ↥(DecV N v), (bkP.br i v hv).toLL (y g ⬝ᵥ ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).mulVec (y' h)) = (bkP.br i v hv).toLL (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) * f h - f (g * h) + f g := by
  intro D N X bkP i s h ρ hρ v hv c c' y y' hc hc' hy hy'
  haveI : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed D.host.E
  refine cup_cob (bkP.br i v hv) (D.loc (X.l i)) ((Tgl i s).comp (DecV N v).subtype) (ρ.comp (DecV N v).subtype)
    ?_ ?_ (fun g => ?_) (h.2.2.2.2.2.1 _ _).1 (h.1.2.1 v hv (Tgl i s) (Or.inr rfl)).1 c c' y y' hc hc' hy hy'
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tmat i s).comp continuous_subtype_val).congr fun g => (Tgl_coe i s g).symm
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp continuous_subtype_val).congr fun g => (hρ g).symm
  · refine (hρ g).trans ?_
    rw [Tdual, ← Tgl_coe]
    rfl

end GlobalTheory.BKCup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_algebraicClosure_mem_deRhamFil_zero (P : LocPrime l) (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)
  rw [P.PD_Fil (botExt l) K 0]
  exact h2

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  show (frobUr l ^ 0) c = c
  rw [pow_zero]
  rfl

theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)
  rw [pow_add]
  rfl

theorem fr_mul_self {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (q : ℕ) : fr l (r * q) c = c := by
  induction q with
  | zero => simpa using fr_zero c
  | succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]

theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (m : ℕ) : fr l m c = fr l (m % r) c := by
  conv_lhs => rw [← Nat.mod_add_div m r]
  rw [fr_add, fr_mul_self hc]

variable (P : LocPrime l) {K : FinExt l} {n : Type} [Fintype n] [DecidableEq n]

theorem matD_mod {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) (m : ℕ) (g : ↥(GK K)) :
    matD P ρ m g = matD P ρ (m % r) g := by
  ext i j
  simp only [matD, Matrix.map_apply]
  rw [fr_mod (h.rat g i j) m]

theorem matD_mem (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) (i j : n) :
    matD P ρ m g i j ∈ Fil P 0 := by
  simp only [matD, Matrix.map_apply, kd, RingHom.comp_apply]
  exact algebraMap_algebraicClosure_mem_deRhamFil_zero P _

end GlobalTheory.PMon.FrameEquiv

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem tz_facts {AI : LocAinf l P} (T : LocTied l P AI) :
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P _ T
  exact ⟨hact, hadd, h0⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tDiag (h : ∀ a : ℤ, tz P a * tz P (-a) = 1) (a : n → ℤ) : GL n P.R.BdR where
  val := Matrix.diagonal fun j => tz P (a j)
  inv := Matrix.diagonal fun j => tz P (-a j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : ∀ j, tz P (-a j) * tz P (a j) = 1 := fun j => by simpa using h (-a j)
    simp [this]

theorem frameEx : FrameEx := by
  intro l _ P AI T n _ _ K r ρ hρ
  constructor
  · intro hD
    have H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K),
        matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
          (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
            algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := fun m => by
      obtain ⟨Q, hQ⟩ := hD m
      exact GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ
    choose U w hU using H
    exact ⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩
  · rintro ⟨w, hw⟩ m
    obtain ⟨hact, hadd, h0⟩ := tz_facts P T
    have hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1 := fun a => by rw [← hadd, add_neg_cancel, h0]
    let k : Fin r := ⟨m % r, Nat.mod_lt _ hρ.pos⟩
    obtain ⟨U, -, hU⟩ := hw k
    refine ⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩
    have hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) =
        X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l)) := fun X Y =>
      Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))
    have hm : matD P ρ m g = matD P ρ (k : ℕ) g := matD_mod P hρ m g
    rw [Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]
    congr 1
    show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) =
      Matrix.diagonal fun j => tz P (-w k j)
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]

end GlobalTheory.PMon.FrameEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
section
noncomputable section

namespace GlobalTheory.DecLocal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem exists_place_below : ∀ {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ w : HeightOneSpectrum (𝓞 F), w ∈ Formalism.BasicNotions.placesOver F p ∧ IsPlaceOver A w := by
  intro p _ F Ω _ _ _ _ A hp
  have hint : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let f : 𝓞 F →+* A := RingHom.codRestrict ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)) A hint
  let I : Ideal (𝓞 F) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 F, x ∈ I ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := fun x => by
    change f x ∈ IsLocalRing.maximalIdeal A ↔ _
    exact ValuationSubring.valuation_lt_one_iff A (f x)
  have hpI : ((p : 𝓞 F)) ∈ I := by
    rw [hI]; simpa using hp
  have hp0 : ((p : 𝓞 F)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let w : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := I, isPrime := Ideal.comap_isPrime f _,
      ne_bot := fun h => hp0 (by rw [← Ideal.mem_bot, ← h]; exact hpI) }
  exact ⟨w, hpI, fun x => (hI x).symm⟩

theorem exists_root_of_unity : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl p)
    (n : ℕ) (z : PadicAlgCl p), z ^ (p ^ n) = 1 → ∃ y : Ω, y ^ (p ^ n) = 1 ∧ j y = z := by
  intro p _ Ω _ _ j n z hz
  have hf : ((X ^ (p ^ n) - 1 : Polynomial Ω).map j) = X ^ (p ^ n) - 1 := by simp
  have hne : (X ^ (p ^ n) - 1 : Polynomial (PadicAlgCl p)) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) (1 : PadicAlgCl p)
  have hz' : z ∈ ((X ^ (p ^ n) - 1 : Polynomial Ω).map j).roots := by
    rw [hf, mem_roots hne]; simp [hz]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  refine ⟨y, ?_, rfl⟩
  have := isRoot_of_mem_roots hy
  simpa [sub_eq_zero] using this

theorem norm_lt_one_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p)
    (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : ‖j y‖ < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', hA, hA]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < ‖j y‖ := norm_pos_iff.2 ((map_ne_zero j).2 hy)
    rw [map_inv₀, norm_inv]
    simp only [hy, false_or]
    constructor
    · intro h
      exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
    · rintro ⟨h1, h2⟩
      refine lt_of_le_of_ne h1 fun h => h2 ?_
      rw [h, inv_one]

theorem finrank_closure_eq_locDeg : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v →
      Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x))) =
        locDeg v := by
  intro p _ F Ω _ _ _ _ A j hA v hv
  let φ : F →+* PadicAlgCl p := j.comp (algebraMap F Ω)
  obtain ⟨v', -, hφ⟩ := PI.CompDegEF.placeProp p F φ
  have hvp : v ∈ Formalism.BasicNotions.placesOver F p := by
    show ((p : 𝓞 F)) ∈ v.asIdeal
    rw [← hv, ← norm_lt_one_iff A j hA]
    simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := p)
  exact PI.CompDegEF.locDegOf_of PI.CompDegEF.ballCard PI.CompDegEF.denseSurj PI.CompDegEF.kerProp
    PI.CompDegEF.normCard p F φ ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range φ⟩
    (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
    (GlobalTheory.PlaceBridge.adjoin_range_subset_closure φ) v hvp
    (fun x => ⟨(hφ x).1, (norm_lt_one_iff A j hA _).trans (hv x)⟩)

theorem decEquiv : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  intro p _ F Ω _ _ _ _ _ A hp
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨w, hw, hAw⟩ := exists_place_below (F := F) A hp
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding F Ω w A hw hAw
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois p F Ω A j hj
  refine ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω)), i, ?_,
    fun g => GlobalTheory.T.localInertia_iff_mem_placeInertia p F Ω A j hj _ i.toMulEquiv hi g,
    fun v hv => finrank_closure_eq_locDeg p F Ω A j hj v hv⟩
  intro O _ ε hε g n ζ hζ
  obtain ⟨y, hy, rfl⟩ := exists_root_of_unity p Ω j n ζ hζ
  obtain ⟨a, ha, ha'⟩ := hε (i.symm g) n y hy
  refine ⟨a, ?_, ha'⟩
  have e := hi (i.symm g) y
  rw [ContinuousMulEquiv.apply_symm_apply] at e
  rw [e, ha, map_pow]

end GlobalTheory.DecLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSuccStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  first | exact @GlobalTheory.BSP.delta_pow_succ_mem_pow | exact GlobalTheory.BSP.delta_pow_succ_mem_pow | (intros; apply GlobalTheory.BSP.delta_pow_succ_mem_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deltaRingHom_unique_of_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  first | exact @GlobalTheory.BSP.deltaHom_unique_of_base | exact GlobalTheory.BSP.deltaHom_unique_of_base | (intros; apply GlobalTheory.BSP.deltaHom_unique_of_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusCommStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deltaRingStructure_delta_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A), D.δ (D.φ a) = D.φ (D.δ a) := by
  first | exact @GlobalTheory.BSP.Delta.δ_φ_comm | exact GlobalTheory.BSP.Delta.δ_φ_comm | (intros; apply GlobalTheory.BSP.Delta.δ_φ_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingData
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.AdmDepthZero

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  intro D P h i k v PI τ hτ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro hsq hu
  obtain ⟨ρ, hρ, he⟩ := GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent (D.host.g k) D.R.r (P.lz k) τ
  have hO := PairedCharacterCondition.RT.ktyTie_of_spec P i PI k v τ hτ
  rw [he] at hO
  have hs : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k ((P.lz k).lab τ) =
      Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
    rw [← he]
    exact PairedCharacterCondition.RT.idem_mul_eSer P k τ
  exact h i k v PI ρ _ hρ hs hO hsq hu

end GlobalTheory.AdmDepthZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicCompleteStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  first | exact @GlobalTheory.BKReal.eisPoly_distinguished_complete | exact GlobalTheory.BKReal.eisPoly_distinguished_complete | (intros; apply GlobalTheory.BKReal.eisPoly_distinguished_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  first | exact @GlobalTheory.AinfEPow.ePow_facts | exact GlobalTheory.AinfEPow.ePow_facts | (intros; apply GlobalTheory.AinfEPow.ePow_facts; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMinpolyUniformizerWittTotallyRamifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∀ π : O, Irreducible π → ∃ Ep : Polynomial (Wq l a), Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  first | exact @GlobalTheory.TotRam.eisenstein_minpoly_Wq | exact GlobalTheory.TotRam.eisenstein_minpoly_Wq | (intros; apply GlobalTheory.TotRam.eisenstein_minpoly_Wq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRealisation_indep_ainfModel : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  first | exact @GlobalTheory.Prism.realisation_indep_model | exact GlobalTheory.Prism.realisation_indep_model | (intros; apply GlobalTheory.Prism.realisation_indep_model <;> assumption)
end


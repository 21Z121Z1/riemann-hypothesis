import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutMult

open scoped InnerProductSpace
open GlobalTheory.Cusp

open Classical in

theorem rank_homIn_eq_rank_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} (hirr : σ.IsIrreducible)
    (hadm : IsAdmissible σ) (hcopy : IsCopyFinDS σ M π ⊤) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : GA D V →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) {U : Submodule ℂ K} (hU : IsClosed (U : Set K)) :
    Module.rank ℂ (homIn π ρ U) = Module.rank ℂ (homFinDS σ M ρ U) := by
  obtain ⟨T, hT, hinj, hd⟩ := hcopy
  have hTm := mem_homTensorPi.1 hT
  let f : homIn π ρ U →ₗ[ℂ] (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) :=
    { toFun := fun A => (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H K (A : H →L[ℂ] K)).toLinearMap ∘ₗ T
      map_add' := fun A B => by ext w y; simp
      map_smul' := fun c A => by ext w y; simp }
  have hmem : ∀ A, f A ∈ homFinDS σ M ρ U := fun A => by
    refine mem_homTensorPi.2 ⟨fun w y => ?_, fun g w y => ?_, fun i g w y => ?_⟩
    · exact A.2.1 _
    · change (A : H →L[ℂ] K) (T (σ g w) y) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.1 g w y)).trans (A.2.2 _ _)
    · change (A : H →L[ℂ] K) (T w _) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.2 i g w y)).trans (A.2.2 _ _)
  let F : homIn π ρ U →ₗ[ℂ] homFinDS σ M ρ U := f.codRestrict _ hmem
  have hdense : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  have hbij : Function.Bijective F := by
    constructor
    · intro A B hAB
      have e : ∀ w y, (A : H →L[ℂ] K) (T w y) = (B : H →L[ℂ] K) (T w y) := fun w y =>
        congrArg (fun Φ : homFinDS σ M ρ U => ((Φ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) w) y) hAB
      refine Subtype.ext (ContinuousLinearMap.ext_on hdense ?_)
      rintro _ ⟨w, y, rfl⟩
      exact e w y
    · intro Φ
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hirr hadm H π hπ T hT hinj hd K ρ hρ U hU Φ.1 Φ.2
      exact ⟨⟨A, hA⟩, Subtype.ext (LinearMap.ext fun w => ContinuousMultilinearMap.ext fun y => hAe w y)⟩
  exact (LinearEquiv.ofBijective F hbij).rank_eq

open Classical in

theorem mCusp_eq_mCuspDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  intro D V S M μ _ _ H _ _ π hπ W _ _ σ hirr hadm hcopy
  haveI : CompleteSpace H := hπ.complete
  exact rank_homIn_eq_rank_homFinDS hπ.unitary hirr hadm hcopy (isUnitaryRep_RG V μ) (isSubrep_L2cusp V μ).1

end GlobalTheory.AutMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMaps
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult.MultAssembly

open GlobalTheory.CuspMult

variable {D : D7} {θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem continuous_of_mem_allMaps {T : MMap M} (hT : T ∈ allMaps θ M) (v : M.Vec) : Continuous (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact (hT.aut v).cont
  | zero => exact continuous_const
  | add T T' _ _ ih ih' => exact ih.add ih'
  | smul a T _ ih => exact ih.const_smul a

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def Represents (Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)) (T : MMap M) : Prop :=
  ∀ v : M.Vec, lift (GQ V) (Φ fun τ => (v τ : M.H τ)) =ᵐ[μ] T v

variable {μ}

theorem eq_of_represents_cont {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T T' : MMap M}
    (hT : ∀ v, Continuous (T v)) (hT' : ∀ v, Continuous (T' v)) (h : Represents μ Φ T) (h' : Represents μ Φ T') :
    T = T' :=
  MultilinearMap.ext fun v => (hT v).ae_eq_iff_eq μ (hT' v) |>.1 ((h v).symm.trans (h' v))

theorem represents_zero : Represents μ (0 : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)) 0 := fun _ => by
  simp only [ContinuousMultilinearMap.zero_apply, MultilinearMap.zero_apply]
  exact ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)

theorem Represents.add {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T T' : MMap M} (h : Represents μ Φ T)
    (h' : Represents μ Φ' T') : Represents μ (Φ + Φ') (T + T') := fun v => by
  simp only [ContinuousMultilinearMap.add_apply, MultilinearMap.add_apply]
  exact lift_add_ae (h v) (h' v)

theorem Represents.smul (c : ℂ) {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M} (h : Represents μ Φ T) :
    Represents μ (c • Φ) (c • T) := fun v => by
  simp only [ContinuousMultilinearMap.smul_apply, MultilinearMap.smul_apply]
  exact lift_smul_ae c (h v)

theorem Represents.translate (g : GfC V) {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M}
    (h : Represents μ Φ T) :
    Represents μ (postRepPi M.H ((RG V μ).comp (GfC V).subtype) g Φ) (finRep M g T) := fun v =>
  (lift_R (g : GA D V) _).trans ((measurePreserving_mul_right μ (g : GA D V)).quasiMeasurePreserving.ae (h v))

theorem Represents.translate' (g : GfC V) {Φ Φ' : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} {T : MMap M}
    (h : Represents μ Φ T) (h' : ∀ y, Φ' y = RG V μ (g : GA D V) (Φ y)) : Represents μ Φ' (finRep M g T) := fun v => by
  rw [h']
  exact (lift_R (g : GA D V) _).trans ((measurePreserving_mul_right μ (g : GA D V)).quasiMeasurePreserving.ae (h v))

variable (μ) in

def phiOf (T : MMap M) : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ) :=
  open Classical in
  if h : ∃ Φ, Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ Φ T then h.choose else 0

theorem phiOf_spec (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {T : MMap M} (hT : T ∈ allMaps θ M) :
    phiOf μ T ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ (phiOf μ T) T := by
  have h : ∃ Φ, Φ ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ∧ Represents μ Φ T :=
    (GlobalTheory.CuspIntertwiner.existsUnique_intertwiner hP D θ hθ V S M μ T hT).exists
  rw [phiOf, dif_pos h]
  exact h.choose_spec

theorem phiOf_eq (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {T : MMap M} (hT : T ∈ allMaps θ M)
    {Φ : ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ)} (h : Represents μ Φ T) : phiOf μ T = Φ :=
  GlobalTheory.CuspIntertwiner.eq_of_represents (phiOf_spec hP hθ hT).2 h

variable {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

variable (μ) in

def homOf (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (f : W →ₗ[ℂ] MMap M) (hf : ∀ w, f w ∈ allMaps θ M) :
    W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H (DividedPowerChartLift V μ) where
  toFun w := phiOf μ (f w)
  map_add' w w' := by
    rw [map_add]
    exact phiOf_eq hP hθ (add_mem (hf w) (hf w')) ((phiOf_spec hP hθ (hf w)).2.add (phiOf_spec hP hθ (hf w')).2)
  map_smul' c w := by
    rw [map_smul]
    exact phiOf_eq hP hθ (Submodule.smul_mem _ c (hf w)) ((phiOf_spec hP hθ (hf w)).2.smul c)

theorem homOf_apply (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (f : W →ₗ[ℂ] MMap M)
    (hf : ∀ w, f w ∈ allMaps θ M) (w : W) : homOf μ hP hθ f hf w = phiOf μ (f w) := rfl

open Classical in
theorem homOf_mem (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {f : W →ₗ[ℂ] MMap M}
    (hf : f ∈ homInto σ (finRep M) (allMaps θ M)) :
    homOf μ hP hθ f hf.1 ∈ homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) := by
  unfold homFinDS
  rw [mem_homTensorPi]
  have hs := fun w => mem_homPi.1 (phiOf_spec (μ := μ) hP hθ (hf.1 w)).1
  refine ⟨fun w y => (hs w).1 y, fun g w y => ?_, fun i g w y => (hs w).2 i g y⟩
  rw [homOf_apply, homOf_apply, hf.2 g w]
  have hm : finRep M g (f w) ∈ allMaps θ M := by
    rw [← hf.2 g w]
    exact hf.1 _
  rw [phiOf_eq hP hθ hm ((phiOf_spec hP hθ (hf.1 w)).2.translate g)]
  rfl

variable (μ) in

def toHom (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    homInto σ (finRep M) (allMaps θ M) →ₗ[ℂ] homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) where
  toFun f := ⟨homOf μ hP hθ f.1 f.2.1, homOf_mem hP hθ f.2⟩
  map_add' f f' := by
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    exact phiOf_eq hP hθ (add_mem (f.2.1 w) (f'.2.1 w))
      ((phiOf_spec hP hθ (f.2.1 w)).2.add (phiOf_spec hP hθ (f'.2.1 w)).2)
  map_smul' c f := by
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    exact phiOf_eq hP hθ (Submodule.smul_mem _ c (f.2.1 w)) ((phiOf_spec hP hθ (f.2.1 w)).2.smul c)

theorem toHom_injective (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) :
    Function.Injective (toHom (σ := σ) (M := M) μ hP hθ) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext (LinearMap.ext fun w => ?_)
  have h0 : phiOf μ (f.1 w) = 0 := congrArg (fun Ψ : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) => Ψ.1 w) hf
  have hr := (phiOf_spec (μ := μ) hP hθ (f.2.1 w)).2
  rw [h0] at hr
  exact eq_of_represents_cont (continuous_of_mem_allMaps (f.2.1 w)) (fun _ => continuous_const) hr represents_zero

variable (σ) in

def stab (w : W) : Subgroup (GfC V) where
  carrier := {g | σ g w = w}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
    rw [hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

open Classical in
theorem toHom_surjective (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (hσ : GlobalTheory.PRep.IsSmooth σ) :
    Function.Surjective (toHom (σ := σ) (M := M) μ hP hθ) := by
  intro Ψ
  have hΨ := Ψ.2
  unfold homFinDS at hΨ
  rw [mem_homTensorPi] at hΨ
  obtain ⟨h1, h2, h3⟩ := hΨ
  have hΨ : ∀ w, Ψ.1 w ∈ homDS M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) := fun w => mem_homPi.2 ⟨h1 w, fun i g => h3 i g w⟩
  have hex : ∀ w, ∃ T ∈ allMaps θ M, Represents μ (Ψ.1 w) T := fun w =>
    GlobalTheory.CuspRepr.exists_allMaps D θ hθ V S M μ (Ψ.1 w) (hΨ w) (stab σ w) (hσ w) fun k hk y => by
      have hk' : σ k w = w := hk
      exact (h2 k w y).symm.trans (congrArg (fun u => Ψ.1 u y) hk')
  choose T hT hr using hex
  have hc : ∀ w v, Continuous (T w v) := fun w => continuous_of_mem_allMaps (hT w)
  let f : W →ₗ[ℂ] MMap M :=
    { toFun := T
      map_add' := fun w w' => eq_of_represents_cont (hc _) (fun v => (hc w v).add (hc w' v)) (hr (w + w'))
        (by rw [map_add]; exact (hr w).add (hr w'))
      map_smul' := fun c w => eq_of_represents_cont (hc _) (fun v => (hc w v).const_smul c) (hr (c • w))
        (by rw [map_smul]; exact (hr w).smul c) }
  have hf : f ∈ homInto σ (finRep M) (allMaps θ M) :=
    ⟨hT, fun g w => eq_of_represents_cont (hc _) (fun v => (hc w v).comp (continuous_mul_right _)) (hr (σ g w))
      ((hr w).translate' g (h2 g w))⟩
  exact ⟨⟨f, hf⟩, Subtype.ext (LinearMap.ext fun w => phiOf_eq hP hθ (hT w) (hr w))⟩

end GlobalTheory.AutMult.MultAssembly

namespace GlobalTheory.AutMult

open GlobalTheory.AutMult.MultAssembly in

theorem cuspMult_eq_mCuspDS : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → ∀ (D : D7) (θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → GlobalTheory.CuspMult.cuspMult θ M σ = mCuspDS μ σ M := by
  intro hP _ _ D θ hθ V S M μ _ _ W _ _ σ hσ
  exact (LinearEquiv.ofBijective (toHom μ hP hθ) ⟨toHom_injective hP hθ, toHom_surjective hP hθ hσ⟩).rank_eq

end GlobalTheory.AutMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDS
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

theorem topologicalClosure_span_eq_top_of_le {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : Submodule ℂ K) (s : Set U)
    (h : U ≤ (Submodule.span ℂ (Subtype.val '' s)).topologicalClosure) :
    (Submodule.span ℂ s).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hmap : (Subtype.val '' (Submodule.span ℂ s : Set U) : Set K) = Submodule.span ℂ (Subtype.val '' s) := by
    exact congrArg (fun p : Submodule ℂ K => (p : Set K)) (Submodule.map_span U.subtype s)
  have h2 : v ∈ closure (Subtype.val '' (Submodule.span ℂ s : Set U)) := by
    rw [hmap, ← Submodule.topologicalClosure_coe]
    exact h hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  exact h2

theorem exists_isIrrUnitary_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)),
      IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  intro D V S M μ _ _ W _ _ σ hirr hadm hm
  classical
  have hne : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ≠ ⊥ := fun h => hm (by rw [mCuspDS, h]; simp)
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinj : Function.Injective T := injective_of_mem_homInto hirr hT hT0
  have hTt : T ∈ homFinDS σ M (RG V μ) ⊤ := homTensorPi_mono le_top hT
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule ℂ (DividedPowerChartLift V μ), (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U :=
    ⟨_, rfl⟩
  have hcopy : IsCopyFinDS σ M (RG V μ) U := ⟨T, hTt, hinj, hUdef⟩
  have hU := TrCopy.isIrredSubrep_of_isCopyFinDS D V S M W σ hirr hadm (DividedPowerChartLift V μ) (RG V μ) (isUnitaryRep_RG V μ) U hcopy
  refine ⟨U, inferInstance, inferInstance, hU.1.rep, isIrrUnitary_rep (isUnitaryRep_RG V μ) hU, ?_⟩
  have hmem : ∀ w y, T w y ∈ U := fun w y =>
    hUdef ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, y, rfl⟩)
  let T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H U :=
    { toFun := fun w => (T w).codRestrict U (hmem w)
      map_add' := fun a b => by ext y; simp
      map_smul' := fun c a => by ext y; simp }
  have hT'v : ∀ w y, (T' w y : DividedPowerChartLift V μ) = T w y := fun _ _ => rfl
  have hTm := mem_homTensorPi.1 hTt
  refine ⟨T', mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => Subtype.ext ?_, fun i g w y => Subtype.ext ?_⟩,
    fun a b h => hinj (ContinuousMultilinearMap.ext fun y => congrArg Subtype.val (DFunLike.congr_fun h y)), ?_⟩
  · exact hTm.2.1 g w y
  · exact hTm.2.2 i g w y
  · have himg : Subtype.val '' {v : U | ∃ w y, v = T' w y} = {v | ∃ w y, v = T w y} := by
      ext x
      constructor
      · rintro ⟨_, ⟨w, y, rfl⟩, rfl⟩
        exact ⟨w, y, rfl⟩
      · rintro ⟨w, y, rfl⟩
        exact ⟨T' w y, ⟨w, y, rfl⟩, rfl⟩
    exact topologicalClosure_span_eq_top_of_le U _ (le_of_eq (by rw [himg]; exact hUdef.symm))

end GlobalTheory.AutMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubquotientPrinSeriesOfHasVec
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

theorem subquotient_prinSeries_of_hasVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → HasVec ψ π → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Agree ψ ω ∧ IsSubquotient π (prinSeries ω) := by
  intro hBZ k _ _ _ _ n ψ V _ _ π hπ hirr hψ hord hvec
  obtain ⟨v, hv0, hv⟩ := hvec
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  have hx0 : (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) ≠ 0 := by
    intro h
    exact hv0 (GlobalTheory.T.eq_zero_of_mem_twistedJacquetKernel_upperUnitriangular k n ψ V π hπ hψ hord v ((Submodule.Quotient.mk_eq_zero _).1 h) hv)
  have hact : ∀ t ∈ torusO k (Fin n), jacB π t (Submodule.Quotient.mk v) =
      (torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) := by
    intro t ht
    have hgrp : diagT k (Fin n) t ∈ grp ψ := by
      refine ⟨iwahori_le_KO k _ (diagT_mem_iwahori ht), fun i j hij => ?_⟩
      rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne]
      exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
    have hth : theta ψ (diagT k (Fin n) t) = (torusChar ψ t : ℂ) := by
      rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ (diagT k (Fin n) t) t ht (fun i => by rw [val_diagT, Matrix.diagonal_apply_eq])
        (Or.inr fun i j hij => by rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne'])]
      simp
    rw [UnramFixed.jacB_apply, jacBU_mk, hv _ hgrp, hth]
    have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
      UnramFixed.deltaHalf_torusO k ht
    rw [this]
    simp
  obtain ⟨ω, l, hl0, hω, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π) (Submodule.Quotient.mk v) ψ
    (isSmooth_jacB hπ) hl hψ hx0 hact
  exact ⟨ω, fun i => GlobalTheory.TameIwahori.isSmoothChar_of_eq_on_units (hψ i) (hu i),
    fun i u hu' => (hu i u hu').symm,
    SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hω⟩

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeries
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.AutMult

theorem isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  classical
  intro D V S M H _ _ π hπ W _ _ σ hσ hσa hc H' _ _ π' hπ' W' _ _ σ' hσ' hσa' hc'
  have := hπ.complete
  have := hπ'.complete
  obtain ⟨T, hT, hTi, hTd⟩ := hc
  obtain ⟨T', hT', hTi', hTd'⟩ := hc'
  have hTf : T ∈ homFinDS σ M π ⊤ := hT
  have hTf' : T' ∈ homFinDS σ' M π' ⊤ := hT'
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  haveI : σ.IsIrreducible := hσ
  haveI : σ'.IsIrreducible := hσ'
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ.asModule
  haveI : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ'.asModule
  constructor
  · rintro ⟨A, hA⟩
    have hAs : ∀ g x, A.symm (π' g x) = π g (A.symm x) := fun g x => by
      apply A.injective
      rw [hA, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    let Ac : H' →L[ℂ] H := A.symm.toLinearIsometry.toContinuousLinearMap
    let T'' : W' →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
      (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H' H Ac).toLinearMap ∘ₗ T'
    have hT''v : ∀ w y, T'' w y = A.symm (T' w y) := fun _ _ => rfl
    have hT'' : ∀ w, T'' w ∈ homDS M π ⊤ := fun w => ⟨fun _ => trivial, fun τ g y => by
      rw [hT''v, hT''v, hTm'.2.2, hAs]⟩
    let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    let C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T'' w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
      bePi_self_pos hδ hπ.unitary (hT.1 x) ((map_ne_zero_iff T hTi).2 hx)
    have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
      change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
      rw [hTm.2.1, hTm.2.1, inner_map_map hπ.unitary]
    have hC : ∀ g x y, C (σ g x) (σ' g y) = C x y := fun g x y => by
      change ⟪T'' (σ' g y) _, T (σ g x) _⟫_ℂ = ⟪T'' y _, T x _⟫_ℂ
      rw [hT''v, hT''v, hTm'.2.1, hAs, hTm.2.1, inner_map_map hπ.unitary]
    obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
    obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K₀ hKo hKc W W' σ σ' hσa hσa'.1 B C hBpos hB hC
    obtain ⟨w', hw'⟩ := exists_ne (0 : W')
    have h1 : T'' w' ≠ 0 := by
      intro h
      apply hw'
      apply hTi'
      rw [map_zero]
      ext y
      apply A.symm.injective
      rw [← hT''v, h]
      simp
    obtain ⟨y', hy'⟩ : ∃ y', T'' w' y' ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    obtain ⟨w, y, hwy⟩ : ∃ w y, ⟪T'' w' y', T w y⟫_ℂ ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hy'
      have hsub : Submodule.span ℂ {v | ∃ w y, v = T w y} ≤ (ℂ ∙ T'' w' y')ᗮ := Submodule.span_le.2 (by
        rintro _ ⟨w, y, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hn w y))
      have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
      rw [hTd] at hcl
      exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
    have hC0 : C w w' ≠ 0 := fun h => hwy (by
      rw [inner_eq_bePi hδ hπ.unitary (hT.1 w) (hT'' w') y y']
      change C w w' * _ = 0
      rw [h, zero_mul])
    have hφ0 : φ w' ≠ 0 := fun h => hC0 (by rw [hCB, h, map_zero])
    let f : Representation.IntertwiningMap σ' σ := ⟨φ, fun g => LinearMap.ext fun y => hφ g y⟩
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hf0
    · exact ⟨(Representation.IntertwiningMap.ofBijective f hb).symm⟩
    · exact absurd (congrArg (fun F : Representation.IntertwiningMap σ' σ => F w') hf0) hφ0
  · rintro ⟨e⟩
    let T₂ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H' := T' ∘ₗ e.toLinearMap
    have hT₂ : T₂ ∈ homFinDS σ M π' ⊤ := by
      refine mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => ?_, fun τ g w y => hTm'.2.2 τ g (e w) y⟩
      change T' (e (σ g w)) y = _
      rw [show e (σ g w) = σ' g (e w) from Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w]
      exact hTm'.2.1 g (e w) y
    obtain ⟨B, hB, hBv⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hσ hσa H π hπ.unitary T hTf hTi hTd H' π'
      hπ'.unitary ⊤ isClosed_univ T₂ hT₂
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : T' (e w) ≠ 0 := fun h => hw (e.injective (hTi' (h.trans (map_zero T').symm) |>.trans (map_zero e).symm))
    obtain ⟨y, hy⟩ : ∃ y, T' (e w) y ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    have hB0 : B ≠ 0 := fun h => hy (by rw [← show B (T w y) = T' (e w) y from hBv w y, h]; rfl)
    have hm : multIn π π' ⊤ ≠ 0 := by
      intro h0
      rw [multIn, Submodule.rank_eq_zero] at h0
      exact hB0 (by simpa [h0] using hB)
    obtain ⟨f, hf⟩ := uEquiv_of_multIn_ne_zero hπ hπ' hm
    exact ⟨f, hf⟩

end GlobalTheory.AutMult
end
end


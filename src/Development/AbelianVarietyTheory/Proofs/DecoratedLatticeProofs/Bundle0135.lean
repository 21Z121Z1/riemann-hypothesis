import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ContDiff

namespace GlobalTheory.AdjointPair

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.mul_add, Matrix.add_mul]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp only [dagger, adj_zero, Matrix.zero_mul, Matrix.mul_zero]
  map_add' := dagger_add S T

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem map_dagger_zero {B : Type} [CommRing B] (p : AE D →+* B) (hp : ∀ z, p z = 0 → p (cA D z) = 0)
    (S T : HSp D) {x : WO S T} (hx : x.map p = 0) : (dagger S T x).map p = 0 := by
  have h1 : (adj x).map p = 0 := by
    funext i j
    have := congrFun (congrFun hx j) i
    simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply] at this ⊢
    exact hp _ this
  rw [dagger, Matrix.map_mul, Matrix.map_mul, h1, Matrix.zero_mul, Matrix.mul_zero]

theorem infPart_zero (z : AE D) (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  rw [infPart_cA, h, RingHom.map_zero]

theorem finPart_zero (z : AE D) (h : finPart D z = 0) : finPart D (cA D z) = 0 := by
  rw [finPart_cA, h, RingHom.map_zero]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  rw [hO_eq_trace, hO_eq_trace]
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, gA_giA_cancel, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_dagger (S T : HSp D) (x y : WO S T) :
    symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y := by
  have h := GlobalTheory.OrientedHeis.symplO_skew x y
  unfold symplO at h ⊢
  rw [hO_dagger]
  exact h

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_dagger, mul_neg]

theorem act_dagger (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    dagger S T (actO S T g h x) = actO T S h g (dagger S T x) := by
  simp only [dagger, actO_eq, adj_mul, mt_inv S g, mt_inv T h, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (hn a)).symm

theorem heis_dagger (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) : heisO ψ T S (dagger S T w) (cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (heisO ψ S T w f) := by
  funext y
  have hs : symplOH T S y (dagger S T w) = -symplOH S T (dagger T S y) w := by
    have := symplOH_dagger S T (dagger T S y) w
    rwa [dagger_dagger] at this
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, map_mul]
  rw [dagger_add, dagger_dagger, hs, conj_psi hn]

theorem theta_fwd (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (cj (dagger T S) f) where
  quasi γ w := by
    have hr : dagger T S (ratW S T γ) = ratW T S (T.gram⁻¹ * (γᴴ * S.gram)) := by
      rw [ratW_eq, ratW_eq]; exact dagger_rat T S γ
    have hq := hf.quasi (T.gram⁻¹ * (γᴴ * S.gram)) (dagger T S w)
    rw [← hr, symplOH_dagger, neg_neg] at hq
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [dagger_add, hq, map_mul, conj_psi hn]
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (daggerHom T S), hU.preimage (continuous_dagger T S), fun u hu hinf => ?_⟩
    have h1 := heis_dagger ψ hn S T (dagger T S u) f
    rw [dagger_dagger, hfix (dagger T S u) hu (map_dagger_zero (infPart D) infPart_zero T S hinf)] at h1
    exact h1
  cont := Complex.continuous_conj.comp (hf.cont.comp (continuous_dagger T S))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((daggerHom T S).comp L) ((continuous_dagger T S).comp hL)
      (fun t => map_dagger_zero (finPart D) finPart_zero T S (hfin t)) (dagger T S w)
    have e : (fun t => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f (w + L t)) =
        fun t => Complex.conjCLE (f (dagger T S w + (daggerHom T S).comp L t)) := by
      funext t
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, AddMonoidHom.comp_apply, Complex.conjCLE_apply]
      rw [dagger_add]; rfl
    rw [e]
    exact Complex.conjCLE.contDiff.comp h

theorem theta_iff (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (f : WO S T → ℂ) :
    IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f := by
  refine ⟨fun h => ?_, theta_fwd ψ hn S T⟩
  have := theta_fwd ψ hn T S h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at this

theorem adjoint_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ x y : WO S T, symplO T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T y) = -symplO S T x y) ∧ (∀ g h (x : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (actO S T g h x) = actO T S h g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x)) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) ↔ IsThetaFunO ψ S T f) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T w) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) (heisO ψ S T w f) := by
  intro D ψ hψ S T
  exact ⟨symplO_dagger S T, act_dagger S T, fun f => theta_iff ψ hψ.1.2.1 S T f, heis_dagger ψ hψ.1.2.1 S T⟩

end GlobalTheory.AdjointPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LatIndHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b :=
  calc p.sec (a * b) = p.sec (p.pr (p.sec a * p.sec b)) := by rw [map_mul p.pr, p.pr_sec, p.pr_sec]
    _ = p.e * (p.sec a * p.sec b) := p.sec_pr _
    _ = p.sec a * p.sec b := by rw [← mul_assoc, e_mul_sec]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  obtain ⟨α, rfl, -, h0⟩ := hε
  have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
    rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
    unfold idAt
    rw [Submodule.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
    refine ⟨?_, fun w => RingHom.mem_ker.2 ?_⟩
    · change fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · change evalV D.host.F w.1 α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  rw [← heε]
  exact Ideal.mul_mem_right _ _ hmem

theorem mul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => w * y i) ∈ latV S L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun y i => w * y i) fun a b => funext fun i => mul_add w (a i) (b i)
  have main : latV S L P ≤ (latV S L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
      AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (1 * x i))))
        fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add]; rfl
    have hle : intAE D ≤ (latV S L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨γ, hγ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (1 * x i))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
        show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
      congr 1
      ring
    have e : Ψ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w β _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hy

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem mulVec_sec (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) (x : n' → k) :
    t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) = fun i => p.sec ((β.b *ᵥ (rd α β t *ᵥ x)) i) := by
  have hM : (β.b * rd α β t * α.b') *ᵥ (α.b *ᵥ x) = β.b *ᵥ (rd α β t *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (β.b * rd α β t), α.b'b, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [← hM]
  funext i
  conv_lhs => rw [← GlobalTheory.FinPl.HalfInd.wr_rd α β ht]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.HalfInd.wr_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (sec_mul p _ _).symm

theorem mem_latO_iff_rd (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) (hU : p.UnitAA) {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)}
    (hα : α.IsLat LS ΛS) (hβ : β.IsLat LT ΛT) {t : WO S T} (ht : IsHalf p.e t) :
    t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ x ∈ ΛS, rd α β t *ᵥ x ∈ ΛT := by
  have hmem := GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = p.v) t
  rw [hU.2 T LT] at hmem
  constructor
  · intro h x hx
    have h1 : t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) ∈ latV T LT (· = p.v) := (hmem.1 h).2 _ ((hα x).1 hx)
    rw [mulVec_sec α β ht] at h1
    exact (hβ _).2 h1
  · intro h
    refine hmem.2 ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← ht i j]
      exact Ideal.mul_mem_right _ _ (e_mem_idAt p)
    · have hy' : t *ᵥ y = t *ᵥ (fun j => p.e * y j) := by
        funext i
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, mul_comm (t i j) p.e, ht i j]
      have hey : (fun j => p.e * y j) = fun j => p.sec ((α.b *ᵥ (α.b' *ᵥ fun j => p.pr (y j))) j) := by
        funext j
        rw [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec, p.sec_pr]
      have hint : finPart D p.e ∈ intAE D := by
        rw [← sec_one p]
        exact (p.int_iff 1).1 (one_mem _)
      have hx : α.b' *ᵥ (fun j => p.pr (y j)) ∈ ΛS := (hα _).2 (hey ▸ mul_mem_latV hint hy)
      show t *ᵥ y ∈ latV T LT (· = p.v)
      rw [hy', hey, mulVec_sec α β ht]
      exact (hβ _).1 (h _ hx)

end GlobalTheory.FinPl.LatIndHalf

theorem GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT hU ΛS ΛT hα hβ
  funext t
  unfold extFun halfInd
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    unfold latInd
    have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hS hT hU hα hβ ht
    by_cases h : t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v)
    · rw [if_pos (key.1 h), if_pos ⟨h, ht⟩]
    · rw [if_neg fun h' => h (key.2 h'), if_neg fun h' => h h'.1]
  · rw [if_neg ht, if_neg fun h => ht h.2]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexIntegralMatricesInSubstitutionImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm.IntIndex

section Det

variable {K : Type} [Field K] {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def mulRight (Y : Type) (G : Matrix Y' Y' K) : Matrix Y Y' K →ₗ[K] Matrix Y Y' K :=
  LinearMap.pi fun i : Y => (Matrix.toLin' Gᵀ).comp (LinearMap.proj i)

theorem mulRight_apply (G : Matrix Y' Y' K) (w : Matrix Y Y' K) : mulRight Y G w = w * G := by
  ext i j
  change (Gᵀ.mulVec (w i)) j = _
  rw [Matrix.mulVec_transpose]
  rfl

theorem det_mulRight (G : Matrix Y' Y' K) : LinearMap.det (mulRight Y G) = G.det ^ Fintype.card Y := by
  have := LinearMap.det_pi (R := K) (ι := Y) fun _ => Matrix.toLin' Gᵀ
  rw [LinearMap.det_toLin', Matrix.det_transpose, Finset.prod_const, Finset.card_univ] at this
  exact this

theorem exists_mul_map (H : Matrix Y Y K) (G : Matrix Y' Y' K) :
    ∃ B : Matrix Y Y' K →ₗ[K] Matrix Y Y' K, (∀ w, B w = H * w * G) ∧
      LinearMap.det B = G.det ^ Fintype.card Y * H.det ^ Fintype.card Y' := by
  let τ := Matrix.transposeLinearEquiv Y' Y K K
  refine ⟨mulRight Y G ∘ₗ ((τ : _ →ₗ[K] _) ∘ₗ mulRight Y' Hᵀ ∘ₗ (τ.symm : _ →ₗ[K] _)), fun w => ?_, ?_⟩
  · change mulRight Y G (mulRight Y' Hᵀ wᵀ)ᵀ = _
    rw [mulRight_apply, mulRight_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  · rw [LinearMap.det_comp, LinearMap.det_conj, det_mulRight, det_mulRight, Matrix.det_transpose]

end Det

theorem index_integral_image : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), Enl gk hk → ∃ R₀ : Finset (Matrix Y Y' k), (R₀.card : ℝ) = nabs k (Matrix.GeneralLinearGroup.det hk) ^ (Fintype.card Y' : ℝ) * nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card Y : ℝ)) ∧ (∀ v ∈ R₀, ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * v * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) ∧ ∀ w : Matrix Y Y' k, (∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) → ∃! v, v ∈ R₀ ∧ ∀ r q, (w - v) r q ∈ 𝒪[k] := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk hE
  let M : Submodule 𝒪[k] (Matrix Y Y' k) :=
    { carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
      add_mem' := fun ha hb r q => add_mem (ha r q) (hb r q)
      zero_mem' := fun _ _ => zero_mem _
      smul_mem' := fun c x hx r q => by
        rw [Matrix.smul_apply, Algebra.smul_def]
        exact mul_mem c.2 (hx r q) }
  haveI : Submodule.IsLattice k M := by
    constructor
    · let φ : Matrix Y Y' 𝒪[k] →ₗ[𝒪[k]] Matrix Y Y' k := (Algebra.linearMap 𝒪[k] k).mapMatrix
      refine Submodule.FG.of_le (Submodule.fg_range φ) fun m hm => ⟨Matrix.of fun i j => ⟨m i j, hm i j⟩, ?_⟩
      ext i j
      rfl
    · rw [eq_top_iff]
      intro w _
      rw [Matrix.matrix_eq_sum_single w]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      have h1 : Matrix.single i j (1 : k) ∈ M := fun r q => by
        rw [Matrix.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      have := Submodule.smul_mem _ (w i j) (Submodule.subset_span (R := k) h1)
      rwa [Matrix.smul_single, smul_eq_mul, mul_one] at this
  obtain ⟨Bl, hBl, hd⟩ := exists_mul_map (↑(hk⁻¹) : Matrix Y Y k) (↑gk : Matrix Y' Y' k)
  have hbij : Function.Bijective Bl := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun w => (↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k), fun w => ?_, fun w => ?_⟩
    · change (↑hk : Matrix Y Y k) * Bl w * (↑(gk⁻¹) : Matrix Y' Y' k) = w
      rw [hBl]
      calc (↑hk : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) * (↑(gk⁻¹) : Matrix Y' Y' k)
          = ((↑hk : Matrix Y Y k) * (↑(hk⁻¹) : Matrix Y Y k)) * w * ((↑gk : Matrix Y' Y' k) * (↑(gk⁻¹) : Matrix Y' Y' k)) := by
            simp only [Matrix.mul_assoc]
        _ = w := by rw [hk.mul_inv, gk.mul_inv, Matrix.one_mul, Matrix.mul_one]
    · change Bl ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) = w
      rw [hBl]
      calc (↑(hk⁻¹) : Matrix Y Y k) * ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) * (↑gk : Matrix Y' Y' k)
          = ((↑(hk⁻¹) : Matrix Y Y k) * (↑hk : Matrix Y Y k)) * w * ((↑(gk⁻¹) : Matrix Y' Y' k) * (↑gk : Matrix Y' Y' k)) := by
            simp only [Matrix.mul_assoc]
        _ = w := by rw [hk.inv_mul, gk.inv_mul, Matrix.one_mul, Matrix.mul_one]
  have hM : ∀ m ∈ M, Bl m ∈ M := fun m hm =>
    show ∀ r q, (Bl m) r q ∈ 𝒪[k] by rw [hBl]; exact hE m hm
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, e1, e2⟩ := GlobalTheory.SplitLinear.relIndex_comap_lattice M Bl hbij hM hp
  have hq : Nat.card (𝒪[k] ⧸ Ideal.span {p}) = resCard k := by
    rw [resCard, ← hp.maximalIdeal_eq]
    rfl
  have hq0 : 0 < resCard k := Nat.card_pos
  set A := M.toAddSubgroup with hA
  set Bs := AddSubgroup.comap Bl.toAddMonoidHom A with hBs
  have hne : A.relIndex Bs ≠ 0 := by rw [e2, hq]; exact pow_ne_zero _ hq0.ne'
  haveI : (A.addSubgroupOf Bs).FiniteIndex := ⟨hne⟩
  haveI : Finite (Bs ⧸ A.addSubgroupOf Bs) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨R, hRc, hRB, hRu⟩ := GlobalTheory.SplitLinear.exists_reps A Bs
  have hmemB : ∀ w, w ∈ Bs ↔ ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k] := by
    intro w
    change (∀ r q, (Bl w) r q ∈ 𝒪[k]) ↔ _
    rw [hBl]
  refine ⟨R, ?_, fun v hv => (hmemB v).1 (hRB v hv), fun w hw => hRu w ((hmemB w).2 hw)⟩

  have hpow : ∀ (x : kˣ) (n : ℕ), nabs k (x ^ n) = nabs k x ^ n := by
    intro x n; simp [nabs, map_pow]
  have hinv : ∀ x : kˣ, nabs k x⁻¹ = (nabs k x)⁻¹ := by
    intro x; simp [nabs, map_inv]
  have hp0 : (p : k) ≠ 0 := fun h => hp.ne_zero (by exact_mod_cast h)
  let X : kˣ := Matrix.GeneralLinearGroup.det gk ^ Fintype.card Y * Matrix.GeneralLinearGroup.det hk⁻¹ ^ Fintype.card Y'
  let U : kˣ := Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) u
  let P : kˣ := Units.mk0 (p : k) hp0
  have hXU : X * U = P ^ m := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hd]
    exact e1
  have hU : nabs k U = 1 := by
    apply nabs_eq_one_of_valuation_eq_one
    exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.mp u.isUnit
  have hP : nabs k P = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp rfl
  have key := congrArg (nabs k) hXU
  rw [GlobalTheory.SplitWeil.nabs_mul, GlobalTheory.SplitWeil.nabs_mul, hpow, hpow, hpow, hU, hP, map_inv, hinv, mul_one] at key
  rw [hRc, e2, hq, Real.rpow_natCast, Real.rpow_neg (GlobalTheory.SplitWeil.nabs_pos k _).le, Real.rpow_natCast]
  push_cast
  have hq' : ((resCard k : ℝ)) ^ m = (((resCard k : ℝ))⁻¹ ^ m)⁻¹ := by rw [inv_pow, inv_inv]
  rw [hq', ← key, inv_pow (nabs k _), mul_inv, inv_inv, mul_comm]

end GlobalTheory.LocOm.IntIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCompAddEquivEqSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfTwist

theorem integral_comp_addEquiv_eq_smul {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem isClosed_fix (D : D7) (m n : ℕ) (c : AE D) : IsClosed {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
  obtain ⟨i1, i2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have : {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  · exact (continuous_apply j).comp (continuous_apply i)

theorem integral_twist_fix_eq_smul : ∀ (D : D7) (m n : ℕ) (c : AE D) (H : AddSubgroup (Mx D m n)), (∀ x, x ∈ H ↔ ∀ i j, c * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure] (h : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ φ : Mx D m n → ℂ, ∫ x : H, φ (h.1 ⬝ x.1 ⬝ a.1) ∂ν = r * ∫ x : H, φ x.1 ∂ν := by
  intro D m n c H hH _ _ ν _ h a
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  have key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y := by
    intro y
    rw [hH]
    constructor
    · intro hy; ext i j; simpa using hy i j
    · intro hy i j; simpa using congrFun (congrFun hy i) j
  have mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H := by
    intro g b y hy
    rw [key] at hy ⊢
    show c • (g.1 * y * b.1) = g.1 * y * b.1
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hcl : IsClosed (H : Set (Mx D m n)) := by
    have : (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
      ext x; exact hH x
    rw [this]; exact isClosed_fix D m n c
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : H ≃+ H :=
    { toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩
      invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        apply Subtype.ext
        show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      map_add' := fun x y => by
        apply Subtype.ext
        show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous T := by
    show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv_eq_smul ν T hc hc'
  exact ⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩

end GlobalTheory.HalfTwist
end


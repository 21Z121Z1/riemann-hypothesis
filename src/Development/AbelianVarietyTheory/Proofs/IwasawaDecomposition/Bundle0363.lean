import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjVecLow

open Formalism.L2.SG.InstExistsPf

theorem lowKSub_le_sm_of_unique {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp) (τ : D.what₂.Tau)
    (hone : ∀ S S' : Submodule ℂ (M.H τ),
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S →
      Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S' → S = S') :
    Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V Sp M τ
  exact le_trans (sSup_le fun S' hS' => (hone S' S hS' hS).le) hSle

theorem gap_rows {D : D7} (hG : GapHyp D) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (fun i : Fin n => Formalism.MainNotions.S.epsS D.R (Fin.cast hn i))
      (fun i : Fin n => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast hn i)) (16 * (D.R.r : ℝ) ^ 19) := by
  subst hn
  have h := Formalism.L2.SG.Pf.BunD.gap_lamS D.R (D.hc τ) (h := 16 * (D.R.r : ℚ) ^ 19) (by positivity)
    (fun j hj => hG.2 τ j hj)
  intro a b hab
  have := h a b (by simpa using hab)
  push_cast at this
  simpa using this

theorem npq_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) :
    (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1 < 16 * (n : ℝ) ^ 19 := by
  have hp : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hq : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp' : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h3 : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hp' (by positivity)) hq' (by positivity) (by positivity)
    nlinarith
  have h19 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 19 := pow_le_pow_right₀ hn' (by norm_num)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 19 := one_le_pow₀ hn'
  linarith

theorem exists_conj_intertwiner_of_gap (hUq : GlobalTheory.Published.DiscreteSeriesUpqUnique) {D : D7} (hG : GapHyp D)
    (I : Formalism.MainNotions.S.AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = Formalism.MainNotions.S.lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, Formalism.MainNotions.S.IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, Formalism.MainNotions.S.IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 hUq
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (GlobalTheory.SeeInt.frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) :=
          funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => GlobalTheory.SeeInt.fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (GlobalTheory.SeeInt.frP D τ)⁻¹ * g * GlobalTheory.SeeInt.frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((GlobalTheory.SeeInt.frP D τ)⁻¹ * g * ((GlobalTheory.SeeInt.frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.SeeInt.frP_unit D τ)]
  · intro τ
    have hone : ∀ S S' : Submodule ℂ (M0.H τ),
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S →
        Formalism.MainNotions.S.IsKTypeOf (M0.ε τ) (M0.σ τ) (Formalism.QuantumDeterminants.lowK (M0.ε τ) (M0.lam τ)) S' → S = S' := by
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      haveI : CompleteSpace (M0.H τ) := (M0.ds τ).1
      have hgap : Formalism.QuantumDeterminants.GapAtLeast (M0.ε τ) (M0.lam τ) (16 * (D.R.r : ℝ) ^ 19) := by
        have e1 : M0.ε τ = fun i => Formalism.MainNotions.S.epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq (pl.symm τ) i
        have e2 : M0.lam τ = fun i => Formalism.MainNotions.S.lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by
            show lam (pl.symm τ) i = _
            exact (lam_eq (pl.symm τ) i).trans (by rw [Equiv.apply_symm_apply])
        rw [e1, e2]
        exact gap_rows hG n_eq τ
      have hr : (D.sp.Y 0).rank = D.R.r := n_eq
      have hbig : ((D.sp.Y 0).rank : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (M0.ε τ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf (M0.ε τ) : ℝ) + 1 <
          16 * (D.R.r : ℝ) ^ 19 := by
        have h1 : 1 ≤ (D.sp.Y 0).rank := by have := hG.1; omega
        exact (npq_lt (M0.ε τ) h1).trans_eq (by rw [hr])
      exact (ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap _ _ _ hHC _ hgap hbig _ _ (M0.ds τ)).2.1
    have hw : w (pl.symm τ) ∈ M0.sm τ := lowKSub_le_sm_of_unique M0 τ hone (low _).2
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

theorem conjModel_of_gap : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro _ _ hUq _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hG _ hinf _ _
  have key : (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y :=
    GlobalTheory.IotaReal.iota_real_finite_of_eq R.θ hinf X.B.I h X.ιE X.pl X.φ_eq hιE
  obtain ⟨-, hreal, -⟩ := key
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner_of_gap hUq hG X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.ConjVecLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.InertSatake

def transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) : SmIrr H where
  V := σ.V
  ρ := σ.ρ.comp P.symm.toMulEquiv.toMonoidHom
  smooth v := (σ.smooth v).preimage P.symm.continuous
  irred := by
    obtain ⟨h0, h⟩ := (CuspRep.isIrreducible_iff _).1 σ.irred
    refine (CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have := hW (P g) v hv
    change σ.ρ (P.symm (P g)) v ∈ W at this
    rwa [P.symm_apply_apply] at this

theorem transport_apply {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) (g : G) (v : σ.V) : (transport P σ).ρ (P g) v = σ.ρ g v := by
  change σ.ρ (P.symm (P g)) v = _
  rw [P.symm_apply_apply]

theorem isAdmissible_transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (P : G ≃ₜ* H) (σ : SmIrr G) (h : IsAdmissible σ.ρ) : IsAdmissible (transport P σ).ρ := by
  refine ⟨(transport P σ).smooth, fun K ho hc => ?_⟩
  let K' : Subgroup G := K.comap P.toMulEquiv.toMonoidHom
  show FiniteDimensional ℂ (fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K)
  have e : fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K = fixed σ.ρ K' := by
    ext x
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hx k hk
      have := hx (P k) hk
      change σ.ρ (P.symm (P k)) x = x at this
      rwa [P.symm_apply_apply] at this
    · intro hx k hk
      exact hx (P.symm k) (by change P (P.symm k) ∈ K; rwa [P.apply_symm_apply])
  rw [e]
  refine h.2 K' (ho.preimage P.continuous) ?_
  have : (K' : Set G) = P.toHomeomorph ⁻¹' (K : Set H) := rfl
  rw [this]
  exact P.toHomeomorph.isCompact_preimage.2 hc

variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ}

def conjEquiv (s : L →+* L) (b : GL (Fin n) L) (hb : cT s b.1 * 1 * b.1 = antiJ L n) :
    UJ s (1 : Matrix (Fin n) (Fin n) L) ≃ₜ* GU s n where
  toFun g := ⟨b⁻¹ * g * b, GlobalTheory.InertDoubleCoset.conj_mem_UJ s hb g.2⟩
  invFun h := ⟨b * h * b⁻¹, by simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ s (GlobalTheory.InertDoubleCoset.inv_frame s hb) h.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.InertSatake

open GlobalTheory.InertSatake in

theorem GlobalTheory.InertSatake.sph_iff_isSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  intro E _ _ _ n π w hun hns
  obtain ⟨π, rfl⟩ := AU.mk_surjective π
  show IsUnramU π.V w ↔ ∃ α, π.IsSat w α
  constructor
  · rintro ⟨φ, hφ, h0, hfix⟩
    obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser E w hun hns
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (one_mem (GlobalTheory.LFun.KGL w n))
      (by rw [Units.val_one, cT_one])
    let P : locU n w ≃ₜ* GU s n := e.trans (conjEquiv s b hb)
    have hP : ∀ x : locU n w, ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) = b⁻¹ * cLoc w x.1 * b := fun x => by
      change b⁻¹ * (e x : GL (Fin n) _) * b = _
      rw [he]
    obtain ⟨σ0, hadm, hcomp⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
    obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
    obtain ⟨-, f, hf0, hfm, hf⟩ := hcomp
    let F : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
      have := congrArg Subtype.val (DFunLike.congr_fun h v)
      exact this)
    have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ0.V σ0.V π.rep (locU n w).subtype σ0.ρ σ0.ρ
      π.isIrreducible_rep σ0.irred σ0.irred (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ0.ρ σ0.irred
      (fun i : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => i.toLinearMap)
      (fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u) {x | cLoc w x.1 ∈ GlobalTheory.LFun.KGL w n} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hfix k.1 k.2 hk))
      (htop ▸ Submodule.mem_top)
    let σ1 := transport P σ0
    have hsph : GlobalTheory.LGrp.IsSpherical σ1.ρ (KU s n) := by
      refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hv0⟩
      obtain ⟨x, rfl⟩ := P.surjective k
      rw [transport_apply]
      refine hv x ?_
      have h1 : ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL (w.adicCompletion E)) :=
        (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) (P x)).1 hk
      have h2 : cLoc w x.1 = b * (P x : GL (Fin n) (w.adicCompletion E)) * b⁻¹ := by rw [hP]; group
      show cLoc w x.1 ∈ GlobalTheory.LFun.KGL w n
      rw [h2]
      exact mul_mem (mul_mem hbK h1) (inv_mem hbK)
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary E w ϖ s q n hU σ1.V σ1.ρ σ1.irred (isAdmissible_transport P σ0 hadm) hsph
    refine ⟨α, s, ϖ, q, hs, hU, b, hbK, by have h := hb; rw [Units.val_one, Matrix.mul_one] at h; exact h, P.toMulEquiv.toMonoidHom, hP, σ1,
      ⟨σ1.irred, f, hf0, hfm, fun x u => ?_⟩, hα⟩
    change f (σ0.ρ (P.symm (P x)) u) = _
    rw [P.symm_apply_apply]
    exact hf x u
  · rintro ⟨α, s, ϖ, q, hs, hU, b, hbK, hb, p, hp, σ, ⟨-, f, hf0, hfm, hf⟩, hsat⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    have hb1 : cT s b.1 * 1 * b.1 = antiJ _ n := by rwa [Matrix.mul_one]
    have hsurj : Function.Surjective p := fun g => by
      let P := e.trans (conjEquiv s b hb1)
      have hP : ((P (P.symm g) : GU s n) : GL (Fin n) (w.adicCompletion E)) =
          b⁻¹ * cLoc w (P.symm g).1 * b := by
        change b⁻¹ * (e _ : GL (Fin n) _) * b = _
        rw [he]
      refine ⟨P.symm g, Subtype.ext ?_⟩
      rw [hp, ← hP, P.apply_symm_apply]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have hfv : f v ≠ 0 := by
      intro h
      have hker := ((CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) fun g u hu => by
        obtain ⟨x, rfl⟩ := hsurj g
        rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hu, map_zero]
      rcases hker with h1 | h1
      · have m : v ∈ LinearMap.ker f := LinearMap.mem_ker.2 h
        rw [h1] at m
        exact hv0 ((Submodule.mem_bot ℂ).1 m)
      · exact hf0 (LinearMap.ker_eq_top.1 h1)
    refine ⟨f v, hfm v, hfv, fun x hx hk => ?_⟩
    have hpk : p ⟨x, hx⟩ ∈ KU s n := by
      refine (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) _).2 ?_
      show ((p ⟨x, hx⟩ : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL _)
      rw [hp]
      exact mul_mem (mul_mem (inv_mem hbK) hk) hbK
    refine (hf ⟨x, hx⟩ v).symm.trans ?_
    rw [GlobalTheory.LGrp.mem_fixed.1 hv _ hpk]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPoint
section
namespace GlobalTheory.OneMapRef.DictPt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isDerivAt0_comp {X : Scheme.{0}} {g g' : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (hol : IsHolTo Set.univ e)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {u : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e (ρ w) u) :
    IsDerivAt0 (fun z => e (ρ z)) w u := by
  rw [HolHom.isDerivAt0_iff] at h ⊢
  refine ⟨h.1.trans (congrArg e (map_zero ρ).symm), fun U hU f => ?_⟩
  have hU' : ⊤ ≤ e 0 ⁻¹ᵁ U := by simpa only [map_zero] using hU
  have h1 : HasFDerivAt (fun t => valAt' (e t) U f) (fderiv ℂ (fun t => valAt' (e t) U f) 0) (ρ 0) := by
    rw [map_zero]; exact ((HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) U hU').2 f).hasFDerivAt
  exact (h.2 U hU' f).trans (congrArg (· w) (h1.comp 0 ρ.hasFDerivAt).fderiv).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g' → (E →+* ℂ)}

theorem isHolTo_ex (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) : IsHolTo Set.univ (fun z => (F.ex i P z).left) := by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
    (HolHom.holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem levPt_eq (F : FamilyUnif Xo σ ty) (i : Fin F.n) {Pm : (F.Di i).La →+ (Fin g' → ℂ)}
    (hper : IsPeriod (F.Di i) ty Pm) (π : Fin g ≃ Fin g') {y : Sp ℂ ⟶ Xo.X} (h : y = F.u i Pm)
    (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G)) (u : Fin g' → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (b2 : IsHolTo Set.univ (fun z => (ex z).left))
    (b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (Pi.single (π.symm m) 1) (u m))
    (b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1) (u m))
    (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y a = ex (fun j => (l.M : ℂ)⁻¹ * Pm (F.t i a) (π j)) := by
  subst h
  let ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (π j)
  have hρ : ∀ m, ρ (Pi.single m 1) = Pi.single (π.symm m) 1 := fun m => by
    funext j
    change (Pi.single m 1 : Fin g' → ℂ) (π j) = _
    simp only [Pi.single_apply, Equiv.eq_symm_apply]
  have E : (fun z => ex (ρ z)) = F.ex i Pm :=
    GlobalTheory.AnUniq.exp_eq (fun z w => by rw [map_add, b1]) (F.ex_add _ _ hper)
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo b2 (Set.mem_univ (ρ z))).precomp ρ.differentiableAt) (isHolTo_ex F _ hper)
      u (fun m => isDerivAt0_comp b2 ρ (by rw [hρ]; exact b3 m)) b4
  exact (F.ex_eta i Pm hper a ha).trans (congrFun E _).symm

theorem ex_add_ker {y : Sp ℂ ⟶ Xo.X} (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (z k z' : Fin g → ℂ) (hk : ex k = 1) (h : z' = z + k) : ex z = ex z' := by
  rw [h, b1, hk, _root_.mul_one]

theorem sub_eq_nsmul {A : Type} [AddCommGroup A] (M : ℕ) (p q z w w' : A) (e : p - z = M • w)
    (e' : q - z = M • w') : p - q = M • (w - w') := by
  rw [smul_sub, ← e, ← e', sub_sub_sub_cancel_right]

end GlobalTheory.OneMapRef.DictPt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.DictPt.exists_sub_eq {D : D7} (V : HSp D) (g : GA D V) (M : ℕ) (hM : M ≠ 0)
    (p q : Fin V.rank → D.host.E) (z w w' : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V g) (hw' : w' ∈ latGHat V g) (e : finVec V p - z = M • w) (e' : finVec V q - z = M • w') :
    (M : D.host.E)⁻¹ • (p - q) ∈ latG V g := by
  rw [(GlobalTheory.MarkCoset.latG_spec D V g).1]
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : M • finVec V ((M : D.host.E)⁻¹ • (p - q)) = M • (w - w') := by
    refine Eq.trans ?_ (GlobalTheory.OneMapRef.DictPt.sub_eq_nsmul M _ _ z w w' e e')
    funext i
    change M • ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : D.host.E)⁻¹ * (p i - q i))) = 1 ⊗ₜ p i - 1 ⊗ₜ q i
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, mul_inv_cancel_left₀ hM', TensorProduct.tmul_sub]
  have h2 : finVec V ((M : D.host.E)⁻¹ • (p - q)) = w - w' :=
    GlobalTheory.MarkCoset.nsmul_cancel D.host.F M (Nat.cast_ne_zero.2 hM) h1
  rw [h2]
  exact sub_mem hw hw'

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.OneMapRef.DictPt.dict_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  intro D H Dw l Xo c σ W r hr U dict ι g₀ e₀ F ik φ th x₀ θ Z₀ hσ hU h1 hθ hth hD hx₀ h
  subst hr
  obtain ⟨γ, hγ, hl, hm, hf⟩ := hD.2 h
  have hΛ : (U.X (dict h).1).Λ = latG W (γ * h) := SetLike.ext' (hl.trans (Set.image_id _))
  refine ⟨γ, hγ, ⟨hγ, hl, hm⟩, hΛ, fun eT heT => ?_, ?_⟩
  · funext τ
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    have e1 : th _ (eT ρ) = θ ρ :=
      GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth _ (eT ρ)) (by rw [heT]; exact hθ ρ)
    have := hf (eT ρ)
    rw [e1, heT, hx₀] at this
    funext a b
    simp only [frOf, Equiv.symm_apply_apply]
    exact congrFun (congrFun this a) b
  · intro hx g bas idx e hs hM
    letI : Algebra c.F ℂ := σ.toAlgebra
    intro A mk hmk hA a ha
    obtain ⟨Pm, hPm, hP, hu, hder⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hx⟩
    have hM0 : l.M ≠ 0 := by have := l.three_le; omega
    have key := GlobalTheory.OneMapRef.DictPt.levPt_eq F _ hP (e.trans e₀.symm) hu A.ex (fun m => (U.un _ ⟨(dict h).2, hx⟩).u (e₀ m).1 (e₀ m).2)
      A.ex_add A.hol (fun m => A.der (e₀ m)) (fun m => by simpa only [Sigma.eta, Equiv.symm_apply_apply] using hder (e₀ m).1 (e₀ m).2) a ha
    obtain ⟨w, hw, ew⟩ := hA a ha
    obtain ⟨w', hw', ew'⟩ := hm a ha
    have hmem := GlobalTheory.OneMapRef.DictPt.exists_sub_eq W (γ * h) l.M hM0 _ _ _ w w' hw hw' ew ew'
    rw [← hΛ] at hmem
    have hk := (A.ex_ker _).2 ⟨_, hmem, rfl⟩
    refine key.trans (GlobalTheory.OneMapRef.DictPt.ex_add_ker A.ex A.ex_add _ _ _ hk ?_)
    funext j
    have e3 : ∀ v (ℓ ℓ' : Lt1 Dw), ℓ = ℓ' → perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ.1) ℓ.2 =
        perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ'.1) ℓ'.2 := fun v ℓ ℓ' hℓ => by rw [hℓ]
    rw [Pi.add_apply, hPm, Equiv.trans_apply, e3 _ _ _ (e₀.apply_symm_apply (e j)), ← hM.1]
    have e2 : ∀ p q : Fin W.rank → D.host.E, (l.M : D.host.E)⁻¹ • p =
        (l.M : D.host.E)⁻¹ • q + (l.M : D.host.E)⁻¹ • (p - q) := fun p q => by rw [← smul_add, add_sub_cancel]
    rw [e2 (mk a) (φ _ (F.t _ a))]
    simp only [pv, Function.comp_apply, per_add, Pi.add_apply]
    congr 1
    rw [per_smul, map_inv₀, map_natCast]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdlCutProj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ProjTest

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z]

theorem valAt_algebraMap (y : Sp K ⟶ Z) (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ _ h.choose_spec]

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    {f : Z.functionField} (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have h := CxPts.mem_ptsIn.2 hU
  rw [ratVal_fnOf h, ← algebraMap_germ hU, valAt_algebraMap, CxPts.ev, valR,
    dif_pos (show ⊤ ≤ y.1 ⁻¹ᵁ U from h)]
  have e := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U hU)
  refine Eq.trans ?_ e.symm
  simp [Scheme.Hom.appLE]
  rfl

end Val

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

omit [NumberField F] in

theorem isEqn_eqn (Δ : Y.Dv) (x : Y.X) : Δ.IsEqn x (eqn Δ x) := (Δ.exists_isEqn x).choose_spec

theorem pn_pos {M : TrueGeo.Model Y} {L : HermLB M.p} (h : A.Induced M L 1 0) (σ : F →+* ℂ) (z : Pts Y σ)
    (f : Y.Fn) (hf : A.D.GeneratesAt (under z) f) : 0 < C.pn Y σ A.D (A.m σ) (C.cx Y σ f) z := by
  obtain ⟨-, r, hr, h, -⟩ := h
  obtain ⟨i, hi⟩ := exists_chart hr.isLB (under z)
  have hf' : (((1 : ℕ+) : ℕ) • A.D).GeneratesAt (under z) f := by simpa using hf
  have h₁ := h σ z ⟨z.1 ≫ M.j, by
    rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, ← Spec.map_comp]; rfl⟩ i f rfl hi hf'.regularAt
  have h₂ := C.pn_mPow Y σ A.D 1 (A.m σ) f z hf
  simp only [pow_one] at h₂
  have h₃ := ratVal_ne_zero ((hr.isEqn i _ hi).generatesAt_iff.1 hf')
  exact ((mul_pos_iff_of_pos_left (Real.exp_pos _)).1 (lt_of_lt_of_eq (by positivity) h₁.symm)).trans_eq h₂

variable (F) (n : ℕ)

def pick (i : Fin n) (l : Fin (n + 1)) : 𝓞 F := if l = i.succ then 1 else 0

end GlobalTheory.TrueGeo.ProjTest

namespace GlobalTheory.TrueGeo

end GlobalTheory.TrueGeo
end
end


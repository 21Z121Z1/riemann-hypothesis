import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem continuous_covolOne_integral {D : D7} {m n : ℕ} {X : Type} [TopologicalSpace X] {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (F : X → Mx D m n → ℂ)
    (hc : Continuous fun p : X × Mx D m n => F p.1 p.2)
    (hF : ∀ x, ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, F x (γ + a) = F x a) :
    Continuous fun x => ∫ a in 𝓕, F x a ∂μ := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have hi : ∀ x, IntegrableOn (F x) 𝓕 μ := fun x =>
    GlobalTheory.MixModel.covolOne_integrableOn h _ (hc.comp (Continuous.prodMk_right x)) (hF x)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc' : Continuous fun p : X × Mx D m n => ‖F p.1 p.2 - F x₀ p.2‖ :=
    (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).norm
  have hev : ∀ᶠ x in nhds x₀, ∀ a ∈ K, ‖F x a - F x₀ a‖ < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hc'.continuousAt.eventually_lt continuousAt_const ?_
    simpa using hε
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  have hb : ∀ a, ‖F x a - F x₀ a‖ ≤ ε / 2 := fun a => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hF x γ hγ a, ← hF x₀ γ hγ a]
    exact (hx _ ha).le
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)).trans_lt ?_
  rw [measureReal_def, Measure.restrict_apply_univ, h.2.2, ENNReal.toReal_one, mul_one]
  exact half_lt_self hε

theorem swSec_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IntegrableOn (fun w => φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w)) 𝓕 ν ∧ Continuous (swSec A B omh ν 𝓕 φ) := by
  intro D ψ A B χB omh hω ν 𝓕 hν φ hφ
  refine ⟨GlobalTheory.ThetaMean.integrableOn_lagr hν hφ, ?_⟩
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ omh hω φ hφ
  exact continuous_covolOne_integral hν (fun g w => omh (g, 1) φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w))
    (hj.comp ((continuous_fst.prodMk continuous_const).prodMk (GlobalTheory.ThetaMean.continuous_lagr.comp continuous_snd)))
    (fun g => GlobalTheory.ThetaMean.periodic_lagr (hω.om_pres _ _ hφ))

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def signEquiv {n : ℕ} (ε : Fin n → Bool) {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : Fin n ≃ Fin p ⊕ Fin q :=
  (Equiv.sumCompl fun a => ε a = true).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; exact hp))
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simpa using hq)))

theorem signEquiv_inl {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin p) : ε ((signEquiv ε hp hq).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]
  generalize (Fintype.equivFinOfCardEq (α := {a // ε a = true}) _).symm i = x
  exact x.2

theorem signEquiv_inr {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin q) : ε ((signEquiv ε hp hq).symm (Sum.inr i)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  generalize (Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) _).symm i = x
  simpa using x.2

theorem card_true (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = true).card = (V.sig (tauE D τ)).1 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).1

theorem card_false (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).2

def sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Mem.Th.CptF V := fun τ =>
  (M.fr τ).submatrix (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ)).symm id

theorem Jpq_submatrix {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) :
    (Formalism.UG.Jpq p q).submatrix (signEquiv ε hp hq) (signEquiv ε hp hq) = Formalism.REAL.Jm ε := by
  ext a b
  simp only [submatrix_apply, Formalism.REAL.Jm, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rcases h1 : signEquiv ε hp hq a with i | i
    · have := signEquiv_inl hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
    · have := signEquiv_inr hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
  · have hne : signEquiv ε hp hq a ≠ signEquiv ε hp hq b := (signEquiv ε hp hq).injective.ne hab
    rw [if_neg hab]
    rcases h1 : signEquiv ε hp hq a with i | i <;> rcases h2 : signEquiv ε hp hq b with j | j <;> rw [h1, h2] at hne <;>
      simp_all [Formalism.UG.Jpq, Matrix.one_apply]

end GlobalTheory.ChainOnto.RealData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizesLe
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

namespace GlobalTheory.Core.Rk.HdGap

theorem bOne_eq (D : D7) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    bOne D τ (j + 1) = (((D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
  unfold bOne
  rw [dif_pos (by omega)]
  rfl

theorem gap_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := H
  have h := hg τ (j + 1) (by omega) (by omega)
  rwa [bOne_eq D τ (j + 1) hj, bOne_eq D τ j (by omega)] at h

theorem scale_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl)
    (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ∧ 1801 ≤ D.R.r := by
  obtain ⟨hL, -, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := H
  have hm : 1801 ≤ D.R.m := by exact_mod_cast hCl.trans hClm
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, by unfold Ranks.r; omega⟩
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf1
  have hr : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have h1 : 1 ≤ (D.R.f : ℝ) ^ 5 * L := by nlinarith
  calc 1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    _ = Cl * (D.R.r : ℝ) ^ 19 * 1 := by ring
    _ ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * L) := by
        apply mul_le_mul_of_nonneg_left h1; nlinarith
    _ = _ := by ring

end GlobalTheory.Core.Rk.HdGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParams
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

theorem heckeLin_eq_of_rep {K : Subgroup (GA D V)} {α α' : GA D V} {R R' : Finset (GA D V)}
    (hR : IsCosetRep V (K : Set (GA D V)) α R) (hR' : IsCosetRep V (K : Set (GA D V)) α' R')
    {a b : GA D V} (ha : a ∈ K) (hb : b ∈ K) (hα : α' = a * α * b) {f : GA D V → ℂ}
    (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) : heckeLin V R f = heckeLin V R' f := by
  classical
  have m1 : ∀ γ ∈ R, ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α' * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR.1 γ hγ
    exact ⟨k₁ * a⁻¹, K.mul_mem h₁ (K.inv_mem ha), b⁻¹ * k₂, K.mul_mem (K.inv_mem hb) h₂, by rw [hα]; group⟩
  have m2 : ∀ γ ∈ R', ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR'.1 γ hγ
    exact ⟨k₁ * a, K.mul_mem h₁ ha, b * k₂, K.mul_mem hb h₂, by rw [hα]; group⟩
  have inv : ∀ x y : GA D V, x⁻¹ * y ∈ K → y⁻¹ * x ∈ K := fun x y h => by
    simpa using K.inv_mem h
  funext g
  simp only [heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_bij' (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose)
    (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose_spec.1)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose_spec.1) ?_ ?_ ?_
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have s2 := (hR.2 γ' (m2 γ' s1.1)).exists.choose_spec
    exact (hR.2 γ' (m2 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR.2 γ (m2 γ hγ)).exists.choose_spec
    set γ' := (hR.2 γ (m2 γ hγ)).exists.choose
    have s2 := (hR'.2 γ' (m1 γ' s1.1)).exists.choose_spec
    exact (hR'.2 γ' (m1 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have e : g * γ = g * γ' * (γ'⁻¹ * γ) := by group
    rw [e, hf _ s1.2]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.AdelicU GlobalTheory.PRep in

theorem heckeLin_eq_heckeVec {v : HeightOneSpectrum (𝓞 D.host.F)} {K : Set (GA D V)}
    (hK : ∀ x, x ∈ K ↔ ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x)
    (g : GLoc D.sp.cm.sig V.gram v) {R : Finset (GA D V)} (hR : IsCosetRep V K (emb D.sp.cm.sig V.gram v g) R)
    {φ : GA D V → ℂ}
    (hφ : φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) :
    heckeLin V R φ = GlobalTheory.LFun.heckeVec ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v)
      (Formalism.UG.dosetInd ℂ (stabLoc D.sp.cm.sig V.gram (frameLat V) v) g) φ := by
  classical
  let H : Subgroup (GA D V) := (stabLoc D.sp.cm.sig V.gram (frameLat V) v).map (emb D.sp.cm.sig V.gram v)
  have hKH : K = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  subst hKH
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨R₀, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
    (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g
  obtain ⟨s1, s2⟩ := GlobalTheory.LFun.rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2
  have hR₀ : IsCosetRep V (H : Set (GA D V)) (emb D.sp.cm.sig V.gram v g) (R₀.image (emb D.sp.cm.sig V.gram v)) :=
    ⟨fun γ hγ => ⟨by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact mem_finPts.2 (projInf_emb _ _ v y), s1 γ hγ⟩, s2⟩
  have hinv : ∀ k ∈ H, ∀ x, φ (x * k) = φ x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hφ k hk) x
  rw [heckeLin_eq_of_rep hR hR₀ (one_mem H) (one_mem H) (by group) hinv,
    GlobalTheory.LFun.heckeVec_dosetInd hφ (R := R₀) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ))
      fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]
  funext x
  rw [heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]
  rfl

theorem doubleCoset_of_divAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (hP : IsPrimeIdem P e f)
    {ϖ ϖ' : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal)
    (h2' : ϖ' ∉ P.asIdeal ^ 2) {d : List ℤ} (hd : d.Pairwise (fun a b => b ≤ a)) {α α' : GA D V}
    (hα : SuppF V f α) (hα' : SuppF V f α') (hD : DivAt V e (ϖ : D.host.E) d α)
    (hD' : DivAt V e (ϖ' : D.host.E) d α') :
    ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V f a ∧ b ∈ KsphC V ∅ ∧ SuppF V f b ∧ α' = a * α * b := by
  rcases id hP with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ :=
      GlobalTheory.SplitLabel.split_label V P e ϖ ϖ' d α α' hi h1 h2 h1' h2' hα hα' hD hD'
    exact ⟨a, b, ha, ha', hb, hb', hab⟩
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ hP (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).2.2
      ϖ ϖ' d α' h1 h2 h1' h2' hd hα' hD hD'

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.AdelicU GlobalTheory.PRep in

theorem exists_eig {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hJ : SphOff J χ Sb) (B : GlobalTheory.LFun.Fam D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    ∃ z : ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ R, Hecke₂ V J χ Sb P d R →
      heckeLin V R f = z • f := by
  classical
  by_cases h : ∃ R, Hecke₂ V J χ Sb P d R
  swap
  · exact ⟨0, fun f _ R hR => absurd ⟨R, hR⟩ h⟩
  obtain ⟨R₀, e₀, f₀, ϖ₀, α₀, hS, hP₀, p1, p2, hd, hJ1, -, hα₀, hD₀, -, hR₀⟩ := h
  have hv : P.under (𝓞 D.host.F) ∉ Sb := GlobalTheory.LFun.offS_iff.1 hS
  have hs := Supp.suppF_iff_of_isPrimeIdem V hP₀ rfl
  have hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f₀ k} ↔
      ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F)), emb D.sp.cm.sig V.gram _ k = x :=
    fun x => by
      constructor
      · rintro ⟨m1, m2⟩
        obtain ⟨k, rfl⟩ := (hs x).1 m2
        exact ⟨k, (Supp.emb_mem_KsphC V k).1 ((hJ1 _ m2).1 m1), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have := (hs _).2 ⟨k, rfl⟩
        exact ⟨(hJ1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩
  let H : Subgroup (GA D V) :=
    (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))).map (emb D.sp.cm.sig V.gram _)
  have hKH : {k | k ∈ J ∧ SuppF V f₀ k} = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  obtain ⟨g₀, rfl⟩ := (hs α₀).1 hα₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.sphericalHeckeOperator_eq_smul_of_localParameter _ _ D.sp.cm.sig V.rank V.gram (frameLat V) _ P rfl (B P) _
    (Formalism.UG.Final.DosetIndMem _ (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))) ℂ g₀)
  refine ⟨z, fun f hf R hR => ?_⟩
  obtain ⟨e, f', ϖ, α, -, hP', q1, q2, -, -, -, hα, hD, -, hRc⟩ := hR
  obtain ⟨rfl, rfl⟩ :=
    ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e₀ f₀ hP₀).2.2.2.1 e f' hP'
  have hpv := hf _ hv P rfl
  have hfix := hpv.mem_fixed
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := doubleCoset_of_divAt hP₀ p1 p2 q1 q2 hd hα₀ hα hD₀ hD
  have hmem : ∀ k, k ∈ KsphC V ∅ → SuppF V f' k → k ∈ H := fun k hk hk' => by
    rw [← SetLike.mem_coe, ← hKH]
    exact ⟨(hJ1 k hk').2 hk, hk'⟩
  have hinv : ∀ k ∈ H, ∀ x, f (x * k) = f x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hfix k hk) x
  rw [hKH] at hRc hR₀
  rw [heckeLin_eq_of_rep hRc hR₀ (H.inv_mem (hmem a ha ha')) (H.inv_mem (hmem b hb hb')) (by rw [hab]; group) hinv,
    heckeLin_eq_heckeVec hK g₀ (hKH ▸ hR₀) hfix, hz _ _ f hpv]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

theorem eig_of_param : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E,
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B →
      ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  intro D V J χ Sb hJ B
  choose a ha using exists_eig (V := V) hJ B
  exact ⟨a, fun f hf P d R hR => ha P d f hf R hR⟩

end GlobalTheory.ParamEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlace
section
noncomputable section

namespace GlobalTheory.Core.Rk.BdSplit

section Abstract

open Formalism.UG GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

open Classical in

def cosetInd (S : Finset (G ⧸ K)) : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0

theorem cosetInd_mem {S : Finset (G ⧸ K)} (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) : cosetInd S ∈ Hecke ℂ K := by
  classical
  refine ⟨fun a b g => ?_, S.image Quotient.out, fun g hg => ?_⟩
  · have e : ((a * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K) := QuotientGroup.mk_mul_of_mem _ b.2
    have : (a : G) • (g : G ⧸ K) ∈ S ↔ (g : G ⧸ K) ∈ S :=
      ⟨fun h => by simpa using hS _ (inv_mem a.2) _ h, hS _ a.2 _⟩
    simp only [cosetInd, e, this]
  · have h : (g : G ⧸ K) ∈ S := by
      by_contra h
      exact hg (if_neg h)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ h, 1, k⁻¹, by rw [hk]; simp⟩

theorem heckeVec_cosetInd (ρ : Representation ℂ G V) (S : Finset (G ⧸ K)) (x : V) :
    heckeVec ρ K (cosetInd S) x = ∑ c ∈ S, ρ c.out x := by
  rw [heckeVec, finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun c hc => by simp [cosetInd, hc]
  · intro c hc
    by_contra h
    exact hc (by simp [cosetInd, show c ∉ S from h])

theorem norm_le_card {ι : Type} (ρ : Representation ℂ G V) {x : V} (l : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) (S : Finset ι) (g : ι → G) (a : ℂ)
    (h : ∑ c ∈ S, ρ (g c) x = a • x) : ‖a‖ ≤ S.card := by
  have hb : BddAbove (Set.range fun y => ‖l (ρ y x)‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  set M := ⨆ y, ‖l (ρ y x)‖
  have hM : ∀ y, ‖l (ρ y x)‖ ≤ M := fun y => le_ciSup hb y
  have hM0 : 0 < M := (norm_pos_iff.2 h1).trans_le (hM 1)
  have key : ∀ y, ‖a‖ * ‖l (ρ y x)‖ ≤ S.card * M := fun y => by
    rw [← norm_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← h, map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun c _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact hM _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have : M ≤ S.card * M / ‖a‖ := ciSup_le fun y => by rw [le_div_iff₀' h0]; exact key y
    rw [le_div_iff₀' h0] at this
    exact le_of_mul_le_mul_right this hM0

end Abstract

section Linear

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SatakeBound

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem norm_le_of_isSatVecGL {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (l : V →ₗ[ℂ] ℂ) {C : ℝ} (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) :
    ∀ β ∈ B, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, hφ1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at hφ1
  have hy := isSatVecGL_of_isSpherical hφ hφ0
  have hKO : KO (w.adicCompletion E) (Fin n) = KGL w n := SphCompletion.KO_completion w n
  have hb : HasBoundedSums (w.adicCompletion E) φ := by
    intro S hS
    have H := SatCompare.exists_eigenvalue_GL hx hy
    rw [← hKO] at H
    obtain ⟨c, e1, e2⟩ := H _ (cosetInd_mem hS)
    rw [heckeVec_cosetInd] at e1 e2
    have e3 : ∑ c ∈ S, φ c.out = c := by
      have := congrFun e2 1
      rw [Finset.sum_apply, Pi.smul_apply, hφ1, smul_eq_mul, mul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => congrArg φ (one_mul _).symm
    rw [e3]
    exact norm_le_card ρ l hC h1 S _ c e1
  have hs : IsBorelSph (w.adicCompletion E) (fun i : Fin n => (α i : ℂ) *
      (((resCard (w.adicCompletion E) : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ := by
    refine ⟨fun g k hk => congrFun (GlobalTheory.LGrp.mem_fixed.1 hy.2.1 k (hKO ▸ hk)) g, fun b hb' t ht => ?_⟩
    obtain ⟨y, -, rfl⟩ := (SphCompletion.isSpherical_iff E w n α φ).1 hφ
    have h := GlobalTheory.SatakeBound.Rep.law α y b hb' t ht 1
    rwa [hφ1, mul_one, mul_one] at h
  intro β hβ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
  have hq : (0 : ℝ) < resCard (w.adicCompletion E) := by
    exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard (w.adicCompletion E)).le
  have h2 := norm_le_pow hs hb i
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), ← Real.rpow_natCast] at h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h2
  rw [← GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  exact h2.trans_eq (congrArg _ (by ring))

end Linear

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem paramBound_split : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  rintro D A L - v hv par c ⟨⟨C, hC⟩, V, _, _, ρ, x, l, hx, -, hc⟩ h1 w h
  refine ⟨(hx w h).card, fun β hβ => ?_⟩
  rcases hx w h with ⟨-, e, -, hx⟩ | ⟨hw, -⟩
  · have hb := norm_le_of_isSatVecGL hx l (C := C) (fun y => (hc (e.symm y)) ▸ hC (e.symm y))
      (by rw [hc] at h1; rwa [map_one, ← map_one ρ]) β hβ
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm w).le
  · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)

end GlobalTheory.Core.Rk.BdSplit

end
end


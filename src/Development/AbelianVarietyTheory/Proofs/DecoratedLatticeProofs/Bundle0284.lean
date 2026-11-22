import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeCombinationMovesLastStepDatumToChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem exchange_posOne_last : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m) (s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h)), s₁.χW = χ Q.s → ∀ α (Tm : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] (WO (c.V Q.s) (c.V (Q.s + 1)) → ℂ)), (ofSplit Q.q).IsModel c.ψ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 (by omega)) Tm → ∀ Φ Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k), Φ.1 = Q.T.Phi Q.s 0 rfl → Φα.1 = om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl) → ∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (Tm Φ) = Tm Φα := by
  intro D c v χ Q _ h s₁ hχ α Tm hTm Φ Φα hΦ hΦα
  obtain ⟨⟨ρ', hρ'⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep Q.k (Q.X Q.s ⊕ Fin (0 + 1)) (Q.X (Q.s + 1) ⊕ Fin 0)
    (Q.T.mu (Q.s + 1)) (Q.mu Q.s (by omega)).2
  have hsmooth := hsm ρ' hρ'
  obtain ⟨e, he, heL⟩ := Q.εL_at Q.s 0 h 0 rfl α
  obtain ⟨μS, hμS⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) s₁.χV
  have hμT : (ofSplit Q.q).IsComp s₁.χW (Q.T.mu (Q.s + 1))⁻¹ := by
    intro x a hxa
    have := (Q.mu Q.s (by omega)).1 x a hxa
    rw [hχ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this]
    simp
  have hloc1 : (ofSplit Q.q).IsLoc (Q.FY (Q.s + 1) 0 (by omega)) 1 1 := by
    have := Q.gl_loc (Q.s + 1) 0 (by omega) 1
    rwa [map_one] at this
  have key : ∀ g, s₁.om (Q.gl Q.s (0 + 1) (by omega) g, 1) (Tm Φ) = Tm (ρ' g Φ) := by
    intro g
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) c.ψ _ _ s₁.χV s₁.χW s₁.om s₁.weil μS _ hμS hμT _ _ _ _ Tm hTm
      _ g 1 1 (Q.gl_loc Q.s (0 + 1) (by omega) g) hloc1 Φ (ρ' g Φ) ?_
    rw [hρ']
    funext x
    have hu : (((μS * Q.T.mu (Q.s + 1)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        = ((Q.T.mu (Q.s + 1) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm (μS _), mul_assoc, mul_inv_cancel, mul_one]
    simp only [om, Pi.smul_apply, smul_eq_mul, map_one, inv_one, Units.val_one, inv_inv]
    rw [← hu]
    ring
  have hN : ∀ g ∈ N Q.k (Q.X Q.s) (0 + 1) (0 + 1), g = 1 := by
    intro g hg
    have hle : N Q.k (Q.X Q.s) (0 + 1) (0 + 1) ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 fun g' hg' => ?_
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      ext r s
      refine hg' r s ?_
      rcases r with r | r <;> rcases s with s | s <;> simp [GlobalTheory.RootEx.lev, Fin.val_eq_zero]
    exact Subgroup.mem_bot.1 (hle hg)
  let lx : Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k →
      (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] ℂ) :=
    fun x => (LinearMap.proj x).comp (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k)).subtype
  have hsum : Φα = e.sum (fun g a => a • ρ' g Φ) := by
    apply Subtype.ext
    funext x
    have h1 := he _ ρ' hsmooth (lx x) (fun g hg w => by
        rw [hN g hg]
        simp [GlobalTheory.RootEx.simpleSum]) Φ (fun j => by
        apply Subtype.ext
        rw [hρ', Submodule.coe_smul, hΦ, (Q.laws.1 Q.s 0 rfl).1 j])
    have h2 : (Φα : Matrix _ _ _ → ℂ) x = lx x (ρ' (Q.rep Q.s 0 rfl α) Φ) := by
      simp only [lx, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, hΦα]
      rw [hρ', hΦ]
    have h3 : ((e.sum fun g a => a • ρ' g Φ : SB _) : Matrix _ _ _ → ℂ) x = lx x (e.sum fun g a => a • ρ' g Φ) := rfl
    rw [h2, h3, map_finsuppSum]
    refine h1.trans ?_
    simp [GlobalTheory.PosOne.comb, map_smul]
  rw [heL]
  show (Finsupp.mapDomain _ e).sum (fun g a => a • s₁.om (g, 1) (Tm Φ)) = Tm Φα
  rw [Finsupp.sum_mapDomain_index (h := fun g (a : ℂ) => a • s₁.om (g, 1) (Tm Φ)) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [hsum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, key]

end GlobalTheory.QPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod Filter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.DblInhab

theorem exists_dbl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (n₀ n₁ n₂ : Type)
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (F₀ : GlobalTheory.LocMod.Frame k B.A.rank n₀) (F₁ : GlobalTheory.LocMod.Frame k J.W₀.rank n₁) (F₂ : GlobalTheory.LocMod.Frame k B'.A.rank n₂) (s : k),
    s ≠ 0 → ∃ F : Dbl p B J B' n₀ n₁ n₂ (2 * σ), F.s = s ∧ F.F₀ = F₀ ∧ F.F₁ = F₁ ∧ F.F₂ = F₂ := by
  intro D k _ _ _ _ p σ B J B' n₀ n₁ n₂ _ _ _ _ _ _ F₀ F₁ F₂ s hs
  have hx := GlobalTheory.LocChar.xi_ne p
  obtain ⟨-, ⟨G₀, h₀⟩, hz⟩ := (Exist.exists_frames D k p n₀ (σ + 1) s hs).1 B F₀
  obtain ⟨G₁, h₁⟩ := (Exist.exists_frames D k p n₁ (σ + 1) s hs).2 J _ hz F₁
  obtain ⟨-, ⟨G₂, h₂⟩, -⟩ := (Exist.exists_frames D k p n₂ σ (s * p.xi) (mul_ne_zero hs hx)).1 B' F₂
  exact ⟨⟨s, hs, F₀, F₁, F₂, G₀, G₁, G₂, h₀, h₁, h₂⟩, rfl, rfl, rfl, rfl⟩

section Gram

variable (E : Type) [Field E] [CharZero E] [StarRing E]

theorem five_gram (e e' : Matrix (Fin 5) (Fin 1) E) (i : Matrix (Fin 5) (Fin 3) E) (he : e = !![0; 0; 0; 1; 1])
    (he' : e' = !![0; 0; 0; 1 / 2; -(1 / 2)]) (hi : i = !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0]) :
    eᴴ * sgnM E ![false, false, false, false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, false, false, false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, false, false, false, true] * e = 1 ∧
    iᴴ * sgnM E ![false, false, false, false, true] * i = sgnM E (fun _ => false) ∧
    iᴴ * sgnM E ![false, false, false, false, true] * e = 0 ∧ iᴴ * sgnM E ![false, false, false, false, true] * e' = 0 := by
  subst he he' hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b <;> rw [Matrix.mul_apply] <;>
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_five, Examples₂.sgn] <;> norm_num

omit [CharZero E] in
theorem sub_gram {N a b : ℕ} (M : Matrix (Fin N) (Fin N) E) (f : Fin a → Fin N) (g : Fin b → Fin N) :
    ((1 : Matrix (Fin N) (Fin N) E).submatrix id f)ᴴ * M * (1 : Matrix (Fin N) (Fin N) E).submatrix id g = M.submatrix f g := by
  have h := Matrix.submatrix_mul (1 : Matrix (Fin N) (Fin N) E) M f id id Function.bijective_id
  rw [Matrix.submatrix_id_id] at h
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, ← h, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.one_mul, Matrix.mul_one]

omit [CharZero E] in
theorem last_gram (N : ℕ) (a : Matrix (Fin (N + 1)) (Fin N) E) (b : Matrix (Fin (N + 1)) (Fin 1) E)
    (ha : a = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).submatrix id Fin.castSucc)
    (hb : b = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).submatrix id fun _ => Fin.last N) :
    aᴴ * sgnM E (fun i => decide (i = Fin.last N)) * a = sgnM E (fun _ => false) ∧
    bᴴ * sgnM E (fun i => decide (i = Fin.last N)) * b = sgnM E ![true] ∧
    bᴴ * sgnM E (fun i => decide (i = Fin.last N)) * a = 0 := by
  subst ha hb
  refine ⟨?_, ?_, ?_⟩ <;> rw [sub_gram] <;> ext i j
  · simp [Matrix.diagonal_apply, Fin.castSucc_ne_last]
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp
  · simp [Matrix.diagonal_apply, (Fin.castSucc_ne_last j).symm]

end Gram

abbrev posSp (D : D7) (N : ℕ) : HSp D := diagSp D N (fun _ => false) N 0

theorem coCpt_posSp (D : D7) (N : ℕ) : CoCpt (posSp D N) := by
  refine GlobalTheory.Unf.Inhab.coCpt_of_posDef fun τ => ?_
  have h : gramAt D (posSp D N) τ = 1 := by
    rw [gramAt, diagSp_gram]
    exact Matrix.map_one _ (map_zero (tauE D τ)) (map_one (tauE D τ))
  rw [h]
  exact Matrix.PosDef.one

def hypFive (D : D7) : HypDec (diagSp D 5 ![false, false, false, false, true] 4 1) (posSp D 3) 1 where
  e := (!![0; 0; 0; 1; 1] : Matrix (Fin 5) (Fin 1) D.host.E)
  e' := (!![0; 0; 0; 1 / 2; -(1 / 2)] : Matrix (Fin 5) (Fin 1) D.host.E)
  i₀ := (!![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0] : Matrix (Fin 5) (Fin 3) D.host.E)
  ee := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).1
  e'e' := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.1
  e'e := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.1
  iso := (gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.1).trans (diagSp_gram 3 _ 3 0).symm
  i₀e := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.1
  i₀e' := gram_check _ _ _ (five_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.2
  rank_add := rfl

def orthLast (D : D7) (N : ℕ) :
    OrthDec (diagSp D (N + 1) (fun i => decide (i = Fin.last N)) N 1) (posSp D N) (GlobalTheory.Unf.Inhab.negLine D) where
  iA := ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) D.host.E).submatrix id Fin.castSucc : Matrix (Fin (N + 1)) (Fin N) D.host.E)
  iB := ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) D.host.E).submatrix id fun _ => Fin.last N :
    Matrix (Fin (N + 1)) (Fin 1) D.host.E)
  isoA := (gram_check _ _ _ (last_gram D.host.E N _ _ rfl rfl).1).trans (diagSp_gram N _ N 0).symm
  isoB := (gram_check _ _ _ (last_gram D.host.E N _ _ rfl rfl).2.1).trans (diagSp_gram 1 _ 0 1).symm
  orth := gram_check _ _ _ (last_gram D.host.E N _ _ rfl rfl).2.2
  rank_add := rfl

open GlobalTheory.Unf.Inhab in

theorem exists_levels (D : D7) : ∃ (B : BesLev D (0 + 1)) (J : JacLev D (0 + 1)) (B' : BesLev D 0),
    1 = B.A.rank ∧ 3 = J.W₀.rank ∧ 5 = B'.A.rank ∧ Nonempty (Link B B'.L B'.ζ) := by
  let B : BesLev D 1 := besPlane (GlobalTheory.RegSW.Model.hypFour D) (cmHost_imaginaryGenerator_ne_zero D)
  let J : JacLev D 1 := ⟨_, _, hypFive D, coCpt_posSp D 3, (nonempty_vol _).some, (nonempty_volN _).some⟩
  let B' : BesLev D 0 := ⟨_, _, _, _, hypRefl _, orthLast D 5, fun _ => 1, isLineVec_negLine one_ne_zero, coCpt_posSp D 5,
    (nonempty_vol _).some, (nonempty_volN _).some⟩
  have e : D.host.xi0⁻¹ • B.ζ = B'.ζ := funext fun _ => inv_mul_cancel₀ (cmHost_imaginaryGenerator_ne_zero D)
  have l : Link B B.L B'.ζ := e ▸ selfLink B
  exact ⟨B, J, B', rfl, rfl, rfl, ⟨l⟩⟩

section Place

open GlobalTheory.FinPl (SplitPt Pl idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := GlobalTheory.LocChar.ι_one (ofSplit q)

theorem sec_mul_pr (a : k) (o : AE D) : q.sec (a * q.pr o) = q.sec a * o := by
  have h := q.sec_pr (q.sec a * o)
  rw [map_mul, q.pr_sec] at h
  rw [h, ← mul_assoc]
  exact congrArg (· * o) (GlobalTheory.LocChar.e_mul_ι (ofSplit q) a)

theorem sec_mem_idAt (a : k) : q.sec a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  obtain ⟨hee, hec, -⟩ := q.split
  have he : q.e ∈ idAt D (· = q.v) := by
    refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 q.e).2 ?_
    rw [← hsum, add_mul, hee, mul_comm (cA D q.e), hec, add_zero]
  have h : q.e * q.sec a = q.sec a := GlobalTheory.LocChar.e_mul_ι (ofSplit q) a
  rw [← h]
  exact Ideal.mul_mem_right _ _ he

theorem sec_mem_intAt (a : k) : q.sec a ∈ intAt D (· = q.v) ↔ valuation k a ≤ 1 :=
  (and_iff_right (sec_mem_idAt q a)).trans (q.int_iff a).symm

theorem pr_le_one {o : AE D} (ho : o ∈ intAt D (· = q.v)) : valuation k (q.pr o) ≤ 1 := by
  refine (q.int_iff _).2 ?_
  rw [q.sec_pr, ← sec_one, map_mul]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ((q.int_iff 1).1 (one_mem _)) ho.2

theorem hasConductor {ψ : AddChar (AF D.host.F) ℂ}
    (hc : ∀ s ∈ idAt D (· = q.v), (∀ o ∈ intAt D (· = q.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = q.v))
    (h1 : ∀ a ∈ intAt D (· = q.v), incA D D.host.xi0 * a ∈ intAt D (· = q.v))
    (h2 : ∀ a ∈ intAt D (· = q.v), incA D D.host.xi0⁻¹ * a ∈ intAt D (· = q.v))
    {ψk : AddChar k Circle} (hk : (ofSplit q).IsChar ψ ψk) : HasConductor ψk 1 := by
  have hk' : ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec x) := hk
  intro x
  rw [Units.val_one, map_one]
  refine ⟨fun h => ?_, fun h y hy => Circle.ext ?_⟩
  · have hs := (hc _ (Ideal.mul_mem_left _ (incA D D.host.xi0) (sec_mem_idAt q x))).1 fun o ho => by
      rw [mul_assoc, ← sec_mul_pr, ← hk', h _ (by rw [map_mul]; exact mul_le_of_le_one_right' (pr_le_one q ho)), Circle.coe_one]
    have := h2 _ hs
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D), map_one, one_mul] at this
    exact (sec_mem_intAt q x).1 this
  · have hs := h1 _ ((sec_mem_intAt q y).2 (hy.trans h))
    have := (hc _ hs.1).2 hs _ ((sec_mem_intAt q 1).2 (map_one _).le)
    rw [mul_assoc, ← sec_mul_pr, q.pr_sec, mul_one] at this
    rw [hk', this, Circle.coe_one]

end Place

theorem eventually_isUnram (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) : ∀ᶠ v : GlobalTheory.FinPl.Pl D in cofinite,
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k),
      q.v = v → ∀ μ, (ofSplit q).IsComp χ μ → IsUnram μ := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv k _ _ _ _ q hq μ hμ x hx
  subst hq
  have key : ∀ y : k, valuation k y ≤ 1 → infPart D (q.sec y + (1 - q.e)) = 1 ∧ finPart D (q.sec y + (1 - q.e)) ∈ intAE D ∧
      ∃ z ∈ intAE D, finPart D (q.sec y + (1 - q.e)) - 1 = N • z := fun y hy => by
    have hy' := (sec_mem_intAt q (y - 1)).2 ((Valuation.map_sub _ _ _).trans (max_le hy (map_one _).le))
    have e : q.sec y + (1 - q.e) = q.sec (y - 1) + 1 := by rw [map_sub, sec_one]; ring
    have hi : infPart D (q.sec (y - 1)) = 0 := hy'.1.1
    rw [e, RingHom.map_add, RingHom.map_add, RingHom.map_one, RingHom.map_one, hi, zero_add, add_sub_cancel_right]
    refine ⟨rfl, add_mem hy'.2 (GlobalTheory.HeckeConj.one_mem_intAE D), _, (hv _ hy').2, ?_⟩
    have e' : q.sec (y - 1) = N • (incA D (N : D.host.E)⁻¹ * q.sec (y - 1)) := by
      rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
    exact (congrArg (finPart D) e').trans ((finPart D).toAddMonoidHom.map_nsmul _ _)
  have hx' : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have h1 : χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) = 1 :=
    hker _ ⟨(key _ hx.le).1, (key _ hx.le).2.1, (key _ hx').2.1⟩ (key _ hx.le).2.2
  have h2 := hμ x (GlobalTheory.LocChar.unitsHom (ofSplit q) x) rfl
  rw [h1, Circle.coe_one] at h2
  exact Units.ext h2

theorem isTame_of_isUnram {k : Type} [Field k] [ValuativeRel k] {μ : kˣ →* ℂˣ} (h : IsUnram μ) : IsTame μ := fun x hx =>
  h x (by simpa using Valuation.map_one_add_of_lt (valuation k) hx)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_good_place (D : D7) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (χ₁ χ₂ : (AE D)ˣ →* Circle)
    (h₁ : Continuous χ₁) (h₂ : Continuous χ₂) : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
      (_ : IsNonarchimedeanLocalField k) (p : Place D k) (ψk : AddChar k Circle) (μ₁ μ₂ : kˣ →* ℂˣ),
      p.IsChar ψ ψk ∧ HasConductor ψk 1 ∧ p.IsComp χ₁ μ₁ ∧ IsUnram μ₁ ∧ p.IsComp χ₂ μ₂ ∧ IsUnram μ₂ := by
  have hev := (GlobalTheory.T.standard_character_conductor_almost_all D ψ hψ).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹).and
      ((eventually_isUnram D χ₁ h₁).and (eventually_isUnram D χ₂ h₂))))
  obtain ⟨v, ⟨e, ε, he, hε, hs⟩, a1, a2, a3, a4, a5⟩ := ((Filter.frequently_cofinite_iff_infinite.2 (GlobalTheory.T.infinitely_many_split_places D)).and_eventually hev).exists
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  obtain ⟨⟨ψk, hk⟩, -, -, -, hc⟩ := GlobalTheory.LocChar.weil_char_split D _ (ofSplit q) ψ hψ
  obtain ⟨μ₁, c₁⟩ := hc χ₁
  obtain ⟨μ₂, c₂⟩ := hc χ₂
  exact ⟨_, _, _, _, _, ofSplit q, ψk, μ₁, μ₂, hk, hasConductor q (by rw [hq]; exact a1) (by rw [hq]; exact a2)
    (by rw [hq]; exact a3) hk, c₁, a4 _ q hq _ c₁, c₂,
    a5 _ q hq _ c₂⟩

end GlobalTheory.LocMod.DblInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.SevPl

open GlobalTheory.IdemSupport

theorem ev_sum {D : D7} {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {ι : Type}
    (s : Finset ι) (f : ι → Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (∑ i ∈ s, f i) Q = ∑ i ∈ s, Φ (f i) Q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]; exact ev_zero Q
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem cP_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (D := D) (cP (D := D) P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by
    show cO D (cO D x) ∈ P.asIdeal ↔ x ∈ P.asIdeal
    rw [cO_cO])

theorem mul_conj_add_eq_zero {D : D7} {Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))} {E : Formalism.L2.Theta.AE D}
    (hE : IsIdemSum E Pg) {P P' : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Pg) (hP' : P' ∈ Pg) (hne : P ≠ P')
    {e e' : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P') :
    e * (e' + cA D e') = 0 := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ he
  have hd' := delta_of_isIdemAt hΦ he'
  have hc' := delta_conj hΦ hd'
  have hne2 : P ≠ cP (D := D) P' := by
    intro hPc
    obtain ⟨⟨es, hes, rfl⟩, h0⟩ := hE
    have h1 : Φ (∑ Q ∈ Pg, es Q) P = 1 := by
      rw [ev_sum, Finset.sum_eq_single_of_mem P hP fun Q hQ hQP => ?_]
      · exact (delta_of_isIdemAt hΦ (hes P hP)).2.1
      · exact (delta_of_isIdemAt hΦ (hes Q hQ)).2.2 P (Ne.symm hQP)
    have h2 : Φ (cA D (∑ Q ∈ Pg, es Q)) P = 1 := by
      rw [map_sum, ev_sum, Finset.sum_eq_single_of_mem P' hP' fun Q hQ hQP => ?_]
      · rw [hPc]; exact (delta_conj hΦ (delta_of_isIdemAt hΦ (hes P' hP'))).2.1
      · refine (delta_conj hΦ (delta_of_isIdemAt hΦ (hes Q hQ))).2.2 P fun h => hQP ?_
        have h4 := congrArg (cP (D := D)) (h.symm.trans hPc)
        rwa [cP_cP, cP_cP] at h4
    have h3 := ev_mul (Φ := Φ) (∑ Q ∈ Pg, es Q) (cA D (∑ Q ∈ Pg, es Q)) P
    rw [h0, ev_zero, h1, h2, one_mul] at h3
    exact zero_ne_one h3
  refine hΦ.ext' (by rw [map_mul, hd.1, zero_mul, map_zero]) fun Q => ?_
  rw [ev_mul, ev_add, ev_zero]
  by_cases hQ : Q = P
  · subst hQ; rw [hd'.2.2 Q hne, hc'.2.2 Q hne2, add_zero, mul_zero]
  · rw [hd.2.2 Q hQ, zero_mul]

theorem pr_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {f : Formalism.L2.Theta.AE D} (h : q.e * f = 0) : q.pr f = 0 := by
  rw [← q.pr_sec (q.pr f), q.sec_pr, h, map_zero]

theorem map_mt_eq_one {D : D7} {k : Type} [Field k] (π : Formalism.L2.Theta.AE D →+* k) {e : Formalism.L2.Theta.AE D}
    (V : HSp D) (g : GA D V) (hs : Formalism.L2.Theta.SuppAt e V g) (h0 : π (e + cA D e) = 0) :
    (mt V g).map π = 1 := by
  ext i j
  have h1 := congrArg π (hs i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1.symm]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

def locHom {D : D7} {k : Type} [Field k] (π : Formalism.L2.Theta.AE D →+* k) (V : HSp D) :
    GA D V →* Matrix (Fin V.rank) (Fin V.rank) k where
  toFun g := (mt V g).map π
  map_one' := by rw [GlobalTheory.IdemSupport.mt_one]; exact Matrix.map_one π π.map_zero π.map_one
  map_mul' g h := by rw [GlobalTheory.IdemSupport.mt_mul, Matrix.map_mul]

theorem prod_map_single {M α : Type} [Monoid M] (g : α → M) (a : α) :
    ∀ l : List α, l.Nodup → a ∈ l → (∀ x ∈ l, x ≠ a → g x = 1) → (l.map g).prod = g a
  | [], _, ha, _ => by simp at ha
  | x :: l, hn, ha, h1 => by
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 hn
    by_cases hxa : x = a
    · subst hxa
      rw [List.prod_eq_one fun y hy => ?_, mul_one]
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact h1 z (List.mem_cons_of_mem _ hz) fun h => hx (h ▸ hz)
    · rw [h1 x (by simp) hxa, one_mul]
      exact prod_map_single g a l hl ((List.mem_cons.1 ha).resolve_left (Ne.symm hxa))
        fun y hy => h1 y (List.mem_cons_of_mem _ hy)

end GlobalTheory.LocMod.SevPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenFix
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.OneComb

theorem exists_open_fix' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Y : Type} [Fintype Y] [DecidableEq Y]
    (L : Level (GL Y k)) (hL : IsOpen (L.J : Set (GL Y k))) (α : GL Y k) :
    ∃ U : Subgroup (GL Y k), IsOpen (U : Set (GL Y k)) ∧ ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL Y k) A),
      IsSmoothRep σ → ∀ v : A, (∀ j : L.J, σ (j : GL Y k) v = (L.lam j : ℂ) • v) → ∀ u ∈ U, σ u (σ α v) = σ α v := by
  by_cases h : IsOpen ((L.lam.ker.map L.J.subtype : Subgroup (GL Y k)) : Set (GL Y k))
  · refine ⟨(L.lam.ker.map L.J.subtype).comap (MulAut.conj α⁻¹).toMonoidHom,
      h.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun A _ _ σ _ v hv u hu => ?_⟩
    obtain ⟨j, hj, e⟩ := hu
    have e' : u * α = α * j := by
      have e2 : (j : GL Y k) = α⁻¹ * u * α⁻¹⁻¹ := e
      simp [e2, mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, hv, show L.lam j = 1 from hj, Units.val_one, one_smul]
  · refine ⟨⊤, isOpen_univ, fun A _ _ σ hσ v hv u _ => ?_⟩
    obtain rfl : v = 0 := by
      by_contra v0
      refine h (Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hL.inter (hσ v)).mem_nhds ⟨L.J.one_mem, by simp⟩) fun g hg => ⟨⟨g, hg.1⟩, Units.ext ?_, rfl⟩))
      exact smul_left_injective ℂ v0 (((hv ⟨g, hg.1⟩).symm.trans hg.2).trans (one_smul ℂ v).symm)
    simp

theorem exists_isOneComb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), IsCO L.J → ∀ α, ∃ e, IsOneComb ψ ν P L α e := by
  intro k _ _ _ _ _ _ n _ _ c P h1 hP ψ hψc hψ1 ν hν L hL α
  obtain ⟨U, hU, h⟩ := exists_open_fix' L hL.1 α
  obtain ⟨e, e', he⟩ := GlobalTheory.T.exchangeToPositionOne_uniform_in_level k n c P h1 hP ψ hψc hψ1 ν hν U hU
  refine ⟨e.mapDomain (· * α), fun A _ _ σ hσ l hl v hv => ?_⟩
  rw [(he A σ hσ l _ hl (h A σ hσ v hv)).1, GlobalTheory.PosOne.comb, GlobalTheory.PosOne.comb,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_mul _ _ _)]
  simp only [map_mul, Module.End.mul_apply]

end GlobalTheory.QPl.OneComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realCentre_character_on_definiteVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  first | exact @GlobalTheory.CenterVac.exists_center_char | exact GlobalTheory.CenterVac.exists_center_char | (intros; apply GlobalTheory.CenterVac.exists_center_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompactStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∀ (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∃ p : siegel A, IsConj A a κ p := by
  first | exact @GlobalTheory.StdUnn.ConjElt.exists_isConj | exact GlobalTheory.StdUnn.ConjElt.exists_isConj | (intros; apply GlobalTheory.StdUnn.ConjElt.exists_isConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceInvariantFormOfWittCoreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_invariantForm_of_wittCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ (d.mixS T ψ μ 𝓕 (f') x) = k * ℓ₀ (d.mixS T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  first | exact @GlobalTheory.SplitPlaceForm.exists_form_of_core | exact GlobalTheory.SplitPlaceForm.exists_form_of_core | (intros; apply GlobalTheory.SplitPlaceForm.exists_form_of_core <;> assumption)
end


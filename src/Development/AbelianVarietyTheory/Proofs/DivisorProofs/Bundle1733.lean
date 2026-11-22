import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankAddLtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank_lt | exact GlobalTheory.FunObj.squareTriple_sig_rank_lt | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank | exact GlobalTheory.FunObj.squareTriple_sig_rank | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory

open scoped Pointwise

namespace StarAAbar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

theorem bb_ne_bot {D : D7} : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem conj_bb_ne_bot {D : D7} : D.host.conj • D.host.𝔟 ≠ ⊥ := by
  intro h
  apply bb_ne_bot (D := D)
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa using this

theorem conj_inv_smul {D : D7} (x : 𝓞 D.host.E) : D.host.conj⁻¹ • x = D.host.conj • x := by
  have h : D.host.conj⁻¹ = D.host.conj := by
    rw [inv_eq_iff_mul_eq_one]
    exact AlgEquiv.ext fun y => conj_conj D y
  rw [h]

end StarAAbar

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 800000 in

theorem star_mem_AA_of_mem_AAbar : ∀ {D : D7} {c : D.host.E}, c ∈ D.host.AAbar → star c ∈ D.host.AA := by
  intro D c hc
  have hJ : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.bb_ne_bot
  have hJc : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.conj_bb_ne_bot

  have h1 : ∀ y ∈ D.host.conj • D.host.𝔟, c * (y : D.host.E) ∈
      ((D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro y hy
    have hyJ : (y : D.host.E) ∈ ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩
    have := FractionalIdeal.mul_mem_mul hc hyJ
    unfold Host.AAbar at this
    rwa [mul_assoc, inv_mul_cancel₀ hJc, mul_one] at this

  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
      ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hy : D.host.conj • j' ∈ D.host.conj • D.host.𝔟 := Ideal.smul_mem_pointwise_smul _ _ _ hj'
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 _ hy)
    have hxs : D.host.conj • x ∈ D.host.ccE := by
      have := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 hx
      rwa [StarAAbar.conj_inv_smul] at this
    have key : star c * algebraMap (𝓞 D.host.E) D.host.E j' = algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • x) := by
      show star c * (j' : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [StarAAbar.coe_smul, show ((x : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x from rfl, hxe,
        map_mul, StarAAbar.coe_smul, StarAAbar.conj_conj, StarAAbar.star_eq_conj]
    rw [smul_mul_assoc, key]
    exact Submodule.smul_mem _ _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hxs, rfl⟩)
  have h3 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) ≤ D.host.AA := by
    unfold Host.AA Host.AA0
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hJ, mul_one]
      _ ≤ _ := by gcongr
  exact h3 (FractionalIdeal.mem_spanSingleton_self _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdSumFixEig
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem hatId_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

abbrev mat {N : ℕ} (k : GA D N) : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))

theorem mat_mul {N : ℕ} (x y : GA D N) : mat (x * y) = mat x * mat y := rfl

theorem mat_inv_mul {N : ℕ} (x : GA D N) : mat x⁻¹ * mat x = 1 := by
  simp [mat]

theorem mat_mul_inv {N : ℕ} (x : GA D N) : mat x * mat x⁻¹ = 1 := by
  simp [mat]

theorem ent_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (hB : ∀ i j, B i j ∈ hatId D 𝔪) (i j : Fin N) : (A * B) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => hatId_mul_left (hA i l) (hB l j)

theorem ent_mul_right {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hB : ∀ i j, B i j ∈ hatId D 𝔪) (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : (B * A) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => by rw [mul_comm]; exact hatId_mul_left (hA l j) (hB i l)

theorem ent_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k i j ∈ OhE D :=
  ((mem_intG k).1 hk i j).1

theorem ent_inv_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k⁻¹ i j ∈ OhE D :=
  ((mem_intG k⁻¹).1 (inv_mem hk) i j).1

variable {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}

theorem congOne_one : CongOne D 𝔪 (1 : GA D N) := fun i j => by
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]; exact zero_mem _

theorem congOne_mul {x y : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) (cy : CongOne D 𝔪 y) :
    CongOne D 𝔪 (x * y) := fun i j => by
  have e : mat (x * y) - 1 = mat x * (mat y - 1) + (mat x - 1) := by rw [mat_mul, mul_sub, mul_one]; abel
  change (mat (x * y) - 1) i j ∈ _
  rw [e, Matrix.add_apply]
  exact add_mem (ent_mul_left (ent_of_mem hx) cy i j) (cx i j)

theorem congOne_inv {x : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 x⁻¹ := fun i j => by
  have e : mat x⁻¹ - 1 = -(mat x⁻¹ * (mat x - 1)) := by rw [mul_sub, mat_inv_mul, mul_one]; abel
  change (mat x⁻¹ - 1) i j ∈ _
  rw [e, Matrix.neg_apply]
  exact neg_mem (ent_mul_left (ent_inv_of_mem hx) cx i j)

theorem congOne_conj {g x : GA D N} (hg : g ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 (g * x * g⁻¹) :=
  fun i j => by
  have e : mat (g * x * g⁻¹) - 1 = mat g * (mat x - 1) * mat g⁻¹ := by
    rw [mat_mul, mat_mul, mul_sub, sub_mul, mul_one, mat_mul_inv]
  change (mat (g * x * g⁻¹) - 1) i j ∈ _
  rw [e]
  exact ent_mul_right (ent_mul_left (ent_of_mem hg) cx) (ent_inv_of_mem hg) i j

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem zero_mem_TT (T : Tor D) (N N' : ℕ) : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem add_mem_TT {T : Tor D} {N N' : ℕ} {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') :
    F + G ∈ TT D T N N' := by
  obtain ⟨hF1, m, hm, hFm⟩ := hF
  obtain ⟨hG1, n, hn, hGn⟩ := hG
  refine ⟨hF1.add hG1, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
  have h1 := hFm (n • x) (AddSubgroup.nsmul_mem _ hx n)
  have h2 := hGn (m • x) (AddSubgroup.nsmul_mem _ hx m)
  rw [smul_smul] at h1 h2
  rw [mul_comm n m] at h2
  funext z
  have e1 := congrFun h1 z
  have e2 := congrFun h2 z
  simp only [Wd, U, Pi.add_apply] at e1 e2 ⊢
  linear_combination e1 + e2

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {ι : Type*} (s : Finset ι) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i ∈ s, f i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, f i) ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, f i) = ∑ i ∈ s, W.Om g g' (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using zero_mem_TT (tor0 D cc δ) N N', ?_⟩
    have h := W.smul g g' 0 0 (zero_mem_TT _ N N')
    simpa using h
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hfi := hf i (Finset.mem_insert_self i s)
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact ⟨add_mem_TT hfi h1, by rw [W.add g g' _ hfi _ h1, h2]⟩

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

section Reps

variable {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) {𝔪 : Ideal (𝓞 D.host.E)}
  {v : VC D a d → ℂ} {R : Finset (GA D a)}

theorem Om_rep (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    {x r : GA D a} (hx : x ∈ intG D a) (hr : r ∈ intG D a) (hc : CongOne D 𝔪 (r⁻¹ * x)) :
    W.Om x 1 v = W.Om r 1 v := by
  have h := W.mul r (r⁻¹ * x) 1 1 v hv
  rw [mul_inv_cancel_left, mul_one] at h
  rw [h, hfix _ (mul_mem (inv_mem hr) hx) hc]

theorem sum_reindex (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    (hRi : ∀ r ∈ R, r ∈ intG D a) (hR : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k))
    (φ : GA D a → GA D a) (hφ : ∀ r ∈ R, φ r ∈ intG D a)
    (inj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s ∈ R, CongOne D 𝔪 (s⁻¹ * φ r₁) → CongOne D 𝔪 (s⁻¹ * φ r₂) → r₁ = r₂)
    (surj : ∀ s ∈ R, ∃ r ∈ R, CongOne D 𝔪 (s⁻¹ * φ r)) :
    ∑ r ∈ R, W.Om (φ r) 1 v = ∑ s ∈ R, W.Om s 1 v := by
  classical
  let ψ : GA D a → GA D a := fun r => if h : r ∈ R then (hR (φ r) (hφ r h)).exists.choose else r
  have hψ : ∀ r ∈ R, ψ r ∈ R ∧ CongOne D 𝔪 ((ψ r)⁻¹ * φ r) := fun r hr => by
    simp only [ψ, dif_pos hr]; exact (hR (φ r) (hφ r hr)).exists.choose_spec
  refine Finset.sum_nbij ψ (fun r hr => (hψ r hr).1) ?_ ?_ ?_
  · intro r₁ hr₁ r₂ hr₂ e
    have h1 := (hψ r₁ hr₁).2
    have h2 := (hψ r₂ hr₂).2
    rw [e] at h1
    exact inj r₁ hr₁ r₂ hr₂ (ψ r₂) (hψ r₂ hr₂).1 h1 h2
  · intro s hs
    obtain ⟨r, hr, hc⟩ := surj s hs
    exact ⟨r, hr, (hR (φ r) (hφ r hr)).unique (hψ r hr) ⟨hs, hc⟩⟩
  · intro r hr
    exact Om_rep W hv hfix (hφ r hr) (hRi _ (hψ r hr).1) (hψ r hr).2

end Reps

theorem stdSum_fix_eig : ∀ (D : D7) (δ : ℂ) (a d : ℕ) (e0 : VC D a d → ℂ) (W : WeilO D ⊤ δ a d e0)
    (𝔪 : Ideal (𝓞 D.host.E)) (v : VC D a d → ℂ), v ∈ TT D (tor0 D ⊤ δ) a d →
    (∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) →
    (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (∀ k ∈ intG D a, W.Om k 1 (∑ r ∈ R, W.Om r 1 v) = ∑ r ∈ R, W.Om r 1 v) ∧
    ∀ (j : GA D d) (k : GA D a) (c : ℂ), k ∈ intG D a → W.Om 1 j v = c • W.Om k 1 v →
      W.Om 1 j (∑ r ∈ R, W.Om r 1 v) = c • ∑ r ∈ R, W.Om r 1 v := by
  intro D δ a d e0 W 𝔪 v hv hfix R hRi hR
  have hTT : ∀ r ∈ R, W.Om r 1 v ∈ TT D (tor0 D ⊤ δ) a d := fun r _ => W.maps r 1 v hv
  have uniq : ∀ r₁ ∈ R, ∀ r₂ ∈ R, CongOne D 𝔪 (r₁⁻¹ * r₂) → r₁ = r₂ := fun r₁ h₁ r₂ h₂ hc =>
    (hR r₂ (hRi r₂ h₂)).unique ⟨h₁, hc⟩ ⟨h₂, by rw [inv_mul_cancel]; exact congOne_one⟩
  refine ⟨fun k hk => ?_, fun j k c hk hj => ?_⟩
  · rw [(Om_sum W k 1 R _ hTT).2]
    have e : ∀ r ∈ R, W.Om k 1 (W.Om r 1 v) = W.Om (k * r) 1 v := fun r _ => by
      rw [← W.mul k r 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e]
    refine sum_reindex W hv hfix hRi hR (fun r => k * r) (fun r hr => mul_mem hk (hRi r hr)) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm : s⁻¹ * (k * r₁) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem hk (hRi r₁ h₁))
      have h := congOne_mul (inv_mem hm) (congOne_inv hm c₁) c₂
      have e' : (s⁻¹ * (k * r₁))⁻¹ * (s⁻¹ * (k * r₂)) = r₁⁻¹ * r₂ := by group
      rw [e'] at h
      exact uniq r₁ h₁ r₂ h₂ h
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (k⁻¹ * s) (mul_mem (inv_mem hk) (hRi s hs))
      refine ⟨r, hr, ?_⟩
      have h := congOne_inv (mul_mem (inv_mem (hRi r hr)) (mul_mem (inv_mem hk) (hRi s hs))) hc
      have e' : (r⁻¹ * (k⁻¹ * s))⁻¹ = s⁻¹ * (k * r) := by group
      rwa [e'] at h
  · rw [(Om_sum W 1 j R _ hTT).2]
    have e : ∀ r ∈ R, W.Om 1 j (W.Om r 1 v) = c • W.Om (r * k) 1 v := fun r _ => by
      rw [← W.mul 1 r j 1 v hv, one_mul, mul_one,
        show W.Om r j v = W.Om (r * 1) (1 * j) v by rw [mul_one, one_mul], W.mul r 1 1 j v hv, hj,
        W.smul r 1 c _ (W.maps k 1 v hv), ← W.mul r k 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e, ← Finset.smul_sum]
    congr 1
    refine sum_reindex W hv hfix hRi hR (fun r => r * k) (fun r hr => mul_mem (hRi r hr) hk) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm₂ : s⁻¹ * (r₂ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₂ h₂) hk)
      have hm₁ : s⁻¹ * (r₁ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₁ h₁) hk)
      have h := congOne_conj (g := r₂⁻¹ * s) (mul_mem (inv_mem (hRi r₂ h₂)) (hRi s hs))
        (congOne_mul hm₁ c₁ (congOne_inv hm₂ c₂))
      have e' : r₂⁻¹ * s * (s⁻¹ * (r₁ * k) * (s⁻¹ * (r₂ * k))⁻¹) * (r₂⁻¹ * s)⁻¹ = r₂⁻¹ * r₁ := by group
      rw [e'] at h
      exact (uniq r₂ h₂ r₁ h₁ h).symm
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (s * k⁻¹) (mul_mem (hRi s hs) (inv_mem hk))
      refine ⟨r, hr, ?_⟩
      have hm : r⁻¹ * (s * k⁻¹) ∈ intG D a := mul_mem (inv_mem (hRi r hr)) (mul_mem (hRi s hs) (inv_mem hk))
      have h := congOne_conj (g := k⁻¹) (inv_mem hk) (congOne_inv hm hc)
      have e' : k⁻¹ * (r⁻¹ * (s * k⁻¹))⁻¹ * k⁻¹⁻¹ = s⁻¹ * (r * k) := by group
      rwa [e'] at h

end GlobalTheory.StdSumFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepOpIndefOne
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWOpCase

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF

def DefinitePlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ), 3 ≤ m → ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    ∃ ι : F →+* ℝ, Formalism.UG.IsDefiniteAt σ (l • JV) ι

def StepOpDefinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    ∀ ι : F →+* ℝ, Formalism.UG.IsDefiniteAt σ (l • JV) ι →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ Φ ∈ kfin σ om K,
  ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ W ≤ kfin σ om K ∧
  ∃ Φ' ∈ W, sec σ om Φ' = sec σ om Φ ∧ thetaI σ om ν 𝓕 Φ' = thetaI σ om ν 𝓕 Φ ∧
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ρ : Measure Ω) (y : Ω → UA σ J₂) (η : Ω → ℂ) (C : Set (UA σ J₂)),
    IsFiniteMeasure ρ ∧ Measurable y ∧ IsCompact C ∧ (∀ ω, y ω ∈ C) ∧ Integrable η ρ ∧
    (∀ D : UA σ J₂ → ℂ, Continuous D → (∀ γ ∈ ratU σ J₂, ∀ g, D (γ * g) = D g) → IsSing σ T D →
      ∀ g, ∫ ω, η ω * D (g * y ω) ∂ρ = 0) ∧
    ∃ L : ℂ → W →ₗ[ℂ] W, (∀ (Ψ : W) (f : Module.Dual ℂ W), Differentiable ℂ fun s => f (L s Ψ)) ∧
      Function.Bijective (L (((m : ℂ) - (n : ℂ)) / 2)) ∧
      (∀ (Ψ : W) (s : ℂ) (g : UA σ J₂), ∫ ω, η ω * flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om (Ψ : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s (g * y ω) ∂ρ =
        flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om ((L s Ψ : W) : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s g) ∧
      ∀ (Ψ : W) (g : UA σ J₂), ∫ ω, η ω * thetaI σ om ν 𝓕 (Ψ : (κ → AF F) → ℂ) (g * y ω) ∂ρ =
        thetaI σ om ν 𝓕 ((L (((m : ℂ) - (n : ℂ)) / 2) Ψ : W) : (κ → AF F) → ℂ) g

def StepOpIndefOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    n = 1 → (∀ ι : F →+* ℝ, ¬ Formalism.UG.IsDefiniteAt σ (l • JV) ι) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ Φ ∈ kfin σ om K,
  ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ W ≤ kfin σ om K ∧
  ∃ Φ' ∈ W, sec σ om Φ' = sec σ om Φ ∧ thetaI σ om ν 𝓕 Φ' = thetaI σ om ν 𝓕 Φ ∧
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ρ : Measure Ω) (y : Ω → UA σ J₂) (η : Ω → ℂ) (C : Set (UA σ J₂)),
    IsFiniteMeasure ρ ∧ Measurable y ∧ IsCompact C ∧ (∀ ω, y ω ∈ C) ∧ Integrable η ρ ∧
    (∀ D : UA σ J₂ → ℂ, Continuous D → (∀ γ ∈ ratU σ J₂, ∀ g, D (γ * g) = D g) → IsSing σ T D →
      ∀ g, ∫ ω, η ω * D (g * y ω) ∂ρ = 0) ∧
    ∃ L : ℂ → W →ₗ[ℂ] W, (∀ (Ψ : W) (f : Module.Dual ℂ W), Differentiable ℂ fun s => f (L s Ψ)) ∧
      Function.Bijective (L (((m : ℂ) - (n : ℂ)) / 2)) ∧
      (∀ (Ψ : W) (s : ℂ) (g : UA σ J₂), ∫ ω, η ω * flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om (Ψ : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s (g * y ω) ∂ρ =
        flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om ((L s Ψ : W) : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s g) ∧
      ∀ (Ψ : W) (g : UA σ J₂), ∫ ω, η ω * thetaI σ om ν 𝓕 (Ψ : (κ → AF F) → ℂ) (g * y ω) ∂ρ =
        thetaI σ om ν 𝓕 ((L (((m : ℂ) - (n : ℂ)) / 2) Ψ : W) : (κ → AF F) → ℂ) g

end GlobalTheory.SWOpCase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOverCosetRepresentativesEq
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.RepSum

theorem congOne_one {D : D7} {a : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} : CongOne D 𝔪 (1 : GA D a) := by
  intro i j
  simp

end GlobalTheory.FunObj.SqNum.RepSum

namespace GlobalTheory.FunObj.SqNum

end GlobalTheory.FunObj.SqNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPartOfPulledActionStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_part_of_pulled_action : ∀ (O : Type) [CommRing O] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω)) [GrpObj G'] (i' : OAct O G')
    (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u' : splitTorus (Sp Ω) X ⟶ G') (A : Over (Sp Ω)) [GrpObj A] (q' : G' ⟶ A) (j : OAct O A),
    IsAbelianScheme A → IsMonHom u' → IsKer u' q' → (∀ a, i'.act a ≫ q' = q' ≫ j.act a) →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∃ (G₀ : Over (Sp F)) (_ : GrpObj G₀) (i₀ : OAct O G₀) (φ₀ : G₀.left ⟶ G.left)
        (Y : Type) (_ : AddCommGroup Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y) (u₀ : splitTorus (Sp F) Y ⟶ G₀)
        (B : Over (Sp F)) (_ : GrpObj B) (q₀ : G₀ ⟶ B) (j₀ : OAct O B) (ψ : A.left ⟶ B.left),
        IsActPull i₀ i (spMap (algebraMap K F)) φ₀ ∧ IsAbelianScheme B ∧ IsMonHom u₀ ∧ IsKer u₀ q₀ ∧
        (∀ a, i₀.act a ≫ q₀ = q₀ ≫ j₀.act a) ∧ IsActPull j j₀ (spMap (algebraMap F Ω)) ψ := by
  first | exact @GlobalTheory.TorusPart.exists_finite_torusExtension_act | exact GlobalTheory.TorusPart.exists_finite_torusExtension_act | (intros; apply GlobalTheory.TorusPart.exists_finite_torusExtension_act <;> assumption)
end


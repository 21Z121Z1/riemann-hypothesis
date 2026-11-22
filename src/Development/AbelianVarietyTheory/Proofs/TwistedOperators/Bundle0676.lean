import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConnectionLinear
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem conAt_zero (hM : M.Is t) (Φ : SchDown G t) (h : Pts G) (j : ℕ) (hj : Even j) (hm : ¬ (Even D.R.m ∧ j + 2 ≤ D.R.m)) :
    conAt W hM Φ h j = 0 := by
  unfold conAt
  split_ifs with h1 h2
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h1]; simpa [Nat.even_add] using hj
  · exfalso; apply hm; refine ⟨?_, by omega⟩; rw [← h2]; obtain ⟨r, hr⟩ := hj; exact ⟨r + ((D.R.m - 4 - j) / 2 + 1) + 1, by omega⟩
  · exact dif_neg h2

theorem conAt_local (hM : M.Is t) (Φ Φ' : SchDown G t) (h : Pts G) (j : ℕ)
    (hΦ : ∀ a : Fin D.R.m, ((a : ℕ) = j ∨ (a : ℕ) = j + 1) → Φ a = Φ' a) : conAt W hM Φ h j = conAt W hM Φ' h j := by
  have key : ∀ (a : ℕ) (ha : a < D.R.m), (a = j ∨ a = j + 1) → Φ ⟨a, ha⟩ = Φ' ⟨a, ha⟩ := fun a ha e => hΦ ⟨a, ha⟩ e
  unfold conAt
  simp (disch := simp) only [key]

theorem sum_eq_zero_of_multilin {ι I : Type} [Fintype ι] [dI : DecidableEq ι] {Y : ι → Type} (V : ∀ j, Submodule ℂ (Y j → ℂ))
    (E : (∀ j, Y j → ℂ) → ℂ)
    (hE : ∀ Φ : ∀ j, Y j → ℂ, (∀ j, Φ j ∈ V j) → ∀ a (φ φ' : Y a → ℂ) (c : ℂ), φ ∈ V a → φ' ∈ V a →
      E (Function.update Φ a (c • φ + φ')) = c * E (Function.update Φ a φ) + E (Function.update Φ a φ'))
    (S : Finset I) (x : I → ℂ) (Φ : I → ∀ j, Y j → ℂ) (hΦ : ∀ i ∈ S, ∀ j, Φ i j ∈ V j)
    (h0 : ∀ v : ∀ j, Y j, ∑ i ∈ S, x i * ∏ j, Φ i j (v j) = 0) : ∑ i ∈ S, x i * E (Φ i) = 0 := by
  have coe_upd : ∀ (m : ∀ j, V j) (a : ι) (p : V a),
      (fun j => ((Function.update m a p j : V j) : Y j → ℂ)) = Function.update (fun j => (m j : Y j → ℂ)) a (p : Y a → ℂ) :=
    fun m a p => funext fun j => Function.apply_update (fun j (z : V j) => (z : Y j → ℂ)) m a p j
  let Mm : MultilinearMap ℂ (fun j => V j) ℂ :=
    { toFun := fun m => E fun j => (m j : Y j → ℂ)
      map_update_add' := by
        intro inst m a p q
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_add]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p q 1 p.2 q.2
        rw [one_smul, one_mul] at this
        exact this
      map_update_smul' := by
        intro inst m a c p
        obtain rfl : inst = dI := Subsingleton.elim _ _
        simp only [coe_upd, Submodule.coe_smul, smul_eq_mul]
        have := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a p 0 c p.2 (V a).zero_mem
        rw [add_zero] at this
        rw [this]
        have h00 := hE (fun j => (m j : Y j → ℂ)) (fun j => (m j).2) a 0 0 1 (V a).zero_mem (V a).zero_mem
        simp only [smul_zero, add_zero, one_mul] at h00
        have hz : E (Function.update (fun j => (m j : Y j → ℂ)) a 0) = 0 := by linear_combination -h00
        rw [hz, add_zero] }
  classical
  let φ : I → ∀ j, V j := fun i j => if hi : i ∈ S then ⟨Φ i j, hΦ i hi j⟩ else 0
  let τ : I →₀ ℂ := Finsupp.onFinset S (fun i => if i ∈ S then x i else 0) (fun i hi => by by_contra h; simp [h] at hi)
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V Mm τ 0 φ φ (fun z => by
    rw [Finsupp.sum_zero_index, Finsupp.onFinset_sum _ (fun _ => zero_mul _)]
    rw [← h0 z]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [φ, hi])
  rw [Finsupp.sum_zero_index] at key
  dsimp only [τ] at key
  rw [Finsupp.onFinset_sum _ (g := fun a c => c • Mm (φ a)) (fun _ => zero_smul _ _)] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [φ, hi, Mm]
end GlobalTheory.ConnectionLinear

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def PositionLinAt (j off : ℕ) : Prop :=
  ∀ t (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (Φ : SchDown ch.G t) (a : Fin D.R.m), (a : ℕ) = j + off →
    ∀ (φ φ' : Sch ch.G (.down t D.R.m a)) (c : ℂ), (∀ b, IsThetaFunO ch.W.ψ _ _ (Φ b)) → IsThetaFunO ch.W.ψ _ _ φ →
      IsThetaFunO ch.W.ψ _ _ φ' → ∀ u v,
      conAt ch.W hM (fockD ch.W t (Function.update Φ a (c • φ + φ')) P) h j u v =
        c * conAt ch.W hM (fockD ch.W t (Function.update Φ a φ) P) h j u v +
          conAt ch.W hM (fockD ch.W t (Function.update Φ a φ') P) h j u v

def ContrLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 < D.R.m → Even D.R.m → PositionLinAt ch j off

def LastLin (off : ℕ) : Prop := ∀ j, Even j → j + 2 = D.R.m → PositionLinAt ch j off

theorem conLin_of_positions (hC0 : ContrLin ch 0) (hC1 : ContrLin ch 1) (hL0 : LastLin ch 0) (hL1 : LastLin ch 1) :
    ConLin ch := by
  intro t M hM P h I S x f Φ hΦ h0 u y
  have intersection_update_fsHerm_neg_one : ∀ j off, Even j → off ≤ 1 → PositionLinAt ch j off := by
    intro j off hj ho
    by_cases hm : Even D.R.m ∧ j + 2 ≤ D.R.m
    · rcases Nat.lt_or_eq_of_le hm.2 with hlt | heq
      · interval_cases off
        · exact hC0 j hj hlt hm.1
        · exact hC1 j hj hlt hm.1
      · interval_cases off
        · exact hL0 j hj heq
        · exact hL1 j hj heq
    · intro t M hM P h Φ a _ φ φ' c _ _ _ u v
      simp only [conAt_zero ch.W hM _ h j hj hm, Pi.zero_apply, mul_zero, add_zero]
  let E : SchDown ch.G t → ℂ := fun Ψ => ∏ k ∈ Finset.range (D.R.m / 2),
    conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1))
  have hev : ∀ i, evT (conAt ch.W hM (fockD ch.W t (Φ i) P) h) (f i) u y = (∏ n, f i n (y n)) * E (Φ i) := fun i => by
    simp only [evT, E]; ring
  simp only [hev, ← mul_assoc]
  refine sum_eq_zero_of_multilin (fun j : Fin D.R.m => GlobalTheory.LastVertexInv.thSub ch.W (.mu t D.R.m (j : ℕ))) E ?_ S
    (fun i => x i * ∏ n, f i n (y n)) Φ (fun i hi j => hΦ i hi j) (fun v => ?_)
  · intro Ψ hΨ a φ φ' c hφ hφ'
    by_cases hm : Even D.R.m
    · have hk : (a : ℕ) / 2 ∈ Finset.range (D.R.m / 2) := by
        obtain ⟨r, hr⟩ := hm; have := a.2; rw [Finset.mem_range]; omega
      have hrest : ∀ ψ : Sch ch.G (.down t D.R.m a), ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) =
          ∏ k ∈ Finset.range (D.R.m / 2) \ {(a : ℕ) / 2},
          conAt ch.W hM (fockD ch.W t Ψ P) h (2 * k) (u (2 * k)) (u (2 * k + 1)) := by
        intro ψ
        refine Finset.prod_congr rfl fun k hk' => ?_
        have hk2 : k ≠ (a : ℕ) / 2 := by simpa using (Finset.mem_sdiff.1 hk').2
        rw [conAt_local ch.W hM (fockD ch.W t (Function.update Ψ a ψ) P) (fockD ch.W t Ψ P) h (2 * k) (fun b hb => ?_)]
        have hne : b ≠ a := fun e => by subst e; omega
        simp only [fockD, Function.update_of_ne hne]
      simp only [E]
      have hsplit := fun (g : ℕ → ℂ) => Finset.prod_eq_mul_prod_diff_singleton (s := Finset.range (D.R.m / 2)) ((a : ℕ) / 2) g (fun h' => absurd hk h')
      rw [hsplit, hsplit, hsplit, hrest, hrest, hrest]
      rw [intersection_update_fsHerm_neg_one (2 * ((a : ℕ) / 2)) ((a : ℕ) - 2 * ((a : ℕ) / 2)) (even_two_mul _) (by omega) t M hM P h Ψ a (by omega)
        φ φ' c hΨ hφ hφ']
      ring
    · have h0m : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; rw [Finset.mem_range]; omega
      have hz : ∀ Ψ' : SchDown ch.G t, E Ψ' = 0 := fun Ψ' => Finset.prod_eq_zero h0m (by
        rw [conAt_zero ch.W hM _ h (2 * 0) (even_two_mul 0) (fun e => hm e.1)]
        rfl)
      simp only [hz, mul_zero, add_zero]
  · rw [← h0 y v]
    exact Finset.sum_congr rfl fun i _ => by ring
end
end GlobalTheory.ConnectionLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_snd_one_sub_idemS :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) => sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) atTop (𝓝 0) := by
  classical
  have hin : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) w, w ∈ T → evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) = 0 := by
    intro T w hw
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) = 0
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS, if_pos hw, sub_self]
  have hint : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) w,
      evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) ∈ w.adicCompletionIntegers F := by
    intro T w
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) ∈ w.adicCompletionIntegers F
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS]
    split_ifs
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact one_mem _
  let A : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F) := fun w => w.adicCompletionIntegers F
  let o : ∀ w, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩
  let g : Finset (HeightOneSpectrum (𝓞 F)) → ∀ w, A w := fun T w => ⟨_, hint T w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({w} : Finset _)] with T hT
    exact Subtype.ext (hin T w (hT (Finset.mem_singleton_self w))).symm
  have h := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_infIdem : At (evI F) (pairA F 1 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * 1, u.2 * 0) = (0, 0)
  rw [h1, zero_mul, mul_zero]

theorem one_sub_idemS_eq (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) :
    1 - GlobalTheory.FinDecomp.idemS F T = pairA F 1 0 + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) := by
  have h := GlobalTheory.FinDecomp.fst_idemS (F := F) T
  refine Prod.ext ?_ ?_
  · change 1 - fstA F (GlobalTheory.FinDecomp.idemS F T) = 1 + 0
    rw [h, sub_zero, add_zero]
  · change sndA F (1 - GlobalTheory.FinDecomp.idemS F T) = 0 + sndA F (1 - GlobalTheory.FinDecomp.idemS F T)
    rw [zero_add]

theorem tendsto_cut :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) => pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_snd_one_sub_idemS (F := F))
  exact h

theorem tendsto_phi {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E)) (hM : pairA F 1 0 • (M - 1) = 0) :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) => GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M) atTop (𝓝 M) := by
  have key : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M =
      M + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) • (1 - M) := by
    intro T
    have h0 : pairA F 1 0 • (1 - M) = 0 := by rw [← neg_sub, smul_neg, hM, neg_zero]
    have h1 : GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M = M + (1 - GlobalTheory.FinDecomp.idemS F T) • (1 - M) := by
      simp only [GlobalTheory.FinDecomp.phi, sub_smul, smul_sub, one_smul]; abel
    rw [h1, congrArg (· • (1 - M)) (one_sub_idemS_eq T), add_smul, h0, zero_add]
  simp_rw [key]
  have h := (tendsto_const_nhds (x := M)).add ((tendsto_cut (F := F)).smul_const (1 - M))
  have e : M + (0 : AF F) • (1 - M) = M := by rw [zero_smul, add_zero]
  rw [e] at h
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

theorem tendsto_loc_idemS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J),
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K - 1) = 0) →
    Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idemS F T) (GlobalTheory.FinDecomp.idemS_mul_self T) K) Filter.atTop (nhds K) := by
  intro F E _ _ _ _ _ σ d J K hK
  have hM : pairA F 1 0 • (mat K - 1) = 0 := hK _ at_infIdem
  have hN : pairA F 1 0 • (mat K⁻¹ - 1) = 0 := by
    have h : mat K⁻¹ - 1 = mat K⁻¹ * (1 - mat K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, GlobalTheory.FinDecomp.mat_inv_mul]
    rw [h, ← Matrix.mul_smul, ← neg_sub (mat K), smul_neg, hM, neg_zero, Matrix.mul_zero]
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  change Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K),
        MulOpposite.op (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K⁻¹)))) atTop
      (𝓝 (mat K, MulOpposite.op (mat K⁻¹)))
  exact (tendsto_phi _ hM).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_phi _ hN))

end GlobalTheory.FinDecompLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSender
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.GridMeasDown

open GlobalTheory.GridJoin GlobalTheory.Grid

variable {D : D7}

theorem exch {V₁ V₂ : HSp D} (hV : SameSp V₂ V₁) (e : GA D V₁ = GA D V₂)
    {μ₁ : Measure (GA D V₁)} {F₁ : Set (GA D V₁)} {μ₂ : Measure (GA D V₂)} {F₂ : Set (GA D V₂)}
    (hμ : HEq μ₁ μ₂) (hH₂ : μ₂.IsHaarMeasure) (h1 : IsFundamentalDomain (GQ V₁) F₁ μ₁)
    (h2 : IsFundamentalDomain (GQ V₂) F₂ μ₂) (H : GA D V₂ → ℂ) (hH : ∀ γ ∈ GQ V₂, ∀ g, H (γ * g) = H g) :
    (IntegrableOn (fun g => H (cast e g)) F₁ μ₁ ↔ IntegrableOn H F₂ μ₂) ∧
      ∫ g in F₁, H (cast e g) ∂μ₁ = ∫ g in F₂, H g ∂μ₂ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl : μ₁ = μ₂ := eq_of_heq hμ
  exact GlobalTheory.FlipStart.Col.fund_exch (V := V₂) (μ := μ₁) h1 h2 H hH

theorem measFD_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  have h1 : Lev.IsMeasLevDef V₀ K μ := h.1
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h1 h₀.1)

theorem lev_heq {V V' : HSp D} (hsp : SameSp V V') {β : GL (Fin V'.rank) (Lev.EAf D)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hl : HEq Λ' Λ) (hf : Formalism.L2.DIV.IsFrame β Λ') :
    HEq (UA D.sp.cm V'.gram ⊓ St β) (GlobalTheory.ChiGrid.congLev D.sp.cm V.gram Λ ⊤) := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hsp
  obtain rfl := eq_of_heq hl
  have hs := Formalism.L2.DIV.stabilizer_eq_stabilizer_lattice _ _ _ _ _ hf
  have h2 := GlobalTheory.ChiGrid.congLev_top (hc := D.sp.cm) (J := V.gram) (Λ := Λ')
  apply heq_of_eq
  rw [h2, hs]
  rfl

theorem cast_heq {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) :
    HEq (Node.MeasDat.cast h m).ν m.ν ∧ HEq (Node.MeasDat.cast h m).fd m.fd := by
  subst h; exact ⟨HEq.rfl, HEq.rfl⟩

theorem cast_fd {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) (hf : IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    IsFundamentalDomain (GQ S'.V) (Node.MeasDat.cast h m).fd (Node.MeasDat.cast h m).ν := by
  subst h; exact hf

theorem meas_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F hS hc G' W hW G hG hJ M t hM i j hi hj e H hH
  have hAt := hM.vtx (.grid i (j + 1)) ⟨hi, by omega⟩
  obtain ⟨hHaar, hfd⟩ := hAt.haar_fund
  have hsp : SameSp (G'.V (.grid i (j + 1))) (G.V i (j + 1)).V := (hJ.1.vert i (j + 1) hi (by omega)).sp
  suffices key : HEq (G.meas t i (j + 1)).ν (M.ν (.grid i (j + 1))) ∧
      IsFundamentalDomain (GQ (G.V i (j + 1)).V) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν from
    exch hsp e key.1 hHaar key.2 hfd H hH
  unfold Vol.IsAt at hAt
  rcases i with _ | i
  · have hmod := hS.core.models
    by_cases h : j + 1 < D.R.m
    · have hT : G'.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh h)
      have hK : HEq (levJ G' t (.grid 0 (j + 1)))
          (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeY_eq_chainVertexAtRowZero_of_lt R h) ⟨R.νY t (j + 1), R.fdY t (j + 1)⟩ := by
        show meas0 R t j = _
        rw [meas0, dif_pos h]
      rw [e0]
      rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h' | h'
      · have hc := hmod.νY t (j + 1) h'
        rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measFD_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
      · have e1 : j + 1 = D.R.m - 1 := by omega
        have hc := hmod.νY' t
        rw [← e1] at hc
        rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
    · have hj' : j + 1 = D.R.m := by omega
      have hT : G'.V (.grid 0 (j + 1)) = D.sp.X' := by
        show (columnBlock R.toLevCh (j + 1)).sp = _
        rw [hj', colY_m]
      have hK : HEq (levJ G' t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) := levCol_top R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeX_eq_chainVertexAtRowZero_of_ge R h) ⟨R.νX t, R.fdX t⟩ := by
        show meas0 R t j = _
        rw [meas0, dif_neg h]
      rw [e0]
      have hc := hmod.νX t
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
  · have hN := hJ.1.vert (i + 1) (j + 1) hi (by omega)
    have hm := hG.meas.vert i j hi (by omega)
    obtain ⟨c, hfr⟩ := (hG.spaces.vert i (j + 1) hi (by omega)).frame
    have hK : HEq ((G.nV i (j + 1)).princ ⊤) (levJ G' t (.grid (i + 1) (j + 1))) := by
      rw [GlobalTheory.Grid.Node.princ_top]
      exact lev_heq hN.sp hN.lat hfr.1
    show HEq (G.mV i (j + 1)).ν _ ∧ IsFundamentalDomain (GQ (G.nV i (j + 1)).V) (G.mV i (j + 1)).fd (G.mV i (j + 1)).ν
    by_cases hd : D.R.m - 1 ≤ j + 1
    · have h1 := hm.1 hd
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hN.sp hK h1 hAt, h1.2⟩
    · have h1 := hm.2 hd
      rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hN.sp hK h1 hAt, h1.2⟩

end GlobalTheory.GridMeasDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DownKer

theorem kerA_down_left_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  intro D T L sc G W t i j hi hj Ψ hΨ h γ hγ g
  have hR : (Pair.mu t i j : Pair T).InRange D.R.m := ⟨hi, hj⟩
  have hw := W.om_is (.mu t i j) hR
  show (W.om (.mu t i j)) (h, γ * g) Ψ 0 = (W.om (.mu t i j)) (h, g) Ψ 0
  have e : ((h, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (h, g) := by
    simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hΨ)

end GlobalTheory.DownKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGrid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipDown

theorem kernel_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW G hG hM t i j hi hj eA eB Ψ hΨ
  obtain ⟨L1, a1, b1, e1⟩ := (hM.1.vert i j hi (by omega)).sp
  obtain ⟨L2, a2, b2, e2⟩ := (hM.1.vert i (j + 1) hi (by omega)).sp
  have hω := hM.2.omT t i j hi hj
  revert eA eB hω
  generalize (G.th t i j).ω = ω
  revert ω
  generalize (G.V i j).V = S at e1 ⊢
  generalize (G.V i (j + 1)).V = U at e2 ⊢
  subst e1 e2
  intro ω eA eB hω
  have hω' : ω = W.om (.mu t i j) := eq_of_heq hω
  subst hω'
  refine ⟨Ψ, ?_, fun h g => rfl⟩
  rw [← hW.ψ]
  exact ⟨hΨ.1, hΨ.2, hΨ.3, hΨ.4⟩

end GlobalTheory.FlipDown
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0738
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagCharacterPrimitiveRowTestMovedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem colMul_besDecAt (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (hjm : j < D.R.m) (i : Fin σ)
    (t : AE D) : colMul (besDecAt G j σ hj).jX i t = fun k => (incA D (D.host.xi0 ^ (i : ℕ)) * t) *
      incA D ((G.rowDec j hjm).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [colMul, HypDec.jX, rat, Matrix.map_apply, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id, map_mul]
  ring

theorem rowId_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p := by
  rw [rowId, tiltSc, if_neg hj, FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem primAt_rowN {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (G : GridData L sc) (j σ : ℕ)
    (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) : PrimAt ψ (besDecAt G j σ hj) (rowN G j) v := by
  have hjm : j < D.R.m := by omega
  have hodd : ¬ Odd j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  obtain ⟨-, f2, f3, -, f5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero

  set I : Fin σ → FI D := fun i => FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (i : ℕ))⁻¹ *
    stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) (Fin.castLE (by omega) i) with hIdef
  have hI0 : ∀ i, I i ≠ 0 := fun i => mul_ne_zero
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (inv_ne_zero (pow_ne_zero _ hξ))) (stairId_ne_zero _ _)
  have sub : ∀ (𝔞 : FI D) a, a ∈ idV 𝔞 v → a ∈ idAt D (· = v) := fun 𝔞 a ha => by
    have := (f3 𝔞 1 one_ne_zero a).1 (by rwa [FractionalIdeal.spanSingleton_one, one_mul])
    exact this.2
  have line : ∀ i (t : AE D), t ∈ idAt D (· = v) →
      (colMul (besDecAt G j σ hj).jX i t ∈ latV _ (rowN G j) (· = v) ↔ t ∈ idV (I i) v) := by
    intro i t ht
    rw [colMul_besDecAt G j σ hj hjm, rowN, dif_pos hjm,
      (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff (G.rowDec j hjm) (neg_ne_zero.2 one_ne_zero) _ _ _ v _).1, rowId_even hodd,
      hIdef, f3 _ _ (inv_ne_zero (pow_ne_zero _ hξ)), inv_inv]
    exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩
  intro i i' hii s hs
  have key : (∀ a : AE D, colMul (besDecAt G j σ hj).jX i' a ∈ latV _ (rowN G j) (· = v) →
      colMul (besDecAt G j σ hj).jX i (s * a) ∈ latV _ (rowN G j) (· = v)) ↔
      ∀ a ∈ idV (I i') v, s * a ∈ idV (I i) v := by
    constructor
    · intro h a ha
      have haA := sub _ a ha
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).1 (h a ((line i' a haA).2 ha))
    · intro h a hc
      have haA := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul _ hc
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).2 (h a ((line i' a haA).1 hc))
  have hratio : I i * (I i')⁻¹ = dI D := by
    have hst := stairId_succ (𝔞 := D.host.AA) (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (Fin.castLE (by omega) i : Fin (D.R.m - 1 - j))
      (Fin.castLE (by omega) i') (by simp only [Fin.val_castLE]; exact hii)
    have e : I i = dI D * I i' := by
      simp only [hIdef, dI, hst, hii]
      have e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 ^ (i : ℕ))⁻¹ =
          FractionalIdeal.spanSingleton _ D.host.xi0 * FractionalIdeal.spanSingleton _ (D.host.xi0 ^ ((i : ℕ) + 1))⁻¹ := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        congr 1
        rw [pow_succ, mul_inv, mul_comm (D.host.xi0 ^ (i : ℕ))⁻¹, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
      rw [e2]
      ring
    rw [e, mul_inv_cancel_right₀ (hI0 i')]
  rw [key, f2 _ _ (hI0 i') (hI0 i) s hs, hratio]
  exact f5 s hs

end GlobalTheory.RowShape

namespace GlobalTheory.RowShape

theorem big_primAt_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.PrimAt ch.W.ψ (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) v :=
  big_mono (fun ch h j σ hj v => primAt_rowN h ch.G j σ hj v) GlobalTheory.BigTop.Fun.OneSqTie.big_std

end GlobalTheory.RowShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantPartChosenPlacesMemCompletedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AnnPart

theorem idemSum_mul_conj {D : D7} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e₀ a : AE D} (he₀ : IsIdemSum e₀ P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (ha : Formalism.L2.NTheta.IsIdemAt a Q) : e₀ * cA D a = 0 := by
  obtain ⟨q0, q1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, d2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt ha
  have k : e₀ * a = a := by
    refine GlobalTheory.DepthFix.ext_cpt ?_ fun R => ?_
    · rw [RingHom.map_mul, q0, zero_mul, GlobalTheory.SplitScalar.infPart_splitIdem ha.1]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hR : R = Q
      · rw [hR, q1 _ hQ, one_mul]
      · rw [d2 R hR, mul_zero]
  rw [← k, RingHom.map_mul, ← mul_assoc, he₀.2, zero_mul]

theorem part_mem_latO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → e • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True := by
  intro D T L sc μ₀ hL G ψ hψ i hi e he w hw hinf
  obtain ⟨hS, hT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨-, hw2⟩ := hw
  have hmx : MxAt (fun _ => True) (e • w) := fun a b => by
    refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun v => (v.2 trivial).elim⟩
    have h0 : infPart D (w a b) = 0 := by simpa using congrFun (congrFun hinf a) b
    rw [RingHom.mem_ker, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, h0, mul_zero]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ _ _ _ _ hS hT (fun _ => True) (e • w) hmx).2 fun u hu => ?_
  rw [GlobalTheory.SplitScalar.symplO_smul]
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, Finset.sum_smul, ← GlobalTheory.LatVac.symplHom_apply, map_sum]
  refine Finset.sum_induction _ (fun z => ψ z = 1) (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, mul_one])
    (AddChar.map_zero_eq_one ψ) fun PP hPP => ?_
  rw [GlobalTheory.LatVac.symplHom_apply]
  have hsp := GlobalTheory.SplitScalar.isSplitIdem_conj (hes PP hPP).1
  have hmem : cA D (es PP) • u ∈ depLat G (.chi i 0) := by
    show _ ∧ _
    refine ⟨GlobalTheory.CosetRow.smul_mem_latO_idem _ _ hsp.1 hu, fun e₀ he₀ => ?_⟩
    rw [smul_smul, idemSum_mul_conj he₀ hPP (hes PP hPP), zero_smul]
    exact zero_mem _
  refine hw2 _ hsp _ hmem ?_
  rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hsp.1]

end GlobalTheory.AnnPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharComb

variable {D : D7}

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  exact Prod.ext (zero_mul _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem complId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : AE D} (hx : x ∈ complId 𝔞)
    (hy : y ∈ complId 𝔟) : x * y ∈ complId (𝔞 * 𝔟) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, b, hb, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]
      exact tmul_mem_complId (intAf_mul hα hβ) (FractionalIdeal.mul_mem_mul ha hb)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem infPart_of_mem {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    infPart D x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, a, -, rfl⟩ := hx
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] a = 0
    exact TensorProduct.zero_tmul _ _
  | zero => exact map_zero _
  | add x z _ _ hx hz => rw [RingHom.map_add, hx, hz, add_zero]
  | neg x _ hx => rw [RingHom.map_neg, hx, neg_zero]

def finId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (EAf D) :=
  (complId 𝔠).map (toEAf D).toAddMonoidHom

theorem finId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : EAf D} (hx : x ∈ finId 𝔞)
    (hy : y ∈ finId 𝔟) : x * y ∈ finId (𝔞 * 𝔟) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact ⟨x₀ * y₀, complId_mul hx₀ hy₀, map_mul (toEAf D) x₀ y₀⟩

theorem tmul_one_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {a : D.host.E} (ha : a ∈ 𝔠) :
    a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ finId 𝔠 :=
  ⟨_, tmul_mem_complId one_mem_intAf ha, rfl⟩

theorem int_mem_finId_one {z : EAf D} (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    z ∈ finId (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  induction hz using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨b, hb⟩ := b
      exact tmul_one_mem_finId ((FractionalIdeal.mem_one_iff _).2 hb)
    · exact ⟨_, tmul_mem_complId y.2 (FractionalIdeal.one_mem_one _), rfl⟩
  | zero => exact zero_mem _
  | one => exact tmul_one_mem_finId (FractionalIdeal.one_mem_one _)
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => simpa using finId_mul hx hy

theorem idS_mem_finId (𝔪 : Ideal (𝓞 D.host.E)) {t : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) ∈ finId ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe]
    exact tmul_one_mem_finId ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => rw [Subring.coe_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul]
    simpa using finId_mul (int_mem_finId_one c.2) hx

theorem idem_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {e : AE D} {Q : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e Q) {a : D.host.E} (ha : a ∈ 𝔠)
    (hv : Valued.v (algebraMap D.host.E (Kw Q) a) = 1) : toEAf D e ∈ finId 𝔠 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨h1, h2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt he
  have hu : toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q' => ?_
    rw [map_mul, GlobalTheory.FunObj.Comparison₂.cpt_tmul]
    by_cases hQ : Q' = Q
    · subst hQ
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q' hQ, zero_mul]
      exact zero_mem _
  have e1 : toEAf D e = (toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F))) *
      (a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha0, one_mul,
      Algebra.TensorProduct.one_def.symm, mul_one]
  rw [e1]
  simpa using finId_mul (int_mem_finId_one hu) (tmul_one_mem_finId ha)

theorem toEAf_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    toEAf D x ∈ finId 𝔠 := ⟨x, hx, rfl⟩

theorem ring_key {R : Type*} [CommRing R] (e c : R) : c = e * (e * c) + ((1 + e) * (1 - e)) * c := by ring

theorem mem_complId_of_finId {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : AE D} (hc : c ∈ complId 𝔞)
    (h : toEAf D c ∈ finId 𝔟) : c ∈ complId 𝔟 := by
  obtain ⟨z, hz, hze⟩ := h
  have hze' : toEAf D z = toEAf D c := hze
  have hzc : z = c := GlobalTheory.DepthFix.ext_cpt (by rw [infPart_of_mem hz, infPart_of_mem hc])
    fun Q => by rw [hze']
  exact hzc ▸ hz

theorem core {𝔞 𝔟 𝔪 𝔡 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hid : 𝔪 * 𝔡 = 𝔞 * 𝔟) {e c : EAf D}
    (he : e ∈ finId 𝔞) (hec : e * c ∈ finId 𝔟) (hm : (1 + e) * (1 - e) ∈ finId 𝔪) (hc : c ∈ finId 𝔡) :
    c ∈ finId (𝔞 * 𝔟) := by
  have h3 := finId_mul hm hc
  rw [hid] at h3
  have h4 := add_mem (finId_mul he hec) h3
  rwa [← ring_key e c] at h4

theorem ideal_key {M A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hM : M ≠ 0) :
    M * (A * (B * M⁻¹)) = A * B := by
  calc _ = A * B * (M * M⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hM, mul_one]

theorem mem_complId_AA_AAbar : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 →
    ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) →
    (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  classical
  intro D hq T L μ0 hL sc G c hc hec
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h1 := hec e he
  obtain ⟨-, heO, t, ht, hte⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0
    (fun Q => G.pl.depth sc (Q.under (𝓞 D.host.F))) he
  have hprod : (∏ Q ∈ G.pl.W0, Q.asIdeal ^ G.pl.depth sc (Q.under (𝓞 D.host.F))) = G.pl.modul sc := by
    unfold Places.W0 Places.modul
    rw [Finset.prod_image fun v hv v' hv' h =>
      (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
    exact Finset.prod_congr rfl fun v hv => by rw [G.pl.under_w hv]
  rw [hprod] at ht

  have heA : toEAf D e ∈ finId D.host.AA := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := id he
    rw [show toEAf D (∑ Q ∈ G.pl.W0, es Q) = ∑ Q ∈ G.pl.W0, toEAf D (es Q) from
      map_sum (toEAf D).toAddMonoidHom (fun Q => es Q) G.pl.W0]
    refine sum_mem fun Q hQ => ?_
    obtain ⟨a, ha, hv⟩ := GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hq hL G Q hQ
    exact idem_mem_finId (hes Q hQ) ha hv

  have ht2 : ((⟨1 + toEAf D e, add_mem (one_mem _) heO⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * t) ∈
      Formalism.L2.DIV.idS D.host.F (G.pl.modul sc) := Ideal.mul_mem_left _ _ ht
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hid : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
      (D.host.AA * G.pl.stAbar sc) = D.host.AA * D.host.AAbar := ideal_key hM
  have hm := idS_mem_finId _ ht2
  rw [Subring.coe_mul, hte] at hm
  have h1f := toEAf_mem_finId h1
  rw [RingHom.map_mul] at h1f
  exact mem_complId_of_finId hc (core hid heA h1f hm (toEAf_mem_finId hc))

end GlobalTheory.XCharComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthShift

open GlobalTheory.StdFrames (cpt mem_OA_iff comp_toAd toAd toAd_spec)
open scoped Pointwise

variable {D : D7}

theorem modul_mem_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {r : 𝓞 D.host.E}
    (hr : r ∈ G.modul) : (r : D.host.E) ∈ shiftId G := by
  have h0 : G.pl.modulBar sc ≠ ⊥ := by
    intro h
    apply G.pl.modul_ne_bot sc
    unfold Places.modulBar at h
    have := congrArg (fun J => D.host.conj⁻¹ • J) h
    simpa using this
  have h1 := FractionalIdeal.one_mem_inv_coe_ideal (K := D.host.E) h0
  have h2 : (r : D.host.E) ∈ ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hr
  simpa [shiftId] using FractionalIdeal.mul_mem_mul h2 h1

theorem smul_mem_idLat {n : ℕ} {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {r : 𝓞 D.host.E} (hr : (r : D.host.E) ∈ J)
    {t : Fin n → D.host.E} (ht : t ∈ idLat I Λ) : r • t ∈ idLat (I * J) Λ := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨s * r, FractionalIdeal.mul_mem_mul hs hr, y, hy, ?_⟩
    rw [mul_comm, mul_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

variable {S B : HSp D} {LS : Lat S} {LT LT' : Lat B}

theorem inc_smul_mem {r : 𝓞 D.host.E} (hr : ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) :
    incA D (r : D.host.E) • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, r • t, hr t ht, ?_⟩
    ext i j
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * ((r : D.host.E) * t i) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_eq_of_toEAf {b b' x : AE D} (h : toEAf D b = toEAf D b') (h0 : infPart D x = 0) : b * x = b' * x := by
  have h1 : infPart D ((b - b') * x) = 0 := ((infPart D).map_mul _ _).trans (by rw [h0, mul_zero])
  have h2 : toEAf D (b - b') = 0 := ((toEAf D).map_sub _ _).trans (sub_eq_zero.2 h)
  have h3 : toEAf D ((b - b') * x) = 0 := ((toEAf D).map_mul _ _).trans (by rw [h2, zero_mul])
  have h4 := (comp_toAd D).ext _ h1 ((congrArg (toAd D) h3).trans (toAd D).map_zero)
  exact sub_eq_zero.1 ((sub_mul b b' x).symm.trans h4)

theorem exists_lift_int (c : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ c' : AE D, toEAf D c' = c.1 ∧ finPart D c' ∈ intAE D := by
  obtain ⟨c', -, hc'⟩ := (comp_toAd D).surj (toAd D c.1)
  refine ⟨c', GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D) hc', ((comp_toAd D).int c').2 fun Q => ?_⟩
  rw [hc']
  exact (mem_OA_iff _).1 c.2 Q

set_option maxHeartbeats 800000 in

theorem smul_mem_of_idS {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : ∀ r ∈ 𝔪, ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F 𝔪) {b : AE D} (hb : toEAf D b = s.1) :
    b • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  have key : ∃ b' : AE D, toEAf D b' = s.1 ∧ b' • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
    clear hb
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨incA D (r : D.host.E), rfl, inc_smul_mem (h𝔪 r hr) hu⟩
    | zero => exact ⟨0, RingHom.map_zero _, by rw [zero_smul]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c, hc, hc'⟩ := hy
      exact ⟨a + c, by rw [RingHom.map_add, ha, hc, Subring.coe_add], by rw [add_smul]; exact add_mem ha' hc'⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c', hc, hc'⟩ := exists_lift_int c
      refine ⟨c' * a, ((toEAf D).map_mul c' a).trans (congrArg₂ (· * ·) hc ha), ?_⟩
      rw [mul_smul]
      exact GlobalTheory.LatticeStable.smul_mem_latO D S B _ _ _ _ hc' _ ha'
  obtain ⟨b', hb', hm⟩ := key
  have e : b • u = b' • u := Matrix.ext fun i j =>
    mul_eq_of_toEAf (hb.trans hb'.symm) (GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)).1
  rw [e]
  exact hm

theorem mem_latO_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  intro D hOff T L μ0 hL sc G S B LS I Λ₀ hS _ _ z hz ⟨e, he, hez⟩
  have h𝔪 : ∀ r ∈ G.modul, ∀ t ∈ idLat I Λ₀, r • t ∈ idLat (I * shiftId G) Λ₀ :=
    fun r hr t ht => smul_mem_idLat (modul_mem_shiftId G hr) ht
  have hle : G.modul • homLat LS (idLat I Λ₀) ≤ homLat LS (idLat (I * shiftId G) Λ₀) :=
    Submodule.smul_le.2 fun r hr x hx y hy => by
      rw [smul_mulVec]
      exact h𝔪 r hr _ (hx y hy)
  have h1 : e • z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) fun _ => True := by
    refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hOff hL G) (fun i j => ?_) ?_
    · change e * (e * z i j) = e * z i j
      rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
    · refine AddSubgroup.closure_mono ?_ hez
      rintro _ ⟨α, hα, x, hx, rfl⟩
      exact ⟨α, hα, x, hle hx, rfl⟩
  obtain ⟨-, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (mem_OA_iff _).2 fun Q => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
    by_cases hQ : Q ∈ G.pl.W0
    · rw [e1 Q hQ, sub_self]; exact zero_mem _
    · rw [e2 Q hQ, sub_zero]; exact one_mem _
  have hid : (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F G.modul := by
    refine (Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
    change Valued.v (cpt (D := D) w (toEAf D (1 - e))) ≤ _
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
    exact zero_le
  have h2 := smul_mem_of_idS (LS := LS) h𝔪 hz hid rfl
  have h3 := add_mem h1 h2
  rwa [← add_smul, add_sub_cancel, one_smul] at h3

end GlobalTheory.DepthShift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @GlobalTheory.WeilConv.weilConvergence | exact GlobalTheory.WeilConv.weilConvergence | (intros; apply GlobalTheory.WeilConv.weilConvergence <;> assumption)
end


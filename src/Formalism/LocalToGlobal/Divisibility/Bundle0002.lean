import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0037
import Formalism.LocalRingCardinality.FactDelDualNabla
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0003
import Formalism.LocalToGlobal.Divisibility.LinkDef
import Formalism.AdicCompletionExports.NonnegativeDivisors.Imports
import Formalism.SharpRestriction.Bundle0002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct

-- bundled from Formalism.LocalToGlobal.Divisibility.BrJoint
section
noncomputable section

namespace Formalism.L2.DIV.BrJ

open Formalism.BasicNotions Formalism.MainNotions

theorem branching_interlacing_pairs : PrimeDegreeVariant.Conclusion6 := by
  intro n N h lam sg hI
  exact _root_.gTLower_of Formalism.BasicNotions.factDelDualNabla n N h lam sg hI

variable {D : D7} {u : D.what₂.Word}

private theorem map_intCast_mem_delSq {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ delSq ℤ N lam) : MvPolynomial.map (Int.castRingHom ℂ) f ∈ delSq ℂ N lam := by
  unfold delSq Formalism.GradedWeylDivisibility.weyl at *
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨w, by rw [Formalism.UG.P.wlocal_map_applyWord, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

private theorem isBr_of_eqOn_delSq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br br' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hb : PrimeDegreeVariant.IsBr h lam sg br) (he : Set.EqOn br' br (delSq ℂ N lam : Set _)) :
    PrimeDegreeVariant.IsBr h lam sg br' := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  refine ⟨fun f hf => ?_, fun f hf => ?_, ?_, fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩
  · rw [he (map_intCast_mem_delSq lam f hf)]
    exact b1 f hf
  · rw [he hf]
    exact b2 f hf
  · obtain ⟨f, hf, hne⟩ := b3
    exact ⟨f, hf, by rw [he hf]; exact hne⟩
  · rw [he (PI.GTS.sqAct_mem_delSq N lam _ f hf), he hf]
    exact b4 g f hf
  · rw [he (PI.GTS.sqAct_mem_delSq N lam _ f hf), he hf]
    exact b5 a f hf
  · rw [he hf]
    exact b6 f hf

private theorem interlace_lamTr_sgTr (P : product_first_zeroth_parts.Pend D u) (τ : D.what₂.Tau) :
    PrimeDegreeVariant.Interlace (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) := by
  unfold PrimeDegreeVariant.Interlace product_first_zeroth_parts.lamTr product_first_zeroth_parts.sgTr
  simp only [product_first_zeroth_parts.wSh, sub_le_sub_iff_right]
  exact fun i => P.interlace τ i

private theorem isBr_and_isTranspose_lamTr_sgTr (h : ∀ τ : D.what₂.Tau, PrimeDegreeVariant.Interlace (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ))
    (τ : D.what₂.Tau) : ∃ io br, PrimeDegreeVariant.IsIota (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io ∧
      PrimeDegreeVariant.IsBr (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) br ∧
      PrimeDegreeVariant.IsTranspose (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io br := by
  have hB := branching_interlacing_pairs _ _ (product_first_zeroth_parts.Nm_succ D.R) _ _ (h τ)
  unfold PrimeDegreeVariant.Branch at hB
  exact hB.2.2.2.2

theorem archimedean_signature_matching_of_brTie (P : product_first_zeroth_parts.Pend D u) (tie : J.BrTie P) : product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro τ
  obtain ⟨io0, br0, hio, hbr, htr⟩ := isBr_and_isTranspose_lamTr_sgTr (interlace_lamTr_sgTr P) τ
  exact isBr_of_eqOn_delSq _ _ _ _ _ hbr (tie τ io0 br0 hio hbr htr)

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.DIV.BrJ
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.LinkDefN
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions Formalism.AdicCompletionExports.NonnegativeDivisors

section Rec

variable {D : D7}

theorem zero_le_logWeight (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP Formalism.BasicNotions.lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem Nc_nonneg_rec (L : SizeData₂ D) : 0 ≤ L.Nc := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have h1 := Real.rpow_pos_of_pos hx L.sc.eps
  have h2 := Real.rpow_pos_of_pos hx (-L.sc.eps)
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  refine div_nonneg ?_ (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) h2.le))
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le) h1.le

def rowSize (L : SizeData₂ D) (C : ℝ) : ℝ := (C + 1) * L.sc.x ^ L.sc.eps * (L.B0 + L.Nc)

def SubspaceRankAt (L : SizeData₂ D) : Prop := ∀ j ∈ SizeData₂.lifts D, L.dZ0 j = D.what₂.D0

def TieTwRec (L : SizeData₂ D) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop :=
  ∀ y ∈ Tw, D.plEq.symm y ∈ L.supp ∧ D.what₂.muAt (D.plEq.symm y) ≠ D.what₂.mu0

def TieTwMu (D : D7) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop :=
  ∀ y ∈ Tw, D.what₂.muAt (D.plEq.symm y) ≠ D.what₂.mu0

end Rec

section Ties

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  (F : DefFam D.what₂.LL G Pl0 T (Fin D.R.m)) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub F.amb)
  (μ : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (Tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))

def liftRec : Fin D.R.m → ℕ := fun j => j.val + 1

def TieEtaN {M : Formalism.L2.MtFam D} (Tn : Formalism.L2.NormalizedLocalCompatibility D M) : Prop :=
  ∀ y ∈ Tw, ∀ j : Fin D.R.m, F.etaJ P ψ Zs j (μ y) y = Formalism.L2.etaN Tn (j.val + 1) (D.plEq.symm y)

def RowCountEqDimension : Prop := D.what₂.D0 = (F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0)

end Ties

theorem log_sq_le_rpow_eventually {e : ℝ} (he : 0 < e) : ∃ X : ℝ, ∀ x ≥ X, Real.log x ^ 2 ≤ x ^ e := by
  have h := (isLittleO_log_rpow_atTop (half_pos he)).bound one_pos
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h1 := hX x (le_trans (le_max_left _ _) hx)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hp : 0 ≤ x ^ (e / 2) := Real.rpow_nonneg (by linarith) _
  rw [abs_of_nonneg hl, abs_of_nonneg hp] at h1
  calc Real.log x ^ 2 ≤ (x ^ (e / 2)) ^ 2 := pow_le_pow_left₀ hl h1 2
    _ = x ^ e := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num

theorem subspace_rank_at_of_family {eps : ℝ} (Fm : FamP eps) (h : SmallLevelRankEq Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SubspaceRankAt (Fm.L x i) := h

section Inputs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure DivInputsDefN (A : FamIn K G Pl0 T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)) (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (C CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A.fam.base.J Pl) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (bd : A.fam.base.J → ℝ) where

  Nu_lat : Submodule.IsLattice K Nu

  sg_fin : (Function.support (shiftZ sg)).Finite

  Xc_unit : ∀ v, IsUnit ((Dc Pk.Zs).Xc u v).det

  a_pos : 0 < (Dc Pk.Zs).a u

  X0 : InfinitePlace K → Matrix (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0))
    (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0)) ℂ

  base_matrix_det_unit : ∀ v, IsUnit (X0 v).det ∧
    ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((A.side P1 ψ1 Pk.Zs).HV A.fam.base.μ0).map v.embedding

  ch : ColChain (Dc Pk.Zs) u

  hn : HtNums R (InfinitePlace K)

  nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
    (Pi.basisFun K (Fin ((A.side P1 ψ1 Pk.Zs).nV A.fam.base.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤
      Real.exp hn.hPn

  cb : CBData ch.X ch.Kj

  nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v

  eig6 : ∑ j, R.hX j ≤ ∑ j, ((Zsc Pk.Zs).num C CH).l6 j

  h11 : LiftExponentAtTwisted A P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw (Zsc Pk.Zs).J0

  dg : ℕ

  dg_pos : 0 < dg

  dg_dvd : ∀ j t, (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dg

  hG0 : Real.log (Fintype.card G) ≤ R.lam0

  El3 : ℝ

  L3main : ∑ j, ((Zsc Pk.Zs).num C CH).l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3

  errB : El3 + lgDef R s + (∑ j, (((Zsc Pk.Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤ R.errB

  Q : ℝ

  de0 : 0 ≤ ((Zsc Pk.Zs).num C CH).de

  deQ : 3 * ((Zsc Pk.Zs).num C CH).de * Q ≤ 1

  Q1 : 1 ≤ Q

  Qb : boundB Pk.core (lgDef R s) 1 (etaSumBound bd dg s) + ((Zsc Pk.Zs).num C CH).hh + 28 * ((Zsc Pk.Zs).num C CH).la ≤ Q

  la_le : ((Zsc Pk.Zs).num C CH).la ≤ R.lam0

  constant_ge_twenty_eight : 28 ≤ R.C0

variable {A : FamIn K G Pl0 T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {C CH : ℝ} {Pk : IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A.fam.base.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} {bd : A.fam.base.J → ℝ}

def DivInputsDefN.toDef (I : DivInputsDefN A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg bd)
    (hN : InEta A.fam P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw bd) :
    DivInputsDef A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg :=
  { I with bd := bd, hN := hN }

theorem DivInputsDefN.toDef_bd (I : DivInputsDefN A s P0 ψ0 P1 ψ1 Dc Sp Zsc C CH Pk R u Nu sg bd)
    (hN : InEta A.fam P0 ψ0 Pk.Zs Pk.core.base.μ Pk.core.base.Tw bd) : (I.toDef hN).bd = bd := rfl

end Inputs

end Formalism.L2.DIV
end
end


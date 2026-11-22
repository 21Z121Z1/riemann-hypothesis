import Formalism.LocalToGlobal.Columns.WmpNatCardQuotEqPowFinrank
import Formalism.LocalToGlobal.Columns.NonDeg
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Columns.Bundle0012
import Mathlib
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.LocalToGlobal.Columns.BzdConjTTranspose
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.Columns.Bundle0019
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0003

-- bundled from Formalism.LocalToGlobal.Columns.AnisotropicOfPositiveDefinite
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Adj

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def conjugateSplitOff {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0) : SplitOff S0 :=
  ⟨conjPrime₂ P.1, by
    obtain ⟨h1, h2, h3⟩ := P.2
    refine ⟨?_, ?_, ?_⟩
    · rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime]
      intro e
      exact h1 (by rw [conjIdeal_asIdeal, e])
    · intro hm
      exact h3 _ hm (conjIdeal_asIdeal P.1).symm
    · intro Q hQ e
      rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime] at e
      have hQP : Q = P.1 := HeightOneSpectrum.ext e
      exact h2 (hQP ▸ hQ)⟩

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem mem_neighbour_iff_conj (c : DecoPts S E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (i : ℕ) (d d' : S.D) :
    d ∈ c.nb P.asIdeal i d' ↔ d' ∈ c.nb (conjPrime₂ P).asIdeal i d := by
  rw [c.mem_nb, c.mem_nb, DecoSet.mem_heckeNb P.ne_bot (conjIdeal_ne_bot P.ne_bot),
    DecoSet.mem_heckeNb (conjPrime₂ P).ne_bot (conjIdeal_ne_bot (conjPrime₂ P).ne_bot)]
  constructor
  · rintro ⟨hn, hf, hb⟩
    exact ⟨wmp_isHeckeNbr_symm (c.pts d').2.lat (c.pts d).2.lat (c.pts d').2.uni (c.pts d).2.uni hn, hf.symm, hb.symm⟩
  · rintro ⟨hn, hf, hb⟩
    have h' := wmp_isHeckeNbr_symm (c.pts d).2.lat (c.pts d').2.lat (c.pts d).2.uni (c.pts d').2.uni hn
    rw [conjugatePrime_conjugatePrime] at h'
    exact ⟨h', hf.symm, hb.symm⟩

theorem neighbour_smul_iff (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) (g : S.G) (d' d : S.D) :
    g • d ∈ c.nb P i (g • d') ↔ d ∈ c.nb P i d' := by
  rw [c.mem_nb, c.mem_nb, c.pts_smul, c.pts_smul]
  exact DecoSet.smul_mem_heckeNb_iff (c.hom g)

theorem heckeOperator_adjoint_conj (c : DecoPts S E n ST SG) (h : S.Ok) (P : HeightOneSpectrum (𝓞 E)) (i : ℕ) (φ ψ : S.EqFun) :
    S.ip h ((heckeD c P.asIdeal i).op φ) ψ = S.ip h φ ((heckeD c (conjPrime₂ P).asIdeal i).op ψ) := by
  have key := LocOp.ofNbr_adjoint (S := S) (S' := S) h h (MulEquiv.refl S.G) (c.nb P.asIdeal i)
    (c.nb (conjPrime₂ P).asIdeal i) LinearMap.id LinearMap.id (fun g d' d => neighbour_smul_iff c _ i g d' d) (fun _ _ => rfl)
    (fun g d d' => neighbour_smul_iff c _ i g d d') (fun _ _ => rfl) (fun d d' => mem_neighbour_iff_conj c P i d d') Iff.rfl
    (fun _ _ => rfl) S.outSec S.outSec φ ψ
  exact key

end Adj

section Aniso

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Aniso

section ThZero

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ThZero

section Final2

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Final2

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.FactorialSumLePowMulProd
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def extQ (lam : DomWeight n) : ℚ := Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n lam) (extremal ℚ n lam)

def supS : Finset ((Unit × Fin n × Fin n) →₀ ℕ) :=
  Finset.univ.biUnion fun i : VVIdx (oneW lam) => (bVVfun K (oneW lam) i).support

end Std

section Std2

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def wS (m : (Unit × Fin n × Fin n) →₀ ℕ) : ℝ := (mfact m : ℝ) / (extQ lam : ℝ)

end Std2

theorem factorial_sum_le_pow_mul_prod {k : ℕ} (a : Fin k → ℕ) : (∑ i, a i).factorial ≤ k ^ (∑ i, a i) * ∏ i, (a i).factorial := by
  have h1 := Nat.multinomial_spec Finset.univ a
  have h2 := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin k)) (fun _ => (1 : ℕ)) (∑ i, a i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow, Finset.prod_const_one,
    Nat.cast_id] at h2
  have h3 : Nat.multinomial Finset.univ a ≤ k ^ (∑ i, a i) := by
    rw [h2]
    exact Finset.single_le_sum (f := fun b => Nat.multinomial Finset.univ b) (fun _ _ => Nat.zero_le _)
      (Finset.mem_piAntidiag.2 ⟨rfl, fun i _ => Finset.mem_univ i⟩)
  calc (∑ i, a i).factorial = (∏ i, (a i).factorial) * Nat.multinomial Finset.univ a := h1.symm
    _ ≤ (∏ i, (a i).factorial) * k ^ (∑ i, a i) := Nat.mul_le_mul_left _ h3
    _ = _ := mul_comm _ _

section Deg

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Deg

def HwNormBound : Prop :=
  ∀ (κ : ℕ) (ν : Fin (κ + 1) → ℕ), Antitone ν →
    Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl (κ + 1)) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl (κ + 1)) ν) ≤
      ((∏ i, (ν i).factorial : ℕ) : ℚ) * ((ν 0 + κ + 1 : ℕ) : ℚ) ^ ((κ + 1) * κ / 2)

theorem natural_weight_cast_eq {κ : ℕ} (lam : DomWeight (κ + 1)) (i : Fin (κ + 1)) :
    ((lam.natW i : ℕ) : ℤ) = plus (castW rfl lam) i := by
  have hds : lam.detShift = lam.w (Fin.last κ) := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos κ)]
    congr 1
  have hle : lam.w (Fin.last κ) ≤ lam.w i := lam.anti (Fin.le_last i)
  simp only [DomWeight.natW, plus, castW, Fin.cast_eq_self, hds]
  rw [Int.toNat_of_nonneg (by linarith)]

theorem natural_weight_antitone {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := fun a b hab => by
  show (lam.w b - lam.detShift).toNat ≤ (lam.w a - lam.detShift).toNat
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hab) _)

theorem triangular_number_cast (κ : ℕ) : (((κ + 1) * κ / 2 : ℕ) : ℝ) = ((κ : ℝ) + 1) * (κ : ℝ) / 2 := by
  have h2 : 2 ∣ (κ + 1) * κ := by
    rw [mul_comm]
    exact (Nat.even_mul_succ_self κ).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  push_cast
  ring

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_Pv_max (v : (D.mem u).A.vT) : (A.Pv v).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)

def AtTSeen : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then A.Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v)))

variable (D u) in

def AtTDisc : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((CH.Ld D u i c ⧸ (D.clsLat u i c).comap (CH.Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))

set_option maxHeartbeats 4000000 in

structure AtTMoves where

  upG : ∀ i v (c : (D.mem u).C.cls i), CH.Ld D u i c → CH.GX D i

  up_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : CH.Ld D u i c), (D.fm u).fv i v c (hxPr A P i v c y) = 1 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : ((D.mem u).A.T : D.host.E) • (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → CH.GX D i

  dn_tie : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (CH.Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Lk D u (A.Pv v) i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = g (hxPrk A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → CH.GX D i

  dil_tie : ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.HermitianLatticesTheory.gmap (dilG i v a c).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))

set_option maxHeartbeats 4000000 in

structure AtTXp where

  lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V

  levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0)

  clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂

  z0 : (D.sp.X D.R.m).V
  cocycle_zero_mem_invariants : z0 ∈ Submodule.span D.host.E {D.sp.z}
  hermitianForm_lastCoordinateUniformizerVector_self : (D.sp.X D.R.m).hT z0 z0 = ((D.mem u).A.T : D.host.E)
  tilG : (D.fm u).clsP → CH.GX D D.R.m

  til_tie : ∀ c : (D.fm u).clsP,
    Formalism.HermitianLatticesTheory.gmap (tilG c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} ∧
    ∀ v (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E),
      (a : D.host.E) = (D.sp.X D.R.m).hT z0 ((tilG c).1 (z : (D.sp.X D.R.m).V)) →
      (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a

set_option maxHeartbeats 4000000 in

def atTOf (eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal))
    (hF : ∀ v (a : 𝓞 D.host.F), eF v (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a)
    (hs : AtTSeen A) (hd : AtTDisc D u) (M : AtTMoves A P) (Xp : AtTXp A P) : CH.AtT D u A.eV eF where
  piU := A.piU
  piU_K := A.piU_K
  piU_norm := A.piU_norm
  piU_cong := A.piU_cong
  Pv := A.Pv
  Pv_max := hx_Pv_max A
  Pv_pi := A.res_pi
  Pv_over := fun v => Ideal.ext fun x => ((A.res_v v x).symm)
  res := A.res
  res_surj := A.res_surj
  res_ker := fun _ => rfl
  res_F := hF
  seen := hs
  disc := hd
  pr := hxPr A P
  pr_surj := hxPr_surj A P
  pr_smul := hxPr_smul A P
  pr_ker := hxPr_ker A P
  fv_ker := hx_fv_ker A P
  prk := hxPrk A P
  prk_surj := hxPrk_surj A P
  prk_smul := hxPrk_smul A P
  prk_ker := hxPrk_ker A P
  te_tie := hx_te A P
  upG := M.upG
  up_tie := M.up_tie
  dnG := M.dnG
  dn_tie := M.dn_tie
  dilG := M.dilG
  dil_tie := M.dil_tie
  lattice₂ := Xp.lattice₂
  levP := Xp.levP
  clsP := Xp.clsP
  z0 := Xp.z0
  cocycle_zero_mem_invariants := Xp.cocycle_zero_mem_invariants
  hermitianForm_lastCoordinateUniformizerVector_self := Xp.hermitianForm_lastCoordinateUniformizerVector_self
  tilG := Xp.tilG
  til_tie := Xp.til_tie

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MaxSlopeOrthogonalNegLog
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section F3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem majorant_conj_symm (A : HLat K) (v : InfinitePlace K) (x y : A.V) :
    majAt A.b A.X v y x = star (majAt A.b A.X v x y) := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]

variable [IsTotallyComplex K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem slope_line_le_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : c ^ (nPl K) ≤ ht b X L := by
    rw [hL, hg]
    have h1 : ∀ v : InfinitePlace K, c ≤ (gramPl b X v (fun _ : Fin 1 => x)).det.re := by
      intro v
      rw [Matrix.det_fin_one]
      simp only [gramPl, Matrix.of_apply]
      rw [Formalism.ExtensionFiltration.majAt_self_re]
      exact hn v
    calc c ^ (nPl K) = ∏ _v : InfinitePlace K, c := by rw [Finset.prod_const, Finset.card_univ]; rfl
      _ ≤ ∏ v, (gramPl b X v (fun _ : Fin 1 => x)).det.re := Finset.prod_le_prod (fun v _ => hc.le) (fun v _ => h1 v)
  have hlog : (nPl K : ℝ) * Real.log c ≤ Real.log (ht b X L) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hht
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk]
  have : Real.log c / 2 ≤ (1 : ℝ) / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem max_slope_line_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muMaxDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  have : Module.Finite K V := Module.Finite.of_basis b
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le b X hL0 fun Q hQ hQ0 => ?_
  have h1 : rkK (K := K) Q ≤ 1 := by
    rw [← hrk]
    exact Submodule.finrank_mono (Submodule.span_mono hQ)
  have h2 : 0 < rkK (K := K) Q := Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hrkQ : rkK (K := K) Q = rkK (K := K) L := by omega
  have hi := (Formalism.LFunctionChainParameters.LLcv.index_slope_formula K V ι b X hX L Q hLfg hQ hQ0 hrkQ).1
  have hl : 0 ≤ Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
  have hn' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : 0 ≤ 2 * Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
    rw [hrk]
    positivity
  have := slope_line_le_neg_log b X hX x hx c hc hn
  rw [hi]
  linarith

end F3

section F3b

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem max_slope_orthogonal_neg_log (A : HLat K) (hA : FrameOK A) {γ : Type} [Fintype γ] [Nonempty γ] (e : γ → A.V) (he : ∀ c, e c ≠ 0)
    (horth : ∀ c c', c ≠ c' → ∀ v, majAt A.b A.X v (e c) (e c') = 0) (c0 : ℝ) (hc0 : 0 < c0)
    (hn : ∀ c v, c0 ≤ normAt A.b A.X v (e c) ^ 2) :
    muMaxDef A.b A.X (⨆ c, Submodule.span (𝓞 K) ({e c} : Set A.V)) ≤ -Real.log c0 := by
  classical
  set N : γ → Submodule (𝓞 K) A.V := fun c => Submodule.span (𝓞 K) ({e c} : Set A.V) with hN
  have hfg : ∀ c, (N c).FG := fun c => Submodule.fg_span (Set.finite_singleton _)
  have hne : ∀ c, N c ≠ ⊥ := fun c h => he c ((Submodule.span_singleton_eq_bot).1 h)
  have ho : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0 := by
    intro c c' hcc x hx y hy v
    have h1 : N c ≤ brzo_perp A (e c') :=
      (Submodule.span_singleton_le_iff_mem _ _).2 fun v => horth c' c (Ne.symm hcc) v
    have h2 : e c' ∈ brzo_perp A x := fun v => by
      rw [majorant_conj_symm A v (e c') x, h1 hx v, star_zero]
    exact ((Submodule.span_singleton_le_iff_mem _ _).2 h2) hy v
  obtain ⟨-, h2⟩ := hlat_orth_fin N hA hfg hne ho Finset.univ
  have hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c := by simp
  rw [hsup]
  have hb := (h2 Finset.univ_nonempty).2 ((-Real.log c0 + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2) fun c _ => by
    have := max_slope_line_neg_log A.b A.X hA (e c) (he c) c0 hc0 (hn c)
    unfold muMaxDef at this
    linarith
  unfold muMaxDef
  linarith

end F3b

end Formalism.L2.Col
end
end


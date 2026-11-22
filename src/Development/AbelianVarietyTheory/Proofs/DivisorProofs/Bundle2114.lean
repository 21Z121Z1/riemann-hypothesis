import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

section Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure TwLev (R : RealDat D A Ks) (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E))
    (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop where
  xi : ChrEq xi χ
  xi_fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  xi_triv : χ.TrivOn D.host.F
  xi_tame : ∀ v, χ.TameAt v
  Q_pl : IsTwistPlaces D.host.g Q
  Q_off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
    ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  Q_de : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
      ∀ PP ∈ Q, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭
  Q_ram : ∀ PP, ¬ χ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP
  xiR : ∀ PP ∈ Q, IsRes χ PP (xiR PP)
  roots : ∀ PP ∈ Q, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  muVal : ∀ (i : Fin D.R.m) (P : Pl0), Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (Q : Set (Pl D.host.E))) →
    ∃ a : D.what₂.LLˣ, D.what₂.embLL (a : D.what₂.LL) = (((R.C.mu0 i * χ).val (R.pl P) : ℂˣ) : ℂ)
  half : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  guard : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

theorem twLev_of_core {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) (t : T0) :
    TwLev R (R.xiH t) (R.xi t) (R.Q t) (R.xiR t) where
  xi := hC.lev.xi t
  xi_fin := hC.lev.xi_fin t
  xi_triv := hC.lev.xi_triv t
  xi_tame := hC.lev.xi_tame t
  Q_pl := hC.lev.Q_pl t
  Q_off := hC.lev.Q_off t
  Q_de p hp := by
    obtain ⟨𝔭, h𝔭⟩ := hC.lev.Q_de p hp
    exact ⟨𝔭, h𝔭, h𝔭 t⟩
  Q_ram := hC.lev.Q_ram t
  xiR := hC.lev.xiR t
  roots PP hPP := hC.fam.roots t PP (Or.inr hPP)
  muVal i P hP := by
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    exact ⟨A.muVal i t P, hC.fam.muVal i t P ((ht.ok t P).2 hP)⟩
  half := hG.1 t
  guard := hG.2 t

end Lev

section Laws

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def Laws (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ Finite T0 ∧ Nonempty (FWTie T R κ v₀) ∧ IoExt R ∧ QGuard R ∧ OMPins T R κ v₀ O j ∧ PhaseTie T R κ v₀ O ph j ∧
    BaseOf R j B

def Ext (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (j : Fin D.R.m)
    {T0' : Type} {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} (R' : RealDat D A' T.Q.c.F)
    (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)) : Prop :=
  (∀ τ, FixBase T R j τ → FixBase T R' j τ) ∧
    (∀ τ ζ Φ Φ', ConjFun (O' j) (κ j) τ ζ Φ Φ' → ConjFun (O j) (κ j) τ ζ Φ Φ') ∧
    (∀ (c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W) (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ), ExtC R j (inC (O j).c') (O j).c0' c →
      (∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) →
      ∃ (c' : VsV D j ℂ →ₗ[ℂ] (R'.cV j).W) (u' : ∀ ρ, lowT (R'.MW j (sg0 D A')) ρ), ExtC R' j (inC (O' j).c') (O' j).c0' c' ∧
        (∀ ρ, (u' ρ : (R'.MW j (sg0 D A')).sm ρ) = v₀' j (sg0 D A') ρ) ∧
        ∀ x, R'.ioP j (PiTensorProduct.tprod ℂ u') (c' x) = R.ioP j (PiTensorProduct.tprod ℂ u) (c x))

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}

theorem Ext.refl : Ext T R κ v₀ O j R v₀ O :=
  ⟨fun _ h => h, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩

theorem Ext.trans {T1 T2 : Type} {A1 : FamIn D.what₂.LL G Pl0 T1 D.R.m} {A2 : FamIn D.what₂.LL G Pl0 T2 D.R.m}
    {R1 : RealDat D A1 T.Q.c.F} {R2 : RealDat D A2 T.Q.c.F} {v1 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R1.MW i σ).Vec}
    {v2 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R2.MW i σ).Vec} {O1 : ∀ i, OMDat T.toCore R1 i Unit (fun _ => A1.μ0)}
    {O2 : ∀ i, OMDat T.toCore R2 i Unit (fun _ => A2.μ0)} (h1 : Ext T R κ v₀ O j R1 v1 O1) (h2 : Ext T R1 κ v1 O1 j R2 v2 O2) :
    Ext T R κ v₀ O j R2 v2 O2 := by
  refine ⟨fun τ h => h2.1 τ (h1.1 τ h), fun τ ζ Φ Φ' h => h1.2.1 τ ζ Φ Φ' (h2.2.1 τ ζ Φ Φ' h), fun c u hc hu => ?_⟩
  obtain ⟨c1, u1, hc1, hu1, e1⟩ := h1.2.2 c u hc hu
  obtain ⟨c2, u2, hc2, hu2, e2⟩ := h2.2.2 c1 u1 hc1 hu1
  exact ⟨c2, u2, hc2, hu2, fun x => (e2 x).trans (e1 x)⟩

theorem hasTuples_of_laws {ph : Fin D.R.m → ℂ} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle} {T0' : Type}
    {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} {R' : RealDat D A' T.Q.c.F} {F' : Face D A'}
    {v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec} {O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)}
    (hL : Laws T R' F' κ v₀' O' ph j B) (hE : Ext T R κ v₀ O j R' v₀' O') {t t' : T0'} (ht : IsTupOf R' B ψ t)
    (ht' : IsTupOf R' B ψ' t') : HasTuples T R κ v₀ O ph j B ψ ψ' :=
  ⟨T0', A', R', F', v₀', O', hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.1, hL.2.2.2.2.2.1, hL.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2,
    hE.1, hE.2.1, hE.2.2, t, t', ht, ht'⟩

end Laws

section Point

open Classical in

def TwLevAt : Prop := AtTw fun Fm x hx i p w j => ∀ ρ ρ' : Setup (Fm.D x i).ntw, ρ.Good → ρ'.Good → RealPin p.R p.cG ρ →
  SameBut ρ ρ' → (Adapted p w ρ ∨ Adapted p w ρ') →
  ∃ (χ χ' : Formalism.L2.Host.HChar (Fm.D x i).host.E) (xiR xiR' : ∀ PP : Pl (Fm.D x i).host.E, (kP PP)ˣ →* ℂˣ),
    TwLev p.R.toRealDat χ ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) xiR ∧
    TwLev p.R.toRealDat χ' ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q) xiR' ∧
    χ ≠ 1 ∧ χ' ≠ 1 ∧ (χ ≠ χ' ∨ (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi =
      (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)

end Point

end GlobalTheory.BigOn.Exp.TwConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChange
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem baseChange_holds : BaseChange := by
  intro O _ _ _ ϖ hϖ N ν _
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hdom : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  constructor
  · intro f hf
    rw [standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
      refine ⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩
      rw [← hsh]
      exact bidetMem O N N K sz hsz I
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, by simp⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  · intro g hg h0
    have hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨h, hh⟩ := hk
    have hgh : g = ϖ • h := by rw [smul_eq_C_mul, ← hh, mul_comm]
    refine ⟨h, ?_, hgh⟩
    exact dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)

end GlobalTheory.HighWt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThreshold
section
namespace GlobalTheory.HodgeMultNum

theorem nat_bound (r f T : ℕ) (hr : 100 ≤ r) (hf : 5 ≤ f) (hT : 11 * (f * r.choose 2) ^ 2 ≤ T) :
    2 * r + 50 * r ^ 2 * (f * (r * r / 4)) + 2 ≤ T := by
  have hq : 4 * (r * r / 4) ≤ r * r := Nat.mul_div_le (r * r) 4
  have hc : 2 * r.choose 2 = r * (r - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 100 := ⟨r - 100, by omega⟩
  have h1 : s + 100 - 1 = s + 99 := by omega
  rw [h1] at hc
  set q := (s + 100) * (s + 100) / 4
  set c := (s + 100).choose 2
  have key : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) ≤ 4 * (11 * (f * c) ^ 2) := by
    have e1 : 4 * (11 * (f * c) ^ 2) = 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by rw [← hc]; ring
    rw [e1]
    have e2 : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) = 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * (4 * q) := by ring
    rw [e2]
    have h3 : 50 * (s+100)^2 * f * (4 * q) ≤ 50 * (s+100)^2 * f * ((s+100)*(s+100)) := Nat.mul_le_mul_left _ hq
    have h4 : 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * ((s+100)*(s+100)) ≤ 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      ring_nf
      nlinarith [Nat.zero_le (s * g), Nat.zero_le (s * g ^ 2), Nat.zero_le (s ^ 2 * g), Nat.zero_le (s ^ 2 * g ^ 2),
        Nat.zero_le (s ^ 3 * g), Nat.zero_le (s ^ 3 * g ^ 2), Nat.zero_le (s ^ 4 * g), Nat.zero_le (s ^ 4 * g ^ 2),
        Nat.zero_le (s ^ 2), Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 4), Nat.zero_le (g ^ 2)]
    omega
  omega

theorem five_le_of_pow (r f : ℕ) (hr : 100 ≤ r) (h : (r : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ 1 / 16) : 5 ≤ f := by
  by_contra hf
  push_neg at hf
  have h1 : (7 / 8 : ℝ) ^ 4 ≤ (7 / 8 : ℝ) ^ f := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [pow_pos (show (0:ℝ) < 7/8 by norm_num) f]

end GlobalTheory.HodgeMultNum

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

theorem GlobalTheory.HodgeMultNum.hodgeMult_le_TO : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤
      (Fm.parT x hx ι).TO := by
  refine Closed.imp GlobalTheory.T.badShareSize_bounds_along_family fun Fm _ _ H => ?_
  obtain ⟨x0, H⟩ := H
  refine ⟨x0, fun x hx h0 ι => ?_⟩
  obtain ⟨hr, -, hE, hk⟩ := H x hx h0 ι
  obtain ⟨hg, hsum⟩ := hk 0
  set D := Fm.D x ι
  set g : ℝ := (D.host.g 0 : ℝ)
  have hg1 : (4096 : ℝ) ≤ g := by simp only [g]; exact_mod_cast hg
  have hlogg : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  have hr' : (100 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr
  have hlogr : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg (by linarith)
  have hfpos : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ 3 * (D.R.f : ℝ) / g := by positivity
  have hB : 0 ≤ 23 * (D.R.f : ℝ) * Real.log g / Real.sqrt g := by positivity
  have hC : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
      (1 + Real.log (D.R.r : ℝ)) / (g - 1)) := by
    have : 0 ≤ g - 1 := by linarith
    positivity
  have hE' : 0 ≤ Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := (Real.exp_pos _).le
  have hP : (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f ≤ 1 / 16 := by linarith
  have hf := GlobalTheory.HodgeMultNum.five_le_of_pow _ _ hr hP
  have hT := (Fm.parT x hx ι).TO_11D2
  rw [(Fm.parT x hx ι).Dp_eq] at hT
  exact GlobalTheory.HodgeMultNum.nat_bound _ _ _ hr hf hT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpan
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.MulSpan

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zero_mem_SS' (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  refine ⟨⟨⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by
    simp [Data.pnorm]⟩, fun ξ _ x _ => ?_⟩
  unfold Data.fj
  split_ifs <;> simp

open Classical in

def mulAt {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) : FDSec X →ₗ[ℂ] FDSec X :=
  (LinearMap.single ℂ (fun k => Frame (X k).Ψ r → ℂ) k0) ∘ₗ (LinearMap.mulLeft ℂ h) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) k0)

theorem mulAt_same {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) :
    mulAt X k0 h P k0 = fun y => h y * P k0 y := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same, LinearMap.mulLeft_apply,
    LinearMap.proj_apply]
  rfl

open Classical in
theorem mulAt_ne {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ) (P : FDSec X) {k : Comp}
    (hk : k ≠ k0) : mulAt X k0 h P k = 0 := by
  simp only [mulAt, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_of_ne hk]

theorem mulAt_mem_holSub {Comp : Type} (X : Comp → Data E r) (k0 : Comp) (h : Frame (X k0).Ψ r → ℂ)
    (la la' : ∀ k, Wt (X k).Ψ r) (hh : ∀ Q ∈ (X k0).SS (la k0), (fun y => h y * Q y) ∈ (X k0).SS (la' k0))
    {P : FDSec X} (hP : P ∈ holSub X la) : mulAt X k0 h P ∈ holSub X la' := by
  have hle : holSub X la ≤ (holSub X la').comap (mulAt X k0 h) := by
    refine Submodule.span_le.2 fun Q hQ => ?_
    refine Submodule.subset_span (s := {P | IsHolCusp X la' P}) fun k => ?_
    by_cases hk : k = k0
    · subst hk
      rw [mulAt_same]
      exact hh _ (hQ k)
    · rw [mulAt_ne X k0 h Q hk]
      exact zero_mem_SS' _ _
  exact hle hP

theorem horizGen_zpow_mul_rdU_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z σ hσ k0 hk τ' m b b' n hb hb' hpos hn hw f hf
  have hP : rdU (U σ) f ∈ holSub (U σ).X (modelWt (U σ) (wtZ b n)) := (mem_cuspW.1 (cuspOn_le U Z _ hf)).2 σ hσ
  have hLP : mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) ∈
      holSub (U σ).X (modelWt (U σ) (wtZ b' n)) := by
    refine mulAt_mem_holSub _ k0 _ _ _ (fun Q hQ => ?_) hP
    rw [hw]
    refine HorizMul.horizGen_zpow_mul_mem_SS E r _ τ' _ m (hL.det σ hσ k0) (fun γ hγ => ?_) Q hQ
    rw [← hw, modelWt_wtZ, modelWt_wtZ, hL.chi σ hσ b n hb k0 γ hγ, hL.chi σ hσ b' n hb' k0 γ hγ]
  have hoff : ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k y = 0 := by
    intro k y hy
    by_cases hkk : k = k0
    · subst hkk
      have hd : y ∉ ((U σ).X k).dom := fun hd => hy (by rw [hk]; exact ⟨rfl, hd⟩)
      have h0 : rdU (U σ) f k y = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_neg, not_false_eq_true]
      rw [mulAt_same]
      simp only [h0, mul_zero]
    · rw [mulAt_ne _ _ _ _ hkk]
      rfl
  have hsp := (cuspOn_fd_and_span_rdU E H Dw l Xo c r U x hL Z σ hσ b' n hb' hpos hn).2 _ hLP hoff
  let R : FDSec (U σ).X →ₗ[ℂ] (↥((U σ).X k0).dom → ℂ) :=
    { toFun := fun Q y => Q k0 y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmap := Submodule.mem_map_of_mem (f := R) hsp
  rw [Submodule.map_span, Set.image_image] at hmap
  have e : R (mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f)) =
      fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1 := by
    funext y
    show mulAt (U σ).X k0 (fun y => horizGen τ' y ^ m) (rdU (U σ) f) k0 y.1 = _
    rw [mulAt_same]
  rw [e] at hmap
  exact hmap

end GlobalTheory.FlatCore.MulSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtValAtNonempty
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.Fin

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem htValAt_nonempty (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io)
    (hy : y₀.IsAlg) : (htValAt la y₀).Nonempty := by
  obtain ⟨p, hp, ha, k, y, h⟩ := (GlobalTheory.CompHt.exists_isHTFrameCp_and_nonempty E H Dw l Xo c).1 T io y₀ hy
  exact ⟨_, p, hp, ha, k, y, h, rfl⟩

theorem finConst_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (h₁ : HTConst U x) (h₂ : HTShift Xo c) :
    FinConst U x := fun Z τ s la => by
  obtain ⟨ρ, hρ⟩ := h₁ Z τ s la
  obtain ⟨κ, hκ⟩ := h₂ τ la
  refine ⟨ρ - κ, ?_⟩
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := htValAt_nonempty la y hy.1
  have h3 := (hρ w ⟨T, io, e, y, ho, hy, hw⟩).symm.trans (hκ T io e y ho hy.1 w hw _ s.sig_mem)
  show nval T.V e (evI y s.sig) = _
  by_cases h0 : evI y s.sig = 0
  · rw [h0, nval_zero, EReal.top_add_coe] at h3
    exact absurd h3 (EReal.coe_ne_top ρ)
  · rw [nval_of_ne h0] at h3 ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h3
    rw [EReal.coe_eq_coe_iff, h3]; ring

theorem finConst_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    Laws U x → HTShift Xo c → HTConst U x → FinConst U x :=
  by
  intro E _ _ _ H Dw l Xo c r U x _ h₂ h₁
  exact finConst_of h₁ h₂

end GlobalTheory.FlatCore.Fin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveICRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_iC_rows : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  first | exact @GlobalTheory.BigTop.Fun.iC_base_factor_of_rows | exact GlobalTheory.BigTop.Fun.iC_base_factor_of_rows | (intros; apply GlobalTheory.BigTop.Fun.iC_base_factor_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnisoAt
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase

namespace GlobalTheory.SWOpIndef

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

def supAt {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) (v₀ : HeightOneSpectrum (𝓞 F)) : Subgroup (UA σ J₂) where
  carrier := {g | (mat g).det = 1 ∧ (∀ v, v ≠ v₀ → (mat g).map (compFin F E v) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (mat g).map (piInf τ) = 1}
  one_mem' := by
    refine ⟨by simp [show mat (1 : UA σ J₂) = 1 from rfl], fun v _ => ?_, fun w τ => ?_⟩ <;>
      simp [show mat (1 : UA σ J₂) = 1 from rfl]
  mul_mem' := by
    rintro g h ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    have e : mat (g * h) = mat g * mat h := rfl
    refine ⟨by rw [e, Matrix.det_mul, h1, h1', one_mul], fun v hv => ?_, fun w τ => ?_⟩
    · rw [e, Matrix.map_mul, h2 v hv, h2' v hv, one_mul]
    · rw [e, Matrix.map_mul, h3 w τ, h3' w τ, one_mul]
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    have e : mat g⁻¹ * mat g = 1 := by
      change mat (g⁻¹ * g) = 1
      rw [inv_mul_cancel]; rfl
    refine ⟨?_, fun v hv => ?_, fun w τ => ?_⟩
    · have := congrArg Matrix.det e
      rwa [Matrix.det_mul, h1, mul_one, Matrix.det_one] at this
    · have := congrArg (fun M => M.map (compFin F E v)) e
      simp only [Matrix.map_mul, h2 v hv, mul_one] at this
      simpa using this
    · have := congrArg (fun M => M.map (piInf τ)) e
      simp only [Matrix.map_mul, h3 w τ, mul_one] at this
      simpa using this

def IsAnisoAt {m : ℕ} (JV : Matrix (Fin m) (Fin m) E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : Fin m → Fv F v ⊗[F] E,
    x ⬝ᵥ (JV.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E)) *ᵥ
      (fun i => Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (x i)) = 0 → x = 0

example {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) (g h : UA σ J₂) : mat (g * h) = mat g * mat h := by rfl
example {N : ℕ} (J₂ : Matrix (Fin N) (Fin N) E) : mat (1 : UA σ J₂) = 1 := by rfl

end GlobalTheory.SWOpIndef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsLevGrp {H : Host E} (l : Level H) {r : ℕ} (Y : Data E r) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧
    (∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M • y) ∧
    (∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.A • y)

def IsSelfDualTr {r : ℕ} (Y : Data E r) : Prop :=
  ∀ x : Fin r → E, x ∈ Y.Λ ↔ ∀ y ∈ Y.Λ, ∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm x y) = n

end GlobalTheory.EqCovol
end
end


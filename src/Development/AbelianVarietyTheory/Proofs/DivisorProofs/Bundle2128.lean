import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistScalarMemRange
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistScalarField

open NumberField IsDedekindDomain

theorem val_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (χ₁ * χ₂).val v = χ₁.val v * χ₂.val v :=
  Formalism.L2.Host.HChar.loc_mul χ₁ χ₂ v _

theorem onId_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := by
  unfold Formalism.L2.Host.HChar.onId
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := L) I)
  have hs : ∀ χ : Formalism.L2.Host.HChar L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v I).Finite :=
    fun χ => hfin.subset fun v hv h0 => hv (by show χ.val v ^ _ = 1; rw [h0, zpow_zero])
  rw [← finprod_mul_distrib (hs χ₁) (hs χ₂)]
  exact finprod_congr fun v => by rw [val_mul, mul_zpow]

theorem onId_mem_range {L C : Type} [Field L] [NumberField L] [Field C] (emb : C →+* ℂ) (ξ : Formalism.L2.Host.HChar L)
    (h : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ emb.range) (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :
    ((ξ.onId I : ℂˣ) : ℂ) ∈ emb.range := by
  let S : Subgroup ℂˣ :=
    { carrier := {u | (u : ℂ) ∈ emb.range}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x * y, by rw [map_mul, hx, hy, Units.val_mul]⟩
      one_mem' := ⟨1, by rw [map_one, Units.val_one]⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨x, hx⟩ := ha
        exact ⟨x⁻¹, by rw [map_inv₀, hx, Units.val_inv_eq_inv_val]⟩ }
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), ξ.val v ∈ S := fun v => h _
  exact finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) (fun v => S.zpow_mem (hv v) _)

set_option maxHeartbeats 1000000 in

theorem twist_scalar_mem_range : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∃ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv htup hQG hF0 hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h N hU hTb hTl hLevOK hconj e Ps yd hh he hPs hPsO hs hy hcard
  classical
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.p.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.J.toCore.good_σ₀).1
  have hInR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hlev := hT.sh.dLev _ hInR (Vc D i).rank
  obtain ⟨pp, -, hpd⟩ := hT.sh.dPd
  have hpd1 := hRun.2.1
  rw [hpd _ hInR] at hpd1
  have hpd2 : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).pd = ownAt D v := by rw [hpd _ hInR, hpd1]
  have hL := hC.lev
  have hstd := hO.2.lift.std
  have hbadO := hO.2.bad ()
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad () := ⟨_, rfl⟩
  have hbPs : ∀ PP ∈ Ps, ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP hm => by
    rw [hb, Nat.cast_mul (badN D * _)] at hm
    rcases PP.isPrime.mem_or_mem hm with h1 | h1
    · exact hPs PP hP h1
    · exact hPsO PP hP h1
  have h2b : 2 ∣ b := hb ▸ dvd_mul_of_dvd_right hbadO.2.1 _
  have hMb' : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∣ b := hb ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have g := GlobalTheory.AdTh.SerOne.guard_of_splitOffBad (Vc D i) hstd.1 hstd.2 _ h2b hMb' ⟨hh, e, Ps, he, hbPs, hs⟩
  obtain ⟨gU, ⟨k, hk1, hk2, hk3⟩, gS⟩ := g
  have gT : (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank).TrivAt ((O i).bad ()) :=
    ⟨k, Nat.Coprime.coprime_dvd_right (hb ▸ dvd_mul_left _ _) hk1, hk2, hk3⟩
  have hΛ : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) := by
    cases Λ with
    | mk La => congr 1; ext w; exact hconj w
  have memb : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((b : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := fun Q hQ => by
    rw [hb, hlev.2.1, hpd2, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hQ))
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal (Vc D i) hstd.1 hstd.2 h e Ps yd he hs hy b hbPs
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹)
    (GlobalTheory.ClassScalarValue.chrEq_mul_inv (hL.mu0 i) hK.chr hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ hbadO.2.2.2.2)
        rw [hb, hu]
        simp only [Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hj))
      have a2 : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).UnrAt Q := by
        by_contra hn
        rcases (hK.ram Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (memb Q (Finset.mem_filter.1 a).2)
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (memb Q' (Finset.mem_filter.1 a).2)
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
        R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, hK.triv.1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.2.ep ()).2 _ cc gU gT gS c1 c3
  have c2' : cc ⊔ Ideal.span {(((O i).bad () : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    refine top_le_iff.1 (c2 ▸ sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 ?_) _)
    rw [hb]; exact Nat.cast_dvd_cast (dvd_mul_left _ _)
  have hB := (hO.2.tuple ()).B cc c0 c2'
  have hxi : R.xiH A.μ0 = 1 := hL.xi_base
  have S1 : ∀ (χ₁ χ₂ : Formalism.L2.Host.HChar D.host.E) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := fun χ₁ χ₂ I => onId_mul χ₁ χ₂ I
  have S2 : ∀ (ξ : Formalism.L2.Host.HChar D.host.E), (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) →
      ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, ((ξ.onId I : ℂˣ) : ℂ) ∈ D.what₂.embLL.range :=
    fun ξ hξ I => onId_mem_range D.what₂.embLL ξ hξ I
  have e1 : R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹ =
      (R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹) * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) := by
    rw [hxi, mul_one, mul_right_comm]
  rw [e1, S1, Units.val_mul] at c4
  obtain ⟨a3, ha3⟩ := S2 _ hdel (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  have hF := hO.1
  have memF : ∀ x : (O i).c'.F, ∃ a : D.what₂.LL, D.what₂.embLL a = (x : ℂ) := fun x => by
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 ((SetLike.ext_iff.1 hF (x : ℂ)).1 x.2)
    exact ⟨a, ha⟩
  obtain ⟨a1, ha1⟩ := memF (incF T.Q.c (O i).c' (O i).hle (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))
  obtain ⟨a2, ha2⟩ := memF ((O i).B () cc)
  have hi : GlobalTheory.ClassScalarCompare.stdIndex Λ =
      GlobalTheory.ClassScalarCompare.stdIndex (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank) := by
    rw [hΛ]; exact GlobalTheory.ClassScalarCompare.stdIndex_conjLat _
  have q1' : (q : ℝ) ^ 2 * ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) := by
    rw [hi, hpq]; exact_mod_cast q1
  have hsq : ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ) =
      ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) * ((q : ℂ))⁻¹ := by
    have hq : (0:ℝ) < q := by exact_mod_cast q0
    have e2 : ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) / (q : ℝ) ^ 2 := by
      rw [← q1']; field_simp
    rw [e2, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hq.le, Complex.ofReal_div, div_eq_mul_inv,
      Complex.ofReal_ratCast]
  have h1 : (O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ) = D.what₂.embLL a1 := ha1.symm
  beta_reduce at hB
  have h2 := ha2.trans hB
  refine ⟨a1⁻¹ * a2 * a3 * ((q⁻¹ : ℚ) : D.what₂.LL), ?_⟩
  change _ = _ * _ * ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ)
  rw [h1, c4, hsq, map_mul, map_mul, map_mul, map_inv₀, map_ratCast, h2, ha3]
  push_cast
  ring

end GlobalTheory.TwistScalarField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramified
section
namespace GlobalTheory.TwistedKernelChar

section General

open NumberField IsDedekindDomain Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem inf_triv [IsTotallyComplex L] (χ : HChar L) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hpow : ∀ x, χ.1 x ^ n = 1 := fun x => by
    have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
    simpa using h1
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h0
    have h1 : z = 0 := by simpa using congrArg e h0
    rw [h1, zero_pow hn.ne'] at hz
    exact (atInf w k).ne_zero (e.injective (by rw [← hz, map_zero]))
  have hk : atInf w k = Units.mk0 _ hz0 ^ n := Units.ext (e.injective (by
    rw [← hz, Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, RingEquiv.apply_symm_apply]))
  rw [MonoidHom.comp_apply, hk, map_pow, map_pow, hpow]

theorem hasInf_mul_inv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n m : I → ℤ} {α β γ : HChar L}
    (ha : α.HasInf φ n) (hb : ∀ k, β.inf k = 1) (hc : γ.HasInf φ m) : (α * β * γ⁻¹).HasInf φ (fun i => n i - m i) := by
  intro k
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, hb, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, ha k, hc k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have h1 : φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0))
  rw [zpow_sub₀ h1, div_eq_mul_inv (_ ^ _)]

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem frame_char (D : D7) (C : Formalism.L2.Host.CharFrame D) (i : Fin D.R.m) (l : ℕ) :
    ∃ (b : ℕ) (n : D.R.Psi → ℤ), b ≠ 0 ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ Q.asIdeal → ((badN D : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → (C.mu0 i * C.delAt l * C.eta⁻¹).UnrAt Q) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        ∀ k : D.host.Fˣ, (C.mu0 i * C.delAt l * C.eta⁻¹).resFin (Q.under (𝓞 D.host.F)) k = 1) ∧
      (∀ Q, (C.mu0 i * C.delAt l * C.eta⁻¹).TameAt Q) ∧
      (C.mu0 i * C.delAt l * C.eta⁻¹).HasInf (Formalism.L2.Host.embPsi D.host) n := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨p, hp, hpl, hδ⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ D.host.levelPrimes ∧ Formalism.L2.Host.IsDelta (H := D.host) p (C.delAt l) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    · exact ⟨_, D.host.pde'_prime, D.host.pde_level.2, C.isDel'⟩
    · exact ⟨_, D.host.pde_prime, D.host.pde_level.1, C.isDel⟩
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ∀ a b : ℕ, a ∣ b → (a : 𝓞 D.host.E) ∈ Q.asIdeal →
      (b : 𝓞 D.host.E) ∈ Q.asIdeal := by
    rintro Q a b ⟨u, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have lev : ∀ a ∈ D.host.levelPrimes, a ∣ badN D := fun a ha =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => p) ha) _
  obtain ⟨n, -, hn⟩ := (C.isMu0 i).inf
  obtain ⟨o, ho, hod⟩ := hδ.fin
  refine ⟨D.host.g 0 * D.host.g 1 * p, fun τ => n τ - 1,
    mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) hp.ne_zero, fun Q hQ => ?_,
    fun Q hQ x hx => ?_, fun Q hQ x => ?_, fun Q x hx hx' => ?_,
    hasInf_mul_inv hn (inf_triv _ ho hod) C.isEta.inf⟩
  · rw [Nat.cast_mul, Nat.cast_mul] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h | h
    · rcases Q.isPrime.mem_or_mem h with h | h
      · exact key Q _ _ (lev _ (D.host.g_level 0)) h
      · exact key Q _ _ (lev _ (D.host.g_level 1)) h
    · exact key Q _ _ (lev _ hpl) h
  · have a1 : (C.mu0 i).UnrAt Q := (C.isMu0 i).unr Q fun j hj => hQ (key Q _ _ (by
      refine Dvd.dvd.mul_right ?_ p
      rw [← Fin.prod_univ_two D.host.g]
      exact Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)) hj)
    have a2 : (C.delAt l).UnrAt Q := hδ.unr Q fun hj => hQ (key Q _ _ (Dvd.intro_left _ rfl) hj)
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1 x hx, a2 x hx,
      C.isEta.unr Q x hx, inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
      (C.isMu0 i).triv.1, hδ.triv.1, C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
      Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, (C.isMu0 i).tame Q x hx hx',
      hδ.tame Q x hx hx', C.isEta.unr Q x hx, inv_one, one_mul, one_mul]

set_option maxHeartbeats 800000 in

theorem twisted_kernel_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i _ v _ _ _ _ _ _ _ _ ℓ _ _ χ ξR ω φ hK Λ h N _ _ _ _ _ e Ps yd _ _ hb
  obtain ⟨b, n, h0, h1, h2, h3, h4, h5⟩ := frame_char D R.C i (Formalism.EigenvalueLevelCeiling.plc v)
  refine ⟨_, b, _, _, _, n, h0, fun Q hQ hm => hb Q hQ ?_,
    GlobalTheory.ClassScalarValue.chrEq_mul_inv (hC.lev.mu0 i) hK.chr hC.lev.eta, h2, h3, h4, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (h1 Q hm)

end GlobalTheory.TwistedKernelChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterLocalGL
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinBarChar

open Matrix

theorem boxFun_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem fromBlocks_diag_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A - 1 = Matrix.fromBlocks (A - 1) 0 0 (A - 1) := by
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

theorem fromBlocks_diag_mul_diagCols {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A * (diagCols n : Matrix (n ⊕ n) n R) = (diagCols n : Matrix (n ⊕ n) n R) * A := by
  ext (i | i) j <;> simp [diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply]

theorem unif_pow_ne_real : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hχ t K hK S hS ν α ι hι hint m hm r hr
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw

  haveI : Nonempty (Fin a') := ⟨⟨0, by have := hT.geo.aBig; omega⟩⟩
  obtain ⟨g₀, hg₀⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a') (R := Fv F v) (unifAt v)

  set k := K g₀ with hk
  have hkU : (mat k)ᵀ * incM F G.V'.J * (mat k).map (cA σ) = incM F G.V'.J := k.2
  set mi : Matrix (Fin a') (Fin a') (AE F E) := ((k : GL (Fin a') (AE F E))⁻¹).1
  have h1 : mat k * mi = 1 := Units.mul_inv (k : GL (Fin a') (AE F E))
  have h2 : mi * mat k = 1 := Units.inv_mul (k : GL (Fin a') (AE F E))
  let P₀ : GL (Fin a' ⊕ Fin a') (AE F E) := ⟨Matrix.fromBlocks (mat k) 0 0 (mat k), Matrix.fromBlocks mi 0 0 mi,
    by rw [Matrix.fromBlocks_multiply, h1]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply, h2]; simp [Matrix.fromBlocks_one]⟩
  have hP₀ : P₀ ∈ UG (cA σ) (dbl (incM F G.V'.J)) := by
    show (Matrix.fromBlocks (mat k) 0 0 (mat k))ᵀ * dbl (incM F G.V'.J) * (Matrix.fromBlocks (mat k) 0 0 (mat k)).map (cA σ) = _
    have hn : (mat k)ᵀ * (-incM F G.V'.J) * (mat k).map (cA σ) = -incM F G.V'.J := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hkU]
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.map_zero _ (map_zero (cA σ))]
    rw [hkU, hn]
  let p : UG (cA σ) (dbl (incM F G.V'.J)) := ⟨P₀, hP₀⟩
  have hpm : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 (mat k) := rfl
  have hAt : At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g₀).1 u hu
    rw [hpm, fromBlocks_diag_sub_one, Matrix.fromBlocks_smul]
    simp [hk1]
  have hpt : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) *
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) =
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) *
        (((k : UA σ G.V'.J) : GL (Fin a') (AE F E)) : Matrix (Fin a') (Fin a') (AE F E)) := by
    rw [hpm]
    exact fromBlocks_diag_mul_diagCols _

  obtain ⟨l, hl, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hlφ, φ₀, hφ₀, hI⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  have hbox := boxFun_mem_SB hφ₀ hφ₀
  obtain ⟨φ'', hφ'', hact⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hAt _ hbox
  have h4 := GlobalTheory.T.triple_local_gl_embedding_integral hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl
    (fun g gd hgd φ₁ h₁ φ₂ h₂ => hres g gd hgd φ₁ h₁ φ₂ h₂) g₀ p hpm φ₀ hφ₀ φ₀ hφ₀ φ'' hφ'' hact μ hμ
  have hs := hsieg l hl hinv p _ hpt _ (hr₀ _ hbox).2
  rw [hact r₀ (hr₀ _ hbox), hlφ _ hφ'', hlφ _ hbox, h4] at hs
  have hbd : (∫ x, boxFun φ₀ φ₀ (Sum.elim x x) ∂μ) = ∫ x, φ₀ x * φ₀ x ∂μ := rfl
  rw [hbd] at hs
  set I := ∫ x, φ₀ x * φ₀ x ∂μ
  set val := ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) with hval
  set u : ℂ := (ν (GlobalTheory.SplitFlip.gdet g₀) : ℂ) with hu
  have hratio : u / starRingEnd ℂ u = val := by
    have : c₀ * I * (u / starRingEnd ℂ u) = c₀ * I * val := by linear_combination hs
    exact mul_left_cancel₀ (mul_ne_zero hc₀ hI) this
  have h6 := GlobalTheory.T.triple_local_gl_embedding_equivariant F E σ B a a' G X om om' hT v hv t K hK g₀

  have hgd : GlobalTheory.SplitFlip.gdet g₀ = unifAt v := hg₀
  rw [hgd] at hu h6
  have hu0 : u ≠ 0 := by rw [hu]; exact Units.ne_zero _
  have hr' : u ^ m = (r : ℂ) := by rw [hu]; exact hr
  have hrc : starRingEnd ℂ u ^ m = (r : ℂ) := by rw [← map_pow, hr', Complex.conj_ofReal]
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr']; exact pow_ne_zero _ hu0
  have hone : val ^ m = 1 := by
    rw [← hratio, div_pow, hr', hrc, div_self hr0]
  set z := chrW X.ν t (unifAt v) with hz
  rcases h6 with h | h
  · have e1 : ((z ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (((2 * m : ℕ) : ℤ)) (by omega)
    rw [zpow_natCast]
    exact Units.ext e1
  · have e1 : (((z⁻¹) ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (-((2 * m : ℕ) : ℤ)) (by omega)
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact Units.ext e1

end GlobalTheory.LinBarChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContraction
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteLevel

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_comb_colP {r : ℕ} (X : Data E r) (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (v : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, v = ∑ a, K a • X.colP x τ a := by
  refine ⟨fun a => ((mat x τ)⁻¹ *ᵥ v) (Fin.castLE X.p0_le a), ?_⟩
  have h1 : v = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  have h2 : ∀ w : Fin r → ℂ, mat x τ *ᵥ w = ∑ j, w j • ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j := by
    intro w; funext k; simp [Matrix.mulVec, dotProduct, ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_apply, mul_comm]
  conv_lhs => rw [h1, h2]
  exact (Fintype.sum_equiv (finCongr hp) _ _ (fun a => rfl)).symm

theorem maj_mulVec_of_definite {r : ℕ} (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v)
    (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ (((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ u) = X.maj x τ u := by
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg' : ∀ w, g *ᵥ (g' *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hg'g : ∀ w, g' *ᵥ (g *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hiso := GlobalTheory.MajInv.hermC_stab X hγ τ.1
  have key := MajorantConjugateTransfer.maj_transfer X hx hx τ g g' hgg' hiso ?_ ?_ (g *ᵥ u)
  · rwa [hg'g] at key
  · intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · exact exists_comb_colP X hp x τ (hx τ).1 _
  · intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · obtain ⟨L, hL⟩ := exists_comb_colP X hp x τ (hx τ).1 (g' *ᵥ X.colP x τ a)
      refine ⟨L, ?_⟩
      calc X.colP x τ a = g *ᵥ (g' *ᵥ X.colP x τ a) := (hgg' _).symm
        _ = g *ᵥ ∑ c, L c • X.colP x τ c := by rw [hL]
        _ = ∑ c, L c • (g *ᵥ X.colP x τ c) := by
          rw [Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul]

theorem eq_one_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g →
    (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) →
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∀ γ ∈ G, γ = 1 := by
  intro E _ _ _ r X G g hg hgr hU hUn hp x hx hnc γ hγ
  refine GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hg hgr G hU hUn x hx hnc γ hγ fun τ u => ?_
  rw [maj_mulVec_of_definite X.toData hp hx γ (hU γ hγ).1 τ u]
  have h0 := MajorantConjugateTransfer.maj_nonneg X.toData hx τ u
  have h1 : 1 ≤ Real.exp (1 / (3 * (r : ℝ))) := Real.one_le_exp (by positivity)
  exact le_mul_of_one_le_left h0 (one_le_pow₀ h1)

end GlobalTheory.DefiniteLevel
end


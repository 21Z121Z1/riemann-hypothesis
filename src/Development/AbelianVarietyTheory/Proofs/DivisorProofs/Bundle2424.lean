import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_exp_of_log_le {y L : ℝ} (hy : 0 ≤ y) (h : Real.log y ≤ L) : y ≤ Real.exp L := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0]; exact (Real.exp_pos L).le
  · exact (Real.log_le_iff_le_exp h0).1 h

theorem kapQ_inl (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (a : Fin p) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inl a) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t a := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have ha := a.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) a = DV.sigPar D t a := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inl]
  rw [if_pos (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem kapQ_inr (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) (c : Fin q) :
    Formalism.L2.NTheta.kapQ (D.hc t) p q (Sum.inr c) + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t (p + c) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hc := c.2
  have e0 : Formalism.L2.NTheta.lamAt (D.hc t) (p + c) = DV.sigPar D t (p + c) := rfl
  unfold Formalism.L2.NTheta.kapQ GlobalTheory.CovTop.WtShape.ent
  simp only [Sum.elim_inr]
  rw [if_neg (by omega), e0]
  subst hp hq
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr, Nat.cast_sub (by omega : 1 ≤ D.R.k + D.R.m), Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ D.R.m)]
  push_cast
  ring

theorem abs_wt_le (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) {p q : ℕ} (hp : p = D.R.k + i)
    (hq : q = D.R.m - ((i : ℕ) + 1)) {B : ℝ}
    (hB : ∀ n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) (a : Fin p ⊕ Fin q) :
    |((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + (((D.hc t).e i : ℚ) : ℝ)| ≤ B + 1 := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨n, hn, hx⟩ : ∃ n, n < D.R.r ∧
      Formalism.L2.NTheta.kapQ (D.hc t) p q a + (D.hc t).e i = GlobalTheory.CovTop.WtShape.ent D i t n := by
    cases a with
    | inl a => exact ⟨a, by have := a.2; omega, kapQ_inl D i t hp hq a⟩
    | inr c => exact ⟨p + c, by have := c.2; omega, kapQ_inr D i t hp hq c⟩
  have h1 : ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) ≤ (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) := by
    unfold Formalism.L2.NTheta.kapW
    exact_mod_cast Int.floor_le _
  have h2 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) < ((Formalism.L2.NTheta.kapW (D.hc t) p q a : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (Formalism.L2.NTheta.kapQ (D.hc t) p q a)
    have h' : ((Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℚ) : ℝ) <
        (((⌊Formalism.L2.NTheta.kapQ (D.hc t) p q a⌋ : ℤ) : ℚ) : ℝ) + 1 := by
      have := (Rat.cast_lt (K := ℝ)).2 h
      rw [Rat.cast_add, Rat.cast_one] at this
      exact this
    rw [Rat.cast_intCast] at h'
    exact h'
  have h3 : (Formalism.L2.NTheta.kapQ (D.hc t) p q a : ℝ) + (((D.hc t).e i : ℚ) : ℝ) =
      ((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ) := by
    rw [← hx]; push_cast; ring
  obtain ⟨b1, b2⟩ := abs_le.1 (hB n hn)
  rw [abs_le]
  constructor <;> linarith

theorem wtSize_le (D : D7) (i : Fin D.R.m) {B : ℝ}
    (hB : ∀ t n, n < D.R.r → |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ B) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i ≤ D.R.f * D.R.r * (B + 1) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
  calc _ ≤ ∑ _τ : D.what₂.Tau, (D.R.r : ℝ) * (B + 1) := Finset.sum_le_sum fun τ _ => ?_
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]; ring
  have hs : (Wc D i).sig (TH.tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have s1 : ((Wc D i).sig (TH.tauE D τ)).1 = D.R.k + i := by rw [hs]; rfl
  have s2 : ((Wc D i).sig (TH.tauE D τ)).2 = D.R.m - ((i : ℕ) + 1) := by rw [hs]; rfl
  calc _ ≤ ∑ _a : Fin ((Wc D i).sig (TH.tauE D τ)).1 ⊕ Fin ((Wc D i).sig (TH.tauE D τ)).2, (B + 1) :=
        Finset.sum_le_sum fun a _ => abs_wt_le D i τ s1 s2 (hB τ) a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, s1, s2]
      congr 1
      rw [hr]; push_cast [show (i : ℕ) + 1 ≤ D.R.m by omega, show 1 ≤ D.R.k + D.R.m by omega]; ring

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasUp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem abs_ent_le {PP : ℝ} (hW : WtNum p i PP) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.r) :
    |((GlobalTheory.CovTop.WtShape.ent D i t n : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hp := p.fw.laws.pins.1
  let τ : Psi p.T.Q.H := ⟨DV.tauEmb D t, hp.2.2.2 t⟩
  let k : Fin ((dat p i).p + (dat p i).q) := ⟨n, by rw [GlobalTheory.CovTop.WtShape.dat_rank p i]; exact hn⟩
  have e := GlobalTheory.CovTop.WtShape.laOf_read p i τ t rfl k
  have h := hW.up τ k
  rw [← e, Rat.cast_intCast]
  exact h

theorem sizes_two {PP A PP' : ℝ} (P : ParameterChoice' D L) (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D (2 * L.sc.L) := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hnV : (0 : ℝ) ≤ D.R.nV := Nat.cast_nonneg _
  obtain ⟨hL10, -⟩ := hH.big.2
  obtain ⟨hlfr, hlnV⟩ := hH.logfr
  set Lc := L.sc.L with hLc
  have hb : L.sc.b = Real.exp Lc := rfl
  have hfr : (D.R.f : ℝ) * D.R.r ≤ Real.exp Lc := le_exp_of_log_le (by positivity) hlfr
  have hnVe : (D.R.nV : ℝ) ≤ Real.exp Lc := le_exp_of_log_le hnV hlnV
  have hE0 : 0 < Real.exp Lc := Real.exp_pos _
  have hE1 : Lc + 1 ≤ Real.exp Lc := Real.add_one_le_exp _
  have e2 : Real.exp (2 * Lc) = Real.exp Lc * Real.exp Lc := by rw [two_mul, Real.exp_add]
  refine ⟨?_, fun j => ?_, ?_, ?_⟩
  · rw [e2]
    exact mul_le_mul hfr hnVe hnV hE0.le
  · have hw := wtSize_le D j (abs_ent_le p j (hW j))
    rw [e2, ← hb]
    rw [← hb] at hE1 hfr
    have h1 : (D.R.f : ℝ) * D.R.r * (4 * L.sc.b + 1) ≤ L.sc.b * (5 * L.sc.b) :=
      mul_le_mul hfr (by linarith) (by linarith) (by linarith)
    have h5 : 5 ≤ L.sc.b * L.sc.b := by nlinarith
    have h6 : L.sc.b * (5 * L.sc.b) ≤ (L.sc.b * L.sc.b) ^ 2 := by nlinarith
    linarith
  · have g0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    rw [Real.log_mul g0.ne' g1.ne']
    linarith [hH.logg 0, hH.logg 1]
  · have h1 := Formalism.BasicNotions.log_rdE_le_scL P
    have h2 : |dlogL D 1| ≤ Lc := by
      rw [← L.logDerivative_at_one_eq]; exact P.logDerivative_le_power
    linarith

theorem ratAt_pos_le (hOM : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) {PP A PP' : ℝ} (P : ParameterChoice' D L)
    (hH : HostNum D L PP A 2) (hW : ∀ j, WtNum p j PP') :
    0 < ratAt p i ∧ Real.log (ratAt p i) ≤ 244 * unitE p := by
  obtain ⟨-, hd, h2⟩ := hOM D _ p.R.toLevCh _ p.charW.base.lev i p.R.triv
  obtain ⟨h0, ht, -, hb⟩ := h2 _ _ (p.charW.base.models.νW i)
  have hr : 0 < ratAt p i :=
    mul_pos (ENNReal.toReal_pos h0 ht) (Finset.prod_pos fun τ _ => zero_lt_one.trans_le (hd τ))
  refine ⟨hr, ?_⟩
  have hB := (hb _ (sizes_two p P hH hW)).2.2
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hnV1 : (1 : ℝ) ≤ D.R.nV := by
    have : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
    exact_mod_cast this
  obtain ⟨-, hL10, -, hll⟩ := hH.big
  obtain ⟨-, -, hpoly⟩ := hH.poly
  have hroom := hH.room
  rw [Real.rpow_two] at hroom

  have hr_le : (D.R.r : ℝ) ≤ L.sc.x ^ A := by
    refine le_trans ?_ hpoly
    have a1 : (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := le_mul_of_one_le_left (by linarith) (by linarith)
    have a2 : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := le_mul_of_one_le_right (by positivity) hnV1
    have a3 : (D.R.f : ℝ) * D.R.r * D.R.nV ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have hr2 : (D.R.r : ℝ) ^ 2 ≤ L.sc.b := (pow_le_pow_left₀ (by linarith) hr_le 2).trans hroom
  have hu : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := (hW i).unit
  rw [hu]
  have hL0 : 0 ≤ L.sc.L := by linarith
  have hfL : 0 ≤ (D.R.f : ℝ) * L.sc.L := by positivity
  have c1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hr2 hfL
    nlinarith
  have hb1 : 0 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
    have : 0 < L.sc.b := Real.exp_pos _
    positivity
  have c2 : (D.R.f : ℝ) * L.sc.b * L.sc.L ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := by
    have h1 : (1 : ℝ) ≤ D.R.m * Real.log (Real.log L.sc.x) := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hb1
    nlinarith
  have e3 : (122 : ℝ) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * L.sc.L)) = 244 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L.sc.L) := by
    ring
  have e4 : ratAt p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.νW i) (p.R.fdW i) := rfl
  rw [e4]
  linarith

end GlobalTheory.CovTop.MeasUp

namespace GlobalTheory.CovTop.MeasRd

theorem ratAt_upper : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D) → Closed FamHyp fun Fm _ =>
    ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, 0 < ratAt p i ∧ Real.log (ratAt p i) ≤ K * unitE p := by
  intro hOM
  refine Closed.imp (Closed.and (GlobalTheory.CovTop.Sizes.hostN 2) GlobalTheory.CovTop.WtShape.wtN) fun Fm CH _ h => ?_
  obtain ⟨⟨A, -, hA⟩, ⟨C, -, hC⟩⟩ := h
  obtain ⟨x0, hx⟩ := EvTied.and hA hC
  refine ⟨244, by norm_num, x0, fun x hx' hle ι p hp i => ?_⟩
  obtain ⟨h1, h2⟩ := hx x hx' hle ι p hp
  exact GlobalTheory.CovTop.MeasUp.ratAt_pos_le p i hOM (Fm.params x hx' ι) (h1 i) h2

end GlobalTheory.CovTop.MeasRd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_diag_of_triv_ev_of_symm : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  intro R _ _ G _ hA P hP h0l h0r hsym T a ha
  have hs : (swap P).IsLB := pull_isLB hP _
  have hadd := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hA hA hP h0l h0r)
  have hadd' := (isAdditive_iff hs).1 (CubeNoeth.isAdditive_swap_of_triv_axes hA hA hP h0l h0r)
  have hadd2 : ∀ (Y : Over (Sp R)) (u v w : Y ⟶ G), evc hP u (v * w) = evc hP u v + evc hP u w := by
    intro Y u v w
    rw [← evc_swap hP hs, ← evc_swap hP hs, ← evc_swap hP hs]
    exact hadd' Y v w u
  have hc : cls P hP = cls (swap P) hs := (cls_eq_iff hP hs).2 hsym
  have hsymm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP u v = evc hP v u := by
    intro Y u v
    rw [← evc_swap hP hs u v]
    simp only [evc, hc]
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hcL : ∀ (Y : Over (Sp R)) (u : Y ⟶ G), CechPic.pull u.left (cls _ hL) = evc hP u u := by
    intro Y u
    rw [cls_ev hP, pull_evc, Category.comp_id]
  have hx0 : evc hP (fst T G ≫ a) (snd T G) = 0 := by
    have e := congrArg (CechPic.pull (lift (snd T G) (fst T G)).left) ((triv_ev_iff hP _ _).1 ha)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
  have hD : (Out.translDiff G _ a).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero (evc hP a a) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL a hD (fst T G) (snd T G)
  rw [lift_fst_snd, Over.id_left, pull_id, hcL, hcL] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T G).left (evc hP a a) := by
    rw [e₁, pull_evc, hadd, hadd2, hadd2, hsymm _ (snd T G) (fst T G ≫ a), hx0]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T G).left ⁻¹ᵁ V).ι ≫ (fst T G).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_lift_one_of_triv_ev : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  intro R _ _ G _ hG P hP h0l h0r _ T a ha
  have hadd : IsAdditive P := CubeNoeth.isAdditive_of_triv_axes hG hG hP h0l h0r
  have hD : (Out.translDiff (G ⊗ G) P (lift a (1 : T ⟶ G))).IsLB := LB.isLB_linComb hP _ _
  have hz : cls _ hD = 0 := by
    have e₁ := pull_translDiff hP (lift a (1 : T ⟶ G)) hD (fst T (G ⊗ G)) (snd T (G ⊗ G))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have em : (fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G) =
        lift ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp [MonObj.mul_comp]
    have eu : snd T (G ⊗ G) = lift (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp
    have k₁ : CechPic.pull ((fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G)).left (cls P hP) =
        evc hP ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [em]; rfl
    have k₂ : CechPic.pull (snd T (G ⊗ G)).left (cls P hP) =
        evc hP (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [evc, ← eu]
    have k₃ : evc hP (fst T (G ⊗ G) ≫ a) (snd T (G ⊗ G) ≫ snd G G) = 0 := by
      have e := congrArg (CechPic.pull (lift (snd T (G ⊗ G) ≫ snd G G) (fst T (G ⊗ G))).left)
        ((triv_ev_iff hP _ _).1 ha)
      rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
    rw [e₁, k₁, k₂, (isAdditive_iff hP).1 hadd, add_sub_cancel_right, k₃]
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, hz, map_zero]

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivial
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbDual

theorem memKL_of_triv_ev_left : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB →
    ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  intro K _ _ A B _ _ P L hA _ hD hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have hadd := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  obtain ⟨φ, hφ, -⟩ := hD.univ A (abelian₂ A L) hP hadd
  have hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ) :=
    (cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ
  have hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e₁ := congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e₁
    rw [← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]
    exact e₁
  have hD' : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

namespace Sys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}} {π : R →+* R₀}
  {s₀ : X₀ ⟶ Sp R₀}

def viaDR (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) :
    CoefMap (((RingHom.id R₀).comp (RingHom.id R₀)).comp π) (O (divided₂ hI) (s₀ ≫ spMap π)) (OAff s₀) :=
  ((redMor hI hk s₀).coef.comp (CoefMap.restrict (O (dp0 R₀) s₀) (IsTriv s₀).ι)).comp
    (ptCoef (F := OAff s₀) (fun U ↦ affPt s₀ U.unop) (fun U ↦ affPt_w s₀ U.unop)
      fun _ _ a ↦ affPt_res s₀ (leOfHom a.unop))

variable (S : Sys I π s₀) (hI : I ^ 2 = 0) (hk : RingHom.ker π = I)

def redTrans : ((S.coef hI).comp S.redO).G ⟶ (viaDR hI hk s₀).G where
  app U :=
    { φ := { (S.p U : S.F.obj U →+* Sec s₀ U.unop.1) with
        commutes' := fun r ↦ (S.semi U).map_algebraMap r }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := by
        refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_, fun n hn a ha ↦ ?_⟩
        · exact Ideal.mem_comap.2 (Ideal.mem_bot.2 ((S.ker U a).2 ha))
        · change (dp0 _).dpow n (S.p U a) = S.p U _
          rw [(S.ker U a).2 ha, dpow_eval_zero _ hn]
          exact ((S.ker U _).2 ((divided₂ (map_sq hI _)).dpow_mem hn ha)).symm
      pt := by
        change spMap (RingHom.id _) ≫ affPt s₀ U.unop = affPt s₀ U.unop ≫ 𝟙 X₀
        rw [Cris.spMap_id, Category.id_comp, Category.comp_id] }
  naturality U V a := Thick.hom_ext fun b ↦ S.nat a b

theorem redO_r (c : Cr hI π s₀) :
    S.redO.pull1 (S.r hI c) = cmpO s₀ (toH1O s₀ (rho hI hk s₀ c)) := by
  refine (CoefMap.pullCohomologyOne_comp _ _ c).symm.trans
    ((CoefMap.pullCohomologyOne_eq_of_natTrans _ (viaDR hI hk s₀) (S.redTrans hI hk) (fun _ _ ↦ rfl) c).trans ?_)
  rw [viaDR, CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp]
  rfl

end Sys

end GlobalTheory.LiftSys

namespace GlobalTheory.LiftSys

theorem Sys.mem_K_sup_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀,
      c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  intro R R₀ _ _ I hI π _ hk X₀ s₀ S hBC hF c
  have key : ∀ c, rho hI hk s₀ c ∈ F1 s₀ ↔ S.redO.pull1 (S.r hI c) = 0 := fun c ↦ by
    rw [Sys.redO_r S hI hk c]
    change toH1O s₀ (rho hI hk s₀ c) = 0 ↔ _
    exact ⟨fun h ↦ by rw [h, map_zero],
      fun h ↦ GlobalTheory.CechDR.cmpO_injective R₀ X₀ s₀ (h.trans (map_zero _).symm)⟩
  rw [key]
  constructor
  · intro h
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 h
    have h0 : S.r hI k = 0 := hk'
    rw [map_add, h0, zero_add]
    refine (key i).1 ?_
    rw [(hBC.2 i).2 hi]
    exact Submodule.zero_mem _
  · intro h
    obtain ⟨z, hz⟩ := H1.mk_surjective _ (S.r hI c)
    rw [← hz, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h
    obtain ⟨g₀, hg₀⟩ := h
    choose g hg using fun U ↦ S.surj U (g₀ U)
    let z' : Z1 S.F := z - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
    have hz' : S.IsIdealValuedLiftSystemCocycle z' := by
      intro U V a
      rw [← S.ker]
      have e := congrFun (congrFun (congrFun hg₀ U) V) a
      rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
      change g₀ V - mp (OAff s₀) a (g₀ U) = S.p V (z.1 U V a) at e
      change S.p V (z.1 U V a - (g V - mp S.F a (g U))) = 0
      rw [map_sub, map_sub, S.nat, hg, hg, ← e, sub_self]
    obtain ⟨c', hc', hrc'⟩ := hF z' hz'
    have hr : S.r hI (c - c') = 0 := by
      rw [map_sub, hrc', ← hz, map_sub, sub_sub_cancel]
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    exact Submodule.mem_sup.2 ⟨c - c', hr, c', hc', sub_add_cancel c c'⟩

end GlobalTheory.LiftSys
end
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.BotSmallDict.CosetCong

open GlobalTheory.BotClassDict GlobalTheory.BotFormula

variable {D : D7}

theorem hatId_mul {I : Ideal (𝓞 D.host.E)} {x y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) (hy : y ∈ OhE D) :
    x * y ∈ hatId D I := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, s * y, mul_mem hs hy, by ring⟩
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

def rho (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Lev.EAf D := (Lev.swapAE D).comp (toAfE D).toRingHom

theorem rho_finQ (z : Formalism.L2.Theta.AE D) : rho D (finQ D z) = toEAf D z := by
  change Lev.swapAE D (toAfE D (finQ D z)) = _
  rw [toAfE_finQ]
  rfl

theorem rho_int (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : rho D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ y ∈ OhE D := toAfE_int_iff y

theorem rho_bij : Function.Bijective (rho D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (toAfE D).bijective

theorem rho_inc (b : 𝓞 D.host.E) :
    rho D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Lev.EAf D) := by
  rw [← finQ_inclR, rho_finQ]
  rfl

theorem mem_map_iff {A R S : Type} [CommRing A] [CommRing R] [CommRing S] (ρ : R →+* S) (hρ : Function.Bijective ρ)
    (O : Subring R) (O' : Subring S) (hO : ∀ y, ρ y ∈ O' ↔ y ∈ O) (ι : A → R) (ι' : A →+* O') (hι : ∀ b, ρ (ι b) = ι' b)
    (I : Ideal A) (y : R) :
    (∃ h : ρ y ∈ O', (⟨ρ y, h⟩ : O') ∈ I.map ι') ↔ y ∈ AddSubgroup.closure {y | ∃ b ∈ I, ∃ s ∈ O, y = ι b * s} := by
  constructor
  · rintro ⟨h, hI⟩
    have key : ∀ s ∈ I.map ι', ∀ u ∈ O, ∀ y, ρ y = s.1 →
        y * u ∈ AddSubgroup.closure {y | ∃ b ∈ I, ∃ s ∈ O, y = ι b * s} := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem s hs =>
        obtain ⟨b, hb, rfl⟩ := hs
        intro u hu y hy
        rw [← hι] at hy
        rw [hρ.1 hy]
        exact AddSubgroup.subset_closure ⟨b, hb, u, hu, rfl⟩
      | zero =>
        intro u _ y hy
        rw [hρ.1 (hy.trans (map_zero ρ).symm), zero_mul]
        exact zero_mem _
      | add s t _ _ hs ht =>
        intro w hw y hy
        obtain ⟨u, hu⟩ := hρ.2 s.1
        obtain ⟨v, hv⟩ := hρ.2 t.1
        have : y = u + v := hρ.1 (by rw [hy, map_add, hu, hv]; rfl)
        rw [this, add_mul]
        exact add_mem (hs w hw u hu) (ht w hw v hv)
      | smul a t _ ht =>
        intro w hw y hy
        obtain ⟨u, hu⟩ := hρ.2 a.1
        obtain ⟨v, hv⟩ := hρ.2 t.1
        have : y = v * u := hρ.1 (by rw [hy, map_mul, hu, hv, mul_comm]; rfl)
        rw [this, mul_assoc]
        exact ht _ (mul_mem ((hO u).1 (hu ▸ a.2)) hw) v hv
    have := key _ hI 1 (one_mem _) y rfl
    rwa [mul_one] at this
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, s, hs, rfl⟩ := hz
      have h1 : ι' b * ⟨ρ s, (hO s).2 hs⟩ ∈ I.map ι' := Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
      rw [map_mul, hι]
      exact ⟨(ι' b * ⟨ρ s, (hO s).2 hs⟩).2, h1⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | add u v _ _ hu hv =>
      obtain ⟨h1, h2⟩ := hu
      obtain ⟨h3, h4⟩ := hv
      rw [map_add]
      exact ⟨add_mem h1 h3, add_mem h2 h4⟩
    | neg u _ hu =>
      obtain ⟨h1, h2⟩ := hu
      rw [map_neg]
      exact ⟨neg_mem h1, neg_mem h2⟩

theorem inId_rho (I : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (rho D y) ↔ y ∈ hatId D I :=
  mem_map_iff (rho D) rho_bij (OhE D) (Formalism.L2.Herm.intAf D.host.F D.host.E) rho_int (fun b : 𝓞 D.host.E => inc D (b : D.host.E))
    (Formalism.L2.DIV.oToS D.host.F D.host.E) rho_inc I y

theorem inId_iff (I : Ideal (𝓞 D.host.E)) (z : Formalism.L2.Theta.AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D z) ↔ finQ D z ∈ hatId D I := by
  rw [← rho_finQ, inId_rho]

theorem sgA_hatId {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) :
    sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s, Formalism.UG.P.csDual_sig_mem _ hs, ?_⟩
    rw [map_mul]
    rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem conj_idem {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (c : Formalism.L2.DIV.Pl D.host.E → ℕ)
    (he : IsIdemSum e P) : finQ D (cA D e) ∈ OhE D ∧ 1 - finQ D (cA D e) ∈ hatId D (D.host.conj • modul P c) := by
  obtain ⟨-, h1, t, ht, h2⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e P c he
  have hc : finQ D (cA D e) = sgA D (finQ D e) := finQ_sigR e
  have h3 : finQ D e ∈ OhE D := by
    rw [← rho_int, rho_finQ]
    exact h1
  have h4 : finQ D (1 - e) ∈ hatId D (modul P c) := by
    rw [← inId_iff, RingHom.map_sub, RingHom.map_one, ← h2]
    exact ⟨t.2, ht⟩
  rw [hc]
  refine ⟨Formalism.UG.P.csDual_sig_mem _ h3, ?_⟩
  have h5 := sgA_hatId h4
  rwa [map_sub, map_one, map_sub, map_one] at h5

theorem core {R : Type} [CommRing R] (O : Subring R) (J : AddSubgroup R) (hJ : ∀ x ∈ J, ∀ y ∈ O, x * y ∈ J)
    {n d o : ℕ} (ho : o + n = d) {a : R} (haO : a ∈ O) (ha : 1 - a ∈ J) (Y : Matrix (Fin d) (Fin n) R)
    (H : Matrix (Fin n) (Fin n) R) (hH : ∀ i j, H i j ∈ O)
    (hY : ∀ i j, Y i j - (if i.1 = o + j.1 then a else 0) ∈ J) :
    (∀ i j, (Y * H) i j - (if i.1 = o + j.1 then a else 0) ∈ J) ↔ ∀ i j, (H - 1) i j ∈ J := by
  let X : Matrix (Fin d) (Fin n) R := Matrix.of fun i j => if i.1 = o + j.1 then a else 0
  have hX : ∀ i j, X i j ∈ O := fun i j => by
    change (if i.1 = o + j.1 then a else 0) ∈ O
    split_ifs
    exacts [haO, zero_mem _]
  have hH1 : ∀ i j, (H - 1) i j ∈ O := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem (hH i j) ?_
    split_ifs
    exacts [one_mem _, zero_mem _]
  have e : Y * H - X = (Y - X) * H + X * (H - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one]
    abel
  have h1 : ∀ i j, ((Y - X) * H) i j ∈ J := fun i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => hJ _ (hY i l) _ (hH l j)
  have h2 : ∀ i j, ((Y * H) i j - (if i.1 = o + j.1 then a else 0) ∈ J) ↔ (X * (H - 1) : Matrix (Fin d) (Fin n) R) i j ∈ J := fun i j => by
    change (Y * H - X) i j ∈ J ↔ _
    rw [e, Matrix.add_apply]
    exact AddSubgroup.add_mem_cancel_left _ (h1 i j)
  simp only [h2]
  constructor
  · intro h i j
    have h3 := h ⟨o + i.1, by omega⟩ j
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h3
    · have h4 : X ⟨o + i.1, by omega⟩ i = a := if_pos rfl
      rw [h4] at h3
      have h5 : (H - 1) i j = (1 - a) * (H - 1) i j + a * (H - 1) i j := by ring
      rw [h5]
      exact add_mem (hJ _ ha _ (hH1 i j)) h3
    · intro l _ hl
      have h4 : X ⟨o + i.1, by omega⟩ l = 0 := if_neg fun h' => hl (Fin.ext (by simp only at h'; omega))
      rw [h4, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
  · intro h i j
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => by rw [mul_comm]; exact hJ _ (h l j) _ (hX i l)

theorem congOne_inv {I : Ideal (𝓞 D.host.E)} {N : ℕ} {k : Formalism.MainNotions.StandardLatticesGL3.GA D N} (hk : k ∈ GlobalTheory.NormSum.intG D N)
    (h : CongOne D I k) : CongOne D I k⁻¹ := by
  intro i j
  have e : (k⁻¹).1.1 - 1 = -((k.1.1 - 1) * (k⁻¹).1.1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, neg_sub, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  change ((k⁻¹).1.1 - 1) i j ∈ _
  rw [e, Matrix.neg_apply, Matrix.mul_apply]
  exact neg_mem (sum_mem fun l _ => hatId_mul (h i l) ((GlobalTheory.NormSum.mem_intG _).1 (inv_mem hk) l j).1)

theorem cosetFn_ne_zero {S T : HSp D} (a : Formalism.L2.Theta.AE D) (I : Ideal (𝓞 D.host.E)) (o : ℕ) (y : WO S T) :
    cosetFn a I (unitPt S T a o) y ≠ 0 ↔ IsHalf a y ∧
      ∀ i j, (y.map (finQ D)) i j - (if i.1 = o + j.1 then finQ D a else 0) ∈ hatId D I := by
  have : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (y i j - unitPt S T a o i j)) ↔
      (y.map (finQ D)) i j - (if i.1 = o + j.1 then finQ D a else 0) ∈ hatId D I := fun i j => by
    rw [inId_iff, map_sub, unitPt, apply_ite (finQ D), map_zero]
    rfl
  unfold cosetFn
  simp only [this]
  split_ifs with h
  · exact iff_of_true one_ne_zero h
  · exact iff_of_false (fun h' => h' rfl) h

theorem actO_inv_one (S T : HSp D) (g g' : Formalism.L2.Theta.GA D S) (y : WO S T) :
    actO S T g'⁻¹ 1 y = HMul.hMul (actO S T g⁻¹ 1 y : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.Theta.AE D)) (Formalism.L2.Theta.mt S (g⁻¹ * g')) := by
  unfold actO Formalism.L2.Theta.mt
  rw [inv_inv, inv_inv, Matrix.mul_assoc _ (matHom S g).1, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]

theorem coset_iff_congOne : ∀ {D : D7} (S T : HSp D), S.gram = 1 →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e P →
    ∀ o : ℕ, o + S.rank = T.rank → ∀ k ∈ GlobalTheory.NormSum.intG D S.rank, ∀ k' ∈ GlobalTheory.NormSum.intG D S.rank, ∀ g g' : Formalism.L2.Theta.GA D S,
    GlobalTheory.BotFormula.IsFinPt S g k → GlobalTheory.BotFormula.IsFinPt S g' k' → ∀ y : WO S T,
    cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g⁻¹ 1 y) ≠ 0 →
    (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g'⁻¹ 1 y) ≠ 0 ↔
      CongOne D (D.host.conj • modul P c) (k'⁻¹ * k)) := by
  intro D S T hG e P c he o ho k hk k' hk' g g' hg hg' y hy
  obtain ⟨h1, h2⟩ := conj_idem c he
  have hkk := mul_mem (inv_mem hk) hk'
  have hfin : finStd S hG (g⁻¹ * g') = k⁻¹ * k' := by
    rw [map_mul, map_inv, finStd_of_isFinPt S hG hg, finStd_of_isFinPt S hG hg']
  have hM : (Formalism.L2.Theta.mt S (g⁻¹ * g')).map (finQ D) = (k⁻¹ * k').1.1 := by
    rw [← hfin]
    rfl
  have hc : CongOne D (D.host.conj • modul P c) (k'⁻¹ * k) ↔ CongOne D (D.host.conj • modul P c) (k⁻¹ * k') := by
    constructor
    · intro h
      have := congOne_inv (mul_mem (inv_mem hk') hk) h
      rwa [mul_inv_rev, inv_inv] at this
    · intro h
      have := congOne_inv hkk h
      rwa [mul_inv_rev, inv_inv] at this
  rw [cosetFn_ne_zero] at hy
  rw [hc, cosetFn_ne_zero, actO_inv_one S T g g' y, Matrix.map_mul, hM,
    core (OhE D) (hatId D (D.host.conj • modul P c)) (fun x hx y hy => hatId_mul hx hy) ho h1 h2 _ _
      (fun i j => ((GlobalTheory.NormSum.mem_intG _).1 hkk i j).1) hy.2]
  refine and_iff_right fun i j => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy.1 i l]

end GlobalTheory.BotSmallDict.CosetCong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorEqOneOfCongruentOne
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead.CongOneChar

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem hat_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) :
    x ∈ hatId D J := by
  refine AddSubgroup.closure_mono ?_ hx
  rintro _ ⟨b, hb, t, ht, rfl⟩
  exact ⟨b, h hb, t, ht, rfl⟩

theorem hat_int {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) : x ∈ OhE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, -, t, ht, rfl⟩ := hy
    exact mul_mem (inc_int b) ht
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | neg a _ ha => exact neg_mem ha

theorem toE_surj (z : EAf D) : ∃ y, toE D y = z := by
  obtain ⟨w, -, hw⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj z
  exact ⟨finQ D w, by rw [toE_finQ, hw]⟩

theorem toE_inj : Function.Injective (toE D) := fun _ _ h =>
  (GlobalTheory.BotFormula.toAfE D).injective ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h)

theorem rho_one_add (Q : Formalism.L2.DIV.Pl D.host.E) {a b : Formalism.MainNotions.StandardLatticesGL3.AE D} (ha : a ∈ OhE D) (hb : b ∈ OhE D)
    (hu : 1 + a * b ∈ OhE D) (h0 : rho Q ⟨a, ha⟩ * rho Q ⟨b, hb⟩ = 0) : rho Q ⟨_, hu⟩ = 1 := by
  have e : (⟨_, hu⟩ : OhE D) = 1 + ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
  rw [e, RingHom.map_add, RingHom.map_mul, h0, RingHom.map_one, add_zero]

theorem exists_inv {u : Formalism.MainNotions.StandardLatticesGL3.AE D} (hu : u ∈ OhE D) (h : ∀ Q : Formalism.L2.DIV.Pl D.host.E, rho Q ⟨u, hu⟩ ≠ 0) :
    ∃ v ∈ OhE D, u * v = 1 := by
  have hU : IsUnit (⟨toE D u, (toE_int_iff u).2 hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) :=
    Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm _ fun Q => h Q
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  obtain ⟨v, hv⟩ := toE_surj (w : EAf D)
  refine ⟨v, (toE_int_iff v).1 (hv ▸ w.2), toE_inj ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, hv]
  exact congrArg Subtype.val hw

set_option maxHeartbeats 1000000 in

theorem unitChar_cong : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {k : ℕ} (P : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, (P - 1) i j ∈ hatId D 𝔪) →
  unitChar ν e (P.map (toE D)) = 1 := by
  intro D e 𝔪 hG ν hK k P hP
  have hm1 := one_sub_eps_mod hG
  obtain ⟨S, c, he, hc, h𝔪, -⟩ := hG
  have hO := eps_int he
  have h2 := eps_conj he
  have hte := toE_finQ e
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => by
    have h1 : (1 : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h3 := add_mem (hat_int (hP i j)) h1
    rwa [Matrix.sub_apply, sub_add_cancel] at h3
  have hm := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of P hPO hP
  have hdet : (P.map (toE D)).det = toE D P.det := (RingHom.map_det (toE D) _).symm
  have hmO := hat_int hm
  have huO : 1 + finQ D e * (P.det - 1) ∈ OhE D := add_mem (one_mem _) (mul_mem hO hmO)
  obtain ⟨v, hvO, huv⟩ := exists_inv huO fun Q => by
    have := Q.isPrime
    have h0 : rho Q ⟨_, hO⟩ * rho Q ⟨_, hmO⟩ = 0 := by
      by_cases hQ : Q ∈ S
      · have hle : 𝔪 ≤ Q.asIdeal := by
          rw [h𝔪]
          exact (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => w.asIdeal ^ c w) hQ)).trans
            (Ideal.pow_le_self (hc Q hQ).ne')
        obtain ⟨_, h5⟩ := rho_hat Q (hat_mono hle hm)
        rw [h5, mul_zero]
      · have h5 : rho Q ⟨_, hO⟩ = Formalism.L2.DIV.resS D.host.F Q ⟨_, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he⟩ :=
          congrArg (Formalism.L2.DIV.resS D.host.F Q) (Subtype.ext hte)
        rw [h5, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.res_off he _ hQ, zero_mul]
    have h6 : rho Q ⟨_, huO⟩ = 1 := rho_one_add Q hO hmO huO h0
    rw [h6]
    exact one_ne_zero
  have hm' := hat_mul hm (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1)
  rw [map_sub, map_one] at hm'
  have hm'' := GlobalTheory.FunObj.StdDatum.mul_mem_hatId hO hm'
  generalize finQ D e = ε at hO h2 hte huO huv hm''
  generalize P.det = d at hdet huO huv hm''
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := ⟨_, _, huv, by rw [mul_comm, huv]⟩
  have hyv : (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 + ε * (d - 1) := rfl
  have hyi : ((y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = v := rfl
  obtain ⟨x, hx, hx1, hx2⟩ := exists_finIdl y
  have hU : IsUnitDet e (P.map (toE D)) x := by
    refine ⟨hx.1, ?_, ?_⟩
    · rw [hx1, show (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * d by rw [hyv]; ring, hdet, RingHom.map_add, RingHom.map_sub,
        RingHom.map_mul, RingHom.map_one, hte]
    · rw [hx2, toE_int_iff, hyi]
      exact hvO
  have hν : ν x = 1 := hK x y hx ⟨huO, hvO⟩ (by
    convert hm'' using 1
    rw [hyv]
    linear_combination (d - 1) * h2)
  rw [unitChar_eq ν e _ hU, hν, inv_one, Circle.coe_one]

end GlobalTheory.StdRead.CongOneChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePartIdempotentBlendMemLatticeStabil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StabMove

theorem mul_entries_mem {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) (hN : ∀ i j, N i j ∈ R) :
    ∀ i j, (M * N) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem R fun k _ => R.mul_mem (hM i k) (hN k j)

def lift {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩

theorem lift_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) :
    (lift R M hM).map R.subtype = M := by
  ext i j; rfl

def liftGL {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) : GL (Fin n) R where
  val := lift R u.val hu
  inv := lift R (u⁻¹).val hu'
  val_inv := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.inv_mul

theorem liftGL_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) :
    Formalism.UG.bc R.subtype (liftGL R u hu hu') = u := by
  ext i j; rfl

end GlobalTheory.StabMove

open GlobalTheory.StabMove in
theorem GlobalTheory.StabMove.finE_mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  intro D V g β₀ β₁ h₀ h₁ ε φ hε hφ hg hg'
  set R := Formalism.L2.Herm.intAf D.host.F D.host.E with hR
  have hcF : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D), (∀ i j, M i j ∈ R) →
      ∀ i j, ((M.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro M hM i j
    exact GlobalTheory.LevSplit.sigR_int (hM j i)
  have hshape : ∀ (a b : GL (Fin V.rank) (Lev.EAf D)), (∀ i j, a.val i j ∈ R ∧ (a⁻¹).val i j ∈ R) →
      (∀ i j, b.val i j ∈ R ∧ (b⁻¹).val i j ∈ R) →
      ∀ i j, ((1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
        ε • (a * b⁻¹).val + φ • ((b * a⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro a b ha hb i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine R.add_mem (R.add_mem (R.mul_mem ?_ ?_) (R.mul_mem hε ?_)) (R.mul_mem hφ ?_)
    · exact R.sub_mem (R.sub_mem R.one_mem hε) hφ
    · rw [Matrix.one_apply]; split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).2) i j
    · apply hcF
      rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (hb i j).1) (fun i j => (ha i j).2)
  have hE : ∀ i j, (Formalism.IndefR.Lev.finE V g).val i j ∈ R := by
    have : (Formalism.IndefR.Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl
    rw [this, hg]; exact hshape β₁ β₀ h₁ h₀
  have hE' : ∀ i j, ((Formalism.IndefR.Lev.finE V g)⁻¹).val i j ∈ R := by
    have : ((Formalism.IndefR.Lev.finE V g)⁻¹).val = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
      rw [← map_inv]; rfl
    rw [this, hg']; exact hshape β₀ β₁ h₀ h₁
  set u := β₁⁻¹ * Formalism.IndefR.Lev.finE V g * β₁ with hu
  have hu1 : ∀ i j, u.val i j ∈ R := by
    intro i j
    simp only [hu, Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE) (fun i j => (h₁ i j).1) i j
  have hu2 : ∀ i j, (u⁻¹).val i j ∈ R := by
    intro i j
    have : u⁻¹ = β₁⁻¹ * (Formalism.IndefR.Lev.finE V g)⁻¹ * β₁ := by
      simp only [hu, mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    simp only [Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE') (fun i j => (h₁ i j).1) i j
  refine ⟨liftGL R u hu1 hu2, ?_⟩
  show MulAut.conj β₁ (Formalism.UG.bc R.subtype (liftGL R u hu1 hu2)) = _
  rw [liftGL_map, MulAut.conj_apply, hu]
  group
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodingerStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_operator_commutes_schrodinger : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  first | exact @GlobalTheory.AdelicSchur.schur | exact GlobalTheory.AdelicSchur.schur | (intros; apply GlobalTheory.AdelicSchur.schur <;> assumption)
end


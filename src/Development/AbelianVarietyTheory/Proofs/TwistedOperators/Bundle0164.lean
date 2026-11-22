import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalOfRatAt
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.Arith

namespace GlobalTheory.LiftRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

end Abstract

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (A : FormsL LL Ks WL W G)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Package

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem j_eq_sum (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.FW i).j σ y = ∑ k, σ (y k) • (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k) := by
  conv_lhs => rw [← (Pi.basisFun D.what₂.LL (Fin (R.nW i))).sum_repr y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, Pi.basisFun_repr]

theorem span_basis (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Submodule.span ℂ (Set.range fun k => (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k)) = ⊤ := by
  refine top_le_iff.1 ((hU i σ).2.1.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨y, rfl⟩
  rw [j_eq_sum]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Package

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

end GlobalTheory.LiftRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.TwistValues

section General

variable {L : Type} [Field L] [NumberField L]

theorem locK_int_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hP : P ∈ S) (b : 𝓞 L) (k : Lˣ) (hk : (k : L) = b) : χ.locK P k ∈ Λ := by
  classical
  have hb : b ≠ 0 := by
    rintro rfl
    exact k.ne_zero hk
  have h0 : P.intValuation b ≠ 0 := P.intValuation_ne_zero b hb
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation b = WithZero.exp (-(n : ℤ)) := by
    have h1 := P.intValuation_le_one b
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    refine ⟨(-WithZero.log (P.intValuation b)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => n + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have h1 : P.intValuation (a - b) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    have h1 := ha P hP
    rw [if_pos rfl] at h1
    exact (P.intValuation_le_pow_iff_mem _ _).2 h1
  have h2 : P.intValuation a = P.intValuation b := by
    refine Valuation.map_eq_of_sub_lt _ (h1.trans_lt ?_)
    rw [hn, WithZero.exp_lt_exp]
    push_cast
    omega
  have ha0 : (a : L) ≠ 0 := by
    intro h
    have h3 : a = 0 := by exact_mod_cast h
    rw [h3, map_zero] at h2
    exact h0 h2.symm
  have hmem : χ.locK P (Units.mk0 _ ha0) ∈ Λ := by
    have h := TypeValues.productRule χ S hu (Units.mk0 _ ha0)
    rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => TypeValues.locK_eq_one (ht v) _ a rfl (by
      have h1 := ha v hvS
      rw [if_neg hvP] at h1
      exact Ideal.pow_le_self (Nat.succ_ne_zero n) h1))] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
    exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _
  have hval : ∀ z : L, Valued.v (algebraMap L (P.adicCompletion L) z) = P.valuation L z :=
    fun z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P z
  have hint : ∀ z : 𝓞 L, P.valuation L (z : L) = P.intValuation z := fun z => P.valuation_of_algebraMap z
  have h4 : χ.locK P (Units.mk0 _ ha0 * k⁻¹) = 1 := by
    have e : ((atFin P (Units.mk0 _ ha0 * k⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
        algebraMap L (P.adicCompletion L) ((a : L) * (b : L)⁻¹) := by
      rw [← hk, ← Units.val_inv_eq_inv_val]
      rfl
    refine ht P _ ?_ ?_
    · unfold IsUnitAt
      rw [e, hval, map_mul, map_inv₀, hint, hint, h2, mul_inv_cancel₀ h0]
    · have e' : (a : L) * (b : L)⁻¹ - 1 = ((a - b : 𝓞 L) : L) * (b : L)⁻¹ := by
        have : (b : L) ≠ 0 := hk ▸ k.ne_zero
        push_cast
        field_simp
      rw [e, ← map_one (algebraMap L (P.adicCompletion L)), ← map_sub, hval, e', map_mul, map_inv₀, hint, hint, hn]
      refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
      rw [← WithZero.exp_neg, ← WithZero.exp_add]
      congr 1
      push_cast
      ring
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4 ▸ hmem

theorem locK_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ∈ Λ := by
  by_cases hP : P ∈ S
  · obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
    have hb0 : (b : L) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
    have h1 := locK_int_mem χ Λ S ht hi hu hv hP b (Units.mk0 _ hb0) rfl
    have h2 := locK_int_mem χ Λ S ht hi hu hv hP a (k * Units.mk0 _ hb0) (by
      rw [Units.val_mul, ← e]
      exact div_mul_cancel₀ _ hb0)
    rw [map_mul] at h2
    exact (mul_mem_cancel_right h1).1 h2
  · have h : χ.locK P k = χ.val P ^ ordF P k := GlobalTheory.Mem.Chr.CharModel.locK_unr (F := L) ⟨χ.1, χ.2⟩ (hu P hP) k
    rw [h]
    exact Λ.zpow_mem (hv P hP) _

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
  Formalism.L2.Col GlobalTheory.RationalValues
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_mem {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) {n : ℕ} (hn : 0 < n)
    (ho : χ.OrderDvd n) (M : Subfield ℂ) (hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ M) (x : (AE D)ˣ) : ((c x : Circle) : ℂ) ∈ M := by
  have h1 : ∀ x, c x ^ n = 1 := HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨y, hy⟩ := IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn (a x) (ha x).2
  rw [hab x, map_mul, ← hy, map_pow, h1, one_mul]
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j j1 j2 (PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom (b x))
  rw [hprod (b x) (hb x).1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => hM P _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem xiH_locK_mem (hL : R.toLevCh.Is A.μ0) (hon : R.fam_pl_onto) (hmu : R.fam_muVal)
    (hok : ∀ t P, P ∈ A.ok t ↔ Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))))
    (i : Fin D.R.m) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ R.Q t ∪ R.Q A.μ0
  have hQ : ∀ v ∈ R.Q t, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).UnrAt v := fun v hv => by
    by_contra hn
    rcases (hL.Q_ram t v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : (((R.xiH t).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm (hL.xi_triv t) (hu v hv) hc, Units.val_one]
      show (((R.xiH t).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hon v (hs _ hS)
      have h1 : (R.C.mu0 i * R.xiH t).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i t P ((hok t P).2 (hs _ fun w hw => hw.elim (hS w) (hQ w)))⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i A.μ0 P ((hok A.μ0 P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact locK_mem (R.xiH t) _ (T ∪ T.image conjPrime₂) (hL.xi_tame t) (TypeValues.inf_eq_one _ hn ho) hu hv PP k

theorem xiVal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → GlobalTheory.TwistField.XiVal R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF t x
  obtain ⟨_, _, _, hT⟩ := hF.tie
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact char_mem _ _ (hL.xi t) hn ho _
    (xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t) x

end GlobalTheory.TwistValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLevelDatumEqFunctionOfResidueReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

variable {D : D7}

theorem isUnit_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    {x : v.adicCompletionIntegers D.host.F} (h : IsUnit (r x)) : IsUnit x := by
  by_contra hx
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx
  have h2 : r x = 0 := (hr.2.1 x).2 h1
  rw [h2] at h
  exact not_isUnit_zero h

theorem redRel_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    (x : v.adicCompletionIntegers D.host.F) : RedRel φ PP (x : Fv D.host.F v) (r x) :=
  (hr.2.2.1 _ _).2 ⟨x.2, rfl⟩

set_option maxHeartbeats 1000000 in

theorem locDatum_eq_viaRed : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  intro D v φ PP r hr a b t ht L H c J lam hJ mu χ hmu Y
  have hinl : ∀ (i : Fin a) (j : Fin a), rowsTB ht Y (Sum.inl i) j = Y ⟨i.val, by omega⟩ j := fun _ _ => rfl
  have hinr : ∀ (i : Fin t) (j : Fin a), rowsTB ht Y (Sum.inr i) j = Y ⟨a + i.val, by omega⟩ j := fun _ _ => rfl

  unfold viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dif_neg hint]
    unfold localNewformFunction
    rw [dif_neg]
    rintro ⟨⟨k, hk⟩, hbot⟩
    apply hint
    intro i j
    by_cases hi : i.val < a
    · have h1 := congrFun (congrFun hk ⟨i.val, hi⟩) j
      rw [Matrix.submatrix_apply, hinl] at h1
      simp only [Matrix.map_apply, id] at h1
      rw [show i = ⟨i.val, by omega⟩ from rfl, ← h1]
      exact ((k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)) ⟨i.val, hi⟩ j |>.2
    · have h1 := (hbot ⟨i.val - a, by omega⟩ j).1
      rw [hinr] at h1
      have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
      rwa [this] at h1
  rw [dif_pos hint]

  set y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) := Matrix.of fun i j => r ⟨Y i j, hint i j⟩ with hy
  let K : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y ⟨i.val, by omega⟩ j, hint _ _⟩
  have hKr : K.map r = topL a y := by
    ext i j
    simp only [topL, Matrix.map_apply]
    rw [dif_pos ⟨by omega, j.2⟩]
    rfl

  have hKk : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F),
      ((k : Matrix (Fin a) (Fin a) _).map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) =
        (rowsTB ht Y).submatrix Sum.inl id) → (k : Matrix (Fin a) (Fin a) _) = K := by
    intro k hk
    funext i j
    apply Subtype.ext
    have h1 := congrFun (congrFun hk i) j
    rw [Matrix.submatrix_apply, hinl] at h1
    exact h1

  have hred : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F), (k : Matrix (Fin a) (Fin a) _) = K →
      ((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      ∀ i j, RedRel φ PP (((k : Matrix (Fin a) (Fin a) _) i j : v.adicCompletionIntegers D.host.F) : Fv D.host.F v)
        (((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) i j) := by
    intro k hk
    refine ⟨?_, fun i j => redRel_of_isRedMap hr _⟩
    rw [← hKr, ← hk]
    rfl

  unfold gLoc localNewformFunction
  split_ifs with hP hG hG
  ·
    have hk0 := hP.1.choose_spec
    have hg0 := hG.2.choose_spec
    generalize hP.1.choose = k₀ at hk0 ⊢
    obtain ⟨k, hkJ⟩ := k₀
    have hK := hKk k hk0
    obtain ⟨hm, hrr⟩ := hred k hK
    have hkg : Matrix.GeneralLinearGroup.map r k = hG.2.choose := Units.ext (hm.trans hg0.1.symm)
    have hlam := (hJ _ _ hrr).2 hkJ
    rw [hkg, Formalism.L2.DIV.extendOne_of_mem _ hg0.2.2] at hlam
    have hdet : RedRel φ PP ((Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom
        (Matrix.GeneralLinearGroup.det k) : (Fv D.host.F v)ˣ) : Fv D.host.F v)
          ((Matrix.GeneralLinearGroup.det hG.2.choose : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) := by
      have e2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map r k) : (Formalism.L2.DIV.kP PP)ˣ) :
          Formalism.L2.DIV.kP PP) = r ((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers D.host.F)ˣ) :
            v.adicCompletionIntegers D.host.F) := by
        exact (RingHom.map_det r (k : Matrix (Fin a) (Fin a) _)).symm
      rw [← hkg, e2]
      exact redRel_of_isRedMap hr _
    rw [hlam, hmu _ _ hdet]
    push_cast
    rfl
  ·
    exfalso
    apply hG
    obtain ⟨⟨⟨k, hkJ⟩, hk⟩, hbot⟩ := hP
    have hK := hKk k hk
    obtain ⟨hm, hrr⟩ := hred k hK
    have hJk := ((hJ k _ hrr).1.1 hkJ)
    refine ⟨?_, Matrix.GeneralLinearGroup.map r k, hm, hJk⟩
    intro i j hi hj
    have h1 := hbot ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩
    rw [hinr] at h1
    have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
    rw [this] at h1
    exact (hr.2.1 ⟨Y i ⟨j.val, hj⟩, hint _ _⟩).2 h1.2
  ·
    exfalso
    apply hP
    obtain ⟨hlow, g, hg, hgT, hgH⟩ := hG
    have hdet : IsUnit K.det := by
      apply isUnit_of_isRedMap hr
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hKr, ← hg]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    let k : GL (Fin a) (v.adicCompletionIntegers D.host.F) := ((Matrix.isUnit_iff_isUnit_det K).2 hdet).unit
    have hkK : (k : Matrix (Fin a) (Fin a) _) = K := rfl
    obtain ⟨hm, hrr⟩ := hred k hkK
    have hkg : Matrix.GeneralLinearGroup.map r k = g := Units.ext (hm.trans hg.symm)
    have hkJ : k ∈ J := (hJ k _ hrr).1.2 (hkg ▸ ⟨hgT, hgH⟩)
    refine ⟨⟨⟨k, hkJ⟩, ?_⟩, ?_⟩
    · funext i j
      rfl
    · intro i j
      rw [hinr]
      refine ⟨hint _ _, (hr.2.1 ⟨Y _ j, hint _ _⟩).1 ?_⟩
      exact hlow ⟨a + i.val, by omega⟩ j (by simp) j.2
  · rfl

end GlobalTheory.StepVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.StabLatInv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem intGL_mulVec_mem (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : ∀ i, x i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) :
    (intGL F E n y).val.mulVec x i ∈ Formalism.L2.Herm.intAf F E := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => mul_mem (y.val i j).2 (hx j)

theorem isFrame_mul_of_mem_St (β k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hk : k ∈ St β) : IsFrame (k * β) Λ := by
  obtain ⟨y, hy⟩ := hk
  have e : k * β = β * intGL F E n y := by
    rw [← hy]
    change β * intGL F E n y * β⁻¹ * β = _
    rw [inv_mul_cancel_right]
  intro x
  rw [hβ x, e, mul_inv_rev, ← map_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · exact intGL_mulVec_mem y⁻¹ _
  · intro h
    have h2 := intGL_mulVec_mem y _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2

end General

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh u
  have hS' := isFrame_mul_of_mem_St βS _ ΛS hS hg
  have hT' := isFrame_mul_of_mem_St βT _ ΛT hT hh
  have eS : (finE S g * βS).val = (Formalism.L2.Theta.mt S g).map (toEAf D) * βS.val := rfl
  have eT : (finE T h * βT).val = (Formalism.L2.Theta.mt T h).map (toEAf D) * βT.val := rfl
  constructor
  · exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS hS' hT hT' eS eT u
  · intro hu
    have h1 := GlobalTheory.AdelicLatMove.actO_mem_latO S T g⁻¹ h⁻¹ ΛS ΛS ΛT ΛT _ βS _ βT hS' hS hT' hT
      (GlobalTheory.AdelicLatMove.frame_inv S g _ _ eS) (GlobalTheory.AdelicLatMove.frame_inv T h _ _ eT) _ hu
    have h2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at h2
    rwa [h2] at h1

end GlobalTheory.StabLatInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemUnder

theorem under_eq_of_isIdemAt : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), Formalism.L2.NTheta.IsIdemAt e PP → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → PP.under (𝓞 D.host.F) = v := by
  intro D e PP v ε he hv hsum

  obtain ⟨hee, hec, -⟩ := he.1
  have hfix : e * algebraMap (AF D.host.F) (AE D) ε = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hone : Φ e PP = 1 := (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he).2.1
  by_contra hne
  have hzero := (GlobalTheory.IdemSupport.place_comp hΦ hv).2.2 PP hne
  have hcomp := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (algebraMap (AF D.host.F) (AE D) ε) PP
  rw [hfix, hzero, mul_zero, hone] at hcomp
  exact one_ne_zero hcomp

end GlobalTheory.IdemUnder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTensor_vacuum_eq_smul_basePoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∃ c : ℂ, f = c • f₀ := by
  first | exact @GlobalTheory.VacuumLine.eq_smul_base | exact GlobalTheory.VacuumLine.eq_smul_base | (intros; apply GlobalTheory.VacuumLine.eq_smul_base <;> assumption)
end


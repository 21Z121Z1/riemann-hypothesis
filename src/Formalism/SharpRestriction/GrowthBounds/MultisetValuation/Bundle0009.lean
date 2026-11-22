import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelSumOfClassData
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GShiftRowGenMonomial
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelExpansionOfRestrictions
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def RestSExp (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (Ph : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)),
    Simeq p Ph (∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      ThZ B K' vp (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestSInt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' r0 r1 : ℕ) (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U))

def RestSExpA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (j : ℕ) (Ph : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)),
    Simeq p Ph (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

def RestSIntA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ (j : ℕ) (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)))

section Formal

variable {p : ℕ} [hp : Fact p.Prime]

theorem sSer_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (e : Fin n') (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (sSer p K' e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : Zidx n' r0 r1 →₀ ℕ).degree + 1),
    if (0 : Zidx n' r0 r1 →₀ ℕ) = Finsupp.single (posSub e (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhS_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (u : Fin n' → K') :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p K' u) = 0 := by
  unfold hhS
  simp only [map_sum, map_mul, sSer_const, mul_zero, Finset.sum_const_zero]

theorem coordZ_const {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  simp only [coordZ, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZ_mul {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (f g : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K') :
    ThZ B K' vp (f * g) = ThZ B K' vp f * ThZ B K' vp g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZ_const B K' vp)) f g

theorem map_map_tower {ι : Type} (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (f : MvPowerSeries ι (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) f) =
      MvPowerSeries.map (algebraMap (K0 p) K') f := by
  rw [IsScalarTower.algebraMap_eq (K0 p) K1 K', MvPowerSeries.map_comp]
  rfl

theorem atPi_mul {σ R : Type} [CommRing R] (vp : R) (f g : MvPowerSeries σ R) :
    atPi vp (f * g) = atPi vp f * atPi vp g := by
  classical
  ext n
  show vp ^ n.degree * MvPowerSeries.coeff n (f * g) = MvPowerSeries.coeff n (atPi vp f * atPi vp g)
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  show _ = (vp ^ x.1.degree * MvPowerSeries.coeff x.1 f) * (vp ^ x.2.degree * MvPowerSeries.coeff x.2 g)
  rw [← hx', map_add, pow_add]
  ring

theorem exp_change {ι : Type} (K' : Type) [Field K'] [Algebra (K0 p) K'] (c : K') (hh hh' G : MvPowerSeries ι K')
    (h0 : MvPowerSeries.constantCoeff hh = 0) (h0' : MvPowerSeries.constantCoeff hh' = 0)
    (hE : hh' = hh + MvPowerSeries.C (p : K') * G) :
    expK (-(MvPowerSeries.C (c / (p : K')) * hh)) =
      expK (-(MvPowerSeries.C (c / (p : K')) * hh')) * expK (MvPowerSeries.C c * G) := by
  have := charZero_K' p K'
  have hp0 := pK'_ne p K'
  have hG : MvPowerSeries.constantCoeff G = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hE
    rw [map_add, map_mul, h0, h0', zero_add, MvPowerSeries.constantCoeff_C] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hp0
    · exact h
  rw [← expK_add (by rw [map_neg, map_mul, h0', mul_zero, neg_zero]) (by rw [map_mul, hG, mul_zero])]
  congr 1
  have e : (MvPowerSeries.C (c / (p : K')) : MvPowerSeries ι K') * MvPowerSeries.C (p : K') = MvPowerSeries.C c := by
    rw [← map_mul, div_mul_cancel₀ _ hp0]
  rw [hE, mul_add, ← mul_assoc, e]
  ring

end Formal

theorem SConcl_of {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (hD : DworkLemma p) (hE : RestSExp p) (hI : RestSInt p)
    {n' r0 r1 : ℕ} (h2 : 2 ≤ n') (hev : Even n') (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1]
    (R1 : Subring K1) (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1)
    (hK : ExtensionLocalCondition p K1 R1 be Th) : SConcl B K1 R1 Th := by
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hK
  intro K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨u, hu, V, hV, hEq⟩ := hE h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' vp hvp
  refine ⟨u, fun s => hRp (hu s), fun hh' h0' hG => ?_⟩
  obtain ⟨G, hG, hhE⟩ := hG
  have hW := hI n' r0 r1 B K1 R1 U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') Th) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hh')) *
        (expK (MvPowerSeries.C (vp ^ (p + 1)) * G) * V * ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U)) := by
    rw [hTh, map_mul, map_map_tower, ThZ_mul, hEq,
      exp_change K' (vp ^ (p + 1)) (hhS p K' u) hh' G (hhS_const K' u) h0' hhE]
    ring
  rw [e1]
  exact inClass_of_exp (pK'_ne p K') hc hh' h0' (IntR_mul (IntR_mul (IntR_expK hc hG) (IntR_mono hRp hV)) hW)

theorem kernel_expansion_of_restrictions (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExp p) (hI : RestSInt p) : Conclusion1 D X Y := by
  intro v j hj La La' h1 h2 φ
  exact SConcl_of (X.std v).five_le (hA.1 p) hE hI (X.std v).two_le (X.std v).even (X.om v) Y.Kc Y.Oc Y.be _
    (hA.2.1 v j hj La La' h1 h2 φ)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem vt_nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  exact Int.toNat_le_toNat (by have := h hab; omega)

theorem vt_deltaLTw_le (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    deltaLTw O Kf m lam g ≤ nablaLTw O Kf m lam g := by
  unfold deltaLTw nablaLTw
  apply Submodule.map_mono
  unfold deltaL nablaL
  apply Submodule.comap_mono
  apply Submodule.map_mono
  exact weylLeDual O (m + 1) (m + 1) le_rfl (nuOf lam) (vt_nuOf_antitone hlam)

theorem lowest_invariant_le_delta {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    Dl0 O m lam (colSpan O g) ≤ deltaLTw O Kf m lam g := by
  unfold Dl0
  rw [if_pos hlam]
  exact iInf₂_le g ⟨hg, rfl⟩

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

def vt_G (P : Places p O Kf) : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := PEmpty
  lev := fun x => x.elim
  e := 0

theorem vt_HtenW_le (P : Places p O Kf) (v : Fin P.nV) (Lv : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
    (hLv : IsLattice (P.W v) Lv) :
    ∀ z ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val Lv), z ∈ Vsp Kf (P.lam0 v) := by
  obtain ⟨g, hg, rfl⟩ := hLv
  have hle : HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g)) ≤
      (Vsp Kf (P.lam0 v)).restrictScalars O := by
    unfold HtenW tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨F, fun s => ?_, rfl⟩
    have hanti := kp_lamAt_antitone (P.lam0 v) (P.dom v) s
    beta_reduce
    rw [if_pos hanti]
    have h1 := hF s
    beta_reduce at h1
    have e : extO O (P.ι v) (P.σ v) s.val (colSpan (P.W v) g) = colSpan O (la_tw (P.ι v) (P.σ v) s.val g) :=
      la_extO_G (vt_G P) v s.val g
    rw [e] at h1
    have hd := la_tw_det (P.ι v) (P.σ v) s.val g hg
    exact la_nablaLTw_le _ _ _ hd _ (vt_deltaLTw_le O Kf _ _ hanti _ (lowest_invariant_le_delta _ _ hanti _ hd h1))
  exact fun z hz => hle hz

theorem vt_HtupW_le (P : Places p O Kf) (L : P.Tup) (hL : P.IsLatTup L) : ∀ z ∈ P.HtupW L, z ∈ P.Vtup := by
  have hle : P.HtupW L ≤ P.Vtup.restrictScalars O := by
    unfold Places.HtupW Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, fun v => vt_HtenW_le P v (L v) (hL v) _ (hF v), rfl⟩
  exact fun z hz => hle hz

end Formalism.MainNotions.FormalGroupSystem.Pf

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem vt_FQ {p : ℕ} [Fact p.Prime] (X : Sys p) {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j)
    (L : (X.Pj j).Tup) : F c L ∈ (X.Pj j).Vtup := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    have h := (mem_Int_iff X j x).1 hx
    by_cases hL : (X.Pj j).IsLatTup L
    · exact vt_HtupW_le (X.Pj j) L hL _ (h.1 c L hL)
    · rw [h.2.1 c L hL]; exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmPinvOfPlace
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_pinv_of_eO (Y : Pend X) (he : 0 < X.eO) : (p : Y.Kc)⁻¹ ∉ Y.Oc := by
  intro hmem
  have hinj := algebraMap_inj Y he
  have hpO : (p : X.G.O) ≠ 0 := fun h0 =>
    pow_ne_zero _ X.unif.ne_zero (X.eO_spec.eq_zero_iff.mp h0)
  have hpK : (p : X.G.Kf) ≠ 0 := by
    have := (map_ne_zero_iff _ hinj).mpr hpO
    rwa [map_natCast] at this
  have h1 : algebraMap X.G.Kf Y.Kc ((p : X.G.Kf)⁻¹) ∈ Y.Oc := by
    rwa [map_inv₀, map_natCast]
  obtain ⟨a, ha⟩ := (mem_intK (X := X)).mp ((Y.Oc_K _).mp h1)

  have h1eq : (p : X.G.O) * a = 1 := hinj (by
    rw [map_mul, ha, map_natCast, mul_inv_cancel₀ hpK, map_one])
  have hpu : IsUnit (p : X.G.O) := IsUnit.of_mul_eq_one _ h1eq
  exact X.unif.not_isUnit
    ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp he)).mp (X.eO_spec.isUnit_iff.mp hpu))

theorem nm_pinv_of_place (Y : Pend X) (v : X.Pl) : (p : Y.Kc)⁻¹ ∉ Y.Oc :=
  nm_pinv_of_eO Y (eO_pos X v)

theorem nm_hyp (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : nm_Hyp Y.Oc p :=
  ⟨hp.out.one_lt, Y.Oc_val, Y.Oc_rank1, h⟩

theorem nm_ext (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra Y.Kc K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ‖(p : K')‖ = (p : ℝ)⁻¹ ∧ (∀ x : Y.Kc, ‖algebraMap Y.Kc K' x‖ ≤ 1 ↔ x ∈ Y.Oc) ∧
      ∃ vp : K', vp ^ (p ^ 2 - 1) = (p : K') := by
  have hH := nm_hyp Y h
  have hc : 1 < nm_abs hH ((p : Y.Kc)⁻¹) := by
    rw [map_inv₀]
    show 1 < (nm_N Y.Oc p (p : Y.Kc))⁻¹
    rw [nm_N_p hH, inv_inv]
    exact nm_pR hH
  obtain ⟨K', i1, i2, hu, hac, hn⟩ :=
    nm_extG (nm_abs hH) (fun x y => nm_N_add hH x y) ((p : Y.Kc)⁻¹) hc
  refine ⟨K', i1, i2, hu, hac, ?_, ?_, ?_⟩
  · have := hn (p : Y.Kc)
    rw [map_natCast] at this
    exact this.trans (nm_N_p hH)
  · intro x
    rw [hn x]
    exact nm_N_le_one hH x
  · have h2 : 2 ≤ p := hp.out.two_le
    have hpos : 0 < p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    exact IsAlgClosed.exists_pow_nat_eq (p : K') hpos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem tm_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  have hres := (P.setting v).res_card
  have hfin : Finite (P.W v ⧸ Ideal.span {(p : P.W v)}) := by
    apply Nat.finite_of_card_ne_zero
    rw [hres]
    exact pow_ne_zero _ (P.setting v).prime.ne_zero
  exact ef_edges_finite_gen p (P.n' v) i (P.m + 1) hfin L

def tmE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (tm_fin P v i L).toFinset

theorem tm_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ tmE P v i (L v), F (Function.update L v L'') := by
  show (∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
      (_ : L'' ∈ {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L v⟩}),
      F (Function.update L v L'')) = _
  exact finsum_mem_eq_finite_toFinset_sum _ (tm_fin P v i (L v))

theorem tm_zero (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (hF : ∀ L, ¬ P.IsLatTup L → F L = 0) (L : P.Tup)
    (hL : ¬ P.IsLatTup L) : P.Tminus v i F L = 0 := by
  rw [tm_eq]
  apply Finset.sum_eq_zero
  intro L'' hL''
  apply hF
  intro hlat
  apply hL
  show ∀ w, IsLattice (P.W w) (L w)
  intro w
  by_cases hw : w = v
  · subst hw
    have he : IsEdge p (P.n' w) i ⟨L'', L w⟩ := (tm_fin P w i (L w)).mem_toFinset.mp hL''
    exact he.2.1
  · simpa [Function.update, hw] using hlat w

theorem smul_update (C : Level P) (γ : C.Γ) (v : Fin P.nV) (L : P.Tup)
    (A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    C.smul γ (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A) =
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (C.smul γ L) v (A.map (nt_phi (P.W v) (C.act v γ))) := by
  funext w
  by_cases hw : w = v
  · subst hw
    simp [Function.update, Level.smul, nt_phi]
  · simp [Function.update, hw, Level.smul, nt_phi]

theorem tm_equiv (C : Level P) (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp)
    (hF' : ∀ (γ : C.Γ) (L : P.Tup), F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L)) (γ : C.Γ) (L : P.Tup) :
    P.Tminus v i F (C.smul γ L) = (C.χ γ : O) • C.actX γ (P.Tminus v i F L) := by
  rw [tm_eq, tm_eq, map_sum, Finset.smul_sum]
  symm
  apply Finset.sum_nbij' (fun A => A.map (nt_phi (P.W v) (C.act v γ)))
    (fun A => A.map (nt_phi (P.W v) (C.act v γ)⁻¹))
  · intro A hA
    have hA' : IsEdge p (P.n' v) i ⟨A, L v⟩ := (tm_fin P v i (L v)).mem_toFinset.mp hA
    exact (tm_fin P v i (C.smul γ L v)).mem_toFinset.mpr (nt_edge_map p (P.n' v) i (C.act v γ) A (L v) hA')
  · intro B hB
    have hB' : IsEdge p (P.n' v) i ⟨B, (L v).map (nt_phi (P.W v) (C.act v γ))⟩ :=
      (tm_fin P v i (C.smul γ L v)).mem_toFinset.mp hB
    have h2 := nt_edge_map p (P.n' v) i (C.act v γ)⁻¹ B ((L v).map (nt_phi (P.W v) (C.act v γ))) hB'
    rw [nt_map_inv] at h2
    exact (tm_fin P v i (L v)).mem_toFinset.mpr h2
  · intro A _
    exact nt_map_inv _ _
  · intro B _
    exact nt_map_inv' _ _
  · intro A _
    have h := hF' γ (Function.update L v A)
    rw [smul_update] at h
    exact h.symm

end Gen

variable {p : ℕ} [Fact p.Prime]

theorem restTmEquiv (X : Sys p) : RestTmEquiv X := by
  intro J v i F hF
  refine ⟨fun c L hL => ?_, fun c γ L => ?_⟩
  · exact tm_zero (X.Pj J) (X.vJ J v) i (F c) (fun L' hL' => hF.1 c L' hL') L hL
  · exact tm_equiv (X.Pj J) (X.Lv.lev J c) (X.vJ J v) i (F c) (fun γ' L' => hF.2 c γ' L') γ L

theorem formB (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) : FormB X Y :=
  formB_of D Y hA (restTmEquiv X)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end


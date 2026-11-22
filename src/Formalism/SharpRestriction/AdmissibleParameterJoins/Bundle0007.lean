import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLb
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLj
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

def Per0 (D : D7) : Prop :=
  DGamDef D → ∀ u, ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
      ∀ w : D.what₂.places.Pl, y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PerTw (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → ∀ u μ, μ ≠ D.what₂.mu0 → ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
        y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PtTw (D : D7) (T : TwForms D) : Prop :=
  ∀ u μ, μ ≠ D.what₂.mu0 → ∃ h : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral h

def DGamT (D : D7) : Prop := ∀ u, ¬ (D.mem u).A.T ∣ (D.mem u).C.DGam

def PeriodBoundAtLevelPrime (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ))

theorem valGe_iff (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.LL) (k : ℤ) :
    ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y ↔ (y = 0 ∨ (k : ℝ) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [D.val_eq w y hy, WithTop.coe_le_coe]
    simp only [hy, false_or]
    exact Int.cast_le.symm

theorem pair_loc (D : D7) (w : D.what₂.places.Pl) (k : ℤ) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (NumberField.RingOfIntegers D.what₂.LL) V] (Λ : Submodule (NumberField.RingOfIntegers D.what₂.LL) V) (l : V → ℂ)
    (h0 : l 0 = 0) (hadd : ∀ x y, l (x + y) = l x + l y) (hsm : ∀ (a : D.what₂.LL) x, l (a • x) = D.what₂.embLL a * l x)
    (h : ∀ x ∈ Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = l x ∧ ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y) :
    ∀ z ∈ locW D.what₂.places w Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = l z ∧ ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y := by
  intro z hz
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by rw [map_zero, h0], by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hav⟩ := hx
    obtain ⟨b, hb, hbv⟩ := hy
    refine ⟨a + b, by rw [map_add, ha, hb, hadd], ?_⟩
    exact le_trans (le_min hav hbv) (AddValuation.map_add _ _ _)
  | smul c x _ hx =>
    obtain ⟨a, ha, hav⟩ := hx
    refine ⟨(c : D.what₂.LL) * a, ?_, ?_⟩
    · rw [map_mul, ha]
      exact (hsm (c : D.what₂.LL) x).symm
    · rw [AddValuation.map_mul]
      have hc : (0 : WithTop ℤ) ≤ D.what₂.places.val w (c : D.what₂.LL) := c.2
      calc ((k : ℤ) : WithTop ℤ) = 0 + ((k : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add hc hav

theorem neg_ur_vDG (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    -ur D w (vDG D u w) =
      ((-((D.what₂.places.ramIdx w * padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℕ) : ℤ) : ℤ) : ℝ) := by
  simp only [DV.ur, vDG, Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]

theorem pairing_lift_valuation_bound (hD : DGamDef D) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) (hp : Per0 D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ∀ z ∈ locW D.what₂.places w ((D.fm u).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.Ptil ((D.fm u).emb D.R.m z) ((D.eMt u).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro z hz F hF hF0
  obtain ⟨hPR, hInt, -⟩ := (h6 u).2.2.2.1
  obtain ⟨y, hy1, hy2⟩ := pair_loc D w
    (-((D.what₂.places.ramIdx w * padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℕ) : ℤ))
    ((D.fm u).lat D.R.m).L
    (fun x => (D.mem u).P.Ptil ((D.fm u).emb D.R.m x) ((D.eMt u).symm F))
    (by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil, LinearMap.map_smulₛₗ])
    (fun x hx => by
      obtain ⟨y, hy1, hy2⟩ := hp hD u _ (hInt x hx) F hF hF0
      refine ⟨y, ?_, ?_⟩
      · rw [hy1, (D.fm u).PtL_spec hPR x]
        rfl
      · have h := hy2 w
        rw [neg_ur_vDG] at h
        exact (valGe_iff D w y _).2 h)
    z hz
  refine ⟨y, hy1, ?_⟩
  rw [neg_ur_vDG]
  exact (valGe_iff D w y _).1 hy2

theorem pairTw_of {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) (h6 : PtTw D T) (hp : PerTw D Dx T) (u : D.what₂.Word)
    (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (w : D.what₂.places.Pl) (hQ : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    ∀ z ∈ locW D.what₂.places w ((T.fm u μ).lat D.R.m).L,
    ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m z) ((D.eMtTw u μ).symm F) ∧
        (y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)) := by
  intro z hz F hF hF0
  obtain ⟨hPR, hInt⟩ := h6 u μ hμ
  obtain ⟨y, hy1, hy2⟩ := pair_loc D w
    (-((D.what₂.places.ramIdx w * padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℕ) : ℤ))
    ((T.fm u μ).lat D.R.m).L
    (fun x => (D.PTw u μ).Ptil ((T.fm u μ).emb D.R.m x) ((D.eMtTw u μ).symm F))
    (by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil])
    (fun a b => by simp [PeriodMap.Ptil, LinearMap.map_smulₛₗ])
    (fun x hx => by
      obtain ⟨y, hy1, hy2⟩ := hp hD u μ hμ _ (hInt x hx) F hF hF0
      refine ⟨y, ?_, ?_⟩
      · rw [hy1, (T.fm u μ).PtL_spec hPR x]
        rfl
      · have h := hy2 w hQ
        rw [neg_ur_vDG] at h
        exact (valGe_iff D w y _).2 h)
    z hz
  refine ⟨y, hy1, ?_⟩
  rw [neg_ur_vDG]
  exact (valGe_iff D w y _).1 hy2

def LevelPrimeColumnOtherTuples (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def DlSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps

theorem numsL_wtsL_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn :=
  flipTwoThree.nums_wts_of_tuSize Fm hT hDl

theorem factDGam_mono {D : D7} {C C' : ℝ} (h : FactDGam D C) (hC : C ≤ C') : FactDGam D C' := by
  intro u
  refine (h u).trans ?_
  have h1 : (0 : ℝ) ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    have : ((D.R.f : ℝ) * D.R.N D.R.m) = ((D.R.f * D.R.N D.R.m : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact Real.log_natCast_nonneg _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h1
  have := mul_le_mul_of_nonneg_right hC h2
  simp only [mul_assoc] at this ⊢
  exact this

theorem slopes_family_of_column_values {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (h5 : flipTwoThree.ConclusionF5 Fm)
    (h6 : flipTwoThree.ConclusionF6 Fm) (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    LocalQuadraticParts.SlopesFamily Fm := by
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hCV⟩ := hCV
  refine family_orderBound_of_fifth_sixth Fm Cn 3 h5 h6 (by norm_num) ⟨max x0 x1, fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : x ≥ x1 := le_trans (le_max_right _ _) hx
  exact ⟨by linarith [flipTwoThree.two_le_rdE (Fm.D x i).host], (hN x e0 i).1, (hN x e0 i).2, hCV x e1 i⟩

theorem levelPrime_summary_of_fifth_without_span (D : D7) (L : SizeData₂ D) (C C1 : ℝ) (h2 : ∀ u, product_first_zeroth_parts.Conclusion2 D u)
    (h5 : ∀ u, product_first_zeroth_parts.Conclusion5 D u C) (hNu : DV.NuDef D L) (hAtT : NuAtTDef D L) (hS : LevelPrimeSizeBounds D L C1)
    (hSet : ∀ u, product_first_zeroth_parts.HidaSetting D u) (hC1 : 0 ≤ C1) : LocalQuadraticParts.adm26 L (4 * C1) :=
  levelPrime_summary_of_fifth D L C C1 h2 h5 hNu hAtT (locSpan D) (lenAtT D L hAtT) hS hSet hC1

theorem family_levelPrime_summary_simple {eps : ℝ} (Fm : FamP eps) (C C1 : ℝ) (hC1 : 0 ≤ C1)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C) ∧
      LevelPrimeSizeBounds (Fm.D x i) (Fm.L x i) C1 ∧ ∀ u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, hE⟩ := hE
  refine family_levelPrime_summary Fm C C1 hC1 ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx)
  obtain ⟨a, b, c, d⟩ := hE x e0 i
  exact ⟨a, b, locSpan _, lenAtT _ _ (Fm.ex x e1 i).lat.atT, c, d⟩

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSab
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem four_orbit_conditions_of_proof {X : Inst D L} {K : Consts} {Dx : DivX D} {T : TwForms D} {E : Formalism.MainNotions.OrbitPlaces.Ent D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp C : ℝ} (h : Formalism.MainNotions.OrbitPlaces.Conclusion₂ D L X K Dx T E lev Xe ce sp C) :
    Formalism.MainNotions.WeilJacquetShalikaLaw.OrbitsWithoutOperator D L X K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp ∧
      Formalism.MainNotions.WeilJacquetShalikaLaw.LossAtDiscriminant D L K Dx T lev Xe ce sp ∧ Formalism.MainNotions.WeilJacquetShalikaLaw.IsotypicPartsInternalDirectSum D Dx T sp := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSu
section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Be

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem lg_pt (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hax : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hae : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply hae hax, hinv, PowerSeries.subst_X hax]

variable (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p])

theorem be_at (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {a b : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst ![C ep * g.lg a, C ep * g.lg b] (map i0 be) = g.be a b := by
  have hlg : ∀ {σ' : Type} {c : σ' → MvPowerSeries τ ℂ_[p]}, HasSubst c → ∀ i : σ',
      subst c (C ep * g.lg (X i)) = C ep * g.lg (c i) := by
    intro σ' c hc i
    have hXi : HasSubst (fun _ : Unit => (X i : MvPowerSeries σ' ℂ_[p])) :=
by
      have hz : ∀ _ : Unit, constantCoeff (X i : MvPowerSeries σ' ℂ_[p]) = 0 := fun _ => constantCoeff_X i
      first
        | exact hasSubst_of_constantCoeff_zero hz
        | exact HasSubst.of_constantCoeff_zero' hz
        | exact hasSubst_of_constantCoeff_nilpotent (fun j => by rw [hz j]; exact IsNilpotent.zero)
    rw [← smul_eq_C_mul, subst_smul hc, ← smul_eq_C_mul]
    congr 1
    unfold G1.lg PowerSeries.subst
    rw [subst_comp_subst_apply hXi hc]
    simp only [subst_X hc]
  have h0 : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hc : HasSubst ![a, b] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have hl0 : ∀ i : Fin 2, constantCoeff (g.lg (X i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ (cc_l g)
  have h1 : ∀ i : Fin 2, constantCoeff
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i) = 0 := by
    intro i; fin_cases i <;> simp [hl0]
  have hd : HasSubst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] := by
    first
      | exact hasSubst_of_constantCoeff_zero h1
      | exact HasSubst.of_constantCoeff_zero' h1
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h1 i]; exact IsNilpotent.zero)
  have h := congrArg (subst ![a, b]) be_tie
  rw [be_subst g hex hc (constantCoeff_X _) (constantCoeff_X _), subst_X hc, subst_X hc,
    subst_comp_subst_apply hd hc] at h
  have hfun : (fun i => subst ![a, b]
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i)) = ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hlg hc 0
    · exact hlg hc 1
  rw [hfun] at h
  simpa using h

def LogOf (x : MvPowerSeries τ (K0 p)) (a : MvPowerSeries τ ℂ_[p]) : Prop :=
  constantCoeff x = 0 ∧ constantCoeff a = 0 ∧
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 x) = C ep * g.lg a

theorem logOf_X (i : τ) : LogOf g i0 ep (X i) (X i) := by
  refine ⟨constantCoeff_X i, constantCoeff_X i, ?_⟩
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  rw [map_X, subst_X (hs_dg hc), dg_Cmul]

theorem logOf_add (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) : LogOf g i0 ep (x + y) (g.add a b) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hlb : constantCoeff (g.lg b) = 0 := PowerSeries.constantCoeff_subst_eq_zero hb0 _ (cc_l g)
  have hs : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add, hla, hlb, add_zero]
  refine ⟨by rw [map_add, hx0, hy0, add_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_add, subst_add (hs_dg hc), hx1, hy1, G1.add, lg_pt g hex hinv hs, mul_add]

theorem logOf_mul (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) (c : K0 p) {x : MvPowerSeries τ (K0 p)}
    {a : MvPowerSeries τ ℂ_[p]} (hx : LogOf g i0 ep x a) : LogOf g i0 ep (C c * x) (g.mulBy (i0 c) a) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hs : constantCoeff (C (i0 c) * g.lg a) = 0 := by rw [map_mul, hla, mul_zero]
  refine ⟨by rw [map_mul, hx0, mul_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_mul, map_C, ← smul_eq_C_mul, subst_smul (hs_dg hc), hx1, G1.mulBy, lg_pt g hex hinv hs,
      smul_eq_C_mul]
    ring

theorem subtraction_formal_group_log (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) :
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 (sub2 p be x y)) = g.be a b := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have h0' : ∀ i : Fin 2, constantCoeff (map i0 (![x, y] i)) = 0 := by
    intro i; rw [constantCoeff_map, h0 i, map_zero]
  have hs' : HasSubst (fun i : Fin 2 => map i0 (![x, y] i)) := by
    first
      | exact hasSubst_of_constantCoeff_zero h0'
      | exact HasSubst.of_constantCoeff_zero' h0'
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0' i]; exact IsNilpotent.zero)
  unfold sub2
  rw [map_subst hs, subst_comp_subst_apply hs' (hs_dg hc)]
  have hfun : (fun i : Fin 2 => subst (diagS (PowerSeries.C ep * g.l)) (map i0 (![x, y] i))) =
      ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hx1
    · exact hy1
  rw [hfun]
  exact be_at g i0 be ep hex be_tie ha0 hb0

theorem constantCoeff_sub2_eq_zero (hbe : constantCoeff be = 0) {x y : MvPowerSeries τ (K0 p)} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : constantCoeff (sub2 p be x y) = 0 := by
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact Formalism.G.LogP.hs2 hx hy
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  unfold sub2
  first
    | exact constantCoeff_subst_eq_zero hs h0 hbe
    | exact constantCoeff_subst_eq_zero h0 hbe
    | exact MvPowerSeries.constantCoeff_subst_eq_zero hs h0 hbe

end Be

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSx
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sumFE_atG_le {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (i : Fin 2) (w : D.what₂.places.Pl)
    (hwi : D.what₂.places.resChar w = D.host.g i) (u : D.what₂.Word) (hw : D.what₂.places.resChar w ≠ (D.mem u).A.T) :
    ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) ≤
      -(∑ j ∈ Formalism.MainNotions.LiftErrorLocal.lifts D, vNN Xe i u j w) - C1 * Formalism.MainNotions.LiftErrorLocal.errC D L := by
  have hg : D.what₂.places.resChar w ∈ L.gTypes := by
    rw [hwi]
    unfold SizeData₂.gTypes
    fin_cases i <;> simp
  have hFj : ∀ j ∈ SizeData₂.lifts D, L.F j w = FTypeG D j := by
    intro j hj
    rw [hF j hj w]
    exact if_pos hg
  have hEj : ∀ j ∈ SizeData₂.lifts D, L.E u j w = vDG D u w + EatG L Xe ce i u j w := by
    intro j hj
    rw [hE.edef u j hj w]
    unfold Eval vDG
    dsimp only
    rw [if_neg hw]
    fin_cases i
    · have h0 : D.what₂.places.resChar w = D.host.g 0 := hwi
      rw [if_pos h0]
      rfl
    · have h1 : D.what₂.places.resChar w = D.host.g 1 := hwi
      rw [if_neg (by rw [h1]; exact D.host.g_ne.symm), if_pos h1]
      rfl
  have hvD : 0 ≤ vDG D u w := Nat.cast_nonneg _
  set A : ℝ := (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) with hA
  set B : ℝ := (D.R.f : ℝ) * (Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz) with hB
  have hη := L.etaSz_pos.le
  have hN0 : 0 ≤ Nm D := by unfold Nm; positivity
  have ht : (D.R.t : ℝ) ≤ Nm D := by
    have h1 : D.R.t + 1 ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_left _ (by have := D.R.two_le_m; omega)
    have h2 : D.R.t ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    unfold Nm
    exact_mod_cast h2
  have hA0 : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hη))
  have hBA : B ≤ 2 * A := by
    have h3 : Nm D * (Nm D + D.R.t) + (D.R.m : ℝ) ^ 2 * L.etaSz ≤ 2 * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) := by
      nlinarith [mul_le_mul_of_nonneg_left ht hN0, mul_nonneg (sq_nonneg (D.R.m : ℝ)) hη]
    have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ (D.R.f : ℝ))
    rw [hA, hB]
    linarith
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by
    unfold SizeData₂.lifts
    simp
  have hsum : ∑ j ∈ SizeData₂.lifts D, (L.F j w - L.E u j w) =
      -(∑ j ∈ SizeData₂.lifts D, vNN Xe i u j w) - (D.R.m : ℝ) * (ce.g * A) - (D.R.m : ℝ) * vDG D u w := by
    have : ∀ j ∈ SizeData₂.lifts D, L.F j w - L.E u j w = -vNN Xe i u j w - (ce.g * A + vDG D u w) := by
      intro j hj
      rw [hFj j hj, hEj j hj]
      unfold EatG
      rw [hA]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul,
      hcard]
    ring
  have hEr : Formalism.MainNotions.LiftErrorLocal.errC D L = (D.R.m : ℝ) * B := by
    unfold Formalism.MainNotions.LiftErrorLocal.errC
    rw [hB]
    unfold Nm
    ring
  have hl : Formalism.MainNotions.LiftErrorLocal.lifts D = SizeData₂.lifts D := rfl
  rw [hEr, hl, hsum]
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have h1 : C1 * ((D.R.m : ℝ) * B) ≤ (D.R.m : ℝ) * (ce.g * A) := by
    have h5 : C1 * ((D.R.m : ℝ) * B) ≤ C1 * ((D.R.m : ℝ) * (2 * A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBA hm0) hC1
    have h6 : (2 * C1) * ((D.R.m : ℝ) * A) ≤ ce.g * ((D.R.m : ℝ) * A) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hm0 hA0)
    nlinarith
  have h2 : 0 ≤ (D.R.m : ℝ) * vDG D u w := mul_nonneg hm0 hvD
  linarith

theorem noGainBound_of_local {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 C2 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (h : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) :
    NoGainBoundAtTypePrimes D L := by
  intro u w hw hgm φ hφ F hF1 _
  obtain ⟨i, hwi⟩ : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by
    rcases Finset.mem_insert.1 hgm with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, Finset.mem_singleton.1 h1⟩
  obtain ⟨y, hy, hv⟩ := h.1 i w hwi u hw (D.what₂.muAt w) φ hφ F hF1
  refine ⟨y, hy, hv.imp id fun hv => ?_⟩
  have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h3 := le_trans (sumFE_atG_le hF hE hC1 hC i w hwi u hw) hv
  unfold Formalism.MainNotions.LiftErrorLocal.vG at h3
  unfold ur
  rw [le_div_iff₀ he] at h3
  linarith

end Formalism.MainNotions.J

end
end


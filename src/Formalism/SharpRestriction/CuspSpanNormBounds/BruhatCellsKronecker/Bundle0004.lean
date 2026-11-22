import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.PrimeToDifferent
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ParabolicSumAdmissibleOfParabolic
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.S.UnitaryVolumeMass MeasureTheory Formalism.QuantumDeterminants
open scoped ENNReal InnerProductSpace

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsNormSq_eq_sum (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

def hsVec (A : Wq →L[ℂ] Wp) : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))

theorem hsVec_norm_sq (A : Wq →L[ℂ] Wp) : ‖hsVec A‖ ^ 2 = hsNormSq A := by
  rw [hsNormSq_eq_sum, PiLp.norm_sq_eq_of_L2]
  rfl

theorem hsVec_sum_smul {ι : Type} [Fintype ι] (a : ι → ℂ) (X : ι → (Wq →L[ℂ] Wp)) :
    hsVec (∑ i, a i • X i) = ∑ i, a i • hsVec (X i) := by
  ext j
  simp [hsVec]

theorem hsNormSq_sum_le {ι : Type} [Fintype ι] (a : ι → ℂ) (X : ι → (Wq →L[ℂ] Wp)) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i, hsNormSq (X i) ≤ K) : hsNormSq (∑ i, a i • X i) ≤ K * (∑ i, ‖a i‖) ^ 2 := by
  have h1 : ‖hsVec (∑ i, a i • X i)‖ ≤ (∑ i, ‖a i‖) * Real.sqrt K := by
    rw [hsVec_sum_smul, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.le_sqrt_of_sq_le ?_
    rw [hsVec_norm_sq]; exact h i
  rw [← hsVec_norm_sq]
  calc ‖hsVec (∑ i, a i • X i)‖ ^ 2 ≤ ((∑ i, ‖a i‖) * Real.sqrt K) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = K * (∑ i, ‖a i‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]; ring

theorem hsNormSq_real_smul (c : ℝ) (A : Wq →L[ℂ] Wp) : hsNormSq (((c : ℝ) : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [_root_.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end HS

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

theorem jhUnit_le {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (νR : Measure (Mt D.R.k D.R.rS))
    (γ : MatKR D.R.k D.R.rS) (wt B : ℝ) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (wt * hsNormSq (A.J νR γ)) ≤ ENNReal.ofReal B * MMv D w w' A μsec) :
    wt * hsNormSq (jhUnit D w w' A μsec νR γ) ≤ B := by
  unfold jhUnit
  rw [hsNormSq_real_smul]
  by_cases hM : (MMv D w w' A μsec).toReal = 0
  · rw [hM, Real.zero_rpow (by norm_num)]
    simpa using hB
  · have hpos : 0 < (MMv D w w' A μsec).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
    have htop : MMv D w w' A μsec ≠ ⊤ := fun e => hM (by rw [e]; rfl)
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hB] at h
    have h2 : wt * hsNormSq (A.J νR γ) ≤ B * (MMv D w w' A μsec).toReal :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hpos.le)).1 h
    have h3 : ((MMv D w w' A μsec).toReal ^ (-(1 / 2 : ℝ))) ^ 2 = ((MMv D w w' A μsec).toReal)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
      norm_num
    rw [h3]
    calc wt * (((MMv D w w' A μsec).toReal)⁻¹ * hsNormSq (A.J νR γ))
        = (wt * hsNormSq (A.J νR γ)) * ((MMv D w w' A μsec).toReal)⁻¹ := by ring
      _ ≤ (B * (MMv D w w' A μsec).toReal) * ((MMv D w w' A μsec).toReal)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hpos.le)
      _ = B := by field_simp

theorem stPTsum_of_stPT (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ)
    (h : stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C) : stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro h0 τ w w' hTT θ hθ W hW ι _ lams As a hl μsec hsec γ p hrel θ' hθ' νR hν
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  set B : ℝ := large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
    (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2) with hBdef
  have hB : 0 ≤ B := by
    have : (0 : ℝ) < max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  set wt : ℝ := ptWeight D.R.k D.R.rS (Tr D w) (Tr D w') p with hwt
  have hi : ∀ i, wt * hsNormSq (jhUnit D w w' (As i) μsec νR γ) ≤ B := fun i =>
    jhUnit_le D w w' (As i) μsec νR γ wt B hB
      (h h0 τ w w' hTT θ hθ W hW (lams i) (hl i).1 (As i) (hl i).2 μsec hsec γ p hrel θ' hθ' νR hν)
  rcases le_or_gt wt 0 with hw | hw
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hw (hsNormSq_nonneg _)) (by positivity)
  · have hi' : ∀ i, hsNormSq (jhUnit D w w' (As i) μsec νR γ) ≤ B / wt := fun i => by
      rw [le_div_iff₀ hw, mul_comm]; exact hi i
    have := hsNormSq_sum_le a (fun i => jhUnit D w w' (As i) μsec νR γ) (B / wt) (by positivity) hi'
    calc wt * hsNormSq (∑ i, a i • jhUnit D w w' (As i) μsec νR γ)
        ≤ wt * (B / wt * (∑ i, ‖a i‖) ^ 2) := mul_le_mul_of_nonneg_left this hw.le
      _ = B * (∑ i, ‖a i‖) ^ 2 := by field_simp

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem ptsumF_of_ptF (Cg cb Cu cT CT C0 C1 : ℝ)
    (h : ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => stPT (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) :
    ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => stPTsum (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun Cn => (hC Cn).mono (fun C' Cl x i => stPTsum_of_stPT _ _ C' Cl Cg cb Cu cT CT C0 Cn C1 C)⟩

theorem PTsum_of_PT (Cg cb Cu cT CT C0 C1 : ℝ) (h : AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) :
    PX.PTsum Fm Cg cb Cu cT CT C0 C1 := ptsumF_of_ptF Fm Cg cb Cu cT CT C0 C1 h

theorem parabolic_sum_of_parabolic_family (Cg cb Cu cT CT C0 C1 : ℝ) (h : VanishingOnXAndXPlusBranching.admF1 Fm Cg cb Cu cT CT C0 C1) :
    PX.PTsum Fm Cg cb Cu cT CT C0 C1 := ptsumF_of_ptF Fm Cg cb Cu cT CT C0 C1 h

theorem PTsum_all (h : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) :
    ∀ Cg cb Cu cT CT C0 C1, PX.PTsum Fm Cg cb Cu cT CT C0 C1 :=
  fun Cg cb Cu cT CT C0 C1 => PTsum_of_PT Fm Cg cb Cu cT CT C0 C1 (h Cg cb Cu cT CT C0 C1)

theorem parabolic_sum_admissible_of_parabolic (Cg cb Cu cT CT C0 C1 : ℝ) (h : AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) :
    AuxiliaryNormPrimes.FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1 := ptsumF_of_ptF Fm Cg cb Cu cT CT C0 C1 h

end Fam

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ProductLValuesPolynomialBound
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

variable {eps : ℝ}

theorem f_le_k (D : D7) : (D.R.f : ℝ) ≤ D.R.k := by
  have h := D.R.f_le_k
  exact_mod_cast h

theorem k_le_r (D : D7) : (D.R.k : ℝ) ≤ D.R.r := by
  have h := D.R.two_le_m
  have h' : D.R.k ≤ D.R.r := by
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact_mod_cast h'

theorem gap_of_consec {N : ℕ} (lam : Fin N → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin N) (h : i.1 + 1 < N), G < lam i - lam ⟨i.1 + 1, h⟩) :
    ∀ (d : ℕ) (a : Fin N) (hd : a.1 + d + 1 < N), G < lam a - lam ⟨a.1 + d + 1, hd⟩ := by
  intro d
  induction d with
  | zero => intro a hd; exact h a hd
  | succ d ih =>
    intro a hd
    have h1 := ih a (by omega)
    have h2 : G < lam ⟨a.1 + d + 1, by omega⟩ - lam ⟨a.1 + (d + 1) + 1, hd⟩ := h ⟨a.1 + d + 1, by omega⟩ hd
    linarith

theorem lt_gap_of_consec {N : ℕ} (lam : Fin N → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin N) (h : i.1 + 1 < N), G < lam i - lam ⟨i.1 + 1, h⟩) (a b : Fin N) (hlt : a < b) :
    G < lam a - lam b := by
  have hab : a.1 < b.1 := hlt
  have hb := b.2
  have hd : a.1 + (b.1 - a.1 - 1) + 1 < N := by omega
  have key := gap_of_consec lam G hG h (b.1 - a.1 - 1) a hd
  have e : (⟨a.1 + (b.1 - a.1 - 1) + 1, hd⟩ : Fin N) = b :=
    Fin.ext (by show a.1 + (b.1 - a.1 - 1) + 1 = b.1; omega)
  rwa [e] at key

theorem abs_gap_of_consec {N : ℕ} (lam : Fin N → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin N) (h : i.1 + 1 < N), G < lam i - lam ⟨i.1 + 1, h⟩) (a b : Fin N) (hab : a ≠ b) :
    G < |lam a - lam b| := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact lt_of_lt_of_le (lt_gap_of_consec lam G hG h a b hlt) (le_abs_self _)
  · rw [abs_sub_comm]
    exact lt_of_lt_of_le (lt_gap_of_consec lam G hG h b a hlt) (le_abs_self _)

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplitsCompletelyIff
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField IsDedekindDomain

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  have := dimS_eq D.R
  omega

theorem idxRows_eq (D : D7) (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) :
    LocalBesselAndTopKernel.idxRows D = Formalism.FourierDecayAlt.Sz.rowIdx D.R.k D.R.rS (D.host.g 0 : ℝ) ^ D.R.f *
      Formalism.FourierDecayAlt.Sz.rowIdx D.R.k D.R.rS (D.host.g 1 : ℝ) ^ D.R.f := by
  unfold LocalBesselAndTopKernel.idxRows
  rw [finprod_typedPl D h0 h1
    (fun q => LocalBesselAndTopKernel.cardGL q D.R.r / (q ^ LocalBesselAndTopKernel.dimNS D * q ^ (D.R.k * (D.R.k - 1) / 2)))]
  unfold Formalism.FourierDecayAlt.Sz.rowIdx Formalism.FourierDecayAlt.Sz.glCard Formalism.FourierDecayAlt.Sz.dimN LocalBesselAndTopKernel.cardGL LocalBesselAndTopKernel.dimNS
  rw [rank_eq D]

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {D : D7} (X : TermTie D)

theorem tie_Tu_pos (D : D7) (u : D.what₂.Word) : 0 < Tu D u := (D.mem u).A.T_prime.pos

theorem tie_Gval_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) :
    Gval (X.fl t) (X.fl' t) ≠ 0 := by
  rw [← X.G_eq t]
  exact (map_ne_zero _).2 h

theorem tie_G_pos {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) (τ : D.host.E →+* ℂ) :
    0 < (τ (Gval (X.fl t) (X.fl' t))).re :=
  (b_G_pos (p_starConj D) (tie_Tu_pos D u) (X.fl t) (X.fl' t) (X.fixed t).2.2.1.2 (X.lift' t).2
    (tie_Gval_ne X t h) (p_posX D _ (tie_Tu_pos D u) (X.fl t)) τ).1

theorem GDr_of_tie : PX.GDr D X := by
  intro u u' t h
  have hpos := tie_G_pos X t h
  refine ⟨fun h1 => ?_, fun _ τ => hpos _⟩

  have hG : Gval (X.fl t) (X.fl' t) = -(((Tu D u : ℕ) : D.host.E) * ((Tu D u' : ℕ) : D.host.E) *
      (Dl (X.fl t).fl (X.fl' t).fl D.R.rS * star (Dl (X.fl t).fl (X.fl' t).fl D.R.rS))) := by
    simp only [Formalism.MainNotions.S.Lat.Gval, Formalism.MainNotions.S.Gflag, h1, star_zero, mul_zero, zero_sub]
  haveI := D.host.isCMField_hostE
  have hc : ∀ y : D.host.E, D.host.φ₀ (star y) = starRingEnd ℂ (D.host.φ₀ y) := fun y =>
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ y
  have h0 := hpos D.host.φ₀
  rw [hG, map_neg, map_mul, map_mul, map_mul, map_natCast, map_natCast, hc, Complex.mul_conj] at h0
  have key : 0 ≤ ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
      Complex.normSq (D.host.φ₀ (Dl (X.fl t).fl (X.fl' t).fl D.R.rS)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Complex.normSq_nonneg _)
  simp at h0
  linarith

theorem S0ge1_of_tie (X : TermTie D) : PX.FirstSumAtLeastOne D := by
  intro u u' p h1 _
  rw [X.s0_eq p]
  unfold Lat.s0
  have hr : finrank D.host.E (Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))) = D.R.k - 1 :=
    a_rankHp_k _ (X.fixed _).1 _ _ (X.fixed _).2.2.1.2 (X.lift' _).2 (tie_Gval_ne X _ h1) D.R.k (p_rankV D)
  have hle : Th (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) ≤
      Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) := by
    rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    exact hab.1.1.1
  have h2 := Submodule.finrank_mono hle
  have hk := D.R.m_add_three_le_k
  omega

end Rec

theorem tie_Dl_eq' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (j : ℕ) (hj : j ≤ r + 1) :
    Dl F F' j = ((Zhat F F').submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  unfold Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  rw [dif_pos hj]

section Packets

variable {D : D7} (X : TermTie D)

theorem tie_X_le_ker {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (y : S.V) (h : ∀ a, S.hT (F.e a) y = 0) : ∀ x ∈ F.X, S.hT x y = 0 := by
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact h a
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

theorem tie_Xa_le_X {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold Formalism.MainNotions.S.FlagG.Xa Formalism.MainNotions.S.FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem tie_isId_inS (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.isId t) : D.s.inS t := by
  obtain ⟨n, hn, he, hz⟩ := (X.isId_iff t).1 h
  obtain ⟨_, hj, hw⟩ := hn
  refine (X.inS_iff t).2 ⟨fun a => ?_, ?_⟩
  · have hea : (X.fl t).fl.e a ∈ Submodule.span D.host.E ((X.fl t).fl.e '' {i | i.1 < a.val + 1}) :=
      Submodule.subset_span ⟨a, by simp, rfl⟩
    have ha := hj a.val _ hea
    rw [he a] at ha
    exact ha
  · have hzo : (X.fl t).fl.z ∈ orth _ (Xsp (X.fl t)) := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      exact tie_X_le_ker (X.fl t).fl _ (X.fl t).fl.z_orth
    have hd : (X.fl' t).fl.z - (X.fl t).fl.z =
        (n (X.fl t).fl.z - (X.fl t).fl.z) - (n (X.fl t).fl.z - (X.fl' t).fl.z) := by abel
    rw [hd]
    exact Submodule.sub_mem _ (hw _ hzo) hz

private theorem Zhat_castSucc_eq_zero {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (he : ∀ a, F'.e a - F.e a ∈ F.Xa a.val)
    (hz : F'.z - F.z ∈ F.X) (a : Fin r) (b : Fin (r + 1)) : Zhat F F' (Fin.castSucc a) b = 0 := by

  have hker : ∀ v ∈ F.X, S.hT (F.e a) v = 0 := by
    intro v hv
    unfold Formalism.MainNotions.S.FlagG.X at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact F.e_iso a c
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  induction b using Fin.lastCases with
  | last =>
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]
    rw [show F'.z = F.z + (F'.z - F.z) by abel, map_add, F.z_orth a, hker _ hz, add_zero]
  | cast b =>
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    rw [show F'.e b = F.e b + (F'.e b - F.e b) by abel, map_add, F.e_iso a b,
      hker _ (tie_Xa_le_X F _ (he b)), add_zero]

private theorem Gflag_eq_zero_of_sub_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    {T : E} (F F' : FlagG S r T) (he : ∀ a, F'.e a - F.e a ∈ F.Xa a.val) (hz : F'.z - F.z ∈ F.X)
    (hT : star T = T) : Gflag F F' = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hzz : F'.z = F.z := by
      have h0 : F.X = ⊥ := by
        unfold Formalism.MainNotions.S.FlagG.X
        rw [Set.range_eq_empty, Submodule.span_empty]
      rw [h0, Submodule.mem_bot, sub_eq_zero] at hz
      exact hz
    have kF : ∀ i : Fin (0 + 1), F.fvec i = F.z := by
      intro i
      induction i using Fin.lastCases with
      | last => simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      | cast i => exact i.elim0
    have kF' : ∀ i : Fin (0 + 1), F'.fvec i = F'.z := by
      intro i
      induction i using Fin.lastCases with
      | last => simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      | cast i => exact i.elim0
    have h1 : Dl F F' 1 = -T := by
      rw [tie_Dl_eq' F F' 1 le_rfl, Matrix.det_unique]
      simp only [Matrix.submatrix_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, kF, kF']
      rw [hzz, F.z_norm]
    have h2 : Dl F F' 0 = 1 := by
      rw [tie_Dl_eq' F F' 0 (Nat.zero_le _), Matrix.det_isEmpty]
    simp only [Formalism.MainNotions.S.Gflag, zero_add, h1, h2, star_neg, hT, star_one]
    ring
  · have hrow : ∀ (l : ℕ) (hl : l ≤ r + 1) (h0 : 0 < l), Dl F F' l = 0 := by
      intro l hl h0
      rw [tie_Dl_eq' F F' l hl]
      refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h0⟩ (fun j => ?_)
      rw [Matrix.submatrix_apply]
      have hc : (Fin.castLE hl ⟨0, h0⟩ : Fin (r + 1)) = Fin.castSucc ⟨0, hr⟩ := Fin.ext rfl
      rw [hc]
      exact Zhat_castSucc_eq_zero F F' he hz ⟨0, hr⟩ _
    unfold Formalism.MainNotions.S.Gflag
    rw [hrow (r + 1) le_rfl (Nat.succ_pos r), hrow r (Nat.le_succ r) hr]
    simp

theorem term_in_S_vanishes (X : TermTie D) {u : D.what₂.Word} (t : D.s.Term u u) (h : D.s.inS t) : D.s.Gterm t = 0 := by
  obtain ⟨he, hz⟩ := (X.inS_iff t).1 h
  have hG : Gval (X.fl t) (X.fl' t) = 0 :=
    Gflag_eq_zero_of_sub_mem (X.fl t).fl (X.fl' t).fl he hz (by simp)
  have h2 := X.G_eq t
  rw [hG] at h2
  exact (map_eq_zero_iff _ (algebraMap _ _).injective).1 h2

end Packets

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma

end
end


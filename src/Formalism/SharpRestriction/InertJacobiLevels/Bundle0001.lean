import Formalism.LocalRingCardinality.DataNChoice
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraNch
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

structure NChEmb (D : D7) where
  twI : D.what₂.places.Pl → D.ntw.Tw
  twI_l : ∀ w, D.ntw.l (twI w) = D.what₂.places.resChar w
  sd : D.what₂.places.Pl → Bool
  embW : ∀ w, D.what₂.LL →+* FractionRing (D.ntw.Ok (twI w) 1)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (D.ntw.Ok (twI w) 1) (FractionRing (D.ntw.Ok (twI w) 1))).range

set_option synthInstance.maxHeartbeats 400000 in

def nchZero (D : D7) [∀ μ j, Subsingleton (D.what₂.MtL μ j)]
    [∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)] (N : NChEmb D) : NChoice D :=
  NChoice.ofOk D N.twI N.twI_l N.sd (fun _ => ∅) (fun _ => 1) (fun _ => 1) N.embW N.embW_w (fun _ _ => 0)
    (fun w j _ _ _ b => by
      have : IsEmpty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :=
        ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
      exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩)
    (fun _ _ _ _ _ => Subsingleton.elim _ _)

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Finset

theorem facProd_succ (n : ℕ) : facProd (n + 1) = (n.superFactorial : ℝ) := by
  unfold facProd
  rw [Finset.prod_range_succ', Nat.factorial_zero, Nat.cast_one, mul_one, ← Nat.prod_range_factorial_succ]
  push_cast
  rfl

theorem sf_pos (n : ℕ) : 0 < n.superFactorial := by
  rw [← Nat.prod_range_factorial_succ]
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

theorem dimV_nat {N : ℕ} (x : Fin N → ℝ) (z : Fin N → ℤ) (c : ℝ) (hx : ∀ i, x i = z i + c) (hz : StrictAnti z) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = dimV x := by
  cases N with
  | zero => exact ⟨1, one_pos, by simp [dimV, vand, facProd]⟩
  | succ n =>
    obtain ⟨q, hq⟩ := Matrix.superFactorial_dvd_vandermonde_det (fun i => -z i)
    rw [Matrix.det_vandermonde] at hq
    have hpos : (0 : ℤ) < ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (-z j - -z i) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => by
        have := hz (Finset.mem_Ioi.1 hj)
        omega
    have hsf : (0 : ℤ) < (n.superFactorial : ℤ) := by exact_mod_cast sf_pos n
    have hq0 : 0 < q := by
      rw [hq] at hpos
      exact (pos_iff_pos_of_mul_pos hpos).1 hsf
    have hV : vand x = ((∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (-z j - -z i) : ℤ) : ℝ) := by
      unfold vand
      push_cast
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Finset.filter_lt_eq_Ioi]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hx a, hx b]
      ring
    refine ⟨q.toNat, by omega, ?_⟩
    unfold dimV
    rw [hV, hq, facProd_succ]
    have h1 : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
      have : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0.le
      exact_mod_cast this
    have h2 : ((n.superFactorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (sf_pos n).ne'
    rw [h1]
    push_cast
    field_simp

theorem strictAnti_of_step {N : ℕ} (f : Fin N → ℚ)
    (h : ∀ (i : ℕ) (h1 : i + 1 < N), f ⟨i + 1, h1⟩ < f ⟨i, by omega⟩) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : a + 1 ≤ b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact h a hb
  | succ n hn ih => exact (h n hb).trans (ih (by omega) (by show a < n; omega))

theorem hc_u_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.u :=
  strictAnti_of_step _ fun i h1 =>
    (P.v_gt_u ⟨i, by omega⟩).trans (P.u_gt_v ⟨i, by omega⟩)

theorem dimV_hc {R : Ranks} (P : HCParam R) : ∃ n : ℕ, 0 < n ∧ (n : ℝ) = dimV (fun i => ((P.u i : ℚ) : ℝ)) := by
  choose z hz using P.u_half
  refine dimV_nat _ z (1 / 2) (fun i => by rw [hz i]; push_cast; ring) fun a b hab => ?_
  have := hc_u_strictAnti P hab
  rw [hz a, hz b] at this
  have h2 : (z b : ℚ) < z a := by linarith
  exact_mod_cast h2

def massH {R : Ranks} (H : Host R) (M : ℕ) : ℝ :=
  letI := H.cmStar
  Formalism.HermitianLatticesTheory.mass (stdForm H.E M) (stdLat H.E M)

def duStarH {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) : ℝ :=
  massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f) *
    ∏ ρ, dimV (fun i => (((hc ρ).u i : ℚ) : ℝ))

theorem duStarU_eq (D : D7) (u : D.what₂.Word) : duStarU D u = duStarH D.host (D.hcW u) := rfl

def GSplit {R : Ranks} (H : Host R) : Prop :=
  (∀ i, (placesOver H.E (H.g i)).ncard = Module.finrank ℚ H.E) ∧ ∀ i, 2 * R.f * R.k < H.g i - 1

def MassIntegral : Prop :=
  ∀ (R : Ranks) (H : Host R), GSplit H → ∃ N : ℕ, 0 < N ∧
    (N : ℝ) = massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f)

theorem exists_duStarH (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : ∃ N : ℕ, 0 < N ∧ (N : ℝ) = duStarH H hc := by
  obtain ⟨N0, h0, h1⟩ := hM R H hH
  choose n hn hn' using fun ρ => dimV_hc (hc ρ)
  refine ⟨N0 * ∏ ρ, n ρ, Nat.mul_pos h0 (Finset.prod_pos fun ρ _ => hn ρ), ?_⟩
  unfold duStarH
  rw [← h1]
  push_cast
  congr 1
  exact Finset.prod_congr rfl fun ρ _ => hn' ρ

def duNat (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : ℕ :=
  (exists_duStarH hM H hH hc).choose

theorem duNat_pos (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : 0 < duNat hM H hH hc := (exists_duStarH hM H hH hc).choose_spec.1

theorem duNat_eq (hM : MassIntegral) {R : Ranks} (H : Host R) (hH : GSplit H) {Tau : Type} [Fintype Tau]
    (hc : Tau → HCParam R) : (duNat hM H hH hc : ℝ) = duStarH H hc := (exists_duStarH hM H hH hc).choose_spec.2

theorem duStar_def_iff (D : D7) (u : D.what₂.Word) :
    (((D.mem u).A.duStar : ℕ) : ℝ) = duStarU D u ↔ (((D.mem u).A.duStar : ℕ) : ℝ) = duStarH D.host (D.hcW u) := Iff.rfl

theorem isRowLev_one (k rS n : ℕ) (F : Type) [Zero F] [One F] [DecidableEq (Fin n)] :
    IsRowLev k rS (1 : Matrix (Fin n) (Fin n) F) := by
  refine ⟨fun i j h => Matrix.one_apply_ne ?_, fun i => Matrix.one_apply_eq i,
    fun i j _ h => Matrix.one_apply_ne (ne_of_gt h), fun i j _ h _ => Matrix.one_apply_ne h⟩
  rintro rfl
  exact lt_irrefl _ h

theorem idxRowLoc_pos (g k m : ℕ) [NeZero g] : 0 < idxRowLoc g k m := by
  unfold idxRowLoc idxLoc
  have : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} :=
    ⟨⟨1, by rw [Units.val_one]; exact isRowLev_one _ _ _ _⟩⟩
  have h1 : 0 < Nat.card (GL (Fin (k + m - 1)) (ZMod g)) := Nat.card_pos
  have h2 : 0 < Nat.card {A : GL (Fin (k + m - 1)) (ZMod g) //
      IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := Nat.card_pos
  positivity

def idxSigR (R : Ranks) (g : Fin 2 → ℕ) : ℝ := idxRowLoc (g 0) R.k R.m ^ R.f * idxRowLoc (g 1) R.k R.m ^ R.f

theorem idxSigR_pos (R : Ranks) (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) : 0 < idxSigR R g := by
  have := fun i => NeZero.mk (hg i).ne_zero
  have h0 := idxRowLoc_pos (g 0) R.k R.m
  have h1 := idxRowLoc_pos (g 1) R.k R.m
  unfold idxSigR
  positivity

def volFor (R : Ranks) (g : Fin 2 → ℕ) {Tau : Type} [Fintype Tau] (dsig : Tau → ℝ) (Dst : ℝ) : ℝ :=
  Dst / (idxSigR R g * ∏ ρ, dsig ρ)

theorem volFor_pos (R : Ranks) (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) {Tau : Type} [Fintype Tau] (dsig : Tau → ℝ)
    (hd : ∀ ρ, 0 < dsig ρ) (Dst : ℝ) (hD : 0 < Dst) : 0 < volFor R g dsig Dst :=
  div_pos hD (mul_pos (idxSigR_pos R g hg) (Finset.prod_pos fun ρ _ => hd ρ))

theorem dstar_def_of_vol (D : D7)
    (h : letI := D.host.cmStar; D.vol (D.sp.Y 0) = volFor D.R D.host.g D.dsig D.what₂.Dstar) :
    D.what₂.Dstar = DstarD D := by
  have h1 : 0 < idxSigR D.R D.host.g := idxSigR_pos _ _ D.host.g_prime
  have h2 : 0 < ∏ ρ, D.dsig ρ := Finset.prod_pos fun ρ _ => D.dsig_pos ρ
  show D.what₂.Dstar = volY0 D * idxSigR D.R D.host.g * ∏ ρ, D.dsig ρ
  unfold volY0
  rw [h, volFor]
  field_simp

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.BasicNotions.Examples₂ NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def extZ (n n' : ℕ) : (Fin n → E) →ₗ[E] (Fin n' → E) where
  toFun x := fun i => if h : i.1 < n then x ⟨i.1, h⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : i.1 < n <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.1 < n <;> simp [h]

theorem sum_extZ (n n' : ℕ) (hn : n ≤ n') (g : Fin n → E) :
    ∑ i : Fin n', (if h : i.1 < n then g ⟨i.1, h⟩ else 0) = ∑ i, g i := by
  have h1 := Fin.sum_univ_eq_sum_range (fun i : ℕ => if h : i < n then g ⟨i, h⟩ else 0) n'
  have h2 := Fin.sum_univ_eq_sum_range (fun i : ℕ => if h : i < n then g ⟨i, h⟩ else 0) n
  rw [h1, ← Finset.sum_subset (Finset.range_subset_range.2 hn), ← h2]
  · exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
  · intro i _ hi
    rw [dif_neg (by simpa using hi)]

theorem extZ_form (n n' : ℕ) (hn : n ≤ n') (x y : Fin n → E) :
    diagForm n' (fun _ => false) (extZ n n' x) (extZ n n' y) = diagForm n (fun _ => false) x y := by
  rw [diagForm_apply, diagForm_apply, ← sum_extZ n n' hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  show star (if h : i.1 < n then x ⟨i.1, h⟩ else 0) * _ * (if h : i.1 < n then y ⟨i.1, h⟩ else 0) = _
  by_cases h : i.1 < n <;> simp [h]

theorem extZ_isom (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n n' : ℕ) (hn : n ≤ n') :
    HSpace.IsIsomEmb (posSpace hstar n) (posSpace hstar n') (extZ n n') :=
  fun x y => extZ_form n n' hn x y

end Ext

structure Tow (D : D7) (t : ℕ) where
  Xs : ℕ → HSp D
  Xs_rank : ∀ j, j ≤ D.R.m → (Xs j).rank = D.R.k + j * (t + 1)
  Xs_sig : ∀ j, j ≤ D.R.m → (Xs j).SigOK ∧ (Xs j).IsDefinite
  Ys : ℕ → HSp D
  Ys_rank : ∀ j, j ≤ D.R.m → (Ys j).rank = D.R.r + j * t
  Ys_sig : ∀ j, j ≤ D.R.m → (Ys j).SigOK
  iXYs : ∀ j, (Xs j).V →ₗ[D.host.E] (Ys j).V
  iXYs_isom : ∀ j, j < D.R.m → HSpace.IsIsomEmb (Xs j) (Ys j) (iXYs j)
  iYXm : (Ys D.R.m).V →ₗ[D.host.E] (Xs D.R.m).V
  iYXm_isom : HSpace.IsIsomEmb (Ys D.R.m) (Xs D.R.m) iYXm

def recTow (D : D7) : Tow D D.R.t where
  Xs := D.sp.X
  Xs_rank := fun j hj => D.sp.X_rank j hj
  Xs_sig := fun j hj => ⟨D.sp.X_sig j, D.sp.X_def j hj⟩
  Ys := D.sp.Y
  Ys_rank := fun j hj => D.sp.Y_rank j hj
  Ys_sig := fun j _ => D.sp.Y_sig j
  iXYs := D.sp.iXY
  iXYs_isom := D.sp.iXY_isom
  iYXm := D.sp.iX'.comp D.sp.eYm.symm.toLinearMap
  iYXm_isom := fun x y => by
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm

def stdTow (D : D7) (t : ℕ) : Tow D t where
  Xs := fun j => posSpace star_isIntegral (D.R.k + j * (t + 1))
  Xs_rank := fun _ _ => rfl
  Xs_sig := fun _ _ => ⟨posSpace_sigOK _ _, fun _ => Or.inl rfl⟩
  Ys := fun j => posSpace star_isIntegral (D.R.r + j * t)
  Ys_rank := fun _ _ => rfl
  Ys_sig := fun _ _ => posSpace_sigOK _ _
  iXYs := fun _ => extZ _ _
  iXYs_isom := fun j hj => extZ_isom _ _ _ (by
    have := D.R.two_le_m
    unfold Ranks.r
    rw [Nat.mul_succ]
    omega)
  iYXm := extZ _ _
  iYXm_isom := extZ_isom _ _ _ (by
    have := D.R.two_le_m
    unfold Ranks.r
    rw [Nat.mul_succ]
    omega)

open Classical in

def tow (D : D7) (t : ℕ) : Tow D t := if h : t = D.R.t then h ▸ recTow D else stdTow D t

theorem tow_rec (D : D7) : tow D D.R.t = recTow D := by
  unfold tow
  rw [dif_pos rfl]

def chrExp (D : D7) (j : ℕ) : D.what₂.Tau → ℚ := fun τ =>
  if h : 1 ≤ j ∧ j ≤ D.R.m then -(D.hc τ).e ⟨j - 1, by omega⟩ else 0

def thetaZero (D : D7) : ThetaX D where
  AF := fun _ => PUnit
  cusp := fun _ => ⊤
  pet := fun _ _ _ => 0
  pet_add_left := fun _ _ _ _ => by simp
  pet_smul_left := fun _ _ _ _ => by simp
  pet_right := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  pet_symm := fun _ _ _ => by simp
  pet_pos := fun _ F hF => absurd (Subsingleton.elim F 0) hF
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => PUnit
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ _ _ _ => 0
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := fun t j _ => (tow D t).Ys j
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ F => F
  conjAF_add := fun _ _ _ => rfl
  conjAF_smul := fun _ _ _ => rfl
  conjAF_conjAF := fun _ _ => rfl
  conjAF_cusp := fun _ _ h => h
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ _ _ => 0
  Bper_right := fun _ _ _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ _ _ => 0
  Btop_right := fun _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Btop_add_left := fun _ _ _ _ _ _ => by simp
  Btop_smul_left := fun _ _ _ _ _ _ => by simp
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun _ _ _ => 0
  rowAF := fun _ _ => 0
  PhiY := fun _ _ => PUnit.unit
  PhiYup := fun _ _ => PUnit.unit
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaZero_row (D : D7) [∀ μ j, Subsingleton (D.what₂.Mult μ j)] : (thetaZero D).TieRowIsom :=
  fun μ j _ x y => by
    rw [Subsingleton.elim x 0, inner_zero_left]
    exact mul_zero _

theorem thetaZero_io (D : D7) [∀ μ j, Subsingleton (D.what₂.Mult μ j)] : (thetaZero D).TieIo :=
  fun μ j _ y x => by
    rw [Subsingleton.elim x 0, inner_zero_right]
    exact mul_zero _

theorem thetaZero_bm (D : D7) (h : ∀ u μ φ F, D.what₂.perCol u μ φ F = 0) : (thetaZero D).TieBm :=
  fun u μ φ F => (h u μ φ F).trans (mul_zero _).symm

end Formalism.MainNotions.Inhab

end
end


import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.TLC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem omp_adj_pd (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg r (fun g => star (adjugate (Zhat k r z z' g) a b)) := by
  have e : (fun g => star (adjugate (Zhat k r z z' g) a b)) = fun g =>
      (fun _ => ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ)))) g *
        (((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ).det := by
    funext g
    rw [adjugate_fin_succ_eq_det_submatrix, star_mul', det_conjTranspose, star_pow, star_neg, star_one]
  rw [e]
  have := pd_mul (pd_const (N := 2 * r + k + 1) ((-1 : ℂ) ^ ((b : ℕ) + (a : ℕ))) 0)
    (pd_det (l := r) (fun g => ((Zhat k r z z' g).submatrix b.succAbove a.succAbove)ᴴ) fun c d => by
      simpa [conjTranspose_apply] using zhat_star_pd k r z z' _ _)
  simpa using this

theorem omp_cofL_pd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg r (fun g => D.cofL Bs g s) := by
  unfold D.cofL
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega) (pd_mul (omp_adj_pd Bs.z Bs.z' (Fin.last r) a) (pd_const _ 0))

theorem omp_inv_pd (q s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (Hpk k r * gᴴ * Hpk k r) q s) := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  refine pd_sum _ fun u _ => pd_mono (show 1 + 0 ≤ 1 by omega) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun t _ => pd_mono (show 0 + 1 ≤ 1 by omega) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem omp_poly {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (j : Fin k) :
    U.IsPolyDeg (r + 1) (fun g => omC Bs B0 g j) := by
  unfold omC herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun i _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun q _ => pd_mono (show 0 + (r + 1) ≤ r + 1 by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (omp_inv_pd q s) (omp_cofL_pd Bs s))

end Formalism.FourierDecayAlt.P.TLC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtNonneg
section
open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem pair_prob {W : Type} {s t : Finset W} {a b : W → ℝ} (ha : TB.IsProb s a) (hb : TB.IsProb t b) :
    TB.IsProb (s ×ˢ t) (fun x => a x.1 * b x.2) := by
  refine ⟨fun x => mul_nonneg (ha.1 _) (hb.1 _), fun x hx => ?_, ?_⟩
  · rw [Finset.mem_product, not_and_or] at hx
    rcases hx with h | h
    · simp [ha.2.1 _ h]
    · simp [hb.2.1 _ h]
  · rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum, hb.2.2, mul_one]
    exact ha.2.2

theorem sum_pair {W : Type} (s t : Finset W) (a b f g : W → ℝ) (hb : ∑ y ∈ t, b y = 1)
    (ha : ∑ x ∈ s, a x = 1) :
    ∑ x ∈ s ×ˢ t, a x.1 * b x.2 * ((f x.1 + g x.2) / 2) =
      ((∑ x ∈ s, a x * f x) + ∑ y ∈ t, b y * g y) / 2 := by
  have key : ∀ x, ∑ y ∈ t, a x * b y * ((f x + g y) / 2) =
      (a x * f x + a x * ∑ y ∈ t, b y * g y) / 2 := by
    intro x
    have split : ∀ y, a x * b y * ((f x + g y) / 2) =
        (a x * f x / 2) * b y + (a x / 2) * (b y * g y) := by
      intro y; ring
    simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_product]
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ha]
  ring

theorem mix_sum {X W : Type} (Y : Finset X) (Ws : Finset W) (κ : X → X → ℂ) (c : ℂ) (p : W → ℂ)
    (G : W → X → X → ℂ) :
    ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (c * ∑ w ∈ Ws, p w * G w h h') =
      c * ∑ w ∈ Ws, p w * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G w h h' := by
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun h' _ => ?_
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

theorem av_eq (v : Fin S.f) (x : E) : S.base.av v x = ‖S.σ v x‖ := by
  show (S.pl v) x = ‖S.emb v x‖
  rw [← S.hemb v]
  rfl

theorem loc_join (σ : E →+* ℂ) (h : TB.Pt E) (s : ℕ) (t : E) :
    C.loc σ (TB.join h s t) = C.loc σ h ++ [(s, σ t)] := by
  simp only [C.loc, TB.join, List.map_append, List.map_cons, List.map_nil]

theorem ptSize_loc (σ : E →+* ℂ) (h : TB.Pt E) : D.ptSize (C.loc σ h) = TB.level h := by
  simp only [D.ptSize, C.loc, TB.level, List.map_map]
  rfl

theorem sizeAt_nonneg (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem gN_psd (hpos : C.ThmPPos S) (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) {i : ℕ} (hi : i ≤ S.G.r + 1) (w0 : S.W)
    (Y : Finset C.LPt) : TB.PSDOn Y (KB.gN S v ε i (w0.1 v)) := by
  have h := hpos v ε hε i hi w0 Y
  unfold TB.PSDOn at h ⊢
  have heq : (Matrix.of fun x y : Y => KB.gN S v ε i (w0.1 v) x y) =
      (((S.sizeAt v (w0.1 v))⁻¹ : ℝ) : ℂ) • Matrix.of fun x y : Y => S.gramLoc v ε i (w0.1 v) x y := by
    ext x y
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, KB.gN, div_eq_inv_mul,
      Complex.ofReal_inv]
  rw [heq]
  exact h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (sizeAt_nonneg S v _)))

theorem Nst_eq {ε : ℝ} {i : ℕ} (hi : i ≤ S.G.r + 1) (s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    S.base.Nst ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, KB.gN S v ε i (w.1 v)
      (C.loc (S.σ v) h ++ [(s, S.σ v t)]) (C.loc (S.σ v) h' ++ [(s, S.σ v t')]) := by
  have hsz : ((C.Word.size S.P w.1 : ℝ) : ℂ) = ∏ v, ((S.sizeAt v (w.1 v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    rfl
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) /
      ((C.Word.size S.P w.1 : ℝ) : ℂ) = _
  simp only [C.HidaSetting.gram, if_pos hi, loc_join, KB.gN, Finset.prod_div_distrib, hsz,
    Finset.sum_div, mul_div_assoc]

end

end Formalism.FourierDecayAlt.P.PBA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace UnipotentUpperFacts

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector

section gen

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

lemma agree (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (A B : Matrix n n ℂ)
    (hV : A * V = B * V) (hU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → A *ᵥ x = B *ᵥ x) : A = B := by
  have hV' : ∀ y, A *ᵥ (V *ᵥ y) = B *ᵥ (V *ᵥ y) := by
    intro y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hV]
  have key : ∀ x, A *ᵥ x = B *ᵥ x := by
    intro x
    have hd := decomp H V hΓ x
    have ex : x = V *ᵥ (prj H V *ᵥ x) + (x - V *ᵥ (prj H V *ᵥ x)) := by abel
    rw [ex, Matrix.mulVec_add, Matrix.mulVec_add, hU _ hd, hV']
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

lemma conj_pow (γ X : Matrix n n ℂ) (hγ : IsUnit γ.det) (p : ℕ) : (γ⁻¹ * X * γ) ^ p = γ⁻¹ * X ^ p * γ := by
  induction p with
  | zero => simp [Matrix.nonsing_inv_mul _ hγ]
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]

lemma blk_pow {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix p p ℂ) (D : Matrix q q ℂ) (m : ℕ) :
    (Matrix.fromBlocks A 0 0 D) ^ m = Matrix.fromBlocks (A ^ m) 0 0 (D ^ m) := by
  induction m with
  | zero => simp [Matrix.fromBlocks_one]
  | succ m ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply, pow_succ, pow_succ]; simp

end gen

lemma ut_sub_pow {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : (u - 1) ^ m = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, Matrix.one_apply]
  rcases lt_or_eq_of_le hji with h | h
  · rw [hu.1 i j h, if_neg (fun e => by subst e; exact lt_irrefl _ h), sub_zero]
  · subst h; rw [hu.2, if_pos rfl, sub_self]

variable {k r : ℕ}

lemma N_upper {g : B.Mat k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hji : j ≤ i) :
    g i j = if i = j then 1 else 0 := by
  have hc := ((WeylGroupFacts.nset_iff g).mp hg).2
  by_cases hj : j.val ≤ r + k
  · exact hc i j hj (Or.inl hji)
  · push Not at hj
    have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
      apply Matrix.inv_eq_left_inv
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, WeylGroupFacts.hpk_sq]
    have hci := ((WeylGroupFacts.nset_iff _).mp (WeylGroupFacts.mem_n_inv hg)).2
    rw [hinv] at hci
    have hle : j.val ≤ i.val := hji
    have hsj := GBasic.sig_val k r j
    have hsi := GBasic.sig_val k r i
    rw [if_pos (Or.inr hj)] at hsj
    rw [if_pos (Or.inr (by omega))] at hsi
    have h := hci (GBasic.sig k r j) (GBasic.sig k r i) (by omega) (Or.inl (by omega))
    rw [Matrix.mul_assoc, Hpk_mul_apply, mul_Hpk_apply, Matrix.conjTranspose_apply, GBasic.sig_sig,
      GBasic.sig_sig] at h
    have hs1 : GBasic.sgn k r (GBasic.sig k r j) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    have hs2 : GBasic.sgn k r (GBasic.sig k r i) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    rw [hs1, hs2, one_mul, mul_one] at h
    have hiff : (GBasic.sig k r j = GBasic.sig k r i) ↔ (i = j) := by
      constructor
      · intro e; have := congrArg (GBasic.sig k r) e; rw [GBasic.sig_sig, GBasic.sig_sig] at this; exact this.symm
      · intro e; rw [e]
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : i = j
    · rw [if_pos (hiff.mpr e), if_pos e, star_one]
    · rw [if_neg (fun e' => e (hiff.mp e')), if_neg e, star_zero]

lemma N_unip {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, N_upper hg i j hji, Matrix.one_apply, sub_self]

end UnipotentUpperFacts

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums

private lemma mul_mem_Nset' {k r : ℕ} {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : A ∈ Nset k r) (hB : B ∈ Nset k r) : A * B ∈ Nset k r := by
  obtain ⟨hAu, hAc, hAw⟩ := hA
  obtain ⟨hBu, hBc, hBw⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · have hAu' : Aᴴ * Hpk k r * A = Hpk k r := hAu
    have hBu' : Bᴴ * Hpk k r * B = Hpk k r := hBu
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [Matrix.conjTranspose_mul,
      show Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B by
        simp only [Matrix.mul_assoc], hAu', hBu']
  · intro a i hai
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hBc a (eI k r a) (le_refl a.val), if_pos rfl, mul_one]
      exact hAc a i hai
    · intro j _ hj
      by_cases hja : a.val ≤ j.val
      · rw [hBc a j hja, if_neg hj, mul_zero]
      · rw [not_le] at hja
        have hjr : j.val < r := lt_trans hja a.isLt
        have h1 := hAc ⟨j.val, hjr⟩ i (show j.val ≤ i.val by omega)
        rw [show eI k r ⟨j.val, hjr⟩ = j from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hBw j j hj1 hj2 hj1, if_pos rfl, mul_one]
      exact hAw i j hj1 hj2 hi
    · intro l _ hl
      by_cases hlr : r ≤ l.val
      · rw [hBw l j hj1 hj2 hlr, if_neg hl, mul_zero]
      · rw [not_le] at hlr
        have h1 := hAc ⟨l.val, hlr⟩ i (show l.val ≤ i.val by omega)
        rw [show eI k r ⟨l.val, hlr⟩ = l from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma dite_lt_eq_sum_smul_bvec {k r : ℕ} (g : Fin r → ℂ) :
    (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then g ⟨p.val, hp⟩ else 0) =
      ∑ c, g c • bvec (eI k r c) := by
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, smul_eq_mul, Pi.single_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val, hp⟩]
    · rw [if_pos (show p = eI k r ⟨p.val, hp⟩ from Fin.ext rfl), mul_one]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro h
      apply hc
      apply Fin.ext
      show c.val = p.val
      rw [h]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg, mul_zero]
    intro h
    apply hp
    rw [h]
    exact c.isLt

theorem c2_tau_mem : C2.TauMem := by
  intro k r z hz v hv
  set ξ : Fin r → ℂ := fun a => v a.castSucc (Fin.last r) with hξ
  set vX := v.submatrix Fin.castSucc Fin.castSucc with hvX
  have htau : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := rfl
  have hvX_mem : vX ∈ C2.UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij), fun i => hv.2 _⟩
  have hzW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → z i = 0 := fun i hi => hz.1 i (Or.inr hi)
  have hxi : C2.xiV k r ξ = ∑ c, ξ c • bvec (eI k r c) := by
    rw [← dite_lt_eq_sum_smul_bvec]
    rfl
  have hfc : ∀ c : Fin r, fvec k r z c.castSucc = bvec (eI k r c) := by
    intro c
    simp [fvec]
  have hfl : fvec k r z (Fin.last r) = z := by
    simp [fvec]
  have hact : ∀ b, C2.tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    rw [htau, ← Matrix.mulVec_mulVec, Fin.sum_univ_castSucc]
    simp only [hfc, hfl]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · have hmz : C2.mX k r vX *ᵥ z = z := by
        funext p
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single p]
        · by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p p hp.1 hp.2, if_pos rfl, one_mul]
          · have : z p = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro j _ hj
          by_cases hjW : r ≤ j.val ∧ j.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p j hjW.1 hjW.2, if_neg (Ne.symm hj), zero_mul]
          · have : z j = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hfl, hmz, HermitianXiVector.nEich_apply]
      have h1 : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
        HermitianXiVector.herm_X_right (C2.xiV k r ξ) z (HermitianXiVector.xiV_X ξ) hzW
      have h2 : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := hzz_real z
      have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hz.2)
      have hll : v (Fin.last r) (Fin.last r) = 1 := hv.2 _
      rw [h1, h2, hll, one_smul, ← hxi]
      have : ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) * (-(((-(Tz k r z) : ℝ) : ℂ))) = 1 := by
        push_cast
        field_simp
      rw [zero_smul, mul_zero, zero_smul, add_zero, add_zero, smul_smul, this, one_smul]
      exact add_comm _ _
    · have hmy : C2.mX k r vX *ᵥ bvec (eI k r b') =
          fun p => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0 := by
        rw [FlagSpanVanishing.mulVec_bvec]
        funext p
        exact mX_col_X vX p b'
      have hyX : ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
          (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0) i = 0 := by
        intro i hi
        simp only
        rw [dif_neg (by omega)]
      have h1 := HermitianXiVector.herm_X_left _ z hyX hzW
      have h2 := HermitianXiVector.herm_X_left _ (C2.xiV k r ξ) hyX (HermitianXiVector.xiV_apply_last_block_zero ξ)
      have hlow : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [hfc, hmy, HermitianXiVector.nEich_apply, h1, h2, hlow, zero_smul, add_zero]
      simp only [neg_zero, zero_smul, mul_zero, add_zero, smul_zero]
      exact (dite_lt_eq_sum_smul_bvec (k := k) (fun c => vX c b')).trans rfl
  refine ⟨?_, hact, uMap_eq hz _ v hact⟩
  rw [htau]
  exact mul_mem_Nset' (HermitianXiVector.nEich_mem hz ξ) (mX_mem vX hvX_mem)

theorem zhat_section_exists : C2.ZhatSection :=
  zhat_section_of_parts zhat_equivalence unipotent_map_frame c2_tau_mem standard_flag_property

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def KapPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) : Prop :=
  (∀ ρ σ, (Qr ρ).comp (Qr σ) = if ρ = σ then Qr ρ else 0) ∧ (∑ ρ, Qr ρ = 1) ∧
  (∀ ρ (v w : Wq), inner ℂ (Qr ρ v) w = inner ℂ v (Qr ρ w)) ∧
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT),
    (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (∑ ρ, f ρ • Qr ρ)

end preds

def GTKPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr

def GTKLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ ρ : M.Ty P,
      ∃ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, E.comp (Qr ρ) = E ∧
        inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) ∧
        ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Z.comp (Qr ρ) = Z →
          Z = inner ℂ (B.hsVec E) (B.hsVec Z) • E

def GTKapOfCut : Prop := GTKPt → GTKLine → GTKap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end


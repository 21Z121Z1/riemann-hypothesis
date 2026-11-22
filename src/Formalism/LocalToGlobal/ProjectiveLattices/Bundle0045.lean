import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.ContDiffAtOfDiff
import Formalism.LocalToGlobal.ProjectiveLattices.ValuedUnif
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsBlockProd
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

section GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

structure LetterBlock where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col

variable {Dw n}

def LetterBlock.poly (K : Type) [CommRing K] (B : LetterBlock Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c

def IsBlockProd {K : Type} [CommRing K] (P₁ : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → LetterBlock Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P₁ = ∏ j, (bs j).poly K

end GlobalTheory

section HeadContinuityAtZero

variable {D : D7} (T : Top D) (j : ℕ)

open Classical in

def FrameTie (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th : ℝ) {n : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  IsBlockProd P₁ → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
    x ∈ ((T.U j σ).X k).dom →
    ∃ x' : ((T.U j σ).X k).dom, (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x'.1 τ' i'‖ = 1) ∧
      (∀ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 = recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x) ∧
      ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x'.1 = ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x ∧
      ∃ (W : UnfAt (T.U j σ) k x') (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x'.1)
        (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
        TorusPins W Wu A L ∧
        A.T.l2 1 A.s = 1 ∧
        ∃ ρ : (Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) → ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim,
          (∀ y, L (Pi.single (W.e.symm y) 1) = EuclideanSpace.single (ρ y) 1) ∧
          ∃ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n A.T.dim),
            ReciprocityTheory.ChartRestriction.G.I2.Disj bs ∧
            MvPolynomial.rename (fun l : LtN (T.Q.Dw j) n =>
              ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter n A.T.dim)) (MvPolynomial.map ((starRingEnd ℂ).comp σ) P₁) =
              ReciprocityTheory.ChartRestriction.G.I2.P1 bs ∧
            ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree ∧
            ∃ K, ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T (T.Q.l.M ^ 2) n ((T.Q.l.M : ℂ) • LinearMap.id) K

def GenContain (nab : NabV (T.Q.Xo j) T.Q.c) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c)
    (uL : WtR D.host.E) {n : ℕ} (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom) (W : UnfAt (T.U j σ) k x) (Wu : UnitAt W)
    (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
    (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) (K : Finset (Fin n → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim)),
    ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T (T.Q.l.M ^ 2) n ((T.Q.l.M : ℂ) • LinearMap.id) K →
    TorusPins W Wu A L →
    ∃ jb : (Fin n → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) → Fin (N + 1), Set.InjOn jb K ∧
      ∀ b ∈ K, ∃ (xd x2 : Fin n → (T.Q.Dw j).La) (f : T.R j), IsThRule (T.Q.Xo j) T.Q.c nab xd P₁ f ∧
        (∀ b', x2 b' ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) ∧
        (∀ b', x2 b' - xd b' ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) ∧
        b = (fun b' => -((((T.Q.l.M : ℂ) ^ 2)⁻¹) • L (star (W.Pm (W.F.t (W.ik k) (x2 b')))))) ∧
        ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k x))‖ ≤ recNrm (T.U j σ) xR uL.1 uL.2 (wR (jb b)) k x.1

def RunPar (th tableLineDegreeFive DF cc : ℝ) {n : ℕ} (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  (P₁.totalDegree : ℝ) = DF ∧
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom)
    (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1) (nb : ℕ)
    (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n A.T.dim), ReciprocityTheory.ChartRestriction.G.I2.Disj bs →
    ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree →
    ∃ P : ReciprocityTheory.ChartRestriction.G.I2.Par A.T (ReciprocityTheory.ChartRestriction.G.I2.DF bs), P.q = T.Q.l.M ^ 2 ∧
      ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) P.q P.R0 = th ∧
      (1 / 2 : ℝ) * ((ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E : ℝ) * A.T.r * n * Real.log P.q +
        n * (Real.log 24 + (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ) / 2 *
          Real.log (2 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ))) +
        (A.T.r + 2) * Real.log 2) ≤ tableLineDegreeFive ∧
      ∃ PP : ℝ, 16200 * Real.pi * n * (P.m : ℝ) ^ 4 *
          (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ) ^ 4 ≤ PP ∧
        cc = ReciprocityTheory.ChartRestriction.G.I2.RR (E := D.host.E) * PP * DF ^ 2 / P.q

theorem i2iAt_of (hL : LawsP T) (hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c)
    (hnab : ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab)
    (w : WeightFamilies.Wt D j) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (hP : P₁ ∈ harmA T.Q.c (wtA w) w.n)
    (hP₁ : IsBlockProd P₁)
    (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th tableLineDegreeFive DF cc : ℝ)
    (hw : ∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2)
    (hTV : ThetaValCSt) (hGC : GenContain T j nab xR wR uL P₁) (hFT : FrameTie T j xR wR uL th P₁)
    (hRP : RunPar T j th tableLineDegreeFive DF cc P₁) :
    I2AtFramePoints (T.U j) xR wR uL th tableLineDegreeFive DF cc := by
  classical
  intro σ hσ k x hx
  obtain ⟨x', hu, hrec, hphi, W, Wu, A, L, hpin, hl2, ρ, hρ, nb, bs, hdisj, hren, hdeg, K, hK⟩ :=
    hFT hP₁ hw σ hσ k x hx
  obtain ⟨hDF, hRP'⟩ := hRP
  obtain ⟨P, hq, hth, hP14, PP, hPP, hcc⟩ := hRP' σ hσ k x' A nb bs hdisj hdeg
  have hM0 : 0 < T.Q.l.M := by
    rcases Nat.eq_zero_or_pos T.Q.l.M with h | h
    · have := P.hq
      rw [hq, h] at this
      simp at this
    · exact h
  have hMpos : (0 : ℝ) < T.Q.l.M := by exact_mod_cast hM0
  have hπ : ReciprocityTheory.ChartRestriction.G.I2.IsPi A.T P.q ((T.Q.l.M : ℂ) • LinearMap.id) := by
    rw [hq]; exact I2FramePointLemmas.isPi_nat A.T T.Q.l.M
  have hK' : ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T P.q w.n ((T.Q.l.M : ℂ) • LinearMap.id) K := by
    rw [hq]; exact hK
  have hI := ReciprocityTheory.ChartRestriction.G.I2.I_holds D.host.E A.T w.n nb bs hdisj P _ hπ A.s A.s_mem A.s_ne K hK'
  rw [hl2, one_pow, mul_one, hq] at hI
  have hNs := (ReciprocityTheory.ChartRestriction.G.I2.N_holds D.host.E A.T (T.Q.l.M ^ 2) w.n ((T.Q.l.M : ℂ) • LinearMap.id)
    (hq ▸ P.hq) (I2FramePointLemmas.isPi_nat A.T T.Q.l.M) A.s A.s_mem A.s_ne K hK).1
  obtain ⟨jb, hinj, hb⟩ := hGC σ hσ k x' W Wu A L K hK hpin
  have hLinj : Function.Injective L := by
    intro z z' hzz
    by_contra hne
    have hd : star (z - z') ≠ 0 := star_ne_zero.2 (sub_ne_zero.2 hne)
    have hpos := Wu.pos _ hd
    have h0 := hpin.2.1 (z - z') (z - z')
    rw [map_sub, hzz, sub_self] at h0
    have h00 : ReciprocityTheory.ChartRestriction.G.I2.Hf (0 : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) 0 = 0 := by
      simp [ReciprocityTheory.ChartRestriction.G.I2.Hf]
    rw [h00] at h0
    have h0' : hermForm Wu.Hm (star (z - z')) (star (z - z')) = 0 := star_eq_zero.1 h0.symm
    rw [h0'] at hpos
    simp at hpos
  have hρi : Function.Injective ρ := by
    intro y y' hy
    have h' : L (Pi.single (W.e.symm y) 1) = L (Pi.single (W.e.symm y') 1) := by rw [hρ, hρ, hy]
    have h'' := hLinj h'
    by_contra hne
    have hne' : W.e.symm y ≠ W.e.symm y' := fun h => hne (W.e.symm.injective h)
    have := congrFun h'' (W.e.symm y)
    simp [hne'] at this
  have hρ'i : Function.Injective (fun l : LtN (T.Q.Dw j) w.n =>
      ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter w.n A.T.dim)) := by
    rintro ⟨τ, i, b⟩ ⟨τ', i', b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hb, hr⟩ := h
    have := hρi hr
    simp only [Sigma.mk.inj_iff] at this
    obtain ⟨rfl, hi⟩ := this
    obtain rfl := eq_of_heq hi
    subst hb
    rfl
  have hdir : (fun l : LtN (T.Q.Dw j) w.n => Pi.single l.2.2 (L (Pi.single (W.e.symm ⟨l.1, l.2.1⟩) 1))) =
      ReciprocityTheory.ChartRestriction.G.I2.dir ∘ (fun l : LtN (T.Q.Dw j) w.n =>
        ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter w.n A.T.dim)) := by
    funext l
    simp only [Function.comp_apply, ReciprocityTheory.ChartRestriction.G.I2.dir, hρ]
  have hpt : ∀ b ∈ K, ‖ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (ReciprocityTheory.ChartRestriction.G.I2.P1 bs) ReciprocityTheory.ChartRestriction.G.I2.dir
      (A.T.U (T.Q.l.M ^ 2) b (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) 0‖ ≤
      (T.Q.l.M : ℝ) ^ P₁.totalDegree * recNrm (T.U j σ) xR uL.1 uL.2 (wR (jb b)) k x'.1 := by
    intro b hbK
    obtain ⟨xd, x2, f, hf, hx2a, hx2b, hbeq, hle⟩ := hb b hbK
    have hv := hTV D T hL j hj nab hnab w xd P₁ hP f hf σ hσ k x' hu W Wu A L hpin x2 hx2a hx2b
    have hdiff : Differentiable ℂ (A.T.U (T.Q.l.M ^ 2) b
        (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) := (hNs b hbK).1
    rw [← hbeq, hdir, ← I2FramePointLemmas.polyDeriv_rename (I2FramePointLemmas.contDiffAt_of_diff hdiff 0) _ hρ'i, hren] at hv
    have hn : ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k x'))‖ = ((T.Q.l.M : ℝ)⁻¹) ^ P₁.totalDegree *
        ‖ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (ReciprocityTheory.ChartRestriction.G.I2.P1 bs) ReciprocityTheory.ChartRestriction.G.I2.dir
          (A.T.U (T.Q.l.M ^ 2) b (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) 0‖ := by
      rw [hv, norm_mul, norm_pow, norm_inv, Complex.norm_natCast, norm_star]
    rw [hn] at hle
    calc _ = (T.Q.l.M : ℝ) ^ P₁.totalDegree * (((T.Q.l.M : ℝ)⁻¹) ^ P₁.totalDegree *
          ‖ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (ReciprocityTheory.ChartRestriction.G.I2.P1 bs) ReciprocityTheory.ChartRestriction.G.I2.dir
            (A.T.U (T.Q.l.M ^ 2) b (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) 0‖) := by
            rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hMpos.ne', one_pow, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)
  have hsum : ∑ b ∈ K, ‖ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (ReciprocityTheory.ChartRestriction.G.I2.P1 bs) ReciprocityTheory.ChartRestriction.G.I2.dir
      (A.T.U (T.Q.l.M ^ 2) b (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) 0‖ ^ 2 ≤
      (T.Q.l.M : ℝ) ^ (2 * P₁.totalDegree) * ∑ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 ^ 2 := by
    calc _ ≤ ∑ b ∈ K, ((T.Q.l.M : ℝ) ^ P₁.totalDegree *
          recNrm (T.U j σ) xR uL.1 uL.2 (wR (jb b)) k x'.1) ^ 2 :=
          Finset.sum_le_sum fun b hb => pow_le_pow_left₀ (norm_nonneg _) (hpt b hb) 2
      _ = (T.Q.l.M : ℝ) ^ (2 * P₁.totalDegree) *
          ∑ b ∈ K, recNrm (T.U j σ) xR uL.1 uL.2 (wR (jb b)) k x'.1 ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Finset.sum_image (f := fun i => recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 ^ 2)
            (fun a ha b hb h => hinj ha hb h)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hS := hI.trans hsum
  have hJpos := I2FramePointLemmas.jbound_pos A.T P w.n
  have hn1 : 1 ≤ w.n := I2FramePointLemmas.one_le_n_of_DF bs P.hDF
  have hdgR : ((ReciprocityTheory.ChartRestriction.G.I2.DF bs : ℕ) : ℝ) = DF := by rw [hdeg]; exact hDF
  have hlog := I2FramePointLemmas.log_bound A.T P w.n hn1 T.Q.l.M hq tableLineDegreeFive cc PP hP14 hPP (by rw [hdgR]; exact hcc)
  have hph : ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x = P.ph := by
    rw [← hphi, ReciprocityTheory.ChartRestriction.G.I2.Par.ph, hth]
    exact ((ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf.torusAtLa1_holds _ _ _ x'.1 x'.2 A.T
      (ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.torusAtIs_holds _ _ _ _ A)).2 th).symm
  rw [hph]
  simp only [← hrec]
  set S := ∑ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 ^ 2 with hSdef
  have hMp : (0 : ℝ) < (T.Q.l.M : ℝ) ^ (2 * P₁.totalDegree) := pow_pos hMpos _
  have hS0 : 0 < S := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hMp.le (not_lt.1 h)
    linarith
  rw [Real.log_sqrt hS0.le]
  have hlJ : Real.log (P.Jbound w.n) ≤ ((2 * P₁.totalDegree : ℕ) : ℝ) * Real.log T.Q.l.M + Real.log S := by
    have := Real.log_le_log hJpos hS
    rwa [Real.log_mul hMp.ne' hS0.ne', Real.log_pow] at this
  push_cast at hlJ
  rw [hDF] at hlJ
  rw [hdgR] at hlog
  linarith

end HeadContinuityAtZero

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem wchar_nsmul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) (k : ℕ) :
    wchar (k • e) t = wchar e t ^ k := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem wchar_ne_zero {S : Type} [Field S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) : wchar e t ≠ 0 := by
  unfold wchar
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero

end Weights

variable {D : D7} {T : Top D}

theorem exponent_base_weight_zero (j : ℕ) : ex (T.Q.Dw j) (wtA (wt0 D j)) (wt0 D j).n = 0 := by
  funext i
  cases i <;> simp [ex, wtA, wt0, wscalar, ext0]

theorem ex_addL {j : ℕ} (wL : WeightFamilies.Wt D j) (k : ℕ) :
    ex (T.Q.Dw j) (wtA (addL (wt0 D j) wL k)) (addL (wt0 D j) wL k).n = k • ex (T.Q.Dw j) (wtA wL) wL.n := by
  induction k with
  | zero => rw [addL_zero, exponent_base_weight_zero, zero_smul]
  | succ k ih => rw [← wadd_addL, wtA_wadd, n_wadd, ex_add, ih, succ_nsmul, add_comm]

variable (j : ℕ)

def evIHom {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) : T.R j →+* Tc.Fr where
  toFun := evI y
  map_one' := by
    letI := io.toAlgebra
    exact evalAt_one _ _ y.1 y.2.1
  map_mul' := evI_mul y
  map_zero' := by
    letI := io.toAlgebra
    exact evalAt_zero _ _ y.1
  map_add' := evI_add y

def chiI {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) :
    AddMonoidAlgebra (T.R j) (Deg D j) →+* Tc.Fr :=
  AddMonoidAlgebra.liftNCRingHom (evIHom j y) (1 : Multiplicative (Deg D j) →* Tc.Fr) (fun _ _ => Commute.all _ _)

theorem chiI_single {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (d : Deg D j) (r : T.R j) :
    chiI j y (AddMonoidAlgebra.single d r) = evI y r := by
  unfold chiI
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp only [MonoidHom.one_apply, mul_one]
  rfl

theorem chiI_smul {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (a : T.Q.c.F)
    (f : AddMonoidAlgebra (T.R j) (Deg D j)) : chiI j y (a • f) = io a * chiI j y f := by
  refine AddMonoidAlgebra.induction_linear f ?_ ?_ ?_
  · rw [smul_zero, map_zero, mul_zero]
  · intro f g hf hg
    rw [smul_add, map_add, map_add, hf, hg, mul_add]
  · intro d r
    rw [show a • AddMonoidAlgebra.single d r = AddMonoidAlgebra.single d (a • r) from AddMonoidAlgebra.smul_single a d r,
      chiI_single, chiI_single, evI_smul]

theorem chiI_inc (h : LawsP T) {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : chiI j y (incG deg (cutR T.C j) w F) = evI y (F : T.R j) := by
  rw [incG_apply, chiI_single]

section Main

variable {D : D7} {T : Top D}

theorem evR_eq_of_map {j : ℕ}
    (hWD : EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z))
    {f : T.R j} (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (w : FrPt (T.Q.Xo j) T.Q.c S) (p : TRing T.Q.c.F)
    (φ : p.R →ₐ[T.Q.c.F] S) (y : FrPt (T.Q.Xo j) T.Q.c p.R) (h : FrMap φ y w) :
    evR (T.Q.Xo j) T.Q.c f w = φ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact hWD f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h

def RealPtNZSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] : Prop :=
  ∀ ζ : PtsG G la, ∃ (y : (extAll h j hj).Pt' la) (Tc : CDVR) (ι : Loc ζ →+* Tc.V) (_ : IsLocalHom ι)
    (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)) (ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr)
    (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))),
    (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) =
      nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ) (ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)))) ∧
    (∀ x : ↥(Frac0 (recPlus h j hj) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) hu (x : Lw (recPlus h j hj) la G.w) =
        phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w x)) ∧
    ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
      ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0

theorem realPtSt_of_NZ {h : LawsP T} {j : ℕ} {hj : InR D j} {hG : GenFrEx (T.Q.Xo j) T.Q.c} {ka wL wF : WeightFamilies.Wt D j}
    {G : GlobalFamilyData (recPlus h j hj) ka wL wF} {la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)}
    {hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)} [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hR : RealPtNZSt h j hj hG G la hU) :
    @RealPtSt D (recB h.toLawsCore) T.G.P j (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) ka wL wF G la hU
      ‹∀ ζ : PtsG G la, IsDVRAt ζ› := by
  intro ζ
  obtain ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg, -⟩ := hR ζ
  exact ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg⟩

end Main

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def rdR {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u) :=
  rdU (T.U j T.σ₀) F.1

def TieReadSt : Prop :=
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp),
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k)) ∧
  ∀ u : WeightFamilies.Wt D j, ReciprocityTheory.ChartRestriction.G.PullbackSections.JInjRd T j (wtA u) u.n

abbrev KT (T : Top D) (j N : ℕ) : Type := FractionRing (MvPolynomial (Idx D j N) T.Q.c.F)

def IsIoExt {N : ℕ} (io : KT T j N →+* ℂ) : Prop :=
  ∀ a : T.Q.c.F, io (algebraMap T.Q.c.F (KT T j N) a) = T.σ₀ a

def rdSec {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ)
    (i : Fin (WeightFamilies.dimY D j + 1)) :=
  ∑ k', io (algebraMap (MvPolynomial (Idx D j G.N) T.Q.c.F) (KT T j G.N) (MvPolynomial.X (i, k'))) •
    rdR h j (G.w k')

def TieMaxCuspSt (CR Tt c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : (recB h.toLawsCore).Cusp j ka,
    F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt c j ka ↔
      ∀ k, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt c j)

end Formalism.L2.Pj
end
end


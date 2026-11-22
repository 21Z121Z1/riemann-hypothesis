import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableInvCube
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GSup (S : C.HidaSetting E Wp Wq) (ε : ℝ) (b n : ℕ) (P : ℝ) : Prop :=
  ∀ w' ∈ S.base.Wall, S.base.cnt w' + n * C.Kst ≤ S.Ntop →
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ t : crystallineComparison.V S.f, Good t →
          (KB.NstV S ε (b + n - 1) n w' Y κ t t).re ≤
            P * ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ

theorem integrable_inv_cube : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem zero_mem_dual {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) : (0 : crystallineComparison.V f) ∈ crystallineComparison.dualSet La := by
  intro z _; simp [Lat.psi_zero]

theorem one_le_tsum_mL {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (g : ℝ)
    (hs : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :
    1 ≤ ∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := by
  have := hs.le_tsum (⟨0, zero_mem_dual La⟩ : crystallineComparison.dualSet La) (fun σ _ => mL_nonneg K L hL _)
  simpa [mL_zero] using this

theorem gN_one_reg (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (w : S.W) (h h' : C.LPt) (hh : D.ptSize h = b - 1)
    (hh' : D.ptSize h' = b - 1) :
    ContinuousOn (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) {0}ᶜ ∧
    Integrable (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) := by
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hC⟩, -⟩ := hI v ε hε b hb hbr w h h' hh hh'
  have e : b + 1 - 1 = b := by omega
  rw [e]
  have hcongr : ∀ c ∈ ({0}ᶜ : Set ℂ), φ c / (S.sizeAt v (w.1 v) : ℂ) =
      KB.gN S v ε b (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
    intro c hc
    unfold KB.gN
    rw [hφ c hc]
  have hφi : Integrable φ :=
    Integrable.mono' (integrable_inv_cube.const_mul Cφ) hφc.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hφc.div_const _).continuousOn.congr fun c hc => (hcongr c hc).symm, ?_⟩
  refine (hφi.div_const (S.sizeAt v (w.1 v) : ℂ)).congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with c hc
  exact hcongr c hc

def SumBound (f : ℕ) (Cs : ℝ) : Prop :=
  ∀ (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2)

theorem size_step (f : ℕ) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (dl R g : ℝ) (hdl : 0 ≤ dl) (hR : 0 < R) (hg : 0 < g)
    (L thr : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v ∧ L v ≤ thr v) (M V : ℝ) (hM : M ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2))
    (hV : dl * (∏ v, Cs * (1 + (R * thr v / g) ^ 2)) / R ^ (2 * f) ≤ V) : dl * M / R ^ (2 * f) ≤ V := by
  refine le_trans ?_ hV
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left (hM.trans ?_) hdl
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have h1 : R * L v / g ≤ R * thr v / g := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL v).2 hR.le) hg.le
  have h0 : 0 ≤ R * L v / g := div_nonneg (mul_nonneg hR.le (hL v).1) hg.le
  nlinarith

theorem gsup_one (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hpos : C.ThmPPos S) (hI : KB.IntAll S)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v) (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hbr : b ≤ S.G.r + 1) (hX : ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v) (Cs : ℝ) (hCs1 : 1 ≤ Cs)
    (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b 1) * (∏ v, Cs * (1 + (R * thr S b 1 v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b 1) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b 1 ∧ GSup S ε b 1 P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ X b v := fun v => (hX v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => X b v) hR hg' hL0
  have hM1 := one_le_tsum_mL (Lstd S.f R) C.Kst (fun v => X b v) hL0 (S.g : ℝ) hsm
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) with hMdef
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b 1 := Finset.prod_nonneg fun v _ => (dlB_pos S hg b 1).le
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b 1) * M / R ^ (2 * S.f), by positivity,
    size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b 1) hX M _ hsle hRB, ?_⟩
  intro w' hw' hcnt
  simp only [one_mul] at hcnt ⊢
  obtain ⟨θ, hθ, hWV⟩ := Formalism.FourierDecayAlt.P.plane_wave_bound E Wp Wq S X hW ε hε b hb hbr w' hw' hcnt
  obtain ⟨θ', hθ', hmix⟩ := tsum_mix (S.base.Wb (S.base.cnt w' + C.Kst))
    (fun σ : crystallineComparison.dualSet (Lstd S.f R) => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm (by linarith)
    (fun σ => θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))) (fun σ => hθ _)
  refine ⟨θ', hθ', fun Y hY κ hκ t ht => ?_⟩
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + 1 - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(1, c)]) (C.loc (S.σ v) h' ++ [(1, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + 1 - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(1, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(1, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  have hreg := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) =>
    gN_one_reg S hI v ε hε b hb hbr w' (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [JCx1.needs.ptSize_loc]; exact hY h hh) (by rw [JCx1.needs.ptSize_loc]; exact hY h' hh')
  set N0 : S.W → ℝ := fun u => S.base.N0 ε (b - 1) u Y κ
  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd S.f R),
      ‖Hh Y κ (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h'))
        ((S.g : ℝ) • σ)‖ ≤ crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
          ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u := by
    intro σ _
    exact bound_mL C.Kst (fun v => X b v) hL0 _ _ _ (hWV Y hY κ hκ _ _)
  have hH := herglotz_plain (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b 1)
    (fun _ => dlB_pos S hg b 1)
    (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h')) (fun _ _ _ _ => rfl)
    (Lstd S.f R)
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
      ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u)
    (hmix N0).1 (fun σ hσ => hF σ hσ)
    t {t} (by simp)
  rw [(hmix N0).2, hcov, Finset.sum_singleton] at hH
  have hN : Nz Y κ D t = (KB.NstV S ε (b + 1 - 1) 1 w' Y κ t t).re := by
    simp only [Nz, if_pos ht]
    rw [nstV_eq]
    rfl
  rw [hN] at hH
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  linarith [hH]

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

section reindex

variable {K A S S' : Type}

def relabel (e : S' → S) (w : List (Wd.Letter K S')) : List (Wd.Letter K S) :=
  w.map fun l => ⟨l.plus, e l.intersection_update_fsHerm_neg_one, l.pt⟩

open Classical in

def extA [Zero A] (e : S' → S) (M : Wd.SlopeTestRemainingChoices S' A) : Wd.SlopeTestRemainingChoices S A :=
  Matrix.of fun a b => if ∀ s, (∀ s', e s' ≠ s) → a s = b s then M (a ∘ e) (b ∘ e) else 0

end reindex

def Reindex : Prop :=
  ∀ (K A S S' : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [Fintype S] [DecidableEq S]
    [Fintype S'] [DecidableEq S'] (e : S' → S), Function.Injective e →
    (∀ (QQ : K → Wd.M2 A) (w : List (Wd.Letter K S')), Wd.RRw QQ (relabel e w) = extA e (Wd.RRw QQ w)) ∧
      ∀ (σ : Wd.Site A) (w : List (Wd.Letter K S')), Wd.bT σ (relabel e w) = extA e (Wd.bT σ w)

def PositionedOf : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)), (w.map Wd.Letter.intersection_update_fsHerm_neg_one).Nodup →
    (∀ l ∈ w, star l.pt = l.pt) →
    ∃ σ : Fin (w.map fun l => ((l.plus, l.pt.re) : C.Letter)).length → S, Function.Injective σ ∧
      relabel σ (D.positionted (w.map fun l => ((l.plus, l.pt.re) : C.Letter))) = w

def TowerAt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq),
    ∃ T : D.LevTower k r Wp Wq, T.base.z = Bs.z ∧ T.base.z' = Bs.z' ∧ T.base.π = Bs.π ∧ T.base.π' = Bs.π' ∧
      D.TowerNormalised T

def PlAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π'

def SiteTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k ρ : ℕ)
    (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)) (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq))
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))
    (L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ))
    (st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ)
    (sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))))
    (s : ℂ),
    inWb k ρ z → inWb k ρ z' → IsActualLevel X L → IsActualLevel Xs Ls →
    (∀ Y, st.QQ Y = s • X.QQ Y) → (∀ Y, sts.QQ Y = s • Xs.QQ Y) →
    ∀ t : ℂ, t ≠ 0 →
      ∃ T : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π' →ₗ[ℂ]
          RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)),
        (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
          (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) (consC t c) (ιLev k 1 ρ g)) ∧
        (∀ l : Fin ρ, Rel T (L.p (shS l)) (Ls.p l) ∧ Rel T (L.c (shS l)) (Ls.c l) ∧ Rel T (L.ci (shS l)) (Ls.ci l)) ∧
        (∀ (n : ℕ) (hn : n ≤ ρ) (Y : ℂ),
          MRel T (QQi L st ⟨n + 1, by omega⟩ Y) (QQi Ls sts ⟨n, by omega⟩ Y)) ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)),
          (∀ l : Fin ρ, ARel T (bTl L (shS l) w) (bTl Ls l w)) ∧
          ∀ (n : ℕ) (hn : n ≤ ρ), ARel T (RRi L st ⟨n + 1, by omega⟩ w) (RRi Ls sts ⟨n, by omega⟩ w)

def shiftCf {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) : Cf r i :=
  fun l => c'' ⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩

def LevTrClauses {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (i : Fin (P.r + 1)) (c : Fin P.r → ℂ)
    (Di : B.RealPlaceData P.k (P.r - i) Wp Wq) (μi : Measure (Mt P.k (P.r - i)))
    (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
    (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
    (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π') : Prop :=
  (∀ Φ c'' g, (T Φ : Fn P.k (P.r - i) (Wq →L[ℂ] Wp)) c'' g =
      (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c (shiftCf i c'')) (D.castM (by omega) (ιLev P.k i (P.r - i) g))) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))) ∧
    (∀ (n : ℕ) (hn : n + i ≤ P.r) (Y : ℂ),
      MRel T (QQi L st ⟨n + i, by omega⟩ Y) (QQi Li sti ⟨n, by omega⟩ Y)) ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)),
      (∀ l : Fin (P.r - i), ARel T (bTl L ⟨l.val + i, by omega⟩ w) (bTl Li l w)) ∧
      (∀ (n : ℕ) (hn : n + i ≤ P.r), ARel T (RRi L st ⟨n + i, by omega⟩ w) (RRi Li sti ⟨n, by omega⟩ w)) ∧
      (WordOK P z z' π π' st l0 w → WordOK (JC.parLev P i) Di.z Di.z' Di.π Di.π' sti l0 w)

def LevTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
      (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'),
      IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
        LevTrClauses P μ L st l0 i c Di μi Li sti T

def LevTransportHer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')))
      (T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'),
      IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ Φ ∈ herKc S P z z' π π' L st l0 Bs i,
          T Φ ∈ herKc S (JC.parLev P i) Di.z Di.z' Di.π Di.π' Li sti l0 Di 0

def JFScale : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs Bs' : B.RealPlaceData k r Wp Wq), Bs.z = Bs'.z → Bs.z' = Bs'.z' → Bs.π = Bs'.π →
    Bs.π' = Bs'.π' → ∃ κ : ℂ, ∀ F, B.JF Bs F = κ • B.JF Bs' F

def SliceStepHer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r) (l0 : ℕ), 1 ≤ l0 → l0 ≤ P.k →
    ∀ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')))
      (Xs : ActualOps (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (T.bs (j + 1)).z (T.bs (j + 1)).z'
        (T.bs (j + 1)).π (T.bs (j + 1)).π')
      (μs : Measure (Mt P.k (P.r - (j + 1))))
      (Ls : R.LevelData (Pr (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π')) (P.r - (j + 1)))
      (sts : Fr.Start (Pr (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π'))),
    IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 →
    IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Xs μs Ls
      sts l0 →
    ∀ (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
        RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π') (t : ℂ),
      t ≠ 0 →
      (∀ Φ c g, (Tt Φ : Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast (by omega) l))
          (D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g))) →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      WordOK (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' stj l0 w →
      ∀ Ψ ∈ herKc S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0,
        Tt ((bTl Lj (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w a b).1 Ψ) ∈
          herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
            l0 (T.bs (j + 1)) 0

end Formalism.FourierDecayAlt.P.PTie
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormTwoSidedTranslateGrowthBound
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem norm_two_sided_translate_growth_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖e0 (x⁻¹ * A * y)‖ₑ ≤ ENNReal.ofReal (|C0| * (B.gN x * B.gN y) ^ b) * ‖B.gN A ^ (-b)‖ₑ := by
  have hxi := (MatrixMultiplicationContinuity.uh_inv hx).1
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hxi hA) hy
  have h1 : 1 ≤ B.gN (x⁻¹ * A * y) := ((hNI k r).2 _ hM).2
  have hAp : 0 ≤ B.gN A ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hxy : 0 ≤ (B.gN x * B.gN y) ^ b := Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  rw [Real.enorm_eq_ofReal hAp, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hxy), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc ‖e0 (x⁻¹ * A * y)‖ ≤ C0 * B.gN (x⁻¹ * A * y) ^ (-a) := hb0e _ hM
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ |C0| * ((B.gN x * B.gN y) ^ b * B.gN A ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_sandwich hNI hx hA hy hb0) (abs_nonneg _)
    _ = |C0| * (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by ring

theorem lam_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hq : ∀ᵐ q ∂μq, Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    abelian₂ e0 γ μp μq x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-b)‖ₑ ∂μq ∂μp := by
  unfold abelian₂
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hq] with q hqq
  have hQi := (MatrixMultiplicationContinuity.uh_inv hqq).1
  have hA : (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ ∈
      Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hpp hγ) hQi
  have e : (Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
      Matrix.of y = (Matrix.of x)⁻¹ * ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) *
      Matrix.of y := by simp only [Matrix.mul_assoc]
  rw [e]
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hA hy

theorem lambda_integral_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Lam1 e0 μp x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)‖ₑ ∂μp := by
  unfold Lam1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hpp hy

end Formalism.FourierDecayAlt.P.S3dx4
end
end


import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocalOfFibres
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0122

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem perm_id_of_mono {m : ℕ} (τ : Equiv.Perm (Fin m)) (h : StrictMono (fun l => (τ l).val)) : τ = 1 := by
  have hm : StrictMono τ := fun a b hab => Fin.lt_def.mpr (h hab)
  have hinv : StrictMono τ.symm := by
    intro a b hab
    by_contra hc
    have h' := hm.monotone (not_lt.mp hc)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
    exact absurd hab (not_lt.mpr h')
  refine Equiv.ext fun l => ?_
  have h1 : l ≤ τ l := hm.le_apply
  have h2 : l ≤ τ.symm l := hinv.le_apply
  have h3 := hm.monotone h2
  rw [Equiv.apply_symm_apply] at h3
  rw [Equiv.Perm.one_apply]
  exact le_antisymm h3 h1

theorem top_self {m N : ℕ} (a : Fin m → Fin N) (ha : Function.Injective a) :
    (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = a k then (1 : ℂ) else 0)) = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra H
      exact hσ (Equiv.ext fun l => by simpa using not_not.mp (fun h => H ⟨l, h⟩))
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (ha.ne hk)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem prod_ne_zero_imp {m N : ℕ} (a b : Fin m → Fin N) (σ : Equiv.Perm (Fin m))
    (h : ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0) ≠ 0) : ∀ k, a (σ k) = b k := by
  intro k
  by_contra hk
  exact h (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk))

private theorem leading_term_identity_lemma {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (P : (Fin m → Fin n) → Prop) [DecidablePred P] (d : (Fin m → Fin n) → ℂ)
    (fa fb : (Fin m → Fin n) → Fin m → Fin n) (s0 : ℂ) (c0 : Fin m → Fin n) (h0 : P c0)
    (h1 : ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c0 (σ k) = fb c0 k then (1 : ℂ) else 0) = 1)
    (hz : ∀ c, P c → c ≠ c0 → ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0) = 0) :
    ∃ C : Fin m → A, ∀ u : ℂ, (∑ c, if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) =
      algebraMap ℂ A (u ^ m * d c0) + ∑ l : Fin m, algebraMap ℂ A (u ^ (l : ℕ)) * C l := by
  have hP : PolyLe m (fun u => ∑ c, if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    refine pl_sum Finset.univ (fun c u => if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0)
      fun c _ => ?_
    by_cases hc : P c
    · simp only [hc, if_true]
      exact pl_lmul _ (qminor_poly E (fa c) (fb c) s0)
    · simp only [hc, if_false]
      exact pl_zero m
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun u => ?_⟩
  rw [← hC u]
  beta_reduce
  have hsplit : ∀ c, (if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      (if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) -
        (if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    intro c
    split_ifs
    · rw [mul_sub, Algebra.smul_def, ← map_mul]
      congr 2
      ring
    · simp
  have hsecond : (∑ c, if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      algebraMap ℂ A (u ^ m * d c0) := by
    rw [Finset.sum_eq_single c0]
    · rw [if_pos h0, h1, mul_one]
    · intro c _ hc
      split_ifs with hPc
      · rw [hz c hPc hc, mul_zero, mul_zero, map_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_sub_distrib, hsecond]
  abel

theorem leading_term_identity : LeadAA := by
  intro A _ _ k r E xi m hm
  classical
  have hxv : ∀ l, (xR k r m hm l).val = l.val := fun l => rfl
  have hxinj : Function.Injective (xR k r m hm) := fun a b h => Fin.ext (by rw [← hxv a, ← hxv b, h])
  have hxm : StrictMono (xR k r m hm) := fun a b hab => Fin.lt_def.mpr (by rw [hxv, hxv]; exact hab)
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun c => StrictMono c)
    (fun c => (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det)
    (fun _ => xR k r m hm) id 0 (xR k r m hm) hxm (top_self _ hxinj) (by
      intro c hc hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp (xR k r m hm) c σ (right_ne_zero_of_mul hσ)
      have hσm : StrictMono (fun l => (σ l).val) := by
        intro a b hab
        have h1 : c a < c b := hc hab
        rw [← heq a, ← heq b, Fin.lt_def, hxv, hxv] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ hσm
      apply hne
      funext l
      rw [← heq l, hσ1]
      rfl)
  refine ⟨C, fun u => ?_⟩
  have h := hC u
  simp only [id, add_zero] at h
  unfold AAx
  exact h

theorem leading_term_vector_identity : LeadAAv := by
  intro A _ _ k r E y m hm
  classical
  have hkey : ∀ l, keyS k r (sR k r m hm l) = l.val := by
    intro l
    have hl := l.isLt
    have hv : (sR k r m hm l).val = 2 * r + k - l.val := rfl
    unfold keyS
    rw [hv]
    split_ifs with h
    · omega
    · omega
  have hsinj : Function.Injective (sR k r m hm) := fun a b h =>
    Fin.ext (by rw [← hkey a, ← hkey b, h])
  have hsm : StrictMono (fun l => keyS k r (sR k r m hm l)) := fun a b hab => by
    simp only [hkey]
    exact hab
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun B => StrictMono (fun l => keyS k r (B l)))
    (fun B => (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) (B l)).det)
    id (fun _ => sR k r m hm) ((m : ℂ) - 1) (sR k r m hm) hsm (top_self _ hsinj) (by
      intro B hB hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp B (sR k r m hm) σ (right_ne_zero_of_mul hσ)
      have hB' : ∀ l, B l = sR k r m hm (σ.symm l) := by
        intro l
        have := heq (σ.symm l)
        rwa [Equiv.apply_symm_apply] at this
      have hσm : StrictMono (fun l => (σ.symm l).val) := by
        intro a b hab
        have h1 := hB hab
        simp only [hB', hkey] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ.symm hσm
      apply hne
      funext l
      rw [hB' l, hσ1]
      rfl)
  refine ⟨C, fun ell => ?_⟩
  have h := hC ell
  simp only [id] at h
  unfold AAv
  rw [show ell + (m : ℂ) - 1 = ell + ((m : ℂ) - 1) by ring]
  exact h

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdRearrange
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem measurePreserving_prod_rearrange {L M P N : Type*} [MeasurableSpace L] [MeasurableSpace M] [MeasurableSpace P] [MeasurableSpace N]
    (μL : Measure L) (μM : Measure M) (μP : Measure P) (μN : Measure N) [SigmaFinite μL] [SigmaFinite μM]
    [SigmaFinite μP] [SigmaFinite μN] :
    MeasurePreserving (fun p : L × (M × (P × N)) => (p.2.1, ((p.1, p.2.2.1), p.2.2.2)))
      (μL.prod (μM.prod (μP.prod μN))) (μM.prod ((μL.prod μP).prod μN)) := by
  have h1 := (measurePreserving_prodAssoc μL μM (μP.prod μN)).symm
  have h2 := (Measure.measurePreserving_swap (μ := μL) (ν := μM)).prod (MeasurePreserving.id (μP.prod μN))
  have h3 := measurePreserving_prodAssoc μM μL (μP.prod μN)
  have h4 := (MeasurePreserving.id μM).prod (measurePreserving_prodAssoc μL μP μN).symm
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext ⟨l, m, p, n⟩
  rfl

theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1)))
    (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ)) (he : MeasurePreserving e volume volume)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (c1 c2 : NNReal)
    (hN1 : S.μN = c1 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
    (hN2 : S.μN = c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) :
    S.μSS = (c1 * c2) • ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0')).map
      (fun p => OD.Xi S w e p.1 p.2) := by
  have sf : ∀ {V : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn V μ → SigmaFinite μ := by
    intro V μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := sf S.haarW
  haveI := sf S.haarW'
  haveI := sf hμ0
  haveI := sf hμ0'
  have m1 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z).measurable
  have m2 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z').measurable

  have hA : MeasurePreserving
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0'))
      ((S.μW.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0)).prod
        (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))) := by
    have h1 := (measurePreserving_prodAssoc (volume : Measure (C2.Lstidx w → ℂ))
      (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0))
      (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))).symm
    have h2 := (measurePreserving_prod_rearrange (volume : Measure (C2.Lstidx w → ℂ)) S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have h3 := ((MeasurePreserving.id S.μW).prod (he.prod (MeasurePreserving.id μ0))).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have := h3.comp (h2.comp h1)
    simp only [OD.nuR]
    convert this using 1
    all_goals first | rfl | (funext p; rfl)
  have hB : Measurable (Prod.map
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) :=
    (measurable_id.prodMap m1).prodMap (measurable_id.prodMap m2)
  have hXi : (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => OD.Xi S w e p.1 p.2) =
      (Prod.map
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) ∘
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2)) := by
    funext p; rfl
  rw [hXi, ← Measure.map_map hB hA.measurable, hA.map_eq,
    ← Measure.map_prod_map _ _ (measurable_id.prodMap m1) (measurable_id.prodMap m2),
    ← Measure.map_prod_map _ _ measurable_id m1, ← Measure.map_prod_map _ _ measurable_id m2,
    Measure.map_id, Measure.map_id]
  show (S.μW.prod S.μN).prod (S.μW'.prod S.μN) = _
  have e2 : S.μW'.prod S.μN = S.μW'.prod (c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) := by rw [← hN2]
  rw [e2, hN1]
  rw [ENNReal.smul_def c1, ENNReal.smul_def c2, ENNReal.smul_def (c1 * c2), Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNegBetaL
section
namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt NumberField

noncomputable section

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def betaL (S : C.HidaSetting E Wp Wq) : ℂ := ((4 * Real.pi / (S.g : ℝ) : ℝ) : ℂ)

theorem psi_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (betaL S) (σ * z) = KB.psiL S σ z := by
  unfold G.psi KB.psiL betaL
  congr 1
  rw [Complex.re_ofReal_mul]
  push_cast
  ring

theorem psi_neg_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (-betaL S) (σ * z) = KB.psiL S (-σ) z := by
  have h : G.psi (-betaL S) (σ * z) = G.psi (betaL S) (-σ * z) := by
    unfold G.psi
    rw [show -betaL S * (σ * z) = betaL S * (-σ * z) by ring]
  rw [h, psi_betaL]

theorem betaL_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold betaL
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TLChoiceChk
section
namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

theorem wordLiftOfParts : WordLiftOfParts := by
  intro hstep hlet A S _ _ _ _ _ _ r n L st Lf w hA hL hn
  induction w with
  | nil =>
    intro _ e
    have h1 : ((ofWord L st ([] : List (Letter ℂ S))).F * bTA L ([] : List (Letter ℂ S))) = 1 := by
      simp [ofWord, bTA, bT, Start.frame]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using hL.one
    · exact hL.zero _ _
  | cons l w ih =>
    intro hw e
    have hw' : admitted st w := by
      obtain ⟨h1, h2, h3, h4⟩ := hw
      refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
        fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), h4.of_cons⟩
      simp only [List.map_cons, List.nodup_cons] at h1
      exact h1.2
    rw [hstep A S r L st l w hA hw e, Matrix.mul_apply]
    refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
    intro f _
    have hcoef : Lf n (9 * (r + 1) * n) ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i : SlopeTestRemainingChoices S A) e f) := by
      rw [Matrix.sum_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro i _
      rw [Matrix.mul_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro g _
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]
        exact hlet A S r n L st Lf l w hA hL hn hw i g f
      · rw [zero_mul]
        exact hL.zero _ _
    refine hL.mono ?_ ?_ (hL.mul hcoef (ih hw' f))
    · simp only [List.length_cons]
      exact le_of_eq (by ring)
    · simp only [List.length_cons]
      exact le_of_eq (by ring)

end Formalism.FourierDecayAlt.TL

example {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] (st : Formalism.FourierDecayAlt.Fr.Start A)
    (X φ τ α β γ : Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) (h1 : Formalism.FourierDecayAlt.TL.kMat st α) (h2 : Formalism.FourierDecayAlt.TL.kMat st β) (h3 : Formalism.FourierDecayAlt.TL.kMat st γ) :
    Matrix.of (fun i j => ∑ k, α i k * ((X * β - β * X) * γ) k j) ∈ Formalism.FourierDecayAlt.TL.dSpan st X φ τ :=
  Submodule.subset_span (Or.inl ⟨α, β, γ, h1, h2, h3, by rw [Matrix.mul_assoc]; rfl⟩)
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralRankZero
section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

theorem locPt_zero {h : C.LPt} {n : ℕ} (hh : D.IsLocPt h n) (hn : n = 0) : h = [] := by
  rcases h with _ | ⟨b, t⟩
  · rfl
  · exfalso
    have h1 := (hh.1 b (by simp)).1
    have h2 := hh.2
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at h2
    omega

theorem top_unipotent_integral_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) (hR : P.r = 0)
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have hh0 : h = [] := locPt_zero hh hR
  subst hh0
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hR
  subst hR
  have e1 : p.ν' = ν'r := by
    rw [← hν]
    funext i
    simp only [D.castV, liftVec]
    rw [dif_pos (by simp; omega)]
    exact congrArg ν'r (Fin.ext (by simp))
  have e2 : p.m₀ = m₀r := by
    rw [← hm]
    ext i j
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    exact congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))
  have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F := by
    funext γ
    simp only [D.castF]
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_
    exact congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)
  simp only [List.nil_append]
  rw [e3]
  subst e1
  subst e2
  rfl

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end


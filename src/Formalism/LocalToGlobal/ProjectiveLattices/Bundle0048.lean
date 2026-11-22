import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsAlgebraicOfTrdegEq
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}

variable (K) in

def HomQ (x : Fin N → L) (f : L) : Prop :=
  ∃ (e : ℕ) (A B : MvPolynomial (Fin N) K), A.IsHomogeneous e ∧ B.IsHomogeneous e ∧
    MvPolynomial.aeval x B ≠ 0 ∧ f = MvPolynomial.aeval x A / MvPolynomial.aeval x B

theorem homQ_mul {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f * g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * A', B * B', hA.mul hA', hB.mul hB', by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem homQ_add {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f + g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * B' + B * A', B * B', (hA.mul hB').add (hB.mul hA'), hB.mul hB',
    by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hBx hBx']⟩

theorem homQ_inv {x : Fin N → L} {f : L} (hf : HomQ K x f) : HomQ K x f⁻¹ := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  by_cases hAx : MvPolynomial.aeval x A = 0
  · rw [hAx, zero_div, inv_zero]
    exact ⟨0, 0, 1, MvPolynomial.isHomogeneous_zero _ _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩
  · exact ⟨e, B, A, hB, hA, hAx, by rw [inv_div]⟩

theorem homQ_algebraMap (x : Fin N → L) (c : K) : HomQ K x (algebraMap K L c) :=
  ⟨0, MvPolynomial.C c, 1, MvPolynomial.isHomogeneous_C _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩

theorem homQ_ratio (x : Fin N → L) (m k₀ : Fin N) (hx : x k₀ ≠ 0) : HomQ K x (x m / x k₀) :=
  ⟨1, MvPolynomial.X m, MvPolynomial.X k₀, MvPolynomial.isHomogeneous_X _ _, MvPolynomial.isHomogeneous_X _ _,
    by simpa using hx, by simp⟩

variable (K) in

def homQField (x : Fin N → L) : IntermediateField K L where
  carrier := {f | HomQ K x f}
  mul_mem' := fun ha hb => homQ_mul ha hb
  add_mem' := fun ha hb => homQ_add ha hb
  algebraMap_mem' := homQ_algebraMap x
  inv_mem' := fun _ hf => homQ_inv hf

theorem homQ_of_mem_adjoin (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0) {f : L}
    (hf : f ∈ IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) : HomQ K x f := by
  have hle : IntermediateField.adjoin K (Set.range fun m => x m / x k₀) ≤ homQField K x := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    exact homQ_ratio x m k₀ hx
  exact hle hf

theorem isAlgebraic_of_trdeg_eq (F : IntermediateField K L) (d : ℕ) (hF : Algebra.trdeg K F = d)
    (hL : Algebra.trdeg K L = d) : Algebra.IsAlgebraic F L := by
  have hs := trdeg_add_eq K F (A := L)
  rw [hF, hL] at hs
  have h0 : Algebra.trdeg F L = 0 := by
    rcases Cardinal.add_eq_left_iff.1 hs with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.2 ((Cardinal.natCast_lt_aleph0 (n := d))))
    · exact h
  exact trdeg_eq_zero_iff.1 h0

theorem exists_homInt (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) L) (a : L) :
    ∃ (k n : ℕ) (P : MvPolynomial (Fin N) K) (cf : ℕ → MvPolynomial (Fin N) K), 0 < k ∧ P.IsHomogeneous k ∧
      MvPolynomial.aeval x P ≠ 0 ∧ (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) ∧
      (MvPolynomial.aeval x P * a) ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval x (cf i) * (MvPolynomial.aeval x P * a) ^ i = 0 := by
  set F := IntermediateField.adjoin K (Set.range fun m => x m / x k₀) with hFdef
  obtain ⟨p, hpm, hp⟩ := ((halg.isAlgebraic a).isIntegral : IsIntegral F a)
  have hq : ∀ i, HomQ K x ((p.coeff i : F) : L) := fun i => homQ_of_mem_adjoin x k₀ hx (p.coeff i).2
  choose e A B hA hB hBx hf using hq
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  set P : MvPolynomial (Fin N) K := MvPolynomial.X k₀ * ∏ i ∈ Finset.range n, B i with hPdef
  have hPh : P.IsHomogeneous (1 + ∑ i ∈ Finset.range n, e i) :=
    (MvPolynomial.isHomogeneous_X K k₀).mul (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => hB i)
  have hPx : MvPolynomial.aeval x P = x k₀ * ∏ i ∈ Finset.range n, MvPolynomial.aeval x (B i) := by
    rw [hPdef, map_mul, MvPolynomial.aeval_X, map_prod]
  have hPx0 : MvPolynomial.aeval x P ≠ 0 := by
    rw [hPx]; exact mul_ne_zero hx (Finset.prod_ne_zero_iff.2 fun i _ => hBx i)
  refine ⟨1 + ∑ i ∈ Finset.range n, e i, n, P,
    fun i => P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i,
    by omega, hPh, hPx0, ?_, ?_⟩
  · intro i hi
    have hS : ∑ j ∈ Finset.range n, e j = e i + ∑ j ∈ (Finset.range n).erase i, e j :=
      (Finset.add_sum_erase _ _ (Finset.mem_range.2 hi)).symm
    have h1 := ((hPh.pow (n - i - 1)).mul ((MvPolynomial.isHomogeneous_X K k₀).mul
      (MvPolynomial.IsHomogeneous.prod ((Finset.range n).erase i) B e fun j _ => hB j))).mul (hA i)
    convert h1 using 1
    obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, hS]
    ring
  · beta_reduce
    have hp' : Polynomial.aeval a p = 0 := by rw [Polynomial.aeval_def]; exact hp
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul, hn] at hp'
    have key : ∀ i ∈ Finset.range n,
        MvPolynomial.aeval x (P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i) *
          (MvPolynomial.aeval x P * a) ^ i = MvPolynomial.aeval x P ^ n * (p.coeff i • a ^ i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hPi : MvPolynomial.aeval x P = x k₀ * (MvPolynomial.aeval x (B i) *
          ∏ j ∈ (Finset.range n).erase i, MvPolynomial.aeval x (B j)) := by
        rw [hPx, ← Finset.mul_prod_erase _ _ hi]
      have hsm : p.coeff i • a ^ i = MvPolynomial.aeval x (A i) / MvPolynomial.aeval x (B i) * a ^ i := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hf i]
      obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
      have hpow : MvPolynomial.aeval x P ^ n =
          MvPolynomial.aeval x P ^ t * MvPolynomial.aeval x P * MvPolynomial.aeval x P ^ i := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hsm, hpow]
      simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_prod]
      rw [ht, Nat.add_sub_cancel, hPi]
      field_simp [hBx i]
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_pow, ← mul_add, add_comm, hp', mul_zero]

end Alg

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def IntFormSt {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (k n : ℕ) (cf : ℕ → MvPolynomial (Fin N) T.Q.c.F) (b : Om Z), 0 < k →
    (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) →
    b ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval (fun m => evC hG Z ((w m : (recB h.toLawsCore).Cusp j wL) : T.R j)) (cf i) * b ^ i = 0 →
    ∃ g : (recB h.toLawsCore).Cusp j (wsmul k wL),
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j) = b

theorem birSt_of (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB2 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
      Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
        evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
          evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)
    (hint : IntFormSt h j hG G.w) : BIRSt h j hj hG G := by
  intro Z a
  obtain ⟨k₀, hx0, htrF⟩ := hB2 Z
  have halg := isAlgebraic_of_trdeg_eq _ _ htrF (htr Z)
  obtain ⟨k, n, P, cf, hk, hP, hP0, hcf, heq⟩ := exists_homInt (K := T.Q.c.F) _ k₀ hx0 halg a
  obtain ⟨g, hg⟩ := hint Z k n cf _ hk hcf heq
  exact ⟨k, g, P, hP, hP0, by rw [hg, mul_comm]⟩

theorem birSt_of_big (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hBig : BigAt h j hj hG G) (hint : IntFormSt h j hG G.w) :
    BIRSt h j hj hG G :=
  birSt_of h j hj hG htr G hBig.2 hint

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D}

theorem mul_ringHom_units_ratio {K : Type} [Field K] {W S R : K} (hW : W ≠ 0) (k : ℕ) :
    W ^ k * R * (W * S)⁻¹ ^ k = R / S ^ k := by
  have h1 : W ^ k * W⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hW, one_pow]
  rw [mul_inv, mul_pow, div_eq_mul_inv, ← inv_pow]
  linear_combination (R * S⁻¹ ^ k) * h1

set_option maxHeartbeats 4000000 in
theorem realPt_of (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hwL : 0 < wL.n) (hPt : PtOfSSt h j hj hG G la) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (hIF : IntFramesSt (T.Q.Xo j) T.Q.c) (hWt : WtField (T.Q.Xo j) T.Q.c)
    (hMod : ModelAtSt (T.Q.Xo j) T.Q.c la) :
    RealPtNZSt h j hj hG G la hU := by
  have hWD := h.toLawsCore.evalWD j hj
  intro ζ
  haveI hD : IsDVRAt (show Pts (Op (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.N)
      (OsK (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.w) from ζ) :=
    ‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ
  haveI : CharZero (Loc ζ) := loc_charZero hU ζ
  obtain ⟨Tc, ι, hloc, hunr⟩ := complSt_holds (Loc ζ)
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  let kap : Kp (recPlus h j hj) la G.N →+* Tc.Fr :=
    kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  letI instK : Algebra (Kp (recPlus h j hj) la G.N) Tc.Fr := kap.toAlgebra
  let φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] Tc.Fr :=
    { toRingHom := phiAt ζ Tc.Fr ι hU hι, commutes' := fun _ => by rfl }
  obtain ⟨alg, y₀, ⟨Z, ψ, hψ⟩, halg, hs0, hrat⟩ := hPt hwL Tc.Fr φ
  have halg' : alg = kap.comp ((@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _
      (Kp.algKl (recPlus h j hj) la G.N)).comp (algebraMap (recB h.toLawsCore).KO ((recPlus h j hj).Kl la))) :=
    RingHom.ext fun a => halg a
  have ho : OverLa la Tc.V alg (ep (unifO (recPlus h j hj) la G.N) ζ) := by
    rw [halg']
    exact overLa_kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  obtain ⟨O, _, β, Y, -, hPI, hB⟩ := hMod
  obtain ⟨b, hb⟩ := hB Tc alg _ ho
  letI := alg.toAlgebra
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF Tc alg Y hPI b hb y₀
  obtain ⟨p, φ', y', hm⟩ := hT Z
  have hm2 : FrMap (ψ.comp φ') y' y₀ := frMap_trans _ _ _ φ' ψ y' (genFr hG Z) y₀ hm hψ
  have hy₀T : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) y₀ :=
    ⟨p, ψ.comp φ', y', hm2⟩
  have hW : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      evI y (F : T.R j) = wchar (ex (T.Q.Dw j) (wtA w) w.n) t * evR (T.Q.Xo j) T.Q.c (F : T.R j) y₀ := fun w F =>
    hWt (wtA w) w.n (F : T.R j) (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)) Tc.Fr t y₀ y.1 hy₀T y.2.1 hbor
  let χ : (recPlus h j hj).Forms →+* Tc.Fr := chiI j y
  let ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr := evRp la G.N kap χ (fun a f => by
    have e := chiI_smul j y a f
    rw [halg a] at e
    exact e)
  have hev_k : ∀ c : Kp (recPlus h j hj) la G.N, ev (algebraMap _ (Rp (recPlus h j hj) la G.N) c) = kap c :=
    evRp_alg la G.N kap χ _
  have hev_inc : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      ev (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc w F)) = evI y (F : T.R j) := by
    intro w F
    exact (evRp_emb la G.N kap χ _ ((recPlus h j hj).inc w F)).trans (chiI_inc j h y w F)
  have hev_sec : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) =
      ∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
        evI y ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) := by
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hev_k, hev_inc]
  have hs0' : (∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
      evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ≠ 0 := hs0
  have hev_s0 : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) = wchar (ex (T.Q.Dw j) (wtA wL) wL.n) t *
      ∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
        evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀ := by
    rw [hev_sec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hW wL (G.w k)]
    ring
  have hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0)) :=
    IsUnit.mk0 _ (by rw [hev_s0]; exact mul_ne_zero (wchar_ne_zero _ _) hs0')
  let yV : PtV (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y trivial () trivial
  let yP : (extAll h j hj).Pt' la := ⟨vAtV yV, yV, rfl⟩
  refine ⟨yP, Tc, ι, hloc, hunr, ev, hu, ?_, ?_, ?_⟩
  · intro w F
    rw [extAll_vAt_inc]
    show vAtV yV (F : T.R j) = _
    exact congrArg (nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ)) (hev_inc w F).symm
  · intro x
    obtain ⟨k, ⟨g, hg⟩, rfl⟩ := exists_weightZero_fraction_eq _ _ _ x
    rw [coe_weightZeroFraction, liftEv_frac]
    have key : ∀ (g : Rp (recPlus h j hj) la G.N) (hg : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k))
        (hg' : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k)),
        ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))⁻¹ ^ k =
          phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)
            (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨g, hg'⟩)) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg0 =>
        intro hg'
        obtain ⟨F, rfl⟩ := hg0
        have hr := hrat k F
        have hr' : phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
            ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ F), hg'⟩)) =
            evR (T.Q.Xo j) T.Q.c ((F : T.R j)) y₀ /
              (∑ k', kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k'))) *
                evR (T.Q.Xo j) T.Q.c ((G.w k' : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ^ k := hr
        rw [hr', hev_inc, hW, ex_addL, wchar_nsmul, hev_s0]
        exact mul_ringHom_units_ratio (wchar_ne_zero (ex (T.Q.Dw j) (wtA wL) wL.n) t) k
      | zero =>
        intro hg'
        have e0 : fr0 (recPlus h j hj) la G.w k ⟨0, hg'⟩ = 0 := Subtype.ext (by rw [coe_weightZeroFraction]; exact map_zero _)
        rw [e0, map_zero, map_zero, map_zero, zero_mul]
      | add a b ha hb iha ihb =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨a + b, hg'⟩ =
            fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ + fr0 (recPlus h j hj) la G.w k ⟨b, hb⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_add, coe_weightZeroFraction, coe_weightZeroFraction]; exact map_add _ _ _)
        rw [e1, map_add (toOsK (recPlus h j hj) la G.w), map_add (phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)),
          map_add ev, add_mul, iha ha, ihb hb]
      | smul c a ha iha =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨c • a, hg'⟩ = c • fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_smul, coe_weightZeroFraction]; exact map_smul _ _ _)
        rw [e1, map_smul (toOsK (recPlus h j hj) la G.w) c,
          Algebra.smul_def c (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩)),
          map_mul, ← iha ha, Algebra.smul_def c a, map_mul, hev_k, mul_assoc]
        rfl
    exact key g hg hg
  · intro w F hNZ
    rw [show ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = evI y (F : T.R j) from hev_inc w F, hW w F]
    refine mul_ne_zero (wchar_ne_zero _ _) ?_
    have hnat := (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)).1
    rw [evR_eq_of_map hWD hnat y₀ p (ψ.comp φ') y' hm2, AlgHom.comp_apply]
    have h2 : evC hG Z (F : T.R j) = φ' ((F : T.R j) p y') := evR_eq_of_map hWD hnat (genFr hG Z) p φ' y' hm
    rw [← h2]
    exact (map_ne_zero_iff _ ψ.toRingHom.injective).2 (hNZ Z)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D}

set_option maxHeartbeats 1000000 in

abbrev OmSK (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
    Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) (Jid (recPlus h j hj) la G.w)

set_option maxHeartbeats 4000000 in

def qZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F : (recB h.toLawsCore).Cusp j wF) : OmSK h j hj hG hT G la Z :=
  Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))
    (lwZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w
      (algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
        (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc wF F))))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in

def algZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) :
    Kp (recPlus h j hj) la G.N →+* OmSK h j hj hG hT G la Z :=
  (Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))).comp
    (algebraMap (Kp (recPlus h j hj) la G.N) (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in

def TieSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  letI : ∀ Z, Module (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z) := fun Z =>
    (algZ h j hj hG hT G la Z).toModule
  (∃ e : SectionSheafQuotient (recPlus h j hj) la G.w wF ≃ₗ[Kp (recPlus h j hj) la G.N] (∀ Z, OmSK h j hj hG hT G la Z),
    ∀ (F : (recB h.toLawsCore).Cusp j wF) (Z : Comp (T.Q.Xo j) T.Q.c),
      e (resF G la F) Z * qZ h j hj hG hT G la Z g0 = qZ h j hj hG hT G la Z F) ∧
  G.del = ∑ᶠ Z : Comp (T.Q.Xo j) T.Q.c, Module.finrank (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z)

abbrev AZ (T : Top D) (j N : ℕ) (Z : Comp (T.Q.Xo j) T.Q.c) : Type := KT T j N ⊗[T.Q.c.F] Om Z

def secT (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c)
    (i : Fin (WeightFamilies.dimY D j + 1)) : AZ T j N Z :=
  ∑ k, algebraMap (MvPolynomial (Idx D j N) T.Q.c.F) (KT T j N) (MvPolynomial.X (i, k)) ⊗ₜ evC hG Z (w k).1

set_option synthInstance.maxHeartbeats 1000000 in

abbrev OmST (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  Localization.Away (secT h j hG w Z 0) ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
    algebraMap (AZ T j N Z) (Localization.Away (secT h j hG w Z 0)) (secT h j hG w Z i.succ))

set_option synthInstance.maxHeartbeats 1000000 in

def ratioST (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL wF : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F g0 : (recB h.toLawsCore).Cusp j wF) : OmST h j hG w Z :=
  Ideal.Quotient.mk _ (algebraMap (AZ T j N Z) (Localization.Away (secT h j hG w Z 0))
    ((1 : KT T j N) ⊗ₜ (evC hG Z F.1 / evC hG Z g0.1)))

set_option synthInstance.maxHeartbeats 1000000 in

def wST (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c) (k : Fin N) : OmST h j hG w Z :=
  Ideal.Quotient.mk _ (algebraMap (AZ T j N Z) (Localization.Away (secT h j hG w Z 0))
    ((1 : KT T j N) ⊗ₜ evC hG Z (w k).1))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in

def TiePtsSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  ∀ io : KT T j G.N →+* ℂ, IsIoExt j io →
    letI := io.toAlgebra
    ∃ (δ : (T.U j T.σ₀).Comp → ℕ) (xs : ∀ k, Fin (δ k) → Frame ((T.U j T.σ₀).X k).Ψ D.R.r)
      (bij : (Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ) ≃ Σ k, Fin (δ k)),
      (∀ k i, xs k i ∈ ((T.U j T.σ₀).X k).dom) ∧
      ∀ (p : Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ) (F : (recB h.toLawsCore).Cusp j wF),
        rdR h j g0 (bij p).1 (xs (bij p).1 (bij p).2) ≠ 0 ∧
        p.2 (ratioST h j hG G.w p.1 F g0) =
          rdR h j F (bij p).1 (xs (bij p).1 (bij p).2) / rdR h j g0 (bij p).1 (xs (bij p).1 (bij p).2) ∧
      (∀ p : Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ,
        ∃ k, rdR h j (G.w k) (bij p).1 (xs (bij p).1 (bij p).2) ≠ 0) ∧
      (∀ (p : Σ Z : Comp (T.Q.Xo j) T.Q.c, OmST h j hG G.w Z →ₐ[KT T j G.N] ℂ) (k₁ k₂ : Fin G.N),
        rdR h j (G.w k₁) (bij p).1 (xs (bij p).1 (bij p).2) * p.2 (wST h j hG G.w p.1 k₂) =
          rdR h j (G.w k₂) (bij p).1 (xs (bij p).1 (bij p).2) * p.2 (wST h j hG G.w p.1 k₁)) ∧
      ∀ (k : (T.U j T.σ₀).Comp) (i i' : Fin (δ k)), i ≠ i' →
        ¬ ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∃ b ∈ Bor ((T.U j T.σ₀).X k).Ψ D.R.r, xs k i' = lact γ (rmul (xs k i) b)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieUpR
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def KappaTie (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (f : T.R j), f ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n →
    (evC hG Z f = 0 ↔ ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, rdU (T.U j T.σ₀) f (κ Z) x = 0)

def DTie (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) : Prop :=
  ∃ (uL : WeightFamilies.Wt D j) (W : Fin (d.N + 1) → (recB h.toLawsCore).Cusp j uL), Even uL.n ∧
    d.wL = wtZ (wtA uL) uL.n ∧ (∀ i Z, d.w i Z = valC hG (wtA uL) uL.n (W i).1 Z) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra T.Q.c.F k] (y : FrPt (T.Q.Xo j) T.Q.c k),
      ∃ i, evR (T.Q.Xo j) T.Q.c (W i).1 y ≠ 0

def NrmTie (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (G : WTZ D.host.E) (P : Om Z →+* ℂ), d.nrm Z G 0 P = 0) ∧
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c), ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, ∀ P : Om Z →+* ℂ,
    P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀ →
    (∀ (u : WeightFamilies.Wt D j) (F G' : T.R j),
      F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → G' ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
      valC hG (wtA u) u.n G' Z ≠ 0 →
      rdU (T.U j T.σ₀) F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F Z)
        (valC hG (wtA u) u.n G' Z)) * rdU (T.U j T.σ₀) G' (κ Z) x) →
    ∀ (u : WeightFamilies.Wt D j) (F : T.R j), F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
      ((T.U j T.σ₀).X (κ Z)).pnorm (laU (T.U j T.σ₀) (wtA u) u.n (κ Z)) (rdU (T.U j T.σ₀) F (κ Z)) x =
        d.nrm Z (wtZ (wtA u) u.n) (valC hG (wtA u) u.n F Z) P

def KappaOnto (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) :
    Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ), P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀ →
    ∃ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, ∀ (u : WeightFamilies.Wt D j) (F G' : T.R j),
      F ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → G' ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n → Even u.n →
      valC hG (wtA u) u.n G' Z ≠ 0 →
      rdU (T.U j T.σ₀) F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F Z)
        (valC hG (wtA u) u.n G' Z)) * rdU (T.U j T.σ₀) G' (κ Z) x

def TieReadingSt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  FnAlgClosed (T.Q.Xo j) T.Q.c → KappaTie j hG κ → KappaOnto h j hG κ → DTie h j hG d → NrmTie h j hG d κ →
  ∃ R : ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      ReciprocityTheory.ChartRestriction.G.AR.Up.Reading (𝒜 := fun Z G => AG Z G) d Z ((T.U j T.σ₀).X (κ Z)) T.σ₀,
    (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u)
      (hF : valC hG (wtA u) u.n F.1 Z ∈ (R Z).Rg),
        ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, (R Z).rd ⟨_, hF⟩ x = rdR h j F (κ Z) x) ∧
    (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), Even u.n →
      valC hG (wtA u) u.n F.1 Z ∈ (R Z).Rg) ∧
    (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j), Even u.n → wtZ (wtA u) u.n ∈ (R Z).WE) ∧
    ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (hu : wtZ (wtA u) u.n ∈ (R Z).WE),
      (R Z).wt ⟨_, hu⟩ = laU (T.U j T.σ₀) (wtA u) u.n (κ Z)

end Formalism.L2.Pj
end
end


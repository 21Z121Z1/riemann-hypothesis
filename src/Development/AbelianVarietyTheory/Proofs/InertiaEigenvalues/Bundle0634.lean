import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mul_eq_smul_one_comm {R : Type} [CommRing R] [IsDomain R] {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} {c : R} (hc : c ≠ 0) (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) R)) :
    M' * M = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : M.det • (M' * M) = M.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc M.det • (M' * M) = (M.adjugate * M) * (M' * M) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * (M * M') * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa [Matrix.smul_apply] using mul_left_cancel₀ hdet h2

theorem eq_zero_of_mul_eq_zero_of_mul_eq_smul {R : Type} [CommRing R] {d : ℕ}
    {W W' M : Matrix (Fin d) (Fin d) R} {t : R} (ht : t ∈ nonZeroDivisors R)
    (h : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hM : W * M = 0) : M = 0 := by
  have hdet : W.det ∈ nonZeroDivisors R := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have htp : t ^ Fintype.card (Fin d) ∈ nonZeroDivisors R := pow_mem ht _
    rw [mem_nonZeroDivisors_iff] at htp ⊢
    refine ⟨fun x hx => htp.1 x (by rw [← h1, mul_comm W.det, mul_assoc, hx, mul_zero]),
      fun x hx => htp.2 x (by rw [← h1, ← mul_assoc, hx, zero_mul])⟩
  have key : W.det • M = 0 := by
    rw [← Matrix.one_mul M, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, hM, Matrix.mul_zero]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h2 ⊢
  exact (mem_nonZeroDivisors_iff.1 hdet).1 _ h2

theorem map_smul_ringHom {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (f : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem Height.bas_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  intro l _ K bk d ρ τ s ht hτ Φ hΦ
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := by
    unfold BK.ρ₀
    exact NNReal.rpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hρ1 : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    apply NNReal.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · have : (0:ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith
  have hev : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ
  have hXl : frobS l bk.a (X : bk.S) = X ^ l := by
    simp [frobS]
  have hfr : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [← bk.ev_frob, hXl, map_pow]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1) (Fact.out : l.Prime).ne_zero
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hev with hi_def
  have hi : IsDiscMap bk.ev i := isDiscMap_map _ _
  set ΦA : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map WittVector.frobenius hfr with hΦA_def
  have hΦA : IsDiscMap WittVector.frobenius ΦA := isDiscMap_map _ _
  have hcomm : i.comp Φ = ΦA.comp i := by
    have h1 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (i.comp Φ) :=
      ⟨fun a => by simp only [RingHom.comp_apply, hΦ.ext, hi.ext], fun x => (hi.norm_le _).trans (hΦ.norm_le _)⟩
    have h2 : IsDiscMap (bk.ev.comp (frobS l bk.a)) (ΦA.comp i) := by
      have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
        RingHom.ext bk.ev_frob
      rw [e]
      exact ⟨fun a => by simp only [RingHom.comp_apply, hΦA.ext, hi.ext], fun x => (hΦA.norm_le _).trans (hi.norm_le _)⟩
    exact h1.unique h2
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective i := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk _ bk.ev ι tb).2.2.2 i hi
  have hlS : (l : bk.S) ∈ nonZeroDivisors bk.S :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk bk.S (RingHom.id _) Unit (@TopBasis.self _ _ bk.J bk.complete)).2.2.1
  have hτr : bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc l K bk τ hτ
  have hφE : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map i
    rw [hi.ext] at h; exact h
  have hL : IsUnit ((l : ℕ) : bk.DA bk.ρ₀) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hiS : ∀ a, i (toDisc l (X : bk.S) bk.ρ₀ a) = bk.iS a := hi.ext
  have hΦiA : ∀ a, ΦA (bk.iA a) = bk.iA (WittVector.frobenius a) := hΦA.ext
  have hΦiS : ∀ a, ΦA (bk.iS a) = bk.iS (frobS l bk.a a) := fun a => by
    simp only [BK.iS, RingHom.comp_apply, hΦiA, bk.ev_frob]
  have hXX : s.X' * s.X = ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S) :=
    mul_eq_smul_one_comm (mul_ne_zero (pow_ne_zero _ (nonZeroDivisors.ne_zero hlS)) (pow_ne_zero _ bk.E_ne_zero)) s.X_mul

  have hmapinj : ∀ M M' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀), M.map i = M'.map i → M = M' := fun M M' h => by
    ext a b; exact hinj (congrFun (congrFun h a) b)
  apply hmapinj
  have hcomm' : ∀ z, i (Φ z) = ΦA (i z) := RingHom.congr_fun hcomm
  simp only [map_smul_ringHom, Matrix.map_mul, Height.bas, Matrix.map_map, Function.comp_def, hiS, map_mul, map_pow,
    map_natCast, RingHom.comp_apply, hcomm', hΦ.ext]

  set L : bk.DA bk.ρ₀ := ((l : ℕ) : bk.DA bk.ρ₀) with hL_def
  set e : bk.DA bk.ρ₀ := bk.iS bk.E with he_def
  set φe : bk.DA bk.ρ₀ := bk.iS (frobS l bk.a bk.E) with hφe_def
  set XA := s.X.map bk.iS with hXA
  set X'A := s.X'.map bk.iS with hX'A
  set φXA := s.X.map (bk.iS.comp (frobS l bk.a)) with hφXA
  set φX'A := s.X'.map (bk.iS.comp (frobS l bk.a)) with hφX'A
  set FA := s.F.map (bk.iS.comp C) with hFA
  set AA := ht.A.map bk.iS with hAA
  set Zi := ht.Z.map i with hZi
  set ZΦ := ht.Z.map (fun z => ΦA (i z)) with hZΦ
  set YA := ht.Y.map bk.iA with hYA
  have hW : s.W * Zi = YA := ht.W_mul i hi
  have hZΦ' : ZΦ = Zi.map ΦA := by rw [hZΦ, hZi, Matrix.map_map]; rfl
  have hWΦ : s.W.map ΦA * ZΦ = YA.map ΦA := by rw [hZΦ', ← Matrix.map_mul, hW]
  have hP : e ^ ht.a • YA.map ΦA = YA * AA := by
    have h := congrArg (fun M => M.map bk.iA) ht.φ
    simp only [map_smul_ringHom, Matrix.map_mul, Matrix.map_map] at h
    have e1 : YA.map ΦA = ht.Y.map (bk.iA.comp WittVector.frobenius) := by
      rw [hYA, Matrix.map_map]; congr 1; funext x; exact hΦiA x
    rw [e1]; rw [map_pow] at h; exact h
  have hS : L ^ s.c₁ • (s.W.map ΦA * φX'A) = φe ^ s.N • (s.W * X'A * FA) := by
    have h := s.φ ΦA hΦA
    rw [Matrix.map_mul] at h
    have e1 : (s.X'.map bk.iS).map ΦA = φX'A := by
      rw [Matrix.map_map, hφX'A]; congr 1; funext x; exact hΦiS x
    rw [e1] at h
    simpa only [map_natCast, map_pow] using h
  have hXXφ : φX'A * φXA = (L ^ s.c₂ * φe ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map (bk.iS.comp (frobS l bk.a))) hXX
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hXX2 : XA * X'A = (L ^ s.c₂ * e ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map bk.iS) s.X_mul
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hQ : (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA = s.W * X'A * FA * φXA := by
    apply ((hφE.pow s.N).smul_left_cancel).1
    calc φe ^ s.N • (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA
        = (L ^ s.c₁ • (s.W.map ΦA * φX'A)) * φXA := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hXXφ, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
          congr 1; ring
      _ = _ := by rw [hS, Matrix.smul_mul]
  have hD : s.W * ((L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (Zi * AA) - e ^ ht.a • (X'A * FA * φXA * ZΦ)) = 0 := by
    rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hW, ← hP, ← hWΦ,
      smul_comm, ← Matrix.smul_mul, hQ]
    simp only [Matrix.mul_assoc]
  have hD' := eq_zero_of_mul_eq_zero_of_mul_eq_smul (pow_mem hτr _) s.W_mul hD
  rw [sub_eq_zero] at hD'
  have hX := congrArg (fun M => XA * M) hD'
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hXX2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hX
  have G : (L ^ s.c₁ * φe ^ s.N) • (XA * Zi * AA) = e ^ (ht.a + 2 * s.N) • (FA * (φXA * ZΦ)) := by
    apply ((hL.pow s.c₂).smul_left_cancel).1
    rw [smul_smul, smul_smul]
    calc (L ^ s.c₂ * (L ^ s.c₁ * φe ^ s.N)) • (XA * Zi * AA) = (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (XA * Zi * AA) := by
          congr 1; ring
      _ = _ := by rw [hX, ← Matrix.mul_assoc]; congr 1; ring
  exact G

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEuler
section
namespace GlobalTheory

theorem langRecCore_of_artinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hT : Formalism.GaloisCohomology.LocalTateDualityK)
    (hE : Formalism.GaloisCohomology.LocalEulerCharK) : ReciprocityTheory.ChartRestriction.T2.Core where
  dec := GlobalTheory.T.decomposition_group_equiv_local_galois_group
  inv := GlobalTheory.T.invIso_of_localTateDuality hT
  fin := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hT
  rat := GlobalTheory.T.rationalLocalDuality_of_localTateDuality hT
  int := GlobalTheory.T.integral_localDuality_of_localTateDuality hT
  jspan := GlobalTheory.T.span_of_local_cohomology_shape
  nat := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT
  shape := GlobalTheory.T.cohomology_shape_of_tate_duality_euler hT hE
  shapeUnr := GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality hT hE
  unr := GlobalTheory.T.unramified_padic_decomposition_hom_exists
  vhE := GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA
  top := GlobalTheory.T.dvr_finite_over_padic_topologies_exist
  elem := GlobalTheory.T.local_cohomology_seven_elementary_facts

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.taylor_rho : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ v : OD l ↥(OL LL), IsUnit v ∧ ∀ w ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)), ∀ (R : ℕ) (j : ι), GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt w)) j - v ^ α * ∑ i ∈ Finset.range R, toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL)) * GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (w τ k))) j ∈ Ideal.span {GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ ^ R} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg
  obtain ⟨v, hv, hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg
  refine ⟨v, hv, fun w hw R j => ?_⟩
  exact taylor_vec (thetaW a LL) ϖ P α (descN_mem_Mext P) (E_pow_xiExt_mem_Man P α hα)
    (galOD ↥(OL LL) (sQ l g)) (rhoDHom T jD g) (rhoD_smul T jD g) (v ^ α)
    (GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg v hED)
    (fun i => toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL))) R _
    (fun f hf => GlobalTheory.T.taylor_formula_pi_invPrime_mod_eisenstein_pow l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg f hf R) hw j

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.key_sums (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (hl2 : l ≠ 2) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (hStd : IsStd Pl AI) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz (thetaW a LL) ϖ (sQ l) P jB) (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (hjD : ∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z)
    (α b : ℕ) (hα : ∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (ε : OCb l) (c : ℕ)
    (hk : ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k)) {m : Vec ↥LL.1 a ι} (hm : m ∈ P.M)
    {wx : Vec ↥LL.1 a ι} (hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e))) (hwxdef : P.xiExt wx = E ↥LL.1 l e ^ b • m) (j : ι)
    (k : ℕ) : ∑ i ∈ Finset.range (α + b), ((toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1) ^ i *
      Ring.inverse (i.factorial : OD l ↥(OL LL)) *
      YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
  have hgk : sQ l (g ^ k) ∈ GK (ϖ.field a) := by rw [map_pow]; exact Subgroup.pow_mem _ hg k
  obtain ⟨v, hv, htay⟩ := taylor_rho hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα (g ^ k) hgk
  have h1 := htay wx hwx (α + b) j
  obtain ⟨v', hv', hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l (g ^ k)) hgk
  have hxe : E ↥LL.1 l e ^ α • P.xiExt wx = E ↥LL.1 l e ^ (α + b) • m := by
    rw [hwxdef, smul_smul, ← pow_add]
  have h2 : rhoD T jD (g ^ k) (YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt wx)) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
    rw [hxe, YD_E_pow_smul (thetaW a LL) ϖ (P.M_le_Man hm) (α + b), rhoD_smul, Pi.smul_apply, smul_eq_mul, map_pow,
      hED, mul_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h3 : toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l (g ^ k))) = (toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1 := by
    rw [PiSys.mu, hk k, TensorProduct.tmul_sub, map_sub, ← Algebra.TensorProduct.one_def, map_one,
      ← pow_mul, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow, map_pow (WittVector.teichmuller l)]
  rw [h3] at h1
  have h4 := sub_mem h2 h1
  rw [sub_sub_cancel] at h4
  have h5 := Ideal.mul_mem_left _ (↑(hv.pow α).unit⁻¹ : OD l ↥(OL LL)) h4
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h5

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in

theorem GlobalTheory.GalStep.main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD m hm n hn w hw j
  obtain ⟨α, β₀, hα, hβ₀⟩ := P.exists_exponents
  have hβ : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.L := by
    have h1 := P.L.smul_mem (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) (hβ₀ m hm)
    have h2 : E ↥LL.1 l e ^ (β₀ + n) • m =
        (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) • E ↥LL.1 l e ^ β₀ • m := by
      rw [pow_add, mul_comm, mul_smul]
      rfl
    rw [h2]
    exact h1
  obtain ⟨g, ε, c, hε, hc, hg, hk⟩ := GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer l a e ϖ hl2
  obtain ⟨u, hu, hq⟩ := GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ε c hε hc
  obtain ⟨hnz, hnat⟩ := GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ
  have hxM : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.MMl := P.ext_mono (le_trans (A_le_S l e) (le_away _ _)) hβ
  have hsurj := P.xiExt.surjective (E ↥LL.1 l e ^ (β₀ + n) • m)
  obtain ⟨wx, hwxdef⟩ := hsurj
  have hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)) :=
    ((GlobalTheory.BK.xi_trivialises_invL_S ↥(OL LL) ↥LL.1 l e a ι P).2 wx).1 (by rw [hwxdef]; exact hxM)
  have hD1 := GlobalTheory.T.divided_difference_ideal_power_mem (OD l ↥(OL LL)) hnat (ED ↥LL.1 (thetaW a LL) ϖ) _ u hu hq (α + (β₀ + n))
    (fun i => YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j)
    (key_sums hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α (β₀ + n) hα g hg ε c hk hm hwx hwxdef j)
  have hfin := tail_step (thetaW a LL) ϖ P hnz (E_pow_xiExt_mem_Man P) (descN_mem_Mext P) α β₀ n hα hm hn hwx hwxdef j hD1
  rw [← iD_eq_YD (thetaW a LL) ϖ hn j (fun τ => w τ j) (fun τ => hw τ j)] at hfin
  exact hfin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.MooreDeterminant

variable {B Q : Type} [CommRing B] [IsDomain B] [Field Q] [Algebra Q B]

theorem det_mem (S : B → Prop) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι B) (hM : ∀ i j, S (M i j)) : S M.det := by
  rw [Matrix.det_apply]
  have hz : S 0 := by simpa using h0 0
  refine Finset.sum_induction _ S hadd hz ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply hmul
  · have := h0 (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Q)
    simpa using this
  · have h1 : S 1 := by simpa using h0 1
    exact Finset.prod_induction _ S hmul h1 (fun i _ => hM _ _)

theorem iter_eq (φ : B →+* B) (m : ℕ) : ⇑(φ ^ m) = (⇑φ)^[m] := RingHom.coe_pow φ m

theorem moore_core (φ : B →+* B) (S : B → Prop)
    (hφ : ∀ b, S b → S (φ b)) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    (L : B) (hL : φ L = L) (h : ℕ)
    (ratio : ∀ s, s < h → ∀ ω ω' : B, S ω → S ω' → φ^[h] ω = L ^ s * ω → φ^[h] ω' = L ^ s * ω' → ω' ≠ 0 →
      φ ω * ω' = ω * φ ω' → ∃ c : Q, ω = c • ω') :
    ∀ (n : ℕ) (a : Fin (n + 1) → B), n + 1 ≤ h → (∀ j, S (a j)) → (∀ j, φ^[h] (a j) = L * a j) →
      LinearIndependent Q a → (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a j)).det ≠ 0 := by
  have hSit : ∀ (i : ℕ) b, S b → S (φ^[i] b) := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [Function.iterate_succ_apply']; exact hφ _ (ih b hb)
  intro n
  induction n with
  | zero =>
    intro a _ _ _ ha
    rw [Matrix.det_fin_one]
    simpa using ha.ne_zero 0
  | succ n ih =>
    intro a hk hSa hfa ha hdet
    set M : Matrix (Fin (n + 2)) (Fin (n + 2)) B := Matrix.of fun i j => φ^[i] (a j) with hMdef

    have hA := ih (a ∘ Fin.castSucc) (by omega) (fun j => hSa _) (fun j => hfa _)
      (ha.comp _ (Fin.castSucc_injective _))
    set ω : Fin (n + 2) → B := fun m => (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))).det with hωdef
    have hωl : ω (Fin.last _) = (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)).det := by
      simp [ω, Fin.succAbove_last]
    have hωl0 : ω (Fin.last _) ≠ 0 := by rw [hωl]; exact hA
    have hu : ∀ m, M.adjugate m (Fin.last _) = (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * ω m := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_last, Fin.succAbove_last, ω]
      congr 2
    have hw : ∀ m, M.adjugate m 0 = (-1) ^ (m : ℕ) * φ (ω m) := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hωdef]
      simp only [Fin.val_zero, zero_add, Fin.succAbove_zero]
      rw [RingHom.map_det]
      congr 2
      ext i j
      simp [M, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Function.iterate_succ_apply']
    have hK : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    have hker : ∀ i c, ∑ m, M i m * M.adjugate m c = 0 := fun i c => by
      have := congrFun (congrFun hK i) c
      simpa [Matrix.mul_apply] using this

    set v : Fin (n + 2) → B := fun m => M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0 -
      M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _) with hvdef
    have hv : ∀ i, ∑ m, M i m * v m = 0 := by
      intro i
      have e1 := hker i 0
      have e2 := hker i (Fin.last _)
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      have : ∑ m, M i m * (M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0) =
          M.adjugate (Fin.last _) (Fin.last _) * ∑ m, M i m * M.adjugate m 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ m, M i m * (M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _)) =
          M.adjugate (Fin.last _) 0 * ∑ m, M i m * M.adjugate m (Fin.last _) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all
    have hvl : v (Fin.last _) = 0 := by simp only [v]; ring
    have hv' : Matrix.mulVec (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)) (v ∘ Fin.castSucc) = 0 := by
      funext i
      have := hv (Fin.castSucc i)
      rw [Fin.sum_univ_castSucc, hvl, mul_zero, add_zero] at this
      simpa [Matrix.mulVec, dotProduct, M] using this
    have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hA hv'
    have hvall : ∀ m, v m = 0 := by
      intro m
      refine Fin.lastCases hvl (fun j => ?_) m
      exact congrFun hv0 j

    have hcomm : ∀ m, φ (ω m) * ω (Fin.last _) = ω m * φ (ω (Fin.last _)) := by
      intro m
      have E := hvall m
      simp only [v, hu, hw, Fin.val_last, pow_add] at E
      have hs : ((-1 : B) ^ (m : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      have he : ((-1 : B) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      linear_combination ((-1 : B) ^ (m : ℕ)) * E
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * hs
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * ((-1 : B) ^ (m : ℕ)) ^ 2 * he

    have hSω : ∀ m, S (ω m) := fun m => det_mem S h0 hadd hmul _ (fun i j => hSit _ _ (hSa _))
    have hLi : ∀ i : ℕ, φ^[i] L = L := fun i => Function.iterate_fixed hL i
    have hfω : ∀ m, φ^[h] (ω m) = L ^ (n + 1) * ω m := by
      intro m
      rw [← iter_eq, hωdef]
      simp only
      rw [RingHom.map_det]
      have : (φ ^ h).mapMatrix (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) =
          L • (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, iter_eq]
        rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfa, ← iter_eq, map_mul, iter_eq, hLi]
      rw [this, Matrix.det_smul, Fintype.card_fin]

    have hrat : ∀ m, ∃ c : Q, ω m = c • ω (Fin.last _) := fun m =>
      ratio (n + 1) (by omega) _ _ (hSω m) (hSω _) (hfω m) (hfω _) hωl0 (hcomm m)
    choose c hc using hrat

    have hrow := hker 0 (Fin.last _)
    set d : Fin (n + 2) → Q := fun m => (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * c m with hd
    have hsum : (∑ m, d m • a m) * ω (Fin.last _) = 0 := by
      rw [← hrow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hu, hc m]
      simp only [M, Matrix.of_apply, Fin.val_zero, Function.iterate_zero, id, hd, Algebra.smul_def, map_mul, map_pow,
        map_neg, map_one]
      ring
    have hsum0 : ∑ m, d m • a m = 0 := (mul_eq_zero.1 hsum).resolve_right hωl0
    have hdl := Fintype.linearIndependent_iff.1 ha d hsum0 (Fin.last _)
    have hcl : c (Fin.last _) = 0 := by
      simp only [hd, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or] at hdl
      exact hdl
    apply hωl0
    rw [hc (Fin.last _), hcl, zero_smul]

end GlobalTheory.PMon.MooreDeterminant

namespace GlobalTheory.PMon

theorem moore_statement : Moore := by
  intro l _ P AI T h k hk a hPa hfa ha
  obtain ⟨hF, hinj, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  obtain ⟨hpφ, -, hpR, hpQ, -⟩ := GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T
  haveI : IsDomain P.R.BdR := hF.isDomain
  haveI : IsDomain P.R.B := Function.Injective.isDomain (P.ιB : P.R.B →+* P.R.BdR) hinj
  cases k with
  | zero => simp
  | succ n =>
    exact GlobalTheory.PMon.MooreDeterminant.moore_core (Q := ℚ_[l]) (P.φB : P.R.B →+* P.R.B) (Plus T) hpφ hpQ
      (fun a b ha hb => (hpR a b ha hb).1) (fun a b ha hb => (hpR a b ha hb).2) (l : P.R.B) (map_natCast _ l) h
      (fun s hs ω ω' h1 h2 h3 h4 h5 h6 => GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic l P AI T h s hs ω ω' h1 h2 h3 h4 h5 h6)
      n a hk hPa hfa ha

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  first | (exact @GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (exact GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (intros; apply GlobalTheory.RSNonvan.norm_prod_sat_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | exact GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | (intros; apply GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodicStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_add_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_of_per | exact GlobalTheory.CuspGeneric.avg_add_of_per | (intros; apply GlobalTheory.CuspGeneric.avg_add_of_per <;> assumption)
end


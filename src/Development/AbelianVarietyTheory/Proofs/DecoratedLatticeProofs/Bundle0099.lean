import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlEmbed

section Alg

variable {A k : Type} [CommRing A] [Field k] {m : Type} [Fintype m] [DecidableEq m]

theorem cT_add' (c : A →+* A) (X Y : Matrix m m A) : Formalism.UG.cT c (X + Y) = Formalism.UG.cT c X + Formalism.UG.cT c Y := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul' (c : A →+* A) (a : A) (X : Matrix m m A) : Formalism.UG.cT c (a • X) = c a • Formalism.UG.cT c X := by
  ext i j; simp [Formalism.UG.cT]

theorem smul_mul_smul' (a b : A) (P Q : Matrix m m A) : (a • P) * (b • Q) = (a * b) • (P * Q) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem blk_mul (e f u : A) (hef : e * f = 0) (hue : u * e = 0) (huf : u * f = 0) (huu : u * u = u)
    {X1 Y1 X2 Y2 M : Matrix m m A} (h1 : e • X1 = X1) (h2 : f • Y1 = Y1) (h3 : e • X2 = X2) (h4 : f • Y2 = Y2) :
    (X1 + Y1 + u • M) * (X2 + Y2 + u • 1) = X1 * X2 + Y1 * Y2 + u • M := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have a1 : X1 * Y2 = 0 := by rw [← h1, ← h4, smul_mul_smul', hef, zero_smul]
  have a2 : X1 * (u • 1) = 0 := by rw [← h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, hue, zero_smul]
  have a3 : Y1 * X2 = 0 := by rw [← h2, ← h3, smul_mul_smul', hfe, zero_smul]
  have a4 : Y1 * (u • 1) = 0 := by rw [← h2, Matrix.mul_smul, Matrix.mul_one, smul_smul, huf, zero_smul]
  have a5 : (u • M) * X2 = 0 := by rw [← h3, smul_mul_smul', hue, zero_smul]
  have a6 : (u • M) * Y2 = 0 := by rw [← h4, smul_mul_smul', huf, zero_smul]
  have a7 : (u • M) * (u • 1) = u • M := by rw [smul_mul_smul', huu, Matrix.mul_one]
  simp only [add_mul, mul_add, a1, a2, a3, a4, a5, a6, a7, add_zero, zero_add]

variable (c : A →+* A) (e : A) (pr : A →+* k) (sec : k →+ A)

theorem sec_eq (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (a : k) : e * sec a = sec a := by
  rw [← sec_pr, pr_sec]

theorem sec_mul (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (a b : k) :
    sec (a * b) = sec a * sec b := by
  calc sec (a * b) = sec (pr (sec a * sec b)) := by rw [map_mul pr, pr_sec, pr_sec]
    _ = e * (sec a * sec b) := sec_pr _
    _ = sec a * sec b := by rw [← mul_assoc, sec_eq e pr sec pr_sec sec_pr]

theorem secM_mul (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (Z W : Matrix m m k) :
    (Z * W).map sec = Z.map sec * W.map sec := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, sec_mul e pr sec pr_sec sec_pr]

theorem secM_one (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) :
    (1 : Matrix m m k).map sec = e • (1 : Matrix m m A) := by
  have h1 : sec 1 = e := by rw [← map_one pr, sec_pr, mul_one]
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply, h1]
  · simp [Matrix.one_apply, h]

theorem secM_supp (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (Z : Matrix m m k) :
    e • Z.map sec = Z.map sec := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sec_eq e pr sec pr_sec sec_pr]

end Alg

end GlobalTheory.GlEmbed

namespace GlobalTheory.GlEmbed

section Phi

variable {A k : Type} [CommRing A] [Field k] {m : Type} [Fintype m] [DecidableEq m]
variable (c : A →+* A) (e : A) (pr : A →+* k) (sec : k →+ A) (J Ji : Matrix m m A)

def phi (G Gi : Matrix m m k) : Matrix m m A :=
  G.map sec + Formalism.UG.cT c (J * Gi.map sec * Ji) + (1 - e - c e) • (1 : Matrix m m A)

theorem cT_cT' (hcc : ∀ x, c (c x) = x) (X : Matrix m m A) : Formalism.UG.cT c (Formalism.UG.cT c X) = X := by
  ext i j; simp [Formalism.UG.cT, hcc]

theorem cT_three (hh : Formalism.UG.cT c J = J) (P Q : Matrix m m A) :
    Formalism.UG.cT c P * J * Formalism.UG.cT c Q = Formalism.UG.cT c (Q * J * P) := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hh, Matrix.mul_assoc]

variable (he : e * e = e) (hef : e * c e = 0) (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x)
include he hef pr_sec sec_pr

theorem hQ (G : Matrix m m k) : e • (J * G.map sec * Ji) = J * G.map sec * Ji := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, secM_supp e pr sec pr_sec sec_pr]

theorem hY (G : Matrix m m k) : c e • Formalism.UG.cT c (J * G.map sec * Ji) = Formalism.UG.cT c (J * G.map sec * Ji) := by
  rw [← cT_smul', hQ c e pr sec J Ji he hef pr_sec sec_pr]

theorem scal : c e * c e = c e ∧ (1 - e - c e) * e = 0 ∧ (1 - e - c e) * c e = 0 ∧
    (1 - e - c e) * (1 - e - c e) = 1 - e - c e := by
  have hff : c e * c e = c e := by rw [← map_mul, he]
  have hue : (1 - e - c e) * e = 0 := by rw [sub_mul, sub_mul, one_mul, he, mul_comm (c e) e, hef]; ring
  have huf : (1 - e - c e) * c e = 0 := by rw [sub_mul, sub_mul, one_mul, hef, hff]; ring
  refine ⟨hff, hue, huf, ?_⟩
  calc (1 - e - c e) * (1 - e - c e) = (1 - e - c e) - (1 - e - c e) * e - (1 - e - c e) * c e := by ring
    _ = 1 - e - c e := by rw [hue, huf]; ring

theorem phi_mul (hJ : Ji * J = 1) (G Gi G' Gi' : Matrix m m k) :
    phi c e sec J Ji G Gi * phi c e sec J Ji G' Gi' = phi c e sec J Ji (G * G') (Gi' * Gi) := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  unfold phi
  rw [blk_mul e (c e) _ hef hue huf huu (secM_supp e pr sec pr_sec sec_pr G) (hY c e pr sec J Ji he hef pr_sec sec_pr Gi)
    (secM_supp e pr sec pr_sec sec_pr G') (hY c e pr sec J Ji he hef pr_sec sec_pr Gi'),
    secM_mul e pr sec pr_sec sec_pr G G', secM_mul e pr sec pr_sec sec_pr Gi' Gi, ← Formalism.UG.cT_mul]
  congr 3
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ji J, hJ, Matrix.one_mul]

theorem phi_one (hJ : Ji * J = 1) : phi c e sec J Ji 1 1 = 1 := by
  have hJ' : J * Ji = 1 := mul_eq_one_comm.1 hJ
  unfold phi
  rw [secM_one e pr sec pr_sec sec_pr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hJ', cT_smul', Formalism.UG.cT_one,
    ← add_smul, ← add_smul]
  have : e + c e + (1 - e - c e) = 1 := by ring
  rw [this, one_smul]

theorem phi_unitary (hcc : ∀ x, c (c x) = x) (hJ : Ji * J = 1) (hh : Formalism.UG.cT c J = J) (G Gi : Matrix m m k)
    (hG : Gi * G = 1) :
    Formalism.UG.cT c (phi c e sec J Ji G Gi) * J * phi c e sec J Ji G Gi = J := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hcu : c (1 - e - c e) = 1 - e - c e := by rw [map_sub, map_sub, map_one, hcc]; ring
  set S := G.map sec with hSdef
  set Q := J * Gi.map sec * Ji with hQdef
  have hS : e • S = S := secM_supp e pr sec pr_sec sec_pr G
  have hQ' : e • Q = Q := hQ c e pr sec J Ji he hef pr_sec sec_pr Gi
  have hL : c e • Formalism.UG.cT c S = Formalism.UG.cT c S := by rw [← cT_smul', hS]
  have h1 : Formalism.UG.cT c (phi c e sec J Ji G Gi) * J = Q * J + Formalism.UG.cT c S * J + (1 - e - c e) • J := by
    unfold phi
    rw [← hSdef, ← hQdef, cT_add', cT_add', cT_smul', Formalism.UG.cT_one, cT_cT' c hcc, hcu]
    simp only [add_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hQJ : e • (Q * J) = Q * J := by rw [← Matrix.smul_mul, hQ']
  have hLJ : c e • (Formalism.UG.cT c S * J) = Formalism.UG.cT c S * J := by rw [← Matrix.smul_mul, hL]
  rw [h1]
  unfold phi
  rw [← hSdef, ← hQdef, blk_mul e (c e) _ hef hue huf huu hQJ hLJ hS (hY c e pr sec J Ji he hef pr_sec sec_pr Gi)]
  have h2 : Q * J * S = e • J := by
    rw [hQdef, hSdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ji J, hJ, Matrix.one_mul, ← secM_mul e pr sec pr_sec sec_pr, hG,
      secM_one e pr sec pr_sec sec_pr, Matrix.mul_smul, Matrix.mul_one]
  have h3 : Formalism.UG.cT c S * J * Formalism.UG.cT c Q = c e • J := by
    rw [cT_three c J hh, h2, cT_smul', hh]
  rw [h2, h3, ← add_smul, ← add_smul]
  have : e + c e + (1 - e - c e) = 1 := by ring
  rw [this, one_smul]

theorem phi_map (G Gi : Matrix m m k) : (phi c e sec J Ji G Gi).map pr = G := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hpe : pr e = 1 := by
    have h1 : sec 1 = e := by rw [← map_one pr, sec_pr, mul_one]
    rw [← h1, pr_sec]
  have hpf : pr (c e) = 0 := by
    have := congrArg pr hef
    rwa [map_mul, map_zero, hpe, one_mul] at this
  have hpu : pr (1 - e - c e) = 0 := by rw [map_sub, map_sub, map_one, hpe, hpf]; ring
  have hYe := hY c e pr sec J Ji he hef pr_sec sec_pr Gi
  ext i j
  have hij : Formalism.UG.cT c (J * Gi.map sec * Ji) i j = c e * Formalism.UG.cT c (J * Gi.map sec * Ji) i j := by
    conv_lhs => rw [← hYe]
    rfl
  unfold phi
  rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, map_add, map_add, hij, Matrix.smul_apply, smul_eq_mul,
    map_mul, map_mul, hpf, hpu, Matrix.map_apply, pr_sec]
  ring

theorem phi_supp (G Gi : Matrix m m k) :
    (e + c e) • (phi c e sec J Ji G Gi - 1) = phi c e sec J Ji G Gi - 1 := by
  obtain ⟨hff, -, -, -⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hS := secM_supp e pr sec pr_sec sec_pr G
  have hYe := hY c e pr sec J Ji he hef pr_sec sec_pr Gi
  ext i j
  have hs : e * G.map sec i j = G.map sec i j := by
    conv_rhs => rw [← hS]
    rfl
  have hy : c e * Formalism.UG.cT c (J * Gi.map sec * Ji) i j = Formalism.UG.cT c (J * Gi.map sec * Ji) i j := by
    conv_rhs => rw [← hYe]
    rfl
  unfold phi
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (1 - c e) * hs + (1 - e) * hy +
    (G.map sec i j + Formalism.UG.cT c (J * Gi.map sec * Ji) i j - 2 * (1 : Matrix m m A) i j) * hef -
    (1 : Matrix m m A) i j * he - (1 : Matrix m m A) i j * hff

end Phi

end GlobalTheory.GlEmbed

namespace GlobalTheory.GlEmbed

variable {D : D7}

theorem cT_JR (S : HSp D) : Formalism.UG.cT (cA D) (S.gram.map (incA D)) = S.gram.map (incA D) := by
  ext i j
  have hh : D.sp.cm.sig (S.gram j i) = S.gram i j := S.herm.eq (S.frame j) (S.frame i)
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [← hh]
  simp [cA, sigR, inclR, incA]

theorem JR_inv_mul (S : HSp D) (h : IsUnit S.gram.det) :
    (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_gl (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k)
    (b' : Matrix n (Fin S.rank) k) : b * b' = 1 → b' * b = 1 →
    ∃ gl : GL n k →* GA D S, (∀ g, SuppAt p.e S (gl g)) ∧ ∀ g, (mt S (gl g)).map p.pr = b * g.val * b' := by
  intro bb' b'b
  obtain ⟨he, hef, -⟩ := p.split
  set J := S.gram.map (incA D) with hJdef
  set Ji := (S.gram⁻¹).map (incA D) with hJidef
  have hJ : Ji * J = 1 := JR_inv_mul S (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S)
  have hh : Formalism.UG.cT (cA D) J = J := cT_JR S
  have hcc : ∀ x, cA D (cA D x) = x := Formalism.L2.Theta.cA_cA
  have Gmul : ∀ g h : Matrix n n k, b * g * b' * (b * h * b') = b * (g * h) * b' := fun g h => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b' b, b'b, Matrix.one_mul]
  let Φ : GL n k →* Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
    { toFun := fun g => phi (cA D) p.e p.sec J Ji (b * g.val * b') (b * (g⁻¹).val * b')
      map_one' := by
        simp only [inv_one, Units.val_one, Matrix.mul_one, bb']
        exact phi_one (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hJ
      map_mul' := fun g h => by
        rw [phi_mul (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hJ, Gmul, Gmul, mul_inv_rev, Units.val_mul,
          Units.val_mul] }
  have hmem : ∀ g, Φ.toHomUnits g ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := fun g => by
    show Formalism.UG.cT (cA D) (Φ g) * J * Φ g = J
    refine phi_unitary (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hcc hJ hh _ _ ?_
    rw [Gmul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, bb']
  refine ⟨Φ.toHomUnits.codRestrict _ hmem, fun g => ?_, fun g => ?_⟩
  · intro i j
    have h := phi_supp (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr (b * g.val * b') (b * (g⁻¹).val * b')
    exact congrFun (congrFun h i) j
  · exact phi_map (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr _ _

end GlobalTheory.GlEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitApprox

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (x : D.host.E) : cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] star x := rfl

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [cA_tmul, cA_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem approx_gen {F A B E : Type} [Field F] [CharZero F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (φ : A → B) (σ : E →+* E) (fp : A ⊗[F] E →+* B ⊗[F] E) (c : A ⊗[F] E →+* A ⊗[F] E)
    (hfp : ∀ a x, fp (a ⊗ₜ[F] x) = φ a ⊗ₜ[F] x) (h1 : φ 1 = 1) (hc : ∀ a x, c (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x)
    (O : Set B) (I : AddSubgroup (B ⊗[F] E)) (hI : ∀ b ∈ O, ∀ x : E, IsIntegral ℤ x → b ⊗ₜ[F] x ∈ I)
    (hE : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x)) (N : ℕ)
    (hB : ∀ y : B, ∃ (f : F) (β : B), β ∈ O ∧ y = algebraMap F B f + N • β) (z : A ⊗[F] E) :
    ∃ x : E, ∃ a ∈ I, ∃ a' ∈ I, fp (z - 1 ⊗ₜ[F] x) = N * a ∧ fp (c z - c (1 ⊗ₜ[F] x)) = N * a' := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, 0, zero_mem _, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, a, ha, a', ha', h, h'⟩ := hx
    obtain ⟨e, b, hb, b', hb', g, g'⟩ := hy
    refine ⟨d + e, a + b, add_mem ha hb, a' + b', add_mem ha' hb', ?_, ?_⟩
    · rw [mul_add, ← h, ← g, ← map_add, TensorProduct.tmul_add]; congr 1; ring
    · rw [mul_add, ← h', ← g', ← map_add fp, TensorProduct.tmul_add, map_add c, map_add c]; congr 1; ring
  | tmul a x =>
    obtain ⟨m, hm, hx⟩ := hE x
    have hm' : (m : F) ≠ 0 := Int.cast_ne_zero.2 hm
    obtain ⟨f, β, hβ, hy⟩ := hB ((m : F)⁻¹ • φ a)
    have key : ∀ x : E, fp (a ⊗ₜ[F] x - 1 ⊗ₜ[F] (f • (m • x))) = N * (β ⊗ₜ[F] (m • x)) := by
      intro x
      have e2 : φ a ⊗ₜ[F] x = ((m : F)⁻¹ • φ a) ⊗ₜ[F] (m • x) := by
        rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [map_sub, hfp, hfp, h1, e2, hy, TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul f, add_sub_cancel_left, ← TensorProduct.smul_tmul', nsmul_eq_mul]
    have hx' : IsIntegral ℤ (m • σ x) := by
      rw [← map_zsmul]
      exact hx.map σ.toIntAlgHom
    refine ⟨f • (m • x), _, hI _ hβ _ hx, _, hI _ hβ _ hx', key x, ?_⟩
    rw [hc, ← TensorProduct.smul_tmul, hc, TensorProduct.smul_tmul, map_zsmul]
    exact key _

theorem cancel_gen {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {N : ℕ} (hN : 0 < N) {a b : R}
    (h : (N : R) * a = N * b) : a = b := by
  have : IsUnit (N : R) := by
    have := (IsUnit.mk0 (N : F) (Nat.cast_ne_zero.2 hN.ne')).map (algebraMap F R)
    rwa [map_natCast] at this
  exact this.mul_left_cancel h

theorem tmul_mem {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    a ⊗ₜ[D.host.F] x ∈ intAE D :=
  AddSubgroup.subset_closure ⟨a, ha, ⟨x, hx⟩, rfl⟩

theorem mul_mem_intAE {a b : Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) (hb : b ∈ intAE D) :
    a * b ∈ intAE D := by
  induction ha using AddSubgroup.closure_induction with
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hx
      obtain ⟨b, hb, y, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      refine tmul_mem (fun v => ?_) (x.2.mul y.2)
      rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem approx (N : ℕ) (hN : 0 < N) (z : AE D) : ∃ c : D.host.E, ∃ A ∈ intAE D, ∃ A' ∈ intAE D,
    finPart D (z - incA D c) = N * A ∧ finPart D (cA D z - incA D (star c)) = N * A' :=
  approx_gen (F := D.host.F) (sndA D.host.F) (starRingEnd D.host.E) (finPart D) (cA D) finPart_tmul (map_one _) cA_tmul
    (intAf D.host.F) (intAE D) (fun _ hb _ hx => tmul_mem hb hx)
    (fun x => ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple) N
    (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N hN).1 z

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le (p : SplitPt D k) (N : ℕ) (hN : 0 < N) (z : AE D) (A : Af D.host.F ⊗[D.host.F] D.host.E)
    (hA : A ∈ intAE D) (h : finPart D z = N * A) : valuation k (p.pr z) ≤ valuation k (N : k) := by
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNk : (N : k) ≠ 0 := by
    have := (map_ne_zero (p.pr.comp (incA D))).2 hNE
    rwa [map_natCast] at this
  have he : finPart D p.e ∈ intAE D := by
    have := (p.int_iff 1).1 (one_mem _)
    rwa [← map_one p.pr, p.sec_pr, mul_one] at this
  have h0 : (N : AE D) * p.sec (p.pr z / N) = p.e * z := by
    rw [← p.sec_pr, ← nsmul_eq_mul, ← AddMonoidHom.map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hNk]
  have h1 := congrArg (finPart D) h0
  rw [RingHom.map_mul, RingHom.map_mul, h, mul_left_comm] at h1
  have h1' : finPart D (N : AE D) = N := map_natCast (finPart D) N
  rw [h1'] at h1
  have h2 := cancel_gen (F := D.host.F) hN h1
  have h3 : p.pr z / N ∈ 𝒪[k] := (p.int_iff _).2 (by rw [h2]; exact mul_mem_intAE he hA)
  have h4 : valuation k (p.pr z / N) ≤ 1 := h3
  have h5 : p.pr z = N * (p.pr z / N) := (mul_div_cancel₀ _ hNk).symm
  rw [h5, map_mul]
  exact mul_le_of_le_one_right' h4

theorem exists_nat (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 ∧
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) < valuation k ((q.1 : 𝒪[k]) : k) := by
  have hlt : ∀ x : 𝒪[k], ¬ IsUnit x → valuation k (x : k) < 1 := fun x hx =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have hq := hlt _ q.2.not_isUnit
  refine ⟨hq, ?_⟩
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨r, hr⟩ := hQ
  have hr' : (Q : k) = (q.1 : k) * r := by exact_mod_cast congrArg (fun x : 𝒪[k] => (x : k)) hr
  have hle : valuation k (Q : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  have hq0 : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
    rw [Valuation.pos_iff]
    exact fun h => q.2.ne_zero (Subtype.ext h)
  refine ⟨Q * Q, Nat.mul_pos Fintype.card_pos Fintype.card_pos, ?_⟩
  rw [Nat.cast_mul, map_mul]
  exact (mul_le_mul' hle hle).trans_lt (mul_lt_of_lt_one_right hq0 hq)

theorem exists_unif_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k), ∃ c : D.host.E, valuation k (p.pr (incA D c)) = valuation k ((q.1 : 𝒪[k]) : k) ∧ valuation k (p.pr (incA D (star c))) = 1 := by
  intro D k _ _ _ _ p q
  obtain ⟨hq, N, hN, hNq⟩ := exists_nat q
  have hs : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have he : p.pr p.e = 1 := by rw [← hs, p.pr_sec]
  have hce : p.pr (cA D p.e) = 0 := by
    have h : p.e * cA D p.e = 0 := p.split.2.1
    have := congrArg p.pr h
    rwa [map_mul, he, one_mul, map_zero] at this
  have hcq : ∀ a, p.pr (cA D (p.sec a)) = 0 := fun a => by
    have h : p.sec a = p.e * p.sec a := by rw [← p.sec_pr, p.pr_sec]
    rw [h, map_mul, map_mul, hce, zero_mul]
  obtain ⟨c, A, hA, A', hA', h, h'⟩ := approx N hN (p.sec (q.1 : k) + cA D p.e)
  have v1 := val_le p N hN _ A hA h
  have v2 := val_le p N hN _ A' hA' h'
  rw [map_sub, map_add, p.pr_sec, hce, add_zero] at v1
  rw [map_sub, map_add, map_add, hcq, cA_cA, he, zero_add] at v2
  refine ⟨c, ?_, ?_⟩
  · exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap]; exact v1.trans_lt hNq)
  · rw [← map_one (valuation k)]
    exact Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, map_one]; exact v2.trans_lt (hNq.trans hq))

end GlobalTheory.FinPl.SplitApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem fjKer_eq_om_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  intro D ψ W W₀ V₀ A L ρ dW o ζ χ χ' om hW Ξ hΞ h₀ n h
  have hp : (o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n) = ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    rw [← ptT_yZero_vecB o dW ζ n, AddEquiv.symm_apply_apply]
  have hfix : actO V₀ W₀ (o.emb (h₀, 1)) 1 (ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n) =
      ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    apply (o.resS W₀).injective
    rw [o.resS_actO, ptT_yZero_vecB]
    simp only [actO_eq, inv_one, mt_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul]
  have hm : om (o.emb (h₀, 1), 1) (om (1, h) Ξ) = om (o.emb (h₀, 1), h) Ξ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [hp, fjKer, opA, jacT, map_smul, hW.om_heis _ _ _ _ (hW.om_pres _ _ hΞ), hfix, hm, cenT_yZero_vecB]
  simp only [Pi.smul_apply, smul_eq_mul, heisO, zero_add, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDisj

variable {D : D7}

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [TensorProduct.smul_tmul']; rfl
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_smul (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) :
    hO S T (c • x) (c' • y) = (c * c') • hO S T x y := by
  simp only [hO, Matrix.smul_apply, cA_smul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, smul_smul]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO, hO_add_left, mul_add, map_add]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO_add_right, mul_add, map_add]

theorem symplOH_smul_smul_eq_zero (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (h : c * c' = 0) :
    symplOH S T (c • x) (c' • y) = 0 := by
  rw [symplOH, symplO, hO_smul_smul, h, zero_smul, mul_zero, map_zero, mul_zero]

theorem heisO_smul_add_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  intro D ψ S T c c' x y f h
  funext w
  simp only [heisO]
  rw [symplOH_add_right, symplOH_add_left, symplOH_smul_smul_eq_zero S T c c' x y h, add_zero,
    AddChar.map_add_eq_mul, add_assoc, mul_assoc]

end GlobalTheory.HeisDisj
end


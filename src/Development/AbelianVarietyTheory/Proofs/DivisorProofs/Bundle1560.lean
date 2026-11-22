import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanOrbitExpEigenvector
section
open scoped TensorProduct Matrix
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU tensNU_tmul extH)
open GlobalTheory.AutFunCompare (sgW sgW_mul mat_extH)

noncomputable section

namespace GlobalTheory.StabLine

theorem smul_mat_mulVec {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (c • M) *ᵥ x = c • (M *ᵥ x) := by
  ext p; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem exp_mulVec_of_eigen {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (l : ℂ)
    (h : Z *ᵥ v = l • v) (t : ℝ) :
    NormedSpace.exp (t • Z) *ᵥ v = NormedSpace.exp ((t : ℂ) * l) • v := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have ht : t • Z = (t : ℂ) • Z := by ext i j; simp [Complex.real_smul]
  rw [ht]
  have hpow : ∀ k : ℕ, ((t : ℂ) • Z) ^ k *ᵥ v = ((t : ℂ) * l) ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, smul_mat_mulVec, h, smul_smul,
        smul_smul]
      congr 1; ring
  let f : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ) :=
    AddMonoidHom.mk' (fun A => A *ᵥ v) (fun A B => Matrix.add_mulVec A B v)
  have hf : Continuous f := continuous_id.matrix_mulVec continuous_const
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • Z)).map f hf
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) * l)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  simp only [Function.comp_apply, f, AddMonoidHom.mk'_apply, smul_mat_mulVec, hpow, smul_smul, smul_eq_mul]

theorem tensNU_mul_one_tmul {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * ((1 : R') ⊗ₜ[F] e) = tensNU j hj (u * ((1 : R) ⊗ₜ[F] e)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  | tmul a e' => simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem mat_extH_eq {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (g : HA R σ J) (r s : Fin n) :
    (HA.mat R' σ J (extH σ J j hj g)).1 r s =
      (1 : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) r s +
        tensNU j hj ((HA.mat R σ J g).1 r s - (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s) := by
  rw [mat_extH]
  by_cases h : r = s
  · subst h; simp [map_sub]; ring
  · simp [Matrix.one_apply, h]

theorem mulVec_embArch_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E), x ≠ 0 → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (l : ℂ),
      Z *ᵥ (fun i => τ.1 (x i)) = l • (fun i => τ.1 (x i)) → ∀ (t : ℝ) (y : GArch σ J w), GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z) →
      ∃ a : AF F ⊗[F] E, (matHom _ σ J (embArch σ J w y)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = a • fun i => inclR (F := F) (AF F) (x i) := by
  intro F E _ _ _ _ _ σ hcm n J x _hx w τ Z l hZ t y hy
  classical
  let T1 := tensNU (E := E) (sgW w) (sgW_mul w)
  let T2 := tensNU (E := E) (R' := AF F) (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)
  let Y : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := (matHom _ σ J y).1
  let X' : Fin n → w.Completion ⊗[F] E := fun i => (1 : w.Completion) ⊗ₜ[F] x i
  obtain ⟨b, hb⟩ := (infEmb_bijective hcm τ).2 (NormedSpace.exp ((t : ℂ) * l))
  have hτ : ∀ i, infEmb τ (X' i) = τ.1 (x i) := fun i => by simp [X']
  have hYX : ∀ r, (Y *ᵥ X') r = b * X' r := by
    intro r
    apply (infEmb_bijective hcm τ).1
    rw [RingHom.map_mulVec, map_mul, hb, hτ]
    have e1 := congrFun (exp_mulVec_of_eigen Z _ l hZ t) r
    rw [← hy, GlobalTheory.Orb.archMat_apply] at e1
    have e2 : (infEmb τ ∘ X') = fun i => τ.1 (x i) := funext hτ
    rw [e2]
    simpa [Pi.smul_apply, smul_eq_mul] using e1
  have hM : ∀ r s, (matHom _ σ J (embArch σ J w y)).1 r s =
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s +
        T2 (T1 (Y r s - (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s)) := by
    intro r s
    show (HA.mat _ σ J (extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)
      (extH σ J (sgW w) (sgW_mul w) y))).1 r s = _
    refine (mat_extH_eq (R' := AF F) σ J _ _ _ r s).trans ?_
    rw [mat_extH_eq]
    simp [T1, T2, Y, matHom_apply]
  have hinc : ∀ e : E, inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := fun _ => rfl
  have hkey : ∀ (u : w.Completion ⊗[F] E) (e : E), T2 (T1 u) * inclR (F := F) (AF F) e = T2 (T1 (u * ((1 : w.Completion) ⊗ₜ[F] e))) := by
    intro u e
    rw [hinc]
    exact (tensNU_mul_one_tmul (R' := AF F) _ _ (T1 u) e).trans (congrArg T2 (tensNU_mul_one_tmul _ _ u e))
  refine ⟨1 + T2 (T1 (b - 1)), funext fun r => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hM, add_mul, Finset.sum_add_distrib, hkey]
  have hs : ∑ s, T2 (T1 ((Y r s - (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s) * ((1 : w.Completion) ⊗ₜ[F] x s))) =
      T2 (T1 ((b - 1) * ((1 : w.Completion) ⊗ₜ[F] x r))) := by
    rw [← map_sum, ← map_sum]
    congr 2
    have := hYX r
    simp only [Matrix.mulVec, dotProduct, X'] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hs, ← hkey]
  simp [Matrix.one_apply]

end GlobalTheory.StabLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPoint
section
noncomputable section

namespace GlobalTheory.LevModel

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem exists_frBor_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {p p' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d p y) (h' : FrOver d p' y') (hb : FrBor t p p') : ∃ t' : Ix Dw → Sˣ, FrBor t' y y' := by
  obtain ⟨e, hu, -⟩ := h
  obtain ⟨e', hu', -⟩ := h'
  obtain ⟨ex, au, -⟩ := hb
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').2.1 (by rw [← e, ← e', ex]) fun τ i => ?_
  obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
  refine ⟨cf, by rw [c₁]; exact (t _).isUnit, c₂, ?_⟩
  have k := (GlobalTheory.FrameLift.comb_iff d.m e (fun j => (p.tan τ j).1) cf (ex ▸ (p'.tan τ i).1)).1 hcf
  rw [funext (hu τ), hu'] at k
  exact k

theorem lact_conj_eq_rmul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hLev σ₂ hσ₂ k₂ k δ hG hδ hOv γ₂ hγ₂ x hx x' hM
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    unfold GoodEmb at hσ₂ ⊢
    rw [← hσ₂]
    rfl
  have hU := hL.unf _ hσ
  have hU₂ := hL₂.unf _ hσ₂
  have hγx : lact γ₂ x ∈ ((U₂ σ₂).X k₂).dom := (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ hγ₂ x).2 hx
  obtain ⟨t₀, ht₀⟩ := (hU₂.2.2.2.1 k₂ k₂ ⟨x, hx⟩ ⟨lact γ₂ x, hγx⟩).2
    ⟨γ₂, hγ₂, ExtFPf.oneF _, ExtFPf.oneF_mem _, by rw [ExtFPf.rmul_oneF]⟩
  have hM' : Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ (lact γ₂ x) (lact (MulAut.conj δ γ₂) x') := by
    intro τ h₂ h₁
    have e := hM τ h₂ h₁
    show ((MulAut.conj δ γ₂ : GL _ _) : Matrix _ _ _).map τ * mat x' ⟨τ, h₁⟩ =
      (δ : Matrix _ _ _).map τ * ((γ₂ : Matrix _ _ _).map τ * mat x ⟨τ, h₂⟩)
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul (f := τ), ← Matrix.map_mul (f := τ),
      ← Units.val_mul, ← Units.val_mul, MulAut.conj_apply, inv_mul_cancel_right]
  obtain ⟨hx', t₁, -, y, hy₁, hy₂⟩ := hOv x hx x' hM
  obtain ⟨hx'', t₂, -, y', hy₁', hy₂'⟩ := hOv (lact γ₂ x) hγx _ hM'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨t', ht'⟩ := exists_frBor_of_frOver d hy₂ hy₂' ht₀
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have hb := G.2.1 _ _ _ _ _ (G.2.1 _ _ _ _ _ hy₁ ht') (G.2.2.1 _ _ _ hy₁')
  obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k ⟨x', hx'⟩ ⟨_, hx''⟩).1 ⟨_, hb⟩
  exact ⟨γ, hγ, b, hb', eq_of_heq (Sigma.mk.inj e).2⟩

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectivePairTOfLev
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.TatePerfect

theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (k n : ℕ) :
    (k • t).lev n = t.lev n ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem lev_congr {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (h2 : ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s)
    (φ : Tate p M →ₗ[ℤ_[p]] Tate p M') {n : ℕ} {t t' : Tate p M} (h : t.lev n = t'.lev n) :
    (φ t).lev n = (φ t').lev n := by
  have e : t = t' + (t - t') := by abel
  have h3 : (t - t').lev n = 1 := by
    have := congrArg (·.lev n) e
    simp only [Tate.lev_add] at this
    rw [h] at this
    exact left_eq_mul.1 this
  obtain ⟨s, hs⟩ := (h2 n _).1 h3
  rw [e, hs, map_add, map_smul, Tate.lev_add, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, lev_nsmul,
    Tate.lev_pow, _root_.mul_one]

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  (A : Out.PolAV (Sp C))

theorem weilT_flip_surjective
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (h2 : ∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s)
    (φ : TateA A p →ₗ[ℤ_[p]] Tate p Cˣ) : ∃ s : TateA A p, ∀ t, weilT A p t s = φ t := by
  choose! τ hτ using h1
  let κ : ℕ → GlobalTheory.ChTor.Pts A.A → Cˣ := fun n x => (φ (τ n x)).lev n
  have hκ : ∀ n (t : TateA A p), κ n (t.lev n) = (φ t).lev n := fun n t =>
    lev_congr h2 φ (hτ n _ (t.lev_pow n))
  have hm : ∀ n z z', z ^ p ^ n = 1 → z' ^ p ^ n = 1 → κ n (z * z') = κ n z * κ n z' := by
    intro n z z' hz hz'
    have e : z * z' = (τ n z + τ n z').lev n := by rw [Tate.lev_add, hτ n z hz, hτ n z' hz']
    rw [e, hκ, map_add, Tate.lev_add]
  have hp := fun n => weil_perfect (A := A) (one_le_ppow p n) (κ n) (hm n)
  choose s hs hu using hp
  have hc : ∀ n, s (n + 1) ^ p = s n := by
    intro n
    refine hu n _ ⟨?_, fun z hz => ?_⟩
    · rw [← pow_mul, ← pow_succ']; exact (hs (n + 1)).1
    · have hz' : z ^ p ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hz, one_pow]
      rw [← weil_level (one_le_ppow p n) (Fact.out : p.Prime).pos hz
        (by rw [← pow_succ]; exact (hs (n + 1)).1), ← pow_succ, (hs (n + 1)).2 z hz']
      have e : z = (p • τ n z).lev (n + 1) := by rw [lev_nsmul, Tate.lev_succ, hτ n z hz]
      conv_lhs => rw [e, hκ, map_nsmul, lev_nsmul, Tate.lev_succ]
  refine ⟨Tate.mk s fun n => ⟨(hs n).1, hc n⟩, fun t => Tate.ext fun n => ?_⟩
  rw [lev_weilT, Tate.lev_mk, (hs n).2 _ (t.lev_pow n), hκ]

theorem eq_zero_of_weilT
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (s : TateA A p) (hs : ∀ t, weilT A p t s = 0) : s = 0 := by
  refine Tate.ext fun n => ?_
  have hp := weil_perfect (A := A) (one_le_ppow p n) (fun _ => 1) (fun _ _ _ _ => (_root_.mul_one _).symm)
  refine hp.unique ⟨s.lev_pow n, fun z hz => ?_⟩ ⟨(0 : TateA A p).lev_pow n, fun z hz => ?_⟩
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, hs, Tate.lev_zero]
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, map_zero, Tate.lev_zero]

end GlobalTheory.HTLat.TatePerfect

namespace GlobalTheory.HTLat

theorem bijective_pairT_of_lev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) (ε : Eps p C), (∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x) → (∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s) → Function.Bijective (pairT A ε).flip ∧ Function.Bijective (pairT A ε) := by
  intro p _ C _ _ _ A ε h1 h2
  have hb : Function.Bijective (pairT A ε).flip := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun s hs => TatePerfect.eq_zero_of_weilT A h1 s fun t => ?_
      have : ε.equiv.symm (weilT A p t s) = 0 := LinearMap.congr_fun hs t
      exact ε.equiv.symm.map_eq_zero_iff.1 this
    · intro l
      obtain ⟨s, hs⟩ := TatePerfect.weilT_flip_surjective A h1 h2 (ε.equiv.toLinearMap ∘ₗ l)
      refine ⟨s, LinearMap.ext fun t => ?_⟩
      change ε.equiv.symm (weilT A p t s) = l t
      rw [hs]
      exact ε.equiv.symm_apply_apply _
  refine ⟨hb, ?_⟩
  have e : ⇑(pairT A ε) = Neg.neg ∘ ⇑(pairT A ε).flip := by
    funext s
    exact LinearMap.ext fun t => ((isAlt_pairT A ε).neg_eq t s).symm
  rw [e]
  exact (Equiv.neg _).bijective.comp hb

end GlobalTheory.HTLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPointsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  first | exact @GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | exact GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | (intros; apply GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingUnipotentMemFlagUnipotentRadicalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∀ x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E, ι (GlobalTheory.CuspRep.unip x) ∈ GlobalTheory.StdPar.unip σ J Xf (insert k S) := by
  first | exact @GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem | exact GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem | (intros; apply GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRankStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant_rank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row | exact GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row | (intros; apply GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanThetaAnFib
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

set_option maxHeartbeats 1000000 in

theorem canTheta_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (Wt : UW U) (k : U.Comp) (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (Wt.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → ∀ Pm : (Wt.F.Di (Wt.ik k)).La →+ (Fin Wt.g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (Wt.φ k a : Fin r → E) (relab c σ (Wt.e j).1) (Wt.e j).2) → (∃ Hm θ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta Wt.F (Wt.ik k) Pm (U.un k x) Hm θ) ∧ ∀ Hm θ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta Wt.F (Wt.ik k) Pm (U.un k x) Hm θ → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx Wt.e x.1 (U.X k).Λ (unC U k x), A.Marked (Wt.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ ∧ ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hb hper hty x hx1 Pm' hPm'
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr W k
  obtain ⟨-, -, -, -, hsm, -, huniq, -⟩ := GlobalTheory.Dict.hx_laws E r (U.X k) W.g bas idx 0 hb (by simp) x.1 x.2
  obtain ⟨Pm, hPm, hP, hu, hder, hrest⟩ := W.pt k x
  obtain rfl : Pm' = Pm := AddMonoidHom.ext fun a => funext fun j => (hPm' a j).trans (hPm a j).symm
  obtain ⟨Hm, χl, fr, θ, Fd, hH, hpos, hIm, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrest hx1
  have hcan : GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsCanTheta W.F (W.ik k) Pm' (U.un k x) Hm θ :=
    ⟨hH, hpos, hIm, χl, fr, h1, h2, h3, h4, h5, h6⟩
  refine ⟨⟨Hm, θ, hcan⟩, fun Hm' θ' hcan' => ?_⟩
  obtain ⟨rfl, rfl⟩ : Hm = Hm' ∧ θ = θ' :=
    GlobalTheory.TwistFactorCompare.isCanTheta_unique (F := W.F) (k := W.ik k) (Pm := Pm') (y := U.un k x)
      ⟨hP, hu, hcan⟩ ⟨hP, hu, hcan'⟩
  obtain ⟨ex, hl, e1, e2, e3, e4, e5⟩ := exists_ex_transport W.F (W.ik k) Pm' hP (unC U k x).x hu
  have hpv : ∀ a, Pm' a = pv (U.X k) idx x.1 (W.emb k a) := fun a => by
    funext j
    rw [hPm, hper]
    rfl
  have hsurj : ∀ v ∈ (U.X k).Λ, ∃ a, W.emb k a = v := fun v hv =>
    ⟨(W.φ k).symm ⟨v, hv⟩, by simp [UW.emb]⟩
  have hmem : ∀ a, W.emb k a ∈ (U.X k).Λ := fun a => (W.φ k a).2
  have hrange : ∀ z, z ∈ Pm'.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := fun z => by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, hmem a, hpv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj v hv
      exact ⟨a, hpv a⟩
  have hspan' : Submodule.span E ((U.X k).Λ : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hhx : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w := by
    refine (huniq _ hspan').2 Hm hH ?_
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hsurj u hu
    obtain ⟨b, rfl⟩ := hsurj v hv
    rw [← hpv, ← hpv, hIm, ← hEF]
    simp
  have hl' : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm' z).left := funext hl
  refine ⟨{ ex := ex
            ex_add := e1
            ex_onto := e2
            ex_ker := fun z => (e3 z).trans (hrange z)
            ex_lin := fun a z => by simp only [hty]; exact e4 a z
            hol := ?_
            der := fun ℓ => by rw [hl']; exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hl]; exact h1 j
            fr_ne := fun j z => by rw [hl]; exact h2 j z
            fr_g := fun j j' z => by rw [hl]; exact h3 j j' z
            fr_0 := fun j => by rw [hl]; exact h4 j
            χ := fun v => χl (pv (U.X k) idx x.1 v)
            χ_norm := ?_
            fr_per := ?_ }, ?_, ?_, ⟨Pm'.range, Fd, hrange, h7, ?_⟩, hhx⟩
  · rw [hl']
    intro V f
    have := ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm' hP V f
    simpa only [Set.mem_univ, true_and] using this
  · intro v hv
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [← hpv]
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1
      (Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((ex 0).left (IsLocalRing.closedPoint ℂ))))
    exact (h5 a j 0).1
  · intro v hv j z
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [hl, ← hpv, ← hhx, ← hhx]
    exact (h5 a j z).2
  · intro a ha
    show levPt Xo (unC U k x).x a = ex _
    rw [e5 a ha, hsm, hpv]
    congr 1
    funext j
    simp [UW.mark]
  · intro j z pt
    show _ = (ex z).left → _ → ⊤ ≤ (ex z).left ⁻¹ᵁ _ → _ = θ z * fr j z ^ (1 : ℤ)
    rw [hl, zpow_one]
    exact h6 j z pt
  · simp only [← hhx]
    exact h8

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelianStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_trivial_bundle_abelian : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  first | exact @GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two | exact GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two | (intros; apply GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassGradedTensorBundleFinsetSum
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem cls_LL_add (F : FlagMod.Frames Y π) (e e' : Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (e + e')) (F.isLB_LL _) =
      GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _) + GlobalTheory.CechPic.cls (F.LL e') (F.isLB_LL _) := by
  have h := GlobalTheory.CechPic.isLB_tens (F.isLB_LL e) (F.isLB_LL e')
  refine ((GlobalTheory.CechPic.cls_eq_iff (F.isLB_LL (e + e')) h).2 (GlobalTheory.CechPic.iso_of_chart h ⟨fun k => (k, k), fun _ _ h => ⟨h, h⟩, ?_⟩)).trans
    (GlobalTheory.CechPic.cls_tens _ _ h)
  intro y p q hp hq
  refine Eq.trans ?_ (GlobalTheory.CechPic.gm_tens (F.LL e) (F.LL e') (𝟙 Z) y (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).symm
  exact (congrArg (gm (𝟙 Z) y _) (F.LL_add_g e e' p q)).trans (map_mul _ _ _)

def clsLLHom (F : FlagMod.Frames Y π) : (Ix Dw → ℤ) →+ GlobalTheory.CechPic.Pic Z :=
  AddMonoidHom.mk' (fun e => GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _)) (cls_LL_add F)

theorem cls_LL_sum (F : FlagMod.Frames Y π) {ι : Type} (s : Finset ι) (e : ι → Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (∑ i ∈ s, e i)) (F.isLB_LL _) = ∑ i ∈ s, GlobalTheory.CechPic.cls (F.LL (e i)) (F.isLB_LL _) :=
  map_sum (clsLLHom F) e s

end GlobalTheory.FlagPlucker
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStepStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  first | exact @GlobalTheory.cuspForm_decay_step | exact GlobalTheory.cuspForm_decay_step | (intros; apply GlobalTheory.cuspForm_decay_step <;> assumption)
end


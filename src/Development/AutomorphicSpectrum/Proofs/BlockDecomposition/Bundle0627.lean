import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0237
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.JacquetLeft

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tmul_ne_zero' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DYha2.main hx hy

theorem isCuspidal_of_jacquet_min_left {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [Nontrivial W']
    (π : Representation ℂ (GL (Fin n) k) V) (h : a + b = n)
    (hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < a →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))))
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W') (hσ : IsSmooth σ)
    (φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ)) (hφ : Function.Surjective φ) :
    IsCuspidal σ := by
  refine (isCuspidal_iff_maximal k a W σ).2 ⟨hσ, fun r t h' hr ht => ?_⟩
  have hcd : r + (t + b) = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin r (t + b) hcd hr (by omega))
  set K' := twKer σ (unipRad k (two (stdSum h'))) 1 with hK'
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  let T : W ⊗[ℂ] W' →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := LinearMap.rTensor W' K'.mkQ
  let Φ : V →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := T ∘ₗ φ.toLinearMap ∘ₗ Kab.mkQ
  have hΦ : ∀ v, Φ v = T (φ (Submodule.Quotient.mk v)) := fun v => rfl

  have hA : ∀ u' ∈ unipRad k (two (stdSum h')), ∀ y : W ⊗[ℂ] W',
      T (extTensor σ ρ (u', 1) y) = T y := by
    intro u' hu' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w w' =>
      rw [extTensor_tmul]
      simp only [T, LinearMap.rTensor_tmul, map_one, Module.End.one_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq K').2 (Submodule.subset_span ⟨⟨u', hu'⟩, w, by simp⟩)
    | add x y hx hy => simp only [map_add, hx, hy]

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, GeneralLinearGroup.det g.1 = 1 → g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)
  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V, Φ (π u v) = Φ v := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg2 : g.2 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg1 : g.1 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.1 = 1 := det_eq_one_of_mem_unipRad k hg1
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    rw [hu_eq, map_mul, Module.End.mul_apply, hΦ, ← hB g hdet hg2, φ.isIntertwining,
      show g = (g.1, 1) from Prod.ext rfl hg2, hA _ hg1, hN _ hn', ← hΦ]

  have hΦ0 : ∀ v, Φ v = 0 := by
    intro v
    have hv : v ∈ twKer π (unipRad k (two (stdSum hcd))) 1 := hJ ▸ Submodule.mem_top
    have : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, w, rfl⟩
      simp [hC u u.2 w]
    exact this hv
  have hsurj : Function.Surjective Φ :=
    (LinearMap.rTensor_surjective W' (Submodule.mkQ_surjective K')).comp
      (hφ.comp (Submodule.mkQ_surjective Kab))

  show Subsingleton (W ⧸ K')
  refine ⟨fun x y => ?_⟩
  rw [← sub_eq_zero]
  by_contra hq
  obtain ⟨w, hw⟩ := exists_ne (0 : W')
  obtain ⟨v, hv⟩ := hsurj ((x - y) ⊗ₜ w)
  exact tmul_ne_zero' hq hw (hv.symm.trans (hΦ0 v))

theorem nontrivial_jacquet_top {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : π.IsIrreducible) (h : n + 0 = n) :
    Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = false := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · rfl
    · exact Fin.elim0 y
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  haveI : Nontrivial V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hπ
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

theorem bernsteinZelevinsky (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness := fun k _ _ _ _ =>
  ⟨GlobalTheory.BZBridge.irreducibleAdmissible hA k, GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k, GlobalTheory.SmGL.IndDual.inductionContragredient k⟩

theorem exists_quotient_jac₂ (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k)),
      0 < a ∧ IsCuspidal s.ρ ∧
        ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor s.ρ t.ρ), Function.Surjective φ := by
  classical
  let P : ℕ → Prop := fun d => 0 < d ∧ ∃ (t : ℕ) (h : d + t = n),
    Nontrivial (Jacquet π (unipRad k (two (stdSum h))))
  have hP : ∃ d, P d := ⟨n, hn, 0, rfl, nontrivial_jacquet_top π hi _⟩
  obtain ⟨ha, b, h, hJ⟩ := Nat.find_spec hP
  have hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < Nat.find hP →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))) := fun c d h' hc hca => by
    by_contra hns
    exact Nat.find_min hP hca ⟨hc, d, h', not_subsingleton_iff_nontrivial.1 hns⟩
  generalize Nat.find hP = a at ha h hJ hmin
  have hBZ := bernsteinZelevinsky hA
  have hfl : HasFiniteLength (jac (two (stdSum h)) π) :=
    (hBZ k).2.1 _ _ _ (two (stdSum h)) V π hs (hasFiniteLength_of_isIrreducible hi)
  obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ :=
    IrrQuot.exists_irreducible_smooth_quotient _ (isSmooth_jac (two (stdSum h)) hs) hfl hJ
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k Bool (Two (Fin a) (Fin b))
    (⟨Y, τ, hτs, hτi⟩ : IrrRep _)
  let F : ∀ j : Bool, Representation ℂ (GL (Two (Fin a) (Fin b) j) k) (s j).V := fun j => (s j).ρ
  let B := GlobalTheory.JacFactor.piTensorBoolEquiv F
  let φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor (F false) (F true)) :=
    ⟨B.toLinearEquiv.toLinearMap ∘ₗ E.toLinearEquiv.toLinearMap ∘ₗ q.toLinearMap, fun g =>
      LinearMap.ext fun v => by
        show B (E (q (jac (two (stdSum h)) π (leviTwo k _ _ g) v))) =
          extTensor (F false) (F true) g (B (E (q v)))
        have e1 : E (τ (leviTwo k _ _ g) (q v)) = piTensor F (leviTwo k _ _ g) (E (q v)) :=
          E.toIntertwiningMap.isIntertwining _ _ _ _
        have e2 := B.toIntertwiningMap.isIntertwining _ _ g (E (q v))
        rw [q.isIntertwining]
        exact (congrArg B e1).trans e2⟩
  have hφ : Function.Surjective φ :=
    B.toLinearEquiv.surjective.comp (E.toLinearEquiv.surjective.comp hq)
  haveI : Nontrivial (s true).V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible (s true).irr
  exact ⟨a, b, h, s false, s true, ha,
    isCuspidal_of_jacquet_min_left π h hmin (s false).ρ (s true).ρ (s false).smooth φ hφ, φ, hφ⟩

theorem exists_injective_comp {G A B C : Type} [Group G] [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    [AddCommMonoid C] [Module ℂ C] {ρ₁ : Representation ℂ G A} {ρ₂ : Representation ℂ G B}
    {ρ₃ : Representation ℂ G C} (ψ : ρ₁.IntertwiningMap ρ₂) (hψ : Function.Injective ψ) (E : ρ₂.Equiv ρ₃) :
    ∃ f : ρ₁.IntertwiningMap ρ₃, Function.Injective f :=
  ⟨E.toIntertwiningMap.comp ψ, E.toLinearEquiv.injective.comp hψ⟩

set_option maxHeartbeats 4000000 in

theorem exists_embedding_of_prod₂ {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k))
    (ha : 0 < a) (hc : IsCuspidal s.ρ) (ψ : π.IntertwiningMap (prod₂ s.ρ t.ρ)) (hψ : Function.Injective ψ) :
    ∃ (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = a + b), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  have hd : ∑ i, (![IrrGL.of s.ρ s.smooth s.irr, IrrGL.of t.ρ t.smooth t.irr] i).1 = a + b :=
    Fin.sum_univ_two _
  obtain ⟨E⟩ := nonempty_prod₂_equiv_prodIrr s.ρ s.smooth s.irr t.ρ t.smooth t.irr hd
  obtain ⟨f, hf⟩ := exists_injective_comp ψ hψ E
  exact ⟨_, hd, IrrGL.isCusp_of.2 ⟨ha, hc⟩, f, hf⟩

theorem exists_embedding {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = n), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  obtain ⟨a, b, rfl, s, t, ha, hc, φ, hφ⟩ := exists_quotient_jac₂ hA π hs hi hn
  haveI : Nontrivial s.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible s.irr
  haveI : Nontrivial t.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible t.irr
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw⟩ := exists_ne (0 : s.V)
    obtain ⟨w', hw'⟩ := exists_ne (0 : t.V)
    obtain ⟨v, hv⟩ := hφ (w ⊗ₜ w')
    exact tmul_ne_zero' hw hw' hv.symm
  exact (GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V s.V t.V π s.ρ t.ρ hs hi φ hφ0).elim fun ψ hψ =>
    exists_embedding_of_prod₂ π s t ha hc ψ hψ

theorem jacquetSubLeft : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k :=
  fun hA x hx => exists_embedding hA x.rep x.2.rep.smooth x.2.rep.irr hx

end GlobalTheory.CompanionTheory.JacquetLeft

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFunctionalEquationOfTwoVariable
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RSKernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def mt (r₁ r₃ : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := !![r₁ 0, r₃ 0; r₁ 1, r₃ 1]

def sw (D : F) : Matrix (Fin 2) (Fin 2) F := !![0, D; -D, 0]

theorem mt_det (r₁ r₃ : Fin 2 → F) : (mt r₁ r₃).det = dt r₁ r₃ := by
  simp [mt, det_fin_two, dt]; ring

theorem sw_det (D : F) : (sw D).det = D * D := by
  simp [sw, det_fin_two]

theorem sw_zero (D : F) (v : Fin 2 → F) : (sw D *ᵥ v) 0 = D * v 1 := by
  simp [sw, mulVec, dotProduct, Fin.sum_univ_two]

theorem sw_one (D : F) (v : Fin 2 → F) : (sw D *ᵥ v) 1 = -D * v 0 := by
  simp [sw, mulVec, dotProduct, Fin.sum_univ_two]

theorem dt_left (r₁ r₃ v : Fin 2 → F) : dt r₁ (mt r₁ r₃ *ᵥ v) = (sw (dt r₁ r₃) *ᵥ v) 0 := by
  rw [sw_zero]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

theorem dt_right (r₁ r₃ v : Fin 2 → F) : dt r₃ (mt r₁ r₃ *ᵥ v) = (sw (dt r₁ r₃) *ᵥ v) 1 := by
  rw [sw_one]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

theorem dt_both (r₁ r₃ v' v : Fin 2 → F) : dt (mt r₁ r₃ *ᵥ v') (mt r₁ r₃ *ᵥ v) =
    v' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + v' 1 * (sw (dt r₁ r₃) *ᵥ v) 1 := by
  rw [sw_zero, sw_one]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

theorem chF_zero (c : Fˣ →* ℂˣ) (s : ℂ) : chF c s (0 : F) = 0 := by
  simp [chF]

theorem chF_unit (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) : chF c s (u : F) = ((c u : ℂˣ) : ℂ) * mp u s := by
  simp [chF]

theorem chF_mul (c : Fˣ →* ℂˣ) (s : ℂ) (a b : F) : chF c s (a * b) = chF c s a * chF c s b := by
  by_cases ha : a = 0
  · simp [chF, ha]
  by_cases hb : b = 0
  · simp [chF, hb]
  have h : a * b = ((Units.mk0 a ha * Units.mk0 b hb : Fˣ) : F) := rfl
  have ha' : a = ((Units.mk0 a ha : Fˣ) : F) := rfl
  have hb' : b = ((Units.mk0 b hb : Fˣ) : F) := rfl
  rw [h, chF_unit]
  conv_rhs => rw [ha', hb', chF_unit, chF_unit]
  rw [map_mul, Units.val_mul, GlobalTheory.CompanionTheory.WhittakerTrans.mp_mul']
  ring

theorem mp_neg_one (s : ℂ) : mp (-1 : Fˣ) s = 1 := by
  simp [mp, modulus_neg_eq]

theorem chF_neg (c : Fˣ →* ℂˣ) (s : ℂ) (x : F) : chF c s (-x) = ((c (-1) : ℂˣ) : ℂ) * chF c s x := by
  have h : -x = ((-1 : Fˣ) : F) * x := by simp
  rw [h, chF_mul, chF_unit, mp_neg_one, mul_one]

theorem mp_add (u : Fˣ) (a b : ℂ) : mp u (a + b) = mp u a * mp u b := by
  have h : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero u.ne_zero
  exact Complex.cpow_add _ _ h

theorem const_eq (ν c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) :
    ((modulus (u : F) : ℝ) : ℂ) * (chF (ν * c) (s - 1) (u : F) * chF (ν⁻¹ * c) (s - 1) (u : F) *
      chF c⁻¹ (-s) (u : F)) = chF c (s - 1) (u : F) := by
  simp only [chF_unit]
  have e : (((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ) = ((c u : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_inv_cancel_right]
  have e2 : ((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s) = 1 := by
    have h1 : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by simp [mp]
    rw [← h1, ← mp_add, ← mp_add]
    have : (1 + (s - 1) + -s : ℂ) = 0 := by ring
    rw [this]
    simp [mp]
  calc _ = ((((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ)) *
        (((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s)) * mp u (s - 1) := by ring
    _ = _ := by rw [e, e2, mul_one]

theorem sign_eq (ν c : Fˣ →* ℂˣ) :
    (((ν * c) (-1) : ℂˣ) : ℂ) * (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = 1 := by
  rw [← Units.val_mul]
  have h : (c (-1)) * (c (-1)) = 1 := by rw [← map_mul]; simp
  have : (ν * c) (-1) * (ν⁻¹ * c) (-1) = 1 := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, h]
  rw [this, Units.val_one]

theorem isUnit1_mul {μ ν : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ) (h₂ : IsUnit1 ν) : IsUnit1 (μ * ν) :=
  ⟨h₁.1.mul h₂.1, fun x => by simp [h₁.2, h₂.2]⟩

theorem isUnit1_inv {μ : Fˣ →* ℂˣ} (h : IsUnit1 μ) : IsUnit1 μ⁻¹ :=
  ⟨h.1.inv, fun x => by simp [h.2]⟩

theorem kr_left (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₃ v : Fin 2 → F) :
    Kr ν c⁻¹ (1 - s) r₁ (mt r₁ r₃ *ᵥ v) r₃ = chF c (s - 1) (dt r₁ r₃) *
      (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) := by
  have e1 : (ν⁻¹ * c)⁻¹ = ν * c⁻¹ := by rw [mul_inv, inv_inv]
  have e2 : (ν * c)⁻¹ = ν⁻¹ * c⁻¹ := mul_inv ν c
  have e3 : (1 - s - 1 : ℂ) = -s := by ring
  have e4 : (-(1 - s) : ℂ) = s - 1 := by ring
  simp only [Kr, dt_left, dt_right, e1, e2, e3, e4, inv_inv]
  ring

theorem kr_right (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₃ v : Fin 2 → F) :
    Kr ν c s r₁ (mt r₁ r₃ *ᵥ v) r₃ = (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) *
      (chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) * chF c⁻¹ (-s) (dt r₁ r₃)) *
      (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) := by
  simp only [Kr, dt_left, dt_right, sw_zero, sw_one, chF_mul, neg_mul, chF_neg]
  ring

variable [MeasurableSpace F] [BorelSpace F]

theorem integral_eq_mulVec (ψ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det ≠ 0)
    (f : (Fin 2 → F) → ℂ) :
    ∫ x, f x ∂m2 ψ = ((modulus M.det : ℝ) : ℂ) * ∫ x, f (M *ᵥ x) ∂m2 ψ := by
  set g := GeneralLinearGroup.mkOfDetNeZero M hM with hg
  have hgM : (g : Matrix (Fin 2) (Fin 2) F) = M := rfl
  have h := GlobalTheory.CompanionTheory.JSBound.setIntegral_image_mulVec (selfDualMeasure ψ) g Set.univ f
  have hs : (fun x => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) '' Set.univ = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y, trivial, ?_⟩
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hs, Measure.restrict_univ, hgM] at h
  have hu : Measures.modulus M.det = modulus M.det := by
    have := Measures.modulus_units (Units.mk0 M.det hM)
    rw [distribHaarChar_eq_modulus] at this
    exact this
  rw [hu] at h
  exact h

theorem sF_comp (ψ : AddChar F Circle) (Ψ : (Fin 2 → F) → ℂ) (r₁ r₃ v : Fin 2 → F)
    (hD : dt r₁ r₃ ≠ 0) :
    sF ψ Ψ (mt r₁ r₃ *ᵥ v) = ((modulus (dt r₁ r₃) : ℝ) : ℂ) *
      ∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ := by
  have hM : (mt r₁ r₃).det ≠ 0 := by rwa [mt_det]
  rw [sF, integral_eq_mulVec ψ _ hM, mt_det]
  simp only [dt_both]

theorem kernel_local_functional_equation : A7 → A8 := by
  intro hA F _ _ _ _ _ _ ψ hψ ν c hν hc Ψ hΨ s hs r₁ r₃
  by_cases hD : dt r₁ r₃ = 0
  · simp only [Kr, hD, chF_zero, mul_zero, integral_zero]
  have hM : (mt r₁ r₃).det ≠ 0 := by rwa [mt_det]
  have hS : (sw (dt r₁ r₃)).det ≠ 0 := by rw [sw_det]; exact mul_ne_zero hD hD
  have hf : SB (fun v => Ψ (mt r₁ r₃ *ᵥ v)) := by
    have hT : (mt r₁ r₃)ᵀ.det ≠ 0 := by rwa [det_transpose]
    have h := GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hΨ (GeneralLinearGroup.mkOfDetNeZero _ hT)
    have e : (fun v => Ψ (mt r₁ r₃ *ᵥ v)) = Ad3.SchwartzSpaceL2.rt Ψ (GeneralLinearGroup.mkOfDetNeZero _ hT) := by
      funext v
      show _ = Ψ (v ᵥ* (mt r₁ r₃)ᵀ)
      rw [vecMul_transpose]
    rw [e]
    exact h
  have h1 : IsUnit1 (ν⁻¹ * c) := isUnit1_mul (isUnit1_inv hν) hc
  have h2 : IsUnit1 (ν * c) := isUnit1_mul hν hc
  have h7 : ∫ r, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) *
        (chF (ν⁻¹ * c)⁻¹ (-s) (r 0) * chF (ν * c)⁻¹ (-s) (r 1)) ∂m2 ψ =
      gam ψ (ν⁻¹ * c) s * gam ψ (ν * c) s * ∫ r, Ψ (mt r₁ r₃ *ᵥ r) *
        (chF (ν⁻¹ * c) (s - 1) (r 0) * chF (ν * c) (s - 1) (r 1)) ∂m2 ψ :=
    hA F ψ hψ (ν⁻¹ * c) (ν * c) h1 h2 _ hf s hs
  have hSm : ((modulus (sw (dt r₁ r₃)).det : ℝ) : ℂ) =
      ((modulus (dt r₁ r₃) : ℝ) : ℂ) * ((modulus (dt r₁ r₃) : ℝ) : ℂ) := by
    rw [sw_det, modulus_mul]
    push_cast
    rfl
  rw [integral_eq_mulVec ψ _ hS, hSm] at h7
  rw [integral_eq_mulVec ψ _ hM, integral_eq_mulVec ψ (f := fun r => Ψ r * Kr ν c s r₁ r r₃) _ hM, mt_det]
  simp only [sF_comp ψ Ψ r₁ r₃ _ hD, kr_left]
  simp only [kr_right]
  have hK := const_eq ν c s (Units.mk0 _ hD)
  simp only [Units.val_mk0] at hK
  have hτ := sign_eq ν c
  generalize ((modulus (dt r₁ r₃) : ℝ) : ℂ) = A at h7 hK ⊢
  generalize chF c (s - 1) (dt r₁ r₃) = C at hK ⊢
  generalize chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) *
    chF c⁻¹ (-s) (dt r₁ r₃) = K at hK ⊢
  generalize (((ν * c) (-1) : ℂˣ) : ℂ) = τ at hτ ⊢
  generalize (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = σ at hτ ⊢
  have eL : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, A * J v * (C * P v) ∂m2 ψ = A * C * ∫ v, J v * P v ∂m2 ψ := by
    intro J P
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  have eR : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, J v * (σ * K * P v) ∂m2 ψ = σ * K * ∫ v, J v * P v ∂m2 ψ := by
    intro J P
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [eL (fun v => ∫ r', Ψ (mt r₁ r₃ *ᵥ r') *
      (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ)
      (fun v => chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)),
    eR (fun v => Ψ (mt r₁ r₃ *ᵥ v))
      (fun v => chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1))]
  generalize (∫ v, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') *
      (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ) *
      (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) ∂m2 ψ) = X at h7 ⊢
  generalize (∫ v, Ψ (mt r₁ r₃ *ᵥ v) *
      (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) ∂m2 ψ) = I at h7 ⊢
  generalize gam ψ (ν⁻¹ * c) s = g₁ at h7 ⊢
  generalize gam ψ (ν * c) s = g₂ at h7 ⊢
  linear_combination C * h7 - g₁ * g₂ * I * τ * σ * hK - g₁ * g₂ * I * C * hτ

end GlobalTheory.CompanionTheory.RSKernel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.DualForms

theorem exists_revOrdered_dual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k →
    ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL k), LFactors 𝔪 x →
      ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  intro k _ _ _ _ hA hD 𝔪 h x hx
  obtain ⟨Δ, ⟨-, hord⟩, hL⟩ := hx
  refine ⟨fun i => segDual (Δ i), fun i j hij hp => hord i j hij ((GlobalTheory.T.segment_dual_precedes_iff hA _ _).1 hp), fun i => ?_⟩
  rw [GlobalTheory.CompanionTheory.Zcore.dualCl_eq_of hA (x i)]
  exact (hD (Δ i) (x i).rep (hL i)).of_equiv (IrrGL.equivOf _ _ _)

end GlobalTheory.CompanionTheory.DualForms
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_rational_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRat := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat | exact GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat | (intros; apply GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat <;> assumption)
end


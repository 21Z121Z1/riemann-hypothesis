import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Norm

section Generic

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def twistEquivOf {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • σ g (φ.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (φ.isIntertwining' g) v)

def pairT (a : V) (y : W) : ∀ x : Bool, TwoT V W x
  | false => a
  | true => y

theorem bool_tprod_pairT (a : V) (y : W) :
    Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ (pairT a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] W) :=
  Exponents.boolTensorEquiv_tprod _

theorem tprod_pairT_smul (a : V) (c d : ℂ) (y : W) :
    PiTensorProduct.tprod ℂ (pairT (c • a) (d • y)) = (c * d) • PiTensorProduct.tprod ℂ (pairT a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V W)).injective
  rw [map_smul, bool_tprod_pairT, bool_tprod_pairT]
  exact TensorProduct.smul_tmul_smul c d a y

end Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

theorem det_levi' (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

theorem det_unip' (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [colMat]
    · simp [colMat, hi]
  · intro a b hab
    have hb : b ≠ Fin.last n := fun h => by
      subst h
      exact absurd (Fin.le_last a) (not_le.2 hab)
    have hne : a ≠ b := fun h => by
      subst h
      exact lt_irrefl _ hab
    simp [colMat, hb, Matrix.one_apply, hne]

theorem dpowM_levi' (n : ℕ) (s : ℝ) (g : GL (Fin n) k) : dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi']

theorem dpowM_of_mem' (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip', map_one]

theorem scalar_sum (i t : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * (absPow k 1 b * (absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) a *
        absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) b)) =
      absPow k ((t : ℂ) / 2) a * absPow k (-(i : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) a := by
  have e0 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    ring
  have e1 : absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k (-(i : ℂ) / 2) * (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg, ← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k ((t : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e0, e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((t : ℂ) / 2) a = T
  generalize absPow k (-(i : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (B * B * (T * (R * B⁻¹))) = (B⁻¹ * B) * (B * B⁻¹) * (T * R * A⁻¹) := by ac_rfl
    _ = T * R * A⁻¹ := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem twKer_twist_dpowM {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (τ : Representation ℂ (Mir k n) V) (s : ℝ) :
    twKer (twist τ (dpowM n s)) (MirUin k n) 1 = twKer τ (MirUin k n) 1 := by
  unfold twKer
  congr 1
  ext w
  refine exists_congr fun u => exists_congr fun v => ?_
  have hu : dpowM n s (u : Mir k n) = 1 := dpowM_of_mem' n s u.1 u.2
  rw [twist_apply, hu, Units.val_one, one_smul]

end Chars

section Main

variable {i t : ℕ} (τ : MRep k i) (σ : GRep k t)

abbrev eIT (i t : ℕ) : (Σ x, Two (Fin i) (Fin t) x) ≃ Fin (i + t) := two (stdSum (rfl : i + t = i + t))

abbrev sigT : Representation ℂ (Qp k i t) (PiTensorProduct ℂ (TwoT (psiN τ).V σ.V)) :=
  (twist (piTensor (twoRep (psiN τ).ρ σ.ρ)) (deltaHalf k (Two (Fin i) (Fin t)))).comp (leviProj k (eIT i t))

abbrev mkT (s : ℝ) : τ.V →ₗ[ℂ] Jacquet (mtw τ s).ρ (MirUin k i) := (twKer (mtw τ s).ρ (MirUin k i) 1).mkQ

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k i) 1).mkQ

def Lq (s : ℝ) : (Jacquet (mtw τ s).ρ (MirUin k i) ⊗[ℂ] σ.V) ≃ₗ[ℂ] PiTensorProduct ℂ (TwoT (psiN τ).V σ.V) :=
  (TensorProduct.congr (Submodule.quotEquivOfEq _ _ (twKer_twist_dpowM i τ.ρ s)) (LinearEquiv.refl ℂ σ.V)).trans
    (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).symm

theorem Lq_tmul (s : ℝ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s y ⊗ₜ[ℂ] w) = PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).injective
  rw [bool_tprod_pairT]
  refine (LinearEquiv.apply_symm_apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)) _).trans ?_
  rfl

theorem qRep_tmul (s₁ s₂ : ℝ) (q : Qp k i t) (y : τ.V) (w : σ.V) :
    qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) •
        (mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V)) := by
  have h : extTensor (psiMinus k (mtw τ s₁).ρ) (σ.tw s₂).ρ (qBlocks k i t q) (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V) := by
    refine (extTensor_tmul _ _ _ _ _).trans ?_
    show mkT τ s₁ (((dpowM i s₁ (levi k i (qBlocks k i t q).1) : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] _ = _
    rw [dpowM_levi']
    rfl
  exact congrArg (fun z => ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) • z) h

theorem Lq_tmul_smul (s : ℝ) (c d : ℂ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s (c • y) ⊗ₜ[ℂ] (d • w : σ.V)) = (c * d) • PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  rw [Lq_tmul, map_smul, tprod_pairT_smul]

theorem scalar_q (i t : ℕ) (q : Qp k i t) :
    ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) *
        (((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) *
          (((dpow i (((t : ℕ) : ℝ) / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) *
            ((dpow t (-((i + 1 : ℕ) : ℝ) / 2) (qBlocks k i t q).2 : ℂˣ) : ℂ))) =
      ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) *
        ((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) := by
  have hlev : leviProj k (eIT i t) q = leviTwo k (Fin i) (Fin t) (qBlocks k i t q) := by
    funext x
    cases x
    · rfl
    · rfl
  have hdet : GeneralLinearGroup.det (q : GL (Fin (i + t)) k) =
      GeneralLinearGroup.det (qBlocks k i t q).1 * GeneralLinearGroup.det (qBlocks k i t q).2 := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
    rfl
  rw [hlev, deltaHalf_two]
  simp only [← Units.val_mul]
  congr 1
  have := scalar_sum (k := k) i t (GeneralLinearGroup.det (qBlocks k i t q).1)
    (GeneralLinearGroup.det (qBlocks k i t q).2)
  simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
  exact this

def qEnd (s₁ s₂ : ℝ) (q : Qp k i t) :
    (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) →ₗ[ℂ] (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) :=
  qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q

theorem sigT_Lq (q : Qp k i t) (v : Jacquet (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (MirUin k i) ⊗[ℂ] σ.V) :
    sigT τ σ q (Lq τ σ (((t : ℕ) : ℝ) / 2) v) =
      ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) •
        Lq τ σ (((t : ℕ) : ℝ) / 2) (qEnd τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul x w =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h2 : (fun x => twoRep (psiN τ).ρ σ.ρ x (leviProj k (eIT i t) q x) (pairT (mkY τ y) w x)) =
        pairT (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y))
          ((1 : ℂ) • σ.ρ (qBlocks k i t q).2 w) := by
      funext x
      cases x
      · rfl
      · exact (one_smul ℂ _).symm
    have hL : sigT τ σ q (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) =
        ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
          (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) * 1) •
            PiTensorProduct.tprod ℂ (pairT (mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) (σ.ρ (qBlocks k i t q).2 w)) := by
      show ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
        piTensor (twoRep (psiN τ).ρ σ.ρ) (leviProj k (eIT i t) q) (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = _
      rw [piTensor_tprod]
      exact congrArg _ ((congrArg (PiTensorProduct.tprod ℂ) h2).trans (tprod_pairT_smul _ _ _ _))
    have hR := qRep_tmul τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q y w
    refine (congrArg (sigT τ σ q) (Lq_tmul τ σ _ y w)).trans (hL.trans ?_)
    refine Eq.trans ?_ (congrArg (fun z => ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) z) hR.symm)
    show _ = ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) (_ • _)
    rw [map_smul, Lq_tmul_smul, smul_smul, smul_smul, smul_smul, mul_one]
    congr 1
    rw [← scalar_q i t q]
    ring

end Main

theorem psiN_prodPGn_of_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  intro k _ _ _ _ i t τ σ _ _ hE
  obtain ⟨E⟩ := hE
  exact ⟨(twistEquivOf E (dpow (i + t) (-1 / 2))).trans
    (GlobalTheory.LocGL.smIndTwistEquiv le_rfl le_rfl (isSmoothChar_dpow _ _) (Lq τ σ _) fun q v => sigT_Lq τ σ q v)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Norm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctional
section
noncomputable section

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_par_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {p : G2 σ Y} {t : GL (Fin n) (AE F E)}
    (hp : IsPar p t) (x : G2 σ Y) :
    a (p * x) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * a x := by
  obtain ⟨p', t', hp', k, hk, rfl⟩ := hK.iwa x
  rw [← mul_assoc, hK.val _ _ (hp.mul hp') k hk, hK.val _ _ hp' k hk, map_mul, map_mul]
  push_cast
  rfl

theorem hgt_nonneg {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) (x : G2 σ Y) : 0 ≤ a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hK.iwa x
  rw [hK.val _ _ hp k hk]
  exact NNReal.coe_nonneg _

theorem absE_ne_zero (u : (AF F ⊗[F] E)ˣ) : ((absE F E u : ℝ) : ℂ) ≠ 0 := by
  have h : absE F E u ≠ 0 := ((absE F E).toHomUnits u).ne_zero
  exact_mod_cast h

theorem law_flat {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsHgt K a) {χ : Chr F E} {s₁ : ℂ} {f : G2 σ Y → ℂ}
    (hf : IsSec K χ s₁ f) (s : ℂ) : Law χ (s + n / 2) (flat a f s₁ s) := by
  intro p t x hp
  have hd := absE_ne_zero (F := F) (E := E) (Matrix.GeneralLinearGroup.det t)
  have h0 : (0 : ℝ) ≤ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := NNReal.coe_nonneg _
  have hc : ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s + (n : ℂ) / 2) =
      ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s - s₁) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + (n : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hd]
    congr 1
    ring
  simp only [flat]
  rw [hgt_par_mul hK hp x, hf.law p t x hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h0 (hgt_nonneg hK x), hc]
  ring

end GlobalTheory.CompanionTheory.EisRat

namespace GlobalTheory.CompanionTheory.EisRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem eis_left_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  intro F E _ _ _ _ _ σ B n Y r s _ _ _ b K a _ _ hK χ s₁ f hf hχ t Ê hs s' hs' γ hγ x
  exact (law_flat hK hf s').eis_rat hχ (hs s' hs') hγ x

end GlobalTheory.CompanionTheory.EisRat

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactorStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedded_small_neighbourhood_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
    ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
      ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent | exact GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuOfDifferentiableAt
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.RmHol.GelCoef

variable {n : ℕ}

theorem Eu_of_differentiableAt {f : Mat n → ℂ} {z : Mat n} (hf : DifferentiableAt ℂ f z) (a b : Fin n) :
    Eu true a b f z = fderiv ℂ f z (z * Matrix.single a b 1) ∧ Eu false a b f z = 0 := by
  have hR : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  have hI : z * Matrix.single a b Complex.I = Complex.I • (z * Matrix.single a b (1 : ℂ)) := by
    rw [← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, if_true, hR,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination (-(1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, hR, Bool.false_eq_true, if_false,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination ((1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII

theorem Eu_congr_germ {f h : Mat n → ℂ} {g : Mat n} (e : f =ᶠ[𝓝 g] h) (s : Bool) (a b : Fin n) :
    Eu s a b f g = Eu s a b h g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, e.fderiv_eq]

end GlobalTheory.CompanionTheory.RmHol.GelCoef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Frob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def evalMap {π : Representation ℂ (GL (Fin (a + b)) k) V} {σ : Representation ℂ (GL (Fin a) k) W}
    {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    V →ₗ[ℂ] TensorProduct ℂ W W' :=
  φ.toLinearMap ∘ₗ (twKer π (unipRad k (two (stdSum (rfl : a + b = a + b)))) 1).mkQ

theorem evalMap_law {π : Representation ℂ (GL (Fin (a + b)) k) V}
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ))
    (q : parab k (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    evalMap φ (π q w) =
      (deltaHalf k (Two (Fin a) (Fin b)) (leviProj k _ q) : ℂ) •
        extTensor σ ρ ((leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q)) (evalMap φ w) := by
  set xy := (leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q) with hxy
  have hL : leviProj k (two (stdSum (rfl : a + b = a + b))) q = leviTwo k _ _ xy :=
    (MulEquiv.apply_symm_apply _ _).symm
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k (two (stdSum (rfl : a + b = a + b))) q
  rw [hL] at hpu ⊢
  have hpu' : (q : GL (Fin (a + b)) k) =
      leviEmb k (two (stdSum (rfl : a + b = a + b))) (leviTwo k _ _ xy) * u := hpu
  have hmk : (Submodule.Quotient.mk (π u w) :
      Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) = Submodule.Quotient.mk w := by
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨u, hu⟩, w, ?_⟩
    simp
  have key : ∀ (M : Levi k (Two (Fin a) (Fin b))) (x : V),
      (Submodule.Quotient.mk (π (leviEmb k (two (stdSum (rfl : a + b = a + b))) M) x) :
        Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) =
        (deltaHalf k (Two (Fin a) (Fin b)) M : ℂ) •
          jac (two (stdSum (rfl : a + b = a + b))) π M (Submodule.Quotient.mk x) := by
    intro M x
    rw [jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hint := Representation.IntertwiningMap.isIntertwining _ _ φ xy
    (Submodule.Quotient.mk w : Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b)))))
  simp only [evalMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
  change _ • φ (jac₂ (stdSum (rfl : a + b = a + b)) π xy (Submodule.Quotient.mk w)) = _
  rw [hint]
  rfl

def frobMap {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    π.IntertwiningMap (prod₂ σ ρ) :=
  { toFun := fun v => ⟨⟨fun x => evalMap φ (π x v), fun q x => by
        show evalMap φ (π (q * x) v) = _
        rw [map_mul, Module.End.mul_apply]
        exact evalMap_law φ q (π x v)⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
        have hh' : π h v = v := hh
        refine Subtype.ext (funext fun x => ?_)
        show evalMap φ (π (x * h) v) = evalMap φ (π x v)
        rw [map_mul, Module.End.mul_apply, hh'])⟩
    map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (v + w)) = evalMap φ (π x v) + evalMap φ (π x w)
      rw [map_add, map_add]))
    map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (c • v)) = c • evalMap φ (π x v)
      rw [map_smul, map_smul]))
    isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (π h v)) = evalMap φ (π (x * h) v)
      rw [map_mul, Module.End.mul_apply])) }

theorem frobMap_one {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) (v : V) :
    (frobMap hs φ v).1.1 1 = φ (Submodule.Quotient.mk v) := by
  show evalMap φ (π 1 v) = _
  rw [map_one]
  rfl

theorem exists_injective_of_jac₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (σ : Representation ℂ (GL (Fin a) k) W)
    (ρ : Representation ℂ (GL (Fin b) k) W'), IsSmooth π → π.IsIrreducible →
    ∀ φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 →
      ∃ ψ : π.IntertwiningMap (prod₂ σ ρ), Function.Injective ψ := by
  intro k _ _ _ _ a b V W W' _ _ _ _ _ _ π σ ρ hs hπ φ hφ
  refine ⟨frobMap hs φ, ?_⟩
  haveI := hπ
  refine (Representation.IsIrreducible.injective_or_eq_zero (frobMap hs φ)).resolve_right fun h0 => hφ ?_
  ext v
  show φ (Submodule.Quotient.mk v) = 0
  rw [← frobMap_one hs φ v, h0]
  rfl

end GlobalTheory.CompanionTheory.Frob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamilyStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_lie_family : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | exact GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | (intros; apply GlobalTheory.CompanionTheory.RealCountG.dualFam_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicatorStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_ball_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E), ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | exact GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr | (intros; apply GlobalTheory.CompanionTheory.MirLevi.Bump.exists_bump_restr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_induced_section_supported_open : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G), IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) → ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧ ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HBBump.exists_bump | exact GlobalTheory.CompanionTheory.HBBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.HBBump.exists_bump <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProjStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_lift_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | exact GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift <;> assumption)
end


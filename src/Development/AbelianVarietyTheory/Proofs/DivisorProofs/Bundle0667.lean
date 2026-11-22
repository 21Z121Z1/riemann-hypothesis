import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.AxesPull

variable {R : Type} [CommRing R]

theorem isAffine_unit : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))

theorem pO1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pO1 g (pO1 f a) = pO1 (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).1 a)

theorem pF_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pF g (pF f a) = pF (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.1 a)

theorem pH1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : deRhamH1Pullback g (deRhamH1Pullback f a) = deRhamH1Pullback (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.2.1 a)

theorem pO1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pO1 (u ≫ f) a = 0 := by
  rw [← pO1_comp]
  haveI := ((GlobalTheory.AbCoh.Vanish.main.1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom isAffine_unit).1)
  rw [Subsingleton.elim (pO1 f a) 0, map_zero]

theorem pF_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pF (u ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem pH1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    deRhamH1Pullback (u ≫ f) a = 0 := by
  rw [← pH1_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).2
  rw [Subsingleton.elim (deRhamH1Pullback f a) 0, map_zero]

theorem main : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  intro R _ A _
  have hid := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A)
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · simp only [pO1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pO1_unit, hid.1, and_self]
  · simp only [pF_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pF_unit, hid.2.2.1, and_self]
  · simp only [pH1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pH1_unit, hid.2.2.2.1, and_self]

end GlobalTheory.AbCoh.AxesPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspidalFactorAtBlockLeviPiTensor
section
noncomputable section

namespace GlobalTheory.HcIrr.Factor

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr Representation

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem tprod_update_injective (v : ∀ i, M i) (hv : ∀ i, v i ≠ 0) (i : ι) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap v i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hw : ∀ j, Function.update v i x j ≠ 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hx0
    · rw [Function.update_of_ne hj]; exact hv j
  have hφ : ∀ j, ∃ φ : Module.Dual ℂ (M j), φ (Function.update v i x j) ≠ 0 := by
    intro j
    by_contra hc
    push_neg at hc
    exact hw j ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  choose φ hφ using hφ
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) hx
  rw [MultilinearMap.toLinearMap_apply, PiTensorProduct.lift.tprod, map_zero,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
  exact (Finset.prod_ne_zero_iff.2 fun j _ => hφ j) h1

end Tensor

section Blocks

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def blockIdx (b : Fin r → Fin s) (c : Fin s) : {i // b i = c} ≃ Block (natBlocks b) (c : ℕ) :=
  Equiv.subtypeEquivRight fun i => by simp [natBlocks, Fin.val_inj]

def blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) :
    {i // b i = c} ≃ Fin d :=
  (blockIdx b c).trans (monoEquivOfFin _ h).toEquiv.symm

theorem monoEquivOfFin_blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ}
    (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (x : {i // b i = c}) :
    ((monoEquivOfFin (Block (natBlocks b) (c : ℕ)) h (blockNum b c h x) : Block (natBlocks b) (c : ℕ)) : Fin r) = x.1 := by
  simp [blockNum, blockIdx]

theorem blockEmb_eq (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d)
    (g : GL (Fin d) K) :
    blockEmb (natBlocks b) (c : ℕ) h g = blockExt b c ((glEquiv K (blockNum b c h)).symm g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : b i = c ∧ b j = c
  · have h1 := blockEmb_in (natBlocks b) (c : ℕ) h g (blockNum b c h ⟨i, hij.1⟩) (blockNum b c h ⟨j, hij.2⟩)
    rw [monoEquivOfFin_blockNum, monoEquivOfFin_blockNum] at h1
    have h2 := blockExt_in b c ((glEquiv K (blockNum b c h)).symm g) ⟨i, hij.1⟩ ⟨j, hij.2⟩
    rw [h1, h2]
    rfl
  · have hn : ¬ (natBlocks b i = (c : ℕ) ∧ natBlocks b j = (c : ℕ)) := by
      simpa [natBlocks, Fin.val_inj] using hij
    rw [blockEmb_out (natBlocks b) (c : ℕ) h g i j hn, blockExt_out b c _ i j hij]

end Blocks

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem blockRes_leviTensor (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (g : GL (Fin d) K) :
    blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h g = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c
        ((lam c).ρ ((glEquiv K (blockNum b c h)).symm g))) := by
  show leviTensor b lam (blockEmb (natBlocks b) (c : ℕ) h g) = _
  rw [blockEmb_eq, leviTensor_blockExt]

theorem map_update_tprod {s : ℕ} {M : Fin s → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (c : Fin s) (A : M c →ₗ[ℂ] M c) (v : ∀ i, M i) (x : M c) :
    PiTensorProduct.map (Function.update (fun c' => (LinearMap.id : M c' →ₗ[ℂ] M c')) c A)
      (PiTensorProduct.tprod ℂ (Function.update v c x)) = PiTensorProduct.tprod ℂ (Function.update v c (A x)) := by
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext c'
  by_cases hc : c' = c
  · subst hc; simp
  · simp [Function.update_of_ne hc]

theorem factor_iso : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → ∀ (c : Fin s) (d : ℕ)
    (h : Fintype.card (GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.Block (natBlocks b) (c : ℕ)) = d) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin d) K) W), GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.HasFactor (natBlocks b) (leviTensor b lam) (c : ℕ) h ρ →
    ∃ (e : {i // b i = c} ≃ Fin d) (L : W ≃ₗ[ℂ] (lam c : Type)),
      ∀ g v, L (ρ g v) = (lam c).ρ ((glEquiv K e).symm g) (L v) := by
  intro K _ _ _ r s b lam hsimp c d h W _ _ ρ hF
  refine ⟨blockNum b c h, ?_⟩
  set e := blockNum b c h
  let ρ' : Representation ℂ (GL (Fin d) K) (lam c) := (transp e (lam c)).ρ
  have hirr : ρ'.IsIrreducible := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (Formalism.L2.PT.simple_transp e (hsimp c))
  have hnt : ∀ c', Nontrivial (lam c') := fun c' =>
    PI.GreenLabelSurjWork.nontrivial_of_simple _ (hsimp c')
  choose v hv using fun c' => exists_ne (0 : (lam c' : Type))
  let f : IntertwiningMap ρ' (blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h) :=
    ((PiTensorProduct.tprod ℂ).toLinearMap v c).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => by
      rw [blockRes_leviTensor, MultilinearMap.toLinearMap_apply, MultilinearMap.toLinearMap_apply,
        map_update_tprod]
      rfl)
  have hinj : Function.Injective (IntertwiningMap.equivLinearMapAsModule ρ' _ f) :=
    tprod_update_injective v hv c
  have hiso := hF.2.of_injective _ hinj
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule :=
    (irreducible_iff_isSimpleModule_asModule ρ').1 hirr
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) (⊤ : Submodule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule) :=
    IsSimpleModule.congr (Submodule.topEquiv)
  let E : ρ.asModule ≃ₗ[MonoidAlgebra ℂ (GL (Fin d) K)] ρ'.asModule := ((hiso ⊤).some.symm.trans Submodule.topEquiv)
  let F : IntertwiningMap ρ ρ' := (IntertwiningMap.equivLinearMapAsModule ρ ρ').symm E.toLinearMap
  refine ⟨LinearEquiv.ofBijective F.toLinearMap E.bijective, fun g x => ?_⟩
  exact IntertwiningMap.isIntertwining ρ ρ' F g x

end Main

end GlobalTheory.HcIrr.Factor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.ValLin

lemma eval_map_hom {σ Q Q' : Type} [CommRing Q] [CommRing Q'] (R : Q →+* Q') (x : σ → Q)
    (P : MvPolynomial σ Q) :
    R (MvPolynomial.eval x P) = MvPolynomial.eval (fun i => R (x i)) (MvPolynomial.map R P) := by
  rw [MvPolynomial.eval_map]
  show R (MvPolynomial.eval₂ (RingHom.id Q) x P) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]

theorem hasVal_add_smul_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B) (f g : MvPowerSeries σ Q) (q r : Q), HasVal p z f q → (HasVal p z g r → HasVal p z (f + g) (q + r)) ∧ (∀ c : Q, HasVal p z (c • f) (c * q)) ∧ ∀ (B' Q' : Type) [CommRing B'] [CommRing Q'] [Algebra B' Q'] (ρ : B →+* B') (R : Q →+* Q'), (∀ b, R (algebraMap B Q b) = algebraMap B' Q' (ρ b)) → HasVal p (fun i => ρ (z i)) (map R f) (R q) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z f g q r hf
  refine ⟨?_, ?_, ?_⟩
  · intro hg m
    obtain ⟨N₁, h₁⟩ := hf m
    obtain ⟨N₂, h₂⟩ := hg m
    refine ⟨max N₁ N₂, fun N' hN => ?_⟩
    obtain ⟨b₁, hb₁⟩ := h₁ N' (le_trans (le_max_left _ _) hN)
    obtain ⟨b₂, hb₂⟩ := h₂ N' (le_trans (le_max_right _ _) hN)
    refine ⟨b₁ + b₂, ?_⟩
    rw [map_add, map_add, mul_add, map_add, ← hb₁, ← hb₂]
    ring
  · intro c m
    obtain ⟨k, b₀, hk⟩ := hF.denom c
    obtain ⟨N, h⟩ := hf (m + k)
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨b₀ * b, ?_⟩
    rw [map_smul, MvPolynomial.smul_eval]
    have e : c * q - c * MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') f)
        = c * algebraMap B Q (p ^ (m + k) * b) := by rw [← hb]; ring
    rw [e]
    simp only [map_mul, map_pow, map_natCast] at hk ⊢
    rw [← hk]
    ring
  · intro B' Q' _ _ _ ρ R hR m
    obtain ⟨N, h⟩ := hf m
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨ρ b, ?_⟩
    rw [trunc'_map]
    have := congrArg R hb
    rw [map_sub, eval_map_hom, hR] at this
    simp only [hR] at this
    rw [this]
    simp

end GlobalTheory.QLog.ValLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatio
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem eval_coe_polynomial_of_isEval {p : ℕ} {B : Type} [CommRing B] {σ : Type}
    (z : σ → B) (E : MvPowerSeries σ B →ₐ[B] B) (hE : IsEval p z E) (P : MvPolynomial σ B) :
    E (P : MvPowerSeries σ B) = MvPolynomial.eval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom B) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE.1 i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem hasVal_map_of_isEval : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  intro p _ B O Q _ _ _ _ θ _ σ _ _ z _ E hE s m
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun N' hN' => ?_⟩
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N'
  have hdiv : (p : B) ^ m ∣ E (s - (trunc' B n s : MvPowerSeries σ B)) := by
    apply hN
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        classical
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N'
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  rw [map_sub, eval_coe_polynomial_of_isEval z E hE] at hb
  have key : algebraMap B Q (MvPolynomial.eval z (trunc' B n s)) =
      MvPolynomial.eval₂ (algebraMap B Q) (fun i => algebraMap B Q (z i)) (trunc' B n s) := by
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    exact MvPolynomial.eval₂_comp_left _ _ _ _
  rw [trunc'_map, MvPolynomial.eval_map, ← key, ← map_sub, hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.HasValCong

open scoped Nat

section Ring

variable {B : Type} [CommRing B]

theorem pow_eq_pow_factorization_mul (p : ℕ) (hp : p.Prime) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ x ∈ J, ∃ y ∈ J, x ^ n = (p : B) ^ ((n)!.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmn : m < p * m := by
        have := hp.two_le
        nlinarith
      obtain ⟨y, hy, hxy⟩ := hJ x hx
      obtain ⟨y', hy', hyy⟩ := ih m hmn hm y hy
      refine ⟨y', hy', ?_⟩
      rw [Nat.factorization_factorial_mul hp, pow_mul, hxy, mul_pow, hyy, pow_add]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨x, hx, by simp⟩
      obtain ⟨y, hy, hxy⟩ := ih k (by omega) hk x hx
      refine ⟨x * y, J.mul_mem_left x hy, ?_⟩
      have h0 : (k + 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero k),
        Finsupp.coe_add, Pi.add_apply, h0, zero_add, pow_succ, hxy]
      ring

theorem pow_eq_factorial_mul (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (n : ℕ) (hn : 0 < n) (x : B) (hx : x ∈ J) :
    ∃ y ∈ J, x ^ n = ((n ! : ℕ) : B) * y := by
  obtain ⟨y, hy, hxy⟩ := pow_eq_pow_factorization_mul p hp J hJ n hn x hx
  obtain ⟨u, hu'⟩ := hu (n ! / p ^ (n !).factorization p)
    (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  refine ⟨(↑u⁻¹ : B) * y, J.mul_mem_left _ hy, ?_⟩
  have hfac : ((n ! : ℕ) : B) =
      (p : B) ^ (n !).factorization p * ((n ! / p ^ (n !).factorization p : ℕ) : B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hxy, hfac, ← hu', mul_assoc, ← mul_assoc (u : B), Units.mul_inv, one_mul]

theorem sum_eq_mul_mem {ι : Type} (s : Finset ι) (c : B) (J : Ideal B) (f : ι → B)
    (h : ∀ i ∈ s, ∃ y ∈ J, f i = c * y) : ∃ y ∈ J, ∑ i ∈ s, f i = c * y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', mul_add]⟩

theorem add_pow_sub_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (a j : B) (hj : j ∈ J) (n : ℕ) :
    ∃ y ∈ J, (a + j) ^ n - a ^ n = (n : B) * y := by
  rcases n with _ | n
  · exact ⟨0, J.zero_mem, by simp⟩
  rw [add_comm a j, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
  rw [add_sub_cancel_right]
  apply sum_eq_mul_mem
  intro k _
  obtain ⟨y, hy, hjy⟩ := pow_eq_factorial_mul p hp hu J hJ (k + 1) (Nat.succ_pos k) j hj
  refine ⟨((n.descFactorial k : ℕ) : B) * a ^ (n + 1 - (k + 1)) * y, J.mul_mem_left _ hy, ?_⟩
  have h : (n + 1).choose (k + 1) * (k + 1)! = (n + 1) * n.descFactorial k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ]
  have h' : (((n + 1).choose (k + 1) : ℕ) : B) * (((k + 1)! : ℕ) : B) =
      ((n + 1 : ℕ) : B) * ((n.descFactorial k : ℕ) : B) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, h]
  rw [hjy]
  linear_combination (a ^ (n + 1 - (k + 1)) * y) * h'

end Ring

section Monomial

variable {B : Type} [CommRing B] {σ : Type}

theorem prod_pow_sub_prod_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ → ℕ) (s : Finset σ) :
    ∃ b : σ → B, (∀ i, b i ∈ J) ∧
      ∏ i ∈ s, z i ^ α i - ∏ i ∈ s, z' i ^ α i = ∑ i ∈ s, (α i : B) * b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b, hb, e⟩ := ih
    obtain ⟨y, hy, ey⟩ := add_pow_sub_pow p hp hu J hJ (z' i) (z i - z' i) (hz i) (α i)
    have hzz : z' i + (z i - z' i) = z i := by ring
    rw [hzz] at ey
    refine ⟨Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k), ?_, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact J.mul_mem_right _ hy
      · rw [Function.update_of_ne hk]
        exact J.mul_mem_left _ (hb k)
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Function.update_self]
      have h1 : ∑ k ∈ s, (α k : B) *
          Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k) k =
          z' i ^ α i * ∑ k ∈ s, (α k : B) * b k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
        ring
      rw [h1]
      linear_combination (∏ k ∈ s, z k ^ α k) * ey + z' i ^ α i * e

theorem sum_eq_map_mem {Q : Type} [CommRing Q] [Algebra B Q] {ι : Type} (s : Finset ι)
    (J : Ideal B) (f : ι → Q) (h : ∀ i ∈ s, ∃ b ∈ J, f i = algebraMap B Q b) :
    ∃ b ∈ J, ∑ i ∈ s, f i = algebraMap B Q b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', map_add]⟩

variable [Fintype σ] {Q : Type} [CommRing Q] [Algebra B Q]

theorem monomial_val_sub (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ →₀ ℕ) (a : Q) (ha : ∀ i, ∃ c : B, (α i : Q) * a = algebraMap B Q c) :
    ∃ b ∈ J, a * (∏ i, algebraMap B Q (z i) ^ α i) - a * ∏ i, algebraMap B Q (z' i) ^ α i =
      algebraMap B Q b := by
  choose c hc using ha
  obtain ⟨b, hb, e⟩ := prod_pow_sub_prod_pow p hp hu J hJ z z' hz α Finset.univ
  refine ⟨∑ i, b i * c i, J.sum_mem (fun i _ => J.mul_mem_right _ (hb i)), ?_⟩
  have e' := congrArg (algebraMap B Q) e
  simp only [map_sub, map_prod, map_pow, map_sum, map_mul, map_natCast] at e'
  rw [← mul_sub, e', Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hc i]
  ring

theorem eval_sub_eval (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (P : MvPolynomial σ Q)
    (hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) * P.coeff α = algebraMap B Q c) :
    ∃ b ∈ J, MvPolynomial.eval (fun i => algebraMap B Q (z i)) P -
      MvPolynomial.eval (fun i => algebraMap B Q (z' i)) P = algebraMap B Q b := by
  rw [P.as_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply sum_eq_map_mem
  intro v _
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact monomial_val_sub p hp hu J hJ z z' hz v (P.coeff v) (hP v)

end Monomial

theorem hasVal_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q),
    (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' →
    ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  intro p hpf B O Q _ _ _ _ θ hF σ _ _ z _ J hJ z' f q q' hzz hD hv hv' m
  have hp : p.Prime := hpf.out
  obtain ⟨N1, h1⟩ := hv m
  obtain ⟨N2, h2⟩ := hv' m
  obtain ⟨b1, e1⟩ := h1 (max N1 N2) (le_max_left _ _)
  obtain ⟨b2, e2⟩ := h2 (max N1 N2) (le_max_right _ _)
  have hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) *
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max N1 N2) f).coeff α =
        algebraMap B Q c := by
    intro α i
    rw [coeff_trunc']
    split_ifs
    · obtain ⟨c, -, hc⟩ := hD α i
      exact ⟨c, hc⟩
    · exact ⟨0, by simp⟩
  obtain ⟨b, hb, e⟩ := eval_sub_eval p hp hF.unit_coprime J hJ z z' hzz _ hP
  refine ⟨b, hb, b1 - b2, ?_⟩
  simp only [map_add, map_mul, map_sub, map_pow, map_natCast] at e1 e2 ⊢
  linear_combination e1 - e2 + e

end GlobalTheory.HasValCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimirStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_iso_of_equal_casimir : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  first | exact @GlobalTheory.LowGen.gen_iso_of_lowest_type | exact GlobalTheory.LowGen.gen_iso_of_lowest_type | (intros; apply GlobalTheory.LowGen.gen_iso_of_lowest_type <;> assumption)
end


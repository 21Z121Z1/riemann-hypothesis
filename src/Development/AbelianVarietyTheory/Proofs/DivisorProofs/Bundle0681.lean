import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveOfAxesVanishing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.PrimLift

theorem pO1_comp {R : Type} [CommRing R] {Y A B : Over (Sp R)} (f : Y ⟶ A) (g : A ⟶ B) (a : HO1 B.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) := by
  unfold pO1
  exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R B.left A.left B.hom A.hom (RingHom.id R) g.left (ovw g) R Y.left Y.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (by simp)
    (fun _ => rfl)).1 a).symm

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A).1 a

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := by
    show IsAffine (Sp R)
    infer_instance
  exact (GlobalTheory.AbCoh.Vanish.main.1 R _ _ this).1.elim a 0

theorem primO1_of_axesO1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  intro R _ A _ hax x
  have key : ∀ j : A ⟶ A ⊗ A, pO1 (j ≫ μ[A]) x - pO1 (j ≫ fst A A) x - pO1 (j ≫ snd A A) x =
      pO1 j (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) := by
    intro j
    rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp]
  have hη : pO1 (toUnit A ≫ η[A]) x = 0 := by
    rw [pO1_comp, pO1_unit_eq_zero (pO1 η[A] x), map_zero]
  have h := hax (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x)
    (by
      rw [← key, lift_comp_one_right, lift_fst, lift_snd, pO1_id, hη]
      simp)
    (by
      rw [← key, lift_comp_one_left, lift_fst, lift_snd, pO1_id, hη]
      simp)
  rw [sub_sub, sub_eq_zero] at h
  exact h

end GlobalTheory.AbCoh.PrimLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem projective_dvd_of_forall_dual_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M),
      (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  intro O M _ _ _ _ a b h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O M)
  have hc : ∀ i : M, a ∣ s b i := fun i => h ((Finsupp.lapply i).comp s)
  choose c hc using hc
  refine ⟨∑ i ∈ (s b).support, c i • i, ?_⟩
  have hb : Finsupp.linearCombination O id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [Finset.smul_sum]
  conv_lhs => rw [← hb]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  intro R k _ _ σ hσ X s X₀ s₀ ψ w
  let e : R ≃+* k := RingEquiv.ofBijective σ hσ
  let τ : k →+* R := e.symm.toRingHom
  have hστ : ∀ r, σ (τ r) = r := fun r => e.apply_symm_apply r
  have hτσ : ∀ r, τ (σ r) = r := fun r => e.symm_apply_apply r
  have c1 : spMap τ ≫ spMap σ = 𝟙 (Sp R) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    have : τ.comp σ = RingHom.id R := RingHom.ext hτσ
    rw [this]; simp
  have c2 : spMap σ ≫ spMap τ = 𝟙 (Sp k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    rw [this]; simp
  let l : X ⟶ X₀ := w.lift (𝟙 X) (s ≫ spMap τ) (by rw [Category.id_comp, Category.assoc, c1, Category.comp_id])
  have hl1 : l ≫ ψ = 𝟙 X := w.lift_fst _ _ _
  have hl2 : l ≫ s₀ = s ≫ spMap τ := w.lift_snd _ _ _
  have hl3 : ψ ≫ l = 𝟙 X₀ := by
    apply w.hom_ext
    · rw [Category.assoc, hl1, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hl2, ← Category.assoc, w.w, Category.assoc, c2, Category.comp_id, Category.id_comp]
  obtain ⟨hcomp, -, hid⟩ := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  intro b
  refine ⟨pullHO1 hl2 b, ?_⟩
  have := (hcomp k R X₀ X s₀ s τ l hl2 k X₀ s₀ σ ψ w.w (RingHom.id k) (𝟙 (Over.mk s₀) : Over.mk s₀ ⟶ Over.mk s₀).left
    (ovw (𝟙 (Over.mk s₀))) (by simp [hl3]) (fun r => (hστ r).symm)).1 b
  rw [this]
  exact (hid k (Over.mk s₀)).1 b

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverBaseChangeComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pull_over_baseChange_comm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A Y : Over (Sp R)) (A' Y' : Over (Sp R')) (f : Y ⟶ A) (f' : Y' ⟶ A') (φ : A'.left ⟶ A.left) (ψ : Y'.left ⟶ Y.left) (hA : φ ≫ A.hom = A'.hom ≫ spMap σ) (hY : ψ ≫ Y.hom = Y'.hom ≫ spMap σ), f'.left ≫ φ = ψ ≫ f.left → (∀ x, pullHO1 hY (pO1 f x) = pO1 f' (pullHO1 hA x)) ∧ ∀ x, pullHO2 hY (structureSheafH2Pullback f x) = structureSheafH2Pullback f' (pullHO2 hA x) := by
  intro R R' _ _ σ A Y A' Y' f f' φ ψ hA hY hcomm
  have hχ : (ψ ≫ f.left) ≫ A.hom = Y'.hom ≫ spMap σ := by
    rw [Category.assoc, Over.w f, hY]
  have H := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · have e1 := (H R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) R'
      Y'.left Y'.hom σ ψ hY σ (ψ ≫ f.left) hχ rfl (fun _ ↦ rfl)).1 x
    have e2 := (H R R' A.left A'.left A.hom A'.hom σ φ hA R' Y'.left Y'.hom
      (RingHom.id R') f'.left (ovw f') σ (ψ ≫ f.left) hχ hcomm.symm (fun _ ↦ rfl)).1 x
    simp only [pO1]
    rw [e1, e2]
  · have e1 := (H R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) R'
      Y'.left Y'.hom σ ψ hY σ (ψ ≫ f.left) hχ rfl (fun _ ↦ rfl)).2.1 x
    have e2 := (H R R' A.left A'.left A.hom A'.hom σ φ hA R' Y'.left Y'.hom
      (RingHom.id R') f'.left (ovw f') σ (ψ ≫ f.left) hχ hcomm.symm (fun _ ↦ rfl)).2.1 x
    simp only [structureSheafH2Pullback]
    rw [e1, e2]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverse
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.BasisTrans

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_add {g h : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) (hh : In (⊤ : Ideal B) h) :
    In (⊤ : Ideal B) (g + h) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  obtain ⟨b, -, hb⟩ := hh α
  exact ⟨a + b, trivial, by rw [map_add, ha, hb, map_add]⟩

theorem in_smul (c : B) {g : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) :
    In (⊤ : Ideal B) (algebraMap B Q c • g) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩

theorem in_sum {κ : Type} (s : Finset κ) (g : κ → MvPowerSeries σ Q)
    (hg : ∀ j ∈ s, In (⊤ : Ideal B) (g j)) : In (⊤ : Ideal B) (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem comb_one {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvPowerSeries σ Q) (i : ι) :
    comb ((1 : Matrix ι ι B) i) e = e i := by
  simp [comb, Matrix.one_apply]

theorem comb_mul {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι → MvPowerSeries σ Q)
    (f : κ → MvPowerSeries σ Q) (P : ι → κ → B) (P' : κ → ι → B) (i : ι) :
    e i - comb ((Matrix.of P * Matrix.of P') i) e =
      (e i - comb (P i) f) + ∑ j, algebraMap B Q (P i j) • (f j - comb (P' j) e) := by
  simp only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib,
    Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]
  abel

theorem mul_eq_one {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q)
    (he : IsBasis μ e) (P : ι → κ → B) (P' : κ → ι → B)
    (h1 : ∀ i, In (⊤ : Ideal B) (e i - comb (P i) f))
    (h2 : ∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) :
    Matrix.of P * Matrix.of P' = 1 := by
  funext i
  obtain ⟨b, -, hb⟩ := he.2 (e i) (he.1 i)
  have hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e) := by
    rw [comb_mul e f P P' i]
    exact in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))
  have hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e) := by
    rw [comb_one, sub_self]; exact in_zero
  exact (hb _ hA).trans (hb _ hB).symm

theorem trans_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  intro B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2
  exact ⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩

end GlobalTheory.BasisTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageStepIndependent
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DevStep

theorem in_sub {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f - g) := fun α => by
  obtain ⟨x, hx, hfx⟩ := hf α
  obtain ⟨y, hy, hgy⟩ := hg α
  exact ⟨x - y, N.sub_mem hx hy, by rw [map_sub, map_sub, hfx, hgy]⟩

theorem in_subst {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Finite σ] {N : Ideal B}
    {a : σ → MvPowerSeries τ B} (ha : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ Q}
    (hf : In N f) : In N (subst (fun i => map (algebraMap B Q) (a i)) f) := by
  choose g hgN hg using hf
  let G : MvPowerSeries σ B := fun α => g α
  have hfG : f = map (algebraMap B Q) G := by ext α; rw [coeff_map, hg]; rfl
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  intro α
  refine ⟨coeff α (subst a G), ?_, ?_⟩
  · rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs G α)]
    exact Ideal.sum_mem _ fun d _ => by rw [smul_eq_mul]; exact N.mul_mem_right _ (hgN d)
  · rw [hfG, ← map_subst hs, coeff_map]

theorem coeffsInIdeal_formalGroupLawCoboundaryOne {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} {N : Ideal B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In N f) : In N (cob1 (up Q μ) f) := by
  unfold cob1 inL inR
  have hl : (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
      fun i => map (algebraMap B Q) (X (Sum.inl i)) := by funext i; rw [map_X]
  have hr : (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
      fun i => map (algebraMap B Q) (X (Sum.inr i)) := by funext i; rw [map_X]
  rw [hl, hr]
  exact in_sub (in_sub (in_subst hμ hf) (in_subst (fun _ => constantCoeff_X _) hf))
    (in_subst (fun _ => constantCoeff_X _) hf)

theorem map_formalGroupLawCoboundaryOne_eq {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
    [Algebra O C] {d : ℕ} (θ : B →+* O) (Θ : Q →+* C)
    (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ) f) = cob1 (up C fun i => map θ (μ i)) (map Θ f) := by
  have h1 : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, hμ i]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst h1, map_subst h2, map_subst h3]
  congr 3
  · funext i; ext α; simp [up, coeff_map, hΘ]
  · funext i; rw [map_X]
  · funext i; rw [map_X]

def coeffIdeal {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) : Submodule B Q :=
  Submodule.map (Algebra.linearMap B Q) N

theorem mem_coeffIdeal {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B} {q : Q} :
    q ∈ coeffIdeal N ↔ ∃ b ∈ N, q = algebraMap B Q b := by
  simp only [coeffIdeal, Submodule.mem_map, Algebra.linearMap_apply]
  exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩

theorem mul_mem_coeffIdeal {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {r : B} (hr : r ∈ N) {q : Q} (hq : q ∈ coeffIdeal (⊤ : Ideal B)) :
    algebraMap B Q r * q ∈ coeffIdeal N := by
  obtain ⟨y, -, rfl⟩ := mem_coeffIdeal.1 hq
  exact mem_coeffIdeal.2 ⟨r * y, N.mul_mem_right _ hr, (map_mul _ _ _).symm⟩

theorem mul_mem_coeffIdeal' {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    (r : B) {q : Q} (hq : q ∈ coeffIdeal N) : algebraMap B Q r * q ∈ coeffIdeal N := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ r hq

end GlobalTheory.DevStep

open GlobalTheory.DevStep in

theorem GlobalTheory.step_independent : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → ∀ N' N : Ideal B, IsStep p θ N' N → ∀ (b : ι → B) (s : MvPowerSeries (Fin d) Q), (∀ i, b i ∈ N) → In N s → QL μ N' (comb b e - s) → (∀ i, b i ∈ N') ∧ In N' s := by
  intro p _ B O Q _ _ _ _ θ hF d μ hμ C _ _ hC Θ hΘ ι _ e he hB N' N hstep b s hb hs hQL
  obtain ⟨n, a, ⟨c, hc⟩, hN, hn⟩ := hstep
  have hμ0 := hμ.const
  have hup0 : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by simp [up, hμ0 i]
  have hdec : ∀ x ∈ N, ∃ m ∈ N', ∃ t : B, x = m + t * n := by
    intro x hx
    rw [hN, Submodule.mem_sup] at hx
    obtain ⟨m, hm, z, hz, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨m, hm, t, rfl⟩
  choose n' hn' β hβ using fun i => hdec (b i) (hb i)
  have hcomb : ∀ (w : ι → B) α, coeff α (comb w e) = ∑ i, algebraMap B Q (w i) * coeff α (e i) := by
    intro w α; simp only [comb, map_sum, coeff_smul, smul_eq_mul]
  have he0 : ∀ i, coeff 0 (e i) = 0 := fun i => by
    rw [coeff_zero_eq_constantCoeff_apply]; exact (he i).1
  have hs0 : coeff 0 s = 0 := by
    have h := hQL.1
    rw [← coeff_zero_eq_constantCoeff_apply, map_sub, hcomb] at h
    simpa [he0] using h
  have hsdec : ∀ α, ∃ m ∈ N', ∃ t : B, coeff α s = algebraMap B Q (m + t * n) ∧ (α = 0 → t = 0) := by
    intro α
    by_cases h0 : α = 0
    · exact ⟨0, N'.zero_mem, 0, by rw [h0, hs0]; simp, fun _ => rfl⟩
    · obtain ⟨x, hx, hxs⟩ := hs α
      obtain ⟨m, hm, t, rfl⟩ := hdec x hx
      exact ⟨m, hm, t, hxs, fun h => absurd h h0⟩
  choose m hm t hts ht0 using hsdec
  let S' : MvPowerSeries (Fin d) Q := map (algebraMap B Q) (fun α => m α)
  let S₁ : MvPowerSeries (Fin d) Q := map (algebraMap B Q) (fun α => t α)
  have cS' : ∀ α, coeff α S' = algebraMap B Q (m α) := fun α => by simp only [S', coeff_map]; rfl
  have cS₁ : ∀ α, coeff α S₁ = algebraMap B Q (t α) := fun α => by simp only [S₁, coeff_map]; rfl
  have hS' : In N' S' := fun α => ⟨m α, hm α, cS' α⟩
  have hS₁ : In (⊤ : Ideal B) S₁ := fun α => ⟨t α, trivial, cS₁ α⟩
  obtain ⟨E, hE⟩ : ∃ E, E = comb β e - S₁ := ⟨_, rfl⟩
  have cE : ∀ α, coeff α E = ∑ i, algebraMap B Q (β i) * coeff α (e i) - algebraMap B Q (t α) := by
    intro α; rw [hE, map_sub, hcomb, cS₁]
  have hkey : comb b e - s = (comb n' e - S') + algebraMap B Q n • E := by
    ext α
    rw [map_sub, map_add, map_sub, coeff_smul, cE, hcomb, hcomb, hts, cS']
    simp only [hβ, map_add, map_mul, add_mul, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
    ring_nf

  let L : MvPowerSeries (Fin d) Q →ₗ[Q] MvPowerSeries (Fin d ⊕ Fin d) Q :=
    { toFun := cob1 (up Q μ), map_add' := formalCoboundary_add hup0, map_smul' := formalCoboundary_smul hup0 }
  have hL : ∀ f, L f = cob1 (up Q μ) f := fun _ => rfl
  have hcobcomb : ∀ (w : ι → B) α, coeff α (cob1 (up Q μ) (comb w e)) =
      ∑ i, algebraMap B Q (w i) * coeff α (cob1 (up Q μ) (e i)) := by
    intro w α; rw [← hL]; unfold comb; rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coeff_smul]; rfl
  have hdiv : ∀ q : Q, q ∈ coeffIdeal (⊤ : Ideal B) → algebraMap B Q n * q ∈ coeffIdeal N' →
      ∃ y, q = algebraMap B Q y ∧ a ∣ θ y := by
    intro q hq hnq
    obtain ⟨y, -, rfl⟩ := mem_coeffIdeal.1 hq
    obtain ⟨x, hx, hxy⟩ := mem_coeffIdeal.1 hnq
    refine ⟨y, rfl, (hn y).1 ?_⟩
    rw [← map_mul] at hxy
    rw [mul_comm, hF.inj hxy]; exact hx
  have hl : ∀ (f : MvPowerSeries (Fin d) Q) i, lin f i = coeff (Finsupp.single i 1) f := fun _ _ => rfl
  have hlinE : ∀ i, ∃ y, lin E i = algebraMap B Q y ∧ a ∣ θ y := by
    intro i
    have hej : ∀ j, coeff (Finsupp.single i 1) (e j) ∈ coeffIdeal (⊤ : Ideal B) := fun j => by
      obtain ⟨y, hy, h⟩ := (he j).2.1 i
      exact mem_coeffIdeal.2 ⟨y, hy, by rw [← hl]; exact h⟩
    apply hdiv
    · rw [hl, cE]
      exact Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal' _ (hej j))
        (mem_coeffIdeal.2 ⟨_, trivial, rfl⟩)
    · have h1 := congrArg (coeff (Finsupp.single i 1)) hkey
      rw [map_add, coeff_smul] at h1
      have h2 : algebraMap B Q n * coeff (Finsupp.single i 1) E =
          lin (comb b e - s) i - coeff (Finsupp.single i 1) (comb n' e - S') := by
        rw [hl, h1]; ring
      rw [hl, h2, map_sub]
      refine Submodule.sub_mem _ ?_ (Submodule.sub_mem _ ?_ ?_)
      · obtain ⟨y, hy, h⟩ := hQL.2.1 i; exact mem_coeffIdeal.2 ⟨y, hy, h⟩
      · rw [hcomb]; exact Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal (hn' j) (hej j)
      · rw [cS']; exact mem_coeffIdeal.2 ⟨_, hm _, rfl⟩
  have hcobE : ∀ α, ∃ y, coeff α (cob1 (up Q μ) E) = algebraMap B Q y ∧ a ∣ θ y := by
    intro α
    have hej : ∀ j, coeff α (cob1 (up Q μ) (e j)) ∈ coeffIdeal (⊤ : Ideal B) := fun j => by
      obtain ⟨y, hy, h⟩ := (he j).2.2 α
      exact mem_coeffIdeal.2 ⟨y, hy, h⟩
    apply hdiv
    · rw [hE, ← hL, map_sub, hL, hL, map_sub, hcobcomb]
      refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal' _ (hej j)) ?_
      obtain ⟨y, hy, h⟩ := coeffsInIdeal_formalGroupLawCoboundaryOne hμ0 hS₁ α
      exact mem_coeffIdeal.2 ⟨y, hy, h⟩
    · have h1 : cob1 (up Q μ) (comb b e - s) =
          cob1 (up Q μ) (comb n' e - S') + algebraMap B Q n • cob1 (up Q μ) E := by
        rw [← hL, hkey, map_add, map_smul]; rfl
      have h2 : algebraMap B Q n * coeff α (cob1 (up Q μ) E) =
          coeff α (cob1 (up Q μ) (comb b e - s)) - coeff α (cob1 (up Q μ) (comb n' e - S')) := by
        rw [h1, map_add, coeff_smul]; ring
      rw [h2]
      refine Submodule.sub_mem _ ?_ ?_
      · obtain ⟨y, hy, h⟩ := hQL.2.2 α; exact mem_coeffIdeal.2 ⟨y, hy, h⟩
      · rw [← hL, map_sub, hL, hL, map_sub, hcobcomb]
        refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal (hn' j) (hej j)) ?_
        obtain ⟨y, hy, h⟩ := coeffsInIdeal_formalGroupLawCoboundaryOne hμ0 hS' α
        exact mem_coeffIdeal.2 ⟨y, hy, h⟩
  have hupC : ∀ i, constantCoeff (up C (fun i => map θ (μ i)) i) = 0 := fun i => by
    simp [up, hμ0 i]
  obtain ⟨u, hu⟩ : ∃ u : C, u * algebraMap O C a = 1 := by
    refine ⟨algebraMap O C c * ↑hC.unit_p.unit⁻¹, ?_⟩
    rw [mul_right_comm, ← map_mul, mul_comm c a, ← hc, map_natCast]
    exact hC.unit_p.mul_val_inv
  have hT : ∀ q : Q, (∃ y, q = algebraMap B Q y ∧ a ∣ θ y) →
      ∃ z, u * Θ q = algebraMap O C z ∧ Θ q = algebraMap O C (a * z) := by
    rintro q ⟨y, rfl, z, hz⟩
    refine ⟨z, ?_, by rw [hΘ, hz]⟩
    rw [hΘ, hz, map_mul, ← mul_assoc, hu, one_mul]
  have hnat := map_formalGroupLawCoboundaryOne_eq θ Θ hΘ hμ0 E
  have hE0 : coeff 0 E = 0 := by
    rw [cE, ht0 0 rfl]; simp [he0]
  obtain ⟨F, hFd⟩ : ∃ F, F = u • map Θ E := ⟨_, rfl⟩
  have hQLF : QL (fun i => map θ (μ i)) ⊤ F := by
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [hFd, ← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_map, hE0, map_zero, mul_zero]
    · obtain ⟨z, hz, -⟩ := hT _ (hlinE i)
      refine ⟨z, trivial, ?_⟩
      show coeff (Finsupp.single i 1) F = _
      rw [hFd, coeff_smul, coeff_map, ← hl]; exact hz
    · obtain ⟨z, hz, -⟩ := hT _ (hcobE α)
      refine ⟨z, trivial, ?_⟩
      rw [hFd, formalCoboundary_smul hupC, coeff_smul, ← hnat, coeff_map]; exact hz
  have hQLΘ : QL (fun i => map θ (μ i)) ⊤ (map Θ E) := by
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hE0, map_zero]
    · obtain ⟨z, -, hz⟩ := hT _ (hlinE i)
      exact ⟨a * z, trivial, by
        show coeff (Finsupp.single i 1) (map Θ E) = _
        rw [coeff_map, ← hl]; exact hz⟩
    · obtain ⟨z, -, hz⟩ := hT _ (hcobE α)
      exact ⟨a * z, trivial, by rw [← hnat, coeff_map]; exact hz⟩
  obtain ⟨γ, hγ, -⟩ := hB.2 F hQLF
  have hcΘ : ∀ (w : ι → O) α, coeff α (comb w (fun i => map Θ (e i))) =
      ∑ i, algebraMap O C (w i) * Θ (coeff α (e i)) := by
    intro w α; simp only [comb, map_sum, coeff_smul, smul_eq_mul, coeff_map]
  have hc1 : ∀ α, coeff α (map Θ E - comb (fun i => θ (β i)) (fun i => map Θ (e i))) =
      -algebraMap O C (θ (t α)) := by
    intro α
    rw [map_sub, coeff_map, cE, hcΘ, map_sub, map_sum]
    simp only [map_mul, hΘ]; ring
  have h2 : map Θ E - comb (fun i => a * γ i) (fun i => map Θ (e i)) =
      algebraMap O C a • (F - comb γ (fun i => map Θ (e i))) := by
    rw [smul_sub, hFd, smul_smul, mul_comm, hu, one_smul, comb, comb, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, map_mul]
  have hin2 : In (⊤ : Ideal O) (map Θ E - comb (fun i => a * γ i) (fun i => map Θ (e i))) := by
    rw [h2]; intro α
    obtain ⟨w, -, hw⟩ := hγ α
    exact ⟨a * w, trivial, by rw [coeff_smul, hw, map_mul]⟩
  have hin1 : In (⊤ : Ideal O) (map Θ E - comb (fun i => θ (β i)) (fun i => map Θ (e i))) :=
    fun α => ⟨-θ (t α), trivial, by rw [hc1, map_neg]⟩
  have heq := (hB.2 _ hQLΘ).unique hin1 hin2
  have hbN' : ∀ i, b i ∈ N' := fun i => by
    rw [hβ i]; exact N'.add_mem (hn' i) ((hn (β i)).2 ⟨γ i, congrFun heq i⟩)
  refine ⟨hbN', fun α => ⟨m α + t α * n, N'.add_mem (hm α) ((hn (t α)).2 ?_), hts α⟩⟩
  obtain ⟨w, -, hw⟩ := hγ α
  have h3 := congrArg (coeff α) h2
  rw [coeff_smul, hw, ← heq, hc1, ← map_mul] at h3
  have h4 : θ (t α) = -(a * w) := by
    apply hC.inj; rw [map_neg, ← h3, neg_neg]
  exact ⟨-w, by rw [h4]; ring⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.res0_bijective_of_affine_intersections_of_iSup_eq_top : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)), ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  first | exact @GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective | exact GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective | (intros; apply GlobalTheory.CechPoset.restrictCompatibleFamilyToIntersections_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHomStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  first | exact @GlobalTheory.spec_local_hom_ext_of_injective | exact GlobalTheory.spec_local_hom_ext_of_injective | (intros; apply GlobalTheory.spec_local_hom_ext_of_injective <;> assumption)
end


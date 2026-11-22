import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehler
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameTransitionPsiMatrix
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isMat_twist : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e e' t t' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), Function.Surjective ψ → (∀ w, t (fun i => ψ (w i)) = fun j => phiInv p O (e w j)) → (∀ w, t' (fun i => ψ (w i)) = fun j => phiInv p O (e' w j)) → IsMat e e' X Y → IsMat t t' (X.map (phiInv p O)) (Y.map ψ) := by
  intro p _ O _ _ _ Λ _ _ N h ψ e e' t t' X Y hψ ht ht' hXY v
  obtain ⟨w, rfl⟩ : ∃ w : Fin N → RL p O Λ, (fun i => ψ (w i)) = v :=
    ⟨fun i => (hψ (v i)).choose, funext fun i => (hψ (v i)).choose_spec⟩
  have hY : Y.map ψ *ᵥ (fun i => ψ (w i)) = fun i => ψ ((Y *ᵥ w) i) := by
    funext i
    exact (RingHom.map_mulVec ψ Y w i).symm
  rw [hY, ht, ht', ← hXY w]
  funext j
  exact (RingHom.map_mulVec (phiInv p O) X (e w) j).symm

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafCechDegreeTwoExactForall
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.Et.CovChar.Trip

noncomputable section
namespace GlobalTheory.Et.CovChar.Trip.CechLevels
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev L (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin (n+1) => Y) (fun _ => f)

def e0 : L f 0 ≅ Y where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f (fun _ => 𝟙 Y) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j; simp [WidePullback.lift_π]
    · simp [WidePullback.lift_base, WidePullback.π_arrow]
  inv_hom_id := by simp [WidePullback.lift_π]

def e1 : L f 1 ≅ pullback f f where
  hom := pullback.lift (WidePullback.π _ 0) (WidePullback.π _ 1) (by simp)
  inv := WidePullback.lift (pullback.fst f f ≫ f) ![pullback.fst f f, pullback.snd f f]
    (by intro j; fin_cases j <;> simp [pullback.condition])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_snd]; simp
    · simp only [Category.assoc, WidePullback.lift_base]; erw [pullback.lift_fst_assoc]; simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc]; erw [pullback.lift_fst]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_snd]; simp [WidePullback.lift_π]

def e2 : L f 2 ≅ Tr f where
  hom := pullback.lift (pullback.lift (WidePullback.π _ 0) (WidePullback.π _ 1) (by simp))
    (pullback.lift (WidePullback.π _ 1) (WidePullback.π _ 2) (by simp)) (by
      erw [pullback.lift_snd, pullback.lift_fst])
  inv := WidePullback.lift (pullback.fst _ _ ≫ pullback.fst f f ≫ f)
    ![pullback.fst _ _ ≫ pullback.fst f f, pullback.fst _ _ ≫ pullback.snd f f, pullback.snd _ _ ≫ pullback.snd f f]
    (by
      intro j; fin_cases j
      · simp
      · show (pullback.fst _ _ ≫ pullback.snd f f) ≫ f = _
        rw [Category.assoc, ← pullback.condition (f := f) (g := f)]
      · show (pullback.snd _ _ ≫ pullback.snd f f) ≫ f = _
        rw [Category.assoc, ← pullback.condition (f := f) (g := f),
          ← pullback.condition_assoc (f := pullback.snd f f) (g := pullback.fst f f),
          ← pullback.condition (f := f) (g := f)])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst_assoc, pullback.lift_fst]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst_assoc, pullback.lift_snd]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_snd_assoc, pullback.lift_snd]; simp
    · simp only [Category.assoc, WidePullback.lift_base]; erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]; simp
  inv_hom_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext
    · simp only [Category.assoc]; erw [pullback.lift_fst_assoc, pullback.lift_fst]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_fst_assoc, pullback.lift_snd]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_snd_assoc, pullback.lift_fst]; simp [WidePullback.lift_π]; exact pullback.condition
    · simp only [Category.assoc]; erw [pullback.lift_snd_assoc, pullback.lift_snd]; simp [WidePullback.lift_π]

theorem face_π {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.π (fun _ => f) j = WidePullback.π (fun _ => f) (i.succAbove j) := by
  simp only [SimplicialObject.δ, Arrow.cechNerve_map]
  erw [WidePullback.lift_π]
  rfl

theorem cech_nerve_face_one_zero : (Arrow.mk f).cechNerve.δ (0 : Fin 2) ≫ (e0 f).hom = (e1 f).hom ≫ pullback.snd f f := by
  erw [pullback.lift_snd]; exact face_π f 0 0
theorem cech_nerve_face_one_one : (Arrow.mk f).cechNerve.δ (1 : Fin 2) ≫ (e0 f).hom = (e1 f).hom ≫ pullback.fst f f := by
  erw [pullback.lift_fst]; exact face_π f 1 0

theorem cech_nerve_face_two_zero : (Arrow.mk f).cechNerve.δ (0 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc]; erw [pullback.lift_fst, pullback.lift_snd_assoc, pullback.lift_fst]; exact face_π f 0 0
  · simp only [Category.assoc]; erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]; exact face_π f 0 1
theorem cech_nerve_face_two_one : (Arrow.mk f).cechNerve.δ (1 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pr13 f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pr13_fst]; erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]; exact face_π f 1 0
  · simp only [Category.assoc, pr13_snd]; erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]; exact face_π f 1 1
theorem cech_nerve_face_two_two : (Arrow.mk f).cechNerve.δ (2 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pullback.fst _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc]; erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]; exact face_π f 2 0
  · simp only [Category.assoc]; erw [pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd]; exact face_π f 2 1

end GlobalTheory.Et.CovChar.Trip.CechLevels

namespace GlobalTheory.Et.CovChar.Trip
open CechLevels in

theorem free_sheaf_cech_degree_two_exact (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X) :
    (ShortComplex.mk (d2 f R) (d1 f R) (d2_comp f R)).Exact := by
  have h := freeOn_cechNerve_exactAt (R := R) f 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  refine ShortComplex.isoMk ((freeOn R).mapIso (e2 f)) ((freeOn R).mapIso (e1 f)) ((freeOn R).mapIso (e0 f)) ?_ ?_
  · have hd : ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 2 1 =
        (freeOn R).map ((Arrow.mk f).cechNerve.δ (0 : Fin 3)) - (freeOn R).map ((Arrow.mk f).cechNerve.δ (1 : Fin 3))
          + (freeOn R).map ((Arrow.mk f).cechNerve.δ (2 : Fin 3)) := by
      erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [Fin.sum_univ_three, SimplicialObject.δ, sub_eq_add_neg]
    change _ = ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 2 1 ≫ _
    rw [hd]
    simp only [d2, Functor.mapIso_hom, Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
      Preadditive.sub_comp, ← Functor.map_comp, cech_nerve_face_two_zero, cech_nerve_face_two_one, cech_nerve_face_two_two]
    simp only [Functor.map_comp]
    erw [Preadditive.comp_add, Preadditive.comp_sub]
    rfl
  · have hd : ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 1 0 =
        (freeOn R).map ((Arrow.mk f).cechNerve.δ (0 : Fin 2)) - (freeOn R).map ((Arrow.mk f).cechNerve.δ (1 : Fin 2)) := by
      erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [Fin.sum_univ_two, SimplicialObject.δ, sub_eq_add_neg]
    change _ = ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 1 0 ≫ _
    rw [hd]
    simp only [d1, Functor.mapIso_hom, Preadditive.comp_sub,
      Preadditive.sub_comp, ← Functor.map_comp, cech_nerve_face_one_zero, cech_nerve_face_one_one]
    simp only [Functor.map_comp]
    erw [Preadditive.comp_sub]
    rfl
end GlobalTheory.Et.CovChar.Trip

example : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X), (ShortComplex.mk (d2 f R) (d1 f R) (d2_comp f R)).Exact :=
  fun R _ _ _ f => GlobalTheory.Et.CovChar.Trip.free_sheaf_cech_degree_two_exact R f
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehlerStatement
section
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusDerivation_factors_through_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  first | exact @GlobalTheory.DI.frobDeriv_factors_kaehler | exact GlobalTheory.DI.frobDeriv_factors_kaehler | (intros; apply GlobalTheory.DI.frobDeriv_factors_kaehler <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PsiPhi

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_phiInv' (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p _

theorem phiInv_frobenius' (a : Ainf p O) : phiInv p O (WittVector.frobenius a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_apply_frobenius (PreTilt O p) p _

theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

theorem frobenius_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  have key : (_root_.frobenius (PreTilt O p) p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

def phiInvAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { phiInv p O with commutes' := fun c => phiInv_ofPadic c }

def frobAlg : Ainf p O →ₐ[ℤ_[p]] Ainf p O :=
  { (WittVector.frobenius : Ainf p O →+* Ainf p O) with commutes' := fun c => frobenius_ofPadic c }

end GlobalTheory.DetInv.PsiPhi

namespace GlobalTheory.DetInv

open PsiPhi in

theorem psi_phi_tensor : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ],
    (∀ c : ℤ_[p], phiInv p O (ofPadic p O c) = ofPadic p O c) ∧ Function.Bijective (phiInv p O) ∧
    ∃ ψ φ : RL p O Λ →+* RL p O Λ, IsPsi ψ ∧
      (∀ (a : Ainf p O) (l : Λ), φ (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l) ∧
      (∀ r, φ (ψ r) = r) ∧ ∀ r, ψ (φ r) = r := by
  intro p _ O _ _ _ Λ _ _
  refine ⟨fun c => phiInv_ofPadic c,
    Function.bijective_iff_has_inverse.mpr ⟨WittVector.frobenius, frobenius_phiInv', phiInv_frobenius'⟩,
    (Algebra.TensorProduct.map (phiInvAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom,
    (Algebra.TensorProduct.map (frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom,
    fun a l => rfl, fun a l => rfl, ?_, ?_⟩
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      change (frobAlg (phiInvAlg a)) ⊗ₜ l = a ⊗ₜ l
      exact congrArg (· ⊗ₜ[ℤ_[p]] l) (frobenius_phiInv' a)
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  · intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      change (phiInvAlg (frobAlg a)) ⊗ₜ l = a ⊗ₜ l
      exact congrArg (· ⊗ₜ[ℤ_[p]] l) (phiInv_frobenius' a)
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSum
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma summable_weierstrassP_terms (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 := by
  have h := (L.hasSum_weierstrassPExcept 0 z).summable
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0)
    ?_)).congr ?_
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [hl]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma latticeEquivProd_symm_coe (L : PeriodPair) (p : ℤ × ℤ) :
    (L.latticeEquivProd.symm p : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ := by
  simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    PeriodPair.latticeBasis]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

lemma _root_.GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * τ + m) ^ 2)
      (EisensteinSeries.G2 τ + (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP z) := by
  set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef
  have hω₁ : L.ω₁ = τ := rfl
  have hω₂ : L.ω₂ = 1 := rfl
  set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2
    with hfdef
  have hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z) :=
    (summable_weierstrassP_terms L z).hasSum
  have hf : HasSum f (L.weierstrassP z) := by
    have := (L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg
    convert this using 1
    funext p
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, latticeEquivProd_symm_coe, hω₁, hω₂,
      hfdef, mul_one]
  have hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z) :=
    hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum
  have hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ) := by
    rw [← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]
    exact (_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum
  have hsum := hG.add hrow
  have hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2)
      (EisensteinSeries.G2 τ + L.weierstrassP z) := by
    convert hsum using 1
    funext n
    have ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2 := by
      have := EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl
      convert this using 1
      funext m
      simp [zpow_ofNat]
    have hba : Summable fun m : ℤ => f (n, m) := hf.summable.prod_factor n
    have he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2 := by
      unfold EisensteinSeries.e2Summand
      congr 1
      funext m
      simp [EisensteinSeries.eisSummand]
    rw [he]
    have := (ha.hasSum.add hba.hasSum).tsum_eq
    simp only [hfdef, add_sub_cancel] at this
    exact this
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hF
  convert hneg using 1
  funext n
  simp only [Function.comp_apply, Equiv.neg_apply]
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring_nf

end GlobalTheory.WpFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisComparisonMapInjectiveOfFlatStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisComparisonMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  first | (exact @GlobalTheory.GoodEtale.galMap_injective_of_flat) | (exact GlobalTheory.GoodEtale.galMap_injective_of_flat) | (intros; apply GlobalTheory.GoodEtale.galMap_injective_of_flat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentSemilinearBijectiveStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisDescent_sum_basis_smul_ker_bijective : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (V : Type) [AddCommGroup V] [Module F' V] [Module F V] [IsScalarTower F F' V] (T : Module.End F V), (∀ (c : F') (v : V), T (c • v) = s c • T v) → T ^ Module.finrank F F' = 1 → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι F F'), Function.Bijective (fun v : ι → LinearMap.ker (T - 1) => ∑ i, b i • (v i : V)) := by
  first | (exact @GlobalTheory.Shin.galoisDescent_semilinear_bijective) | (exact GlobalTheory.Shin.galoisDescent_semilinear_bijective) | (intros; apply GlobalTheory.Shin.galoisDescent_semilinear_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisElementDvdOfFormallyUnramifiedStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisElement_dvd_of_formallyUnramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (exact GlobalTheory.GoodEtale.galElt_dvd_of_unramified) | (intros; apply GlobalTheory.GoodEtale.galElt_dvd_of_unramified  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTwistedNormGL_basic_properties : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  first | (exact @GlobalTheory.Shin.NrmBasic.main) | (exact GlobalTheory.Shin.NrmBasic.main) | (intros; apply GlobalTheory.Shin.NrmBasic.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLDiagonalBlocksStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (γ : GL (Fin n) F) (δ : GL (Fin n) F'), InPar a γ → InPar a δ → nrm s δ = incl F F' n γ → nrm s (tlG a δ) = incl F F' a (tlG a γ) ∧ nrm s (brG a b δ) = incl F F' b (brG a b γ) := by
  first | (exact @GlobalTheory.ShinBlock.nrm_blocks) | (exact GlobalTheory.ShinBlock.nrm_blocks) | (intros; apply GlobalTheory.ShinBlock.nrm_blocks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModuleStatement
section
open GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussSum_nondegenerate_finite_hermitian_module : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  first | exact @GlobalTheory.HermitianGauss.gauss_hermitian | exact GlobalTheory.HermitianGauss.gauss_hermitian | (intros; apply GlobalTheory.HermitianGauss.gauss_hermitian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

def genFibMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E] [Algebra T O]
    (ψ : E →ₐ[T] O) : GenFib T E →+* GenFib T O :=
  IsLocalization.map (M := Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (T := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (GenFib T O) ψ.toRingHom (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ψ.commutes t).symm⟩)

theorem genFibMap_algebraMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) :
    genFibMap ψ (algebraMap E (GenFib T E) e) = algebraMap O (GenFib T O) (ψ e) := by
  simp [genFibMap, IsLocalization.map_eq]

theorem genFib_ringHom_ext {T E C : Type} [CommRing T] [CommRing E] [CommRing C] [Algebra T E]
    {f g : GenFib T E →+* C} (h : ∀ e : E, f (algebraMap E _ e) = g (algebraMap E _ e)) : f = g :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (RingHom.ext h)

end GlobalTheory.LocAcyc
end
end


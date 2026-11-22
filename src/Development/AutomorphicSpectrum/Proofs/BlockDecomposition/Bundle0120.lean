import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUnique
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensityStatement
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_binary_gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
  tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} →
  Continuous (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  HasCompactSupport (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  (∀ s : Ainf F, ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ s)) = ENNReal.ofReal (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))) ∧
  ENNReal.ofReal (∫ s, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | exact GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | (intros; apply GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_full_subcategory_iso : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p, Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | exact GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H | (intros; apply GlobalTheory.CompanionTheory.CechFull.cechH_fullSubcategory_H <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDOneZero
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] (A : D ⥤ CommAlgCat.{0} R)

abbrev Co (k : ℕ) : Type 1 := CH.Cn (CH.modF A) k

def one0 : Co A 0 := fun s => (1 : A.obj (s.obj (Fin.last 0)))

def aL : ∀ {p : ℕ}, (Fin (p + 1) → Co A 1) → Co A p := fun {p} =>
  Nat.rec (motive := fun p => (Fin (p + 1) → Co A 1) → Co A p) (fun _ => one0 A)
    (fun p ih β => (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (ih fun i => β i.succ)) p

theorem aL_succ {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    aL A β = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (aL A fun i => β i.succ) := rfl

theorem cupList_left {k : ℕ} (l : Fin (k + 1) → Co A 1) :
    cupListC A l = (CH.mulP A).cupC (by omega : 1 + k = k + 1) (l 0) (cupListC A fun i => l i.succ) := by
  induction k with
  | zero =>
    have e1 : cupListC A l = (CH.mulP A).cupC (Nat.zero_add 1) (one0 A) (l (Fin.last 0)) := rfl
    have e2 : (cupListC A fun i : Fin 0 => l i.succ) = one0 A := rfl
    rw [e1, e2]
    exact (Auxff.unit_left A _).trans (Auxff.unit_right A _).symm
  | succ k ih =>
    have e1 : cupListC A l = (CH.mulP A).cupC (by omega : k + 1 + 1 = k + 1 + 1)
      (cupListC A fun i : Fin (k + 1) => l i.castSucc) (l (Fin.last (k + 1))) := rfl
    have e2 : (cupListC A fun i : Fin (k + 1) => l i.succ) = (CH.mulP A).cupC (by omega : k + 1 = k + 1)
      (cupListC A fun i : Fin k => l i.castSucc.succ) (l (Fin.last k).succ) := rfl
    rw [e1, e2, ih (fun i => l i.castSucc)]
    exact Auxff.assoc A _ _ (by omega : k + 1 = k + 1) (by omega) _ _ _

theorem aL_eq {p : ℕ} (β : Fin (p + 1) → Co A 1) : aL A β = cupListC A fun k : Fin p => β k.castSucc - β k.succ := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [aL_succ, ih, cupList_left]
    rfl

theorem cech_d_one_zero : CH.d (CH.modF A) 0 (one0 A) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem aL_closed {p : ℕ} (β : Fin (p + 1) → Co A 1) (hβ : ∀ i j, CH.d _ 1 (β i) = CH.d _ 1 (β j)) :
    CH.d _ p (aL A β) = 0 := by
  induction p with
  | zero => exact cech_d_one_zero A
  | succ p ih =>
    rw [aL_succ, P.leibniz, ih _ fun i j => hβ _ _, map_sub, hβ 0 1, sub_self]
    simp

theorem pow_closed (z : Co A 2) (hz : CH.d _ 2 z = 0) (k : ℕ) : CH.d _ (2 * k) (cupPowC A z k) = 0 := by
  induction k with
  | zero => exact cech_d_one_zero A
  | succ k ih =>
    have e : cupPowC A z (k + 1) = (CH.mulP A).cupC (by omega) (cupPowC A z k) z := rfl
    rw [e, P.leibniz, ih, hz]
    simp

theorem aL_cocycle {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • aL A (β ∘ j.succAbove) = 0 := by
  induction p with
  | zero =>
    rw [Fin.sum_univ_two]
    have e : ∀ γ : Fin 1 → Co A 1, aL A γ = one0 A := fun _ => rfl
    rw [e, e]
    simp
  | succ p ih =>
    have ih' := ih fun i => β i.succ
    rw [Fin.sum_univ_succ] at ih'
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have e0 : β ∘ (0 : Fin (p + 3)).succAbove = fun i => β i.succ := by
      funext i; simp
    have e1 : aL A (β ∘ (Fin.succ 0 : Fin (p + 3)).succAbove) = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 2)
        (aL A ((fun i => β i.succ) ∘ (0 : Fin (p + 2)).succAbove)) := by
      rw [aL_succ]
      refine congrArg₂ (fun x y => (CH.mulP A).cupC (by omega : 1 + p = p + 1) x y) ?_ (congrArg _ ?_)
      · simp only [Function.comp]
        congr 2
      · funext i
        simp only [Function.comp]
        congr 1
    have e2 : ∀ j : Fin (p + 1), aL A (β ∘ (Fin.succ (Fin.succ j)).succAbove) = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1)
        (aL A ((fun i => β i.succ) ∘ (Fin.succ j).succAbove)) := by
      intro j
      rw [aL_succ]
      refine congrArg₂ (fun x y => (CH.mulP A).cupC (by omega : 1 + p = p + 1) x y) ?_ (congrArg _ ?_)
      · simp only [Function.comp]
        congr 2
      · funext i
        simp only [Function.comp]
        exact congrArg β (Fin.succ_succAbove_succ _ _)
    have e3 : aL A (fun i => β i.succ) = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 1 - β 2)
        (aL A ((fun i => β i.succ) ∘ (0 : Fin (p + 2)).succAbove)) := by
      rw [aL_succ]
      refine congrArg₂ (fun x y => (CH.mulP A).cupC (by omega : 1 + p = p + 1) x y) rfl (congrArg _ ?_)
      funext i
      simp
    simp only [e2]
    rw [e0, e1, e3]
    generalize aL A ((fun i => β i.succ) ∘ (0 : Fin (p + 2)).succAbove) = B at ih' ⊢
    generalize hM : (CH.mulP A).cupC (by omega : 1 + p = p + 1) = M
    have h1 : ∑ i : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ i : Fin (p + 2)) : ℕ) • aL A ((fun i => β i.succ) ∘ (Fin.succ i).succAbove) = -B := by
      refine eq_neg_of_add_eq_zero_right ?_
      simpa using ih'
    have h2 : ∑ j : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ (Fin.succ j) : Fin (p + 3)) : ℕ) • M (β 0 - β 1) (aL A ((fun i => β i.succ) ∘ (Fin.succ j).succAbove)) =
        M (β 0 - β 1) B := by
      rw [← neg_neg B, ← h1, map_neg, map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← neg_smul]
      congr 1
      simp [Fin.val_succ, pow_succ]
    rw [h2]
    simp only [map_sub, LinearMap.sub_apply, Fin.val_zero, Fin.val_succ, pow_zero, one_smul, zero_add, pow_one, neg_smul]
    abel

theorem aL_E {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β (j.succAbove 0)) (aL A (β ∘ j.succAbove)) =
      - aL A β := by
  have h0 := aL_cocycle A β
  rw [Fin.sum_univ_succ] at h0
  rw [Fin.sum_univ_succ]
  have e0 : β ∘ (0 : Fin (p + 2)).succAbove = fun i => β i.succ := by
    funext i; simp
  rw [e0] at h0 ⊢
  generalize hM : (CH.mulP A).cupC (by omega : 1 + p = p + 1) = M
  have h1 : ∑ i : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ i : Fin (p + 2)) : ℕ) • aL A (β ∘ (Fin.succ i).succAbove) = -aL A fun i => β i.succ := by
    refine eq_neg_of_add_eq_zero_right ?_
    simpa using h0
  have h2 : ∑ j : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ j : Fin (p + 2)) : ℕ) • M (β ((Fin.succ j).succAbove 0)) (aL A (β ∘ (Fin.succ j).succAbove)) =
      - M (β 0) (aL A fun i => β i.succ) := by
    rw [← map_neg, ← h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, Fin.succ_succAbove_zero]
  rw [h2, aL_succ, hM]
  simp only [map_sub, LinearMap.sub_apply, Fin.val_zero, pow_zero, one_smul, Fin.zero_succAbove]
  have : (Fin.succ 0 : Fin (p + 2)) = 1 := rfl
  rw [this]
  abel

def fP (z : Co A 2) {p : ℕ} (β : Fin (p + 1) → Co A 1) (k q : ℕ) (h : 2 * k + (p + 1) = q) : Co A q :=
  (CH.mulP A).cupC h (cupPowC A z k) ((CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0) (aL A β))

def gP (z : Co A 2) {p : ℕ} (β : Fin (p + 1) → Co A 1) (k q : ℕ) (h : 2 * k + p = q) : Co A q :=
  (CH.mulP A).cupC h (cupPowC A z k) (aL A β)

theorem d_fP (z : Co A 2) (hz : CH.d _ 2 z = 0) {p : ℕ} (β : Fin (p + 1) → Co A 1) (hβ : ∀ i, CH.d _ 1 (β i) = z)
    (k q : ℕ) (h : 2 * k + (p + 1) = q) : CH.d _ q (fP A z β k q h) = gP A z β (k + 1) (q + 1) (by omega) := by
  unfold fP gP
  rw [P.leibniz, pow_closed A z hz, P.leibniz, aL_closed A β (fun i j => by rw [hβ, hβ]), hβ, pow_mul]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero, zero_add, neg_one_sq, one_pow, one_smul]
  exact (Auxff.assoc A _ _ _ _ _ _ _).symm

theorem sum_fP (z : Co A 2) {p : ℕ} (β : Fin (p + 2) → Co A 1) (k q : ℕ) (h : 2 * k + (p + 1) = q) :
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • fP A z (β ∘ j.succAbove) k q h = - gP A z β k q h := by
  unfold fP gP
  rw [← map_neg, ← aL_E, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

section Res

variable {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C}

def resM (h : V ≤ U) : CH.Mor (CH.modF (U.ι ⋙ A)) (CH.modF (V.ι ⋙ A)) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem d_resB (h : V ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    CH.d _ k (resB A h b) = resB A h (CH.d _ k b) := (resM A h).d_pullC k b

theorem resB_cup (h : V ≤ U) {p q n : ℕ} (e : p + q = n) (a : CH.Cn (CH.modF (U.ι ⋙ A)) p) (b : CH.Cn (CH.modF (U.ι ⋙ A)) q) :
    resB A h ((CH.mulP _).cupC e a b) = (CH.mulP _).cupC e (resB A h a) (resB A h b) := by
  funext s
  rw [Auxff.cupC_apply]
  exact congrArg₂ (fun x y => (CH.mulP _).μ _ x y) (Auxff.term_pull (resM A h) s a _ _) (Auxff.term_pull (resM A h) s b _ _)

theorem resB_sub (h : V ≤ U) {k : ℕ} (a b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h (a - b) = resB A h a - resB A h b := rfl

theorem resB_pow (h : V ≤ U) (z : Co (U.ι ⋙ A) 2) (k : ℕ) :
    resB A h (cupPowC (U.ι ⋙ A) z k) = cupPowC (V.ι ⋙ A) (resB A h z) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : cupPowC (U.ι ⋙ A) z (k + 1) = (CH.mulP _).cupC (by omega) (cupPowC (U.ι ⋙ A) z k) z := rfl
    rw [e, resB_cup, ih]
    rfl

theorem resB_aL (h : V ≤ U) {p : ℕ} (β : Fin (p + 1) → Co (U.ι ⋙ A) 1) :
    resB A h (aL (U.ι ⋙ A) β) = aL (V.ι ⋙ A) fun i => resB A h (β i) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [aL_succ, resB_cup, ih, resB_sub, aL_succ]

theorem resB_fP (h : V ≤ U) (z : Co (U.ι ⋙ A) 2) {p : ℕ} (β : Fin (p + 1) → Co (U.ι ⋙ A) 1) (k q : ℕ)
    (e : 2 * k + (p + 1) = q) :
    resB A h (fP (U.ι ⋙ A) z β k q e) = fP (V.ι ⋙ A) (resB A h z) (fun i => resB A h (β i)) k q e := by
  unfold fP
  rw [resB_cup, resB_cup, resB_pow, resB_aL]

theorem resB_resB {T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h' (resB A h b) = resB A h'' b := rfl

end Res

end GlobalTheory.CompanionTheory.ConeCech
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.KummerPrimitive

theorem res_d_neg {R : Type} [CommRing R] (F : Shv R) : (res R F).d (-1) 0 = 0 := by
  have : (res R F).IsStrictlyGE 0 := by
    unfold res
    infer_instance
  exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 (-1) (by omega)).eq_of_src _ _

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x')
    (hy : ∀ i, y i = y' i) : cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx
  obtain rfl := funext hy
  rfl

def pt0 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b : V ⟶ Y) : Sx (cech f) 0 V :=
  cechPt f 0 (b ≫ f) ![b] (by intro i; fin_cases i; rfl)

def pt1 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : Sx (cech f) 1 V :=
  cechPt f 1 (b ≫ f) ![b, c] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm)

def pt2 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    Sx (cech f) 2 V :=
  cechPt f 2 (b ≫ f) ![b, c, e] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm
    · exact (h.trans h').symm)

section Simplices

variable (hC : CechPt) {Y X : Scheme.{0}} (f : Y ⟶ X) {V V' : Scheme.{0}}
include hC

theorem cechPoint_augmentation (b : V ⟶ Y) : Sx.map (cechAug f) (pt0 f b) = b ≫ f :=
  (((hC Y X f 0 V).2.2 _ _ _).1)

theorem cechPoint_restrict (g : V' ⟶ V) (b : V ⟶ Y) : Sx.res g (pt0 f b) = pt0 f (g ≫ b) := by
  refine ((hC Y X f 0 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i; rfl

theorem cechPair_restrict (g : V' ⟶ V) (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : (g ≫ b) ≫ f = (g ≫ c) ≫ f) :
    Sx.res g (pt1 f b c h) = pt1 f (g ≫ b) (g ≫ c) h' := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i <;> rfl

theorem cechPair_face_zero (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 0 = pt0 f c := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i; rfl

theorem cechPair_face_one (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 1 = pt0 f b := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i; rfl

theorem cechTriple_face_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 0 = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 1 = pt1 f b e (h.trans h') := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_two (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 2 = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 2) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 0 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 0 1 hs = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 0 1 hs) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 1 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 1 1 hs = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 1 1 hs) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

end Simplices

section Coboundary

variable (hD : EvDel) {R : Type} [CommRing R] {E : Spc} {I : GlobalTheory.EtC.Cx R} (β : Cochain ((chains R).obj E) I 1)
  (U : Scheme.{0})
include hD

theorem del_one (z : Sx E 1 U) : ev (δ 1 2 β) 1 1 (by simp) U z =
    Sec.map (I.d 0 1) (ev β 1 0 (by simp) U z) +
      (ev β 0 1 (by simp) U (z.face 0) - ev β 0 1 (by simp) U (z.face 1)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 0 0 1 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

theorem del_two (z : Sx E 2 U) : ev (δ 1 2 β) 2 0 (by simp) U z =
    Sec.map (I.d (-1) 0) (ev β 2 (-1) (by simp) U z) +
      (ev β 1 0 (by simp) U (z.face 0) - ev β 1 0 (by simp) U (z.face 1) + ev β 1 0 (by simp) U (z.face 2)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 1 (-1) 0 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

end Coboundary

theorem main : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.EvDel → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.CechPt →
    CrystallineSemistableComparison.E.FirstChernCoboundary := by
  intro hExt hNat hDel hConc hBasic hCech hC1 q _ X D L hL hInv x hx
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := hC1 q (cech D.f) L hInv
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (res _ (tw q 1)) X 2).1 x
  obtain ⟨α, hαc, hαx⟩ := (hConc (ZMod q) (res _ (tw q 1)) X 2 a).2.1 x ha
  have hmk : CohomologyClass.mk (γ - zcomp (Cocycle.ofHom ((chains (ZMod q)).map (cechAug D.f))) α (zero_add 2)) = 0 := by
    rw [CohomologyClass.mk_sub, hγ, ← hx, ← hαx]
    exact sub_self _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)] at hmk
  obtain ⟨β, hβ⟩ := hmk
  have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) p U),
      ev (δ 1 2 β) p s h U z = ev γ.1 p s h U z - ev α.1 p s h U (Sx.map (cechAug D.f) z) := by
    intro p s h U z
    have e : δ 1 2 β = γ.1 - (Cochain.ofHom ((chains (ZMod q)).map (cechAug D.f))).comp α.1 (zero_add 2) := hβ
    rw [e, ((hExt _ _ _ _ _ _).2 p s h U z).2.1, ((hNat _ _ _ _ α.1 p s h U).2 _ _ z)]
  have hv1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) (p + 1) U),
      ev (δ 1 2 β) (p + 1) s h U z = ev γ.1 (p + 1) s h U z := by
    intro p s h U z
    rw [hv, show ev α.1 (p + 1) s h U (Sx.map (cechAug D.f) z) = 0 from hαc.2 p s h U (Sx.map (cechAug D.f) z), sub_zero]
  refine ⟨a, fun V b => - ev β 0 1 (by simp) V (pt0 D.f b), fun V b c h => ev β 1 0 (by simp) V (pt1 D.f b c h),
    ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro V V' g b
    have e := (hNat _ _ _ _ β 0 1 (by simp) V).1 V' g (pt0 D.f b)
    rw [cechPoint_restrict hCech] at e
    simp only [map_neg]
    exact congrArg Neg.neg e.symm
  · intro V V' g b c h h'
    rw [← (hNat _ _ _ _ β 1 0 (by simp) V).1 V' g (pt1 D.f b c h), cechPair_restrict hCech]
  · intro V b
    have h0 := ((hDel _ _ _ 1 2 (by norm_num) β V).1 (pt0 D.f b))
    rw [hv, hγ0, cechPoint_augmentation hCech, show ev α.1 0 2 (by simp) V (b ≫ D.f) = Sec.res (b ≫ D.f) a from hαc.1 V _, zero_sub] at h0
    simp only [map_neg]
    exact (congrArg Neg.neg h0).symm.trans (neg_neg _)
  · intro V b c h v hv'
    have hu : v ^ q = lineUnit L (pt1 D.f b c h) := hv'.trans (hL V _ ![b, c] _).symm
    have h1 := del_one hDel β V (pt1 D.f b c h)
    rw [hv1 0 1 _ V (pt1 D.f b c h), hγ1 V _ v hu, cechPair_face_zero hCech, cechPair_face_one hCech] at h1
    simp only [map_sub]
    change -ev β 0 1 (by simp) V (pt0 D.f c) - -ev β 0 1 (by simp) V (pt0 D.f b) =
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (ev β 1 0 (by simp) V (pt1 D.f b c h)) -
        Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V v)
    rw [h1]
    abel
  · intro V b c e h h' v w hv' hw'
    have hu : v ^ q = lineUnit L ((pt2 D.f b c e h h').sub 0 1 (by omega)) := by
      rw [cechTriple_subface_zero hCech]
      exact hv'.trans (hL V _ ![b, c] _).symm
    have hu' : w ^ q = lineUnit L ((pt2 D.f b c e h h').sub 1 1 (by omega)) := by
      rw [cechTriple_subface_one hCech]
      exact hw'.trans (hL V _ ![c, e] _).symm
    have h2 := del_two hDel β V (pt2 D.f b c e h h')
    have hz : ∀ y : Sec ((res (ZMod q) (tw q 1)).X (-1)) V, Sec.map ((res (ZMod q) (tw q 1)).d (-1) 0) y = 0 := by
      intro y
      rw [res_d_neg]
      rfl
    rw [hv1 1 0 _ V (pt2 D.f b c e h h'), hγ2 V _ v w hu hu', cechTriple_face_zero hCech, cechTriple_face_one hCech, cechTriple_face_two hCech,
      hz, zero_add] at h2
    exact h2.symm

end GlobalTheory.CompanionTheory.KummerPrimitive
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassCompatibleSystem
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ChernSys

theorem inv_cech (hpt : CrystallineSemistableComparison.E.CechPt) (l : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hl : IsUnit (l : Γ(X, ⊤))) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (cech f) := by
  rintro U ⟨z⟩
  obtain ⟨x, y, h, -⟩ := (hpt Y X f 0 U).1 z
  have h1 : IsUnit (l : Γ(U, ⊤)) := by
    have := hl.map x.appTop.hom
    rwa [map_natCast] at this
  rw [Nat.cast_pow]
  exact h1.pow n

theorem chern_class_compatible_system (hpt : CrystallineSemistableComparison.E.CechPt) : CrystallineSemistableComparison.E.FirstChernCompatibleSystem := by
  intro a2 a11 l _ Y X f _ _ hl L
  have hinv := inv_cech hpt l f hl
  have hne : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨hinv, ?_⟩
  have hb : ∀ n, Function.Bijective (pull (ZMod (l ^ n)) (cechAug f) (tw (l ^ n) 1) 2) :=
    fun n => a2 (ZMod (l ^ n)) f (tw (l ^ n) 1) 2
  choose x hx using fun n => (hb n).2 (c1 (l ^ n) L)
  refine ⟨⟨x, fun k => ?_⟩, hx⟩
  apply (hb k).1
  have e := ((a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) (cech f)).2.1 (hinv (k + 1))).2 L
  have e2 := pull_red (l ^ (k + 1)) (l ^ k) (cechAug f) 2 1 (x (k + 1))
  exact e2.trans ((congrArg _ (hx (k + 1))).trans (e.trans (hx k).symm))

end GlobalTheory.CompanionTheory.ChernSys
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUniqueStatement
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_label_unique : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) (P P' : K[X]),
    HasCuspLabel C τ P → HasCuspLabel C τ P' → P = P' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique | exact GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique | (intros; apply GlobalTheory.CompanionTheory.TyFin.LabelUniq.hasCuspLabel_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeCupOfSteps
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem edgeCup_of_steps : CrystallineSemistableComparison.E.CupCls → CrystallineSemistableComparison.E.StTop → CrystallineSemistableComparison.E.StCupA → CrystallineSemistableComparison.E.StCupB → CrystallineSemistableComparison.E.EdgeCup := by
  intro hCls hTop hA hB
  unfold CrystallineSemistableComparison.E.EdgeCup
  intro R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn x y a b hx hy
  obtain ⟨z, hz, hzx, rfl⟩ := hx
  obtain ⟨z', hz', hzy, rfl⟩ := hy
  obtain ⟨hu, hcls⟩ := hCls R C F₁ F₂ F₃ P i j n hn z z' hz hz'
  refine ⟨P.cupC hn z z', hu, ?_, hcls.symm⟩
  have hyy := hTop R C F₂ T₂ hT₂ j z' hz' j 0 y hzy
  have hb := hB R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn z z' hz j 0 i (add_zero i) y hzy
  exact hA R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n z y (P.cupC hn z z') hyy.1 hyy.2 hb i 0 n hn x hzx

end GlobalTheory.CompanionTheory.EdgeMap
end


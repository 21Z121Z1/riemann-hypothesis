import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0147
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLoweringDerivationFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleOnProductFromSecondFactor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem mp_box_tmul {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {a a' b b' : C}
    (φ : a ⟶ a') (ψ : b ⟶ b') (u : F.obj a) (v : F.obj b) :
    mp (box F) (show ((a, b) : C × C) ⟶ (a', b') from (φ, ψ)) (u ⊗ₜ[R] v) = mp F φ u ⊗ₜ[R] mp F ψ v :=
  rfl

theorem exists_pull_of_vanish_fst (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hU : USt F) (f : Z1 (box F))
    (hf : ∀ (a a' b : C) (φ : a ⟶ a'), f.1 (a, b) (a', b) (φ, 𝟙 b) = 0) :
    ∃ y : Z1 F, (boxR F).pullbackOneCocycle y = f := by

  have hk : ∀ {b b' : C} (ψ : b ⟶ b') {a a' : C} (φ : a ⟶ a'),
      f.1 (a', b) (a', b') (𝟙 a', ψ) =
        mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b'))
          (f.1 (a, b) (a, b') (𝟙 a, ψ)) := by
    intro b b' ψ a a' φ
    have e1 := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ, 𝟙 b) (𝟙 a', ψ)
    have e2 := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a', b'))
      (𝟙 a, ψ) (φ, 𝟙 b')
    have e : (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', ψ)) =
        (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) := by
      simp
    rw [e, e2, hf a a' b' φ, add_zero, hf a a' b φ, map_zero, zero_add] at e1
    exact e1.symm
  have hcomm : ∀ {a a' b' : C} (φ : a ⟶ a') (x : F.obj a ⊗[R] F.obj b'),
      TensorProduct.comm R (F.obj a') (F.obj b')
          (mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) x) =
        (mp F φ).toLinearMap.lTensor (F.obj b') (TensorProduct.comm R (F.obj a) (F.obj b') x) := by
    intro a a' b' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rw [mp_box_tmul, mp_id]; simp
    | add u v hu hv => simp only [map_add, hu, hv]

  have hex : ∀ {b b' : C} (ψ : b ⟶ b'), ∃! m : F.obj b', ∀ a : C,
      f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m := by
    intro b b' ψ
    obtain ⟨m, hm, hu⟩ := hU (F.obj b')
      (fun a ↦ TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)))
      (fun a a' φ ↦ by rw [hk ψ φ, hcomm])
    have hiff : ∀ (a : C) (m' : F.obj b'),
        TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)) = m' ⊗ₜ[R] (1 : F.obj a) ↔
          f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m' := by
      intro a m'
      exact (TensorProduct.comm R (F.obj a) (F.obj b')).injective.eq_iff' (TensorProduct.comm_tmul R _ _ _ _)
    exact ⟨m, fun a ↦ (hiff a m).1 (hm a), fun m' h ↦ hu m' fun a ↦ (hiff a m').2 (h a)⟩
  choose y hy huniq using @hex
  refine ⟨⟨fun b b' ψ ↦ y ψ, fun b b' b'' ψ χ ↦ ?_⟩, ?_⟩
  · refine (huniq (ψ ≫ χ) _ fun a ↦ ?_).symm
    have e := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a, b''))
      (𝟙 a, ψ) (𝟙 a, χ)
    have e' : (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a, b'') from (𝟙 a, χ)) = (𝟙 a, ψ ≫ χ) := by
      simp
    rw [e', hy ψ a, hy χ a] at e
    refine e.trans ?_
    rw [mp_box_tmul, mp_id, TensorProduct.tmul_add]
  · refine Subtype.ext ?_
    funext T T' φ
    obtain ⟨a, b⟩ := T
    obtain ⟨a', b'⟩ := T'
    obtain ⟨φ₁, φ₂⟩ := φ
    have e := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ₁, 𝟙 b) (𝟙 a', φ₂)
    have e' : (show ((a, b) : C × C) ⟶ (a', b) from (φ₁, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', φ₂)) = (φ₁, φ₂) := by
      simp
    rw [e', hf a a' b φ₁, map_zero, zero_add, hy φ₂ a'] at e
    exact e.symm

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZeroAlt
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CovDescent

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)

theorem cosieve_capU (hU : ∀ α, Cosieve (U α)) (S : Finset ι) : Cosieve (capU U S) := fun _ _ φ h =>
  ⟨h.1.imp fun a ha => hU a φ ha, fun α hα => hU α φ (h.2 α hα)⟩

variable {U} in
theorem capU_mono {S T : Finset ι} (h : S ⊆ T) {X : C} (hX : capU U T X) : capU U S X :=
  ⟨hX.1, fun α hα => hX.2 α (h hα)⟩

variable {U} in
theorem capU_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capU U (ent i) T) :
    capU U (ent (Fin.cons (α := fun _ => ι) a i)) T := by
  refine ⟨⟨a, ha⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi.2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

def liftC (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : ComposableArrows (capU U S).FullSubcategory n :=
  (capU U S).lift s fun k => cosieve_capU U hU S (s.map (homOfLE (Fin.zero_le k))) h

abbrev Tm (n : ℕ) : PM.{max u v w} R ι := (covSy F U hQ).term n

def evL (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : (Tm F U hQ n).M S →ₗ[R] F.obj (s.obj (Fin.last n)) :=
  (LinearMap.proj (R := R) (φ := fun t : ComposableArrows (capU U S).FullSubcategory n =>
    ((capU U S).ι ⋙ F).obj (t.obj (Fin.last n))) (liftC U hU S s h)) ∘ₗ
    (relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n).subtype

variable {F U hQ}

theorem evL_congr (hU : ∀ α, Cosieve (U α)) {n p : ℕ} (f : ∀ i : Fin p → ι, (Tm F U hQ n).M (ent i))
    {i i' : Fin p → ι} (e : i = i') (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0))
    (h' : capU U (ent i') (s.obj 0)) : evL F U hQ hU _ s h (f i) = evL F U hQ hU _ s h' (f i') := by
  subst e; rfl

theorem evL_d (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X p)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0)) :
    evL F U hQ hU _ s h ((Tm F U hQ n).cech.d p y i) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        evL F U hQ hU _ s (capU_mono (ent_comp i k.succAbove) h) (y (i ∘ k.succAbove)) := by
  have e := congrArg ((evL F U hQ hU _ s h) ∘ₗ
    (LinearMap.proj (R := R) (φ := fun i : Fin (p + 2) → ι => (Tm F U hQ n).M (ent i)) i))
    (Cos.d_apply (Tm F U hQ n).cech p y)
  rw [map_sum] at e
  simp only [map_zsmul] at e
  exact e

theorem capU_const {b : ι} {T : C} (hb : U b T) : capU U (ent fun _ : Fin 1 => b) T := by
  refine ⟨⟨b, hb⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  exact hb

theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

theorem M_ext (hU : ∀ α, Cosieve (U α)) {n : ℕ} {S : Finset ι} {x y : (Tm F U hQ n).M S}
    (h : ∀ t : ComposableArrows (capU U S).FullSubcategory n,
      evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property x =
        evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property y) : x = y :=
  Subtype.ext (funext h)

def mkM {n : ℕ} (S : Finset ι) (f : CH.Cn ((capU U S).ι ⋙ F) n)
    (hf : ∀ t : ComposableArrows (capU U S).FullSubcategory n, Q (t.obj 0).obj → f t = 0) :
    (Tm F U hQ n).M S :=
  (⟨f, hf⟩ : relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n)

theorem evL_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (x : (Tm F U hQ n).M S)
    (s : ComposableArrows C n) (h : capU U S (s.obj 0)) (hs : Q (s.obj 0)) :
    evL F U hQ hU S s h x = 0 :=
  x.2 (liftC U hU S s h) hs

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X (p + 1))
    (hy : (Tm F U hQ n).cech.d (p + 1) y = 0) (i : Fin (p + 2) → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d (p + 1) y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_succ] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 : ∀ j : Fin (p + 2),
      evL F U hQ hU _ s (capU_mono (ent_comp _ j.succ.succAbove) h')
        (y ((Fin.cons (α := fun _ => ι) b i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) =
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) :=
    fun j => evL_congr hU y (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (y : (Tm F U hQ n).cech.X 0)
    (hy : (Tm F U hQ n).cech.d 0 y = 0) (i : Fin 1 → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = evL F U hQ hU _ s (capU_const hb) (y fun _ => b) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d 0 y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_two] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 := evL_congr hU y (i := (Fin.cons (α := fun _ => ι) b i : Fin 2 → ι) ∘ (1 : Fin 2).succAbove)
    (i' := fun _ => b) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (capU_mono (ent_comp _ _) h') (capU_const hb)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

def hh (hU : ∀ α, Cosieve (U α)) (a : ∀ T, (∃ b, U b T) → ι) (ha : ∀ T h, U (a T h) T) {p n : ℕ}
    (y : (Tm F U hQ n).cech.X (p + 1)) : (Tm F U hQ n).cech.X p := fun i =>
  mkM (ent i) (fun t => evL F U hQ hU _ (t ⋙ (capU U (ent i)).ι)
      (capU_cons (ha _ (t.obj 0).property.1) (t.obj 0).property)
      (y (Fin.cons (α := fun _ => ι) (a _ (t.obj 0).property.1) i)))
    fun t ht => evL_zero hU _ _ _ _ ht

theorem desc (hU : ∀ α, Cosieve (U α)) (n : ℕ) : (Tm F U hQ n).Ex := by
  have hc : ∀ T : C, ∀ h : ∃ b, U b T, ∃ b, U b T := fun _ h => h
  choose a ha using hc
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU _ i _ _).trans ?_
    refine Eq.trans ?_ (map_zero (evL F U hQ hU _ _ _)).symm
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x +
      (-1 : ℤ) ^ 1 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x = 0
    simp
  · rw [one_smul]
    refine M_ext hU fun t => ?_
    have hb := ha _ (t.obj 0).property.1
    have h1 := congrArg (evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const hb))
      (congrFun hx fun _ => a _ (t.obj 0).property.1)
    exact (h1.trans (map_zero _)).trans (map_zero _).symm
  · refine ⟨mkM ∅ (fun t => evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const (ha _ (t.obj 0).property.1))
      (y fun _ => a _ (t.obj 0).property.1)) fun t ht => evL_zero hU _ _ _ _ ht, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    exact (cocycle_zero hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
  · refine ⟨hh hU a ha y, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU (hh hU a ha y) i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
    rfl

theorem covDesc : CovDesc := fun _ _ _ _ _ _ _ _ _ _ hU n => desc hU n

end GlobalTheory.CompanionTheory.CovDescent
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinduced_cech_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Surjective e → ∀ (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinduced_nerve_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | exact GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
open scoped TensorProduct
open GlobalTheory.TopForm

def allE (n d : ℕ) : Gam n d := ∑ e, oneE e

theorem allE_apply {n d : ℕ} (e : E n d) : allE n d e = 1 := by
  classical
  simp [allE, oneE, Finset.sum_apply, Pi.single_apply]

theorem allE_mem {n d : ℕ} (S : Finset (Fin d)) : allE n d ∈ (cone S : AddSubmonoid (Gam n d)) :=
  sum_mem fun e _ => oneE_mem S e

theorem exists_add_nsmul_mem {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d) :
    ∃ N : ℕ, g + N • allE n d ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨(∑ e, |g e|).toNat, ?_⟩
  have hall : ∀ e, 0 ≤ (g + (∑ e, |g e|).toNat • allE n d) e := by
    intro e
    have h1 : |g e| ≤ ∑ e, |g e| :=
      Finset.single_le_sum (f := fun e => |g e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
    have h2 : ((∑ e, |g e|).toNat : ℤ) = ∑ e, |g e| :=
      Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have h3 := neg_abs_le (g e)
    rw [Pi.add_apply, Pi.smul_apply, allE_apply, nsmul_eq_mul, mul_one, h2]
    linarith
  exact ⟨fun _ => hall _, fun _ _ => hall _, Finset.sum_nonneg fun _ _ => hall _⟩

theorem injective_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {f : M →ₗ[A] N} (hf : IsBaseChange B f)
    (hinj : Function.Injective (algebraMap A B)) : Function.Injective f := by
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap A B) hinj
  intro x y hxy
  have h3 : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y := by
    apply hf.equiv.injective
    simp [IsBaseChange.equiv_tmul, hxy]
  have h4 : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y := by
    apply h2
    simpa using h3
  simpa using congrArg (TensorProduct.lid A M) h4

theorem omMap_incl_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ),
    Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  intro K _ n d S a
  letI : Algebra (R0 K n d S) (Lr K n d) :=
    (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d S) (Lr K n d) :=
    IsScalarTower.of_algHom (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤))
  haveI hl : IsLocalization.Away (mon K (allE n d) (allE_mem S)) (Lr K n d) :=
    Away.isLocalization_away le_top (allE n d) (allE_mem S) (AddSubmonoid.mem_top _)
      (fun g _ => exists_add_nsmul_mem S g)
  haveI : Algebra.FormallyEtale (R0 K n d S) (Lr K n d) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (allE n d) (allE_mem S)))
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale K (R0 K n d S) (Lr K n d)
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hb a
  haveI : Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := GlobalTheory.T.kaehler_free_cone_ring S
  have hinj := injective_of_isBaseChange hE (Away.incl_injective le_top)
  have heq : ∀ ω, omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a ω =
      exteriorPowerMapOver (Lr K n d) a (KaehlerDifferential.map K K (R0 K n d S) (Lr K n d)) ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule (R0 K n d S) (Om K (R0 K n d S) a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [omMap_ιMulti, exteriorPowerMapOver_ιMulti]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx =>
      rw [omMap_smul, hx, map_smul]
      exact algebraMap_smul (Lr K n d) c _
  intro x y hxy
  exact hinj (by rw [← heq, ← heq, hxy])

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeUnit

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem pt_of_hom {T T' : Thick (smFun X q)} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T = pt T' := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

theorem spec_comp {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) := by
  have hφ : (g.map (a ≫ b)).φ = (g.map b).φ.comp (g.map a).φ := by rw [g.map_comp]; rfl
  rw [← Spec.map_comp]
  congr 1
  ext x
  show Ideal.Quotient.mk _ ((g.map (a ≫ b)).φ x) = Ideal.Quotient.mk _ ((g.map b).φ ((g.map a).φ x))
  rw [hφ]
  rfl

theorem u_points (D : E.LineData X) {V : Scheme.{0}} {a a' b : V ⟶ D.Y} (ha : a = a')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b ≫ D.f) : D.u a b h = D.u a' b h' := by
  subst ha
  rfl

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem r_sub_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈
      (g.obj c₂).J := by
  subst hc
  have ea := pt_of_hom (g.map a)
  have eb := pt_of_hom (g.map b)
  have ec := pt_of_hom (g.map (a ≫ b))
  have h1 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₁ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ea]
  have h2 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, eb]
  have h3 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ec]
  have wa := Λ.hw a h1
  have wb := Λ.hw b h2
  have wc := Λ.hw (a ≫ b) h3
  have nat := D.nat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle))) _ _ h1
  have h12 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f := by
    simpa only [Category.assoc] using
      congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ ·) h1
  have coc := D.coc _ _ _ h12 h2
  have uc := u_points D (show Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ
      (g.map (a ≫ b)).hle)) ≫ Λ.p c₀ = _ by rw [spec_comp, Category.assoc]) h3 (h12.trans h2)
  have A : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) =
      (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c₂).B ⧸ (g.obj c₂).J))).hom.hom
        (D.u _ _ h12).1 := by
    show Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle (Ideal.Quotient.mk (g.obj c₁).J (Λ.w a)) = _
    rw [wa, nat, ← gamma_nat]
    rfl
  have B : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) *
      Ideal.Quotient.mk (g.obj c₂).J (Λ.w b) = Ideal.Quotient.mk (g.obj c₂).J (Λ.w (a ≫ b)) := by
    rw [A, wb, wc, ← map_mul, ← Units.val_mul, coc, uc]
  rw [← Ideal.Quotient.eq, map_one, Units.val_mul, Units.val_mul, map_mul, map_mul, B, ← map_mul, Units.mul_inv, map_one]

theorem r_sub_one : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  intro K _ _ X q C _ g D Λ σ
  exact r_sub_mem Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (by
    rw [← Functor.map_comp]
    rfl)

end GlobalTheory.CompanionTheory.ConeUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctionalStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_linear_in_functional : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q), Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Con_linear_form | exact GlobalTheory.CompanionTheory.HopfC.Con_linear_form | (intros; apply GlobalTheory.CompanionTheory.HopfC.Con_linear_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLoweringDerivationFormulaStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_lowering_derivation_formula : ∀ {R : Type} [CommRing R] (H : ℕ → Type) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] (g : ℕ) (_ : Module.Basis (Fin g) R (H 1)) (one : H 0) (L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1)) (D : ∀ n, Module.Dual R (H 1) → H (n + 1) →ₗ[R] H n) (τ : ∀ n, H n →ₗ[R] H n), (∀ r : R, r • one = 0 → r = 0) → (∀ x, L 0 x one = x) → (∀ l x, D 0 l x = l x • one) → (∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z)) → (∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z)) → (∀ x, τ 1 x = x) → (∀ y, τ 2 y = y) → Subsingleton (H (g + 2)) → ∃ e : ⋀[R]^2 (H 1) ≃ₗ[R] H 2, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = L 1 a b := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Wedge.exteriorSquare_equiv | exact GlobalTheory.CompanionTheory.HopfC.Wedge.exteriorSquare_equiv | (intros; apply GlobalTheory.CompanionTheory.HopfC.Wedge.exteriorSquare_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionMulLeftRightAndOneStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_mul_left_right_and_one : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (x : Cn F p) (y : Cn F q) (B : Bi F p q), Con F Ξ q ((fun a _ ↦ x a ⊗ₜ[R] 1 : Bi F p q) * B) = Con F (Ξ ∘ₗ LinearMap.mulLeft R x) q B ∧ Con F Ξ q ((fun _ b ↦ 1 ⊗ₜ[R] y b : Bi F p q) * B) = y * Con F Ξ q B ∧ Con F Ξ q (1 : Bi F p q) = Ξ 1 • (1 : Cn F q) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ConMul.con_products | exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_products | (intros; apply GlobalTheory.CompanionTheory.HopfC.ConMul.con_products <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionNaturalInFaceMapsStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_natural_in_face_maps : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (Ξ' : Cn F p' →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (e' : Fin (p + 1) →o Fin (p' + 1)), (∀ B : Bi F p q, Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B)) ∧ (∀ B : Bi F p q, Con F Ξ' q (prA F e' B) = Con F (Ξ' ∘ₗ (pr F e').toLinearMap) q B) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr | exact GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr | (intros; apply GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr <;> assumption)
end


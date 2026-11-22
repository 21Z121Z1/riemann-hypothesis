import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0110
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0115

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonalityStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_character_sum_orthogonality : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ), ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Orth.orth | exact GlobalTheory.CompanionTheory.TyFin.Orth.orth | (intros; apply GlobalTheory.CompanionTheory.TyFin.Orth.orth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverseStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_embedding_GL_inverse : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d → ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | (intros; apply GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardJPat
section
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.WtFormPf

open ReciprocityTheory.Ty.Fin.Lq

section Dat

variable (g N : ℕ) [Fact g.Prime] [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
  (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ)

end Dat

theorem entN_eq {A : Type} [Semiring A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (x y : ℕ) :
    entN M x y = ∑ i : Fin N, ∑ j : Fin N, (if (i : ℕ) = x ∧ (j : ℕ) = y then (1 : A) else 0) * M i j := by
  unfold entN
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨x, h.1⟩ : Fin N), Finset.sum_eq_single (⟨y, h.2⟩ : Fin N)]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ y := fun e => hj (Fin.ext e)
      simp [this]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ x := fun e => hi (Fin.ext e)
      simp [this]
    · simp
  · symm
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : ¬ ((i : ℕ) = x ∧ (j : ℕ) = y) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨i.2, j.2⟩
    simp [this]

end GlobalTheory.CompanionTheory.TyFin.WtFormPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpaceStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_orthonormal_frames_hermitian_space : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | exact GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIso
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe u v w

namespace GlobalTheory.CompanionTheory.CechFull

section Complexes

variable {R : Type} [CommRing R]

theorem mapH_mapH_of_inv {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R))
    (ψ : Cx.Hom L K (RingHom.id R)) (h : ∀ n x, ψ.f n (φ.f n x) = x) (p : ℕ) (x : K.H p) :
    ψ.mapH p (φ.mapH p x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ψ.mapZ p (φ.mapZ p z)) = Submodule.Quotient.mk z
  exact congrArg _ (Subtype.ext (h p z.1))

def equivH {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (h' : ∀ n x, φ.f n (ψ.f n x) = x) (p : ℕ) : K.H p ≃ₗ[R] L.H p :=
  LinearEquiv.ofLinear (φ.mapH p) (ψ.mapH p)
    (LinearMap.ext (mapH_mapH_of_inv ψ φ h' p)) (LinearMap.ext (mapH_mapH_of_inv φ ψ h p))

def cosHom {K L : Cos.{w} R} (f : ∀ n, K.X n →ₗ[R] L.X n)
    (h : ∀ n k x, L.δ n k (f n x) = f (n + 1) (K.δ n k x)) : Cx.Hom K.cx L.cx (RingHom.id R) :=
  ⟨f, fun n x => by
    change L.d n (f n x) = f (n + 1) (K.d n x)
    rw [Cos.d_apply, Cos.d_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul, h]⟩

end Complexes

section Cat

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem pull_pull_of_inv {C' : Type u} [Category.{v} C'] {G : C ⥤ ModuleCat.{w} R} {G' : C' ⥤ ModuleCat.{w} R}
    (m : CH.Mor G G' (RingHom.id R)) (m' : CH.Mor G' G (RingHom.id R))
    (h : ∀ n f, m'.pullC n (m.pullC n f) = f) (p : ℕ) (x : CH.H G p) : m'.pull p (m.pull p x) = x :=
  mapH_mapH_of_inv m.hom m'.hom h p x

variable (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C)

abbrev subFam : ι → ObjectProperty Q.FullSubcategory := fun α T => W α T.obj

variable {Q W}

def upG (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT W i).FullSubcategory ⥤ (capT (subFam Q W) i).FullSubcategory :=
  (capT (subFam Q W) i).lift (Q.lift (capT W i).ι fun T => hW (i 0) _ (T.property 0)) fun T => T.property

def downG {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT (subFam Q W) i).FullSubcategory ⥤ (capT W i).FullSubcategory :=
  (capT W i).lift ((capT (subFam Q W) i).ι ⋙ Q.ι) fun T => T.property

def upM (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) ((capT W i).ι ⋙ F) (RingHom.id R) where
  G := upG hW i
  τ _ := LinearMap.id
  nat _ _ := rfl

def downM {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT W i).ι ⋙ F) ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) (RingHom.id R) where
  G := downG i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem down_up_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) m) :
    (downM F i).pullC m ((upM F hW i).pullC m f) = f := rfl

theorem up_down_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT W i).ι ⋙ F) m) :
    (upM F hW i).pullC m ((downM F i).pullC m f) = f := rfl

end Cat

section Assemble

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) {Q : ObjectProperty C} {ι : Type} {W : ι → ObjectProperty C}

def upX (hW : ∀ α, W α ≤ Q) (q n : ℕ) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).X n →ₗ[R] (cechH F W q).X n :=
  LinearMap.pi fun i => ((upM F hW i).pull q).comp (LinearMap.proj i)

def downX (q n : ℕ) :
    (cechH F W q).X n →ₗ[R] (cechH (Q.ι ⋙ F) (subFam Q W) q).X n :=
  LinearMap.pi fun i => ((downM F i).pull q).comp (LinearMap.proj i)

theorem upX_δ (hW : ∀ α, W α ≤ Q) (q n : ℕ) (k : Fin (n + 2))
    (x : (cechH (Q.ι ⋙ F) (subFam Q W) q).X n) :
    (cechH F W q).δ n k (upX F hW q n x) = upX F hW q (n + 1) ((cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU F _).pull q ((upM F hW (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (upM F hW t).pull q ((resU (Q.ι ⋙ F) _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

theorem downX_δ (q n : ℕ) (k : Fin (n + 2)) (x : (cechH F W q).X n) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k (downX (Q := Q) F q n x) =
      downX (Q := Q) F q (n + 1) ((cechH F W q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU (Q.ι ⋙ F) _).pull q ((downM F (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (downM F t).pull q ((resU F _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

end Assemble

theorem cechH_fullSubcategory_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p,
    Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  intro R _ C _ F Q ι W hW q p
  exact ⟨equivH (cosHom (upX F hW q) (upX_δ F hW q)) (cosHom (downX (Q := Q) F q) (downX_δ F q))
    (fun n x => funext fun i => pull_pull_of_inv (upM F hW i) (downM F i) (down_up_pullC F hW i) q (x i))
    (fun n x => funext fun i => pull_pull_of_inv (downM F i) (upM F hW i) (up_down_pullC F hW i) q (x i)) p⟩

end GlobalTheory.CompanionTheory.CechFull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechRowExact

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
  {ι : Type} (U : ι → ObjectProperty C)

theorem cosieve_capT (hU : ∀ α, Cosieve (U α)) {n : ℕ} (i : Fin n → ι) : Cosieve (capT U i) :=
  fun _ _ φ h a => hU (i a) φ (h a)

theorem capT_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capT U i T) :
    capT U (Fin.cons (α := fun _ => ι) a i) T := fun k => by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi k

def liftC (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (i : Fin n → ι) (s : ComposableArrows C q)
    (h : capT U i (s.obj 0)) : ComposableArrows (capT U i).FullSubcategory q :=
  (capT U i).lift s fun k => cosieve_capT U hU i (s.map (homOfLE (Fin.zero_le k))) h

def ev (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (i : Fin n → ι) (x : CH.Cn ((capT U i).ι ⋙ F) q)
    (s : ComposableArrows C q) (h : capT U i (s.obj 0)) : F.obj (s.obj (Fin.last q)) :=
  x (liftC U hU i s h)

variable {F U}

theorem ev_congr (hU : ∀ α, Cosieve (U α)) {n q : ℕ} (f : ∀ i : Fin n → ι, CH.Cn ((capT U i).ι ⋙ F) q)
    {i i' : Fin n → ι} (e : i = i') (s : ComposableArrows C q) (h : capT U i (s.obj 0))
    (h' : capT U i' (s.obj 0)) : ev F U hU i (f i) s h = ev F U hU i' (f i') s h' := by
  subst e; rfl

theorem ev_d (hU : ∀ α, Cosieve (U α)) {p q : ℕ} (f : ∀ i : Fin (p + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (((cechCC F U).cos q).d p f i) s h =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • ev F U hU (i ∘ k.succAbove) (f (i ∘ k.succAbove)) s (fun a => h _) := by
  have e := congrFun (congrFun (Cos.d_apply ((cechCC F U).cos q) p f) i) (liftC U hU i s h)
  refine e.trans ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  rfl

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

def hh (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {p q : ℕ}
    (f : ∀ i : Fin (p + 2) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (i : Fin (p + 1) → ι) :
    CH.Cn ((capT U i).ι ⋙ F) q := fun t =>
  ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (t.obj 0).obj) i)) (t ⋙ (capT U i).ι)
    (capT_cons U (hα _) (t.obj 0).property)

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {p q : ℕ}
    (f : ∀ i : Fin (p + 2) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (hf : ((cechCC F U).cos q).d (p + 1) f = 0)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (f i) s h = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s
        (capT_cons U (hα _) fun a => h _) := by
  have h' := capT_cons U (hα (s.obj 0)) h
  have e := ev_d hU f _ s h'
  have z : ev F U hU _ (((cechCC F U).cos q).d (p + 1) f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by
    rw [hf]; rfl
  rw [z, Fin.sum_univ_succ] at e
  have e0 := ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h
  have e1 : ∀ j : Fin (p + 2), ev F U hU _ (f ((Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) s (fun a => h' _) =
      ev F U hU _ (f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) (i ∘ j.succAbove))) s (capT_cons U (hα _) fun a => h _) :=
    fun j => ev_congr hU f (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact (add_neg_eq_zero.1 e.symm)

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) (α : C → ι) (hα : ∀ T, U (α T) T) {q : ℕ}
    (f : ∀ i : Fin (0 + 1) → ι, CH.Cn ((capT U i).ι ⋙ F) q) (hf : ((cechCC F U).cos q).d 0 f = 0)
    (i : Fin (0 + 1) → ι) (s : ComposableArrows C q) (h : capT U i (s.obj 0)) :
    ev F U hU i (f i) s h = ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _) := by
  have h' := capT_cons U (hα (s.obj 0)) h
  have e := ev_d hU f _ s h'
  have z : ev F U hU _ (((cechCC F U).cos q).d 0 f (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i)) s h' = 0 := by
    rw [hf]; rfl
  rw [z, Fin.sum_univ_two] at e
  have e0 := ev_congr hU f (cons_zero (α (s.obj 0)) i) s (fun a => h' _) h
  have e1 := ev_congr hU f (i := (Fin.cons (α := fun _ => ι) (α (s.obj 0)) i : Fin (0 + 2) → ι) ∘ (1 : Fin (0 + 2)).succAbove)
    (i' := fun _ => α (s.obj 0)) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (fun a => h' _) (fun _ => hα _)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact (add_neg_eq_zero.1 e.symm)

end GlobalTheory.CompanionTheory.CechRowExact

open GlobalTheory.CompanionTheory.CechRowExact in

theorem GlobalTheory.CompanionTheory.CechRowExact.cech_rows : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ q, ((cechCC F U).dcx.row q).ResUpTo 1 ((cechAugRowU F U).ε q) := by
  intro R _ C _ F ι U hU hc q
  choose α hα using hc
  refine ⟨(cechAugRowU F U).hε q, fun g hg => ?_, fun f hf => ?_, fun n f hf => ?_⟩
  · rw [one_smul]
    funext s
    have h1 := congrFun (congrFun hg fun _ => α (s.obj 0)) (liftC U hU _ s fun _ => hα _)
    exact h1
  · refine ⟨fun s => ev F U hU _ (f fun _ => α (s.obj 0)) s (fun _ => hα _), ?_⟩
    rw [one_smul]
    funext i t
    exact (cocycle_zero hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm
  · refine ⟨hh hU α hα f, ?_⟩
    rw [one_smul]
    funext i t
    refine (ev_d hU (hh hU α hα f) i (t ⋙ (capT U i).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU α hα f hf i (t ⋙ (capT U i).ι) (t.obj 0).property).symm
    rfl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCochainCoordinateExtension
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.GrpOnto

theorem sum_range_periodic {A : Type*} [AddCommMonoid A] (u : ℕ → A) (p : ℕ)
    (hu : ∀ t, u (t + p) = u t) (q : ℕ) :
    ∑ t ∈ Finset.range (p * q), u t = q • ∑ t ∈ Finset.range p, u t := by
  have hper : ∀ q t, u (p * q + t) = u t := by
    intro q t
    induction q with
    | zero => simp
    | succ q ih => rw [show p * (q + 1) + t = (p * q + t) + p by ring, hu, ih]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hper q t

theorem val_sub_one {P : ℕ} [NeZero P] (z : ZMod P) :
    (z.val ≠ 0 → (z - 1).val = z.val - 1) ∧ (z.val = 0 → (z - 1).val = P - 1) := by
  have hlt := ZMod.val_lt z
  have hz : ((z.val : ℕ) : ZMod P) = z := ZMod.natCast_zmod_val z
  have hP := NeZero.pos P
  constructor
  · intro h
    have e1 : z - 1 = ((z.val - 1 : ℕ) : ZMod P) := by
      rw [Nat.cast_sub (by omega), hz]; simp
    rw [e1, ZMod.val_natCast_of_lt (by omega)]
  · intro h
    have hz0 : z = 0 := by rw [← hz, h]; simp
    have e1 : z - 1 = ((P - 1 : ℕ) : ZMod P) := by
      rw [Nat.cast_sub hP, hz0]; simp
    rw [e1, ZMod.val_natCast_of_lt (by omega)]

theorem core {R : Type} [CommRing R] (l : ℕ) [Fact l.Prime] (k : ℕ) {M : Type w} [AddCommGroup M]
    [Module R M] (ρ : Multiplicative (Fin k → ℤ_[l]) →* (M →ₗ[R] M)) (n c : ℕ) (S : Set (Fin k))
    (i : Fin k) (hiS : i ∉ S) (hc : ∀ x : M, l ^ c • x = 0)
    (hsm : ∀ x : M, ∃ a : ℕ, ∀ g : Fin k → ℤ_[l], ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) x = x)
    (f : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M)
    (hf : ∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      f (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (f x)) :
    ∃ g : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M,
      (∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
        g (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (g x)) ∧
      ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
        ρ (Multiplicative.ofAdd (Pi.single i 1)) (g fun j => x j - Pi.single i 1) - g x = f x := by
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.SmoothUniform.smooth_uniform_exponent (R := R) l k ρ n hsm f
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨e, he⟩ : ∃ e : Fin k → ℤ_[l], e = Pi.single i 1 := ⟨_, rfl⟩
  rw [← he]
  have hcomm : ∀ (p q : Multiplicative (Fin k → ℤ_[l])) (y : M), ρ p (ρ q y) = ρ q (ρ p y) := by
    intro p q y
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hmul : ∀ (p q : Fin k → ℤ_[l]) (y : M),
      ρ (Multiplicative.ofAdd (p + q)) y = ρ (Multiplicative.ofAdd p) (ρ (Multiplicative.ofAdd q) y) := by
    intro p q y
    rw [ofAdd_add, map_mul, Module.End.mul_apply]
  let sh : ℕ → (Fin (n + 1) → Fin k → ℤ_[l]) → (Fin (n + 1) → Fin k → ℤ_[l]) :=
    fun t x j => x j - t • e
  let F : ℕ → (Fin (n + 1) → Fin k → ℤ_[l]) → M :=
    fun t x => ρ (Multiplicative.ofAdd (t • e)) (f (sh t x))
  have hF0 : ∀ x, F 0 x = f x := by
    intro x
    have h1 : sh 0 x = x := by funext j; simp [sh]
    simp [F, h1]
  have hFs : ∀ t x, ρ (Multiplicative.ofAdd e) (F t fun j => x j - e) = F (t + 1) x := by
    intro t x
    have h1 : sh t (fun j => x j - e) = sh (t + 1) x := by
      funext j
      simp only [sh, succ_nsmul]
      abel
    change ρ _ (ρ _ (f (sh t fun j => x j - e))) = ρ _ (f (sh (t + 1) x))
    rw [h1, succ_nsmul', hmul]
  have hE : (l ^ a) • e = (l : ℤ_[l]) ^ a • e := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    rfl
  have hper : ∀ t x, F (t + l ^ a) x = F t x := by
    intro t x
    have h1 := (ha e (sh (t + l ^ a) x)).1
    have h2 := (ha e (sh (t + l ^ a) x)).2
    have h3 : (fun s => (l : ℤ_[l]) ^ a • e + sh (t + l ^ a) x s) = sh t x := by
      funext s
      simp only [sh, add_nsmul, ← hE]
      abel
    rw [h3] at h1
    change ρ _ (f (sh (t + l ^ a) x)) = ρ _ (f (sh t x))
    rw [add_nsmul, hmul, hE, h2, h1]
  have hsum : ∀ x, ∑ t ∈ Finset.range (l ^ (a + c)), F (t + 1) x = 0 := by
    intro x
    rw [pow_add, sum_range_periodic (fun t => F (t + 1) x) (l ^ a)
      (fun t => by
        change F (t + l ^ a + 1) x = F (t + 1) x
        rw [add_right_comm]
        exact hper (t + 1) x) (l ^ c)]
    exact hc _
  haveI : NeZero (l ^ (a + c)) := ⟨pow_ne_zero _ hlpos.ne'⟩
  let z : (Fin (n + 1) → Fin k → ℤ_[l]) → ZMod (l ^ (a + c)) :=
    fun x => PadicInt.toZModPow (a + c) (x 0 i)
  have hz1 : ∀ x, z (fun j => x j - e) = z x - 1 := by
    intro x
    simp [z, he, map_sub]
  have hzj : ∀ j ∈ S, ∀ x, z (fun t => Pi.single j (1 : ℤ_[l]) + x t) = z x := by
    intro j hj x
    have hij : i ≠ j := fun h => hiS (h ▸ hj)
    simp [z, Pi.single_eq_of_ne hij]
  have hzl : IsLocallyConstant z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have hb : Metric.closedBall (x 0 i) ((l : ℝ) ^ (-((a + c : ℕ) : ℤ))) ∈ nhds (x 0 i) :=
      Metric.closedBall_mem_nhds _ (zpow_pos (by exact_mod_cast hlpos) _)
    have hcont : Continuous (fun y : Fin (n + 1) → Fin k → ℤ_[l] => y 0 i) :=
      (continuous_apply i).comp (continuous_apply 0)
    filter_upwards [hcont.continuousAt.preimage_mem_nhds hb] with y hy
    have h1 : ‖y 0 i - x 0 i‖ ≤ (l : ℝ) ^ (-((a + c : ℕ) : ℤ)) := by
      simpa [dist_eq_norm] using hy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h1
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hFl : ∀ t, IsLocallyConstant (F t) := by
    intro t
    have hsh : Continuous (sh t) := continuous_pi fun j => (continuous_apply j).sub continuous_const
    exact (f.isLocallyConstant.comp_continuous hsh).comp _
  let gf : (Fin (n + 1) → Fin k → ℤ_[l]) → M :=
    fun x => -∑ t ∈ Finset.range ((z x).val + 1), F t x
  have hg : IsLocallyConstant gf := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h1 := (IsLocallyConstant.iff_eventually_eq _).1 hzl x
    have h2 : ∀ᶠ y in nhds x, ∀ t ∈ Finset.range ((z x).val + 1), F t y = F t x :=
      (Filter.eventually_all_finset _).2 fun t _ => (IsLocallyConstant.iff_eventually_eq _).1 (hFl t) x
    filter_upwards [h1, h2] with y hy1 hy2
    change -∑ t ∈ Finset.range ((z y).val + 1), F t y = -∑ t ∈ Finset.range ((z x).val + 1), F t x
    rw [hy1]
    exact congrArg _ (Finset.sum_congr rfl hy2)
  have hgE : ∀ j ∈ S, ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      gf (fun t => Pi.single j (1 : ℤ_[l]) + x t) = ρ (Multiplicative.ofAdd (Pi.single j 1)) (gf x) := by
    intro j hj x
    have hFj : ∀ t, F t (fun s => Pi.single j (1 : ℤ_[l]) + x s) =
        ρ (Multiplicative.ofAdd (Pi.single j 1)) (F t x) := by
      intro t
      have h1 : sh t (fun s => Pi.single j (1 : ℤ_[l]) + x s) =
          fun s => Pi.single j (1 : ℤ_[l]) + sh t x s := by
        funext s
        simp only [sh, add_sub_assoc]
      change ρ _ (f (sh t _)) = ρ _ (ρ _ (f (sh t x)))
      rw [h1, hf j hj, hcomm]
    simp only [gf]
    rw [hzj j hj x, map_neg, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun t _ => hFj t)
  have hgT : ∀ x : Fin (n + 1) → Fin k → ℤ_[l],
      ρ (Multiplicative.ofAdd e) (gf fun j => x j - e) - gf x = f x := by
    intro x
    simp only [gf]
    rw [map_neg, map_sum, hz1 x]
    simp only [hFs]
    obtain ⟨hne, h0⟩ := val_sub_one (z x)
    by_cases hx : (z x).val = 0
    · have hP := NeZero.pos (l ^ (a + c))
      rw [h0 hx, hx, Nat.sub_add_cancel hP, hsum x]
      simp [hF0]
    · rw [hne hx, Nat.sub_add_cancel (Nat.pos_of_ne_zero hx),
        Finset.sum_range_succ' (fun t => F t x) (z x).val, hF0]
      abel
  exact ⟨⟨gf, hg⟩, hgE, hgT⟩

end GlobalTheory.CompanionTheory.GrpOnto
end


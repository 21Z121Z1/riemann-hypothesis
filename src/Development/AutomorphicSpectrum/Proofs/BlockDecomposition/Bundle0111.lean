import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0102
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0103
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainExt
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatPieces

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
  {ι : Type t} (c : C → ι)

abbrev piece (i : ι) : ObjectProperty C := fun T => c T = i

abbrev res (i : ι) : Mor F ((ObjectProperty.ι (piece c i)) ⋙ F) (RingHom.id R) :=
  Mor.restrict F (ObjectProperty.ι (piece c i))

variable {c}

theorem chain_piece (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} (s : ComposableArrows C n)
    (k : Fin (n + 1)) : c (s.obj k) = c (s.obj 0) :=
  (hc (s.map (homOfLE (Fin.zero_le k)))).symm

variable {F}

def glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) : Cn F n :=
  fun s => g (c (s.obj 0)) (ObjectProperty.lift (piece c (c (s.obj 0))) s (chain_piece hc s))

theorem val_congr {n : ℕ} (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) {i j : ι} (e : i = j)
    (s : ComposableArrows C n) (h : ∀ k, piece c i (s.obj k)) (h' : ∀ k, piece c j (s.obj k)) :
    (g i (ObjectProperty.lift (piece c i) s h) : F.obj (s.obj (Fin.last n))) =
      g j (ObjectProperty.lift (piece c j) s h') := by
  subst e; rfl

theorem pullC_glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) (i : ι) :
    (res F c i).pullC n (glue hc g) = g i := by
  funext s
  have hi : ∀ k, piece c i ((s ⋙ ObjectProperty.ι (piece c i)).obj k) := fun k => (s.obj k).property
  exact val_congr g (hi 0) (s ⋙ ObjectProperty.ι (piece c i)) _ hi

theorem glue_pullC (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} (f : Cn F n) :
    glue hc (fun i => (res F c i).pullC n f) = f := rfl

theorem cochain_ext (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ} {f f' : Cn F n}
    (h : ∀ i, (res F c i).pullC n f = (res F c i).pullC n f') : f = f' := by
  rw [← glue_pullC hc f, ← glue_pullC hc f']
  exact congrArg _ (funext h)

theorem d_glue (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') {n : ℕ}
    (g : ∀ i, Cn ((ObjectProperty.ι (piece c i)) ⋙ F) n) :
    d F n (glue hc g) = glue hc (fun i => d _ n (g i)) := by
  refine cochain_ext hc fun i => ?_
  rw [← Mor.d_pullC, pullC_glue, pullC_glue]

end GlobalTheory.CompanionTheory.CatPieces

open GlobalTheory.CompanionTheory.CatPieces in

theorem GlobalTheory.CompanionTheory.CatPieces.sigmaH {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {ι : Type t} (c : C → ι) (hc : ∀ {T T' : C}, (T ⟶ T') → c T = c T') (n : ℕ) : Function.Bijective fun (x : H F n) (i : ι) => (Mor.restrict F (ObjectProperty.ι fun T => c T = i)).pull n x := by
  have hz : ∀ (i : ι) (a : Cn F n), d F n a = 0 →
      d _ n ((res F c i).pullC n a) = 0 := fun i a ha => by
    rw [Mor.d_pullC, ha, map_zero]
  have hp : ∀ (i : ι) (a : Cn F n) (ha : d F n a = 0),
      (res F c i).pull n ((cx F).cls a ha) = (cx _).cls ((res F c i).pullC n a) (hz i a ha) :=
    fun i a ha => CrystallineSemistableComparison.P.mapH_cls (res F c i).hom n a ha (hz i a ha)
  constructor
  · intro x y hxy
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 y
    have hi : ∀ i, (res F c i).pullC n (a - b) ∈ (cx ((ObjectProperty.ι (piece c i)) ⋙ F)).B n := fun i => by
      have h1 := congrFun hxy i
      change (res F c i).pull n _ = (res F c i).pull n _ at h1
      rw [hp i a ha, hp i b hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1] at h1
      rwa [map_sub]
    rw [(CrystallineSemistableComparison.P.cls_surj (cx F) n).2.2.1]
    cases n with
    | zero =>
      have : a - b = 0 := cochain_ext hc fun i => by
        rw [map_zero]; exact hi i
      rw [this]; exact Submodule.zero_mem _
    | succ n =>
      choose h hh using hi
      refine ⟨glue hc h, ?_⟩
      change d F n (glue hc h) = a - b
      rw [d_glue]
      refine cochain_ext hc fun i => ?_
      rw [pullC_glue]
      exact hh i
  · intro y
    choose a ha hy using fun i => (CrystallineSemistableComparison.P.cls_surj (cx ((ObjectProperty.ι (piece c i)) ⋙ F)) n).1 (y i)
    have hg : d F n (glue hc a) = 0 := by
      rw [d_glue]
      have : (fun i => d _ n (a i)) = fun i => (0 : Cn ((ObjectProperty.ι (piece c i)) ⋙ F) (n + 1)) :=
        funext ha
      rw [this]
      exact cochain_ext hc fun i => by rw [pullC_glue, map_zero]
    refine ⟨(cx F).cls _ hg, funext fun i => ?_⟩
    change (res F c i).pull n _ = _
    rw [hp i _ hg, hy i, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1, pullC_glue, sub_self]
    exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegralStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_unit_ideal_integral : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | exact GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupAssocC
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CupAssocC

section
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem term_term (F : C ⥤ ModuleCat.{w} R) {p m n : ℕ} (s : ComposableArrows C n) (f : Cn F p)
    (g : Fin (m + 1) → Fin (n + 1)) (hg : Monotone g) (g' : Fin (p + 1) → Fin (m + 1)) (hg' : Monotone g') :
    (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (term F (hg.functor ⋙ s) f g' hg') =
      term F s f (g ∘ g') (hg.comp hg') := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last (g' (Fin.last p)))) ≫
      s.map (homOfLE (Fin.le_last (g (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (g (g' (Fin.last p))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have key : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (x : F.obj X),
      (F.map b).hom ((F.map a).hom x) = (F.map (a ≫ b)).hom x := by
    intro X Y Z a b x
    rw [F.map_comp]; rfl
  refine (key _ _ _).trans ?_
  exact congrArg (fun φ => (F.map φ).hom (f ((hg.comp hg').functor ⋙ s))) e

theorem term_id (F : C ⥤ ModuleCat.{w} R) {n : ℕ} (s : ComposableArrows C n) (f : Cn F n) :
    term F s f id monotone_id = f s := by
  have e : s.map (homOfLE (Fin.le_last (id (Fin.last n)))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  unfold term
  rw [e, F.map_id]
  rfl

theorem term_cupC {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q a n : ℕ} (h : p + q = a) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) (θ : Fin (a + 1) → Fin (n + 1)) (hθ : Monotone θ) :
    term F₃ s (P.cupC h f g) θ hθ =
      P.μ _ (term F₁ s f (θ ∘ front h) (hθ.comp (front_mono h)))
        (term F₂ s g (θ ∘ back h) (hθ.comp (back_mono h))) := by
  rw [← term_term F₁ s f θ hθ _ (front_mono h), ← term_term F₂ s g θ hθ _ (back_mono h), P.nat]
  rfl

theorem cupC_at {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) :
    P.cupC h f g s = P.μ _ (term F₁ s f (front h) (front_mono h)) (term F₂ s g (back h) (back_mono h)) := rfl

theorem term_one (A : C ⥤ CommAlgCat.{w} R) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin (0 + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (modF A) s (fun s => (1 : A.obj (s.obj (Fin.last 0)))) g hg = (1 : A.obj (s.obj (Fin.last n))) :=
  map_one (A.map (s.map (homOfLE (Fin.le_last (g (Fin.last 0)))))).hom

end

theorem cup_assocC : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R), (∀ n (x : Cn (modF A) n), (mulP A).cupC (Nat.zero_add n) (fun s => (1 : A.obj (s.obj (Fin.last 0)))) x = x ∧ (mulP A).cupC (Nat.add_zero n) x (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = x) ∧ ∀ {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n) x y z, (mulP A).cupC h₂ ((mulP A).cupC h₁ x y) z = (mulP A).cupC h₄ x ((mulP A).cupC h₃ y z) := by
  intro R _ C _ A
  refine ⟨fun n x => ⟨?_, ?_⟩, ?_⟩
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (back_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [back])), term_id]
    exact one_mul (M := A.obj (s.obj (Fin.last n))) _
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (front_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [front])), term_id]
    exact mul_one (M := A.obj (s.obj (Fin.last n))) _
  · intro p q r a b n h₁ h₂ h₃ h₄ x y z
    funext s
    rw [cupC_at, cupC_at, term_cupC, term_cupC,
      term_congr (modF A) s x ((front_mono h₂).comp (front_mono h₁)) (front_mono h₄)
        (funext fun i => Fin.ext (by simp [front])),
      term_congr (modF A) s y ((front_mono h₂).comp (back_mono h₁)) ((back_mono h₄).comp (front_mono h₃))
        (funext fun i => Fin.ext (by simp [front, back])),
      term_congr (modF A) s z (back_mono h₂) ((back_mono h₄).comp (back_mono h₃))
        (funext fun i => Fin.ext (by simp [back]; omega))]
    exact mul_assoc (G := A.obj (s.obj (Fin.last n))) _ _ _

end GlobalTheory.CompanionTheory.CupAssocC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismPropertiesStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_isomorphism_properties : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | exact GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanishStatement
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_unipotent_sums_vanish : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | exact GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalUnipotentRadicalSumZero
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspSum

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem blk_unip (b : ι → Fin s) (c : Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    Formalism.IrreducibleCountingLemmas.TYPES.blk K b c (g : Matrix ι ι K) = 1 := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply, Subtype.mk.injEq]
  exact hg.2 i l (hi.trans hl.symm)

omit [Fintype K] [DecidableEq K] [Fintype ι] in

theorem entry_of_blk (b : ι → Fin s) {M : Matrix ι ι K}
    (h : ∀ c, Formalism.IrreducibleCountingLemmas.TYPES.blk K b c M = 1) (i j : ι) (hij : b i = b j) :
    M i j = if i = j then 1 else 0 := by
  have := congrFun (congrFun (h (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  simpa only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply,
    Subtype.mk.injEq] using this

theorem unip_mul_mem (b : ι → Fin s) {g h : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) (hh : h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    g * h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨mul_mem hg.1 hh.1, entry_of_blk b fun c => ?_⟩
  rw [Units.val_mul, Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.1 hh.1.1, blk_unip b c hg, blk_unip b c hh,
    one_mul]

theorem unip_inv_mem (b : ι → Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) : g⁻¹ ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨inv_mem hg.1, entry_of_blk b fun c => ?_⟩
  have h := Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.2 hg.1.1
  rw [Units.inv_mul, blk_unip b c hg, mul_one] at h
  rw [← h]
  exact Matrix.submatrix_one _ Subtype.val_injective

open Classical in

theorem sum_rho_unip (τ : FDRep ℂ (GL ι K)) (hc : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ)
    (b : ι → Fin s) (hb : Function.Surjective b) (hs : 2 ≤ s) :
    (∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0) = 0 := by
  set P : Module.End ℂ τ := ∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0
    with hP
  have hfix : ∀ a ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b, τ.ρ a * P = P := by
    intro a ha
    rw [hP, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft a)
      (fun v : GL ι K => if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : a * v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b ↔ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
      refine ⟨fun h => ?_, unip_mul_mem b ha⟩
      simpa using unip_mul_mem b (unip_inv_mem b ha) h
    simp only [Equiv.coe_mulLeft, hiff]
    split_ifs
    · rw [map_mul]
    · rw [mul_zero]
  refine LinearMap.ext fun w => ?_
  exact hc s b hb hs (P w) fun a ha => LinearMap.congr_fun (hfix a ha) w

theorem twoBlock_surjective {d j : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    Function.Surjective (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
  intro c
  fin_cases c
  · exact ⟨⟨0, by omega⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]; omega⟩
  · exact ⟨⟨j, hjd⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]⟩

theorem sum_character_translate :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  intro K _ _ _ d j τ hj hjd hc u
  classical
  have h0 := sum_rho_unip τ hc (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) (twoBlock_surjective hj hjd) le_rfl
  have h1 : LinearMap.trace ℂ τ (τ.ρ u * ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.ρ v else 0) = 0 := by
    rw [h0, mul_zero, map_zero]
  rw [Finset.mul_sum, map_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h1
  split_ifs
  · rw [FDRep.character, map_mul]
  · rw [mul_zero, map_zero]

end GlobalTheory.CompanionTheory.TyFin.CuspSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishingStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_vanishing : ReciprocityTheory.Ty.Fin.St.CuspVanish := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish | exact GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBaseStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_haar_base : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | exact GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementsBijectiveOfBijectiveApp
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.Cech

theorem elMor_bijective_of_bijective {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) (h : ∀ T, Function.Bijective (p.app T)) (n : ℕ) : Function.Bijective ((elMor p F).hom.f n) := by
  haveI : ∀ T, IsIso (p.app T) := fun T => (isIso_iff_bijective _).2 (h T)
  haveI : IsIso p := NatIso.isIso_of_isIso_app p
  have e1 : ∀ x, (elMor (inv p) F).pullC n ((elMor p F).pullC n x) = x := fun x => by
    have e : (inv p ≫ p : E ⟶ E) = 𝟙 E := IsIso.inv_hom_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  have e2 : ∀ x, (elMor p F).pullC n ((elMor (inv p) F).pullC n x) = x := fun x => by
    have e : (p ≫ inv p : E' ⟶ E') = 𝟙 E' := IsIso.hom_inv_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  exact Function.bijective_iff_has_inverse.2 ⟨(elMor (inv p) F).pullC n, e1, e2⟩

end GlobalTheory.CompanionTheory.Cech
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductConvergenceBoundStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_convergence_bound : CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (K : Set (Ainf F)), IsCompact K → ∀ N : ℕ, 0 < N → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), 0 ≤ C → (∀ v, v ∉ S → (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧ ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ δ : ℝ, 0 < δ → ∀ D : Finset (HeightOneSpectrum (𝓞 F)), Disjoint D S → ∀ B : Finset F, (∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ (∃ y : 𝓞 F, (y : F) = (N : F) * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K) → δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤ C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod | exact GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod | (intros; apply GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDegreeOnePrimeNotSplitsCompletely
section
open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density

open Filter Topology Set in

theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hsub : degreeOnePrimes L F ⊆ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∪ (B \ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}) := by
    intro v hv
    by_cases hvB : v ∈ B
    · by_cases hvS : v ∈ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}
      · exact Or.inl hvS
      · exact Or.inr ⟨hvB, hvS⟩
    · exact Or.inl (hcon v hv hvB)
  have hDd := GroundTheory.Global.hasDirichletDensity_degreeOnePrimes L F
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely F M
  have hBfin : (B \ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}).Finite := hB.subset Set.sdiff_subset
  have hBd := GroundTheory.Global.hasDirichletDensity_zero_of_finite hBfin
  have hle : ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum (degreeOnePrimes L F) s / NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 F))) s ≤
        NumberField.Set.primeIdealZetaSum {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} s /
            NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 F))) s +
          NumberField.Set.primeIdealZetaSum (B \ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}) s /
            NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 F))) s := by
    intro s hs
    rw [← add_div, ← GroundTheory.Global.primeIdealZetaSum_union Set.disjoint_sdiff_right hs]
    apply div_le_div_of_nonneg_right (GroundTheory.Global.primeIdealZetaSum_mono hsub hs)
    exact tsum_nonneg (fun _ => by positivity)
  have hlim := le_of_tendsto_of_tendsto hDd (Filter.Tendsto.add hSd hBd) (eventually_nhdsWithin_of_forall hle)
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlacesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_multiple_bounded_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator | exact GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator <;> assumption)
end


import Development.EtaleCohomology.EtaleSheaves.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

structure Base : Prop where
  (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5) (a6nat : DivisorNaturality) (a6ring : DivisorRingCompatibility) (a6supp : DivisorSupportCondition) (a6add : DivisorAdditivity)
  (a7 : A7) (a8 : A8) (a9 : A9) (a10 : A10) (a11 : A11) (b1 : B1) (b2 : B2) (b3 : B3) (b4 : B4) (b5 : B5) (b7 : B7)
  (c1 : C1) (c2 : C2) (c3 : C3) (c4 : C4) (c5 : C5) (d1 : D1) (d2 : D2) (d3 : D3)
  (e1 : E1) (e2 : E2) (e3 : E3) (e4 : E4) (e6 : E6)

def PD (q : ℕ) (X : Scheme.{0}) (d : ℕ) : Prop :=
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

def DimLE {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (d : ℕ) : Prop :=
  ∀ x : X, @Algebra.trdeg k (X.residueField x) _ _ (Spec.preimage (X.fromSpecResidueField x ≫ p)).hom.toAlgebra ≤ d

def CupUnitChernKummerLaws : Prop := DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity

def EtaleSmoothDim : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (d : ℕ)
  [SmoothOfRelativeDimension d p], DimLE p d

def EtaleCdField : Prop := Base → ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (d : ℕ),
  IsUnit (q : k) → Algebra.trdeg k K ≤ d → ∀ n i : ℤ, (d : ℤ) < n → Subsingleton (Ht q (sp K) n i)

def EtaleCdProper : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ), DimLE p d →
  ∀ n i : ℤ, 2 * (d : ℤ) < n → Subsingleton (Ht q (sch.obj X) n i)

def EtaleDegZero : Prop := Base → ∀ (q : ℕ) [NeZero q],
  (∀ (X : Scheme.{0}) [IsIntegral X], IsUnit (q : Γ(X, ⊤)) → ∀ c : Ht q (sch.obj X) 0 0, ∃ m : ℤ, c = m • one q (sch.obj X)) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ i : ℤ, ∃ (ρ : Ht q (sp k) 0 i) (ρ' : Ht q (sp k) 0 (-i)),
    cup q ρ ρ' = (one q (sp k)).cast (by ring) (by ring)

def EtaleBaseExt : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (A : Type) [CommRing A], SH A →
  ∀ (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) (i : ℤ), Eqv _ (sch.map (pullback.fst r s)) (tw q i)

def EtaleKunneth : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (r : Y ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p]
    [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ) (b : ∀ s, Ht q (sch.obj Y) (deg s) j),
  (∀ m : ℤ, Function.Bijective fun c : {s // deg s = m} → ZMod q =>
    ∑ s : {s // deg s = m}, c s • ((b s.1).cast s.2 rfl : Ht q (sch.obj Y) m j)) →
  ∀ n i : ℤ, Function.Bijective fun a : ∀ s, Ht q (sch.obj X) (n - deg s) i =>
    ∑ s, ((cup q (pull _ (sch.map (pullback.fst p r)) _ _ (a s)) (pull _ (sch.map (pullback.snd p r)) _ _ (b s))).cast
      (by ring) rfl : Ht q (sch.obj (pullback p r)) n (i + j))

def LeafSupp : Prop := Base → ∀ (q : ℕ) [NeZero q] {X Z : Scheme.{0}} [IsNoetherian X] (ι : Z ⟶ X) [IsClosedImmersion ι],
  IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → ∀ {n m i j : ℤ} (a : Ht q (sch.obj X) n i)
  (b : Ht q (sch.obj X) m j), pull _ (sch.map U.ι) _ _ a = 0 → pull _ (sch.map ι) _ _ b = 0 → cup q a b = 0

def LeafDiag : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ δ : Ht q (sch.obj (pullback p p)) (2 * d) d,
    (∀ W : (pullback p p).Opens, (W : Set ↥(pullback p p)) = (Set.range (pullback.diagonal p))ᶜ →
      pull _ (sch.map W.ι) _ _ δ = 0) ∧
    ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens), (U : Set X) = (Set.range x)ᶜ →
      ∀ c : Ht q (sch.obj X) (2 * d) d, pull _ (sch.map U.ι) _ _ c = 0 →
        ∃ m : ℤ, c = m • pull _ (sch.map (pullback.lift (p ≫ x) (𝟙 X) (by simp [hx]))) _ _ δ

def EtaleExcise : Prop := Base → ∀ (q : ℕ) [NeZero q] {X' X Z : Scheme.{0}} [IsNoetherian X] (f : X' ⟶ X) [IsProper f]
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → IsIso (f ∣_ U) →
  ∀ n i : ℤ, Function.Bijective (HK.pull (ZMod q)
    (mappingCone.map ((chains _).map (sch.map (pullback.fst f ι))) ((chains _).map (sch.map ι))
      ((chains _).map (sch.map (pullback.snd f ι))) ((chains _).map (sch.map f))
      (by simp only [← Functor.map_comp, pullback.condition])) (tw q i) n)

def EtalePoint' : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (c : Ht q (sch.obj X) (2 * d) d),
    (U : Set X) = (Set.range x)ᶜ ∧ pull _ (sch.map U.ι) _ _ c = 0 ∧ addOrderOf c = q

def EtalePrime : Prop := Base → ∀ (q : ℕ), q.Prime → ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  PD q X d

def EtaleCoef : Prop := Base → ∀ (q a b : ℕ) [NeZero a] [NeZero b], q = a * b → ∀ E : Spc, Inv q E →
  ∃ (ι : ∀ n i : ℤ, Ht a E n i →+ Ht q E n i) (β : ∀ n i : ℤ, Ht b E n i →+ Ht a E (n + 1) i),
    (∀ n i, Function.Exact (ι n i) (red q b E n i) ∧ Function.Exact (red q b E n i) (β n i) ∧
      Function.Exact (β n i) (ι (n + 1) i)) ∧
    ∀ (n m i j : ℤ), (∀ (x : Ht a E n i) (y : Ht q E m j),
        cup q (ι n i x) y = ι _ _ (cup a x (red q a E m j y))) ∧
      ∀ (y : Ht q E n i) (x : Ht a E m j), cup q y (ι m j x) = ι _ _ (cup a (red q a E n i y) x)

def LeafStep : Prop := Base → ∀ (a b : ℕ) [NeZero a] [NeZero b] (k : Type) [Field k] [IsAlgClosed k], IsUnit ((a * b : ℕ) : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  PD a X d → PD b X d → PD (a * b) X d

theorem pd_one (X : Scheme.{0}) (d : ℕ) : PD 1 X d := by
  have hs : ∀ n i : ℤ, Subsingleton (Ht 1 (sch.obj X) n i) := fun n i => Module.subsingleton (ZMod 1) _
  have := hs (2 * d) d
  let _ : Unique (Ht 1 (sch.obj X) (2 * d) d) := uniqueOfSubsingleton 0
  refine ⟨AddEquiv.ofUnique, fun n i φ => ⟨0, fun b => Subsingleton.elim _ _, fun y _ => (hs n i).elim _ _⟩⟩

theorem goal_of (hA : CupUnitChernKummerLaws) (hP : EtalePrime) (hS : LeafStep) : LateralTheory.E.EtaleChapterEEight := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b7 c1 c2 c3 c4 c5 d1 d2 d3 e1 e2 e3 e4 e6
  have B : Base := ⟨a1, a2, a3, a4, a5, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7,
    c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3, e4, e6⟩
  intro q hq k _ _ hu X _ p _ d _
  change PD q X d
  have hq0 := hq.out
  clear hq
  induction q using Nat.recOnMul with
  | zero => exact absurd rfl hq0
  | one => exact pd_one X d
  | prime l hl => exact hP B l hl k hu p d
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hq0
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hq0
    have : NeZero a := ⟨ha0⟩
    have : NeZero b := ⟨hb0⟩
    have hu' : IsUnit ((a : k) * (b : k)) := by simpa using hu
    exact hS B a b k hu p d (ha (isUnit_of_mul_isUnit_left hu') ha0) (hb (isUnit_of_mul_isUnit_right hu') hb0)

end LateralTheory.E.E8

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.t_E3Cut

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A9 ∧ B1 ∧ B2 ∧ B4 ∧ C3 ∧ C4

def RE (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop := Eqv _ (sch.map (Spec.map f)) (tw q i)

def BC (q : ℕ) (i : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RE q i φ'

def Et : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.Etale

def IE : MorphismProperty CommRingCat.{0} := MorphismProperty.ind.{0} Et

def AlgRes : MorphismProperty CommRingCat.{0} := fun A C f =>
  ∀ Q : Ideal C, Q.IsPrime → ∀ c : C, ∃ p : Polynomial A, (∃ n, f.hom (p.coeff n) ∉ Q) ∧ p.eval₂ f.hom c ∈ Q

def SpS {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  ∀ r : Ideal A, r.IsPrime → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap f.hom = r

abbrev pC (A : CommRingCat.{0}) : A ⟶ CommRingCat.of (Polynomial A) := CommRingCat.ofHom Polynomial.C

def Good (q : ℕ) (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) : Prop :=
  ∀ (B : CommRingCat.{0}) (c : A ⟶ B), Et c → BC q i k (t ≫ c)

theorem RE.comp {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f) (hg : RE q i g) :
    RE q i (f ≫ g) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  rw [h]; exact (hg n).comp (hf n)

theorem RE.of_comp_left {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f)
    (hfg : RE q i (f ≫ g)) : RE q i g := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff _ (hf n)).1 this

theorem RE.of_comp_right {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hg : RE q i g)
    (hfg : RE q i (f ≫ g)) : RE q i f := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff' (hg n) _).1 this

theorem RE.id (q : ℕ) (i : ℤ) (A : CommRingCat.{0}) : RE q i (𝟙 A) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (𝟙 A))) (tw q i) n) = _root_.id := by
    funext x; rw [Spec.map_id, CategoryTheory.Functor.map_id, pull_id]; rfl
  rw [h]; exact Function.bijective_id

theorem RE.of_isIso (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) [IsIso f] : RE q i f := fun n => by
  have h1 : ∀ x, pull _ (sch.map (Spec.map (inv f))) (tw q i) n (pull _ (sch.map (Spec.map f)) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull _ (sch.map (Spec.map f)) (tw q i) n (pull _ (sch.map (Spec.map (inv f))) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem BC.of_one {q : ℕ} {i : ℤ} {A Y C Y' : CommRingCat.{0}} {φ : A ⟶ Y} {c : A ⟶ C} {w : Y ⟶ Y'} {φ' : C ⟶ Y'}
    (h : IsPushout φ c w φ') (hr : RE q i φ') : BC q i φ c := fun _ _ ψ h' => by
  rw [← h.inr_isoIsPushout_hom _ _ h']
  exact hr.comp (RE.of_isIso q i _)

def AlgResProps : Prop :=
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)) ∧
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes (f ≫ g) → AlgRes g) ∧
  (∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral → AlgRes f) ∧
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
    AlgRes (CommRingCat.ofHom (algebraMap A B))

def IEComp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

def LocIE : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
  IE (CommRingCat.ofHom (algebraMap A B))

def SHExists : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A), r.IsPrime →
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ ∀ a : A, a ∈ r ↔ ¬ IsUnit (f.hom a)

def AICSH : Prop := ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → SH T

def AICExt : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ Function.Injective g.hom ∧ AIC D

def DomCover : Prop := ∀ (C : CommRingCat.{0}), AIC C → ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧ AIC (Localization.AtPrime r)

def HensInt : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] (f : A →+* B),
  f.IsIntegral → (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → Nonempty (HenselianLocalRing B)

def SHTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → SH Z

def IntClos : Prop := ∀ {A C : CommRingCat.{0}} (c : A ⟶ C) [IsDomain C], SH A → AIC C → AlgRes c →
  ∃ (B : CommRingCat.{0}) (b : A ⟶ B) (j : B ⟶ C), b ≫ j = c ∧ b.hom.IsIntegral ∧ Function.Injective j.hom ∧ IsLocalRing B ∧
    AIC B ∧ ∀ z : C, ∃ s y : B, s ≠ 0 ∧ j.hom s * z = j.hom y

def SHSection : Prop := ∀ (A : CommRingCat.{0}), SH A → ∀ {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ s : Spec A ⟶ V, s ≫ g = 𝟙 _

def Coprod : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (X : ι → Scheme.{0}) (n : ℤ),
  Function.Bijective fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x

def ZarLocal : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X),
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U → Eqv R (sch.map (g ∣_ V)) F) → Eqv R (sch.map g) F

def Limit : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), Et c → BC q i φ c) → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), IE c → BC q i φ c

def Stalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop,
  (∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)) →
  (∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → ∃ (D : CommRingCat.{0}) (g : C ⟶ D), g.hom.IsIntegral ∧ SpS g ∧ P D (c ≫ g) ∧
    ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
      BC q i φ (c ≫ g ≫ o)) →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BC q i φ c

def SHEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B → RE q i f

def EtaleBaseChangeFractionFieldIndEtaleOverPolynomial : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [Field K] [Algebra T K]
  [IsFractionRing T K], AIC T → IsUnit (q : T) → ∀ (X : CommRingCat.{0}) (h : CommRingCat.of (Polynomial T) ⟶ X), IE h →
  BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ h)

def ULAStalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C) [IsDomain C] [IsLocalRing C], AIC C → AlgRes c → BC q i (pC A ≫ h) c

def ULA : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), AlgRes c → BC q i (pC A ≫ h) c

def Step : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A), IsUnit (q : T) →
  AlgRes k → Good q i k t → Good q i k (t ≫ pC A)

def Base : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T))) (𝟙 _)

def Global : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K),
  (∀ n : ℕ, Good q i k (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T))) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p], Eqv _ (sch.map (pullback.fst p (Spec.map k))) (tw q i)

theorem Good.of_equiv {q : ℕ} {i : ℤ} {T K A A' : CommRingCat.{0}} {k : T ⟶ K} {t : T ⟶ A} (h : Good q i k t)
    (e : A ≃+* A') (t' : T ⟶ A') (ht : t ≫ CommRingCat.ofHom e.toRingHom = t') : Good q i k t' := fun B c hc => by
  rw [← ht, Category.assoc]
  exact h B _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) hc)

theorem goal_of (h1 : AlgResProps) (h2 : Base) (h3 : Step) (h4 : Global) : LateralTheory.E.EtaleChapterEThree := by
  intro a1 a2 a3 a4 a5 _ _ a9 _ _ b1 b2 _ b4 _ _ _ _ c3 c4 _ _ _ _ _ _ q _ T _ _ _ hT hq X p _ i
  have H : Hyp := ⟨a1, a2, a3, a4, a5, a9, b1, b2, b4, c3, c4⟩
  refine h4 H q i _ (fun n => ?_) p
  induction n with
  | zero =>
    refine (h2 H q i T hT hq).of_equiv (MvPolynomial.isEmptyRingEquiv T (Fin 0)).symm _ ?_
    ext x; simp
  | succ n ih =>
    refine (h3 H q i _ _ hq (h1.2.2.2.2.2 T _ (nonZeroDivisors T)) ih).of_equiv
      (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
    ext1
    exact RingHom.ext fun x => (MvPolynomial.finSuccEquiv T n).symm.commutes x

end LateralTheory.E.t_E3Cut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.t_E1Cut

def QA (S : Type) [CommRing S] : Prop :=
  ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (π : T →+* S), AIC T ∧ Function.Surjective π

def Good (C : Type) [CommRing C] (J : Ideal C) : Prop :=
  J ≤ Ideal.jacobson ⊥ ∧ ∀ e : C ⧸ J, IsIdempotentElem e → ∃ x : C, IsIdempotentElem x ∧ Ideal.Quotient.mk J x = e

def lcMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type} (φ : LocallyConstant (PrimeSpectrum A) Y) :
    LocallyConstant (PrimeSpectrum B) Y :=
  φ.comap ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩

def rL {S : Type} [CommRing S] (f g : S) : Localization.Away f →+* Localization.Away (f * g) :=
  IsLocalization.Away.awayToAwayRight f g

def rR {S : Type} [CommRing S] (f g : S) : Localization.Away g →+* Localization.Away (f * g) :=
  IsLocalization.Away.awayToAwayLeft g f

def Conn (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) : Prop :=
  (∀ j, j < n → Function.Bijective (pull R f F j)) ∧ Function.Injective (pull R f F n)

def Cover : Prop := ∀ (A : Type) [CommRing A], ∃ (A' : Type) (_ : CommRing A') (φ : A →+* A'),
  φ.IsIntegral ∧ Function.Surjective (PrimeSpectrum.comap φ) ∧ QA A'

def HensIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → Good B (I.map φ)

def LCGood : Prop := ∀ (C : Type) [CommRing C] (J : Ideal C), Good C J → ∀ Y : Type,
  Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum C) Y => lcMap (Ideal.Quotient.mk J) φ)

def QAClosed : Prop := ∀ (S : Type) [CommRing S], QA S →
  AIC S ∧ (∀ f : S, QA (Localization.Away f)) ∧ ∀ J : Ideal S, QA (S ⧸ J)

def EtLift : Prop := ∀ (T S C : Type) [CommRing T] [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C] (π : T →+* S),
  Function.Surjective π → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra T C') (ρ : C' →+* C), Algebra.Etale T C' ∧
    Function.Surjective ρ ∧ ρ.comp (algebraMap T C') = (algebraMap S C).comp π ∧
    RingHom.ker ρ = (RingHom.ker π).map (algebraMap T C')

def EtAIC : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap T C))))

def FinEtSection : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C] [Module.Finite S C], QA S →
  Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) → Nonempty (C →ₐ[S] S)

def LCSplit : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S], QA S → ∀ f g : S, Ideal.span {f, g} = ⊤ →
  ∀ φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q),
  ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

def EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions : Prop := A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ e : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) ≃+ Ht q (sp B) 0 i),
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      pull _ (spMap f) _ _ (e B ζ φ) = e C (ζ.map f) (lcMap f φ)

def MV : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ → ∀ n : ℤ,
  (∀ c : H R (sp (Localization.Away (f * g))) F n, ∃ a b, c = pull R (spMap (rL f g)) F n a - pull R (spMap (rR f g)) F n b) →
  ∀ x : H R (sp S) F (n + 1), pull R (spMap (algebraMap S (Localization.Away f))) F _ x = 0 →
    pull R (spMap (algebraMap S (Localization.Away g))) F _ x = 0 → x = 0

def ZarLocal : Prop := B1 → B2 → ∀ (q : ℕ) (S : Type) [CommRing S], AIC S → IsUnit (q : S) → ∀ n i : ℤ, 0 < n →
  ∀ (x : Ht q (sp S) n i) (p : PrimeSpectrum S), ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0

def AcycQA : Prop := A1 → A9 → B1 → B2 → ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S], QA S → IsUnit (q : S) → Acyc q (sp S)

def EqvQA : Prop := A1 → A9 → B1 → B2 → ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (J : Ideal S), QA S → Good S J →
  IsUnit (q : S) → ∀ i : ℤ, Eqv _ (spMap (Ideal.Quotient.mk J)) (tw q i)

def DescStep : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (n : ℤ),
  (∀ p, Conn R (disc.map (f.app p)) F n) → Eqv R (disc.map (f.app (op (SimplexCategory.mk 0)))) F → Conn R f F (n + 1)

def CechLevels : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A), φ.IsIntegral →
  Function.Surjective (PrimeSpectrum.comap φ) →
  (IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)))) ∧
  ∃ ψ : cech (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ⟶
      cech (Spec.map (CommRingCat.ofHom φ)),
    ψ ≫ cechAug _ = cechAug _ ≫ spMap (Ideal.Quotient.mk I) ∧
    (∀ p, ∃ (B : Type) (_ : CommRing B) (χ : A →+* B), χ.IsIntegral ∧ Nonempty (Arrow.mk (ψ.app p) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map χ))))))) ∧
    Nonempty (Arrow.mk (ψ.app (op (SimplexCategory.mk 0))) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))))

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem sq (R : Type) [CommRing R] {E E' G G' : Spc} {f : E ⟶ E'} {g : G ⟶ G'} {a : E ⟶ G} {b : E' ⟶ G'} (w : f ≫ b = a ≫ g)
    {F : Shv R} (ha : Eqv R a F) (hb : Eqv R b F) (n : ℤ) :
    (Function.Bijective (pull R f F n) ↔ Function.Bijective (pull R g F n)) ∧
    (Function.Injective (pull R f F n) ↔ Function.Injective (pull R g F n)) := by
  have h : pull R f F n ∘ pull R b F n = pull R a F n ∘ pull R g F n := by
    funext x; simp only [Function.comp]; rw [← pull_comp, ← pull_comp, w]
  constructor
  · rw [← Function.Bijective.of_comp_iff _ (hb n), h, Function.Bijective.of_comp_iff' (ha n)]
  · rw [← Function.Injective.of_comp_iff' _ (hb n), h, Function.Injective.of_comp_iff (ha n).1]

theorem conn_sq (R : Type) [CommRing R] {E E' G G' : Spc} {f : E ⟶ E'} {g : G ⟶ G'} {a : E ⟶ G} {b : E' ⟶ G'} (w : f ≫ b = a ≫ g)
    {F : Shv R} (ha : Eqv R a F) (hb : Eqv R b F) (n : ℤ) : Conn R f F n ↔ Conn R g F n :=
  and_congr (forall_congr' fun j => imp_congr_right fun _ => (sq R w ha hb j).1) (sq R w ha hb n).2

theorem arr_w {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'} (e : Arrow.mk f ≅ Arrow.mk g) :
    ∃ (a : P ⟶ Q) (b : P' ⟶ Q'), IsIso a ∧ IsIso b ∧ disc.map f ≫ disc.map b = disc.map a ≫ disc.map g :=
  ⟨e.hom.left, e.hom.right, inferInstanceAs (IsIso e.hom.left), inferInstanceAs (IsIso e.hom.right), by
    rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ (Arrow.w e.hom).symm⟩

theorem unit_spec {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem goal_of (hC : Cover) (hH : HensIdem) (hE : EqvQA) (hD : DescStep) (hL : CechLevels) : LateralTheory.E.EtaleChapterEOne := by
  intro a1 _ _ _ _ _ _ a9 _ _ b1 b2 _ b4 _ _ _ _ _ _ _ _ _ _ q A _ I _ hq i
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · have : Subsingleton A := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hq))
    have hb : Function.Bijective (Ideal.Quotient.mk I) := ⟨fun _ _ _ => Subsingleton.elim _ _, Ideal.Quotient.mk_surjective⟩
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) := (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
    exact eqv_iso _ _ _
  have : NeZero q := ⟨hpos.ne'⟩
  have key : ∀ (m : ℕ) (B : Type) [CommRing B] (J : Ideal B),
      (∀ (C : Type) [CommRing C] (φ : B →+* C), φ.IsIntegral → Good C (J.map φ)) → IsUnit (q : B) →
      Conn _ (spMap (Ideal.Quotient.mk J)) (tw q i) ((m : ℤ) - 1) := by
    intro m
    induction m with
    | zero =>
      intro B _ J _ _
      have hs := (a9 _ (tw q i)).1
      refine ⟨fun j hj => ?_, ?_⟩
      · have := hs (sp B) j (by omega)
        have := hs (sp (B ⧸ J)) j (by omega)
        exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
      · have := hs (sp B) (((0 : ℕ) : ℤ) - 1) (by omega)
        exact Function.injective_of_subsingleton _
    | succ m ih =>
      intro B _ J hG hu
      obtain ⟨B', _, φ, hi, hs, hqa⟩ := hC B
      obtain ⟨⟨i1, i2, i3, i4⟩, ψ, w, hp, ⟨e0⟩⟩ := hL B B' φ J hi hs
      have d1 := b4 q (Spec.map (CommRingCat.ofHom φ)) (unit_spec hu) i
      have d2 := b4 q (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map φ) φ Ideal.le_comap_map)))
        (unit_spec (by simpa using hu.map (Ideal.Quotient.mk J))) i
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) - 1 + 1 by push_cast; ring]
      refine (conn_sq _ w d2 d1 _).1 (hD a1 _ _ ψ _ (fun p => ?_) ?_)
      · obtain ⟨C, _, χ, hχ, ⟨e⟩⟩ := hp p
        obtain ⟨a, b, _, _, w'⟩ := arr_w e
        refine (conn_sq _ w' (eqv_iso _ _ _) (eqv_iso _ _ _) _).2 (ih C (J.map χ) (fun D _ θ hθ => ?_) (by simpa using hu.map χ))
        rw [Ideal.map_map]
        exact hG D _ (hχ.trans _ _ hθ)
      · obtain ⟨a, b, _, _, w'⟩ := arr_w e0
        intro n
        exact (sq _ w' (eqv_iso _ _ _) (eqv_iso _ _ _) n).1.2
          (hE a1 a9 b1 b2 q B' (J.map φ) hqa (hG B' φ hi) (by simpa using hu.map φ) i n)
  intro n
  exact (key (n.toNat + 2) A I (fun C _ φ h => hH A I C φ h) hq).1 n (by omega)

end LateralTheory.E.t_E1Cut

end
end


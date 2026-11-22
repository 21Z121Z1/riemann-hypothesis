import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsRatDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def RatDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (U : X.Opens), IsAffineOpen U →
    ∀ b : Γ(baseChange f ℚ, baseChangeMap f ℚ ⁻¹ᵁ U),
      ∃ N : ℕ, 0 < N ∧ ∃ c : Γ(X, U), (baseChangeMap f ℚ).app U c = N • b

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

section PullbackHom

variable {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}

def pullbackHomAlong (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G) :
    (Scheme.Modules.pullback k).obj F ⟶ (Scheme.Modules.pullback k).obj G :=
  (pullbackCompIso e (Iso.refl _)).hom ≫ (Scheme.Modules.pullback g).map ψ ≫
    (pullbackCompIso e (Iso.refl _)).inv

lemma pullbackIsoAlong_hom (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (pullbackIsoAlong e ψ).hom = pullbackHomAlong e ψ.hom := by
  simp [pullbackIsoAlong, pullbackHomAlong]

lemma pullbackHomAlong_comp (e : g ≫ h = k) {F G H : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G)
    (ψ' : (Scheme.Modules.pullback h).obj G ⟶ (Scheme.Modules.pullback h).obj H) :
    pullbackHomAlong e (ψ ≫ ψ') = pullbackHomAlong e ψ ≫ pullbackHomAlong e ψ' := by
  simp [pullbackHomAlong]

lemma pullbackHomAlong_id (e : g ≫ h = k) (F : Z.Modules) :
    pullbackHomAlong e (𝟙 ((Scheme.Modules.pullback h).obj F)) = 𝟙 _ := by
  simp [pullbackHomAlong]

end PullbackHom

section Spread

def SpreadHom.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (hn : 0 < n), m ∣ n →
      ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G,
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ = φ

def SpreadHomInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (hn : 0 < n), m ∣ n →
      ∀ ψ₁ ψ₂ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G,
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ₁ =
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ₂ →
        ψ₁ = ψ₂

end Spread

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

def SpreadsOn (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    (W : X.Opens) : Prop :=
  ∃ E' : (W : Scheme.{0}).Modules, IsVectorBundle E' ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E)

def SpreadLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (E : (baseChange f (ZLoc p)).Modules),
    IsVectorBundle E → ∀ x : baseChange f (ZLoc p),
      ∃ W : X.Opens, x ∈ baseChangeMap f (ZLoc p) ⁻¹ᵁ W ∧ SpreadsOn f (ZLoc p) E W

def specZLocToBaseChange :
    Spec (CommRingCat.of (ZLoc ⟨2, Nat.prime_two⟩)) ⟶ baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (Int.castRingHom _))) (𝟙 _) (by simp)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

def toOpen (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) : baseChange f R ⟶ (W : Scheme.{0}) :=
  IsOpenImmersion.lift W.ι (baseChangeMap f R) hW

@[reassoc (attr := simp)]
lemma toOpen_ι (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) :
    toOpen f R W hW ≫ W.ι = baseChangeMap f R :=
  IsOpenImmersion.lift_fac _ _ _

def SpreadBundleNbhd.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules), IsVectorBundle E →
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f (ZLoc p) W hW)).obj E' ≅ E)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsZLocDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def ZLocDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (U : X.Opens), IsAffineOpen U →
    ∀ b : Γ(baseChange f (ZLoc p), baseChangeMap f (ZLoc p) ⁻¹ᵁ U),
      ∃ N : ℕ, 0 < N ∧ ¬ (p : ℕ) ∣ N ∧ ∃ c : Γ(X, U), (baseChangeMap f (ZLoc p)).app U c = N • b

end

end GroundTheory.Heights₂.Heights.Model
end


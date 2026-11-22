import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PZLocDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace ZLocDenominators

theorem proof : ZLocDenominators.Statement := by
  intro X f p U hU
  have : IsAffineHom (baseChangeMap f (ZLoc p)) := by
    set_option backward.isDefEq.respectTransparency.types false in
    exact MorphismProperty.pullback_fst _ _ inferInstance
  set g := baseChangeMap f (ZLoc p) with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  intro b
  let φ : Γ(X, U) ⟶ Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U) := g.appLE U (g ⁻¹ᵁ U) le_rfl
  have hφ : g.app U = φ := Scheme.Hom.app_eq_appLE _
  let ιA : CommRingCat.of ℤ ⟶ Γ(X, U) := CommRingCat.ofHom (Int.castRingHom Γ(X, U))
  let h : CommRingCat.of ℤ ⟶ CommRingCat.of (ZLoc p) :=
    CommRingCat.ofHom (Int.castRingHom (ZLoc p))
  have hUf : hU.fromSpec ≫ f = Spec.map ιA := specZIsTerminal.hom_ext _ _

  have key := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
  have Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h))
      (Spec.map ιA) (Spec.map h) := by
    have P := (isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))
    rw [← hUf]
    refine P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι,
        ← hV.isoSpec_inv_ι]
      simp [morphismRestrict_ι]
    · rw [← hV.isoSpec_inv_ι]
      simp
    · rw [← hU.isoSpec_inv_ι]
      simp
    · simp

  let S : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  let M : Submonoid Γ(X, U) := S.map (Int.castRingHom Γ(X, U))
  let L := Localization M
  let fZ : ZLoc p →+* L := IsLocalization.map (M := S) (S := ZLoc p) L
    (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)
  have H : fZ.comp (algebraMap ℤ (ZLoc p)) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U)) :=
    IsLocalization.map_comp _
  have Palg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fZ H S)
  have hh : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p) := Subsingleton.elim _ _
  rw [hh] at Palg
  let e := Pgeo.isoIsPullback _ _ Palg
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective e.hom
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.inv
  have hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg
  have hχψ : χ ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]
  have hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a) := fun a => by rw [← hcomp]; rfl
  have hψa : ∀ b, ψ (χ b) = b := fun b => by
    rw [← CommRingCat.comp_apply, hχψ]; rfl

  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M (χ b)
  obtain ⟨n, hn, hnm⟩ := Submonoid.mem_map.mp m.2
  have hpn : ¬ ((p : ℕ) : ℤ) ∣ n := fun hd => hn (Ideal.mem_span_singleton.mpr hd)
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero _)
  have hb : b * (n : Γ(baseChange f (ZLoc p), g ⁻¹ᵁ U)) = φ a := by
    have := congrArg ψ ham
    rw [map_mul, hψa, ← hφa, ← hφa, ← hnm] at this
    simpa using this
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun hd => hpn (Int.natCast_dvd.mpr hd), ?_⟩
  rw [hφ, nsmul_eq_mul]
  rcases Int.natAbs_eq n with hn' | hn'
  · refine ⟨a, ?_⟩
    rw [← hb, mul_comm, hn']
    simp
  · refine ⟨-a, ?_⟩
    rw [map_neg, ← hb, mul_comm, hn']
    simp

end ZLocDenominators

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsDescendHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def DescendHom.Statement : Prop :=
  ∀ (T Y Z : Scheme.{0}) (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) (g : T ⟶ Y) (e : g' ≫ ι = g)
    (F G : Y.Modules)
    (φ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G),
    (∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn g G V)) →
    (∀ V : Y.Opens, V ≤ ι.opensRange → ∀ s : Γ(F, V), ∃ t : Γ(G, V),
      pullSectionOn g G V t = φ.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) →
    ∃ ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G,
      pullbackHomAlong e ψ = φ

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericPullInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def GenericPullInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n →
      ∀ V : (invOpen f a : Scheme.{0}).Opens, V ≤ invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n) →
        Function.Injective
          (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlueTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def GlueTwo.Statement : Prop :=
  ∀ (X : Scheme.{0}) (O₁ O₂ O O₁₂ : X.Opens) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O ≤ O₁ ⊔ O₂ →
    ∀ (k₁ : O₁₂ ≤ O₁) (k₂ : O₁₂ ≤ O₂), O₁ ⊓ O₂ ≤ O₁₂ →
    ∀ (F₁ : (O₁ : Scheme.{0}).Modules) (F₂ : (O₂ : Scheme.{0}).Modules)
      (ψ : (Scheme.Modules.pullback (X.homOfLE k₁)).obj F₁ ≅
        (Scheme.Modules.pullback (X.homOfLE k₂)).obj F₂),
    ∃ (F : (O : Scheme.{0}).Modules) (e₁ : (Scheme.Modules.pullback (X.homOfLE h₁)).obj F ≅ F₁)
      (e₂ : (Scheme.Modules.pullback (X.homOfLE h₂)).obj F ≅ F₂),
      pullbackCompIso (X.homOfLE_homOfLE k₂ h₂) e₂ =
        pullbackCompIso (X.homOfLE_homOfLE k₁ h₁) e₁ ≪≫ ψ

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullInjLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def PullInjLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (G : (U : Scheme.{0}).Modules), IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ V : (U : Scheme.{0}).Opens, V ≤ invOpen (U.ι ≫ f) n →
        Function.Injective (pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) G V)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomInjLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadHomInjLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ ψ₁ ψ₂ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj G,
        pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ₁ =
          pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ₂ →
        ψ₁ = ψ₂

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadHomLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ⟶
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj G,
        pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ =
          pullbackHomAlong (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) (U ⊓ invOpen f n) U
            inf_le_left).symm φ

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomNbhd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

@[reassoc (attr := simp)]
lemma toOpen_homOfLE (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) {m : ℤ} (hm : IsUnit (m : R))
    (h : W ≤ invOpen f m) : toOpen f R W hW ≫ X.homOfLE h = toInvOpen f R m hm := by
  rw [← cancel_mono (invOpen f m).ι]
  simp [Scheme.homOfLE_ι]

def SpreadHomNbhd.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ (W : X.Opens) (hWa : W ≤ invOpen f a) (hW : Set.range (baseChangeMap f ℚ) ⊆ Set.range W.ι)
      (ψ : (Scheme.Modules.pullback (X.homOfLE hWa)).obj F ⟶
        (Scheme.Modules.pullback (X.homOfLE hWa)).obj G),
      pullbackHomAlong (toOpen_homOfLE f ℚ W hW
        (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa) ψ = φ

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def SpreadHomSections.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n →
      ∀ V : (invOpen f a : Scheme.{0}).Opens, V ≤ invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n) →
        ∀ s : Γ(F, V), ∃ t : Γ(G, V),
          pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V t =
            φ.app ((toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) ⁻¹ᵁ V)
              (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) F V s)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSectionsLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def SpreadHomSectionsLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ⟶
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ V : (U : Scheme.{0}).Opens, V ≤ invOpen (U.ι ≫ f) n →
        ∀ s : Γ(F, V), ∃ t : Γ(G, V),
          pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) G V t =
            φ.app ((baseChangeMap f (ZLoc p) ∣_ U) ⁻¹ᵁ V)
              (pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) F V s)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadIsoLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadIsoLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ β : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ≅
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ (m : ℕ) (_ : 0 < m) (_ : ¬ (p : ℕ) ∣ m)
      (ψ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U))).obj G),
      pullbackIsoAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f m)) ≫
          X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U) = _) ψ =
        pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) (U ⊓ invOpen f m) U
          inf_le_left).symm β

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadStep.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules) (W₁ W₂ : X.Opens),
    SpreadsOn f (ZLoc p) E W₁ → SpreadsOn f (ZLoc p) E W₂ →
    ∃ W : X.Opens, baseChangeMap f (ZLoc p) ⁻¹ᵁ W₁ ⊔ baseChangeMap f (ZLoc p) ⁻¹ᵁ W₂ ≤
        baseChangeMap f (ZLoc p) ⁻¹ᵁ W ∧ SpreadsOn f (ZLoc p) E W

end

end GroundTheory.Heights₂.Heights.Model
end


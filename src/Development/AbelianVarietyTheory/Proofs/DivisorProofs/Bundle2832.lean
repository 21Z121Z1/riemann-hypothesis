import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularPeriodicRatioCoverFamilies
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isUnit_res_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem ratio_periodic_isReg : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (N : ℕ) (σ : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (σ k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), σ k (z + l) = σ k z) → (∀ k j, ∀ z ∈ pre u.ex (W k), z ∈ pre u.ex (W j) → σ k z = val u.ex _ (r k j) z ^ N * σ j z) → ∀ k, IsReg u.ex (W k) (σ k) := by
  intro A _ g L u hA n W r hR N σ hhol hper htr
  obtain ⟨-, -, -, -, hinf, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨-, hcov, hbasic, hself, hcoc⟩ := hR
  have hv : ∀ (U V : A.left.Opens) (h : V ≤ U) (b : Γ(A.left, U)), ∀ z ∈ pre u.ex V,
      val u.ex V ((A.left.presheaf.map (homOfLE h).op).hom b) z = val u.ex U b z :=
    fun U V h b z hz => hres U V h b z hz
  have hmul : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a * b) z = val u.ex U a z * val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_mul e (a : Sec (str A) U) b
  have hsub : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a - b) z = val u.ex U a z - val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_sub e (a : Sec (str A) U) b
  have hpow : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ (a : Γ(A.left, U)) (m : ℕ),
      val u.ex U (a ^ m) z = val u.ex U a z ^ m := by
    intro U z hz a m
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he]; exact map_pow e (a : Sec (str A) U) m
  have hunit : ∀ k j, IsUnit ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) :=
    fun k j => isUnit_res_of_le_basicOpen _ _ (hbasic k j).ge
  let M : LB A.left := ⟨Fin n, W, fun k j => (hunit k j).unit ^ N⟩
  have hMg : ∀ k j, ((M.g k j : Γ(A.left, W k ⊓ W j))) =
      ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) ^ N := by
    intro k j
    change (((hunit k j).unit ^ N : Γ(A.left, W k ⊓ W j)ˣ) : Γ(A.left, W k ⊓ W j)) = _
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]

  have hval : ∀ k j (V : A.left.Opens) (h : V ≤ W k ⊓ W j), ∀ z ∈ pre u.ex V,
      val u.ex V ((res h (M.g k j) : Γ(A.left, V))) z = val u.ex (W k) (r k j) z ^ N := by
    intro k j V h z hz
    have hz' : z ∈ pre u.ex (W k ⊓ W j) := hmono _ _ h hz
    have e1 : ((res h (M.g k j) : Γ(A.left, V))) =
        (A.left.presheaf.map (homOfLE h).op).hom (M.g k j : Γ(A.left, W k ⊓ W j)) := rfl
    rw [e1, hv _ _ h _ z hz, hMg, hpow _ z hz', hv _ _ _ _ z hz']
  have hM : M.IsLB := by
    refine ⟨hcov, fun k => ?_, fun k j l => ?_⟩
    · apply Units.ext
      change (A.left.presheaf.map _).hom (M.g k k : Γ(A.left, W k ⊓ W k)) = 1
      rw [hMg, hself k, map_one, one_pow, map_one]
    · apply Units.ext
      rw [Units.val_mul]
      apply sub_eq_zero.mp
      apply GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA
      intro z hz
      have hk : z ∈ pre u.ex (W k) := hmono _ _ (inf_le_left.trans inf_le_left) hz
      have hj : z ∈ pre u.ex (W j) := hmono _ _ (inf_le_left.trans inf_le_right) hz
      rw [hsub _ z hz, hmul _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz,
        hcoc k j l z hk hj, mul_pow, sub_self]
  have htrans : ∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j),
      σ i z = val u.ex _ (M.g i j).val z * σ j z := by
    intro i j z hz
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := hz
    rw [hinf] at hz'
    have e := hval i j (W i ⊓ W j) le_rfl z hz
    have e2 : ((res (le_rfl : W i ⊓ W j ≤ W i ⊓ W j) (M.g i j) : Γ(A.left, W i ⊓ W j))) = (M.g i j).val := by
      change (A.left.presheaf.map (homOfLE le_rfl).op).hom _ = _
      have : (homOfLE (le_rfl : W i ⊓ W j ≤ W i ⊓ W j)).op = 𝟙 _ := rfl
      rw [this, CategoryTheory.Functor.map_id]; rfl
    rw [e2] at e
    change σ i z = val u.ex (W i ⊓ W j) (M.g i j).val z * σ j z
    rw [e]
    exact htr i j z hz'.1 hz'.2
  exact GlobalTheory.T.periodic_holomorphic_sections_regular_abelianVariety A g L u hA M hM σ hhol hper htrans

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SemiProd

theorem torus_prod_iso : ∀ (S : Scheme.{0}) (X₁ X₂ : Type) [AddCommGroup X₁] [AddCommGroup X₂], IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂)) (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) := by
  intro S X₁ X₂ _ _
  let comb : ∀ {M : Type} [CommGroup M], (Multiplicative X₁ →* M) → (Multiplicative X₂ →* M) →
      (Multiplicative (X₁ × X₂) →* M) := fun u v =>
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X₁ X₂)) *
      v.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X₁ X₂))
  let l : ∀ {Z : Over S}, (Z ⟶ splitTorus S X₁) → (Z ⟶ splitTorus S X₂) → (Z ⟶ splitTorus S (X₁ × X₂)) :=
    fun {Z} f g => (splitTorusPointsEquiv S (X₁ × X₂) Z).symm
      (comb (splitTorusPointsEquiv S X₁ Z f) (splitTorusPointsEquiv S X₂ Z g))
  have f₁ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂) = f := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₁ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have f₂ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂) = g := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₂ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have u : ∀ {Z : Over S} (m : Z ⟶ splitTorus S (X₁ × X₂)),
      m = l (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
        (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    intro Z m
    apply (splitTorusPointsEquiv S (X₁ × X₂) Z).injective
    rw [MulEquiv.apply_symm_apply, SplitTorusPow.points_comp_torusMap,
      SplitTorusPow.points_comp_torusMap]
    refine MonoidHom.ext fun x => ?_
    have hx : x = Multiplicative.ofAdd (AddMonoidHom.inl X₁ X₂ x.toAdd.1) *
        Multiplicative.ofAdd (AddMonoidHom.inr X₁ X₂ x.toAdd.2) := by
      rw [← ofAdd_add]; simp
    conv_lhs => rw [hx]
    rw [map_mul]
    rfl
  have hl : IsLimit (BinaryFan.mk (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) :=
    BinaryFan.IsLimit.mk _ (fun f g => l f g) (fun f g => f₁ f g) (fun f g => f₂ f g)
      (fun f g m h₁ h₂ => by rw [u m]; exact congrArg₂ l h₁ h₂)
  have e : lift (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) =
      (hl.conePointUniqueUpToIso (tensorProductIsBinaryProduct _ _)).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.left⟩).symm
    · rw [lift_snd]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.right⟩).symm
  rw [e]
  infer_instance

theorem tensorHom_prop : ∀ (S : Scheme.{0}) (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange] (A B C D : Over S) (f : A ⟶ B) (g : C ⟶ D), P f.left → P g.left → P (f ⊗ₘ g).left := by
  intro S P _ _ A B C D f g hf hg
  have e : (f ⊗ₘ g).left = pullback.map A.hom C.hom B.hom D.hom f.left g.left (𝟙 S) (by simp) (by simp) := by
    first | rfl | simp
  rw [e]
  exact P.pullback_map hf hg (Over.w f).symm (Over.w g).symm

theorem kernel_tensor : ∀ (S : Scheme.{0}) (T₁ T₂ G₁ G₂ B₁ B₂ : Over S) [GrpObj B₁] [GrpObj B₂] (i₁ : T₁ ⟶ G₁) (i₂ : T₂ ⟶ G₂) (q₁ : G₁ ⟶ B₁) (q₂ : G₂ ⟶ B₂), IsPullback i₁ (toUnit T₁) q₁ (η : 𝟙_ (Over S) ⟶ B₁) → IsPullback i₂ (toUnit T₂) q₂ (η : 𝟙_ (Over S) ⟶ B₂) → IsPullback (i₁ ⊗ₘ i₂) (toUnit (T₁ ⊗ T₂)) (q₁ ⊗ₘ q₂) (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
  intro S T₁ T₂ G₁ G₂ B₁ B₂ _ _ i₁ i₂ q₁ q₂ h₁ h₂
  have e₁ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ fst _ _ = η := by simp [MonObj.tensorObj.one_def]
  have e₂ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ snd _ _ = η := by simp [MonObj.tensorObj.one_def]
  have c₁ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ fst _ _) ≫ q₁ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ fst _ _) h
    simp only [Category.assoc, tensorHom_fst, e₁] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have c₂ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ snd _ _) ≫ q₂ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ snd _ _) h
    simp only [Category.assoc, tensorHom_snd, e₂] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have w : (i₁ ⊗ₘ i₂) ≫ (q₁ ⊗ₘ q₂) = toUnit (T₁ ⊗ T₂) ≫ (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, e₁, tensorHom_fst_assoc]
      rw [h₁.w, ← Category.assoc, toUnit_unique (fst T₁ T₂ ≫ toUnit T₁) (toUnit _)]
    · simp only [Category.assoc, tensorHom_snd, e₂, tensorHom_snd_assoc]
      rw [h₂.w, ← Category.assoc, toUnit_unique (snd T₁ T₂ ≫ toUnit T₂) (toUnit _)]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (h₁.lift (s.fst ≫ fst _ _) (toUnit _) (c₁ _ _ s.condition))
      (h₂.lift (s.fst ≫ snd _ _) (toUnit _) (c₂ _ _ s.condition)))
    (fun s => ?_) (fun s => toUnit_unique _ _) (fun s m hm _ => ?_)⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, tensorHom_snd, lift_snd_assoc, h₂.lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← tensorHom_fst, ← Category.assoc, hm]
      · exact toUnit_unique _ _
    · rw [lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← tensorHom_snd, ← Category.assoc, hm]
      · exact toUnit_unique _ _

variable {S : Scheme.{0}}

theorem isAbelianScheme_tensor {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) := by
  haveI := hA.comm; haveI := hB.comm; haveI := hA.smooth; haveI := hB.smooth
  haveI := hA.proper; haveI := hB.proper; haveI := hA.geomConnected; haveI := hB.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · show Smooth (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show IsProper (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom); exact GeometricallyConnected.comp _ _

theorem torusExtension_of_prod {K : Type} [Field K] {G G₁ G₂ : Over (Spec (.of K))} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] (a₁ : G ⟶ G₁) (a₂ : G ⟶ G₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)]
    (E₁ : TorusExtension G₁) (E₂ : TorusExtension G₂) : Nonempty (TorusExtension G) := by
  letI := E₁.addCommGroup; haveI := E₁.free; haveI := E₁.finite; letI := E₁.grpB
  letI := E₂.addCommGroup; haveI := E₂.free; haveI := E₂.finite; letI := E₂.grpB
  haveI := E₁.q_hom; haveI := E₂.q_hom; haveI := E₁.i_hom; haveI := E₂.i_hom
  haveI := torus_prod_iso (Spec (.of K)) E₁.X E₂.X
  haveI := SplitTorusPow.isMonHom_torusMap (S := Spec (.of K)) (AddMonoidHom.inl E₁.X E₂.X)
  haveI := SplitTorusPow.isMonHom_torusMap (S := Spec (.of K)) (AddMonoidHom.inr E₁.X E₂.X)
  have key := kernel_tensor _ _ _ _ _ _ _ E₁.i E₂.i E₁.q E₂.q E₁.isKernel E₂.isKernel
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget _).map (lift a₁ a₂)))
  haveI : IsMonHom (inv (lift a₁ a₂)) := inferInstanceAs (IsMonHom (asIso (lift a₁ a₂)).inv)
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P E₁.q.left → P E₂.q.left → P (lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)).left := by
    intro P _ _ h₁ h₂
    rw [Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _) (tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂)
  refine ⟨{ X := E₁.X × E₂.X
            B := E₁.B ⊗ E₂.B
            isAbelian := isAbelianScheme_tensor E₁.isAbelian E₂.isAbelian
            q := lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)
            q_hom := inferInstance
            q_flat := hP @Flat E₁.q_flat E₂.q_flat
            q_surjective := hP @Surjective E₁.q_surjective E₂.q_surjective
            q_quasiCompact := hP @QuasiCompact E₁.q_quasiCompact E₂.q_quasiCompact
            i := lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
                (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)) ≫ (E₁.i ⊗ₘ E₂.i) ≫ inv (lift a₁ a₂)
            i_hom := inferInstance
            isKernel := ?_ }⟩
  refine IsPullback.of_iso key (asIso (lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
    (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)))).symm (asIso (lift a₁ a₂)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · exact toUnit_unique _ _
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem isSemiAbelian_tensor : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  intro S G₁ G₂ _ _ h₁ h₂
  haveI := h₁.comm; haveI := h₂.comm; haveI := h₁.smooth; haveI := h₂.smooth
  haveI := h₁.separated; haveI := h₂.separated; haveI := h₁.quasiCompact; haveI := h₂.quasiCompact
  haveI := h₁.geomConnected; haveI := h₂.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, fun Ω _ _ p => ?_⟩
  · show Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show QuasiCompact (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show GeometricallyConnected (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); exact GeometricallyConnected.comp _ _
  · obtain ⟨E₁⟩ := h₁.fibres Ω p
    obtain ⟨E₂⟩ := h₂.fibres Ω p
    haveI : IsIso (lift ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂))) :=
      isIso_prodComparison_of_preservesLimit_pair (Over.pullback p) G₁ G₂
    exact torusExtension_of_prod ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂)) E₁ E₂

end GlobalTheory.SemiProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

def IsPre {F : Type} [Field F] [NumberField F] {G T : Scheme.{0}} (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T)
    {X W : Scheme.{0}} (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T) : Prop :=
  IsArithVar q d ∧ IsPullback jB (πB ≫ s) q (spMap (algebraMap (𝓞 F) F)) ∧ IsFinite πB ∧ Set.range πB = S ∧
    jB ≫ ρ = πB ≫ ι

def IntCrit {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} (s : W ⟶ Sp F) (jB : W ⟶ X) : Prop :=
  ∀ (V : X.Opens), IsAffineOpen V → ∀ f : Γ(W, jB ⁻¹ᵁ V),
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W)
      (xt : Sp ε.O ⟶ X), xg ≫ s = spMap (algebraMap F (AlgebraicClosure F)) → spMap ε.O.subtype ≫ xt = xg ≫ jB →
      ⊤ ≤ xt ⁻¹ᵁ V → ∀ hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V), TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx f ∈ ε.O) →
    ∃ f₀ : Γ(X, V), jB.app V f₀ = f

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {T : Scheme.{0}}
  (t : SAB H T)

def LatPres {R : Type} [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) {g M : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R) : Prop :=
  (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
    ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
        (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) cf w →
      (spMap (epsMul δ) ≫ w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (kind p) ↔
        ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1)

end Tangent

def IsSplitting {R : Type} [CommRing R] {g M r : ℕ} (D : ℕ) (P : Matrix (Fin g) (Fin g) R) (h : Fin M → Fin g → R)
    (N : ℕ) (U : Matrix (Fin g) (Fin r) R) (I : Fin r → Fin M) : Prop :=
  P * U = (D : R) • U ∧ (Matrix.of fun i => h (I i)) * U = (N : R) • (1 : Matrix (Fin r) (Fin r) R) ∧
    U * (Matrix.of fun i => h (I i)) * P = (N : R) • P ∧
    ∀ j, ∃ a : Fin r → R, Matrix.vecMul (h j) P = ∑ i, a i • Matrix.vecMul (h (I i)) P

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

open Classical in

def scOf (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (kind : ℕ → Bool) (p : ℕ) : ℝ :=
  if kind p = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p else 0

def IsEigProj {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (D : ℕ) (P : Matrix (Fin g) (Fin g) R) : Prop :=
  P * P = (D : R) • P ∧
  ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β) →
    ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left),
      IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
      (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ (P.map ψ).mulVec cf = (D : K) • cf)

def RingBasis {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (r : ℕ) (kind : ℕ → Bool) (sc : ℕ → ℝ) : Prop :=
  ∃ (N : ℕ) (u : Fin r → (Sp (DualNumber R) ⟶ Z.t.G.left)), N ≠ 0 ∧
    (∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp β) →
      IsEigBasis Z φ (spMap ψ ≫ x) τ (fun i => spMap (dualMap ψ) ≫ u i)) ∧
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (φ : c.F →+* ℂ_[p]),
      spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) →
      ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
        ∀ w, IsEigTan Z φ (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) τ w →
          ((∃ a : Fin r → ℂ_[p], (∀ i, ‖(N : ℂ_[p]) * a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x)
                (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp ψ)) ≫ u i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ lat Z.t p (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) (kind p))

abbrev LocAssign {X W : Scheme.{0}} (r : ℕ) (jB : W ⟶ X) (U : X.Opens) : Type 1 :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

def IsLocFrame {F : Type} [Field F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) (r : ℕ)
    (τ : E →+* ℂ) (U : X.Opens) (u : LocAssign Z r jB U) : Prop :=
  (∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (ψ : F →+* K),
      x ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ →
      IsEigBasis Z (ψ.comp e.symm.toRingHom) (x ≫ πB ≫ genι Z) τ (u K x hx)) ∧
  ∀ (K K' : Type) [CommRing K] [CommRing K'] (ψ : K →+* K') (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
      (hx' : ⊤ ≤ ((spMap ψ ≫ x) ≫ jB) ⁻¹ᵁ U) (i : Fin r),
      u K' (spMap ψ ≫ x) hx' i = spMap (dualMap ψ) ≫ u K x hx i

def IsLocLat {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z)
    (r : ℕ) (τ : E →+* ℂ) (kind : ℕ → Bool) (U : X.Opens) (u : LocAssign Z r jB U) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X),
    xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)) →
    spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ U → ∀ (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      ∃ δ : ℂ_[resP v], ‖δ‖ = (resP v : ℝ) ^ (-scOf H τ kind (resP v)) ∧
        ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
          ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
                (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u _ xg hx i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ lat Z.t (resP v) (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) (kind (resP v)))

def IsTrans {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {r : ℕ} {U U' : X.Opens} (u : LocAssign Z r jB U)
    (u' : LocAssign Z r jB U') (A : Matrix (Fin r) (Fin r) Γ(X, U ⊓ U')) : Prop :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
    (hxx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ U')) (i : Fin r),
    IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx) (fun b => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (A b i))
      (u' K x hx' i)

def FramesMatch {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {M : X.Modules} {r : ℕ} (dual : Bool)
    {U U' : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) (f' : Fin r → Γ(M, U')) (u : LocAssign Z r jB U)
    (u' : LocAssign Z r jB U') : Prop :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U')
    (hxx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ (U ⊓ U')) (i : Fin r),
    cond dual
      (IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u' K x hx')
        (fun a => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' i a)) (u K x hx i))
      (IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx)
        (fun b => TangentOrigin.evalPt (x ≫ jB) (U ⊓ U') hxx (trCo hf f' b i)) (u' K x hx' i))

def EigConj (G : ∀ σ' : c.F →+* ℂ, EigMet Z σ') : Prop :=
  ∀ (σ σ' : c.F →+* ℂ) (y : CxPts (genStr Z) σ) (y' : CxPts (genStr Z) σ') (g : EigFrame Z σ (y.1 ≫ genι Z))
    (g' : EigFrame Z σ' (y'.1 ≫ genι Z)) (τ : E →+* ℂ), σ' = (starRingEnd ℂ).comp σ →
    y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g.IsMap (starRingEnd ℂ) g' →
    (G σ').gram y' g' τ = ((G σ).gram y g τ).map (starRingEnd ℂ)

end Free

end GlobalTheory.ArLieBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem triv_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), GlobalTheory.TensBal.Triv T 0 := by
  intro R _ _ D D' r W T
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB
    (φ' := fun v : (0 : Vec r →₀ ℤ).support => (vecHom T v.1).left) (ε' := fun v => (0 : Vec r →₀ ℤ) v.1)
    (fun U _ h => by simp) (LB.oneGen D.P.L (Y := (D'.P.A ⊗ D'.P.A).left)) (LB.isGen_oneGen _)
  refine ⟨t, ht, fun z J hJ => (hv _ _ z J hJ).trans (val_one _), fun z J hJ y y' => ?_⟩
  rw [hv _ _ z J hJ, val_one]
  simp

end GlobalTheory.TensBal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThPull
open GlobalTheory.ThetaPtMove

theorem thG_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)} {y : T ⟶ G} {c : Γ(T.left, ⊤)}
    (H : ThG G L ρ m θ y c) : ThG G L ρ m (VVRank.pullS G _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS G _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec G ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec G t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'

theorem thList_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  intro S G _ _ L ρ hL hρ m N K K' _ _ i x θ pt c H
  let β : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hβ : β.left = spMap i := Over.homMk_left _ _
  refine ⟨fun a => β ≫ pt a, fun a => by simp only [Over.comp_left, hβ], fun a b h => H.1 (TorsionFieldExt.comp_injective β _ h), fun a => ?_,
    fun F _ _ k => ?_⟩
  · have q := thG_pull hL hρ β (H.2.1 a)
    have e : β.left.appTop.hom (GlobalTheory.ZH.fn (c a)) = GlobalTheory.ZH.fn (i (c a)) :=
      (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
    rw [e] at q
    exact q
  · have e : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
    rw [e]
    intro p hp
    obtain ⟨a, ha⟩ := H.2.2 F (k.comp i) p hp
    refine ⟨a, ?_⟩
    rw [ha, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Over.comp_left, hβ, Category.assoc]

end GlobalTheory.UMin.ThPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescentStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → (letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra; IsGalois c.F d.c₂.F) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂)) ∧ (∀ (m : ℕ) (b : Fin m → cuspW Xo c U (wtZ a n)), LinearIndependent c.F b → LinearIndependent d.c₂.F (fun k => π (b k))) ∧ (∀ (σ₂ : d.c₂.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)), normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ (π f) = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))) f) ∧ (∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n)) ∧ (∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (Set.range π) ↔ FibConst d (g : Rul d.Xo₂ d.c₂)) ∧ ∀ (C : Submodule c.F (cuspW Xo c U (wtZ a n))), ∀ δ ∈ differentIdeal ℤ (𝓞 d.c₂.F), ∀ g ∈ latW U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n)))) → δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  first | exact @GlobalTheory.LevRingDesc.levRing_descent | exact GlobalTheory.LevRingDesc.levRing_descent | (intros; apply GlobalTheory.LevRingDesc.levRing_descent <;> assumption)
end


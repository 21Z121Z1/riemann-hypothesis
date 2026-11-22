import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsOfPullEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.SmallGlue
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmallGlue

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (q : Y ⟶ X)
    (h : GlobalTheory.CechPic.pull q (cls L hL) = 0) :
    ∃ a : ∀ j, Γ(Y, q ⁻¹ᵁ L.U j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : L.ι),
      q (f z) ∈ L.U i → q (f z) ∈ L.U j →
      gm f z (q ⁻¹ᵁ L.U i) (a i) = gm (f ≫ q) z (L.U i ⊓ L.U j) (L.g i j) * gm f z (q ⁻¹ᵁ L.U j) (a j) := by
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hL q)).1 h
  have le : ∀ j, q ⁻¹ᵁ L.U j ≤ (L.pull q).U (fun _ => j) := fun j y hy => mem_pull.2 hy
  refine ⟨fun j => res (le j) (t.s (fun _ => j)), fun Z f z i j hi hj => ?_⟩
  have hm : f z ∈ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have := congrArg (gm f z _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res _ z _ hm, gm_res _ z _ hm] at this
  rw [gm_res f z (le i) hi, gm_res f z (le j) hj]
  exact this.trans (congrArg (· * _) (gm_pull_g L q f z (fun _ => i) (fun _ => j) hm.1 hm.2))

theorem pullU_isGen_of_germ {X Y : Scheme.{0}} {L : LB X} (q : Y ⟶ X) (d : ∀ j, Γ(X, L.U j)ˣ) (i j : L.ι)
    (h : ∀ y : Y, q y ∈ L.U i → q y ∈ L.U j →
      gm (𝟙 Y) y (q ⁻¹ᵁ L.U i) (pullU q _ (d i)) =
        gm (𝟙 Y ≫ q) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (q ⁻¹ᵁ L.U j) (pullU q _ (d j))) :
    pullU q (L.U i ⊓ L.U j) (res inf_le_left (d i)) =
      pullU q (L.U i ⊓ L.U j) (L.g i j * res inf_le_right (d j)) := by
  refine unit_ext fun y hy => ?_
  have hm : q ((𝟙 Y : Y ⟶ Y) y) ∈ L.U i ⊓ L.U j := hy
  have e := h y hm.1 hm.2
  rw [gm_pull (𝟙 Y) q y _ hm.1, gm_pull (𝟙 Y) q y _ hm.2] at e
  rw [gm_pull (𝟙 Y) q y _ hm, gm_pull (𝟙 Y) q y _ hm, map_mul, gm_res (𝟙 Y ≫ q) y _ hm,
    gm_res (𝟙 Y ≫ q) y _ hm]
  exact e

theorem cech_patching : ∀ {X X₁ X₂ X₀ : Scheme.{0}} (ι₁ : X₁ ⟶ X) (ι₂ : X₂ ⟶ X) (ρ₁ : X₀ ⟶ X₁) (ρ₂ : X₀ ⟶ X₂), ρ₁ ≫ ι₁ = ρ₂ ≫ ι₂ →
    (∀ u : Γ(X₀, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : X₀, gm ρ₁ x ⊤ v = gm (𝟙 X₀) x ⊤ u) →
    (∀ (U : X.Opens) (a₁ : Γ(X₁, ι₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(X₂, ι₂ ⁻¹ᵁ U)ˣ),
      (∀ x : X₀, ρ₁ x ∈ ι₁ ⁻¹ᵁ U → gm ρ₁ x (ι₁ ⁻¹ᵁ U) a₁ = gm ρ₂ x (ι₂ ⁻¹ᵁ U) a₂) →
      ∃ d : Γ(X, U)ˣ, pullU ι₁ U d = a₁ ∧ pullU ι₂ U d = a₂) →
    (∀ (U : X.Opens) (d d' : Γ(X, U)ˣ), pullU ι₁ U d = pullU ι₁ U d' → pullU ι₂ U d = pullU ι₂ U d' → d = d') →
    ∀ c : Pic X, GlobalTheory.CechPic.pull ι₁ c = 0 → GlobalTheory.CechPic.pull ι₂ c = 0 → c = 0 := by
  intro X X₁ X₂ X₀ ι₁ ι₂ ρ₁ ρ₂ hsq hlift hpatch huniq c h₁ h₂
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨α, hα⟩ := exists_units_of_pull_eq_zero hL ι₁ h₁
  obtain ⟨β, hβ⟩ := exists_units_of_pull_eq_zero hL ι₂ h₂
  have pt : ∀ x : X₀, ι₂ (ρ₂ x) = ι₁ (ρ₁ x) := fun x => congrArg (fun g => g x) hsq.symm
  have le : ∀ j, ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ρ₂ ⁻¹ᵁ (ι₂ ⁻¹ᵁ L.U j) := fun j x hx => by
    show ι₂ (ρ₂ x) ∈ L.U j
    rw [pt]; exact hx
  have hu : ∀ j (x : X₀), ι₁ (ρ₁ x) ∈ L.U j →
      gm (𝟙 X₀) x (ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹) =
        gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ := fun j x hx => by
    rw [map_mul, map_inv, gm_res (𝟙 X₀) x (le j) hx, gm_pull (𝟙 X₀) ρ₁ x _ hx,
      gm_pull (𝟙 X₀) ρ₂ x _ (le j hx), Category.id_comp, Category.id_comp]
  obtain ⟨w, hw⟩ := glue_unit (⊤ : X₀.Opens) (fun j => ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (ι₁ (ρ₁ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩)
    (fun j => pullU ρ₁ _ (α j) * (res (le j) (pullU ρ₂ _ (β j)))⁻¹)
    (fun i j x hx => by
      refine (hu i x hx.1).trans (Eq.trans ?_ (hu j x hx.2).symm)
      rw [hα _ ρ₁ x i j hx.1 hx.2, hβ _ ρ₂ x i j (le i hx.1) (le j hx.2), hsq, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨v, hv⟩ := hlift w
  have hd : ∀ j, ∃ d : Γ(X, L.U j)ˣ, pullU ι₁ _ d = α j * (res le_top v)⁻¹ ∧ pullU ι₂ _ d = β j := fun j =>
    hpatch _ _ _ fun x hx => by
      have e : gm (𝟙 X₀) x ⊤ w = gm ρ₁ x _ (α j) * (gm ρ₂ x _ (β j))⁻¹ :=
        (gm_res (𝟙 X₀) x (le_top : ρ₁ ⁻¹ᵁ (ι₁ ⁻¹ᵁ L.U j) ≤ ⊤) hx w).symm.trans
          ((congrArg _ (hw j)).trans (hu j x hx))
      rw [map_mul, map_inv, gm_res ρ₁ x _ hx, hv, e, mul_inv, inv_inv, mul_inv_cancel_left]
  choose d hd₁ hd₂ using hd
  refine (cls_eq_zero_iff hL).2 ⟨⟨d⟩, fun i j => huniq _ _ _ ?_ ?_⟩
  · refine pullU_isGen_of_germ ι₁ d i j fun y hi hj => ?_
    rw [hd₁, hd₁, map_mul, map_mul, map_inv, map_inv, gm_res (𝟙 X₁) y _ hi, gm_res (𝟙 X₁) y _ hj,
      hα _ (𝟙 X₁) y i j hi hj, _root_.mul_assoc]
  · refine pullU_isGen_of_germ ι₂ d i j fun y hi hj => ?_
    rw [hd₂, hd₂]
    exact hβ _ (𝟙 X₂) y i j hi hj

end GlobalTheory.SmallGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVertOfMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_vert_of_mem (S : Type) [CommRing S] [IsDomain S] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp S) [IsDominant p] (f : S) (hf : f ≠ 0) (hx : ∃ x : X, f ∈ (p x).asIdeal) : ∃ z : X, Vert p f z := by
  obtain ⟨x, hfx⟩ := hx
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have key : ∀ q : PrimeSpectrum Γ(X, U), f ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom f ∈ q.asIdeal := by
    intro q
    have h : p (hU.fromSpec q) = (Spec.map φ) q := by
      rw [hφ]; rfl
    rw [h]; rfl
  have key' : ∀ y : U, f ∈ (p y.1).asIdeal ↔ φ.hom f ∈ (hU.primeIdealOf y).asIdeal := by
    intro y
    rw [← key, hU.fromSpec_primeIdealOf]
  have ha : φ.hom f ≠ 0 := by
    intro h0
    have hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.basicOpen f).isOpen
    have hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩
    obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open hO hne
    obtain ⟨w, hwU, hw⟩ := nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩
    have : f ∈ (p w).asIdeal := (key' ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)
    exact hw this
  have hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ((key' ⟨x, hx⟩).1 hfx)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hQp : Q.IsPrime := hQ.1.1
  have haQ : φ.hom f ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self _)
  have h1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have h0 : Q.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    exact ha (by simpa [h] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  let P : PrimeSpectrum Γ(X, U) := ⟨Q, hQp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  clear_value z
  letI := X.presheaf.algebra_section_stalk z
  haveI := hU.isLocalization_stalk z
  refine ⟨z.1, ?_, (key' z).2 (by rw [hP]; exact haQ)⟩
  have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
    (X.presheaf.stalk (z : X))
  rw [this, hP]
  change ((Q.height : ℕ∞) : WithBot ℕ∞) = 1
  rw [hQ1]; rfl

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
section
noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

def logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) :
    Submodule A (Derivation ℤ A A) where
  carrier := {D | (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun g hg => add_mem (h.2 g hg) (h'.2 g hg)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun g hg => Ideal.mul_mem_left _ r (h.2 g hg)⟩

theorem mem_logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) (D : Derivation ℤ A A) :
    D ∈ logSub φ J ↔ (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J := Iff.rfl

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S]
include f

def ext (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Classical.choose (GlobalTheory.LogDerLoc.exists_extension (B := S) f D)

theorem ext_algebraMap (D : Derivation ℤ R R) (r : R) :
    ext (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  Classical.choose_spec (GlobalTheory.LogDerLoc.exists_extension (B := S) f D) r

theorem der_ext (D₁ D₂ : Derivation ℤ S S) (h : ∀ r, D₁ (algebraMap R S r) = D₂ (algebraMap R S r)) :
    D₁ = D₂ := by
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
  have hu : IsUnit (algebraMap R S t) := IsLocalization.map_units S t
  have e' : y * algebraMap R S t = algebraMap R S r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : algebraMap R S t * D₁ y = algebraMap R S t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

def extL : Derivation ℤ R R →ₗ[R] Derivation ℤ S S where
  toFun := ext f
  map_add' D D' := der_ext f _ _ fun r => by
    rw [ext_algebraMap, Derivation.add_apply, Derivation.add_apply, ext_algebraMap, ext_algebraMap, map_add]
  map_smul' c D := der_ext f _ _ fun r => by
    rw [ext_algebraMap, RingHom.id_apply, Derivation.smul_apply, Derivation.smul_apply, ext_algebraMap,
      smul_eq_mul, map_mul, Algebra.smul_def]

theorem extL_algebraMap (D : Derivation ℤ R R) (r : R) :
    extL (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  ext_algebraMap f D r

variable {k : Type} [CommRing k]

def res (φ : k →+* R) (J : Ideal R) :
    logSub φ J →ₗ[R] (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R where
  toFun D := ⟨extL f D.1, fun a => by
      rw [RingHom.comp_apply, extL_algebraMap, D.2.1 a, map_zero],
    GlobalTheory.LogDerLoc.map_mem_map (algebraMap R S) D.1 (extL f D.1) (extL_algebraMap f D.1) J D.2.2⟩
  map_add' D D' := Subtype.ext (map_add (extL (S := S) f) D.1 D'.1)
  map_smul' c D := Subtype.ext (map_smul (extL (S := S) f) c D.1)

theorem res_apply (φ : k →+* R) (J : Ideal R) (D : logSub φ J) (r : R) :
    (res (S := S) f φ J D).1 (algebraMap R S r) = algebraMap R S (D.1 r) :=
  ext_algebraMap f D.1 r

end GlobalTheory.LogDerProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocallyNormalNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.ExtGlue

open GlobalTheory.GroupGlue

theorem exists_scheme_two {Y Y₀ Y₁ Y₂ : Scheme.{0}} {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] {q₁ : Y₀ ⟶ Y₁} {q₂ : Y₀ ⟶ Y₂} (hq : IsPullback q₁ q₂ f₁ f₂)
    {G₁ : Over Y₁} {G₂ : Over Y₂} {G₀ : Over Y₀} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom q₁) (h₂ : IsPullback φ₂ G₀.hom G₂.hom q₂) :
    ∃ (G : Over Y) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom f₁ ∧
      IsPullback ψ₂ G₂.hom G.hom f₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion q₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq.flip inferInstance
  have : IsOpenImmersion q₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq inferInstance
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ Y := pushout.desc (G₁.hom ≫ f₁) (G₂.hom ≫ f₂) (by
    rw [h₁.w_assoc, h₂.w_assoc, hq.w])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ f₁ := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ f₂ := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = f₁ (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = f₂ (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback hq y (G₂.hom x) (hy.trans (e2 x))
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x w hw.symm
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hq (G₁.hom x) y (hy.trans (e1 x)).symm
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x w hw.symm
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_semiAbelian_two {Y Y₀ Y₁ Y₂ : Scheme.{0}} {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [o₁ : IsOpenImmersion f₁]
    [o₂ : IsOpenImmersion f₂] {q₁ : Y₀ ⟶ Y₁} {q₂ : Y₀ ⟶ Y₂} (hq : IsPullback q₁ q₂ f₁ f₂)
    (hcov : ∀ y : Y, y ∈ Set.range f₁ ∨ y ∈ Set.range f₂)
    {G₁ : Over Y₁} [i₁ : GrpObj G₁] {G₂ : Over Y₂} [i₂ : GrpObj G₂] {G₀ : Over Y₀} [GrpObj G₀]
    {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left} (s₁ : IsSemiAbelian G₁) (s₂ : IsSemiAbelian G₂)
    (h₁ : IsGrpPullback G₀ G₁ q₁ φ₁) (h₂ : IsGrpPullback G₀ G₂ q₂ φ₂) :
    ∃ (G : Over Y) (_ : GrpObj G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧
      IsGrpPullback G₁ G f₁ ψ₁ ∧ IsGrpPullback G₂ G f₂ ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme_two hq h₁.1 h₂.1
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ Y₁} {v : S ⟶ Y₂} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ w : S ⟶ Y₀, w ≫ q₁ = u ∧ w ≫ q₂ = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    have e : u ≫ f₁ = v ≫ f₂ := by
      rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
    exact ⟨hq.lift u v e, hq.lift_fst _ _ _, hq.lift_snd _ _ _⟩
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ Y₀) (a : Over.mk (w ≫ q₁) ⟶ G₁) (b : Over.mk (w ≫ q₂) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ Y₁} {v : S ⟶ Y₂} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec Y₁ Y₂ i
  let t : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) f₁ f₂ i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    exacts [o₁, o₂]
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hcov x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  exact ⟨G, iG, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ⟩

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {k : S'' ⟶ S} (w : g ≫ f = k) {F : G''.left ⟶ G.left}
    (h : IsGrpPullback G'' G k F) : ∃ e, IsGrpPullback G'' ((Over.pullback f).obj G) g e := by
  subst w
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor f g h⟩

theorem isDominant_of_isPullback {X X₁ Y Y₁ : Scheme.{0}} {k : X₁ ⟶ X} {j₁ : X₁ ⟶ Y₁} {j : X ⟶ Y} {f : Y₁ ⟶ Y}
    [IsOpenImmersion f] (hj : IsDominant j) (h : IsPullback k j₁ j f) : IsDominant j₁ := by
  refine ⟨(hj.denseRange.preimage f.isOpenEmbedding.isOpenMap).mono ?_⟩
  rintro y ⟨x, hx⟩
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback h x y hx
  exact ⟨z, hz⟩

theorem isNoetherian_of_isOpenImmersion {Y S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (f : Y ⟶ S)
    [IsOpenImmersion f] : AlgebraicGeometry.IsNoetherian Y := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion f
  have : TopologicalSpace.NoetherianSpace Y := f.isOpenEmbedding.isInducing.noetherianSpace
  exact {}

theorem hasExt_two {X X₁ Y Y₁ Y₂ : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y₁]
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₁) {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] (hcov : ∀ y : Y, y ∈ Set.range f₁ ∨ y ∈ Set.range f₂) {j₂ : X ⟶ Y₂} {k : X₁ ⟶ X}
    {j₁ : X₁ ⟶ Y₁} [IsOpenImmersion j₁] [IsDominant j₁] (w : k ≫ j₂ ≫ f₂ = j₁ ≫ f₁) {A : Over X} [GrpObj A]
    (h₁ : HasExt j₁ ((Over.pullback k).obj A)) (h₂ : HasExt j₂ A) : HasExt (j₂ ≫ f₂) A := by
  obtain ⟨G₁, i₁, e₁, s₁, g₁⟩ := h₁
  obtain ⟨G₂, i₂, e₂, s₂, g₂⟩ := h₂
  let j₀ : X₁ ⟶ pullback f₁ f₂ := pullback.lift j₁ (k ≫ j₂) (by rw [Category.assoc, w])
  have w₁ : j₀ ≫ pullback.fst f₁ f₂ = j₁ := pullback.lift_fst _ _ _
  have w₂ : j₀ ≫ pullback.snd f₁ f₂ = k ≫ j₂ := pullback.lift_snd _ _ _
  have : IsOpenImmersion (j₀ ≫ pullback.fst f₁ f₂) := by rw [w₁]; infer_instance
  have : IsOpenImmersion j₀ := IsOpenImmersion.of_comp j₀ (pullback.fst f₁ f₂)
  have : IsDominant (j₀ ≫ pullback.fst f₁ f₂) := by rw [w₁]; infer_instance
  have : IsDominant j₀ := IsDominant.of_comp_of_isOpenImmersion j₀ (pullback.fst f₁ f₂)
  have := isNoetherian_of_isOpenImmersion (pullback.fst f₁ f₂)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have hn₀ := GlobalTheory.IsNormalScheme.of_isOpenImmersion (pullback.fst f₁ f₂)
  obtain ⟨a₁, ha₁⟩ := exists_factor _ _ w₁ g₁
  obtain ⟨a₂, ha₂⟩ := exists_factor _ _ w₂ ((isGrpPullback_pullback A k).comp g₂)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsSemiAbelian.pullback _ G₁ s₁) (IsSemiAbelian.pullback _ G₂ s₂) ha₁ ha₂
  obtain ⟨G, iG, ψ₁, ψ₂, s, -, g, -⟩ := exists_semiAbelian_two (IsPullback.of_hasPullback f₁ f₂) hcov s₁ s₂
    (isGrpPullback_pullback G₁ _)
    (((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso E).comp (isGrpPullback_pullback G₂ _)).congr
      (Category.id_comp _) rfl)
  exact ⟨G, iG, e₂ ≫ ψ₂, s, g₂.comp g⟩

theorem hasExt_of_locally : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A)) → HasExt j A := by
  intro X S _ hn j _ hj A _ hA hloc
  classical
  choose U hU hE using hloc
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have key : ∀ t : Finset S, ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (_ : IsOpenImmersion f) (i : X ⟶ Y), i ≫ f = j ∧
      HasExt i A ∧ ∀ s ∈ t, (U s : Set S) ⊆ Set.range f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨X, j, inferInstance, 𝟙 X, Category.id_comp _, ⟨A, inferInstance, _, isSemiAbelian_of_isAbelianScheme A hA,
        @ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso _ A A _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))⟩,
        by simp⟩
    | insert s t _ ih =>
      obtain ⟨Y, f, _, i, hi, hext, ht⟩ := ih
      let W : S.Opens := U s ⊔ f.opensRange
      have r₂ : Set.range f ⊆ Set.range W.ι := by
        rw [Scheme.Opens.range_ι]
        exact fun y hy => Or.inr hy
      let f₁ : (U s).toScheme ⟶ W.toScheme := S.homOfLE le_sup_left
      let f₂ : Y ⟶ W.toScheme := IsOpenImmersion.lift W.ι f r₂
      have w₁ : f₁ ≫ W.ι = (U s).ι := Scheme.homOfLE_ι _ _
      have w₂ : f₂ ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
      have : IsOpenImmersion (f₂ ≫ W.ι) := by rw [w₂]; infer_instance
      have : IsOpenImmersion f₂ := IsOpenImmersion.of_comp f₂ W.ι
      have := isNoetherian_of_isOpenImmersion (U s).ι
      have : IsDominant (j ∣_ U s) := isDominant_of_isPullback hj (isPullback_morphismRestrict j (U s)).flip
      refine ⟨W, W.ι, inferInstance, i ≫ f₂, by rw [Category.assoc, w₂, hi], ?_, ?_⟩
      · refine hasExt_two (f₁ := f₁) (GlobalTheory.IsNormalScheme.pred _) ?_ ?_ (hE s) hext
        · rintro ⟨y, hy | ⟨z, hz⟩⟩
          · exact Or.inl ⟨⟨y, hy⟩, W.ι.isOpenEmbedding.injective (congrArg (fun g => g ⟨y, hy⟩) w₁)⟩
          · exact Or.inr ⟨z, W.ι.isOpenEmbedding.injective ((congrArg (fun g => g z) w₂).trans hz)⟩
        · rw [← cancel_mono W.ι]
          simp only [Category.assoc, w₁, w₂, hi, morphismRestrict_ι]
      · intro s' hs'
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · rw [Scheme.Opens.range_ι]
          exact fun y hy => Or.inl hy
        · exact (ht s' hs').trans r₂
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s : S => (U s : Set S)) (fun s => (U s).isOpen)
    (fun s _ => Set.mem_iUnion.2 ⟨s, hU s⟩)
  obtain ⟨Y, f, _, i, hi, ⟨G, iG, e, s, g⟩, hf⟩ := key t
  have : Surjective f := ⟨fun y => by
    obtain ⟨s, hs, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact hf s hs hy⟩
  have : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨a, ha⟩ := exists_factor (inv f) j (k := i) (by rw [← hi]; simp) g
  exact ⟨_, inferInstance, a, IsSemiAbelian.pullback _ G s, ha⟩

end GlobalTheory.ExtGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyExpLogCoverBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.TanPtMod

namespace GlobalTheory.UPel.HT.ES.WTors

theorem killedBy_iff_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy o w x := by
  constructor
  · intro h a ha
    exact h _ (Ideal.mem_map_of_mem _ ha)
  · intro h a ha
    simp only [GlobalTheory.IwLevel.htAct_act]
    refine Submodule.span_induction (p := fun y _ => x ≫ o.act.act y = 1) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨c, hc, rfl⟩
      exact h c hc
    · have h0 : o.act.act 0 = 1 := by
        have := o.act.add 0 0
        rw [add_zero] at this
        exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
      rw [h0, comp_one]
    · intro y z _ _ hy hz
      rw [o.act.add, comp_mul, hy, hz, _root_.mul_one]
    · intro c y _ hy
      haveI := o.act.hom c
      rw [smul_eq_mul, o.act.mul, ← Category.assoc, hy, one_comp]

end GlobalTheory.UPel.HT.ES.WTors
end


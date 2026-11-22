import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointScheme
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.KerSch

theorem exists_lift_of_finite {k : Type} [Field k] [IsAlgClosed k] {Y Z : Scheme.{0}} (q : Y ⟶ Z)
    [IsFinite q] [Surjective q] (x : Sp k ⟶ Z) : ∃ y : Sp k ⟶ Y, y ≫ q = x := by
  have : CompactSpace ↥(pullback q x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  obtain ⟨p, -⟩ := (pullback.snd q x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z hz ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_lift_ext {k : Type} [Field k] {Y Z : Scheme.{0}} (f : Y ⟶ Z) (u : Sp k ⟶ Z) (t : Sp k) (y₀ : Y)
    (h : f y₀ = u t) : ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (a : Sp k' ⟶ Sp k) (y : Sp k' ⟶ Y),
      Epi a ∧ y ≫ f = a ≫ u := by
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₀ t h
  obtain ⟨k', _, _, z, -⟩ := exists_geomPt_range_eq (pullback f u) w
  refine ⟨k', inferInstance, inferInstance, z ≫ pullback.snd f u, z ≫ pullback.fst f u, ?_, ?_⟩
  · generalize z ≫ pullback.snd f u = a
    have : Surjective a := ⟨fun x => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have : Flat a := inferInstance
    exact Flat.epi_of_flat_of_surjective a
  · rw [Category.assoc, Category.assoc, pullback.condition]

section

variable {A X G₁ Z GY Y : Scheme.{0}} {α : A ⟶ X} {g₁ : G₁ ⟶ Z} {gY : GY ⟶ Y} {φ : G₁ ⟶ A} {ψ : GY ⟶ G₁}
  {π : Z ⟶ X} {q : Y ⟶ Z} {n : ℕ} {σ : Fin n → (Y ⟶ GY)}

theorem range_subset_iff (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y : Sp k ⟶ Y) (u : Sp k ⟶ G₁) (hu : u ≫ g₁ = y ≫ q) :
    Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) ↔ ∃ j, u = y ≫ σ j ≫ ψ := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := h ⟨(default : PrimeSpectrum k), rfl⟩
    obtain ⟨j, y₀, rfl⟩ := Set.mem_iUnion.1 hw
    obtain ⟨k', _, _, a, y', ha, e'⟩ := exists_lift_ext (σ j ≫ ψ) u _ y₀ (by rw [Scheme.Hom.comp_apply]; exact e)
    have e₁ : y' ≫ q = (a ≫ y) ≫ q := by
      rw [Category.assoc, ← hu, ← reassoc_of% e', hs j]
    have e₂ : y' ≫ σ j ≫ ψ ≫ φ ∈ Set.range (fun j => (a ≫ y) ≫ σ j ≫ ψ ≫ φ) := hfib k' _ _ e₁ ▸ ⟨j, rfl⟩
    obtain ⟨j', e₃⟩ := e₂
    refine ⟨j', h₁.hom_ext ?_ ?_⟩
    · rw [← cancel_epi a, ← reassoc_of% e']
      simpa using e₃.symm
    · simp only [Category.assoc, hs, hu]
  · rintro ⟨j, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨σ j (y t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, by simp⟩

theorem preimage_eq (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {GT T : Scheme.{0}} {gT : GT ⟶ T} {ν : GT ⟶ G₁} {h : T ⟶ Y} (h₃ : IsPullback ν gT g₁ (h ≫ q))
    {τ : Fin n → (T ⟶ GT)} (hτ : ∀ j, τ j ≫ gT = 𝟙 T) (hh : ∀ j, τ j ≫ ν = h ≫ σ j ≫ ψ) :
    (⋃ j, Set.range (τ j)) = ν ⁻¹' (ψ '' (⋃ j, Set.range (σ j))) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.1 hw
    refine ⟨σ j (h t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hh]
  · intro hw
    obtain ⟨k, _, _, z, hz⟩ := exists_geomPt_range_eq GT w
    have hzw : ∀ t, z t = w := fun t => by
      have : z t ∈ Set.range z := ⟨_, rfl⟩
      rwa [hz] at this
    obtain ⟨t₀⟩ : Nonempty (Sp k) := ⟨(default : PrimeSpectrum k)⟩
    obtain ⟨j, e⟩ := (range_subset_iff h₁ h₂ hσ hfib (z ≫ gT ≫ h) (z ≫ ν) (by simp [h₃.w])).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply, hzw]
      exact hw)
    have e' : z = z ≫ gT ≫ τ j := h₃.hom_ext (by simp [e, hh]) (by simp [hτ])
    refine Set.mem_iUnion.2 ⟨j, gT w, ?_⟩
    rw [← hzw t₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e']

theorem range_subset_range (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y y' : Sp k ⟶ Y) (e : y ≫ q ≫ π = y' ≫ q ≫ π)
    (H : ∀ u u' : Sp k ⟶ G₁, u ≫ g₁ = y ≫ q → u' ≫ g₁ = y' ≫ q → u ≫ φ = u' ≫ φ →
      Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) → Set.range u' ⊆ ψ '' (⋃ j, Set.range (σ j))) :
    Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) ⊆ Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ) := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  rintro _ ⟨j, rfl⟩
  have w : (y ≫ σ j ≫ ψ ≫ φ) ≫ α = (y' ≫ q) ≫ π := by
    simp only [Category.assoc, h₁.w, reassoc_of% hs, e]
  have hu : (y ≫ σ j ≫ ψ) ≫ g₁ = y ≫ q := by simp only [Category.assoc, hs]
  have := H (y ≫ σ j ≫ ψ) (h₁.lift _ _ w) hu (h₁.lift_snd _ _ _) (by simp)
    ((range_subset_iff h₁ h₂ hσ hfib y _ hu).2 ⟨j, rfl⟩)
  obtain ⟨j', e'⟩ := (range_subset_iff h₁ h₂ hσ hfib y' _ (h₁.lift_snd _ _ w)).1 this
  refine ⟨j', ?_⟩
  have := h₁.lift_fst _ _ w
  rw [e'] at this
  simpa using this

end

end GlobalTheory.HkFam.KerSch

namespace GlobalTheory.HkFam

open KerSch

theorem exists_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  obtain ⟨Y, Hk, q, π₁, oY, m, σ, K, hqf, hqe, hqs, hπf, hπe, hL, hK, hfib, huniv⟩ :=
    GlobalTheory.T.exists_heckeKernelLists_modulo_permutations E H D l Xo 𝔓 p i (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hA
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (π₁ ≫ Xo.s) π₁ rfl rfl
    (by simp [spMap]) Xo.univ
  obtain ⟨m', hm'⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ oY).2 π₁ q m₁).2 m
  have h₁ := m₁.cart.1
  have h₂ := m'.cart.1
  have hσ : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w (σ j)
  rw [hm'] at hfib
  have hfib' := fun (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y) e => ((hfib k y y').1 e).1
  have hKσ := hL.2.1
  have hpre : K = m'.toSABMap.φ ⁻¹' (m'.toSABMap.φ '' K) := by
    have := preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' (h := 𝟙 Y) (ν := m'.toSABMap.φ)
      (gT := oY.t.G.hom) (by simpa using h₂) (τ := fun j => (σ j).left) hσ (fun j => by simp)
    rw [hKσ]; exact this
  refine ⟨Hk, π₁, o₁, m₁, m'.toSABMap.φ '' K, hπf, hπe, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.heckeSet_descends E H D l 𝔓 p i _ _ _ _ q o₁ oY m' _ hA hqs (hpre ▸ hK)
  · refine etSet_of_lists _ _ q _ _ m'.toSABMap.φ (p ^ 2) _ σ _ (ObjDim.isAbelianScheme o₁) m'.cart ?_ hqf hqe hqs
      (hpre ▸ hL)
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ (π₁ ≫ Xo.s).appTop).hom
    rwa [map_natCast] at this
  · intro k _ _ z z' e h
    obtain ⟨y, rfl⟩ := exists_lift_of_finite q z
    obtain ⟨y', rfl⟩ := exists_lift_of_finite q z'
    rw [Category.assoc, Category.assoc] at e
    rw [hKσ] at h
    refine (hfib k y y').2 ⟨subset_antisymm ?_ ?_, e⟩
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y y' e fun u u' hu hu' e' =>
        (h (Over.homMk u hu) (Over.homMk u' hu') e').1
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y' y e.symm fun u u' hu hu' e' =>
        (h (Over.homMk u' hu') (Over.homMk u hu) e'.symm).2
  · intro T s o f mu τ K' hL' hK'
    obtain ⟨h, hf, hh⟩ := huniv T f o.t mu.toSABMap τ K' hL' hK'
    rw [← Category.assoc] at hf
    subst hf
    obtain ⟨n, hn⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ (h ≫ q) m₁).2 mu
    have h₃ := n.cart.1
    have hτ : ∀ j, (τ j).left ≫ o.t.G.hom = 𝟙 T := fun j => Over.w (τ j)
    refine ⟨h ≫ q, n, rfl, hn.symm, ?_⟩
    rw [hL'.2.1, hKσ]
    refine preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' h₃ (τ := fun j => (τ j).left) hτ fun j => ?_
    refine h₁.hom_ext ?_ ?_
    · have := hh j
      rw [hm', hn] at this
      simpa using this.symm
    · have e₁ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (h ≫ q)) (hτ j))
      have e₂ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) (hσ j))
      simp only [Category.assoc, h₃.w, h₂.w]
      exact (e₁.trans (Category.id_comp _)).trans (congrArg (h ≫ ·) (e₂.trans (Category.id_comp _)).symm)

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFamily_over_thetaPointScheme : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ Y : MMPre n (n ^ j) (thIdeal em C), ∃ t : TObj g ((n ^ j) ^ 2) J b Y.s, Dense (fromSet em C t) ∧ t.Shape Mat κ ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v ↔ SecCoord Y.de Y.th x v) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' t x := by
  first | exact @GlobalTheory.ZM.exists_family_over_MMPre | exact GlobalTheory.ZM.exists_family_over_MMPre | (intros; apply GlobalTheory.ZM.exists_family_over_MMPre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionHomImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsRepMap

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare GlobalTheory.TorusModel GlobalTheory.FieldRestrictionTest

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem isIota_zero {F : Type} [Field F] [Algebra (FractionRing R) F] (hB : D.TauBimult) {h : GtPtF D F}
    (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isZero_iff h).1 hh
  refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

variable {Gt : Over (Sp R)} [GrpObj Gt] {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem nsmul_eq (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) {h : GtPt D T}
    (H : GtPt.IsNsmul k (Φ T x) h) : h = Φ T (x ^ k) := by
  obtain ⟨u, u0, us, rfl⟩ := H
  have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
    induction i using Fin.induction with
    | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
    | succ i ih =>
      have h := us i
      rw [ih] at h
      rw [Fin.val_succ, pow_succ]
      exact isAdd_unique h (hΦ.2 T _ _)
  exact this (Fin.last k)

theorem iota_pull_eq {W : (Sp R).Opens} {ψW : PsiOn D W} {T T' : Over W.toScheme} (h₁ h₂ : T' ⟶ T) {y : D.X}
    {g : GtPt D (overW W T)} (hg : GtPt.IsIotaW ψW y g) {g₁ g₂ : GtPt D (overW W T')}
    (H₁ : GtPt.IsPull ((Over.map W.ι).map h₁).left g g₁) (H₂ : GtPt.IsPull ((Over.map W.ι).map h₂).left g g₂) :
    g₁ = g₂ := by
  have key : ∀ (h : T' ⟶ T) (g' : GtPt D (overW W T')), GtPt.IsPull ((Over.map W.ι).map h).left g g' →
      g'.b = DegPre.cT D _ y ∧ ∀ χ z J, Good D.P.L z J →
        val (g'.s χ) (𝟙 _) z J = val (ψW.tau y χ) T'.hom z J := fun h g' H => by
    refine ⟨?_, fun χ z J hJ => ?_⟩
    · have : g'.b = (Over.map W.ι).map h ≫ g.b := Over.OverMorphism.ext H.1
      rw [this, hg.1, DegPre.cT, comp_toUnit_assoc]
    · refine (val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hg.2 χ) _).trans
        ((val_pull hJ _ _ _).trans ?_)))
      rw [Category.id_comp]
      exact congrArg (fun m => val (ψW.tau y χ) m z J) (Over.w h)
  obtain ⟨a₁, b₁⟩ := key h₁ g₁ H₁
  obtain ⟨a₂, b₂⟩ := key h₂ g₂ H₂
  exact pt_ext (a₁.trans a₂.symm) fun χ z J hJ => (b₁ χ z J hJ).trans (b₂ χ z J hJ).symm

theorem isPullF_iff_eq (hΦ : Represents Φ) {F : Type} [Field F] [Algebra (FractionRing R) F] {T : Over (Sp R)}
    (σ : TF (R := R) F ⟶ T) (x : T ⟶ Gt) (g : GtPtF D F) :
    GtPt.IsPullF F σ.left (Φ T x) g ↔ toT g = Φ _ (σ ≫ x) :=
  ⟨fun H => isPull_unique (k := σ) H (hΦ.1 _ _ σ x), fun H => (isPullF_iff_isPull _ _ _).2 (H ▸ hΦ.1 _ _ σ x)⟩

end Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem isImage_mul {P : PELUnif I t} (hP : P.TorsionIso) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k) {q q' q'' : QkPt P.D.toPre F k} (hq : QkAdd q q' q'')
    {v v' v'' : TF (R := R) F ⟶ t.G} (h : IsImage P F k q v.left) (h' : IsImage P F k q' v'.left)
    (h'' : IsImage P F k q'' v''.left) : v'' = v * v' := by
  obtain ⟨f, f1, -, -, f4, -⟩ := hP F k hk
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.LevelRatio.exists_ptsEquiv P.U.toUnifPre F
  have key : ∀ {q : QkPt P.D.toPre F k} {v : TF (R := R) F ⟶ t.G}, IsImage P F k q v.left → v = Ψ (f q) := by
    rintro q v ⟨a, e, ha⟩
    obtain rfl := (f1 _ _).1 ha
    exact Over.OverMorphism.ext (e.symm.trans (hΨ _).symm)
  rw [key h, key h', key h'', f4 _ _ _ hq, map_mul]

theorem exists_repMap : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ v : overW W N ⟶ t.G, v ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F (overW W N) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F x p₀ q → IsImage P F k q (x ≫ v.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk y N p₀ hN
  have := hR.1
  have := hR.2.2.1
  have hP := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR t P
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.generic_part_image_pullback E H R hR t P W hW hp ψW k hk y N p₀ hN
  obtain ⟨Z, g₀, x₀, z1, z2, -, z3, z4, z5, z6⟩ := GlobalTheory.FlatTors.exists_torsion_toG E H R hR t P W hW hp ψW k hk
  have hZ : IsFinitePart P.U.toUnifPre k Z g₀ x₀ :=
    ⟨z1, z2, z3, z4, z5, GlobalTheory.TorsMono.mono_torsion E H R hR t P W hW hp ψW k hk Z g₀ x₀ z1 z3 z4 z6,
      GlobalTheory.FiniteTorsLift.main E H R hR t P W hW hp ψW k hk Z g₀ x₀ z1 z3 z4 z6, z6⟩
  have hgen := GlobalTheory.T.finite_part_image_generic E H R hR t P W hW hp ψW k hk Z g₀ x₀ hZ
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨c₀, rfl⟩ := (Φ Z).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 z3
  obtain ⟨c, hc⟩ := (Φ (overW W N)).surjective p₀.g
  let n₁ : overW W (N ⊗ N) ⟶ overW W N := (Over.map W.ι).map (fst N N)
  let n₂ : overW W (N ⊗ N) ⟶ overW W N := (Over.map W.ι).map (snd N N)
  have hk₀ : GtPt.IsIotaW ψW p₀.y (Φ _ (c ^ k)) := by
    obtain ⟨h, h1, h2⟩ := p₀.eq
    rw [← hc] at h1
    rwa [nsmul_eq hΦ k c h1] at h2
  have hpow : n₁ ≫ c ^ k = n₂ ≫ c ^ k :=
    (Φ _).injective (iota_pull_eq (fst N N) (snd N N) hk₀ (hΦ.1 _ _ _ _) (hΦ.1 _ _ _ _))
  have hδ : ((n₂ ≫ c)⁻¹ * (n₁ ≫ c)) ^ k = 1 := by
    rw [mul_pow, inv_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, hpow, inv_mul_cancel]
  obtain ⟨e, he, -⟩ := z4 _ _ ((tors_iff hΦ k _).2 hδ)
  have he' : e ≫ c₀ = (n₂ ≫ c)⁻¹ * (n₁ ≫ c) := (isPull_iff_comp hΦ _ _ _).1 he
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.T.torsion_descent_finite_etale_cover R W t.G k t.semi.separated
    (GlobalTheory.T.torsion_representable_finite_etale E H R hR t P W hW hp ψW k hk).2.1 N hN.1 hN.2.1 u (e ≫ x₀) hu
    (by rw [← MonObj.comp_pow, z5, MonObj.comp_one]) (fun F _ _ _ a b s ha hb => by
      obtain ⟨qa, hqa, -⟩ := (existsUnique_pair_iff (F := F) (a ≫ genι (overW W N)).left p₀).2
        (Over.w (a ≫ genι (overW W N)))
      obtain ⟨qb, hqb, -⟩ := (existsUnique_pair_iff (F := F) (b ≫ genι (overW W N)).left p₀).2
        (Over.w (b ≫ genι (overW W N)))
      obtain ⟨g, hg⟩ := exists_isPullF (s ≫ e) (Φ Z c₀)
      obtain ⟨h, h1, h2⟩ := z3
      obtain ⟨h', hh⟩ := exists_isPullF (s ≫ e) h
      let qd : QkPt P.D.toPre F k := ⟨0, g, h', isNsmul_restrict hg hh h1,
        isIota_zero P.D.tau_bimult (isZero_restrict hh h2)⟩
      have ia : IsImage P F k qa (a ≫ u).left := hu' F a.left (Over.w a) qa hqa
      have ib : IsImage P F k qb (b ≫ u).left := hu' F b.left (Over.w b) qb hqb
      have id : IsImage P F k qd (s ≫ e ≫ x₀).left := by
        rw [← Category.assoc]
        exact hgen F (s ≫ e).left (Over.w _) qd rfl hg
      refine isImage_mul hP hk ⟨qa, ?_, ?_, qk_equiv_refl P.D.tau_bimult qa⟩ ib id ia
      · exact hqa.1.trans (hqb.1.symm.trans (add_zero _).symm)
      · have ea := hqa.2
        have eb := hqb.2
        rw [← hc] at ea eb
        rw [isPullF_iff_eq hΦ] at ea eb hg
        have add := hΦ.2 _ ((b ≫ genι (overW W N)) ≫ c) ((s ≫ e) ≫ c₀)
        have em : ((b ≫ genι (overW W N)) ≫ c) * ((s ≫ e) ≫ c₀) = (a ≫ genι (overW W N)) ≫ c := by
          rw [← ha, ← hb, Category.assoc, Category.assoc, Category.assoc, he', ← MonObj.comp_mul,
            mul_inv_cancel_left]
        rw [em, ← ea, ← eb, ← hg] at add
        exact add)
  refine ⟨v, hv, fun F _ _ _ x hx q hq => ?_⟩
  let x' : Sp F ⟶ (genPart (overW W N)).left := pullback.lift x (jFK (R := R) F) hx
  have e₁ : x' ≫ (genι (overW W N)).left = x := pullback.lift_fst _ _ _
  have := hu' F x' (by
    show x' ≫ (genι (overW W N)).left ≫ _ = _
    rw [← Category.assoc, e₁]
    exact hx) q (e₁.symm ▸ hq)
  rwa [← hv', Over.comp_left, ← Category.assoc, e₁] at this

end GlobalTheory.TorsRepMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem desc_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (h : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [h]; simp [spMap]) o

theorem desc_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') :
    ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem desc_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (m : ObjMap o' o f)
    (m'' : ObjMap o'' o g) (e : f' ≫ f = g) :
    ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  subst e
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem desc_cocycle (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S']
    {s : S ⟶ Sp (KA l)} (π : S' ⟶ S) [Etale π] (o : Ob D l s) (o' o₂' : Ob D l (π ≫ s)) (m : ObjMap o' o π)
    (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K) (ψ' : o'.t.G ⟶ o₂'.t.G)
    (hψ : IsIsog o' o₂' p ψ') (hker : KerSet ψ' (m.toSABMap.φ ⁻¹' K)) (f' : S' ⟶ Xo.X) (hf' : f' ≫ Xo.s = π ≫ s)
    (n' : ObjMap o₂' Xo.univ f') :
    (∀ {Z : Scheme.{0}} (x y : Z ⟶ S'), x ≫ π = y ≫ π → x ≫ f' = y ≫ f') ∧
    ∀ {Z : Scheme.{0}} (x y : Z ⟶ o'.t.G.left), x ≫ m.toSABMap.φ = y ≫ m.toSABMap.φ →
      x ≫ ψ'.left ≫ n'.toSABMap.φ = y ≫ ψ'.left ≫ n'.toSABMap.φ := by
  have hab : pullback.fst π π ≫ π = pullback.snd π π ≫ π := pullback.condition
  haveI : IsReduced (pullback π π) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  obtain ⟨oT, ⟨mT⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π ≫ π) (by simp) o
  obtain ⟨ma, hma⟩ := desc_cancel (f' := pullback.fst π π) m mT rfl
  obtain ⟨mb, hmb⟩ := desc_cancel (f' := pullback.snd π π) m mT hab.symm
  obtain ⟨oa, ⟨na⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π) rfl o₂'
  obtain ⟨ob, ⟨nb⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.snd π π)
    (by rw [reassoc_of% hab]) o₂'
  obtain ⟨⟨ψa, hψa, -⟩, Ha⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT oa ma na ψ'
  obtain ⟨⟨ψb, hψb, -⟩, Hb⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT ob mb nb ψ'
  obtain ⟨ia, ka⟩ := Ha ψa hψa
  obtain ⟨ib, kb⟩ := Hb ψb hψb
  have ka' : KerSet ψa (mT.toSABMap.φ ⁻¹' K) := by
    have := ka _ hψ.1.1 hker
    rw [hma]; simpa [Set.preimage_comp] using this
  have kb' : KerSet ψb (mT.toSABMap.φ ⁻¹' K) := by
    have := kb _ hψ.1.1 hker
    rw [hmb]; simpa [Set.preimage_comp] using this
  have hKT : HeckeSet D oT.t 𝔓 p i (mT.toSABMap.φ ⁻¹' K) :=
    ((GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t oT.t _ mT.toSABMap o.proper).2 K).1 hK
  obtain ⟨na', hna⟩ := desc_comp n' na
  obtain ⟨nb', hnb⟩ := desc_comp n' nb
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i _ _ oT oa ob ψa ψb _ _ _ na' nb' hA hKT
    (by rw [Category.assoc, hf']) (by rw [Category.assoc, hf', reassoc_of% hab]) (ia hψ) (ib hψ) ka' kb'
  rw [hna, hnb, reassoc_of% hψa, reassoc_of% hψb] at e₂
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have := pullback.lift x y hxy ≫= e₁
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  · have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
    have pa : IsPullback ma.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.fst π π) := ma.cart.1
    have pb : IsPullback mb.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.snd π π) := mb.cart.1
    have h₀ : (x ≫ o'.t.G.hom) ≫ π = (y ≫ o'.t.G.hom) ≫ π := by
      simp only [Category.assoc, ← pm.w, reassoc_of% hxy]
    let w := pa.lift x (pullback.lift _ _ h₀) (pullback.lift_fst _ _ _).symm
    have wa : w ≫ ma.toSABMap.φ = x := pa.lift_fst _ _ _
    have wb : w ≫ mb.toSABMap.φ = y := by
      apply pm.hom_ext
      · rw [Category.assoc, ← hmb, hma, reassoc_of% wa, hxy]
      · rw [Category.assoc, pb.w, pa.lift_snd_assoc, pullback.lift_snd]
    rw [← wa, ← wb, Category.assoc, Category.assoc, e₂]

theorem hasQuot_descend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (π : S' ⟶ S) (o : Ob D l s) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → Etale π → Surjective π → QuasiCompact π → HasQuot o' p (m.toSABMap.φ ⁻¹' K) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S S' _ s π o o' m K hA hK hE hS hQ ⟨o₂', ψ', hψ, hker⟩
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  obtain ⟨f', ⟨hf', ⟨n'⟩⟩, -⟩ := Xo.rep S' (π ≫ s) inferInstance o₂'
  obtain ⟨c₁, c₂⟩ := desc_cocycle Xo 𝔓 p i π o o' o₂' m K hA hK ψ' hψ hker f' hf' n'
  have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
  have pn' : IsPullback n'.toSABMap.φ o₂'.t.G.hom Xo.univ.t.G.hom f' := n'.cart.1
  haveI : Flat m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip (inferInstance : Flat π)
  haveI : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hS
  haveI : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hQ
  haveI : EffectiveEpi π := inferInstance
  haveI : EffectiveEpi m.toSABMap.φ := inferInstance
  obtain ⟨f, hf⟩ : ∃ f : S ⟶ Xo.X, π ≫ f = f' := ⟨_, EffectiveEpi.fac π f' c₁⟩
  obtain ⟨h, hh⟩ : ∃ h, m.toSABMap.φ ≫ h = ψ'.left ≫ n'.toSABMap.φ := ⟨_, EffectiveEpi.fac _ _ c₂⟩
  have hfs : f ≫ Xo.s = s := by rw [← cancel_epi π, reassoc_of% hf, hf']
  obtain ⟨o₂, ⟨n⟩⟩ := desc_pull s f hfs Xo.univ
  obtain ⟨n₂, hn₂⟩ := desc_cancel n n' hf
  have pn : IsPullback n.toSABMap.φ o₂.t.G.hom Xo.univ.t.G.hom f := n.cart.1
  have pn₂ : IsPullback n₂.toSABMap.φ o₂'.t.G.hom o₂.t.G.hom π := n₂.cart.1
  have hw : h ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ f := by
    rw [← cancel_epi m.toSABMap.φ, reassoc_of% hh, pn'.w, pm.w_assoc, hf, Over.w_assoc]
  let ψ : o.t.G ⟶ o₂.t.G := Over.homMk (pn.lift h _ hw) (pn.lift_snd _ _ _)
  have hψn : ψ.left ≫ n.toSABMap.φ = h := pn.lift_fst _ _ _
  have sq : ψ'.left ≫ n₂.toSABMap.φ = m.toSABMap.φ ≫ ψ.left := by
    apply pn.hom_ext
    · rw [Category.assoc, Category.assoc, ← hn₂, hψn, hh]
    · rw [Category.assoc, Category.assoc, pn₂.w, Over.w_assoc, Over.w, pm.w]
  have P : IsPullback m.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact pm) sq.symm pn₂
  have q : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) n₂.toSABMap.φ :=
    ⟨⟨MorphismProperty.of_isPullback pn₂.flip hS,
      MorphismProperty.of_isPullback pn₂.flip (inferInstance : Flat π)⟩,
      MorphismProperty.of_isPullback pn₂.flip hQ⟩
  have hEt : Etale ψ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) P.flip q hψ.1.2.2.1
  haveI : IsFinite ψ'.left := hψ.1.2.1
  haveI : IsAffineHom ψ.left := by
    refine GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ ψ.left n₂.toSABMap.φ q.1.1 q.1.2 q.2 ?_
    rw [← P.isoPullback_inv_snd]
    infer_instance
  haveI := o₂.proper
  haveI : IsProper (ψ.left ≫ o₂.t.G.hom) := by rw [Over.w]; exact o.proper
  haveI : IsProper ψ.left := IsProper.of_comp ψ.left o₂.t.G.hom
  have hFin : IsFinite ψ.left := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨r₁, r₂⟩ := GlobalTheory.isIsog_of_surjective_baseChange E H D l p S S' s _ π o o₂ o' o₂' m n₂ ψ ψ' hS sq hψ hFin hEt
  exact ⟨o₂, ψ, r₁, r₂ K hker⟩

end GlobalTheory.HkFam
end


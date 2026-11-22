import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2538
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedSpaceOfFinGenSubfieldBaseChanges
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem flat_spec_field {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Sp K) : Flat f := by
  haveI : IsIntegral (Sp K) := by unfold Sp; infer_instance
  haveI : Subsingleton (Sp K) := by unfold Sp; infer_instance
  infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : A →+* B) (j : B →+* C) :
    spMap (j.comp i) = spMap j ≫ spMap i := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem appTop_spMap_injective {A B : Type} [CommRing A] [CommRing B] (j : A →+* B)
    (hj : Function.Injective j) : Function.Injective (spMap j).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap j).appTop.hom x) =
      j ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x) := fun x => congrArg (fun f => f.hom x) e
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  rw [h3, h3] at h2
  have h4 := hj h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom h4
  simpa using this

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (j : A →+* B) (y : A) :
    (spMap j).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (j y) := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j)
  exact (congrArg (fun f => f.hom y) e).symm

variable {F : Type} [CommRing F] {X : Scheme.{0}} (f : X ⟶ Sp F)

def bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    pullback f (spMap i₀) ⟶ pullback f (spMap i) :=
  pullback.map f (spMap i₀) f (spMap i) (𝟙 X) (spMap j) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← hji, spMap_comp])

theorem bc_fst {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.fst f (spMap i) = pullback.fst f (spMap i₀) := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

theorem bc_snd {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.snd f (spMap i) = pullback.snd f (spMap i₀) ≫ spMap j := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

theorem isPullback_bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    IsPullback (bc f i₀ i j hji) (pullback.snd f (spMap i₀)) (pullback.snd f (spMap i)) (spMap j) := by
  have s : IsPullback (bc f i₀ i j hji ≫ pullback.fst f (spMap i)) (pullback.snd f (spMap i₀)) f
      (spMap j ≫ spMap i) := by
    rw [bc_fst, ← spMap_comp, hji]
    exact IsPullback.of_hasPullback f (spMap i₀)
  exact IsPullback.of_right s (bc_snd f i₀ i j hji) (IsPullback.of_hasPullback f (spMap i))

theorem bc_trans {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i₀ : F →+* K) (i₁ : F →+* A) (j₁ : A →+* K) (h₁ : j₁.comp i₁ = i₀)
    (i₂ : F →+* B) (j₂ : B →+* K) (h₂ : j₂.comp i₂ = i₀) (k : A →+* B) (hk : k.comp i₁ = i₂)
    (hk' : j₂.comp k = j₁) :
    bc f i₀ i₁ j₁ h₁ = bc f i₀ i₂ j₂ h₂ ≫ bc f i₂ i₁ k hk := by
  apply pullback.hom_ext
  · simp [bc_fst]
  · rw [Category.assoc, bc_snd, bc_snd, ← Category.assoc, bc_snd, Category.assoc, ← spMap_comp, hk']

theorem mem_of_isPushout {R A B P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ B} {inl : A ⟶ P} {inr : B ⟶ P}
    (H : IsPushout φ ψ inl inr) (S : Subring P) (hA : ∀ a, inl.hom a ∈ S) (hB : ∀ b, inr.hom b ∈ S)
    (x : P) : x ∈ S := by
  let inl' : A ⟶ CommRingCat.of S := CommRingCat.ofHom (inl.hom.codRestrict S hA)
  let inr' : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S hB)
  have w : φ ≫ inl' = ψ ≫ inr' := by
    ext r
    exact congrArg (fun g => g.hom r) H.w
  have hd : H.desc inl' inr' w ≫ CommRingCat.ofHom S.subtype = 𝟙 P := by
    apply H.hom_ext
    · rw [H.inl_desc_assoc, Category.comp_id]; rfl
    · rw [H.inr_desc_assoc, Category.comp_id]; rfl
  have := congrArg (fun g => g.hom x) hd
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  rw [← this]
  exact ((H.desc inl' inr' w).hom x).2

theorem isClosed_basicOpen_idem {Y : Scheme.{0}} {e : Γ(Y, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (Y.basicOpen e : Set Y) := by
  have : (Y.basicOpen e : Set Y) = (Y.basicOpen (1 - e) : Set Y)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ Y.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Y.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (Y.mem_basicOpen e x trivial).2 h'
      · exact absurd ((Y.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (Y.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory.GeomConnDesc

end

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

variable {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Sp F) {K : Type} [Field K] (i₀ : F →+* K)

def Lc {n : ℕ} (c : Fin n → K) : Subfield K := Subfield.closure (Set.range i₀ ∪ Set.range c)

theorem mem_Lc {n : ℕ} (c : Fin n → K) (x : F) : i₀ x ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inl ⟨x, rfl⟩)

theorem mem_Lc' {n : ℕ} (c : Fin n → K) (k : Fin n) : c k ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inr ⟨k, rfl⟩)

theorem hji_L (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) : L.subtype.comp (i₀.codRestrict L hL) = i₀ :=
  RingHom.ext fun _ => rfl

def hcL (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict L hL)) :=
  bc f i₀ (i₀.codRestrict L hL) L.subtype (hji_L i₀ L hL)

theorem hcL_factor {L₁ L₂ : Subfield K} (hL₁ : ∀ x, i₀ x ∈ L₁) (hL₂ : ∀ x, i₀ x ∈ L₂) (hle : L₁ ≤ L₂)
    (y : Γ(pullback f (spMap (i₀.codRestrict L₁ hL₁)), ⊤)) :
    ∃ y', (hcL f i₀ L₁ hL₁).appTop.hom y = (hcL f i₀ L₂ hL₂).appTop.hom y' := by
  have e : hcL f i₀ L₁ hL₁ = hcL f i₀ L₂ hL₂ ≫ bc f (i₀.codRestrict L₂ hL₂)
      (i₀.codRestrict L₁ hL₁) (Subfield.inclusion hle) (RingHom.ext fun _ => rfl) :=
    bc_trans f i₀ (i₀.codRestrict L₁ hL₁) L₁.subtype (hji_L i₀ L₁ hL₁)
      (i₀.codRestrict L₂ hL₂) L₂.subtype (hji_L i₀ L₂ hL₂) (Subfield.inclusion hle)
      (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)
  exact ⟨_, by rw [e, appTop_comp_apply]⟩

def hc {n : ℕ} (c : Fin n → K) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))) :=
  hcL f i₀ (Lc i₀ c) (mem_Lc i₀ c)

theorem hc_factor {n m : ℕ} (c : Fin n → K) (d : Fin m → K) (hle : Lc i₀ c ≤ Lc i₀ d)
    (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)) :
    ∃ y', (hc f i₀ c).appTop.hom y = (hc f i₀ d).appTop.hom y' :=
  hcL_factor f i₀ (mem_Lc i₀ c) (mem_Lc i₀ d) hle y

theorem Lc_le_append_left {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ c ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.castAdd m k, Fin.append_left _ _ _⟩))

theorem Lc_le_append_right {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ d ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.natAdd n k, Fin.append_right _ _ _⟩))

theorem gen [QuasiCompact f] [QuasiSeparated f] (x : Γ(pullback f (spMap i₀), ⊤)) :
    ∃ (n : ℕ) (c : Fin n → K) (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)),
      (hc f i₀ c).appTop.hom y = x := by
  haveI : Flat (spMap i₀) := flat_spec_field _
  let S : Subring Γ(pullback f (spMap i₀), ⊤) :=
    { carrier := {x | ∃ (n : ℕ) (c : Fin n → K)
        (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)), (hc f i₀ c).appTop.hom y = x}
      zero_mem' := ⟨0, Fin.elim0, 0, map_zero _⟩
      one_mem' := ⟨0, Fin.elim0, 1, map_one _⟩
      neg_mem' := by
        rintro _ ⟨n, c, y, rfl⟩
        exact ⟨n, c, -y, map_neg _ _⟩
      add_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' + z', by rw [map_add, hy', hz']⟩
      mul_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' * z', by rw [map_mul, hy', hz']⟩ }
  have H := ProperFunctions.isPushout_appTop (IsPullback.of_hasPullback f (spMap i₀))
  refine mem_of_isPushout H S (fun a => ?_) (fun b => ?_) x
  · refine ⟨0, Fin.elim0, (pullback.fst f _).appTop.hom a, ?_⟩
    rw [← appTop_comp_apply]
    exact congrArg (fun g => g.appTop.hom a) (bc_fst f i₀ (i₀.codRestrict (Lc i₀ Fin.elim0) (mem_Lc i₀ Fin.elim0)) (Lc i₀ Fin.elim0).subtype (hji_L i₀ _ (mem_Lc i₀ Fin.elim0)))
  · let c : Fin 1 → K := ![(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b]
    refine ⟨1, c, (pullback.snd f _).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Lc i₀ c))).inv.hom ⟨c 0, mem_Lc' i₀ c 0⟩), ?_⟩
    rw [← appTop_comp_apply]
    rw [show hc f i₀ c ≫ pullback.snd f _ = pullback.snd f (spMap i₀) ≫ spMap (Lc i₀ c).subtype from
      bc_snd f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)), appTop_comp_apply, appTop_spMap_inv]
    change (pullback.snd f (spMap i₀)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b)) = _
    simp

theorem preconnectedSpace_of_finGen : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F),
    QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  intro F _ X f _ _ K _ i₀ hyp
  haveI : Flat f := flat_spec_field f
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ U hU
  obtain ⟨n, c, y, rfl⟩ := gen f i₀ e
  have hinj : Function.Injective (hc f i₀ c).appTop.hom :=
    ProperFunctions.injective_appTop_of_isPullback (isPullback_bc f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)))
      (appTop_spMap_injective _ (Lc i₀ c).subtype.injective)
  have hy : IsIdempotentElem y := hinj (by rw [map_mul]; exact he)
  have hcl : IsClopen (SetLike.coe (Scheme.basicOpen _ y)) :=
    ⟨isClosed_basicOpen_idem hy, (Scheme.basicOpen _ y).isOpen⟩
  haveI := hyp (Lc i₀ c) (mem_Lc i₀ c) n c rfl
  have hU' : U = (hc f i₀ c) ⁻¹' (SetLike.coe (Scheme.basicOpen _ y)) := by
    rw [← hUe, ← Scheme.preimage_basicOpen_top]; rfl
  rcases isClopen_iff.1 hcl with h0 | h1
  · left; rw [hU', h0]; rfl
  · right; rw [hU', h1]; rfl

end GlobalTheory.GeomConnDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverOrdEqSumAdaptedMonomial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.MonoOrd

variable {Y : Scheme.{0}} [IsIntegral Y]

def schOrdHom [IsLocallyNoetherian Y] (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem schOrd_prod_zpow [IsLocallyNoetherian Y] {ι : Type} (s : Finset ι)
    (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ s, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ s, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (schOrdHom v) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

theorem schOrd_inv [IsLocallyNoetherian Y] (g : Y.functionFieldˣ) (v : Y) :
    Scheme.ord ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) v =
      - Scheme.ord (g : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_inv (schOrdHom v) g)
  rw [toAdd_inv] at h
  exact h

variable {k : Type} [Field k] {q : Y ⟶ Sp k}

def divOrdHom (E : DivOver q) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (E.ord g)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul, ofAdd_add]

theorem divOrd_prod_zpow (E : DivOver q) {ι : Type} (s : Finset ι) (u : ι → Y.functionFieldˣ)
    (m : ι → ℤ) : E.ord (∏ j ∈ s, u j ^ m j) = ∑ j ∈ s, m j * E.ord (u j) := by
  have h := congrArg Multiplicative.toAdd (map_prod (divOrdHom E) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

end GlobalTheory.Discrepancy.MonoOrd

open GlobalTheory.Discrepancy.MonoOrd in

theorem GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  intro k _ Y _ _ _ q E y hE ι _ w u hw _ _ hself hother φ hφ
  classical
  set a : ι → ℤ := fun j => Scheme.ord (φ : Y.functionField) (w j) with ha
  set ψ : Y.functionFieldˣ := φ * ∏ j, u j ^ (-a j) with hψ
  have hord : ∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (ψ : Y.functionField) v = 0 := by
    intro v hv h1
    rw [hψ, Units.val_mul, Scheme.ord_mul φ.ne_zero (Units.ne_zero _), schOrd_prod_zpow]
    by_cases h : ∃ i, v = w i
    · obtain ⟨i, rfl⟩ := h
      rw [Finset.sum_eq_single i]
      · rw [hself i, ha]
        ring
      · intro j _ hji
        rw [hother j (w i) hv h1 (fun e => hji (hw e.symm)), mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => by rw [hother j v hv h1 (h j), mul_zero],
        hφ v hv h1 h, add_zero]
  have hreg : ∀ g : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (g : Y.functionField) v = 0) →
        0 ≤ E.ord g := fun g hg =>
    (E.ord_nonneg_iff g).2 (hE _ (regAt_of_forall_coheight_eq_one fun z hz h1 =>
      (GlobalTheory.RegCodimOne.regAt_iff_ord_nonneg h1 g.ne_zero).2 (hg z hz h1).ge))
  have h0 := hreg ψ hord
  have h0' := hreg ψ⁻¹ fun v hv h1 => by rw [schOrd_inv, hord v hv h1, neg_zero]
  rw [E.ord_inv] at h0'
  have hψ0 : E.ord ψ = 0 := by omega
  rw [hψ, E.ord_mul, divOrd_prod_zpow] at hψ0
  simp only [neg_mul, Finset.sum_neg_distrib] at hψ0
  rw [ha] at hψ0
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsPol

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem polOnAb_genPt : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsOpen (abLocus G) →
    genericPoint S ∈ abLocus G → PolOnAb G L.L → PolOnAb (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)).L := by
  intro S _ G _ _ L hO hg hpol V _
  obtain ⟨U, hU, hp, hUs⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⟨abLocus G, hO⟩) (x := genericPoint S) hg
  obtain ⟨ha, hk⟩ := hpol U hUs
  obtain ⟨f, hf⟩ : ∃ f : V.toScheme ⟶ U.toScheme, f ≫ U.ι = V.ι ≫ KeyVals.genPt S :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ KeyVals.genPt S) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact KeyVals.genPt_le U hp (Set.mem_univ (V.ι y))), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (KeyVals.genPt S)
  have h' := isGrpPullback_pullback (KeyVals.bG G (KeyVals.genPt S)) V.ι
  have h₀ := isGrpPullback_pullback G U.ι
  have h₂ := (h'.comp h).congr hf.symm rfl
  let A' := (Over.pullback V.ι).obj (KeyVals.bG G (KeyVals.genPt S))
  let a : (KeyVals.bG G (KeyVals.genPt S)).left ⟶ G.left := pullback.fst G.hom (KeyVals.genPt S)
  let b : A'.left ⟶ (KeyVals.bG G (KeyVals.genPt S)).left := pullback.fst (KeyVals.bG G (KeyVals.genPt S)).hom V.ι
  let ψ : A'.left ⟶ ((Over.pullback U.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom U.ι = b ≫ a := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback A' ((Over.pullback U.ι).obj G) f ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB (pull_isLB L.isLB a) b
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom U.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.L.pull a).pull b) ((L.L.pull (pullback.fst G.hom U.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb L.L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (lbIso_self (pull_isLB L.isLB (b ≫ a)))
  have : IsAffine U.toScheme := hU
  exact ⟨relAmple_pull h₃.1 hL₀ hL ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha,
    kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk⟩

end GlobalTheory.KeyValsPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelLowerLevelDescendsGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PrincipalDescent

theorem principal_descends : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  intro h n N o o' _ _ _ b ζ' j X Y s' π sY C Ga _ ρ ν hN hNu hdiv hζ hbase hπ hq hft hP ν1 νm hν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨c, hCc, -⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o' b.ζ ζ' j X s' C hN hNu hdiv hζ
  have hqA : IsQProjOver (C.A.hom ≫ π ≫ sY) := GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian o X (π ≫ sY) C.A C.diag hq (pull_isLB C.isLB _) hP.1
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ := GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base o X Y π sY Ga ρ C.A ν hπ hqA C.ab (fun a => (hν a).1) ν1 νm
  obtain ⟨P₀, φ₂, hP₀, sq, iso, norm⟩ := GlobalTheory.T.exists_squareBundle_descent_galoisCover X Y π Ga ρ C.A A₀ φ ν C.P hπ C.ab hA₀ gp hφ (fun a => (hν a).1) ν1 νm
    C.isLB C.rig₁ (fun a => (hν a).2.1)
  have hlev : ∀ a, ∃ x₀ : 𝟙_ (Over Y) ⟶ A₀, (C.lev a ^ (N / n)).left ≫ φ = π ≫ x₀.left := by
    intro a
    obtain ⟨f, hf, -⟩ := hπ.existsUnique_desc ((C.lev a ^ (N / n)).left ≫ φ) (fun g => by
      rw [← Category.assoc, ← (hν g).2.2 a, Category.assoc, hφ.inv g])
    have hf' : f ≫ A₀.hom = 𝟙 Y := by
      have := hπ.fin
      have := hπ.etale
      have := hπ.onto
      have : Epi π := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi π, ← Category.assoc, hf, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
      simp
    exact ⟨Over.homMk f hf', hf.symm⟩
  choose lev₀ hlev₀ using hlev
  obtain ⟨φ', φ₂', gp', sq', iso', hlev'⟩ := GlobalTheory.T.descendedData_transport_identity_levelChange h n N (N / n) o o' b.ζ ζ' X Y (s' ≫ spMap j) s' C c π A₀ φ φ₂ P₀ lev₀
    hCc gp sq hP₀ iso hlev₀
  obtain ⟨c₀, hpb⟩ := GlobalTheory.T.exists_siegelObject_of_galois_descended_data h n o b.ζ X Y π (s' ≫ spMap j) sY Ga ρ c A₀ φ' φ₂' P₀ lev₀ hbase.symm hπ hA₀ gp' sq' hP₀
    iso' norm hlev'
  have hR : SRel C c₀ (N / n) 1 π := by
    have e := ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N o o o' b.ζ b.ζ ζ' Y X X sY (s' ≫ spMap j) s' c₀ c C π (𝟙 X) 1 1 (N / n)
      ((sRel_one_one_iff c c₀ π).2 hpb)).1).1 hCc
    rwa [Category.id_comp] at e
  exact ⟨c₀, GlobalTheory.T.principal_descent_finite_etale_surjective h N n (N / n) 1 o' o ζ' b.ζ X Y s' sY π C c₀ hπ.fin hπ.etale hπ.onto hR hP, hR⟩

end GlobalTheory.PrincipalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → D.PsiEven → D.TauBimult → ∀ (χ : D.X) (n : ℕ), ∃ u : Rˣ, ((a (n • χ) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) (u : R) * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2) := by
  first | exact @GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow | exact GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow | (intros; apply GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalingIntegralRescaleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_scaling_integral_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → ∀ c : D.X → (FractionRing R)ˣ, (∀ χ : D.X, ∃ u : Rˣ, c χ * a χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) → Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D c) ⊤) := by
  first | exact @GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale | exact GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale | (intros; apply GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale <;> assumption)
end


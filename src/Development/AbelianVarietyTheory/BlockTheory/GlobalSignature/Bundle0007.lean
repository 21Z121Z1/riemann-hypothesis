import Mathlib
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def CosetMass {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (stabAt Γ K y)) ∧
  ∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
    ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m

def stabHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E) (N : Submodule (𝓞 E) W.V) : Subgroup (UAf hc W) :=
  (stabGL (hatL (F := F) (crdLat W N))).subgroupOf (UAf hc W)

def General : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → W.IsPosDef →
    ∀ N : Submodule (𝓞 E) W.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular W.hT N →
      CosetMass (UFin hc W) (stabHat hc W N) (Formalism.HermitianLatticesTheory.mass W.hT N)

def DefiniteSpaceClassStatement (D : D7) (_Lv : LevelData D) (_u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
    CosetMass
      ((ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      ((levelAfL D.sp.cm.sig D.sp.gram0 (D.sp.crdLat0 N)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def ClassesAsDoubleCosets : Prop :=
  General ∧ ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), DefiniteSpaceClassStatement D Lv u

theorem CosetMass.unique {G : Type} [Group G] {Γ K : Subgroup G} {m m' : ℝ}
    (h : CosetMass Γ K m) (h' : CosetMass Γ K m') : m = m' := by
  haveI := h.1
  letI := Fintype.ofFinite (ClassSet Γ K)
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  rw [← h.2.2 _ hs, ← h'.2.2 _ hs]

example {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E) (N : Submodule (𝓞 E) W.V) :
    stabHat hc W N = (levelAfL hc.sig W.gram (crdLat W N)).subgroupOf (UAf hc W) := by
  ext x
  simp only [stabHat, Subgroup.mem_subgroupOf, levelAfL, level, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CosetGroupMembership
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CosetGroupMembership

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def cosetGrp {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom

def CosetSum {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (cosetGrp Γ K y)) ∧
  ∀ (ι : Type) [Fintype ι] (y : ι → G),
    Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
    ∑ i, ((Nat.card (cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def stabHat (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) : Subgroup (UAf hc S) :=
  (stabGL (hatL (F := F) (crdLat S N))).subgroupOf (UAf hc S)

def rat0 {R : Ranks} (sp : Spaces R F E) : Subgroup (UPts sp.cm.sig sp.gram0 (Af F)) :=
  (ratPts sp.cm.sig sp.gram0 (Af F)).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F))

def stabHat0 {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    Subgroup (UPts sp.cm.sig sp.gram0 (Af F)) :=
  (stabGL (hatL (F := F) (sp.crdLat0 N))).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F))

end Obj

def GeneralForm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (S : HSpace E), S.SigOK → S.IsPosDef →
    ∀ N : Submodule (𝓞 E) S.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular S.hT N →
      CosetSum (UFin hc S) (stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N)

def ColumnForm (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
      CosetSum (rat0 D.sp) (stabHat0 D.sp N) (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def MassAsCosetSum : Prop := GeneralForm ∧ ∀ D : D7, ColumnForm D

def ClassDictionary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (S : HSpace E), S.SigOK → S.IsPosDef →
    ∀ N : Submodule (𝓞 E) S.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular S.hT N →
      (∀ y : UAf hc S, ∃! L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L ∧
        Carries (F := F) (y : GL (Fin S.rank) (E ⊗[F] Af F)) (crdLat S N) (crdLat S L)) ∧
      (∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L →
        ((L ∈ Formalism.HermitianLatticesTheory.genus S.hT N ↔ ∃ y : UAf hc S,
          Carries (F := F) (y : GL (Fin S.rank) (E ⊗[F] Af F)) (crdLat S N) (crdLat S L)) ∧
        (L ∈ Formalism.HermitianLatticesTheory.genus S.hT N ↔ Formalism.HermitianLatticesTheory.IsUnimodular S.hT L))) ∧
      (∀ (y y' : UAf hc S) (L L' : Submodule (𝓞 E) S.V), Submodule.IsLattice E L →
        Submodule.IsLattice E L' →
        Carries (F := F) (y : GL (Fin S.rank) (E ⊗[F] Af F)) (crdLat S N) (crdLat S L) →
        Carries (F := F) (y' : GL (Fin S.rank) (E ⊗[F] Af F)) (crdLat S N) (crdLat S L') →
        ((DoubleCoset.mk (UFin hc S) (stabHat hc S N) y = DoubleCoset.mk (UFin hc S) (stabHat hc S N) y') ↔
          ∃ g ∈ Formalism.HermitianLatticesTheory.isom S.hT, Formalism.HermitianLatticesTheory.gmap g L = L')) ∧
      (∀ (y : UAf hc S) (L : Submodule (𝓞 E) S.V), Submodule.IsLattice E L →
        Carries (F := F) (y : GL (Fin S.rank) (E ⊗[F] Af F)) (crdLat S N) (crdLat S L) →
        ∀ γ : GL (Fin S.rank) E, γ ∈ UF hc S →
          (bc (inclE (F := F) (Af F)) γ ∈ (cosetGrp (UFin hc S) (stabHat hc S N) y).map (UAf hc S).subtype ↔
            γ ∈ stabGL (crdLat S L)))

theorem mem_cosetGrp {G : Type} [Group G] (Γ K : Subgroup G) (y x : G) :
    x ∈ cosetGrp Γ K y ↔ x ∈ Γ ∧ y⁻¹ * x * y ∈ K := by
  simp only [cosetGrp, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by group⟩⟩
  rintro ⟨k, hk, rfl⟩
  have : y⁻¹ * (y * k * y⁻¹) * y = k := by group
  rwa [this]

theorem stabHat_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    stabHat hc S N = (levelAfL hc.sig S.gram (crdLat S N)).subgroupOf (UAf hc S) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem CosetSum.pos {G : Type} [Group G] {Γ K : Subgroup G} {m : ℝ} (h : CosetSum Γ K m) : 0 < m := by
  obtain ⟨h1, h2, h3⟩ := h
  letI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  haveI : Nonempty (ClassSet Γ K) := ⟨DoubleCoset.mk Γ K 1⟩
  have hb : Function.Bijective
      (fun c : ClassSet Γ K => (DoubleCoset.mk Γ K (Quotient.out c) : ClassSet Γ K)) := by
    have : (fun c : ClassSet Γ K => (DoubleCoset.mk Γ K (Quotient.out c) : ClassSet Γ K)) = id := by
      funext c
      exact Quotient.out_eq' c
    rw [this]
    exact Function.bijective_id
  rw [← h3 _ _ hb]
  refine Finset.sum_pos (fun c _ => ?_) Finset.univ_nonempty
  haveI := h2 (Quotient.out c)
  exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)

end GlobalTheory.IndefiniteRowSideFullHecke.CosetGroupMembership

end
end


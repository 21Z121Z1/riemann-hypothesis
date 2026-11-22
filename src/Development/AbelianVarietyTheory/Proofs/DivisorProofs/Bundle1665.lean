import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqOfPointsOfGerm
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel.KerDet

theorem isClosed_pt {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) [IsFinite s] (x : X) :
    IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : s w = s x := Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hd := (s.isDiscrete_preimage_singleton (s x)).to_subtype
  have hs : (⟨x, rfl⟩ : s ⁻¹' {s x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

theorem exists_section {k L : Type} [Field k] [IsAlgClosed k] [Field L] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [IsFinite s] (u : Sp L ⟶ X) : ∃ a : Sp k ⟶ X, a ≫ s = 𝟙 _ ∧ u = (u ≫ s) ≫ a := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective u
  have hx := isClosed_pt s x
  refine ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, ?_⟩
  change Spec.map φ ≫ X.fromSpecResidueField x =
    ((Spec.map φ ≫ X.fromSpecResidueField x) ≫ s) ≫ Spec.map (residueFieldIsoBase s x hx).hom ≫
      X.fromSpecResidueField x
  simp only [Category.assoc]
  rw [← SpecMap_residueFieldIsoBase_inv_assoc s x hx, ← Spec.map_comp_assoc (residueFieldIsoBase s x hx).hom,
    Iso.hom_inv_id, Spec.map_id, Category.id_comp]

theorem exists_stalk_factor {X : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint R) = x) : ∃ ψ : X.presheaf.stalk x ⟶ R, f = Spec.map ψ ≫ X.fromSpecStalk x := by
  obtain ⟨⟨y, φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X R).symm.surjective f
  have hy : y = x := by
    rw [← hx]
    change y = (Spec.map φ ≫ X.fromSpecStalk y) _
    exact ((Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (X.fromSpecStalk y) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)).symm
  subst hy
  exact ⟨φ, rfl⟩

variable {k : Type} [Field k]

def InK {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Scheme.{0}} (y : T ⟶ A.left) : Prop :=
  ∃ z : T ⟶ Sp k, z ≫ (η[B]).left = y ≫ π.left

theorem inK_iff {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Scheme.{0}} (y : T ⟶ A.left) :
    InK π y ↔ y ≫ π.left = (y ≫ A.hom) ≫ (η[B]).left := by
  have hη : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w (η[B])
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => ⟨_, h.symm⟩⟩
  have e : z = y ≫ A.hom := by
    have := congrArg (· ≫ B.hom) hz
    simp only [Category.assoc, hη, Category.comp_id, Over.w π] at this
    exact this
  rw [← hz, e]

theorem comp_eq_one_iff {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Over (Sp k)} (Y : T ⟶ A) :
    Y ≫ π = 1 ↔ InK π Y.left := by
  have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  rw [inK_iff, Over.w Y, ← hT]
  constructor
  · intro h; exact congrArg (fun q => q.left) h
  · intro h; exact Over.OverMorphism.ext h

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel.KerDet

variable {k : Type} [Field k]

theorem toUnit_left (T : Over (Sp k)) : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)

theorem one_left {A T : Over (Sp k)} [GrpObj A] : (1 : T ⟶ A).left = T.hom ≫ (η[A]).left := by
  rw [← toUnit_left]; rfl

variable [IsAlgClosed k]

theorem local_step {A B B' : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj B'] (π : A ⟶ B) (π' : A ⟶ B')
    [IsMonHom π] [IsMonHom π'] [IsFinite π.left]
    (h1 : ∀ a : 𝟙_ (Over (Sp k)) ⟶ A, a ≫ π = 1 → a ≫ π' = 1)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base)
    (h2 : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      InK π (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) →
      InK π' (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀))
    {R : CommRingCat.{0}} [IsLocalRing R] (y : Spec R ⟶ A.left) (hy : InK π y) : InK π' y := by
  let c : Sp (IsLocalRing.ResidueField R) ⟶ Spec R := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hc : c (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
    Spec_closedPoint
  obtain ⟨z, hz⟩ := hy
  let ũ : Sp (IsLocalRing.ResidueField R) ⟶ pullback π.left (η[B]).left :=
    pullback.lift (c ≫ y) (c ≫ z) (by rw [Category.assoc, Category.assoc, hz])
  obtain ⟨a', ha's, hu⟩ := exists_section (pullback.snd π.left (η[B]).left) ũ
  let a0 := a' ≫ pullback.fst π.left (η[B]).left
  have hη : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w (η[B])
  have ha0 : a0 ≫ A.hom = 𝟙 _ := by
    simp only [a0, Category.assoc]
    rw [← Over.w π, pullback.condition_assoc, hη, Category.comp_id, ha's]
  let a : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk a0 ha0
  have ha : a ≫ π = 1 := (comp_eq_one_iff π a).2 ⟨a' ≫ pullback.snd _ _, by
    simp only [a, a0, Over.homMk_left, Category.assoc, pullback.condition]⟩
  have ha' : a ≫ π' = 1 := h1 a ha
  have e1 : c ≫ y = (ũ ≫ pullback.snd _ _) ≫ a0 := by
    simp only [a0]; rw [← Category.assoc, ← hu]; exact (pullback.lift_fst _ _ _).symm
  have hu' : c ≫ y = ((c ≫ y) ≫ A.hom) ≫ a0 := by
    have e2 : (c ≫ y) ≫ A.hom = ũ ≫ pullback.snd _ _ := by
      rw [e1, Category.assoc, ha0]; exact Category.comp_id _
    rw [e2]; exact e1
  let T' : Over (Sp k) := Over.mk (y ≫ A.hom)
  let Y : T' ⟶ A := Over.homMk y rfl
  let Ta : T' ⟶ A := toUnit T' ≫ a
  let D : T' ⟶ A := Y / Ta
  have hYπ : Y ≫ π = 1 := (comp_eq_one_iff π Y).2 ⟨z, hz⟩
  have hDπ : D ≫ π = 1 := by
    simp only [D, Ta]
    rw [GrpObj.div_comp, hYπ, Category.assoc, ha, MonObj.comp_one, div_one]
  let C : Over.mk ((c ≫ y) ≫ A.hom) ⟶ T' := Over.homMk c (by simp [T'])
  have hCY : C ≫ Y = C ≫ Ta := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Ta, toUnit_left, Over.homMk_left, C, Y, T', Over.mk_hom]
    rw [← Category.assoc c, ← Category.assoc c]
    exact hu'
  have hCD : C ≫ D = 1 := by
    simp only [D]; rw [GrpObj.comp_div, hCY, div_self']
  have hD0 : c ≫ D.left = ((c ≫ y) ≫ A.hom) ≫ (η[A]).left := by
    have := congrArg (fun q => q.left) hCD
    simp only [Over.comp_left, one_left] at this
    exact this
  have hDx : D.left (IsLocalRing.closedPoint R) = x₀ := by
    obtain ⟨p, hp⟩ := hx₀
    rw [← hc]
    change (c ≫ D.left) _ = x₀
    rw [hD0, ← hp]
    change (η[A]).left (((c ≫ y) ≫ A.hom) _) = (η[A]).left p
    exact congrArg (η[A]).left (Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _)
  obtain ⟨ψ, hψ⟩ := exists_stalk_factor D.left x₀ hDx
  have hDK : InK π D.left := (comp_eq_one_iff π D).1 hDπ
  have hDK' : InK π' D.left := by
    rw [hψ] at hDK ⊢
    exact h2 R ψ.hom hDK
  have hDπ' : D ≫ π' = 1 := (comp_eq_one_iff π' D).2 hDK'
  have hYπ' : Y ≫ π' = 1 := by
    rw [← div_mul_cancel Y Ta, MonObj.mul_comp, hDπ', Category.assoc, ha', MonObj.comp_one, _root_.one_mul]
  exact (comp_eq_one_iff π' Y).1 hYπ'

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel.KerDet

variable {k : Type} [Field k] [IsAlgClosed k]

theorem inK_of_inK {A B B' : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj B'] (π : A ⟶ B) (π' : A ⟶ B')
    [IsMonHom π] [IsMonHom π'] [IsFinite π.left]
    (h1 : ∀ a : 𝟙_ (Over (Sp k)) ⟶ A, a ≫ π = 1 → a ≫ π' = 1)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base)
    (h2 : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      InK π (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) →
      InK π' (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀))
    {T : Scheme.{0}} (y : T ⟶ A.left) (hy : InK π y) : InK π' y := by
  rw [inK_iff] at hy ⊢
  refine ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk _ _ fun t => ?_
  have h := local_step π π' h1 x₀ hx₀ h2 (T.fromSpecStalk t ≫ y) ((inK_iff π _).2 (by
    simp only [Category.assoc]; rw [hy, Category.assoc]))
  rw [inK_iff] at h
  simpa only [Category.assoc] using h

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KilledByIdealFiniteEtale
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killed_by_ideal_finite_etale : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∃ (K : Over S) (i : K ⟶ o.A), Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x := by
  first | (exact @GlobalTheory.HTTorsRep.exists_finiteEtale_killedBy) | (exact GlobalTheory.HTTorsRep.exists_finiteEtale_killedBy) | (intros; apply GlobalTheory.HTTorsRep.exists_finiteEtale_killedBy  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R).submatrix finSumFinEquiv.symm id)

theorem dC_mul_inl {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inl p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_inr {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inr p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_castAdd {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (Fin.castAdd n p) j = a p j := by
  simpa using dC_mul_inl a p j

theorem dC_mul_addNat {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (p.addNat n) j = a p j := by
  simpa using dC_mul_inr a p j

theorem dC_mul_eq {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) :
    dC R n * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p
  · rw [dC_mul_inl, Matrix.of_apply, Equiv.symm_apply_apply]; rfl
  · rw [dC_mul_inr, Matrix.of_apply, Equiv.symm_apply_apply]; rfl

theorem dblG_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i k : Fin n ⊕ Fin n) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J (finSumFinEquiv i) (finSumFinEquiv k) = dbl J i k := by
  simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem hTens_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB) (dC (AF F ⊗[F] E) nT * a) (dC (AF F ⊗[F] E) nT * b) = 0 := by
  unfold hTens
  have ha : dC (AF F ⊗[F] E) nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq a
  have hb : dC (AF F ⊗[F] E) nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq b
  rw [ha, hb]
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, incM, Matrix.map_apply,
    Matrix.transpose_apply, dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib, dC_mul_castAdd, dC_mul_addNat]

end GlobalTheory.LagrThetaInv

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ)
    (ψ : AddChar (AF F) ℂ) (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ) :
    schr ψ (co.e (dC (AF F ⊗[F] E) nT * a)) (schr ψ (co.e (dC (AF F ⊗[F] E) nT * b)) φ) =
      schr ψ (co.e (dC (AF F ⊗[F] E) nT * (a + b))) φ := by
  rw [GlobalTheory.ThetaQuasiRat.schr_schr, ← co.form, symp, hTens_dC, mul_zero, map_zero, mul_zero,
    AddChar.map_zero_eq_one, one_smul, ← map_add, Matrix.mul_add]

theorem dC_map {n : ℕ} : (dC E n).map (incAF F E) = dC (AF F ⊗[F] E) n := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p <;>
    simp only [dC, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, diagCols,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply] <;> split_ifs <;> simp

theorem dC_mul_rat {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    dC (AF F ⊗[F] E) nT * γ.map (incAF F E) = incM F (dC E nT * γ) := by
  rw [← dC_map, ← Matrix.map_mul]
  rfl

end GlobalTheory.LagrThetaInv

open scoped Pointwise in
open GlobalTheory.LagrThetaInv in

theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroup
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

namespace GlobalTheory.FinLatF

theorem latRepF_cont : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om h f u
  have hσ : ∀ x, σ (σ x) = x := fun x => GlobalTheory.AdelicU.cm_conj_conj hB.cm x
  have H := isHeis_opFF hσ hS hT hξ hc h.hw
  have hfix : ∀ p : GAF σ JS × GAF σ JT, (∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ) →
      ∀ e, Fixes (opFF hc w) (latF F E nS nT Λ) e → Om p e = e := by
    intro p hp e he
    rw [h.vac p e he]
    exact GlobalTheory.FinWeilO.normOp_of_le H lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he
  have hev : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
    intro f
    have hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} := by
      rw [h.span]; trivial
    induction hf using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨x, e, he, rfl⟩ := hm
      obtain ⟨N, hN, hNl⟩ := h.lev (w • x)
      filter_upwards [h.near, h.near' x N hN] with p hp hp'
      obtain ⟨l, hl, hl'⟩ := hp'
      have e2 : gamFF σ JS JT ξ₀ B.ψ (w • x) (N • l) = 1 := by
        rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNl l hl, one_mul]
      have e4 := H.comp x (N • l) e
      rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
      rw [h.op, hfix p hp e he, hl', ← e4]
    | zero => exact Filter.Eventually.of_forall fun p => map_zero _
    | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add, h3, h4]
    | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]
  haveI : IsTopologicalGroup (GAF σ JS) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GAF σ JT) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (hev f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

end GlobalTheory.FinLatF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem normOp_eq_self_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B)
    (hle : B ≤ A) {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

end Abstract

variable {nS nT : ℕ}

theorem fin_smul_mtF_sub_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ J) : pairA F 0 1 • (mtF σ J g - 1) = 0 := by
  have h : (mtF σ J g).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  apply GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF
  ext i j
  rw [Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.zero_apply, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPartF F E) (finPartF F E).map_zero (finPartF F E).map_one]
  rfl

theorem fin_smul_XFF (x : XFF F E nS nT) : pairA F 0 1 • (x : WOF F E nS nT) = x := by
  have h1 : pairA F 1 0 • (x : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF x.fin
  have h2 : pairA F 0 1 = 1 - pairA F 1 0 := Prod.ext (by show (0 : Ainf F) = 1 - 1; rw [sub_self])
    (by show (1 : Af F) = 1 - 0; rw [sub_zero])
  rw [h2, sub_smul, one_smul, h1, sub_zero]

theorem rhoFF_real {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (x : XFF F E nS nT) : rhoFF σ JS JT (g, h) x = x := by
  apply XFF.ext
  rw [coe_rhoFF]
  have hL : mtF σ JT h * (x : WOF F E nS nT) = x := by
    have : (mtF σ JT h - 1) * (x : WOF F E nS nT) = 0 := by
      rw [← fin_smul_XFF x, Matrix.mul_smul, ← Matrix.smul_mul, fin_smul_mtF_sub_one hh, Matrix.zero_mul]
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hR : (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x := by
    have : (x : WOF F E nS nT) * (mtF σ JS g⁻¹ - 1) = 0 := by
      rw [← fin_smul_XFF x, Matrix.smul_mul, ← Matrix.mul_smul,
        fin_smul_mtF_sub_one (Subgroup.inv_mem _ hg), Matrix.mul_zero]
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  show mtF σ JT h * (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x
  rw [hL, hR]

theorem IsLatRepF.real_triv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh f
  have hσ : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have key : Om (g, h) = LinearMap.id := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have hfix : Om (g, h) e = e := by
      rw [hR.vac _ e he]
      exact normOp_eq_self_of_le H lam (hR.sd' _)
        (by rintro _ ⟨a, ha, rfl⟩; rw [rhoFF_real hg hh]; exact ha) he
    rw [hR.op, rhoFF_real hg hh, hfix, LinearMap.id_apply]
  rw [key, LinearMap.id_apply]

end GlobalTheory.FinLatF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantChartPointCentreFactorTwoStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_chart_point_centre_factor_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (cpt X x z) τ v ≤ 2 * X.maj x τ v ∧ X.maj x τ v ≤ 2 * X.maj (cpt X x z) τ v := by
  first | exact @GlobalTheory.ChartGraph.maj_cpt_le_two | exact GlobalTheory.ChartGraph.maj_cpt_le_two | (intros; apply GlobalTheory.ChartGraph.maj_cpt_le_two <;> assumption)
end


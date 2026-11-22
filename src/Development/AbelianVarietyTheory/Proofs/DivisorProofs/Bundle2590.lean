import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundary
section
set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.EpsGenCob

theorem evU_mul' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU y U (a * b) = evU y U a * evU y U b := by
  unfold evU; rw [dif_pos h, dif_pos h, dif_pos h, map_mul]

theorem evU_isUnit' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a : Γ(Y, U)ˣ) : IsUnit (evU y U a.val) := by
  unfold evU; rw [dif_pos h]; exact a.isUnit.map _

theorem evU_cocycle {X : Scheme.{0}} (P : LB X) (hP : P.IsLB) {D : Type} [CommRing D] (y : Sp D ⟶ X)
    (a b c : P.ι) (ha : ⊤ ≤ y ⁻¹ᵁ P.U a) (hb : ⊤ ≤ y ⁻¹ᵁ P.U b) (hc : ⊤ ≤ y ⁻¹ᵁ P.U c) :
    evU y (P.U a ⊓ P.U c) (P.g a c).val =
      evU y (P.U a ⊓ P.U b) (P.g a b).val * evU y (P.U b ⊓ P.U c) (P.g b c).val := by
  have h3 : ⊤ ≤ y ⁻¹ᵁ (P.U a ⊓ P.U b ⊓ P.U c) := fun p hp ↦ ⟨⟨ha hp, hb hp⟩, hc hp⟩
  have e := congrArg (fun u ↦ evU y _ (Units.val u)) (hP.cocycle a b c)
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e
  rw [evU_mul' y _ h3, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction] at e
  · exact e.symm
  all_goals exact h3

theorem snd_eq_fst_mul_dl {D : Type} [CommRing D] (u : DualNumber D) (hu : IsUnit u) : u.snd = u.fst * dl u := by
  obtain ⟨w, hw⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hw
  unfold dl
  rw [← hw, Ring.inverse_unit]
  rw [mul_comm, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem dualNumber_inl_mul_one_add_inr_fst_snd {D : Type} [CommRing D] (a c : D) :
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).fst = a ∧
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).snd = a * c := by
  constructor <;> simp

end GlobalTheory.PtExt.EpsGenCob

namespace GlobalTheory.PtExt.EpsGenCob

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x = x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = toUnit _ ≫ η[B] := by
    refine Over.OverMorphism.ext ?_
    refine hv.trans ?_
    simp [spMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst, Category.comp_id]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by ext; simp
    rw [this]
    refine Over.OverMorphism.ext ?_
    simp [spOver, spMap]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', Hom.one_def, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

theorem ptV_mem (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (i : P.ι) (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P i) : ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U i := by
  intro p _
  have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)) := by
    refine (PrimeSpectrum.isHomeomorph_comap _ (fun a ↦ ⟨1, one_pos, TrivSqZeroExt.inl a, by simp⟩) ?_).surjective
    intro a ha
    obtain ⟨c, rfl⟩ := DualNumber.fst_eq_zero_iff_eps_dvd.1 (show TrivSqZeroExt.fst a = 0 from ha)
    exact mem_nilradical.2 ⟨2, by rw [mul_pow, sq DualNumber.eps, DualNumber.eps_mul_eps, zero_mul]⟩
  obtain ⟨p', rfl⟩ := hs p
  have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
  rw [← red_ptV hv] at h1
  exact h1 (Set.mem_univ p')

theorem ptV_nat (v : epsR R ⟶ B) {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (x : Pt A E) : ptV v (spOver ψ ≫ x) = spOver (epsHom ψ) ≫ ptV v x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
    congr 2
    ext a <;> simp [epsHom, DualNumber.lift_apply_inl]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    congr 2
    apply DualNumber.algHom_ext
    simp [epsHom, EpsWeil.epsMap]

theorem memV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    ⊤ ≤ (ptV v x).left ⁻¹ᵁ (P.U a ⊓ P.U b) := fun p hp ↦
  ⟨ptV_mem P hv x a ha hp, ptV_mem P hv x b hb hp⟩

theorem fst_gV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    (evU (ptV v x).left (P.U a ⊓ P.U b) (P.g a b).val).fst =
      evU (x ≫ AbDual.inl A B).left (P.U a ⊓ P.U b) (P.g a b).val := by
  have h := evalSectionAtPointOrZero_specMap_comp _ _ _ (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) (ptV v x).left _
    (P.g a b).val (memV P hv x a b ha hb)
  have e : spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ (ptV v x).left =
      (x ≫ AbDual.inl A B).left := by
    rw [← red_ptV hv x, Over.comp_left]; rfl
  rw [e] at h
  rw [h]; rfl

end GlobalTheory.PtExt.EpsGenCob

open GlobalTheory.PtExt.EpsGenCob in

theorem GlobalTheory.PtExt.exists_isEpsGen_of_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  intro R _ A B _ _ P hP v hv j hj s hs k hk
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨fun E _ _ x i ↦ TrivSqZeroExt.inl (s E x i) * (1 + TrivSqZeroExt.inr
    (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)), ?_, ?_, ?_⟩
  · intro E _ _ x i h
    exact ((hs1 E x i h).map (TrivSqZeroExt.inlHom E E)).mul (EpsWeil.epsUnit _).isUnit
  · intro E _ _ E' _ _ ψ x i h
    have h' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P i := fun p _ ↦ h (Set.mem_univ _)
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, h⟩
    have hjx2 : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E x) := fun p _ ↦ hjx (Set.mem_univ _)
    have hjx' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E' (spOver ψ ≫ x)) := hj E' _ ⟨i, h'⟩
    have hc := evU_cocycle P hP (ptV v (spOver ψ ≫ x)).left i (j E' (spOver ψ ≫ x)) (j E x)
      (ptV_mem P hv _ i h') (ptV_mem P hv _ _ hjx') (ptV_mem P hv _ _ hjx2)
    have u1 := evU_isUnit' _ _ (memV P hv _ i _ h' hjx') (P.g i (j E' (spOver ψ ≫ x)))
    have u2 := evU_isUnit' _ _ (memV P hv _ _ _ hjx' hjx2) (P.g (j E' (spOver ψ ≫ x)) (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E' _ _ u1 u2
    rw [← hc] at hd
    have uG := evU_isUnit' _ _ (memV P hv x i _ h hjx) (P.g i (j E x))
    have hnat : evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val =
        epsHom ψ (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) := by
      have e : (ptV v (spOver ψ ≫ x)).left = spMap (epsHom ψ : DualNumber E →+* DualNumber E') ≫ (ptV v x).left := by
        rw [ptV_nat, Over.comp_left]; rfl
      rw [e, evalSectionAtPointOrZero_specMap_comp _ _ _ _ _ _ _ (memV P hv x i _ h hjx)]
      rfl
    have e1 : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) =
        ψ (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val)) := by
      rw [hnat, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.2 uG]
    have hcob : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U (j E' (spOver ψ ≫ x)) ⊓ P.U (j E x))
        (P.g (j E' (spOver ψ ≫ x)) (j E x)).val) = k E' (spOver ψ ≫ x) - ψ (k E x) := hk E E' ψ x ⟨i, h⟩
    have hs := hs2 E E' ψ x i h
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E' (spOver ψ ≫ x) i) (dl (evU (ptV v (spOver ψ ≫ x)).left
      (P.U i ⊓ P.U (j E' (spOver ψ ≫ x))) (P.g i (j E' (spOver ψ ≫ x))).val) + k E' (spOver ψ ≫ x))
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [b1, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).1, a1, hs]
    · rw [b2, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.1, a2, hs, map_mul, map_add]
      linear_combination (ψ (s E x i)) * (-hd + e1 - hcob)
  · intro E _ _ x i i' hi hi'
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, hi⟩
    have hc := evU_cocycle P hP (ptV v x).left i i' (j E x) (ptV_mem P hv x i hi)
      (ptV_mem P hv x i' hi') (ptV_mem P hv x _ hjx)
    have u1 := evU_isUnit' _ _ (memV P hv x i i' hi hi') (P.g i i')
    have u2 := evU_isUnit' _ _ (memV P hv x i' (j E x) hi' hjx) (P.g i' (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E _ _ u1 u2
    rw [← hc] at hd
    have hsnd := snd_eq_fst_mul_dl _ u1
    have hfst := fst_gV P hv x i i' hi hi'
    have ht := hs3 E x i i' hi hi'
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i') (dl (evU (ptV v x).left (P.U i' ⊓ P.U (j E x)) (P.g i' (j E x)).val) + k E x)
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [a1, TrivSqZeroExt.fst_mul, b1, hfst, ht]
    · rw [a2, TrivSqZeroExt.snd_mul, b1, b2, hsnd, hfst, hd, ht, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.DualBasis

open GlobalTheory.LieVB GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.Pdiv (LieG ptMap dualScale specO)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem fst_of_isTangent {w : epsR R ⟶ G} (hw : IsTangent w) :
    ptMap (TrivSqZeroExt.fstHom R R R) ≫ (w : specO R (DualNumber R) ⟶ G) = toUnit (specO R R) ≫ η[G] := by
  have h : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  ext1
  simp only [Over.comp_left, h]
  exact hw.trans (Category.id_comp _).symm

theorem isTangent_val (x : LieG G) : IsTangent (G := G) x.1 := sec_epsZero_comp x

theorem exists_prod [QuasiSeparated G.hom] (l : List (LieG G)) :
    ∃ p : LieG G, p.1 = (l.map (·.1)).prod ∧ tangent p = (l.map tangent).sum := by
  induction l with
  | nil =>
    refine ⟨⟨1, ?_⟩, rfl, ?_⟩
    · exact comp_one _
    · refine dual_ext fun W _ s => ?_
      have e : cotMap (1 : specO R (DualNumber R) ⟶ G) (epsZero_comp ⟨1, comp_one _⟩) = 0 := cotMap_eq_zero rfl _
      rw [List.map_nil, List.sum_nil]
      exact (congr((epsIso R).hom.app W (($e).app W s))).trans (map_zero _)
  | cons x l ih =>
    obtain ⟨p, hp, hp'⟩ := ih
    refine ⟨⟨x.1 * p.1, OmegaGlobal.fst_mul x p⟩, by simp [hp], ?_⟩
    rw [tangent_mul, hp', List.map_cons, List.sum_cons]

theorem isLieComb_iff [QuasiSeparated G.hom] {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G) :
    IsLieComb (G := G) a (fun i => (v i).1) w.1 ↔ tangent w = ∑ i, cst R (a i) • tangent (v i) := by
  let u : Fin n → LieG G := fun i => ⟨ptMap (dualScale (a i)) ≫ (v i).1, OmegaGlobal.fst_scale (a i) (v i)⟩
  have hu (i : Fin n) : (u i).1.left = spMap (epsScaleR (a i)) ≫ (v i).1.left := by
    have ha : (dualScale (a i)).toRingHom = epsScaleR (a i) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v i).1.left) ha
  obtain ⟨p, hp, hp'⟩ := exists_prod (List.ofFn u)
  rw [List.map_ofFn] at hp hp'
  rw [List.sum_ofFn] at hp'
  have hs : tangent p = ∑ i, cst R (a i) • tangent (v i) :=
    hp'.trans (Finset.sum_congr rfl fun i _ => tangent_scale (a i) (v i) _)
  constructor
  · rintro ⟨u', hu', e⟩
    obtain rfl : u' = fun i => (u i).1 := funext fun i => Over.OverMorphism.ext ((hu' i).trans (hu i).symm)
    obtain rfl : w = p := Subtype.ext (e.trans hp.symm)
    exact hs
  · intro e
    obtain rfl : w = p := tangent_injective R G (e.trans hs.symm)
    exact ⟨fun i => (u i).1, hu, hp⟩

theorem exists_dual_of_isFrame [QuasiSeparated G.hom] {n : ℕ} {e : Fin n → Γ(omega G, ⊤)} (he : IsFrame e) :
    ∃ v : Fin n → LieG G, (∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0) ∧
      IsLieBasis (G := G) fun j => (v j).1 := by
  choose v hv using fun j => TangentSurj.tangent_surjective R G (he.coord j)
  refine ⟨v, fun j k => ?_, fun j => isTangent_val (v j), fun w hw => ?_⟩
  · have h := he.dualApp_coord_frame j k le_rfl
    rw [Twist.resM_self] at h
    rw [hv]
    exact h.trans (if_congr eq_comm rfl rfl)
  · have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
    let b := he.dual.basis le_rfl
    have hb (j : Fin n) : b j = tangent (v j) := by
      rw [hv]
      exact (IsFrame.basis_apply _ _ _).trans (Twist.resM_self _ _)
    have key (a : Fin n → R) := isLieComb_iff a v ⟨w, fst_of_isTangent hw⟩
    simp only [← hb] at key
    choose a ha using fun j => hc.2 (b.repr (tangent ⟨w, fst_of_isTangent hw⟩) j)
    refine ⟨a, (key a).2 ?_, fun a' h' => funext fun j => hc.1 ?_⟩
    · simp only [ha]
      exact (b.sum_repr _).symm
    · rw [ha, (key a').1 h', b.repr_sum_self]

theorem exists_isDual : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R : Type) [CommRing R]
    (ξ : Sp R ⟶ S), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ⊤ ≤ ξ ⁻¹ᵁ c.U →
    ∃ y : Fin g → (epsR R ⟶ KeyVals.bG G ξ), KeyVals.IsDual c ξ y ∧ IsLieBasis y := by
  intro S G _ g c R _ ξ hG _ hc
  have h := isGrpPullback_pullback G ξ
  have : QuasiSeparated (bG G ξ).hom := MorphismProperty.of_isPullback h.1 inferInstance
  have h₁ := ((c.isFrame.pullback ξ).res hc).map_iso (omegaBase h)
  have hf : IsFrame (pfr c ξ hc) := by
    convert h₁ using 2 with k
    exact congrArg _ (QCoh.res_pullbackSections ξ _ le_rfl hc (c.e k)).symm
  obtain ⟨v, hv, hb⟩ := exists_dual_of_isFrame hf
  exact ⟨fun j => (v j).1, ⟨hc, fun j => ⟨v j, rfl, hv j⟩⟩, hb⟩

end GlobalTheory.KeyVals.DualBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceOfPrimeElementOfNormalLocalModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvrPlace_of_prime_element_of_normal_localModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T) (ψ : T →+* K) (f : T), IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) → RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → ∃ (S : Place cL) (hS : S.IsPrimeOf T) (ψS : S.ring →+* K), Function.Surjective ψS ∧ (∀ a, ψS (S.const a) = cK a) ∧ (∀ t : T, ψS ⟨t, hS.1 t t.2⟩ = ψ t) ∧ Irreducible (⟨f, hS.1 f f.2⟩ : S.ring) := by
  first | exact @GlobalTheory.FieldPair.PrimeElementPlace.main | exact GlobalTheory.FieldPair.PrimeElementPlace.main | (intros; apply GlobalTheory.FieldPair.PrimeElementPlace.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 → ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  first | exact @GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' | exact GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' | (intros; apply GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8ThetaPowerOverModuliDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem exists_sharpOver_connected {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) {S : Scheme.{0}} [ConnectedSpace S] (u : S ⟶ F.X) : ∃ P : PolAV S, SharpOver F W P u := by
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := GlobalTheory.LowChart.siegPull F.univ u (u ≫ F.s) rfl
  have hpb : SiegPB c F.univ u := GlobalTheory.LowChart.siegPB_siegPull F.univ u _ rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ u _ rfl F.princ
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected c.A c.ab
  obtain ⟨G, _, pr, hA, hdim, hpr, hu⟩ := GlobalTheory.EighthPower.exists_power c.A c.ab hd 8
  have hb := GlobalTheory.EighthPower.isSymBilin hG c hc.1
  have hL : (GlobalTheory.MatrixBundle.matLB c.P pr W).IsLB := LB.isLB_linComb c.isLB _ _
  refine ⟨{ A := G, isAb := hA, g := 8 * d, smoothDim := hdim, L := GlobalTheory.MatrixBundle.matLB c.P pr W, isLB := hL
            rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb hpr, sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb hpr
            ample := _root_.GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG _ _ 8 _ _ _ _ c G pr W hpr hu hc.1 hW.1
            ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb hpr hu hW.2 hc.2 }, c, hpb, pr, hpr, hu, ?_⟩
  exact PolBaseChange.lbIso_refl hL

theorem exists_sharpOver_domain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (R : Type) [CommRing R] [IsDomain R] (u : Sp R ⟶ F.X), ∃ P : PolAV (Sp R), SharpOver F W P u := by
  intro g n F W hW R _ _ u
  haveI : ConnectedSpace (Sp R) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  exact exists_sharpOver_connected F W hW u

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveQDivisorOffPointAmpleClass
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

namespace GlobalTheory

theorem exists_common_den_nonneg (q₁ q₂ : ℚ) (h₁ : 0 ≤ q₁) (h₂ : 0 ≤ q₂) :
    ∃ a b M : ℕ, 0 < M ∧ q₁ = a / M ∧ q₂ = b / M := by
  refine ⟨q₁.num.toNat * q₂.den, q₂.num.toNat * q₁.den, q₁.den * q₂.den,
    Nat.mul_pos q₁.den_pos q₂.den_pos, ?_, ?_⟩
  · have e : ((q₁.num.toNat : ℕ) : ℚ) = q₁.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₁)
    have hd : (q₂.den : ℚ) ≠ 0 := by exact_mod_cast q₂.den_ne_zero
    push_cast
    rw [e, mul_div_mul_right _ _ hd, Rat.num_div_den]
  · have e : ((q₂.num.toNat : ℕ) : ℚ) = q₂.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₂)
    have hd : (q₁.den : ℚ) ≠ 0 := by exact_mod_cast q₁.den_ne_zero
    push_cast
    rw [e, mul_comm (q₁.den : ℚ) (q₂.den : ℚ), mul_div_mul_right _ _ hd, Rat.num_div_den]

theorem exists_eff_off_pt_ample_class : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N₀ : LB X) (A : CartierDiv X) (x : X) (r : ℕ) (lam μ : ℚ), N₀.IsLB → IsNef ℂ N₀ → IsAmpleLB (toLB A) → 0 < r → lam ≤ 1 → 0 < μ → ∃ (M : ℕ) (E : CartierDiv X), 0 < M ∧ E.Eff ∧ x ∉ E.supp ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB E] : ℚ) / M = (1 - lam) * interNumRed ℂ C ![N₀] / r + μ * interNumRed ℂ C ![toLB A] := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro N₀ A x r lam μ hN₀ hNef hA hr hlam hμ
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  obtain ⟨a, b, M, hM, ha, hb⟩ :=
    exists_common_den_nonneg ((1 - lam) / r) μ (div_nonneg (by linarith) hr'.le) hμ.le
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb; simp at hb; linarith
    · exact h
  have hAb : IsAmpleLB (lbPow (toLB A) b) := (isAmpleLB_pow_iff hA.isLB hb1).2 hA
  have hNa : IsNef ℂ (lbPow N₀ a) := hNef.pow hA a
  have hP : (tens (lbPow (toLB A) b) (lbPow N₀ a)).IsLB := isLB_tens hAb.isLB hNa.isLB
  have hPa : IsAmpleLB (tens (lbPow (toLB A) b) (lbPow N₀ a)) :=
    isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp _ _ _ hAb hNa hP
      (cls_tens hAb.isLB hNa.isLB hP)
  obtain ⟨n, hn, s, hx, -, -⟩ := hPa.exists_affine_le (x := x) (U := ⊤) trivial
  have hgen : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  have hLn := isLB_lbPow hPa.isLB n
  refine ⟨M * n, divOfSec hLn s hgen, Nat.mul_pos hM hn, eff_divOfSec_of_sec hLn s hgen,
    notMem_supp_divOfSec.2 hx, fun C hC => ?_⟩
  have hcls : toPic (divOfSec hLn s hgen) = cls _ hLn :=
    (presents_divOfRatSec hLn (isRatSec_ratOfSec s hgen)).toPic_eq
  have e : cls (toLB (divOfSec hLn s hgen)) (isLB_toLB _) =
      (n * a) • cls N₀ hN₀ + (n * b) • cls (toLB A) (isLB_toLB A) := by
    change toPic (divOfSec hLn s hgen) = _
    rw [hcls, cls_lbPow hPa.isLB, cls_tens hAb.isLB hNa.isLB, cls_lbPow (isLB_toLB A),
      cls_lbPow hN₀]
    rw [smul_add, smul_smul, smul_smul, add_comm]
  rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ N₀ (toLB A) (isLB_toLB _) hN₀ (isLB_toLB A)
    (n * a) (n * b) C hC e]
  have hMn : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  rw [hb, mul_div_right_comm, ha]
  push_cast
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  intro S A B _ _ _ pr hP m
  letI cG : ∀ Z : Over S, CommGroup (Z ⟶ B) := fun Z => Hom.commGroup
  have mc : ∀ {T : Over S} (u v : T ⟶ A) (e : A ⟶ B), IsMonHom e → (u * v) ≫ e = (u ≫ e) * (v ≫ e) := by
    intro T u v e he
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
  have pc : ∀ {T : Over S} (x : T ⟶ A) (a : Fin 8),
      x ≫ (∏ b, pr b ^ m a b : A ⟶ B) = ∏ b, (x ≫ pr b) ^ m a b := by
    intro T x a
    let φ : (A ⟶ B) →* (T ⟶ B) :=
      { toFun := fun u => x ≫ u, map_one' := MonObj.comp_one x, map_mul' := fun u v => MonObj.comp_mul x u v }
    have := map_prod φ (fun b => pr b ^ m a b) Finset.univ
    simp only [map_zpow] at this
    exact this
  obtain ⟨f, hf, -⟩ := hP.2 A (fun a => ∏ b, pr b ^ m a b)
  refine ⟨f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_, hf⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  rw [mc _ _ _ (hP.1 a), Category.assoc, Category.assoc, Category.assoc, hf, pc, pc, pc,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [mc _ _ _ (hP.1 b), mul_zpow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEltPrescribedValuationsBalancedArchimedeanStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elt_prescribed_valuations_balanced_archimedean : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧ (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  first | exact @GlobalTheory.CovHt.exists_elt_balanced | exact GlobalTheory.CovHt.exists_elt_balanced | (intros; apply GlobalTheory.CovHt.exists_elt_balanced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPosStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (id : ℤ → ℤ) (Fin r → ℤ) := by
  first | exact @GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | exact GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | (intros; apply GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int <;> assumption)
end


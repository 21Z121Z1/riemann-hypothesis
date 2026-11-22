import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VampIsoOfSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimAdditionGraphPrincipalPolarisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0208

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdditionGraphThetaObjectCutOutBoundedDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.AddGraph

open GlobalTheory.CechPic

theorem pull_inv_cls {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨U, hU, ht⟩ := hs (default : PrimeSpectrum K)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun q _ => by rw [Subsingleton.elim q (default : PrimeSpectrum K)]; exact hU
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ht
  rw [cls_linComb hL, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_comp] at e
  obtain ⟨ψ, k⟩ : ∃ ψ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, ψ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have e' := congrArg (pull ψ) (add_neg_eq_zero.1 e)
  rwa [← pull_comp ψ, ← pull_comp ψ, k, pull_id, pull_id] at e'

theorem pull_inv_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : B ⟶ A)
    (hf : (GrpObj.inv : B ⟶ B) ≫ f = f ≫ (GrpObj.inv : A ⟶ A)) (c : Pic A.left)
    (hc : pull (GrpObj.inv : A ⟶ A).left c = c) :
    pull (GrpObj.inv : B ⟶ B).left (pull f.left c) = pull f.left c := by
  rw [← pull_comp, ← Over.comp_left, hf, Over.comp_left, pull_comp, hc]

theorem lab_add {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (a a' : Ix g k) : t.lab (a + a') = t.lab a * t.lab a' := by
  haveI := t.ab.comm
  simp only [TObj.lab, Out.linComb, List.prod_ofFn]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, Pi.add_apply, ZMod.val_add]
  exact (pow_eq_pow_mod _ (t.torsion i)).symm

def red (g : ℕ) {k k' : ℕ} (h : k' ∣ k) (a : Ix g k) : Ix g k' := fun i => ZMod.castHom h (ZMod k') (a i)

theorem red_surjective (g : ℕ) {k k' : ℕ} (h : k' ∣ k) : Function.Surjective (red g h) := fun a =>
  ⟨fun i => (ZMod.castHom_surjective h (a i)).choose, funext fun i => (ZMod.castHom_surjective h (a i)).choose_spec⟩

theorem modEq_of_red {g k k' : ℕ} [NeZero k] (h : k' ∣ k) {a a' : Ix g k} (e : red g h a = red g h a') (i) :
    (a i).val ≡ (a' i).val [MOD k'] := by
  have := congrFun e i
  simp only [red, ZMod.castHom_apply, ZMod.cast_eq_val] at this
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this

theorem square_data {K : Type} [Field K] (P P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A)
    (h₁ : IsMonHom (e.hom ≫ fst P.A P.A)) (h₂ : IsMonHom (e.hom ≫ snd P.A P.A)) (Z : Over (Sp K)) (π : Z ⟶ P.A)
    [IsIso π] (N : ℕ) (M : LB (Z ⊗ Z).left) (hM : M.IsLB)
    (hc : cls M hM = N • pull (fst Z Z ≫ π).left (cls P.L P.isLB) + N • pull (snd Z Z ≫ π).left (cls P.L P.isLB) +
      N • pull ((fst Z Z ≫ π) * (snd Z Z ≫ π)).left (cls P.L P.isLB)) :
    ∃ (E : (Z ⊗ Z).left ≅ P₂.A.left), E.hom ≫ P₂.A.hom = (Z ⊗ Z).hom ∧ SymB (A := P₂.A) (M.pull E.inv) ∧
      (∀ n r, SectionsHaveFiniteDimension (P.A ⊗ P.A).hom (lbPow (LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left,
        (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]) n) r → SectionsHaveFiniteDimension (Z ⊗ Z).hom (lbPow M n) r) ∧
      (∀ x y : Out.baseOver (Sp K) ⟶ Z, (lift (x ≫ π) (y ≫ π) ≫ e.inv).left ≫ E.inv = (lift x y).left) ∧
      ∀ (k : ℕ) (I : Type) (u : I → (Out.baseOver (Sp K) ⟶ P.A)), (∀ x, x ^ k = 1 → ∃ i, u i = x) →
        ∀ x : Out.baseOver (Sp K) ⟶ P₂.A, x ^ k = 1 → ∃ i : I × I, lift (u i.1) (u i.2) ≫ e.inv = x := by
  haveI := P.isAb.comm
  let F : Z ⊗ Z ≅ P.A ⊗ P.A := tensorIso (asIso π) (asIso π)
  have F₁ : F.hom ≫ fst _ _ = fst Z Z ≫ π := tensorHom_fst _ _
  have F₂ : F.hom ≫ snd _ _ = snd Z Z ≫ π := tensorHom_snd _ _
  let G : Z ⊗ Z ≅ P₂.A := F ≪≫ e.symm
  have G₁ : G.inv ≫ fst Z Z ≫ π = e.hom ≫ fst _ _ := by
    rw [← F₁]; simp [G]
  have G₂ : G.inv ≫ snd Z Z ≫ π = e.hom ≫ snd _ _ := by
    rw [← F₂]; simp [G]
  have hinv := pull_inv_cls P.A P.L P.isLB P.sym
  refine ⟨(Over.forget _).mapIso G, Over.w G.hom, ?_, fun n r H => ?_, fun x y => ?_,
    fun k I u hu x hx => ?_⟩
  · show LBIso (M.pull G.inv.left) ((M.pull G.inv.left).pull (GrpObj.inv : P₂.A ⟶ P₂.A).left)
    refine (cls_eq_iff (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)).1 ?_
    rw [cls_pull (pull_isLB hM _), cls_pull hM, hc]
    simp only [map_add, map_nsmul, ← pull_comp G.inv.left, ← Over.comp_left, Hom.mul_def, ← Category.assoc G.inv (lift _ _), comp_lift, G₁, G₂]
    have i₁ : (GrpObj.inv : P₂.A ⟶ P₂.A) ≫ e.hom ≫ fst _ _ = (e.hom ≫ fst _ _) ≫ (GrpObj.inv : P.A ⟶ P.A) :=
      GrpObj.inv_hom _
    have i₂ : (GrpObj.inv : P₂.A ⟶ P₂.A) ≫ e.hom ≫ snd _ _ = (e.hom ≫ snd _ _) ≫ (GrpObj.inv : P.A ⟶ P.A) :=
      GrpObj.inv_hom _
    rw [pull_inv_hom _ i₁ _ hinv, pull_inv_hom _ i₂ _ hinv, pull_inv_hom _ _ _ hinv]
    rw [← Hom.mul_def, MonObj.comp_mul, i₁, i₂, ← Hom.inv_def, ← Hom.inv_def, ← Hom.inv_def, mul_inv]
  · have hN := LB.isLB_linComb P.isLB (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left,
        (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
    have hNn := LB.isLB_linComb hN (K := PUnit) (fun _ => 𝟙 _) (fun _ => (n : ℤ))
    have hMn := LB.isLB_linComb hM (K := PUnit) (fun _ => 𝟙 _) (fun _ => (n : ℤ))
    have H' : SectionsHaveFiniteDimension (F.hom.left ≫ (P.A ⊗ P.A).hom) (LB.pull _ F.hom.left) r := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ hNn).2.2.2.2.2 _ ((Over.forget _).mapIso F) r).1 H
    rw [Over.w F.hom] at H'
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ (pull_isLB hNn _)).2.1 _ hMn ?_).1 r H'
    refine (cls_eq_iff (pull_isLB hNn _) hMn).1 ?_
    rw [cls_pull hNn, cls_lbPow hN, cls_lbPow hM, hc, cls_linComb P.isLB, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, natCast_zsmul, map_add, map_nsmul,
      ← pull_comp, ← Over.comp_left, MonObj.comp_mul, F₁, F₂]
  · show (lift (x ≫ π) (y ≫ π) ≫ e.inv).left ≫ G.inv.left = _
    rw [← Over.comp_left]
    congr 1
    simp [G, F]
  · obtain ⟨a₁, ha₁⟩ := hu (x ≫ e.hom ≫ fst _ _) (by rw [← MonObj.pow_comp, hx, MonObj.one_comp])
    obtain ⟨a₂, ha₂⟩ := hu (x ≫ e.hom ≫ snd _ _) (by rw [← MonObj.pow_comp, hx, MonObj.one_comp])
    refine ⟨(a₁, a₂), ?_⟩
    rw [ha₁, ha₂, Iso.comp_inv_eq]
    ext1 <;> simp

end GlobalTheory.AddGraph

open GlobalTheory.AddGraph GlobalTheory.CechPic in

theorem GlobalTheory.cutBy_graph_addition : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (M₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (th₂ : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2) → M₂.Sec), M₂.IsLB → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (v₁ v₂ : _ → T), SecCoord _ σ (x ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₁ → SecCoord _ σ (x ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h)) → CutBy (graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K)))) ((fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A))).left) Q d (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  have hn1 := hn.one_lt
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, H⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion hL hL2 (2 * g) (2 * (n ^ 2) ^ 2)
    ((Ix g ((n ^ 2) ^ 2) × Ix g ((n ^ 2) ^ 2)) × Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdiv : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdiv' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdiv 2
  have hδ : 3 ^ g * ((n ^ 2) ^ 2) ^ (2 * g) ≤ (2 * (n ^ 2) ^ 2) ^ (2 * g) := by
    rw [mul_pow 2, pow_mul 2]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) g)
  obtain ⟨Q, HQ⟩ := H _ hδ ((Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2))
    (Prod.map (Prod.map (red g hdiv') (red g hdiv')) (red g hdiv'))
    (((red_surjective g hdiv').prodMap (red_surjective g hdiv')).prodMap (red_surjective g hdiv'))
  refine ⟨Q, d, fun K _ _ β t σ p M₂ th₂ hM₂ hemb hseg hp => ?_⟩
  obtain ⟨hiso, hH, hva, hHiso, hper, -, hlab⟩ := GlobalTheory.embSec_veryAmple_periodic hL hL2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdiv
    (hn.two_le.trans (Nat.le_self_pow two_ne_zero n)) hemb
  haveI := t.ab.comm
  haveI hπ : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A) := by
    haveI : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp K))) t.A)) := hiso
    exact isIso_of_reflects_iso _ (Over.forget _)
  have hZ : (fst (Over.mk (𝟙 (Sp K))) t.A).left = ((Over.mk (𝟙 (Sp K))) ⊗ t.A).hom := (Category.comp_id _).symm.trans (Over.w (fst (Over.mk (𝟙 (Sp K))) t.A))
  rw [hZ] at hva
  obtain ⟨hva₂, hiso₂, hper₂⟩ := GlobalTheory.ZV.SegreSquare.vamp_iso_of_segre_coordinates K _ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) _ σ M₂ th₂ hH hM₂ hva hseg
  suffices key : ∀ add : ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⊗ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⟶ (Over.mk (𝟙 (Sp K))) ⊗ t.A, add ≫ snd (Over.mk (𝟙 (Sp K))) t.A =
      (fst ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ≫ snd _ t.A) * (snd ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ≫ snd _ t.A) →
      CutBy (graphIdeal (((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⊗ ((Over.mk (𝟙 (Sp K))) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ add.left) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) from
    key _ (lift_snd _ _)
  intro add hadd'
  obtain ⟨M, th, hM, hvaM, hisoM, hI, hco, hperM⟩ := GlobalTheory.ZV.GraphSystem.exists_product_system K _ _ _ _ _ _ _ _ M₂ _ th₂ σ (𝟙 _) add.left hM₂ hH hva₂ hva
    inferInstance (Category.id_comp _) (Over.w add)
  obtain ⟨P₂, e, h₁, h₂, hg, -⟩ := GlobalTheory.SquarePol.exists_square K t.pol
  have cH := (cls_eq_iff hH (pull_isLB (LB.isLB_linComb t.isLB _ _) _)).2 hHiso
  rw [cls_pull (LB.isLB_linComb t.isLB _ _), cls_lbPow t.isLB, map_nsmul] at cH
  have c₂ := (cls_eq_iff hM₂ (LB.isLB_linComb hH _ _)).2 hiso₂
  rw [cls_linComb hH, Fin.sum_univ_two, cH] at c₂
  have cM := (cls_eq_iff (LB.isLB_div hM (pull_isLB hM₂ _)) (pull_isLB hH _)).2 hisoM
  rw [cls_div hM (pull_isLB hM₂ _), cls_pull hM₂, cls_pull hH, pull_id, sub_eq_iff_eq_add', c₂, cH] at cM
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, map_nsmul, ← pull_comp, ← Over.comp_left, hadd'] at cM
  obtain ⟨E, hE, hsym, hH0, hpt, htor⟩ := @square_data K _ t.pol P₂ e h₁ h₂ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) (snd (Over.mk (𝟙 (Sp K))) t.A) hπ ((n ^ 2) ^ 2) M hM cM
  rw [hI, ← hE]
  refine HQ K P₂ hg _ E M th (n ^ j) _ (fun h => lift (t.lab h.1 ^ n ^ j) (t.lab h.2 ^ n ^ j) ≫ e.inv) _ hM hsym
    (hE ▸ hvaM) (fun a a' haa => ?_) (fun m hm => ?_) ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn1).le) ?_
    (htor _ _ (fun h => t.lab h ^ n ^ j) hlab) (fun h => ?_)
  · have e₁ := congrArg (fun z => z.1.1) haa
    have e₂ := congrArg (fun z => z.1.2) haa
    have e₃ := congrArg (fun z => z.2) haa
    exact hperM a a' (hper₂ _ _ (hper _ _ (modEq_of_red hdiv' e₁)) (hper _ _ (modEq_of_red hdiv' e₂)))
      (hper _ _ (modEq_of_red hdiv' e₃))
  · rw [hE, Nat.mul_assoc, ← mul_pow]
    exact hH0 m _ (GlobalTheory.sectionsDim_additionGraph_principalPolarisation hL hL2 K t.pol _ (Nat.one_le_iff_ne_zero.2 (NeZero.ne _)) m hm)
  · have u := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow] at u
    exact ne_zero_pow two_ne_zero u
  · have k : (lift (t.lab h.1 ^ n ^ j) (t.lab h.2 ^ n ^ j) ≫ e.inv).left ≫ E.inv =
        (lift (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.1 ^ n ^ j)) (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.2 ^ n ^ j))).left := by
      refine Eq.trans ?_ (hpt _ _)
      exact congrArg (fun z => (z ≫ e.inv).left ≫ E.inv) (congrArg₂ lift (lift_snd _ _).symm (lift_snd _ _).symm)
    refine k ▸ hco K _ (fun i => p h.1 i.1 * p h.2 i.2) (p (h.1 + h.2)) (hseg K _ _ _ ?_ ?_) ?_
    · rw [Category.comp_id, ← Over.comp_left, lift_fst]; exact hp _
    · rw [Category.comp_id, ← Over.comp_left, lift_snd]; exact hp _
    · have : lift (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.1 ^ n ^ j)) (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.2 ^ n ^ j)) ≫ add =
          lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (h.1 + h.2) ^ n ^ j) := by
        rw [← cancel_mono (snd (Over.mk (𝟙 (Sp K))) t.A), Category.assoc, hadd', MonObj.comp_mul, lab_add, mul_pow]
        simp
      rw [← Over.comp_left, this]; exact hp _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  first | exact @GlobalTheory.TopOfFamily.exists_top | exact GlobalTheory.TopOfFamily.exists_top | (intros; apply GlobalTheory.TopOfFamily.exists_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_model_of_local_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  first | exact @GlobalTheory.GlobalModel.exists_global_model | exact GlobalTheory.GlobalModel.exists_global_model | (intros; apply GlobalTheory.GlobalModel.exists_global_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.SystemAmple

theorem exists_system_ampFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  intro hx h1 h2 h3 htop E _ _ _ H D Xo hpq hN
  classical
  obtain ⟨⟨n₀, n₁, a₀, a₁, hne⟩, -⟩ := GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level E H
  let n : Bool → ℕ := fun i => cond i n₁ n₀
  have aux : ∀ i, AuxiliaryInertOddPrime H (n i) := fun i => by cases i <;> assumption
  choose J k T hJ hamp using fun i => htop E H D hpq Xo (n i) (aux i)
  let B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀ := fun i l₀ h =>
    (GlobalTheory.T.exists_base_model_semiAbelian hx h1 h2 h3 E H D Xo hpq hN (n i) (J i) (T i) l₀ (aux i) (hJ i) h).some
  let ch : ℕ → Bool := fun p => decide (n₀ = p)
  have ch_ne : ∀ p, n (ch p) ≠ p := by
    intro p
    by_cases h : n₀ = p
    · have : ch p = true := by simp [ch, h]
      rw [this]
      exact fun h' => hne (h.trans h'.symm)
    · have : ch p = false := by simp [ch, h]
      rw [this]
      exact h
  have key : ∀ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (i : Idx H p),
      ∃ Y : Model (Xo i.l) i.c (i.c.V W).subtype, ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
        Raises (B (ch p) l₀ h.1) Y := by
    intro p W hp hW i
    obtain ⟨hex, hsp, -⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
    obtain ⟨l₀, h⟩ := hex i.l i.good
    obtain ⟨hdvd, hcop, -⟩ := hsp i.l l₀ h
    obtain ⟨hded, -, hb⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
    have hnp : (n (ch p)).Coprime p := (Nat.coprime_primes (aux _).1 hp).2 (ch_ne p)
    have hz : zeta 1 ∈ i.c.F := by
      have : zeta 1 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    obtain ⟨b, hbi⟩ := hb (n (ch p) * l₀.M) 1 (Nat.Coprime.mul_left hnp hcop) one_pos hz
    obtain ⟨Y, hY⟩ := GlobalTheory.LocalModelExists.exists_model_raises h1 h2 h3 E H D Xo _ _ (T (ch p)) hN l₀ i.l
      (B (ch p) l₀ h.1) i.c _ (i.c.V W).subtype b (aux _).1.pos hdvd hded hbi
    exact ⟨Y, l₀, h, hY⟩
  choose Y hY using key
  exact ⟨⟨n, J, aux, hJ, T, B, ch, ch_ne, Y, hY⟩, fun i => ⟨k i, hamp i⟩⟩

end GlobalTheory.SystemAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegDataFiniteUnramified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

theorem eq_of_basis {κ La Γ : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup La] [CommGroup Γ]
    (bas : (κ → ℤ) ≃ₗ[ℤ] La) (F F' : La → Γ) (hF : ∀ x y, F (x + y) = F x * F y)
    (hF' : ∀ x y, F' (x + y) = F' x * F' y) (h : ∀ i, F (bas (Pi.single i 1)) = F' (bas (Pi.single i 1))) : F = F' := by
  let G : La →+ Additive Γ := AddMonoidHom.mk' (fun x => Additive.ofMul (F x)) fun x y => congrArg _ (hF x y)
  let G' : La →+ Additive Γ := AddMonoidHom.mk' (fun x => Additive.ofMul (F' x)) fun x y => congrArg _ (hF' x y)
  have e : G.toIntLinearMap ∘ₗ bas.toLinearMap = G'.toIntLinearMap ∘ₗ bas.toLinearMap :=
    (Pi.basisFun ℤ κ).ext fun i => by
      rw [Pi.basisFun_apply]
      exact congrArg Additive.ofMul (h i)
  funext x
  obtain ⟨y, rfl⟩ := bas.surjective x
  exact Additive.ofMul.injective (LinearMap.congr_fun e y)

theorem mul_of_isGrpPullback {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y z : 𝟙_ (Over B') ⟶ G')
    (x₀ y₀ : 𝟙_ (Over B) ⟶ G) (hx : x.left ≫ φ = f ≫ x₀.left) (hy : y.left ≫ φ = f ≫ y₀.left)
    (hz : z.left ≫ φ = f ≫ (x₀ * y₀).left) : z = x * y := by
  let U : Over.mk ((𝟙_ (Over B')).hom ≫ f) ⟶ 𝟙_ (Over B) := Over.homMk f (by simp)
  have e := H.2 (𝟙_ (Over B')) x y (U ≫ x₀) (U ≫ y₀) hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  refine Over.OverMorphism.ext (H.1.hom_ext (hz.trans e) ?_)
  rw [Over.w, Over.w]

theorem exists_siegData_finite_unramified : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o), Odd k → 3 ≤ k → (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → em (b.ζ : o) = zeta k → ArBase em → ∀ (X : Scheme.{0}) (s : X ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H X), PELRep D a bas ρ t → IsPEL D a bas ρ t τ → ∀ (p : ℕ) (Ag : SiegelFamily g p k), p.Prime → k.Coprime p → SRep Ag → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ lev : D.La → (𝟙_ (Over X) ⟶ τ.G), LevUnder D a bas t τ lev → ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i → GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb → ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ X) (tT : SAB H T) (ν : SABMap tT τ f) (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT s (spMap bb) → (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) → ∃ u : T ⟶ pullback Ag.s (spMap z), GlobalTheory.Models.SiegData sT tT levT Ag z bas' u ∧ IsFinite u ∧ FormallyUnramified u := by
  intro hL hL2 hTh E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl k o _ b em ρ hodd h3 hsq hρ hζ hAr X s t τ hrep hpel
    p Ag hp hkp hS bas' hbas' lev hlev O _ i z bb hi hz hbb T sT f tT ν levT hpb hlevT
  obtain ⟨t', ht'⟩ := GlobalTheory.tObj_pull o g k J b X T s (sT ≫ spMap bb) f t hpb.w
  obtain ⟨c, u, hc, hu, hpbS, hfin, hunr⟩ := GlobalTheory.SiegelClassify.exists_classifying_finite_unramified hL hL2 hTh E H D g J a w w' bas hpq hbas hw hw' hcl k o b em ρ
    hodd h3 hsq hρ hζ hAr X s t τ hrep hpel p Ag hp hkp hS bas' hbas' O i z bb hi hz hbb T sT f hpb t' ht'
  refine ⟨u, ?_, hfin, hunr⟩
  obtain ⟨ψ, hψ, hψL, hψp, -⟩ := ht'
  obtain ⟨φ₀, hφ₀, hφL, -, hadd, hφp⟩ := hlev
  letI := t'.ab.comm
  obtain ⟨χ, hχ, hχL, hχp⟩ := hc
  have hcart : IsGrpPullback tT.G t.A f (ν.φ ≫ φ₀.hom.left) :=
    (ν.cart.comp (isGrpPullback_of_iso φ₀)).congr (Category.comp_id _) rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso hψ hcart
  have hν : LBIso tT.PP.L (τ.PP.L.pull ν.φ) := ν.lin.imp fun _ h => h.1
  have h₁ : LBIso tT.PP.L (t.L.pull (ν.φ ≫ φ₀.hom.left)) :=
    LBIso.trans tT.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) hν (lbIso_pull_pull hφL _)
  have h₂ : LBIso t'.L (tT.PP.L.pull e.hom.left) := by
    have := lbIso_pull_pull h₁ e.hom.left
    rw [hee] at this
    exact LBIso.trans t'.isLB (pull_isLB t.isLB _) (pull_isLB tT.PP.isLB _) hψL this.symm
  have h₃ := lbIso_pull_pull (lbIso_lam_pull e.hom t'.isLB tT.PP.isLB h₂) (χ.hom ⊗ₘ χ.hom).left
  have hm : IsMonHom (χ ≪≫ e).hom := inferInstanceAs (IsMonHom (χ.hom ≫ e.hom))
  have haddT : ∀ x y, levT (x + y) = levT x * levT y := fun x y =>
    mul_of_isGrpPullback ν.cart _ _ _ (lev x) (lev y) (hlevT x) (hlevT y) (by rw [← hadd]; exact hlevT _)
  have key : (fun x => c.lev (bas'.symm x) ≫ χ.hom ≫ e.hom) = levT := by
    refine eq_of_basis bas _ _ (fun x y => ?_) haddT fun j => ?_
    · rw [map_add, c.lev_add, MonObj.mul_comp]
    · refine Over.OverMorphism.ext (hcart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
      have q₁ : (levT (bas (Pi.single j 1))).left ≫ ν.φ ≫ φ₀.hom.left = f ≫ (t.pt j).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ₀.hom.left) (hlevT _)).trans
          ((Category.assoc _ _ _).trans (congrArg (f ≫ ·) (hφp j))))
      have q₂ : (c.lev (bas'.symm (bas (Pi.single j 1))) ≫ χ.hom).left ≫ e.hom.left ≫ ν.φ ≫ φ₀.hom.left =
          f ≫ (t.pt j).left := by
        rw [hee, hχp]
        exact hψp j
      refine Eq.trans ?_ (q₂.trans q₁.symm)
      simp only [Over.comp_left, Category.assoc]
  refine ⟨c, (χ ≪≫ e).hom.left, (χ.hom ⊗ₘ χ.hom).left ≫ (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso _, ⟨?_, ?_⟩,
    LBIso.trans c.isLB (pull_isLB (DVR.linComb_isLB _ t'.isLB _ _) _) (pull_isLB (DVR.linComb_isLB _ tT.PP.isLB _ _) _)
      hχL h₃, fun v => ?_, hu, hpbS⟩
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    simp
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    simp
  · rw [← key]
    simp

end GlobalTheory.ZM.SiegClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOverCompleteDvrSpecialisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  first | exact @GlobalTheory.ZM.exists_obj_over_complete_dvr | exact GlobalTheory.ZM.exists_obj_over_complete_dvr | (intros; apply GlobalTheory.ZM.exists_obj_over_complete_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transition_map_raised_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀') (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (l₂ : Level H) (c₂ : Coeff l₂) (O₂ : Type) [CommRing O₂] (β₂ : O₂ →+* c₂.F) (Y₂ : Model (Xo l₂) c₂ β₂) (b : O →+* O₂), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → l₀.Dvd l → l₀'.Dvd l₂ → l.Dvd l₂ → c.F ≤ c₂.F → IsDedFrac β → IsDedFrac β₂ → IsInc (c.F.val.toRingHom.comp β) (c₂.F.val.toRingHom.comp β₂) b → Raises B Y → Raises B' Y₂ → ∃ π : Y₂.X ⟶ Y.X, IsTransition Y Y₂ b π := by
  first | exact @GlobalTheory.RaisedTransition.exists_isTransition | exact GlobalTheory.RaisedTransition.exists_isTransition | (intros; apply GlobalTheory.RaisedTransition.exists_isTransition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionEndomorphismGraphOfTorsionActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertFunction_endomorphismGraph_of_torsionAction : Out.Laws → Out.Laws2 → ∀ (g N κ l j : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (l ^ j))), 1 ≤ N → l.Prime → (N * (1 + κ)) ^ (2 * g) < l ^ j → ∃ δ ≤ (N * (1 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f : P.A ⟶ P.A), P.g = g → (l : K) ≠ 0 → IsPrimitiveRoot ζ (l ^ j) → TorsBasis P.A (l ^ j) pt → (∀ i i', Out.WeilIs P.A P.L ((l ^ j : ℕ) : ℤ) (pt i) (pt i') (unitOn (ζ ^ Out.stdSymp g i i'))) → IsMonHom f → ActsBy pt f Mat → Out.RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) → SymB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) e) (δ * e ^ g) := by
  first | exact @GlobalTheory.hilbert_graph_of_torsion | exact GlobalTheory.hilbert_graph_of_torsion | (intros; apply GlobalTheory.hilbert_graph_of_torsion <;> assumption)
end


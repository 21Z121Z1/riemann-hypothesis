import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
import Development.EtaleCohomology.KummerTheory.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0016
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0041
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0031
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyRepresentatives
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Et

theorem UpperTheory.cohomology_representatives :
    SlopeTestRemainingChoices → ∀ (R : Type) [CommRing R] (I : Cx R) (U : Scheme.{0}) (m n k : ℤ), m + 1 = n → n + 1 = k →
      (∀ z : Sec (I.X n) U, Sec.map (I.d n k) z = 0 → ∃ c, Rep z c) ∧ (∀ c, ∃ z : Sec (I.X n) U, Rep z c) ∧
      (∀ (z : Sec (I.X n) U) c, Rep z c → Sec.map (I.d n k) z = 0 ∧ (c = 0 ↔ ∃ y : Sec (I.X m) U, Sec.map (I.d m n) y = z)) ∧
      (∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z + z') (c + c') ∧ Rep (z - z') (c - c') ∧ (c = c' ↔ ∃ y : Sec (I.X m) U, z = z' + Sec.map (I.d m n) y)) ∧
      Rep (0 : Sec (I.X n) U) 0 ∧ ∀ (a : ℕ) (z : Sec (I.X n) U) c, Rep z c → Rep (a • z) (a • c) := by
  intro A R _ I U m n k hmn hnk
  have hrep := A.rep R U I m n k hmn hnk
  have hev := (A.evs R (E := sch.obj U) (I := I) (n := n)).1
  have hvan : ∀ (z : Sec (I.X n) U) c, Rep z c →
      Sec.map (I.d n k) z = 0 ∧ (c = 0 ↔ ∃ y : Sec (I.X m) U, Sec.map (I.d m n) y = z) := by
    rintro z c ⟨α, rfl, rfl⟩
    exact hrep.2 α
  have hadd : ∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z + z') (c + c') := by
    rintro z z' c c' ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    exact ⟨α + β, CohomologyClass.mk_add α β, (hev α.1 β.1 0 n (by simp) U (𝟙 U)).1⟩
  have hsub : ∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z - z') (c - c') := by
    rintro z z' c c' ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    exact ⟨α - β, CohomologyClass.mk_sub α β, (hev α.1 β.1 0 n (by simp) U (𝟙 U)).2.1⟩
  have hzero : Rep (0 : Sec (I.X n) U) 0 :=
    ⟨0, CohomologyClass.mk_zero _ _ _, (hev 0 0 0 n (by simp) U (𝟙 U)).2.2.1⟩
  refine ⟨?_, ?_, hvan, ?_, hzero, ?_⟩
  · intro z hz
    obtain ⟨α, h0, -⟩ := hrep.1 z hz
    refine ⟨CohomologyClass.mk α, α, rfl, ?_⟩
    rw [h0]
    change ((I.X n).obj.map (𝟙 (op U))).hom z = z
    rw [CategoryTheory.Functor.map_id]
    rfl
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    exact ⟨_, α, rfl, rfl⟩
  · intro z z' c c' h h'
    refine ⟨hadd _ _ _ _ h h', hsub _ _ _ _ h h', ?_⟩
    rw [← sub_eq_zero, (hvan _ _ (hsub _ _ _ _ h h')).2]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro a z c h
    induction a with
    | zero => simpa using hzero
    | succ a ih => simpa [succ_nsmul] using hadd _ _ _ _ ih h

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CurvePicardOfSelmerPicardOfModelCurve
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.curve_picard_of_selmerPicard_of_modelCurve :
    LateralTheory.E.LeafPicCut.LeafSelPic → LateralTheory.E.LeafCurveVCut.LeafModelCurve → LateralTheory.E.E4.LeafPic := by
  intro hSel hModel hH q _ k B _ _ _ _ _ _ hq
  by_cases hB : IsField B
  · letI := hB.toField
    haveI : Subsingleton (CommRing.Pic B) := inferInstance
    exact Finite.of_subsingleton
  · haveI hK : IsFunctionField k (FractionRing B) := UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType k B hB
    obtain ⟨u, hu, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := FractionRing B)
    obtain ⟨C0, c0, x, ψ, hc, hx, hψ⟩ := hModel k (FractionRing B) u hu hfd
    haveI : IsIntegral C0 := hc.1
    obtain rfl : x = genericPoint C0 := hx.eq (genericPoint_spec C0)
    letI : Algebra k C0.functionField :=
      (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ).hom.toAlgebra
    letI : Algebra (FractionRing B) C0.functionField := (Spec.preimage ψ).hom.toAlgebra
    haveI : IsScalarTower k (FractionRing B) C0.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have heq : Spec.map (CommRingCat.ofHom (algebraMap k C0.functionField)) =
        C0.fromSpecStalk (genericPoint C0) ≫ c0 := by
      change Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ) = _
      rw [Spec.map_comp, Spec.map_preimage, hψ]
    obtain ⟨hF, hch⟩ := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit hH q k hq c0 hc heq
    haveI := hF
    exact UpperTheory.finite_pic_torsion_of_finite_kummerSelmer hSel k B q
      (UpperTheory.finite_kummerSelmer_of_finite_extension k (FractionRing B) C0.functionField q hq (UpperTheory.finite_kummerSelmer_of_charts k _ q hch))
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SectionsBijectiveDisjointCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Et

theorem UpperTheory.sections_bijective_disjoint_cover :
    ∀ (R : Type) [CommRing R] (G : Shv R) {Y : Scheme.{0}} {ι : Type} (V : ι → Scheme.{0}) (j : ∀ a, V a ⟶ Y) [∀ a, IsOpenImmersion (j a)],
      (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) → (∀ y : Y, ∃ a, y ∈ Set.range (j a)) → Function.Bijective fun (x : Sec G Y) (a : ι) => Sec.res (j a) x := by
  intro R _ G Y ι V j _ hd hc
  have hop : IsOpenImmersion (Sigma.desc j) :=
    isOpenImmersion_sigmaDesc V j (fun a b hab => hd a b hab)
  have htop : (Sigma.desc j).opensRange = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨a, z, rfl⟩ := hc y
    refine ⟨(Sigma.ι V a) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hiso : IsIso (Sigma.desc j) := isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  have hb : Function.Bijective (fun x : Sec G Y => Sec.res (Sigma.desc j) x) := by
    have h1 : ∀ x : Sec G Y, Sec.res (inv (Sigma.desc j)) (Sec.res (Sigma.desc j) x) = x := by
      intro x
      have := congrArg (fun f => (G.obj.map f.op).hom x) (IsIso.inv_hom_id (Sigma.desc j))
      simpa [Sec.res] using this
    have h2 : ∀ x : Sec G (∐ V), Sec.res (Sigma.desc j) (Sec.res (inv (Sigma.desc j)) x) = x := by
      intro x
      have := congrArg (fun f => (G.obj.map f.op).hom x) (IsIso.hom_inv_id (Sigma.desc j))
      simpa [Sec.res] using this
    exact Function.bijective_iff_has_inverse.2 ⟨_, h1, h2⟩
  have heq : (fun (x : Sec G Y) (a : ι) => Sec.res (j a) x) =
      (fun (b : Sec G (∐ V)) (a : ι) => Sec.res (Sigma.ι V a) b) ∘
        (fun x : Sec G Y => Sec.res (Sigma.desc j) x) := by
    funext x a
    have e : G.obj.map (j a).op = G.obj.map (Sigma.desc j).op ≫ G.obj.map (Sigma.ι V a).op := by
      rw [← Functor.map_comp, ← op_comp, Sigma.ι_desc]
    show (G.obj.map (j a).op).hom x = _
    rw [e]
    rfl
  rw [heq]
  exact (GlobalTheory.T.sec_sigma_res_bijective R G V).comp hb

end
end


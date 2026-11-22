import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointGaloisConjugate
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem comp_hom_eq_one_of_torsion_pts (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ)
    (hn : (n : K) ≠ 0) (hker : ∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1)
    (T : Over (Sp K)) (x : T ⟶ A.X) (hx : x ^ n = 1) : x ≫ f.hom = 1 := by
  have hA := A.ab
  have hC := C.ab
  have := hA.proper
  have := hC.proper
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨_, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion A.X hu
  have hι : torsion.ι A.X n ≫ mulN A.X n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))
  set L := AlgebraicClosure K
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let P := (Over.pullback t).obj (torsion A.X n)
  let C' := (Over.pullback t).obj C.X
  have hP : Etale P.hom := by
    change Etale (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hPf : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hC' : IsProper C'.hom := by
    change IsProper (pullback.snd C.X.hom t)
    infer_instance
  have hPr : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  have hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t =
      pullback.fst (torsion A.X n).hom t ≫ g.left := fun g => by
    simp
    exact pullback.lift_fst _ _ _
  have hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) =
      (Over.pullback t).map (1 : torsion A.X n ⟶ C.X) := by
    refine TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_
    let z : Sp L ⟶ (torsion A.X n).left := y.left ≫ pullback.fst (torsion A.X n).hom t
    have hz : z ≫ (torsion A.X n).hom = t := by
      have e1 : y.left ≫ P.hom = 𝟙 _ := by
        change y.left ≫ pullback.snd (torsion A.X n).hom t = _
        simpa using Over.w y
      simp only [z, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      change (y.left ≫ P.hom) ≫ t = t
      rw [e1, Category.id_comp]
    let z' : ptOver K L ⟶ torsion A.X n := Over.homMk z hz
    have hw : (z' ≫ torsion.ι A.X n) ^ n = 1 := by
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have hk := hker (z' ≫ torsion.ι A.X n) hw
    have hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X) := by
      rw [MonObj.comp_one, ← Category.assoc, hk]
    have hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left :=
      congrArg CommaMorphism.left hk'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, hfst]
      simpa [z] using hkl
    · have w1 := Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))
      have w2 := Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))
      change _ ≫ pullback.snd C.X.hom t = _ at w1 w2
      rw [w1, w2]
  have hred : IsReduced (torsion A.X n).left := isReduced_of_smooth_of_isReduced (torsion A.X n).hom
  have hdom : IsDominant (pullback.fst (torsion A.X n).hom t) := inferInstance
  have h6 : torsion.ι A.X n ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_
    rw [← hfst, ← hfst, hEq]
  have e : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
  obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x :=
    ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
  rw [← e', Category.assoc, h6, MonObj.comp_one]

end GlobalTheory.AV.AbVar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstOrderValue

def evalSq {S : Type} [CommRing S] (e : S) (he : e * e = 0) : DualNumber S →+* S where
  toFun z := z.fst + e * z.snd
  map_one' := by simp
  map_mul' a b := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul]
    linear_combination (-(a.snd * b.snd)) * he
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]; ring

theorem evalSq_apply {S : Type} [CommRing S] (e : S) (he : e * e = 0) (z : DualNumber S) :
    evalSq e he z = z.fst + e * z.snd := rfl

theorem dual_apply {R S : Type} [CommRing R] [CommRing S] (f : DualNumber R →+* S) (z : DualNumber R) :
    f z = f (TrivSqZeroExt.inl z.fst) + f (TrivSqZeroExt.inl z.snd) * f DualNumber.eps := by
  have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps := by
    ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_mul]

theorem comp_prod_ofFn {C : Type*} [Category C] [CartesianMonoidalCategory C] {M A B : C} [MonObj M]
    (k : A ⟶ B) : ∀ {m : ℕ} (u : Fin m → (B ⟶ M)), k ≫ (List.ofFn u).prod = (List.ofFn fun i => k ≫ u i).prod
  | 0, u => by simp [MonObj.comp_one]
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, comp_prod_ofFn]

end GlobalTheory.FirstOrderValue

namespace GlobalTheory.FirstOrderValue

theorem valR_mul_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (c : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v c x.left → (∀ (S : Type) [CommRing S] (ψ : DualNumber Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U)) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), a.left = spMap ψ → (∀ b, IsTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) g₀ (v b) (w b)) → ∀ (O : t.G.left.Opens) (f : Γ(t.G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O → ⊤ ≤ ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left ⁻¹ᵁ O ∧ valR ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left O f = valR g₀ O f + ψ DualNumber.eps * ∑ b, ψ (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)) (c b)) * (valR (w b) O f).snd) := by
  intro E _ _ _ H X t U n v hv c x hx S _ ψ g₀ a w ha hw O f hO
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, U.1) →+* S, φ = ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := ⟨_, rfl⟩
  rw [← hφ] at hw
  obtain ⟨e, hedef⟩ : ∃ e : S, e = ψ DualNumber.eps := ⟨_, rfl⟩
  rw [← hedef]
  have he : e * e = 0 := by rw [hedef, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφs : ∀ s, φ s = ψ (TrivSqZeroExt.inl s) := fun s => by
    rw [hφ, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl]

  have hg₀ : g₀ ≫ t.G.hom = spMap φ ≫ chart U := by
    have h1 : a.left ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom := Over.w a
    rw [← h1, ha, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hφ]
  choose g'' v'' hg'' hv'' hw'' using hw
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  have hgg : ∀ b, g'' b = g' := fun b => Over.OverMorphism.ext (hg'' b)

  let h : tEpsG (g₀ ≫ t.G.hom) ⟶ Over.mk (chart U) :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) (by
      show (spMap _ ≫ spMap φ) ≫ chart U = spMap _ ≫ g₀ ≫ t.G.hom
      rw [Category.assoc, hg₀])
  have hy0 : ∀ b, smT (g₀ ≫ t.G.hom) 0 (v'' b) = 1 := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) 0 (v'' b)).left = spMap (epsMul 0) ≫ (v'' b).left := rfl
    have e1 : (epsMul (0 : S)).comp (dualMap φ) = ((algebraMap S (DualNumber S)).comp φ).comp
        (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
      apply RingHom.ext; intro z; ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [h1, hv'' b, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, e1, ← GlobalTheory.KSLin.spMap_comp_spMap,
      ← GlobalTheory.KSLin.spMap_comp_spMap, Category.assoc, Category.assoc, (hv b).2]
    have h2 : (h ≫ (1 : Over.mk (chart U) ⟶ t.G)).left = (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left :=
      congrArg (fun k : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G => k.left) (MonObj.comp_one h)
    have h3 : (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ≫ (1 : Over.mk (chart U) ⟶ t.G).left =
        (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left := h2
    rw [← h3, Category.assoc]

  obtain ⟨u, hu, hux⟩ := hx
  obtain rfl : x = (List.ofFn u).prod := (Over.OverMorphism.ext hux).symm

  let ρ := evalSq e he
  have hρψ : ∀ r, ψ.comp (epsMul r) = (ρ.comp (epsMul (φ r))).comp (dualMap φ) := by
    intro r
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply]
    rw [dual_apply ψ, ← hedef, evalSq_apply]
    simp [epsMul, dualMap, hφs]
    ring
  have hsp : spMap ρ ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.KSLin.spMap_comp_spMap]
    have : ρ.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp [ρ, evalSq_apply, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  let ρh : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap ρ) (by
      show spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, hsp, Category.id_comp])
  have hu' : ∀ b, a ≫ u b = ρh ≫ smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b) := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).left = spMap (epsMul (φ (c b))) ≫ (v'' b).left := rfl
    simp only [Over.comp_left]
    rw [h1, hv'' b, hu b, ha]
    show spMap ψ ≫ spMap (epsMul (c b)) ≫ v b = spMap ρ ≫ spMap (epsMul (φ (c b))) ≫ spMap (dualMap φ) ≫ v b
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hρψ]
  have hg'eq : (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) = ρh ≫ g' := by
    apply Over.OverMorphism.ext
    show g₀ = spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀
    rw [← Category.assoc, hsp, Category.id_comp]
  have hmain : (a ≫ (List.ofFn u).prod) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) =
      ρh ≫ (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) := by
    rw [comp_prod_ofFn, hg'eq, MonObj.comp_mul, comp_prod_ofFn, mul_comm]
    simp only [hu']
  have hP1 := GlobalTheory.KSLin.snd_sectionValue_translate_list_prod_induction g₀ g' rfl O hO f n v'' (fun b => φ (c b)) hy0
  have hQ0 : smT (g₀ ≫ t.G.hom) 0 (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) = g' := by
    rw [smT_mul, GlobalTheory.KSLin.smT_const g₀ g' rfl, hP1.1, _root_.mul_one]
  have hQ : ⊤ ≤ (Over.Hom.left (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod)) ⁻¹ᵁ O :=
    GlobalTheory.KSLin.top_le_of_smT_zero g₀ g' rfl O hO _ hQ0
  have hfst := GlobalTheory.KSLin.fst_comp_of_smT_zero g₀ g' rfl _ hQ0
  have hwb : ∀ b, (g' * v'' b).left = w b := fun b => by rw [← hgg b]; exact hw'' b
  rw [hmain, Over.comp_left]
  show ⊤ ≤ (spMap ρ ≫ _) ⁻¹ᵁ O ∧ valR (spMap ρ ≫ _) O f = _
  refine ⟨GlobalTheory.TanDeriv.comp_top_le ρ _ O hQ, ?_⟩
  have hOg : ⊤ ≤ g₀ ⁻¹ᵁ O := hO
  rw [GlobalTheory.KSLin.valR_spMap_comp ρ _ O hQ f, evalSq_apply, hP1.2]
  conv_rhs => rw [← hfst, GlobalTheory.KSLin.valR_spMap_comp _ _ O hQ f]
  simp only [hwb, hφs, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

end GlobalTheory.FirstOrderValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointGaloisConjugateStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_point_galois_conjugate : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ)
    (L L' : Set E) (T : CxPt 𝔠 φ L) (R : Type) [CommRing R] (σ : R →+* ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
    (N : I → Module.End R (HdR X₀.A)), T.IsOver σ X₀ δ₀ N →
    ∀ (g : ℂ ≃+* ℂ) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
      (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L' 0 X') (κ : ℂ),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p → κ ≠ 0 → U'.e = T.U.e → U'.c = T.U.c →
      (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
          U'.u.IsDiff (fun j ↦ κ * g (w j)) v') →
      (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
        (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
          ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) →
      ∃ T' : CxPt 𝔠 (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L', T'.IsOver ((g : ℂ →+* ℂ).comp σ) X₀ δ₀ N ∧
        T'.C * κ ^ Fintype.card I = g T.C ∧
        ∀ i, T'.U.h i = U'.h i ∧ T'.s i * T'.w i ^ 2 = κ ^ 2 * g (T.s i * T.w i ^ 2) := by
  first | exact @GlobalTheory.ConjTransport.exists_conj_point | exact GlobalTheory.ConjTransport.exists_conj_point | (intros; apply GlobalTheory.ConjTransport.exists_conj_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurveTangentCompatStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_torsion_point_compat : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (a a' : K), (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) → pt Λ₁ Ω₁ (io a') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (io a) := by
  first | exact @GlobalTheory.CMTorsion.ConjPt.conj_pt | exact GlobalTheory.CMTorsion.ConjPt.conj_pt | (intros; apply GlobalTheory.CMTorsion.ConjPt.conj_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistFunctionDecompositionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_curve_point_addition_compat : ∀ (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 → ∀ h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁, (∀ z', ∃ z, pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ∧ ∀ z w z' w', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z → pt Λ₁ Ω₁ w' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ w → pt Λ₁ Ω₁ (z' + w') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (z + w) := by
  first | exact @GlobalTheory.CMTorsion.Conj.pt_conj_onto_add | exact GlobalTheory.CMTorsion.Conj.pt_conj_onto_add | (intros; apply GlobalTheory.CMTorsion.Conj.pt_conj_onto_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationDifferentialZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_uniformization_differential_zero : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (n n' : ℕ) (u : HolUnif A L n)
    (u' : HolUnif A' L' n') (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
    v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff 0 v → u'.IsDiff 0 v' := by
  first | exact @GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback | exact GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback | (intros; apply GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationSemilinearMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_uniformization_semilinear_map : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (N : ℕ) (u : HolUnif A L N)
    (u' : HolUnif A' L' N), (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) →
    ∃ T : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ), Function.Injective T ∧
      ∀ (w : Fin N → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), IsTangent v →
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v → u'.IsDiff (T w) v' := by
  first | exact @GlobalTheory.ConjTangentSemilin.exists_semilinear_transport | exact GlobalTheory.ConjTangentSemilin.exists_semilinear_transport | (intros; apply GlobalTheory.ConjTangentSemilin.exists_semilinear_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceOfIsConnected
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.EtCover

variable {K : Type} [Field K]

def obj (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : Over (Sp K) := Over.mk (π ≫ A.X.hom)

def hom (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : obj A π ⟶ A.X := Over.homMk π rfl

@[simp] theorem obj_left (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : (obj A π).left = Y := rfl

@[simp] theorem obj_hom (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) :
    (obj A π).hom = π ≫ A.X.hom := rfl

@[simp] theorem hom_left (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : (hom A π).left = π := rfl

end GlobalTheory.AV.EtCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_coefficients_complexForm_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  first | exact @GlobalTheory.CxForm.contDiff_coeff_mul | exact GlobalTheory.CxForm.contDiff_coeff_mul | (intros; apply GlobalTheory.CxForm.contDiff_coeff_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderivStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U → DifferentiableOn ℂ τ U →
    ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  first | exact @GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | exact GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | (intros; apply GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateExistenceOfPeriodsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_existence_of_periods : GlobalTheory.Published.GaussManinPeriods → JetCalc → DiagFrame → CoordEx := by
  first | exact @GlobalTheory.LatJet.An.coordEx | exact GlobalTheory.LatJet.An.coordEx | (intros; apply GlobalTheory.LatJet.An.coordEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinateMap_etale_near_properFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  first | exact @GlobalTheory.Mum.fibre_etale_near | exact GlobalTheory.Mum.fibre_etale_near | (intros; apply GlobalTheory.Mum.fibre_etale_near <;> assumption)
end


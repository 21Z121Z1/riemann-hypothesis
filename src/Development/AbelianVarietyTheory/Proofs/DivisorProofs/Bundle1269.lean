import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import GroundTheory.AutomorphicForms.MeasuresModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem model_aeval_mulVec {K : UQ} {L : Type} [Field L] (e : K.E ≃+* L) {B : InvAlg K} {n : ℕ}
    (ψ : B.A ≃+ (Fin n → L)) (hs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (u : B.A)
    (g : Matrix (Fin n) (Fin n) L) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) (p : K.E[X]) (y : B.A) :
    ψ (aeval u p * y) = aeval g (p.map (e : K.E →+* L)) *ᵥ ψ y := by
  induction p using Polynomial.induction_on generalizing y with
  | C a =>
    rw [aeval_C, ← Algebra.smul_def, hs, Polynomial.map_C, aeval_C, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  | add p q hp hq =>
    rw [map_add, add_mul, map_add, hp, hq, Polynomial.map_add, map_add, Matrix.add_mulVec]
  | monomial k a h =>
    have h1 : aeval u (C a * X ^ (k + 1)) = aeval u (C a * X ^ k) * u := by
      rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, aeval_X]
    have h2 : aeval g ((C a * X ^ (k + 1)).map (e : K.E →+* L)) = aeval g ((C a * X ^ k).map (e : K.E →+* L)) * g := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X, Polynomial.aeval_mul, aeval_X]
    rw [h1, h2, mul_assoc, h, hu, Matrix.mulVec_mulVec]

theorem prod_herm_fst {K : UQ} (B₁ B₂ : InvAlg K) (x : (B₁.prod B₂).A) (y z : B₁.A) :
    (B₁.prod B₂).herm x ((y, 0) : B₁.A × B₂.A) ((z, 0) : B₁.A × B₂.A) = B₁.herm x.1 y z := by
  unfold InvAlg.herm
  have hel : x * (show (B₁.prod B₂).A from (y, 0)) * (B₁.prod B₂).σ (show (B₁.prod B₂).A from (z, 0)) =
      (show (B₁.prod B₂).A from (x.1 * y * B₁.σ z, 0)) := by
    refine Prod.ext rfl ?_
    show x.2 * 0 * B₂.σ 0 = 0
    simp
  rw [hel]
  exact (Algebra.trace_prod_apply (R := K.E) ((x.1 * y * B₁.σ z, 0) : B₁.A × B₂.A)).trans (by simp)

theorem neg_one_zpow_val_norm_mul (K : UQ) (d g : K.E) (hd : d ≠ 0) :
    (-1 : ℂ) ^ val K.O (d * g * K.c d) = ((K.eta g : ℚ) : ℂ) := by
  unfold UQ.eta
  by_cases hg : g = 0
  · subst hg; simp
  have hval : ∀ a b : K.E, a ≠ 0 → b ≠ 0 → val K.O (a * b) = val K.O a + val K.O b := by
    intro a b ha hb
    unfold val
    rw [Valuation.map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
    ring
  have hcd : K.c d ≠ 0 := by simpa using hd
  rw [hval _ _ (mul_ne_zero hd hg) hcd, hval _ _ hd hg, UnramNorm.val_c]
  have h2 : (-1 : ℂ) ^ (val K.O d + val K.O g + val K.O d) = (-1 : ℂ) ^ val K.O g := by
    rw [show val K.O d + val K.O g + val K.O d = 2 * val K.O d + val K.O g by ring,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
    norm_num
  rw [h2]
  push_cast
  rfl

end GlobalTheory.KapLat

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem kapSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  intro E _ _ _ w hns K e hB n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ x γ hM
  obtain ⟨ψ, hs, hu, hh⟩ := hM
  obtain ⟨-, -, hval, -⟩ := hB
  set P₁ : K.E[X] := Q₁.map e.symm.toRingHom with hP₁
  have hQ₁ : Q₁ = P₁.map (e : K.E →+* w.adicCompletion E) := by
    rw [hP₁, Polynomial.map_map]
    ext i
    simp
  have hunit : IsUnit (aeval u₂ P₁) := by
    obtain ⟨a, b, hab⟩ := hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
    have h := congrArg (aeval u₂) hab
    simp only [Polynomial.coe_mapRingHom, map_add, map_mul, map_one] at h
    rw [hF₂.2.1, mul_zero, add_zero] at h
    exact ⟨⟨aeval u₂ P₁, aeval u₂ a, by rw [mul_comm]; exact h, h⟩, rfl⟩
  have hker : ∀ y : (B₁.prod B₂).A, aeval γ.val Q₁ *ᵥ ψ y = 0 ↔ y.2 = 0 := by
    intro y
    rw [hQ₁, ← model_aeval_mulVec e ψ hs _ γ.val hu P₁ y, AddEquiv.map_eq_zero_iff]
    have hp1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 = aeval u₁ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have hp2 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).2 = aeval u₂ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have h1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).2 = aeval u₂ P₁ * y.2 := by
      rw [← hp2]; rfl
    have h0 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).1 = 0 := by
      show (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 * y.1 = 0
      rw [hp1, hF₁.2.1, zero_mul]
    constructor
    · intro h
      have h2 := congrArg Prod.snd h
      rw [h1] at h2
      exact hunit.mul_right_eq_zero.mp h2
    · intro h
      exact Prod.ext h0 (by rw [h1, h, mul_zero]; rfl)
  unfold kapSign
  rw [if_neg hns]
  dsimp only
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁)) with hV₁
  set m := Module.finrank (w.adicCompletion E) V₁ with hm
  set v := Module.finBasis (w.adicCompletion E) V₁ with hv
  have hmem : ∀ y : (B₁.prod B₂).A, ψ y ∈ V₁ ↔ y.2 = 0 := fun y => by
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hker]
  let ψ₁ : B₁.A →+ (Fin n → w.adicCompletion E) :=
    AddMonoidHom.mk' (fun z => ψ (show (B₁.prod B₂).A from (z, 0))) (fun z z' => by
      rw [← map_add]
      congr 1
      exact Prod.ext rfl (show (0 : B₂.A) = 0 + 0 by simp))
  have hψ₁ : ∀ z, ψ₁ z = ψ (show (B₁.prod B₂).A from (z, 0)) := fun z => rfl
  have hψ₁s : ∀ (c : K.E) z, ψ₁ (c • z) = e c • ψ₁ z := by
    intro c z
    rw [hψ₁, hψ₁, ← hs]
    congr 1
    exact Prod.ext rfl (show (0 : B₂.A) = c • 0 by simp)
  have hψ₁i : Function.Injective ψ₁ := by
    intro z z' hzz
    rw [hψ₁, hψ₁] at hzz
    exact congrArg Prod.fst (ψ.injective hzz)
  let a' : Fin m → B₁.A := fun i => (ψ.symm (v i : Fin n → w.adicCompletion E)).1
  have hva : ∀ i, ψ₁ (a' i) = v i := by
    intro i
    have h2 : (ψ.symm (v i : Fin n → w.adicCompletion E)).2 = 0 :=
      (hmem _).1 (by rw [ψ.apply_symm_apply]; exact (v i).2)
    have h3 : (show (B₁.prod B₂).A from (a' i, 0)) = ψ.symm (v i) := Prod.ext rfl h2.symm
    rw [hψ₁, h3, ψ.apply_symm_apply]
  have hsum : ∀ g : Fin m → K.E, ψ₁ (∑ i, g i • a' i) = ∑ i, e (g i) • (v i : Fin n → w.adicCompletion E) := by
    intro g
    rw [map_sum]
    simp only [hψ₁s, hva]
  have hli : LinearIndependent K.E a' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : ∑ j, e (g j) • v j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum g, hg, map_zero]
      rfl
    have := Fintype.linearIndependent_iff.mp v.linearIndependent _ h0 i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range a') := by
    intro z _
    have hz : ψ₁ z ∈ V₁ := (hmem _).2 rfl
    have hrep := congrArg Subtype.val (v.sum_repr ⟨ψ₁ z, hz⟩)
    rw [Submodule.coe_sum] at hrep
    simp only [Submodule.coe_smul] at hrep
    have hz' : z = ∑ i, e.symm (v.repr ⟨ψ₁ z, hz⟩ i) • a' i := by
      apply hψ₁i
      rw [hsum]
      simp only [RingEquiv.apply_symm_apply]
      exact hrep.symm
    rw [hz']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let hb : Module.Basis (Fin m) K.E B₁.A := Module.Basis.mk hli hsp
  have hbapp : ⇑hb = a' := funext fun i => Module.Basis.mk_apply hli hsp i
  have hdm : Module.finrank K.E B₁.A = m := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_fin]
  let bm := (Module.finBasis K.E B₁.A).reindex (finCongr hdm)
  have hgram : B₁.gramDet x.1 = (Matrix.of fun i j => B₁.herm x.1 (bm i) (bm j)).det := by
    unfold InvAlg.gramDet
    rw [← Matrix.det_reindex_self (finCongr hdm)]
    congr 1
    ext i j
    simp [bm, Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdetM : IsUnit (bm.toMatrix a').det := by
    have h := bm.isUnit_det hb
    rwa [Module.Basis.det_apply, hbapp] at h
  have hGa := GlobalTheory.GramChange.gram_of_sum K B₁ K.E (RingEquiv.refl K.E) (K.c : K.E →+* K.E) (fun _ => rfl) x.1 bm a'
    (bm.toMatrix a') (fun j => (bm.sum_toMatrix_smul_self a' j).symm)
  have e1 : (bm.toMatrix a').map (RingEquiv.refl K.E) = bm.toMatrix a' := Matrix.ext fun _ _ => rfl
  rw [e1] at hGa
  have e2 : ((bm.toMatrix a').map (K.c : K.E →+* K.E)).det = K.c (bm.toMatrix a').det :=
    (RingHom.map_det (K.c : K.E →+* K.E) (bm.toMatrix a')).symm
  have hdetG : (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det =
      (bm.toMatrix a').det * B₁.gramDet x.1 * K.c (bm.toMatrix a').det := by
    calc (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det
        = (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (a' i) (a' j))).det := rfl
      _ = ((bm.toMatrix a')ᵀ * (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (bm i) (bm j))) *
            (bm.toMatrix a').map (K.c : K.E →+* K.E)).det := by rw [hGa]
      _ = _ := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2, hgram]
        rfl
  have hK : (Matrix.of fun i j => ∑ k, cj w ((v i : Fin n → w.adicCompletion E) k) * (v j : Fin n → w.adicCompletion E) k) =
      (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j)))ᵀ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    calc _ = stdH w (ψ₁ (a' j)) (ψ₁ (a' i)) := by
          rw [hva, hva]
          unfold stdH
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = e ((B₁.prod B₂).herm x (show (B₁.prod B₂).A from (a' j, 0)) (show (B₁.prod B₂).A from (a' i, 0))) :=
          hh _ _
      _ = e (B₁.herm x.1 (a' j) (a' i)) := congrArg e (prod_herm_fst B₁ B₂ x _ _)
  have hdetE : (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j))).det =
      e (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det := by
    exact (RingHom.map_det (e : K.E →+* w.adicCompletion E) _).symm
  rw [hK, Matrix.det_transpose, hdetE, ← hval, hdetG]
  exact neg_one_zpow_val_norm_mul K _ _ hdetM.ne_zero

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinityTypeUnitaryHeckeCharCMRestrictingToEta
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuInfType

theorem char_eq_zpow (χ : ℂˣ →* ℂˣ) (hc : Continuous χ) (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hp : ∀ z : ℂˣ, (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χ z = 1) :
    ∃ n : ℤ, ∀ z : ℂˣ, (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n := by
  have hmem : ∀ z, (χ (Circle.toUnits z) : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hu _
  let f : Circle →* Circle :=
    { toFun := fun z => (⟨(χ (Circle.toUnits z) : ℂ), hmem z⟩ : Circle)
      map_one' := Circle.ext (by simp)
      map_mul' := fun a b => Circle.ext (by
        change ((χ (Circle.toUnits (a * b))) : ℂ) = (χ (Circle.toUnits a) : ℂ) * (χ (Circle.toUnits b) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcu : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · exact continuous_subtype_val
    · have : (fun x : Circle => ((Circle.toUnits x)⁻¹ : ℂˣ).val) = fun x : Circle => (x : ℂ)⁻¹ := by
        funext x; simp
      rw [this]
      exact (continuous_subtype_val).inv₀ fun x => Circle.coe_ne_zero x
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.comp (hc.comp hcu)
  obtain ⟨n, hn⟩ := GlobalTheory.circle_hom_eq_zpow f hf
  refine ⟨n, fun z => ?_⟩
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hn0 : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hw : (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere, mem_sphere_zero_iff_norm, norm_div, hz0]
  let w : Circle := (⟨_, hw⟩ : Circle)
  let r : ℂˣ := Units.mk0 (‖(z : ℂ)‖ : ℂ) hn0
  have hzr : z = Circle.toUnits w * r := Units.ext (by
    change (z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) * (‖(z : ℂ)‖ : ℂ)
    field_simp)
  have hr : χ r = 1 := hp r (by simp [r])
  have h1 := congrArg (fun c : Circle => (c : ℂ)) (hn w)
  have hχ : χ z = χ (Circle.toUnits w) := by rw [hzr, map_mul, hr, mul_one]
  rw [hχ]
  change ((f w : Circle) : ℂ) = _
  rw [h1, Circle.coe_zpow]

end GlobalTheory.MuInfType

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def single (v : InfinitePlace E) : ℂˣ →* (Cinf E)ˣ := Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℂ) v)

theorem continuous_single (v : InfinitePlace E) : Continuous (single v) :=
  Continuous.units_map _ (by
    show Continuous (fun z : ℂ => (Pi.mulSingle v z : InfinitePlace E → ℂ))
    exact continuous_mulSingle (A := fun _ : InfinitePlace E => ℂ) v)

variable (E) in

abbrev below (v : InfinitePlace E) : InfinitePlace (maximalRealSubfield E) := v.comap (algebraMap (maximalRealSubfield E) E)

def iota (v : InfinitePlace E) : (below E v).Completion →+* ℂ :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).toRingHom.comp
    (LiesOver.completionMap (v := below E v) (w := v))

theorem ideleMap_infIdele (v : InfinitePlace E) (x : ((below E v).Completion)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) =
      infId E (single v (Units.map (iota v).toMonoidHom x)) := by
  classical
  refine Units.ext (ad_ext ?_ ?_)
  · funext w
    have h1 : ∀ u : (Cinf E)ˣ, pInf E (infId E u).val = u.val := fun u => by
      change (infEq E).symm (1 - infEq E 1 + infEq E u.val) = _
      simp
    rw [h1]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
      (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w)
        (Pi.mulSingle (below E v) ((x : (below E v).Completion)) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same]
      simp [single, iota]
    · have h' : w.comap (algebraMap (maximalRealSubfield E) E) ≠ below E v := fun e =>
        h ((IsCMField.equivInfinitePlace E).injective e)
      rw [Pi.mulSingle_eq_of_ne h']
      simp [single, Pi.mulSingle_eq_of_ne h]
  · change pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) : Ad E) =
      pFin E (infId E _).val
    refine (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)).trans ?_
    change (1 : Af E) = 1 - 0 + 0
    simp

theorem iota_real (v : InfinitePlace E) (s : ℝ) :
    iota v ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s) = s := by
  let ψ : ℝ →+* ℂ := (iota v).comp
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.toRingHom
  have hψ : Continuous ψ :=
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      (LiesOver.continuous_completionMap (v := below E v) (w := v))).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.continuous
  have := map_real_smul ψ hψ s 1
  simpa [ψ] using this

end GlobalTheory.MuInfType

end

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

theorem infType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ∃ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ hU hη
  let χv : InfinitePlace E → ℂˣ →* ℂˣ := fun v => (chiInf μ).comp (single v)
  have hcont : ∀ v, Continuous (χv v) := fun v => (continuous_chiInf μ).comp (continuous_single v)
  have hunit : ∀ v z, ‖(χv v z : ℂ)‖ = 1 := fun v z => hU _
  have hval : ∀ v (x : ((below E v).Completion)ˣ),
      χv v (Units.map (iota v).toMonoidHom x) = (GlobalTheory.GalOfCusp.quadChar E).1 (infIdele _ (below E v) x) := by
    intro v x
    change μ.1 (infId E (single v _)) = _
    rw [← ideleMap_infIdele, hη]
  have hneg : ∀ v, χv v (-1) = -1 := by
    intro v
    have e : Units.map (iota v).toMonoidHom (-1) = -1 := Units.ext (by simp)
    have h := hval v (-1)
    rw [e] at h
    rw [h]
    exact GlobalTheory.GalOfCusp.quadChar_locInf E (below E v)
  have hpos : ∀ v (z : ℂˣ), (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χv v z = 1 := by
    intro v z hz
    set s : ℝ := Real.sqrt ‖(z : ℂ)‖ with hs
    have hs0 : s ≠ 0 := by
      rw [hs]
      exact (Real.sqrt_pos.2 (norm_pos_iff.2 z.ne_zero)).ne'
    have hx0 : (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s ≠ 0 := by
      simpa using hs0
    let x : ((below E v).Completion)ˣ := Units.mk0 _ hx0
    have hx : Units.map (iota v).toMonoidHom x ^ 2 = z := Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, x,
        Units.val_mk0, iota_real]
      rw [← Complex.ofReal_pow, hs, Real.sq_sqrt (norm_nonneg _), hz])
    rw [← hx, map_pow, hval]
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E _)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  choose e he using fun v => GlobalTheory.MuInfType.char_eq_zpow (χv v) (hcont v) (hunit v) (hpos v)
  refine ⟨e, fun v => ?_, fun z => ?_⟩
  · have h := he v (-1)
    rw [hneg] at h
    simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, div_one] at h
    rcases Int.even_or_odd (e v) with h' | h'
    · rw [h'.neg_one_zpow] at h
      norm_num at h
    · exact h'
  · let zv : InfinitePlace E → ℂˣ := fun v => Units.map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) v) z
    have hz : z = ∏ v, single v (zv v) := Units.ext (by
      rw [Units.coe_prod]
      simp only [single, zv, Units.coe_map, MonoidHom.coe_coe, MonoidHom.mulSingle_apply, Pi.evalMonoidHom_apply]
      exact (Finset.univ_prod_mulSingle z.val).symm)
    conv_lhs => rw [hz]
    rw [map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl fun v _ => he v (zv v)

end GlobalTheory.MuInfType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory
open scoped NNReal Pointwise

namespace GlobalTheory.DetScale

theorem integral_comp_linearEquiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [TopologicalSpace V] [IsModuleTopology k V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : V ≃ₗ[k] V) (f : V → ℂ) :
    ∫ y, f (L y) ∂μ = (((distribHaarChar k (LinearEquiv.det L) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ∫ y, f y ∂μ := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup k V
  let n := Module.finrank k V
  let e0 : V ≃ₗ[k] (Fin n → k) := (Module.finBasis k V).equivFun
  let e : V ≃L[k] (Fin n → k) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  borelize (Fin n → k)
  let ν : Measure (Fin n → k) := μ.map e
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let L' : (Fin n → k) ≃ₗ[k] (Fin n → k) := (e0.symm.trans L).trans e0
  set c : ℝ≥0 := distribHaarChar k (LinearEquiv.det L) with hc
  have hd : distribHaarChar (Fin n → k) L' = c := by
    rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, LinearEquiv.det_conj]
  have hc0 : c ≠ 0 := (distribHaarChar_pos (A := k) (g := LinearEquiv.det L)).ne'
  let Lh : V ≃ₜ V :=
    { L.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }
  have hν : ∀ s : Set V, ν (e '' s) = μ s := fun s => by
    have h := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ) (e '' s)
    refine h.trans ?_
    congr 1
    exact Set.preimage_image_eq s e.injective
  have hm : μ.map Lh.toMeasurableEquiv = c⁻¹ • μ := by
    ext s _
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, ← hν, ← hν s]
    have h := distribHaarChar_mul ν L' (e '' (Lh ⁻¹' s))
    have hs : L' • (e '' (Lh ⁻¹' s)) = e '' s := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨L y, hy, ?_⟩
        simp [L', e, LinearEquiv.smul_def]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨e (L.symm y), ⟨L.symm y, ?_, rfl⟩, ?_⟩
        · simpa [Lh] using hy
        · simp [L', e, LinearEquiv.smul_def]
    rw [hs, hd] at h
    rw [← h, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0,
      ENNReal.coe_one, one_mul]
    rfl
  have e1 : ∫ y, f (L y) ∂μ = ∫ y, f (Lh.toMeasurableEquiv y) ∂μ := rfl
  rw [e1, ← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  rfl

theorem integral_comp_matrix : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (a b : ℕ) (L : Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F) (hL : LinearMap.det L ≠ 0)
    (φ : Matrix (Fin a) (Fin b) F → ℂ) (μ : @MeasureTheory.Measure (Matrix (Fin a) (Fin b) F) (borel _)),
    @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∫ x, φ (L x) ∂μ = ((((MeasureTheory.distribHaarChar F (Units.mk0 _ hL) : NNReal) : ℝ) : ℂ))⁻¹ * ∫ x, φ x ∂μ := by
  intro F _ _ _ _ a b L hL φ μ hμ
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) F) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) F) := ⟨rfl⟩
  haveI : IsModuleTopology F (Matrix (Fin a) (Fin b) F) :=
    show IsModuleTopology F (Fin a → Fin b → F) from inferInstance
  let Le := LinearMap.equivOfDetNeZero L hL
  have hdet : LinearEquiv.det Le = Units.mk0 _ hL := by
    ext
    rw [LinearEquiv.coe_det, Units.val_mk0]
    rfl
  have h := integral_comp_linearEquiv (k := F) μ Le φ
  rw [hdet] at h
  exact h

end GlobalTheory.DetScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoordStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  first | exact @GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic | exact GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic | (intros; apply GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic <;> assumption)
end


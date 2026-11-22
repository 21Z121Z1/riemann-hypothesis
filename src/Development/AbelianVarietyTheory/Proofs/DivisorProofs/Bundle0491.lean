import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwist

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveProjBundleModelCochainComplexX
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC
open CupSpec

variable {R : Type} [CommRing R]

section Build
variable (q N : ℕ) (I : Cx R) (n : ℤ) {B : Shv R}
  (χ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec B V →ₗ[ULift.{1} R] Sec (I.X s) V)
  (hχ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (b : Sec B V),
      Sec.res w (χ p s h V x b) = χ p s h W (x.res w) (Sec.res w b))
include hχ in
theorem buildC_exists (U : Scheme.{0}) (b : Sec B U) :
    ∃ α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ∀ p s h W y,
      ev α p s h W y = χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) := by
  refine ev_exists _ (fun p s h W W' g y => ?_)
  rw [hχ, secRes_res, sxMap_res, sxMap_res]
  rfl

def cochainOfSection (U : Scheme.{0}) (b : Sec B U) : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (buildC_exists q N I n χ hχ U b).choose

theorem buildC_ev (U : Scheme.{0}) (b : Sec B U) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0})
    (y : Sx (sch.obj U ⨯ fibQ q N) p W) :
    ev (cochainOfSection q N I n χ hχ U b) p s h W y = χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) :=
  (buildC_exists q N I n χ hχ U b).choose_spec p s h W y

def buildMor : B.obj ⟶ cotPre R q N I n where
  app U := ModuleCat.ofHom
    { toFun := cochainOfSection q N I n χ hχ U.unop
      map_add' := fun b b' => ev_ext _ _ (fun p s h W y => by
        rw [ev_add, buildC_ev, buildC_ev, buildC_ev, Sec.res, Sec.res, Sec.res, map_add, map_add])
      map_smul' := fun r b => ev_ext _ _ (fun p s h W y => by
        rw [RingHom.id_apply, ev_smulU, buildC_ev, buildC_ev, Sec.res, Sec.res, map_smul, map_smul]) }
  naturality U U' g := by
    ext b : 2
    refine ev_ext _ _ (fun p s h W y => ?_)
    change ev (cochainOfSection q N I n χ hχ U'.unop (Sec.res g.unop b)) p s h W y =
      ev (((cotPre R q N I n).map g.unop.op).hom (cochainOfSection q N I n χ hχ U.unop b)) p s h W y
    have e2 := ev_pull (I := I) (prod.map (sch.map g.unop) (𝟙 (fibQ q N))) (cochainOfSection q N I n χ hχ U.unop b) p s h W y
    refine Eq.trans ?_ e2.symm
    rw [buildC_ev, buildC_ev, secRes_res, ← sxMap_comp, ← sxMap_comp, prod.map_snd, prod.map_fst, Category.comp_id]
    rfl

end Build

theorem injective_cotSheaf (q N : ℕ) (I : Cx R) (hI : ∀ m, Injective (I.X m)) (n : ℤ)
    (hS : Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n)) :
    Injective (⟨cotPre R q N I n, hS⟩ : Shv R) := by
  constructor
  intro A B g f hf
  let ψ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec A V →ₗ[ULift.{1} R] Sec (I.X s) V :=
    fun p s h V x => (evLin I _ n p s h V (sxPair (schSx (𝟙 V) p) x)).comp (g.hom.app (op V)).hom
  have hψ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (a : Sec A V),
      Sec.res w (ψ p s h V x a) = ψ p s h W (x.res w) (Sec.res w a) := by
    intro p s h V W w x a
    have hn : (g.hom.app (op W)).hom (Sec.res w a) = ((cotPre R q N I n).map w.op).hom ((g.hom.app (op V)).hom a) :=
      ConcreteCategory.congr_hom (g.hom.naturality w.op) a
    refine (ev_res (E := sch.obj V ⨯ fibQ q N) (I := I) ((g.hom.app (op V)).hom a) p s h w _).trans ?_
    refine Eq.trans ?_ (congrArg (fun c => ev (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))) hn).symm
    have e2 := ev_pull (I := I) (prod.map (sch.map w) (𝟙 (fibQ q N))) ((g.hom.app (op V)).hom a) p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))
    refine Eq.trans ?_ e2.symm
    rw [sxPair_res, sxPair_map]
    congr 2
  have hχ := fun p s h => GlobalTheory.T.natural_sections_linear_extension R ((fibQ q N).obj (op (SimplexCategory.mk p))) (I.X s) (hI s) f hf (ψ p s h) (hψ p s h)
  choose χ hχn hχf using hχ
  refine ⟨⟨buildMor q N I n χ hχn⟩, ?_⟩
  ext U a : 4
  refine LinearMap.ext fun a => ?_
  change cochainOfSection q N I n χ hχn U.unop (Sec.map f a) = (g.hom.app U).hom a
  refine ev_ext _ _ (fun p s h W y => ?_)
  refine (buildC_ev q N I n χ hχn U.unop (Sec.map f a) p s h W y).trans ?_
  refine (congrArg (χ p s h W (y.map prod.snd)) (map_res f (show W ⟶ U.unop from y.map prod.fst) a)).trans ?_
  refine (hχf p s h W _ _).trans ?_
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (show W ⟶ U.unop from y.map prod.fst).op) a
  refine (congrArg (fun c => ev (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
    (sxPair (schSx (𝟙 W) p) (y.map prod.snd))) hn).trans ?_
  refine (ev_pull (I := I) (prod.map (sch.map (show W ⟶ U.unop from y.map prod.fst)) (𝟙 (fibQ q N)))
    ((g.hom.app U).hom a) p s h W _).trans ?_
  congr 1
  rw [sxPair_map]
  exact sxPair_eta y

theorem Jcx_X_injective : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) →
    ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  intro R _ q N I hI n
  have hS := GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale R q N I n
  exact Injective.of_iso (sheafificationIso (⟨cotPre R q N I n, hS⟩ : Shv R)) (injective_cotSheaf q N I hI n hS)

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtension
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.PullAd

section
variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] {n : ℕ}

theorem val_eq_one_iff {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {z : K}
    (hz : z ≠ 0) : w z = 1 ↔ w z ≤ 1 ∧ w z⁻¹ ≤ 1 := by
  constructor
  · intro h; simp [map_inv₀, h]
  · rintro ⟨h1, h2⟩
    rw [map_inv₀] at h2
    have h0 : w z ≠ 0 := (Valuation.ne_zero_iff w).2 hz
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = w z * (w z)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ w z * 1 := mul_le_mul_right h2 _
      _ = w z := mul_one _

theorem res_eq_one {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x : F} (hx : x ≠ 0) :
    p.1 (algebraMap F E x) = 1 ↔ (ρ p).1 x = 1 := by
  rw [val_eq_one_iff _ hx, val_eq_one_iff _ ((map_ne_zero _).2 hx), ← map_inv₀, hρ, hρ]

theorem res_mono {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x y : F}
    (h : (ρ p).1 x ≤ (ρ p).1 y) : p.1 (algebraMap F E x) ≤ p.1 (algebraMap F E y) := by
  by_cases hy : y = 0
  · subst hy
    have h0 : (ρ p).1 x = 0 := le_antisymm (by simpa using h) zero_le'
    have hx : x = 0 := (Valuation.zero_iff _).1 h0
    simp [hx]
  · have h1 : (ρ p).1 (x * y⁻¹) ≤ 1 := by
      have h0 : (ρ p).1 y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
      rw [map_mul, map_inv₀]
      calc (ρ p).1 x * ((ρ p).1 y)⁻¹ ≤ (ρ p).1 y * ((ρ p).1 y)⁻¹ := mul_le_mul_left h _
        _ = 1 := mul_inv_cancel₀ h0
    have h2 := (hρ p (x * y⁻¹)).2 h1
    have e : algebraMap F E x = algebraMap F E (x * y⁻¹) * algebraMap F E y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h2

theorem det_map (M : Matrix (Fin n) (Fin n) F) :
    (M.map (algebraMap F E)).det = algebraMap F E M.det := by
  rw [RingHom.map_det]; rfl

theorem unimod_map {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E)
    (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) :
    Unimod p (M.map (algebraMap F E)) ↔ Unimod (ρ p) M := by
  unfold Unimod
  rw [det_map, res_eq_one hρ p hM]
  simp only [Matrix.map_apply]
  exact and_congr_left fun _ => forall_congr' fun i => forall_congr' fun j => hρ p _

theorem nrm_of_max (v : Place k F) (x : Fin n → F) (i : Fin n) (h : ∀ j, v.1 (x j) ≤ v.1 (x i)) :
    nrm v x = v.1 (x i) :=
  le_antisymm (Finset.sup_le fun j _ => h j) (Finset.le_sup (f := fun j => v.1 (x j)) (Finset.mem_univ i))

end

theorem adm_pullAd_and_deg_mul_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ n g hg
  have hP := GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul k F E hFF ρ hρ
  have hdet : ∀ p, (pullAd ρ g p).det = algebraMap F E (g (ρ p)).det := fun p => det_map _
  have hadm : admitted (pullAd ρ g) := by
    refine ⟨fun p => by rw [hdet]; exact (map_ne_zero _).2 (hg.1 _), ?_⟩
    refine (hP.1 _ hg.2).subset fun p hp => ?_
    exact fun h => hp ((unimod_map hρ p (g (ρ p)) (hg.1 _)).2 h)
  have hdeg : deg (pullAd ρ g) = Module.finrank F E * deg g := by
    have hfin : {v | ord v (g v).det ≠ 0}.Finite := hg.2.subset fun v hv hu => hv (by simp [ord, hu.2])
    unfold deg
    rw [← hP.2 (fun v => (g v).det) hfin]
    exact finsum_congr fun p => by rw [hdet]
  have hline : ∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i))
      = Module.finrank F E * degLine g w := by
    intro w hw
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      obtain ⟨i, -⟩ := Function.ne_iff.1 hw; exact ⟨i, Finset.mem_univ _⟩
    have hmax : ∀ v : Place k F, ∃ i, ∀ j, v.1 ((g v).mulVec w j) ≤ v.1 ((g v).mulVec w i) := fun v => by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => v.1 ((g v).mulVec w i)) hne
      exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
    choose idx hidx using hmax
    let φ : Place k F → F := fun v => (g v).mulVec w (idx v)
    have hvo : ∀ v, ordVec v ((g v).mulVec w) = ord v (φ v) := fun v => by
      simp only [ordVec, ord, φ, nrm_of_max v _ _ (hidx v)]
    have hpo : ∀ p, ordVec p ((pullAd ρ g p).mulVec (fun i => algebraMap F E (w i)))
        = ord p (algebraMap F E (φ (ρ p))) := fun p => by
      have e : (pullAd ρ g p).mulVec (fun i => algebraMap F E (w i))
          = fun i => algebraMap F E ((g (ρ p)).mulVec w i) := by
        funext i; exact (RingHom.map_mulVec _ _ _ _).symm
      rw [e]
      simp only [ordVec, ord, φ]
      rw [nrm_of_max p _ (idx (ρ p)) fun j => res_mono hρ p (hidx (ρ p) j)]
    have hfin : {v | ord v (φ v) ≠ 0}.Finite := by
      have hS : ({v | ¬ Unimod v (g v)} ∪ ⋃ i, {v : Place k F | w i ≠ 0 ∧ v.1 (w i) ≠ 1}).Finite := by
        refine hg.2.union (Set.finite_iUnion fun i => ?_)
        by_cases hi : w i = 0
        · simp [hi]
        · exact (GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1.subset fun v hv => hv.2
      refine hS.subset fun v hv => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_and,
        not_not] at hc
      obtain ⟨hu, hw1⟩ := hc
      apply hv
      rw [← hvo v]
      have h1 : nrm v w = 1 := by
        obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
        replace hi0 : w i0 ≠ 0 := hi0
        apply le_antisymm
        · refine Finset.sup_le fun j _ => ?_
          by_cases hj : w j = 0
          · simp [hj]
          · exact (hw1 j hj).le
        · rw [← hw1 i0 hi0]; exact Finset.le_sup (f := fun j => v.1 (w j)) (Finset.mem_univ i0)
      simp only [ordVec]
      rw [(GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1 n (g v) w hu, h1]
      simp
    unfold degLine
    rw [finsum_congr hpo, hP.2 φ hfin, finsum_congr hvo]
  have hlines : ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
    intro b hb E' _ _ _ _ _ ρ' hρ' w hw
    letI : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
    haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k F E' := IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k F E,
        ← IsScalarTower.algebraMap_apply k E E']
    haveI : FiniteDimensional F E' := Module.Finite.trans E E'
    have hres : IsRes (fun p => ρ (ρ' p)) := fun p x => (hρ' p (algebraMap F E x)).trans (hρ (ρ' p) x)
    have heq : pullAd ρ' (pullAd ρ g) = pullAd (fun p => ρ (ρ' p)) g := by
      funext p; ext i j; rfl
    have hb' := hb E' (fun p => ρ (ρ' p)) hres w hw
    rw [heq]
    calc (degLine (pullAd (fun p => ρ (ρ' p)) g) w : ℝ) ≤ b * Module.finrank F E' := hb'
      _ = b * Module.finrank F E * Module.finrank E E' := by
        rw [← Module.finrank_mul_finrank F E E']; push_cast; ring
  exact ⟨hadm, hdeg, hline, hlines⟩

end GlobalTheory.Nef.PullAd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwise
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ContLevel

theorem chains_map_f (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (k : ℕ) :
    ((chains R).map φ).f (-(k : ℤ)) = (chainsXIso R E k).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv :=
  HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := k) rfl

end GlobalTheory.EtC.ContLevel

open GlobalTheory.EtC.ContLevel in

theorem GlobalTheory.EtC.contCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  intro R _ F I _ _ G c hG
  obtain ⟨-, hneg, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨cl, hsurj, hiff, hzero, hpull⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  refine fun n => GlobalTheory.EtC.cont_cx_of_degreewise R I (G ⋙ chains R) ((chains R).mapCone c) (res R F)
     (fun i p hp => hpos (G.obj i) p hp) (fun p hp => hpos c.pt p hp) hneg ?_ n
  intro p s
  by_cases hp : 0 < p
  · constructor
    · intro t _
      obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
      refine ⟨i, 0, 0, zero_comp, ?_⟩
      have : t = 0 := (hpos c.pt p hp).eq_of_src _ _
      simp [this]
    · intro i u _ _
      refine ⟨i, 𝟙 i, 0, ?_⟩
      have : u = 0 := (hpos (G.obj i) p hp).eq_of_src _ _
      simp [this]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    have hk := hG (op (SimplexCategory.mk k)) s
    constructor
    · intro t ht
      let t' := (chainsXIso R c.pt k).inv ≫ t
      have ht' : t' ≫ (res R F).d s (s + 1) = 0 := by simp [t', ht]
      obtain ⟨i, y, hy⟩ := hk.1 (cl _ s t' ht')
      obtain ⟨u', hu', rfl⟩ := hsurj _ s y
      obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
      change pull R (disc.map ((c.π.app i).app (op (SimplexCategory.mk k)))) F s _ = _ at hy
      rw [hp2, hiff] at hy
      obtain ⟨y', hy'⟩ := hy
      refine ⟨i, (chainsXIso R (G.obj i) k).hom ≫ u', (chainsXIso R c.pt k).hom ≫ y', by simp [hu'], ?_⟩
      change ((chains R).map (c.π.app i)).f _ ≫ _ = _
      rw [chains_map_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hy']
      simp [t', Preadditive.comp_add]
    · rintro i u hu ⟨y, hy⟩
      let u' := (chainsXIso R (G.obj i) k).inv ≫ u
      have hu' : u' ≫ (res R F).d s (s + 1) = 0 := by simp [u', hu]
      have hdie : pull R ((((evaluation _ PSh).obj (op (SimplexCategory.mk k)) ⋙ disc).mapCone c).π.app i) F s
          (cl _ s u' hu') = 0 := by
        change pull R (disc.map ((c.π.app i).app _)) F s _ = 0
        obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
        rw [hp2, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) s, hiff]
        refine ⟨(chainsXIso R c.pt k).inv ≫ y, ?_⟩
        change ((chains R).map (c.π.app i)).f _ ≫ u = _ at hy
        rw [chains_map_f] at hy
        rw [zero_add, Category.assoc, ← hy]
        simp [u']
      obtain ⟨k', f, hf⟩ := hk.2 i _ hdie
      change pull R (disc.map ((G.map f).app (op (SimplexCategory.mk k)))) F s _ = 0 at hf
      obtain ⟨h3, hp3⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((G.map f).app (op (SimplexCategory.mk k))) s u' hu'
      rw [hp3, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) s, hiff] at hf
      obtain ⟨y'', hy''⟩ := hf
      refine ⟨k', f, (chainsXIso R (G.obj k') k).hom ≫ y'', ?_⟩
      change ((chains R).map (G.map f)).f _ ≫ u = _
      rw [chains_map_f, zero_add] at *
      simp only [Category.assoc]
      exact congrArg ((chainsXIso R (G.obj k') k).hom ≫ ·) hy''

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRad
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem hankel_pow_mul (a : F) (c : ℕ → F) (n : ℕ) :
    hankel (fun i => a ^ i * c i) n = a ^ (n * (n + 1)) * hankel c n := by
  have hM : (Matrix.of fun i j : Fin (n + 1) => a ^ ((i : ℕ) + j) * c (i + j)) =
      Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) * (Matrix.of fun i j : Fin (n + 1) => c (i + j)) *
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, pow_add]
    ring
  unfold hankel
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ i : Fin (n + 1), (i : ℕ)) * 2 = n * (n + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id_mul_two]
    simp [mul_comm]
  rw [← hs, pow_mul]
  ring

theorem ord_mul' (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_pow' (v : Place k F) (x : F) (m : ℕ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem ord_of_eq_one (v : Place k F) {x : F} (h : v.1 x = 1) : ord v x = 0 := by
  simp [ord, h]

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem ord_hankel_ge (v : Place k F) (φ : PowerSeries F) (u : F) (e ψ : PowerSeries v.O) (hu : u ≠ 0)
    (he0 : PowerSeries.constantCoeff e ≠ 0)
    (heq : sc v u e * φ = sc v u ψ) (n : ℕ) (hH : hankel (fun i => PowerSeries.coeff i φ) n ≠ 0) :
    ((n * (n + 1) : ℕ) : ℤ) * ord v u - ((2 * (n + 1) : ℕ) : ℤ) * ord v ((PowerSeries.constantCoeff e : v.O) : F) ≤
      ord v (hankel (fun i => PowerSeries.coeff i φ) n) := by
  have hr : ∀ f : PowerSeries F, PowerSeries.rescale u⁻¹ (PowerSeries.rescale u f) = f := by
    intro f; ext m
    simp only [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  have h1 : PowerSeries.map v.O.subtype e * PowerSeries.rescale u⁻¹ φ = PowerSeries.map v.O.subtype ψ := by
    have := congrArg (PowerSeries.rescale u⁻¹) heq
    simpa only [sc, RingHom.comp_apply, map_mul, hr] using this
  obtain ⟨z, hz⟩ := GlobalTheory.T.hankelDeterminant_integral_of_quotient v.O F v.O.subtype e ψ (PowerSeries.rescale u⁻¹ φ) n h1
  have h2 : (fun i => PowerSeries.coeff i φ) = fun i => u ^ i * PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ) := by
    funext i
    rw [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
  set c : F := ((PowerSeries.constantCoeff e : v.O) : F) with hc
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  set H0 := hankel (fun i => PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ)) n with hH0
  have h3 : H = u ^ (n * (n + 1)) * H0 := by rw [hHdef, h2, hankel_pow_mul]
  have hz' : (z : F) = c ^ (2 * (n + 1)) * H0 := hz
  have h4 : c ^ (2 * (n + 1)) * H = u ^ (n * (n + 1)) * (z : F) := by rw [h3, hz']; ring
  have hH0 : H0 ≠ 0 := by
    intro h; exact hH (by rw [h3, h, mul_zero])
  have hcne : c ≠ 0 := by
    intro h; apply he0; ext; simpa [hc] using h
  have hzne : (z : F) ≠ 0 := by rw [hz']; exact mul_ne_zero (pow_ne_zero _ hcne) hH0
  have hz1 : 0 ≤ ord v (z : F) :=
    ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.1 _ hzne).1 ((Valuation.mem_valuationSubring_iff _ _).1 z.2)
  have h5 := congrArg (ord v) h4
  rw [ord_mul' v (pow_ne_zero _ hcne) hH, ord_mul' v (pow_ne_zero _ hu) hzne, ord_pow', ord_pow'] at h5
  linarith

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

theorem isRat_of_adelic : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  intro k F _ _ _ _ _ hFF φ u e ψ hu0 hufin hdeg he0 hefin heq
  classical
  set c : Place k F → F := fun v => ((PowerSeries.constantCoeff (e v) : v.O) : F) with hc
  have hcunit : ∀ v, IsUnit (PowerSeries.constantCoeff (e v)) → v.1 (c v) = 1 := by
    intro v h
    obtain ⟨a, ha⟩ := h
    have h1 := ValuationSubring.valuation_unit v.O a
    rw [ha] at h1
    exact (Valuation.isEquiv_valuation_valuationSubring v.1).eq_one_iff_eq_one.2 h1
  set δ := ∑ᶠ v, ord v (c v) with hδ
  set D := ∑ᶠ v, ord v (u v) with hD
  apply GlobalTheory.T.isRat_of_hankel_eventually_eq_zero F φ ((2 * δ).toNat + 1)
  intro n hn
  by_contra hH
  obtain ⟨hHfin, hHsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF _ hH
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  let T : Finset (Place k F) := hufin.toFinset ∪ hefin.toFinset ∪ hHfin.toFinset
  have sU : Function.support (fun v => ord v (u v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl (Or.inl hv)
  have sC : Function.support (fun v => ord v (c v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inl (Or.inr ?_)
    intro h
    exact hv (ord_of_eq_one v (hcunit v h))
  have sH : Function.support (fun v => ord v H) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inr ?_
    intro h
    exact hv (ord_of_eq_one v h)
  rw [finsum_eq_sum_of_support_subset _ sH] at hHsum
  rw [finsum_eq_sum_of_support_subset _ sC] at hδ
  rw [finsum_eq_sum_of_support_subset _ sU] at hD
  have hsum : ∑ v ∈ T, (((n * (n + 1) : ℕ) : ℤ) * ord v (u v) - ((2 * (n + 1) : ℕ) : ℤ) * ord v (c v)) ≤
      ∑ v ∈ T, ord v H :=
    Finset.sum_le_sum fun v _ => ord_hankel_ge v φ (u v) (e v) (ψ v) (hu0 v) (he0 v) (heq v) n hH
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hD, ← hδ, hHsum] at hsum
  have hn' : 2 * δ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat (2 * δ)
    omega
  have hD1 : 1 ≤ D := hdeg
  push_cast at hsum
  have h6 : (n + 1 : ℤ) * (n * D - 2 * δ) ≤ 0 := by linarith [hsum]
  have h7 : (n : ℤ) * D - 2 * δ ≤ 0 := by
    by_contra h8
    push_neg at h8
    have : (0 : ℤ) < (n + 1 : ℤ) * (n * D - 2 * δ) := mul_pos (by positivity) h8
    linarith
  have h9 : (n : ℤ) ≤ n * D := by nlinarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
  linarith

end GlobalTheory.RatCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_sequence_etale_tateTwist : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Mono κ ∧ κ ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.kummer_sequence) | (exact GlobalTheory.EtC.kummer_sequence) | (intros; apply GlobalTheory.EtC.kummer_sequence  <;> assumption)
end


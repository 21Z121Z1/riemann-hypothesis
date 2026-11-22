import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.TrueGeo.SmallSec

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_mul (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem regAt_pow {x : Z} (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem valAt_pow (hf : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map (Scheme.stalkClosedPointTo y).hom).ne_zero

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = valR y U a := by
  have e : fnOf U h a = algebraMap _ Z.functionField (Z.presheaf.germ U (below y) hy a) :=
    (algebraMap_germ hy a).symm
  have ht : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y hy).ge
  have H := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  rw [e, valAt_algebraMap]
  first
  | rw [valR, dif_pos ht]
  | simp only [valR, dif_pos ht]
  | simp only [valR, ht, dite_true]
  refine H.trans ?_
  first
  | rfl
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; done)
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; rfl)
  | (simp [Scheme.Hom.appLE]; done)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  rw [ratVal, dif_pos hf]
  have he := hf.exists_fnOf.choose_spec.choose_spec.choose_spec
  conv_rhs => rw [← he]
  exact (valAt_fnOf hf.exists_fnOf.choose_spec.choose _ _).symm

theorem regAt_of_pow {x : Z} (hx : IsIntegrallyClosed (Z.presheaf.stalk x)) {n : ℕ} (hn : 0 < n)
    (h : RegAt x (f ^ n)) : RegAt x f := by
  haveI := hx
  obtain ⟨a, ha⟩ := h
  have hint : IsIntegral (Z.presheaf.stalk x) f := by
    refine ⟨Polynomial.X ^ n - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hn.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ha]
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Z.presheaf.stalk x)
    (K := Z.functionField)).1 hint
  exact ⟨b, hb⟩

end Val

section Fn

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

def fnMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fnMap_fnOf {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) : fnMap j hη (fnOf U h s) = fnOf (j ⁻¹ᵁ U) h' (j.app U s) := by
  show (X.presheaf.germ U _ h ≫ X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom s =
    (j.app U ≫ Y.presheaf.germ (j ⁻¹ᵁ U) (genericPoint Y) h').hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem fnMap_algebraMap_eq_algebraMap_stalkMap (y : Y) (b : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField b) = algebraMap _ Y.functionField (j.stalkMap y b) := by
  have e1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Y) y
    ((genericPoint_spec Y).specializes trivial) b
  simp only [RingHom.algebraMap_toAlgebra, fnMap]
  rw [← e1]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem exists_fnMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : RegAt y u) : ∃ t, RegAt (j y) t ∧ fnMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  exact ⟨algebraMap _ X.functionField b, ⟨b, rfl⟩, fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b⟩

theorem fnMap_surjective [IsPreimmersion j] : Function.Surjective (fnMap j hη) := fun u =>
  let ⟨t, _, ht⟩ := exists_fnMap_eq j hη (regAt_genericPoint u)
  ⟨t, ht⟩

theorem regAt_fnMap_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    RegAt y (fnMap j hη t) ↔ RegAt (j y) t := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fnMap_eq j hη h
    rwa [(fnMap j hη).injective e] at ht'
  · rintro ⟨b, rfl⟩
    exact ⟨_, (fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b).symm⟩

theorem valAt_fnMap {K : Type} [Field K] (y : Sp K ⟶ Y) {t : X.functionField}
    (h : RegAt (j (below y)) t) : valAt y (fnMap j hη t) = valAt (y ≫ j) t := by
  obtain ⟨b, rfl⟩ := h
  rw [fnMap_algebraMap_eq_algebraMap_stalkMap, valAt_algebraMap]
  refine Eq.trans ?_ (valAt_algebraMap (y := y ≫ j) b).symm
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Fn

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)

theorem isPreimmersion_j : IsPreimmersion M.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip this

private theorem asIdeal_spMap_algebraMap_eq_bot (s : Sp F) : (spMap (algebraMap (𝓞 F) F) s).asIdeal = ⊥ := by
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have e : (spMap (algebraMap (𝓞 F) F) s).asIdeal = Ideal.comap (algebraMap (𝓞 F) F) s.asIdeal := by
    first
    | rfl
    | simp [spMap]
    | simp [spMap, Spec.map_base]
  rw [e, hs]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j {x : M.X} (hx : (M.p x).asIdeal = ⊥) : x ∈ Set.range M.j := by
  have e : M.p x = spMap (algebraMap (𝓞 F) F) (IsLocalRing.closedPoint F) :=
    PrimeSpectrum.ext (hx.trans (asIdeal_spMap_algebraMap_eq_bot _).symm)
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ e
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz1, ← M.pb.isoPullback_inv_fst]
  first
  | rfl
  | exact (Scheme.comp_apply _ _ _).symm
  | simp

theorem asIdeal_p_j (y : Y.X) : (M.p (M.j y)).asIdeal = ⊥ := by
  have e : M.p (M.j y) = spMap (algebraMap (𝓞 F) F) (Y.str y) := by
    first
    | (show (M.j ≫ M.p) y = (Y.str ≫ spMap _) y
       rw [M.pb.w])
    | rw [← Scheme.comp_apply, M.pb.w, Scheme.comp_apply]
  rw [e, asIdeal_spMap_algebraMap_eq_bot]

theorem asIdeal_p_gen [IsIntegral M.X] : (M.p (genericPoint M.X)).asIdeal = ⊥ := by
  obtain ⟨y⟩ : Nonempty Y.X := inferInstance
  have hs : genericPoint M.X ⤳ M.j y := (genericPoint_spec M.X).specializes trivial
  have h3 : (M.p (genericPoint M.X)).asIdeal ≤ (M.p (M.j y)).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (M.p.base.hom.map_specializes hs)
  rw [asIdeal_p_j] at h3
  exact le_bot_iff.1 h3

theorem j_gen_specializes [IsIntegral M.X] : M.j (genericPoint Y.X) ⤳ genericPoint M.X := by
  obtain ⟨y0, hy0⟩ := mem_range_j M (asIdeal_p_gen M)
  rw [← hy0]
  exact M.j.base.hom.map_specializes ((genericPoint_spec Y.X).specializes trivial)

end Model

end GlobalTheory.TrueGeo.SmallSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem lvlE_range_iff : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  have h := congrArg (fun s : Set S.Forms => f ∈ s) (GlobalTheory.Mem.LiftForms.range_lvlForm S r P ψ)
  simp only [Set.mem_range, GlobalTheory.Mem.LiftForms.lvlForm_apply] at h
  rw [h]
  rfl

end GlobalTheory.TopSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_refl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp only [reL, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_refl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  simp [reGL]

theorem fvTie_of_coords (hc : CMData F E) (S : HSpace E) {cls : Type}
    (y : cls → Formalism.L2.Herm.UAf hc S) (lat : cls → Submodule (𝓞 E) S.V)
    (w : HeightOneSpectrum (𝓞 F)) (k : Type) [AddCommGroup k]
    (fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) {b : ℕ} (h : S.rank = b)
    (J : Matrix (Fin b) (Fin b) E) (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ c, y' c = reGL h _ (y c).1)
    (fT : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb')) →+ k)
    (hfv : ∀ c (z : Formalism.HermitianLatticesTheory.dual S.hT (lat c))
      (hz : ((bc (prV (E := E) w) (y' c))⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (reV h E (Formalism.L2.Herm.crd S z.1) a)) ∈
        latS (F := F) (w.adicCompletion F) (intV E w)
          (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb'))),
      fz c z = fT ⟨_, hz⟩) :
    Nonempty (Formalism.L2.Herm.FvTie hc S Lb y lat w k fz) := by
  subst h
  obtain rfl : J = S.gram := by rw [hJ]; ext i j; simp
  obtain rfl : Lb' = Lb := hL.trans (reL_refl Lb)
  obtain rfl : y' = fun c => (y c).1 := funext fun c => (hy c).trans (reGL_refl _ _)
  refine ⟨⟨fT, fun c z t ht => ?_⟩⟩
  have ht' : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) = t.1 := by
    have e : (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (Formalism.L2.Herm.crd S z.1 a) := rfl
    rw [e, ← ht, Matrix.mulVec_mulVec]
    simp
  have hz : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) S.gram Lb')) := by
    rw [ht']; exact t.2
  rw [hfv c z hz]
  exact congrArg fT (Subtype.ext ht')

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (G : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (G.reindex (finCongr h) (finCongr h)) (reV h E x) (reV h E y) = hform σ G x y := by
  subst h
  have e : (G.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) = G := by ext i j; simp
  rw [e]; rfl

end Generic

theorem crdN_mem_Ld {D : D7} (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ Ld D u i hi c := by
  refine Submodule.subset_span ?_
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have h1 : (D.sp.X i).hT x0 z.1 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := z.2
    simp only [Formalism.L2.Herm.Ld, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
    exact this x0 hx0
  rw [Formalism.L2.Herm.hT_crd D.sp.cm] at h1
  have h2 := hform_reindex (rankN D i hi) (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd _ x0) (Formalism.L2.Herm.crd _ z.1)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
  exact ⟨r, hr.trans h2.symm⟩

set_option maxHeartbeats 4000000 in

theorem fvTie_top {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (h1 : 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u D.R.m) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl β).Lb (H.cls u D.R.m h1 le_rfl β).y
      (fun c => D.clsLat u D.R.m c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
  obtain rfl : β = chM H u := @Subsingleton.elim _ (@Unique.instSubsingleton _ (H.Ch_m u).some) _ _
  have key : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl (chM H u)).Lb
        (H.cls u D.R.m h1 le_rfl (chM H u)).y (fun c => D.clsLat u D.R.m c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
    intro w hw
    subst hw
    have hc := hH.carM u
    refine fvTie_of_coords D.sp.cm (D.sp.X D.R.m) _ _ _ _ _ _ (rankN D D.R.m le_rfl) (gramN D D.R.m le_rfl) rfl
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb hc.Lb_eq
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c.1).1) (fun c => hc.y_eq c.1)
      (((F u).fMe D.R.m le_rfl (Or.inr rfl) v).toAddMonoidHom.comp
        (((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.fT _ ((F u).atT.eV v).2).toAddMonoidHom) ?_
    intro c z hz
    have hz' := crdN_mem_Ld u D.R.m le_rfl c.1 z
    have e1 := (F u).fv D.R.m le_rfl (Or.inr rfl) v c.1 ⟨_, hz'⟩ hz
    have e2 := hT.pr u D.R.m le_rfl v c.1 z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv D.R.m v c.1 p) e2.symm).trans e1
  exact key _ (by rw [hH.eV u])

set_option maxHeartbeats 4000000 in

theorem fvTie_chart_top : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u h1 v β
  exact fvTie_top H F A hH hT u h1 v β

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHilbertModelInjectiveContainsGoodForms
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.LiftHilbertModel

open Formalism.IndefR.Mult GlobalTheory.HilbertLevels

theorem hasPeterssonInner_smul_measure' {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {T T' : MMap M} {c : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) :
    IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]

theorem ipM_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {T T' : MMap M} {a : ℝ} (ha : 0 ≤ a) (hne : ∀ τ, ∃ w : M.sm τ, w ≠ 0)
    (h : ∃ c, IsMultIP M μ 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  choose w hw using hne
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 := hasPeterssonInner_smul_measure' M μ 𝓕 ha (ipM_spec M μ 𝓕 T T' h)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 (ipM_spec M _ 𝓕 T T' ⟨_, h1⟩) h1

theorem mult_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Formalism.IndefR.Datum.InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem wat_le_wall (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) : R.Wat i σ P ≤ R.Wall i σ :=
  le_trans inf_le_left (mult_mono R.θ (R.MW i σ) (levS_mono fun x hx =>
    lev_datY_triv D.R.r D.R.t 0 (r_le_rank_Wc i) R.Pg ∅ P (fun _ _ => 1) (fun _ => 1) x hx))

theorem model_facts (hI : Inputs D) (hM : R.IsModels) (y : Hd R) (i : Fin D.R.m) :
    Function.Injective (R.HW i (sg0 D A)).e ∧
      R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ≤ LinearMap.range (R.HW i (sg0 D A)).e ∧
      ∀ u v, (y.L F).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) =
        (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  obtain ⟨h1, h2, h3⟩ := hM.HW i (sg0 D A)
  refine ⟨h1, h2 ▸ wat_le_wall R i _ _, fun u v => ?_⟩
  have h0 := hM.νW i
  have hu : (R.HW i (sg0 D A)).e u ∈ R.Wall i (sg0 D A) := h2 ▸ LinearMap.mem_range_self _ u
  have hv : (R.HW i (sg0 D A)).e v ∈ R.Wall i (sg0 D A) := h2 ▸ LinearMap.mem_range_self _ v
  have hs := ipM_smul_measure (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) (inv_pos.2 (nP_pos F false)).le
    (hI.sm _ _ _) (hI.schur _ (D.sp.W_sig _) _ R.θ _ _ _ _ _ hM.inf h0.1.1 h0.2 _ hu _ hv)
  have e : (y.L F).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
        ipMT (R.MW i (sg0 D A)) (ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i) (R.fdW i)
          (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) := rfl
  rw [e, h3, ipMT, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hs, ipAt, mul_left_comm]

end

theorem hilbert_model_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), Function.Injective (R.toRealDat.HW i (sg0 D A3.A)).e ∧ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) ≤ LinearMap.range (R.toRealDat.HW i (sg0 D A3.A)).e ∧ ∀ u v, (y.L F.lv2).ipWc i (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e u)) (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e v)) = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hI hP _ y i
  exact model_facts R.toRealDat F.lv2 hI hP.char.base.models y i

end GlobalTheory.LiftHilbertModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_law_implies_adelic_extension_base_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | exact GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | (intros; apply GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyA
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem algebraMap_mem_span_of_mem_span {K L A M : Type} [Field K] [Field L] [Algebra K L]
    [Field A] [CommRing M] [Algebra L M] [Algebra A M] (g : K →+* A)
    (hg : ∀ c : K, algebraMap A M (g c) = algebraMap L M (algebraMap K L c))
    {ι : Type} (s : ι → L) (x : L) (hx : x ∈ Submodule.span K (Set.range s)) :
    algebraMap L M x ∈ Submodule.span A (Set.range fun i => algebraMap L M (s i)) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Algebra.smul_def, map_mul, ← hg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hy

theorem linearIndependent_completion_of_irreducible_minpoly :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  intro K L _ _ _ _ _ v v' f hf hirr
  letI := f.toAlgebra
  intro n b
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hcomp : f.comp (algebraMap K (v.adicCompletion K)) =
      (algebraMap L (v'.adicCompletion L)).comp (algebraMap K L) := RingHom.ext hf
  have hroot : Polynomial.aeval (algebraMap L (v'.adicCompletion L) α)
      ((minpoly K α).map (algebraMap K (v.adicCompletion K))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (f.comp (algebraMap K (v.adicCompletion K))) _ _ = 0
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmin : (minpoly K α).map (algebraMap K (v.adicCompletion K)) =
      minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α) :=
    minpoly.eq_of_irreducible_of_monic (hirr α) hroot ((minpoly.monic hint).map _)
  have hdeg : (minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree
      = n := by
    rw [← hmin, (minpoly.monic hint).natDegree_map, ← IntermediateField.adjoin.finrank hint, hα,
      IntermediateField.finrank_top', Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hpow := linearIndependent_pow (K := v.adicCompletion K)
    (algebraMap L (v'.adicCompletion L) α)
  have hle : Submodule.span (v.adicCompletion K) (Set.range fun i : Fin (minpoly
      (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree =>
        (algebraMap L (v'.adicCompletion L) α) ^ (i : ℕ)) ≤
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := algebraMap_mem_span_of_mem_span (M := v'.adicCompletion L)
      (algebraMap K (v.adicCompletion K)) hf b (α ^ (i : ℕ)) (by rw [b.span_eq]; trivial)
    simpa using this
  have h1 := finrank_span_eq_card hpow
  have h2 := finrank_range_le_card (R := v.adicCompletion K)
    (fun i => algebraMap L (v'.adicCompletion L) (b i))
  haveI : Module.Finite (v.adicCompletion K) (Submodule.span (v.adicCompletion K)
      (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have h3 := Submodule.finrank_mono hle
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_fin] at h1 h2 ⊢
  rw [Set.finrank] at h2 ⊢
  omega

end GlobalTheory
end


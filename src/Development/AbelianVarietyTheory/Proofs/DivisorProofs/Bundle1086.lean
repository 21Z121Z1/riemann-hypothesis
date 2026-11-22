import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOver
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.RepOver

noncomputable def coverOf {T : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i)) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J Z z (fun p => hc p) hz

theorem hom_eq_of_local {T S : Scheme.{0}} (t t' : T ⟶ S)
    (h : ∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧
      z ≫ t = z ≫ t') : t = t' := by
  choose Z z hz hp he using h
  exact Scheme.Cover.hom_ext (coverOf Z z hz (fun p => ⟨p, hp p⟩)) t t' he

theorem exists_glue {T S : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i))
    (t : ∀ i, Z i ⟶ S)
    (ht : ∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k →
      a ≫ t i = b ≫ t k) : ∃ t₀ : T ⟶ S, ∀ i, z i ≫ t₀ = t i :=
  ⟨Scheme.Cover.glueMorphisms (coverOf Z z hz hc) t
      (fun i k => ht i k _ _ _ pullback.condition),
    fun i => Scheme.Cover.ι_glueMorphisms (coverOf Z z hz hc) t _ i⟩

variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1)

theorem map_map {X Y Z : Over S} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a.left ≫ b.left = c.left)
    (d : F.obj (op Z)) : F.map a.op (F.map b.op d) = F.map c.op d := by
  have : c = a ≫ b := Over.OverMorphism.ext (by simpa using h.symm)
  subst this
  simp

theorem sig_eq {Y : Scheme.{0}} (r r' : Y ⟶ S) (h : r = r') (e : F.obj (op (Over.mk r)))
    (e' : F.obj (op (Over.mk r'))) (c : Over.mk r ⟶ Over.mk r') (hc : c.left = 𝟙 Y)
    (he : F.map c.op e' = e) :
    (⟨r, e⟩ : Σ t : Y ⟶ S, F.obj (op (Over.mk t))) = ⟨r', e'⟩ := by
  subst h
  have : c = 𝟙 _ := Over.OverMorphism.ext hc
  subst this
  subst he
  simp

noncomputable def tot : Scheme.{0}ᵒᵖ ⥤ Type 1 where
  obj X := Σ t : X.unop ⟶ S, F.obj (op (Over.mk t))
  map {X Y} f := TypeCat.ofHom fun y =>
    ⟨f.unop ≫ y.1, F.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ y.1) ⟶ Over.mk y.1).op y.2⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    exact sig_eq F _ _ (Category.id_comp _) _ _ _ rfl rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    refine sig_eq F _ _ (Category.assoc _ _ _) _ _ (Over.homMk (𝟙 _) (by simp)) rfl ?_
    refine (map_map F _ _ (Over.homMk g.unop (Category.assoc _ _ _).symm) (by simp) _).trans ?_
    exact map_map F _ _ _ (by simp) _

def el {V : Over S} (v : F.obj (op V)) : (tot F).obj (op V.left) := ⟨V.hom, v⟩

theorem el_inj {V : Over S} {v v' : F.obj (op V)} (h : el F v = el F v') : v = v' :=
  eq_of_heq (Sigma.mk.inj h).2

theorem map_el {Y V : Over S} (a : Y ⟶ V) (v : F.obj (op V)) :
    (tot F).map a.left.op (el F v) = el F (F.map a.op v) :=
  sig_eq F (a.left ≫ V.hom) Y.hom (Over.w a) _ _ (Over.homMk (𝟙 _) (by simp)) rfl
    (map_map F _ _ _ (by simp) _)

theorem w_of_map_el {Y V : Over S} {a : Y.left ⟶ V.left} {v : F.obj (op V)} {y : F.obj (op Y)}
    (h : (tot F).map a.op (el F v) = el F y) : a ≫ V.hom = Y.hom :=
  congrArg Sigma.fst h

theorem w_of_map_eq {Y : Scheme.{0}} {V V' : Over S} {a : Y ⟶ V.left} {b : Y ⟶ V'.left}
    {v : F.obj (op V)} {v' : F.obj (op V')}
    (h : (tot F).map a.op (el F v) = (tot F).map b.op (el F v')) : a ≫ V.hom = b ≫ V'.hom :=
  congrArg Sigma.fst h

theorem map_eq_iff {Y V V' : Over S} (a : Y ⟶ V) (b : Y ⟶ V')
    (v : F.obj (op V)) (v' : F.obj (op V')) :
    (tot F).map a.left.op (el F v) = (tot F).map b.left.op (el F v') ↔
      F.map a.op v = F.map b.op v' := by
  rw [map_el, map_el]
  exact ⟨el_inj F, fun h => by rw [h]⟩

end GlobalTheory.RepOver

open GlobalTheory.RepOver in

theorem GlobalTheory.RepOver.representable_over : ∀ (S : Scheme.{0}) (F : (Over S)ᵒᵖ ⥤ Type 1), (∀ (T : Over S) (y y' : F.obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Over S) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Over S) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Over S) (y : F.obj (op T)), ∃ W : T.left.Opens, ∀ (Y : Over S) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a.left q ∈ W) → (∀ (T : Over S) (y : F.obj (op T)) (p : T.left), ∃ (i : Ix) (Y : Over S) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a.left ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Over S) (x₀ : F.obj (op B)), (∀ (T : Over S) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro S F hsep hglue Ix U x hmono hopen hcov
  refine Exists.elim (GlobalTheory.T.representable_of_zariski_sheaf_open_charts_large (tot F) ?_ ?_ Ix (fun i => (U i).left)
    (fun i => el F (x i)) ?_ ?_ ?_) ?_
  rotate_right
  · rintro B ⟨⟨tB, dB⟩, huniv, j, hj, hc, hx⟩
    refine ⟨Over.mk tB, dB, fun T y => ?_, fun i => Over.homMk (j i)
      (w_of_map_el F (V := Over.mk tB) (hx i)), hj, hc, fun i => ?_⟩
    · obtain ⟨g, hg, hu⟩ := huniv T.left (el F y)
      refine ⟨Over.homMk g (w_of_map_el F (V := Over.mk tB) hg), ?_, fun g' hg' => ?_⟩
      · exact el_inj F ((map_el F _ dB).symm.trans hg)
      · exact Over.OverMorphism.ext (hu g'.left ((map_el F g' dB).trans (congrArg (el F) hg')))
    · exact el_inj F ((map_el F _ dB).symm.trans (hx i))
  · rintro T ⟨t, d⟩ ⟨t', d'⟩ h
    obtain rfl : t = t' := hom_eq_of_local t t' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Z, z, hz, hp, congrArg Sigma.fst he⟩
    obtain rfl : d = d' := hsep (Over.mk t) d d' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Over.mk (z ≫ t), Over.homMk z rfl, hz, hp, (map_eq_iff F _ _ d d').1 he⟩
    rfl
  · intro T J Z z y hz hc hy
    obtain ⟨t, ht⟩ := exists_glue Z z hz hc (fun i => (y i).1)
      (fun i k Y a b hab => congrArg Sigma.fst (hy i k Y a b hab))
    obtain ⟨d, hd⟩ := hglue (Over.mk t) J (fun i => Over.mk (y i).1)
      (fun i => Over.homMk (z i) (ht i)) (fun i => (y i).2) hz hc
      (fun i k Y a b hab => (map_eq_iff F a b _ _).1
        (hy i k Y.left a.left b.left (congrArg (fun c => c.left) hab)))
    exact ⟨⟨t, d⟩, fun i => (map_el F (Y := Over.mk (y i).1) (V := Over.mk t)
      (Over.homMk (z i) (ht i)) d).trans (congrArg (el F) (hd i))⟩
  · intro i Y u u' h
    have := hmono i (Over.mk (u ≫ (U i).hom)) (Over.homMk u rfl)
      (Over.homMk u' (w_of_map_eq F h).symm) ((map_eq_iff F _ _ _ _).1 h)
    exact congrArg (fun c => c.left) this
  · rintro i T ⟨t, d⟩
    obtain ⟨W, hW⟩ := hopen i (Over.mk t) d
    refine ⟨W, fun Y a => Iff.trans ?_ (hW (Over.mk (a ≫ t)) (Over.homMk a rfl))⟩
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨Over.homMk u (w_of_map_eq F (V := Over.mk t) hu).symm, (map_eq_iff F _ _ _ _).1 hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u.left, (map_eq_iff F _ _ _ _).2 hu⟩
  · rintro T ⟨t, d⟩ p
    obtain ⟨i, Y, a, u, hp, h⟩ := hcov (Over.mk t) d p
    exact ⟨i, Y.left, a.left, u.left, hp, (map_eq_iff F _ _ _ _).2 h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjType

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

noncomputable def rt (P : HeightOneSpectrum (𝓞 E)) : ℝ := (Real.sqrt ((Ideal.absNorm P.asIdeal : ℕ) : ℝ))⁻¹

theorem rt_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < rt P :=
  inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot))))

theorem rt_sq (P : HeightOneSpectrum (𝓞 E)) : rt P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [rt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem mk_eq (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : FinitePlace.mk P (k : E) = (rt P ^ ordF P k) ^ 2 := by
  obtain ⟨u, hu, hk⟩ := GlobalTheory.EtaConjChar.exists_unit_part P k
  generalize ordF P k = n at hk ⊢
  rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, GlobalTheory.EtaConjLocal.mk_unit P hu,
    GlobalTheory.EtaConjLocal.mk_unif, mul_one, ← rt_sq, sq, sq, mul_zpow]

theorem prod_rt [IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) : (∏ i, ‖φ i k‖) * ∏ P ∈ S, rt P ^ ordF P k = 1 := by
  have h := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    finprod_eq_prod_of_mulSupport_subset (s := S)] at h
  · rw [← sq_eq_sq₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun P _ => (zpow_pos (rt_pos P) _).le)) zero_le_one, one_pow, mul_pow, ← Finset.prod_pow,
      ← Finset.prod_pow, ← h]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
    · exact Finset.prod_congr rfl fun P _ => (mk_eq P k).symm
  · intro P hP
    refine hS P fun h0 => hP ?_
    exact (mk_eq P k).trans (by rw [h0]; simp)

theorem prod_val (χ : HChar E) (hu : ∀ P, χ.UnrAt P) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) :
    ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ S, (((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF P k =
      ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) := by
  have h := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at h
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => hS P fun h0 => hP (by simp [h0]))] at h
  have h' := congrArg (Units.val : ℂˣ → ℂ) h
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at h'
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, h', one_mul]
  push_cast
  rfl

theorem unrAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1) : χ.UnrAt P := by
  intro x
  have hc : IsClopen {x : (P.adicCompletion E)ˣ | IsUnitAt P x} := by
    have := (Valued.isClopen_sphere (P.adicCompletion E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := P.adicCompletion E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on (p := fun x => IsUnitAt P x → χ.loc P x = 1) x ?_
    fun k hk => h k ((P.valuedAdicCompletion_eq_valuation' _).symm.trans hk)
  exact isClosed_imp hc.2 (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)

variable {L : Type} [Field L] (ι σ : L →+* ℂ) {χ χ' : HChar E} (hu : ∀ P, χ.UnrAt P) (hu' : ∀ P, χ'.UnrAt P)
  (y : HeightOneSpectrum (𝓞 E) → L) (hy : ∀ P, ι (y P) = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ))
  (hy' : ∀ P, σ (y P) = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ))

include hu hu' hy hy'

theorem inf_eq [IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (hi : χ.HasInf φ fun _ => 1)
    (ht : ∀ k : E, ∃ t : L, ι t = ∏ i, φ i k ∧ σ t = ∏ i, φ i k) (k : Eˣ) : χ'.inf k = χ.inf k := by
  obtain ⟨t, ht1, ht2⟩ := ht k
  let S := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
  have hS : ∀ P, ordF P k ≠ 0 → P ∈ S := fun P hP => (Set.Finite.mem_toFinset _).2 hP
  have h1 := prod_val χ hu k S hS
  have h2 := prod_val χ' hu' k S hS
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) (prod_rt φ hφ k S hS)
  have h4 : ((χ.inf k : ℂˣ) : ℂ) * ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = ∏ i, φ i k := by
    rw [hi k, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_one, div_mul_cancel₀ _ (by simp)]
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h2
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h3
  generalize ∏ P ∈ S, y P ^ ordF P k = Y at h1 h2
  generalize ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) = r at h1 h2 h3
  generalize ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = s at h3 h4
  have h5 : Y * t = 1 := ι.injective (by
    rw [map_mul, map_one, ht1, ← h4, ← h3, ← h1]
    ring)
  have h6 : σ Y * (∏ i, φ i k) = 1 := by rw [← ht2, ← map_mul, h5, map_one]
  refine Units.ext ?_
  calc ((χ'.inf k : ℂˣ) : ℂ) = (χ'.inf k : ℂˣ) * (σ Y * (((χ.inf k : ℂˣ) : ℂ) * s)) := by rw [h4, h6, mul_one]
    _ = (χ.inf k : ℂˣ) * (s * (((χ'.inf k : ℂˣ) : ℂ) * σ Y)) := by ring
    _ = _ := by rw [h2, h3, mul_one]

theorem resFin_eq {F : Type} [Field F] [NumberField F] [Algebra F E] (h2 : Module.finrank F E = 2)
    (hF : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal) (hr : χ.ResEta F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ'.resFin v k = χ.resFin v k := by
  have key : ∀ (ψ : HChar E), (∀ P, ψ.UnrAt P) →
      ∏ P ∈ aboveF (L := E) F v, (((ψ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF v k =
        ((ψ.resFin v k : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ ^ ordF v k := by
    intro ψ hψ
    have h1 : ∏ P ∈ aboveF (L := E) F v, rt P = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
      rw [← sq_eq_sq₀ (Finset.prod_nonneg fun P _ => (rt_pos P).le) (by positivity), ← Finset.prod_pow]
      simp only [rt_sq]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, GlobalTheory.ToricDistribution.prod_absNorm hF, h2, Nat.cast_pow, inv_pow]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    · rw [HChar.resFin_apply, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [GlobalTheory.HeckeProduct.locK_unr ψ (hψ P), GlobalTheory.ToricDistribution.ordF_up hF, GlobalTheory.ToricDistribution.mem_aboveF.1 hP,
        Units.val_zpow_eq_zpow_val]
    · rw [Finset.prod_zpow, ← Complex.ofReal_prod, h1]
      simp
  have h1 := key χ hu
  have h3 := key χ' hu'
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h3
  obtain ⟨z, hz⟩ : ∃ z : L, ∀ f : L →+* ℂ, f z = ((χ.resFin v k : ℂˣ) : ℂ) := by
    rw [hr.1, etaFin]
    split_ifs
    · exact ⟨(-1) ^ ordF v k, fun f => by simp⟩
    · exact ⟨1, fun f => by simp⟩
  have h4 : ∏ P ∈ aboveF (L := E) F v, y P ^ ordF v k = z * ((Ideal.absNorm v.asIdeal : ℕ) : L)⁻¹ ^ ordF v k :=
    ι.injective (by rw [h1, map_mul, hz, map_zpow₀, map_inv₀, map_natCast])
  rw [h4, map_mul, hz, map_zpow₀, map_inv₀, map_natCast] at h3
  refine Units.ext (mul_right_cancel₀ (zpow_ne_zero _ (inv_ne_zero ?_)) h3.symm)
  exact Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

end General

theorem isEtaT_of_conj {D : D7} {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {η η' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E}
    (hc : ChrEq η χ) (hc' : ChrEq η' χ') (hχ : IsEtaT D.host χ) (hη : IsEtaConj σ η η') : IsEtaT D.host χ' := by
  have hu' : ∀ P, χ'.UnrAt P := fun P => unrAt_of_locK χ' P (GlobalTheory.EtaConjChar.locK_eq_one hc' hη.2.1 P)
  have hy : ∀ P, ∃ y : D.what₂.LL, D.what₂.embLL y = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ) ∧
      σ y = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ) := by
    intro P
    obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
    obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
    rw [hc.2 P e he _ (locU he.1 (unif P)) rfl] at hy1
    rw [hc'.2 P e he _ (locU he.1 (unif P)) rfl] at hy2
    exact ⟨y, hy1, hy2⟩
  choose y hy hy' using hy
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  haveI := hcm.cplx
  obtain ⟨hb, hl⟩ := (labels_overK σ).1 hσ
  have hinf : ∀ k, (χ' * χ⁻¹).inf k = 1 := fun k => by
    rw [HChar.inf_mul, HChar.inf_inv, mul_inv_eq_one]
    refine inf_eq D.what₂.embLL σ hχ.unr hu' y hy hy' (embPsi D.host) hcm.bij hχ.inf (fun a => ?_) k
    refine ⟨∏ τ, labLL D τ a, ?_, ?_⟩
    · rw [map_prod, ← D.eTau.prod_comp]
      exact Finset.prod_congr rfl fun τ _ => embLL_embE D _
    · rw [map_prod, ← D.eTau.prod_comp, ← hb.prod_comp]
      exact Finset.prod_congr rfl fun ρ _ => RingHom.congr_fun (hl ρ) a
  obtain ⟨n, hn, ho⟩ := GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one _ _ hinf
  have hp : ∀ x, (χ' * χ⁻¹).1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) ho
  have hξ : IsClsF D.host (χ' * χ⁻¹) := by
    refine ⟨HChar.isUnitary_of_order hn ho, fun P => (hu' P).mul (hχ.unr P).inv, hinf, fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, HChar.resFin_inv, mul_inv_eq_one]
      exact resFin_eq D.what₂.embLL σ hχ.unr hu' y hy hy' hcm.rank
        (GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm) hχ.res v k
    · rw [HChar.resInf_apply]
      exact Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hn.ne' hp w' _
  have := hχ.mul_cls hξ
  rwa [mul_comm χ', mul_inv_cancel_left] at this

theorem resEta_hasInfExp_of_isEtaConj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ σ hσ η' hη
  obtain ⟨χ', hc⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  have h := isEtaT_of_conj hσ hR.lev.eta hc R.C.isEta hη
  have he := GlobalTheory.Mem.EtaTilde.isEta_res D η' χ' hc h
  refine ⟨⟨⟨_, he⟩, fun η hη' a => ?_⟩, fun τ => ⟨1, by norm_num, ?_, fun θ hθ x hx hx' => ?_⟩⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' he, pow_one, MonoidHom.comp_apply]
  · obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  · rw [GlobalTheory.Mem.EtaTilde.val_infinite D η' χ' hc h.unr _ h.inf θ hθ x hx,
      Finset.prod_eq_single τ (fun τ' _ hτ => by rw [hx' τ' hτ]; simp) (by simp)]

end GlobalTheory.EtaConjType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
section
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.SteepMult

variable {R S : ℕ}

abbrev NC (R S : ℕ) : Type := {x : Ix R S × Ix R S // ¬ sameBlock x.1 x.2}

def eNC (x : NC R S) : Mat R S := Eab x.1.1 x.1.2

def adP (Z : Mat R S) (y x : NC R S) : ℂ :=
  Z y.1.1 x.1.1 * (if y.1.2 = x.1.2 then 1 else 0) - (if y.1.1 = x.1.1 then 1 else 0) * Z x.1.2 y.1.2

lemma adCoeff_add (Z Z' : Mat R S) (y x : NC R S) : adP (Z + Z') y x = adP Z y x + adP Z' y x := by
  simp only [adP, Matrix.add_apply]; ring

lemma adCoeff_smul (c : ℂ) (Z : Mat R S) (y x : NC R S) : adP (c • Z) y x = c * adP Z y x := by
  simp only [adP, Matrix.smul_apply, smul_eq_mul]; ring

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def factorOp (k : ℕ) (i : Fin k) (Z : Mat R S) : Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Ψ g := ∑ x, adP Z (g i) x • Ψ (Function.update g i x)
  map_add' Ψ Φ := by ext g; simp [Finset.sum_add_distrib]
  map_smul' c Ψ := by ext g; simp [Finset.smul_sum, smul_comm c]

def tAct (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) : Mat R S →ₗ[ℂ] Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Z := LinearMap.pi (fun g => actW Z ∘ₗ LinearMap.proj g) + ∑ i, factorOp k i Z
  map_add' Z Z' := by
    ext Ψ g
    simp [factorOp, adCoeff_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c Z := by
    ext Ψ g
    simp [factorOp, adCoeff_smul, mul_smul, Finset.smul_sum]

lemma tAct_apply (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W)
    (g : Fin k → NC R S) :
    tAct k actW Z Ψ g = actW Z (Ψ g) + ∑ i, ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := by
  simp [tAct, factorOp]

def formT (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) :
    ((Fin k → NC R S) → W) →ₗ⋆[ℂ] ((Fin k → NC R S) → W) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun Ψ Φ => ∑ g, B (Ψ g) (Φ g))
    (fun Ψ Ψ' Φ => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])
    (fun Ψ Φ Φ' => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])

lemma formT_apply (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (Ψ Φ : (Fin k → NC R S) → W) :
    formT k B Ψ Φ = ∑ g, B (Ψ g) (Φ g) := rfl

def IsUnitary (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, star (B x y) = B y x) ∧ (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
    ∀ a b, sameBlock a b → ∀ x y, B (actW (Eab a b) x) y = B x (actW (Eab b a) y)

example : IsUnitary (R := 1) (S := 1) (W := ℂ) 0
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => star x * y) (fun _ _ _ => by simp [add_mul])
      (fun _ _ _ => by simp [mul_assoc]) (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp; ring)) := by
  refine ⟨fun x y => by simp [mul_comm], fun x hx => ?_, fun a b _ x y => by simp⟩
  have : star x * x = ((Complex.normSq x : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [LinearMap.mk₂'ₛₗ_apply, this, Complex.ofReal_re]
  exact Complex.normSq_pos.2 hx

def kpart (Z : Mat R S) : Mat R S := Matrix.of fun a b => if sameBlock a b then Z a b else 0

lemma isKC_kpart (Z : Mat R S) : IsKC (kpart Z) := fun a b h => by simp [kpart, h]

lemma kpart_of_isKC {Z : Mat R S} (h : IsKC Z) : kpart Z = Z := by
  ext a b
  by_cases hab : sameBlock a b
  · simp [kpart, hab]
  · simp [kpart, hab, h a b hab]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def restrAct (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) :
    Mat R S →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (act (kpart Z)).restrict fun x hx => hN _ (isKC_kpart Z) x hx
  map_add' Z Z' := by
    ext x
    have : kpart (Z + Z') = kpart Z + kpart Z' := by ext a b; by_cases h : sameBlock a b <;> simp [kpart, h]
    simp [this]
  map_smul' c Z := by
    ext x
    have : kpart (c • Z) = c • kpart Z := by ext a b; by_cases h : sameBlock a b <;> simp [kpart, h]
    simp [this]

lemma restrAct_apply (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) (Z : Mat R S)
    (x : N) : (restrAct act N hN Z x : V) = act (kpart Z) x := rfl

def word (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (g : Fin k → NC R S) : Module.End ℂ V :=
  (List.ofFn fun i => act (eNC (g i))).prod

def phiN (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (k : ℕ) :
    ((Fin k → NC R S) → N) →ₗ[ℂ] V :=
  ∑ g, word act g ∘ₗ N.subtype ∘ₗ LinearMap.proj g

lemma phiN_apply (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (k : ℕ) (Ψ : (Fin k → NC R S) → N) :
    phiN act N k Ψ = ∑ g, word act g (Ψ g) := by
  simp [phiN]

def filt (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (k : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin (k + 1), LinearMap.range (phiN act N j)

def section1 {k : ℕ} (Ψ : (Fin k → NC R S) → W) (i : Fin k) (g : Fin k → NC R S) : (Fin 1 → NC R S) → W :=
  fun h => Ψ (Function.update g i (h 0))

end GlobalTheory.SteepMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefFormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_signature_one_preserves_posDef_form : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  first | (exact @GlobalTheory.similitude_preserves_posDef) | (exact GlobalTheory.similitude_preserves_posDef) | (intros; apply GlobalTheory.similitude_preserves_posDef  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOneStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W : HeightOneSpectrum (𝓞 E)), SplitsFully E (W.under (𝓞 F)) → ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  first | exact @GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | exact GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | (intros; apply GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully <;> assumption)
end


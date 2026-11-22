import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabLeBlockTri
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundary
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic.Cobd

theorem res_zero {F : Shv ℤ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_id {F : Shv ℤ} {U : Scheme.{0}} (s : Sec F U) : Sec.res (𝟙 U) s = s := by simp [Sec.res]

theorem res_res {F : Shv ℤ} {W V U : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (s : Sec F U) :
    Sec.res g' (Sec.res g s) = Sec.res (g' ≫ g) s := by simp [Sec.res]

theorem umap_id {U : Scheme.{0}} (b : (Γ(U, ⊤))ˣ) : Units.map (𝟙 U : U ⟶ U).appTop.hom.toMonoidHom b = b := by
  ext; simp

theorem umap_comp {W V U : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (b : (Γ(U, ⊤))ˣ) :
    Units.map (g' ≫ g).appTop.hom.toMonoidHom b =
      Units.map g'.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b) := by
  ext; simp; rfl

theorem ev_sub {E : Spc} {I : Cx ℤ} {n : ℤ} (a b : Cochain ((chains ℤ).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := map_sub (CupSpec.evHom I n p s h U x) a b

theorem ev_comp {E : Spc} {L M : Cx ℤ} {n₁ n₂ n : ℤ} (a : Cochain ((chains ℤ).obj E) L n₁) (b : Cochain L M n₂)
    (hn : n₁ + n₂ = n) (p : ℕ) (t s : ℤ) (ht : -(p : ℤ) + n₁ = t) (hs : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (a.comp b hn) p s hs U x = Sec.map (b.v t s (by omega)) (ev a p t ht U x) := by
  rw [CupSpec.ev_def, CupSpec.ev_def, Cochain.comp_v a b hn (-(p : ℤ)) t s ht (by omega)]
  rfl

theorem sglZ (C : Shv ℤ) (k : ℤ) (hk : k ≠ 0) : IsZero ((sgl C).X k) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 C k hk

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  have e : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
      SimplexCategory.subinterval 0 1 (by omega) :=
    CupSpec.hom_ext_val _ _ fun v => by
      rw [CupSpec.δ_val, CupSpec.sub_val]; have := v.2; simp; omega
  show (E.map (SimplexCategory.δ (2 : Fin 3)).op).app (op U) x = _
  rw [e]; rfl

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  have e : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
      SimplexCategory.subinterval 1 1 (by omega) :=
    CupSpec.hom_ext_val _ _ fun v => by
      rw [CupSpec.δ_val, CupSpec.sub_val]; simp
  show (E.map (SimplexCategory.δ (0 : Fin 3)).op).app (op U) x = _
  rw [e]; rfl

theorem mkiff {E : Spc} {I : Cx ℤ} (a b : Cocycle ((chains ℤ).obj E) I 2) :
    CohomologyClass.mk a = CohomologyClass.mk b ↔ ∃ w : Cochain _ I 1, δ 1 2 w = a.1 - b.1 := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  rfl

theorem sep_zero {F : Shv ℤ} {U : Scheme.{0}} (s : Sec F U) (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ F U).1 s 0 ?_
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => (hP V g hg).trans (res_zero g).symm⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem isUnit_of_sx {q : ℕ} {E : Spc} (hE : Inv q E) {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    IsUnit (q : Γ(U, ⊤)) :=
  hE U ⟨x.sub 0 0 (by omega)⟩

theorem eta_unique (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
    (b : (Γ(U, ⊤))ˣ) (η η' : Sec ((res ℤ (twZ q)).X 0) U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b →
      Sec.res g η = dv q φ V v)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b →
      Sec.res g η' = dv q φ V v) : η = η' :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ _ U).1 η η' (loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq b)
    fun V g ⟨v, hv⟩ => (h V g v hv).trans (h' V g v hv).symm)

def thF (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ (twZ q)).X s) U
  | 1, s, h, U, x => Sec.map ((res ℤ (twZ q)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom (η U x)
  | _, _, _, _, _ => 0

theorem thF_zero (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) (s : ℤ)
    (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E 0 U) : thF q η 0 s h U x = 0 := rfl

theorem thF_two (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : thF q η (p + 2) s h U x = 0 := rfl

theorem thF_one (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) : thF q η 1 0 h U x = η U x := by
  simp [thF, Sec.map]

theorem thF_nat (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (hη : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (η U x) = η V (x.res g)) :
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (thF q η p s h U x) = thF q η p s h V (x.res g) := by
  intro p s h V U g x
  match p with
  | 0 => rw [thF_zero, thF_zero, res_zero]
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [thF_one, thF_one, hη]
  | p + 2 => rw [thF_two, thF_two, res_zero]

theorem thF_one' (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((0 + 1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E (0 + 1) U) : thF q η (0 + 1) 0 h U x = η U x :=
  thF_one q η h U x

theorem thF_two' (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((1 + 1 : ℕ) : ℤ) + 1 = -1) (U : Scheme.{0}) (x : Sx E (1 + 1) U) : thF q η (1 + 1) (-1) h U x = 0 := rfl

theorem smap_sub {F G : Shv ℤ} (f : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map f (a - b) = Sec.map f a - Sec.map f b := map_sub _ _ _

theorem cobd : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ E L hE φ hφ C a w hw
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hE
  obtain ⟨β, hβ⟩ := SemiMap.image_exists (restrMap (Int.castRingHom (ZMod q)) (tw q 1)) E 2 γ
  have hβc : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) = CohomologyClass.mk β := by
    rw [← hγ]; exact SemiMap.op_spec _ E 2 γ β hβ
  rw [hβc]
  have h2 : (1 : ℤ) + 1 = 2 := by norm_num
  change CohomologyClass.mk (zcomp a w h2) = _
  choose η hη using fun (U : Scheme.{0}) (x : Sx E 1 U) => hφ U (lineUnit L x) (isUnit_of_sx hE x)
  have ηnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (η U x) = η V (x.res g) := by
    intro V U g x
    refine eta_unique q φ (isUnit_of_sx hE (x.res g)) (lineUnit L (x.res g)) _ _ (fun V' g' v hv => ?_)
      (hη V (x.res g))
    rw [res_res]
    exact hη U x V' (g' ≫ g) v (by rw [umap_comp, ← PicSpec.lineUnit_res]; exact hv)
  have ηroot : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → η U x = dv q φ U v := by
    intro U x v hv
    have := hη U x U (𝟙 U) v (by rw [umap_id]; exact hv)
    rwa [res_id] at this
  obtain ⟨θ, hθ⟩ := CupSpec.ev_exists (E := E) (I := res ℤ (twZ q)) (n := 1) (thF q η) (thF_nat q η ηnat)
  have hzc : (zcomp a w h2).1 = a.1.comp w.1 h2 := rfl
  have key1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (δ 1 2 θ - ((zcomp a w h2).1 - β.1)) 1 1 (by simp) U x = 0 := by
    intro U x v hv
    rw [ev_sub, ev_sub, CupSpec.ev_δ_succ (by norm_num) θ U 0 0 1 (by simp) (by simp) x, hzc,
      ev_comp a.1 w.1 h2 1 0 1 (by simp) (by simp) U x, hw U x v hv, hβ, hγ1 U x v hv,
      ← (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).comm]
    simp only [hθ, thF_zero, thF_one', ηroot U x v hv, dv, smap_sub, smul_zero, Finset.sum_const_zero, add_zero]
    abel
  have key2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v u : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      u ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (δ 1 2 θ - ((zcomp a w h2).1 - β.1)) 2 0 (by simp) U x = 0 := by
    intro U x v u hv hu
    rw [ev_sub, ev_sub, CupSpec.ev_δ_succ (by norm_num) θ U 1 (-1) 0 (by simp) (by simp) x, hzc,
      ev_comp a.1 w.1 h2 2 (-1) 0 (by simp) (by simp) U x,
      PicSpec.sec_eq_zero (sglZ C (-1) (by omega)) (ev a.1 2 (-1) _ U x), PicSpec.sec_map_zero, hβ,
      hγ2 U x v u hv hu, Fin.sum_univ_three]
    simp only [hθ, thF_two', thF_one, PicSpec.sec_map_zero]
    have e2 : η U (x.face 2) = dv q φ U v := ηroot U _ v (by rw [face_two]; exact hv)
    have e0 : η U (x.face 0) = dv q φ U u := ηroot U _ u (by rw [face_zero]; exact hu)
    have e1 : η U (x.face 1) = dv q φ U (v * u) := ηroot U _ (v * u) (by
      rw [PicSpec.lineUnit_face, face_two, face_zero, mul_pow, hv, hu, mul_comm])
    rw [e0, e1, e2]
    have hn2 : (2 : ℤ).negOnePow = 1 := by decide
    simp only [dv, PicSpec.unitSec_mul, PicSpec.sec_map_add, smap_sub, map_add, map_sub, hn2, one_smul, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, neg_smul]
    abel
  refine (mkiff _ _).2 ⟨θ, sub_eq_zero.mp (CupSpec.ev_ext _ _ fun p s h U x => ?_)⟩
  rw [CupSpec.ev_zero]
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [ev_sub, ev_sub, CupSpec.ev_δ_zero (by norm_num) θ U 1 2 (by simp) h x, hθ, thF_zero, PicSpec.sec_map_zero, hzc,
      ev_comp a.1 w.1 h2 0 1 2 (by simp) h U x, PicSpec.sec_eq_zero (sglZ C 1 (by omega)) (ev a.1 0 1 _ U x),
      PicSpec.sec_map_zero, hβ, hγ0, map_zero]
    simp
  | 1 =>
    obtain rfl : s = 1 := by omega
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 (isUnit_of_sx hE x) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_
    rw [CupSpec.ev_res]
    exact key1 V (x.res g) v (by rw [PicSpec.lineUnit_res]; exact hv)
  | 2 =>
    obtain rfl : s = 0 := by omega
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 (isUnit_of_sx hE x) (lineUnit L (x.sub 0 1 (by omega))))
      fun V g ⟨v, hv⟩ => ?_
    rw [CupSpec.ev_res]
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.2 (isUnit_of_sx hE (x.res g)) (lineUnit L ((x.res g).sub 1 1 (by omega))))
      fun V' g' ⟨u, hu⟩ => ?_
    rw [CupSpec.ev_res]
    refine key2 V' ((x.res g).res g') (Units.map g'.appTop.hom.toMonoidHom v) u ?_ ?_
    · rw [CupSpec.sub_res, CupSpec.sub_res, PicSpec.lineUnit_res, PicSpec.lineUnit_res, ← hv, map_pow]
    · rw [CupSpec.sub_res, PicSpec.lineUnit_res]; exact hu
  | p + 3 =>
    exact PicSpec.sec_eq_zero (PicSpec.res_isZero _ s (by omega)) _

end GlobalTheory.EtC.KumPic.Cobd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRoots
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section
namespace GlobalTheory.EtC.KumPic.DvGlue

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (h : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem dv_res (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ)
    (hq : IsUnit (q : Γ(U, ⊤))) :
    Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => map_sub _ a b]
  rw [PicSpec.sec_map_res, PicSpec.unitSec_res, SemiMap.nat, (kumT_spec q).1 V U g v hq]

theorem glue : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  intro q _ φ hdv U b hq
  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom b
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq b
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res ℤ (twZ q)).X 0) V :=
    fun V g hg => dv q φ V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hqV : IsUnit (q : Γ(V, ⊤)) := isUnit_natCast_appTop g q hq
    have hqW : IsUnit (q : Γ(W, ⊤)) := isUnit_natCast_appTop k q hqV
    change Sec.res k (dv q φ V hg.choose) = dv q φ W (S.downward_closed hg k).choose
    rw [dv_res q φ k hg.choose hqV]
    refine hdv W hqW _ _ ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  refine ⟨a, fun V g v hv => ?_⟩
  have hg : S.arrows g := ⟨v, hv⟩
  rw [ha V g hg]
  exact hdv V (isUnit_natCast_appTop g q hq) _ _ (hg.choose_spec.trans hv.symm)

end GlobalTheory.EtC.KumPic.DvGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDifferenceMulRootOfUnity
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem unitSec_mul_kd {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U)) (ULift.up (Additive.ofMul v))

theorem unitSec_res_kd {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := congrArg (fun f => f.hom (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact this.symm

theorem Sec.res_map_kd {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => f.hom x) (φ.hom.naturality g.op)
  exact this.symm

theorem Sec.map_add_kd {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem Sec.res_sub_kd {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

theorem Prim.pow_eq_one_kd {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

def kumDiff (q : ℕ) (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (U : Scheme.{0})
    (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

theorem kumDiff_res (q : ℕ) (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v : (Γ(U, ⊤))ˣ) :
    Sec.res g (kumDiff q φ U v) = kumDiff q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold kumDiff
  rw [Sec.res_sub_kd, Sec.res_map_kd, unitSec_res_kd, (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).nat g 0,
    (kumT_spec q).1 V U g v hq]

theorem kumDiff_mul_root (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u)
    (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    (hφ : κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
    {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (z w : (Γ(V, ⊤))ˣ) (hz : (z : Γ(V, ⊤)) = ζ.1) :
    kumDiff q φ V (z * w) = kumDiff q φ V w := by
  unfold kumDiff
  have h1 : Sec.map φ (unitSec z) =
      Sec.map (resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
        (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from twGen 1 ζ) := by
    rw [← hκ V ζ z hz, ← hφ]; rfl
  have h2 := (kumT_spec q).2 V ζ w (z * w) (by rw [Units.val_mul, hz])
  have h3 := restrMap_spec (Int.castRingHom (ZMod q)) (tw q 1) V (twGen 1 ζ)
  rw [unitSec_mul_kd, Sec.map_add_kd, h2, map_add, h1]
  unfold resGen
  rw [h3]
  abel

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem kumDiff_pow_root (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u)
    (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0)
    (hφ : κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)))
    {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (z : (Γ(V, ⊤))ˣ) (hz : (z : Γ(V, ⊤)) = ζ.1) (a : ℕ) (w : (Γ(V, ⊤))ˣ) :
    kumDiff q φ V (z ^ a * w) = kumDiff q φ V w := by
  induction a with
  | zero => rw [pow_zero, one_mul]
  | succ a ih => rw [pow_succ', mul_assoc, kumDiff_mul_root q κ hκ φ hφ ζ z _ hz, ih]

theorem kumDiff_mul_rootOfUnity : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := by
  intro q _ κ hκ φ hφ U hq v ω hω
  change kumDiff q φ U (ω * v) = kumDiff q φ U v
  obtain ⟨S, hS, hP⟩ := GlobalTheory.T.rootOfUnity_etaleLocally_pow_primitiveRoot q U hq ω hω
  refine Sheaf.isSeparated _ U S hS _ _ ?_
  intro V g hg
  obtain ⟨ζ, a, ha⟩ := hP V g hg
  change Sec.res g _ = Sec.res g _
  rw [kumDiff_res q φ g hq, kumDiff_res q φ g hq, map_mul]
  have hz := Units.val_ofPowEqOne ζ.1 q ζ.pow_eq_one_kd (NeZero.ne q)
  have e : Units.map g.appTop.hom.toMonoidHom ω = Units.ofPowEqOne ζ.1 q ζ.pow_eq_one_kd (NeZero.ne q) ^ a :=
    Units.ext (by rw [ha, Units.val_pow_eq_pow_val, hz])
  rw [e]
  exact kumDiff_pow_root q κ hκ φ hφ ζ _ hz a _

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt
section
noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def extMat (b : Fin r → Fin s) (c : Fin s) :
    Matrix {i // b i = c} {i // b i = c} K →* Matrix (Fin r) (Fin r) K where
  toFun g := Matrix.reindex (Equiv.sumCompl fun a => b a = c) (Equiv.sumCompl fun a => b a = c)
    (Matrix.fromBlocks g 0 0 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem extMat_in (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K)
    (i j : {i // b i = c}) : extMat b c g i.1 j.1 = g i j := by
  simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) i.2,
    Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) j.2]

theorem extMat_out (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) : extMat b c g i j = (1 : Matrix (Fin r) (Fin r) K) i j := by
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · exact absurd ⟨hi, hj⟩ h
  · have : i ≠ j := fun e => hj (e ▸ hi)
    simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, this]
  · have : i ≠ j := fun e => hi (e ▸ hj)
    simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hj, this]
  · simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, Matrix.one_apply]

def blockExt (b : Fin r → Fin s) (c : Fin s) :
    GL {i // b i = c} K →* blockTri (κ := K) (natBlocks b) :=
  (Units.map (extMat b c)).codRestrict (blockTri (κ := K) (natBlocks b)) fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show extMat b c _ i j = 0
    have hne : b i ≠ b j := fun e => by
      simp only [natBlocks, e] at hij
      exact lt_irrefl _ hij
    rw [extMat_out b c _ i j (fun e => hne (e.1.trans e.2.symm)),
      Matrix.one_apply_ne (fun e => hne (congrArg b e))]

theorem blockExt_in (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : {i // b i = c}) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i.1 j.1 =
      (g : Matrix _ _ K) i j :=
  extMat_in b c _ i j

theorem blockExt_out (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j =
      (1 : Matrix (Fin r) (Fin r) K) i j :=
  extMat_out b c _ i j h

theorem levi_blockExt_same (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) :
    levi K b c (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = g := by
  apply Units.ext
  ext x y
  exact blockExt_in b c g x y

theorem levi_blockExt_ne (b : Fin r → Fin s) {c c' : Fin s} (h : c' ≠ c) (g : GL {i // b i = c} K) :
    levi K b c' (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = 1 := by
  apply Units.ext
  ext x y
  have := blockExt_out b c g x.1 y.1 (fun e => h (x.2.symm.trans e.1))
  show (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 =
    (1 : Matrix _ _ K) x y
  rw [this]
  simp [Matrix.one_apply, Subtype.ext_iff]

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem leviTensor_blockExt (c : Fin s) (g : GL {i // b i = c} K) :
    leviTensor b lam (blockExt b c g) = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ g)) := by
  rw [leviTensor_apply]
  congr 1
  funext c'
  by_cases h : c' = c
  · subst h
    rw [levi_blockExt_same, Function.update_self]
  · rw [levi_blockExt_ne b h, Function.update_of_ne h, map_one]
    rfl

end GlobalTheory.HcIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem ofForm_injective_of_H0Const (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hF : CohomZeroIsConstants F) : Function.Injective (ofForm F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 hω
  have h0 : d0 F g = 0 := by
    funext T T' φ
    have e : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
    rw [e, ← hg φ, sub_self]; rfl
  obtain ⟨r, hr, -⟩ := hF g h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  rw [← hD T, hr T]
  exact (D R (F.obj T)).map_algebraMap r

end GlobalTheory.AbCoh
end


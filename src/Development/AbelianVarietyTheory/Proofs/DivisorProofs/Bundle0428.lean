import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0090

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBaseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  first | (exact @GlobalTheory.EtC.GmStep.cechDiag_spec) | (exact GlobalTheory.EtC.GmStep.cechDiag_spec) | (intros; apply GlobalTheory.EtC.GmStep.cechDiag_spec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.PsiModel
variable {R : Type} [CommRing R]

theorem map_sres {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sx.map f (Sx.res g x) = Sx.res g (Sx.map f x) := by
  unfold Sx.map Sx.res
  exact NatTrans.naturality_apply (f.app (op (SimplexCategory.mk p))) g.op x

theorem map_face {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    Sx.map f (Sx.face x i) = Sx.face (Sx.map f x) i := by
  unfold Sx.map Sx.face
  have h1 := NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)
  simp only [NatTrans.comp_app] at h1
  have h2 := ConcreteCategory.congr_hom h1 x
  simp only [ConcreteCategory.comp_apply] at h2
  exact h2

theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map f' (Sx.map f x) = Sx.map (f ≫ f') x := rfl

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp [Sec.res]

theorem ev_smul {E : Spc} {I : Cx R} {n : ℤ} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (r • α) p s h U x = r • ev α p s h U x := by
  rw [ev_def, ev_def, Cochain.smul_v, Linear.comp_smul]
  rfl

variable {q N : ℕ}

def fstH {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) p V) : V ⟶ U :=
  Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y

theorem fstH_res {U V' V : Scheme.{0}} {p : ℕ} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    fstH (Sx.res g y) = g ≫ fstH y := by
  unfold fstH
  rw [map_sres]
  rfl

theorem fstH_face {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) (p + 1) V) (i : Fin (p + 2)) :
    fstH (Sx.face y i) = fstH y := by
  unfold fstH
  rw [map_face]
  rfl

theorem fstH_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    fstH (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = fstH y ≫ g := by
  unfold fstH
  rw [map_map, prod.map_fst]
  rfl

theorem snd_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    Sx.map (prod.snd : sch.obj U ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y := by
  rw [map_map, prod.map_snd, Category.comp_id]

variable {I₁ I₂ K : Cx R} (μ : Pair I₁ I₂ K) {n : ℤ} (z : Cochain ((chains R).obj (fibQ q N)) I₂ n)

def pval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : Sec (K.X s) V :=
  μ.mul V m (-(p : ℤ) + n) s (by omega) (Sec.res (fstH y) a) (ev z p (-(p : ℤ) + n) rfl V (Sx.map prod.snd y))

theorem pval_res {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    {V' V : Scheme.{0}} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    Sec.res g (pval μ z hw a p s hs V y) = pval μ z hw a p s hs V' (y.res g) := by
  unfold pval
  rw [μ.nat, res_res, ev_res, map_sres, fstH_res]

def cval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) K w :=
  (ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose

theorem cval_ev {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : ev (cval μ z hw a) p s hs V y = pval μ z hw a p s hs V y :=
  (ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose_spec p s hs V y

theorem cval_add {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a b : Sec (I₁.X m) U) :
    cval μ z hw (a + b) = cval μ z hw a + cval μ z hw b := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_add, cval_ev, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (a + b) = Sec.res (fstH y) a + Sec.res (fstH y) b from map_add _ _ _, LinearMap.map_add₂]

theorem cval_smul {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (r : ULift.{1} R) (a : Sec (I₁.X m) U) :
    cval μ z hw (r • a) = r • cval μ z hw a := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_smul, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (r • a) = r • Sec.res (fstH y) a from map_smul _ _ _, LinearMap.map_smul₂]

theorem cval_nat {U U' : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (g : U' ⟶ U) (a : Sec (I₁.X m) U) :
    cval μ z hw (Sec.res g a) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (cval μ z hw a) (zero_add w) := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_pull, cval_ev, cval_ev]
  unfold pval
  rw [fstH_map, snd_map, res_res]

def pmor {m w : ℤ} (hw : m + n = w) : (I₁.X m).obj ⟶ cotPre R q N K w where
  app U := ModuleCat.ofHom
    { toFun := fun a => cval μ z hw (U := U.unop) a
      map_add' := cval_add μ z hw
      map_smul' := cval_smul μ z hw }
  naturality U U' f := by
    ext a : 2
    exact cval_nat μ z hw f.unop a

def smor {m w : ℤ} (hw : m + n = w) : I₁.X m ⟶ (Jcx R q N K).X w :=
  ObjectProperty.homMk (pmor μ z hw ≫ toSheafify Scheme.etaleTopology.{0} (cotPre R q N K w))

def psiC : Cochain I₁ (Jcx R q N K) n := Cochain.mk fun m w hw => smor μ z hw

theorem psiC_v {m w : ℤ} (hw : m + n = w) : (psiC μ z).v m w hw = smor μ z hw := Cochain.mk_v _ _ _ _

theorem Jcx_d (w : ℤ) : (Jcx R q N K).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N K w) := by
  simp [Jcx]

theorem mul_d_congr {V : Scheme.{0}} {m T t1 t2 w : ℤ} (e : t1 = t2) (h1 : m + t1 = w) (h2 : m + t2 = w)
    (A : Sec (I₁.X m) V) (B : Sec (I₂.X T) V) :
    μ.mul V m t1 w h1 A (Sec.map (I₂.d T t1) B) = μ.mul V m t2 w h2 A (Sec.map (I₂.d T t2) B) := by
  subst e
  rfl

theorem cval_δ (hn : Even n) (hz : δ n (n + 1) z = 0) {U : Scheme.{0}} {m w w' : ℤ} (hw : m + n = w)
    (hw' : m + 1 + n = w') (a : Sec (I₁.X m) U) :
    δ w w' (cval μ z hw a) = cval μ z hw' (Sec.map (I₁.d m (m + 1)) a) := by
  have hww : w + 1 = w' := by omega
  refine ev_ext _ _ fun k t ht V y => ?_
  rcases k with _ | k
  · rw [ev_δ_zero hww _ V w t (by simp) ht y, cval_ev, cval_ev]
    unfold pval
    obtain rfl : t = w + 1 := by simp at ht; omega
    rw [μ.leibniz]
    have hz0 : Sec.map (I₂.d (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + n + 1))
        (ev z 0 (-((0 : ℕ) : ℤ) + n) rfl V (Sx.map prod.snd y)) = 0 := by
      rw [← ev_δ_zero (n := n) (m := n + 1) rfl z V _ _ rfl (by omega), hz, ev_zero]
    rw [hz0, map_zero, smul_zero, add_zero, map_res]
  · rw [ev_δ_succ hww _ V k (-((k + 1 : ℕ) : ℤ) + w) t rfl ht y, cval_ev]
    obtain rfl : t = -((k + 1 : ℕ) : ℤ) + w + 1 := by omega
    have e2 : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ev (cval μ z hw a) k (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega) V (y.face i) =
        ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • μ.mul V m (-(k : ℤ) + n) (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega)
          (Sec.res (fstH y) a) (ev z k (-(k : ℤ) + n) rfl V ((Sx.map prod.snd y).face i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cval_ev]
      unfold pval
      rw [fstH_face, map_face]
    rw [e2, cval_ev]
    unfold pval
    rw [μ.leibniz, mul_d_congr μ (t2 := -(k : ℤ) + n) (by push_cast; omega) _ (by push_cast; omega)]
    have hzS := ev_δ_succ (n := n) (m := n + 1) rfl z V k (-((k + 1 : ℕ) : ℤ) + n) (-(k : ℤ) + n) rfl (by push_cast; omega)
      (Sx.map prod.snd y)
    rw [hz, ev_zero, Int.negOnePow_succ, Int.negOnePow_even n hn, Units.neg_smul, one_smul, eq_comm,
      add_neg_eq_zero] at hzS
    rw [hzS, map_sum, ← map_res]
    have hs : w'.negOnePow = -m.negOnePow := by
      rw [← hw', Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_even n hn, mul_one]
    simp only [map_zsmul]
    rw [hs, Units.neg_smul]
    exact add_neg_cancel_right _ _

theorem psiC_δ (hn : Even n) (hz : δ n (n + 1) z = 0) : δ n (n + 1) (psiC μ z) = 0 := by
  refine Cochain.ext _ _ fun p q' hpq => ?_
  obtain ⟨w, rfl⟩ : ∃ w, q' = w + 1 := ⟨q' - 1, by omega⟩
  rw [δ_v n (n + 1) rfl _ p (w + 1) hpq w (p + 1) (by omega) rfl, psiC_v, psiC_v, Jcx_d, Int.negOnePow_succ,
    Int.negOnePow_even n hn, Cochain.zero_v, Units.neg_smul, one_smul, add_neg_eq_zero]
  apply Sheaf.hom_ext
  change pmor μ z _ ≫ toSheafify _ _ ≫ sheafifyMap _ (cotD R q N K w) =
    (I₁.d p (p + 1)).hom ≫ pmor μ z _ ≫ toSheafify _ _
  rw [← toSheafify_naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact cval_δ μ z hn hz _ _ a

end GlobalTheory.EtC.PsiModel

namespace GlobalTheory.EtC.PsiModel

theorem psi_exists : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  intro q N i₁ i₂ i h d z
  subst h
  refine ⟨Cocycle.mk (psiC (twPair q i₁ i₂) z.1) (2 * (d : ℤ) + 1) rfl
    (psiC_δ _ _ (even_two_mul _) (z.δ_eq_zero _)), fun m w hw U a => ⟨cval (twPair q i₁ i₂) z.1 hw a, ?_, fun k s hs V y => ?_⟩⟩
  · change Sec.map ((psiC (twPair q i₁ i₂) z.1).v m w hw) a = _
    rw [psiC_v]
    rfl
  · rw [cval_ev]
    rfl

end GlobalTheory.EtC.PsiModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic

def liftSec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec C U :=
  Function.surjInv (hb U (hE U ⟨x.face 0⟩)).2 (unitSec (lineUnit L x))

theorem liftSec_spec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec.map qb (liftSec qb L hE hb U x) = unitSec (lineUnit L x) :=
  Function.surjInv_eq _ _

theorem liftSec_res {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    Sec.res g (liftSec qb L hE hb U x) = liftSec qb L hE hb V (x.res g) := by
  apply (hb V (hE V ⟨(x.res g).face 0⟩)).1
  rw [← CupSpec.map_res, liftSec_spec, liftSec_spec, PicSpec.unitSec_res, PicSpec.lineUnit_res]

theorem liftSec_face {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 2 U) :
    liftSec qb L hE hb U (x.face 1) = liftSec qb L hE hb U (x.face 0) + liftSec qb L hE hb U (x.face 2) := by
  apply (hb U (hE U ⟨(x.face 0).face 0⟩)).1
  rw [PicSpec.sec_map_add, liftSec_spec, liftSec_spec, liftSec_spec, PicSpec.lineUnit_face, PicSpec.unitSec_mul]

def liftFam {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((sgl C).X s) U
  | 1, s, h, U, x => Sec.map ((sgl C).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (sglι C) (liftSec qb L hE hb U x))
  | _, _, _, _, _ => 0

theorem liftFam_nat {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (liftFam qb L hE hb p s h U x) = liftFam qb L hE hb p s h V (x.res g) := by
  match p with
  | 0 => exact map_zero _
  | 1 =>
    simp only [liftFam]
    rw [CupSpec.map_res, CupSpec.map_res, liftSec_res]
  | p + 2 => exact map_zero _

end GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic

theorem liftFam_one {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) :
    liftFam qb L hE hb 1 0 h U x = Sec.map (sglι C) (liftSec qb L hE hb U x) := by
  simp [liftFam, Sec.map]

theorem liftFam_cocycle {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (α : Cochain ((chains ℤ).obj E) (sgl C) 1)
    (hα : ∀ p s h U x, ev α p s h U x = liftFam qb L hE hb p s h U x) : δ 1 2 α = 0 := by
  apply CupSpec.ev_ext
  intro p t ht U x
  rw [CupSpec.ev_zero]
  by_cases h0 : t = 0
  · subst h0
    obtain rfl : p = 2 := by omega
    rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
    simp only [hα]
    rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl, PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
    simp only [liftFam_one]
    rw [liftSec_face, PicSpec.sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _

theorem lift_cocycle : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  refine ⟨Cocycle.mk α 2 (by norm_num) (liftFam_cocycle qb L hE hb α hα), fun U x => ⟨liftSec qb L hE hb U x,
    liftSec_spec qb L hE hb U x, ?_⟩⟩
  refine (hα 1 0 _ U x).trans ?_
  exact liftFam_one qb L hE hb _ U x

end GlobalTheory.EtC.KumPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalkStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  first | (exact @GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk) | (exact GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk) | (intros; apply GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexPointNormLtOfNotIsUnit
section
open Polynomial Filter Topology

namespace GlobalTheory

namespace SmallPoint

theorem exists_extend_of_ker_le {R B Ω : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) (h : RingHom.ker (algebraMap R B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* Ω, ψ.comp (algebraMap R B) = φ := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker φ) ⊥ h
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω := IsAlgClosed.lift
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)

theorem exists_extend_apply_eq {R B Ω : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) (u : B) (t : Ω)
    (ht : (minpoly R u).eval₂ ψ t = 0) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap R B) = ψ ∧ φ u = t := by
  letI : Algebra R[X] B := (aeval u : R[X] →ₐ[R] B).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] B :=
    IsScalarTower.of_algebraMap_eq fun x => ((aeval u : R[X] →ₐ[R] B).commutes x).symm
  haveI : Algebra.IsIntegral R[X] B := Algebra.IsIntegral.tower_top (R := R)
  obtain ⟨φ, hφ⟩ := exists_extend_of_ker_le (B := B) (eval₂RingHom ψ t) (fun f hf => by
    obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd
      (Algebra.IsIntegral.isIntegral (R := R) u) (p := f) hf
    rw [RingHom.mem_ker, map_mul, coe_eval₂RingHom, ht, zero_mul])
  have h : ∀ f : R[X], φ (aeval u f) = f.eval₂ ψ t := fun f => DFunLike.congr_fun hφ f
  refine ⟨φ, RingHom.ext fun r => ?_, ?_⟩
  · simpa using h (C r)
  · simpa using h X

theorem exists_root_norm_lt {F : ℂ[X]} (hF : F.Monic) {ε : ℝ} (hε : 0 < ε)
    (h : ‖F.coeff 0‖ < ε ^ F.natDegree) : ∃ t, F.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt ..)

theorem exists_eventually_norm_le {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (Ψ : R →+* ℂ[X]) {b : B} (hb : IsIntegral R b) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ φ : B →+* ℂ,
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ → ‖φ b‖ ≤ M := by
  obtain ⟨G, hG, hGb⟩ := hb
  have h1 : ∀ i : ℕ, ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ (G.coeff i)).eval s‖ < ‖(Ψ (G.coeff i)).eval 0‖ + 1 := fun i =>
    ((Ψ (G.coeff i)).continuous.norm.tendsto 0).eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖ + 1) + 1, ?_⟩
  filter_upwards [(Finset.range G.natDegree).eventually_all.2 fun i _ => h1 i] with s hs φ hφ
  have hm : (G.map ((evalRingHom s).comp Ψ)).Monic := hG.map _
  have hr : (G.map ((evalRingHom s).comp Ψ)).IsRoot (φ b) := by
    rw [IsRoot, eval_map, ← hφ, ← hom_eval₂, hGb, map_zero]
  have h2 := hr.norm_lt_cauchyBound hm.ne_zero
  rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hG.natDegree_map] at h2
  have h3 : ((Finset.range G.natDegree).sup
      (fun i => ‖(G.map ((evalRingHom s).comp Ψ)).coeff i‖₊) : NNReal) ≤
      ∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖₊ + 1) := by
    refine Finset.sup_le fun i hi => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ‖(Ψ (G.coeff i)).eval 0‖₊ + 1) (fun _ _ => zero_le) hi)
    rw [coeff_map]
    exact_mod_cast (hs i hi).le
  have h4 := h2.le.trans (add_le_add_left h3 1)
  have h5 := NNReal.coe_le_coe.2 h4
  push_cast at h5
  exact h5

theorem exists_small_of_curve {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    (Ψ : R →+* ℂ[X]) (p : B →+* ℂ) (hp : p.comp (algebraMap R B) = (evalRingHom 0).comp Ψ)
    {n : ℕ} (w : Fin n → B) {u : B} (hu : p u = 0) {r : R} (hr : Ψ r ≠ 0) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ (s : ℂ) (φ : B →+* ℂ),
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ ∧ (Ψ r).eval s ≠ 0 ∧ ‖φ u‖ < ε ∧
        ∀ i, ‖φ (w i)‖ ≤ M := by
  choose M hM using fun i => exists_eventually_norm_le Ψ
    (Algebra.IsIntegral.isIntegral (R := R) (w i))
  refine ⟨∑ i, |M i|, fun ε hε => ?_⟩
  have hint := Algebra.IsIntegral.isIntegral (R := R) u
  have hF := minpoly.monic hint
  have h0 : (Ψ ((minpoly R u).coeff 0)).eval 0 = 0 := by
    have h := congrArg p (minpoly.aeval R u)
    rw [aeval_def, hom_eval₂, hu, eval₂_at_zero, hp, map_zero] at h
    exact h
  have h1 : ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ ((minpoly R u).coeff 0)).eval s‖ < ε ^ (minpoly R u).natDegree :=
    ((Ψ _).continuous.norm.tendsto 0).eventually (gt_mem_nhds (by
      simp only [h0, norm_zero]
      positivity))
  have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ¬ (Ψ r).IsRoot s :=
    nhdsNE_le_cofinite _ (eventually_cofinite.2 (by
      simpa using (Ψ r).finite_setOf_isRoot hr))
  obtain ⟨s, hs2, hs1, hs3⟩ := (h2.and
    ((h1.and (eventually_all.2 hM)).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨t, ht, htε⟩ := exists_root_norm_lt (hF.map ((evalRingHom s).comp Ψ)) hε (by
    rw [coeff_map, hF.natDegree_map]
    exact hs1)
  obtain ⟨φ, hφ, hφu⟩ := exists_extend_apply_eq ((evalRingHom s).comp Ψ) u t (by
    rwa [IsRoot, eval_map] at ht)
  refine ⟨s, φ, hφ, hs2, hφu ▸ htε, fun i => (hs3 i φ hφ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end SmallPoint

theorem exists_complex_point_norm_lt_of_not_isUnit :
    ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
      (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 →
      ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧
        ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  intro K B _ _ _ _ _ σ n w u q hu hq
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) B := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Nontrivial (B ⧸ Ideal.span {u}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨p₀, hp₀⟩ := exists_ringHom_extend_of_finiteType K (B ⧸ Ideal.span {u}) ℂ σ
  let p : B →+* ℂ := p₀.comp (Ideal.Quotient.mk _)
  have hpu : p u = 0 := by
    change p₀ (Ideal.Quotient.mk _ u) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self u), map_zero]
  obtain ⟨r, hr, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) K) q).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hq)
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, MvPolynomial.eval z (MvPolynomial.map σ r) ≠ 0 := by
    by_contra! h
    exact hr (MvPolynomial.map_injective σ σ.injective
      (MvPolynomial.funext (by simpa using h)))
  let Ψ : MvPolynomial (Fin d) K →+* ℂ[X] := MvPolynomial.eval₂Hom (C.comp σ)
    fun j => C (p (g (MvPolynomial.X j))) + X * C (z j - p (g (MvPolynomial.X j)))
  have hΨ0 : p.comp (algebraMap (MvPolynomial (Fin d) K) B) = (evalRingHom 0).comp Ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · have : p (g (MvPolynomial.C a)) = σ a := by
        rw [MvPolynomial.algHom_C]
        exact hp₀ a
      exact this.trans (by simp [Ψ])
    · simp [Ψ]
      rfl
  have hΨ1 : (evalRingHom 1).comp Ψ = (MvPolynomial.eval z).comp (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_) <;> simp [Ψ]
  have hΨr : Ψ r ≠ 0 := fun h => hz (by
    have := DFunLike.congr_fun hΨ1 r
    simpa [h] using this.symm)
  obtain ⟨M, hM⟩ := SmallPoint.exists_small_of_curve Ψ p hΨ0 w hpu hΨr
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨s, φ, hφ, h1, h2, h3⟩ := hM ε hε
  refine ⟨φ, RingHom.ext fun a => ?_, fun h => h1 ?_, h2, h3⟩
  · have := DFunLike.congr_fun hφ (MvPolynomial.C a)
    rw [RingHom.comp_apply, ← MvPolynomial.algHom_C g]
    exact this.trans (by simp [Ψ])
  · have := DFunLike.congr_fun hφ r
    rw [RingHom.comp_apply, hc, map_mul, h, zero_mul] at this
    exact this.symm

end GlobalTheory
end


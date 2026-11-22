import Development.EtaleCohomology.KummerTheory.Bundle0005
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
import Development.EtaleCohomology.KummerTheory.Bundle0008
import Development.EtaleCohomology.KummerTheory.Bundle0006

-- bundled from Development.EtaleCohomology.KummerTheory.AdicLimPfKer
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

universe u

namespace LateralTheory.KummerTheory.KerPf

theorem seqSec (S : ℕ → Type u) [∀ a, Finite (S a)] [∀ a, Nonempty (S a)] (t : ∀ a, S (a + 1) → S a) :
    ∃ s : ∀ a, S a, ∀ a, t a (s (a + 1)) = s a :=
  _root_.UpperTheory.Reformulated.B.DYra4.main S t

variable (l : ℕ) [Fact l.Prime]

theorem redk (hA : A11) (E : Spc) (n i : ℤ) (x : Hl l E n i) (m : ℕ) :
    ∀ a : ℕ, red (l ^ (m + a)) (l ^ m) E n i (x.1 (m + a)) = x.1 m := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  intro a
  induction a with
  | zero => exact (@hA (l ^ m) (l ^ m) _ dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    have h := (@hA (l ^ (m + (a + 1))) (l ^ (m + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (x.1 (m + (a + 1)))
    rw [← h, ← ih]
    exact congrArg _ (x.2 (m + a))

omit [Fact l.Prime] in
theorem smul_zero_of (E : Spc) (n i : ℤ) (k b : ℕ) (hkb : k ≤ b) (z : Ht (l ^ k) E n i) : (l ^ b) • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ k)), (CharP.cast_eq_zero_iff (ZMod (l ^ k)) (l ^ k) _).2 (pow_dvd_pow l hkb), zero_smul]

theorem ker (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) (b : ℕ) (x : Hl l E n i) (hx : lev l x b = 0) :
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ b) • y := by
  obtain ⟨u, d, h⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin a n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).1 (x.1 (b + a))).1 (by rw [redk l hA E n i x b a]; exact hx)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (h a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  obtain ⟨s, hs⟩ := seqSec S t
  let y : Hl l E n i := ⟨fun a => (s a).1, fun a => congrArg Subtype.val (hs a)⟩
  refine ⟨y, ?_⟩
  have e : ((l : ℤ_[l]) ^ b) • y = (l ^ b : ℕ) • y := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]; push_cast; rfl
  rw [e]
  apply Subtype.ext
  funext k
  change x.1 k = (l ^ b) • (s k).1
  rcases le_or_gt b k with hk | hk
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hr := redk l hA E n i y a b
    rw [Nat.add_comm a b] at hr
    rw [← (h a n).2.2.2.1 ((s (b + a)).1)]
    change x.1 (b + a) = u a n (red _ _ E n i (y.1 (b + a)))
    rw [hr]
    exact (s a).2.symm
  · rw [smul_zero_of l E n i k b hk.le]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    rw [← redk l hA E n i x k c]
    change red _ _ E n i (lev l x (k + c)) = 0
    rw [hx, map_zero]

end LateralTheory.KummerTheory.KerPf

namespace LateralTheory.KummerTheory

theorem AdicKer_holds : AdicKer := fun hA l _ E i hB hFin n k x hx => KerPf.ker l hA E i hB hFin n k x hx

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.CokAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem bcMap_comp' {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (g' : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = g') :
    bcMap p g g' h' e' ≫ bcMap p f g h e = bcMap p f g' (h ≫ h') (by rw [← Category.assoc, e, e']) := by
  apply pullback.hom_ext <;>
    simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.comp_id, Spec.map_comp]

theorem bcMap_eq {X : Scheme.{0}} {R A B : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B)
    (h h' : A ⟶ B) (e : f ≫ h = g) (hh : h = h') : bcMap p f g h e = bcMap p f g h' (hh ▸ e) := by
  subst hh; rfl

theorem CokAff_of (hS : StrictHenselization) (hC : Cont) (hL : LhNat) : CokAff := by
  classical
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso B s b x
  obtain ⟨J, _, _, D, cc, hcc, u, hSH, hu⟩ := hS B b
  have hun : ∀ {j k : J} (f : j ⟶ k), u.app j ≫ D.map f = u.app k := by
    intro j k f
    have := u.naturality f
    simpa using this.symm
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  let w : B ⟶ cc.pt := u.app j0 ≫ cc.ι.app j0
  have hw : ∀ j, u.app j ≫ cc.ι.app j = w := by
    intro j
    show _ = u.app j0 ≫ cc.ι.app j0
    rw [← cc.w (IsFiltered.leftToMax j j0), ← cc.w (IsFiltered.rightToMax j j0), ← Category.assoc,
      ← Category.assoc, hun, hun]
  let v : R ⟶ cc.pt := s ≫ w
  obtain ⟨y, hy⟩ := (hiso cc.pt v hSH).2 (pull _ (sch.map (bcMap p s v w rfl)) _ _ x)
  have hqc : IsUnit ((q : ℕ) : cc.pt) := by simpa using hq.map v.hom
  have hB := fun n' i' => (hb1 q D cc hcc n' i').1
  choose jj z hz using fun (a : Fin (M + 1)) (t : Fin (r a)) => hB _ _ (y a t) hqc
  obtain ⟨k0, hk0⟩ := IsFiltered.sup_objs_exists
    (Finset.univ.image (fun pr : (Σ a : Fin (M + 1), Fin (r a)) => jj pr.1 pr.2))
  have fk : ∀ a t, jj a t ⟶ k0 := fun a t => (hk0 (Finset.mem_image.2 ⟨⟨a, t⟩, Finset.mem_univ _, rfl⟩)).some
  let y0 : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj (Spec (D.obj k0))) (n - ((a : ℕ) : ℤ)) 0 :=
    fun a t => pull _ (sch.map (Spec.map (D.map (fk a t)))) _ _ (z a t)
  have hy0 : ∀ a t, pull _ (sch.map (Spec.map (cc.ι.app k0))) _ _ (y0 a t) = y a t := by
    intro a t
    rw [← hz a t]
    simp only [y0]
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, cc.w]
    rfl
  let g : Over.mk (Spec.map v) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
    Over.homMk (Spec.map (cc.ι.app k0)) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, Category.assoc, hw])
  have hrst : rst p g = bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]) := rfl
  have h0 := hL h6 q p i r c M n g y0
  rw [hrst] at h0
  have hyy : (fun a t => pull _ (sch.map g.left) _ _ (y0 a t)) = y := by
    funext a t; exact hy0 a t
  rw [hyy] at h0
  let e := lh q p (Spec.map (s ≫ u.app k0)) i r c M n y0 -
    N • pull _ (sch.map (bcMap p s (s ≫ u.app k0) (u.app k0) rfl)) _ _ x
  have he : pull _ (sch.map (bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]))) _ _ e = 0 := by
    simp only [e, map_sub, map_nsmul]
    erw [h0, hy, ← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hw k0)]
    exact sub_self _
  have hC2 := (hC h2 hb1 q p hq D cc hcc (fun j => s ≫ u.app j)
    (fun {j k} f => by simp only [Category.assoc, hun]) v (fun j => by simp only [v, Category.assoc, hw]) n i).2 k0 e he
  obtain ⟨k1, f1, hk1⟩ := hC2
  obtain ⟨het, 𝔮, h𝔮⟩ := hu k1
  refine ⟨D.obj k1, u.app k1, het, ⟨(by exact 𝔮 : Spec (D.obj k1)), ?_⟩, fun a t => pull _ (sch.map (Spec.map (D.map f1))) _ _ (y0 a t), ?_⟩
  · exact (PrimeSpectrum.ext h𝔮 : PrimeSpectrum.comap (u.app k1).hom 𝔮 = b)
  · let g' : Over.mk (Spec.map (s ≫ u.app k1)) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
      Over.homMk (Spec.map (D.map f1)) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, Category.assoc, hun])
    have h1 := hL h6 q p i r c M n g' y0
    have hrst' : rst p g' = bcMap p (s ≫ u.app k0) (s ≫ u.app k1) (D.map f1) (by rw [Category.assoc, hun]) := rfl
    rw [hrst'] at h1
    beta_reduce at hk1
    simp only [e, map_sub, map_nsmul, sub_eq_zero] at hk1
    erw [h1] at hk1
    refine hk1.trans ?_
    erw [← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hun f1)]

end LateralTheory.KummerTheory.LHCut
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.DictNormalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def NrmMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (a p s h U x) = a p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def NrmDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (_hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
  (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
  ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
    m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U ((E.δ i).app (op U) x)

def up {X U : Scheme.{0}} {p q : ℕ} (x : Sx (sch.obj X) p U) : Sx (sch.obj X) q U := x

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) :
    ((sch.obj X).δ i).app (op U) x = up x := rfl

theorem altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h2, this, hk.neg_one_pow]

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]

theorem ev_sub' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of (hM : NrmMk) (hD : NrmDelta) : DictNormal := by
  intro R _ I X n α
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  obtain ⟨β, hβ⟩ := hM R (E := sch.obj X) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      dsimp only
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))
      · exact map_zero _)
  let γ : Cocycle ((chains R).obj (sch.obj X)) I n :=
    ⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩
  refine ⟨α - γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff γ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p s h U y
    show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0
    rw [ev_sub', sub_eq_zero]
    rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
    simp only [face_sch, hβ]
    rcases Nat.even_or_odd p with hp | hp
    ·
      have hp1 : Odd (p + 1) := hp.add_one
      have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
      simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
      have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
        (by push_cast at h ⊢; omega) (up y)
      rw [hα, ev_zero'] at hc
      simp only [face_sch] at hc
      rw [← Finset.sum_smul, altsum] at hc
      have he : ¬ Even (p + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
      simp only [he, if_false, one_smul] at hc
      rw [Int.negOnePow_succ, Units.neg_smul] at hc
      have key := add_neg_eq_zero.1 hc.symm
      rw [Units.smul_def]
      refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
      rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
          = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
      rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      rfl
    · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
      simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
      rw [← Finset.sum_smul, altsum]
      have he : ¬ Even (p + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
      simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
      rfl

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem chains_d (R : Type) [CommRing R] (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  simp only [chainsN, Functor.comp_obj]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

def evAt {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := (φ.hom.app (op U)).hom y
  map_zero' := by simp
  map_add' := by simp

theorem evAt_apply {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) (φ : F ⟶ G) :
    evAt U y φ = (φ.hom.app (op U)).hom y := rfl

theorem nrmDelta : NrmDelta := by
  intro R _ E I n m hm α U p s t hs ht x
  unfold ev
  rw [δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
    chains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp [Units.smul_def, Finset.smul_sum]
  refine (map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 2
  have := free_gen_map R (E.δ i) U x
  rw [evAt_apply]
  simp
  exact congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U)))
    ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of' (hM : NrmMk) : DictNormal := DictNormal_of hM nrmDelta
end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.EtaleLerayHirschConeSourceComponentVanishesAfter
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem lcv_cls_of_d {R : Type} [CommRing R] (hD : Dict) {I : Cx R} {X : Scheme.{0}} (n n' : ℤ) (h : n + 1 = n')
    (a : Sec (I.X n) X) (ha : Sec.map (I.d n n') a = 0) : ∃ x, IsCls x a := by
  subst h; exact (hD R I X n).1 a ha

theorem lcv_d_of_cls {R : Type} [CommRing R] (hD : Dict) {I : Cx R} {X : Scheme.{0}} {n : ℤ} (n' : ℤ) (h : n + 1 = n')
    x (a : Sec (I.X n) X) (ha : IsCls x a) : Sec.map (I.d n n') a = 0 := by
  subst h; exact ((hD R I X n).2.2.1 x a ha).1

section
variable {Λ : Type} [CommRing Λ] {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ}
  (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem lcv_cD_fst (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).1 = dS (j + 1) (j' + 1) x.1 := rfl

theorem lcv_cD_snd (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).2 = Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2 := rfl

theorem lcv_cres_fst {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) :
    (cres g x).1 = fun a s => Sec.res g.left (x.1 a s) := rfl

theorem lcv_cres_snd {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) :
    (cres g x).2 = Sec.res (rst p g) x.2 := rfl
end

theorem lcv_step1 (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ : ℤ) (hK : KerLoc q p i r c M N (j₀ + 1 + 1)) (U : Over S)
    (x1 : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1 + 1) U.left) (k : Sec ((res _ (tw q i)).X (j₀ + 1)) (pullback p U.hom))
    (hx1 : dS (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) x1 = 0)
    (hx2 : Phi (mu q i) p γ (j₀ + 1 + 1) (j₀ + 1 + 1) rfl U x1 = Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) k)
    (u : U.left) : ∃ (V1 : Over S) (g1 : V1 ⟶ U), Nbhd g1 u ∧ ∃ b : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1) V1.left,
      dS (j₀ + 1) (j₀ + 1 + 1) b = fun a s => N • Sec.res g1.left (x1 a s) := by
  have hCM := clsMore_of hD
  have hb : ∀ (a : Fin (M + 1)) (s : Fin (r a)),
      Sec.map ((res _ (tw q 0)).d (j₀ + 1 + 1 - ((a : ℕ) : ℤ)) (j₀ + 1 + 1 + 1 - ((a : ℕ) : ℤ))) (x1 a s) = 0 := by
    intro a s
    have h0 := congrFun (congrFun hx1 a) s
    have := congrArg (fun v => ((a : ℕ) : ℤ).negOnePow • v) h0
    simpa only [dS, Pi.zero_apply, smul_smul, Int.units_mul_self, one_smul, smul_zero] using this
  choose y hy using fun a s => lcv_cls_of_d hD _ _ (by omega) _ (hb a s)
  have hl := hL q p i r c γ hc M (j₀ + 1 + 1) U y x1 hy
  have hly : lh q p U.hom i r c M (j₀ + 1 + 1) y = 0 :=
    ((hCM _ _ _ _).2.2.2 (j₀ + 1) rfl _ 0 _ 0 hl (hCM _ _ _ _).1).2 ⟨k, by rw [sub_zero]; exact hx2.symm⟩
  obtain ⟨V1, g1, hg1, hk1⟩ := hK U u y hly
  have hcl1 : ∀ (a : Fin (M + 1)) (s : Fin (r a)),
      IsCls (N • pull _ (sch.map g1.left) _ _ (y a s)) (N • Sec.res g1.left (x1 a s)) :=
    fun a s => (hCM _ _ _ _).2.1 N _ _ ((hD _ _ _ _).2.2.2.2 g1.left _ _ (hy a s))
  choose b1 hb1 using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    ((hCM _ _ _ _).2.2.2 (j₀ + 1 - ((a : ℕ) : ℤ)) (by omega) _ 0 _ 0 (hcl1 a s) (hCM _ _ _ _).1).1 (hk1 a s)
  refine ⟨V1, g1, hg1, fun a s => ((a : ℕ) : ℤ).negOnePow • b1 a s, ?_⟩
  funext a s
  simp only [dS, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact (hb1 a s).trans (sub_zero _)

theorem lcv_step2 (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ : ℤ) (hC : CokLoc q p i r c M N (j₀ + 1)) (V1 : Over S) (v1 : V1.left)
    (k : Sec ((res _ (tw q i)).X (j₀ + 1)) (pullback p V1.hom))
    (hk : Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) k = 0) :
    ∃ (V2 : Over S) (g2 : V2 ⟶ V1), Nbhd g2 v1 ∧ ∃ (b2 : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1) V2.left)
      (k' : Sec ((res _ (tw q i)).X j₀) (pullback p V2.hom)), dS (j₀ + 1) (j₀ + 1 + 1) b2 = 0 ∧
      Phi (mu q i) p γ (j₀ + 1) (j₀ + 1) rfl V2 b2 - Sec.map ((res _ (tw q i)).d j₀ (j₀ + 1)) k' =
        N • Sec.res (rst p g2) k := by
  have hCM := clsMore_of hD
  obtain ⟨κ, hκ⟩ := (hD _ _ _ _).1 k hk
  obtain ⟨V2, g2, hg2, y2, hy2⟩ := hC V1 v1 κ
  choose b2 hb2 using fun (a : Fin (M + 1)) (s : Fin (r a)) => (hD _ _ _ _).2.1 (y2 a s)
  have hl2 := hL q p i r c γ hc M (j₀ + 1) V2 y2 b2 hb2
  have hcl2 : IsCls (N • pull _ (sch.map (rst p g2)) _ _ κ) (N • Sec.res (rst p g2) k) :=
    (hCM _ _ _ _).2.1 N _ _ ((hD _ _ _ _).2.2.2.2 (rst p g2) _ _ hκ)
  obtain ⟨k', hk'⟩ := ((hCM _ _ _ _).2.2.2 j₀ rfl _ _ _ _ hl2 hcl2).1 hy2
  refine ⟨V2, g2, hg2, b2, k', ?_, ?_⟩
  · funext a s
    simp only [dS, Pi.zero_apply]
    rw [lcv_d_of_cls hD _ (by omega) _ _ (hb2 a s), smul_zero]
  · rw [hk', sub_sub_cancel]

section
variable {Λ : Type} [CommRing Λ] {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ}
  (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem etale_leray_hirsch_cone_comparison_map_degree_cast (n w : ℤ) (h : n = w) (U : Over S) : Phi (J := J) (M := M) μ p γ n w h U 0 = 0 := by
  simp [Phi]

theorem etale_leray_hirsch_cone_source_component_vanishes_after_correction (j₀ : ℤ) {U V1 : Over S} (g1 : V1 ⟶ U) (x : Cone J K p r M (j₀ + 1) U) (N : ℕ)
    (b1 : FinalTheorems J r M (j₀ + 1) V1.left) (hb1 : dS (j₀ + 1) (j₀ + 1 + 1) b1 = fun a s => N • Sec.res g1.left (x.1 a s)) :
    (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 (b1, 0)).1 = 0 := by
  rw [Prod.fst_sub, Prod.smul_fst, lcv_cres_fst, lcv_cD_fst, hb1]
  funext a s
  simp only [Pi.sub_apply, Pi.smul_apply, sub_self, Pi.zero_apply]

theorem etale_leray_hirsch_cone_cycle_with_zero_source_has_closed_complex_part (j₀ : ℤ) {V1 : Over S} (z : Cone J K p r M (j₀ + 1) V1) (hz1 : z.1 = 0)
    (hzc : cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl V1 z = 0) : Sec.map (K.d (j₀ + 1) (j₀ + 1 + 1)) z.2 = 0 := by
  have := congrArg Prod.snd hzc
  rw [lcv_cD_snd, hz1, etale_leray_hirsch_cone_comparison_map_degree_cast, zero_sub, Prod.snd_zero, neg_eq_zero] at this
  exact this

theorem lcv_bk (j₀ : ℤ) {V1 V2 : Over S} (g2 : V2 ⟶ V1) (z : Cone J K p r M (j₀ + 1) V1) (hz1 : z.1 = 0) (N : ℕ)
    (b2 : FinalTheorems J r M (j₀ + 1) V2.left) (k' : Sec (K.X j₀) (pullback p V2.hom)) (hdb2 : dS (j₀ + 1) (j₀ + 1 + 1) b2 = 0)
    (hk' : Phi μ p γ (j₀ + 1) (j₀ + 1) rfl V2 b2 - Sec.map (K.d j₀ (j₀ + 1)) k' = N • Sec.res (rst p g2) z.2) :
    cD μ p γ j₀ (j₀ + 1) rfl V2 (b2, k') = N • cres g2 z := by
  refine Prod.ext ?_ ?_
  · rw [lcv_cD_fst, Prod.smul_fst, lcv_cres_fst, hz1]
    exact hdb2.trans (by funext a s; simp)
  · rw [lcv_cD_snd, Prod.smul_snd, lcv_cres_snd]
    exact hk'

theorem lcv_nbhd {U V1 V2 : Over S} (g1 : V1 ⟶ U) (g2 : V2 ⟶ V1) (u : U.left) (hg1 : Nbhd g1 u) (v1 : V1.left)
    (hv1 : g1.left v1 = u) (hg2 : Nbhd g2 v1) : Nbhd (g2 ≫ g1) u := by
  refine ⟨?_, ?_⟩
  · have := hg1.1; have := hg2.1
    rw [Over.comp_left]; infer_instance
  · obtain ⟨v2, hv2⟩ := hg2.2
    exact ⟨v2, by simp [hv2, hv1]⟩

theorem lcv_alg (hA : ConeAlg) (hγ : Closed γ) (j₀ : ℤ) {U V1 V2 : Over S} (g1 : V1 ⟶ U) (g2 : V2 ⟶ V1)
    (x : Cone J K p r M (j₀ + 1) U) (N : ℕ)
    (w0 : Cone J K p r M j₀ V1) (y2 : Cone J K p r M j₀ V2)
    (hy2 : cD μ p γ j₀ (j₀ + 1) rfl V2 y2 = N • cres g2 (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 w0)) :
    cD μ p γ j₀ (j₀ + 1) rfl V2 (N • cres g2 w0 + y2) = N ^ 2 • cres (g2 ≫ g1) x := by
  obtain ⟨-, -, nat1⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V1
  obtain ⟨-, -, nat2⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl V1
  obtain ⟨-, -, natU⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl U
  obtain ⟨linV2, -, -⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V2
  have e1 := (map_add (IsLinearMap.mk' _ linV2) (N • cres g2 w0) y2).trans
    (congrArg (· + _) (map_nsmul (IsLinearMap.mk' _ linV2) N (cres g2 w0)))
  simp only [IsLinearMap.mk'_apply] at e1
  have e2 := map_sub (IsLinearMap.mk' _ (nat2 V2 g2).1) (N • cres g1 x) (cD μ p γ j₀ (j₀ + 1) rfl V1 w0)
  have e3 := map_nsmul (IsLinearMap.mk' _ (nat2 V2 g2).1) N (cres g1 x)
  simp only [IsLinearMap.mk'_apply] at e2 e3
  rw [e1, hy2, e2, e3, (nat1 V2 g2).2.1 w0, smul_sub, add_sub_cancel, smul_smul, ← pow_two,
    (natU V1 g1).2.2 V2 g2 x]

theorem lcv_zc (hA : ConeAlg) (hγ : Closed γ) (j₀ : ℤ) {U V1 : Over S} (g1 : V1 ⟶ U)
    (x : Cone J K p r M (j₀ + 1) U) (hx : cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x = 0) (N : ℕ)
    (w0 : Cone J K p r M j₀ V1) :
    cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl V1 (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 w0) = 0 := by
  obtain ⟨-, sq1, -⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V1
  obtain ⟨lin2, -, -⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl V1
  obtain ⟨-, -, natU⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl U
  have c0 : cres g1 (0 : Cone J K p r M (j₀ + 1 + 1) U) = 0 :=
    map_zero (IsLinearMap.mk' _ ((hA _ μ p r M γ hγ (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) rfl U).2.2 V1 g1).1)
  have e := (map_sub (IsLinearMap.mk' _ lin2) (N • cres g1 x) (cD μ p γ j₀ (j₀ + 1) rfl V1 w0)).trans
    (congrArg (· - _) (map_nsmul (IsLinearMap.mk' _ lin2) N (cres g1 x)))
  simp only [IsLinearMap.mk'_apply] at e
  rw [e, sq1 _ rfl w0, ← (natU V1 g1).2.1 x, hx, c0, smul_zero, sub_zero]
end

theorem etale_leray_hirsch_cone_cycle_locally_bounded_boundary (hD : Dict) (hL : LhSec) (hA : ConeAlg) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ j : ℤ) (h : j₀ + 1 = j) (hK : KerLoc q p i r c M N (j + 1)) (hC : CokLoc q p i r c M N j)
    (U : Over S) (x : Cone (res _ (tw q 0)) (res _ (tw q i)) p r M j U)
    (hx : cD (mu q i) p γ j (j + 1) rfl U x = 0) (u : U.left) :
    ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧
      ∃ y : Cone (res _ (tw q 0)) (res _ (tw q i)) p r M j₀ V, cD (mu q i) p γ j₀ j h V y = N ^ 2 • cres g x := by
  subst h
  have hγ : Closed γ := fun a s => ((hD _ _ X _).2.2.1 _ _ (hc a s)).1
  have hx1 : dS (J := res _ (tw q 0)) (r := r) (M := M) (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) x.1 = 0 :=
    ((lcv_cD_fst (mu q i) p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x).symm.trans (congrArg Prod.fst hx)).trans Prod.fst_zero
  have hx2 : Phi (mu q i) p γ (j₀ + 1 + 1) (j₀ + 1 + 1) rfl U x.1 =
      Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) x.2 :=
    sub_eq_zero.1 (((lcv_cD_snd (mu q i) p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x).symm.trans (congrArg Prod.snd hx)).trans
      Prod.snd_zero)
  obtain ⟨V1, g1, hg1, b1, hb1⟩ := lcv_step1 hD hL q p i r c γ hc M N j₀ hK U x.1 x.2 hx1 hx2 u
  have hz1 := etale_leray_hirsch_cone_source_component_vanishes_after_correction (mu q i) p γ j₀ g1 x N b1 hb1
  have hzc := lcv_zc (mu q i) p γ hA hγ j₀ g1 x hx N (b1, 0)
  have hz2 := etale_leray_hirsch_cone_cycle_with_zero_source_has_closed_complex_part (mu q i) p γ j₀ _ hz1 hzc
  obtain ⟨v1, hv1⟩ := hg1.2
  obtain ⟨V2, g2, hg2, b2, k', hdb2, hk'⟩ := lcv_step2 hD hL q p i r c γ hc M N j₀ hC V1 v1 _ hz2
  exact ⟨V2, g2 ≫ g1, lcv_nbhd g1 g2 u hg1 v1 hv1 hg2, N • cres g2 (b1, 0) + (b2, k'),
    lcv_alg (mu q i) p γ hA hγ j₀ g1 g2 x N (b1, 0) (b2, k') (lcv_bk (mu q i) p γ j₀ g2 _ hz1 N b2 k' hdb2 hk')⟩

theorem locCone_of (hD : Dict) (hL : LhSec) (hA : ConeAlg) : LocCone := by
  intro q X S p i r c γ hc M N j hK hC U x hx u
  exact etale_leray_hirsch_cone_cycle_locally_bounded_boundary hD hL hA q p i r c γ hc M N (j - 1) j (by omega) hK hC U x hx u
end LateralTheory.KummerTheory.LHCut
end
end


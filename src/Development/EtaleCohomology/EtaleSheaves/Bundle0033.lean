import Development.EtaleCohomology.EtaleSheaves.Bundle0020
import Development.EtaleCohomology.EtaleSheaves.Bundle0018
import Development.EtaleCohomology.EtaleSheaves.Bundle0019
import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono

-- bundled from Development.EtaleCohomology.EtaleSheaves.ColimHensPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.ColimHensPf

variable {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
  (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) {c : Cocone D}

lemma beta_nat {j j' : J} (f : j ⟶ j') (b : B) : (D.map f).hom ((β.app j).hom b) = (β.app j').hom b := by
  have h := congrArg (fun g => g.hom b) (β.naturality f)
  simpa using h.symm

lemma iota_nat (c : Cocone D) {j j' : J} (f : j ⟶ j') (x : D.obj j) :
    (c.ι.app j').hom ((D.map f).hom x) = (c.ι.app j).hom x := by
  have h := congrArg (fun g => g.hom x) (c.w f)
  simpa using h

lemma mapI (I : Ideal B) {j j' : J} (f : j ⟶ j') {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (D.map f).hom x ∈ I.map (β.app j').hom := by
  have h : (D.map f).hom.comp (β.app j).hom = (β.app j').hom := RingHom.ext (beta_nat β f)
  have := Ideal.mem_map_of_mem (D.map f).hom hx
  rwa [Ideal.map_map, h] at this

def phi (c : Cocone D) : B →+* c.pt :=
  (c.ι.app (IsFiltered.nonempty (C := J)).some).hom.comp (β.app (IsFiltered.nonempty (C := J)).some).hom

lemma phi_eq (c : Cocone D) (j : J) (b : B) : (c.ι.app j).hom ((β.app j).hom b) = phi β c b := by
  let j0 := (IsFiltered.nonempty (C := J)).some
  show _ = (c.ι.app j0).hom ((β.app j0).hom b)
  rw [← iota_nat c (IsFiltered.leftToMax j j0), ← iota_nat c (IsFiltered.rightToMax j j0), beta_nat, beta_nat]

lemma KofI (c : Cocone D) (I : Ideal B) {j : J} {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (c.ι.app j).hom x ∈ I.map (phi β c) := by
  have h : (c.ι.app j).hom.comp (β.app j).hom = phi β c := RingHom.ext (phi_eq β c j)
  have := Ideal.mem_map_of_mem (c.ι.app j).hom hx
  rwa [Ideal.map_map, h] at this

variable (hc : IsColimit c)
include hc

lemma rep (z : c.pt) : ∃ j, ∃ y : D.obj j, (c.ι.app j).hom y = z :=
  Concrete.isColimit_exists_rep D hc z

lemma rep_above (j : J) (z : c.pt) : ∃ (j' : J) (_ : j ⟶ j') (y : D.obj j'), (c.ι.app j').hom y = z := by
  obtain ⟨j1, y, rfl⟩ := rep hc z
  exact ⟨IsFiltered.max j j1, IsFiltered.leftToMax j j1, (D.map (IsFiltered.rightToMax j j1)).hom y, iota_nat c _ y⟩

lemma eq_later {j : J} (x y : D.obj j) (h : (c.ι.app j).hom x = (c.ι.app j).hom y) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = (D.map f).hom y := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x y h
  refine ⟨_, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom x = (D.map g).hom y := hfg
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom x
        = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom x) := by simp
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom y) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom y := by simp
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom y := by rw [IsFiltered.coeq_condition]

lemma zero_later {j : J} (x : D.obj j) (h : (c.ι.app j).hom x = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = 0 := by
  obtain ⟨j', f, hf⟩ := eq_later hc x 0 (by rw [h, map_zero])
  exact ⟨j', f, by rw [hf, map_zero]⟩

lemma Krep (I : Ideal B) {k : c.pt} (hk : k ∈ I.map (phi β c)) :
    ∃ j, ∃ x : D.obj j, x ∈ I.map (β.app j).hom ∧ (c.ι.app j).hom x = k := by
  have hk' : k ∈ Ideal.span (phi β c '' I) := hk
  clear hk
  induction hk' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨(IsFiltered.nonempty (C := J)).some, _, Ideal.mem_map_of_mem _ hi, phi_eq β c _ i⟩
  | zero => exact ⟨(IsFiltered.nonempty (C := J)).some, 0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨j1, x1, h1, rfl⟩ := hx
    obtain ⟨j2, x2, h2, rfl⟩ := hy
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom x1 +
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, add_mem (mapI β I _ h1) (mapI β I _ h2), ?_⟩
    rw [map_add, iota_nat, iota_nat]
  | smul a x _ hx =>
    obtain ⟨j2, x2, h2, rfl⟩ := hx
    obtain ⟨j1, y, rfl⟩ := rep hc a
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom y *
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, Ideal.mul_mem_left _ _ (mapI β I _ h2), ?_⟩
    rw [map_mul, iota_nat, iota_nat, smul_eq_mul]

lemma memK_descend (I : Ideal B) {j : J} (y : D.obj j) (hy : (c.ι.app j).hom y ∈ I.map (phi β c)) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom y ∈ I.map (β.app j').hom := by
  obtain ⟨j1, x, hx, hxe⟩ := Krep β hc I hy
  let l := IsFiltered.leftToMax j j1
  let r := IsFiltered.rightToMax j j1
  obtain ⟨j', g, hg⟩ := zero_later hc ((D.map l).hom y - (D.map r).hom x)
    (by rw [map_sub, iota_nat, iota_nat, hxe, sub_self])
  refine ⟨j', l ≫ g, ?_⟩
  rw [map_sub, sub_eq_zero] at hg
  have : (D.map (l ≫ g)).hom y = (D.map (r ≫ g)).hom x := by simpa using hg
  rw [this]
  exact mapI β I _ hx

lemma poly_lift (g : Polynomial c.pt) : ∃ j, g ∈ Polynomial.lifts (c.ι.app j).hom := by
  have mono : ∀ {j j' : J} (f : j ⟶ j') (g : Polynomial c.pt),
      g ∈ Polynomial.lifts (c.ι.app j).hom → g ∈ Polynomial.lifts (c.ι.app j').hom := by
    intro j j' f g ⟨q, hq⟩
    refine ⟨q.map (D.map f).hom, ?_⟩
    have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
    simp only [Polynomial.coe_mapRingHom] at hq ⊢
    rw [Polynomial.map_map, h, hq]
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, h1⟩ := hp
    obtain ⟨j2, h2⟩ := hq
    exact ⟨_, add_mem (mono (IsFiltered.leftToMax j1 j2) _ h1)
      (mono (IsFiltered.rightToMax j1 j2) _ h2)⟩
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := rep hc a
    exact ⟨j, Polynomial.monomial_mem_lifts n ⟨y, hy⟩⟩

omit hc in
lemma ev_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R) (b : R) :
    φ (p.eval b) = (p.map φ).eval (φ b) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

omit hc in
lemma pmap (c : Cocone D) {j j' : J} (f : j ⟶ j') (p : Polynomial (D.obj j)) :
    (p.map (D.map f).hom).map (c.ι.app j').hom = p.map (c.ι.app j).hom := by
  have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
  rw [Polynomial.map_map, h]

end LateralTheory.E.ColimHensPf

namespace LateralTheory.E.ColimHensPf
open LateralTheory.E.ColimHensPf

theorem ColimHens_of : LateralTheory.E.HensCut.ColimHens := by
  intro B _ I J _ _ D β c hc ha hb hcc
  refine ⟨I.map (phi β c), ⟨?_, ?_⟩, ⟨RingEquiv.ofBijective
    (Ideal.quotientMap (I.map (phi β c)) (phi β c) Ideal.le_comap_map) ⟨?_, ?_⟩⟩⟩
  ·
    intro k hk
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I (Ideal.mul_mem_right y _ hk)
    obtain ⟨j', f, hu⟩ := hb j x hx
    have := hu.map (c.ι.app j').hom
    rw [iota_nat, map_add, map_one, hxe, add_comm] at this
    exact this
  ·
    intro g hg a₀ hev hder
    by_cases hnt : Nontrivial c.pt
    swap
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact ⟨a₀, Subsingleton.elim _ _, by rw [sub_self]; exact zero_mem _⟩
    obtain ⟨j1, hj1⟩ := poly_lift hc g
    haveI : Nontrivial (((Functor.const J).obj c.pt).obj j1) := hnt
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic hj1 hg
    obtain ⟨w, hw⟩ := hder.exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (phi β c))), Ideal.Quotient.eq] at hw
    obtain ⟨j2, f12, b0, hb0⟩ := rep_above hc j1 a₀
    obtain ⟨j3, f23, v, hv⟩ := rep_above hc j2 u
    set p3 := p.map (D.map (f12 ≫ f23)).hom with hp3
    set b3 := (D.map f23).hom b0 with hb3
    have hp3g : p3.map (c.ι.app j3).hom = g := by rw [hp3, pmap, hp]
    have hb3a : (c.ι.app j3).hom b3 = a₀ := by rw [hb3, iota_nat, hb0]
    have hy1 : (c.ι.app j3).hom (p3.eval b3) ∈ I.map (phi β c) := by
      rw [ev_map, hp3g, hb3a]; exact hev
    have hy2 : (c.ι.app j3).hom (p3.derivative.eval b3 * v - 1) ∈ I.map (phi β c) := by
      rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map, hp3g, hb3a, hv]; exact hw
    obtain ⟨j4, f34, h4⟩ := memK_descend β hc I _ hy1
    obtain ⟨j5, f45, h5⟩ := memK_descend β hc I ((D.map f34).hom (p3.derivative.eval b3 * v - 1))
      (by rw [iota_nat]; exact hy2)
    let h := f34 ≫ f45
    set P := p3.map (D.map h).hom with hP
    set b := (D.map h).hom b3 with hb
    have hPm : P.Monic := (hpm.map _).map _
    have hPe : P.eval b ∈ I.map (β.app j5).hom := by
      rw [hP, hb, ← ev_map]
      have := mapI β I f45 h4
      simpa [h] using this
    have hPd : IsUnit (Ideal.Quotient.mk (I.map (β.app j5).hom) (P.derivative.eval b)) := by
      have e : (D.map h).hom (p3.derivative.eval b3 * v - 1) = P.derivative.eval b * (D.map h).hom v - 1 := by
        rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map]
      have h5' : P.derivative.eval b * (D.map h).hom v - 1 ∈ I.map (β.app j5).hom := by
        rw [← e]; simpa [h] using h5
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ ((D.map h).hom v)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact h5'
    obtain ⟨j6, f56, a, ha1, ha2⟩ := hcc j5 P b hPm hPe hPd
    refine ⟨(c.ι.app j6).hom a, ?_, ?_⟩
    · have hr := ha1.map (f := (c.ι.app j6).hom)
      rwa [pmap, hP, pmap, hp3g] at hr
    · have := KofI β c I ha2
      rwa [map_sub, iota_nat, hb, iota_nat, hb3a] at this
  ·
    rw [injective_iff_map_eq_zero]
    intro a ha0
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha0
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I ha0
    obtain ⟨j', f, hf⟩ := zero_later hc ((β.app j).hom b - x)
      (by rw [map_sub, hxe, phi_eq, sub_self])
    rw [map_sub, sub_eq_zero, beta_nat] at hf
    have hm : (β.app j').hom b ∈ I.map (β.app j').hom := by rw [hf]; exact mapI β I f hx
    apply (ha j').1
    rw [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  ·
    intro z
    obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨j, y, rfl⟩ := rep hc z'
    obtain ⟨w, hw⟩ := (ha j).2 (Ideal.Quotient.mk _ y)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨Ideal.Quotient.mk I b, ?_⟩
    rw [Ideal.quotientMap_mk] at hw ⊢
    rw [Ideal.Quotient.eq] at hw ⊢
    have := KofI β c I hw
    rwa [map_sub, phi_eq] at this

end LateralTheory.E.ColimHensPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmptyVan2
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.EmptyVan₂

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    Subsingleton (G.obj.obj (op X)) := by
  have h := Sheaf.isTerminalOfBotCover G X (Scheme.bot_mem_grothendieckTopology X)
  constructor
  intro a b
  have e := h.hom_ext (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ b))
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) e
  simpa using this

theorem free_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  ext U x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have := sec_subsingleton (R := R) ((free R).obj (yoneda.obj X)) U.unop
    exact @Subsingleton.elim _ this _ _
  · have : IsEmpty ((yoneda.obj X).obj U) := ⟨fun (f : U.unop ⟶ X) => IsEmpty.false (f.base (Classical.arbitrary U.unop))⟩
    have hx : x = 0 := Subsingleton.elim (α := ULift.{1} ((yoneda.obj X).obj U) →₀ ULift.{1} R) x 0
    rw [hx, map_zero, map_zero]

theorem chains_X_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (m : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X m) := by
  rcases le_or_gt m 0 with h | h
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = -(p : ℤ) := ⟨(-m).toNat, by omega⟩
    exact (free_isZero (R := R) X).of_iso (chainsXIso R _ p)
  · exact HomologicalComplex.isZero_extend_X _ _ m (fun i => by
      change -(i : ℤ) ≠ m; omega)

theorem cc_subsingleton {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ}
    (hK : ∀ m, IsZero (K.X m)) (n : ℤ) : Subsingleton (CohomologyClass K L n) := by
  have : Subsingleton (Cochain K L n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hK p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle K L n) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

theorem EmptyVan_of : LateralTheory.E.CoverPf.EmptyVan := by
  intro _ q _ i n S _ hS x
  have : IsEmpty (Spec (CommRingCat.of S)) :=
    ⟨fun p => (p : PrimeSpectrum S).isPrime.ne_top (Subsingleton.elim _ _)⟩
  have := cc_subsingleton (L := res (ZMod q) (tw q i)) (chains_X_isZero (R := ZMod q) (Spec (CommRingCat.of S))) (n + 1)
  exact Subsingleton.elim _ _

end LateralTheory.E.EmptyVan₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibStalkPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf

namespace LateralTheory.E.FibStalkPf

theorem eqv_iso {X Y : Scheme.{0}} (e : X ≅ Y) (q : ℕ) (i : ℤ) : Eqv _ (sch.map e.hom) (tw q i) := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (sch.map e.inv) (tw q i) n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_comp {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (hf : Eqv _ f F) (hg : Eqv _ g F) :
    Eqv _ (f ≫ g) F := by
  intro n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_left {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hg : Eqv _ g F) :
    Eqv _ f F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff _ (hg n)).1 h1

theorem eqv_right {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hf : Eqv _ f F) :
    Eqv _ g F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 h1

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSH : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of A)),
  AICSch S → ∀ s : (pullback p (cpt A) : Scheme.{0}), SH ((pullback p (cpt A)).presheaf.stalk s)

def FibreEqv : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.snd (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))
      (cpt ((pullback p (cpt A)).presheaf.stalk s)))) (tw q i)

theorem FibStalk_of (hS : StalkSH) (hF : FibreEqv) : FibStalk := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  have hsh : SH ((pullback p (cpt A)).presheaf.stalk s) := hS A p hSs s
  obtain ⟨_, _⟩ := id hsh
  have hu0 : IsUnit (q : Γ((pullback p (cpt A) : Scheme.{0}), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  have hu : IsUnit (q : (pullback p (cpt A)).presheaf.stalk s) := by
    simpa using hu0.map ((pullback p (cpt A)).presheaf.germ ⊤ s trivial).hom
  have hfst := hB _ hsh hu ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A))
  have hfib := hF H h0 hA q i A hq c p hZs hSs hB s
  have hE1 : Eqv _ (sch.map (cpt ((pullback p (cpt A)).presheaf.stalk s))) (tw q i) :=
    H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  have core : Eqv _ (sch.map (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))) (tw q i) := by
    refine eqv_right ?_ hfst
    rw [← Functor.map_comp, pullback.condition, Functor.map_comp]
    exact eqv_comp hfib hE1
  have sq2 : IsPullback (pullback.fst (c ≫ p) (cpt A)) (fm c p ≫ 𝟙 _) c (pullback.fst p (cpt A)) := by
    rw [Category.comp_id]; exact (fm_isPullback c p).flip
  have big := (IsPullback.of_hasPullback (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s)).paste_horiz sq2
  have hsnd : Eqv _ (sch.map (pullback.snd (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) (tw q i) := by
    rw [← big.isoPullback_hom_snd, Functor.map_comp]; exact eqv_comp (eqv_iso _ q i) core
  refine eqv_left (g := sch.map (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) ?_
    (eqv_iso (asIso (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) q i)
  rw [← Functor.map_comp]
  convert hsnd using 2
  rw [pullback.map]; erw [pullback.lift_snd]; exact Category.comp_id _

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSHS : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, SH (S.presheaf.stalk x)

def QuotSH : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R'), Function.Surjective f → SH R → SH R'

theorem StalkSH_of (hS : StalkSHS) (hQ : QuotSH) : StalkSH := by
  intro A _ _ S p hSs s
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks (pullback.fst p (cpt A)) := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  exact hQ _ _ ((pullback.fst p (cpt A)).stalkMap s).hom ((pullback.fst p (cpt A)).stalkMap_surjective s) (hS S hSs _)

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

theorem quotSH : QuotSH := by
  intro R R' _ _ _ f hf ⟨hH, hK⟩
  have hl : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hmem : ∀ x, f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hx => h (hx.map f), fun h hx => h (isUnit_of_map_unit f x hx)⟩
  refine ⟨⟨fun g hg a₀' h0 h1 => ?_⟩, ?_⟩
  · obtain ⟨G, hGm, -, hGmon⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts g).2 fun n => hf _) hg
    obtain ⟨a₀, rfl⟩ := hf a₀'
    have e0 : f (G.eval a₀) = g.eval (f a₀) := by rw [← hGm, Polynomial.eval_map, eval₂_at_apply]
    have e1 : f (G.derivative.eval a₀) = g.derivative.eval (f a₀) := by
      rw [← hGm, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian G hGmon a₀ ((hmem _).1 (e0 ▸ h0))
      (isUnit_of_map_unit f _ (e1 ▸ h1))
    refine ⟨f a, ?_, ?_⟩
    · rw [IsRoot, ← hGm, Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
    · rw [← map_sub]; exact (hmem _).2 ha'
  · have hs : Function.Surjective (ResidueField.map f) := by
      intro y
      obtain ⟨y, rfl⟩ := residue_surjective y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨residue R x, ResidueField.map_residue f x⟩
    refine IsSepClosed.of_exists_root _ fun p hpm hpi hps => ?_
    obtain ⟨P, hP, hdeg, -⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts p).2 fun n => hs _) hpm
    have hPs : P.Separable := (separable_map (ResidueField.map f)).1 (hP ▸ hps)
    have hPd : P.degree ≠ 0 := by
      have := hpi.natDegree_pos
      intro h; rw [natDegree_eq_zero_iff_degree_le_zero.2 h.le] at hdeg; omega
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root P hPd hPs
    exact ⟨ResidueField.map f x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx.eq_zero]; simp⟩

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

theorem aic_root {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : ∀ (n : ℕ) (f : R[X]), f.Monic → f.natDegree = n →
    ∀ a₀, f.eval a₀ ∈ maximalIdeal R → ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hm hd a₀ h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hm hd, eval_one] at h0
    exact absurd ((Ideal.eq_top_iff_one _).2 h0) (maximalIdeal.isMaximal R).ne_top
  | succ n ih =>
    intro f hm hd a₀ h0
    obtain ⟨b, hb⟩ := h f hm (by omega)
    have hf : (X - C b) * (f /ₘ (X - C b)) = f := by rw [mul_divByMonic_eq_iff_isRoot]; exact hb
    have hgm : (f /ₘ (X - C b)).Monic := (monic_X_sub_C b).of_mul_monic_left (by rw [hf]; exact hm)
    have hgd : (f /ₘ (X - C b)).natDegree = n := by rw [natDegree_divByMonic f (monic_X_sub_C b), natDegree_X_sub_C]; omega
    rw [← hf, eval_mul, eval_sub, eval_X, eval_C] at h0
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h0 with h1 | h2
    · exact ⟨b, hb, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨a, ha, ha'⟩ := ih _ hgm hgd a₀ h2
      exact ⟨a, by rw [IsRoot, ← hf, eval_mul, ha.eq_zero, mul_zero], ha'⟩

theorem sh_of_aic {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : SH R := by
  refine ⟨{ is_henselian := fun f hf a₀ h0 _ => aic_root h _ f hf rfl a₀ h0 }, ?_⟩
  refine IsSepClosed.of_exists_root _ fun p hpm hpi _ => ?_
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts p).2 fun n => residue_surjective _) hpm
  obtain ⟨x, hx⟩ := h P hPm (by have := hpi.natDegree_pos; omega)
  exact ⟨residue R x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx]; simp⟩

theorem stalkSHS_of (hA : StalkAIC) : StalkSHS := fun S hS x => sh_of_aic (hA S hS x)

end LateralTheory.E.FibStalkPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.HalfDegreeVanishing

theorem um_hom_val {N : ℕ} {A : Type} [CommRing A] {v w v' w' : Um N A} (hv : v = v') (hw : w = w') (p : v' ⟶ w') :
    (eqToHom hv ≫ p ≫ eqToHom hw.symm).1 = p.1 := by
  subst hv hw; simp

theorem um_functor_ext {N n : ℕ} {A : Type} [CommRing A] (F G : Fin (n + 1) ⥤ Um N A)
    (ho : ∀ i, (F.obj i).1 = (G.obj i).1) (hm : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), (F.map f).1 = (G.map f).1) : F = G := by
  refine CategoryTheory.Functor.ext (fun i => Subtype.ext (ho i)) (fun i j f => ?_)
  apply Subtype.ext
  exact (hm f).trans (um_hom_val (Subtype.ext (ho i)) (Subtype.ext (ho j)) (G.map f)).symm

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem arrow_eq {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (pe V W x)).map f).val.mulVec (wb (a := a) ((pv V W x).obj i).1) =
      (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj j).1 := by
  have e := ((pv V W x).map f).2
  rw [cond] at e
  have e2 := congrArg (wb (a := a)) e
  rw [wb_mulVec] at e2
  exact e2

def gfun {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) (hx : AllSec V W x) :
    Fin (n + 1) ⥤ Um b (Scheme.Γ.obj (op X)) where
  obj i := ⟨wb (a := a) ((pv V W x).obj i).1, hx i⟩
  map {i j} f := ⟨((pw W (pe V W x)).map f, ((pv V W x).map f).1.2), arrow_eq V W x f⟩
  map_id i := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_id i) (congrArg (fun p => p.1.2) ((pv V W x).map_id i)))
  map_comp f g := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_comp f g) (congrArg (fun p => p.1.2) ((pv V W x).map_comp f g)))

theorem pe_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) = (E.obj (op (SimplexCategory.mk n))).map k.op (pe V W x) :=
  ConcreteCategory.congr_hom (((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x

theorem pw_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (e : Sx E n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op Y)) from (pw W ((E.obj (op (SimplexCategory.mk n))).map k.op e)).map f) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map k.op).hom (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W e).map f) :=
  eq_of_heq (Functor.hcongr_hom (ConcreteCategory.congr_hom ((W.app (op (SimplexCategory.mk n))).naturality k.op) e) f)

end LateralTheory.E.HalfDegreeVanishing
end
end


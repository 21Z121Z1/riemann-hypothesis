import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Development.EtaleCohomology.EtaleSheaves.Bundle0005

-- bundled from Development.EtaleCohomology.EtaleSheaves.AICAcycPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.AICAcycPf

theorem acyc_of_iso (q : ℕ) {X Y : Scheme.{0}} (e : X ≅ Y) (h : Acyc q (sch.obj Y)) : Acyc q (sch.obj X) := by
  intro n i hn
  have := h n i hn
  constructor
  intro a b
  have key : ∀ a : Ht q (sch.obj X) n i,
      a = pull _ (sch.map e.hom) _ n (pull _ (sch.map e.inv) _ n a) := by
    intro a
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key a, key b, Subsingleton.elim (pull _ (sch.map e.inv) _ n a) (pull _ (sch.map e.inv) _ n b)]

theorem aff (hB5 : B5) (q : ℕ) (Z : Scheme.{0}) [IsAffine Z] (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) :
    Acyc q (sch.obj Z) := by
  have : IsIntegral Z := hZ.1
  have hA : AIC Γ(Z, ⊤) := hZ.2 ⊤ (isAffineOpen_top Z) ⟨Nonempty.some inferInstance, by simp⟩
  have h5 := hB5 q Γ(Z, ⊤) hA hq
  exact acyc_of_iso q Z.isoSpec h5

def Step : Prop := Hyp → MV → HZero → ∀ (q : ℕ) {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
  Acyc q (sch.obj U) → Acyc q (sch.obj V) → (Nonempty ↥(pullback f g : Scheme.{0}) → Acyc q (sch.obj (pullback f g))) → Acyc q (sch.obj X)

def Cov : Prop := ∀ (q : ℕ) (P : Scheme.{0} → Prop), (∀ {X Y : Scheme.{0}}, (X ≅ Y) → P Y → P X) →
  (∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z) →
  (∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X) →
  ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z], AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z

theorem AICAcyc_of (hZ : HZero) (hMV : MV) (hStep : Step) (hCov : Cov) : AICAcyc := by
  intro hyp q Z _ _ hZs hq
  refine hCov q (fun W => Acyc q (sch.obj W)) ?_ ?_ ?_ Z hZs hq
  · intro X Y e h
    exact acyc_of_iso q e h
  · intro W hA hW hWq
    exact aff hyp.b5 q W hW hWq
  · intro U V X f g _ _ hc hX hU hV hq' hPU hPV hPW
    exact hStep hyp hMV hZ q f g hc hX hU hV hq' hPU hPV hPW

end LateralTheory.E.AICAcycPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AICSHPf
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.AICSHPf

theorem root_near {T : Type} [CommRing T] [IsDomain T] (hA : ∀ p : Polynomial T, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0)
    (P : Ideal T) [P.IsPrime] (a₀ : T) :
    ∀ (n : ℕ) (f : T[X]), f.natDegree = n → f.Monic → f.eval a₀ ∈ P → ∃ a, f.IsRoot a ∧ a - a₀ ∈ P := by
  intro n
  induction n with
  | zero =>
    intro f hd hm hv
    have : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst this
    simp only [eval_one] at hv
    exact absurd ((Ideal.eq_top_iff_one P).2 hv) (Ideal.IsPrime.ne_top inferInstance)
  | succ n ih =>
    intro f hd hm hv
    obtain ⟨r, hr⟩ := hA f hm (by omega)
    have hroot : f.IsRoot r := hr
    set q := f /ₘ (X - C r) with hq
    have hfac : (X - C r) * q = f := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) (by rw [hfac]; exact hm)
    have hdeg : q.natDegree = n := by
      have := (monic_X_sub_C r).natDegree_mul hqm
      rw [hfac, natDegree_X_sub_C] at this; omega
    have hv' : (a₀ - r) * q.eval a₀ ∈ P := by
      rw [← hfac] at hv; simpa [eval_mul] using hv
    rcases (inferInstance : P.IsPrime).mem_or_mem hv' with h | h
    · refine ⟨r, hroot, ?_⟩
      have := P.neg_mem_iff.2 h; simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih q hdeg hqm h
      refine ⟨a, ?_, ha'⟩
      rw [← hfac]; simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₀ _ := root_near hA (IsLocalRing.maximalIdeal T) a₀ _ f rfl hf h₀

theorem algClosed {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hirr
  obtain ⟨P, hPl, hPd, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective _) hpm
  have hpos : 0 < P.natDegree := by
    rw [Polynomial.natDegree_eq_of_degree_eq hPd]; exact Irreducible.natDegree_pos hirr
  obtain ⟨a, ha⟩ := hA P hPm hpos
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hPl, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

end LateralTheory.E.AICSHPf

namespace LateralTheory.E.t_E3Cut

theorem AICSH_of : AICSH := by
  intro T _ _ _ hA
  let _ := LateralTheory.E.AICSHPf.henselian hA
  have := LateralTheory.E.AICSHPf.algClosed hA
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.E.t_E3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AcycQAPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.AcycQAPf

def MVHyp (q : ℕ) (i n : ℤ) : Prop := ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) → ∀ f g : S,
  Ideal.span {f, g} = ⊤ → ∀ c : Ht q (sp (Localization.Away (f * g))) n i,
    ∃ a b, c = pull _ (spMap (rL f g)) _ n a - pull _ (spMap (rR f g)) _ n b

def Deg0 : Prop := QAClosed → EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions → LCSplit → A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ), MVHyp q i 0

def Cover : Prop := QAClosed → MV → A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ), MVHyp q i n → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
  ∀ x : Ht q (sp S) (n + 1) i, (∀ p : PrimeSpectrum S, ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0) → x = 0

theorem step (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hC : Cover) (h1 : A1) (b1 : B1) (b2 : B2) (q : ℕ) [NeZero q] (i : ℤ) :
    ∀ k : ℕ, MVHyp q i k → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
      Subsingleton (Ht q (sp S) ((k : ℤ) + 1) i) := by
  intro k hk S _ hS hq
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine hC hQ hM h1 q i k hk S hS hq x fun p => ?_
  exact hZ b1 b2 q S (hQ S hS).1 hq _ i (by omega) x p

theorem AcycQA_of (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hH : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hL : LCSplit) (hD : Deg0) (hC : Cover) :
    AcycQA := by
  intro h1 h9 b1 b2 q _ S _ hS hq
  have key : ∀ k : ℕ, MVHyp q 0 k ∧ ∀ (i : ℤ), MVHyp q i k := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hD hQ hH hL h9 q 0, fun i => by simpa using hD hQ hH hL h9 q i⟩
    | succ k ih =>
      have hv : ∀ (i : ℤ), MVHyp q i ((k + 1 : ℕ) : ℤ) := by
        intro i S' _ hS' hq' f g _ c
        have hfg : QA (Localization.Away (f * g)) := (hQ S' hS').2.1 (f * g)
        have hqfg : IsUnit (q : Localization.Away (f * g)) := by
          simpa using hq'.map (algebraMap S' (Localization.Away (f * g)))
        have hs := step hQ hZ hM hC h1 b1 b2 q i k (ih.2 i) _ hfg hqfg
        refine ⟨0, 0, ?_⟩
        have : c = 0 := by
          have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
          revert c; rw [e]; intro c; exact Subsingleton.elim _ _
        simp [this]
      exact ⟨hv 0, hv⟩
  intro n i hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  exact step hQ hZ hM hC h1 b1 b2 q i k ((key k).2 i) S hS hq

end LateralTheory.E.AcycQAPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.AlgResPropsPf
open LateralTheory.E.t_E3Cut

theorem cancel {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : AlgRes (f ≫ g)) : AlgRes g := by
  intro Q hQ c
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := h Q hQ c
  refine ⟨p.map f.hom, ⟨n, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map]; simpa using hn
  · rw [Polynomial.eval₂_map]; simpa using hp

theorem integral {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.IsIntegral) : AlgRes f := by
  intro Q hQ c
  obtain ⟨p, hm, hp⟩ := h c
  refine ⟨p, ⟨p.natDegree, ?_⟩, ?_⟩
  · rw [← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
    exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  · rw [hp]; exact Q.zero_mem

theorem loc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] :
    AlgRes (CommRingCat.ofHom (algebraMap A B)) := by
  intro Q hQ c
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
  refine ⟨Polynomial.C (s : A) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
  · have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    intro hm
    apply hQ.ne_top
    apply Q.eq_top_of_isUnit_mem hm
    simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hu
  · have := IsLocalization.mk'_spec B a s
    simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_comm, this, sub_self]; exact Q.zero_mem

def Comp : Prop :=
  ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)

def Push : Prop :=
  ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v

def EtAlg : Prop := ∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f

theorem AlgResProps_of (h1 : Comp) (h2 : Push) (h3 : EtAlg) : LateralTheory.E.t_E3Cut.AlgResProps :=
  ⟨fun f g hf hg => h1 f g hf hg, fun f g h => cancel f g h, fun f g u v h hf => h2 f g u v h hf,
    fun f h => h3 f h, fun f h => integral f h, fun A B _ _ _ S _ => loc A B S⟩

end LateralTheory.E.AlgResPropsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BasePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.BasePf

theorem polyPO {A C : CommRingCat.{0}} (f : A ⟶ C) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC C) := by
  algebraize [f.hom, Polynomial.mapRingHom f.hom]
  exact (CommRingCat.isPushout_of_isPushout A C (Polynomial A) (Polynomial C)).flip

theorem et_map {A C : CommRingCat.{0}} (f : A ⟶ C) (hf : Et f) :
    Et (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty RingHom.Etale).of_isPushout (polyPO f) hf

theorem Base_of (h : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial) : LateralTheory.E.t_E3Cut.Base := by
  intro H q _ i T _ _ _ hT hq B c hc Y' w φ' hpo
  rw [Category.id_comp] at hpo
  have hc4 : C4 := H.2.2.2.2.2.2.2.2.2.2
  have hqB : IsUnit (q : B) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqB.map φ'.hom
  have sq := hpo.flip.paste_horiz (polyPO φ')
  have e1 : c ≫ pC B = pC (CommRingCat.of T) ≫ CommRingCat.ofHom (Polynomial.mapRingHom c.hom) := by
    ext x; simp
  rw [e1] at sq
  have hIE : IE (CommRingCat.ofHom (Polynomial.mapRingHom c.hom)) :=
    MorphismProperty.le_ind _ _ (et_map c hc)
  have r2 : RE q i (CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom)) :=
    h H q i T (FractionRing T) hT hq _ _ hIE _ _ _ sq.flip
  have r1 : RE q i (pC B) := hc4 q B hqB i
  have r3 : RE q i (pC Y') := hc4 q Y' hqY i
  have e2 : pC B ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom) = φ' ≫ pC Y' := by
    ext x; simp
  have r4 : RE q i (φ' ≫ pC Y') := e2 ▸ r1.comp r2
  exact RE.of_comp_right r3 r4

end LateralTheory.E.BasePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechLevel
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.SSPf

def kbc {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S) : pullback (k ≫ t) c ⟶ pullback t c :=
  pullback.map (k ≫ t) c t c k (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem kbc_fst {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S) :
    pullback.fst (k ≫ t) c ≫ k = kbc k t c ≫ pullback.fst t c := by
  unfold kbc pullback.map
  rw [pullback.lift_fst]

def cechBC {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S) : cech (kbc k t c) ⟶ cech k :=
  Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk (yoneda.map (kbc k t c))) (g := Arrow.mk (yoneda.map k))
    (yoneda.map (pullback.fst (k ≫ t) c)) (yoneda.map (pullback.fst t c))
    (by simp only [Arrow.mk_hom, ← Functor.map_comp, kbc_fst]))

def CechCmp : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S),
  IsIntegralHom k → Surjective k → IsUnit (q : Γ(S, ⊤)) → ∀ n : ℤ,
  Subsingleton (Hrel _ (cechBC k t c) (tw q i) n) → Subsingleton (Hrel _ (sch.map (pullback.fst t c)) (tw q i) n)

def CechFilt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (n : ℤ),
  (∀ p : ℕ, Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p))) → Subsingleton (Hrel R g F n)

def CechLevel : Prop := ∀ {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S), IsIntegralHom k →
  ∀ (p : ℕ) (R : Type) [CommRing R] (F : Shv R) (m : ℤ),
  (p = 0 → Subsingleton (Hrel R (sch.map (pullback.fst (k ≫ t) c)) F m)) →
  (0 < p → ∀ (W : Scheme.{0}) (w : W ⟶ X), IsIntegralHom w → Subsingleton (Hrel R (sch.map (pullback.fst (w ≫ t) c)) F m)) →
  Subsingleton (Hrel R (disc.map ((cechBC k t c).app (op (SimplexCategory.mk p)))) F m)

def SS : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {Y X S S₀ : Scheme.{0}} (k : Y ⟶ X) (t : X ⟶ S) (c : S₀ ⟶ S),
  IsIntegralHom k → Surjective k → IsUnit (q : Γ(S, ⊤)) → ∀ n : ℤ,
  (∀ m, Subsingleton (Hrel _ (sch.map (pullback.fst (k ≫ t) c)) (tw q i) m)) →
  (∀ (W : Scheme.{0}) (w : W ⟶ X), IsIntegralHom w → ∀ m < n,
    Subsingleton (Hrel _ (sch.map (pullback.fst (w ≫ t) c)) (tw q i) m)) →
  Subsingleton (Hrel _ (sch.map (pullback.fst t c)) (tw q i) n)

end LateralTheory.E.SSPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechLevels
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf
open PrimeSpectrum

theorem qm_comp {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map φ)).comp φ := Ideal.quotientMap_comp_mk _

theorem qm_integral {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).IsIntegral := by
  apply RingHom.IsIntegral.tower_top (Ideal.Quotient.mk I)
  rw [qm_comp]
  exact RingHom.IsIntegral.trans _ _ h (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)

theorem qm_surj {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    Function.Surjective (PrimeSpectrum.comap (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  intro P
  obtain ⟨Q, hQ⟩ := hs (PrimeSpectrum.comap (Ideal.Quotient.mk I) P)
  have hmem : Q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map φ))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    show I.map φ ≤ Q.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have : x ∈ (PrimeSpectrum.comap φ Q).asIdeal := by
      rw [hQ]; show Ideal.Quotient.mk I x ∈ P.asIdeal; rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact zero_mem _
    exact this
  obtain ⟨Q', rfl⟩ := hmem
  refine ⟨Q', comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
  rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, qm_comp]

theorem spec_surj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hs : Function.Surjective (PrimeSpectrum.comap f)) : Surjective (Spec.map (CommRingCat.ofHom f)) := by
  rw [surjective_iff]; exact hs

theorem part1 {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) :=
  ⟨IsIntegralHom.SpecMap_iff.2 h, spec_surj _ hs, IsIntegralHom.SpecMap_iff.2 (qm_integral φ I h),
    spec_surj _ (qm_surj φ I hs)⟩

end LateralTheory.E.CechLevelsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChowCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowCut

def Img : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → IsIntegral Z → ∃ (X₁ : Scheme.{0}) (h₁ : Z ⟶ X₁) (p₁ : X₁ ⟶ Spec (CommRingCat.of A)),
    IsIntegral X₁ ∧ IsProper p₁ ∧ IsIntegralHom h₁ ∧ IsDominant h₁ ∧ h₁ ≫ p₁ = h ≫ p

def ChowL : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (X' : Scheme.{0}) (π : X' ⟶ X₁) (U : X₁.Opens) (s : U.toScheme ⟶ X'),
    (U : Set X₁).Nonempty ∧ s ≫ π = U.ι ∧ IT π ∧ IT (π ≫ p₁)

def Norm : Prop := ∀ {Z W : Scheme.{0}} (f : W ⟶ Z) [QuasiSeparated f], AICSch Z →
  (∃ (U : Z.Opens) (s : U.toScheme ⟶ W), (U : Set Z).Nonempty ∧ s ≫ f = U.ι) →
  ∃ (Z' : Scheme.{0}) (v : Z' ⟶ W), IsIntegralHom v ∧ AICSch Z' ∧ IsDominant (v ≫ f)

theorem goal_of (hI : Img) (hC : ChowL) (hN : Norm) : LateralTheory.E.t_E2Cut.Chow := by
  intro A _ Z X h p _ hh hZ
  obtain ⟨X₁, h₁, p₁, hX₁, hp₁, hh₁, hd₁, e⟩ := hI A h p hh hZ.1
  have := hp₁
  have := hh₁
  have := hd₁
  obtain ⟨X', π, U, s, hU, hs, hπ, hπp⟩ := hC A p₁ hX₁
  obtain ⟨_, _⟩ := (hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip).qc
  have hU' : ((h₁ ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hxU, y, rfl⟩ := h₁.denseRange.inter_open_nonempty _ U.isOpen hU
    exact ⟨y, hxU⟩
  have sec : ∃ (V : Z.Opens) (t : V.toScheme ⟶ pullback h₁ π), (V : Set Z).Nonempty ∧ t ≫ pullback.fst h₁ π = V.ι :=
    ⟨h₁ ⁻¹ᵁ U, pullback.lift (h₁ ⁻¹ᵁ U).ι ((h₁ ∣_ U) ≫ s) (by rw [Category.assoc, hs, morphismRestrict_ι]), hU',
      pullback.lift_fst _ _ _⟩
  obtain ⟨Z', v, hv, hZ', hd⟩ := hN (pullback.fst h₁ π) hZ sec
  refine ⟨Z', v ≫ pullback.fst h₁ π, hZ', hd, hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip |>.pre v hv, ?_⟩
  have : (v ≫ pullback.fst h₁ π) ≫ h ≫ p = (v ≫ pullback.snd h₁ π) ≫ π ≫ p₁ := by
    rw [← e, Category.assoc, reassoc_of% pullback.condition, Category.assoc]
  rw [this]
  exact hπp.pre _ inferInstance

end LateralTheory.E.ChowCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ConeExcision
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafExcPf

def LeafMono : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [Mono f] (n : ℤ),
  Mono (((chains R).map f).f n)

def LeafSq : Prop := ∀ (R : Type) [CommRing R] {U E' E : Spc} (f : U ⟶ E) [Mono f] (g : E' ⟶ E),
  (∀ (p : ℕ) (T : Scheme.{0}) (y : Sx E p T), EtLoc T fun V k =>
    (∃ u : Sx U p V, sxMap f u = sxRes k y) ∨ ∃ a : Sx E' p V, sxMap g a = sxRes k y) →
  (∀ (p : ℕ) (T : Scheme.{0}) (a b : Sx E' p T), sxMap g a = sxMap g b → EtLoc T fun V k =>
    sxRes k a = sxRes k b ∨ ∃ u : Sx U p V, sxMap f u = sxRes k (sxMap g a)) →
  ∀ n : ℤ, IsPushout (((chains R).map (pullback.snd f g)).f n) (((chains R).map (pullback.fst f g)).f n)
    (((chains R).map g).f n) (((chains R).map f).f n)

def LeafConePush : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {K' L' K L : Cx R}
  (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L), a ≫ v = u ≫ b →
  (∀ n, Mono (a.f n)) → (∀ n, Mono (b.f n)) → (∀ n, IsPushout (a.f n) (u.f n) (v.f n) (b.f n)) →
  ∀ n : ℤ, (Subsingleton (HK R (mappingCone a) F n) ↔ Subsingleton (HK R (mappingCone b) F n))

theorem LeafExc_of (hRel : LeafRel) (hMono : LeafMono) (hSq : LeafSq) (hCone : LeafConePush) : LeafExc := by
  intro hA1 R _ F c U E' E f _ g h1 h2
  unfold Conn
  rw [hRel R F c, hRel R F c]
  have hsq : (chains R).map (pullback.snd f g) ≫ (chains R).map g =
      (chains R).map (pullback.fst f g) ≫ (chains R).map f := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  have key := hCone hA1 R F _ _ _ _ hsq (fun n => hMono R _ n) (fun n => hMono R f n) (hSq R f g h1 h2)
  constructor
  · intro h n hn; exact (key n).2 (h n hn)
  · intro h n hn; exact (key n).1 (h n hn)

end LateralTheory.E.LeafExcPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ContPf

def PC (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

def ContAff : Prop := Hyp → ∀ (X : Scheme.{0}) [IsAffine X], PC X

def ContStep : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PC X

def ContInd : Prop := ∀ (P : Scheme.{0} → Prop), (∀ (X : Scheme.{0}) [IsAffine X], P X) →
  (∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X) →
  ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X], P X

theorem Cont_of (hMV : MV) (hA : ContAff) (hS : ContStep) (hI : ContInd) : Cont := by
  intro h q J _ _ D c hc ha hcs hqs hu n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have := hcs j0
  have := hqs j0
  have key : PC (D.obj j0) := hI PC (fun X _ => hA h X) (fun X U V hU hV hUV pU pV pW => hS h hMV X U V hU hV hUV pU pV pW)
    (D.obj j0)
  exact key q D c hc ha hcs hqs hu j0 ⟨Iso.refl _⟩ n i

end LateralTheory.E.ContPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoprodPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.CoprodPf

def FreeCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (X : ι → Scheme.{0}),
  Nonempty (IsColimit (Cofan.mk ((free R).obj (yoneda.obj (∐ X))) fun j => (free R).map (yoneda.map (Sigma.ι X j))))

def ChainsDiscCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q),
  Nonempty (IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))

def HKCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (K : ι → Cx R) (c : Cofan K), IsColimit c →
  ∀ (F : Shv R) (n : ℤ), Function.Bijective fun (x : HK R c.pt F n) (j : ι) => HK.pull R (c.inj j) F n x

theorem Coprod_of (h1 : FreeCoprod) (h2 : ChainsDiscCoprod) (h3 : HKCoprod) : LateralTheory.E.t_E3Cut.Coprod := by
  intro R _ F ι X n
  obtain ⟨hc⟩ := h2 R (fun j => yoneda.obj (X j)) (yoneda.obj (∐ X)) (fun j => yoneda.map (Sigma.ι X j)) (h1 R X)
  exact h3 R _ _ hc F n

end LateralTheory.E.CoprodPf
end
end


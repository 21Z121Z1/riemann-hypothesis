import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.EtaleCohomology.EtaleSheaves.Bundle0005

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.StalkCut

def RelZ (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map f)) (tw q i) m)) ∧
  Function.Injective (pull _ (sch.map (Spec.map f)) (tw q i) n)

def BCn (q : ℕ) (i n : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RelZ q i n φ'

def PushClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)

def EtClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)

theorem relZ_neg (hH : Hyp) (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (hn : n < 0) : RelZ q i n f := by
  have hA9 := (hH.2.2.2.2.2.1 (ZMod q) (tw q i)).1
  refine ⟨fun m hm y => ?_, fun x y _ => ?_⟩
  · haveI := hA9 (sch.obj (Spec B)) m (by omega)
    exact ⟨0, Subsingleton.elim _ _⟩
  · haveI := hA9 (sch.obj (Spec A)) n hn
    exact Subsingleton.elim _ _

theorem re_of_relZ {q : ℕ} {i : ℤ} {A B : CommRingCat.{0}} {f : A ⟶ B} (h : ∀ n, RelZ q i n f) : RE q i f :=
  fun m => ⟨(h m).2, (h (m + 1)).1 m rfl⟩

def DescInt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  BCn q i n φ (c ≫ g) → BCn q i n φ c

def DescLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  (∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)) →
  BCn q i n φ d

theorem goal_of (hInt : DescInt) (hLoc : DescLoc) : LateralTheory.E.t_E3Cut.Stalk := by
  intro hH q _ i A Y φ hq P hpush het hcov C c hC
  have key : ∀ k : ℕ, ∀ m : ℤ, m < k → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c := by
    intro k
    induction k with
    | zero =>
      intro m hm C c _ Y' w φ' _
      exact relZ_neg hH q i m φ' (by exact_mod_cast hm)
    | succ k ih =>
      intro m hm C c hC
      have hm' : m ≤ (k : ℤ) := by push_cast at hm; omega
      rcases lt_or_eq_of_le hm' with h | h
      · exact ih m h C c hC
      · subst h
        obtain ⟨D, g, hgi, hgs, hD, hpts⟩ := hcov C c hC
        have hDl : BCn q i (k : ℤ) φ (c ≫ g) :=
          hLoc hH q i k φ hq P @hpush @het ih D (c ≫ g) hD (fun r hr => by
            obtain ⟨O, o, Q, h1, h2, h3, h4⟩ := hpts r hr
            exact ⟨O, o, Q, h1, h2, h3, by rwa [Category.assoc]⟩)
        exact hInt hH q i k φ hq P @hpush ih c g hC hD hgi hgs hDl
  intro Y' w φ' hpo
  refine re_of_relZ fun n => ?_
  exact key (n.toNat + 1) n (by omega) C c hC Y' w φ' hpo

end LateralTheory.E.StalkCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkGerm
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ZLGPf

variable {Y X S : Scheme.{0}}

abbrev overO (p : X ⟶ S) (U : S.Opens) : Scheme.{0} := pullback p U.ι

abbrev resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : overO p V ⟶ overO p U :=
  pullback.map p V.ι p U.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp)

abbrev fO (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : overO (f ≫ p) U ⟶ overO p U :=
  pullback.map (f ≫ p) U.ι p U.ι f (𝟙 _) (𝟙 _) (by simp) (by simp)

def Germ (q : ℕ) (i n : ℤ) (f : Y ⟶ X) (p : X ⟶ S) (s : S) : Prop :=
  (∀ (U : S.Opens), s ∈ U → ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ (U : S.Opens), s ∈ U → ∀ y : Ht q (sch.obj (overO (f ≫ p) U)) n i,
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ ∃ x : Ht q (sch.obj (overO p V)) n i,
      pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y)

def StalkGerm : Prop := Cont → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, ∀ s : S,
  Eqv _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) →
  ∀ n : ℤ, Germ q i n f p s

def ZarInd : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, (∀ (s : S) (n : ℤ), Germ q i n f p s) → Eqv _ (sch.map f) (tw q i)

theorem ZLG_of (hC : Cont) (hM : MV) (h1 : StalkGerm) (h2 : ZarInd) : ZLG := by
  intro hH q Y X S f p _ _ _ _ _ _ hq i hs
  exact h2 hM hH q f p hq i fun s n => h1 hC hH q f p hq i s (hs s) n

end LateralTheory.E.ZLGPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SteinPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SteinPf
open LateralTheory.E.t_E2Cut

def RelNorm : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], AICSch Z →
  ∃ (T : Scheme.{0}) (c : Z ⟶ T) (k : T ⟶ S), IsIntegral T ∧ IsDominant c ∧ IsIntegralHom k ∧ c ≫ k = g ∧
    ∀ V : T.Opens, IsAffineOpen V → (V : Set T).Nonempty →
      ((c ⁻¹ᵁ V : Set Z).Nonempty ∧ Function.Injective (c.app V) ∧
        ∀ b : Γ(Z, c ⁻¹ᵁ V), (c.app V).hom.IsIntegralElem b → ∃ a, c.app V a = b)

def AICOpen : Prop := ∀ {Z : Scheme.{0}}, AICSch Z → ∀ W : Z.Opens, (W : Set Z).Nonempty → AIC Γ(Z, W)

theorem aic_of_int {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hB : AIC B) (hi : Function.Injective φ)
    (hc : ∀ b : B, φ.IsIntegralElem b → ∃ a, φ a = b) (hn : Nontrivial B) : AIC A := by
  intro p hm hd
  obtain ⟨b, hb⟩ := hB (p.map φ) (hm.map φ) (by rw [hm.natDegree_map]; exact hd)
  obtain ⟨a, rfl⟩ := hc b ⟨p, hm, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  refine ⟨a, hi ?_⟩
  rw [map_zero, ← Polynomial.eval_map_apply]; exact hb

theorem Stein_of (hR : RelNorm) (hA : AICOpen) : Stein := by
  intro Z S g _ _ hZ
  obtain ⟨T, c, k, hT, hc, hk, hck, hV⟩ := hR g hZ
  refine ⟨T, c, k, ⟨hT, fun V hV' hne => ?_⟩, hc, hk, hck⟩
  obtain ⟨hne', hi, hcl⟩ := hV V hV' hne
  have hB := hA hZ _ hne'
  have : IsIntegral Z := hZ.1
  have : Nonempty (c ⁻¹ᵁ V) := hne'.to_subtype
  exact aic_of_int (c.app V).hom hB hi hcl inferInstance

end LateralTheory.E.SteinPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

def PolyPO : Prop := ∀ {A B : CommRingCat.{0}} (b : A ⟶ B),
  IsPushout (pC A) b (CommRingCat.ofHom (Polynomial.mapRingHom b.hom)) (pC B)

def IECob : Prop := ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D),
  IsPushout f g u v → IE f → IE v

def FracAIC : Prop := ∀ (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K], AIC T → AIC K

def FracOf : Prop := ∀ (B C : Type) [CommRing B] [CommRing C] [IsDomain C] (j : B →+* C), Function.Injective j →
  (∀ z : C, ∃ s y : B, s ≠ 0 ∧ j s * z = j y) →
  @IsFractionRing B _ (FractionRing C) _ ((algebraMap C (FractionRing C)).comp j).toAlgebra

theorem ULAStalk_of (hI : IntClos) (hT : SHTensor) (hA : AICSH) (hE : SHEqv) (hC3 : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial)
    (p1 : PolyPO) (p2 : IECob) (p3 : FracAIC) (p4 : FracOf) : ULAStalk := by
  intro H q _ i A X h hq hA' hX hh hloc C c _ _ hCa hCr Y' w φ' sq
  obtain ⟨B, b, j, hbj, hbint, hjinj, hBloc, hBaic, hfr⟩ := hI c hA' hCa hCr
  have : IsDomain B := Function.Injective.isDomain j.hom hjinj
  let K := FractionRing C
  let l : C ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap C K)
  let algBK : Algebra B K := ((algebraMap C K).comp j.hom).toAlgebra
  have : IsFractionRing B K := p4 B C j.hom hjinj hfr
  have hKsh : SH K := hA K (p3 C K hCa)
  have hBsh : SH B := hA B hBaic
  have hCsh : SH C := hA C hCa
  have hqB : IsUnit (q : B) := by simpa using hq.map b.hom
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom

  let mB : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial B) := CommRingCat.ofHom (Polynomial.mapRingHom b.hom)
  have sB : IsPushout h mB (pushout.inl h mB) (pushout.inr h mB) := IsPushout.of_hasPushout _ _
  have hBIE : IE (pushout.inr h mB) := p2 _ _ _ _ sB hh
  have sBA : IsPushout (pC A ≫ h) b (pushout.inl h mB) (pC B ≫ pushout.inr h mB) := (p1 b).paste_horiz sB
  let ZB : CommRingCat.{0} := pushout h mB
  have hZBsh : SH ZB := hT _ _ _ _ sBA hA' hX hloc hbint hBloc
  have r1 : RE q i (pC B ≫ pushout.inr h mB) := hE H q i _ hqB hBsh hZBsh
  let bl : B ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap B K)
  have sL : IsPushout (pC B ≫ pushout.inr h mB) bl (pushout.inl _ bl) (pushout.inr _ bl) := IsPushout.of_hasPushout _ _
  have r2 : RE q i (pushout.inl (pC B ≫ pushout.inr h mB) bl) :=
    hC3 H q i B K hBaic hqB (pushout h mB) (pushout.inr h mB) hBIE _ _ _ sL.flip
  have r3 : RE q i bl := hE H q i bl hqB hBsh hKsh
  have r4 : RE q i (pushout.inr (pC B ≫ pushout.inr h mB) bl) :=
    RE.of_comp_left r3 (by rw [← pushout.condition]; exact r1.comp r2)

  let mC : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial C) := CommRingCat.ofHom (Polynomial.mapRingHom c.hom)
  let hC : CommRingCat.of (Polynomial C) ⟶ Y' := (p1 c).desc (h ≫ w) φ' (by rw [← Category.assoc]; exact sq.w)
  have e1 : mC ≫ hC = h ≫ w := (p1 c).inl_desc _ _ _
  have e2 : pC C ≫ hC = φ' := (p1 c).inr_desc _ _ _
  have sC : IsPushout h mC w hC := IsPushout.of_left (by rw [e2]; exact sq) e1.symm (p1 c)
  have hCIE : IE hC := p2 _ _ _ _ sC hh
  have sq' : IsPushout l (pC C ≫ hC) (pushout.inr φ' l) (pushout.inl φ' l) := by
    rw [e2]; exact (IsPushout.of_hasPushout φ' l).flip
  have r5 : RE q i (pushout.inl φ' l) := hC3 H q i C K hCa hqC Y' hC hCIE _ _ _ sq'
  have r6 : RE q i l := hE H q i l hqC hCsh hKsh
  have ebl : b ≫ bl = c ≫ l := by rw [← hbj]; rfl
  have PZ : IsPushout (pC A ≫ h) (c ≫ l) (pushout.inl h mB ≫ pushout.inl (pC B ≫ pushout.inr h mB) bl)
      (pushout.inr (pC B ≫ pushout.inr h mB) bl) := by
    rw [← ebl]; exact sBA.paste_vert sL
  have PZ' : IsPushout (pC A ≫ h) (c ≫ l) (w ≫ pushout.inl φ' l) (pushout.inr φ' l) :=
    sq.paste_vert (IsPushout.of_hasPushout φ' l)
  have r7 : RE q i (pushout.inr φ' l) := by
    rw [← PZ.inr_isoIsPushout_hom _ _ PZ']; exact r4.comp (RE.of_isIso q i _)
  exact RE.of_comp_right r5 (by rw [pushout.condition]; exact r6.comp r7)

end LateralTheory.E.ULAStalkPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ValSuccAbove
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

theorem slantHom_neg (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} :
    ∃ f : ((Fin m → Γ) →₀ R) →+ _, ∀ c, f c = slantHom R X c :=
  ⟨AddMonoidHom.mk' (slantHom R X) (slantHom_add R X), fun _ => rfl⟩

theorem homD_of (h : Faces) : HomD := by
  intro R _ Γ _ X m b
  induction b using Finsupp.induction_linear with
  | zero => rw [slantHom_zero, show bd R (0 : (Fin (m + 1) → Γ) →₀ R) = 0 from map_zero _, slantHom_zero]; exact zero_comp
  | add a b ha hb =>
    rw [slantHom_add, show bd R (a + b) = bd R a + bd R b from map_add _ _ _, slantHom_add, ← ha, ← hb]
    exact Preadditive.add_comp _ _ _ _ _ _
  | single g r =>
    obtain ⟨f, hf⟩ := slantHom_neg R X (Γ := Γ) (m := m)
    have e : bd R (Finsupp.single g r) = Finsupp.single (fun i => g i.succ) r +
        ∑ j : Fin (m + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r := by
      have := groupHomology.inhomogeneousChains.d_single (A := Rep.trivial R Γ R) m g r
      refine this.trans ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul R]
      simp
    have d : ((chainsN R).obj (BX Γ X)).d (m + 1) m =
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((BX Γ X).δ i) :=
      AlgebraicTopology.alternatingFaceMapComplex_obj_d _ m
    rw [e, ← hf (_ + _), map_add, map_sum, d, slantHom_single]
    have e2 : ∀ j : Fin (m + 1), f ((-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r) =
        (-1 : ℤ) ^ ((j : ℕ) + 1) • (ULift.up r : ULift.{1} R) • (free R).map (grpPt X (j.contractNth (· * ·) g)) :=
      fun j => by rw [map_zsmul, hf, slantHom_single]
    rw [Finset.sum_congr rfl fun j _ => e2 j, hf, slantHom_single]
    erw [Preadditive.comp_sum]
    rw [Fin.sum_univ_succ]
    congr 1
    · erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).1]
      exact one_smul ℤ _
    · refine Finset.sum_congr rfl fun j _ => ?_
      erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).2 j]
      rfl

theorem sch_d (R : Type) [CommRing R] (X : Scheme.{0}) : ((chains R).obj (sch.obj X)).d (-1) 0 = 0 := by
  have d : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((sch.obj X).δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0
  have d0 : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 = 0 := by
    rw [d, Fin.sum_univ_two]
    have : (sch.obj X).δ (0 : Fin (0 + 2)) = (sch.obj X).δ 1 := rfl
    rw [this]; simp; rfl
  have := ((chainsN R).obj (sch.obj X)).extend_d_eq ComplexShape.embeddingDownNat (i := 0 + 1) (j := 0) (i' := -1) (j' := 0)
    (by simp) (by simp)
  refine this.trans ?_
  rw [d0]; simp; rfl

theorem single_congr {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q q' : ℤ} (f : K.X p ⟶ L.X q)
    (n m : ℤ) (hm : n + 1 = m) (hq : q + 1 = q') (hK : K.d (p - 1) p = 0) :
    δ n m (Cochain.single f n) = Cochain.single (f ≫ L.d q q') m := by
  rw [Cochain.δ_single f n m hm (p - 1) q' (by omega) hq, hK]
  simp

theorem deltaCo_of (h : HomD) : DeltaCo := by
  intro R _ Γ _ X
  refine ⟨fun c => ?_, fun m b => ?_⟩
  · unfold slantCo
    rw [single_congr _ _ _ rfl rfl (sch_d R X)]
    have z : IsZero (((chains R).obj (BX Γ X)).X (-((0 : ℕ) : ℤ) + 1)) :=
      ((chainsN R).obj (BX Γ X)).isZero_extend_X ComplexShape.embeddingDownNat _ (fun i hi => by
        simp at hi; omega)
    rw [z.eq_of_tgt (_ ≫ _) 0]
    simp
  · unfold slantCo
    rw [single_congr (q' := -(m : ℤ)) _ _ _ (by omega) (by omega) (sch_d R X)]
    congr 1
    have := ((chainsN R).obj (BX Γ X)).extend_d_eq ComplexShape.embeddingDownNat (i := m + 1) (j := m)
      (i' := -((m + 1 : ℕ) : ℤ)) (j' := -(m : ℤ)) (by simp) (by simp)
    unfold slantV
    rw [← h R Γ X m b]
    erw [this, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
    rfl

theorem gmap1 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c : Fin n) (ha : a.val = c.val)
    (hb : b.val = c.val + 1) : (show Γ from (grpSimplex g).map f) = (g c)⁻¹ := by
  obtain ⟨a, _⟩ := a
  obtain ⟨b, _⟩ := b
  obtain ⟨c, hc⟩ := c
  obtain rfl : a = c := ha
  obtain rfl : b = a + 1 := hb
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹) a hc

theorem gmap2 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c d : Fin n) (ha : a.val = c.val)
    (hd : d.val = c.val + 1) (hb : b.val = c.val + 2) : (show Γ from (grpSimplex g).map f) = (g c * g d)⁻¹ := by
  have h1 : a ≤ d.castSucc := by rw [Fin.le_def]; simp; omega
  have h2 : d.castSucc ≤ b := by rw [Fin.le_def]; simp; omega
  have e := (grpSimplex g).map_comp (homOfLE h1) (homOfLE h2)
  have e1 := gmap1 g _ _ (homOfLE h1) c ha (by simpa using hd)
  have e2 := gmap1 g _ _ (homOfLE h2) d (by simp) (by omega)
  rw [mul_inv_rev, ← e1, ← e2]
  exact e

theorem nerve_ext {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : ∀ (i : Fin m) (f : j.succAbove i.castSucc ⟶ j.succAbove i.succ), (show Γ from (grpSimplex g).map f) = (g' i)⁻¹) :
    (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g' := by
  refine ComposableArrows.ext (fun _ => rfl) fun i hi => ?_
  erw [Category.id_comp, Category.comp_id]
  exact (h ⟨i, hi⟩ _).trans (gmap1 g' _ _ _ ⟨i, hi⟩ rfl rfl).symm

theorem nerve_zero {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) :
    (nerve (SingleObj Γ)).δ 0 (grpSimplex g) = grpSimplex (fun i => g i.succ) :=
  nerve_ext g _ 0 fun i f => gmap1 g _ _ f i.succ (by simp) (by simp)

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (i : Fin n) : (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by
  unfold Fin.succAbove
  by_cases h : i.val < j.val
  · rw [if_pos h, if_pos (show i.castSucc < j from h)]; rfl
  · rw [if_neg h, if_neg (show ¬ i.castSucc < j from h)]; rfl

theorem nerve_succ {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (j : Fin (m + 1)) :
    (nerve (SingleObj Γ)).δ j.succ (grpSimplex g) = grpSimplex (j.contractNth (· * ·) g) := by
  refine nerve_ext g _ _ fun i f => ?_
  have a := val_succAbove j.succ i.castSucc
  have b := val_succAbove j.succ i.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at a b
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_pos (by omega)]; rfl) (by rw [b, if_pos (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
    exact gmap2 g _ _ f _ _ (by rw [a, if_pos (by omega)]; rfl) rfl (by rw [b, if_neg (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_neg (by omega)]; rfl) (by rw [b, if_neg (by omega)]; rfl)

theorem ev_pres (P Q : Spc) (n : SimplexCategoryᵒᵖ) : PreservesLimit (pair P Q) ((evaluation SimplexCategoryᵒᵖ PSh).obj n) :=
  (evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit

theorem lift_fst {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u : W ⟶ P.obj n) (v : W ⟶ Q.obj n) :
    haveI := ev_pres P Q n
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.fst : P ⨯ Q ⟶ P).app n = u ∧
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.snd : P ⨯ Q ⟶ Q).app n = v := by
  haveI := ev_pres P Q n
  constructor
  · erw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  · erw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

theorem prod_ext {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u v : W ⟶ (P ⨯ Q).obj n)
    (h1 : u ≫ (prod.fst : P ⨯ Q ⟶ P).app n = v ≫ (prod.fst : P ⨯ Q ⟶ P).app n)
    (h2 : u ≫ (prod.snd : P ⨯ Q ⟶ Q).app n = v ≫ (prod.snd : P ⨯ Q ⟶ Q).app n) : u = v := by
  haveI := ev_pres P Q n
  exact BinaryFan.IsLimit.hom_ext
    (isLimitOfHasBinaryProductOfPreservesLimit ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q) h1 h2

theorem face_of {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g') : grpPt X g ≫ (BX Γ X).δ j = grpPt X g' := by
  have a := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk (m + 1))) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  have b := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk m)) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g', naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  refine prod_ext _ _ ?_ ?_
  · refine Eq.trans ?_ b.1.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    refine (congrArg (· ≫ (cst (SingleObj Γ)).δ j) a.1).trans ?_
    ext U x
    exact h
  · refine Eq.trans ?_ b.2.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    exact congrArg (· ≫ (sch.obj X).δ j) a.2

theorem faces : Faces := fun _ _ X _ g =>
  ⟨face_of X g _ _ (nerve_zero g), fun j => face_of X g _ _ (nerve_succ g j)⟩

theorem goal : LateralTheory.E.EtaleChapterDThree := goal_of (deltaCo_of (homD_of faces))

end LateralTheory.E.t_D3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZarLocalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZarLocalPf

def LocSH : Prop := ∀ (S : Type) [CommRing S], AIC S → ∀ p : PrimeSpectrum S, SH (Localization.AtPrime p.asIdeal)

def LocDiag : Prop := ∀ (S : Type) [CommRing S] (p : PrimeSpectrum S),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
    Nonempty (IsColimit c) ∧ (SH (Localization.AtPrime p.asIdeal) → SH c.pt) ∧
    ∃ (j0 : J) (a : S →+* D.obj j0), ∀ (k : J) (m : j0 ⟶ k), ∃ f : S, f ∉ p.asIdeal ∧
      ∃ r : D.obj k →+* Localization.Away f, r.comp ((D.map m).hom.comp a) = algebraMap S (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem ZarLocal_of (hSH : LocSH) (hD : LocDiag) : LateralTheory.E.t_E1Cut.ZarLocal := by
  intro hB1 hB2 q S _ hS hq n i hn x p
  obtain ⟨J, _, _, D, c, ⟨hc⟩, hpt, j0, a, hk⟩ := hD S p
  have hsh : SH c.pt := hpt (hSH S hS p)
  set y := pull _ (spMap a) _ _ x with hy
  have hqa : IsUnit ((q : ℕ) : D.obj j0) := by simpa using hq.map a
  have h0 : pull _ (spMap (c.ι.app j0).hom) _ _ y = 0 := by
    exact @Subsingleton.elim _ (hB2 (ZMod q) c.pt hsh (tw q i) n hn) _ _
  obtain ⟨k, m, hm⟩ := (hB1 q D c hc n i).2 j0 y hqa h0
  obtain ⟨f, hf, r, hr⟩ := hk k m
  refine ⟨f, hf, ?_⟩
  rw [← hr, spMap_comp, pull_comp, spMap_comp, pull_comp, ← hy, hm, map_zero]

end LateralTheory.E.ZarLocalPf
end
end


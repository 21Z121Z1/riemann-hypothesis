import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0035

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CoverCut

def ClopenSys {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) : Prop :=
  Nonempty (IsLimit c) ∧ (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
    ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)

def Build : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧
    ∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ AICSch c.pt ∧ ∀ j, IsIntegralHom ((c.π.app j ≫ ι j) ≫ k)

def ProEqv : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)),
  (∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) →
  PB q i g

theorem goal_of (hB : Build) (hP : ProEqv) : Cover := by
  intro H q i A _ _ hq P _ _ p hZ
  obtain ⟨Y, k, hk, hs, hY⟩ := hB (P := P)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated k
  refine ⟨Y, k, hk, hs, hP H q i A hq (k ≫ p) fun y => ?_⟩
  obtain ⟨J, _, _, D, c, ι, hc, hA, hint⟩ := hY y
  refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, fun j => ?_⟩
  have := hZ c.pt ((c.π.app j ≫ ι j) ≫ k) (hint j) hA
  simpa only [Category.assoc] using this

end LateralTheory.E.CoverCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverIntegralClosure
section
noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.CoverIntegralClosure

theorem inj_sub (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) :=
  Subtype.val_injective

theorem aic_integralClosure (P : Type) [CommRing P] [IsDomain P] :
    AIC (integralClosure P (AlgebraicClosure (FractionRing P))) := by
  intro p hp hdeg
  have hdeg' : (p.map (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P)))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (inj_sub P)]
    intro h
    rw [Polynomial.degree_eq_natDegree hp.ne_zero] at h
    norm_cast at h
    omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg'
  have hTa : IsIntegral (integralClosure P (AlgebraicClosure (FractionRing P))) a :=
    ⟨p, hp, by simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha⟩
  have hPa : IsIntegral P a := isIntegral_trans a hTa
  have ha' : Polynomial.eval₂ (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) a p = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha
  refine ⟨⟨a, hPa⟩, ?_⟩
  apply inj_sub P
  rw [map_zero, ← Polynomial.eval₂_at_apply]
  exact ha'

theorem inj_P (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap P (integralClosure P (AlgebraicClosure (FractionRing P)))) := by
  have h : Function.Injective (algebraMap P (AlgebraicClosure (FractionRing P))) := by
    rw [IsScalarTower.algebraMap_eq P (FractionRing P) (AlgebraicClosure (FractionRing P))]
    exact (algebraMap (FractionRing P) _).injective.comp (IsFractionRing.injective P _)
  rw [IsScalarTower.algebraMap_eq P (integralClosure P (AlgebraicClosure (FractionRing P)))
    (AlgebraicClosure (FractionRing P))] at h
  exact fun x y hxy => h (by simp only [RingHom.comp_apply, hxy])

theorem Cover_of : LateralTheory.E.t_E1Cut.Cover := by
  intro A _
  let π : MvPolynomial A ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hπ : Function.Surjective π := fun a => ⟨MvPolynomial.X a, by simp [π]⟩
  let T := integralClosure (MvPolynomial A ℤ) (AlgebraicClosure (FractionRing (MvPolynomial A ℤ)))
  let I : Ideal T := (RingHom.ker π).map (algebraMap (MvPolynomial A ℤ) T)
  let ψ : MvPolynomial A ℤ ⧸ RingHom.ker π →+* T ⧸ I :=
    Ideal.quotientMap I (algebraMap (MvPolynomial A ℤ) T) Ideal.le_comap_map
  let φ : A →+* T ⧸ I := ψ.comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hcomp : φ.comp π = (Ideal.Quotient.mk I).comp (algebraMap (MvPolynomial A ℤ) T) := by
    apply RingHom.ext
    intro x
    simp [φ, ψ, Ideal.quotientMap_mk]
  refine ⟨T ⧸ I, inferInstance, φ, ?_, ?_, ?_⟩
  · apply RingHom.IsIntegral.tower_top π φ
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  · intro p
    have : (Ideal.comap π p.asIdeal).IsPrime := Ideal.comap_isPrime π p.asIdeal
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T)
      (Ideal.comap π p.asIdeal) (⊥ : Ideal T) (by
        rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (inj_P _)]
        exact bot_le)
    have hIQ : I ≤ Q := by
      apply Ideal.map_le_iff_le_comap.2
      rw [hQc]
      intro x hx
      simp [RingHom.mem_ker.1 hx]
    have hQ' : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨Q.map (Ideal.Quotient.mk I), hQ'⟩, ?_⟩
    ext1
    apply Ideal.comap_injective_of_surjective π hπ
    simp only [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIQ, hQc]
  · exact ⟨T, inferInstance, inferInstance, Ideal.Quotient.mk I, aic_integralClosure _,
      Ideal.Quotient.mk_surjective⟩

end LateralTheory.E.CoverIntegralClosure
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.CupProductRingLaws

def LeafCupSpec : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
  (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
  ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
    μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LeafTwPairExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def LeafTwPairUnique : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k), μ.cup E hk = μ'.cup E hk

def LeafKumTExists : Prop := ∀ (q : ℕ) [NeZero q], ∃ t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U, IsKum q t

def IsOneCocycle (q : ℕ) (E : Spc) (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

def IsKumCocycle (q : ℕ) {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) :
    Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
      ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def IsEtaleFirstChernClassCocycle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def LeafOneSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  (∃ α, IsOneCocycle q E α) ∧ ∀ α, IsOneCocycle q E α → one q E = CohomologyClass.mk α

def LeafKumSpec : Prop := ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
  (∃ γ, IsKumCocycle q u γ) ∧ ∀ γ, IsKumCocycle q u γ → kum q u = CohomologyClass.mk γ

def EtaleFirstChernClassRepresentedByChernCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  (∃ γ, IsEtaleFirstChernClassCocycle q L γ) ∧ ∀ γ, IsEtaleFirstChernClassCocycle q L γ → c1 q L = CohomologyClass.mk γ

def LeafNatCup : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
  pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)

def LeafNatOne : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E

def EtaleFirstChernClassNaturalUnderPullback : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
  pull _ f _ _ (c1 q L) = c1 q (f ≫ L)

def LeafNatKum : Prop := ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
  pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def LeafRingUnit : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)

def LeafRingAssoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
  cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)

def LeafRingComm : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j),
  cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

def LeafSupp : Prop := ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g →
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), pull _ f _ _ a = 0 → pull _ g _ _ b = 0 → cup q a b = 0

def ChernClassAdditive : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
  (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M

def LeafAddKum : Prop := ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
  kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

theorem goal_of (_hCup : LeafCupSpec) (_hTw : LeafTwPairExists) (_hTwU : LeafTwPairUnique) (_hKT : LeafKumTExists)
    (_hOne : LeafOneSpec) (_hKum : LeafKumSpec) (_hC1 : EtaleFirstChernClassRepresentedByChernCocycle)
    (h1 : LeafNatCup) (h2 : LeafNatOne) (h3 : EtaleFirstChernClassNaturalUnderPullback) (h4 : LeafNatKum) (h5 : LeafRingUnit) (h6 : LeafRingAssoc)
    (h7 : LeafRingComm) (h8 : LeafSupp) (h9 : ChernClassAdditive) (h10 : LeafAddKum) : LateralTheory.E.E8.CupUnitChernKummerLaws := by
  refine ⟨fun q _ => ⟨h1 q, h2 q, h3 q, h4 q⟩, fun q _ E => ⟨h5 q E, h6 q E, h7 q E⟩, h8, fun q _ => ⟨h9 q, h10 q⟩⟩

end LateralTheory.E.CupProductRingLaws
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescentInduction
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.DescStepPf

def Bounds : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  ((chains R).obj E).IsStrictlyLE 0 ∧ (res R F).IsStrictlyGE 0 ∧ ∀ m, Injective ((res R F).X m)

def LevelIdent : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (p : ℕ) (j : ℤ),
  (Function.Bijective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j)) ∧
  (Function.Injective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j))

def CxDesc : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (n : ℤ),
  (∀ (p : ℕ) (j : ℤ), j < n → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I j)) →
  (∀ p : ℕ, Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I n)) →
  (∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
  (∀ j : ℤ, j < n + 1 → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I (n + 1))

theorem DescStep_of (hB : Bounds) (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep := by
  intro _ R _ F E E' f n hc he
  obtain ⟨h1, h2, h3⟩ := hB R F E
  obtain ⟨h1', -, -⟩ := hB R F E'
  have := h2
  have := h1
  have := h1'
  exact hX R (res R F) h3 ((chains R).map f) n
    (fun p j hj => ((hL R F f p j).1).1 ((hc (op (SimplexCategory.mk p))).1 j hj))
    (fun p => ((hL R F f p n).2).1 (hc (op (SimplexCategory.mk p))).2)
    (fun j => ((hL R F f 0 j).1).1 (he j))

end LateralTheory.E.DescStepPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DomCoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

namespace LateralTheory.E.DomCoverPf

theorem aicFrac (R L : Type) [CommRing R] [CommRing L] (φ : R →+* L) (hR : AIC R)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) : AIC L :=
  _root_.UpperTheory.Reformulated.B.Qn19.aicFrac R L φ hR h

def IdemCover : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ t_E3Cut.SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧
    ∀ z : Localization.AtPrime r, ∃ a b : C, IsUnit (algebraMap D (Localization.AtPrime r) (g.hom b)) ∧
      z * algebraMap D (Localization.AtPrime r) (g.hom b) = algebraMap D (Localization.AtPrime r) (g.hom a)

theorem DomCover_of (h2 : IdemCover) : t_E3Cut.DomCover := by
  intro C hC
  obtain ⟨D, g, hi, hs, hr⟩ := h2 C
  refine ⟨D, g, hi, hs, fun r _ => ⟨(hr r).1, ?_⟩⟩
  exact aicFrac C (Localization.AtPrime r) ((algebraMap D (Localization.AtPrime r)).comp g.hom) hC (hr r).2

end LateralTheory.E.DomCoverPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EqvQAPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EqvQAPf

theorem prim_of_aic (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hS : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  rcases subsingleton_or_nontrivial S with hs | hs
  · exact ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩
  have hm : ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).Monic :=
    (Polynomial.cyclotomic.monic q ℤ).map _
  have hd : 0 < ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).natDegree := by
    rw [(Polynomial.cyclotomic.monic q ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨a, ha⟩ := hS _ hm hd
  exact ⟨⟨a, hq, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; simpa using ha⟩⟩

theorem bij_of_sub {A B : Type*} [AddZeroClass A] [AddZeroClass B] [Subsingleton A] [Subsingleton B] (f : A →+ B) :
    Function.Bijective f :=
  ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end LateralTheory.E.EqvQAPf

open LateralTheory.E.t_E1Cut in
theorem LateralTheory.E.t_E1Cut.EqvQA_of (hAcyc : AcycQA) (hQA : QAClosed) (hH0 : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hLC : LCGood) : EqvQA := by
  intro h1 h9 hb1 hb2 q _ S _ J hS hJ hq i n
  have hqJ : IsUnit (q : S ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
  have hSJ : QA (S ⧸ J) := (hQA S hS).2.2 J
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (h9 (ZMod q) (tw q i)).1 (sp S) n hn
    haveI := (h9 (ZMod q) (tw q i)).1 (sp (S ⧸ J)) n hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
  · obtain ⟨ζ⟩ := LateralTheory.E.EqvQAPf.prim_of_aic q S (hQA S hS).1 hq
    obtain ⟨e, he⟩ := hH0 h9 q i
    have key : ∀ φ, pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0 (e S ζ φ) =
        e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J)) (lcMap (Ideal.Quotient.mk J) φ) :=
      fun φ => he S (S ⧸ J) (Ideal.Quotient.mk J) ζ φ
    have hcomp : (pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0) =
        (e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J))) ∘
          (fun φ => lcMap (Ideal.Quotient.mk J) φ) ∘ (e S ζ).symm := by
      funext x
      obtain ⟨φ, rfl⟩ := (e S ζ).surjective x
      simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
      exact key φ
    rw [hcomp]
    exact (e _ _).bijective.comp ((hLC S J hJ (ZMod q)).comp (e S ζ).symm.bijective)
  · haveI := hAcyc h1 h9 hb1 hb2 q S hS hq n i hn
    haveI := hAcyc h1 h9 hb1 hb2 q (S ⧸ J) hSJ hqJ n i hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtAICPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtAICPf

def Split : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j))

def DomOpen : Prop := ∀ (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D] [Algebra.Etale T D],
  AIC T → IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T D)))

theorem EtAIC_of (hS : Split) (hD : DomOpen) : LateralTheory.E.t_E1Cut.EtAIC := by
  intro T C _ _ _ _ _ hT
  obtain ⟨n, e, he, hdom⟩ := hS T C hT
  refine ⟨n, e, he, fun j => ?_⟩
  have : Algebra.Etale C (Localization.Away (e j)) := inferInstance
  have : Algebra.Etale T (Localization.Away (e j)) := Algebra.Etale.comp T C _
  have h := hD T (Localization.Away (e j)) hT
  rwa [IsScalarTower.algebraMap_eq T C (Localization.Away (e j))] at h

end LateralTheory.E.EtAICPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangePolynomialInductionOfLimit
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.E.t_E3Cut

theorem etale_base_change_fraction_field_of_etale_polynomial_algebra (hC3 : C3) (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (hA : AIC T) (hq : IsUnit (q : T))
    (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C) (hc : Et c) :
    BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c) := by
  letI : Algebra (Polynomial T) C := c.hom.toAlgebra
  haveI : Algebra.Etale (Polynomial T) C := hc
  letI : Algebra T C := (pC (CommRingCat.of T) ≫ c).hom.toAlgebra
  haveI : IsScalarTower T (Polynomial T) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h3 := hC3 q T hA hq C i
  have hsq := CommRingCat.isPushout_tensorProduct T (FractionRing T) C
  let e : CommRingCat.of (FractionRing T) ≅ CommRingCat.of K :=
    (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv.toCommRingCatIso
  have hsq' : IsPushout (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c)
      (e.inv ≫ CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeRight.toRingHom) := by
    refine hsq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x
      simp [e]
    · rfl
    · simp
    · rfl
  exact BC.of_one hsq' h3

theorem etale_base_change_polynomial_induction_of_limit (hL : Limit) : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := by
  intro hH q _ i T K _ _ _ _ _ _ hA hq X h hIE
  have hC3 : C3 := hH.2.2.2.2.2.2.2.2.2.1
  let k := CommRingCat.ofHom (algebraMap T K)
  let φ := pushout.inr k (pC (CommRingCat.of T))
  have P1 : IsPushout k (pC (CommRingCat.of T)) (pushout.inl k (pC (CommRingCat.of T))) φ :=
    IsPushout.of_hasPushout _ _
  have hqX : IsUnit ((q : ℕ) : CommRingCat.of (Polynomial T)) := by
    have := hq.map (Polynomial.C : T →+* Polynomial T)
    simpa using this
  have hEt : ∀ (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C), Et c → BC q i φ c := by
    intro C c hc
    have hb := etale_base_change_fraction_field_of_etale_polynomial_algebra hC3 q i T K hA hq C c hc
    have P2 := IsPushout.of_hasPushout φ c
    exact BC.of_one P2 (hb _ _ _ (P1.paste_vert P2))
  have hB := hL hH q i φ hqX hEt X h hIE
  have P2 := IsPushout.of_hasPushout φ h
  exact BC.of_one (P1.paste_vert P2) (hB _ _ _ P2)

end LateralTheory.E.t_E3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibClosed
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FibPf

def FibClosed : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z S : Scheme.{0}}
  (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  Eqv _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem total (H : Hyp) (h0 : HZero) (hA : AICAcyc) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
    [QuasiSeparated c] (hZ : AICSch Z) (hS : AICSch S) : Eqv _ (sch.map c) (tw q i) := by
  obtain ⟨_, _⟩ := qcqs_of p
  obtain ⟨_, _⟩ := qcqs_of (c ≫ p)
  have : IsIntegral Z := hZ.1
  have : ConnectedSpace Z := inferInstance
  exact eqv_of H.a9 _ (h0 H q c hS this (unit_of hq p) i)
    (fun n hn => hA H q Z hZ (unit_of hq (c ≫ p)) n i hn) (fun n hn => hA H q S hS (unit_of hq p) n i hn)

theorem Fib_of (hF0 : FibClosed) (h0 : HZero) (hA : AICAcyc) : Fib := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZ hS hB
  have ec := total H h0 hA q i A hq c p hZ hS
  have em := hF0 H q i A hq c p hZ hS hB
  have sq : pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst p (cpt A)
      = pullback.fst (c ≫ p) (cpt A) ≫ c := pullback.lift_fst _ _ _
  have key : ∀ n x, pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n (pull _ (sch.map c) (tw q i) n x)
      = pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, sq]
  have fe : ∀ n, (pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)
      = (pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n) := fun n => funext (key n)
  constructor
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)) :=
      (h n).comp (ec n)
    rw [fe n] at h1
    exact (Function.Bijective.of_comp_iff' (em n) _).1 h1
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
        (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n)) := (em n).comp (h n)
    rw [← fe n] at h1
    exact (Function.Bijective.of_comp_iff _ (ec n)).1 h1

end LateralTheory.E.FibPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinEtSectionPf

def Pieces : Prop := LateralTheory.E.t_E1Cut.EtLift → LateralTheory.E.t_E1Cut.EtAIC → ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C], LateralTheory.E.t_E1Cut.QA S →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))))

def FinOpen : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C), IsIdempotentElem e →
  IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) →
  ∃ ε : S, IsIdempotentElem ε ∧
    Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum S)) ∧
    ∃ h : Localization.Away e →+* Localization.Away ε,
      h.comp ((algebraMap C (Localization.Away e)).comp (algebraMap S C)) = algebraMap S (Localization.Away ε)

def Glue : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] (n : ℕ) (e : Fin n → C),
  CompleteOrthogonalIdempotents e → Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) →
  ∀ ε : Fin n → S, (∀ j, IsIdempotentElem (ε j)) →
  (∀ j, Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S))) →
  (∀ j, ∃ h : Localization.Away (e j) →+* Localization.Away (ε j),
      h.comp ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C)) = algebraMap S (Localization.Away (ε j))) →
  Nonempty (C →ₐ[S] S)

theorem FinEtSection_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) (hP : Pieces) (hF : FinOpen) (hG : Glue) : LateralTheory.E.t_E1Cut.FinEtSection := by
  intro S C _ _ _ _ _ hQA hsurj
  obtain ⟨n, e, he, hoi⟩ := hP hL hA S C hQA
  choose ε hε hr hh using fun j => hF S C (e j) (he.idem j) (hoi j)
  exact hG S C n e he hsurj ε hε hr hh

end LateralTheory.E.FinEtSectionPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSuppKillPfSec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafTwSecKill : Prop := ∀ (q : ℕ) [NeZero q] {X Z : Scheme.{0}} [IsNoetherian X] (ι : Z ⟶ X) [IsClosedImmersion ι],
  IsUnit (q : Γ(X, ⊤)) → ∀ (j : ℤ) (s : Sec (tw q j) X), Sec.res ι s = 0 →
  ∀ x ∈ Set.range ι, ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ x ∈ Set.range w ∧ Sec.res w s = 0

end LateralTheory.E.E8
end
end

